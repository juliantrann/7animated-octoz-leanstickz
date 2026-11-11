import FV7z.Start.StackAt
import FV7z.Start.Ready
import FV7z.Start.LoadedAt
import FV7z.Lemmas.CallFn
/-!
# A footprint in the stack and the image of `7zzs` is memory a function can use (PLAN.md G3, startup)

- `Ordinary s x`: the page of `x` is mapped with key 0, on private memory or on a page of a file that a store
  copies. `notKernel_of`, `notShared_of`: regions of such pages are not the kernel's and not shared.
- `seg_ordinary`, `launch_ordinary`: the pages of the segments of `7zzs` are such at its first instruction;
  `StackAt.ordinary`: the stack's.
- `Rgn.In r lo hi`: `r` lies in `[lo, hi)`.
- `launch_footOk`: Zellic's `Footprint.Ok` at the first instruction, for a footprint that owns nothing, writes in
  the stack's mapping and in `.data`/`.bss`'s pages, reads there and in the other segments' pages, has code that is
  the file's in the text segment's pages, and has its code apart from its data.
-/
namespace FV7z.Start
open ZellicX86

/-- The page of `x` is mapped with key 0, on private memory or on a page of a file that a store copies. -/
def Ordinary (s : State) (x : Addr) : Prop :=
  ∃ mp, s.proc.mm.mem.map (pageOf x) = some mp ∧ mp.pkey = 0 ∧
    ((∃ f, s.proc.mm.mem.backings mp.backing = .priv f) ∨
      ∃ fp, s.proc.mm.mem.backings mp.backing = .cow fp ∧ s.proc.mm.mem.files.beyondEof fp = false)

theorem notKernel_of {s : State} {rs : List Rgn} (h : ∀ a, Foot rs a → Ordinary s a) : NotKernel s rs := by
  intro a ha m hm
  obtain ⟨mp, hmp, -, hb⟩ := h a ha
  rw [hm] at hmp
  cases hmp
  rcases hb with ⟨f, hf⟩ | ⟨fp, hf, -⟩
  · rw [hf]
    exact ⟨fun _ e => (by cases e), fun _ e => (by cases e)⟩
  · rw [hf]
    exact ⟨fun _ e => (by cases e), fun _ e => (by cases e)⟩

theorem notShared_of {s : State} {rs : List Rgn} (h : ∀ a, Foot rs a → Ordinary s a) : NotShared s rs := by
  intro a ha m hm fp'
  obtain ⟨mp, hmp, -, hb⟩ := h a ha
  rw [hm] at hmp
  cases hmp
  rcases hb with ⟨f, hf⟩ | ⟨fp, hf, -⟩
  · rw [hf]
    intro e
    cases e
  · rw [hf]
    intro e
    cases e

/-- At the first instruction of `7zzs`, a page of one of the segments' five regions is ordinary. -/
theorem seg_ordinary {l : Launch} (h : Launch.Of V2606.zzs.blob.bytes V2606.zzs.blob.size l) {r : Region}
    {x : Addr}
    (hmem : r ∈ [segFile l.files l.exe ph0, segFile l.files l.exe ph1, segFile l.files l.exe ph2,
      segFile l.files l.exe ph3, segAnon ph3]) (hhas : r.has (pageOf x).toNat = true) : Ordinary l.s₀ x := by
  obtain ⟨mp, hm, hpr, hkey, hb, hsz⟩ := launch_seg' h hmem hhas
  have hcnt : (pageOf x).toNat - r.first < r.count := by
    rw [has_iff] at hhas
    omega
  refine ⟨mp, hm, hkey, ?_⟩
  rw [hb]
  rcases seg_backing l.files l.exe hmem hcnt with hf | ⟨i, hi, hlt⟩
  · exact .inl hf
  · refine .inr ⟨_, hi, ?_⟩
    have hs := h.1.1
    rw [zzs_size_eq] at hs
    simp only [Files.beyondEof, hsz, hs, decide_eq_false_iff_not]
    omega

/-- At the first instruction of `7zzs`, the pages of its segments are ordinary. -/
theorem launch_ordinary {l : Launch} (h : Launch.Of V2606.zzs.blob.bytes V2606.zzs.blob.size l) {x : Addr}
    (hx : (0x400000 ≤ x.toNat ∧ x.toNat < 0x776000) ∨ (0x777000 ≤ x.toNat ∧ x.toNat < 0x7a9000)) :
    Ordinary l.s₀ x := by
  obtain ⟨⟨a0, b0⟩, ⟨a1, b1⟩, ⟨a2, b2⟩, ⟨a3, b3⟩, a4, b4⟩ := seg_pages l.files l.exe
  have hP := pageOf_toNat x
  by_cases h0 : x.toNat < 0x401000
  · exact seg_ordinary h (r := segFile l.files l.exe ph0) (by simp) (by rw [has_iff]; omega)
  by_cases h1 : x.toNat < 0x6d8000
  · exact seg_ordinary h (r := segFile l.files l.exe ph1) (by simp) (by rw [has_iff]; omega)
  by_cases h2 : x.toNat < 0x776000
  · exact seg_ordinary h (r := segFile l.files l.exe ph2) (by simp) (by rw [has_iff]; omega)
  by_cases h3 : x.toNat < 0x795000
  · exact seg_ordinary h (r := segFile l.files l.exe ph3) (by simp) (by rw [has_iff]; omega)
  · exact seg_ordinary h (r := segAnon ph3) (by simp) (by rw [has_iff]; omega)

theorem StackAt.ordinary {prof : Profile} {s : State} {a : ExecArgs} {hdr : ElfHeader} {phs : List Phdr}
    {c : ExecChoice} (h : StackAt prof s a hdr phs c) {x : Addr}
    (h1 : (stackLayout a prof.linux c).start ≤ x.toNat) (h2 : x.toNat < c.stackTop) : Ordinary s x := by
  obtain ⟨mp, hm, -, -, hk, f, hf⟩ := h.page x h1 h2
  exact ⟨mp, hm, hk, .inl ⟨f, hf⟩⟩

/-- The stack's mapping can be read and written where `PKRU` allows key 0. -/
theorem StackAt.rw {prof : Profile} {s : State} {a : ExecArgs} {hdr : ElfHeader} {phs : List Phdr}
    {c : ExecChoice} (h : StackAt prof s a hdr phs c) (hp : s.cpu.pkru &&& 3 = 0) {x : Addr}
    (h1 : (stackLayout a prof.linux c).start ≤ x.toNat) (h2 : x.toNat < c.stackTop) :
    x.canonical prof.feat.la57 = true ∧ s.proc.mm.mem.check prof.feat s.cpu.pkru .read x = none ∧
      s.proc.mm.mem.check prof.feat s.cpu.pkru .write x = none := by
  obtain ⟨mp, hm, hr, hw, hk, f, hf⟩ := h.page x h1 h2
  obtain ⟨cr, cw⟩ := check_priv (feat := prof.feat) hm hk hf hp
  have := h.top.2
  exact ⟨canonical_low (by omega) _, cr hr, cw hw⟩

/-- `r` lies in `[lo, hi)`. -/
def _root_.ZellicX86.Rgn.In (r : Rgn) (lo hi : Nat) : Prop := lo ≤ r.base.toNat ∧ r.base.toNat + r.len ≤ hi

/-- At the first instruction of `7zzs`: a footprint that owns nothing, writes in the stack's mapping and in the
pages of `.data` and `.bss`, reads there and in the other segments' pages, has code that is the file's in the text
segment's pages, and has its code apart from its data, is memory a function can use. -/
theorem launch_footOk {l : Launch} {hdr : ElfHeader} {c : ExecChoice}
    (h : Launch.Of V2606.zzs.blob.bytes V2606.zzs.blob.size l)
    (hst : StackAt l.prof l.s₀ l.args hdr zzsPhdrs c) {F : Footprint} (hown : F.own = [])
    (hw : ∀ r ∈ F.writes, r.In (stackLayout l.args l.prof.linux c).start c.stackTop ∨ r.In 0x777000 0x7a9000)
    (hr : ∀ r ∈ F.reads, r.In (stackLayout l.args l.prof.linux c).start c.stackTop ∨ r.In 0x400000 0x776000 ∨
      r.In 0x777000 0x7a9000)
    (hc : ∀ p ∈ F.code, ∃ a, p.1 = BitVec.ofNat 64 a ∧ 0x401000 ≤ a ∧ a + p.2.length ≤ 0x6d8000 ∧
      Exe.bytesAt V2606.zzs.blob a p.2.length = some p.2)
    (hap : Apart F.data F.codeRgns) : F.Ok l.prof.feat l.s₀ := by
  obtain ⟨hpk, hrs, -⟩ := launch_misc h
  have htop := hst.top.2
  have hd : ∀ r ∈ F.data, r.In (stackLayout l.args l.prof.linux c).start c.stackTop ∨ r.In 0x400000 0x776000 ∨
      r.In 0x777000 0x7a9000 := by
    intro r hr'
    simp only [Footprint.data, hown, List.append_nil, List.mem_append] at hr'
    rcases hr' with hr' | hr'
    · rcases hw r hr' with h1 | h1
      · exact .inl h1
      · exact .inr (.inr h1)
    · exact hr r hr'
  have hcr : ∀ r ∈ F.codeRgns, r.In 0x401000 0x6d8000 := by
    intro r hr'
    simp only [Footprint.codeRgns, List.mem_map] at hr'
    obtain ⟨p, hp, rfl⟩ := hr'
    obtain ⟨a, ea, h1, h2, -⟩ := hc p hp
    show 0x401000 ≤ p.1.toNat ∧ p.1.toNat + p.2.length ≤ 0x6d8000
    rw [ea, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    exact ⟨h1, h2⟩
  have hord : ∀ a, Foot (F.data ++ F.codeRgns) a → Ordinary l.s₀ a := by
    intro a ha
    rcases foot_append_iff.1 ha with ⟨r, hr', hm⟩ | ⟨r, hr', hm⟩
    · rcases hd r hr' with h1 | h1 | h1
      · exact hst.ordinary (Nat.le_trans h1.1 hm.1) (Nat.lt_of_lt_of_le hm.2 h1.2)
      · exact launch_ordinary h (.inl ⟨Nat.le_trans h1.1 hm.1, Nat.lt_of_lt_of_le hm.2 h1.2⟩)
      · exact launch_ordinary h (.inr ⟨Nat.le_trans h1.1 hm.1, Nat.lt_of_lt_of_le hm.2 h1.2⟩)
    · have h1 := hcr r hr'
      exact launch_ordinary h (.inl ⟨Nat.le_trans (by decide) (Nat.le_trans h1.1 hm.1),
        Nat.lt_of_lt_of_le hm.2 (Nat.le_trans h1.2 (by decide))⟩)
  refine ⟨?_, ?_, ?_, ?_, notKernel_of hord, launch_noAlias h _, ?_, ?_, hap, ?_⟩
  · intro r hr'
    rcases List.mem_append.1 hr' with hr' | hr'
    · rcases hd r hr' with h1 | h1 | h1
      · exact Nat.le_trans h1.2 (Nat.le_trans htop (by decide))
      · exact Nat.le_trans h1.2 (by decide)
      · exact Nat.le_trans h1.2 (by decide)
    · exact Nat.le_trans (hcr r hr').2 (by decide)
  · intro r hr' a hm
    rcases hw r hr' with h1 | h1
    · have := hst.rw hpk (Nat.le_trans h1.1 hm.1) (Nat.lt_of_lt_of_le hm.2 h1.2)
      exact ⟨this.1, this.2.2⟩
    · have h2 : 0x777000 ≤ a.toNat := Nat.le_trans h1.1 hm.1
      have h3 : a.toNat < 0x7a9000 := Nat.lt_of_lt_of_le hm.2 h1.2
      exact ⟨canonical_low (by omega) _, ((launch_access h a).2.2.2 h2 h3).2⟩
  · intro r hr' a hm
    rcases hr r hr' with h1 | h1 | h1
    · exact ⟨(hst.rw hpk (Nat.le_trans h1.1 hm.1) (Nat.lt_of_lt_of_le hm.2 h1.2)).1,
        (hst.rw hpk (Nat.le_trans h1.1 hm.1) (Nat.lt_of_lt_of_le hm.2 h1.2)).2.1⟩
    · have h2 : 0x400000 ≤ a.toNat := Nat.le_trans h1.1 hm.1
      have h3 : a.toNat < 0x776000 := Nat.lt_of_lt_of_le hm.2 h1.2
      obtain ⟨c0, c1, c2, -⟩ := launch_access h a
      refine ⟨canonical_low (by omega) _, ?_⟩
      by_cases g0 : a.toNat < 0x401000
      · exact c0 h2 g0
      by_cases g1 : a.toNat < 0x6d8000
      · exact (c1 (by omega) g1).2
      · exact c2 (by omega) h3
    · have h2 : 0x777000 ≤ a.toNat := Nat.le_trans h1.1 hm.1
      have h3 : a.toNat < 0x7a9000 := Nat.lt_of_lt_of_le hm.2 h1.2
      exact ⟨canonical_low (by omega) _, ((launch_access h a).2.2.2 h2 h3).1⟩
  · intro p hp
    obtain ⟨a, ea, h1, h2, hb⟩ := hc p hp
    refine ⟨?_, ?_⟩
    · intro x hm
      have e : (BitVec.ofNat 64 a).toNat = a := by
        rw [BitVec.toNat_ofNat]
        exact Nat.mod_eq_of_lt (by omega)
      simp only [Rgn.Mem, ea, e] at hm
      exact ⟨canonical_low (by omega) _, ((launch_access h x).2.1 (by omega) (by omega)).1⟩
    · rw [ea]
      exact bytes_getD (launch_img h a p.2.length p.2 hb (by omega) (by omega))
  · exact notShared_of fun a ha => hord a (foot_append_iff.2 (.inl (foot_append_iff.2 (.inl ha))))
  · intro a ha
    rw [hown] at ha
    obtain ⟨r, hr', -⟩ := ha
    cases hr'
  · intro r hr'
    simp only [rseqArea, hrs, List.not_mem_nil] at hr'

end FV7z.Start
