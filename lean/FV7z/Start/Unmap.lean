import FV7z.Start.Prot
import FV7z.Lemmas.SysMunmap
import FV7z.Lemmas.Frame
/-!
# `munmap (a, n)`, a step of a run (PLAN.md §M, M1)

`Lemmas/SysMunmap.lean`'s system call as a step of a run that `Fn.Seg` describes, modelled on `Start/Prot.lean`'s
`mprotect`. When the kernel answers an error or finds nothing mapped, nothing changes: the run goes on in the same
`Fn.Seg`. When it unmaps the pages, the layout changes: the run goes on from the state after as a new start, with a
footprint `G` whose bytes are bytes of `F` outside the pages (the code outside them too).

- `unmap_out`, `unmap_cases`: the page map after; `unmap_readByte_out`, `unmap_check_out`: a byte outside the pages
  reads and checks as before.
- `touchesFixed_congr`: `Memory.touchesFixed` depends on the page map and `growsDown` only; `gd_of_fixed`: the initial
  stack's first page is not among the pages.
- `unmap_sub`, `footOk_unmap`, `ready_unmap`, `agree_unmap`: `Footprint.Ok` of such a footprint `G`, `Ready`, the
  footprint's bytes.
- `Seg.s_munmap`: the step.
-/
namespace FV7z.Start
open ZellicX86

variable {m : Memory} {P n : Nat}

theorem unmap_out {p : PageNum} (h : inPages P n p = false) : (m.unmap P n).map p = m.map p := by
  simp only [Memory.unmap, h, Bool.false_eq_true, ↓reduceIte]

theorem unmap_in {p : PageNum} (h : inPages P n p = true) : (m.unmap P n).map p = none := by
  simp only [Memory.unmap, h, ↓reduceIte]

/-- A page mapped after is outside the pages, mapped as before. -/
theorem unmap_cases {p : PageNum} {mp : Mapping} (h : (m.unmap P n).map p = some mp) :
    inPages P n p = false ∧ m.map p = some mp := by
  cases hi : inPages P n p
  · exact ⟨rfl, by rw [← unmap_out hi]; exact h⟩
  · rw [unmap_in hi] at h
    cases h

theorem unmap_readByte_out {x : Addr} (h : inPages P n (pageOf x) = false) :
    (m.unmap P n).readByte x = m.readByte x := by
  have hb : (m.unmap P n).backings = m.backings := rfl
  have hf : (m.unmap P n).files = m.files := rfl
  simp only [Memory.readByte, unmap_out h, hb, hf]

theorem unmap_check_out {feat : Features} {pkru : BitVec 32} {acc : Access} {x : Addr}
    (h : inPages P n (pageOf x) = false) : (m.unmap P n).check feat pkru acc x = m.check feat pkru acc x := by
  have hb : (m.unmap P n).backings = m.backings := rfl
  have hf : (m.unmap P n).files = m.files := rfl
  simp only [Memory.check, unmap_out h, hb, hf]

/-- `Memory.touchesFixed` looks at the page map and `growsDown` only. -/
theorem touchesFixed_congr {m' : Memory} (hm : m.map = m'.map) (hg : m.growsDown = m'.growsDown) :
    m.touchesFixed P n = m'.touchesFixed P n := by
  unfold Memory.touchesFixed Memory.mapAt
  rw [hm, hg]

/-- The initial stack's first page is not among pages that do not touch it. -/
theorem gd_of_fixed {g : PageNum} (h : m.touchesFixed P n = false) (hg : g ∈ m.growsDown) :
    inPages P n g = false := by
  cases hi : inPages P n g
  · rfl
  · exfalso
    simp only [inPages, decide_eq_true_eq] at hi
    unfold Memory.touchesFixed at h
    rw [List.any_eq_false] at h
    apply h (g.toNat - P) (List.mem_range.2 (by omega))
    simp only [Bool.or_eq_true, List.any_eq_true, decide_eq_true_eq]
    exact .inr ⟨g, hg, by omega⟩

/-- A byte of a region's addresses is in the region, if it fits. -/
theorem mem_of_byteAddrs {a x : Addr} {k : Nat} (hf : a.toNat + k ≤ 2 ^ 64) (hx : x ∈ byteAddrs a k) :
    Rgn.Mem ⟨a, k⟩ x := by
  obtain ⟨i, hi, rfl⟩ := mem_byteAddrs.1 hx
  have e := toNat_add_of_fits (a := a) hi hf
  simp only [Rgn.Mem, e]
  omega

/-- The bytes of a footprint `G` that writes bytes `F` writes and reads bytes `F` writes or reads, all outside the
pages, are bytes of `F` outside the pages. -/
theorem unmap_sub {F G : Footprint} (hown : F.own = []) (hGo : G.own = [])
    (hGw : ∀ r ∈ G.writes, ∀ a, r.Mem a → Foot F.writes a ∧ inPages P n (pageOf a) = false)
    (hGr : ∀ r ∈ G.reads, ∀ a, r.Mem a → (Foot F.writes a ∨ Foot F.reads a) ∧ inPages P n (pageOf a) = false) :
    ∀ a, Foot G.data a → Foot F.data a ∧ inPages P n (pageOf a) = false := by
  intro a ha
  simp only [Footprint.data, hGo, hown, List.append_nil] at ha ⊢
  rcases foot_append_iff.1 ha with ⟨r, hr, hm⟩ | ⟨r, hr, hm⟩
  · obtain ⟨h1, h2⟩ := hGw r hr a hm
    exact ⟨foot_append_iff.2 (.inl h1), h2⟩
  · obtain ⟨h1, h2⟩ := hGr r hr a hm
    exact ⟨foot_append_iff.2 h1, h2⟩

/-- `Footprint.Ok` after the `n` pages from `P` are unmapped: of a footprint `G` whose bytes are bytes of `F` outside
the pages, with `F`'s code, which is outside the pages. -/
theorem footOk_unmap {feat : Features} {X Y : State} {F G : Footprint} (hok : F.Ok feat X)
    (hmem : Y.proc.mm.mem = X.proc.mm.mem.unmap P n) (hpk : Y.cpu.pkru = X.cpu.pkru)
    (hrs : X.thread.rseq = none) (hrs' : Y.thread.rseq = none) (hown : F.own = []) (hGo : G.own = [])
    (hGc : G.code = F.code) (hfit : ∀ r ∈ G.writes ++ G.reads, r.Fits)
    (hGw : ∀ r ∈ G.writes, ∀ a, r.Mem a → Foot F.writes a ∧ inPages P n (pageOf a) = false)
    (hGr : ∀ r ∈ G.reads, ∀ a, r.Mem a → (Foot F.writes a ∨ Foot F.reads a) ∧ inPages P n (pageOf a) = false)
    (hcode : ∀ a, Foot F.codeRgns a → inPages P n (pageOf a) = false) : G.Ok feat Y := by
  have hcr : G.codeRgns = F.codeRgns := by simp only [Footprint.codeRgns, hGc]
  have hsub : ∀ a, Foot G.data a → Foot F.data a := fun a ha => (unmap_sub hown hGo hGw hGr a ha).1
  have hsub' : ∀ a, Foot (G.data ++ G.codeRgns) a → Foot (F.data ++ F.codeRgns) a := by
    intro a ha
    rw [hcr] at ha
    rcases foot_append_iff.1 ha with ha | ha
    · exact foot_append_iff.2 (.inl (hsub a ha))
    · exact foot_append_iff.2 (.inr ha)
  have hbk : ∀ a mp, Y.proc.mm.mem.map (pageOf a) = some mp → ∃ m0, X.proc.mm.mem.map (pageOf a) = some m0 ∧
      Y.proc.mm.mem.backings mp.backing = X.proc.mm.mem.backings m0.backing ∧ mp.backing = m0.backing := by
    intro a mp hm
    rw [hmem] at hm ⊢
    exact ⟨mp, (unmap_cases hm).2, rfl, rfl⟩
  have hrsY : rseqArea Y = [] := by simp only [rseqArea, hrs']
  have hrsX : rseqArea X = [] := by simp only [rseqArea, hrs]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- fits
    intro r hr
    rw [hcr] at hr
    rcases List.mem_append.1 hr with hr | hr
    · refine hfit r ?_
      simpa only [Footprint.data, hGo, List.append_nil] using hr
    · exact hok.fits r (List.mem_append_right _ hr)
  · -- writable
    intro r hr a hm
    obtain ⟨⟨q, hq, hqm⟩, hout⟩ := hGw r hr a hm
    rw [hmem, hpk, unmap_check_out hout]
    exact hok.writable q hq a hqm
  · -- readable
    intro r hr a hm
    obtain ⟨hfr, hout⟩ := hGr r hr a hm
    rw [hmem, hpk, unmap_check_out hout]
    rcases hfr with ⟨q, hq, hqm⟩ | ⟨q, hq, hqm⟩
    · obtain ⟨h1, h2⟩ := hok.writable q hq a hqm
      exact ⟨h1, check_read_of_write h2⟩
    · exact hok.readable q hq a hqm
  · -- code
    intro c hc
    rw [hGc] at hc
    obtain ⟨hacc, hb⟩ := hok.code c hc
    have hcf : c.1.toNat + c.2.length ≤ 2 ^ 64 :=
      hok.fits ⟨c.1, c.2.length⟩ (List.mem_append_right _ (List.mem_map.2 ⟨c, hc, rfl⟩))
    refine ⟨fun a hm => ?_, ?_⟩
    · rw [hmem, hpk, unmap_check_out (hcode a ⟨_, List.mem_map.2 ⟨c, hc, rfl⟩, hm⟩)]
      exact hacc a hm
    · have e : readBytes Y.proc.mm.mem c.1 c.2.length = readBytes X.proc.mm.mem c.1 c.2.length := by
        unfold readBytes
        apply List.map_congr_left
        intro x hx
        rw [hmem]
        exact unmap_readByte_out (hcode x ⟨_, List.mem_map.2 ⟨c, hc, rfl⟩, mem_of_byteAddrs hcf hx⟩)
      unfold Bytes at hb ⊢
      rw [e]
      exact hb
  · -- notKernel
    intro a ha mp hm
    obtain ⟨m0, h0, hb, -⟩ := hbk a mp hm
    rw [hb]
    exact hok.notKernel a (hsub' a ha) m0 h0
  · -- noAlias
    intro a b ha hb hne ma mb hma hmb
    rw [hrsY, List.append_nil] at ha hb
    obtain ⟨a0, ha0, hba, ea⟩ := hbk a ma hma
    obtain ⟨b0, hb0, hbb, eb⟩ := hbk b mb hmb
    rw [hba, hbb, ea, eb]
    exact hok.noAlias a b (by rw [hrsX, List.append_nil]; exact hsub' a ha)
      (by rw [hrsX, List.append_nil]; exact hsub' b hb) hne a0 b0 ha0 hb0
  · -- notShared
    intro a ha mp hm fp
    simp only [hGo, List.append_nil] at ha
    obtain ⟨r, hr, hrm⟩ := ha
    obtain ⟨⟨q, hq, hqm⟩, -⟩ := hGw r hr a hrm
    obtain ⟨m0, h0, hb, -⟩ := hbk a mp hm
    rw [hb]
    exact hok.notShared a ⟨q, List.mem_append_left _ hq, hqm⟩ m0 h0 fp
  · -- notFixed
    rintro a ⟨r, hr, -⟩
    rw [hGo] at hr
    cases hr
  · -- codeApart
    intro r hr q hq a hra hqa
    rw [hcr] at hq
    obtain ⟨r', hr', hm'⟩ := hsub a ⟨r, hr, hra⟩
    exact hok.codeApart r' hr' q hq a hm' hqa
  · -- rseqApart
    intro r hr
    rw [hrsY] at hr
    cases hr

/-- `Ready` after the pages are unmapped, for a thread without an `rseq` area, the initial stack's first page not
among them. -/
theorem ready_unmap {feat : Features} {X Y : State} (hR : Ready feat X)
    (hmem : Y.proc.mm.mem = X.proc.mm.mem.unmap P n) (hbm : Y.proc.mm.brkMin = X.proc.mm.brkMin)
    (hbk : Y.proc.mm.brk = X.proc.mm.brk) (htf : Y.cpu.rflags.tf = false) (hac : Y.cpu.rflags.ac = false)
    (hth : Y.thread = X.thread) (hrs : X.thread.rseq = none)
    (hfx : X.proc.mm.mem.touchesFixed P n = false) : Ready feat Y := by
  obtain ⟨⟨-, -, h3, h4⟩, -, l1, l2, l3, l4, l5, l6, l7, l8⟩ := hR
  refine ⟨⟨htf, hac, by rw [hth]; exact h3, by rw [hth]; exact h4⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [RseqQuiet, hth, hrs]
  · intro g hg
    rw [hmem] at hg ⊢
    have hg' : g ∈ X.proc.mm.mem.growsDown := hg
    rw [unmap_out (gd_of_fixed hfx hg')]
    exact l1 g hg'
  · intro p mp hp
    rw [hmem] at hp ⊢
    exact l2 p mp (unmap_cases hp).2
  · rw [hbm]
    exact l3
  · rw [hbm, hbk]
    exact l4
  · intro p mp hp
    rw [hmem] at hp
    exact l5 p mp (unmap_cases hp).2
  · intro p mp hp
    rw [hmem] at hp
    exact l6 p mp (unmap_cases hp).2
  · rw [hbk]
    exact l7
  · intro p mp hp
    rw [hmem] at hp ⊢
    exact l8 p mp (unmap_cases hp).2

/-- The footprint's bytes after are those before, outside the pages. -/
theorem agree_unmap {X Y : State} {F G : Footprint} {V : Addr → Byte}
    (hmem : Y.proc.mm.mem = X.proc.mm.mem.unmap P n)
    (hsub : ∀ a, Foot G.data a → Foot F.data a ∧ inPages P n (pageOf a) = false)
    (hA : Agree F X.proc.mm.mem V) : Agree G Y.proc.mm.mem V := by
  intro a ha
  obtain ⟨h1, h2⟩ := hsub a ha
  rw [hmem, unmap_readByte_out h2, hA a h1]

end FV7z.Start

namespace FV7z.Fn.Seg
open ZellicX86 Decode FV7z.Leaf FV7z.Start FV7z.Write

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle} {F : Footprint} {Wl : List Rgn}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop} {X : State} {t j : Nat}
  {e' : Addr} {code : List Byte} {V : Addr → Byte}

/-- `syscall` for `munmap (rdi, rsi)`, no page of the range special or the initial stack's first page. With an error
or nothing mapped there the run goes on in the same `Fn.Seg`, `rax` the answer (`k'`). With the pages unmapped, `rax`
0, it goes on from the state after, `Y`, as a new start, with a footprint `G` whose bytes are bytes of `F` outside the
pages, its code `F`'s, outside the pages (`k₁`). `rcx` and `r11` as `syscall` sets them. -/
theorem s_munmap (c : Seg prof F Wl L s₀ o) (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V)
    (hin : CodeIn L e' code) (hj : j < code.length) (hrip : X.cpu.rip = e'.add j) {len : Nat}
    (hd : Dec prof.feat code j (FV7z.mk .syscall 32 [] len)) (hnr : X.cpu.gpr.rax.toNat % 2 ^ 32 = 11)
    (hfx : X.proc.mm.mem.touchesFixed (munFirst X) (munN X) = false) (hrs : s₀.thread.rseq = none)
    {G : Footprint} {Wl' : List Rgn} (hGo : G.own = []) (hGc : G.code = F.code)
    (hfit : ∀ r ∈ G.writes ++ G.reads, r.Fits)
    (hGw : ∀ r ∈ G.writes, ∀ a, r.Mem a → Foot F.writes a ∧ inPages (munFirst X) (munN X) (pageOf a) = false)
    (hGr : ∀ r ∈ G.reads, ∀ a, r.Mem a → (Foot F.writes a ∨ Foot F.reads a) ∧
      inPages (munFirst X) (munN X) (pageOf a) = false)
    (hcode : ∀ a, Foot F.codeRgns a → inPages (munFirst X) (munN X) (pageOf a) = false)
    (hww : ∀ y, Foot Wl' y → ∃ q ∈ G.writes, q.Mem y)
    (k' : ∀ r : BitVec 64, WrErr r ∨ r = 0 →
      ContG prof F Wl L s₀ o (gev ++ [tcEv X.cpu.gpr r []]) gP gE V
        fun Y => Y.cpu.rip = e'.add (j + len) ∧ Y.cpu.gpr = (sysGpr X len).set 0 r)
    (k₁ : ∀ (Y : State) (t' : Nat), Seg prof G Wl' L Y o → Agree G Y.proc.mm.mem V →
      Y.cpu.rip = e'.add (j + len) → Y.cpu.gpr = (sysGpr X len).set 0 0 → Y.cpu.seg = X.cpu.seg →
      GoG prof L o (gev ++ [tcEv X.cpu.gpr 0 []]) gP gE Y t') :
    GoG prof L o gev gP gE X t :=
  c.stepE hK hin hj hrip fun M hM hK' htf hac => by
    have hA' : Agree F (X.withMem M).proc.mm.mem V := c.agreeK hK hA hM
    have hfx' : M.touchesFixed (munFirst X) (munN X) = false :=
      (touchesFixed_congr hM.map hM.growsDown).trans hfx
    refine syscall_munmap (s := X.withMem M) (o := o) (t := t + 1)
      (P := fun res => ∃ Y t' ev, res = (.running Y ev, t') ∧ GoG prof L o (gev ++ ev.toList) gP gE Y t')
      htf (c.dec hK' hin hrip hd) hnr hfx' ?_ ?_ ?_
    · intro r t' he
      exact ⟨_, _, _, rfl, k' r (.inl he) _ _ (hK'.nx rfl rfl rfl) hA' ⟨rip_add hrip M len, rfl⟩⟩
    · intro t'
      exact ⟨_, _, _, rfl, k' 0 (.inr rfl) _ _ (hK'.nx rfl rfl rfl) hA' ⟨rip_add hrip M len, rfl⟩⟩
    · intro t'
      have hokX := c.foot.keptW c.ready.rseq c.hws hK' c.sub_self
      have hRX := c.ready.keptW c.foot c.hws hK'
      have hrsX : (X.withMem M).thread.rseq = none := by rw [hK'.thread]; exact hrs
      refine ⟨_, _, _, rfl, k₁ _ _ ?_ ?_ (rip_add hrip M len) rfl rfl⟩
      · exact
          { foot := footOk_unmap hokX rfl rfl hrsX hrsX c.own hGo hGc hfit hGw hGr hcode
            ready := ready_unmap hRX rfl rfl rfl htf hac rfl hrsX hfx'
            env := c.env
            code := hGc.trans c.code
            own := hGo
            hww := hww }
      · exact agree_unmap rfl (unmap_sub c.own hGo hGw hGr) hA'

end FV7z.Fn.Seg
