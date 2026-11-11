import FV7z.Start.Pages
import FV7z.Start.Stack
/-!
# The stack's pages at the first instruction of `7zzs` (PLAN.md G3, startup)

- `find_stack`: in `vsyscall ++ (stack :: segs ++ post)`, a page of the stack's region that no region of `segs` or
  `post` has is found in the stack's region.
- `launch_stack`: at the first instruction of `7zzs`, launched with room for `n` bytes of stack (`StackRoom`), the
  addresses from `rsp - n` to the stack's end (above `rsp`, at most `2 ^ 47`) are in pages mapped readable and
  writable: the stack's region is over them (`stack_room`), the segments of `7zzs` end at `0x7a9000`, far below, and
  the vDSO is apart from the stack (`ExecChoice.VdsoPlace.stack`).
-/
namespace FV7z.Start
open ZellicX86

theorem find_stack {vs post segs : List Region} {stack : Region} {P : Nat}
    (hpost : ∀ q ∈ post, q.has P = false) (hsegs : ∀ q ∈ segs, q.has P = false) (hs : stack.has P = true) :
    (vs ++ (stack :: segs ++ post)).reverse.find? (·.has P) = some stack := by
  have hp : post.reverse.find? (·.has P) = none := by
    rw [List.find?_eq_none]
    intro q hq
    simpa using hpost q (List.mem_reverse.1 hq)
  have hg : segs.reverse.find? (·.has P) = none := by
    rw [List.find?_eq_none]
    intro q hq
    simpa using hsegs q (List.mem_reverse.1 hq)
  simp only [List.reverse_append, List.reverse_cons, List.find?_append, List.append_assoc, hp, hg, Option.none_or,
    List.find?_cons, hs, Option.some_or]

theorem launch_stack {l : Launch} {n : Nat} (h : Launch.Of V2606.zzs.blob.bytes V2606.zzs.blob.size l)
    (hroom : StackRoom l.args n) :
    ∃ top, l.s₀.cpu.gpr.rsp.toNat < top ∧ top ≤ 2 ^ 47 ∧
      ∀ x : Addr, l.s₀.cpu.gpr.rsp.toNat ≤ x.toNat + n → x.toNat < top →
        ∃ mp, l.s₀.proc.mm.mem.map (pageOf x) = some mp ∧ mp.prot.read = true ∧ mp.prot.write = true ∧
          mp.pkey = 0 ∧ ∃ f, l.s₀.proc.mm.mem.backings mp.backing = .priv f := by
  obtain ⟨hf, hx, -⟩ := h
  obtain ⟨hdr, phs, c, segs, stack, post, gd, hr, hv, hc, hl, hm, hpost, hs1, hs2, hs3, hs4, hs5⟩ :=
    ExecStart.start hx
  obtain ⟨-, rfl⟩ := readElf_zzs hf hr
  obtain rfl := zzs_segs hl
  obtain ⟨h16, hn, hst, hpg, hlt, hlo, htop⟩ :=
    stack_room (lb := l.prof.linux) hv.stackTop hv.stackAlign (ExecStart.limits hx) hroom
  have e : l.s₀.cpu.gpr.rsp = BitVec.ofNat 64 (stackLayout l.args l.prof.linux c).sp := by rw [hc]; rfl
  have hlt' : (stackLayout l.args l.prof.linux c).sp < 2 ^ 64 := by omega
  have er : l.s₀.cpu.gpr.rsp.toNat = (stackLayout l.args l.prof.linux c).sp := by
    rw [e, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt']
  have hT := hv.stackTop.1
  refine ⟨c.stackTop, by omega, htop, ?_⟩
  intro x hx1 hx2
  have hP : (pageOf x).toNat = x.toNat / 4096 := by
    have := x.isLt
    simp only [pageOf, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
    omega
  have hfind := find_stack (vs := vsyscallRegions l.prof.linux.vsyscall) (post := post)
    (segs := [segFile l.files l.exe ph0, segFile l.files l.exe ph1, segFile l.files l.exe ph2,
      segFile l.files l.exe ph3, segAnon ph3]) (stack := stack) (P := (pageOf x).toNat)
    (by
      intro q hq
      obtain ⟨hvd, hq'⟩ := hpost q hq
      have vp := hv.vdso hvd
      have hs := vp.stack
      have hal := vp.aligned
      rw [← Bool.not_eq_true, has_iff]
      simp only [ExecChoice.vdsoEnd, ExecChoice.vdsoText] at hs hq'
      rcases hq' with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega)
    (by
      intro q hq
      obtain ⟨⟨a0, b0⟩, ⟨a1, b1⟩, ⟨a2, b2⟩, ⟨a3, b3⟩, a4, b4⟩ := seg_pages l.files l.exe
      rw [← Bool.not_eq_true, has_iff]
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl <;> omega)
    (by rw [has_iff, hs1, hs2]; omega)
  refine ⟨⟨stack.prot, (pageOf x).toNat, 0, stack.special, stack.origin ((pageOf x).toNat - stack.first),
    (pageOf x).toNat, stack.maxProt, stack.growsDown⟩, ?_, hs3, hs4, rfl, ?_⟩
  · rw [hm]
    simp only [regionsMemory, hfind, Option.map_some]
  · rw [hm]
    simp only [regionsMemory, hfind]
    exact ⟨_, hs5 _⟩

/-- At the first instruction of `7zzs`, launched with room for `n` bytes of stack, for one choice of the kernel: a
byte from `rsp - n` to the stack's end is what `execve` wrote there (`stackRuns`: the words from `rsp`, `AT_RANDOM`'s
bytes and the platform string, the argument and environment strings), 0 elsewhere; and every page of the stack's
mapping (from `StackLayout.start`, at or below `rsp - n`) is mapped readable and writable, with key 0, on private
memory. -/
theorem launch_stack_at {l : Launch} {n : Nat} (h : Launch.Of V2606.zzs.blob.bytes V2606.zzs.blob.size l)
    (hroom : StackRoom l.args n) :
    ∃ hdr c, readElf l.files l.exe = some (hdr, zzsPhdrs) ∧ c.Valid l.prof.linux zzsPhdrs l.args l.kcfg ∧
      l.s₀.cpu.gpr.rsp.toNat = (stackLayout l.args l.prof.linux c).sp ∧
      (stackLayout l.args l.prof.linux c).sp < c.stackTop ∧ c.stackTop ≤ 2 ^ 47 ∧
      (∀ x : Addr, (stackLayout l.args l.prof.linux c).sp ≤ x.toNat + n → x.toNat < c.stackTop →
        l.s₀.proc.mm.mem.readByte x = runsByte (stackRuns l.prof hdr zzsPhdrs l.args c) x.toNat) ∧
      ∀ x : Addr, (stackLayout l.args l.prof.linux c).start ≤ x.toNat → x.toNat < c.stackTop →
        ∃ mp, l.s₀.proc.mm.mem.map (pageOf x) = some mp ∧ mp.prot.read = true ∧ mp.prot.write = true ∧
          mp.pkey = 0 ∧ ∃ f, l.s₀.proc.mm.mem.backings mp.backing = .priv f := by
  obtain ⟨hf, hx, -⟩ := h
  obtain ⟨hdr, phs, c, segs, stack, post, gd, hr, hv, hc, hl, hm, hpost, hs1, hs2, hs3, hs4, hs5⟩ :=
    ExecStart.start hx
  obtain ⟨-, rfl⟩ := readElf_zzs hf hr
  obtain rfl := zzs_segs hl
  obtain ⟨h16, hn, hst, hpg, hlt, hlo, htop⟩ :=
    stack_room (lb := l.prof.linux) hv.stackTop hv.stackAlign (ExecStart.limits hx) hroom
  have e : l.s₀.cpu.gpr.rsp = BitVec.ofNat 64 (stackLayout l.args l.prof.linux c).sp := by rw [hc]; rfl
  have hlt' : (stackLayout l.args l.prof.linux c).sp < 2 ^ 64 := by omega
  have er : l.s₀.cpu.gpr.rsp.toNat = (stackLayout l.args l.prof.linux c).sp := by
    rw [e, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt']
  have hT := hv.stackTop.1
  have hP : ∀ x : Addr, (pageOf x).toNat = x.toNat / 4096 := by
    intro x
    have := x.isLt
    simp only [pageOf, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
    omega
  have hfind : ∀ x : Addr, (stackLayout l.args l.prof.linux c).start ≤ x.toNat → x.toNat < c.stackTop →
      (vsyscallRegions l.prof.linux.vsyscall ++ (stack :: [segFile l.files l.exe ph0, segFile l.files l.exe ph1,
        segFile l.files l.exe ph2, segFile l.files l.exe ph3, segAnon ph3] ++ post)).reverse.find?
          (·.has (pageOf x).toNat) = some stack := by
    intro x hx1 hx2
    have hPx := hP x
    exact find_stack
      (by
        intro q hq
        obtain ⟨hvd, hq'⟩ := hpost q hq
        have vp := hv.vdso hvd
        have hs := vp.stack
        have hal := vp.aligned
        rw [← Bool.not_eq_true, has_iff]
        simp only [ExecChoice.vdsoEnd, ExecChoice.vdsoText] at hs hq'
        rcases hq' with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega)
      (by
        intro q hq
        obtain ⟨⟨a0, b0⟩, ⟨a1, b1⟩, ⟨a2, b2⟩, ⟨a3, b3⟩, a4, b4⟩ := seg_pages l.files l.exe
        rw [← Bool.not_eq_true, has_iff]
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
        rcases hq with rfl | rfl | rfl | rfl | rfl <;> omega)
      (by rw [has_iff, hs1, hs2]; omega)
  refine ⟨hdr, c, hr, hv, er, hlt, htop, ?_, ?_⟩
  · intro x hx1 hx2
    have hPx := hP x
    have hO : (pageOffset x).toNat = x.toNat % 4096 := by
      simp only [pageOffset, BitVec.extractLsb'_toNat, Nat.shiftRight_zero]
    rw [hm, regionsMemory_readByte (hfind x (by omega) hx2), hs5, hs1]
    simp only [Backing.frame]
    congr 1
    omega
  · intro x hx1 hx2
    have hfx := hfind x hx1 hx2
    refine ⟨⟨stack.prot, (pageOf x).toNat, 0, stack.special, stack.origin ((pageOf x).toNat - stack.first),
      (pageOf x).toNat, stack.maxProt, stack.growsDown⟩, ?_, hs3, hs4, rfl, ?_⟩
    · rw [hm]
      simp only [regionsMemory, hfx, Option.map_some]
    · rw [hm]
      simp only [regionsMemory, hfx]
      exact ⟨_, hs5 _⟩

/-- `launch_stack_at`'s bytes. -/
theorem launch_stack_byte {l : Launch} {n : Nat} (h : Launch.Of V2606.zzs.blob.bytes V2606.zzs.blob.size l)
    (hroom : StackRoom l.args n) :
    ∃ hdr c, readElf l.files l.exe = some (hdr, zzsPhdrs) ∧ c.Valid l.prof.linux zzsPhdrs l.args l.kcfg ∧
      l.s₀.cpu.gpr.rsp.toNat = (stackLayout l.args l.prof.linux c).sp ∧
      (stackLayout l.args l.prof.linux c).sp < c.stackTop ∧ c.stackTop ≤ 2 ^ 47 ∧
      ∀ x : Addr, (stackLayout l.args l.prof.linux c).sp ≤ x.toNat + n → x.toNat < c.stackTop →
        l.s₀.proc.mm.mem.readByte x = runsByte (stackRuns l.prof hdr zzsPhdrs l.args c) x.toNat := by
  obtain ⟨hdr, c, hr, hv, er, hlt, htop, hall, -⟩ := launch_stack_at h hroom
  exact ⟨hdr, c, hr, hv, er, hlt, htop, hall⟩

/-- The two low bits of `PKRU` clear: key 0 forbids nothing. -/
theorem pkru_low {v : BitVec 32} (h : v &&& 3 = 0) : v.getLsbD 0 = false ∧ v.getLsbD 1 = false := by
  have h0 : (v &&& 3).getLsbD 0 = false := by rw [h]; rfl
  have h1 : (v &&& 3).getLsbD 1 = false := by rw [h]; rfl
  have e0 : (3 : BitVec 32).getLsbD 0 = true := by decide
  have e1 : (3 : BitVec 32).getLsbD 1 = true := by decide
  rw [BitVec.getLsbD_and, e0, Bool.and_true] at h0
  rw [BitVec.getLsbD_and, e1, Bool.and_true] at h1
  exact ⟨h0, h1⟩

/-- An address below `2 ^ 47` is canonical. -/
theorem canonical_low {x : Addr} (h : x.toNat < 2 ^ 47) (b : Bool) : x.canonical b = true := by
  have e1 : x >>> 47 = 0 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
    show _ = 0
    omega
  have e2 : x >>> 56 = 0 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
    show _ = 0
    omega
  cases b <;> simp [Addr.canonical, e1, e2]

/-- A mapped page with key 0 and private memory can be read if readable and written if writable, when `PKRU`'s two
low bits are clear. -/
theorem check_priv {feat : Features} {pkru : BitVec 32} {mem : Memory} {x : Addr} {mp : Mapping} {f : Frame}
    (hm : mem.map (pageOf x) = some mp) (hk : mp.pkey = 0) (hb : mem.backings mp.backing = .priv f)
    (hp : pkru &&& 3 = 0) :
    (mp.prot.read = true → mem.check feat pkru .read x = none) ∧
      (mp.prot.write = true → mem.check feat pkru .write x = none) := by
  obtain ⟨p0, p1⟩ := pkru_low hp
  constructor <;> intro hpr
  · simp [Memory.check, Memory.check.rest, hm, hb, Backing.filePage, Backing.noSource, hk, pkeyDenies,
      Mapping.allows, hpr]
    intro _
    simpa using p0
  · simp [Memory.check, Memory.check.rest, hm, hb, Backing.filePage, Backing.noSource, hk, pkeyDenies,
      Mapping.allows, hpr]
    intro _
    exact ⟨by simpa using p0, by simpa using p1⟩

/-- At the first instruction of `7zzs`, launched with room for `n` bytes of stack: the addresses from `rsp - n` to
the stack's end are canonical and can be read and written (Zellic's `Accessible`, byte by byte). -/
theorem launch_stack_rw {l : Launch} {n : Nat} (h : Launch.Of V2606.zzs.blob.bytes V2606.zzs.blob.size l)
    (hroom : StackRoom l.args n) :
    ∃ top, l.s₀.cpu.gpr.rsp.toNat < top ∧ top ≤ 2 ^ 47 ∧
      ∀ x : Addr, l.s₀.cpu.gpr.rsp.toNat ≤ x.toNat + n → x.toNat < top →
        x.canonical l.prof.feat.la57 = true ∧
        l.s₀.proc.mm.mem.check l.prof.feat l.s₀.cpu.pkru .read x = none ∧
        l.s₀.proc.mm.mem.check l.prof.feat l.s₀.cpu.pkru .write x = none := by
  obtain ⟨top, h1, h2, hall⟩ := launch_stack h hroom
  obtain ⟨-, hx, -⟩ := h
  have hk : l.kcfg.initPkru &&& 3 = 0 := hx.1
  obtain ⟨hdr, phs, c, -, -, hc⟩ := ExecStart.cpu hx
  have ep : l.s₀.cpu.pkru = l.kcfg.initPkru := by rw [hc]; rfl
  refine ⟨top, h1, h2, ?_⟩
  intro x hx1 hx2
  obtain ⟨mp, hm, hr, hw, hkey, f, hb⟩ := hall x hx1 hx2
  obtain ⟨cr, cw⟩ := check_priv (feat := l.prof.feat) hm hkey hb (ep ▸ hk)
  exact ⟨canonical_low (by omega) _, cr hr, cw hw⟩

end FV7z.Start
