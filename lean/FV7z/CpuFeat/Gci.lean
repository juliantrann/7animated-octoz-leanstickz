import FV7z.CpuFeat.Inv
import FV7z.CpuFeat.Decode
import FV7z.Lemmas.FnMem
import FV7z.Lemmas.CallFn
import FV7z.Prepare.AesGen
/-!
# `get_common_indices` keeps `CpuOk` (PLAN.md G2, "Dispatch theo CPUID", glibc `init_cpu_features`)

`get_common_indices (cpu_features, family, model, extended_model, stepping)` (glibc 2.31
`sysdeps/x86/cpu-features.c`, inlined `update_usable`; at `0x612cc0` in `7zzs` 26.06, `cpu_features` folded into
`_dl_x86_cpu_features`): with `family` not `NULL`, `CPUID` leaf 1 into `cpuid[1]` and the four pointers; leaf 7 and leaf
`0DH` subleaf 1 if the maximum leaf allows; then, if `OSXSAVE`, the `*_Usable` bits from `XGETBV` and the `CPUID` words,
and the `XSAVE` state size, from leaf `0DH` and a loop over its subleaves 2 to 31 in a 30-word stack array.

The contract: a stack of 256 bytes (`rbx`, 136 bytes of frame, the 112-byte red zone of the array), the words of
`_dl_x86_cpu_features` to `xsave_state_size` (`cfR`) and, with `family` not `NULL`, the four 4-byte outputs written;
`CpuOk` at the call and at the return. Each store keeps `CInv` (`Inv.lean`): a `CPUID` word some CPU answered, or a
`feature` bit whose condition the branches before it checked.
-/
namespace FV7z.CpuFeat
open ZellicX86 Decode FV7z.Leaf FV7z.Fn FV7z.Prepare Glibc

set_option linter.deprecated false

/-- `_dl_x86_cpu_features` up to `xsave_state_size_full`: `[0x7a4ae0, 0x7a4b70)`. -/
def cfR : Rgn := ⟨0x7a4ae0, 0x90⟩

/-- `family`, `model`, `extended_model`, `stepping`. -/
def gPtrs (s : State) : List Rgn :=
  [⟨s.cpu.gpr.rdi, 4⟩, ⟨s.cpu.gpr.rsi, 4⟩, ⟨s.cpu.gpr.rdx, 4⟩, ⟨s.cpu.gpr.rcx, 4⟩]

/-- What it writes besides its stack: `cfR`, and the four outputs if `family` is not `NULL`. -/
def gW (s : State) : List Rgn := cfR :: if s.cpu.gpr.rdi = 0 then [] else gPtrs s

/-- It reads nothing else. -/
def gR (_ : State) : List Rgn := []

/-- An output apart from `cpuRgn` and from the saved `rbx` and the return address. -/
def PtrOk (s : State) (q : Addr) : Prop :=
  (q.toNat + 4 ≤ 0x7a4ae0 ∨ 0x7a4b48 ≤ q.toNat) ∧
  (q.toNat + 4 ≤ s.cpu.gpr.rsp.toNat - 8 ∨ s.cpu.gpr.rsp.toNat + 8 ≤ q.toNat)

/-- `CpuOk`; the stack apart from `cfR`; the outputs, if any, apart. -/
def gPre (prof : Profile) (s : State) : Prop :=
  CpuOk prof s.proc.mm.mem ∧
  (0x7a4b70 + 256 ≤ s.cpu.gpr.rsp.toNat ∨ s.cpu.gpr.rsp.toNat + 8 ≤ 0x7a4ae0) ∧
  (s.cpu.gpr.rdi ≠ 0 → PtrOk s s.cpu.gpr.rdi ∧ PtrOk s s.cpu.gpr.rsi ∧ PtrOk s s.cpu.gpr.rdx ∧
    PtrOk s s.cpu.gpr.rcx)

/-- `CpuOk` at the return, and what the run kept (`fnK`: for a caller's run to go on). -/
def gPost (prof : Profile) (s₀ Y : State) : Prop := CpuOk prof Y.proc.mm.mem ∧ KeptW (ws 256 gW s₀) s₀ Y

/-- The contract of `get_common_indices`. -/
abbrev gciC (prof : Profile) : Contract := fn 256 gW gR (gPre prof) (gPost prof)

/-! ## Invariants -/

/-- The call's `rsp` is `p + 256`; the stack `[p, p + 264)` apart from `cfR`. -/
structure GEnv (s₀ : State) (p : Addr) : Prop where
  lo : s₀.cpu.gpr.rsp - BitVec.ofNat 64 256 = p
  sp : s₀.cpu.gpr.rsp = p.add 256
  fit : p.toNat + 264 ≤ 2 ^ 64
  apart : 0x7a4b70 ≤ p.toNat ∨ p.toNat + 264 ≤ 0x7a4ae0

/-- The registers kept: `rsp` below the frame, the callee-saved ones but `rbx`. -/
structure GB (s₀ : State) (p : Addr) (g : Gprs) : Prop where
  sp : g.rsp = p.add 112
  rbp : g.rbp = s₀.cpu.gpr.rbp
  r12 : g.r12 = s₀.cpu.gpr.r12
  r13 : g.r13 = s₀.cpu.gpr.r13
  r14 : g.r14 = s₀.cpu.gpr.r14
  r15 : g.r15 = s₀.cpu.gpr.r15

@[simp] theorem get_r10 (g : Gprs) : g.get (regOf 10) = g.r10 := rfl
@[simp] theorem set_r10 (g : Gprs) (v : BitVec 64) : g.set (regOf 10) v = { g with r10 := v } := rfl

/-- `GB` after a write to a register other than `rsp`, `rbp`, `r12`–`r15`. -/
theorem GB.set {s₀ : State} {p : Addr} {g : Gprs} (h : GB s₀ p g) {r : Nat}
    (hr : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 6 ∨ r = 7 ∨ r = 8 ∨ r = 9 ∨ r = 10) (v : BitVec 64) :
    GB s₀ p (g.set (regOf r) v) := by
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact ⟨h.sp, h.rbp, h.r12, h.r13, h.r14, h.r15⟩

theorem GB.cpuid {s₀ : State} {p : Addr} {g : Gprs} (h : GB s₀ p g) (a b c d : BitVec 64) :
    GB s₀ p ((((g.set 0 a).set 3 b).set 1 c).set 2 d) := ⟨h.sp, h.rbp, h.r12, h.r13, h.r14, h.r15⟩

/-- The footprint's bytes: `CInv`, and the call's `rbx` in its slot. -/
def GM (prof : Profile) (s₀ : State) (p : Addr) (V : Addr → Byte) : Prop :=
  CInv prof V ∧ ofBytesLE 64 ((byteAddrs (p.add 248) 8).map V) = s₀.cpu.gpr.rbx

variable {prof : Profile}

theorem GEnv.tn {s₀ : State} {p : Addr} (hE : GEnv s₀ p) {n : Nat} (h : n < 264) : (p.add n).toNat = p.toNat + n :=
  toNat_addn h hE.fit

/-- A store into the stack below the saved `rbx`. -/
theorem GM.stk {s₀ : State} {p : Addr} {V : Addr → Byte} (h : GM prof s₀ p V) (hE : GEnv s₀ p) {n m w : Nat}
    (v : BitVec w) (hn : n + m ≤ 248) : GM prof s₀ p (Vst V (p.add n) (toBytesLE v m)) := by
  have e := hE.tn (n := n) (by omega)
  have e2 := hE.tn (n := 248) (by omega)
  have hf := hE.fit
  have ha := hE.apart
  refine ⟨h.1.st_apart _ _ (by rw [toBytesLE_length, e]; omega) fun a hw => ?_, ?_⟩
  · rw [toBytesLE_length, e]
    rcases hw with rfl | rfl | rfl | rfl | rfl | rfl <;> omega
  · rw [rd_apart v (by rw [e]; omega) (by rw [e2]; omega) (by rw [e, e2]; omega)]; exact h.2

/-- A store into `cfR` that keeps `CInv`. -/
theorem GM.cf {s₀ : State} {p : Addr} {V : Addr → Byte} (h : GM prof s₀ p V) (hE : GEnv s₀ p) {g : Addr}
    {bs : List Byte} (hc : CInv prof (Vst V g bs)) (hg : 0x7a4ae0 ≤ g.toNat) (hb : g.toNat + bs.length ≤ 0x7a4b70) :
    GM prof s₀ p (Vst V g bs) := by
  have e2 := hE.tn (n := 248) (by omega)
  have hf := hE.fit
  have ha := hE.apart
  exact ⟨hc, by rw [map_Vst_apart (by omega) (by rw [e2]; omega) (by rw [e2]; omega)]; exact h.2⟩

/-- A store into an output. -/
theorem GM.ptr {s₀ : State} {p : Addr} {V : Addr → Byte} (h : GM prof s₀ p V) (hE : GEnv s₀ p) {q : Addr}
    (hp : PtrOk s₀ q) (hq : q.toNat + 4 ≤ 2 ^ 64) (v : BitVec 32) : GM prof s₀ p (Vst V q (toBytesLE v 4)) := by
  have e2 := hE.tn (n := 248) (by omega)
  have hs : s₀.cpu.gpr.rsp.toNat = p.toNat + 256 := by rw [hE.sp]; exact hE.tn (by omega)
  obtain ⟨h1, h2⟩ := hp
  rw [hs] at h2
  refine ⟨h.1.st_apart _ _ (by rw [toBytesLE_length]; omega) fun a hw => ?_, ?_⟩
  · rw [toBytesLE_length]
    rcases hw with rfl | rfl | rfl | rfl | rfl | rfl <;> omega
  · rw [rd_apart v hq (by rw [e2]; have := hE.fit; omega) (by rw [e2]; omega)]; exact h.2

/-- A store into `cfR` apart from the watched words. -/
theorem GM.cfu {s₀ : State} {p : Addr} {V : Addr → Byte} (h : GM prof s₀ p V) (hE : GEnv s₀ p) {n m w : Nat}
    (v : BitVec w) (hn : 104 ≤ n) (hm : n + m ≤ 0x90) :
    GM prof s₀ p (Vst V (cpuRgn.base.add n) (toBytesLE v m)) := by
  have e : (cpuRgn.base.add n).toNat = 0x7a4ae0 + n := by rw [cpuRgn_base, CpuFeat.tn (by rw [base_toNat]; omega), base_toNat]
  refine h.cf hE (h.1.st_apart _ _ (by rw [toBytesLE_length, e]; omega) fun a hw => ?_)
    (by rw [e]; omega) (by rw [toBytesLE_length, e]; omega)
  rw [toBytesLE_length, e]
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl <;> omega

variable {L : List (Addr × List Byte)} {s₀ : State} {ra : Addr} {o : Oracle}

/-- The frame's bytes are the run's to store into. -/
theorem gS {p : Addr} (hE : GEnv s₀ p) {n : Nat} (h : n < 256) : Foot (ws 256 gW s₀) (p.add n) :=
  ⟨below s₀ 256, by simp, by simp only [below, hE.lo]; exact mem_add_of_fits h (by have := hE.fit; omega)⟩

/-- So are `cfR`'s. -/
theorem gC {a i : Nat} (h : a + i < 0x90) : Foot (ws 256 gW s₀) ((cpuRgn.base.add a).add i) := by
  rw [addr_add_add]
  exact ⟨cfR, by simp [gW], mem_add_of_fits h (by decide)⟩

theorem gS4 {p : Addr} (hE : GEnv s₀ p) {n : Nat} (h : n + 4 ≤ 256) :
    ∀ i < 4, Foot (ws 256 gW s₀) ((p.add n).add i) := fun i hi => by
  rw [addr_add_add]; exact gS hE (by omega)

theorem eaD_p {X : State} {b d n : Nat} {p : Addr} (h : X.cpu.gpr.get (regOf b) = p.add n) :
    eaD X b d = p.add (n + d) := by
  simp only [eaD, h]; exact add_addn p n d

theorem add_neg (a : Addr) (n k d : Nat) (hd : k + d = 2 ^ 64) : a.add (n + k) + BitVec.ofNat 64 d = a.add n := by
  rw [← addr_add_add]
  show a.add n + BitVec.ofNat 64 k + BitVec.ofNat 64 d = a.add n
  rw [BitVec.add_assoc, show BitVec.ofNat 64 k + BitVec.ofNat 64 d = 0#64 from by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; rw [Nat.add_mod_mod,
      Nat.mod_add_mod, hd], BitVec.add_zero]

/-- `CpuOk` of memory agreeing with `V` on `cpuRgn`. -/
theorem gPost_of (c : Call prof 256 gW gR (gPre prof) (gPost prof) 0x612cc0 L s₀ ra o) {V : Addr → Byte}
    (hm : CInv prof V) {M : Memory} (hA : Agree (fp 256 gW gR (gPre prof) (gPost prof) L s₀) M V) :
    CpuOk prof M :=
  hm.mem fun j hj => hA _ (c.hws _ (by have := gC (s₀ := s₀) (a := j) (i := 0) (by omega); rwa [addr_add_zero] at this))

/-! ## The return -/

theorem gTail (c : Call prof 256 gW gR (gPre prof) (gPost prof) 0x612cc0 L s₀ ra o) (hin : CodeIn L 0x612cc0 gci)
    {p : Addr} (hE : GEnv s₀ p) {X : State} {t : Nat} {V : Addr → Byte}
    (hK : KeptW (ws 256 gW s₀) s₀ X) (hA : Agree (fp 256 gW gR (gPre prof) (gPost prof) L s₀) X.proc.mm.mem V)
    (hr : X.cpu.rip = (0x612cc0 : Addr).add 452) (hb : GB s₀ p X.cpu.gpr) (hm : GM prof s₀ p V) :
    Go prof 256 gW gR (gPre prof) (gPost prof) L s₀ ra o X t := by
  have hl : gci.length = 896 := gci_length
  refine c.s_add_ri64 hK hA hin (by omega) hr (gci_452 _) ?_
  rintro Y1 t1 hK1 hA1 ⟨hr1, hg1⟩
  have hsp1 : Y1.cpu.gpr.rsp = p.add 248 := by rw [hg1, set_r4, get_r4, hb.sp, add_addn]
  refine c.s_pop hK1 hA1 hin (by omega) hr1 (gci_459 _)
    (fun i hi => by rw [hsp1, addr_add_add]; exact c.hws _ (gS hE (by omega))) ?_
  rintro Y2 t2 hK2 hA2 ⟨hr2, hg2⟩
  refine c.ret hK2 (callee_of ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ ?_) hin (by omega) hr2 (gci_460 _) fun M hM => ?_
  · rw [hg2, set_r3, hsp1]; exact hm.2
  · simp only [hg2, hg1, set_r3, set_4, set_r4]; exact hb.rbp
  · simp only [hg2, hg1, set_r3, set_4, set_r4]; exact hb.r12
  · simp only [hg2, hg1, set_r3, set_4, set_r4]; exact hb.r13
  · simp only [hg2, hg1, set_r3, set_4, set_r4]; exact hb.r14
  · simp only [hg2, hg1, set_r3, set_4, set_r4]; exact hb.r15
  · rw [hg2, set_r3]; simp only [set_4]; rw [hsp1, add_add8, hE.sp]
  · exact ⟨gPost_of c hm.1 (c.agreeK hK2 hA2 hM), (hK2.withMem hM).upd rfl rfl rfl⟩

/-! ## The loop over leaf `0DH`'s subleaves 2 to 31 -/

/-- At the loop's test (`bt r9d, esi`, `387`), subleaf `n + 2`: `rdi` and `r8` at its words of the two arrays. -/
structure LS (s₀ : State) (p : Addr) (n : Nat) (g : Gprs) : Prop where
  b : GB s₀ p g
  rsi : g.rsi = (BitVec.ofNat 32 (n + 2)).setWidth 64
  rdi : g.rdi = p.add (128 + 4 * n)
  r8 : g.r8 = p.add (4 * n)

theorem LS.set {p : Addr} {n : Nat} {g : Gprs} (h : LS s₀ p n g) {r : Nat}
    (hr : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 9 ∨ r = 10) (v : BitVec 64) : LS s₀ p n (g.set (regOf r) v) := by
  have hb := h.b.set (r := r) (by omega) v
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨hb, h.rsi, h.rdi, h.r8⟩

theorem LS.cpuid {p : Addr} {n : Nat} {g : Gprs} (h : LS s₀ p n g) (a b c d : BitVec 64) :
    LS s₀ p n ((((g.set 0 a).set 3 b).set 1 c).set 2 d) := ⟨h.b.cpuid a b c d, h.rsi, h.rdi, h.r8⟩

theorem rv_rsi {X : State} {n : Nat} (h : X.cpu.gpr.rsi = (BitVec.ofNat 32 n).setWidth 64) :
    rv X 32 6 = BitVec.ofNat 32 n := by
  simp only [rv, get_r6, h, sw_sw]

theorem ofNat32_eq {a b : Nat} (ha : a < 2 ^ 32) (hb : b < 2 ^ 32) :
    decide (BitVec.ofNat 32 a = BitVec.ofNat 32 b) = decide (a = b) := by
  apply decide_eq_decide.2
  constructor
  · intro h; have := congrArg BitVec.toNat h; simp only [BitVec.toNat_ofNat] at this; omega
  · intro h; rw [h]

theorem zf_cmp {f : Rflags} {X : State} {n k : Nat}
    (hf : f = subF (rf0 X) (rv X 32 6) (BitVec.ofNat 32 k)) (hs : X.cpu.gpr.rsi = (BitVec.ofNat 32 n).setWidth 64)
    (hn : n < 2 ^ 32) (hk : k < 2 ^ 32) : f.cond 4 = decide (n = k) := by
  rw [hf]; simp only [Rflags.cond, subF_zf, rv_rsi hs]; exact ofNat32_eq hn hk

theorem eaD_m4 {X : State} {b m : Nat} {p : Addr} (h : X.cpu.gpr.get (regOf b) = p.add (m + 4)) :
    eaD X b 18446744073709551612 = p.add m := by
  simp only [eaD, h]; exact add_neg p m 4 _ (by decide)

theorem gLoop (c : Call prof 256 gW gR (gPre prof) (gPost prof) 0x612cc0 L s₀ ra o) (hin : CodeIn L 0x612cc0 gci)
    {p : Addr} (hE : GEnv s₀ p)
    (next : ∀ (V : Addr → Byte) Y t, KeptW (ws 256 gW s₀) s₀ Y →
      Agree (fp 256 gW gR (gPre prof) (gPost prof) L s₀) Y.proc.mm.mem V → Y.cpu.rip = (0x612cc0 : Addr).add 416 →
      GB s₀ p Y.cpu.gpr → GM prof s₀ p V → Go prof 256 gW gR (gPre prof) (gPost prof) L s₀ ra o Y t) :
    ∀ m n, m + n = 29 → ∀ (V : Addr → Byte) X t, KeptW (ws 256 gW s₀) s₀ X →
      Agree (fp 256 gW gR (gPre prof) (gPost prof) L s₀) X.proc.mm.mem V → X.cpu.rip = (0x612cc0 : Addr).add 387 →
      LS s₀ p n X.cpu.gpr → GM prof s₀ p V → Go prof 256 gW gR (gPre prof) (gPost prof) L s₀ ra o X t := by
  have hl : gci.length = 896 := gci_length
  have body : ∀ n, n ≤ 29 → ∀ (V : Addr → Byte) X t, KeptW (ws 256 gW s₀) s₀ X →
      Agree (fp 256 gW gR (gPre prof) (gPost prof) L s₀) X.proc.mm.mem V → X.cpu.rip = (0x612cc0 : Addr).add 387 →
      LS s₀ p n X.cpu.gpr → GM prof s₀ p V →
      (n < 29 → ∀ (V : Addr → Byte) X t, KeptW (ws 256 gW s₀) s₀ X →
        Agree (fp 256 gW gR (gPre prof) (gPost prof) L s₀) X.proc.mm.mem V → X.cpu.rip = (0x612cc0 : Addr).add 387 →
        LS s₀ p (n + 1) X.cpu.gpr → GM prof s₀ p V → Go prof 256 gW gR (gPre prof) (gPost prof) L s₀ ra o X t) →
      Go prof 256 gW gR (gPre prof) (gPost prof) L s₀ ra o X t := by
    intro n hn V X t hK hA hr hs hm more
    -- `376`: the next subleaf
    have inc : ∀ (V : Addr → Byte) X t, KeptW (ws 256 gW s₀) s₀ X →
        Agree (fp 256 gW gR (gPre prof) (gPost prof) L s₀) X.proc.mm.mem V → X.cpu.rip = (0x612cc0 : Addr).add 376 →
        LS s₀ p n X.cpu.gpr → n < 29 → GM prof s₀ p V → Go prof 256 gW gR (gPre prof) (gPost prof) L s₀ ra o X t := by
      intro V X t hK hA hr hs hn' hm
      refine c.s_add_ri32 hK hA hin (by omega) hr (gci_376 _) ?_
      rintro Y1 t1 hK1 hA1 ⟨hr1, hg1⟩
      refine c.s_add_ri64 hK1 hA1 hin (by omega) hr1 (gci_379 _) ?_
      rintro Y2 t2 hK2 hA2 ⟨hr2, hg2⟩
      refine c.s_add_ri64 hK2 hA2 hin (by omega) hr2 (gci_383 _) ?_
      rintro Y3 t3 hK3 hA3 ⟨hr3, hg3⟩
      refine more hn' V Y3 t3 hK3 hA3 hr3 ⟨?_, ?_, ?_, ?_⟩ hm
      · rw [hg3, hg2, hg1]; exact ((hs.b.set (r := 6) (by omega) _).set (r := 8) (by omega) _).set (r := 7) (by omega) _
      · simp only [hg3, hg2, hg1, set_r7, Prepare.set_r8, set_r6]
        rw [rv_rsi hs.rsi]
        congr 1
        apply BitVec.eq_of_toNat_eq
        simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
        omega
      · simp only [hg3, hg2, hg1, set_r7, Prepare.set_r8, set_r6, get_r7, hs.rdi, add_addn]
        congr 1
      · simp only [hg3, hg2, hg1, set_r7, Prepare.set_r8, set_r6, get_r8, hs.r8, add_addn]
        congr 1
    -- `371`: the last subleaf?
    have chk : ∀ (V : Addr → Byte) X t, KeptW (ws 256 gW s₀) s₀ X →
        Agree (fp 256 gW gR (gPre prof) (gPost prof) L s₀) X.proc.mm.mem V → X.cpu.rip = (0x612cc0 : Addr).add 371 →
        LS s₀ p n X.cpu.gpr → GM prof s₀ p V → Go prof 256 gW gR (gPre prof) (gPost prof) L s₀ ra o X t := by
      intro V X t hK hA hr hs hm
      refine c.s_cmp_ri32 hK hA hin (by omega) hr (gci_371 _) ?_
      rintro Y1 t1 hK1 hA1 ⟨hr1, hg1, hf1⟩
      refine c.s_jcc hK1 hA1 hin (by omega) hr1 (gci_374 _) (tgt := 416) rfl (by omega) (fun _ => ?_) fun hc => ?_
      · rintro Y2 t2 hK2 hA2 ⟨hr2, hg2⟩
        exact next V Y2 t2 hK2 hA2 hr2 (by rw [hg2, hg1]; exact hs.b) hm
      · have h29 : n ≠ 29 := by
          rw [zf_cmp hf1 hs.rsi (by omega) (by decide)] at hc
          simpa using hc
        rintro Y2 t2 hK2 hA2 ⟨hr2, hg2⟩
        exact inc V Y2 t2 hK2 hA2 hr2 (by rw [hg2, hg1]; exact hs) (by omega) hm
    -- `368`: `mov [r8], eax`
    have j368 : ∀ (V : Addr → Byte) X t, KeptW (ws 256 gW s₀) s₀ X →
        Agree (fp 256 gW gR (gPre prof) (gPost prof) L s₀) X.proc.mm.mem V → X.cpu.rip = (0x612cc0 : Addr).add 368 →
        LS s₀ p n X.cpu.gpr → GM prof s₀ p V → Go prof 256 gW gR (gPre prof) (gPost prof) L s₀ ra o X t := by
      intro V X t hK hA hr hs hm
      have he : eaD X 8 0 = p.add (4 * n + 0) := eaD_p (by rw [get_r8, hs.r8])
      refine c.s_mov_mr hK hA hin (by omega) hr (Or.inl rfl) (gci_368 _) (by rw [he]; exact gS4 hE (by omega)) ?_
      rw [he]
      rintro Y1 t1 hK1 hA1 ⟨hr1, hg1⟩
      exact chk _ Y1 t1 hK1 hA1 hr1 (by rw [hg1]; exact hs) (hm.stk hE _ (by omega))
    have hrdi : X.cpu.gpr.get (regOf 7) = p.add (128 + 4 * n) := hs.rdi
    -- `bt r9d, esi`, `jb`
    refine c.s_fll hK hA hin (by omega) hr fl_bt_rr32 (gci_387 _) ?_
    rintro Y1 t1 hK1 hA1 ⟨hr1, hg1⟩
    refine c.s_jcc hK1 hA1 hin (by omega) hr1 (gci_391 _) (tgt := 336) rfl (by omega) (fun _ => ?_) fun _ => ?_
    · -- a subleaf of a component `XCR0` may enable: `CPUID`, its size and offset
      rintro Y2 t2 hK2 hA2 ⟨hr2, hg2⟩
      have hs2 : LS s₀ p n Y2.cpu.gpr := by rw [hg2, hg1]; exact hs
      refine c.s_wrl hK2 hA2 hin (by omega) hr2 wr_mov_rr32 (gci_336 _) ?_
      rintro Y3 t3 hK3 hA3 ⟨hr3, v3, hg3⟩
      refine c.s_wrl hK3 hA3 hin (by omega) hr3 wr_mov_rr32 (gci_339 _) ?_
      rintro Y4 t4 hK4 hA4 ⟨hr4, v4, hg4⟩
      refine c.s_cpuid hK4 hA4 hin (by omega) hr4 (gci_341 _) ?_
      rintro Y5 t5 hK5 hA5 ⟨hr5, cpu, -, hg5⟩
      have hs5 : LS s₀ p n Y5.cpu.gpr := by
        rw [hg5, hg4, hg3]; exact ((hs2.set (r := 0) (by omega) _).set (r := 1) (by omega) _).cpuid _ _ _ _
      have he : eaD Y5 7 0 = p.add (128 + 4 * n + 0) := eaD_p (by rw [get_r7, hs5.rdi])
      refine c.s_mov_mr hK5 hA5 hin (by omega) hr5 (Or.inl rfl) (gci_343 _) (by rw [he]; exact gS4 hE (by omega)) ?_
      rw [he]
      rintro Y6 t6 hK6 hA6 ⟨hr6, hg6⟩
      have hm6 := hm.stk hE (rv Y5 32 0) (n := 128 + 4 * n + 0) (m := 32 / 8) (by omega)
      refine c.s_cmp_ri32 hK6 hA6 hin (by omega) hr6 (gci_345 _) ?_
      rintro Y7 t7 hK7 hA7 ⟨hr7, hg7, hf7⟩
      have hs7 : LS s₀ p n Y7.cpu.gpr := by rw [hg7, hg6]; exact hs5
      refine c.s_jcc hK7 hA7 hin (by omega) hr7 (gci_348 _) (tgt := 376) rfl (by omega) (fun hc => ?_) fun hc => ?_
      · have h0 : n = 0 := by
          rw [zf_cmp hf7 (by rw [hg6]; exact hs5.rsi) (by omega) (by decide)] at hc
          simpa using hc
        rintro Y8 t8 hK8 hA8 ⟨hr8, hg8⟩
        exact inc _ Y8 t8 hK8 hA8 hr8 (by rw [hg8]; exact hs7) (by omega) hm6
      · have h0 : n ≠ 0 := by
          rw [zf_cmp hf7 (by rw [hg6]; exact hs5.rsi) (by omega) (by decide)] at hc
          simpa using hc
        rintro Y8 t8 hK8 hA8 ⟨hr8, hg8⟩
        have hs8 : LS s₀ p n Y8.cpu.gpr := by rw [hg8]; exact hs7
        have he1 : eaD Y8 7 18446744073709551612 = p.add (128 + 4 * (n - 1)) :=
          eaD_m4 (by rw [get_r7, hs8.rdi]; congr 1; omega)
        refine c.s_mov_rm hK8 hA8 hin (by omega) hr8 (Or.inl rfl) (gci_350 _)
          (fun i hi => by rw [he1, addr_add_add]; exact c.hws _ (gS hE (by omega))) ?_
        rintro Y9 t9 hK9 hA9 ⟨hr9, hg9⟩
        have hs9 : LS s₀ p n Y9.cpu.gpr := by rw [hg9]; exact hs8.set (r := 0) (by omega) _
        have he2 : eaD Y9 8 18446744073709551612 = p.add (4 * (n - 1)) :=
          eaD_m4 (by rw [get_r8, hs9.r8]; congr 1; omega)
        refine c.s_add_rm32 hK9 hA9 hin (by omega) hr9 (gci_353 _)
          (fun i hi => by rw [he2, addr_add_add]; exact c.hws _ (gS hE (by omega))) ?_
        rintro Y10 t10 hK10 hA10 ⟨hr10, hg10⟩
        have hs10 : LS s₀ p n Y10.cpu.gpr := by rw [hg10]; exact hs9.set (r := 0) (by omega) _
        refine c.s_wrl hK10 hA10 hin (by omega) hr10 wr_and_ri32 (gci_357 _) ?_
        rintro Y11 t11 hK11 hA11 ⟨hr11, v11, hg11⟩
        have hs11 : LS s₀ p n Y11.cpu.gpr := by rw [hg11]; exact hs10.set (r := 1) (by omega) _
        refine c.s_jcc hK11 hA11 hin (by omega) hr11 (gci_360 _) (tgt := 368) rfl (by omega) (fun _ => ?_) fun _ => ?_
        · rintro Y12 t12 hK12 hA12 ⟨hr12, hg12⟩
          exact j368 _ Y12 t12 hK12 hA12 hr12 (by rw [hg12]; exact hs11) hm6
        · rintro Y12 t12 hK12 hA12 ⟨hr12, hg12⟩
          refine c.s_wrl hK12 hA12 hin (by omega) hr12 wr_add_ri32 (gci_362 _) ?_
          rintro Y13 t13 hK13 hA13 ⟨hr13, v13, hg13⟩
          refine c.s_wrl hK13 hA13 hin (by omega) hr13 wr_and_ri32 (gci_365 _) ?_
          rintro Y14 t14 hK14 hA14 ⟨hr14, v14, hg14⟩
          exact j368 _ Y14 t14 hK14 hA14 hr14
            (by rw [hg14, hg13, hg12]; exact (hs11.set (r := 0) (by omega) _).set (r := 0) (by omega) _) hm6
    · -- a subleaf of no such component: size 0
      rintro Y2 t2 hK2 hA2 ⟨hr2, hg2⟩
      have hs2 : LS s₀ p n Y2.cpu.gpr := by rw [hg2, hg1]; exact hs
      have he : eaD Y2 7 0 = p.add (128 + 4 * n + 0) := eaD_p (by rw [get_r7, hs2.rdi])
      refine c.s_mov_mi32 hK2 hA2 hin (by omega) hr2 (gci_393 _) (by rw [he]; exact gS4 hE (by omega)) ?_
      rw [he]
      rintro Y3 t3 hK3 hA3 ⟨hr3, hg3⟩
      have hm3 := hm.stk hE (BitVec.ofNat 32 0) (n := 128 + 4 * n + 0) (m := 4) (by omega)
      refine c.s_cmp_ri32 hK3 hA3 hin (by omega) hr3 (gci_399 _) ?_
      rintro Y4 t4 hK4 hA4 ⟨hr4, hg4, hf4⟩
      have hs4 : LS s₀ p n Y4.cpu.gpr := by rw [hg4, hg3]; exact hs2
      refine c.s_jcc hK4 hA4 hin (by omega) hr4 (gci_402 _) (tgt := 376) rfl (by omega) (fun hc => ?_) fun hc => ?_
      · have h0 : n = 0 := by
          rw [zf_cmp hf4 (by rw [hg3]; exact hs2.rsi) (by omega) (by decide)] at hc
          simpa using hc
        rintro Y5 t5 hK5 hA5 ⟨hr5, hg5⟩
        exact inc _ Y5 t5 hK5 hA5 hr5 (by rw [hg5]; exact hs4) (by omega) hm3
      · have h0 : n ≠ 0 := by
          rw [zf_cmp hf4 (by rw [hg3]; exact hs2.rsi) (by omega) (by decide)] at hc
          simpa using hc
        rintro Y5 t5 hK5 hA5 ⟨hr5, hg5⟩
        have hs5 : LS s₀ p n Y5.cpu.gpr := by rw [hg5]; exact hs4
        have he1 : eaD Y5 7 18446744073709551612 = p.add (128 + 4 * (n - 1)) :=
          eaD_m4 (by rw [get_r7, hs5.rdi]; congr 1; omega)
        refine c.s_mov_rm hK5 hA5 hin (by omega) hr5 (Or.inl rfl) (gci_404 _)
          (fun i hi => by rw [he1, addr_add_add]; exact c.hws _ (gS hE (by omega))) ?_
        rintro Y6 t6 hK6 hA6 ⟨hr6, hg6⟩
        have hs6 : LS s₀ p n Y6.cpu.gpr := by rw [hg6]; exact hs5.set (r := 0) (by omega) _
        have he2 : eaD Y6 8 18446744073709551612 = p.add (4 * (n - 1)) :=
          eaD_m4 (by rw [get_r8, hs6.r8]; congr 1; omega)
        refine c.s_add_rm32 hK6 hA6 hin (by omega) hr6 (gci_407 _)
          (fun i hi => by rw [he2, addr_add_add]; exact c.hws _ (gS hE (by omega))) ?_
        rintro Y7 t7 hK7 hA7 ⟨hr7, hg7⟩
        have hs7 : LS s₀ p n Y7.cpu.gpr := by rw [hg7]; exact hs6.set (r := 0) (by omega) _
        have he : eaD Y7 8 0 = p.add (4 * n + 0) := eaD_p (by rw [get_r8, hs7.r8])
        refine c.s_mov_mr hK7 hA7 hin (by omega) hr7 (Or.inl rfl) (gci_411 _) (by rw [he]; exact gS4 hE (by omega)) ?_
        rw [he]
        rintro Y8 t8 hK8 hA8 ⟨hr8, hg8⟩
        refine c.s_jmp hK8 hA8 hin (by omega) hr8 (gci_414 _) (tgt := 371) rfl (by omega) ?_
        rintro Y9 t9 hK9 hA9 ⟨hr9, hg9⟩
        exact chk _ Y9 t9 hK9 hA9 hr9 (by rw [hg9, hg8]; exact hs7) (hm3.stk hE _ (by omega))
  intro m
  induction m with
  | zero =>
    intro n hn V X t hK hA hr hs hm
    exact body n (by omega) V X t hK hA hr hs hm (fun h => absurd h (by omega))
  | succ m ih =>
    intro n hn V X t hK hA hr hs hm
    exact body n (by omega) V X t hK hA hr hs hm (fun _ => ih (n + 1) (by omega))

/-! ## The `XSAVE` state size (`225`) -/

theorem gF {a : Nat} (h : a + 4 ≤ 0x90) : ∀ i < 4, Foot (ws 256 gW s₀) ((cpuRgn.base.add a).add i) :=
  fun i hi => gC (by omega)

theorem gD (c : Call prof 256 gW gR (gPre prof) (gPost prof) 0x612cc0 L s₀ ra o) {a n : Nat} (h : a + n ≤ 0x90) :
    ∀ i < n, Foot (fp 256 gW gR (gPre prof) (gPost prof) L s₀).data ((cpuRgn.base.add a).add i) :=
  fun i hi => c.hws _ (gC (by omega))

/-- After the loop (`416`): the size of the enabled components, into `xsave_state_size`. -/
theorem g416 (c : Call prof 256 gW gR (gPre prof) (gPost prof) 0x612cc0 L s₀ ra o) (hin : CodeIn L 0x612cc0 gci)
    {p : Addr} (hE : GEnv s₀ p) {X : State} {t : Nat} {V : Addr → Byte}
    (hK : KeptW (ws 256 gW s₀) s₀ X) (hA : Agree (fp 256 gW gR (gPre prof) (gPost prof) L s₀) X.proc.mm.mem V)
    (hr : X.cpu.rip = (0x612cc0 : Addr).add 416) (hb : GB s₀ p X.cpu.gpr) (hm : GM prof s₀ p V) :
    Go prof 256 gW gR (gPre prof) (gPost prof) L s₀ ra o X t := by
  have hl : gci.length = 896 := gci_length
  have hsp : X.cpu.gpr.get (regOf 4) = p.add 112 := hb.sp
  refine c.s_mov_rm hK hA hin (by omega) hr (Or.inl rfl) (gci_416 _)
    (fun i hi => by rw [eaD_p hsp, addr_add_add]; exact c.hws _ (gS hE (by omega))) ?_
  rintro Y1 t1 hK1 hA1 ⟨hr1, hg1⟩
  have hb1 : GB s₀ p Y1.cpu.gpr := by rw [hg1]; exact hb.set (r := 0) (by omega) _
  have hsp1 : Y1.cpu.gpr.get (regOf 4) = p.add 112 := hb1.sp
  refine c.s_add_rm32 hK1 hA1 hin (by omega) hr1 (gci_423 _)
    (fun i hi => by rw [eaD_p hsp1, addr_add_add]; exact c.hws _ (gS hE (by omega))) ?_
  rintro Y2 t2 hK2 hA2 ⟨hr2, hg2⟩
  have hb2 : GB s₀ p Y2.cpu.gpr := by rw [hg2]; exact hb1.set (r := 0) (by omega) _
  refine c.s_jcc hK2 hA2 hin (by omega) hr2 (gci_427 _) (tgt := 452) rfl (by omega) (fun _ => ?_) fun _ => ?_
  · rintro Y3 t3 hK3 hA3 ⟨hr3, hg3⟩
    exact gTail c hin hE hK3 hA3 hr3 (by rw [hg3]; exact hb2) hm
  rintro Y3 t3 hK3 hA3 ⟨hr3, hg3⟩
  -- `or [feature[0]], 0x400000` (`XSAVEC_Usable`)
  refine c.s_or_rip_i32 hK3 hA3 hin (by omega) hr3 (gci_429 _) (g := cpuRgn.base.add 96) (by decide) (gF (by omega)) ?_
  rintro Y4 t4 hK4 hA4 ⟨hr4, hg4⟩
  have hm4 : GM prof s₀ p _ := hm.cf hE (hm.1.st_f0_or _ _ (fun i hi => getLsbD_rd_or 4194304 hi)
      (fun h => absurd h (by decide)) (fun h => absurd h (by decide)) (fun h => absurd h (by decide))
      (fun h => absurd h (by decide)) (fun h => absurd h (by decide)) (fun h => absurd h (by decide))
      (fun h => absurd h (by decide)) (fun h => absurd h (by decide)))
    (by decide) (by rw [toBytesLE_length]; decide)
  refine c.s_wrl hK4 hA4 hin (by omega) hr4 wr_add_ri32 (gci_439 _) ?_
  rintro Y5 t5 hK5 hA5 ⟨hr5, v5, hg5⟩
  refine c.s_wrl hK5 hA5 hin (by omega) hr5 wr_and_ri32 (gci_442 _) ?_
  rintro Y6 t6 hK6 hA6 ⟨hr6, v6, hg6⟩
  refine c.s_mov_rip_r64 hK6 hA6 hin (by omega) hr6 (gci_445 _) (g := cpuRgn.base.add 128) (by decide)
    (fun i hi => gC (by omega)) ?_
  rintro Y7 t7 hK7 hA7 ⟨hr7, hg7⟩
  exact gTail c hin hE hK7 hA7 hr7 (by rw [hg7, hg6, hg5, hg4, hg3]; exact (hb2.set (r := 0) (by omega) _).set (r := 0) (by omega) _)
    (hm4.cfu hE _ (by omega) (by omega))

/-- From `225`: leaf `0DH` subleaf 0 (`xsave_state_full_size`), then subleaf 1 and the compact sizes. -/
theorem gXs (c : Call prof 256 gW gR (gPre prof) (gPost prof) 0x612cc0 L s₀ ra o) (hin : CodeIn L 0x612cc0 gci)
    {p : Addr} (hE : GEnv s₀ p) {X : State} {t : Nat} {V : Addr → Byte}
    (hK : KeptW (ws 256 gW s₀) s₀ X) (hA : Agree (fp 256 gW gR (gPre prof) (gPost prof) L s₀) X.proc.mm.mem V)
    (hr : X.cpu.rip = (0x612cc0 : Addr).add 225) (hb : GB s₀ p X.cpu.gpr) (hm : GM prof s₀ p V) :
    Go prof 256 gW gR (gPre prof) (gPost prof) L s₀ ra o X t := by
  have hl : gci.length = 896 := gci_length
  refine c.s_cmp_m32i_rip hK hA hin (by omega) hr (gci_225 _) (g := cpuRgn.base.add 108) (by decide)
    (gD c (by omega)) ?_
  rintro Y1 t1 hK1 hA1 ⟨hr1, hg1⟩
  refine c.s_jcc hK1 hA1 hin (by omega) hr1 (gci_232 _) (tgt := 452) rfl (by omega) (fun _ => ?_) fun _ => ?_
  · rintro Y2 t2 hK2 hA2 ⟨hr2, hg2⟩
    exact gTail c hin hE hK2 hA2 hr2 (by rw [hg2, hg1]; exact hb) hm
  rintro Y2 t2 hK2 hA2 ⟨hr2, hg2⟩
  have hb2 : GB s₀ p Y2.cpu.gpr := by rw [hg2, hg1]; exact hb
  refine c.s_wrl hK2 hA2 hin (by omega) hr2 wr_mov_ri32 (gci_238 _) ?_
  rintro Y3 t3 hK3 hA3 ⟨hr3, v3, hg3⟩
  refine c.s_wrl hK3 hA3 hin (by omega) hr3 wr_xor_rr32 (gci_243 _) ?_
  rintro Y4 t4 hK4 hA4 ⟨hr4, v4, hg4⟩
  refine c.s_cpuid hK4 hA4 hin (by omega) hr4 (gci_245 _) ?_
  rintro Y5 t5 hK5 hA5 ⟨hr5, cpu, -, hg5⟩
  have hb5 : GB s₀ p Y5.cpu.gpr := by
    rw [hg5, hg4, hg3]; exact ((hb2.set (r := 0) (by omega) _).set (r := 1) (by omega) _).cpuid _ _ _ _
  refine c.s_fll hK5 hA5 hin (by omega) hr5 fl_test_rr32 (gci_247 _) ?_
  rintro Y6 t6 hK6 hA6 ⟨hr6, hg6⟩
  refine c.s_jcc hK6 hA6 hin (by omega) hr6 (gci_249 _) (tgt := 452) rfl (by omega) (fun _ => ?_) fun _ => ?_
  · rintro Y7 t7 hK7 hA7 ⟨hr7, hg7⟩
    exact gTail c hin hE hK7 hA7 hr7 (by rw [hg7, hg6]; exact hb5) hm
  rintro Y7 t7 hK7 hA7 ⟨hr7, hg7⟩
  refine c.s_wrl hK7 hA7 hin (by omega) hr7 wr_add_ri32 (gci_255 _) ?_
  rintro Y8 t8 hK8 hA8 ⟨hr8, v8, hg8⟩
  refine c.s_wrl hK8 hA8 hin (by omega) hr8 wr_and_ri32 (gci_258 _) ?_
  rintro Y9 t9 hK9 hA9 ⟨hr9, v9, hg9⟩
  refine c.s_wrl hK9 hA9 hin (by omega) hr9 wr_mov_rr32 (gci_261 _) ?_
  rintro Y10 t10 hK10 hA10 ⟨hr10, v10, hg10⟩
  have hb10 : GB s₀ p Y10.cpu.gpr := by
    rw [hg10, hg9, hg8, hg7, hg6]
    exact ((hb5.set (r := 3) (by omega) _).set (r := 3) (by omega) _).set (r := 0) (by omega) _
  refine c.s_mov_rip_r32 hK10 hA10 hin (by omega) hr10 (gci_263 _) (g := cpuRgn.base.add 136) (by decide)
    (gF (by omega)) ?_
  rintro Y11 t11 hK11 hA11 ⟨hr11, hg11⟩
  have hm11 := hm.cfu hE (rv Y10 32 3) (n := 136) (m := 4) (by omega) (by omega)
  refine c.s_mov_rip_r64 hK11 hA11 hin (by omega) hr11 (gci_269 _) (g := cpuRgn.base.add 128) (by decide)
    (fun i hi => gC (by omega)) ?_
  rintro Y12 t12 hK12 hA12 ⟨hr12, hg12⟩
  have hm12 := hm11.cfu hE (rv Y11 64 0) (n := 128) (m := 8) (by omega) (by omega)
  have hb12 : GB s₀ p Y12.cpu.gpr := by rw [hg12, hg11]; exact hb10
  refine c.s_test_m8i_rip hK12 hA12 hin (by omega) hr12 (gci_276 _) (g := (cpuRgn.base.add 48).add 0) (by decide)
    (gD c (a := 48) (n := 1) (by omega) 0 (by omega)) ?_
  rintro Y13 t13 hK13 hA13 ⟨hr13, hg13, -⟩
  have hb13 : GB s₀ p Y13.cpu.gpr := by rw [hg13]; exact hb12
  refine c.s_jcc hK13 hA13 hin (by omega) hr13 (gci_283 _) (tgt := 452) rfl (by omega) (fun _ => ?_) fun _ => ?_
  · rintro Y14 t14 hK14 hA14 ⟨hr14, hg14⟩
    exact gTail c hin hE hK14 hA14 hr14 (by rw [hg14]; exact hb13) hm12
  rintro Y14 t14 hK14 hA14 ⟨hr14, hg14⟩
  have hb14 : GB s₀ p Y14.cpu.gpr := by rw [hg14]; exact hb13
  have hsp14 : Y14.cpu.gpr.get (regOf 4) = p.add (0 + 112) := hb14.sp
  refine c.s_lea_bd hK14 hA14 hin (by omega) hr14 (gci_289 _) ?_
  rintro Y15 t15 hK15 hA15 ⟨hr15, hg15⟩
  have he15 : eaD Y14 4 18446744073709551504 = p.add 0 := by
    show Y14.cpu.gpr.get (regOf 4) + _ = _; rw [hsp14]; exact add_neg p 0 112 _ (by decide)
  have hb15 : GB s₀ p Y15.cpu.gpr := by rw [hg15]; exact hb14.set (r := 8) (by omega) _
  have hsp15 : Y15.cpu.gpr.get (regOf 4) = p.add 112 := hb15.sp
  refine c.s_lea_bd hK15 hA15 hin (by omega) hr15 (gci_294 _) ?_
  rintro Y16 t16 hK16 hA16 ⟨hr16, hg16⟩
  have he16 : eaD Y15 4 16 = p.add (112 + 16) := eaD_p hsp15
  refine c.s_mov_ri32 hK16 hA16 hin (by omega) hr16 (gci_299 _) ?_
  rintro Y17 t17 hK17 hA17 ⟨hr17, hg17⟩
  have hL17 : LS s₀ p 0 Y17.cpu.gpr := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hg17, hg16, hg15]
      exact ((hb14.set (r := 8) (by omega) _).set (r := 7) (by omega) _).set (r := 6) (by omega) _
    · rw [hg17]; rfl
    · rw [hg17, hg16]; exact he16
    · rw [hg17, hg16, hg15]; exact he15
  have he17 : eaD Y17 4 18446744073709551504 = p.add 0 := by
    show Y17.cpu.gpr.get (regOf 4) + _ = _; rw [show Y17.cpu.gpr.get (regOf 4) = p.add (0 + 112) from hL17.b.sp]
    exact add_neg p 0 112 _ (by decide)
  refine c.s_mov_mi32 hK17 hA17 hin (by omega) hr17 (gci_304 _) (by rw [he17]; exact gS4 hE (by omega)) ?_
  rw [he17]
  rintro Y18 t18 hK18 hA18 ⟨hr18, hg18⟩
  have hm18 := hm12.stk hE (BitVec.ofNat 32 576) (n := 0) (m := 4) (by omega)
  refine c.s_wrl hK18 hA18 hin (by omega) hr18 wr_mov_ri32 (gci_312 _) ?_
  rintro Y19 t19 hK19 hA19 ⟨hr19, v19, hg19⟩
  refine c.s_wrl hK19 hA19 hin (by omega) hr19 wr_mov_ri32 (gci_318 _) ?_
  rintro Y20 t20 hK20 hA20 ⟨hr20, v20, hg20⟩
  refine c.s_jmp hK20 hA20 hin (by omega) hr20 (gci_324 _) (tgt := 387) rfl (by omega) ?_
  rintro Y21 t21 hK21 hA21 ⟨hr21, hg21⟩
  exact gLoop c hin hE (fun V Y t hK hA hr hb hm => g416 c hin hE hK hA hr hb hm) 29 0 rfl _ Y21 t21 hK21 hA21 hr21
    (by rw [hg21, hg20, hg19, hg18]; exact (hL17.set (r := 9) (by omega) _).set (r := 10) (by omega) _) hm18

/-! ## The `*_Usable` bits from `XCR0` and leaf 7 (`482` to `891`) -/

/-- From `j`, with `GB` and `GM`, the call keeps its contract. -/
def At (prof : Profile) (L : List (Addr × List Byte)) (s₀ : State) (ra : Addr) (o : Oracle) (p : Addr) (j : Nat) : Prop :=
  ∀ (V : Addr → Byte) X t, KeptW (ws 256 gW s₀) s₀ X →
    Agree (fp 256 gW gR (gPre prof) (gPost prof) L s₀) X.proc.mm.mem V → X.cpu.rip = (0x612cc0 : Addr).add j →
    GB s₀ p X.cpu.gpr → GM prof s₀ p V → Go prof 256 gW gR (gPre prof) (gPost prof) L s₀ ra o X t

/-- The word at offset `a` of `_dl_x86_cpu_features`, as a 4-byte load reads it. -/
abbrev rdw (V : Addr → Byte) (a : Nat) : BitVec 32 := ofBytesLE 32 ((byteAddrs (cpuRgn.base.add a) 4).map V)

/-- `or [feature[0]], imm` with no bit `CpuOk` watches. -/
theorem GM.orU {p : Addr} {V : Addr → Byte} (h : GM prof s₀ p V) (hE : GEnv s₀ p) (imm : Nat)
    (hz : ((BitVec.ofNat 32 imm).getLsbD 0 || (BitVec.ofNat 32 imm).getLsbD 1 || (BitVec.ofNat 32 imm).getLsbD 2 ||
      (BitVec.ofNat 32 imm).getLsbD 6 || (BitVec.ofNat 32 imm).getLsbD 7 || (BitVec.ofNat 32 imm).getLsbD 8 ||
      (BitVec.ofNat 32 imm).getLsbD 17 || (BitVec.ofNat 32 imm).getLsbD 19) = false) :
    GM prof s₀ p (Vst V (cpuRgn.base.add 96) (toBytesLE (rdw V 96 ||| BitVec.ofNat 32 imm) 4)) := by
  simp only [Bool.or_eq_false_iff] at hz
  obtain ⟨⟨⟨⟨⟨⟨⟨z0, z1⟩, z2⟩, z6⟩, z7⟩, z8⟩, z17⟩, z19⟩ := hz
  exact h.cf hE (h.1.st_f0_or _ _ (fun i hi => getLsbD_rd_or imm hi)
      (fun h => by rw [z0] at h; cases h) (fun h => by rw [z1] at h; cases h) (fun h => by rw [z2] at h; cases h)
      (fun h => by rw [z6] at h; cases h) (fun h => by rw [z7] at h; cases h) (fun h => by rw [z8] at h; cases h)
      (fun h => by rw [z17] at h; cases h) (fun h => by rw [z19] at h; cases h))
    (by decide) (by rw [toBytesLE_length]; decide)

/-- `or [feature[0]], imm` setting AVX-512 bits 6 to 8 only, with `AVX512F_Usable` set: `GM`, and still bit 2. -/
theorem GM.orB {p : Addr} {V : Addr → Byte} (h : GM prof s₀ p V) (hE : GEnv s₀ p) (imm : Nat) (h2 : bitV V 96 2 = true)
    (hz : ((BitVec.ofNat 32 imm).getLsbD 0 || (BitVec.ofNat 32 imm).getLsbD 1 || (BitVec.ofNat 32 imm).getLsbD 2 ||
      (BitVec.ofNat 32 imm).getLsbD 17 || (BitVec.ofNat 32 imm).getLsbD 19) = false)
    (a6 : (BitVec.ofNat 32 imm).getLsbD 6 = true → prof.reports 7 0 (·.ebx) 31)
    (a7 : (BitVec.ofNat 32 imm).getLsbD 7 = true → prof.reports 7 0 (·.ebx) 17)
    (a8 : (BitVec.ofNat 32 imm).getLsbD 8 = true → prof.reports 7 0 (·.ebx) 30) :
    GM prof s₀ p (Vst V (cpuRgn.base.add 96) (toBytesLE (rdw V 96 ||| BitVec.ofNat 32 imm) 4)) ∧
      bitV (Vst V (cpuRgn.base.add 96) (toBytesLE (rdw V 96 ||| BitVec.ofNat 32 imm) 4)) 96 2 = true := by
  simp only [Bool.or_eq_false_iff] at hz
  obtain ⟨⟨⟨⟨z0, z1⟩, z2⟩, z17⟩, z19⟩ := hz
  have t2 : (bitV V 96 2 || (BitVec.ofNat 32 imm).getLsbD 2) = true := by rw [h2]; rfl
  refine ⟨h.cf hE (h.1.st_f0_or _ _ (fun i hi => getLsbD_rd_or imm hi)
      (fun h => by rw [z0] at h; cases h) (fun h => by rw [z1] at h; cases h) (fun h => by rw [z2] at h; cases h)
      (fun h => ⟨t2, a6 h⟩) (fun h => ⟨t2, a7 h⟩) (fun h => ⟨t2, a8 h⟩)
      (fun h => by rw [z17] at h; cases h) (fun h => by rw [z19] at h; cases h))
    (by decide) (by rw [toBytesLE_length]; decide), ?_⟩
  rw [bitV_f0_or _ (fun i hi => getLsbD_rd_or imm hi) (by omega), h2]; rfl

/-- From `738`: `*_Usable` bits from leaf 7's `EDX` and `ECX` that `CpuOk` does not watch, then back to `225`. -/
theorem g738 (c : Call prof 256 gW gR (gPre prof) (gPost prof) 0x612cc0 L s₀ ra o) (hin : CodeIn L 0x612cc0 gci)
    {p : Addr} (hE : GEnv s₀ p) : At prof L s₀ ra o p 738 := by
  have hl : gci.length = 896 := gci_length
  have j225 : At prof L s₀ ra o p 225 := fun V X t hK hA hr hb hm => gXs c hin hE hK hA hr hb hm
  have j857 : At prof L s₀ ra o p 857 := by
    intro V X t hK hA hr hb hm
    refine c.s_wrl hK hA hin (by omega) hr wr_and_h8i (gci_857 _) ?_
    rintro Y1 t1 hK1 hA1 ⟨hr1, v1, hg1⟩
    have hb1 : GB s₀ p Y1.cpu.gpr := by rw [hg1]; exact hb.set (r := 2) (by omega) _
    refine c.s_jcc hK1 hA1 hin (by omega) hr1 (gci_860 _) (tgt := 225) rfl (by omega) (fun _ => ?_) fun _ => ?_
    · rintro Y2 t2 hK2 hA2 ⟨hr2, hg2⟩
      exact j225 _ Y2 t2 hK2 hA2 hr2 (by rw [hg2]; exact hb1) hm
    rintro Y2 t2 hK2 hA2 ⟨hr2, hg2⟩
    refine c.s_or_rip_i32 hK2 hA2 hin (by omega) hr2 (gci_866 _) (g := cpuRgn.base.add 96) (by decide) (gF (by omega)) ?_
    rintro Y3 t3 hK3 hA3 ⟨hr3, hg3⟩
    refine c.s_jmp hK3 hA3 hin (by omega) hr3 (gci_876 _) (tgt := 225) rfl (by omega) ?_
    rintro Y4 t4 hK4 hA4 ⟨hr4, hg4⟩
    exact j225 _ Y4 t4 hK4 hA4 hr4 (by rw [hg4, hg3, hg2]; exact hb1) (hm.orU hE 65536 (by decide))
  have j842 : At prof L s₀ ra o p 842 := by
    intro V X t hK hA hr hb hm
    refine c.s_fll hK hA hin (by omega) hr fl_test_h8i (gci_842 _) ?_
    rintro Y1 t1 hK1 hA1 ⟨hr1, hg1⟩
    have hb1 : GB s₀ p Y1.cpu.gpr := by rw [hg1]; exact hb
    refine c.s_jcc hK1 hA1 hin (by omega) hr1 (gci_845 _) (tgt := 857) rfl (by omega) (fun _ => ?_) fun _ => ?_
    · rintro Y2 t2 hK2 hA2 ⟨hr2, hg2⟩
      exact j857 _ Y2 t2 hK2 hA2 hr2 (by rw [hg2]; exact hb1) hm
    rintro Y2 t2 hK2 hA2 ⟨hr2, hg2⟩
    refine c.s_or_rip_i32 hK2 hA2 hin (by omega) hr2 (gci_847 _) (g := cpuRgn.base.add 96) (by decide) (gF (by omega)) ?_
    rintro Y3 t3 hK3 hA3 ⟨hr3, hg3⟩
    exact j857 _ Y3 t3 hK3 hA3 hr3 (by rw [hg3, hg2]; exact hb1) (hm.orU hE 32768 (by decide))
  have j827 : At prof L s₀ ra o p 827 := by
    intro V X t hK hA hr hb hm
    refine c.s_fll hK hA hin (by omega) hr fl_test_r8i (gci_827 _) ?_
    rintro Y1 t1 hK1 hA1 ⟨hr1, hg1⟩
    have hb1 : GB s₀ p Y1.cpu.gpr := by rw [hg1]; exact hb
    refine c.s_jcc hK1 hA1 hin (by omega) hr1 (gci_830 _) (tgt := 842) rfl (by omega) (fun _ => ?_) fun _ => ?_
    · rintro Y2 t2 hK2 hA2 ⟨hr2, hg2⟩
      exact j842 _ Y2 t2 hK2 hA2 hr2 (by rw [hg2]; exact hb1) hm
    rintro Y2 t2 hK2 hA2 ⟨hr2, hg2⟩
    refine c.s_or_rip_i32 hK2 hA2 hin (by omega) hr2 (gci_832 _) (g := cpuRgn.base.add 96) (by decide) (gF (by omega)) ?_
    rintro Y3 t3 hK3 hA3 ⟨hr3, hg3⟩
    exact j842 _ Y3 t3 hK3 hA3 hr3 (by rw [hg3, hg2]; exact hb1) (hm.orU hE 16384 (by decide))
  have j812 : At prof L s₀ ra o p 812 := by
    intro V X t hK hA hr hb hm
    refine c.s_fll hK hA hin (by omega) hr fl_test_r8i (gci_812 _) ?_
    rintro Y1 t1 hK1 hA1 ⟨hr1, hg1⟩
    have hb1 : GB s₀ p Y1.cpu.gpr := by rw [hg1]; exact hb
    refine c.s_jcc hK1 hA1 hin (by omega) hr1 (gci_815 _) (tgt := 827) rfl (by omega) (fun _ => ?_) fun _ => ?_
    · rintro Y2 t2 hK2 hA2 ⟨hr2, hg2⟩
      exact j827 _ Y2 t2 hK2 hA2 hr2 (by rw [hg2]; exact hb1) hm
    rintro Y2 t2 hK2 hA2 ⟨hr2, hg2⟩
    refine c.s_or_rip_i32 hK2 hA2 hin (by omega) hr2 (gci_817 _) (g := cpuRgn.base.add 96) (by decide) (gF (by omega)) ?_
    rintro Y3 t3 hK3 hA3 ⟨hr3, hg3⟩
    exact j827 _ Y3 t3 hK3 hA3 hr3 (by rw [hg3, hg2]; exact hb1) (hm.orU hE 8192 (by decide))
  have j795 : At prof L s₀ ra o p 795 := by
    intro V X t hK hA hr hb hm
    refine c.s_fll hK hA hin (by omega) hr fl_test_ri32 (gci_795 _) ?_
    rintro Y1 t1 hK1 hA1 ⟨hr1, hg1⟩
    have hb1 : GB s₀ p Y1.cpu.gpr := by rw [hg1]; exact hb
    refine c.s_jcc hK1 hA1 hin (by omega) hr1 (gci_800 _) (tgt := 812) rfl (by omega) (fun _ => ?_) fun _ => ?_
    · rintro Y2 t2 hK2 hA2 ⟨hr2, hg2⟩
      exact j812 _ Y2 t2 hK2 hA2 hr2 (by rw [hg2]; exact hb1) hm
    rintro Y2 t2 hK2 hA2 ⟨hr2, hg2⟩
    refine c.s_or_rip_i32 hK2 hA2 hin (by omega) hr2 (gci_802 _) (g := cpuRgn.base.add 96) (by decide) (gF (by omega)) ?_
    rintro Y3 t3 hK3 hA3 ⟨hr3, hg3⟩
    exact j812 _ Y3 t3 hK3 hA3 hr3 (by rw [hg3, hg2]; exact hb1) (hm.orU hE 4096 (by decide))
  have j780 : At prof L s₀ ra o p 780 := by
    intro V X t hK hA hr hb hm
    refine c.s_fll hK hA hin (by omega) hr fl_test_h8i (gci_780 _) ?_
    rintro Y1 t1 hK1 hA1 ⟨hr1, hg1⟩
    have hb1 : GB s₀ p Y1.cpu.gpr := by rw [hg1]; exact hb
    refine c.s_jcc hK1 hA1 hin (by omega) hr1 (gci_783 _) (tgt := 795) rfl (by omega) (fun _ => ?_) fun _ => ?_
    · rintro Y2 t2 hK2 hA2 ⟨hr2, hg2⟩
      exact j795 _ Y2 t2 hK2 hA2 hr2 (by rw [hg2]; exact hb1) hm
    rintro Y2 t2 hK2 hA2 ⟨hr2, hg2⟩
    refine c.s_or_rip_i32 hK2 hA2 hin (by omega) hr2 (gci_785 _) (g := cpuRgn.base.add 96) (by decide) (gF (by omega)) ?_
    rintro Y3 t3 hK3 hA3 ⟨hr3, hg3⟩
    exact j795 _ Y3 t3 hK3 hA3 hr3 (by rw [hg3, hg2]; exact hb1) (hm.orU hE 2048 (by decide))
  have j774 : At prof L s₀ ra o p 774 := by
    intro V X t hK hA hr hb hm
    refine c.s_mov_r32_rip hK hA hin (by omega) hr (gci_774 _) (g := cpuRgn.base.add 24) (by decide) (gD c (by omega)) ?_
    rintro Y1 t1 hK1 hA1 ⟨hr1, hg1⟩
    exact j780 _ Y1 t1 hK1 hA1 hr1 (by rw [hg1]; exact hb.set (r := 2) (by omega) _) hm
  have j759 : At prof L s₀ ra o p 759 := by
    intro V X t hK hA hr hb hm
    refine c.s_wrl hK hA hin (by omega) hr wr_and_r8i (gci_759 _) ?_
    rintro Y1 t1 hK1 hA1 ⟨hr1, v1, hg1⟩
    have hb1 : GB s₀ p Y1.cpu.gpr := by rw [hg1]; exact hb.set (r := 2) (by omega) _
    refine c.s_jcc hK1 hA1 hin (by omega) hr1 (gci_762 _) (tgt := 774) rfl (by omega) (fun _ => ?_) fun _ => ?_
    · rintro Y2 t2 hK2 hA2 ⟨hr2, hg2⟩
      exact j774 _ Y2 t2 hK2 hA2 hr2 (by rw [hg2]; exact hb1) hm
    rintro Y2 t2 hK2 hA2 ⟨hr2, hg2⟩
    refine c.s_or_rip_i32 hK2 hA2 hin (by omega) hr2 (gci_764 _) (g := cpuRgn.base.add 96) (by decide) (gF (by omega)) ?_
    rintro Y3 t3 hK3 hA3 ⟨hr3, hg3⟩
    exact j774 _ Y3 t3 hK3 hA3 hr3 (by rw [hg3, hg2]; exact hb1) (hm.orU hE 1024 (by decide))
  have j744 : At prof L s₀ ra o p 744 := by
    intro V X t hK hA hr hb hm
    refine c.s_fll hK hA hin (by omega) hr fl_test_r8i (gci_744 _) ?_
    rintro Y1 t1 hK1 hA1 ⟨hr1, hg1⟩
    have hb1 : GB s₀ p Y1.cpu.gpr := by rw [hg1]; exact hb
    refine c.s_jcc hK1 hA1 hin (by omega) hr1 (gci_747 _) (tgt := 759) rfl (by omega) (fun _ => ?_) fun _ => ?_
    · rintro Y2 t2 hK2 hA2 ⟨hr2, hg2⟩
      exact j759 _ Y2 t2 hK2 hA2 hr2 (by rw [hg2]; exact hb1) hm
    rintro Y2 t2 hK2 hA2 ⟨hr2, hg2⟩
    refine c.s_or_rip_i32 hK2 hA2 hin (by omega) hr2 (gci_749 _) (g := cpuRgn.base.add 96) (by decide) (gF (by omega)) ?_
    rintro Y3 t3 hK3 hA3 ⟨hr3, hg3⟩
    exact j759 _ Y3 t3 hK3 hA3 hr3 (by rw [hg3, hg2]; exact hb1) (hm.orU hE 512 (by decide))
  intro V X t hK hA hr hb hm
  refine c.s_mov_r32_rip hK hA hin (by omega) hr (gci_738 _) (g := cpuRgn.base.add 28) (by decide) (gD c (by omega)) ?_
  rintro Y1 t1 hK1 hA1 ⟨hr1, hg1⟩
  exact j744 _ Y1 t1 hK1 hA1 hr1 (by rw [hg1]; exact hb.set (r := 2) (by omega) _) hm

theorem rv_set {X : State} {g : Gprs} {r : Nat} (hr : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 6) {v : BitVec 32}
    (h : X.cpu.gpr = g.set (regOf r) (v.setWidth 64)) : rv X 32 r = v := by
  rcases hr with rfl | rfl | rfl | rfl <;> simp [rv, h]

theorem rv_ne {X Y : State} {r q : Nat} {v : BitVec 64} (h : X.cpu.gpr = Y.cpu.gpr.set (regOf r) v)
    (hr : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 6 := by omega) (hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 6 := by omega)
    (hne : q ≠ r := by omega) : rv X 32 q = rv Y 32 q := by
  rcases hr with rfl | rfl | rfl | rfl <;> rcases hq with rfl | rfl | rfl | rfl <;> first | omega | simp [rv, h]

/-- `AVX512F_Usable` (and `AVX512ER_Usable`, bit 3) into `feature[0]`: `GM`, and bit 2. -/
theorem GM.orA {p : Addr} {V : Addr → Byte} (h : GM prof s₀ p V) (hE : GEnv s₀ p) {imm : Nat}
    (himm : imm = 4 ∨ imm = 12) (r16 : prof.reports 7 0 (·.ebx) 16) (en : prof.enabled xcr0Avx512) :
    GM prof s₀ p (Vst V (cpuRgn.base.add 96) (toBytesLE (rdw V 96 ||| BitVec.ofNat 32 imm) 4)) ∧
      bitV (Vst V (cpuRgn.base.add 96) (toBytesLE (rdw V 96 ||| BitVec.ofNat 32 imm) 4)) 96 2 = true := by
  rcases himm with rfl | rfl <;>
    exact ⟨h.cf hE (h.1.st_f0_or _ _ (fun i hi => getLsbD_rd_or _ hi) (fun h => absurd h (by decide))
      (fun h => absurd h (by decide)) (fun _ => ⟨r16, en⟩) (fun h => absurd h (by decide)) (fun h => absurd h (by decide))
      (fun h => absurd h (by decide)) (fun h => absurd h (by decide)) (fun h => absurd h (by decide)))
      (by decide) (by rw [toBytesLE_length]; decide),
      by rw [bitV_f0_or _ (fun i hi => getLsbD_rd_or _ hi) (by omega)]; exact Bool.or_eq_true_iff.2 (Or.inr (by decide))⟩

/-- `XCR0` enables AVX-512's state, from `XCR0 & 6 = 6` and the low half's `& 0xE0`. -/
theorem en512 {x : BitVec 64} (hx : prof.xcr0 = some x) (en6 : prof.enabled xcr0Avx)
    (h : x.setWidth 32 &&& BitVec.ofNat 32 224 = BitVec.ofNat 32 224) : prof.enabled xcr0Avx512 := by
  unfold Profile.enabled xcr0Avx512 at *
  unfold xcr0Avx at en6
  rw [hx] at en6 ⊢
  exact enabled_e6 en6 (enabled_of_low (by decide) h)

/-- AVX-512 from `663`: `e7` is leaf 7's `EBX` in `eax`, `edx` the `feature[0]` word, its bit 2 set. -/
theorem g663 (c : Call prof 256 gW gR (gPre prof) (gPost prof) 0x612cc0 L s₀ ra o) (hin : CodeIn L 0x612cc0 gci)
    {p : Addr} (hE : GEnv s₀ p) (e7 : BitVec 32) (he7 : ∀ i < 32, e7.getLsbD i = true → prof.reports 7 0 (·.ebx) i)
    {V : Addr → Byte} {X : State} {t : Nat} (hK : KeptW (ws 256 gW s₀) s₀ X)
    (hA : Agree (fp 256 gW gR (gPre prof) (gPost prof) L s₀) X.proc.mm.mem V) (hr : X.cpu.rip = (0x612cc0 : Addr).add 663)
    (hb : GB s₀ p X.cpu.gpr) (hm : GM prof s₀ p V) (h2 : bitV V 96 2 = true) (hea : rv X 32 0 = e7)
    (hed : ∀ i < 32, (rv X 32 2).getLsbD i = bitV V 96 i) :
    Go prof 256 gW gR (gPre prof) (gPost prof) L s₀ ra o X t := by
  have hl : gci.length = 896 := gci_length
  have j738 := g738 c hin hE
  have j721 : ∀ (V : Addr → Byte) X t, KeptW (ws 256 gW s₀) s₀ X →
      Agree (fp 256 gW gR (gPre prof) (gPost prof) L s₀) X.proc.mm.mem V → X.cpu.rip = (0x612cc0 : Addr).add 721 →
      GB s₀ p X.cpu.gpr → GM prof s₀ p V → bitV V 96 2 = true → rv X 32 0 = e7 →
      Go prof 256 gW gR (gPre prof) (gPost prof) L s₀ ra o X t := by
    intro V X t hK hA hr hb hm h2 hea
    refine c.s_test_ri32 hK hA hin (by omega) hr (gci_721 _) ?_
    rintro Y1 t1 hK1 hA1 ⟨hr1, hg1, hz1⟩
    refine c.s_jcc hK1 hA1 hin (by omega) hr1 (gci_726 _) (tgt := 738) rfl (by omega) (fun _ => ?_) fun hc => ?_
    · rintro Y2 t2 hK2 hA2 ⟨hr2, hg2⟩
      exact j738 _ Y2 t2 hK2 hA2 hr2 (by rw [hg2, hg1]; exact hb) hm
    have hbit : e7.getLsbD 30 = true := by
      rw [← hea]; exact bit_of_zf (m := 1073741824) (by decide) (by omega) (by rw [← hz1]; exact hc)
    rintro Y2 t2 hK2 hA2 ⟨hr2, hg2⟩
    refine c.s_or_rip_i32 hK2 hA2 hin (by omega) hr2 (gci_728 _) (g := cpuRgn.base.add 96) (by decide) (gF (by omega)) ?_
    rintro Y3 t3 hK3 hA3 ⟨hr3, hg3⟩
    exact j738 _ Y3 t3 hK3 hA3 hr3 (by rw [hg3, hg2, hg1]; exact hb)
      (hm.orB hE 256 h2 (by decide) (fun h => absurd h (by decide)) (fun h => absurd h (by decide))
        (fun _ => he7 30 (by omega) hbit)).1
  have j704 : ∀ (V : Addr → Byte) X t, KeptW (ws 256 gW s₀) s₀ X →
      Agree (fp 256 gW gR (gPre prof) (gPost prof) L s₀) X.proc.mm.mem V → X.cpu.rip = (0x612cc0 : Addr).add 704 →
      GB s₀ p X.cpu.gpr → GM prof s₀ p V → bitV V 96 2 = true → rv X 32 0 = e7 →
      Go prof 256 gW gR (gPre prof) (gPost prof) L s₀ ra o X t := by
    intro V X t hK hA hr hb hm h2 hea
    refine c.s_test_ri32 hK hA hin (by omega) hr (gci_704 _) ?_
    rintro Y1 t1 hK1 hA1 ⟨hr1, hg1, hz1⟩
    refine c.s_jcc hK1 hA1 hin (by omega) hr1 (gci_709 _) (tgt := 721) rfl (by omega) (fun _ => ?_) fun hc => ?_
    · rintro Y2 t2 hK2 hA2 ⟨hr2, hg2⟩
      exact j721 _ Y2 t2 hK2 hA2 hr2 (by rw [hg2, hg1]; exact hb) hm h2 (by rw [rv, hg2, hg1]; exact hea)
    have hbit : e7.getLsbD 17 = true := by
      rw [← hea]; exact bit_of_zf (m := 131072) (by decide) (by omega) (by rw [← hz1]; exact hc)
    rintro Y2 t2 hK2 hA2 ⟨hr2, hg2⟩
    refine c.s_or_rip_i32 hK2 hA2 hin (by omega) hr2 (gci_711 _) (g := cpuRgn.base.add 96) (by decide) (gF (by omega)) ?_
    rintro Y3 t3 hK3 hA3 ⟨hr3, hg3⟩
    have := hm.orB hE 128 h2 (by decide) (fun h => absurd h (by decide)) (fun _ => he7 17 (by omega) hbit)
      (fun h => absurd h (by decide))
    exact j721 _ Y3 t3 hK3 hA3 hr3 (by rw [hg3, hg2, hg1]; exact hb) this.1 this.2 (by rw [rv, hg3, hg2, hg1]; exact hea)
  have j693 : ∀ (V : Addr → Byte) X t, KeptW (ws 256 gW s₀) s₀ X →
      Agree (fp 256 gW gR (gPre prof) (gPost prof) L s₀) X.proc.mm.mem V → X.cpu.rip = (0x612cc0 : Addr).add 693 →
      GB s₀ p X.cpu.gpr → GM prof s₀ p V → bitV V 96 2 = true → rv X 32 0 = e7 →
      Go prof 256 gW gR (gPre prof) (gPost prof) L s₀ ra o X t := by
    intro V X t hK hA hr hb hm h2 hea
    refine c.s_test_rr32s hK hA hin (by omega) hr (gci_693 _) ?_
    rintro Y1 t1 hK1 hA1 ⟨hr1, hg1, hs1⟩
    refine c.s_jcc hK1 hA1 hin (by omega) hr1 (gci_695 _) (tgt := 704) rfl (by omega) (fun _ => ?_) fun hc => ?_
    · rintro Y2 t2 hK2 hA2 ⟨hr2, hg2⟩
      exact j704 _ Y2 t2 hK2 hA2 hr2 (by rw [hg2, hg1]; exact hb) hm h2 (by rw [rv, hg2, hg1]; exact hea)
    have hbit : e7.getLsbD 31 = true := by
      have h1 : (!Y1.cpu.rflags.sf) = false := hc
      have h1' : Y1.cpu.rflags.sf = true := by simpa using h1
      rw [hs1, hea, BitVec.and_self, BitVec.msb_eq_getLsbD_last] at h1'
      exact h1'
    rintro Y2 t2 hK2 hA2 ⟨hr2, hg2⟩
    refine c.s_or_rip_i32 hK2 hA2 hin (by omega) hr2 (gci_697 _) (g := cpuRgn.base.add 96) (by decide) (gF (by omega)) ?_
    rintro Y3 t3 hK3 hA3 ⟨hr3, hg3⟩
    have := hm.orB hE 64 h2 (by decide) (fun _ => he7 31 (by omega) hbit) (fun h => absurd h (by decide))
      (fun h => absurd h (by decide))
    exact j704 _ Y3 t3 hK3 hA3 hr3 (by rw [hg3, hg2, hg1]; exact hb) this.1 this.2 (by rw [rv, hg3, hg2, hg1]; exact hea)
  have j679 : ∀ (V : Addr → Byte) X t, KeptW (ws 256 gW s₀) s₀ X →
      Agree (fp 256 gW gR (gPre prof) (gPost prof) L s₀) X.proc.mm.mem V → X.cpu.rip = (0x612cc0 : Addr).add 679 →
      GB s₀ p X.cpu.gpr → GM prof s₀ p V → bitV V 96 2 = true → rv X 32 0 = e7 →
      Go prof 256 gW gR (gPre prof) (gPost prof) L s₀ ra o X t := by
    intro V X t hK hA hr hb hm h2 hea
    refine c.s_fll hK hA hin (by omega) hr fl_test_ri32 (gci_679 _) ?_
    rintro Y1 t1 hK1 hA1 ⟨hr1, hg1⟩
    refine c.s_jcc hK1 hA1 hin (by omega) hr1 (gci_684 _) (tgt := 693) rfl (by omega) (fun _ => ?_) fun _ => ?_
    · rintro Y2 t2 hK2 hA2 ⟨hr2, hg2⟩
      exact j693 _ Y2 t2 hK2 hA2 hr2 (by rw [hg2, hg1]; exact hb) hm h2 (by rw [rv, hg2, hg1]; exact hea)
    rintro Y2 t2 hK2 hA2 ⟨hr2, hg2⟩
    refine c.s_or_rip_i32 hK2 hA2 hin (by omega) hr2 (gci_686 _) (g := cpuRgn.base.add 96) (by decide) (gF (by omega)) ?_
    rintro Y3 t3 hK3 hA3 ⟨hr3, hg3⟩
    have := hm.orB hE 32 h2 (by decide) (fun h => absurd h (by decide)) (fun h => absurd h (by decide))
      (fun h => absurd h (by decide))
    exact j693 _ Y3 t3 hK3 hA3 hr3 (by rw [hg3, hg2, hg1]; exact hb) this.1 this.2 (by rw [rv, hg3, hg2, hg1]; exact hea)
  -- `663`: `AVX512PF_Usable` (bit 4) in `edx`, stored with the rest
  refine c.s_test_ri32 hK hA hin (by omega) hr (gci_663 _) ?_
  rintro Y1 t1 hK1 hA1 ⟨hr1, hg1, -⟩
  refine c.s_jcc hK1 hA1 hin (by omega) hr1 (gci_668 _) (tgt := 679) rfl (by omega) (fun _ => ?_) fun _ => ?_
  · rintro Y2 t2 hK2 hA2 ⟨hr2, hg2⟩
    exact j679 _ Y2 t2 hK2 hA2 hr2 (by rw [hg2, hg1]; exact hb) hm h2 (by rw [rv, hg2, hg1]; exact hea)
  rintro Y2 t2 hK2 hA2 ⟨hr2, hg2⟩
  refine c.s_or_ri32 hK2 hA2 hin (by omega) hr2 (gci_670 _) ?_
  rintro Y3 t3 hK3 hA3 ⟨hr3, hg3⟩
  refine c.s_mov_rip_r32 hK3 hA3 hin (by omega) hr3 (gci_673 _) (g := cpuRgn.base.add 96) (by decide) (gF (by omega)) ?_
  rintro Y4 t4 hK4 hA4 ⟨hr4, hg4⟩
  have hw : ∀ i < 32, (rv Y3 32 2).getLsbD i = (bitV V 96 i || (BitVec.ofNat 32 16).getLsbD i) := by
    intro i hi
    rw [rv_set (Or.inr (Or.inr (Or.inl rfl))) hg3, BitVec.getLsbD_or, rv, hg2, hg1, ← hed i hi]
  have hm4 := hm.cf hE (hm.1.st_f0_or _ _ hw (fun h => absurd h (by decide)) (fun h => absurd h (by decide))
      (fun h => absurd h (by decide)) (fun h => absurd h (by decide)) (fun h => absurd h (by decide))
      (fun h => absurd h (by decide)) (fun h => absurd h (by decide)) (fun h => absurd h (by decide)))
    (by decide) (by rw [toBytesLE_length]; decide)
  exact j679 _ Y4 t4 hK4 hA4 hr4 (by rw [hg4, hg3, hg2, hg1]; exact hb.set (r := 2) (by omega) _) hm4
    (by rw [bitV_f0_or _ hw (by omega), h2]; rfl)
    (by rw [show rv Y4 32 0 = rv Y3 32 0 by simp only [rv, hg4], rv_ne hg3,
          rv, hg2, hg1]; exact hea)

/-- AVX-512 (`602`): `XCR0` enables AVX's state, `eax` its low half. -/
theorem g602 (c : Call prof 256 gW gR (gPre prof) (gPost prof) 0x612cc0 L s₀ ra o) (hin : CodeIn L 0x612cc0 gci)
    {p : Addr} (hE : GEnv s₀ p) {x : BitVec 64} (hx : prof.xcr0 = some x) (en6 : prof.enabled xcr0Avx)
    {V : Addr → Byte} {X : State} {t : Nat} (hK : KeptW (ws 256 gW s₀) s₀ X)
    (hA : Agree (fp 256 gW gR (gPre prof) (gPost prof) L s₀) X.proc.mm.mem V) (hr : X.cpu.rip = (0x612cc0 : Addr).add 602)
    (hb : GB s₀ p X.cpu.gpr) (hm : GM prof s₀ p V) (hax : rv X 32 0 = x.setWidth 32) :
    Go prof 256 gW gR (gPre prof) (gPost prof) L s₀ ra o X t := by
  have hl : gci.length = 896 := gci_length
  refine c.s_and_ri32 hK hA hin (by omega) hr (gci_602 _) ?_
  rintro Y1 t1 hK1 hA1 ⟨hr1, hg1, -⟩
  refine c.s_cmp_ri32 hK1 hA1 hin (by omega) hr1 (gci_607 _) ?_
  rintro Y2 t2 hK2 hA2 ⟨hr2, hg2, hf2⟩
  have hb2 : GB s₀ p Y2.cpu.gpr := by rw [hg2, hg1]; exact hb.set (r := 0) (by omega) _
  refine c.s_jcc hK2 hA2 hin (by omega) hr2 (gci_612 _) (tgt := 225) rfl (by omega) (fun _ => ?_) fun hc => ?_
  · rintro Y3 t3 hK3 hA3 ⟨hr3, hg3⟩
    exact gXs c hin hE hK3 hA3 hr3 (by rw [hg3]; exact hb2) hm
  have e512 : prof.enabled xcr0Avx512 := by
    have h1 : (!Y2.cpu.rflags.zf) = false := hc
    have h1' : Y2.cpu.rflags.zf = true := by simpa using h1
    rw [hf2, subF_zf, rv_set (Or.inl rfl) hg1, hax] at h1'
    exact en512 hx en6 (of_decide_eq_true h1')
  rintro Y3 t3 hK3 hA3 ⟨hr3, hg3⟩
  -- leaf 7's `EBX` into `eax`: `AVX512F`?
  refine c.s_mov_r32_rip hK3 hA3 hin (by omega) hr3 (gci_618 _) (g := cpuRgn.base.add 20) (by decide) (gD c (by omega)) ?_
  rintro Y4 t4 hK4 hA4 ⟨hr4, hg4⟩
  have he7 : ∀ i < 32, (rdw V 20).getLsbD i = true → prof.reports 7 0 (·.ebx) i :=
    fun i hi h => hm.1.ebx7 i hi (by rw [← getLsbD_rd hi]; exact h)
  have hea4 : rv Y4 32 0 = rdw V 20 := rv_set (Or.inl rfl) hg4
  have hb4 : GB s₀ p Y4.cpu.gpr := by rw [hg4, hg3]; exact hb2.set (r := 0) (by omega) _
  refine c.s_test_ri32 hK4 hA4 hin (by omega) hr4 (gci_624 _) ?_
  rintro Y5 t5 hK5 hA5 ⟨hr5, hg5, hz5⟩
  refine c.s_jcc hK5 hA5 hin (by omega) hr5 (gci_629 _) (tgt := 225) rfl (by omega) (fun _ => ?_) fun hc => ?_
  · rintro Y6 t6 hK6 hA6 ⟨hr6, hg6⟩
    exact gXs c hin hE hK6 hA6 hr6 (by rw [hg6, hg5]; exact hb4) hm
  have r16 : prof.reports 7 0 (·.ebx) 16 :=
    he7 16 (by omega) (by rw [← hea4]; exact bit_of_zf (m := 65536) (by decide) (by omega) (by rw [← hz5]; exact hc))
  rintro Y6 t6 hK6 hA6 ⟨hr6, hg6⟩
  -- `edx = feature[0] | 4`, `ecx = feature[0] | 12`, by `AVX512ER`
  refine c.s_mov_r32_rip hK6 hA6 hin (by omega) hr6 (gci_635 _) (g := cpuRgn.base.add 96) (by decide) (gD c (by omega)) ?_
  rintro Y7 t7 hK7 hA7 ⟨hr7, hg7⟩
  refine c.s_mov_rr32 hK7 hA7 hin (by omega) hr7 (gci_641 _) ?_
  rintro Y8 t8 hK8 hA8 ⟨hr8, hg8⟩
  refine c.s_or_ri32 hK8 hA8 hin (by omega) hr8 (gci_643 _) ?_
  rintro Y9 t9 hK9 hA9 ⟨hr9, hg9⟩
  refine c.s_or_ri32 hK9 hA9 hin (by omega) hr9 (gci_646 _) ?_
  rintro Y10 t10 hK10 hA10 ⟨hr10, hg10⟩
  have d7 : rv Y7 32 2 = rdw V 96 := rv_set (Or.inr (Or.inr (Or.inl rfl))) hg7
  have c8 : rv Y8 32 1 = rdw V 96 := by rw [rv_set (Or.inr (Or.inl rfl)) hg8, d7]
  have d8 : rv Y8 32 2 = rdw V 96 := by rw [rv_ne hg8, d7]
  have d9 : rv Y9 32 2 = rdw V 96 ||| BitVec.ofNat 32 4 := by rw [rv_set (Or.inr (Or.inr (Or.inl rfl))) hg9, d8]
  have c9 : rv Y9 32 1 = rdw V 96 := by rw [rv_ne hg9, c8]
  have d10 : rv Y10 32 2 = rdw V 96 ||| BitVec.ofNat 32 4 := by
    rw [rv_ne hg10, d9]
  have c10 : rv Y10 32 1 = rdw V 96 ||| BitVec.ofNat 32 12 := by rw [rv_set (Or.inr (Or.inl rfl)) hg10, c9]
  have a10 : rv Y10 32 0 = rdw V 20 := by
    rw [rv_ne hg10, rv_ne hg9,
      rv_ne hg8, rv_ne hg7,
      rv, hg6, hg5]; exact hea4
  have hb10 : GB s₀ p Y10.cpu.gpr := by
    rw [hg10, hg9, hg8, hg7, hg6, hg5]
    exact (((hb4.set (r := 2) (by omega) _).set (r := 1) (by omega) _).set (r := 2) (by omega) _).set (r := 1) (by omega) _
  refine c.s_fll hK10 hA10 hin (by omega) hr10 fl_test_ri32 (gci_649 _) ?_
  rintro Y11 t11 hK11 hA11 ⟨hr11, hg11⟩
  refine c.s_cmov32 hK11 hA11 hin (by omega) hr11 (gci_654 _) ?_
  rintro Y12 t12 hK12 hA12 ⟨hr12, hg12⟩
  obtain ⟨imm, himm, d12⟩ : ∃ imm, (imm = 4 ∨ imm = 12) ∧ rv Y12 32 2 = rdw V 96 ||| BitVec.ofNat 32 imm := by
    rw [rv_set (Or.inr (Or.inr (Or.inl rfl))) hg12]
    have e1 : rv Y11 32 1 = rv Y10 32 1 := by simp only [rv, hg11]
    have e2 : rv Y11 32 2 = rv Y10 32 2 := by simp only [rv, hg11]
    cases Y11.cpu.rflags.cond 5
    · exact ⟨4, Or.inl rfl, by rw [if_neg (by decide), e2, d10]⟩
    · exact ⟨12, Or.inr rfl, by rw [if_pos rfl, e1, c10]⟩
  have hb12 : GB s₀ p Y12.cpu.gpr := by rw [hg12, hg11]; exact hb10.set (r := 2) (by omega) _
  have a12 : rv Y12 32 0 = rdw V 20 := by
    rw [rv_ne hg12, show rv Y11 32 0 = rv Y10 32 0 by simp only [rv, hg11], a10]
  refine c.s_mov_rip_r32 hK12 hA12 hin (by omega) hr12 (gci_657 _) (g := cpuRgn.base.add 96) (by decide) (gF (by omega)) ?_
  rw [d12]
  rintro Y13 t13 hK13 hA13 ⟨hr13, hg13⟩
  have hA := hm.orA hE himm r16 e512
  exact g663 c hin hE (rdw V 20) he7 hK13 hA13 hr13 (by rw [hg13]; exact hb12) hA.1 hA.2
    (by rw [show rv Y13 32 0 = rv Y12 32 0 by simp only [rv, hg13]]; exact a12)
    (fun i hi => by
      rw [show rv Y13 32 2 = rv Y12 32 2 by simp only [rv, hg13], d12, bitV_st_self _ (by omega) hi])

/-- Two stores into `cfR` that together keep `CInv`. -/
theorem GM.cf2 {p : Addr} {V : Addr → Byte} (h : GM prof s₀ p V) (hE : GEnv s₀ p) {g1 g2 : Addr}
    {bs1 bs2 : List Byte} (hc : CInv prof (Vst (Vst V g1 bs1) g2 bs2)) (hg1 : 0x7a4ae0 ≤ g1.toNat)
    (hb1 : g1.toNat + bs1.length ≤ 0x7a4b70) (hg2 : 0x7a4ae0 ≤ g2.toNat) (hb2 : g2.toNat + bs2.length ≤ 0x7a4b70) :
    GM prof s₀ p (Vst (Vst V g1 bs1) g2 bs2) := by
  have e2 := hE.tn (n := 248) (by omega)
  have hf := hE.fit
  have ha := hE.apart
  exact ⟨hc, by
    rw [map_Vst_apart (by omega) (by rw [e2]; omega) (by rw [e2]; omega),
      map_Vst_apart (by omega) (by rw [e2]; omega) (by rw [e2]; omega)]; exact h.2⟩

/-- `or [feature[0]], imm` for the bits that need `AVX_Usable` (17, 19) or none: `GM`, and still bit 0. -/
theorem GM.orV {p : Addr} {V : Addr → Byte} (h : GM prof s₀ p V) (hE : GEnv s₀ p) (imm : Nat) (h0 : bitV V 96 0 = true)
    (hz : ((BitVec.ofNat 32 imm).getLsbD 0 || (BitVec.ofNat 32 imm).getLsbD 1 || (BitVec.ofNat 32 imm).getLsbD 2 ||
      (BitVec.ofNat 32 imm).getLsbD 6 || (BitVec.ofNat 32 imm).getLsbD 7 || (BitVec.ofNat 32 imm).getLsbD 8) = false)
    (a17 : (BitVec.ofNat 32 imm).getLsbD 17 = true → prof.reports 1 0 (·.ecx) 12)
    (a19 : (BitVec.ofNat 32 imm).getLsbD 19 = true → prof.reports 7 0 (·.ecx) 9) :
    GM prof s₀ p (Vst V (cpuRgn.base.add 96) (toBytesLE (rdw V 96 ||| BitVec.ofNat 32 imm) 4)) ∧
      bitV (Vst V (cpuRgn.base.add 96) (toBytesLE (rdw V 96 ||| BitVec.ofNat 32 imm) 4)) 96 0 = true := by
  simp only [Bool.or_eq_false_iff] at hz
  obtain ⟨⟨⟨⟨⟨z0, z1⟩, z2⟩, z6⟩, z7⟩, z8⟩ := hz
  have t0 : (bitV V 96 0 || (BitVec.ofNat 32 imm).getLsbD 0) = true := by rw [h0]; rfl
  refine ⟨h.cf hE (h.1.st_f0_or _ _ (fun i hi => getLsbD_rd_or imm hi)
      (fun h => by rw [z0] at h; cases h) (fun h => by rw [z1] at h; cases h) (fun h => by rw [z2] at h; cases h)
      (fun h => by rw [z6] at h; cases h) (fun h => by rw [z7] at h; cases h) (fun h => by rw [z8] at h; cases h)
      (fun h => ⟨t0, a17 h⟩) (fun h => ⟨t0, a19 h⟩))
    (by decide) (by rw [toBytesLE_length]; decide), ?_⟩
  rw [bitV_f0_or _ (fun i hi => getLsbD_rd_or imm hi) (by omega), h0]; rfl

theorem bor13 (b : Bool) (i : Nat) :
    (b || (BitVec.ofNat 32 3).getLsbD i) = ((b || (BitVec.ofNat 32 1).getLsbD i) || (BitVec.ofNat 32 3).getLsbD i) := by
  cases b
  · by_cases h : i = 0
    · subst h; decide
    · have : (BitVec.ofNat 32 1).getLsbD i = false := by
        rw [BitVec.getLsbD_ofNat]
        cases i with
        | zero => exact absurd rfl h
        | succ n => simp [Nat.testBit_succ]
      rw [this]; rfl
  · rfl

/-- Bit `k` of `dh`, `dl`'s high neighbour, of a zero-extended word. -/
theorem getLsbD_h8 (v : BitVec 32) {k : Nat} (hk : k < 8) :
    (((v.setWidth 64) >>> 8).setWidth 8).getLsbD k = v.getLsbD (k + 8) := by
  simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, hk, decide_true, Bool.true_and]
  have : 8 + k < 64 := by omega
  rw [Nat.add_comm 8 k] at *
  simp [this]

/-- From `535`: `FMA` (bit 17), `VAES` (19) and the rest of `AVX`'s bits, `AVX_Usable` set; then `602`. -/
theorem g535 (c : Call prof 256 gW gR (gPre prof) (gPost prof) 0x612cc0 L s₀ ra o) (hin : CodeIn L 0x612cc0 gci)
    {p : Addr} (hE : GEnv s₀ p) {x : BitVec 64} (hx : prof.xcr0 = some x) (en6 : prof.enabled xcr0Avx)
    {V : Addr → Byte} {X : State} {t : Nat} (hK : KeptW (ws 256 gW s₀) s₀ X)
    (hA : Agree (fp 256 gW gR (gPre prof) (gPost prof) L s₀) X.proc.mm.mem V) (hr : X.cpu.rip = (0x612cc0 : Addr).add 535)
    (hb : GB s₀ p X.cpu.gpr) (hm : GM prof s₀ p V) (h0 : bitV V 96 0 = true) (hax : rv X 32 0 = x.setWidth 32)
    (hesi : ∀ i < 32, (rv X 32 6).getLsbD i = true → prof.reports 1 0 (·.ecx) i) :
    Go prof 256 gW gR (gPre prof) (gPost prof) L s₀ ra o X t := by
  have hl : gci.length = 896 := gci_length
  have j602 : ∀ (V : Addr → Byte) X t, KeptW (ws 256 gW s₀) s₀ X →
      Agree (fp 256 gW gR (gPre prof) (gPost prof) L s₀) X.proc.mm.mem V → X.cpu.rip = (0x612cc0 : Addr).add 602 →
      GB s₀ p X.cpu.gpr → GM prof s₀ p V → rv X 32 0 = x.setWidth 32 →
      Go prof 256 gW gR (gPre prof) (gPost prof) L s₀ ra o X t :=
    fun V X t hK hA hr hb hm hax => g602 c hin hE hx en6 hK hA hr hb hm hax
  have j589 : ∀ (V : Addr → Byte) X t, KeptW (ws 256 gW s₀) s₀ X →
      Agree (fp 256 gW gR (gPre prof) (gPost prof) L s₀) X.proc.mm.mem V → X.cpu.rip = (0x612cc0 : Addr).add 589 →
      GB s₀ p X.cpu.gpr → GM prof s₀ p V → rv X 32 0 = x.setWidth 32 →
      Go prof 256 gW gR (gPre prof) (gPost prof) L s₀ ra o X t := by
    intro V X t hK hA hr hb hm hax
    refine c.s_test_m8i_rip hK hA hin (by omega) hr (gci_589 _) (g := (cpuRgn.base.add 41).add 0) (by decide)
      (gD c (a := 41) (n := 1) (by omega) 0 (by omega)) ?_
    rintro Y1 t1 hK1 hA1 ⟨hr1, hg1, -⟩
    refine c.s_jcc hK1 hA1 hin (by omega) hr1 (gci_596 _) (tgt := 881) rfl (by omega) (fun _ => ?_) fun _ => ?_
    · rintro Y2 t2 hK2 hA2 ⟨hr2, hg2⟩
      refine c.s_or_rip_i32 hK2 hA2 hin (by omega) hr2 (gci_881 _) (g := cpuRgn.base.add 96) (by decide) (gF (by omega)) ?_
      rintro Y3 t3 hK3 hA3 ⟨hr3, hg3⟩
      refine c.s_jmp hK3 hA3 hin (by omega) hr3 (gci_891 _) (tgt := 602) rfl (by omega) ?_
      rintro Y4 t4 hK4 hA4 ⟨hr4, hg4⟩
      exact j602 _ Y4 t4 hK4 hA4 hr4 (by rw [hg4, hg3, hg2, hg1]; exact hb) (hm.orU hE 2097152 (by decide))
        (by rw [rv, hg4, hg3, hg2, hg1]; exact hax)
    rintro Y2 t2 hK2 hA2 ⟨hr2, hg2⟩
    exact j602 _ Y2 t2 hK2 hA2 hr2 (by rw [hg2, hg1]; exact hb) hm (by rw [rv, hg2, hg1]; exact hax)
  have j574 : ∀ (V : Addr → Byte) X t, KeptW (ws 256 gW s₀) s₀ X →
      Agree (fp 256 gW gR (gPre prof) (gPost prof) L s₀) X.proc.mm.mem V → X.cpu.rip = (0x612cc0 : Addr).add 574 →
      GB s₀ p X.cpu.gpr → GM prof s₀ p V → rv X 32 0 = x.setWidth 32 →
      Go prof 256 gW gR (gPre prof) (gPost prof) L s₀ ra o X t := by
    intro V X t hK hA hr hb hm hax
    refine c.s_wrl hK hA hin (by omega) hr wr_and_h8i (gci_574 _) ?_
    rintro Y1 t1 hK1 hA1 ⟨hr1, v1, hg1⟩
    have hb1 : GB s₀ p Y1.cpu.gpr := by rw [hg1]; exact hb.set (r := 2) (by omega) _
    have ha1 : rv Y1 32 0 = x.setWidth 32 := by
      rw [rv_ne hg1]; exact hax
    refine c.s_jcc hK1 hA1 hin (by omega) hr1 (gci_577 _) (tgt := 589) rfl (by omega) (fun _ => ?_) fun _ => ?_
    · rintro Y2 t2 hK2 hA2 ⟨hr2, hg2⟩
      exact j589 _ Y2 t2 hK2 hA2 hr2 (by rw [hg2]; exact hb1) hm (by rw [rv, hg2]; exact ha1)
    rintro Y2 t2 hK2 hA2 ⟨hr2, hg2⟩
    refine c.s_or_rip_i32 hK2 hA2 hin (by omega) hr2 (gci_579 _) (g := cpuRgn.base.add 96) (by decide) (gF (by omega)) ?_
    rintro Y3 t3 hK3 hA3 ⟨hr3, hg3⟩
    exact j589 _ Y3 t3 hK3 hA3 hr3 (by rw [hg3, hg2]; exact hb1) (hm.orU hE 1048576 (by decide))
      (by rw [rv, hg3, hg2]; exact ha1)
  have j553 : ∀ (V : Addr → Byte) X t, KeptW (ws 256 gW s₀) s₀ X →
      Agree (fp 256 gW gR (gPre prof) (gPost prof) L s₀) X.proc.mm.mem V → X.cpu.rip = (0x612cc0 : Addr).add 553 →
      GB s₀ p X.cpu.gpr → GM prof s₀ p V → bitV V 96 0 = true → rv X 32 0 = x.setWidth 32 →
      Go prof 256 gW gR (gPre prof) (gPost prof) L s₀ ra o X t := by
    intro V X t hK hA hr hb hm h0 hax
    refine c.s_mov_r32_rip hK hA hin (by omega) hr (gci_553 _) (g := cpuRgn.base.add 24) (by decide) (gD c (by omega)) ?_
    rintro Y1 t1 hK1 hA1 ⟨hr1, hg1⟩
    have hb1 : GB s₀ p Y1.cpu.gpr := by rw [hg1]; exact hb.set (r := 2) (by omega) _
    have ha1 : rv Y1 32 0 = x.setWidth 32 := by
      rw [rv_ne hg1]; exact hax
    have hdx : Y1.cpu.gpr.get (regOf 2) = (rdw V 24).setWidth 64 := by rw [hg1]; simp
    refine c.s_test_h8i hK1 hA1 hin (by omega) hr1 (gci_559 _) ?_
    rintro Y2 t2 hK2 hA2 ⟨hr2, hg2, hz2⟩
    refine c.s_jcc hK2 hA2 hin (by omega) hr2 (gci_562 _) (tgt := 574) rfl (by omega) (fun _ => ?_) fun hc => ?_
    · rintro Y3 t3 hK3 hA3 ⟨hr3, hg3⟩
      exact j574 _ Y3 t3 hK3 hA3 hr3 (by rw [hg3, hg2]; exact hb1) hm (by rw [rv, hg3, hg2]; exact ha1)
    have r9 : prof.reports 7 0 (·.ecx) 9 := by
      have h1 := bit_of_zf (w := 8) (m := 2) (k := 1) (by decide) (by omega) (by rw [← hz2]; exact hc)
      rw [hdx, getLsbD_h8 _ (by omega)] at h1
      exact hm.1.ecx7 9 (by omega) (by rw [← getLsbD_rd (by omega)]; exact h1)
    rintro Y3 t3 hK3 hA3 ⟨hr3, hg3⟩
    refine c.s_or_rip_i32 hK3 hA3 hin (by omega) hr3 (gci_564 _) (g := cpuRgn.base.add 96) (by decide) (gF (by omega)) ?_
    rintro Y4 t4 hK4 hA4 ⟨hr4, hg4⟩
    exact j574 _ Y4 t4 hK4 hA4 hr4 (by rw [hg4, hg3, hg2]; exact hb1)
      (hm.orV hE 524288 h0 (by decide) (fun h => absurd h (by decide)) fun _ => r9).1 (by rw [rv, hg4, hg3, hg2]; exact ha1)
  refine c.s_and_ri32 hK hA hin (by omega) hr (gci_535 _) ?_
  rintro Y1 t1 hK1 hA1 ⟨hr1, hg1, hz1⟩
  have hb1 : GB s₀ p Y1.cpu.gpr := by rw [hg1]; exact hb.set (r := 6) (by omega) _
  have ha1 : rv Y1 32 0 = x.setWidth 32 := by
    rw [rv_ne hg1]; exact hax
  refine c.s_jcc hK1 hA1 hin (by omega) hr1 (gci_541 _) (tgt := 553) rfl (by omega) (fun _ => ?_) fun hc => ?_
  · rintro Y2 t2 hK2 hA2 ⟨hr2, hg2⟩
    exact j553 _ Y2 t2 hK2 hA2 hr2 (by rw [hg2]; exact hb1) hm h0 (by rw [rv, hg2]; exact ha1)
  have r12 : prof.reports 1 0 (·.ecx) 12 :=
    hesi 12 (by omega) (bit_of_zf (m := 4096) (by decide) (by omega) (by rw [← hz1]; exact hc))
  rintro Y2 t2 hK2 hA2 ⟨hr2, hg2⟩
  refine c.s_or_rip_i32 hK2 hA2 hin (by omega) hr2 (gci_543 _) (g := cpuRgn.base.add 96) (by decide) (gF (by omega)) ?_
  rintro Y3 t3 hK3 hA3 ⟨hr3, hg3⟩
  have := hm.orV hE 131072 h0 (by decide) (fun _ => r12) (fun h => absurd h (by decide))
  exact j553 _ Y3 t3 hK3 hA3 hr3 (by rw [hg3, hg2]; exact hb1) this.1 this.2 (by rw [rv, hg3, hg2]; exact ha1)

/-- AVX (`482`): `XCR0` enables AVX's state, `eax` its low half, `esi` leaf 1's `ECX`. -/
theorem g482 (c : Call prof 256 gW gR (gPre prof) (gPost prof) 0x612cc0 L s₀ ra o) (hin : CodeIn L 0x612cc0 gci)
    {p : Addr} (hE : GEnv s₀ p) {x : BitVec 64} (hx : prof.xcr0 = some x) (en6 : prof.enabled xcr0Avx)
    {V : Addr → Byte} {X : State} {t : Nat} (hK : KeptW (ws 256 gW s₀) s₀ X)
    (hA : Agree (fp 256 gW gR (gPre prof) (gPost prof) L s₀) X.proc.mm.mem V) (hr : X.cpu.rip = (0x612cc0 : Addr).add 482)
    (hb : GB s₀ p X.cpu.gpr) (hm : GM prof s₀ p V) (hax : rv X 32 0 = x.setWidth 32)
    (hesi : ∀ i < 32, (rv X 32 6).getLsbD i = true → prof.reports 1 0 (·.ecx) i) :
    Go prof 256 gW gR (gPre prof) (gPost prof) L s₀ ra o X t := by
  have hl : gci.length = 896 := gci_length
  refine c.s_test_ri32 hK hA hin (by omega) hr (gci_482 _) ?_
  rintro Y1 t1 hK1 hA1 ⟨hr1, hg1, hz1⟩
  refine c.s_jcc hK1 hA1 hin (by omega) hr1 (gci_488 _) (tgt := 602) rfl (by omega) (fun _ => ?_) fun hc => ?_
  · rintro Y2 t2 hK2 hA2 ⟨hr2, hg2⟩
    exact g602 c hin hE hx en6 hK2 hA2 hr2 (by rw [hg2, hg1]; exact hb) hm (by rw [rv, hg2, hg1]; exact hax)
  have r28 : prof.reports 1 0 (·.ecx) 28 :=
    hesi 28 (by omega) (bit_of_zf (m := 268435456) (by decide) (by omega) (by rw [← hz1]; exact hc))
  rintro Y2 t2 hK2 hA2 ⟨hr2, hg2⟩
  -- `ecx = feature[0] | 1` (`AVX_Usable`), stored
  refine c.s_mov_r32_rip hK2 hA2 hin (by omega) hr2 (gci_490 _) (g := cpuRgn.base.add 96) (by decide) (gD c (by omega)) ?_
  rintro Y3 t3 hK3 hA3 ⟨hr3, hg3⟩
  refine c.s_mov_rr32 hK3 hA3 hin (by omega) hr3 (gci_496 _) ?_
  rintro Y4 t4 hK4 hA4 ⟨hr4, hg4⟩
  refine c.s_or_ri32 hK4 hA4 hin (by omega) hr4 (gci_498 _) ?_
  rintro Y5 t5 hK5 hA5 ⟨hr5, hg5⟩
  have d3 : rv Y3 32 2 = rdw V 96 := rv_set (Or.inr (Or.inr (Or.inl rfl))) hg3
  have c5 : rv Y5 32 1 = rdw V 96 ||| BitVec.ofNat 32 1 := by
    rw [rv_set (Or.inr (Or.inl rfl)) hg5, rv_set (Or.inr (Or.inl rfl)) hg4, d3]
  have d5 : rv Y5 32 2 = rdw V 96 := by rw [rv_ne hg5, rv_ne hg4, d3]
  have a5 : rv Y5 32 0 = x.setWidth 32 := by
    rw [rv_ne hg5, rv_ne hg4, rv_ne hg3, rv, hg2, hg1]; exact hax
  have s5 : rv Y5 32 6 = rv X 32 6 := by
    rw [rv_ne hg5, rv_ne hg4, rv_ne hg3, rv, hg2, hg1]
  have hb5 : GB s₀ p Y5.cpu.gpr := by
    rw [hg5, hg4, hg3, hg2, hg1]; exact ((hb.set (r := 2) (by omega) _).set (r := 1) (by omega) _).set (r := 1) (by omega) _
  refine c.s_mov_rip_r32 hK5 hA5 hin (by omega) hr5 (gci_501 _) (g := cpuRgn.base.add 96) (by decide) (gF (by omega)) ?_
  rw [c5]
  rintro Y6 t6 hK6 hA6 ⟨hr6, hg6⟩
  have hw1 : ∀ i < 32, (rdw V 96 ||| BitVec.ofNat 32 1).getLsbD i = (bitV V 96 i || (BitVec.ofNat 32 1).getLsbD i) :=
    fun i hi => getLsbD_rd_or 1 hi
  have hm6 := hm.cf hE (hm.1.st_f0_or _ _ hw1 (fun _ => ⟨r28, en6⟩) (fun h => absurd h (by decide))
      (fun h => absurd h (by decide)) (fun h => absurd h (by decide)) (fun h => absurd h (by decide))
      (fun h => absurd h (by decide)) (fun h => absurd h (by decide)) (fun h => absurd h (by decide)))
    (by decide) (by rw [toBytesLE_length]; decide)
  have h06 : bitV (Vst V (cpuRgn.base.add 96) (toBytesLE (rdw V 96 ||| BitVec.ofNat 32 1) 4)) 96 0 = true := by
    rw [bitV_f0_or _ hw1 (by omega)]; exact Bool.or_eq_true_iff.2 (Or.inr (by decide))
  have hb6 : GB s₀ p Y6.cpu.gpr := by rw [hg6]; exact hb5
  -- `AVX2`: leaf 7's `EBX` bit 5
  refine c.s_test_m8i_rip hK6 hA6 hin (by omega) hr6 (gci_507 _) (g := (cpuRgn.base.add 20).add 0) (by decide)
    (gD c (a := 20) (n := 1) (by omega) 0 (by omega)) ?_
  rintro Y7 t7 hK7 hA7 ⟨hr7, hg7, hz7⟩
  refine c.s_jcc hK7 hA7 hin (by omega) hr7 (gci_514 _) (tgt := 535) rfl (by omega) (fun _ => ?_) fun hc => ?_
  · rintro Y8 t8 hK8 hA8 ⟨hr8, hg8⟩
    exact g535 c hin hE hx en6 hK8 hA8 hr8 (by rw [hg8, hg7]; exact hb6) hm6 h06
      (by rw [rv, hg8, hg7, hg6]; exact a5) (by rw [show rv Y8 32 6 = rv Y5 32 6 by simp only [rv, hg8, hg7, hg6], s5]; exact hesi)
  have r5 : prof.reports 7 0 (·.ebx) 5 := by
    have h1 := bit_of_zf (w := 8) (m := 32) (k := 5) (by decide) (by omega) (by rw [← hz7]; exact hc)
    rw [rd1, addr_add_zero] at h1
    exact hm6.1.ebx7 5 (by omega) h1
  rintro Y8 t8 hK8 hA8 ⟨hr8, hg8⟩
  -- `feature[1] |= 256` (`AVX_Fast_Unaligned_Load`), then `feature[0] = old | 3` (`AVX2_Usable`)
  refine c.s_or_rip_i32 hK8 hA8 hin (by omega) hr8 (gci_516 _) (g := cpuRgn.base.add 100) (by decide) (gF (by omega)) ?_
  rintro Y9 t9 hK9 hA9 ⟨hr9, hg9⟩
  refine c.s_or_ri32 hK9 hA9 hin (by omega) hr9 (gci_526 _) ?_
  rintro Y10 t10 hK10 hA10 ⟨hr10, hg10⟩
  have d10 : rv Y10 32 2 = rdw V 96 ||| BitVec.ofNat 32 3 := by
    rw [rv_set (Or.inr (Or.inr (Or.inl rfl))) hg10, show rv Y9 32 2 = rv Y5 32 2 by simp only [rv, hg9, hg8, hg7, hg6], d5]
  refine c.s_mov_rip_r32 hK10 hA10 hin (by omega) hr10 (gci_529 _) (g := cpuRgn.base.add 96) (by decide) (gF (by omega)) ?_
  rw [d10]
  rintro Y11 t11 hK11 hA11 ⟨hr11, hg11⟩
  have hw0 := fun {i : Nat} (hi : i < 32) => bitV_f0_or (V := V) _ hw1 hi
  have hF := hm6.1.f.or (m0 := (BitVec.ofNat 32 3).getLsbD) (m1 := (BitVec.ofNat 32 256).getLsbD)
    (g0 := fun i => (bitV (Vst V (cpuRgn.base.add 96) (toBytesLE (rdw V 96 ||| BitVec.ofNat 32 1) 4)) 96 i ||
      (BitVec.ofNat 32 3).getLsbD i))
    (g1 := fun i => (bitV (Vst V (cpuRgn.base.add 96) (toBytesLE (rdw V 96 ||| BitVec.ofNat 32 1) 4)) 100 i ||
      (BitVec.ofNat 32 256).getLsbD i))
    (fun _ => rfl) (fun _ => rfl) (fun _ => ⟨r28, en6⟩) (fun _ => ⟨Bool.or_eq_true_iff.2 (Or.inr (by decide)), r5⟩)
    (fun h => absurd h (by decide)) (fun h => absurd h (by decide)) (fun h => absurd h (by decide))
    (fun h => absurd h (by decide)) (fun h => absurd h (by decide)) (fun h => absurd h (by decide))
    (fun _ => Bool.or_eq_true_iff.2 (Or.inr (by decide)))
  have hc11 := hm6.1.st_f1_f0 _ (rdw V 96 ||| BitVec.ofNat 32 3)
    (hF.congr (fun i hi => by rw [getLsbD_rd_or 3 hi, hw0 hi, bor13])
      (fun i hi => by rw [getLsbD_rd_or 256 hi]))
  have hm11 := hm6.cf2 hE hc11 (by decide) (by rw [toBytesLE_length]; decide) (by decide) (by rw [toBytesLE_length]; decide)
  have h011 : bitV (Vst (Vst (Vst V (cpuRgn.base.add 96) (toBytesLE (rdw V 96 ||| BitVec.ofNat 32 1) 4))
      (cpuRgn.base.add 100) (toBytesLE (rdw (Vst V (cpuRgn.base.add 96) (toBytesLE (rdw V 96 ||| BitVec.ofNat 32 1) 4)) 100
        ||| BitVec.ofNat 32 256) 4)) (cpuRgn.base.add 96) (toBytesLE (rdw V 96 ||| BitVec.ofNat 32 3) 4)) 96 0 = true := by
    rw [bitV_st_self _ (by omega) (by omega)]; exact (by decide : (BitVec.ofNat 32 3).getLsbD 0 = true) ▸ by
      rw [BitVec.getLsbD_or]; exact Bool.or_eq_true_iff.2 (Or.inr (by decide))
  exact g535 c hin hE hx en6 hK11 hA11 hr11 (by rw [hg11, hg10, hg9, hg8, hg7]; exact hb6.set (r := 2) (by omega) _) hm11 h011
    (by rw [rv, hg11, ← rv, rv_ne hg10, rv, hg9, hg8, hg7, hg6]; exact a5)
    (by rw [show rv Y11 32 6 = rv Y10 32 6 by simp only [rv, hg11], rv_ne hg10,
          show rv Y9 32 6 = rv Y5 32 6 by simp only [rv, hg9, hg8, hg7, hg6], s5]; exact hesi)

/-! ## `XGETBV` (`188`), leaf 7 and leaf `0DH` subleaf 1 (`101` to `182`) -/

/-- `OSXSAVE` (`188`): with it, `XCR0`; AVX's state enabled, `482`, else `225`. -/
theorem g188 (c : Call prof 256 gW gR (gPre prof) (gPost prof) 0x612cc0 L s₀ ra o) (hin : CodeIn L 0x612cc0 gci)
    (hpc : prof.Consistent) {p : Addr} (hE : GEnv s₀ p) : At prof L s₀ ra o p 188 := by
  intro V X t hK hA hr hb hm
  have hl : gci.length = 896 := gci_length
  refine c.s_mov_r32_rip hK hA hin (by omega) hr (gci_188 _) (g := cpuRgn.base.add 8) (by decide) (gD c (by omega)) ?_
  rintro Y1 t1 hK1 hA1 ⟨hr1, hg1⟩
  have hs1 : rv Y1 32 6 = rdw V 8 := rv_set (Or.inr (Or.inr (Or.inr rfl))) hg1
  have hesi : ∀ i < 32, (rdw V 8).getLsbD i = true → prof.reports 1 0 (·.ecx) i :=
    fun i hi h => hm.1.ecx1 i hi (by rw [← getLsbD_rd hi]; exact h)
  have hb1 : GB s₀ p Y1.cpu.gpr := by rw [hg1]; exact hb.set (r := 6) (by omega) _
  refine c.s_test_ri32 hK1 hA1 hin (by omega) hr1 (gci_194 _) ?_
  rintro Y2 t2 hK2 hA2 ⟨hr2, hg2, hz2⟩
  refine c.s_jcc hK2 hA2 hin (by omega) hr2 (gci_200 _) (tgt := 452) rfl (by omega) (fun _ => ?_) fun hc => ?_
  · rintro Y3 t3 hK3 hA3 ⟨hr3, hg3⟩
    exact gTail c hin hE hK3 hA3 hr3 (by rw [hg3, hg2]; exact hb1) hm
  have r27 : prof.reports 1 0 (·.ecx) 27 :=
    hesi 27 (by omega) (by rw [← hs1]; exact bit_of_zf (m := 134217728) (by decide) (by omega) (by rw [← hz2]; exact hc))
  obtain ⟨x, hx⟩ := Option.isSome_iff_exists.1 (hpc.osxsave r27)
  rintro Y3 t3 hK3 hA3 ⟨hr3, hg3⟩
  refine c.s_xor_rr32 hK3 hA3 hin (by omega) hr3 (gci_206 _) ?_
  rintro Y4 t4 hK4 hA4 ⟨hr4, hg4⟩
  refine c.s_xgetbv hK4 hA4 hin (by omega) hr4 (gci_208 _) hx (by rw [hg4]; simp) ?_
  rintro Y5 t5 hK5 hA5 ⟨hr5, hg5⟩
  have a5 : rv Y5 32 0 = x.setWidth 32 := by simp [rv, hg5]
  have s5 : rv Y5 32 6 = rdw V 8 := by
    rw [← hs1]; simp only [rv, hg5, hg4, hg3, hg2]; simp
  have hb5 : GB s₀ p Y5.cpu.gpr := by
    have := (hb1.set (r := 1) (by omega) ((rv Y3 32 1 ^^^ rv Y3 32 1).setWidth 64))
    rw [hg5, hg4, hg3, hg2]
    exact ⟨this.sp, this.rbp, this.r12, this.r13, this.r14, this.r15⟩
  refine c.s_mov_rr32 hK5 hA5 hin (by omega) hr5 (gci_211 _) ?_
  rintro Y6 t6 hK6 hA6 ⟨hr6, hg6⟩
  refine c.s_and_ri32 hK6 hA6 hin (by omega) hr6 (gci_213 _) ?_
  rintro Y7 t7 hK7 hA7 ⟨hr7, hg7, -⟩
  refine c.s_cmp_ri32 hK7 hA7 hin (by omega) hr7 (gci_216 _) ?_
  rintro Y8 t8 hK8 hA8 ⟨hr8, hg8, hf8⟩
  have hb8 : GB s₀ p Y8.cpu.gpr := by
    rw [hg8, hg7, hg6]; exact (hb5.set (r := 2) (by omega) _).set (r := 2) (by omega) _
  have d7 : rv Y7 32 2 = x.setWidth 32 &&& BitVec.ofNat 32 6 := by
    rw [rv_set (Or.inr (Or.inr (Or.inl rfl))) hg7, rv_set (Or.inr (Or.inr (Or.inl rfl))) hg6, a5]
  have a8 : rv Y8 32 0 = x.setWidth 32 := by rw [show rv Y8 32 0 = rv Y7 32 0 by simp only [rv, hg8], rv_ne hg7, rv_ne hg6, a5]
  have s8 : rv Y8 32 6 = rdw V 8 := by rw [show rv Y8 32 6 = rv Y7 32 6 by simp only [rv, hg8], rv_ne hg7, rv_ne hg6, s5]
  refine c.s_jcc hK8 hA8 hin (by omega) hr8 (gci_219 _) (tgt := 482) rfl (by omega) (fun hc => ?_) fun _ => ?_
  · have h6 : x.setWidth 32 &&& BitVec.ofNat 32 6 = BitVec.ofNat 32 6 := by
      have h1 : Y8.cpu.rflags.zf = true := hc
      rw [hf8, subF_zf, show rv Y7 32 2 = x.setWidth 32 &&& BitVec.ofNat 32 6 from d7] at h1
      exact of_decide_eq_true h1
    have en6 : prof.enabled xcr0Avx := by
      unfold Profile.enabled xcr0Avx; rw [hx]; exact enabled_of_low (by decide) h6
    rintro Y9 t9 hK9 hA9 ⟨hr9, hg9⟩
    exact g482 c hin hE hx en6 hK9 hA9 hr9 (by rw [hg9]; exact hb8) hm (by rw [rv, hg9]; exact a8)
      (by rw [show rv Y9 32 6 = rv Y8 32 6 by simp only [rv, hg9], s8]; exact hesi)
  rintro Y9 t9 hK9 hA9 ⟨hr9, hg9⟩
  exact gXs c hin hE hK9 hA9 hr9 (by rw [hg9]; exact hb8) hm

/-- A store into `cfR` apart from the watched words. -/
theorem GM.cfa {p : Addr} {V : Addr → Byte} (h : GM prof s₀ p V) (hE : GEnv s₀ p) {n m w : Nat}
    (v : BitVec w) (hm : n + m ≤ 0x90) (hw : ∀ a, Watched a → n + m ≤ a ∨ a + 4 ≤ n) :
    GM prof s₀ p (Vst V (cpuRgn.base.add n) (toBytesLE v m)) := by
  have e : (cpuRgn.base.add n).toNat = 0x7a4ae0 + n := by rw [cpuRgn_base, CpuFeat.tn (by rw [base_toNat]; omega), base_toNat]
  refine h.cf hE (h.1.st_apart _ _ (by rw [toBytesLE_length, e]; omega) fun a ha => ?_)
    (by rw [e]; omega) (by rw [toBytesLE_length, e]; omega)
  rw [toBytesLE_length, e]
  rcases hw a ha with h | h <;> omega

/-- A `CPUID` word into its watched word. -/
theorem GM.cpw {p : Addr} {V : Addr → Byte} (h : GM prof s₀ p V) (hE : GEnv s₀ p) {b : Nat} (w : BitVec 32)
    (hb : b = 8 ∨ b = 12 ∨ b = 20 ∨ b = 24)
    (hw : ∀ i < 32, w.getLsbD i = true → (b = 8 → prof.reports 1 0 (·.ecx) i) ∧ (b = 12 → prof.reports 1 0 (·.edx) i)
      ∧ (b = 20 → prof.reports 7 0 (·.ebx) i) ∧ (b = 24 → prof.reports 7 0 (·.ecx) i)) :
    GM prof s₀ p (Vst V (cpuRgn.base.add b) (toBytesLE w 4)) := by
  have e : (cpuRgn.base.add b).toNat = 0x7a4ae0 + b := by
    rw [cpuRgn_base, CpuFeat.tn (by rw [base_toNat]; omega), base_toNat]
  exact h.cf hE (h.1.st_cpuid w hb hw) (by rw [e]; omega) (by rw [toBytesLE_length, e]; omega)

theorem rep_of {leaf sub a b : BitVec 32} {cpu : Nat} (hc : cpu < max prof.cpus 1) (ha : a = leaf) (hb : b = sub)
    (r : CpuidResult → BitVec 32) {i : Nat} (h : (r (prof.cpuid cpu a b)).getLsbD i = true) : prof.reports leaf sub r i := by
  subst ha hb; exact ⟨cpu, hc, h⟩

/-- Leaf 7 subleaf 0 if the maximum leaf allows (`101`), leaf `0DH` subleaf 1 (`143`); then `188`. -/
theorem g101 (c : Call prof 256 gW gR (gPre prof) (gPost prof) 0x612cc0 L s₀ ra o) (hin : CodeIn L 0x612cc0 gci)
    (hpc : prof.Consistent) {p : Addr} (hE : GEnv s₀ p) : At prof L s₀ ra o p 101 := by
  have hl : gci.length = 896 := gci_length
  have j188 := g188 c hin hpc hE
  have j143 : At prof L s₀ ra o p 143 := by
    intro V X t hK hA hr hb hm
    refine c.s_cmp_m32i_rip hK hA hin (by omega) hr (gci_143 _) (g := cpuRgn.base.add 108) (by decide) (gD c (by omega)) ?_
    rintro Y1 t1 hK1 hA1 ⟨hr1, hg1⟩
    refine c.s_jcc hK1 hA1 hin (by omega) hr1 (gci_150 _) (tgt := 188) rfl (by omega) (fun _ => ?_) fun _ => ?_
    · rintro Y2 t2 hK2 hA2 ⟨hr2, hg2⟩
      exact j188 _ Y2 t2 hK2 hA2 hr2 (by rw [hg2, hg1]; exact hb) hm
    rintro Y2 t2 hK2 hA2 ⟨hr2, hg2⟩
    refine c.s_wrl hK2 hA2 hin (by omega) hr2 wr_mov_ri32 (gci_152 _) ?_
    rintro Y3 t3 hK3 hA3 ⟨hr3, v3, hg3⟩
    refine c.s_wrl hK3 hA3 hin (by omega) hr3 wr_mov_ri32 (gci_157 _) ?_
    rintro Y4 t4 hK4 hA4 ⟨hr4, v4, hg4⟩
    refine c.s_cpuid hK4 hA4 hin (by omega) hr4 (gci_162 _) ?_
    rintro Y5 t5 hK5 hA5 ⟨hr5, cpu, -, hg5⟩
    have hb5 : GB s₀ p Y5.cpu.gpr := by
      rw [hg5, hg4, hg3, hg2, hg1]; exact ((hb.set (r := 0) (by omega) _).set (r := 1) (by omega) _).cpuid _ _ _ _
    refine c.s_mov_rip_r32 hK5 hA5 hin (by omega) hr5 (gci_164 _) (g := cpuRgn.base.add 48) (by decide) (gF (by omega)) ?_
    rintro Y6 t6 hK6 hA6 ⟨hr6, hg6⟩
    have hm6 := hm.cfa hE (rv Y5 32 0) (n := 48) (m := 4) (by omega)
      (fun a ha => by rcases ha with rfl | rfl | rfl | rfl | rfl | rfl <;> omega)
    refine c.s_mov_rip_r32 hK6 hA6 hin (by omega) hr6 (gci_170 _) (g := cpuRgn.base.add 52) (by decide) (gF (by omega)) ?_
    rintro Y7 t7 hK7 hA7 ⟨hr7, hg7⟩
    have hm7 := hm6.cfa hE (rv Y6 32 3) (n := 52) (m := 4) (by omega)
      (fun a ha => by rcases ha with rfl | rfl | rfl | rfl | rfl | rfl <;> omega)
    refine c.s_mov_rip_r32 hK7 hA7 hin (by omega) hr7 (gci_176 _) (g := cpuRgn.base.add 56) (by decide) (gF (by omega)) ?_
    rintro Y8 t8 hK8 hA8 ⟨hr8, hg8⟩
    have hm8 := hm7.cfa hE (rv Y7 32 1) (n := 56) (m := 4) (by omega)
      (fun a ha => by rcases ha with rfl | rfl | rfl | rfl | rfl | rfl <;> omega)
    refine c.s_mov_rip_r32 hK8 hA8 hin (by omega) hr8 (gci_182 _) (g := cpuRgn.base.add 60) (by decide) (gF (by omega)) ?_
    rintro Y9 t9 hK9 hA9 ⟨hr9, hg9⟩
    exact j188 _ Y9 t9 hK9 hA9 hr9 (by rw [hg9, hg8, hg7, hg6]; exact hb5)
      (hm8.cfa hE (rv Y8 32 2) (n := 60) (m := 4) (by omega)
        (fun a ha => by rcases ha with rfl | rfl | rfl | rfl | rfl | rfl <;> omega))
  intro V X t hK hA hr hb hm
  refine c.s_cmp_m32i_rip hK hA hin (by omega) hr (gci_101 _) (g := cpuRgn.base.add 108) (by decide) (gD c (by omega)) ?_
  rintro Y1 t1 hK1 hA1 ⟨hr1, hg1⟩
  refine c.s_jcc hK1 hA1 hin (by omega) hr1 (gci_108 _) (tgt := 143) rfl (by omega) (fun _ => ?_) fun _ => ?_
  · rintro Y2 t2 hK2 hA2 ⟨hr2, hg2⟩
    exact j143 _ Y2 t2 hK2 hA2 hr2 (by rw [hg2, hg1]; exact hb) hm
  rintro Y2 t2 hK2 hA2 ⟨hr2, hg2⟩
  refine c.s_mov_ri32 hK2 hA2 hin (by omega) hr2 (gci_110 _) ?_
  rintro Y3 t3 hK3 hA3 ⟨hr3, hg3⟩
  refine c.s_xor_rr32 hK3 hA3 hin (by omega) hr3 (gci_115 _) ?_
  rintro Y4 t4 hK4 hA4 ⟨hr4, hg4⟩
  have e7 : Y4.cpu.gpr.rax.setWidth 32 = 7 := by rw [hg4, hg3]; simp
  have e0 : Y4.cpu.gpr.rcx.setWidth 32 = 0 := by rw [hg4]; simp
  refine c.s_cpuid hK4 hA4 hin (by omega) hr4 (gci_117 _) ?_
  rintro Y5 t5 hK5 hA5 ⟨hr5, cpu, hcpu, hg5⟩
  have hb5 : GB s₀ p Y5.cpu.gpr := by
    rw [hg5, hg4, hg3, hg2, hg1]; exact ((hb.set (r := 0) (by omega) _).set (r := 1) (by omega) _).cpuid _ _ _ _
  have rb : rv Y5 32 3 = (prof.cpuid cpu (Y4.cpu.gpr.rax.setWidth 32) (Y4.cpu.gpr.rcx.setWidth 32)).ebx := by
    simp only [rv, hg5]; simp
  have rc : rv Y5 32 1 = (prof.cpuid cpu (Y4.cpu.gpr.rax.setWidth 32) (Y4.cpu.gpr.rcx.setWidth 32)).ecx := by
    simp only [rv, hg5]; simp
  refine c.s_mov_rip_r32 hK5 hA5 hin (by omega) hr5 (gci_119 _) (g := cpuRgn.base.add 16) (by decide) (gF (by omega)) ?_
  rintro Y6 t6 hK6 hA6 ⟨hr6, hg6⟩
  have hm6 := hm.cfa hE (rv Y5 32 0) (n := 16) (m := 4) (by omega)
    (fun a ha => by rcases ha with rfl | rfl | rfl | rfl | rfl | rfl <;> omega)
  refine c.s_mov_rip_r32 hK6 hA6 hin (by omega) hr6 (gci_125 _) (g := cpuRgn.base.add 20) (by decide) (gF (by omega)) ?_
  rintro Y7 t7 hK7 hA7 ⟨hr7, hg7⟩
  have hm7 := hm6.cpw hE (rv Y6 32 3) (b := 20) (by omega) fun i _ hi =>
    ⟨fun h => absurd h (by decide), fun h => absurd h (by decide),
      fun _ => rep_of hcpu e7 e0 (·.ebx) (by rw [← rb, show rv Y5 32 3 = rv Y6 32 3 by simp only [rv, hg6]]; exact hi), fun h => absurd h (by decide)⟩
  refine c.s_mov_rip_r32 hK7 hA7 hin (by omega) hr7 (gci_131 _) (g := cpuRgn.base.add 24) (by decide) (gF (by omega)) ?_
  rintro Y8 t8 hK8 hA8 ⟨hr8, hg8⟩
  have hm8 := hm7.cpw hE (rv Y7 32 1) (b := 24) (by omega) fun i _ hi =>
    ⟨fun h => absurd h (by decide), fun h => absurd h (by decide), fun h => absurd h (by decide),
      fun _ => rep_of hcpu e7 e0 (·.ecx) (by rw [← rc, show rv Y5 32 1 = rv Y7 32 1 by simp only [rv, hg7, hg6]]; exact hi)⟩
  refine c.s_mov_rip_r32 hK8 hA8 hin (by omega) hr8 (gci_137 _) (g := cpuRgn.base.add 28) (by decide) (gF (by omega)) ?_
  rintro Y9 t9 hK9 hA9 ⟨hr9, hg9⟩
  exact j143 _ Y9 t9 hK9 hA9 hr9 (by rw [hg9, hg8, hg7, hg6]; exact hb5)
    (hm8.cfa hE (rv Y8 32 2) (n := 28) (m := 4) (by omega)
      (fun a ha => by rcases ha with rfl | rfl | rfl | rfl | rfl | rfl <;> omega))

/-! ## Leaf 1 and the four outputs (`0` to `95`, `461` to `477`) -/

/-- On the path with `family` not `NULL`: `GB`, and the four pointers in `rdi`, `rsi`, `r8`, `r9`. -/
structure EP (s₀ : State) (p : Addr) (g : Gprs) : Prop where
  b : GB s₀ p g
  rdi : g.rdi = s₀.cpu.gpr.rdi
  rsi : g.rsi = s₀.cpu.gpr.rsi
  r8 : g.r8 = s₀.cpu.gpr.rdx
  r9 : g.r9 = s₀.cpu.gpr.rcx

theorem EP.set {p : Addr} {g : Gprs} (h : EP s₀ p g) {r : Nat} (hr : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3) (v : BitVec 64) :
    EP s₀ p (g.set (regOf r) v) := by
  have hb := h.b.set (r := r) (by omega) v
  rcases hr with rfl | rfl | rfl | rfl <;> exact ⟨hb, h.rdi, h.rsi, h.r8, h.r9⟩

theorem EP.cpuid {p : Addr} {g : Gprs} (h : EP s₀ p g) (a b c d : BitVec 64) :
    EP s₀ p ((((g.set 0 a).set 3 b).set 1 c).set 2 d) := ⟨h.b.cpuid a b c d, h.rdi, h.rsi, h.r8, h.r9⟩

/-- An output: apart, fits, and the run's to store into. -/
def POk (s₀ : State) (q : Addr) : Prop :=
  PtrOk s₀ q ∧ q.toNat + 4 ≤ 2 ^ 64 ∧ ∀ i < 4, Foot (ws 256 gW s₀) (q.add i)

theorem eaD0 {X : State} {b : Nat} {q : Addr} (h : X.cpu.gpr.get (regOf b) = q) : eaD X b 0 = q := by
  show X.cpu.gpr.get (regOf b) + BitVec.ofNat 64 0 = q
  rw [h]; simp

theorem CInv.of_cpuOk {m : Memory} (h : CpuOk prof m) : CInv prof fun a => m.readByte a :=
  ⟨h.ecx1, h.edx1, h.ebx7, h.ecx7, ⟨h.avx, h.avx2, h.avx512f, h.avx512vl, h.avx512dq, h.avx512bw, h.fma, h.vaes,
    h.fastAvx⟩⟩

theorem rep1 (hpc : prof.Consistent) {a b : BitVec 32} {cpu : Nat} (hc : cpu < max prof.cpus 1) (ha : a = 1)
    (r : CpuidResult → BitVec 32) {i : Nat} (h : (r (prof.cpuid cpu a b)).getLsbD i = true) : prof.reports 1 0 r i := by
  subst ha; rw [hpc.noSubleaf cpu hc b] at h; exact ⟨cpu, hc, h⟩

/-- `family == 0x0f` (`461`): `family += (eax >> 20) & 0xff`, `model += extended_model`; then `101`. -/
theorem g461 (c : Call prof 256 gW gR (gPre prof) (gPost prof) 0x612cc0 L s₀ ra o) (hin : CodeIn L 0x612cc0 gci)
    (hpc : prof.Consistent) {p : Addr} (hE : GEnv s₀ p)
    (hP : POk s₀ s₀.cpu.gpr.rdi ∧ POk s₀ s₀.cpu.gpr.rsi ∧ POk s₀ s₀.cpu.gpr.rdx ∧ POk s₀ s₀.cpu.gpr.rcx)
    {V : Addr → Byte} {X : State} {t : Nat} (hK : KeptW (ws 256 gW s₀) s₀ X)
    (hA : Agree (fp 256 gW gR (gPre prof) (gPost prof) L s₀) X.proc.mm.mem V) (hr : X.cpu.rip = (0x612cc0 : Addr).add 461)
    (he : EP s₀ p X.cpu.gpr) (hm : GM prof s₀ p V) :
    Go prof 256 gW gR (gPre prof) (gPost prof) L s₀ ra o X t := by
  have hl : gci.length = 896 := gci_length
  obtain ⟨⟨pd, qd, fd⟩, ⟨ps, qs, fs⟩, ⟨p8, -, f8⟩, -⟩ := hP
  refine c.s_wrl hK hA hin (by omega) hr (wr_shr32 (by omega)) (gci_461 _) ?_
  rintro Y1 t1 hK1 hA1 ⟨hr1, v1, hg1⟩
  refine c.s_wrl hK1 hA1 hin (by omega) hr1 wr_movzx_rr8 (gci_464 _) ?_
  rintro Y2 t2 hK2 hA2 ⟨hr2, v2, hg2⟩
  refine c.s_wrl hK2 hA2 hin (by omega) hr2 wr_add_ri32 (gci_467 _) ?_
  rintro Y3 t3 hK3 hA3 ⟨hr3, v3, hg3⟩
  have he3 : EP s₀ p Y3.cpu.gpr := by
    rw [hg3, hg2, hg1]; exact ((he.set (r := 0) (by omega) _).set (r := 0) (by omega) _).set (r := 0) (by omega) _
  have e7 : eaD Y3 7 0 = s₀.cpu.gpr.rdi := eaD0 (by rw [get_r7, he3.rdi])
  refine c.s_mov_mr hK3 hA3 hin (by omega) hr3 (Or.inl rfl) (gci_470 _) (by rw [e7]; exact fd) ?_
  rw [e7]
  rintro Y4 t4 hK4 hA4 ⟨hr4, hg4⟩
  have hm4 := hm.ptr hE pd qd (rv Y3 32 0)
  have e8 : eaD Y4 8 0 = s₀.cpu.gpr.rdx := eaD0 (by rw [get_r8, hg4, he3.r8])
  refine c.s_mov_rm hK4 hA4 hin (by omega) hr4 (Or.inl rfl) (gci_472 _) (by rw [e8]; exact fun i hi => c.hws _ (f8 i hi)) ?_
  rintro Y5 t5 hK5 hA5 ⟨hr5, hg5⟩
  have he5 : EP s₀ p Y5.cpu.gpr := by rw [hg5, hg4]; exact he3.set (r := 0) (by omega) _
  have e6 : eaD Y5 6 0 = s₀.cpu.gpr.rsi := eaD0 (by rw [get_r6, he5.rsi])
  refine c.s_add_mr32 hK5 hA5 hin (by omega) hr5 (gci_475 _) (by rw [e6]; exact fs) ?_
  rw [e6]
  rintro Y6 t6 hK6 hA6 ⟨hr6, hg6⟩
  refine c.s_jmp hK6 hA6 hin (by omega) hr6 (gci_477 _) (tgt := 101) rfl (by omega) ?_
  rintro Y7 t7 hK7 hA7 ⟨hr7, hg7⟩
  exact g101 c hin hpc hE _ Y7 t7 hK7 hA7 hr7 (by rw [hg7, hg6]; exact he5.b) (hm4.ptr hE ps qs _)

/-- Leaf 1 (`19`): into `cpuid[1]` and, by fields of `EAX`, into the four outputs. -/
theorem g19 (c : Call prof 256 gW gR (gPre prof) (gPost prof) 0x612cc0 L s₀ ra o) (hin : CodeIn L 0x612cc0 gci)
    (hpc : prof.Consistent) {p : Addr} (hE : GEnv s₀ p)
    (hP : POk s₀ s₀.cpu.gpr.rdi ∧ POk s₀ s₀.cpu.gpr.rsi ∧ POk s₀ s₀.cpu.gpr.rdx ∧ POk s₀ s₀.cpu.gpr.rcx)
    {V : Addr → Byte} {X : State} {t : Nat} (hK : KeptW (ws 256 gW s₀) s₀ X)
    (hA : Agree (fp 256 gW gR (gPre prof) (gPost prof) L s₀) X.proc.mm.mem V) (hr : X.cpu.rip = (0x612cc0 : Addr).add 19)
    (he : EP s₀ p X.cpu.gpr) (hm : GM prof s₀ p V) :
    Go prof 256 gW gR (gPre prof) (gPost prof) L s₀ ra o X t := by
  have hl : gci.length = 896 := gci_length
  obtain ⟨⟨pd, qd, fd⟩, ⟨ps, qs, fs⟩, ⟨p8, q8, f8⟩, ⟨p9, q9, f9⟩⟩ := hP
  refine c.s_mov_ri32 hK hA hin (by omega) hr (gci_19 _) ?_
  rintro Y1 t1 hK1 hA1 ⟨hr1, hg1⟩
  have e1 : Y1.cpu.gpr.rax.setWidth 32 = 1 := by rw [hg1]; simp
  refine c.s_cpuid hK1 hA1 hin (by omega) hr1 (gci_24 _) ?_
  rintro Y2 t2 hK2 hA2 ⟨hr2, cpu, hcpu, hg2⟩
  have he2 : EP s₀ p Y2.cpu.gpr := by rw [hg2, hg1]; exact (he.set (r := 0) (by omega) _).cpuid _ _ _ _
  have rd : rv Y2 32 2 = (prof.cpuid cpu (Y1.cpu.gpr.rax.setWidth 32) (Y1.cpu.gpr.rcx.setWidth 32)).edx := by
    simp only [rv, hg2]; simp
  have rc : rv Y2 32 1 = (prof.cpuid cpu (Y1.cpu.gpr.rax.setWidth 32) (Y1.cpu.gpr.rcx.setWidth 32)).ecx := by
    simp only [rv, hg2]; simp
  -- `cpuid[1]`: `edx`, `ebx`, `ecx`, `eax`
  refine c.s_mov_rip_r32 hK2 hA2 hin (by omega) hr2 (gci_26 _) (g := cpuRgn.base.add 12) (by decide) (gF (by omega)) ?_
  rintro Y3 t3 hK3 hA3 ⟨hr3, hg3⟩
  have hm3 := hm.cpw hE (rv Y2 32 2) (b := 12) (by omega) fun i _ hi =>
    ⟨fun h => absurd h (by decide), fun _ => rep1 hpc hcpu e1 (·.edx) (by rw [← rd]; exact hi),
      fun h => absurd h (by decide), fun h => absurd h (by decide)⟩
  refine c.s_wrl hK3 hA3 hin (by omega) hr3 wr_mov_rr32 (gci_32 _) ?_
  rintro Y4 t4 hK4 hA4 ⟨hr4, v4, hg4⟩
  refine c.s_wrl hK4 hA4 hin (by omega) hr4 (wr_shr32 (by omega)) (gci_34 _) ?_
  rintro Y5 t5 hK5 hA5 ⟨hr5, v5, hg5⟩
  refine c.s_mov_rip_r32 hK5 hA5 hin (by omega) hr5 (gci_37 _) (g := cpuRgn.base.add 4) (by decide) (gF (by omega)) ?_
  rintro Y6 t6 hK6 hA6 ⟨hr6, hg6⟩
  have hm6 := hm3.cfa hE (rv Y5 32 3) (n := 4) (m := 4) (by omega)
    (fun a ha => by rcases ha with rfl | rfl | rfl | rfl | rfl | rfl <;> omega)
  refine c.s_wrl hK6 hA6 hin (by omega) hr6 wr_and_ri32 (gci_43 _) ?_
  rintro Y7 t7 hK7 hA7 ⟨hr7, v7, hg7⟩
  have rc7 : rv Y7 32 1 = rv Y2 32 1 := by
    rw [rv_ne hg7, show rv Y6 32 1 = rv Y5 32 1 by simp only [rv, hg6], rv_ne hg5, rv_ne hg4,
      show rv Y3 32 1 = rv Y2 32 1 by simp only [rv, hg3]]
  refine c.s_mov_rip_r32 hK7 hA7 hin (by omega) hr7 (gci_46 _) (g := cpuRgn.base.add 8) (by decide) (gF (by omega)) ?_
  rintro Y8 t8 hK8 hA8 ⟨hr8, hg8⟩
  have hm8 := hm6.cpw hE (rv Y7 32 1) (b := 8) (by omega) fun i _ hi =>
    ⟨fun _ => rep1 hpc hcpu e1 (·.ecx) (by rw [← rc, ← rc7]; exact hi), fun h => absurd h (by decide),
      fun h => absurd h (by decide), fun h => absurd h (by decide)⟩
  refine c.s_mov_rip_r32 hK8 hA8 hin (by omega) hr8 (gci_52 _) (g := cpuRgn.base.add 0) (by decide) (gF (by omega)) ?_
  rintro Y9 t9 hK9 hA9 ⟨hr9, hg9⟩
  have hm9 := hm8.cfa hE (rv Y8 32 0) (n := 0) (m := 4) (by omega)
    (fun a ha => by rcases ha with rfl | rfl | rfl | rfl | rfl | rfl <;> omega)
  have he9 : EP s₀ p Y9.cpu.gpr := by
    rw [hg9, hg8, hg7, hg6, hg5, hg4, hg3]
    exact ((he2.set (r := 2) (by omega) _).set (r := 2) (by omega) _).set (r := 2) (by omega) _
  -- `*family`, `*model`, `*extended_model`, `*stepping`
  have e7 : eaD Y9 7 0 = s₀.cpu.gpr.rdi := eaD0 (by rw [get_r7, he9.rdi])
  refine c.s_mov_mr hK9 hA9 hin (by omega) hr9 (Or.inl rfl) (gci_58 _) (by rw [e7]; exact fd) ?_
  rw [e7]
  rintro Y10 t10 hK10 hA10 ⟨hr10, hg10⟩
  have hm10 := hm9.ptr hE pd qd (rv Y9 32 2)
  refine c.s_wrl hK10 hA10 hin (by omega) hr10 wr_mov_rr32 (gci_60 _) ?_
  rintro Y11 t11 hK11 hA11 ⟨hr11, v11, hg11⟩
  refine c.s_wrl hK11 hA11 hin (by omega) hr11 (wr_shr32 (by omega)) (gci_62 _) ?_
  rintro Y12 t12 hK12 hA12 ⟨hr12, v12, hg12⟩
  refine c.s_wrl hK12 hA12 hin (by omega) hr12 wr_and_ri32 (gci_65 _) ?_
  rintro Y13 t13 hK13 hA13 ⟨hr13, v13, hg13⟩
  have he13 : EP s₀ p Y13.cpu.gpr := by
    rw [hg13, hg12, hg11, hg10]
    exact ((he9.set (r := 2) (by omega) _).set (r := 2) (by omega) _).set (r := 2) (by omega) _
  have e6 : eaD Y13 6 0 = s₀.cpu.gpr.rsi := eaD0 (by rw [get_r6, he13.rsi])
  refine c.s_mov_mr hK13 hA13 hin (by omega) hr13 (Or.inl rfl) (gci_68 _) (by rw [e6]; exact fs) ?_
  rw [e6]
  rintro Y14 t14 hK14 hA14 ⟨hr14, hg14⟩
  have hm14 := hm10.ptr hE ps qs (rv Y13 32 2)
  refine c.s_wrl hK14 hA14 hin (by omega) hr14 wr_mov_rr32 (gci_70 _) ?_
  rintro Y15 t15 hK15 hA15 ⟨hr15, v15, hg15⟩
  refine c.s_wrl hK15 hA15 hin (by omega) hr15 (wr_shr32 (by omega)) (gci_72 _) ?_
  rintro Y16 t16 hK16 hA16 ⟨hr16, v16, hg16⟩
  refine c.s_wrl hK16 hA16 hin (by omega) hr16 wr_and_ri32 (gci_75 _) ?_
  rintro Y17 t17 hK17 hA17 ⟨hr17, v17, hg17⟩
  have he17 : EP s₀ p Y17.cpu.gpr := by
    rw [hg17, hg16, hg15, hg14]
    exact ((he13.set (r := 2) (by omega) _).set (r := 2) (by omega) _).set (r := 2) (by omega) _
  have e8 : eaD Y17 8 0 = s₀.cpu.gpr.rdx := eaD0 (by rw [get_r8, he17.r8])
  refine c.s_mov_mr hK17 hA17 hin (by omega) hr17 (Or.inl rfl) (gci_81 _) (by rw [e8]; exact f8) ?_
  rw [e8]
  rintro Y18 t18 hK18 hA18 ⟨hr18, hg18⟩
  have hm18 := hm14.ptr hE p8 q8 (rv Y17 32 2)
  refine c.s_wrl hK18 hA18 hin (by omega) hr18 wr_mov_rr32 (gci_84 _) ?_
  rintro Y19 t19 hK19 hA19 ⟨hr19, v19, hg19⟩
  refine c.s_wrl hK19 hA19 hin (by omega) hr19 wr_and_ri32 (gci_86 _) ?_
  rintro Y20 t20 hK20 hA20 ⟨hr20, v20, hg20⟩
  have he20 : EP s₀ p Y20.cpu.gpr := by
    rw [hg20, hg19, hg18]
    exact (he17.set (r := 2) (by omega) _).set (r := 2) (by omega) _
  have e9 : eaD Y20 9 0 = s₀.cpu.gpr.rcx := eaD0 (by rw [get_r9, he20.r9])
  refine c.s_mov_mr hK20 hA20 hin (by omega) hr20 (Or.inl rfl) (gci_89 _) (by rw [e9]; exact f9) ?_
  rw [e9]
  rintro Y21 t21 hK21 hA21 ⟨hr21, hg21⟩
  have hm21 := hm18.ptr hE p9 q9 (rv Y20 32 2)
  have he21 : EP s₀ p Y21.cpu.gpr := by rw [hg21]; exact he20
  -- `family == 0x0f`?
  have e7' : eaD Y21 7 0 = s₀.cpu.gpr.rdi := eaD0 (by rw [get_r7, he21.rdi])
  refine c.s_cmp_m32i hK21 hA21 hin (by omega) hr21 (gci_92 _) (by rw [e7']; exact fun i hi => c.hws _ (fd i hi)) ?_
  rintro Y22 t22 hK22 hA22 ⟨hr22, hg22⟩
  have he22 : EP s₀ p Y22.cpu.gpr := by rw [hg22]; exact he21
  refine c.s_jcc hK22 hA22 hin (by omega) hr22 (gci_95 _) (tgt := 461) rfl (by omega) (fun _ => ?_) fun _ => ?_
  · rintro Y23 t23 hK23 hA23 ⟨hr23, hg23⟩
    exact g461 c hin hpc hE ⟨⟨pd, qd, fd⟩, ⟨ps, qs, fs⟩, ⟨p8, q8, f8⟩, ⟨p9, q9, f9⟩⟩ hK23 hA23 hr23
      (by rw [hg23]; exact he22) hm21
  rintro Y23 t23 hK23 hA23 ⟨hr23, hg23⟩
  exact g101 c hin hpc hE _ Y23 t23 hK23 hA23 hr23 (by rw [hg23]; exact he22.b) hm21

/-- The run from the call. -/
theorem gRun (hpc : prof.Consistent) (c : Call prof 256 gW gR (gPre prof) (gPost prof) 0x612cc0 L s₀ ra o)
    (hin : CodeIn L 0x612cc0 gci) (t : Nat) : Go prof 256 gW gR (gPre prof) (gPost prof) L s₀ ra o s₀ t := by
  have hl : gci.length = 896 := gci_length
  have hK0 : KeptW (ws 256 gW s₀) s₀ s₀ := KeptW.refl _ _
  have hA0 : Agree (fp 256 gW gR (gPre prof) (gPost prof) L s₀) s₀.proc.mm.mem
      (fun a => s₀.proc.mm.mem.readByte a) := fun _ _ => rfl
  obtain ⟨hpt0, hsf0⟩ := Call.frame_arith c.frame_fits
  obtain ⟨hcpu, hap, hptr⟩ := c.call.pre
  generalize hpd : s₀.cpu.gpr.rsp - BitVec.ofNat 64 256 = p at hpt0
  have hsp : s₀.cpu.gpr.rsp = Addr.add p 256 := by rw [← hpd]; exact sub_add_self _ _
  have hfit : p.toNat + 264 ≤ 2 ^ 64 := by omega
  have hE : GEnv s₀ p := ⟨hpd, hsp, hfit, by omega⟩
  -- `push rbx`
  refine c.s_push hK0 hA0 hin (by omega) (by rw [addr_add_zero]; exact c.call.shape.1) (gci_0 _)
    (fun i hi => by rw [hsp, add_sub8 p (m := 248) rfl, addr_add_add]; exact gS hE (by omega)) ?_
  rw [hsp, add_sub8 p (m := 248) rfl]
  rintro Y1 t1 hK1 hA1 ⟨hr1, hg1⟩
  have e248 := hE.tn (n := 248) (by omega)
  have hm1 : GM prof s₀ p (Vst (fun a => s₀.proc.mm.mem.readByte a) (Addr.add p 248) (toBytesLE (s₀.cpu.gpr.get (regOf 3)) 8)) :=
    ⟨(CInv.of_cpuOk hcpu).st_apart _ _ (by rw [toBytesLE_length, e248]; omega) (fun a ha => by
        rw [toBytesLE_length, e248]; have := hE.apart; rcases ha with rfl | rfl | rfl | rfl | rfl | rfl <;> omega),
      by rw [read_Vst_self (by rfl) _ (by rw [e248]; omega)]; rfl⟩
  -- `sub rsp, 136`
  refine c.s_sub_ri64 hK1 hA1 hin (by omega) hr1 (gci_1 _) ?_
  rintro Y2 t2 hK2 hA2 ⟨hr2, hg2⟩
  have hb2 : GB s₀ p Y2.cpu.gpr := by
    rw [hg2, hg1]
    exact ⟨add_sub_lit p (n := 248) (d := 136) (by omega), rfl, rfl, rfl, rfl, rfl⟩
  -- `test rdi, rdi`: `family` `NULL`?
  refine c.s_test_rr64 hK2 hA2 hin (by omega) hr2 (gci_8 _) ?_
  rintro Y3 t3 hK3 hA3 ⟨hr3, hg3, hz3⟩
  have hb3 : GB s₀ p Y3.cpu.gpr := by rw [hg3]; exact hb2
  refine c.s_jcc hK3 hA3 hin (by omega) hr3 (gci_11 _) (tgt := 101) rfl (by omega) (fun _ => ?_) fun hc => ?_
  · rintro Y4 t4 hK4 hA4 ⟨hr4, hg4⟩
    exact g101 c hin hpc hE _ Y4 t4 hK4 hA4 hr4 (by rw [hg4]; exact hb3) hm1
  have hnz : s₀.cpu.gpr.rdi ≠ 0 := by
    intro h0
    have hz : Y3.cpu.rflags.zf = true := by rw [hz3]; simp [rv, hg2, hg1, h0]
    have hc' : Y3.cpu.rflags.zf = false := hc
    rw [hz] at hc'; cases hc'
  obtain ⟨pd, ps, p8, p9⟩ := hptr hnz
  have pok : ∀ q, (⟨q, 4⟩ : Rgn) ∈ gW s₀ → PtrOk s₀ q → POk s₀ q := fun q hq hp => by
    have hf : q.toNat + 4 ≤ 2 ^ 64 := c.call.foot.fits ⟨q, 4⟩ (by simp [Footprint.data, Contract.footprint, fn, hq])
    exact ⟨hp, hf, fun i hi => ⟨⟨q, 4⟩, List.mem_cons_of_mem _ hq, mem_add_of_fits hi hf⟩⟩
  have hP : POk s₀ s₀.cpu.gpr.rdi ∧ POk s₀ s₀.cpu.gpr.rsi ∧ POk s₀ s₀.cpu.gpr.rdx ∧ POk s₀ s₀.cpu.gpr.rcx :=
    ⟨pok _ (by simp [gW, gPtrs]; exact Or.inr hnz) pd, pok _ (by simp [gW, gPtrs]; exact Or.inr hnz) ps, pok _ (by simp [gW, gPtrs]; exact Or.inr hnz) p8,
      pok _ (by simp [gW, gPtrs]; exact Or.inr hnz) p9⟩
  rintro Y4 t4 hK4 hA4 ⟨hr4, hg4⟩
  -- `mov r8, rdx`, `mov r9, rcx`
  refine c.s_mov_rr64 hK4 hA4 hin (by omega) hr4 (gci_13 _) ?_
  rintro Y5 t5 hK5 hA5 ⟨hr5, hg5⟩
  refine c.s_mov_rr64 hK5 hA5 hin (by omega) hr5 (gci_16 _) ?_
  rintro Y6 t6 hK6 hA6 ⟨hr6, hg6⟩
  have hb6 : GB s₀ p Y6.cpu.gpr := by
    rw [hg6, hg5, hg4]; exact (hb3.set (r := 8) (by omega) _).set (r := 9) (by omega) _
  exact g19 c hin hpc hE hP hK6 hA6 hr6
    ⟨hb6, by simp [hg6, hg5, hg4, hg3, hg2, hg1], by simp [hg6, hg5, hg4, hg3, hg2, hg1],
      by simp [hg6, hg5, hg4, hg3, hg2, hg1], by simp [hg6, hg5, hg4, hg3, hg2, hg1]⟩ hm1

/-- `get_common_indices`, at `0x612cc0` in `7zzs`: on a consistent profile, every call returns, keeping `CpuOk`. -/
theorem getCommonIndices (prof : Profile) (hpc : prof.Consistent) {L : List (Addr × List Byte)}
    (hin : CodeIn L 0x612cc0 gci) : ImplementsCall prof 0x612cc0 L (gciC prof) := by
  intro s₀ ra hcall
  have hfr := Call.frame_arith (k := 256) (s := s₀)
    (hcall.foot.fits (frame s₀ 256) (by simp [Footprint.data, Contract.footprint, fn]))
  have hslot : ∀ i < 8, ¬ Foot (gW s₀) (Addr.add s₀.cpu.gpr.rsp i) := by
    rintro i hi ⟨r, hr, hm⟩
    obtain ⟨-, hap, hptr⟩ := hcall.pre
    have e1 : (0x7a4ae0 : Addr).toNat = 0x7a4ae0 := rfl
    have hs := toNat_add_of_fits hi hfr.2
    simp only [gW, List.mem_cons] at hr
    rcases hr with rfl | hr
    · simp only [cfR, Rgn.Mem, hs, e1] at hm; omega
    · by_cases h0 : s₀.cpu.gpr.rdi = 0
      · simp [h0] at hr
      · simp only [h0, if_false, gPtrs, List.mem_cons, List.not_mem_nil, or_false] at hr
        obtain ⟨pd, ps, p8, p9⟩ := hptr h0
        rcases hr with rfl | rfl | rfl | rfl <;>
          first
          | (obtain ⟨-, h2⟩ := pd; simp only [Rgn.Mem, hs] at hm; omega)
          | (obtain ⟨-, h2⟩ := ps; simp only [Rgn.Mem, hs] at hm; omega)
          | (obtain ⟨-, h2⟩ := p8; simp only [Rgn.Mem, hs] at hm; omega)
          | (obtain ⟨-, h2⟩ := p9; simp only [Rgn.Mem, hs] at hm; omega)
  exact reachOrEndsIn_of_runsFrom fun o ho t => gRun hpc (Call.of hcall ho hslot) hin t

/-- `getCommonIndices`, by the contract `fnK` a caller's run goes on with (`Seg.s_callK`). -/
theorem getCommonIndicesK (prof : Profile) (hpc : prof.Consistent) {L : List (Addr × List Byte)}
    (hin : CodeIn L 0x612cc0 gci) :
    ImplementsCall prof 0x612cc0 L (fnK 256 gW gR (gPre prof) fun _ Y => CpuOk prof Y.proc.mm.mem) :=
  getCommonIndices prof hpc hin

end FV7z.CpuFeat
