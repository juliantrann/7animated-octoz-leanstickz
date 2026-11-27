import FV7z.Stl.Vc1
/-!
# `____strtoul_l_internal`: the straight pieces, part 2 (PLAN.md §M, M1)

The cut points with nested tests (names as in `Stl/Vc1.lean`):

- `vc_133`: after the sign. A `0` with base 0 or 16: `toupper` of the next byte `X` (`CU[c] = 88`) gives base 16
  past the `0x` (to 171), else base 16 to 604, base 0 to octal (223, `[rsp + 18]` the cut digit); no `0`: base 10 or
  0 to 150, else to 171 with `eax = base - 2`. The byte after the `0` (and after the `x`) is read only on its way.
- `vc_171`: `cdqe`, the base's cut value and cut digit (`[rsp + 18]`); no byte to 745, else 216.
- `vc_604`: a `0` without `x`: base 10 to 216, else to 223 (`ecx = '0'`), `[rsp + 18]` the cut digit.
- `vc_390`: overflow (`r9d ≠ 0`): `errno = ERANGE`, to 448; else the sign's `cmov` (on `rax` alone: `ite_mk0`), the
  pops, to the `ret` (429).
- `vc_296z`: the digit loop at the NUL (`CB[0]` not a letter), to 368.
- `vc_748z`, `vc_748s`, `vc_748l`: no digits. `E = 0`: to 927. Else (`k = rdi - r13`) `k ≤ 1` (`jle`) to 790;
  `k ≥ 2`: a `0x` before (`CU[p[k - 1]] = 88`, `p[k - 2] = '0'`) stores `rdi - 1` at `E`, to 927; else 790.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
namespace FV7z.Stl

variable {F : Footprint} {Wl : List Rgn}

set_option maxHeartbeats 4000000 in
/-- After the sign: the base and the `0x` prefix. -/
theorem vc_133 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} (hr : g.r14 = 0#64)
    (f1 : BitVec.setWidth 8 g.rcx = 48#8 → ∀ i < 1, Foot F.data (Addr.add (g.rbx + 1#64) i))
    (fU : ∀ i < 8, Foot F.data (Addr.add 7935192#64 i))
    (fUe : ∀ i < 4, Foot F.data (Addr.add (Cu V + BitVec.signExtend 64 (rb V (g.rbx + 1#64)) * 4#64) i))
    (f2 : BitVec.setWidth 8 g.rcx = 48#8 →
      rdd(V, Cu V + BitVec.signExtend 64 (rb V (g.rbx + 1#64)) * 4#64) = 88#32 →
      ∀ i < 1, Foot F.data (Addr.add (g.rbx + 2#64) i))
    (fA : ∀ i < 1, Foot F.data (Addr.add 7353702#64 i)) (fB : ∀ i < 8, Foot F.data (Addr.add 7353808#64 i))
    (w18 : ∀ i < 1, Foot Wl (Addr.add (g.rsp + 18#64) i)) :
    W_133 fb F Wl (fun j g' _ V' => g'.rsp = g.rsp ∧ g'.r13 = g.r13 ∧ g'.r14 = 0#64 ∧
      ((j = 171 ∧ V' = V ∧ g'.rax = 14#64 ∧ g'.rbx = g.rbx + 2#64 ∧
          g'.rcx = BitVec.setWidth 64 (BitVec.setWidth 32 (rb V (g.rbx + 2#64))) ∧ g'.rbp = 0#64 ∧
          BitVec.setWidth 8 g.rcx = 48#8 ∧
          rdd(V, Cu V + BitVec.signExtend 64 (rb V (g.rbx + 1#64)) * 4#64) = 88#32) ∨
       (j = 604 ∧ V' = V ∧ g'.rbx = g.rbx ∧ g'.rdx = g.rdx ∧ BitVec.setWidth 8 g.rcx = 48#8) ∨
       (j = 223 ∧ V' = Vst V (g.rsp + 18#64)
          (toBytesLE (BitVec.setWidth 8 (BitVec.setWidth 64 (BitVec.setWidth 32 (rb V 7353702#64)))) 1) ∧
          g'.rbx = g.rbx ∧ g'.rcx = 48#64 ∧ g'.rbp = 0#64 ∧ g'.r10 = Cu V ∧ BitVec.setWidth 8 g.rcx = 48#8) ∨
       (j = 150 ∧ V' = V ∧ g' = g) ∨
       (j = 171 ∧ V' = V ∧ g'.rax = BitVec.setWidth 64 (BitVec.setWidth 32 (g.rdx + 18446744073709551614#64)) ∧
          g'.rbx = g.rbx ∧ g'.rcx = g.rcx ∧ g'.rbp = 0#64))) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [Cu, rb] at hr f1 fU fUe f2 fA fB w18 ⊢
  stlx +contextual [W_133, W_142, W_464, W_473, W_592, W_808, W_827, W_835, W_881, o8, o9, o36, o37, o39, o47,
    o48, o49, hr, f1, fU, fUe, f2, fA, fB, w18]

set_option maxHeartbeats 4000000 in
/-- `cdqe`, the cut value and digit of the base; no byte to 745, else 216. -/
theorem vc_171 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (fT1 : ∀ i < 8, Foot F.data (Addr.add (7353760#64 + BitVec.signExtend 64 (BitVec.setWidth 32 g.rax) * 8#64) i))
    (fT2 : ∀ i < 1, Foot F.data (Addr.add (7353696#64 + BitVec.signExtend 64 (BitVec.setWidth 32 g.rax)) i))
    (w18 : ∀ i < 1, Foot Wl (Addr.add (g.rsp + 18#64) i)) :
    W_171 fb F Wl (fun j g' _ V' => V' = Vst V (g.rsp + 18#64) (toBytesLE (BitVec.setWidth 8 (BitVec.setWidth 64
        (BitVec.setWidth 32 (rb V (7353696#64 + BitVec.signExtend 64 (BitVec.setWidth 32 g.rax)))))) 1) ∧
      g'.rsp = g.rsp ∧ g'.rbx = g.rbx ∧ g'.rcx = g.rcx ∧ g'.rbp = g.rbp ∧ g'.r13 = g.r13 ∧ g'.r14 = g.r14 ∧
      (j = 745 ∨ (j = 216 ∧ (BitVec.setWidth 8 g.rcx &&& BitVec.setWidth 8 g.rcx == 0) = false))) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [rb] at fT1 fT2 w18 ⊢
  stlx +contextual [W_171, W_207, o12, o13, fT1, fT2, w18]

set_option maxHeartbeats 4000000 in
/-- A `0` without `x`: base 10 to 216, else 223 with `ecx = '0'`. -/
theorem vc_604 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} (hr : g.r14 = 0#64)
    (fA : ∀ i < 1, Foot F.data (Addr.add 7353704#64 i)) (fB : ∀ i < 8, Foot F.data (Addr.add 7353824#64 i))
    (w18 : ∀ i < 1, Foot Wl (Addr.add (g.rsp + 18#64) i)) (fU : ∀ i < 8, Foot F.data (Addr.add 7935192#64 i))
    (fT1 : ∀ i < 8, Foot F.data (Addr.add
      (7353760#64 + BitVec.signExtend 64 (BitVec.setWidth 32 (g.rdx + 18446744073709551614#64)) * 8#64) i))
    (fT2 : ∀ i < 1, Foot F.data (Addr.add
      (7353696#64 + BitVec.signExtend 64 (BitVec.setWidth 32 (g.rdx + 18446744073709551614#64))) i)) :
    W_604 fb F Wl (fun j g' _ V' => g'.rsp = g.rsp ∧ g'.rbx = g.rbx ∧ g'.r13 = g.r13 ∧ g'.r14 = 0#64 ∧
      g'.rbp = 0#64 ∧ g'.rcx = 48#64 ∧
      ((j = 216 ∧ V' = Vst V (g.rsp + 18#64)
          (toBytesLE (BitVec.setWidth 8 (BitVec.setWidth 64 (BitVec.setWidth 32 (rb V 7353704#64)))) 1)) ∨
       (j = 223 ∧ V' = Vst V (g.rsp + 18#64) (toBytesLE (BitVec.setWidth 8 (BitVec.setWidth 64 (BitVec.setWidth 32
          (rb V (7353696#64 + BitVec.signExtend 64 (BitVec.setWidth 32 (g.rdx + 18446744073709551614#64))))))) 1) ∧
          g'.r10 = Cu V))) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [Cu, rb] at hr fA fB w18 fU fT1 fT2 ⊢
  stlx +contextual [W_604, W_613, W_934, W_939, o36, o40, o10, o53, hr, fA, fB, w18, fU, fT1, fT2]

set_option maxHeartbeats 4000000 in
/-- Overflow: `errno = ERANGE`, to 448; else the sign's `cmov`, the pops, to the `ret` (429). -/
theorem vc_390 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (ef : ∀ i < 4, Foot Wl (Addr.add (fb + 18446744073709551544#64) i))
    (fS : ∀ i < 4, Foot F.data (Addr.add (g.rsp + 20#64) i))
    (p0 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 40#64) i))
    (p1 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 40#64 + 8) i))
    (p2 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 40#64 + 8 + 8) i))
    (p3 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 40#64 + 8 + 8 + 8) i))
    (p4 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 40#64 + 8 + 8 + 8 + 8) i))
    (p5 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 40#64 + 8 + 8 + 8 + 8 + 8) i)) :
    W_390 fb F Wl (fun j g' _ V' =>
      (j = 448 ∧ V' = Vst V (fb + 18446744073709551544#64) (toBytesLE (34#32) 4) ∧ g'.rsp = g.rsp) ∨
      (j = 429 ∧ V' = V ∧ g'.rsp = g.rsp + 40#64 + 8 + 8 + 8 + 8 + 8 + 8 ∧
        g'.rbx = rdq(V, g.rsp + 40#64) ∧ g'.rbp = rdq(V, g.rsp + 40#64 + 8) ∧
        g'.r12 = rdq(V, g.rsp + 40#64 + 8 + 8) ∧ g'.r13 = rdq(V, g.rsp + 40#64 + 8 + 8 + 8) ∧
        g'.r14 = rdq(V, g.rsp + 40#64 + 8 + 8 + 8 + 8) ∧ g'.r15 = rdq(V, g.rsp + 40#64 + 8 + 8 + 8 + 8 + 8)))
      g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at ef fS p0 p1 p2 p3 p4 p5 ⊢
  stlx +contextual [W_390, W_399, W_1194, o32, o33, o54, ef, fS, p0, p1, p2, p3, p4, p5]

set_option maxHeartbeats 2000000 in
/-- No digits, `E = 0`: to 927. -/
theorem vc_748z {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} (hz : rdq(V, g.rsp + 8#64) = 0#64)
    (fE : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8#64) i)) :
    W_748 fb F Wl (fun j g' _ V' => j = 927 ∧ V' = V ∧ g'.rsp = g.rsp) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hz fE ⊢
  stlx +contextual [W_748, W_760, W_772, W_909, W_915, o43, o44, o45, o50, o51, hz, fE]

set_option maxHeartbeats 2000000 in
/-- No digits, `E ≠ 0`, `rdi - r13 ≤ 1`: to 790. -/
theorem vc_748s {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} (hn : ¬ rdq(V, g.rsp + 8#64) = 0#64)
    (fE : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8#64) i))
    (hk : ∀ fl : Rflags, (subF fl (g.rdi - g.r13) 1#64).cond 14 = true) :
    W_748 fb F Wl (fun j g' _ V' => j = 790 ∧ V' = V ∧ g'.rsp = g.rsp ∧ g'.r13 = g.r13) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hn fE hk ⊢
  stlx +contextual [W_748, W_760, W_772, W_909, W_915, o43, o44, o45, o50, o51, hn, fE, hk]

set_option maxHeartbeats 4000000 in
/-- No digits, `E ≠ 0`, `rdi - r13 ≥ 2`: after `0x`, `*E = rdi - 1`, to 927; else 790. -/
theorem vc_748l {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} (hn : ¬ rdq(V, g.rsp + 8#64) = 0#64)
    (fE : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8#64) i))
    (wE : ∀ i < 8, Foot Wl (Addr.add (rdq(V, g.rsp + 8#64)) i))
    (hk : ∀ fl : Rflags, (subF fl (g.rdi - g.r13) 1#64).cond 14 = false)
    (fm1 : ∀ i < 1, Foot F.data (Addr.add (g.rdi + 18446744073709551615#64) i))
    (fm2 : ∀ i < 1, Foot F.data (Addr.add (g.rdi + 18446744073709551614#64) i))
    (fU : ∀ i < 8, Foot F.data (Addr.add 7935192#64 i))
    (fUe : ∀ i < 4, Foot F.data
      (Addr.add (Cu V + BitVec.signExtend 64 (rb V (g.rdi + 18446744073709551615#64)) * 4#64) i)) :
    W_748 fb F Wl (fun j g' _ V' => (j = 790 ∧ V' = V ∧ g'.rsp = g.rsp ∧ g'.r13 = g.r13) ∨
      (j = 927 ∧ V' = Vst V (rdq(V, g.rsp + 8#64)) (toBytesLE (g.rdi - 1#64) 8) ∧ g'.rsp = g.rsp)) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [Cu, rb] at hn fE wE hk fm1 fm2 fU fUe ⊢
  stlx +contextual [W_748, W_760, W_772, W_909, W_915, o43, o44, o45, o50, o51, hn, fE, wE, hk, fm1, fm2, fU,
    fUe]

set_option maxHeartbeats 2000000 in
/-- The digit loop at the NUL (`rcx = 0`, and `CB[0]` says not a letter): to 368. -/
theorem vc_296z {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} (hz : g.rcx = 0#64) (hbp : g.rbp = 0#64)
    (fC : ∀ i < 1, Foot F.data (Addr.add (g.r11 + 1#64) i)) (ha : (rb V (g.r11 + 1#64) &&& 4#8 == 0) = true) :
    W_296 fb F Wl (fun j g' _ V' => j = 368 ∧ V' = V ∧ Lg g g' ∧ g'.rdi = g.rdi) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [Lg, rb] at hz hbp fC ha ⊢
  subst hz
  stlx +contextual [W_296, W_305, W_314, W_317, W_325, o20, o21, o22, o23, o24, BitVec.zero_mul, BitVec.add_zero,
    hbp, fC, ha]

end FV7z.Stl
