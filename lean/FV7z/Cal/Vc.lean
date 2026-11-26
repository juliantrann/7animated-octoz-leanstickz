import FV7z.Cal.Steps
import FV7z.Mxi.Holds
import FV7z.Prepare.Sub
import FV7z.Sdp.Holds
/-!
# `__libc_calloc`: the straight pieces (PLAN.md §M, M1)

The pieces of `__libc_calloc (n, m)` (glibc 2.31, at `0x634a60`) on its way when the hook is null, the tcache made,
one thread (`fs:0x18` 0), `perturb_byte` 0 and `_int_malloc` gives a chunk of the main arena, not mmapped:

- `vc_0`: the four pushes, `n m` (fits, below 1024) to `r12` and `rsi`, the hook, the tcache and `fs:0x18` read,
  the top chunk `T` (`main_arena.top`) and its size, to the `call` of `_int_malloc (&main_arena, n m)` (123).
- `vc_128`: the chunk `p` back, not null, its size word's bits 2 (mmapped) and 4 (not of the main arena) clear,
  to 148.
- `vc_148`: one thread, `p` not null, `perturb_byte` 0: the size of the chunk `C`, or the old top's when `p` was cut
  from it and that is smaller (`csz`), to 228.
- `vc_228m`: more than 79 bytes to clear: `memset (p, 0, csz - 8)` set up, to its `call` (717); `vc_228i`: at most
  79, to the inline stores (252).
- `vc_722`: `memset`'s return to `r8`, to 196; `vc_196`: the frame given back, the four pops, `rax = r8`, to the
  `ret` (209).
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
open FV7z.Tun (rd_Vst)
namespace FV7z.Cal

/-- The extra lemmas of the pieces' `wp`. -/
macro "cx" cfg:Lean.Parser.Tactic.optConfig "[" ls:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| wpx $cfg [Op.lda, Op.ldf, Op.cmpmif, Op.zxr, Op.setcc, Op.mul64o, Op.mulp, cond_0, BitVec.and_self,
      BitVec.reduceAdd, BitVec.reduceAnd, BitVec.reduceSetWidth, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft,
      BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceBEq, BitVec.reduceBNe, BitVec.reduceEq,
      BitVec.reduceToNat, BitVec.reduceSub, BitVec.reduceMul, BitVec.reduceLT, BitVec.reduceULT, BitVec.reduceOr,
      BitVec.reduceXOr, BitVec.reduceNot, BitVec.ofBool_false, BitVec.setWidth_and, BitVec.setWidth_or,
      BitVec.setWidth_zero, BitVec.shiftLeft_zero, BitVec.or_zero, BitVec.and_zero, BitVec.zero_and, BitVec.zero_or,
      Nat.reduceAdd, Nat.reduceSub, Nat.reduceLeDiff, Nat.reduceLT, decide_false, decide_true, Bool.or_false,
      Bool.false_or, Bool.not_false, Bool.not_true, Bool.false_eq_true, false_imp_iff, true_imp_iff, Bool.or_self,
      Bool.true_or, Bool.or_true, false_implies, true_implies, and_true, true_and, reduceIte, or_true, true_or,
      or_false, false_or, ne_eq, Nat.reduceEqDiff, not_false_eq_true, ofBytesLE_toBytesLE, Bool.true_eq_false,
      BitVec.xor_self, BitVec.add_zero, decide_eq_true_eq, $ls,*])

/-! ## The frame -/

/-- Bytes below the 32 under `S` read through the four pushes. -/
theorem fr_rd (V : Addr → Byte) (S : Addr) (a b c d : BitVec 64) {x : Addr} {n : Nat} (hS : 32 ≤ S.toNat)
    (h : x.toNat + n ≤ S.toNat - 32) :
    List.map (Vst (Vst (Vst (Vst V (S - 8) (toBytesLE a 8)) (S - 8 - 8) (toBytesLE b 8)) (S - 8 - 8 - 8)
      (toBytesLE c 8)) (S - 8 - 8 - 8 - 8) (toBytesLE d 8)) (byteAddrs x n) = List.map V (byteAddrs x n) := by
  have hl := S.isLt
  have e1 := Prepare.toNat_sub8 (a := S) (by omega)
  have e2 := Prepare.toNat_sub8 (a := S - 8) (by rw [e1]; omega)
  have e3 := Prepare.toNat_sub8 (a := S - 8 - 8) (by rw [e2, e1]; omega)
  have e4 := Prepare.toNat_sub8 (a := S - 8 - 8 - 8) (by rw [e3, e2, e1]; omega)
  rw [rd_Vst _ _ _ _ _ (by rw [toBytesLE_length, e4, e3, e2, e1]; omega) (by omega)
      (.inr (by rw [e4, e3, e2, e1]; omega)),
    rd_Vst _ _ _ _ _ (by rw [toBytesLE_length, e3, e2, e1]; omega) (by omega) (.inr (by rw [e3, e2, e1]; omega)),
    rd_Vst _ _ _ _ _ (by rw [toBytesLE_length, e2, e1]; omega) (by omega) (.inr (by rw [e2, e1]; omega)),
    rd_Vst _ _ _ _ _ (by rw [toBytesLE_length, e1]; omega) (by omega) (.inr (by rw [e1]; omega))]

/-- The size `__libc_calloc` clears from a chunk `p` of size `C`: the old top's `O` (`T` the old top) when `p` was
cut from it and `O` is smaller, else `C`. -/
def csz (p T O C : Addr) : Addr := if T = p + 18446744073709551600#64 then (if O.toNat < C.toNat then O else C) else C

variable {F : Footprint} {Wl : List Rgn}

/-! ## The pieces -/

set_option maxHeartbeats 4000000 in
/-- From the entry to the `call` of `_int_malloc` (123). -/
theorem vc_0 {fb T : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (hm : g.rdi.toNat * g.rsi.toNat ≤ 1024) (hS : 32 ≤ g.rsp.toNat)
    (hhk : rdq(V, 7940656#64) = 0#64) (htc : rdq(V, fb + 18446744073709551576#64) ≠ 0#64)
    (hmt : rdd(V, fb + 24#64) = 0) (hT : rdq(V, 7940768#64) = T)
    (d1 : 7940664 ≤ g.rsp.toNat - 32) (d2 : (fb + 18446744073709551576#64).toNat + 8 ≤ g.rsp.toNat - 32)
    (d3 : (fb + 24#64).toNat + 4 ≤ g.rsp.toNat - 32) (d4 : 7940776 ≤ g.rsp.toNat - 32)
    (d5 : (T + 8#64).toNat + 8 ≤ g.rsp.toNat - 32)
    (h1 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8) i)) (h2 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8) i))
    (h3 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8 - 8) i))
    (h4 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8 - 8 - 8) i))
    (f1 : ∀ i < 8, Foot F.data (Addr.add 7940656#64 i))
    (f2 : ∀ i < 8, Foot F.data (Addr.add (fb + 18446744073709551576#64) i))
    (f3 : ∀ i < 4, Foot F.data (Addr.add (fb + 24#64) i)) (f4 : ∀ i < 8, Foot F.data (Addr.add 7940768#64 i))
    (f5 : ∀ i < 8, Foot F.data (Addr.add (T + 8#64) i)) :
    W_0' fb F Wl (fun j' g' _ V' => j' = 123 ∧ V' = Mxi.mx4 V g.rsp g.r13 g.r12 g.rbp g.rbx ∧
      g'.rsp = g.rsp - 8 - 8 - 8 - 8 - 8#64 ∧ g'.rdi = 7940672#64 ∧ g'.rsi = g.rdi * g.rsi ∧
      g'.rbp = 7940672#64 ∧ g'.r12 = g.rdi * g.rsi ∧ g'.r13 = T ∧
      g'.rbx = rdq(V, T + 8#64) &&& 18446744073709551608#64 ∧ g'.r14 = g.r14 ∧ g'.r15 = g.r15) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hm hS d1 d2 d3 d4 d5 h1 h2 h3 h4 ⊢
  have hlt : rdi.toNat * rsi.toNat < 2 ^ 63 := Nat.lt_of_le_of_lt hm (by decide)
  have hh := mul_hi (x := rdi) (y := rsi) (Nat.lt_trans hlt (by decide))
  have hms : (rdi * rsi).msb = false := by
    rw [BitVec.msb_eq_decide, BitVec.toNat_mul, Nat.mod_eq_of_lt (Nat.lt_trans hlt (by decide))]
    exact decide_eq_false (Nat.not_le.2 hlt)
  have htc' := eq_false htc
  have k1 := fr_rd V rsp r13 r12 rbp rbx (x := 7940656#64) (n := 8) hS (by simp only [BitVec.toNat_ofNat]; omega)
  have k2 := fr_rd V rsp r13 r12 rbp rbx (x := fb + 18446744073709551576#64) (n := 8) hS d2
  have k3 := fr_rd V rsp r13 r12 rbp rbx (x := fb + 24#64) (n := 4) hS d3
  have k4 := fr_rd V rsp r13 r12 rbp rbx (x := 7940768#64) (n := 8) hS (by simp only [BitVec.toNat_ofNat]; omega)
  have k5 := fr_rd V rsp r13 r12 rbp rbx (x := T + 8#64) (n := 8) hS d5
  cx +contextual [W_0', W_35, W_47, W_63, W_79, W_95, W_117, o0', o1, o2, o3, o4, o5, o6, Mxi.mx4, mul_lo, hh, hms,
    k1, k2, k3, k4, k5, hhk, htc', hmt, hT, h1, h2, h3, h4, f1, f2, f3, f4, f5]

/-- From the return of `_int_malloc` (128) to 148: the chunk `p` (`rax`) not null, its size word `Z` with bits 2
and 4 clear, `rbp = &main_arena`. -/
theorem vc_128 {fb Z : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} (hax : g.rax ≠ 0#64)
    (hZ : rdq(V, g.rax + 18446744073709551608#64) = Z) (hb2 : Z.setWidth 8 &&& 2#8 = 0#8)
    (hb4 : Z.setWidth 8 &&& 4#8 = 0#8) (hbp : g.rbp = 7940672#64)
    (hfz : ∀ i < 8, Foot F.data (Addr.add (g.rax + 18446744073709551608#64) i)) :
    W_128 fb F Wl (fun j' g' _ V' => j' = 148 ∧ g' = { g with rax := Z, rdx := 7940672#64, r8 := g.rax } ∧ V' = V)
      g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hax hZ hbp hfz ⊢
  subst hbp
  have hax' : (rax == 0) = false := beq_eq_false_iff_ne.2 hax
  cx +contextual [W_128, W_136, W_304, W_328, o7, o8, o21, o22, hax', hZ, hb2, hb4, hfz]

set_option maxHeartbeats 4000000 in
/-- From 148 to 228: one thread, the chunk `p` (`r8`) not null, its size word `Z` with bit 2 clear, `perturb_byte`
0: `rdx` the size to clear and 8 (`csz`). -/
theorem vc_148 {fb Z : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} (hr8 : g.r8 ≠ 0#64)
    (hmt : rdd(V, fb + 24#64) = 0) (hZ : rdq(V, g.r8 + 18446744073709551608#64) = Z)
    (hb2 : Z.setWidth 8 &&& 2#8 = 0#8) (hpt : rdd(V, 8013220#64) = 0)
    (f1 : ∀ i < 4, Foot F.data (Addr.add (fb + 24#64) i))
    (f2 : ∀ i < 8, Foot F.data (Addr.add (g.r8 + 18446744073709551608#64) i))
    (f3 : ∀ i < 4, Foot F.data (Addr.add 8013220#64 i)) :
    W_148 fb F Wl (fun j' g' _ V' => j' = 228 ∧ V' = V ∧
      g'.rdx = csz g.r8 g.r13 g.rbx (Z &&& 18446744073709551608#64) ∧ g'.rsp = g.rsp ∧ g'.r8 = g.r8 ∧
      g'.rbx = g.rbx ∧ g'.rbp = g.rbp ∧ g'.r12 = g.r12 ∧ g'.r13 = g.r13 ∧ g'.r14 = g.r14 ∧ g'.r15 = g.r15)
      g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hr8 hZ f2 ⊢
  have hr8' : (r8 == 0) = false := beq_eq_false_iff_ne.2 hr8
  by_cases e1 : r13 = r8 + 18446744073709551600#64
  · by_cases e2 : rbx.toNat < (Z &&& 18446744073709551608#64).toNat
    · have e1' := eq_true e1
      have e2' := eq_true e2
      cx +contextual [W_148, W_164, W_173, W_216, W_368, W_381, o9, o10, o11, o14, o23, o24, csz, hr8', hmt, hZ,
        hb2, hpt, e1', e2', f1, f2, f3]
    · have e1' := eq_true e1
      have e2' := eq_false e2
      cx +contextual [W_148, W_164, W_173, W_216, W_368, W_381, o9, o10, o11, o14, o23, o24, csz, hr8', hmt, hZ,
        hb2, hpt, e1', e2', f1, f2, f3]
  · have e1' := eq_false e1
    cx +contextual [W_148, W_164, W_173, W_216, W_368, W_381, o9, o10, o11, o14, o23, o24, csz, hr8', hmt, hZ,
      hb2, hpt, e1', f1, f2, f3]

/-- From 228 to the `call` of `memset` (717): `rdx = c`, more than 79 bytes to clear (`c - 8`). -/
theorem vc_228m {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} (h8 : 8 ≤ g.rdx.toNat)
    (hbig : 79 < g.rdx.toNat - 8) :
    W_228 fb F Wl (fun j' g' _ V' => j' = 717 ∧ V' = V ∧
      g' = { g with rdx := g.rdx - 8#64, rsi := 0#64, rdi := g.r8 }) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h8 hbig ⊢
  have e8 := Sdp.sdT8 (x := rdx) h8
  have c1 := eq_false (show ¬ (rdx.toNat - 8 < 23) by omega)
  have c2 := eq_false (show ¬ (rdx - 8#64 = 23#64) from fun h => by
    have := congrArg BitVec.toNat h
    rw [e8] at this
    simp only [BitVec.toNat_ofNat, Nat.reduceMod] at this
    omega)
  have c3 := eq_false (show ¬ (rdx.toNat - 8 < 79) by omega)
  have c4 := eq_false (show ¬ (rdx - 8#64 = 79#64) from fun h => by
    have := congrArg BitVec.toNat h
    rw [e8] at this
    simp only [BitVec.toNat_ofNat, Nat.reduceMod] at this
    omega)
  cx +contextual [W_228, W_242, W_712, o15, o16, o25, e8, c1, c2, c3, c4]

/-- From 228 to the inline stores (252): `rdx = c`, at least 24 and at most 79 bytes to clear (`c - 8`). -/
theorem vc_228i {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} (h8 : 8 ≤ g.rdx.toNat)
    (hlo : 24 ≤ g.rdx.toNat - 8) (hsm : g.rdx.toNat - 8 ≤ 79) :
    W_228 fb F Wl (fun j' g' _ V' => j' = 252 ∧ V' = V ∧ g' = { g with rdx := g.rdx - 8#64 }) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h8 hlo hsm ⊢
  have e8 := Sdp.sdT8 (x := rdx) h8
  have c1 := eq_false (show ¬ (rdx.toNat - 8 < 23) by omega)
  have c2 := eq_false (show ¬ (rdx - 8#64 = 23#64) from fun h => by
    have := congrArg BitVec.toNat h
    rw [e8] at this
    simp only [BitVec.toNat_ofNat, Nat.reduceMod] at this
    omega)
  by_cases e79 : rdx.toNat - 8 = 79
  · have c3 := eq_false (show ¬ (rdx.toNat - 8 < 79) by omega)
    have c4 := eq_true (show rdx - 8#64 = 79#64 from BitVec.eq_of_toNat_eq (by rw [e8, e79]; rfl))
    cx +contextual [W_228, W_242, W_712, o15, o16, o25, e8, c1, c2, c3, c4]
  · have c3 := eq_true (show rdx.toNat - 8 < 79 by omega)
    cx +contextual [W_228, W_242, W_712, o15, o16, o25, e8, c1, c2, c3]

/-- From `memset`'s return (722) to 196: `r8 = rax`. -/
theorem vc_722 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} :
    W_722 fb F Wl (fun j' g' _ V' => j' = 196 ∧ V' = V ∧ g' = { g with r8 := g.rax }) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  cx [W_722, o26]

/-- From 196 to the `ret` (209): the frame given back, the four pops, `rax = r8`. -/
theorem vc_196 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (p0 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8#64) i))
    (p1 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8#64 + 8) i))
    (p2 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8#64 + 8 + 8) i))
    (p3 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8#64 + 8 + 8 + 8) i)) :
    W_196 fb F Wl (fun j' g' _ V' => j' = 209 ∧ V' = V ∧ g'.rax = g.r8 ∧ g'.rsp = g.rsp + 8#64 + 8 + 8 + 8 + 8 ∧
      g'.rbx = rdq(V, g.rsp + 8#64) ∧ g'.rbp = rdq(V, g.rsp + 8#64 + 8) ∧ g'.r12 = rdq(V, g.rsp + 8#64 + 8 + 8) ∧
      g'.r13 = rdq(V, g.rsp + 8#64 + 8 + 8 + 8) ∧ g'.r14 = g.r14 ∧ g'.r15 = g.r15) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at p0 p1 p2 p3 ⊢
  cx +contextual [W_196, o13, p0, p1, p2, p3]

end FV7z.Cal
