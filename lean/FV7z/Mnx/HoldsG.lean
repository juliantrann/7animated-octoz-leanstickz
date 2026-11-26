import FV7z.Mnx.Holds
import FV7z.Im7.Cls
/-!
# `malloc` after the first call: the blocks for a symbolic `nb` (PLAN.md G3, `malloc`)

`Mnx.Holds` proves the blocks for each chunk size `16 k` of `Im5.ClsN` by `ksplit`; here the chunk size `nb` is a
variable, its flags hypotheses in the form `simp` leaves them (as `Im7`):
- `vc_0g`: `vc_0n` for `9 ≤ n ≤ 2 ^ 32`.
- `vc_52g`: the tcache index `(nb - 17) >> 4` not below `mp_.tcache_bins` (64), no bin.
- `vc_114g`: the chunk back, its size word `sw` with the bits 2 and 4 (`IS_MMAPPED`, `NON_MAIN_ARENA`) clear.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn FV7z.Start
namespace FV7z.Mnx
variable {F : Footprint} {Wl : List Rgn}

/-- `vc_0n` for `9 ≤ n ≤ 2 ^ 32`. -/
theorem vc_0g {fb n : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} (hdi : g.rdi = n)
    (hn : 9 ≤ n.toNat) (hn' : n.toNat ≤ 2 ^ 32)
    (hhk : rdq(V, 7940656#64) = 0#64) (hfh : ∀ i < 8, Foot F.data (Addr.add (7940656#64) i))
    (hsp : 7940664 + 8 ≤ g.rsp.toNat) (hst : ∀ i < 24, Foot Wl (Addr.add (g.rsp - 24) i)) :
    W_0 fb F Wl (fun j' g' _ V' => j' = 52 ∧
      g' = { g with rax := n + 23#64 &&& 18446744073709551600#64,
                    rbx := ((n + 23#64 &&& 18446744073709551600#64) + 18446744073709551599#64) >>> 4,
                    rbp := n, rsp := g.rsp - 8 - 8 - 8 } ∧
      V' = Mal.Vm g V) g f V := by
  have m : n.msb = false := by
    rw [BitVec.msb_eq_decide]; exact decide_eq_false (by show ¬ (2 ^ 63 ≤ n.toNat); omega)
  have e : (n + 23#64).toNat = n.toNat + 23 := by rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have d1 : decide ((n + 23#64).toNat < 31) = false := decide_eq_false (by omega)
  have d2 : decide (n + 23#64 = 31#64) = false :=
    decide_eq_false (fun h => by rw [h, BitVec.toNat_ofNat] at e; omega)
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hdi hsp hst ⊢
  subst hdi
  obtain ⟨s1, s2, s3⟩ := Mhi.push3 hst
  have ek := hk_rd V rsp r12 hsp
  wpx [W_0, W_27, W_36, W_176, o0, o1, o2, o12, Op.lda, Op.shr64, Mal.Vm, ek, hhk, m, d1, d2, BitVec.and_self,
      BitVec.reduceAdd, BitVec.reduceAnd, BitVec.reduceSetWidth, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft,
      BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceBEq, BitVec.reduceEq, BitVec.reduceToNat,
      BitVec.reduceSub, BitVec.reduceMul, BitVec.reduceLT, BitVec.reduceULT, BitVec.reduceOr, BitVec.reduceXOr,
      BitVec.reduceNot,
      Nat.reduceAdd, Nat.reduceLeDiff, Nat.reduceLT, decide_false, decide_true, Bool.or_false, Bool.false_or,
      Bool.not_false, Bool.not_true, Bool.false_eq_true, false_imp_iff, true_imp_iff, Bool.or_self, Bool.true_or,
      Bool.or_true, false_implies, true_implies, and_true, true_and, reduceIte, or_true, true_or, or_false, false_or,
      ne_eq, Nat.reduceEqDiff, not_false_eq_true, ofBytesLE_toBytesLE, Bool.true_eq_false, BitVec.xor_self,
      BitVec.add_zero]
  first
    | exact ⟨s1, hfh, s2, s3⟩
    | exact ⟨s1, hfh, s2, s3, fun _ _ => trivial⟩
    | exact ⟨s1, hfh, s2, s3, fun _ => trivial⟩

set_option maxHeartbeats 50000000 in
/-- From 52 to 83: the tcache there, the index `(nb - 17) >> 4` not below `mp_.tcache_bins`. -/
theorem vc_52g {fb C nb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (hbx : g.rbx = (nb + 18446744073709551599#64) >>> 4)
    (hc : decide (((nb + 18446744073709551599#64) >>> 4).toNat < 64) = false)
    (htb : rdq(V, 7940592#64) = 64#64) (htc : rdq(V, fb + 18446744073709551576#64) = C) (hC : C ≠ 0#64)
    (hfb : ∀ i < 8, Foot F.data (Addr.add (7940592#64) i))
    (hft : ∀ i < 8, Foot F.data (Addr.add (fb + 18446744073709551576#64) i)) :
    W_52 fb F Wl (fun j' g' _ V' => j' = 83 ∧ g' = { g with rax := C } ∧ V' = V) g f V := by
  have hC' : (C == 0) = false := beq_eq_false_iff_ne.2 hC
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hbx ⊢
  subst hbx
  wpx [W_52, W_70, o3, o4, Op.cmpma, Op.ldf, htb, htc, hC', hc, BitVec.and_self,
    BitVec.reduceAdd, BitVec.reduceAnd, BitVec.reduceSetWidth, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft,
    BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceBEq, BitVec.reduceEq, BitVec.reduceToNat,
    BitVec.reduceSub, BitVec.reduceMul, BitVec.reduceLT, BitVec.reduceULT, BitVec.reduceOr, BitVec.reduceXOr,
    BitVec.reduceNot,
    Nat.reduceAdd, Nat.reduceLeDiff, Nat.reduceLT, decide_false, decide_true, Bool.or_false, Bool.false_or,
    Bool.not_false, Bool.not_true, Bool.false_eq_true, false_imp_iff, true_imp_iff, Bool.or_self, Bool.true_or,
    Bool.or_true, false_implies, true_implies, and_true, true_and, reduceIte, or_true, true_or, or_false, false_or,
    ne_eq, Nat.reduceEqDiff, not_false_eq_true, ofBytesLE_toBytesLE, Bool.true_eq_false, BitVec.xor_self,
    BitVec.add_zero]
  first | exact ⟨hft, hfb⟩ | exact ⟨hfb, hft⟩

set_option maxHeartbeats 50000000 in
/-- From the return of `_int_malloc` (114) to 164: the chunk not null, its size word `sw` with the bits 2 and 4
clear. -/
theorem vc_114g {fb sw : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (hax : g.rax ≠ 0#64) (hsz : rdq(V, g.rax + 18446744073709551608#64) = sw)
    (h2 : BitVec.setWidth 8 sw &&& 2#8 = 0) (h4 : BitVec.setWidth 8 sw &&& 4#8 = 0)
    (hfz : ∀ i < 8, Foot F.data (Addr.add (g.rax + 18446744073709551608#64) i)) :
    W_114 fb F Wl (fun j' g' _ V' => j' = 164 ∧ g' = { g with rax := sw, r8 := g.rax } ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hax hsz hfz ⊢
  have hax' : (rax == 0) = false := beq_eq_false_iff_ne.2 hax
  wpx [W_114, W_126, W_134, o7, o8, o9, hax', hsz, h2, h4, beq_self_eq_true, BitVec.and_self,
    BitVec.reduceAdd, BitVec.reduceAnd, BitVec.reduceSetWidth, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft,
    BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceBEq, BitVec.reduceEq, BitVec.reduceToNat,
    BitVec.reduceSub, BitVec.reduceMul, BitVec.reduceLT, BitVec.reduceULT, BitVec.reduceOr, BitVec.reduceXOr,
    BitVec.reduceNot,
    Nat.reduceAdd, Nat.reduceLeDiff, Nat.reduceLT, decide_false, decide_true, Bool.or_false, Bool.false_or,
    Bool.not_false, Bool.not_true, Bool.false_eq_true, false_imp_iff, true_imp_iff, Bool.or_self, Bool.true_or,
    Bool.or_true, false_implies, true_implies, and_true, true_and, reduceIte, or_true, true_or, or_false, false_or,
    ne_eq, Nat.reduceEqDiff, not_false_eq_true, ofBytesLE_toBytesLE, Bool.true_eq_false, BitVec.xor_self,
    BitVec.add_zero]
  first | exact hfz

end FV7z.Mnx
