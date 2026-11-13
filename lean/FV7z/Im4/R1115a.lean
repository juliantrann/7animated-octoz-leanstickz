import FV7z.Im4.S1115
import FV7z.Lemmas.Ksplit
/-!
# `_int_malloc` from 1115 to 2549, `nb = 16 k`, `2 ≤ k ≤ 32` (PLAN.md G3, `malloc`)

`P1115 k` (`Im4/S1115.lean`), one `wpx` per `k` (`ksplit`), as `Im2.vc_1115n`, the post on `rbx`, `r13`, `rsp`.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn FV7z.Start
open FV7z.Imm (rd_off rd_off_self rd_below stk_f)
open FV7z.Im2 (G1n V1n V2n W_1115 W_1138 W_1968 W_2012 W_2048 W_2480 W_2488 W_2505 W_2513 W_2530 W_2535
  o12 o13 o14 o15 o16 o17 o18 o19 o20 o21)
namespace FV7z.Im4
variable {F : Footprint} {Wl : List Rgn}

set_option maxHeartbeats 200000000 in
theorem vc_1115a (k : Nat) (hk1 : 2 ≤ k) (hk2 : k ≤ 32) : P1115 F Wl k := by
  intro fb S n g f V hS hlo hun hm0 hm1 hm2 hm3 hW hsw hsd
  have q1 := rd_below (S := S) (x := 7940792#64) (n := 8) (hx := by rw [BitVec.toNat_ofNat]; omega) (hS := hS)
  have q2 := rd_below (S := S) (x := 7942816#64) (n := 4) (hx := by rw [BitVec.toNat_ofNat]; omega) (hS := hS)
  have q3 := rd_below (S := S) (x := 7942820#64) (n := 4) (hx := by rw [BitVec.toNat_ofNat]; omega) (hS := hS)
  have q4 := rd_below (S := S) (x := 7942824#64) (n := 4) (hx := by rw [BitVec.toNat_ofNat]; omega) (hS := hS)
  have q5 := rd_below (S := S) (x := 7942828#64) (n := 4) (hx := by rw [BitVec.toNat_ofNat]; omega) (hS := hS)
  have hS' : S.toNat + 256 < 18446744073709551616 := hS
  have D : ∀ (x : Addr) (n : Nat), 7940480 ≤ x.toNat → x.toNat + n ≤ 7943136 →
      ∀ i < n, Foot F.data (Addr.add x i) :=
    fun x n h1 h2 i hi => hW _ (by simp only [Addr.add]; bv_omega) (by simp only [Addr.add]; bv_omega)
  ksplit k from 2 to 32 using hk1 hk2 <;>
  ( simp only [Nat.reduceMul, Nat.reduceAdd]
    wpx [W_1115, W_1138, W_1968, W_2012, W_2048, W_2480, W_2488, W_2505, W_2513, W_2530, W_2535, V1n, G1n,
      o12, o13, o14, o15, o16, o17, o18, o19, o20, o21, q1, q2, q3, q4, q5, rd_off, rd_off_self, hS, hS', hun, hm0,
      hm1, hm2, hm3,
      BitVec.reduceAdd, BitVec.reduceAnd, BitVec.reduceSetWidth, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft,
      BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceBEq, BitVec.reduceEq, BitVec.reduceToNat,
      BitVec.reduceSub, BitVec.reduceMul, BitVec.reduceLT, BitVec.reduceULT, BitVec.reduceOr, BitVec.reduceXOr,
      Nat.reduceAdd, Nat.reduceLeDiff, Nat.reduceLT, decide_false, decide_true, Bool.or_false, Bool.false_or,
      Bool.not_false, Bool.not_true, Bool.false_eq_true, false_imp_iff, true_imp_iff, Bool.or_self, Bool.true_or,
      Bool.or_true, false_implies, true_implies, and_true, true_and, reduceIte, or_true, true_or, or_false, false_or,
      ne_eq, Nat.reduceEqDiff, not_false_eq_true, ofBytesLE_toBytesLE, Bool.true_eq_false]
    repeat' first
      | apply And.intro
      | intro (_ : Rflags)
      | rfl
      | with_reducible exact stk_f hsw (by decide)
      | with_reducible exact stk_f hsd (by decide)
      | with_reducible exact D _ _ (by decide) (by decide))

end FV7z.Im4
