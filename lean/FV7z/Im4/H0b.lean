import FV7z.Im4.S0
import FV7z.Lemmas.Ksplit
/-!
# `_int_malloc` from the entry to 1115, `nb = 16 k`, `37 ≤ k ≤ 63` (PLAN.md G3, `malloc`)

`P0 k` (`Im4/S0.lean`), one `wpx` per `k` (`ksplit`): `0 → 304 → 340 → 848 → 86`, the smallbin of `nb` empty
(`984`), `1069 → 1099 → 1115`.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn FV7z.Start
open FV7z.Imm (imm imm_at rd_off rd_off_self rd_below stk_f pu)
open FV7z.Im2 (G1n V1n)
namespace FV7z.Im4
variable {F : Footprint} {Wl : List Rgn}

set_option maxHeartbeats 100000000 in
theorem vc_0b (k : Nat) (hk1 : 37 ≤ k) (hk2 : k ≤ 63) : P0 F Wl k := by
  intro fb S n g f V hrsp hsi hdi m d1 d2 e hS hlo hfb hgm sk htc htb hW hgf htf hsw
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hrsp hsi hdi ⊢
  subst hrsp hsi hdi
  obtain ⟨p1, p2, p3, p4, p5, p6, p7⟩ := pu S
  have qk := rd_below (S := S) (x := BitVec.ofNat 64 (7940776 + 16 * k)) (n := 8)
    (hx := by rw [BitVec.toNat_ofNat]; omega) (hS := hS)
  have q1 := rd_below (S := S) (x := 8013224#64) (n := 8) (hx := by rw [BitVec.toNat_ofNat]; omega) (hS := hS)
  have q3 := rd_below (S := S) (n := 8) (hx := hfb) (hS := hS)
  have q5 := rd_below (S := S) (x := 7940592#64) (n := 8) (hx := by rw [BitVec.toNat_ofNat]; omega) (hS := hS)
  have hS' : S.toNat + 256 < 18446744073709551616 := hS
  have D : ∀ (x : Addr) (n : Nat), 7940480 ≤ x.toNat → x.toNat + n ≤ 7943136 →
      ∀ i < n, Foot F.data (Addr.add x i) :=
    fun x n h1 h2 i hi => hW _ (by simp only [Addr.add]; bv_omega) (by simp only [Addr.add]; bv_omega)
  ksplit k from 37 to 63 using hk1 hk2 <;>
  ( simp only [Nat.reduceMul, Nat.reduceAdd] at e sk qk ⊢
    wpx [W_0, W_9, W_304, W_320, W_340, W_848, W_86, W_984, W_1069, W_1099, o0, o1, o2, o3, o4, o5, o6, o7,
      o8, o9, Op.cmpma, Op.cmpmif, Op.cmpmra, Op.shr64, p1, p2, p3, p4, p5, p6, p7, q1, q3, q5, sk, qk, rd_off,
      rd_off_self, hS, hS', m, d1, d2, e, hgm, htb, htc, BitVec.and_self, G1n, V1n,
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
      | intro (_ : Rflags.zf _ = false)
      | intro (_ : Rflags.zf _ = true)
      | rfl
      | with_reducible exact stk_f hsw (by decide)
      | with_reducible exact hgf
      | with_reducible exact htf
      | with_reducible exact D _ _ (by decide) (by decide))

end FV7z.Im4
