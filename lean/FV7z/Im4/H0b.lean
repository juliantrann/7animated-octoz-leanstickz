import FV7z.Im4.S0
import FV7z.Lemmas.Ksplit
/-!
# `_int_malloc` from the entry to 1115, `nb = 16 k`, `37 ≤ k ≤ 63` (PLAN.md G3, `malloc`)

`P0 k` (`Im4/S0.lean`), one `wpx` per `k` (one theorem each, `tools/kexpand.py`): `0 → 304 → 340 → 848 → 86`,
the smallbin of `nb` empty (`984`), `1069 → 1099 → 1115`.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn FV7z.Start
open FV7z.Imm (imm imm_at rd_off rd_off_self rd_below stk_f pu)
open FV7z.Im2 (G1n V1n)
namespace FV7z.Im4
variable {F : Footprint} {Wl : List Rgn}

set_option maxHeartbeats 100000000 in
theorem vc_0b_37 (k : Nat) (hk1 : 37 ≤ k) (hk2 : k ≤ 37) : P0 F Wl k := by
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
  obtain rfl : k = 37 := by omega
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

set_option maxHeartbeats 100000000 in
theorem vc_0b_38 (k : Nat) (hk1 : 38 ≤ k) (hk2 : k ≤ 38) : P0 F Wl k := by
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
  obtain rfl : k = 38 := by omega
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

set_option maxHeartbeats 100000000 in
theorem vc_0b_39 (k : Nat) (hk1 : 39 ≤ k) (hk2 : k ≤ 39) : P0 F Wl k := by
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
  obtain rfl : k = 39 := by omega
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

set_option maxHeartbeats 100000000 in
theorem vc_0b_40 (k : Nat) (hk1 : 40 ≤ k) (hk2 : k ≤ 40) : P0 F Wl k := by
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
  obtain rfl : k = 40 := by omega
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

set_option maxHeartbeats 100000000 in
theorem vc_0b_41 (k : Nat) (hk1 : 41 ≤ k) (hk2 : k ≤ 41) : P0 F Wl k := by
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
  obtain rfl : k = 41 := by omega
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

set_option maxHeartbeats 100000000 in
theorem vc_0b_42 (k : Nat) (hk1 : 42 ≤ k) (hk2 : k ≤ 42) : P0 F Wl k := by
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
  obtain rfl : k = 42 := by omega
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

set_option maxHeartbeats 100000000 in
theorem vc_0b_43 (k : Nat) (hk1 : 43 ≤ k) (hk2 : k ≤ 43) : P0 F Wl k := by
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
  obtain rfl : k = 43 := by omega
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

set_option maxHeartbeats 100000000 in
theorem vc_0b_44 (k : Nat) (hk1 : 44 ≤ k) (hk2 : k ≤ 44) : P0 F Wl k := by
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
  obtain rfl : k = 44 := by omega
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

set_option maxHeartbeats 100000000 in
theorem vc_0b_45 (k : Nat) (hk1 : 45 ≤ k) (hk2 : k ≤ 45) : P0 F Wl k := by
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
  obtain rfl : k = 45 := by omega
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

set_option maxHeartbeats 100000000 in
theorem vc_0b_46 (k : Nat) (hk1 : 46 ≤ k) (hk2 : k ≤ 46) : P0 F Wl k := by
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
  obtain rfl : k = 46 := by omega
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

set_option maxHeartbeats 100000000 in
theorem vc_0b_47 (k : Nat) (hk1 : 47 ≤ k) (hk2 : k ≤ 47) : P0 F Wl k := by
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
  obtain rfl : k = 47 := by omega
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

set_option maxHeartbeats 100000000 in
theorem vc_0b_48 (k : Nat) (hk1 : 48 ≤ k) (hk2 : k ≤ 48) : P0 F Wl k := by
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
  obtain rfl : k = 48 := by omega
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

set_option maxHeartbeats 100000000 in
theorem vc_0b_49 (k : Nat) (hk1 : 49 ≤ k) (hk2 : k ≤ 49) : P0 F Wl k := by
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
  obtain rfl : k = 49 := by omega
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

set_option maxHeartbeats 100000000 in
theorem vc_0b_50 (k : Nat) (hk1 : 50 ≤ k) (hk2 : k ≤ 50) : P0 F Wl k := by
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
  obtain rfl : k = 50 := by omega
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

set_option maxHeartbeats 100000000 in
theorem vc_0b_51 (k : Nat) (hk1 : 51 ≤ k) (hk2 : k ≤ 51) : P0 F Wl k := by
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
  obtain rfl : k = 51 := by omega
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

set_option maxHeartbeats 100000000 in
theorem vc_0b_52 (k : Nat) (hk1 : 52 ≤ k) (hk2 : k ≤ 52) : P0 F Wl k := by
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
  obtain rfl : k = 52 := by omega
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

set_option maxHeartbeats 100000000 in
theorem vc_0b_53 (k : Nat) (hk1 : 53 ≤ k) (hk2 : k ≤ 53) : P0 F Wl k := by
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
  obtain rfl : k = 53 := by omega
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

set_option maxHeartbeats 100000000 in
theorem vc_0b_54 (k : Nat) (hk1 : 54 ≤ k) (hk2 : k ≤ 54) : P0 F Wl k := by
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
  obtain rfl : k = 54 := by omega
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

set_option maxHeartbeats 100000000 in
theorem vc_0b_55 (k : Nat) (hk1 : 55 ≤ k) (hk2 : k ≤ 55) : P0 F Wl k := by
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
  obtain rfl : k = 55 := by omega
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

set_option maxHeartbeats 100000000 in
theorem vc_0b_56 (k : Nat) (hk1 : 56 ≤ k) (hk2 : k ≤ 56) : P0 F Wl k := by
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
  obtain rfl : k = 56 := by omega
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

set_option maxHeartbeats 100000000 in
theorem vc_0b_57 (k : Nat) (hk1 : 57 ≤ k) (hk2 : k ≤ 57) : P0 F Wl k := by
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
  obtain rfl : k = 57 := by omega
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

set_option maxHeartbeats 100000000 in
theorem vc_0b_58 (k : Nat) (hk1 : 58 ≤ k) (hk2 : k ≤ 58) : P0 F Wl k := by
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
  obtain rfl : k = 58 := by omega
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

set_option maxHeartbeats 100000000 in
theorem vc_0b_59 (k : Nat) (hk1 : 59 ≤ k) (hk2 : k ≤ 59) : P0 F Wl k := by
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
  obtain rfl : k = 59 := by omega
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

set_option maxHeartbeats 100000000 in
theorem vc_0b_60 (k : Nat) (hk1 : 60 ≤ k) (hk2 : k ≤ 60) : P0 F Wl k := by
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
  obtain rfl : k = 60 := by omega
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

set_option maxHeartbeats 100000000 in
theorem vc_0b_61 (k : Nat) (hk1 : 61 ≤ k) (hk2 : k ≤ 61) : P0 F Wl k := by
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
  obtain rfl : k = 61 := by omega
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

set_option maxHeartbeats 100000000 in
theorem vc_0b_62 (k : Nat) (hk1 : 62 ≤ k) (hk2 : k ≤ 62) : P0 F Wl k := by
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
  obtain rfl : k = 62 := by omega
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

set_option maxHeartbeats 100000000 in
theorem vc_0b_63 (k : Nat) (hk1 : 63 ≤ k) (hk2 : k ≤ 63) : P0 F Wl k := by
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
  obtain rfl : k = 63 := by omega
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

theorem vc_0b (k : Nat) (hk1 : 37 ≤ k) (hk2 : k ≤ 63) : P0 F Wl k := by
  by_cases h37 : k ≤ 37
  · exact vc_0b_37 k (by omega) h37
  by_cases h38 : k ≤ 38
  · exact vc_0b_38 k (by omega) h38
  by_cases h39 : k ≤ 39
  · exact vc_0b_39 k (by omega) h39
  by_cases h40 : k ≤ 40
  · exact vc_0b_40 k (by omega) h40
  by_cases h41 : k ≤ 41
  · exact vc_0b_41 k (by omega) h41
  by_cases h42 : k ≤ 42
  · exact vc_0b_42 k (by omega) h42
  by_cases h43 : k ≤ 43
  · exact vc_0b_43 k (by omega) h43
  by_cases h44 : k ≤ 44
  · exact vc_0b_44 k (by omega) h44
  by_cases h45 : k ≤ 45
  · exact vc_0b_45 k (by omega) h45
  by_cases h46 : k ≤ 46
  · exact vc_0b_46 k (by omega) h46
  by_cases h47 : k ≤ 47
  · exact vc_0b_47 k (by omega) h47
  by_cases h48 : k ≤ 48
  · exact vc_0b_48 k (by omega) h48
  by_cases h49 : k ≤ 49
  · exact vc_0b_49 k (by omega) h49
  by_cases h50 : k ≤ 50
  · exact vc_0b_50 k (by omega) h50
  by_cases h51 : k ≤ 51
  · exact vc_0b_51 k (by omega) h51
  by_cases h52 : k ≤ 52
  · exact vc_0b_52 k (by omega) h52
  by_cases h53 : k ≤ 53
  · exact vc_0b_53 k (by omega) h53
  by_cases h54 : k ≤ 54
  · exact vc_0b_54 k (by omega) h54
  by_cases h55 : k ≤ 55
  · exact vc_0b_55 k (by omega) h55
  by_cases h56 : k ≤ 56
  · exact vc_0b_56 k (by omega) h56
  by_cases h57 : k ≤ 57
  · exact vc_0b_57 k (by omega) h57
  by_cases h58 : k ≤ 58
  · exact vc_0b_58 k (by omega) h58
  by_cases h59 : k ≤ 59
  · exact vc_0b_59 k (by omega) h59
  by_cases h60 : k ≤ 60
  · exact vc_0b_60 k (by omega) h60
  by_cases h61 : k ≤ 61
  · exact vc_0b_61 k (by omega) h61
  by_cases h62 : k ≤ 62
  · exact vc_0b_62 k (by omega) h62
  exact vc_0b_63 k (by omega) hk2

end FV7z.Im4
