/-!
# The arithmetic of the range decoder (PLAN.md G2, pilot `LzmaDec_DecodeReal_3`)

`LzmaDec_DecodeReal_3` checks its input pointer against `bufLimit` between two symbols only; within a symbol each
normalization of the range may read a byte. That these reads stay within 20 bytes of `bufLimit` follows from the
range: a normalization reads only when the range is below `2^24`, a bit decoded with a probability in `[31, 2017]`
divides a range of at least `2^24` by at most 67, a direct bit by at most `2 + 2^-22`, and a symbol has at most 22 of
the former with 26 of the latter (or 23 and none). `Crd A d c R`: with `c` bytes read at or after `bufLimit` and `d`
direct bits, the range `R` is at least `256^c · 2^24 / (A · (2 + 2^-22)^d)`.

The probabilities stay in `[31, 2017]` under the two updates, `p + ((2048 - p) >> 5)` and `p - (p >> 5)`.
-/
namespace FV7z.Lzma

/-- The range `R` after `c` bytes read at or after `bufLimit`, `d` direct bits, and bits with probabilities that
divided the range by at most `A` in all. -/
def Crd (A d c R : Nat) : Prop := 256 ^ c * 2 ^ 24 * 2 ^ (22 * d) ≤ R * A * (2 ^ 23 + 1) ^ d

theorem crd_succ_d {A d c R : Nat} (h : Crd A d c R) : Crd A (d + 1) c R := by
  unfold Crd at h ⊢
  have e1 : (2 : Nat) ^ (22 * (d + 1)) = 2 ^ (22 * d) * 2 ^ 22 := Nat.pow_add 2 (22 * d) 22
  have e2 : (2 ^ 23 + 1) ^ (d + 1) = (2 ^ 23 + 1) ^ d * (2 ^ 23 + 1) := Nat.pow_succ _ _
  have hx : 2 ^ 22 ≤ 2 ^ 23 + 1 := by decide
  rw [e1, e2]
  generalize 2 ^ 23 + 1 = X at h hx ⊢
  generalize (2 ^ 22 : Nat) = Y at hx ⊢
  calc 256 ^ c * 2 ^ 24 * (2 ^ (22 * d) * Y) = 256 ^ c * 2 ^ 24 * 2 ^ (22 * d) * Y := by ac_rfl
    _ ≤ R * A * X ^ d * X := Nat.mul_le_mul h hx
    _ = R * A * (X ^ d * X) := by ac_rfl

theorem crd_mono_d {A d d' c R : Nat} (h : Crd A d c R) (hd : d ≤ d') : Crd A d' c R := by
  induction hd with
  | refl => exact h
  | step _ ih => exact crd_succ_d ih

theorem crd_mono_A {A A' d c R : Nat} (h : Crd A d c R) (hA : A ≤ A') : Crd A' d c R :=
  Nat.le_trans h (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hA))

/-- A bit with a probability: the range is divided by at most 67. -/
theorem crd_model {A d c R R' : Nat} (h : Crd A d c R) (hR : R ≤ 67 * R') : Crd (67 * A) d c R' := by
  unfold Crd at h ⊢
  generalize (2 ^ 23 + 1) ^ d = X at h ⊢
  calc 256 ^ c * 2 ^ 24 * 2 ^ (22 * d) ≤ R * A * X := h
    _ ≤ 67 * R' * A * X := Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hR)
    _ = R' * (67 * A) * X := by ac_rfl

/-- A direct bit: the range is halved. -/
theorem crd_direct {A d c R R' : Nat} (h : Crd A d c R) (h1 : R ≤ 2 * R' + 1) (h2 : 2 ^ 22 ≤ R') :
    Crd A (d + 1) c R' := by
  unfold Crd at h ⊢
  have e : R * 2 ^ 22 ≤ R' * (2 ^ 23 + 1) := by omega
  have e1 : (2 : Nat) ^ (22 * (d + 1)) = 2 ^ (22 * d) * 2 ^ 22 := Nat.pow_add 2 (22 * d) 22
  have e2 : (2 ^ 23 + 1) ^ (d + 1) = (2 ^ 23 + 1) ^ d * (2 ^ 23 + 1) := Nat.pow_succ _ _
  rw [e1, e2]
  generalize 2 ^ 23 + 1 = X at h e ⊢
  generalize (2 ^ 22 : Nat) = Y at e ⊢
  calc 256 ^ c * 2 ^ 24 * (2 ^ (22 * d) * Y) = 256 ^ c * 2 ^ 24 * 2 ^ (22 * d) * Y := by ac_rfl
    _ ≤ R * A * X ^ d * Y := Nat.mul_le_mul_right _ h
    _ = R * Y * (A * X ^ d) := by ac_rfl
    _ ≤ R' * X * (A * X ^ d) := Nat.mul_le_mul_right _ e
    _ = R' * A * (X ^ d * X) := by ac_rfl

/-- A byte read: the range is multiplied by 256. -/
theorem crd_read {A d c R : Nat} (h : Crd A d c R) : Crd A d (c + 1) (256 * R) := by
  unfold Crd at h ⊢
  have e1 : (256 : Nat) ^ (c + 1) = 256 ^ c * 256 := Nat.pow_succ _ _
  rw [e1]
  generalize (2 ^ 23 + 1) ^ d = X at h ⊢
  calc 256 ^ c * 256 * 2 ^ 24 * 2 ^ (22 * d) = 256 * (256 ^ c * 2 ^ 24 * 2 ^ (22 * d)) := by ac_rfl
    _ ≤ 256 * (R * A * X) := Nat.mul_le_mul_left _ h
    _ = 256 * R * A * X := by ac_rfl

set_option exponentiation.threshold 600

theorem bound_num : (2 ^ 24 - 1) * (256 * 67 ^ 22) * (2 ^ 23 + 1) ^ 26 < 256 ^ 21 * 2 ^ 24 * 2 ^ (22 * 26) :=
  Nat.le_of_ble_eq_true (by decide +kernel)

theorem bound_num' : (2 ^ 24 - 1) * (256 * 67 ^ 23) * (2 ^ 23 + 1) ^ 0 < 256 ^ 21 * 2 ^ 24 * 2 ^ (22 * 0) :=
  Nat.le_of_ble_eq_true (by decide +kernel)

/-- A range below `2^24` after at most 22 bits with probabilities and 26 direct bits: at most 20 bytes were read at
or after `bufLimit`. -/
theorem crd_bound {A d c R : Nat} (h : Crd A d c R) (hA : A ≤ 256 * 67 ^ 22) (hd : d ≤ 26) (hR : R < 2 ^ 24) :
    c ≤ 20 :=
  Nat.le_of_not_lt fun hc => Nat.not_le_of_lt bound_num
    (Nat.le_trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by decide) hc)))
      (Nat.le_trans (crd_mono_d h hd) (Nat.mul_le_mul_right _ (Nat.mul_le_mul (Nat.le_pred_of_lt hR) hA))))

/-- The same after at most 23 bits with probabilities and no direct bit. -/
theorem crd_bound' {A c R : Nat} (h : Crd A 0 c R) (hA : A ≤ 256 * 67 ^ 23) (hR : R < 2 ^ 24) : c ≤ 20 :=
  Nat.le_of_not_lt fun hc => Nat.not_le_of_lt bound_num'
    (Nat.le_trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by decide) hc)))
      (Nat.le_trans h (Nat.mul_le_mul_right _ (Nat.mul_le_mul (Nat.le_pred_of_lt hR) hA))))

/-! ## A bit decoded with a probability -/

/-- The bound `(R >> 11) · P` of a range `R ≥ 2^24` with a probability `P` in `[31, 2017]`: both parts of the range
are at least a 67th of it. -/
theorem bit_bound (R P : BitVec 32) (hR : 2 ^ 24 ≤ R.toNat) (hP1 : 31 ≤ P.toNat) (hP2 : P.toNat ≤ 2017) :
    (R >>> 11 * P).toNat < R.toNat ∧ R.toNat ≤ 67 * (R >>> 11 * P).toNat ∧
      (R - R >>> 11 * P).toNat = R.toNat - (R >>> 11 * P).toNat ∧ R.toNat ≤ 67 * (R - R >>> 11 * P).toNat := by
  have hlt := R.isLt
  have e : (R >>> 11 * P).toNat = R.toNat / 2048 * P.toNat := by
    rw [BitVec.toNat_mul, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
    have h1 : R.toNat / 2 ^ 11 * P.toNat ≤ R.toNat / 2 ^ 11 * 2017 := Nat.mul_le_mul_left _ hP2
    rw [Nat.mod_eq_of_lt (by omega)]
  have h1 : R.toNat / 2048 * P.toNat ≤ R.toNat / 2048 * 2017 := Nat.mul_le_mul_left _ hP2
  have h2 : R.toNat / 2048 * 31 ≤ R.toNat / 2048 * P.toNat := Nat.mul_le_mul_left _ hP1
  have e2 : (R - R >>> 11 * P).toNat = R.toNat - (R >>> 11 * P).toNat := by
    rw [BitVec.toNat_sub, e]
    omega
  rw [e2, e]
  refine ⟨by omega, by omega, rfl, by omega⟩

/-- A direct bit: half the range. -/
theorem dir_bound (R : BitVec 32) (hR : 2 ^ 24 ≤ R.toNat) :
    R.toNat ≤ 2 * (R >>> 1).toNat + 1 ∧ 2 ^ 23 ≤ (R >>> 1).toNat ∧ (R >>> 1).toNat < 2 ^ 31 := by
  have hlt := R.isLt
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  omega

/-! ## The probabilities stay in `[31, 2017]` -/

/-- A value in `[31, 2017]`, as a `Bool`. -/
def pvb (P : BitVec 32) : Bool := decide (31 ≤ P.toNat) && decide (P.toNat ≤ 2017)

/-- A value in `[31, 2017]`. -/
def Pv (P : BitVec 32) : Prop := 31 ≤ P.toNat ∧ P.toNat ≤ 2017

theorem pvb_iff {P : BitVec 32} : pvb P = true ↔ Pv P := by simp [pvb, Pv]

/-- The updates of a probability, all four forms in the code. -/
def pchk (P : BitVec 32) : Bool :=
  pvb (P + (2048#32 - P) >>> 5) && pvb (P - P >>> 5) && pvb ((2048#32 - P).sshiftRight 5 + P) &&
    pvb ((31#32 - P).sshiftRight 5 + P)

theorem prob_all : (List.range 2048).all (fun n => !pvb (BitVec.ofNat 32 n) || pchk (BitVec.ofNat 32 n)) = true := by
  decide +kernel

theorem Pv.all {P : BitVec 32} (h : Pv P) :
    Pv (P + (2048#32 - P) >>> 5) ∧ Pv (P - P >>> 5) ∧ Pv ((2048#32 - P).sshiftRight 5 + P) ∧
      Pv ((31#32 - P).sshiftRight 5 + P) := by
  have := List.all_eq_true.1 prob_all P.toNat (List.mem_range.2 (by have := h.2; omega))
  rw [BitVec.ofNat_toNat, BitVec.setWidth_eq, pvb_iff.2 h] at this
  simpa [pchk, pvb_iff, and_assoc] using this

/-- The update after a bit 0, `p + ((2048 - p) >> 5)`. -/
theorem Pv.up0 {P : BitVec 32} (h : Pv P) : Pv (P + (2048#32 - P) >>> 5) := h.all.1
/-- The update after a bit 1, `p - (p >> 5)`. -/
theorem Pv.up1 {P : BitVec 32} (h : Pv P) : Pv (P - P >>> 5) := h.all.2.1
/-- The update without a branch, `p + ((k - p) >>s 5)` with `k` 2048 after a bit 0, 31 after a bit 1. -/
theorem Pv.upc {P : BitVec 32} (h : Pv P) (b : Bool) :
    Pv (((if b = true then 2048#32 else 31#32) - P).sshiftRight 5 + P) := by
  cases b
  · exact h.all.2.2.2
  · exact h.all.2.2.1

end FV7z.Lzma
