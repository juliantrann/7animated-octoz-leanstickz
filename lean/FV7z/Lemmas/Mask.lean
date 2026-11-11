import FV7z.Lemmas.Ins
/-!
# Byte masks (PLAN.md G2.1)

The vector idiom of `memcmp`, `strcmp` and kin: `VPCMPEQB` sets each byte where two vectors agree to `0xff`
(`elem_eqb`), `VPMOVMSKB` gathers the bytes' top bits into a mask (`movmsk_eqb`), and then
- `SUB mask, 2^k - 1` is 0 exactly when all `k` bytes agree (`mask_sub_eq_zero`), and otherwise its lowest set bit, as
  `TZCNT` (or `BSF`) finds it, is the first byte where they differ (`mask_sub_lowest`);
- `VPTEST v, ones` sets `CF` exactly when every bit of `v` is set (`vptest_cf`).
-/
namespace FV7z
open ZellicX86

attribute [-simp] BitVec.getLsbD_eq_getElem

/-! ## `VPCMPEQB` -/

theorem elem_eqb {w : Nat} (a b : BitVec w) {j : Nat} (hj : j < w / 8) :
    elem 8 (eqb a b) j = if elem 8 a j = elem 8 b j then BitVec.allOnes 8 else 0 := by
  simp only [eqb, lanes]
  rw [elem_ofElems (by decide) _ hj]
  simp [beq_iff_eq]

theorem getLsbD_eqb {w : Nat} (hw : w % 8 = 0) (a b : BitVec w) (i : Nat) :
    (eqb a b).getLsbD i = (decide (i < w) && decide (elem 8 a (i / 8) = elem 8 b (i / 8))) := by
  simp only [eqb, lanes]
  rw [getLsbD_ofElems w 8 (by decide)]
  by_cases hi : i < w
  · have h8 : i / 8 < w / 8 := by omega
    have hm : i % 8 < 8 := Nat.mod_lt _ (by decide)
    by_cases h : elem 8 a (i / 8) = elem 8 b (i / 8)
    · simp only [h, beq_self_eq_true, ↓reduceIte, BitVec.getLsbD_allOnes, hm, hi, h8, decide_true, Bool.and_self]
    · simp [h]
  · simp [hi]

theorem eqb_self {w : Nat} (hw : w % 8 = 0) (a : BitVec w) : eqb a a = BitVec.allOnes w := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [getLsbD_eqb hw]
  simp [hi]

theorem msb_eqb {w : Nat} (a b : BitVec w) {j : Nat} (hj : j < w / 8) :
    (elem 8 (eqb a b) j).msb = decide (elem 8 a j = elem 8 b j) := by
  rw [elem_eqb a b hj]
  by_cases h : elem 8 a j = elem 8 b j
  · simp only [h, ↓reduceIte, decide_true]; exact BitVec.msb_allOnes (by decide)
  · simp [h]

/-- The mask `VPMOVMSKB` makes of `VPCMPEQB`'s result, through a vector register. -/
theorem movmsk_eqb {w : Nat} (hw : w ≤ 512) (a b : BitVec w) :
    (ofBits 32 fun j => decide (j < w / 8) && (elem 8 (((eqb a b).setWidth 512).setWidth w) j).msb) =
      ofBits 32 fun j => decide (j < w / 8) && decide (elem 8 a j = elem 8 b j) := by
  rw [BitVec.setWidth_setWidth_of_le _ hw, BitVec.setWidth_eq]
  apply ofBits_congr
  intro j _
  by_cases hj : j < w / 8
  · simp [hj, msb_eqb a b hj]
  · simp [hj]

/-! ## The mask, less all ones -/

theorem sub_eq_zero_iff {w : Nat} (x y : BitVec w) : x - y = 0 ↔ x = y :=
  ⟨fun h => by have := BitVec.sub_add_cancel x y; rw [h] at this; simp at this; exact this.symm,
    fun h => by simp [h]⟩

/-- The `k` bits of a mask are all set: the mask less `2 ^ k - 1` is 0. -/
theorem mask_sub_eq_zero {k : Nat} (hk : k ≤ 32) (f : Nat → Bool) :
    (ofBits 32 (fun j => decide (j < k) && f j) - BitVec.ofNat 32 (2 ^ k - 1) = 0) ↔ ∀ j < k, f j = true := by
  rw [sub_eq_zero_iff]
  constructor
  · intro h j hj
    have := congrArg (fun x : BitVec 32 => x.getLsbD j) h
    simp only [getLsbD_ofBits, BitVec.getLsbD_ofNat, Nat.testBit_two_pow_sub_one] at this
    simpa [show j < 32 by omega, hj] using this
  · intro h
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [getLsbD_ofBits, BitVec.getLsbD_ofNat, Nat.testBit_two_pow_sub_one, hi, decide_true, Bool.true_and]
    by_cases hik : i < k
    · simp [hik, h i hik]
    · simp [hik]

/-- Some bit of `k` is clear: the first. -/
theorem exists_first (f : Nat → Bool) : ∀ {k : Nat}, (∃ j < k, f j = false) →
    ∃ p < k, f p = false ∧ ∀ i < p, f i = true
  | 0, ⟨_, h, _⟩ => absurd h (Nat.not_lt_zero _)
  | k + 1, h => by
    by_cases h' : ∃ j < k, f j = false
    · obtain ⟨p, hp, hf, ht⟩ := exists_first f h'
      exact ⟨p, by omega, hf, ht⟩
    · obtain ⟨j, hj, hf⟩ := h
      have hjk : j = k := by
        by_cases hjk : j < k
        · exact absurd ⟨j, hjk, hf⟩ h'
        · omega
      subst hjk
      refine ⟨j, by omega, hf, fun i hi => ?_⟩
      by_cases hfi : f i = true
      · exact hfi
      · exact absurd ⟨i, hi, by simpa using hfi⟩ h'

theorem find?_range (P : Nat → Bool) : ∀ {n p : Nat}, p < n → P p = true → (∀ i < p, P i = false) →
    (List.range n).find? P = some p
  | 0, _, h, _, _ => absurd h (Nat.not_lt_zero _)
  | n + 1, p, hp, h1, h0 => by
    rw [List.range_succ, List.find?_append]
    by_cases hpn : p < n
    · rw [find?_range P hpn h1 h0]; rfl
    · have hpn' : p = n := by omega
      subst hpn'
      rw [List.find?_eq_none.2 (fun x hx => by simp [h0 x (List.mem_range.1 hx)])]
      simp [h1]

theorem lowestSetBit_eq {w : Nat} {x : BitVec w} {p : Nat} (hp : p < w) (h1 : x.getLsbD p = true)
    (h0 : ∀ i < p, x.getLsbD i = false) : lowestSetBit x = p := by
  unfold lowestSetBit
  rw [find?_range _ hp h1 h0]
  rfl

/-- Some of the `k` bits of a mask is clear: the mask less `2 ^ k - 1` has the first as its lowest set bit. -/
theorem mask_sub_lowest {k : Nat} (hk : k ≤ 32) (f : Nat → Bool) {p : Nat} (hp : p < k) (hf : f p = false)
    (ht : ∀ i < p, f i = true) :
    lowestSetBit (ofBits 32 (fun j => decide (j < k) && f j) - BitVec.ofNat 32 (2 ^ k - 1)) = p := by
  generalize hM : ofBits 32 (fun j => decide (j < k) && f j) = M
  have hMb : M.toNat % 2 ^ (p + 1) = 2 ^ p - 1 := by
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_mod_two_pow, BitVec.testBit_toNat, ← hM, getLsbD_ofBits, Nat.testBit_two_pow_sub_one]
    by_cases hip : i < p
    · simp [hip, show i < p + 1 by omega, show i < 32 by omega, show i < k by omega, ht i hip]
    · by_cases hip' : i = p
      · subst hip'; simp [hf]
      · simp [hip, show ¬ i < p + 1 by omega]
  have hk1 : 1 ≤ 2 ^ k := Nat.one_le_two_pow
  have hc : (BitVec.ofNat 32 (2 ^ k - 1)).toNat = 2 ^ k - 1 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
    have : 2 ^ k ≤ 2 ^ 32 := Nat.pow_le_pow_right (by decide) hk
    omega
  have hr : (M - BitVec.ofNat 32 (2 ^ k - 1)).toNat % 2 ^ (p + 1) = 2 ^ p := by
    rw [BitVec.toNat_sub, hc, Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by omega : p + 1 ≤ 32))]
    have e32 : 2 ^ 32 = 2 ^ (p + 1) * 2 ^ (31 - p) := by rw [← Nat.pow_add]; congr 1; omega
    have ek : 2 ^ k = 2 ^ (p + 1) * 2 ^ (k - (p + 1)) := by rw [← Nat.pow_add]; congr 1; omega
    have hXY : 2 ^ (k - (p + 1)) ≤ 2 ^ (31 - p) := Nat.pow_le_pow_right (by decide) (by omega)
    have hm := Nat.mul_le_mul_left (2 ^ (p + 1)) hXY
    have hsub := Nat.mul_sub (2 ^ (p + 1)) (2 ^ (31 - p)) (2 ^ (k - (p + 1)))
    have e : 2 ^ 32 - (2 ^ k - 1) + M.toNat =
        2 ^ (p + 1) * (2 ^ (31 - p) - 2 ^ (k - (p + 1))) + (M.toNat + 1) := by
      rw [hsub, e32, ek]; rw [ek] at hk1; omega
    rw [e, Nat.mul_add_mod, Nat.add_mod, hMb]
    have hp1 : 1 ≤ 2 ^ p := Nat.one_le_two_pow
    have hlt : 2 ^ p < 2 ^ (p + 1) := Nat.pow_lt_pow_right (by decide) (by omega)
    rw [Nat.mod_eq_of_lt (show 1 < 2 ^ (p + 1) by omega), show 2 ^ p - 1 + 1 = 2 ^ p by omega,
      Nat.mod_eq_of_lt hlt]
  have hbit : ∀ i < p + 1, (M - BitVec.ofNat 32 (2 ^ k - 1)).getLsbD i = decide (p = i) := fun i hi => by
    rw [← BitVec.testBit_toNat]
    have := Nat.testBit_mod_two_pow (M - BitVec.ofNat 32 (2 ^ k - 1)).toNat (p + 1) i
    rw [hr, Nat.testBit_two_pow] at this
    simp only [hi, decide_true, Bool.true_and] at this
    exact this.symm
  apply lowestSetBit_eq (by omega)
  · simpa using hbit p (by omega)
  · intro i hi
    simpa [show p ≠ i by omega] using hbit i (by omega)

/-! ## `VPTEST` -/

/-- `VPTEST v, ones` sets `CF` exactly when every bit of `v` is set. -/
theorem vptest_cf (Y : BitVec 256) :
    ((~~~Y &&& BitVec.allOnes 256) == 0) = true ↔ ∀ i < 256, Y.getLsbD i = true := by
  rw [beq_iff_eq]
  constructor
  · intro e i hi
    have := congrArg (fun x : BitVec 256 => x.getLsbD i) e
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_not, BitVec.getLsbD_allOnes, BitVec.getLsbD_zero, hi, decide_true,
      Bool.true_and, Bool.and_true] at this
    rw [show (0 : BitVec 256).getLsbD i = false from BitVec.getLsbD_zero] at this
    simpa using this
  · intro h
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp [h i hi]

end FV7z
