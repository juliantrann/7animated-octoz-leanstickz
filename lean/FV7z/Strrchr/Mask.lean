import FV7z.Strlen.Mask
import FV7z.Lemmas.Sse2b
/-!
# The masks of `__strrchr_sse2` (PLAN.md G2)

`strrchr` keeps two masks of the bytes it looks at: where a byte is 0 (`Z`, as `strlen`'s) and where it is the
character (`M`, `pcmpeqb` against the spread character). `lea y, [z - 1]; xor y, z` keeps the bits of `Z` up to its
lowest set bit `p` (`getLsbD_blsmsk`), `and` drops the matches after the first 0, and `bsr` gives the last match left
(`highestSetBit_eq`).
-/
namespace FV7z
open ZellicX86

attribute [-simp] BitVec.getLsbD_eq_getElem

namespace Strrchr

/-- `y = z - 1` and `z`'s low `p + 1` bits `2 ^ p`: the two differ just in the bits up to `p`. -/
theorem testBit_pred {y z p : Nat} (hz : z % 2 ^ (p + 1) = 2 ^ p) (hy : y + 1 = z) (i : Nat) :
    (y.testBit i ^^ z.testBit i) = decide (i ≤ p) := by
  have hp1 : 1 ≤ 2 ^ p := Nat.one_le_two_pow
  have hlt : 2 ^ p < 2 ^ (p + 1) := Nat.pow_lt_pow_right (by decide) (by omega)
  have hP : 0 < 2 ^ (p + 1) := by omega
  have ez := Nat.div_add_mod z (2 ^ (p + 1))
  rw [hz] at ez
  generalize z / 2 ^ (p + 1) = q at ez
  subst ez
  have ey : y = 2 ^ (p + 1) * q + (2 ^ p - 1) := by
    generalize 2 ^ (p + 1) * q = A at hy ⊢
    omega
  subst ey
  by_cases hi : i ≤ p
  · have e1 := Nat.testBit_mod_two_pow (2 ^ (p + 1) * q + (2 ^ p - 1)) (p + 1) i
    rw [Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega), Nat.testBit_two_pow_sub_one,
      decide_eq_true (show i < p + 1 by omega), Bool.true_and] at e1
    have e2 := Nat.testBit_mod_two_pow (2 ^ (p + 1) * q + 2 ^ p) (p + 1) i
    rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hlt, Nat.testBit_two_pow,
      decide_eq_true (show i < p + 1 by omega), Bool.true_and] at e2
    rw [← e1, ← e2, decide_eq_true hi]
    by_cases h : i < p
    · rw [decide_eq_true h, decide_eq_false (show ¬ p = i by omega)]
      rfl
    · rw [decide_eq_false h, decide_eq_true (show p = i by omega)]
      rfl
  · have e1 := Nat.testBit_div_two_pow (n := p + 1) (2 ^ (p + 1) * q + (2 ^ p - 1)) (i - (p + 1))
    rw [Nat.mul_add_div hP, Nat.div_eq_of_lt (by omega), Nat.add_zero, Nat.sub_add_cancel (by omega)] at e1
    have e2 := Nat.testBit_div_two_pow (n := p + 1) (2 ^ (p + 1) * q + 2 ^ p) (i - (p + 1))
    rw [Nat.mul_add_div hP, Nat.div_eq_of_lt hlt, Nat.add_zero, Nat.sub_add_cancel (by omega)] at e2
    rw [← e1, ← e2, Bool.xor_self, decide_eq_false hi]

/-- `lea y, [z - 1]; xor y, z`: the bits up to the lowest set bit `p` of `z`. -/
theorem getLsbD_blsmsk {w : Nat} {Y Z : BitVec w} {p : Nat} (h1 : Z.getLsbD p = true)
    (h0 : ∀ i < p, Z.getLsbD i = false) (hY : Y.toNat + 1 = Z.toNat) (i : Nat) :
    (Y ^^^ Z).getLsbD i = decide (i ≤ p) := by
  rw [BitVec.getLsbD_xor, ← BitVec.testBit_toNat, ← BitVec.testBit_toNat]
  refine testBit_pred ?_ hY i
  apply Nat.eq_of_testBit_eq
  intro k
  rw [Nat.testBit_mod_two_pow, BitVec.testBit_toNat, Nat.testBit_two_pow]
  by_cases hk : k < p
  · rw [h0 k hk, decide_eq_false (show ¬ p = k by omega), Bool.and_false]
  · by_cases hk' : k = p
    · subst hk'
      rw [h1, decide_eq_true (show k < k + 1 by omega), decide_eq_true rfl]
      rfl
    · rw [decide_eq_false (show ¬ k < p + 1 by omega), decide_eq_false (show ¬ p = k by omega), Bool.false_and]

theorem find?_range_rev (P : Nat → Bool) :
    ∀ {n q : Nat}, q < n → P q = true → (∀ i, q < i → i < n → P i = false) → (List.range n).reverse.find? P = some q
  | 0, _, h, _, _ => absurd h (Nat.not_lt_zero _)
  | n + 1, q, hq, h1, h0 => by
    rw [List.range_succ, List.reverse_append, List.reverse_singleton, List.singleton_append]
    by_cases hqn : q = n
    · subst hqn
      simp only [List.find?_cons, h1]
    · simp only [List.find?_cons, h0 n (by omega) (by omega)]
      exact find?_range_rev P (by omega) h1 fun i h h' => h0 i h (by omega)

/-- `bsr`: the set bit with none above it. -/
theorem highestSetBit_eq {w : Nat} {x : BitVec w} {q : Nat} (hq : q < w) (h1 : x.getLsbD q = true)
    (h0 : ∀ i, q < i → i < w → x.getLsbD i = false) : highestSetBit x = q := by
  unfold highestSetBit
  rw [find?_range_rev _ hq h1 h0]
  rfl

/-- `pcmpeqb` against the spread character: the byte's top bit says whether the two bytes agree. -/
theorem msb_peqb (a b : BitVec 128) {j : Nat} (hj : j < 16) :
    (lane 8 (peqb a b) j).msb = decide (lane 8 a j = lane 8 b j) := by
  rw [peqb, lane_ofBytes _ hj]
  by_cases h : lane 8 a j = lane 8 b j
  · rw [if_pos h, decide_eq_true h]
    exact BitVec.msb_allOnes (by decide)
  · rw [if_neg h, decide_eq_false h]
    decide

/-- Bit `i` of the mask of a vector compared with the spread character `c`. -/
theorem getLsbD_cmask (a : BitVec 128) (c : BitVec 64) (i : Nat) :
    (pmsk (peqb a (ofDwords fun j => lane 32 (ofWords (interleave 16 0
      (ofBytes (interleave 8 0 ((c.setWidth 32).setWidth 128) ((c.setWidth 32).setWidth 128)))
      (ofBytes (interleave 8 0 ((c.setWidth 32).setWidth 128) ((c.setWidth 32).setWidth 128)))))
      (0 / 4 ^ j % 4)))).getLsbD i = (decide (i < 16) && decide (lane 8 a i = c.setWidth 8)) := by
  rw [getLsbD_pmsk]
  by_cases hi : i < 16
  · rw [msb_peqb _ _ hi, lane_bcast c hi]
  · rw [decide_eq_false hi, Bool.false_and, Bool.false_and]

end Strrchr
end FV7z
