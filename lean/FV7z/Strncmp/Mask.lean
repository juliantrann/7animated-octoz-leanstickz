import FV7z.Strlen.Mask
import FV7z.Lemmas.Sse2d
/-!
# The masks of `__strncmp_sse2` (PLAN.md G3, `strncmp`)

`__strncmp_sse2` compares 16 bytes `a` of one string with 16 bytes `b` of the other by `pxor xmm0, xmm0`,
`pcmpeqb xmm0, a`, `pcmpeqb a, b`, `psubb a, xmm0`, `pmovmskb`: bit `j` of the mask is set where byte `j` of `a` and
of `b` are equal and not 0 (`cmask`, `getLsbD_cmask`). In the shifted loops `b` is two aligned vectors of the other
string lined up by `psrldq`, `pslldq` and `por` (`lane_shr`, `lane_shl`, `lane_or`, `lane_align`).
-/
namespace FV7z
open ZellicX86

attribute [-simp] BitVec.getLsbD_eq_getElem

namespace Strncmp

/-- The mask of 16 bytes `a` against `b`: bit `j` where byte `j` of each is the same and not 0. -/
def cmask (a b : BitVec 128) : BitVec 32 := pmsk (psb (peqb a b) (peqb 0 a))

theorem peqb_comm (a b : BitVec 128) : peqb a b = peqb b a := by
  unfold peqb
  congr 1
  funext j
  by_cases h : lane 8 a j = lane 8 b j
  · rw [if_pos h, if_pos h.symm]
  · rw [if_neg h, if_neg (Ne.symm h)]

theorem msb_cm (a b : BitVec 128) {j : Nat} (hj : j < 16) :
    (lane 8 (psb (peqb a b) (peqb 0 a)) j).msb = decide (lane 8 a j = lane 8 b j ∧ lane 8 a j ≠ 0) := by
  simp only [psb, peqb, lane_ofBytes _ hj, lane_zero]
  generalize lane 8 a j = x
  generalize lane 8 b j = y
  by_cases h1 : x = y <;> by_cases h2 : (0 : BitVec 8) = x
  · rw [if_pos h1, if_pos h2, decide_eq_false fun h => h.2 h2.symm]
    decide
  · rw [if_pos h1, if_neg h2, decide_eq_true ⟨h1, fun h => h2 h.symm⟩]
    decide
  · rw [if_neg h1, if_pos h2, decide_eq_false fun h => h1 h.1]
    decide
  · rw [if_neg h1, if_neg h2, decide_eq_false fun h => h1 h.1]
    decide

theorem getLsbD_cmask (a b : BitVec 128) (i : Nat) :
    (cmask a b).getLsbD i = (decide (i < 16) && decide (lane 8 a i = lane 8 b i ∧ lane 8 a i ≠ 0)) := by
  rw [cmask, getLsbD_pmsk]
  by_cases h : i < 16
  · rw [msb_cm a b h]
  · simp [h]

/-- `psrldq x, k`: byte `j` is byte `j + k`, or 0. -/
theorem lane_shr (x : BitVec 128) (k : Nat) {j : Nat} (hj : j < 16) :
    lane 8 (x >>> (8 * k)) j = if j + k < 16 then lane 8 x (j + k) else 0 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  unfold lane
  rw [BitVec.getLsbD_extractLsb', BitVec.getLsbD_ushiftRight]
  split
  · rw [BitVec.getLsbD_extractLsb', show 8 * k + (8 * j + i) = 8 * (j + k) + i by omega]
  · rw [BitVec.getLsbD_of_ge x _ (by omega), Bool.and_false]
    exact BitVec.getLsbD_zero.symm

/-- `pslldq x, k`: byte `j` is byte `j - k`, or 0. -/
theorem lane_shl (x : BitVec 128) (k : Nat) {j : Nat} (hj : j < 16) :
    lane 8 (x <<< (8 * k)) j = if k ≤ j then lane 8 x (j - k) else 0 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  unfold lane
  rw [BitVec.getLsbD_extractLsb', BitVec.getLsbD_shiftLeft]
  split
  · have e1 : 8 * j + i < 128 := by omega
    have e2 : ¬ 8 * j + i < 8 * k := by omega
    rw [BitVec.getLsbD_extractLsb', show 8 * j + i - 8 * k = 8 * (j - k) + i by omega]
    simp [e1, e2]
  · have e2 : 8 * j + i < 8 * k := by omega
    simp [e2]

theorem lane_or (x y : BitVec 128) (j : Nat) : lane 8 (x ||| y) j = lane 8 x j ||| lane 8 y j := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp [lane, BitVec.getLsbD_extractLsb', BitVec.getLsbD_or, hi]

/-- `pslldq q, 16 - k; psrldq p, k; por q, p`: the 16 bytes from byte `k` of `p` on, then of `q`. -/
theorem lane_align (p q : BitVec 128) {k j : Nat} (hk : k ≤ 16) (hj : j < 16) :
    lane 8 ((q <<< (8 * (16 - k))) ||| (p >>> (8 * k))) j =
      if j + k < 16 then lane 8 p (j + k) else lane 8 q (j + k - 16) := by
  rw [lane_or, lane_shr p k hj, lane_shl q (16 - k) hj]
  by_cases h : j + k < 16
  · rw [if_pos h, if_neg (by omega)]
    exact BitVec.zero_or (x := _)
  · rw [if_neg h, if_pos (by omega), show j - (16 - k) = j + k - 16 by omega]
    exact BitVec.or_zero (x := _)

end Strncmp
end FV7z
