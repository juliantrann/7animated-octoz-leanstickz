import FV7z.Lemmas.Sse2
import FV7z.Lemmas.Vec
/-!
# The zero masks of `__strlen_sse2` (PLAN.md M, the PLT contracts)

`strlen`'s SSE2 code compares 16 bytes at a time with 0 (`pcmpeqb` against a zeroed register), takes the top bit of each
byte (`pmovmskb`) and joins four such masks into 64 bits (`shl`, `or`); its loop first folds four vectors with `pminub`,
whose byte is 0 when one of the four bytes is. Bit by bit: bit `i` of a mask says whether byte `i` is 0; shifted right
by `r` (`sar`), the lowest set bit of the joined mask is the first 0 from byte `r` on, and no bit is set if there is
none.
-/
namespace FV7z
open ZellicX86

attribute [-simp] BitVec.getLsbD_eq_getElem

namespace Strlen

theorem getLsbD_zero' {w : Nat} (i : Nat) : (0 : BitVec w).getLsbD i = false := BitVec.getLsbD_zero

/-- The 16 bytes at `a`, as a vector. -/
abbrev rd16 (V : Addr → Byte) (a : Addr) : BitVec 128 := ofBytesLE 128 ((byteAddrs a 16).map V)

theorem lane_rd16 (V : Addr → Byte) (a : Addr) {j : Nat} (hj : j < 16) : lane 8 (rd16 V a) j = V (a.add j) := by
  have hl : ((byteAddrs a 16).map V).length = 16 := by simp [byteAddrs]
  have h := elem_ofBytesLE (w := 128) (bs := (byteAddrs a 16).map V) (j := j) (by omega) (by omega)
  show elem 8 (ofBytesLE 128 ((byteAddrs a 16).map V)) j = V (a.add j)
  rw [h]
  simp [byteAddrs]

theorem lane_zero (j : Nat) : lane 8 (0 : BitVec 128) j = 0 := by
  unfold lane
  exact BitVec.extractLsb'_zero

theorem msb_peqb_zero (a : BitVec 128) {j : Nat} (hj : j < 16) :
    (lane 8 (peqb a 0) j).msb = decide (lane 8 a j = 0) := by
  rw [peqb, lane_ofBytes _ hj, lane_zero]
  by_cases h : lane 8 a j = 0
  · rw [if_pos h, decide_eq_true h]
    exact BitVec.msb_allOnes (by decide)
  · rw [if_neg h, decide_eq_false h]
    decide

theorem msb_zero_peqb (a : BitVec 128) {j : Nat} (hj : j < 16) :
    (lane 8 (peqb 0 a) j).msb = decide (lane 8 a j = 0) := by
  rw [peqb, lane_ofBytes _ hj, lane_zero]
  by_cases h : lane 8 a j = 0
  · rw [if_pos h.symm, decide_eq_true h]
    exact BitVec.msb_allOnes (by decide)
  · rw [if_neg (Ne.symm h), decide_eq_false h]
    decide

theorem lane_pminb_eq_zero (a b : BitVec 128) {j : Nat} (hj : j < 16) :
    lane 8 (pminb a b) j = 0 ↔ lane 8 a j = 0 ∨ lane 8 b j = 0 := by
  rw [pminb, lane_ofBytes _ hj]
  generalize lane 8 a j = x
  generalize lane 8 b j = y
  have e : ∀ z : BitVec 8, z = 0 ↔ z.toNat = 0 := fun z =>
    ⟨fun h => by rw [h]; rfl, fun h => BitVec.eq_of_toNat_eq (by rw [h]; rfl)⟩
  by_cases h : x ≤ y
  · rw [if_pos h]
    rw [BitVec.le_def] at h
    simp only [e]
    omega
  · rw [if_neg h]
    rw [BitVec.le_def] at h
    simp only [e]
    omega

/-- Bit `i` of the mask of a vector compared with 0: whether its byte `i` is 0. -/
theorem getLsbD_zmask (a : BitVec 128) (i : Nat) :
    (pmsk (peqb a 0)).getLsbD i = (decide (i < 16) && decide (lane 8 a i = 0)) := by
  rw [getLsbD_pmsk]
  by_cases hi : i < 16
  · rw [msb_peqb_zero a hi]
  · rw [decide_eq_false hi, Bool.false_and, Bool.false_and]

theorem getLsbD_zmask' (a : BitVec 128) (i : Nat) :
    (pmsk (peqb 0 a)).getLsbD i = (decide (i < 16) && decide (lane 8 a i = 0)) := by
  rw [getLsbD_pmsk]
  by_cases hi : i < 16
  · rw [msb_zero_peqb a hi]
  · rw [decide_eq_false hi, Bool.false_and, Bool.false_and]

/-- The loop's mask, of four vectors folded by `pminub` and compared with 0, is 0 just when no byte of the four is. -/
theorem zmask4_eq_zero (a b c d : BitVec 128) :
    pmsk (peqb (pminb (pminb (pminb a b) c) d) 0) = 0 ↔
      ∀ j < 16, lane 8 a j ≠ 0 ∧ lane 8 b j ≠ 0 ∧ lane 8 c j ≠ 0 ∧ lane 8 d j ≠ 0 := by
  constructor
  · intro h j hj
    have hb := congrArg (fun m => m.getLsbD j) h
    simp only [getLsbD_zmask, getLsbD_zero'] at hb
    rw [decide_eq_true hj, Bool.true_and, decide_eq_false_iff_not, lane_pminb_eq_zero _ _ hj,
      lane_pminb_eq_zero _ _ hj, lane_pminb_eq_zero _ _ hj] at hb
    exact ⟨fun h => hb (Or.inl (Or.inl (Or.inl h))), fun h => hb (Or.inl (Or.inl (Or.inr h))),
      fun h => hb (Or.inl (Or.inr h)), fun h => hb (Or.inr h)⟩
  · intro h
    apply BitVec.eq_of_getLsbD_eq
    intro i _
    rw [getLsbD_zmask, getLsbD_zero']
    by_cases hj : i < 16
    · rw [decide_eq_true hj, Bool.true_and, decide_eq_false_iff_not, lane_pminb_eq_zero _ _ hj,
        lane_pminb_eq_zero _ _ hj, lane_pminb_eq_zero _ _ hj]
      obtain ⟨h1, h2, h3, h4⟩ := h i hj
      intro hh
      rcases hh with ((hh | hh) | hh) | hh
      · exact h1 hh
      · exact h2 hh
      · exact h3 hh
      · exact h4 hh
    · rw [decide_eq_false hj, Bool.false_and]

/-- Bit `i < 64` of four 16-bit masks joined as the code joins them (`rdx`, `rsi`, `r8`, `rcx` at `0x6546d0 + 144`). -/
theorem getLsbD_join (m0 m1 m2 m3 : BitVec 32) (f : Nat → Bool)
    (h0 : ∀ i, m0.getLsbD i = (decide (i < 16) && f i)) (h1 : ∀ i, m1.getLsbD i = (decide (i < 16) && f (i + 16)))
    (h2 : ∀ i, m2.getLsbD i = (decide (i < 16) && f (i + 32)))
    (h3 : ∀ i, m3.getLsbD i = (decide (i < 16) && f (i + 48))) {i : Nat} (hi : i < 64) :
    ((m1.setWidth 64 <<< 16 ||| m0.setWidth 64) ||| (m3.setWidth 64 <<< 16 ||| m2.setWidth 64) <<< 32).getLsbD i =
      f i := by
  have : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12 ∨
    i = 13 ∨ i = 14 ∨ i = 15 ∨ i = 16 ∨ i = 17 ∨ i = 18 ∨ i = 19 ∨ i = 20 ∨ i = 21 ∨ i = 22 ∨ i = 23 ∨ i = 24 ∨
    i = 25 ∨ i = 26 ∨ i = 27 ∨ i = 28 ∨ i = 29 ∨ i = 30 ∨ i = 31 ∨ i = 32 ∨ i = 33 ∨ i = 34 ∨ i = 35 ∨ i = 36 ∨
    i = 37 ∨ i = 38 ∨ i = 39 ∨ i = 40 ∨ i = 41 ∨ i = 42 ∨ i = 43 ∨ i = 44 ∨ i = 45 ∨ i = 46 ∨ i = 47 ∨ i = 48 ∨
    i = 49 ∨ i = 50 ∨ i = 51 ∨ i = 52 ∨ i = 53 ∨ i = 54 ∨ i = 55 ∨ i = 56 ∨ i = 57 ∨ i = 58 ∨ i = 59 ∨ i = 60 ∨
    i = 61 ∨ i = 62 ∨ i = 63 := by omega
  rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  simp [h0, h1, h2, h3]

/-- The same without the first mask (`0x6546d0 + 62`: the first 16 bytes were looked at by then). -/
theorem getLsbD_join3 (m1 m2 m3 : BitVec 32) (f : Nat → Bool)
    (h1 : ∀ i, m1.getLsbD i = (decide (i < 16) && f (i + 16)))
    (h2 : ∀ i, m2.getLsbD i = (decide (i < 16) && f (i + 32)))
    (h3 : ∀ i, m3.getLsbD i = (decide (i < 16) && f (i + 48))) {i : Nat} (hi : i < 64) :
    (m1.setWidth 64 <<< 16 ||| (m3.setWidth 64 <<< 16 ||| m2.setWidth 64) <<< 32).getLsbD i =
      (decide (16 ≤ i) && f i) := by
  have : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12 ∨
    i = 13 ∨ i = 14 ∨ i = 15 ∨ i = 16 ∨ i = 17 ∨ i = 18 ∨ i = 19 ∨ i = 20 ∨ i = 21 ∨ i = 22 ∨ i = 23 ∨ i = 24 ∨
    i = 25 ∨ i = 26 ∨ i = 27 ∨ i = 28 ∨ i = 29 ∨ i = 30 ∨ i = 31 ∨ i = 32 ∨ i = 33 ∨ i = 34 ∨ i = 35 ∨ i = 36 ∨
    i = 37 ∨ i = 38 ∨ i = 39 ∨ i = 40 ∨ i = 41 ∨ i = 42 ∨ i = 43 ∨ i = 44 ∨ i = 45 ∨ i = 46 ∨ i = 47 ∨ i = 48 ∨
    i = 49 ∨ i = 50 ∨ i = 51 ∨ i = 52 ∨ i = 53 ∨ i = 54 ∨ i = 55 ∨ i = 56 ∨ i = 57 ∨ i = 58 ∨ i = 59 ∨ i = 60 ∨
    i = 61 ∨ i = 62 ∨ i = 63 := by omega
  rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  simp [h1, h2, h3]

/-- After `sar` by `r`: the lowest set bit is `n` if bit `n + r` is the first set from `r` on. -/
theorem lsb_sar {Z : BitVec 64} {r n : Nat} (hn : n + r < 64) (h1 : Z.getLsbD (n + r) = true)
    (h0 : ∀ i < n, Z.getLsbD (i + r) = false) : lowestSetBit (Z.sshiftRight r) = n := by
  apply lowestSetBit_eq (by omega)
  · rw [BitVec.getLsbD_sshiftRight, if_pos (by omega), Nat.add_comm r n, h1, decide_eq_false (by omega)]
    rfl
  · intro i hi
    rw [BitVec.getLsbD_sshiftRight, if_pos (by omega), Nat.add_comm r i, h0 i hi, Bool.and_false]

/-- After `sar` by `r`, nothing is set if no bit is from `r` on. -/
theorem sar_eq_zero {Z : BitVec 64} {r : Nat} (hr : r < 64) (h0 : ∀ i, r ≤ i → i < 64 → Z.getLsbD i = false) :
    Z.sshiftRight r = 0 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i _
  rw [BitVec.getLsbD_sshiftRight, getLsbD_zero']
  by_cases h : r + i < 64
  · rw [if_pos h, h0 _ (by omega) h, Bool.and_false]
  · rw [if_neg h, show Z.msb = Z.getLsbD 63 from BitVec.msb_eq_getLsbD_last Z, h0 63 (by omega) (by omega),
      Bool.and_false]

end Strlen
end FV7z
