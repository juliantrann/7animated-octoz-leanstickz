import FV7z.Strncmp.Vec16
/-!
# The first 16 bytes of a loop of `__strncmp_sse2` (PLAN.md G3, `strncmp`)

A loop's first compare is of the aligned 16 bytes holding the strings' next bytes, `c` bytes before them: the mask
`m` and `edx = 0xffff` are shifted right by `c` (`shr edx, cl; shr r9d, cl`), and `sub edx, r9d` leaves a set bit for
each byte from `c` on that is not the same or is 0 (`shr_sub_bits`): the result is 0 just when there is none
(`shr_sub_zero`), and otherwise its lowest set bit is the first such byte, less `c` (`shr_sub_low`).

- `sub_of_le`: `x - y` is `x ^^^ y` when `y`'s bits are among `x`'s.
-/
namespace FV7z.Strncmp
open ZellicX86

attribute [-simp] BitVec.getLsbD_eq_getElem

theorem sub_of_le {w : Nat} {x y : BitVec w} (h : ∀ i, y.getLsbD i = true → x.getLsbD i = true) :
    x - y = x ^^^ y := by
  rw [BitVec.sub_eq_iff_eq_add, BitVec.add_eq_or_of_and_eq_zero]
  · apply BitVec.eq_of_getLsbD_eq
    intro i _
    rw [BitVec.getLsbD_or, BitVec.getLsbD_xor]
    have := h i
    revert this
    cases x.getLsbD i <;> cases y.getLsbD i <;> decide
  · apply BitVec.eq_of_getLsbD_eq
    intro i _
    rw [BitVec.getLsbD_and, BitVec.getLsbD_xor, BitVec.getLsbD_zero]
    have := h i
    revert this
    cases x.getLsbD i <;> cases y.getLsbD i <;> decide

/-- Bit `i` of `(0xffff >> c) - (m >> c)`: byte `c + i` is one of the 16 and not the same or 0. -/
theorem shr_sub_bits (A B : BitVec 128) (c i : Nat) :
    ((BitVec.ofNat 32 65535 >>> c) - (cmask A B >>> c)).getLsbD i =
      (decide (c + i < 16) && !decide (lane 8 A (c + i) = lane 8 B (c + i) ∧ lane 8 A (c + i) ≠ 0)) := by
  rw [sub_of_le, BitVec.getLsbD_xor, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_ushiftRight, getLsbD_cmask,
    BitVec.getLsbD_ofNat, show (65535 : Nat) = 2 ^ 16 - 1 from rfl, Nat.testBit_two_pow_sub_one]
  · by_cases h : c + i < 16
    · rw [decide_eq_true h, decide_eq_true (by omega : c + i < 32)]
      cases decide (lane 8 A (c + i) = lane 8 B (c + i) ∧ lane 8 A (c + i) ≠ 0) <;> rfl
    · rw [decide_eq_false h]
      cases decide (c + i < 32) <;>
        cases decide (lane 8 A (c + i) = lane 8 B (c + i) ∧ lane 8 A (c + i) ≠ 0) <;> rfl
  · intro j hj
    rw [BitVec.getLsbD_ushiftRight, getLsbD_cmask] at hj
    rw [BitVec.getLsbD_ushiftRight, BitVec.getLsbD_ofNat, show (65535 : Nat) = 2 ^ 16 - 1 from rfl,
      Nat.testBit_two_pow_sub_one]
    by_cases h16 : c + j < 16
    · rw [decide_eq_true h16, decide_eq_true (by omega : c + j < 32)]
      rfl
    · rw [decide_eq_false h16, Bool.false_and] at hj
      exact absurd hj (by decide)

/-- `(0xffff >> c) - (m >> c)` is 0 just when the bytes from `c` on are the same and not 0. -/
theorem shr_sub_zero (A B : BitVec 128) (c : Nat) :
    (BitVec.ofNat 32 65535 >>> c) - (cmask A B >>> c) = 0 ↔
      ∀ j, c ≤ j → j < 16 → lane 8 A j = lane 8 B j ∧ lane 8 A j ≠ 0 := by
  constructor
  · intro h j hcj hj
    have e := congrArg (fun z : BitVec 32 => z.getLsbD (j - c)) h
    simp only at e
    rw [shr_sub_bits, show c + (j - c) = j by omega, decide_eq_true hj, Bool.true_and,
      Strlen.getLsbD_zero'] at e
    simpa using e
  · intro h
    apply BitVec.eq_of_getLsbD_eq
    intro i _
    rw [shr_sub_bits, Strlen.getLsbD_zero']
    by_cases hi : c + i < 16
    · rw [decide_eq_true hi, decide_eq_true (h _ (by omega) hi)]
      rfl
    · rw [decide_eq_false hi]
      rfl

/-- The first byte from `c` on that is not the same or is 0, at `p`: `(0xffff >> c) - (m >> c)`, as `rdx`, is not 0
and has `p - c` as lowest set bit. -/
theorem shr_sub_low (A B : BitVec 128) {c p : Nat} (hcp : c ≤ p) (hp : p < 16)
    (hf : ¬ (lane 8 A p = lane 8 B p ∧ lane 8 A p ≠ 0))
    (ht : ∀ i, c ≤ i → i < p → lane 8 A i = lane 8 B i ∧ lane 8 A i ≠ 0) :
    ((BitVec.ofNat 32 65535 >>> c) - (cmask A B >>> c)).setWidth 64 ≠ 0 ∧
      lowestSetBit (((BitVec.ofNat 32 65535 >>> c) - (cmask A B >>> c)).setWidth 64) = p - c := by
  have h1 : ((BitVec.ofNat 32 65535 >>> c) - (cmask A B >>> c)).getLsbD (p - c) = true := by
    rw [shr_sub_bits, show c + (p - c) = p by omega, decide_eq_true hp, decide_eq_false hf]
    rfl
  have hnz : (BitVec.ofNat 32 65535 >>> c) - (cmask A B >>> c) ≠ 0 := fun h => by
    rw [h, Strlen.getLsbD_zero'] at h1
    exact absurd h1 (by decide)
  refine ⟨sw64_ne_zero hnz, ?_⟩
  rw [lsb_sw hnz]
  refine lowestSetBit_eq (by omega) h1 fun i hi => ?_
  rw [shr_sub_bits, decide_eq_true (by omega : c + i < 16), decide_eq_true (ht _ (by omega) (by omega))]
  rfl

end FV7z.Strncmp
