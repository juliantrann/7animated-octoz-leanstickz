/-!
# `cmp x, n` then `jbe`/`ja`, unsigned (PLAN.md §M, M1)

After `cmp r, imm`, `wpx` leaves `jbe`'s condition (`CF ∨ ZF`) as `decide (x.toNat < n) || decide (x = n)`: that is
`x ≤ n` (`be_imm`), and `ja`'s its negation.
-/
namespace FV7z

/-- `cmp x, n` then `jbe`: taken just when `x ≤ n`, unsigned. -/
theorem be_imm {w : Nat} (x : BitVec w) (n : Nat) (hn : n < 2 ^ w) :
    (decide (x.toNat < n) || decide (x = BitVec.ofNat w n)) = decide (x.toNat ≤ n) := by
  by_cases h : x.toNat < n
  · rw [decide_eq_true h, decide_eq_true (Nat.le_of_lt h)]
    rfl
  · by_cases h' : x.toNat = n
    · have e : x = BitVec.ofNat w n :=
        BitVec.eq_of_toNat_eq (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]; exact h')
      rw [decide_eq_false h, decide_eq_true e, decide_eq_true (Nat.le_of_eq h')]
      rfl
    · have e : x ≠ BitVec.ofNat w n := fun e => h' (by rw [e, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn])
      rw [decide_eq_false h, decide_eq_false e, decide_eq_false (show ¬ x.toNat ≤ n by omega)]
      rfl

end FV7z
