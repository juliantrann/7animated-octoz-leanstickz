/-!
# `ksplit`: a goal over `lo ≤ k ≤ hi` as one goal per value of `k` (PLAN.md G3, `malloc`)

The verification conditions of `_int_malloc` for a class of request sizes are proved one `wpx` per chunk size `16 k`:
`ksplit k from lo using h1 h2` (`h1 : lo ≤ k`, `h2 : k ≤ hi`) puts `k = lo + j` and `j ≤ hi - lo` (`kbase`), then
peels `j = 0`, `j = i + 1`, … down the bound. The value is left as `lo + (0 + 1 + … + 1)`: `simp only
[Nat.reduceAdd, Nat.reduceMul]` makes it a numeral. Each step is a term (`kpeel`, `kdec`, `kzero`), not `omega`:
`omega` sees the whole context, and with the bounds of the verification conditions (`toNat` of sums, `2 ^ 64`) a
failing call did not come back in six hours. (No `interval_cases` without Mathlib; `omega` on a disjunction of fifty
cases splits `2 ^ 50` ways.)
-/
namespace FV7z

/-- `j` is 0 or a successor. -/
theorem kpeel (j : Nat) : j = 0 ∨ ∃ i, j = i + 1 :=
  match j with
  | 0 => .inl rfl
  | i + 1 => .inr ⟨i, rfl⟩

/-- `k` from `lo` on, the step below `hi - lo`. -/
theorem kbase {lo k hi : Nat} (h1 : lo ≤ k) (h2 : k ≤ hi) : ∃ j, k = lo + j ∧ j ≤ hi - lo :=
  ⟨k - lo, (Nat.add_sub_of_le h1).symm, Nat.sub_le_sub_right h2 lo⟩

/-- One step down the bound (`m - 1` then a numeral: no unification of `m + 1` with a literal). -/
theorem kdec {j m : Nat} (h : j + 1 ≤ m) : j ≤ m - 1 := Nat.le_sub_one_of_lt h

/-- Past the bound. -/
theorem kzero {j : Nat} (h : j + 1 ≤ 0) : False := Nat.not_succ_le_zero _ h

/-- `ksplit k from lo using h1 h2`: with `h1 : lo ≤ k` and `h2 : k ≤ hi`, one goal for each `k` from `lo` to `hi`. -/
syntax "ksplit " ident " from " num " using " ident ident : tactic
macro_rules
  | `(tactic| ksplit $k from $lo using $h1 $h2) => `(tactic| (
      obtain ⟨j, rfl, hb⟩ := FV7z.kbase (lo := $lo) $h1 $h2
      simp only [Nat.reduceSub] at hb
      repeat' (rcases FV7z.kpeel j with rfl | ⟨j, rfl⟩ <;>
        try (first
          | exact (FV7z.kzero hb).elim
          | (replace hb := FV7z.kdec hb; simp only [Nat.reduceSub] at hb)))))

set_option maxHeartbeats 20000 in
example (k : Nat) (h1 : 3 ≤ k) (h2 : k ≤ 6) : 6 ≤ k * 2 ∧ k * 2 ≤ 12 := by
  ksplit k from 3 using h1 h2 <;> decide

set_option maxHeartbeats 20000 in
example (k : Nat) (h1 : 5 ≤ k) (h2 : k ≤ 5) : k = 5 := by
  ksplit k from 5 using h1 h2 <;> rfl

end FV7z
