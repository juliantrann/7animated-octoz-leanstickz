/-!
# `ksplit`: a goal over `lo ≤ k ≤ hi` as one goal per value of `k` (PLAN.md G3, `malloc`)

The verification conditions of `_int_malloc` for a class of request sizes are proved one `wpx` per chunk size `16 k`:
`ksplit k from lo` puts `k = lo + j` and peels `j = 0`, `j = i + 1`, … until the bound `k ≤ hi` among the
hypotheses closes the rest (`omega`). The value is left as `lo + (0 + 1 + … + 1)`: `simp only [Nat.reduceAdd,
Nat.reduceMul]` makes it a numeral. (No `interval_cases` without Mathlib; `omega` on a disjunction of fifty cases
splits `2 ^ 50` ways.)
-/
namespace FV7z

/-- `j` is 0 or a successor. -/
theorem kpeel (j : Nat) : j = 0 ∨ ∃ i, j = i + 1 :=
  match j with
  | 0 => .inl rfl
  | i + 1 => .inr ⟨i, rfl⟩

/-- `ksplit k from lo`: with `lo ≤ k` and `k ≤ hi` among the hypotheses, one goal for each `k` from `lo` to `hi`. -/
syntax "ksplit " ident " from " num : tactic
macro_rules
  | `(tactic| ksplit $k from $lo) => `(tactic| (
      obtain ⟨j, rfl⟩ : ∃ j, $k = $lo + j := ⟨$k - $lo, by omega⟩
      repeat' (first | omega | rcases FV7z.kpeel j with rfl | ⟨j, rfl⟩)))

end FV7z
