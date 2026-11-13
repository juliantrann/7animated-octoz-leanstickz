/-!
# `ksplit`: a goal over `lo ≤ k ≤ hi` as one goal per value of `k` (PLAN.md G3, `malloc`)

The verification conditions of `_int_malloc` for a class of request sizes are proved one `wpx` per chunk size `16 k`:
`ksplit k from lo using h1 h2` (`h1 : lo ≤ k`, `h2 : k ≤ hi`) puts `k = lo + j`, `j ≤ hi - lo`, and peels `j = 0`,
`j = i + 1`, … down the bound. The value is left as `lo + (0 + 1 + … + 1)`: `simp only [Nat.reduceAdd,
Nat.reduceMul]` makes it a numeral. Each step is a term (`kpeel`, `kdec`, `kzero`), not `omega`: `omega` sees
the whole context, and with the bounds of the verification conditions (`toNat` of sums, `2 ^ 64`) a failing call did
not come back in six hours. (No `interval_cases` without Mathlib; `omega` on a disjunction of fifty cases splits
`2 ^ 50` ways.)
-/
namespace FV7z

/-- `j` is 0 or a successor. -/
theorem kpeel (j : Nat) : j = 0 ∨ ∃ i, j = i + 1 :=
  match j with
  | 0 => .inl rfl
  | i + 1 => .inr ⟨i, rfl⟩

/-- `k` from `lo` on. -/
theorem kbase {lo k : Nat} (h : lo ≤ k) : ∃ j, k = lo + j := ⟨k - lo, (Nat.add_sub_of_le h).symm⟩

/-- The bound on the step. -/
theorem kbound {lo j hi : Nat} (h : lo + j ≤ hi) : j ≤ hi - lo := by omega

/-- One step down the bound. -/
theorem kdec {j m : Nat} (h : j + 1 ≤ m + 1) : j ≤ m := Nat.le_of_succ_le_succ h

/-- Past the bound. -/
theorem kzero {j : Nat} (h : j + 1 ≤ 0) : False := Nat.not_succ_le_zero _ h

/-- `ksplit k from lo using h1 h2`: with `h1 : lo ≤ k` and `h2 : k ≤ hi`, one goal for each `k` from `lo` to `hi`. -/
syntax "ksplit " ident " from " num " using " ident ident : tactic
macro_rules
  | `(tactic| ksplit $k from $lo using $h1 $h2) => `(tactic| (
      obtain ⟨j, rfl⟩ := FV7z.kbase (lo := $lo) $h1
      have hb := FV7z.kbound $h2
      simp only [Nat.reduceSub] at hb
      repeat' (first
        | exact (FV7z.kzero hb).elim
        | (rcases FV7z.kpeel j with rfl | ⟨j, rfl⟩
           try replace hb := FV7z.kdec hb))))

example (k : Nat) (h1 : 3 ≤ k) (h2 : k ≤ 6) : 6 ≤ k * 2 ∧ k * 2 ≤ 12 := by
  ksplit k from 3 using h1 h2 <;> decide

end FV7z
