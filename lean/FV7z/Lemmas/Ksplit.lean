/-!
# `ksplit`: a goal over `lo ≤ k ≤ hi` as one goal per value of `k` (PLAN.md G3, `malloc`)

The verification conditions of `_int_malloc` for a class of request sizes are proved one `wpx` per chunk size `16 k`:
`ksplit k from lo to hi using h1 h2` (`h1 : lo ≤ k`, `h2 : k ≤ hi`) is `hi - lo + 1` steps written out by the macro,
each `rcases kstep (lo := N) h1 with e | h1` and `subst e` (the goal `k = N`, and `N + 1 ≤ k` on), the last
`N + 1 ≤ k ≤ hi` closed by `decide`. `k` is left as the numeral `N`. `subst`, not an `rfl` pattern: in the macro
`rfl` is a hygienic name `rfl✝`. No loop: an earlier `repeat'` of `omega` (which sees the whole context of the
verification condition, `toNat` of sums and `2 ^ 64`) did not come back in six hours, and a `repeat'` of peeling
steps did not end. (No `interval_cases` without Mathlib; `omega` on a disjunction of fifty cases splits `2 ^ 50`
ways.)
-/
namespace FV7z

/-- `k` is `lo` or above. -/
theorem kstep {lo k : Nat} (h : lo ≤ k) : k = lo ∨ lo + 1 ≤ k := by omega

/-- `ksplit k from lo to hi using h1 h2`: with `h1 : lo ≤ k` and `h2 : k ≤ hi`, one goal for each `k` from `lo` to
`hi` (in that order), `k` the numeral. -/
syntax "ksplit " ident " from " num " to " num " using " ident ident : tactic
macro_rules
  | `(tactic| ksplit $k from $lo to $hi using $h1 $h2) => do
    let a := lo.getNat
    let b := hi.getNat
    let mut steps : Array (Lean.TSyntax `tactic) := #[]
    for i in List.range (b + 1 - a) do
      let n := Lean.Syntax.mkNumLit (toString (a + i))
      steps := steps.push (← `(tactic| rcases FV7z.kstep (k := $k) (lo := $n) $h1 with e | $h1:ident))
      steps := steps.push (← `(tactic| subst e))
      steps := steps.push (← `(tactic| rotate_left))
    steps := steps.push (← `(tactic| exact absurd (Nat.le_trans $h1 $h2) (by decide)))
    let seq : Lean.Syntax.TSepArray `tactic ";" := .ofElems steps
    `(tactic| ($seq;*))

example (k : Nat) (h1 : 3 ≤ k) (h2 : k ≤ 6) : 6 ≤ k * 2 ∧ k * 2 ≤ 12 := by
  ksplit k from 3 to 6 using h1 h2 <;> decide

example (k : Nat) (h1 : 5 ≤ k) (h2 : k ≤ 5) : k = 5 := by
  ksplit k from 5 to 5 using h1 h2 <;> rfl

end FV7z
