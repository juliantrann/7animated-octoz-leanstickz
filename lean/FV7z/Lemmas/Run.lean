import ZellicX86.Spec.Statement
/-!
# Runs: pieces of a run that compose (PLAN.md G2.0)

`ReachOrEndsIn` (Zellic, `Spec/Statement.lean`) speaks of one run from a call's entry to its return. A proof goes
through the code a basic block at a time; this module gives the pieces: `Runs I s t P E`, some number of steps from
`s` (answers from position `t` of the oracle) to a state with `P` or an end with `E`, every state before satisfying
`I`; `RunsFrom`, the same with the system-call events made before `s` (`pre`); and how they compose (`RunsFrom.bind`,
a block followed by the rest), loop (`runsFrom_loop`, a variant that decreases), take one step (`runsFrom_step`), and
give `ReachOrEndsIn` (`reachOrEndsIn_of_runsFrom`).

The design follows the lemmas of Zellic's proof exports (`Runs`, `RunsFrom`, `RunsFrom.bind`, `runsFrom_loop`, …,
read with `tools/zexport/pp.py`); the definitions and proofs here are this project's.
-/
namespace FV7z
open ZellicX86

/-- `run` of `n + 1` steps is one step, then `n`. -/
theorem run_succ (prof : Profile) (o : Oracle) (n : Nat) (s : State) (t : Nat) :
    run prof o (n + 1) s t =
      match (step prof s).runStream o t with
      | (.running s' ev, t') =>
        match run prof o n s' t' with
        | (st, evs, t'') => (st, ev.toList ++ evs, t'')
      | (.stopped out, t') => (.done out, [], t') := rfl

/-- How the run of `n + m` steps is that of `n`, then that of `m` from where it stands. -/
def runThen (prof : Profile) (o : Oracle) (m : Nat) : Status × List Event × Nat → Status × List Event × Nat
  | (.running s', evs, t') =>
    match run prof o m s' t' with
    | (st, evs', t'') => (st, evs ++ evs', t'')
  | r => r

theorem runThen_zero (prof : Profile) (o : Oracle) (r : Status × List Event × Nat) : runThen prof o 0 r = r := by
  rcases r with ⟨st, evs, t⟩
  cases st <;> simp [runThen, run]

theorem run_add (prof : Profile) (o : Oracle) (n m : Nat) (s : State) (t : Nat) :
    run prof o (n + m) s t = runThen prof o m (run prof o n s t) := by
  induction n generalizing s t with
  | zero => simp [run, runThen]
  | succ n ih =>
    rw [show n + 1 + m = (n + m) + 1 by omega, run_succ, run_succ]
    rcases h : (step prof s).runStream o t with ⟨r, t'⟩
    cases r with
    | running s' ev =>
      simp only [ih]
      rcases run prof o n s' t' with ⟨st, evs, t''⟩
      cases st with
      | running X => simp [runThen]
      | done out => simp [runThen]
    | stopped out => simp [runThen]

/-- Every state the run from `s` is in after fewer than `n` steps satisfies `I`. -/
def Passes (prof : Profile) (o : Oracle) (I : State → Prop) (n : Nat) (s : State) (t : Nat) : Prop :=
  ∀ m < n, ∀ s' evs t', run prof o m s t = (.running s', evs, t') → I s'

/-- Some run from `s` (answers from position `t`) reaches, without ending, a state `X` (next position `T`, events
`evs` on the way) with `P X T evs`, or ends with an outcome `out` and events `evs` with `E out evs`; and every state
before satisfies `I`. -/
def Runs (prof : Profile) (o : Oracle) (I : State → Prop) (s : State) (t : Nat)
    (P : State → Nat → List Event → Prop) (E : Outcome → List Event → Prop) : Prop :=
  ∃ n st evs T, run prof o n s t = (st, evs, T) ∧ Passes prof o I n s t ∧
    match st with
    | .running X => P X T evs
    | .done out => E out evs

/-- `Runs`, with the events `pre` made before `s` put before the run's own. -/
def RunsFrom (prof : Profile) (o : Oracle) (I : State → Prop) (pre : List Event) (s : State) (t : Nat)
    (P : State → Nat → List Event → Prop) (E : Outcome → List Event → Prop) : Prop :=
  Runs prof o I s t (fun X T evs => P X T (pre ++ evs)) (fun out evs => E out (pre ++ evs))

variable {prof : Profile} {o : Oracle} {I : State → Prop} {pre : List Event} {s : State} {t : Nat}
  {P Q : State → Nat → List Event → Prop} {E : Outcome → List Event → Prop}

/-- Nothing to run: `s` itself. -/
theorem runsFrom_done (h : P s t pre) : RunsFrom prof o I pre s t P E :=
  ⟨0, .running s, [], t, rfl, fun _ h => absurd h (Nat.not_lt_zero _), by simpa using h⟩

/-- A step that keeps running (`ev`: the system call it made, if any), from a state with `I`. -/
theorem runsFrom_step {s' : State} {ev : Option Event} {t' : Nat} (hI : I s)
    (h : (step prof s).runStream o t = (.running s' ev, t'))
    (k : RunsFrom prof o I (pre ++ ev.toList) s' t' P E) : RunsFrom prof o I pre s t P E := by
  obtain ⟨n, st, evs, T, hr, hp, hpe⟩ := k
  refine ⟨n + 1, st, ev.toList ++ evs, T, ?_, ?_, ?_⟩
  · rw [run_succ, h]; simp [hr]
  · intro m hm s'' evs'' t'' hm'
    cases m with
    | zero => simp [run] at hm'; exact hm'.1 ▸ hI
    | succ m =>
      rw [run_succ, h] at hm'
      dsimp only at hm'
      rcases hr' : run prof o m s' t' with ⟨st', evs', t'''⟩
      rw [hr'] at hm'
      simp only [Prod.mk.injEq] at hm'
      obtain ⟨rfl, -, -⟩ := hm'
      exact hp m (by omega) _ _ _ hr'
  · cases st <;> simpa [List.append_assoc] using hpe

/-- A step that ends the run, from a state with `I`. -/
theorem runsFrom_stop {out : Outcome} {t' : Nat} (hI : I s)
    (h : (step prof s).runStream o t = (.stopped out, t')) (k : E out pre) : RunsFrom prof o I pre s t P E := by
  refine ⟨1, .done out, [], t', ?_, ?_, by simpa using k⟩
  · rw [run_succ, h]
  · intro m hm s'' evs'' t'' hm'
    have : m = 0 := by omega
    subst this; simp [run] at hm'; exact hm'.1 ▸ hI

/-- A run to `Q`, then from every state with `Q` a run to `P`. -/
theorem RunsFrom.bind (h : RunsFrom prof o I pre s t Q E)
    (k : ∀ X T pre', Q X T pre' → RunsFrom prof o I pre' X T P E) : RunsFrom prof o I pre s t P E := by
  obtain ⟨n, st, evs, T, hr, hp, hq⟩ := h
  cases st with
  | done out =>
    exact ⟨n, .done out, evs, T, hr, hp, hq⟩
  | running X =>
    obtain ⟨m, st', evs', T', hr', hp', hpe⟩ := k X T (pre ++ evs) hq
    refine ⟨n + m, st', evs ++ evs', T', ?_, ?_, ?_⟩
    · rw [run_add, hr]; simp [runThen, hr']
    · intro j hj s'' evs'' t'' hj'
      by_cases hjn : j < n
      · exact hp j hjn _ _ _ hj'
      · obtain ⟨i, rfl⟩ : ∃ i, j = n + i := ⟨j - n, by omega⟩
        rw [run_add, hr] at hj'
        simp only [runThen] at hj'
        rcases hri : run prof o i X T with ⟨sti, evsi, ti⟩
        rw [hri] at hj'
        simp only [Prod.mk.injEq] at hj'
        obtain ⟨rfl, -, -⟩ := hj'
        exact hp' i (by omega) _ _ _ hri
    · cases st' <;> simpa [List.append_assoc] using hpe

/-- Case split on a decidable proposition. -/
theorem runsFrom_cases (p : Prop) [Decidable p] (h₁ : p → RunsFrom prof o I pre s t P E)
    (h₂ : ¬p → RunsFrom prof o I pre s t P E) : RunsFrom prof o I pre s t P E :=
  if hp : p then h₁ hp else h₂ hp

/-- A loop: from every state with the invariant `J v` (`v` a variant), a run either back to the invariant with a
smaller variant or to `P`. -/
theorem runsFrom_loop (J : Nat → State → Nat → List Event → Prop)
    (body : ∀ v X T pre, J v X T pre →
      RunsFrom prof o I pre X T (fun Y T' evs => (∃ v' < v, J v' Y T' evs) ∨ P Y T' evs) E) :
    ∀ {v X T pre}, J v X T pre → RunsFrom prof o I pre X T P E := by
  intro v
  induction v using Nat.strongRecOn with
  | _ v ih =>
    intro X T pre h
    refine (body v X T pre h).bind ?_
    rintro Y T' evs (⟨v', hv', hJ⟩ | hP)
    · exact ih v' hv' hJ
    · exact runsFrom_done hP

/-- The statement of a call from the pieces: for every oracle the environment allows and every position, a run from
`s` with no events before it. -/
theorem reachOrEndsIn_of_runsFrom {env : Oracle → Prop} {P : State → List Event → Prop}
    (h : ∀ o, env o → ∀ t, RunsFrom prof o I [] s t (fun X _ evs => P X evs) E) :
    ReachOrEndsIn prof env s I P E := by
  intro o ho t
  obtain ⟨n, st, evs, T, hr, hp, hpe⟩ := h o ho t
  refine ⟨n, st, evs, T, hr, fun m hm s' evs' t' h' => hp m hm s' evs' t' h', ?_⟩
  cases st <;> simpa using hpe

end FV7z
