import FV7z.Start.Runs
/-!
# The words `execve` writes from `rsp`, one by one (PLAN.md G3, startup)

Zellic's `stackWords` (`Spec/Linux/Exec.lean`), for any arguments.

- `flat_getD`: the type and the value of the `n`-th entry of the auxiliary vector among its words.
- `stackWords_get`: word 0 is `argc`; then the `argv` pointers and a null; the `envp` pointers and a null; then the
  auxiliary vector's entries, two words each.
-/
namespace FV7z.Start
open ZellicX86

theorem getD_skip {α : Type} (A B : List α) (d : α) (k : Nat) : (A ++ B).getD (A.length + k) d = B.getD k d := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left]

theorem getD_in {α : Type} (A B : List α) (d : α) {k : Nat} (h : k < A.length) :
    (A ++ B).getD k d = A.getD k d := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem flat_getD : ∀ (aux : List (Nat × Nat)) (n : Nat), n < aux.length →
    (aux.flatMap fun (t, v) => [t, v]).getD (2 * n) 0 = (aux.getD n (0, 0)).1 ∧
    (aux.flatMap fun (t, v) => [t, v]).getD (2 * n + 1) 0 = (aux.getD n (0, 0)).2
  | [], _, h => by cases h
  | (t, v) :: aux, 0, _ => ⟨rfl, rfl⟩
  | (t, v) :: aux, n + 1, h => by
    have ih := flat_getD aux n (by simpa using h)
    have e1 : 2 * (n + 1) = 2 * n + 2 := by omega
    have e2 : 2 * (n + 1) + 1 = 2 * n + 1 + 2 := by omega
    rw [e2, e1]
    exact ih

theorem stackWords_get (aux : List (Nat × Nat)) (a : ExecArgs) (l : StackLayout) :
    (stackWords aux a l).getD 0 0 = a.argv'.length ∧
    (∀ i < a.argv'.length, (stackWords aux a l).getD (1 + i) 0 =
      (stringAddrs l.strings (a.argv' ++ a.envp)).getD i 0) ∧
    (stackWords aux a l).getD (1 + a.argv'.length) 0 = 0 ∧
    (∀ i < a.envp.length, (stackWords aux a l).getD (1 + a.argv'.length + 1 + i) 0 =
      (stringAddrs l.strings (a.argv' ++ a.envp)).getD (a.argv'.length + i) 0) ∧
    (stackWords aux a l).getD (1 + a.argv'.length + 1 + a.envp.length) 0 = 0 ∧
    (∀ n < aux.length,
      (stackWords aux a l).getD (1 + a.argv'.length + 1 + a.envp.length + 1 + 2 * n) 0 = (aux.getD n (0, 0)).1 ∧
      (stackWords aux a l).getD (1 + a.argv'.length + 1 + a.envp.length + 1 + (2 * n + 1)) 0 =
        (aux.getD n (0, 0)).2) := by
  obtain ⟨P, hPdef⟩ : ∃ P, P = stringAddrs l.strings (a.argv' ++ a.envp) := ⟨_, rfl⟩
  have hP : P.length = a.argv'.length + a.envp.length := by
    rw [hPdef, stringAddrs_length, List.length_append]
  rw [← hPdef]
  have hT : (P.take a.argv'.length).length = a.argv'.length := by
    rw [List.length_take]
    omega
  have hD : (P.drop a.argv'.length).length = a.envp.length := by
    rw [List.length_drop]
    omega
  have e : stackWords aux a l = [a.argv'.length] ++ (P.take a.argv'.length ++ ([0] ++
      (P.drop a.argv'.length ++ ([0] ++ aux.flatMap fun (t, v) => [t, v])))) := by
    rw [hPdef]
    simp only [stackWords, List.append_assoc]
  have s1 : ∀ (B : List Nat) (k : Nat), ([a.argv'.length] ++ B).getD (1 + k) 0 = B.getD k 0 :=
    fun B k => getD_skip [a.argv'.length] B 0 k
  have s2 : ∀ (B : List Nat) (k : Nat), (P.take a.argv'.length ++ B).getD (a.argv'.length + k) 0 = B.getD k 0 := by
    intro B k
    have := getD_skip (P.take a.argv'.length) B 0 k
    rwa [hT] at this
  have s3 : ∀ (B : List Nat) (k : Nat), ([0] ++ B).getD (1 + k) 0 = B.getD k 0 :=
    fun B k => getD_skip [0] B 0 k
  have s4 : ∀ (B : List Nat) (k : Nat), (P.drop a.argv'.length ++ B).getD (a.envp.length + k) 0 = B.getD k 0 := by
    intro B k
    have := getD_skip (P.drop a.argv'.length) B 0 k
    rwa [hD] at this
  rw [e]
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    rw [s1, getD_in _ _ _ (by omega)]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_take, hi, ↓reduceIte]
  · have := s2 ([0] ++ (P.drop a.argv'.length ++ ([0] ++ aux.flatMap fun (t, v) => [t, v]))) 0
    rw [Nat.add_zero] at this
    rw [s1, this]
    rfl
  · intro i hi
    rw [Nat.add_assoc 1, Nat.add_assoc 1, s1, Nat.add_assoc, s2, s3, getD_in _ _ _ (by omega)]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_drop]
  · have := s4 ([0] ++ aux.flatMap fun (t, v) => [t, v]) 0
    rw [Nat.add_zero] at this
    rw [Nat.add_assoc 1, Nat.add_assoc 1, s1, Nat.add_assoc, s2, s3, this]
    rfl
  · intro n hn
    obtain ⟨f1, f2⟩ := flat_getD aux n hn
    constructor
    · rw [Nat.add_assoc 1, Nat.add_assoc 1, Nat.add_assoc 1, Nat.add_assoc 1, s1, Nat.add_assoc, Nat.add_assoc,
        Nat.add_assoc, s2, s3, s4, s3, f1]
    · rw [Nat.add_assoc 1, Nat.add_assoc 1, Nat.add_assoc 1, Nat.add_assoc 1, s1, Nat.add_assoc, Nat.add_assoc,
        Nat.add_assoc, s2, s3, s4, s3, f2]

end FV7z.Start
