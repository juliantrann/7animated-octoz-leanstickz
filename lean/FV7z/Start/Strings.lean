import FV7z.Start.Words
import FV7z.Start.StackWords
/-!
# The argument and environment strings on the initial stack (PLAN.md G3, startup)

Zellic's `stringAddrs` and `ExecArgs.strings` (`Spec/Linux/Exec.lean`), for any arguments.

- `stringAddrs_getD_append`: the address of a string does not depend on the strings after it.
- `strings_at`: the `i`-th of strings laid out from `x`, each with its NUL, lies within them at its address
  (`stringAddrs`), byte by byte.
- `env_bytes`: where memory holds `ExecArgs.strings` from `x`, the bytes at the address of the `i`-th environment
  string are that string's and a NUL.
-/
namespace FV7z.Start
open ZellicX86

theorem stringAddrs_getD_append : ∀ (x : Nat) (A B : List (List Byte)) (i : Nat), i < A.length →
    (stringAddrs x (A ++ B)).getD i 0 = (stringAddrs x A).getD i 0
  | _, [], _, _, h => by cases h
  | _, _ :: _, _, 0, _ => rfl
  | x, s :: A, B, i + 1, h => by
    simp only [List.cons_append, stringAddrs, List.getD_cons_succ]
    exact stringAddrs_getD_append _ A B i (by simpa using h)

theorem strings_at : ∀ (ss : List (List Byte)) (x i : Nat), i < ss.length →
    x ≤ (stringAddrs x ss).getD i 0 ∧
    (stringAddrs x ss).getD i 0 + (ss.getD i []).length + 1 ≤ x + (ss.flatMap fun s => s ++ [0]).length ∧
    ∀ k, k ≤ (ss.getD i []).length →
      (ss.flatMap fun s => s ++ [0]).getD ((stringAddrs x ss).getD i 0 - x + k) 0 = (ss.getD i [] ++ [0]).getD k 0
  | [], _, _, h => by cases h
  | s :: ss, x, 0, _ => by
    simp only [stringAddrs, List.getD_cons_zero, List.flatMap_cons, List.length_append, List.length_cons,
      List.length_nil]
    refine ⟨Nat.le_refl _, by omega, ?_⟩
    intro k hk
    rw [Nat.sub_self, Nat.zero_add]
    exact getD_in _ _ _ (by simp only [List.length_append, List.length_cons, List.length_nil]; omega)
  | s :: ss, x, i + 1, h => by
    obtain ⟨h1, h2, h3⟩ := strings_at ss (x + s.length + 1) i (by simpa using h)
    simp only [stringAddrs, List.getD_cons_succ, List.flatMap_cons, List.length_append, List.length_cons,
      List.length_nil] at h2 ⊢
    refine ⟨by omega, by omega, ?_⟩
    intro k hk
    have e : (stringAddrs (x + s.length + 1) ss).getD i 0 - x + k =
        (s ++ [0]).length + ((stringAddrs (x + s.length + 1) ss).getD i 0 - (x + s.length + 1) + k) := by
      simp only [List.length_append, List.length_cons, List.length_nil]
      omega
    rw [e, getD_skip]
    exact h3 k hk

theorem env_bytes {s : State} {a : ExecArgs} {x : Nat} (hB : Bytes s (BitVec.ofNat 64 x) a.strings) {i : Nat}
    (hi : i < a.envp.length) {k : Nat} (hk : k ≤ (a.envp.getD i []).length) :
    s.proc.mm.mem.readByte
        (BitVec.ofNat 64 ((stringAddrs x (a.argv' ++ a.envp)).getD (a.argv'.length + i) 0 + k)) =
      (a.envp.getD i [] ++ [0]).getD k 0 := by
  have hidx : a.argv'.length + i < (a.argv' ++ a.envp ++ [a.filename]).length := by
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega
  obtain ⟨h1, h2, h3⟩ := strings_at (a.argv' ++ a.envp ++ [a.filename]) x _ hidx
  have eA : (stringAddrs x (a.argv' ++ a.envp ++ [a.filename])).getD (a.argv'.length + i) 0 =
      (stringAddrs x (a.argv' ++ a.envp)).getD (a.argv'.length + i) 0 :=
    stringAddrs_getD_append x _ _ _ (by simp only [List.length_append]; omega)
  have eS : (a.argv' ++ a.envp ++ [a.filename]).getD (a.argv'.length + i) [] = a.envp.getD i [] := by
    rw [List.append_assoc, getD_skip, getD_in _ _ _ hi]
  rw [eA] at h1
  rw [eA, eS] at h2 h3
  have hb := bytes_at hB (i := (stringAddrs x (a.argv' ++ a.envp)).getD (a.argv'.length + i) 0 - x + k) (by
    unfold ExecArgs.strings
    omega)
  have e2 : x + ((stringAddrs x (a.argv' ++ a.envp)).getD (a.argv'.length + i) 0 - x + k) =
      (stringAddrs x (a.argv' ++ a.envp)).getD (a.argv'.length + i) 0 + k := by omega
  rw [e2] at hb
  rw [hb]
  exact h3 k hk

/-- The `i`-th environment string lies within the strings laid out from `x`. -/
theorem env_in (a : ExecArgs) (x : Nat) {i : Nat} (hi : i < a.envp.length) :
    x ≤ (stringAddrs x (a.argv' ++ a.envp)).getD (a.argv'.length + i) 0 ∧
    (stringAddrs x (a.argv' ++ a.envp)).getD (a.argv'.length + i) 0 + (a.envp.getD i []).length + 1 ≤
      x + a.strings.length := by
  have hidx : a.argv'.length + i < (a.argv' ++ a.envp ++ [a.filename]).length := by
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega
  obtain ⟨h1, h2, -⟩ := strings_at (a.argv' ++ a.envp ++ [a.filename]) x _ hidx
  have eA : (stringAddrs x (a.argv' ++ a.envp ++ [a.filename])).getD (a.argv'.length + i) 0 =
      (stringAddrs x (a.argv' ++ a.envp)).getD (a.argv'.length + i) 0 :=
    stringAddrs_getD_append x _ _ _ (by simp only [List.length_append]; omega)
  have eS : (a.argv' ++ a.envp ++ [a.filename]).getD (a.argv'.length + i) [] = a.envp.getD i [] := by
    rw [List.append_assoc, getD_skip, getD_in _ _ _ hi]
  rw [eA] at h1
  rw [eA, eS] at h2
  exact ⟨h1, h2⟩

end FV7z.Start
