import FV7z.Start.Stack
/-!
# What `execve` writes on the new stack, run by run (PLAN.md G3, startup)

`runsByte (stackRuns …)` (`Start/Exec.lean`), the stack's bytes at a program's first instruction, for any executable.

- `wordBytes_length`, `stringAddrs_length`, `auxv_length`, `stackWords_length`: the words from `rsp` are
  `1 + (argc + 1) + (envc + 1) + 2 * auxCount` of 8 bytes each.
- `runs_apart`: the three runs lie one above the other: the words end at or below `AT_RANDOM`'s bytes, those and the
  platform string end at or below the strings, and the strings end 8 bytes below the stack's end.
- `runs_words`, `runs_random`, `runs_strings`: the byte at an address of each run.
-/
namespace FV7z.Start
open ZellicX86

theorem wordBytes_length (ws : List Nat) : (wordBytes ws).length = 8 * ws.length := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    simp only [wordBytes, List.flatMap_cons, List.length_append, List.length_cons] at ih ⊢
    have : (toBytesLE (BitVec.ofNat 64 w) 8).length = 8 := by simp [toBytesLE]
    omega

theorem stringAddrs_length : ∀ (x : Nat) (ss : List (List Byte)), (stringAddrs x ss).length = ss.length
  | _, [] => rfl
  | x, s :: ss => by simp only [stringAddrs, List.length_cons, stringAddrs_length (x + s.length + 1) ss]

theorem auxv_length (prof : Profile) (hdr : ElfHeader) (pa : Nat) (a : ExecArgs) (c : ExecChoice)
    (l : StackLayout) : (auxv prof hdr pa a c l).length = auxCount prof.linux := by
  unfold auxv auxCount
  split <;> rfl

theorem stackWords_length (aux : List (Nat × Nat)) (a : ExecArgs) (l : StackLayout) :
    (stackWords aux a l).length = 1 + (a.argv'.length + 1) + (a.envp.length + 1) + 2 * aux.length := by
  have hf : ∀ xs : List (Nat × Nat), (xs.flatMap fun (t, v) => [t, v]).length = 2 * xs.length := by
    intro xs
    induction xs with
    | nil => rfl
    | cons x xs ih =>
      simp only [List.flatMap_cons, List.length_append, List.length_cons, List.length_nil] at ih ⊢
      omega
  simp only [stackWords, List.length_append, List.length_cons, List.length_nil, List.length_take,
    List.length_drop, stringAddrs_length, hf]
  omega

/-- The three runs lie one above the other, below the stack's end. -/
theorem runs_apart {prof : Profile} {hdr : ElfHeader} {phs : List Phdr} {a : ExecArgs} {c : ExecChoice}
    (hT : 2 ^ 46 ≤ c.stackTop) (hA : c.stackAlign < 8192) (hw : a.withinLimits = true) :
    (stackLayout a prof.linux c).sp + (wordBytes (stackWords (auxv prof hdr (phdrAddr hdr phs) a c
        (stackLayout a prof.linux c)) a (stackLayout a prof.linux c))).length ≤
      (stackLayout a prof.linux c).platform - platformString.length - 16 ∧
    (stackLayout a prof.linux c).platform - platformString.length - 16 +
        (toBytesLE c.random 16 ++ platformString).length ≤ (stackLayout a prof.linux c).strings ∧
    (stackLayout a prof.linux c).strings + a.strings.length + 8 = c.stackTop := by
  rw [wordBytes_length, stackWords_length, auxv_length]
  simp only [ExecArgs.withinLimits, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true] at hw
  obtain ⟨⟨⟨⟨-, -⟩, hptr⟩, hS⟩, -⟩ := hw
  have haux : auxCount prof.linux ≤ 23 := by
    unfold auxCount
    split <;> omega
  have hr : (toBytesLE c.random 16).length = 16 := by simp [toBytesLE]
  have hav : a.argv'.length = max a.argv.length 1 := by
    cases h : a.argv with
    | nil => simp [ExecArgs.argv', h]
    | cons x xs =>
      simp only [ExecArgs.argv', h, List.length_cons]
      split
      · rename_i h'
        cases h'
      · simp only [List.length_cons]
        omega
  simp only [stackLayout, platformString, List.length_cons, List.length_nil, List.length_append, hr,
    stkLim, maxArgStrlen] at *
  omega

/-- The byte at an address in three runs that lie one above the other. -/
theorem runsByte3 {a1 a2 a3 : Nat} {b1 b2 b3 : List Byte} (h12 : a1 + b1.length ≤ a2)
    (h23 : a2 + b2.length ≤ a3) (x : Nat) :
    (a1 ≤ x → x < a1 + b1.length →
      runsByte [(a1, b1.toArray), (a2, b2.toArray), (a3, b3.toArray)] x = b1.getD (x - a1) 0) ∧
    (a2 ≤ x → x < a2 + b2.length →
      runsByte [(a1, b1.toArray), (a2, b2.toArray), (a3, b3.toArray)] x = b2.getD (x - a2) 0) ∧
    (a3 ≤ x → x < a3 + b3.length →
      runsByte [(a1, b1.toArray), (a2, b2.toArray), (a3, b3.toArray)] x = b3.getD (x - a3) 0) := by
  refine ⟨fun h1 h2 => ?_, fun h1 h2 => ?_, fun h1 h2 => ?_⟩
  · have c1 : decide (a1 ≤ x ∧ x < a1 + b1.toArray.size) = true := by
      simp only [List.size_toArray, decide_eq_true_eq]
      omega
    simp only [runsByte, List.find?_cons, c1]
    simp
  · have c1 : decide (a1 ≤ x ∧ x < a1 + b1.toArray.size) = false := by
      simp only [List.size_toArray, decide_eq_false_iff_not]
      omega
    have c2 : decide (a2 ≤ x ∧ x < a2 + b2.toArray.size) = true := by
      simp only [List.size_toArray, decide_eq_true_eq]
      omega
    simp only [runsByte, List.find?_cons, c1, c2]
    simp
  · have c1 : decide (a1 ≤ x ∧ x < a1 + b1.toArray.size) = false := by
      simp only [List.size_toArray, decide_eq_false_iff_not]
      omega
    have c2 : decide (a2 ≤ x ∧ x < a2 + b2.toArray.size) = false := by
      simp only [List.size_toArray, decide_eq_false_iff_not]
      omega
    have c3 : decide (a3 ≤ x ∧ x < a3 + b3.toArray.size) = true := by
      simp only [List.size_toArray, decide_eq_true_eq]
      omega
    simp only [runsByte, List.find?_cons, c1, c2, c3]
    simp

/-- The byte `execve` writes at an address of the new stack: of the words from `rsp`, of `AT_RANDOM`'s bytes and
the platform string, of the argument and environment strings. -/
theorem runs_byte {prof : Profile} {hdr : ElfHeader} {phs : List Phdr} {a : ExecArgs} {c : ExecChoice}
    (hT : 2 ^ 46 ≤ c.stackTop) (hA : c.stackAlign < 8192) (hw : a.withinLimits = true) (x : Nat) :
    ((stackLayout a prof.linux c).sp ≤ x → x < (stackLayout a prof.linux c).sp +
        (wordBytes (stackWords (auxv prof hdr (phdrAddr hdr phs) a c (stackLayout a prof.linux c)) a
          (stackLayout a prof.linux c))).length →
      runsByte (stackRuns prof hdr phs a c) x =
        (wordBytes (stackWords (auxv prof hdr (phdrAddr hdr phs) a c (stackLayout a prof.linux c)) a
          (stackLayout a prof.linux c))).getD (x - (stackLayout a prof.linux c).sp) 0) ∧
    ((stackLayout a prof.linux c).platform - platformString.length - 16 ≤ x →
      x < (stackLayout a prof.linux c).platform - platformString.length - 16 +
        (toBytesLE c.random 16 ++ platformString).length →
      runsByte (stackRuns prof hdr phs a c) x = (toBytesLE c.random 16 ++ platformString).getD
        (x - ((stackLayout a prof.linux c).platform - platformString.length - 16)) 0) ∧
    ((stackLayout a prof.linux c).strings ≤ x → x < (stackLayout a prof.linux c).strings + a.strings.length →
      runsByte (stackRuns prof hdr phs a c) x = a.strings.getD (x - (stackLayout a prof.linux c).strings) 0) := by
  obtain ⟨h12, h23, -⟩ := runs_apart (prof := prof) (hdr := hdr) (phs := phs) hT hA hw
  exact runsByte3 h12 h23 x

/-- `execve` takes fewer than `2 ^ 31` arguments and environment strings (`MAX_ARG_STRINGS`). -/
theorem args_lt {a : ExecArgs} (hw : a.withinLimits = true) : a.argv'.length < 2 ^ 31 ∧ a.envp.length < 2 ^ 31 := by
  simp only [ExecArgs.withinLimits, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true] at hw
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, -⟩, -⟩, -⟩, -⟩ := hw
  have hav : a.argv'.length = max a.argv.length 1 := by
    cases h : a.argv with
    | nil => simp [ExecArgs.argv', h]
    | cons x xs =>
      simp only [ExecArgs.argv', h, List.length_cons]
      split
      · rename_i h'
        cases h'
      · simp only [List.length_cons]
        omega
  simp only [maxArgStrings] at h1 h2
  omega

/-- A count below `2 ^ 31`, read as a 32-bit `int` and sign-extended, is itself. -/
theorem sext_small {n : Nat} (h : n < 2 ^ 31) :
    BitVec.signExtend 64 ((BitVec.ofNat 64 n).setWidth 32) = BitVec.ofNat 64 n := by
  have hm : ((BitVec.ofNat 64 n).setWidth 32).msb = false := by
    rw [BitVec.msb_eq_decide]
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat, decide_eq_false_iff_not]
    omega
  rw [BitVec.signExtend_eq_setWidth_of_msb_false hm]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega

/-- `execve` takes environment strings of fewer than `MAX_ARG_STRLEN` (131072) bytes. -/
theorem env_len {a : ExecArgs} (hw : a.withinLimits = true) {i : Nat} (hi : i < a.envp.length) :
    (a.envp.getD i []).length + 1 ≤ 131072 := by
  simp only [ExecArgs.withinLimits, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, List.all_eq_true] at hw
  obtain ⟨⟨⟨⟨⟨-, -⟩, hall⟩, -⟩, -⟩, -⟩ := hw
  have hm : a.envp.getD i [] ∈ a.argv' ++ a.envp := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
    exact List.mem_append_right _ (List.getElem_mem hi)
  have := hall _ hm
  simp only [maxArgStrlen] at this
  omega

end FV7z.Start
