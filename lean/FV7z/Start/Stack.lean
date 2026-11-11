import FV7z.Start.Exec
/-!
# Where `execve` puts the initial stack pointer (PLAN.md G3, startup)

Arithmetic on Zellic's `stackLayout` (`Spec/Linux/Exec.lean`), for any executable.

- `stack_room`: for a choice the kernel can make of the stack's end and alignment, arguments within `execve`'s limits
  (`ExecArgs.withinLimits`, which `execve` checks) and with room for `n` bytes (`StackRoom`): the initial `rsp` is a
  multiple of 16; the stack's mapping is as `setup_arg_pages` made it (`start = reserved`: it was not grown), a whole
  number of pages, and has at least `n` bytes below `rsp`; and it lies in the top `2 ^ 35` bytes below
  `DEFAULT_MAP_WINDOW` (`stackTopMax`), far above where a program linked low has its segments.
- `ExecStart.limits`: a state `execve` starts a program in is one whose arguments were within the limits.
- `ExecStart.rsp`: so in such a state, with `StackRoom a n`, `rsp` is a multiple of 16 between
  `2 ^ 47 - 2 ^ 35 + n` and `2 ^ 47`.
-/
namespace FV7z.Start
open ZellicX86

theorem stack_room {a : ExecArgs} {lb : LinuxBoot} {c : ExecChoice} {n : Nat}
    (hT : c.stackTop % 4096 = 0 ∧ stackTopMax - 2 ^ 22 * 4096 ≤ c.stackTop ∧ c.stackTop ≤ stackTopMax)
    (hA : c.stackAlign < 8192) (hw : a.withinLimits = true) (hroom : StackRoom a n) :
    (stackLayout a lb c).sp % 16 = 0 ∧ (stackLayout a lb c).reserved + n ≤ (stackLayout a lb c).sp ∧
      (stackLayout a lb c).start = (stackLayout a lb c).reserved ∧ (stackLayout a lb c).reserved % 4096 = 0 ∧
      (stackLayout a lb c).sp < c.stackTop ∧ 2 ^ 47 - 2 ^ 35 ≤ (stackLayout a lb c).reserved ∧
      c.stackTop ≤ 2 ^ 47 := by
  obtain ⟨hT1, hT2, hT3⟩ := hT
  obtain ⟨hr1, hr2⟩ := hroom
  simp only [ExecArgs.withinLimits, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true] at hw
  obtain ⟨⟨⟨⟨-, -⟩, hptr⟩, hS⟩, -⟩ := hw
  have haux : auxCount lb ≤ 23 := by
    unfold auxCount
    split <;> omega
  simp only [stackLayout, pageDown, pageUp, stackTopMax, platformString, List.length_cons, List.length_nil,
    stkLim, maxArgStrlen] at *
  omega

/-- A conditional that gives `.ok s` and whose first branch does not, has a false condition. -/
theorem ite_not {c : Prop} [Decidable c] {A B : ExecResult} {s : State} (h : (if c then A else B) = .ok s)
    (hA : A ≠ .ok s) : ¬ c := by
  intro hc
  simp only [hc, ↓reduceIte] at h
  exact hA h

theorem ExecStart.limits {prof : Profile} {files : Files} {exe : FileId} {a : ExecArgs} {k : KernelConfig}
    {s₀ : State} (h : ExecStart prof files exe a k s₀) : a.withinLimits = true := by
  obtain ⟨-, c, -, he⟩ := h
  unfold execve at he
  split at he
  · cases he
  replace he := ite_ok he (by intro h; cases h)
  replace he := ite_ok he (by intro h; cases h)
  have hn := ite_not he (by intro h; cases h)
  simpa using hn

/-- Where `rsp` is in a state `execve` starts a program in, when the arguments leave room for `n` bytes of stack. -/
theorem ExecStart.rsp {prof : Profile} {files : Files} {exe : FileId} {a : ExecArgs} {k : KernelConfig}
    {s₀ : State} {n : Nat} (h : ExecStart prof files exe a k s₀) (hroom : StackRoom a n) :
    s₀.cpu.gpr.rsp.toNat % 16 = 0 ∧ 2 ^ 47 - 2 ^ 35 + n ≤ s₀.cpu.gpr.rsp.toNat ∧ s₀.cpu.gpr.rsp.toNat < 2 ^ 47 := by
  obtain ⟨hdr, phs, c, -, hv, hc⟩ := ExecStart.cpu h
  obtain ⟨h16, hn, -, -, hlt, hlo, htop⟩ :=
    stack_room (lb := prof.linux) hv.stackTop hv.stackAlign (ExecStart.limits h) hroom
  have e : s₀.cpu.gpr.rsp = BitVec.ofNat 64 (stackLayout a prof.linux c).sp := by rw [hc]; rfl
  have hlt' : (stackLayout a prof.linux c).sp < 2 ^ 64 := by omega
  rw [e, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt']
  omega

end FV7z.Start
