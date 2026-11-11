import ZellicX86.Spec.Process
/-!
# The registers at the first instruction of a program `execve` starts (PLAN.md G3, startup)

On Zellic's model of `execve` alone (`Spec/Linux/Exec.lean`), for any executable.

- `nextSignal_keeps`, `execSignals_keeps`: the signals handled on the way to the first instruction change neither the
  registers nor the address space.
- `ExecStart.start`: in a state `execve` starts a program in (`ExecStart`), the registers are `entryCpu`'s (`rip` the
  file's entry, `rsp` where `stackLayout` puts the argument count, every other general register 0), and the address
  space is `regionsMemory` of the vsyscall page's, the stack's, the segments' (`loadRegions`) and the vDSO's regions.
  `ExecStart.cpu`: its part about the registers.
-/
namespace FV7z.Start
open ZellicX86

theorem nextSignal_keeps {s s₁ : State} {q : Queued} (h : nextSignal s = some (q, s₁)) :
    s₁.cpu = s.cpu ∧ s₁.proc.mm = s.proc.mm := by
  unfold nextSignal at h
  simp only at h
  split at h
  · obtain ⟨q', -, hq⟩ := Option.map_eq_some_iff.1 h
    cases hq
    exact ⟨rfl, rfl⟩
  · split at h
    · obtain ⟨⟨q', tp'⟩, -, hq⟩ := Option.map_eq_some_iff.1 h
      cases hq
      exact ⟨rfl, rfl⟩
    · split at h
      · obtain ⟨⟨q', pp⟩, -, hq⟩ := Option.map_eq_some_iff.1 h
        cases hq
        exact ⟨rfl, rfl⟩
      · cases h

theorem execSignals_keeps : ∀ (n : Nat) {s s' : State}, execSignals n s = .ok s' →
    s'.cpu = s.cpu ∧ s'.proc.mm = s.proc.mm
  | 0, _, _, h => by simp [execSignals] at h
  | n + 1, s, s', h => by
    unfold execSignals at h
    split at h
    · cases h
      exact ⟨rfl, rfl⟩
    · rename_i q s₁ hn
      have h1 := nextSignal_keeps hn
      have ih : execSignals n s₁ = .ok s' → s'.cpu = s.cpu ∧ s'.proc.mm = s.proc.mm := fun h' =>
        ⟨(execSignals_keeps n h').1.trans h1.1, (execSignals_keeps n h').2.trans h1.2⟩
      simp only at h
      split at h
      · split at h
        · exact ih h
        · split at h
          · cases h
          · cases h
          · cases h
          · exact ih h
          · exact ih h
      · exact ih h

/-- A conditional that gives `.ok s` and whose first branch does not, gives it by its second. -/
theorem ite_ok {c : Prop} [Decidable c] {A B : ExecResult} {s : State} (h : (if c then A else B) = .ok s)
    (hA : A ≠ .ok s) : B = .ok s := by
  split at h
  · exact absurd h hA
  · exact h

/-- What `execve` writes on the new stack (address, bytes): the words from `rsp` (`stackWords`: `argc`, the `argv`
and `envp` pointers, the auxiliary vector), `AT_RANDOM`'s 16 bytes with the platform string, and the argument and
environment strings. -/
def stackRuns (prof : Profile) (hdr : ElfHeader) (phs : List Phdr) (a : ExecArgs) (c : ExecChoice) :
    List (Nat × Array Byte) :=
  [((stackLayout a prof.linux c).sp,
      (wordBytes (stackWords (auxv prof hdr (phdrAddr hdr phs) a c (stackLayout a prof.linux c)) a
        (stackLayout a prof.linux c))).toArray),
    ((stackLayout a prof.linux c).platform - platformString.length - 16,
      (toBytesLE c.random 16 ++ platformString).toArray),
    ((stackLayout a prof.linux c).strings, a.strings.toArray)]

/-- A state `execve` starts a program in: the registers are `entryCpu`'s, and the address space is made of the legacy
vsyscall page's region, the stack's (readable and writable, from `StackLayout.start` to the stack's end, holding
`stackRuns` and zeros elsewhere), those of
the loadable segments (`loadRegions`), and the vDSO's two where the kernel maps one, a later one replacing an earlier one where they overlap (`regionsMemory`), over the files as they
are but for the executable's being write-denied. -/
theorem ExecStart.start {prof : Profile} {files : Files} {exe : FileId} {a : ExecArgs} {k : KernelConfig}
    {s₀ : State} (h : ExecStart prof files exe a k s₀) :
    ∃ hdr phs c segs stack post gd, readElf files exe = some (hdr, phs) ∧ c.Valid prof.linux phs a k ∧
      s₀.cpu = entryCpu hdr.entry (stackLayout a prof.linux c).sp k.initPkru ∧
      loadRegions prof.feat files exe k (stackLayout a prof.linux c).start c.stackTop phs = .ok segs ∧
      s₀.proc.mm.mem = regionsMemory (vsyscallRegions prof.linux.vsyscall ++ (stack :: segs ++ post))
        { files with denyWrite := fun f => decide (f = exe) || files.denyWrite f } gd ∧
      (∀ r ∈ post, prof.linux.vdso = true ∧ ((r.first = c.vdsoBase / 4096 ∧ r.count = 6) ∨
        (r.first = c.vdsoText / 4096 ∧ r.count = prof.linux.vdsoText.length))) ∧
      stack.first = (stackLayout a prof.linux c).start / 4096 ∧
      stack.count = (c.stackTop - (stackLayout a prof.linux c).start) / 4096 ∧ stack.prot.read = true ∧
      stack.prot.write = true ∧ ∀ i, stack.backing i = .priv fun o =>
        runsByte (stackRuns prof hdr phs a c) ((stackLayout a prof.linux c).start + 4096 * i + o.toNat) := by
  obtain ⟨-, c, hv, he⟩ := h
  unfold execve at he
  cases hr : readElf files exe with
  | none =>
    simp only [hr] at he
    split at he
    · cases he
    repeat (replace he := ite_ok he (by intro h; cases h))
    cases he
  | some hp =>
    obtain ⟨hdr, phs⟩ := hp
    simp only [hr] at he
    split at he
    · cases he
    repeat (replace he := ite_ok he (by intro h; cases h))
    generalize hl : loadRegions prof.feat files exe k _ _ phs = r at he
    cases r with
    | killed => cases he
    | notModelled w => cases he
    | ok segs =>
      dsimp only at he
      repeat (replace he := ite_ok he (by intro h; cases h))
      refine ⟨hdr, phs, c, segs, _, _, _, rfl, hv hdr phs hr, (execSignals_keeps _ he).1, hl,
        congrArg (·.mem) (execSignals_keeps _ he).2, ?_, rfl, rfl, rfl, rfl, fun _ => rfl⟩
      intro r hr
      split at hr
      · rename_i hvd
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact ⟨hvd, .inl ⟨rfl, rfl⟩⟩
        · exact ⟨hvd, .inr ⟨rfl, rfl⟩⟩
      · cases hr

theorem ExecStart.cpu {prof : Profile} {files : Files} {exe : FileId} {a : ExecArgs} {k : KernelConfig} {s₀ : State}
    (h : ExecStart prof files exe a k s₀) :
    ∃ hdr phs c, readElf files exe = some (hdr, phs) ∧ c.Valid prof.linux phs a k ∧
      s₀.cpu = entryCpu hdr.entry (stackLayout a prof.linux c).sp k.initPkru := by
  obtain ⟨hdr, phs, c, -, -, -, -, hr, hv, hc, -⟩ := ExecStart.start h
  exact ⟨hdr, phs, c, hr, hv, hc⟩

end FV7z.Start
