import FV7z.Start.Exec
/-!
# The whole state `execve` starts a program in (PLAN.md G3, startup)

On Zellic's model of `execve` alone (`Spec/Linux/Exec.lean`), for any executable. `ExecStart.start` says what the
registers and the address space are; here also the program break, the thread, and the regions by name.

- `Pend s s'`: `s'` is `s` but for the pending signals. `nextSignal_pend`, `execSignals_pend`: the signals handled on
  the way to the first instruction change nothing else.
- `stackRegion`, `vdsoRegions`: the stack's region and the vDSO's two as `execve` maps them.
- `ExecStart.full`: in a state `execve` starts a program in, the registers are `entryCpu`'s; the address space is
  `regionsMemory` of the vsyscall page's region, `stackRegion`, the segments' and `vdsoRegions`, the stack's first
  page the one that grows down; the break and its lowest value are the choice's; the thread has the caller's id, no
  `rseq` area, no shadow stack and no `CPUID` faulting.
-/
namespace FV7z.Start
open ZellicX86

/-- `s'` is `s` but for the pending signals, the thread's and the process's. -/
def Pend (s s' : State) : Prop :=
  ∃ tp pp, s' = { s with thread := { s.thread with pending := tp },
                         proc := { s.proc with signal := { s.proc.signal with pending := pp } } }

theorem Pend.refl (s : State) : Pend s s := ⟨_, _, rfl⟩

theorem Pend.trans {a b c : State} (h1 : Pend a b) (h2 : Pend b c) : Pend a c := by
  obtain ⟨t1, p1, rfl⟩ := h1
  obtain ⟨t2, p2, rfl⟩ := h2
  exact ⟨t2, p2, rfl⟩

theorem nextSignal_pend {s s₁ : State} {q : Queued} (h : nextSignal s = some (q, s₁)) : Pend s s₁ := by
  unfold nextSignal at h
  simp only at h
  split at h
  · obtain ⟨q', -, hq⟩ := Option.map_eq_some_iff.1 h
    cases hq
    exact ⟨_, s.proc.signal.pending, rfl⟩
  · split at h
    · obtain ⟨⟨q', tp'⟩, -, hq⟩ := Option.map_eq_some_iff.1 h
      cases hq
      exact ⟨_, s.proc.signal.pending, rfl⟩
    · split at h
      · obtain ⟨⟨q', pp⟩, -, hq⟩ := Option.map_eq_some_iff.1 h
        cases hq
        exact ⟨s.thread.pending, _, rfl⟩
      · cases h

theorem execSignals_pend : ∀ (n : Nat) {s s' : State}, execSignals n s = .ok s' → Pend s s'
  | 0, _, _, h => by simp [execSignals] at h
  | n + 1, s, s', h => by
    unfold execSignals at h
    split at h
    · cases h
      exact Pend.refl _
    · rename_i q s₁ hn
      have h1 := nextSignal_pend hn
      have ih : execSignals n s₁ = .ok s' → Pend s s' := fun h' => h1.trans (execSignals_pend n h')
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

/-- The stack's region as `execve` maps it: from `StackLayout.start` to the stack's end, readable and writable,
holding `stackRuns` and zeros elsewhere, growing down. -/
def stackRegion (prof : Profile) (hdr : ElfHeader) (phs : List Phdr) (a : ExecArgs) (c : ExecChoice) : Region :=
  ⟨(stackLayout a prof.linux c).start / 4096, (c.stackTop - (stackLayout a prof.linux c).start) / 4096,
    ⟨true, true, execStack phs⟩,
    fun k => .priv fun o =>
      runsByte (stackRuns prof hdr phs a c) ((stackLayout a prof.linux c).start + 4096 * k + o.toNat),
    false, fun _ => none, ⟨true, true, true⟩, true⟩

/-- The vDSO's regions as `execve` maps them where the kernel has one: six pages of data the kernel owns, then the
image's pages. -/
def vdsoRegions (prof : Profile) (c : ExecChoice) : List Region :=
  if prof.linux.vdso then
    [⟨c.vdsoBase / 4096, 6, ⟨true, false, false⟩,
        fun i => .kernel (if prof.linux.vdsoData (Fin.ofNat 6 i) then some (c.vdsoData (Fin.ofNat 6 i)) else none),
        true, fun _ => none, ⟨true, false, false⟩, false⟩,
      ⟨c.vdsoText / 4096, prof.linux.vdsoText.length, ⟨true, false, true⟩,
        fun i => .priv (prof.linux.vdsoText.getD i zeroFrame), true, fun _ => none, ⟨true, true, true⟩, false⟩]
  else []

/-- A state `execve` starts a program in. -/
theorem ExecStart.full {prof : Profile} {files : Files} {exe : FileId} {a : ExecArgs} {k : KernelConfig}
    {s₀ : State} (h : ExecStart prof files exe a k s₀) :
    ∃ hdr phs c segs, readElf files exe = some (hdr, phs) ∧ c.Valid prof.linux phs a k ∧
      loadRegions prof.feat files exe k (stackLayout a prof.linux c).start c.stackTop phs = .ok segs ∧
      s₀.cpu = entryCpu hdr.entry (stackLayout a prof.linux c).sp k.initPkru ∧
      s₀.proc.mm.mem = regionsMemory
        (vsyscallRegions prof.linux.vsyscall ++ (stackRegion prof hdr phs a c :: segs ++ vdsoRegions prof c))
        { files with denyWrite := fun f => decide (f = exe) || files.denyWrite f }
        [BitVec.ofNat 52 ((stackLayout a prof.linux c).start / 4096)] ∧
      s₀.proc.mm.brkMin = BitVec.ofNat 64 (brkMin prof.linux phs a c) ∧
      s₀.proc.mm.brk = BitVec.ofNat 64 c.brk ∧
      s₀.thread.tid = a.tid ∧ s₀.thread.rseq = none ∧ s₀.thread.shstk = none ∧
      s₀.thread.cpuidFaults = false := by
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
      obtain ⟨tp, pp, rfl⟩ := execSignals_pend _ he
      exact ⟨hdr, phs, c, segs, rfl, hv hdr phs hr, hl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end FV7z.Start
