import FV7z.Start.Ready
import FV7z.Lemmas.SysTask
/-!
# No signal waits (PLAN.md G3, startup)

`execve` keeps the signals that wait for the caller, and the ones its mask blocks wait on while the new program
runs. glibc's startup unblocks two signals (`__pthread_initialize_minimal`, `SIGCANCEL` and `SIGSETXID`) after it has
set their handlers; a run in which one of them waited would go on in the handler. The statement's launch has no signal
waiting (PLAN.md §5.3), and `Undisturbed` sends none.

- `execSignals_quiet`: with no entry in either set (`nextSignal_quiet`, `Lemmas/SysTask.lean`) `execve`'s return to
  user mode changes nothing.
- `ExecStart.quiet`, `launch_quiet`: a program started with no signal waiting has none at its first instruction.
-/
namespace FV7z.Start
open ZellicX86

theorem execSignals_quiet (n : Nat) {s s' : State} (h : execSignals n s = .ok s') (ht : s.thread.pending = [])
    (hp : s.proc.signal.pending = []) : s'.thread.pending = [] ∧ s'.proc.signal.pending = [] := by
  cases n with
  | zero => simp [execSignals] at h
  | succ n =>
    unfold execSignals at h
    rw [nextSignal_quiet ht hp] at h
    cases h
    exact ⟨ht, hp⟩

/-- A program `execve` starts with no signal waiting has none at its first instruction. -/
theorem ExecStart.quiet {prof : Profile} {files : Files} {exe : FileId} {a : ExecArgs} {k : KernelConfig}
    {s₀ : State} (h : ExecStart prof files exe a k s₀) (ht : a.threadPending = []) (hp : a.signal.pending = []) :
    s₀.thread.pending = [] ∧ s₀.proc.signal.pending = [] := by
  obtain ⟨-, c, hv, he⟩ := h
  unfold execve at he
  cases hr : readElf files exe with
  | none =>
    simp only [hr] at he
    split at he
    · cases he
    repeat (replace he := ite_ok he (by intro h; cases h))
    cases he
  | some hp' =>
    obtain ⟨hdr, phs⟩ := hp'
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
      exact execSignals_quiet _ he ht hp

theorem launch_quiet {l : Launch} (h : Launch.Of V2606.zzs.blob.bytes V2606.zzs.blob.size l)
    (ht : l.args.threadPending = []) (hp : l.args.signal.pending = []) :
    l.s₀.thread.pending = [] ∧ l.s₀.proc.signal.pending = [] :=
  ExecStart.quiet h.2.1 ht hp

end FV7z.Start
