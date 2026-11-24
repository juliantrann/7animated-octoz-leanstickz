import ZellicX86.Spec.Statement.Linux
import FV7z.Statement.Cfg
import FV7z.Statement.Policy
/-!
# The statement `Confined` (PLAN.md §5.2)

`7zzs <cmd> -t<fmt>:s0 <single-thread flags> <archive>`, for every content of the archive:
- (A) `AlwaysPath`: the run follows the file's control-flow graph (`Cfg.lean`): no hijack of control;
- (B) every system call so far is accepted by the command's policy (`Policy.lean`): no action on the system outside
  it;
- (C) `Done7z`: the process ends only in one of the listed ways (as Zellic's statements do): no crash.
A safety statement (`Always`): a run that never ends (an archive that makes a decoder loop) still satisfies it, so
loops need no variant. The final theorems instantiate it with the launch of `7zzs` and the hypotheses of the launch,
the processor and the environment, one theorem per command and format (milestones M1–M5).

`Hijackfree` (A and B, without C) is the fallback statement where C cannot be had: it admits a C++ exception that ends
the process (`std::terminate`, `SIGABRT`) and a fault.
-/

namespace FV7z.Statement
open ZellicX86

/-- (C): how a run of `7zzs` may end: `exit_group` with one of 7-Zip's exit codes (`CPP/7zip/UI/Common/ExitCode.h`:
0 success, 1 warning, 2 fatal error, 7 command-line error, 8 out of memory, 255 stopped by the user), or killed in a
`write` (`SIGPIPE`, `SIGXFSZ`). Not a fault (`SIGSEGV`, `SIGBUS`, `SIGILL`, `SIGFPE`), not `SIGABRT` (a heap check of
`malloc`, `std::terminate`), not what the model does not cover. -/
def Done7z (out : Outcome) (_evs : List Event) : Prop :=
  (∃ s : BitVec 8, out = .exited .exitGroup s ∧ s.toNat ∈ [0, 1, 2, 7, 8, 255]) ∨ out.KilledInWrite

/-- (A), (B) and (C) of the run from `s₀`, with graph `g`, policy `A` and ends `D`. -/
def Confined (prof : Profile) (env : Oracle → Prop) (s₀ : State) (g : Cfg) (A : Policy)
    (D : Outcome → List Event → Prop) : Prop :=
  AlwaysPath prof env s₀ g ∧
    Always prof env s₀ (fun _ evs => A.Accepts evs) (fun out evs => A.Accepts evs ∧ D out evs)

/-- (A) and (B) of the run from `s₀`: `Confined` without a constraint on how the run ends. -/
def Hijackfree (prof : Profile) (env : Oracle → Prop) (s₀ : State) (g : Cfg) (A : Policy) : Prop :=
  AlwaysPath prof env s₀ g ∧ Always prof env s₀ (fun _ evs => A.Accepts evs) (fun _ evs => A.Accepts evs)

/-- `Confined` gives `Hijackfree`. -/
theorem Confined.hijackfree {prof : Profile} {env : Oracle → Prop} {s₀ : State} {g : Cfg} {A : Policy}
    {D : Outcome → List Event → Prop} (h : Confined prof env s₀ g A D) : Hijackfree prof env s₀ g A := by
  unfold Confined Always at h
  unfold Hijackfree Always
  refine ⟨h.1, fun o ho t n => ?_⟩
  have h2 := h.2 o ho t n
  revert h2
  generalize run prof o n s₀ t = r
  rcases r with ⟨st, evs, t'⟩
  cases st with
  | running s => exact id
  | done out => exact fun h' => h'.1

end FV7z.Statement
