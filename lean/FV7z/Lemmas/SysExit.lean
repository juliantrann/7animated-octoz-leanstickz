import FV7z.Lemmas.CallFn
import FV7z.Lemmas.SysMm
/-!
# `exit_group`: the run ends (PLAN.md §M, M1)

`exit_group (status)` ends the process with the low 8 bits of `status` (`.exited .exitGroup`); the model's step is
`.stopped`, so the run is over and only the goal for ends (`gE`) has to hold, of the events before.

- `syscall_exit_group`: what the instruction `syscall` does for `exit_group (rdi)`.
- `runsFrom_insQS`: `runsFrom_insQE` for an instruction that ends the run.
- `Seg.stopE`, `Seg.s_exit_group`: the step of a run that `Fn.Seg` describes.
-/
namespace FV7z
open ZellicX86 Decode

variable {prof : Profile} {o : Oracle} {t : Nat} {s : State}

/-- `syscall` for `exit_group (rdi)`: the run ends with `rdi`'s low 8 bits. -/
theorem syscall_exit_group {len : Nat} (htf : s.cpu.rflags.tf = false)
    (hdec : Decode.decode prof.feat (fetchByte prof.feat s) = .ok (mk .syscall 32 [] len))
    (hnr : s.cpu.gpr.rax.toNat % 2 ^ 32 = 231) :
    (instruction prof s).runStream o t = (.stopped (.exited .exitGroup (s.cpu.gpr.rdi.setWidth 8)), t) := by
  rw [instruction_syscall htf hdec]
  have hrax : (nx s len (sysGpr s len) (rf0 s)).cpu.gpr.rax = s.cpu.gpr.rax := rfl
  unfold syscall
  simp only [hrax, hnr]
  simp only [show ¬ (231 ≥ 2 ^ 31) by decide, show ¬ (231 ≥ x32Bit) by decide,
    show ¬ (231 ≥ nrSyscalls) by decide, show niSyscall 231 = false by decide, ↓reduceIte, Bool.false_eq_true]
  rfl

/-- `runsFrom_insQ` for an instruction that ends the run. -/
theorem runsFrom_insQS {I : State → Prop} {pre : List Event} {X : State}
    {P : State → Nat → List Event → Prop} {E : Outcome → List Event → Prop}
    (hU : Undisturbed o) (hqX : Quiet prof.feat X) (hI : I X)
    (h : ∀ M, Calm (IdAddr X.thread.rseq) X.proc.mm.mem M → ∃ out t',
      (instruction prof (X.withMem M)).runStream o (t + 1) = (.stopped out, t') ∧ E out pre) :
    RunsFrom prof o I pre X t P E := by
  obtain ⟨-, M, hkd, hc⟩ := envEvents_quiet prof.feat (evsAt prof o t) X hqX fun e he => hU t prof.cpus e he
  obtain ⟨out, t', hY, hE⟩ := h M hc
  exact runsFrom_stop hI (by rw [step_runStream prof o t X hU hqX, hkd]; exact hY) hE

end FV7z

namespace FV7z.Fn.Seg
open ZellicX86 Decode FV7z.Leaf

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle} {F : Footprint} {Wl : List Rgn}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop} {X : State}
  {t j : Nat} {e' : Addr} {code : List Byte}

/-- An instruction of the code that ends the run, with the goal for ends of the events before. -/
theorem stopE (c : Seg prof F Wl L s₀ o) (hK : KeptW Wl s₀ X) (hin : CodeIn L e' code) (hj : j < code.length)
    (hrip : X.cpu.rip = e'.add j)
    (h : ∀ M, Calm (IdAddr X.thread.rseq) X.proc.mm.mem M → KeptW Wl s₀ (X.withMem M) →
      X.cpu.rflags.tf = false → X.cpu.rflags.ac = false →
      ∃ out t', (instruction prof (X.withMem M)).runStream o (t + 1) = (.stopped out, t') ∧ gE out gev) :
    GoG prof L o gev gP gE X t := by
  refine runsFrom_insQS c.env (c.quiet hK) (inCode_of_codeIn hin hj hrip) fun M hM => ?_
  exact h M hM (hK.withMem hM) (hK.tf.trans c.ready.plain.1) (hK.ac.trans c.ready.plain.2.1)

/-- `syscall` for `exit_group (rdi)`: the run ends with `rdi`'s low 8 bits, which the goal for ends allows. -/
theorem s_exit_group (c : Seg prof F Wl L s₀ o) (hK : KeptW Wl s₀ X) (hin : CodeIn L e' code)
    (hj : j < code.length) (hrip : X.cpu.rip = e'.add j) {len : Nat}
    (hd : Dec prof.feat code j (FV7z.mk .syscall 32 [] len)) (hnr : X.cpu.gpr.rax.toNat % 2 ^ 32 = 231)
    (hE : gE (.exited .exitGroup (X.cpu.gpr.rdi.setWidth 8)) gev) :
    GoG prof L o gev gP gE X t :=
  c.stopE hK hin hj hrip fun M _ hK' htf _ =>
    ⟨_, _, syscall_exit_group (s := X.withMem M) htf (c.dec hK' hin hrip hd) hnr, hE⟩

end FV7z.Fn.Seg
