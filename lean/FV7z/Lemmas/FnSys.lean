import FV7z.Lemmas.FnSteps
/-!
# A system call, a step of a run (PLAN.md G2, glibc `init_cpu_features`)

A `syscall` step leaves a state and an event (`sysReturn`): the run's events so far grow by it, so the goal of the
rest of the run is a `GoG` with `gev ++ [ev]`. The one here: `arch_prctl` (158) with an option the model answers
`EINVAL` without a change of state (`sysArchPrctl`: every option but those it implements or does not model), such as
`ARCH_CET_STATUS` (0x3001), which glibc 2.31's `init_cpu_features` asks.
-/
namespace FV7z
open ZellicX86 Decode

variable {prof : Profile} {o : Oracle} {t : Nat} {s : State}

/-- A step whose instruction leaves `s₂` and the event `ev`, from a quiet `rseq` area. -/
theorem step_ev {t' : Nat} {s₂ : State} {ev : Option Event} (hU : Undisturbed o) (hq : Quiet prof.feat s)
    (h : (instruction prof (kdata prof.feat s (evsAt prof o t))).runStream o (t + 1) = (.running s₂ ev, t')) :
    (step prof s).runStream o t = (.running s₂ ev, t') := by
  rw [step_runStream prof o t s hU hq, h]

/-- `runsFrom_insQ` for an instruction that leaves an event. -/
theorem runsFrom_insQE {I : State → Prop} {pre : List Event} {X : State}
    {P : State → Nat → List Event → Prop} {E : Outcome → List Event → Prop}
    (hU : Undisturbed o) (hqX : Quiet prof.feat X) (hI : I X)
    (h : ∀ M, Calm (IdAddr X.thread.rseq) X.proc.mm.mem M → ∃ Y t' ev,
      (instruction prof (X.withMem M)).runStream o (t + 1) = (.running Y ev, t') ∧
        RunsFrom prof o I (pre ++ ev.toList) Y t' P E) :
    RunsFrom prof o I pre X t P E := by
  obtain ⟨-, M, hkd, hc⟩ := envEvents_quiet prof.feat (evsAt prof o t) X hqX fun e he => hU t prof.cpus e he
  obtain ⟨Y, t', ev, hY, k⟩ := h M hc
  exact runsFrom_step hI (step_ev hU hqX (by rw [hkd]; exact hY)) k

/-- The registers `syscall` leaves before the kernel: `rcx` the next instruction's address, `r11` the flags. -/
abbrev sysGpr (s : State) (len : Nat) : Gprs :=
  (s.cpu.gpr.set 1 (s.cpu.rip.add len)).set 11 (rf0 s).toBits

/-- `arch_prctl(opt, _)` with an option the model answers `EINVAL`: `rax` is `-EINVAL`, `rcx` and `r11` as `syscall`
sets them; the event records the call. -/
theorem syscall_einval {len : Nat} (htf : s.cpu.rflags.tf = false)
    (hdec : Decode.decode prof.feat (fetchByte prof.feat s) = .ok (mk .syscall 32 [] len))
    (hnr : s.cpu.gpr.rax.toNat % 2 ^ 32 = 158) {opt : Nat} (hopt : arg32 s.cpu.gpr.rdi = opt)
    (h1 : opt ≠ ARCH_GET_CPUID) (h2 : opt ≠ ARCH_SET_CPUID) (h3 : opt ≠ ARCH_SET_FS) (h4 : opt ≠ ARCH_SET_GS)
    (h5 : opt ≠ ARCH_GET_FS) (h6 : opt ≠ ARCH_GET_GS)
    (h7 : ¬ ((0x1021 ≤ opt ∧ opt ≤ 0x1025) ∨ (0x2001 ≤ opt ∧ opt ≤ 0x2003) ∨
      (0x4001 ≤ opt ∧ opt ≤ 0x4004) ∨ (0x5001 ≤ opt ∧ opt ≤ 0x5005))) :
    (instruction prof s).runStream o t = (.running (nx s len ((sysGpr s len).set 0 (errRet EINVAL)) (rf0 s))
      (some ⟨s.cpu.gpr.rax, [s.cpu.gpr.rdi, s.cpu.gpr.rsi, s.cpu.gpr.rdx, s.cpu.gpr.r10, s.cpu.gpr.r8,
        s.cpu.gpr.r9], errRet EINVAL, [], []⟩), t) := by
  have hex : ((exec prof (mk .syscall 32 [] len)).run prof.feat prof.linux.splitLock (advance s len)).runStream o t =
      (.ok .syscall (nx s len (sysGpr s len) (rf0 s)), t) := by
    simp only [exec, Sem.syscall, mk, bind, Prog.bind, Prog.readRip, Prog.readFlags, Prog.writeReg]
    rfl
  unfold instruction
  simp only [htf, Bool.false_eq_true, ↓reduceIte, hdec]
  unfold advance at hex
  show (Req.bind _ _).runStream o t = _
  rw [Req.runStream_bind, hex]
  have hrax : (nx s len (sysGpr s len) (rf0 s)).cpu.gpr.rax = s.cpu.gpr.rax := rfl
  have hrdi : (nx s len (sysGpr s len) (rf0 s)).cpu.gpr.rdi = s.cpu.gpr.rdi := rfl
  show (syscall prof (nx s len (sysGpr s len) (rf0 s))).runStream o t = _
  unfold syscall
  simp only [hrax, hnr]
  simp only [show ¬ (158 ≥ 2 ^ 31) by decide, show ¬ (158 ≥ x32Bit) by decide, show ¬ (158 ≥ nrSyscalls) by decide,
    show niSyscall 158 = false by decide, ↓reduceIte, Bool.false_eq_true]
  unfold sysArchPrctl
  simp only [hrdi, hopt, h1, h2, h3, h4, h5, h6, h7, ↓reduceIte, or_self]
  rfl

end FV7z

namespace FV7z.Fn
open ZellicX86 Decode FV7z.Leaf

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle} {F : Footprint} {Wl : List Rgn}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop} {X : State} {t j : Nat}
  {e' : Addr} {code : List Byte} {V : Addr → Byte}

namespace Seg

/-- `step` for an instruction that may leave an event. -/
theorem stepE (c : Seg prof F Wl L s₀ o) (hK : KeptW Wl s₀ X) (hin : CodeIn L e' code) (hj : j < code.length)
    (hrip : X.cpu.rip = e'.add j)
    (h : ∀ M, Calm (IdAddr X.thread.rseq) X.proc.mm.mem M → KeptW Wl s₀ (X.withMem M) →
      X.cpu.rflags.tf = false → X.cpu.rflags.ac = false →
      ∃ Y t' ev, (instruction prof (X.withMem M)).runStream o (t + 1) = (.running Y ev, t') ∧
        GoG prof L o (gev ++ ev.toList) gP gE Y t') :
    GoG prof L o gev gP gE X t := by
  refine runsFrom_insQE c.env (c.quiet hK) (inCode_of_codeIn hin hj hrip) fun M hM => ?_
  exact h M hM (hK.withMem hM) (hK.tf.trans c.ready.plain.1) (hK.ac.trans c.ready.plain.2.1)

/-- The event of `arch_prctl(ARCH_CET_STATUS, _)` from registers `g`, answered `EINVAL`. -/
abbrev cetEv (g : Gprs) : Event := ⟨g.rax, [g.rdi, g.rsi, g.rdx, g.r10, g.r8, g.r9], errRet EINVAL, [], []⟩

/-- `syscall` for `arch_prctl(ARCH_CET_STATUS, _)` (0x3001): `EINVAL`, no change but `rax`, `rcx`, `r11`. -/
theorem s_cet (c : Seg prof F Wl L s₀ o) (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V)
    (hin : CodeIn L e' code) (hj : j < code.length) (hrip : X.cpu.rip = e'.add j) {len : Nat}
    (hd : Dec prof.feat code j (FV7z.mk .syscall 32 [] len)) (hnr : X.cpu.gpr.rax.toNat % 2 ^ 32 = 158)
    (hopt : arg32 X.cpu.gpr.rdi = 0x3001)
    (k' : ContG prof F Wl L s₀ o (gev ++ [cetEv X.cpu.gpr]) gP gE V fun Y => Y.cpu.rip = e'.add (j + len) ∧
      Y.cpu.gpr = (sysGpr X len).set 0 (errRet EINVAL)) :
    GoG prof L o gev gP gE X t :=
  c.stepE hK hin hj hrip fun M hM hK' htf _ =>
    ⟨_, _, _, syscall_einval (s := X.withMem M) htf (c.dec hK' hin hrip hd) hnr hopt (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide),
      k' _ _ (hK'.nx rfl rfl rfl) (c.agreeK hK hA hM) ⟨rip_add hrip M len, rfl⟩⟩

end Seg

end FV7z.Fn
