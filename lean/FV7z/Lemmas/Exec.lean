import FV7z.Lemmas.Frame
import FV7z.Lemmas.Run
/-!
# Symbolic execution, an instruction at a time (PLAN.md G2.0)

What a proof about a function's code uses at each of its instructions:
- the shapes of the state an instruction leaves: `nx` (on to the next instruction, with new registers and flags), `upd`
  (to a target, a jump or a return), and that both keep `Kept`;
- `runsFrom_ins`: a step of an undisturbed run from a state that `Kept` relates to the call's, given what the
  instruction does from every state the kernel's ordinary events may leave (they change only the `rseq` ids);
- small facts of the semantics' arithmetic (`get_regOf_*`, `bv_sub_beq_zero`, `ofBytesLE_one`).
-/
namespace FV7z
open ZellicX86

/-! ## Shapes of the next state -/

/-- `s` with `rip` past `len` bytes, registers `g` and flags `fl`. -/
def nx (s : State) (len : Nat) (g : Gprs) (fl : Rflags) : State :=
  s.modCpu fun c => { c with rip := c.rip.add len, rflags := fl, gpr := g }

/-- `s` with `rip` at `r`, registers `g` and flags `fl`. -/
def upd (s : State) (r : Addr) (g : Gprs) (fl : Rflags) : State :=
  s.modCpu fun c => { c with rip := r, rflags := fl, gpr := g }

@[simp] theorem nx_gpr (s : State) (len : Nat) (g : Gprs) (fl : Rflags) : (nx s len g fl).cpu.gpr = g := rfl
@[simp] theorem nx_rip (s : State) (len : Nat) (g : Gprs) (fl : Rflags) :
    (nx s len g fl).cpu.rip = s.cpu.rip.add len := rfl
@[simp] theorem nx_rflags (s : State) (len : Nat) (g : Gprs) (fl : Rflags) : (nx s len g fl).cpu.rflags = fl := rfl
@[simp] theorem nx_mem (s : State) (len : Nat) (g : Gprs) (fl : Rflags) :
    (nx s len g fl).proc.mm.mem = s.proc.mm.mem := rfl
@[simp] theorem nx_pkru (s : State) (len : Nat) (g : Gprs) (fl : Rflags) : (nx s len g fl).cpu.pkru = s.cpu.pkru := rfl
@[simp] theorem nx_thread (s : State) (len : Nat) (g : Gprs) (fl : Rflags) : (nx s len g fl).thread = s.thread := rfl
@[simp] theorem upd_gpr (s : State) (r : Addr) (g : Gprs) (fl : Rflags) : (upd s r g fl).cpu.gpr = g := rfl
@[simp] theorem upd_rip (s : State) (r : Addr) (g : Gprs) (fl : Rflags) : (upd s r g fl).cpu.rip = r := rfl
@[simp] theorem upd_rflags (s : State) (r : Addr) (g : Gprs) (fl : Rflags) : (upd s r g fl).cpu.rflags = fl := rfl
@[simp] theorem upd_mem (s : State) (r : Addr) (g : Gprs) (fl : Rflags) :
    (upd s r g fl).proc.mm.mem = s.proc.mm.mem := rfl
@[simp] theorem upd_pkru (s : State) (r : Addr) (g : Gprs) (fl : Rflags) : (upd s r g fl).cpu.pkru = s.cpu.pkru := rfl
@[simp] theorem upd_thread (s : State) (r : Addr) (g : Gprs) (fl : Rflags) : (upd s r g fl).thread = s.thread := rfl

theorem Kept.nx {s₀ s : State} (h : Kept s₀ s) {len : Nat} {g : Gprs} {fl : Rflags}
    (htf : fl.tf = s.cpu.rflags.tf) (hac : fl.ac = s.cpu.rflags.ac) (hdf : fl.df = s.cpu.rflags.df) :
    Kept s₀ (FV7z.nx s len g fl) :=
  h.modCpu rfl rfl rfl rfl htf hac hdf

theorem Kept.upd {s₀ s : State} (h : Kept s₀ s) {r : Addr} {g : Gprs} {fl : Rflags}
    (htf : fl.tf = s.cpu.rflags.tf) (hac : fl.ac = s.cpu.rflags.ac) (hdf : fl.df = s.cpu.rflags.df) :
    Kept s₀ (FV7z.upd s r g fl) :=
  h.modCpu rfl rfl rfl rfl htf hac hdf

/-! ## A step -/

/-- A step of an undisturbed run from a state `X` that `Kept` relates to `s₀`, whose `rseq` area was quiet: the
instruction from every state the kernel's ordinary events may leave, `X` with memory `M` changed only at the ids, runs
on to a state from which the rest of the run goes on. -/
theorem runsFrom_ins {prof : Profile} {o : Oracle} {I : State → Prop} {pre : List Event} {s₀ X : State} {t : Nat}
    {P : State → Nat → List Event → Prop} {E : Outcome → List Event → Prop}
    (hU : Undisturbed o) (hq : Quiet prof.feat s₀) (hK : Kept s₀ X) (hI : I X)
    (h : ∀ M, Calm (IdAddr X.thread.rseq) X.proc.mm.mem M → ∃ Y t',
      (instruction prof (X.withMem M)).runStream o (t + 1) = (.running Y none, t') ∧ RunsFrom prof o I pre Y t' P E) :
    RunsFrom prof o I pre X t P E := by
  have hqX := hK.quiet hq
  obtain ⟨-, M, hkd, hc⟩ := envEvents_quiet prof.feat (evsAt prof o t) X hqX fun e he => hU t prof.cpus e he
  obtain ⟨Y, t', hY, k⟩ := h M hc
  exact runsFrom_step hI (step_next hU hqX (by rw [hkd]; exact hY)) (by simpa using k)

/-! ## Arithmetic of the semantics -/

@[simp] theorem get_regOf_0 (g : Gprs) : g.get (regOf 0) = g.rax := rfl
@[simp] theorem get_regOf_1 (g : Gprs) : g.get (regOf 1) = g.rcx := rfl
@[simp] theorem get_regOf_2 (g : Gprs) : g.get (regOf 2) = g.rdx := rfl
@[simp] theorem get_regOf_3 (g : Gprs) : g.get (regOf 3) = g.rbx := rfl
@[simp] theorem get_regOf_4 (g : Gprs) : g.get (regOf 4) = g.rsp := rfl
@[simp] theorem get_regOf_5 (g : Gprs) : g.get (regOf 5) = g.rbp := rfl
@[simp] theorem get_regOf_6 (g : Gprs) : g.get (regOf 6) = g.rsi := rfl
@[simp] theorem get_regOf_7 (g : Gprs) : g.get (regOf 7) = g.rdi := rfl
@[simp] theorem get_regOf_8 (g : Gprs) : g.get (regOf 8) = g.r8 := rfl

theorem bv_sub_beq_zero {w : Nat} (x y : BitVec w) : (x - y == 0#w) = decide (x = y) := by
  by_cases h : x = y
  · simp [h]
  · simp only [h, decide_false, beq_eq_false_iff_ne, ne_eq]
    intro e; apply h
    rw [← BitVec.sub_add_cancel x y, e, BitVec.zero_add]

/-- One byte, as a load reads it. -/
theorem ofBytesLE_one (m : Memory) (a : Addr) : ofBytesLE 8 (readBytes m a 1) = m.readByte a := by
  simp [readBytes, byteAddrs, ofBytesLE, Addr.add]

end FV7z
