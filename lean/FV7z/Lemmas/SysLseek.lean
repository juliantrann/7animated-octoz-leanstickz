import FV7z.Start.TaskSeg
import FV7z.Lemmas.CallFn
import FV7z.Lemmas.SysMm
/-!
# `lseek`: only a file's position changes (PLAN.md §M, M1)

`lseek (fd, off, whence)` with `whence` one of `SEEK_SET`, `SEEK_CUR`, `SEEK_END` (`SEEK_DATA` and `SEEK_HOLE`
are not modelled) returns a position or an error, and may move the position of the open file (`State.setFilePos`),
part of the process, which `KeptW` keeps; the address space, the descriptor table, the thread and the processor
(but `rax`) stay. So the run goes on from the state after as a new start (`Seg.reroot`), as after `close`.

What `lseek` returns is left open (`r`): the code after it has to hold for any answer, as it has to for the file's.

- `lseek_cps`: every way through the model's `sysLseek` ends with the state after one of that shape.
- `syscall_lseek`: what the instruction `syscall` leaves for `lseek (rdi, rsi, rdx)`.
- `Seg.s_lseek_re`: the step of a run that `Fn.Seg` describes; the run goes on from the state after as a new start.
-/
namespace FV7z
open ZellicX86 Decode

variable {prof : Profile} {o : Oracle} {t : Nat} {s : State}

/-- A request, then what follows from its answer. -/
theorem runStream_req_bind {β : Type} (r : Request) (k : r.Answer → Req β) :
    ((Req.request r) >>= k).runStream o t = (k (o t r)).runStream o (t + 1) := rfl

/-- `sysLseek` with `whence` at most `SEEK_END`: the state after has the processor of `u` with `rax` the answer, and
`u`'s thread, address space and descriptor table. -/
theorem lseek_cps (u : State) (hw : arg32 u.cpu.gpr.rdx ≤ 2) {P : StepResult × Nat → Prop}
    (hk : ∀ (Y : State) (r : BitVec 64) (t' : Nat), Y.cpu = (u.setRax r).cpu → Y.thread = u.thread →
      Y.proc.mm = u.proc.mm → Y.proc.files = u.proc.files →
      P (.running Y (some ⟨u.cpu.gpr.rax, syscallArgs u, r, [], []⟩), t')) :
    P ((sysLseek u).runStream o t) := by
  unfold sysLseek
  dsimp only
  have h0 : SEEK_SET = 0 := rfl
  have h1 : SEEK_CUR = 1 := rfl
  have h2 : SEEK_END = 2 := rfl
  have h4 : SEEK_MAX = 4 := rfl
  repeat' first
    | (refine hk _ _ _ ?_ ?_ ?_ ?_ <;> rfl)
    | contradiction
    | (exfalso; omega)
    | (rw [runStream_req_bind]; try dsimp only)
    | (simp only [bind, pure, Req.request, Req.bind, Req.runStream]; try dsimp only)
    | split

/-- `syscall` for `lseek (rdi, rsi, rdx)` with `whence` at most `SEEK_END`: the state after has the processor after
the `syscall` with `rax` the answer `r`, and the thread, address space and descriptor table of before. -/
theorem syscall_lseek {len : Nat} (htf : s.cpu.rflags.tf = false)
    (hdec : Decode.decode prof.feat (fetchByte prof.feat s) = .ok (mk .syscall 32 [] len))
    (hnr : s.cpu.gpr.rax.toNat % 2 ^ 32 = 8) (hw : arg32 s.cpu.gpr.rdx ≤ 2) :
    ∃ (Y : State) (r : BitVec 64) (t' : Nat),
      (instruction prof s).runStream o t = (.running Y (some (sysEv s r)), t') ∧
      Y.cpu = (sysSt s len r).cpu ∧ Y.thread = s.thread ∧ Y.proc.mm = s.proc.mm ∧
        Y.proc.files = s.proc.files := by
  rw [instruction_syscall htf hdec]
  have hrax : (nx s len (sysGpr s len) (rf0 s)).cpu.gpr.rax = s.cpu.gpr.rax := rfl
  unfold syscall
  simp only [hrax, hnr]
  simp only [show ¬ (8 ≥ 2 ^ 31) by decide, show ¬ (8 ≥ x32Bit) by decide,
    show ¬ (8 ≥ nrSyscalls) by decide, show niSyscall 8 = false by decide, ↓reduceIte, Bool.false_eq_true]
  exact lseek_cps (nx s len (sysGpr s len) (rf0 s)) hw
    (P := fun res => ∃ (Y : State) (r : BitVec 64) (t' : Nat), res = (.running Y (some (sysEv s r)), t') ∧
      Y.cpu = (sysSt s len r).cpu ∧ Y.thread = s.thread ∧ Y.proc.mm = s.proc.mm ∧ Y.proc.files = s.proc.files)
    fun Y r t' h1 h2 h3 h4 => ⟨Y, r, t', rfl, h1, h2, h3, h4⟩

end FV7z

namespace FV7z.Fn.Seg
open ZellicX86 Decode FV7z.Leaf

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle} {F : Footprint} {Wl : List Rgn}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop} {X : State}
  {t j : Nat} {e' : Addr} {code : List Byte} {V : Addr → Byte}

/-- `syscall` for `lseek (rdi, rsi, rdx)` (a start with no `rseq` area, `whence` at most `SEEK_END`): the run goes on
from the state after, its own start, with the processor after the `syscall` and some answer `r` in `rax`, the
address space and descriptor table of before. -/
theorem s_lseek_re (c : Seg prof F Wl L s₀ o) (hrs : s₀.thread.rseq = none) (hK : KeptW Wl s₀ X)
    (hA : Agree F X.proc.mm.mem V) (hin : CodeIn L e' code) (hj : j < code.length) (hrip : X.cpu.rip = e'.add j)
    {len : Nat} (hd : Dec prof.feat code j (FV7z.mk .syscall 32 [] len)) (hnr : X.cpu.gpr.rax.toNat % 2 ^ 32 = 8)
    (hw : arg32 X.cpu.gpr.rdx ≤ 2)
    (k' : ∀ (M : Memory) (Y : State) (r : BitVec 64) (t' : Nat), KeptW Wl s₀ (X.withMem M) →
      Y.cpu = (sysSt (X.withMem M) len r).cpu → Y.proc.mm = (X.withMem M).proc.mm →
      Y.proc.files = X.proc.files → Seg prof F Wl L Y o → Agree F Y.proc.mm.mem V →
      GoG prof L o (gev ++ [sysEv X r]) gP gE Y t') :
    GoG prof L o gev gP gE X t :=
  c.stepE hK hin hj hrip fun M hM hK' htf hac => by
    obtain ⟨Y, r, t', heq, hc, hth, hmm, hfs⟩ :=
      syscall_lseek (s := X.withMem M) (o := o) (t := t + 1) htf (c.dec hK' hin hrip hd) hnr hw
    refine ⟨Y, t', _, heq, ?_⟩
    have hAM : Agree F M V := c.agreeK hK hA hM
    have hY : Seg prof F Wl L Y o :=
      c.reroot hK' hmm ((congrArg (·.pkru) hc).trans rfl) ((congrArg (·.rseq) hth).trans rfl)
        ((congrArg (·.shstk) hth).trans rfl) ((congrArg (·.cpuidFaults) hth).trans rfl)
        ((congrArg (·.rflags.tf) hc).trans htf) ((congrArg (·.rflags.ac) hc).trans hac) hrs
    exact k' M Y r t' hK' hc hmm hfs hY (by rw [hmm]; exact hAM)

end FV7z.Fn.Seg
