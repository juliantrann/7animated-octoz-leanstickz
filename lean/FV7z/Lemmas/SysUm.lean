import FV7z.Start.TaskSeg
import FV7z.Lemmas.CallFn
/-!
# `umask`, and runs whose goal lets a call be put into the log (PLAN.md §M, constructor 17)

Constructor 17 calls `umask (0)` and then `umask (old)`: the process's mask changes in between, which `KeptW` does
not allow, and is as at the start after.

- `umS`: a state with another file mode creation mask; `syscall_umask`: what the instruction `syscall` leaves for
  `umask (mask)`.
- `KeptW.um2`: `KeptW` from the start again after a second `umask` that sets the start's mask back.
- `Seg.s_umask_re`: the first call; the run goes on from the state after as a new start (`Seg.reroot`).
- `Seg.s_umask_back`: the second call, from a run started after the first; `KeptW` from the first start after it.
- `Runs.imp`, `InsOK`, `GoG.ins`: a goal that holds of a log with a call of number `n` put anywhere into it, when
  it holds of the log without; the run from `X` with `gev` then gives the run with `gev ++ [ev]`.
-/
namespace FV7z
open ZellicX86 Decode

variable {prof : Profile} {o : Oracle} {t : Nat} {s : State}

/-- `s` with the file mode creation mask `u`. -/
def umS (s : State) (u : BitVec 9) : State := { s with proc := { s.proc with umask := u } }

/-- `syscall` for `umask (rdi)`: the mask becomes `rdi`'s low 9 bits; the mask before in `rax`. -/
theorem syscall_umask {len : Nat} (htf : s.cpu.rflags.tf = false)
    (hdec : Decode.decode prof.feat (fetchByte prof.feat s) = .ok (mk .syscall 32 [] len))
    (hnr : s.cpu.gpr.rax.toNat % 2 ^ 32 = 95) :
    (instruction prof s).runStream o t =
      (.running (sysSt (umS s (s.cpu.gpr.rdi.setWidth 9)) len (s.proc.umask.setWidth 64))
        (some (sysEv s (s.proc.umask.setWidth 64))), t) := by
  rw [instruction_syscall htf hdec]
  have hrax : (nx s len (sysGpr s len) (rf0 s)).cpu.gpr.rax = s.cpu.gpr.rax := rfl
  unfold syscall
  simp only [hrax, hnr]
  simp only [show ¬ (95 ≥ 2 ^ 31) by decide, show ¬ (95 ≥ x32Bit) by decide, show ¬ (95 ≥ nrSyscalls) by decide,
    show niSyscall 95 = false by decide, ↓reduceIte, Bool.false_eq_true]
  unfold sysUmask
  rfl

/-- `KeptW` from `s₀` after a `umask` from `X'` that sets `s₀`'s mask back, when `X'` is as a start after a `umask`
from `X` (with `KeptW` from `s₀`) allows. -/
theorem KeptW.um2 {ws : List Rgn} {s₀ X X' : State} {u u' : BitVec 9} {len len' : Nat} {v v' : BitVec 64}
    (h : KeptW ws s₀ X) (k : KeptW ws (sysSt (umS X u) len v) X') (hu : u' = s₀.proc.umask) :
    KeptW ws s₀ (sysSt (umS X' u') len' v') where
  proc := by
    subst hu
    have e1 := h.proc
    have e2 := k.proc
    simp only [sysSt, umS, FV7z.nx, State.modCpu] at e2 ⊢
    rw [e2, e1]
  calm := h.calm.trans (by
    have hc := k.calm
    rw [show (sysSt (umS X u) len v).thread = s₀.thread from h.thread] at hc
    exact hc)
  thread := k.thread.trans h.thread
  seg := k.seg.trans h.seg
  x87 := k.x87.trans h.x87
  mxcsr := k.mxcsr.trans h.mxcsr
  pkru := k.pkru.trans h.pkru
  tf := k.tf.trans h.tf
  ac := k.ac.trans h.ac
  df := k.df.trans h.df

variable {I : State → Prop} {pre : List Event}
  {P P' : State → Nat → List Event → Prop} {E E' : Outcome → List Event → Prop}

/-- A run to a weaker goal. -/
theorem Runs.imp (h : Runs prof o I s t P E) (hP : ∀ X T evs, P X T evs → P' X T evs)
    (hE : ∀ out evs, E out evs → E' out evs) : Runs prof o I s t P' E' := by
  obtain ⟨n, st, evs, T, hr, hp, hq⟩ := h
  refine ⟨n, st, evs, T, hr, hp, ?_⟩
  cases st with
  | running X => exact hP _ _ _ hq
  | done out => exact hE _ _ hq

/-- The goal holds of a log with a call of number `n` put into it when it holds of the log without. -/
def InsOK (n : Nat) (gP : State → Nat → List Event → Prop) (gE : Outcome → List Event → Prop) : Prop :=
  ∀ ev : Event, ev.nr.toNat = n →
    (∀ a b X T, gP X T (a ++ b) → gP X T (a ++ ev :: b)) ∧ (∀ a b out, gE out (a ++ b) → gE out (a ++ ev :: b))

/-- The run from `X` after `pre ++ [ev]`, from the run after `pre`. -/
theorem RunsFrom.ins {n : Nat} {ev : Event} (hU : InsOK n P E) (hn : ev.nr.toNat = n)
    (h : RunsFrom prof o I pre s t P E) : RunsFrom prof o I (pre ++ [ev]) s t P E :=
  Runs.imp h (fun X T evs hp => by
      rw [List.append_assoc, List.singleton_append]
      exact (hU ev hn).1 pre evs X T hp)
    fun out evs he => by
      rw [List.append_assoc, List.singleton_append]
      exact (hU ev hn).2 pre evs out he

end FV7z

namespace FV7z.Fn
open ZellicX86 Decode FV7z.Leaf

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle} {F : Footprint} {Wl : List Rgn}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop} {X : State} {t j : Nat}
  {e' : Addr} {code : List Byte} {V : Addr → Byte}

theorem GoG.ins {n : Nat} {ev : Event} {Y : State} {t' : Nat} (hU : InsOK n gP gE) (hn : ev.nr.toNat = n)
    (h : GoG prof L o gev gP gE Y t') : GoG prof L o (gev ++ [ev]) gP gE Y t' :=
  RunsFrom.ins hU hn h

namespace Seg

/-- `syscall` for `umask (rdi)` (a start with no `rseq` area): the run goes on from the state after, its own start,
with the mask before in `rax`. -/
theorem s_umask_re (c : Seg prof F Wl L s₀ o) (hrs : s₀.thread.rseq = none) (hK : KeptW Wl s₀ X)
    (hA : Agree F X.proc.mm.mem V) (hin : CodeIn L e' code) (hj : j < code.length) (hrip : X.cpu.rip = e'.add j)
    {len : Nat} (hd : Dec prof.feat code j (FV7z.mk .syscall 32 [] len)) (hnr : X.cpu.gpr.rax.toNat % 2 ^ 32 = 95)
    (k' : ∀ (M : Memory) (t' : Nat), KeptW Wl s₀ (X.withMem M) →
      Seg prof F Wl L (sysSt (umS (X.withMem M) (X.cpu.gpr.rdi.setWidth 9)) len (X.proc.umask.setWidth 64)) o →
      Agree F M V →
      GoG prof L o (gev ++ [sysEv X (X.proc.umask.setWidth 64)]) gP gE
        (sysSt (umS (X.withMem M) (X.cpu.gpr.rdi.setWidth 9)) len (X.proc.umask.setWidth 64)) t') :
    GoG prof L o gev gP gE X t :=
  c.stepE hK hin hj hrip fun M hM hK' htf hac =>
    ⟨_, _, _, syscall_umask (s := X.withMem M) htf (c.dec hK' hin hrip hd) hnr,
      k' M _ hK' (c.reroot hK' rfl rfl rfl rfl rfl htf hac hrs) (c.agreeK hK hA hM)⟩

/-- `syscall` for `umask (rdi)` in a run started after a `umask` from `Xm` (with `KeptW` from `s₀`), when `rdi`
sets `s₀`'s mask back: `KeptW` from `s₀` after it. -/
theorem s_umask_back {S Xm : State} {u : BitVec 9} {len₀ : Nat} {v₀ : BitVec 64} (c : Seg prof F Wl L S o)
    (hS : S = sysSt (umS Xm u) len₀ v₀) (hK₀ : KeptW Wl s₀ Xm) (hK : KeptW Wl S X)
    (hA : Agree F X.proc.mm.mem V) (hin : CodeIn L e' code) (hj : j < code.length) (hrip : X.cpu.rip = e'.add j)
    {len : Nat} (hd : Dec prof.feat code j (FV7z.mk .syscall 32 [] len)) (hnr : X.cpu.gpr.rax.toNat % 2 ^ 32 = 95)
    (hu : X.cpu.gpr.rdi.setWidth 9 = s₀.proc.umask)
    (k' : ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y → Agree F Y.proc.mm.mem V → Y.cpu.rip = e'.add (j + len) →
      Y.cpu.gpr = (sysGpr X len).set 0 (X.proc.umask.setWidth 64) →
      GoG prof L o (gev ++ [sysEv X (X.proc.umask.setWidth 64)]) gP gE Y t') :
    GoG prof L o gev gP gE X t := by
  subst hS
  refine c.stepE hK hin hj hrip fun M hM hK' htf _ => ?_
  refine ⟨_, _, _, syscall_umask (s := X.withMem M) htf (c.dec hK' hin hrip hd) hnr, ?_⟩
  refine k' _ _ (KeptW.um2 hK₀ hK' hu) (c.agreeK hK hA hM) ?_ rfl
  show X.cpu.rip.add len = _
  rw [hrip, addr_add_add]

end Seg

end FV7z.Fn
