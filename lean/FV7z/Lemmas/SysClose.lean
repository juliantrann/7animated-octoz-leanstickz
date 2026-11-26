import FV7z.Start.TaskSeg
import FV7z.Lemmas.CallFn
/-!
# `close`: the process's descriptor table changes (PLAN.md §M, M1)

`close (fd)` takes the descriptor out of the table whether it succeeds or not, and only then asks the file's `flush`
(`Request.close`) for its result. The table is part of the process, which `KeptW` keeps, so the run goes on from the
state after as a new start (`Seg.reroot`), as after `umask` (`Lemmas/SysUm.lean`).

- `closeSt`: the state with descriptor `rdi` closed; `setFd_none_of_desc`: closing a descriptor that is not open
  changes nothing.
- `closeRes`: what `close` returns and where the stream of answers is after it: `EBADF` for a descriptor not open,
  0 for one opened with `O_PATH`, else the answer of `flush`.
- `syscall_close`: what the instruction `syscall` leaves for `close (rdi)`.
- `Seg.s_close_re`: the step of a run that `Fn.Seg` describes; the run goes on from the state after as a new start.
-/
namespace FV7z
open ZellicX86 Decode

variable {prof : Profile} {o : Oracle} {t : Nat} {s : State}

/-- `s` with descriptor `rdi` (32-bit) closed. -/
abbrev closeSt (s : State) : State := s.setFd (arg32 s.cpu.gpr.rdi) none

/-- What `close (rdi)` from `s` returns, the stream of answers at `t`, and where the stream is after it. -/
def closeRes (o : Oracle) (t : Nat) (s : State) : BitVec 64 × Nat :=
  match s.proc.files.desc (arg32 s.cpu.gpr.rdi) with
  | none => (errRet EBADF, t)
  | some f =>
    if f.map = .path then (0, t) else
    match o t (.close f.id) with
    | none => (0, t + 1)
    | some e => (errRet (closeErr e.val), t + 1)

/-- Closing a descriptor that is not open changes nothing. -/
theorem setFd_none_of_desc {fd : Nat} (h : s.proc.files.desc fd = none) : s.setFd fd none = s := by
  have hf : s.proc.files fd = none := by
    unfold FdTable.desc at h
    cases e : s.proc.files fd with
    | none => rfl
    | some x => rw [e] at h; exact absurd h (by simp)
  have hfun : (fun n => if n = fd then none else s.proc.files n) = s.proc.files := by
    funext n
    by_cases hn : n = fd
    · rw [if_pos hn, hn, hf]
    · rw [if_neg hn]
  unfold State.setFd
  rw [hfun]

/-- `syscall` for `close (rdi)`: the descriptor is closed, `closeRes` in `rax`. -/
theorem syscall_close {len : Nat} (htf : s.cpu.rflags.tf = false)
    (hdec : Decode.decode prof.feat (fetchByte prof.feat s) = .ok (mk .syscall 32 [] len))
    (hnr : s.cpu.gpr.rax.toNat % 2 ^ 32 = 3) :
    (instruction prof s).runStream o t =
      (.running (sysSt (closeSt s) len (closeRes o t s).1) (some (sysEv s (closeRes o t s).1)),
        (closeRes o t s).2) := by
  rw [instruction_syscall htf hdec]
  have hrax : (nx s len (sysGpr s len) (rf0 s)).cpu.gpr.rax = s.cpu.gpr.rax := rfl
  have hrdi : (nx s len (sysGpr s len) (rf0 s)).cpu.gpr.rdi = s.cpu.gpr.rdi := rfl
  have hfs : (nx s len (sysGpr s len) (rf0 s)).proc.files = s.proc.files := rfl
  unfold syscall
  simp only [hrax, hnr]
  simp only [show ¬ (3 ≥ 2 ^ 31) by decide, show ¬ (3 ≥ x32Bit) by decide, show ¬ (3 ≥ nrSyscalls) by decide,
    show niSyscall 3 = false by decide, ↓reduceIte, Bool.false_eq_true]
  show (sysClose (nx s len (sysGpr s len) (rf0 s))).runStream o t = _
  unfold sysClose closeRes
  simp only [hrdi, hfs]
  cases hd : s.proc.files.desc (arg32 s.cpu.gpr.rdi) with
  | none =>
    rw [closeSt, setFd_none_of_desc hd]
    rfl
  | some f =>
    by_cases hp : f.map = .path
    · simp only [hp, ↓reduceIte]
      rfl
    · simp only [hp, ↓reduceIte]
      show (Req.bind (Req.request (.close f.id)) _).runStream o t = _
      rw [Req.runStream_bind,
        show (Req.request (Request.close f.id)).runStream o t = (o t (.close f.id), t + 1) from rfl]
      dsimp only
      cases o t (.close f.id) <;> rfl

end FV7z

namespace FV7z.Fn.Seg
open ZellicX86 Decode FV7z.Leaf

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle} {F : Footprint} {Wl : List Rgn}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop} {X : State} {t j : Nat}
  {e' : Addr} {code : List Byte} {V : Addr → Byte}

/-- `syscall` for `close (rdi)` (a start with no `rseq` area): the run goes on from the state after, its own start,
with descriptor `rdi` closed and `closeRes` in `rax`, the stream of answers at some `t₁` before the call. -/
theorem s_close_re (c : Seg prof F Wl L s₀ o) (hrs : s₀.thread.rseq = none) (hK : KeptW Wl s₀ X)
    (hA : Agree F X.proc.mm.mem V) (hin : CodeIn L e' code) (hj : j < code.length) (hrip : X.cpu.rip = e'.add j)
    {len : Nat} (hd : Dec prof.feat code j (FV7z.mk .syscall 32 [] len)) (hnr : X.cpu.gpr.rax.toNat % 2 ^ 32 = 3)
    (k' : ∀ (M : Memory) (t₁ t' : Nat), KeptW Wl s₀ (X.withMem M) →
      Seg prof F Wl L (sysSt (closeSt (X.withMem M)) len (closeRes o t₁ (X.withMem M)).1) o →
      Agree F M V →
      GoG prof L o (gev ++ [sysEv X (closeRes o t₁ (X.withMem M)).1]) gP gE
        (sysSt (closeSt (X.withMem M)) len (closeRes o t₁ (X.withMem M)).1) t') :
    GoG prof L o gev gP gE X t :=
  c.stepE hK hin hj hrip fun M hM hK' htf hac =>
    ⟨_, _, _, syscall_close (s := X.withMem M) htf (c.dec hK' hin hrip hd) hnr,
      k' M _ _ hK' (c.reroot hK' rfl rfl rfl rfl rfl htf hac hrs) (c.agreeK hK hA hM)⟩

end FV7z.Fn.Seg
