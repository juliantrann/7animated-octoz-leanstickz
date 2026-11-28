import FV7z.Lemmas.SysMm
import FV7z.Lemmas.FnSteps
/-!
# `getpid`: the process's id, no change (PLAN.md G3, startup)

What the instruction `syscall` leaves for `getpid ()` on Zellic's model (`sysGetpid`): the only thread's id, which is
the process's, in `rax`; `rcx` and `r11` as `syscall` sets them; nothing else changes and no answer of the stream is
used.

- `syscall_getpid`: the instruction.
- `Seg.s_getpid`: the step of a run that `Fn.Seg` describes; the run goes on from the same start.
-/
namespace FV7z
open ZellicX86 Decode

variable {prof : Profile} {o : Oracle} {t : Nat} {s : State}

/-- `syscall` for `getpid ()`: the thread's id in `rax`, no other change. -/
theorem syscall_getpid {len : Nat} (htf : s.cpu.rflags.tf = false)
    (hdec : Decode.decode prof.feat (fetchByte prof.feat s) = .ok (mk .syscall 32 [] len))
    (hnr : s.cpu.gpr.rax.toNat % 2 ^ 32 = 39) :
    (instruction prof s).runStream o t =
      (.running (sysSt s len (BitVec.ofNat 64 s.thread.tid)) (some (sysEv s (BitVec.ofNat 64 s.thread.tid))), t) := by
  rw [instruction_syscall htf hdec]
  have hrax : (nx s len (sysGpr s len) (rf0 s)).cpu.gpr.rax = s.cpu.gpr.rax := rfl
  unfold syscall
  simp only [hrax, hnr]
  simp only [show ¬ (39 ≥ 2 ^ 31) by decide, show ¬ (39 ≥ x32Bit) by decide, show ¬ (39 ≥ nrSyscalls) by decide,
    show niSyscall 39 = false by decide, ↓reduceIte, Bool.false_eq_true]
  unfold sysGetpid
  rfl

end FV7z

namespace FV7z.Fn.Seg
open ZellicX86 Decode FV7z.Leaf

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle} {F : Footprint} {Wl : List Rgn}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop} {X : State} {t j : Nat}
  {e' : Addr} {code : List Byte} {V : Addr → Byte}

/-- `syscall` for `getpid ()`: the thread's id in `rax`, `rcx` and `r11` as `syscall` sets them, no other change. -/
theorem s_getpid (c : Seg prof F Wl L s₀ o) (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V)
    (hin : CodeIn L e' code) (hj : j < code.length) (hrip : X.cpu.rip = e'.add j) {len : Nat}
    (hd : Dec prof.feat code j (FV7z.mk .syscall 32 [] len)) (hnr : X.cpu.gpr.rax.toNat % 2 ^ 32 = 39)
    (k' : ContG prof F Wl L s₀ o (gev ++ [sysEv X (BitVec.ofNat 64 X.thread.tid)]) gP gE V fun Y =>
      Y.cpu.rip = e'.add (j + len) ∧ Y.cpu.gpr = (sysGpr X len).set 0 (BitVec.ofNat 64 X.thread.tid)) :
    GoG prof L o gev gP gE X t :=
  c.stepE hK hin hj hrip fun M hM hK' htf _ =>
    ⟨_, _, _, syscall_getpid (s := X.withMem M) htf (c.dec hK' hin hrip hd) hnr,
      k' _ _ (hK'.nx rfl rfl rfl) (c.agreeK hK hA hM) ⟨rip_add hrip M len, rfl⟩⟩

end FV7z.Fn.Seg
