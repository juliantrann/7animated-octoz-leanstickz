import FV7z.Lemmas.SysMm
/-!
# `futex (a, FUTEX_WAKE_PRIVATE, …)` (PLAN.md §M, M1)

glibc 2.31's `__pthread_once_slow` wakes the waiters of its control word after the init routine. On Zellic's model
(`sysFutex`), a private wake (`op` 0x81) wakes nobody (the process has one thread): `rax` is 0, or `-EINVAL` for a word
not aligned to 4, or `-EFAULT` for one beyond the user address space (`fwR`); no change but `rax`, `rcx`, `r11`.

- `sysFutex_wake`: the kernel's answer; `syscall_fwake`: what the instruction `syscall` leaves.
- `Seg.s_fwake`: the step in a run, its event (`fwEv`) put after the run's.
-/
namespace FV7z
open ZellicX86 Decode

variable {prof : Profile} {o : Oracle} {t : Nat} {s : State}

/-- The answer to a private wake of the word at `a`. -/
def fwR (feat : Features) (a : Addr) : BitVec 64 :=
  if a.toNat % 4 ≠ 0 then errRet EINVAL else if !accessOkFixed feat a 4 then errRet EFAULT else 0

/-- The answer is 0, `-EINVAL` or `-EFAULT`. -/
theorem fwR_cases (feat : Features) (a : Addr) :
    fwR feat a = 0 ∨ fwR feat a = errRet EINVAL ∨ fwR feat a = errRet EFAULT := by
  unfold fwR
  by_cases h1 : a.toNat % 4 ≠ 0
  · simp only [h1, ↓reduceIte, true_or, or_true]
  · by_cases h2 : (!accessOkFixed feat a 4) = true
    · simp only [h1, h2, ↓reduceIte, or_true]
    · simp only [h1, h2, ↓reduceIte, Bool.false_eq_true, true_or]

/-- The event of a private wake from the registers `g`. -/
abbrev fwEv (feat : Features) (g : Gprs) : Event :=
  ⟨g.rax, [g.rdi, g.rsi, g.rdx, g.r10, g.r8, g.r9], fwR feat g.rdi, [], []⟩

/-- `futex (a, FUTEX_WAKE | FUTEX_PRIVATE_FLAG, …)`. -/
theorem sysFutex_wake (hop : arg32 s.cpu.gpr.rsi = 0x81) :
    sysFutex prof s = Pure.pure (sysReturn s (fwR prof.feat s.cpu.gpr.rdi) [] []) := by
  unfold sysFutex fwR
  simp only [hop]
  by_cases h1 : s.cpu.gpr.rdi.toNat % 4 ≠ 0 <;> by_cases h2 : (!accessOkFixed prof.feat s.cpu.gpr.rdi 4) = true <;>
    simp (config := { decide := true }) [futexHasTimeout, FUTEX_WAKE, FUTEX_WAKE_BITSET, FUTEX_PRIVATE_FLAG,
      FUTEX_CLOCK_REALTIME, h1, h2]

/-- `syscall` for a private wake. -/
theorem syscall_fwake {len : Nat} (htf : s.cpu.rflags.tf = false)
    (hdec : Decode.decode prof.feat (fetchByte prof.feat s) = .ok (mk .syscall 32 [] len))
    (hnr : s.cpu.gpr.rax.toNat % 2 ^ 32 = 202) (hop : arg32 s.cpu.gpr.rsi = 0x81) :
    (instruction prof s).runStream o t =
      (.running (sysSt s len (fwR prof.feat s.cpu.gpr.rdi)) (some (fwEv prof.feat s.cpu.gpr)), t) := by
  rw [instruction_syscall htf hdec]
  have hrax : (nx s len (sysGpr s len) (rf0 s)).cpu.gpr.rax = s.cpu.gpr.rax := rfl
  unfold syscall
  simp only [hrax, hnr]
  simp only [show ¬ (202 ≥ 2 ^ 31) by decide, show ¬ (202 ≥ x32Bit) by decide, show ¬ (202 ≥ nrSyscalls) by decide,
    show niSyscall 202 = false by decide, ↓reduceIte, Bool.false_eq_true]
  rw [sysFutex_wake (s := nx s len (sysGpr s len) (rf0 s)) hop]
  rfl

end FV7z

namespace FV7z.Fn
open ZellicX86 Decode FV7z.Leaf

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle} {F : Footprint} {Wl : List Rgn}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop} {X : State} {t j : Nat}
  {e' : Addr} {code : List Byte} {V : Addr → Byte}

namespace Seg

/-- `syscall` for `futex (a, FUTEX_WAKE_PRIVATE, …)`: `rax` is `fwR`, `rcx` and `r11` as `syscall` sets them; the
event after the run's. -/
theorem s_fwake (c : Seg prof F Wl L s₀ o) (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V)
    (hin : CodeIn L e' code) (hj : j < code.length) (hrip : X.cpu.rip = e'.add j) {len : Nat}
    (hd : Dec prof.feat code j (FV7z.mk .syscall 32 [] len)) (hnr : X.cpu.gpr.rax.toNat % 2 ^ 32 = 202)
    (hop : arg32 X.cpu.gpr.rsi = 0x81)
    (k' : ContG prof F Wl L s₀ o (gev ++ [fwEv prof.feat X.cpu.gpr]) gP gE V fun Y =>
      Y.cpu.rip = e'.add (j + len) ∧ Y.cpu.gpr = (sysGpr X len).set 0 (fwR prof.feat X.cpu.gpr.rdi)) :
    GoG prof L o gev gP gE X t :=
  c.stepE hK hin hj hrip fun M hM hK' htf _ =>
    ⟨_, _, _, syscall_fwake (s := X.withMem M) htf (c.dec hK' hin hrip hd) hnr hop,
      k' _ _ (hK'.nx rfl rfl rfl) (c.agreeK hK hA hM) ⟨rip_add hrip M len, rfl⟩⟩

end Seg

end FV7z.Fn
