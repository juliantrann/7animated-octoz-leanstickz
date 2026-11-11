import ZellicX86.Spec.Statement
/-!
# The contract of `__libc_init_secure` in `7zzs` (PLAN.md G3, startup)

Only definitions, on Zellic's model alone, for a challenge to import (`Challenges/V2606/InitSecure.lean`).

`__libc_init_secure` (glibc 2.31, `elf/enbl-secure.c`) sets `__libc_enable_secure` from the user's and the group's
ids, which it asks the kernel for, unless `__libc_enable_secure_decided` says that it is set already. `_dl_aux_init`
sets both from the auxiliary vector's `AT_SECURE` entry (`FV7z/Spec/AuxInit.lean`), so in `7zzs` the kernel is not
asked. The contract is for that case: with `__libc_enable_secure_decided` not 0, a call

- reads only `__libc_enable_secure_decided`;
- writes nothing (its frame is the return address's slot);
- returns to its caller with the callee-saved registers kept, having made no system call.
-/
namespace FV7z.InitSecure
open ZellicX86

/-- `__libc_enable_secure_decided` (`0x7a85c4`, an `int`). -/
def rDecided : Rgn := ⟨0x7a85c4, 4⟩

/-- What a call reads. -/
def reads (_ : State) : List Rgn := [rDecided]

/-- What a call assumes: `__libc_enable_secure_decided` is not 0. -/
structure Pre (s : State) : Prop where
  decided : ofBytesLE 32 (readBytes s.proc.mm.mem 0x7a85c4 4) ≠ 0

/-- `__libc_init_secure`'s contract, with `__libc_enable_secure` decided: System V, no stack frame, no system
call. -/
def contract : Contract where
  conv := sysv
  reads := reads
  writes s := [frame s 0]
  pre := Pre
  post _ _ := True
  events _ _ evs := evs = []

end FV7z.InitSecure
