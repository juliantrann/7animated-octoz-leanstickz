import ZellicX86.Spec.Statement
/-!
# The contract of `_fini` in `7zzs` (PLAN.md G3, startup)

Only definitions, on Zellic's model alone, for a challenge to import (`Challenges/V2606/FiniFn.lean`).

`_fini` is the section `.fini` (`0x6d7670`, 13 bytes: `crti.o`'s and `crtn.o`'s pieces, `sysdeps/x86_64/crti.S`),
which `__libc_csu_fini` calls after the functions of `.fini_array`. Between its prologue and its epilogue no object
file of `7zzs` puts anything, so it does nothing: a call

- reads and writes no memory but its return address's slot;
- returns to its caller with the callee-saved registers kept, having made no system call.
-/
namespace FV7z.FiniFn
open ZellicX86

/-- `_fini`'s contract: System V, no stack frame written, nothing assumed, no system call. -/
def contract : Contract where
  conv := sysv
  reads _ := []
  writes s := [frame s 0]
  pre _ := True
  post _ _ := True
  events _ _ evs := evs = []

end FV7z.FiniFn
