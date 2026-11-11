import ZellicX86.Spec.Statement
/-!
# The contract of `_init` in `7zzs` (PLAN.md G3, startup)

Only definitions, on Zellic's model alone, for a challenge to import (`Challenges/V2606/InitFn.lean`).

`_init` is the section `.init` (`0x401000`, 27 bytes: `crti.o`'s and `crtn.o`'s pieces, `sysdeps/x86_64/crti.S`),
which `__libc_csu_init` calls between the functions of `.preinit_array` and those of `.init_array`. It would call
`__gmon_start__`, a weak symbol that is 0 in `7zzs`, so it does nothing: a call

- reads and writes no memory but its return address's slot;
- returns to its caller with the callee-saved registers kept, having made no system call.
-/
namespace FV7z.InitFn
open ZellicX86

/-- `_init`'s contract: System V, no stack frame written, nothing assumed, no system call. -/
def contract : Contract where
  conv := sysv
  reads _ := []
  writes s := [frame s 0]
  pre _ := True
  post _ _ := True
  events _ _ evs := evs = []

end FV7z.InitFn
