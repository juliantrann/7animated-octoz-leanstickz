import ZellicX86.Spec.Statement
/-!
# The contract of `register_tm_clones` in `7zzs` (PLAN.md G3, startup)

Only definitions, on Zellic's model alone, for a challenge to import (`Challenges/V2606/RegTm.lean`).

`register_tm_clones` (`0x41d3c0`, 49 bytes: GCC's `libgcc/crtstuff.c`, in `crtbegin.o`) is what `frame_dummy`, the
first function of `.init_array`, ends in a jump to. The table of transactional-memory clones is empty in `7zzs` (its
begin and its end are both `0x793d10`, so its size, halved, is 0), and `_ITM_registerTMCloneTable` is a weak symbol
that is 0, so it does nothing: a call

- reads and writes no memory but its return address's slot;
- returns to its caller with the callee-saved registers kept, having made no system call.
-/
namespace FV7z.RegTm
open ZellicX86

/-- `register_tm_clones`'s contract: System V, no stack frame written, nothing assumed, no system call. -/
def contract : Contract where
  conv := sysv
  reads _ := []
  writes s := [frame s 0]
  pre _ := True
  post _ _ := True
  events _ _ evs := evs = []

end FV7z.RegTm
