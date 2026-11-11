import ZellicX86.Spec.Statement
/-!
# The contract of `__sigjmp_save` in `7zzs`, without a mask to save (PLAN.md G3, startup)

Only definitions, on Zellic's model alone, for a challenge to import (`Challenges/V2606/SigjmpSave.lean`).

`__sigjmp_save (env, savemask)` (glibc 2.31, `setjmp/sigjmp.c`) ends `__sigsetjmp`: with `savemask` not 0 it asks
the kernel for the mask of blocked signals (`__sigprocmask`) and keeps it in `env`; it sets `env->__mask_was_saved`
and returns 0. `_setjmp`, which `__libc_start_main` calls before `main`, gives `savemask` 0. The contract is for
that: a call

- writes only `env->__mask_was_saved` (4 bytes at `env + 0x40`), 0, and its frame (the saved `rbx`);
- returns 0 to its caller with the callee-saved registers kept, having made no system call.
-/
namespace FV7z.SigjmpSave
open ZellicX86

/-- `env->__mask_was_saved`: an `int` at `env + 0x40`. -/
def rSaved (s : State) : Rgn := ⟨s.cpu.gpr.rdi + 0x40#64, 4⟩

/-- What a call assumes: `savemask` (an `int`) is 0, and the frame is not in `env->__mask_was_saved`. -/
structure Pre (s : State) : Prop where
  nomask : s.cpu.gpr.rsi.setWidth 32 = 0#32
  frameApart : Apart [frame s 8] [rSaved s]

/-- What a call leaves: `rax` is 0 and `env->__mask_was_saved` is 0. -/
structure Post (s s' : State) : Prop where
  ret : s'.cpu.gpr.rax = 0
  saved : ofBytesLE 32 (readBytes s'.proc.mm.mem (s.cpu.gpr.rdi + 0x40#64) 4) = 0

/-- `__sigjmp_save`'s contract without a mask to save: System V, a frame of 8 bytes, no system call. -/
def contract : Contract where
  conv := sysv
  reads _ := []
  writes s := [frame s 8, rSaved s]
  pre := Pre
  post := Post
  events _ _ evs := evs = []

end FV7z.SigjmpSave
