import ZellicX86.Spec.Executable
import FV7z.Image
import FV7z.Spec.SigjmpSave
-- The challenge of `checks/sigjmp-save` (PLAN.md G3, startup): the theorem of `FV7z.Sjs.InitHolds` as stated, without
-- its proof (`sorry`). Lean warns that it uses `sorry`: that is expected; `lake comparator` holds the proof export to
-- exactly this statement and refuses a proof that uses `sorry` (`tools/check.sh`).
--
-- In words: the 52 bytes of `7zzs` 26.06 at `0x67e0b0`, as Zellic's ELF reader reads them from the file (glibc
-- 2.31's `__sigjmp_save`, where `_setjmp`, which `__libc_start_main` calls before `main`, ends), at that address,
-- on any processor profile, keep `SigjmpSave.contract` (`FV7z/Spec/SigjmpSave.lean`): called with `savemask` 0 and
-- its frame apart from `env->__mask_was_saved`, every call returns 0 to its caller, having written only
-- `env->__mask_was_saved` (4 bytes at `env + 0x40`, now 0) and its frame, made no system call (the mask of
-- blocked signals is not asked for), kept the callee-saved registers, and executed no byte outside the code it was
-- given.
namespace FV7z.V2606
open ZellicX86

theorem sigjmpSave_holds : ∀ code, Exe.bytesAt zzs.blob 0x67e0b0 52 = some code →
    ∀ (L : List (Addr × List Byte)) (prof : Profile), CodeIn L 0x67e0b0 code →
      ImplementsCall prof 0x67e0b0 L SigjmpSave.contract := by
  sorry

end FV7z.V2606
