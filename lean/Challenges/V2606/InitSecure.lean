import ZellicX86.Spec.Executable
import FV7z.Image
import FV7z.Spec.InitSecure
-- The challenge of `checks/init-secure` (PLAN.md G3, startup): the theorem of `FV7z.Sec.InitHolds` as stated, without
-- its proof (`sorry`). Lean warns that it uses `sorry`: that is expected; `lake comparator` holds the proof export to
-- exactly this statement and refuses a proof that uses `sorry` (`tools/check.sh`).
--
-- In words: the 78 bytes of `7zzs` 26.06 at `0x6706a0`, as Zellic's ELF reader reads them from the file (glibc
-- 2.31's `__libc_init_secure`, which `__libc_start_main` calls after `_dl_aux_init`), at that address, on any
-- processor profile, keep `InitSecure.contract` (`FV7z/Spec/InitSecure.lean`): called with
-- `__libc_enable_secure_decided` not 0 (`_dl_aux_init` sets it to 1 at an `AT_SECURE` entry), every call returns to
-- its caller, having read only that variable, written nothing, made no system call (the user's and the group's ids
-- are not asked for), kept the callee-saved registers, and executed no byte outside the code it was given. So
-- `__libc_enable_secure` stays what `_dl_aux_init` set it to.
namespace FV7z.V2606
open ZellicX86

theorem initSecure_holds : ∀ code, Exe.bytesAt zzs.blob 0x6706a0 78 = some code →
    ∀ (L : List (Addr × List Byte)) (prof : Profile), CodeIn L 0x6706a0 code →
      ImplementsCall prof 0x6706a0 L InitSecure.contract := by
  sorry

end FV7z.V2606
