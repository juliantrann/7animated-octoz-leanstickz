import ZellicX86.Spec.Executable
import FV7z.Image
import FV7z.Spec.FiniFn
-- The challenge of `checks/fini-fn` (PLAN.md G3, startup): the theorem of `FV7z.Fin.InitHolds` as stated, without
-- its proof (`sorry`). Lean warns that it uses `sorry`: that is expected; `lake comparator` holds the proof export to
-- exactly this statement and refuses a proof that uses `sorry` (`tools/check.sh`).
--
-- In words: the 13 bytes of `7zzs` 26.06 at `0x6d7670`, as Zellic's ELF reader reads them from the file (the
-- section `.fini`: `_fini`, which `__libc_csu_fini` calls after the functions of `.fini_array`), at that address,
-- on any processor profile, keep `FiniFn.contract` (`FV7z/Spec/FiniFn.lean`): every call returns to its caller,
-- having read and written no memory but its return address's slot, made no system call, kept the callee-saved
-- registers, and executed no byte outside the code it was given.
namespace FV7z.V2606
open ZellicX86

theorem finiFn_holds : ∀ code, Exe.bytesAt zzs.blob 0x6d7670 13 = some code →
    ∀ (L : List (Addr × List Byte)) (prof : Profile), CodeIn L 0x6d7670 code →
      ImplementsCall prof 0x6d7670 L FiniFn.contract := by
  sorry

end FV7z.V2606
