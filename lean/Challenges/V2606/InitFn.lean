import ZellicX86.Spec.Executable
import FV7z.Image
import FV7z.Spec.InitFn
-- The challenge of `checks/init-fn` (PLAN.md G3, startup): the theorem of `FV7z.Ini.InitHolds` as stated, without
-- its proof (`sorry`). Lean warns that it uses `sorry`: that is expected; `lake comparator` holds the proof export to
-- exactly this statement and refuses a proof that uses `sorry` (`tools/check.sh`).
--
-- In words: the 27 bytes of `7zzs` 26.06 at `0x401000`, as Zellic's ELF reader reads them from the file (the
-- section `.init`: `_init`, which `__libc_csu_init` calls before the functions of `.init_array`), at that address,
-- on any processor profile, keep `InitFn.contract` (`FV7z/Spec/InitFn.lean`): every call returns to its caller,
-- having read and written no memory but its return address's slot, made no system call, kept the callee-saved
-- registers, and executed no byte outside the code it was given (`__gmon_start__` is 0 in the file, and the
-- `call` through it is not reached).
namespace FV7z.V2606
open ZellicX86

theorem initFn_holds : ∀ code, Exe.bytesAt zzs.blob 0x401000 27 = some code →
    ∀ (L : List (Addr × List Byte)) (prof : Profile), CodeIn L 0x401000 code →
      ImplementsCall prof 0x401000 L InitFn.contract := by
  sorry

end FV7z.V2606
