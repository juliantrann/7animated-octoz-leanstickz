import ZellicX86.Spec.Executable
import FV7z.Image
import FV7z.Spec.RegTm
-- The challenge of `checks/reg-tm` (PLAN.md G3, startup): the theorem of `FV7z.Rtc.InitHolds` as stated, without
-- its proof (`sorry`). Lean warns that it uses `sorry`: that is expected; `lake comparator` holds the proof export to
-- exactly this statement and refuses a proof that uses `sorry` (`tools/check.sh`).
--
-- In words: the 49 bytes of `7zzs` 26.06 at `0x41d3c0`, as Zellic's ELF reader reads them from the file
-- (`register_tm_clones` of GCC's `crtbegin.o`, which the first function of `.init_array` jumps to), at that address,
-- on any processor profile, keep `RegTm.contract` (`FV7z/Spec/RegTm.lean`): every call returns to its caller,
-- having read and written no memory but its return address's slot, made no system call, kept the callee-saved
-- registers, and executed no byte outside the code it was given (the table of clones is empty, so the `jmp` through
-- `_ITM_registerTMCloneTable`, which is 0 in the file, is not reached).
namespace FV7z.V2606
open ZellicX86

theorem regTm_holds : ∀ code, Exe.bytesAt zzs.blob 0x41d3c0 49 = some code →
    ∀ (L : List (Addr × List Byte)) (prof : Profile), CodeIn L 0x41d3c0 code →
      ImplementsCall prof 0x41d3c0 L RegTm.contract := by
  sorry

end FV7z.V2606
