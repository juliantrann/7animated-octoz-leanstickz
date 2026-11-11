import ZellicX86.Spec.Executable
import FV7z.Image
import FV7z.Spec.DeregTm
-- The challenge of `checks/dereg-tm` (PLAN.md G3, startup): the theorem of `FV7z.Dtc.InitHolds` as stated, without
-- its proof (`sorry`). Lean warns that it uses `sorry`: that is expected; `lake comparator` holds the proof export to
-- exactly this statement and refuses a proof that uses `sorry` (`tools/check.sh`).
--
-- In words: the 33 bytes of `7zzs` 26.06 at `0x41d390`, as Zellic's ELF reader reads them from the file
-- (`deregister_tm_clones` of GCC's `crtbegin.o`, which the first function of `.fini_array` calls), at that address,
-- on any processor profile, keep `DeregTm.contract` (`FV7z/Spec/DeregTm.lean`): every call returns to its caller,
-- having read and written no memory but its return address's slot, made no system call, kept the callee-saved
-- registers, and executed no byte outside the code it was given (the table of clones is empty, so the `jmp` through
-- `_ITM_deregisterTMCloneTable`, which is 0 in the file, is not reached).
namespace FV7z.V2606
open ZellicX86

theorem deregTm_holds : ∀ code, Exe.bytesAt zzs.blob 0x41d390 33 = some code →
    ∀ (L : List (Addr × List Byte)) (prof : Profile), CodeIn L 0x41d390 code →
      ImplementsCall prof 0x41d390 L DeregTm.contract := by
  sorry

end FV7z.V2606
