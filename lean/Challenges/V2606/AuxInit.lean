import ZellicX86.Spec.Executable
import FV7z.Image
import FV7z.Spec.AuxInit
-- The challenge of `checks/aux-init` (PLAN.md G3, startup): the theorems of `FV7z.Auxv.InitHolds` as stated, without
-- their proofs (`sorry`). Lean warns that they use `sorry`: that is expected; `lake comparator` holds the proof
-- export to exactly these statements and refuses a proof that uses `sorry` (`tools/check.sh`).
--
-- In words: the 1041 bytes of `7zzs` 26.06 at `0x66f410`, as Zellic's ELF reader reads them from the file
-- (glibc 2.31's `_dl_aux_init`, the first function `__libc_start_main` calls, with the auxiliary vector), at that
-- address, on any processor profile, keep `AuxInit.contract X` (`FV7z/Spec/AuxInit.lean`) for every list of entries
-- `X`: called with `rdi` at a vector whose entries are `X`, none of type 0, one of them `AT_SECURE`, then an entry of
-- type 0, and with the jump table of the `switch` in memory (`AuxInit.Pre`), every call returns to its caller, having
-- read only the vector and the jump table, written only its stack frame, `_dl_auxv` and the twelve variables, made no
-- system call, kept the callee-saved registers, and executed no byte outside the code it was given; then `_dl_auxv`
-- is the vector's address and the variables are as the entries set them one after the other (`AuxInit.step`), so
-- `__libc_enable_secure` is the value of the last `AT_SECURE` entry.
--
-- And the jump table the contract assumes in memory is the 124 bytes the file holds at `0x6f3660`.
namespace FV7z.V2606
open ZellicX86

theorem auxInit_holds : ∀ code, Exe.bytesAt zzs.blob 0x66f410 1041 = some code →
    ∀ (L : List (Addr × List Byte)) (prof : Profile), CodeIn L 0x66f410 code →
      ∀ X : List (BitVec 64 × BitVec 64), ImplementsCall prof 0x66f410 L (AuxInit.contract X) := by
  sorry

theorem auxInit_table : Exe.bytesAt zzs.blob 0x6f3660 124 = some AuxInit.jumpTable := by
  sorry

end FV7z.V2606
