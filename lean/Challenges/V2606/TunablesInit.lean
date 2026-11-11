import ZellicX86.Spec.Executable
import FV7z.Image
import FV7z.Spec.Tunables
-- The challenge of `checks/tunables-init` (PLAN.md G3, startup): the theorem of `FV7z.Tun.InitHolds` as stated,
-- without its proof (`sorry`). Lean warns that it uses `sorry`: that is expected; `lake comparator` holds the proof
-- export to exactly this statement and refuses a proof that uses `sorry` (`tools/check.sh`).
--
-- In words: the 1413 bytes of `7zzs` 26.06 at `0x66ee10`, as Zellic's ELF reader reads them from the file
-- (glibc 2.31's `__tunables_init`, which `__libc_start_main` calls with the environment), at that address, on any
-- processor profile, keep `Tunables.contract A E` (`FV7z/Spec/Tunables.lean`) for every environment `E` and list of
-- aliases `A`: called with `__libc_enable_secure` 0 and an environment `E` none of whose strings begins with
-- `GLIBC_TUNABLES=` or with a tunable's alias and `=` (`Tunables.Pre`), every call returns to its caller, having read
-- only `__libc_enable_secure`, the string `GLIBC_TUNABLES`, the list of tunables, the environment's array and strings
-- and the aliases' strings, written only its stack frame, made no system call, kept the callee-saved registers, and
-- executed no byte outside the code it was given.
namespace FV7z.V2606
open ZellicX86

theorem tunablesInit_holds : ∀ code, Exe.bytesAt zzs.blob 0x66ee10 1413 = some code →
    ∀ (L : List (Addr × List Byte)) (prof : Profile), CodeIn L 0x66ee10 code →
      ∀ A E : List (Addr × List Byte), ImplementsCall prof 0x66ee10 L (Tunables.contract A E) := by
  sorry

end FV7z.V2606
