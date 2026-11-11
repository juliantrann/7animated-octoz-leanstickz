import ZellicX86.Spec.Executable
import FV7z.Image
import FV7z.Spec.DebugInit
-- The challenge of `checks/debug-init` (PLAN.md G3, startup): the theorem of `FV7z.Dbg.InitHolds` as stated, without
-- its proof (`sorry`). Lean warns that it uses `sorry`: that is expected; `lake comparator` holds the proof export to
-- exactly this statement and refuses a proof that uses `sorry` (`tools/check.sh`).
--
-- In words: the 124 bytes of `7zzs` 26.06 at `0x66e4a0`, as Zellic's ELF reader reads them from the file (glibc
-- 2.31's `_dl_debug_initialize`, which `__libc_start_main` calls with `(0, 0)` before `main`), at that address, on
-- any processor profile, keep `DebugInit.contract` (`FV7z/Spec/DebugInit.lean`): called for namespace 0 with the
-- return address outside `_r_debug`, every call returns `&_r_debug` to its caller, having written only `_r_debug`
-- (40 bytes at `0x7a84c0`) and its own return slot, read besides only the map of namespace 0 (`0x793440`), made no
-- system call, kept the callee-saved registers, and executed no byte outside the code it was given. With a map
-- already in `_r_debug` and no `ldbase` given, `_r_debug` is as it was; else its version is 1, its map that of
-- namespace 0, its `r_brk` is `&_dl_debug_state` (`0x66e490`), its `r_ldbase` is `ldbase` (or as it was, with 0),
-- and its `r_state` and padding are as they were.
namespace FV7z.V2606
open ZellicX86

theorem debugInit_holds : ∀ code, Exe.bytesAt zzs.blob 0x66e4a0 124 = some code →
    ∀ (L : List (Addr × List Byte)) (prof : Profile), CodeIn L 0x66e4a0 code →
      ImplementsCall prof 0x66e4a0 L DebugInit.contract := by
  sorry

end FV7z.V2606
