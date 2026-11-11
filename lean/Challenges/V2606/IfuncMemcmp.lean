import ZellicX86.Spec.Executable
import FV7z.Image
import FV7z.Spec.Glibc
-- The challenge of `checks/ifunc-memcmp` (PLAN.md G2, "Dispatch theo CPUID"): the theorem of
-- `FV7z.Glibc.IfuncMemcmpHolds` as stated, without its proof (`sorry`). Lean warns that it uses `sorry`: that is
-- expected; `lake comparator` holds the proof export to exactly this statement (`tools/check.sh`).
--
-- In words: the 105 bytes of `7zzs` 26.06 at `0x6369f0`, as Zellic's ELF reader reads them from the file (glibc
-- 2.31's IFUNC resolver of `memcmp`), run there, on every consistent processor profile, called with
-- `_dl_x86_cpu_features` as `init_cpu_features` leaves it (`Glibc.CpuOk`, `FV7z/Spec/Glibc.lean`), return without a
-- stack frame or a system call `__memcmp_sse2`, or `__memcmp_ssse3` only if the processor has SSSE3,
-- `__memcmp_sse4_1` only with SSE4.1, `__memcmp_avx2_movbe` only with AVX, AVX2 and MOVBE (`Glibc.IfMemcmp.Picks`).
namespace FV7z.V2606
open ZellicX86

theorem ifuncMemcmp_holds : ∀ code, Exe.bytesAt zzs.blob 0x6369f0 105 = some code →
    ∀ (L : List (Addr × List Byte)) (prof : Profile), prof.Consistent → CodeIn L 0x6369f0 code →
      ImplementsCall prof 0x6369f0 L (Glibc.IfMemcmp.contract prof) := by
  sorry

end FV7z.V2606
