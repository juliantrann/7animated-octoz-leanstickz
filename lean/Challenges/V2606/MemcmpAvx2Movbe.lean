import ZellicX86.Spec.Executable
import Examples.Memcmp.Statement
import FV7z.Image
-- The challenge of `checks/memcmp-avx2-movbe` (PLAN.md G2.1): the theorem of `FV7z.Memcmp.Avx2MovbeHolds` as stated,
-- without its proof (`sorry`). Lean warns that it uses `sorry`: that is expected; `lake comparator` holds the proof
-- export to exactly this statement and refuses a proof that uses `sorry` (`tools/check.sh`).
--
-- In words: the 980 bytes of `7zzs` 26.06 at `0x63f660`, as Zellic's ELF reader reads them from the file
-- (`__memcmp_avx2_movbe` of glibc 2.31, the `memcmp` its IFUNC resolver picks on a processor with AVX2 and MOVBE),
-- placed anywhere, on any processor profile with AVX, AVX2 and MOVBE, implement `memcmp` as Zellic's
-- `Memcmp.contract` states it.
namespace FV7z.V2606
open ZellicX86

theorem memcmpAvx2Movbe_holds : ∀ code, Exe.bytesAt zzs.blob 0x63f660 980 = some code →
    ∀ (L : List (Addr × List Byte)) (prof : Profile) (e : Addr), prof.feat.avx = true → prof.feat.avx2 = true →
      prof.feat.movbe = true → CodeIn L e code → ImplementsCall prof e L Memcmp.contract := by
  sorry

end FV7z.V2606
