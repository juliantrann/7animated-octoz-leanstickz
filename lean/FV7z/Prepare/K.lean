import FV7z.Prepare.AesGen
import FV7z.Prepare.Black2sp
import FV7z.Prepare.LzFind
import FV7z.Prepare.Sha
import FV7z.Prepare.Swap
import FV7z.Lemmas.CallFn
/-!
# The `*Prepare` functions by the contract `fnK` (PLAN.md §M, constructors)

Each contract's postcondition (`lzPost`, `shPost`, `agPost`, `b2Post`, `swPost`) is the variant's facts (`lzOk`, …)
and what the run kept, so the same theorem is `ImplementsCall` of `fnK`: what a caller's run goes on with past the
call (`Fn.Seg.s_callK`) or past a constructor that jumps to the function (`Ctor.implK_runs`). The constructors
`csuTg 5`, `7`, `9`, `92` are `endbr64; jmp f` with `f` one of these; `67` ends with `jmp 0x422a20`, `77` calls
`0x43d3d0` first.
-/
namespace FV7z.Prepare
open ZellicX86 FV7z.Fn

variable (prof : Profile) (hpc : prof.Consistent) {L : List (Addr × List Byte)}

/-- `LzFindPrepare`, by `fnK`. -/
theorem lzFindPrepareK (hin : CodeIn L 0x427de0 lz) (hinS : CodeIn L 0x424390 sse41)
    (hinA2 : CodeIn L 0x4244b0 avx2) (hinA : CodeIn L 0x424440 avx) (hinM : CodeIn L 0x4242b0 maxf)
    (hinC : CodeIn L 0x424290 cpuid) :
    ImplementsCall prof 0x427de0 L (fnK 120 lzW lzR lzPre fun _ Y => lzOk prof Y) :=
  lzFindPrepare prof hpc hin hinS hinA2 hinA hinM hinC

/-- `Sha1Prepare`, by `fnK`. -/
theorem sha1PrepareK (hin : CodeIn L 0x43a740 sha1p) (hinH : CodeIn L 0x4243e0 sha)
    (hinS : CodeIn L 0x424340 ssse3) (hinM : CodeIn L 0x4242b0 maxf) (hinC : CodeIn L 0x424290 cpuid) :
    ImplementsCall prof 0x43a740 L (fnK 88 (shW 0x792150 0x7967a8) lzR (shPre 0x792150 0x7967a8)
      fun _ Y => shOk prof 0x439b70 0x43a790 0x792150 0x7967a8 Y) :=
  sha1Prepare prof hpc hin hinH hinS hinM hinC

/-- `Sha256Prepare`, by `fnK`. -/
theorem sha256PrepareK (hin : CodeIn L 0x43b3e0 sha256p) (hinH : CodeIn L 0x4243e0 sha)
    (hinS : CodeIn L 0x424340 ssse3) (hinM : CodeIn L 0x4242b0 maxf) (hinC : CodeIn L 0x424290 cpuid) :
    ImplementsCall prof 0x43b3e0 L (fnK 88 (shW 0x792160 0x7967b0) lzR (shPre 0x792160 0x7967b0)
      fun _ Y => shOk prof 0x43a9f0 0x43b430 0x792160 0x7967b0 Y) :=
  sha256Prepare prof hpc hin hinH hinS hinM hinC

/-- `AesGenTables`, by `fnK`. -/
theorem aesGenTablesK (hin : CodeIn L 0x41e540 aesg) (hinA : CodeIn L 0x4242f0 aes)
    (hinV : CodeIn L 0x4245a0 vaes) (hinX : CodeIn L 0x424440 avx) (hinM : CodeIn L 0x4242b0 maxf)
    (hinC : CodeIn L 0x424290 cpuid) :
    ImplementsCall prof 0x41e540 L (fnK 136 agW agR agPre fun _ Y => agOk prof Y) :=
  aesGenTables prof hpc hin hinA hinV hinX hinM hinC

/-- `z7_Black2sp_Prepare`, by `fnK`. -/
theorem black2spPrepareK (hin : CodeIn L 0x422a20 b2s) (hinS : CodeIn L 0x424390 sse41)
    (hinA2 : CodeIn L 0x4244b0 avx2) (hinA : CodeIn L 0x424440 avx) (hinM : CodeIn L 0x4242b0 maxf)
    (hinC : CodeIn L 0x424290 cpuid) :
    ImplementsCall prof 0x422a20 L (fnK 120 b2W lzR b2Pre fun _ Y => b2Ok prof Y) :=
  black2spPrepare prof hpc hin hinS hinA2 hinA hinM hinC

/-- `z7_SwapBytesPrepare`, by `fnK`. -/
theorem swapBytesPrepareK (hin : CodeIn L 0x43d3d0 swap) (hinS : CodeIn L 0x424340 ssse3)
    (hinA2 : CodeIn L 0x4244b0 avx2) (hinA : CodeIn L 0x424440 avx) (hinM : CodeIn L 0x4242b0 maxf)
    (hinC : CodeIn L 0x424290 cpuid) :
    ImplementsCall prof 0x43d3d0 L (fnK 120 swW lzR swPre fun _ Y => swOk prof Y) :=
  swapBytesPrepare prof hpc hin hinS hinA2 hinA hinM hinC

end FV7z.Prepare
