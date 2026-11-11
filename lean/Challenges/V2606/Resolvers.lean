import ZellicX86.Spec.Executable
import FV7z.Image
import FV7z.Spec.Glibc
-- The challenge of `checks/ifunc-resolvers` (PLAN.md G2, "Dispatch theo CPUID"): the theorem of
-- `FV7z.Glibc.ResolversHolds` as stated, without its proof (`sorry`). Lean warns that it uses `sorry`: that is
-- expected; `lake comparator` holds the proof export to exactly this statement (`tools/check.sh`).
--
-- In words: for each IFUNC resolver of `Glibc.V2606.resolvers` (`FV7z/Spec/Glibc.lean`), its bytes in `7zzs` 26.06,
-- as Zellic's ELF reader reads them from the file, run at its address, on every consistent processor profile (with H-CPU-chain, `Glibc.Chain`), called
-- with `_dl_x86_cpu_features` as `init_cpu_features` leaves it (`Glibc.CpuOk`), return without a stack frame or a
-- system call one of its variants, only one whose features the processor has (`Glibc.Returns`).
namespace FV7z.V2606
open ZellicX86

theorem resolvers_hold : ∀ r ∈ Glibc.V2606.resolvers, ∀ code, Exe.bytesAt zzs.blob r.1 r.2.1 = some code →
    ∀ (L : List (Addr × List Byte)) (prof : Profile), prof.Consistent → Glibc.Chain prof →
      CodeIn L (BitVec.ofNat 64 r.1) code → ImplementsCall prof (BitVec.ofNat 64 r.1) L (Glibc.resolver prof r.2.2) := by
  sorry

end FV7z.V2606
