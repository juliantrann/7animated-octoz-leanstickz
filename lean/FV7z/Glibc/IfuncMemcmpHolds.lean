import FV7z.Glibc.IfuncMemcmp
/-!
# The theorem of `checks/ifunc-memcmp` (PLAN.md G2, "Dispatch theo CPUID")

Under the name and statement of `Challenges/V2606/IfuncMemcmp.lean`: the bytes the file holds at `0x6369f0` are
`IfMemcmp.code` (`IfMemcmp.pin`), which, run there, pick a variant of `memcmp` the processor has
(`IfMemcmp.holds`).
-/
namespace FV7z.V2606
open ZellicX86

theorem ifuncMemcmp_holds : ∀ code, Exe.bytesAt zzs.blob 0x6369f0 105 = some code →
    ∀ (L : List (Addr × List Byte)) (prof : Profile), prof.Consistent → CodeIn L 0x6369f0 code →
      ImplementsCall prof 0x6369f0 L (Glibc.IfMemcmp.contract prof) := by
  intro code hc L prof hcons hin
  rw [Glibc.IfMemcmp.pin] at hc
  obtain rfl := Option.some.inj hc
  exact Leaf.leaf_of_leafK (Glibc.IfMemcmp.holds L prof hcons hin)

end FV7z.V2606
