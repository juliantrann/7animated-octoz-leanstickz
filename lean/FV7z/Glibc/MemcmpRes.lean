import FV7z.Glibc.IfuncMemcmp
import FV7z.Glibc.Pair
/-!
# `memcmp`'s IFUNC resolver as one of the list (PLAN.md G2, "Dispatch theo CPUID")

`IfMemcmp.holds` says the resolver returns what `IfMemcmp.Picks` allows; that is `Returns` of its four variants, so
the resolver implements `resolverK prof IfMemcmp.variants` too (`Leaf.leafK_mono`: a leaf contract with a weaker
postcondition).
-/
namespace FV7z
open ZellicX86

namespace Glibc.IfMemcmp

/-- The variants of `memcmp`, with the features their instructions need (`7zzs.featneed.tsv`). -/
abbrev variants : Variants :=
  [(0x63f260, []), (0x659840, [Features.ssse3]), (0x63fa40, [Features.sse41]),
    (0x63f660, [Features.avx, Features.avx2, Features.movbe])]

theorem returns {prof : Profile} {r : BitVec 64} (h : Picks prof r) : Returns prof variants r := by
  rcases h with rfl | ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, h1, h2, h3⟩
  · exact Returns.of_mem (fs := []) (by simp) (by simp)
  · exact Returns.of_mem (fs := [Features.ssse3]) (by simp) (by simp [h])
  · exact Returns.of_mem (fs := [Features.sse41]) (by simp) (by simp [h])
  · exact Returns.of_mem (fs := [Features.avx, Features.avx2, Features.movbe]) (by simp) (by simp [h1, h2, h3])

/-- `holds`, as one of the list. -/
theorem holds' (L : List (Addr × List Byte)) (prof : Profile) (hc : prof.Consistent) (hin : CodeIn L entry code) :
    ImplementsCall prof entry L (resolverK prof variants) :=
  Leaf.leafK_mono (fun _ _ h => returns h) (holds L prof hc hin)

end Glibc.IfMemcmp
end FV7z
