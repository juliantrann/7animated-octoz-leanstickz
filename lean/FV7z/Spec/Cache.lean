import ZellicX86.Spec.Statement
/-!
# H-CPU-cache: the cache and topology leaves of `cpuid` end (PLAN.md §5.3, M ctor 103)

Only a definition, on Zellic's model alone, for a challenge to import.

glibc 2.31's `init_cacheinfo` (in `7zzs`: `intel_check_word` and the loop over the levels of leaf `0xB`) walks the
subleaves of `cpuid` leaves 4 and `0xB` until the processor says there are no more:

- leaf 4 ("deterministic cache parameters"): a subleaf whose cache type (`EAX[4:0]`) is 0 ends the list;
- leaf `0xB` ("extended topology"): a subleaf whose level type (`ECX[15:8]`) is 0 ends the list.

The code has no bound of its own, so without an assumption on the processor these loops need not end. The Intel SDM
(vol. 2A, `CPUID`) says that once a subleaf reports type 0 every higher subleaf does too; real processors have fewer
than 8 cache levels and topology levels. `CacheEnds` asks only for type 0 from subleaf 64 on, for every CPU the
profile may run the program on (`cpu < max prof.cpus 1`, the range `cpuid` picks from).
-/
namespace FV7z.Glibc
open ZellicX86

/-- H-CPU-cache: on every CPU, leaf 4 and leaf `0xB` report type 0 from subleaf 64 on. -/
structure CacheEnds (prof : Profile) : Prop where
  /-- Leaf 4: the cache type `EAX[4:0]` is 0 ("no more caches"). -/
  leaf4 : ∀ cpu, cpu < max prof.cpus 1 → ∀ sub : BitVec 32, 64 ≤ sub.toNat →
    (prof.cpuid cpu 4#32 sub).eax &&& 31#32 = 0#32
  /-- Leaf `0xB`: the level type `ECX[15:8]` is 0 ("invalid level"). -/
  leafB : ∀ cpu, cpu < max prof.cpus 1 → ∀ sub : BitVec 32, 64 ≤ sub.toNat →
    (prof.cpuid cpu 11#32 sub).ecx &&& 65280#32 = 0#32

end FV7z.Glibc
