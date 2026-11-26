import FV7z.Spec.Glibc
import FV7z.Spec.Cache
/-!
# A processor for the theorem against vacuity (PLAN.md §M)

`launch_main_plt` asks of the processor: a consistent profile (`Profile.Consistent`), the order of glibc's feature
checks (`Chain`), no SSSE3 with SSE3 and no AVX with AVX2, `CPUID`'s cache leaves ending (`CacheEnds`), no vDSO and a
modest kernel (`LinuxBoot.Modest`). `prof0` has them: one Intel CPU whose `CPUID` answers 0 everywhere (no feature
beyond the `x86-64` baseline, no `XSAVE`), with NX.

- `feat0`, `prof0`; `nrep`: no `CPUID` bit of `prof0` is set.
- `consistent0`, `chain0`, `cacheEnds0`, `modest0`, `vdso0`, `ssse3_0`, `avx_0`.
-/
namespace FV7z.Wit
open ZellicX86 FV7z.Glibc

/-- The features: the `x86-64` baseline, with NX. -/
def feat0 : Features where
  ssse3 := false
  sse41 := false
  sha := false
  bmi1 := false
  lzcnt := false
  avx := false
  avx512f := false
  apx := false
  pku := false
  nx := true
  la57 := false
  sse42 := false
  bmi2 := false
  avx2 := false
  avx512bw := false
  avx512dq := false
  avx512vl := false
  movbe := false
  rdtscp := false
  sse3 := false
  fma := false
  cetSs := false
  rtm := false
  hle := false
  xsavec := false
  aes := false
  vaes := false
  popcnt := false
  mpx := false

/-- One Intel CPU, `CPUID` 0 everywhere, no `XSAVE`, Linux without a vDSO. -/
def prof0 : Profile where
  vendor := .intel
  feat := feat0
  aux := ⟨0, 0, 1440⟩
  cpus := 1
  cpuid := fun _ _ _ => ⟨0, 0, 0, 0⟩
  xcr0 := none
  mxcsrMask := 0xffff
  tscAux := fun _ => 0
  fdpExcptnOnly := false
  fcsDeprecated := false
  amdErrPtrs := false
  linux := { vdso := false, vdsoData := fun _ => false, vdsoText := [], compatBrk := false }

/-- No `CPUID` bit of `prof0` is set. -/
theorem nrep {leaf sub : BitVec 32} {r : CpuidResult → BitVec 32} {i : Nat} (hr : r ⟨0, 0, 0, 0⟩ = 0) :
    ¬ prof0.reports leaf sub r i := fun ⟨_, _, h⟩ => by
  change (r ⟨0, 0, 0, 0⟩).getLsbD i = true at h
  rw [hr] at h
  simp at h

theorem consistent0 : prof0.Consistent where
  sse3 h := absurd h (nrep rfl)
  ssse3 h := absurd h (nrep rfl)
  fma h _ := absurd h (nrep rfl)
  sse41 h := absurd h (nrep rfl)
  sse42 h := absurd h (nrep rfl)
  movbe h := absurd h (nrep rfl)
  osxsave h := absurd h (nrep rfl)
  avx h _ := absurd h (nrep rfl)
  bmi1 h := absurd h (nrep rfl)
  avx2 h _ := absurd h (nrep rfl)
  bmi2 h := absurd h (nrep rfl)
  avx512f h _ := absurd h (nrep rfl)
  avx512dq h _ := absurd h (nrep rfl)
  sha h := absurd h (nrep rfl)
  avx512bw h _ := absurd h (nrep rfl)
  avx512vbmi h _ := absurd h (nrep rfl)
  avx512vl h _ := absurd h (nrep rfl)
  pku h := absurd h (nrep rfl)
  cetSs h := absurd h (nrep rfl)
  rtm h := absurd h (nrep rfl)
  hle h := absurd h (nrep rfl)
  xsavec h _ := absurd h (nrep rfl)
  aes h := absurd h (nrep rfl)
  vaes h _ := absurd h (nrep rfl)
  popcnt h := absurd h (nrep rfl)
  mpx h := absurd h (nrep rfl)
  apx h _ := absurd h (nrep rfl)
  lzcnt h := absurd h (nrep rfl)
  rdtscp h := absurd h (nrep rfl)
  fdpExcptnOnly _ h := absurd h (nrep rfl)
  fcsDeprecated _ h := absurd h (nrep rfl)
  amdErrPtrs h _ := absurd h (by decide)
  minSigStkSz := by decide
  noSubleaf _ _ _ := rfl

theorem chain0 : Chain prof0 := ⟨id, id, id, id⟩

theorem cacheEnds0 : CacheEnds prof0 := ⟨fun _ _ _ _ => rfl, fun _ _ _ _ => rfl⟩

theorem modest0 : prof0.linux.Modest := ⟨by decide, by decide⟩

theorem vdso0 : prof0.linux.vdso = false := rfl

theorem ssse3_0 : ¬ (prof0.feat.ssse3 = true ∧ prof0.feat.sse3 = true) := by decide

theorem avx_0 : ¬ (prof0.feat.avx = true ∧ prof0.feat.avx2 = true) := by decide

end FV7z.Wit
