import FV7z.Lemmas.LeafSteps
import FV7z.Spec.Glibc
/-!
# glibc 2.31's `_dl_x86_cpu_features` in `7zzs` (PLAN.md G2, "Dispatch theo CPUID")

`init_cpu_features` (`sysdeps/x86/cpu-features.c`) fills `struct cpu_features` once, at start-up, from `CPUID` and
`XGETBV`; every IFUNC resolver then reads it and returns a variant. In `7zzs` its words `cpuid[k]` (leaves 1, 7,
`80000001H`, `0DH`/1, `80000007H`, `80000008H`, each `eax`, `ebx`, `ecx`, `edx`) and `feature[2]` lie at `0x7a4ae0` to
`0x7a4b47` (`cpuRgn`): `cpuid[0].ecx` at offset 8, `cpuid[0].edx` at 12, `cpuid[1].ebx` at 20, `cpuid[1].ecx` at 24,
`feature[0]` (the `*_Usable` bits) at 96 and `feature[1]` (the `Fast_*`, `Slow_*`, `Prefer_*` bits) at 100.

`CpuOk prof m`: what those words in memory `m` say about the processor `prof`, as `init_cpu_features` leaves them. A
`CPUID` bit glibc kept is one some CPU of `prof` reports (`Profile.reports`); a `*_Usable` bit is set only with the
`CPUID` bits and the `XCR0` state `init_cpu_features` checks for it; `AVX_Fast_Unaligned_Load` only with
`AVX2_Usable` (also by `GLIBC_TUNABLES`, `cpu_features.c`'s `TUNABLE_CALLBACK (set_hwcaps)`). That
`init_cpu_features` establishes it is a separate proof (PLAN.md); the resolvers' theorems assume it at their call.
-/
namespace FV7z.Glibc
open ZellicX86

/-- `resolver`, whose postcondition also says what the resolver kept (`Leaf.leafK`): what the resolvers' theorems
prove, for `apply_irel`'s run to go on past each call. -/
abbrev resolverK (prof : Profile) (vs : Variants) : Contract :=
  Leaf.leafK (fun _ => [cpuRgn]) (fun s => CpuOk prof s.proc.mm.mem) (fun _ r => Returns prof vs r)

/-- Bit `i` of a word of `n` bytes read at offset `a` of `cpuRgn`. -/
theorem getLsbD_word (m : Memory) {a w n i : Nat} (hi : i < 8 * n) (hiw : i < w) :
    (ofBytesLE w (readBytes m (cpuRgn.base.add a) n)).getLsbD i = bit m a i := by
  have h8 : i / 8 < n := by omega
  rw [getLsbD_ofBytesLE]
  simp [readBytes, byteAddrs, hiw, h8, bit, addr_add_add]

/-- A bit `test` or `and` found set. -/
theorem getLsbD_of_and_pow {w i : Nat} (x : BitVec w) (h : (x &&& BitVec.ofNat w (2 ^ i) == 0) = false) :
    x.getLsbD i = true := by
  cases hx : x.getLsbD i
  · have : x &&& BitVec.ofNat w (2 ^ i) = 0 := by
      apply BitVec.eq_of_getLsbD_eq
      intro j hj
      simp only [BitVec.getLsbD_and, BitVec.getLsbD_ofNat, Nat.testBit_two_pow, BitVec.getLsbD_zero]
      by_cases hji : i = j
      · subst hji; simp [hx]
      · simp [hji]
    simp [this] at h
  · rfl

/-- What a set bit of `cpuid[COMMON_CPUID_INDEX_1].ecx` gives, on a consistent profile. -/
theorem feat_of_ecx1 {prof : Profile} {m : Memory} (hc : prof.Consistent) (h : CpuOk prof m) :
    (bit m 8 9 = true → prof.feat.ssse3 = true) ∧ (bit m 8 19 = true → prof.feat.sse41 = true) ∧
      (bit m 8 20 = true → prof.feat.sse42 = true) ∧ (bit m 8 22 = true → prof.feat.movbe = true) ∧
      (bit m 8 0 = true → prof.feat.sse3 = true) ∧ (bit m 8 23 = true → prof.feat.popcnt = true) :=
  ⟨fun b => hc.ssse3 (h.ecx1 9 (by omega) b), fun b => hc.sse41 (h.ecx1 19 (by omega) b),
    fun b => hc.sse42 (h.ecx1 20 (by omega) b), fun b => hc.movbe (h.ecx1 22 (by omega) b),
    fun b => hc.sse3 (h.ecx1 0 (by omega) b), fun b => hc.popcnt (h.ecx1 23 (by omega) b)⟩

/-- `AVX_Usable` and `AVX2_Usable`, on a consistent profile. -/
theorem feat_avx {prof : Profile} {m : Memory} (hc : prof.Consistent) (h : CpuOk prof m) (b : bit m 96 0 = true) :
    prof.feat.avx = true :=
  hc.avx (h.avx b).1 (h.avx b).2

theorem feat_avx2 {prof : Profile} {m : Memory} (hc : prof.Consistent) (h : CpuOk prof m) (b : bit m 96 1 = true) :
    prof.feat.avx = true ∧ prof.feat.avx2 = true :=
  ⟨feat_avx hc h (h.avx2 b).1, hc.avx2 (h.avx2 b).2 (h.avx (h.avx2 b).1).2⟩

/-- `AVX512F_Usable`, on a consistent profile. -/
theorem feat_avx512f {prof : Profile} {m : Memory} (hc : prof.Consistent) (h : CpuOk prof m)
    (b : bit m 96 2 = true) : prof.feat.avx512f = true :=
  hc.avx512f (h.avx512f b).1 (h.avx512f b).2

/-- `AVX512F_Usable` set, from `feature[0..1] & 0x400000000004` found `4` (`AVX512F_Usable`, not
`Prefer_No_AVX512`). -/
theorem avx512_of_eq (W : BitVec 64) (h : (W &&& BitVec.ofNat 64 70368744177668) = BitVec.ofNat 64 4) :
    W.getLsbD 2 = true := by
  have := congrArg (fun x => x.getLsbD 2) h
  simp only [BitVec.getLsbD_and] at this
  have h1 : (BitVec.ofNat 64 70368744177668).getLsbD 2 = true := by decide
  have h2 : (BitVec.ofNat 64 4).getLsbD 2 = true := by decide
  rw [h1, h2, Bool.and_true] at this
  exact this

theorem avx512_of_eq' (W : BitVec 64) (h : (BitVec.ofNat 64 70368744177668 &&& W) = BitVec.ofNat 64 4) :
    W.getLsbD 2 = true :=
  avx512_of_eq W (by rw [BitVec.and_comm]; exact h)

/-- AVX-512F, so (H-CPU-chain) AVX2 and AVX, from `AVX512F_Usable`. -/
theorem feat_avx512 {prof : Profile} {m : Memory} (hc : prof.Consistent) (hch : Chain prof) (h : CpuOk prof m)
    (b : bit m 96 2 = true) : prof.feat.avx = true ∧ prof.feat.avx2 = true ∧ prof.feat.avx512f = true :=
  have h5 := feat_avx512f hc h b
  ⟨hch.avx (hch.avx2 h5), hch.avx2 h5, h5⟩

/-- A `lea rW, [rip + d]` at the `k`-th byte of `code` (at `e`), of 7 bytes, naming `v`, on every processor. -/
def Lea (code : List Byte) (e : Addr) (k r : Nat) (v : Addr) : Prop :=
  ∃ d, (∀ feat, Leaf.Dec feat code k (FV7z.mk .lea 64 [gr 64 r, .mem (mrip d 0)] 7)) ∧
    e.add (k + 7) + BitVec.ofNat 64 d = v

/-- `cpuid[COMMON_CPUID_INDEX_1].ecx` at the call. -/
abbrev ecx1 (s₀ : State) : BitVec 32 := ofBytesLE 32 (readBytes s₀.proc.mm.mem (cpuRgn.base.add 8) 4)

theorem ecx1_bit (s₀ : State) {i : Nat} (hi : i < 32) : (ecx1 s₀).getLsbD i = bit s₀.proc.mm.mem 8 i :=
  getLsbD_word _ (by omega) hi

end FV7z.Glibc
