import ZellicX86.Spec.Statement
/-!
# The definitions the statements about glibc's IFUNC resolvers in `7zzs` use (PLAN.md G2, "Dispatch theo CPUID")

Only definitions, on Zellic's model alone, for a challenge to import (`Challenges/V2606/IfuncMemcmp.lean`):

- `Leaf.leaf`: the contract of a leaf function: System V, no stack frame (it writes only its return address's slot),
  no system call, a postcondition on what it returns in `rax`;
- `Glibc.cpuRgn`, `Glibc.bit`, `Glibc.CpuOk`: glibc 2.31's `_dl_x86_cpu_features` in `7zzs`, and what its words say
  about the processor once `init_cpu_features` has filled them;
- `Glibc.IfMemcmp.Picks`, `Glibc.IfMemcmp.contract`: what `memcmp`'s IFUNC resolver may return;
- `Glibc.Chain`: H-CPU-chain;
- `Glibc.Variants`, `Glibc.Returns`, `Glibc.resolver`: the same for any resolver, from the list of its variants, each
  with the features its instructions need (`7zzs.featneed.tsv`);
- `Glibc.V2606.irel`, `Glibc.V2606.GotOk`: the IRELATIVE relocations and what the GOT holds once `apply_irel` has
  run the resolvers.
-/
namespace FV7z
open ZellicX86

namespace Leaf

/-- A leaf function's contract: System V, no stack frame, no system call, and a postcondition on what it returns in
`rax` (and the state at the call). -/
def leaf (reads : State → List Rgn) (pre : State → Prop) (post : State → BitVec 64 → Prop) : Contract where
  conv := sysv
  reads := reads
  writes s := [frame s 0]
  pre := pre
  post s X := post s X.cpu.gpr.rax
  events _ _ evs := evs = []

end Leaf

namespace Glibc

/-- `cpu_features.cpuid` and `cpu_features.feature` of `_dl_x86_cpu_features` in `7zzs`. -/
def cpuRgn : Rgn := ⟨0x7a4ae0, 0x68⟩

/-- Bit `i` of the little-endian word at offset `a` of `cpuRgn`, in memory `m`. -/
def bit (m : Memory) (a i : Nat) : Bool := (m.readByte (cpuRgn.base.add (a + i / 8))).getLsbD (i % 8)

/-- What `_dl_x86_cpu_features` in memory `m` says about the processor `prof`. -/
structure CpuOk (prof : Profile) (m : Memory) : Prop where
  /-- `cpuid[COMMON_CPUID_INDEX_1].ecx`. -/
  ecx1 : ∀ i < 32, bit m 8 i = true → prof.reports 1 0 (·.ecx) i
  /-- `cpuid[COMMON_CPUID_INDEX_1].edx`. -/
  edx1 : ∀ i < 32, bit m 12 i = true → prof.reports 1 0 (·.edx) i
  /-- `cpuid[COMMON_CPUID_INDEX_7].ebx`. -/
  ebx7 : ∀ i < 32, bit m 20 i = true → prof.reports 7 0 (·.ebx) i
  /-- `cpuid[COMMON_CPUID_INDEX_7].ecx`. -/
  ecx7 : ∀ i < 32, bit m 24 i = true → prof.reports 7 0 (·.ecx) i
  /-- `AVX_Usable` (`feature[0]` bit 0): `CPUID.01H:ECX.AVX`, and `XCR0` has the SSE and AVX state. -/
  avx : bit m 96 0 = true → prof.reports 1 0 (·.ecx) 28 ∧ prof.enabled xcr0Avx
  /-- `AVX2_Usable` (bit 1): with `AVX_Usable`, `CPUID.(EAX=07H,ECX=0):EBX.AVX2`. -/
  avx2 : bit m 96 1 = true → bit m 96 0 = true ∧ prof.reports 7 0 (·.ebx) 5
  /-- `AVX512F_Usable` (bit 2): `CPUID.(EAX=07H,ECX=0):EBX.AVX512F`, and `XCR0` has the AVX-512 state. -/
  avx512f : bit m 96 2 = true → prof.reports 7 0 (·.ebx) 16 ∧ prof.enabled xcr0Avx512
  /-- `AVX512VL_Usable` (bit 6). -/
  avx512vl : bit m 96 6 = true → bit m 96 2 = true ∧ prof.reports 7 0 (·.ebx) 31
  /-- `AVX512DQ_Usable` (bit 7). -/
  avx512dq : bit m 96 7 = true → bit m 96 2 = true ∧ prof.reports 7 0 (·.ebx) 17
  /-- `AVX512BW_Usable` (bit 8). -/
  avx512bw : bit m 96 8 = true → bit m 96 2 = true ∧ prof.reports 7 0 (·.ebx) 30
  /-- `FMA_Usable` (bit 17): with `AVX_Usable`, `CPUID.01H:ECX.FMA`. -/
  fma : bit m 96 17 = true → bit m 96 0 = true ∧ prof.reports 1 0 (·.ecx) 12
  /-- `VAES_Usable` (bit 19): with `AVX_Usable`, `CPUID.(EAX=07H,ECX=0):ECX.VAES`. -/
  vaes : bit m 96 19 = true → bit m 96 0 = true ∧ prof.reports 7 0 (·.ecx) 9
  /-- `AVX_Fast_Unaligned_Load` (`feature[1]` bit 8): only with `AVX2_Usable`. -/
  fastAvx : bit m 100 8 = true → bit m 96 1 = true

end Glibc

namespace Glibc.IfMemcmp

/-- What the resolver may return on processor `prof`. -/
def Picks (prof : Profile) (r : BitVec 64) : Prop :=
  r = 0x63f260 ∨ (r = 0x659840 ∧ prof.feat.ssse3 = true) ∨ (r = 0x63fa40 ∧ prof.feat.sse41 = true) ∨
    (r = 0x63f660 ∧ prof.feat.avx = true ∧ prof.feat.avx2 = true ∧ prof.feat.movbe = true)

abbrev RR : State → List Rgn := fun _ => [cpuRgn]
abbrev PP (prof : Profile) : State → Prop := fun s => CpuOk prof s.proc.mm.mem
abbrev QQ (prof : Profile) : State → BitVec 64 → Prop := fun _ r => Picks prof r

/-- The resolver's contract: a leaf function, reading `_dl_x86_cpu_features`, which `CpuOk` describes at the call,
returning a variant the processor has. -/
abbrev contract (prof : Profile) : Contract := Leaf.leaf RR (PP prof) (QQ prof)

end Glibc.IfMemcmp

namespace Glibc

/-- A resolver's variants: each address, with features (fields of `Features`) the processor has when the resolver
picks it. -/
abbrev Variants := List (BitVec 64 × List (Features → Bool))

/-- `r` is one of the variants `vs` whose features the processor `prof` has. -/
def Returns (prof : Profile) (vs : Variants) (r : BitVec 64) : Prop :=
  ∃ v ∈ vs, r = v.1 ∧ ∀ f ∈ v.2, f prof.feat = true

/-- An IFUNC resolver's contract: a leaf function, reading `_dl_x86_cpu_features`, which `CpuOk` describes at the
call, returning one of the variants `vs` the processor has. -/
abbrev resolver (prof : Profile) (vs : Variants) : Contract :=
  Leaf.leaf (fun _ => [cpuRgn]) (fun s => CpuOk prof s.proc.mm.mem) (fun _ r => Returns prof vs r)

/-- H-CPU-chain (PLAN.md §5.3): the order of the extensions on every Intel and AMD processor. `Profile.Consistent`
ties each `CPUID` flag to its own feature only (a hypervisor may clear the flag of a feature the processor still
executes), while glibc 2.31 picks a variant by one flag whose code also uses the older extensions. -/
structure Chain (prof : Profile) : Prop where
  avx2 : prof.feat.avx512f = true → prof.feat.avx2 = true
  avx : prof.feat.avx2 = true → prof.feat.avx = true
  ssse3 : prof.feat.sse42 = true → prof.feat.ssse3 = true
  sse3 : prof.feat.ssse3 = true → prof.feat.sse3 = true

/-- IFUNC resolvers of `7zzs` 26.06 (`build/7zzs.dispatch.txt`): each address, length in bytes, and variants, a
variant with features the processor has when the resolver picks it, among them every feature its instructions need
beyond the `x86-64` baseline (`build/7zzs.featneed.tsv`). -/
def V2606.resolvers : List (Nat × Nat × Variants) := [
    (0x636090, 53, [(0x6546d0, []), (0x654a90, [Features.avx, Features.avx2])]),
    (0x6a1250, 53, [(0x6a1f00, []), (0x6a21a0, [Features.avx, Features.avx2])]),
    (0x6a1290, 53, [(0x6a1900, []), (0x6a1c30, [Features.avx, Features.avx2])]),
    (0x637440, 53, [(0x63ec30, []), (0x63f110, [Features.avx, Features.avx2])]),
    (0x6369b0, 53, [(0x63e900, []), (0x63ee40, [Features.avx, Features.avx2])]),
    (0x65d1f0, 53, [(0x65e120, []), (0x65edf0, [Features.avx, Features.avx2])]),
    (0x6360d0, 53, [(0x654870, []), (0x654c30, [Features.avx, Features.avx2])]),
    (0x637480, 53, [(0x653bd0, []), (0x654010, [Features.avx, Features.avx2])]),
    (0x636170, 53, [(0x654200, []), (0x654500, [Features.avx, Features.avx2])]),
    (0x6652e0, 30, [(0x665280, []), (0x665240, [Features.popcnt])]),
    (0x6c7320, 30, [(0x6c74f0, []), (0x6c76e0, [Features.sse42, Features.ssse3])]),
    (0x6c7300, 30, [(0x6c7440, []), (0x6c75a0, [Features.sse42, Features.ssse3])]),
    (0x635db0, 30, [(0x65b450, []), (0x65b500, [Features.sse42, Features.ssse3])]),
    (0x636990, 30, [(0x636640, []), (0x65afb0, [])]),
    (0x635cf0, 85, [(0x637670, []), (0x638ac0, []), (0x638d70, [Features.ssse3]), (0x639fe0, [Features.avx, Features.avx2])]),
    (0x6cd120, 85, [(0x6cd180, []), (0x6d06c0, []), (0x6cdb40, [Features.ssse3]), (0x6cd1e0, [Features.avx, Features.avx2])]),
    (0x635d50, 85, [(0x6552e0, []), (0x658480, []), (0x6554c0, [Features.ssse3]), (0x654f50, [Features.avx, Features.avx2])]),
    (0x636c80, 85, [(0x6553d0, []), (0x658ab0, []), (0x656c70, [Features.ssse3]), (0x659170, [Features.avx, Features.avx2])]),
    (0x6c7340, 72, [(0x64c3c0, []), (0x64e610, [Features.ssse3]), (0x650770, [Features.sse42, Features.ssse3]), (0x652320, [Features.avx])]),
    (0x6c7390, 72, [(0x698cc0, []), (0x69b320, [Features.ssse3]), (0x69d884, [Features.sse42, Features.ssse3]), (0x69f854, [Features.avx])]),
    (0x636ce0, 72, [(0x64c3e0, []), (0x64e630, [Features.ssse3]), (0x650784, [Features.sse42, Features.ssse3]), (0x652334, [Features.avx])]),
    (0x698c50, 72, [(0x698ca0, []), (0x69b300, [Features.ssse3]), (0x69d870, [Features.sse42, Features.ssse3]), (0x69f840, [Features.avx])]),
    (0x65d650, 69, [(0x65f460, []), (0x65f240, [Features.sse41]), (0x65f4a0, [Features.avx, Features.avx2])]),
    (0x635ca0, 69, [(0x6539a0, []), (0x659520, []), (0x653de0, [Features.avx, Features.avx2])]),
    (0x636110, 95, [(0x63a420, []), (0x63bc80, [Features.ssse3]), (0x63d3f0, [Features.sse42, Features.ssse3]), (0x63e3d0, [Features.avx, Features.avx2])]),
    (0x6c7810, 85, [(0x65c630, []), (0x65c7b0, [Features.avx, Features.avx2]), (0x65c930, [Features.avx, Features.avx2, Features.avx512f])]),
    (0x636bc0, 186, [(0x65b920, []), (0x65b8d0, []), (0x65b990, []), (0x641090, [Features.ssse3, Features.sse3]), (0x646620, [Features.ssse3, Features.sse3]), (0x65bca0, [Features.avx, Features.avx2]), (0x65bcf0, [Features.avx, Features.avx2]), (0x64bc60, [Features.avx, Features.avx2, Features.avx512f]), (0x65c0e0, [Features.avx, Features.avx2, Features.avx512f]), (0x65c130, [Features.avx, Features.avx2, Features.avx512f])]),
    (0x636d30, 186, [(0x65b950, []), (0x65b8e0, []), (0x65b9a0, []), (0x6410b0, [Features.ssse3, Features.sse3]), (0x646640, [Features.ssse3, Features.sse3]), (0x65bcb0, [Features.avx, Features.avx2]), (0x65bd00, [Features.avx, Features.avx2]), (0x64bc80, [Features.avx, Features.avx2, Features.avx512f]), (0x65c0f0, [Features.avx, Features.avx2, Features.avx512f]), (0x65c140, [Features.avx, Features.avx2, Features.avx512f])]),
    (0x636a60, 186, [(0x65b950, []), (0x65b8e0, []), (0x65b9a0, []), (0x643a90, [Features.ssse3, Features.sse3]), (0x649130, [Features.ssse3, Features.sse3]), (0x65bcb0, [Features.avx, Features.avx2]), (0x65bd00, [Features.avx, Features.avx2]), (0x64bc80, [Features.avx, Features.avx2, Features.avx512f]), (0x65c0f0, [Features.avx, Features.avx2, Features.avx512f]), (0x65c140, [Features.avx, Features.avx2, Features.avx512f])]),
    (0x636b20, 158, [(0x65c6a0, []), (0x65c6c0, []), (0x65c650, []), (0x65c7d0, [Features.avx, Features.avx2]), (0x65c820, [Features.avx, Features.avx2]), (0x65b650, [Features.avx, Features.avx2, Features.avx512f]), (0x65c950, [Features.avx, Features.avx2, Features.avx512f]), (0x65c9b0, [Features.avx, Features.avx2, Features.avx512f])]),
    (0x6369f0, 105, [(0x63f260, []), (0x659840, [Features.ssse3]), (0x63fa40, [Features.sse41]), (0x63f660, [Features.avx, Features.avx2, Features.movbe])])]

/-- The `R_X86_64_IRELATIVE` relocations of `7zzs` 26.06 (`.rela.plt`, `[0x400248, 0x400530)`), in the file's order:
each GOT slot (`r_offset`) with its resolver (`r_addend`). -/
def V2606.irel : List (Nat × Nat) := [
    (0x792108, 0x635cf0), (0x792100, 0x636090), (0x7920f8, 0x65d650), (0x7920f0, 0x6a1250),
    (0x7920e8, 0x6652e0), (0x7920e0, 0x6a1290), (0x7920d8, 0x6c7340), (0x7920d0, 0x6369f0),
    (0x7920c8, 0x6cd120), (0x7920c0, 0x637440), (0x7920b8, 0x636bc0), (0x7920b0, 0x6369b0),
    (0x7920a8, 0x65d1f0), (0x7920a0, 0x6c7810), (0x792098, 0x6c7320), (0x792090, 0x6360d0),
    (0x792088, 0x635d50), (0x792080, 0x6c7390), (0x792078, 0x636b20), (0x792070, 0x637480),
    (0x792068, 0x636d30), (0x792060, 0x6c7300), (0x792058, 0x636ce0), (0x792050, 0x636c80),
    (0x792048, 0x636170), (0x792040, 0x636110), (0x792038, 0x635ca0), (0x792030, 0x636990),
    (0x792028, 0x635db0), (0x792020, 0x698c50), (0x792018, 0x636a60)]

/-- The GOT after `apply_irel`: each slot of `V2606.irel` holds a variant of its resolver's whose features the
processor `prof` has. What a call through the PLT (`jmp *slot`) goes to. -/
def V2606.GotOk (prof : Profile) (m : Memory) : Prop :=
  ∀ p ∈ V2606.irel, ∀ r ∈ V2606.resolvers, r.1 = p.2 →
    Returns prof r.2.2 (ofBytesLE 64 (readBytes m (BitVec.ofNat 64 p.1) 8))

end Glibc

end FV7z
