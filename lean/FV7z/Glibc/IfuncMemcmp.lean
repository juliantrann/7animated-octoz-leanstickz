import ZellicX86.Spec.Executable
import FV7z.Image
import FV7z.Glibc.Cpu
/-!
# glibc's IFUNC resolver of `memcmp` in `7zzs` picks a variant the processor has (PLAN.md G2, "Dispatch theo CPUID")

The 105 bytes at `0x6369f0` of `7zzs` (glibc 2.31's `sysdeps/x86_64/multiarch/ifunc-memcmp.h`, `memcmp`'s IFUNC
resolver): with `_dl_x86_cpu_features` as `init_cpu_features` leaves it (`CpuOk`), on a consistent profile, it returns
`__memcmp_sse2` (`0x63f260`), or `__memcmp_ssse3` (`0x659840`) on a processor with SSSE3, `__memcmp_sse4_1`
(`0x63fa40`) with SSE4.1, `__memcmp_avx2_movbe` (`0x63f660`) with AVX, AVX2 and MOVBE (`Picks`): so the variant a
call of `memcmp` reaches through the GOT never holds an instruction the processor lacks (`7zzs.featneed.tsv`: each
variant needs no feature beyond these).

```
 0  endbr64                    40  test edx, 0x80000 (SSE4_1)      80  test edx, 0x400000 (MOVBE)
 4  movabs rax, 0x80000000002  46  jne 69                          86  je 33
14  mov edx, cpuid[1].ecx      48  and dh, 2 (SSSE3)               88  lea rax, avx2_movbe
20  and rax, feature[0..1]     51  lea rax, sse2                   95  test byte feature[1]+1, 1
27  cmp rax, 2  (AVX2_Usable,  58  lea rdx, ssse3                       (AVX_Fast_Unaligned_Load)
     not Prefer_No_VZEROUPPER) 65  cmovne rax, rdx                102  je 33
31  je 80                      69  ret                            104  ret
33  lea rax, sse4_1
```
-/
namespace FV7z.Glibc.IfMemcmp
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- The bytes of the resolver, `0x6369f0` to `0x636a58` of `7zzs`. -/
def code : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0x48, 0xb8, 0x02, 0x00, 0x00, 0x00, 0x00, 0x08, 0x00, 0x00, 0x8b, 0x15,
  0xe4, 0xe0, 0x16, 0x00, 0x48, 0x23, 0x05, 0x35, 0xe1, 0x16, 0x00, 0x48, 0x83, 0xf8, 0x02, 0x74,
  0x2f, 0x48, 0x8d, 0x05, 0x28, 0x90, 0x00, 0x00, 0xf7, 0xc2, 0x00, 0x00, 0x08, 0x00, 0x75, 0x15,
  0x80, 0xe6, 0x02, 0x48, 0x8d, 0x05, 0x36, 0x88, 0x00, 0x00, 0x48, 0x8d, 0x15, 0x0f, 0x2e, 0x02,
  0x00, 0x48, 0x0f, 0x45, 0xc2, 0xc3, 0x66, 0x2e, 0x0f, 0x1f, 0x84, 0x00, 0x00, 0x00, 0x00, 0x00,
  0xf7, 0xc2, 0x00, 0x00, 0x40, 0x00, 0x74, 0xc9, 0x48, 0x8d, 0x05, 0x11, 0x8c, 0x00, 0x00, 0xf6,
  0x05, 0xef, 0xe0, 0x16, 0x00, 0x01, 0x74, 0xb9, 0xc3]

/-- They are the bytes of `7zzs` at `0x6369f0`, as `execve` maps them. -/
theorem pin : Exe.bytesAt V2606.zzs.blob 0x6369f0 105 = some code := by decide +kernel

theorem code_length : code.length = 105 := rfl

/-- Where `7zzs` has the resolver: its `rip`-relative operands name `_dl_x86_cpu_features` and the variants from
there. -/
def entry : Addr := 0x6369f0

/-! ## Decoding, on every processor -/

theorem d0 : ∀ feat, Dec feat code 0 (FV7z.mk .endbr64 32 [] 4) := by intro feat f; rfl
theorem d4 : ∀ feat, Dec feat code 4 (FV7z.mk .mov 64 [gr 64 0, .imm 64 8796093022210] 10) := by intro feat f; rfl
theorem d14 : ∀ feat, Dec feat code 14 (FV7z.mk .mov 32 [gr 32 2, .mem (mrip 1499364 32)] 6) := by intro feat f; rfl
theorem d20 : ∀ feat, Dec feat code 20 (FV7z.mk .and 64 [gr 64 0, .mem (mrip 1499445 64)] 7) := by intro feat f; rfl
theorem d27 : ∀ feat, Dec feat code 27 (FV7z.mk .cmp 64 [gr 64 0, .imm 64 2] 4) := by intro feat f; rfl
theorem d31 : ∀ feat, Dec feat code 31 (FV7z.mk (.jcc 4) 64 [.rel 47] 2) := by intro feat f; rfl
theorem d33 : ∀ feat, Dec feat code 33 (FV7z.mk .lea 64 [gr 64 0, .mem (mrip 36904 0)] 7) := by intro feat f; rfl
theorem d40 : ∀ feat, Dec feat code 40 (FV7z.mk .test 32 [gr 32 2, .imm 32 524288] 6) := by intro feat f; rfl
theorem d46 : ∀ feat, Dec feat code 46 (FV7z.mk (.jcc 5) 64 [.rel 21] 2) := by intro feat f; rfl
theorem d48 : ∀ feat, Dec feat code 48 (FV7z.mk .and 8 [gh 2, .imm 8 2] 3) := by intro feat f; rfl
theorem d51 : ∀ feat, Dec feat code 51 (FV7z.mk .lea 64 [gr 64 0, .mem (mrip 34870 0)] 7) := by intro feat f; rfl
theorem d58 : ∀ feat, Dec feat code 58 (FV7z.mk .lea 64 [gr 64 2, .mem (mrip 142863 0)] 7) := by intro feat f; rfl
theorem d65 : ∀ feat, Dec feat code 65 (FV7z.mk (.cmovcc 5) 64 [gr 64 0, gr 64 2] 4) := by intro feat f; rfl
theorem d69 : ∀ feat, Dec feat code 69 (FV7z.mk .ret 64 [] 1) := by intro feat f; rfl
theorem d80 : ∀ feat, Dec feat code 80 (FV7z.mk .test 32 [gr 32 2, .imm 32 4194304] 6) := by intro feat f; rfl
theorem d86 : ∀ feat, Dec feat code 86 (FV7z.mk (.jcc 4) 64 [.rel 18446744073709551561] 2) := by intro feat f; rfl
theorem d88 : ∀ feat, Dec feat code 88 (FV7z.mk .lea 64 [gr 64 0, .mem (mrip 35857 0)] 7) := by intro feat f; rfl
theorem d95 : ∀ feat, Dec feat code 95 (FV7z.mk .test 8 [.mem (mrip 1499375 8), .imm 8 1] 7) := by intro feat f; rfl
theorem d102 : ∀ feat, Dec feat code 102 (FV7z.mk (.jcc 4) 64 [.rel 18446744073709551545] 2) := by intro feat f; rfl
theorem d104 : ∀ feat, Dec feat code 104 (FV7z.mk .ret 64 [] 1) := by intro feat f; rfl

/-! ## The run -/

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {ra : Addr} {o : Oracle}

/-- `cpuid[COMMON_CPUID_INDEX_1].ecx` at the call. -/
abbrev ecx (s₀ : State) : BitVec 32 := ofBytesLE 32 (readBytes s₀.proc.mm.mem (cpuRgn.base.add 8) 4)

theorem ecx_bit (s₀ : State) {i : Nat} (hi : i < 32) : (ecx s₀).getLsbD i = bit s₀.proc.mm.mem 8 i :=
  getLsbD_word _ (by omega) hi

theorem hr0 {s : State} : cpuRgn ∈ RR s := List.mem_singleton_self _

/-- `AVX2_Usable` set, from `cmp rax, 2` finding `rax` 2. -/
theorem avx2_of_eq (W : BitVec 64) (h : (BitVec.ofNat 64 8796093022210 &&& W) = BitVec.ofNat 64 2) :
    W.getLsbD 1 = true := by
  have := congrArg (fun x => x.getLsbD 1) h
  simp only [BitVec.getLsbD_and] at this
  have h1 : (BitVec.ofNat 64 8796093022210).getLsbD 1 = true := by decide
  have h2 : (BitVec.ofNat 64 2).getLsbD 1 = true := by decide
  rw [h1, h2, Bool.true_and] at this
  exact this

theorem callee_of {X : State} (h : X.cpu.gpr.rbx = s₀.cpu.gpr.rbx ∧ X.cpu.gpr.rsp = s₀.cpu.gpr.rsp ∧
    X.cpu.gpr.rbp = s₀.cpu.gpr.rbp ∧ X.cpu.gpr.r12 = s₀.cpu.gpr.r12 ∧ X.cpu.gpr.r13 = s₀.cpu.gpr.r13 ∧
    X.cpu.gpr.r14 = s₀.cpu.gpr.r14 ∧ X.cpu.gpr.r15 = s₀.cpu.gpr.r15) : Callee s₀ X := h

/-- From `33`, `rdx` the word `cpuid[1].ecx`: `__memcmp_sse4_1` with SSE4.1, else `__memcmp_ssse3` with SSSE3, else
`__memcmp_sse2`. -/
theorem at33 (c : Call prof RR (PP prof) (QQ prof) code entry L s₀ ra o) (hc : prof.Consistent)
    {X : State} {t : Nat} (hK : Kept s₀ X) (hC : Callee s₀ X) (hrip : X.cpu.rip = entry.add 33)
    (hdx : X.cpu.gpr.rdx = (ecx s₀).setWidth 64) : Go prof RR (PP prof) (QQ prof) L s₀ ra o X t := by
  have hok : CpuOk prof s₀.proc.mm.mem := c.call.pre
  obtain ⟨c1, c2, c3, c4, c5, c6, c7⟩ := hC
  refine c.s_lea_rip hK (by decide) hrip (d33 _) (v := 0x63fa40) (by decide) fun Y1 _ hK1 hr1 ⟨g1, _⟩ => ?_
  refine c.s_test_ri32 hK1 (by decide) hr1 (d40 _) fun Y2 _ hK2 hr2 ⟨g2, z2⟩ => ?_
  refine c.s_jcc hK2 (by decide) hr2 (d46 _) (tgt := 69) (by decide) (by decide) (fun hcc => ?_) (fun hcc => ?_)
  · intro Y3 _ hK3 hr3 g3
    have hz : (rv Y1 32 2 &&& BitVec.ofNat 32 524288 == 0) = false := by
      rw [← z2]; simpa [cond5] using hcc
    have hb := getLsbD_of_and_pow (i := 19) _ hz
    simp only [rv, g1, get_regOf_2, set_rax, hdx, BitVec.getLsbD_setWidth] at hb
    refine c.ret hK3 (callee_of ?_) (by decide) hr3 (d69 _) ?_
    · simp [g3, g2, g1, c1, c2, c3, c4, c5, c6, c7]
    · refine Or.inr (Or.inr (Or.inl ⟨by simp [g3, g2, g1], (feat_of_ecx1 hc hok).2.1 ?_⟩))
      rw [← ecx_bit s₀ (i := 19) (by omega)]; simpa using hb
  · intro Y3 _ hK3 hr3 g3
    refine c.s_and_h8i hK3 (by decide) hr3 (d48 _) fun Y4 _ hK4 hr4 ⟨g4, z4⟩ => ?_
    refine c.s_lea_rip hK4 (by decide) hr4 (d51 _) (v := 0x63f260) (by decide) fun Y5 _ hK5 hr5 ⟨g5, z5⟩ => ?_
    refine c.s_lea_rip hK5 (by decide) hr5 (d58 _) (v := 0x659840) (by decide) fun Y6 _ hK6 hr6 ⟨g6, z6⟩ => ?_
    refine c.s_cmov hK6 (by decide) hr6 (d65 _) fun Y7 _ hK7 hr7 g7 => ?_
    have hdx3 : Y3.cpu.gpr.get (regOf 2) = (ecx s₀).setWidth 64 := by simp [g3, g2, g1, hdx]
    rw [cond5, z6, z5, z4, hdx3] at g7
    refine c.ret hK7 (callee_of ?_) (by decide) hr7 (d69 _) ?_
    · rw [g7]
      split <;> simp [g6, g5, g4, g3, g2, g1, c1, c2, c3, c4, c5, c6, c7]
    · show Picks prof Y7.cpu.gpr.rax
      rw [g7]
      split
      · next hz =>
        have hz' : (((ecx s₀).setWidth 64 >>> 8).setWidth 8 &&& BitVec.ofNat 8 2 == 0) = false := by simpa using hz
        have hb := getLsbD_of_and_pow (i := 1) _ hz'
        simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight] at hb
        refine Or.inr (Or.inl ⟨by simp [g6], (feat_of_ecx1 hc hok).1 ?_⟩)
        rw [← ecx_bit s₀ (i := 9) (by omega)]; simpa using hb
      · exact Or.inl (by simp [g6, g5])

/-- The run of a call, from its first instruction. -/
theorem run (c : Call prof RR (PP prof) (QQ prof) code entry L s₀ ra o) (hc : prof.Consistent) {t : Nat} :
    Go prof RR (PP prof) (QQ prof) L s₀ ra o s₀ t := by
  have hok : CpuOk prof s₀.proc.mm.mem := c.call.pre
  have hrip : s₀.cpu.rip = entry.add 0 := by rw [c.call.shape.1]; simp [Addr.add]
  refine c.s_endbr (Kept.refl s₀) (by decide) hrip (d0 _) fun Y1 _ hK1 hr1 g1 => ?_
  refine c.s_mov_ri64 hK1 (by decide) hr1 (d4 _) fun Y2 _ hK2 hr2 g2 => ?_
  refine c.s_mov32_rip hK2 (by decide) hr2 (d14 _) hr0 (a := 8) (by decide) (by decide)
    fun Y3 _ hK3 hr3 g3 => ?_
  refine c.s_and64_rip hK3 (by decide) hr3 (d20 _) hr0 (a := 96) (by decide) (by decide)
    fun Y4 _ hK4 hr4 ⟨g4, _⟩ => ?_
  refine c.s_cmp_ri hK4 (by decide) hr4 (d27 _) fun Y5 _ hK5 hr5 ⟨g5, f5⟩ => ?_
  have hdx : Y5.cpu.gpr.rdx = (ecx s₀).setWidth 64 := by simp [g5, g4, g3]
  refine c.s_jcc hK5 (by decide) hr5 (d31 _) (tgt := 80) (by decide) (by decide) (fun hcc => ?_) (fun _ => ?_)
  · intro Y6 _ hK6 hr6 g6
    have hW : bit s₀.proc.mm.mem 96 1 = true := by
      rw [cond4, f5, subF_zf, decide_eq_true_iff] at hcc
      simp only [rv, g4, g3, g2, g1, get_regOf_0, set_rax, set_rdx, BitVec.setWidth_eq] at hcc
      rw [← getLsbD_word (a := 96) (w := 64) (n := 8) (i := 1) _ (by omega) (by omega)]
      exact avx2_of_eq _ hcc
    refine c.s_test_ri32 hK6 (by decide) hr6 (d80 _) fun Y7 _ hK7 hr7 ⟨g7, z7⟩ => ?_
    refine c.s_jcc hK7 (by decide) hr7 (d86 _) (tgt := 33) (by decide) (by decide) (fun _ => ?_) (fun hcc7 => ?_)
    · intro Y8 _ hK8 hr8 g8
      exact at33 c hc hK8 (callee_of (by simp [g8, g7, g6, g5, g4, g3, g2, g1])) hr8
        (by rw [g8, g7, g6, hdx])
    · intro Y8 _ hK8 hr8 g8
      have hM : bit s₀.proc.mm.mem 8 22 = true := by
        have hz : (rv Y6 32 2 &&& BitVec.ofNat 32 4194304 == 0) = false := by
          rw [← z7]; simpa [cond4] using hcc7
        have hb := getLsbD_of_and_pow (i := 22) _ hz
        simp only [rv, g6, hdx, get_regOf_2, BitVec.getLsbD_setWidth] at hb
        rw [← ecx_bit s₀ (i := 22) (by omega)]; simpa using hb
      refine c.s_lea_rip hK8 (by decide) hr8 (d88 _) (v := 0x63f660) (by decide) fun Y9 _ hK9 hr9 ⟨g9, _⟩ => ?_
      refine c.s_test_m8i_rip hK9 (by decide) hr9 (d95 _) hr0 (a := 101) (by decide) (by decide)
        fun Y10 _ hK10 hr10 ⟨g10, _⟩ => ?_
      refine c.s_jcc hK10 (by decide) hr10 (d102 _) (tgt := 33) (by decide) (by decide) (fun _ => ?_) (fun _ => ?_)
      · intro Y11 _ hK11 hr11 g11
        exact at33 c hc hK11 (callee_of (by simp [g11, g10, g9, g8, g7, g6, g5, g4, g3, g2, g1])) hr11
          (by simp [g11, g10, g9, g8, g7, g6, hdx])
      · intro Y11 _ hK11 hr11 g11
        refine c.ret hK11 (callee_of (by simp [g11, g10, g9, g8, g7, g6, g5, g4, g3, g2, g1])) (by decide) hr11
          (d104 _) ?_
        have h2 := feat_avx2 hc hok hW
        exact Or.inr (Or.inr (Or.inr ⟨by simp [g11, g10, g9], h2.1, h2.2, (feat_of_ecx1 hc hok).2.2.2.1 hM⟩))
  · intro Y6 _ hK6 hr6 g6
    exact at33 c hc hK6 (callee_of (by simp [g6, g5, g4, g3, g2, g1])) hr6 (by rw [g6, hdx])

/-- glibc 2.31's IFUNC resolver of `memcmp`, the 105 bytes of `7zzs` 26.06 at `0x6369f0`, run there: on a consistent
profile, with `_dl_x86_cpu_features` as `init_cpu_features` leaves it, it returns a variant of `memcmp` whose
instructions the processor has. -/
theorem holds (L : List (Addr × List Byte)) (prof : Profile) (hc : prof.Consistent) (hin : CodeIn L entry code) :
    ImplementsCall prof entry L (Leaf.leafK RR (PP prof) (QQ prof)) := by
  intro s₀ ra hcall
  exact reachOrEndsIn_of_runsFrom fun o ho t => run ⟨hcall, hin, ho⟩ hc

end FV7z.Glibc.IfMemcmp
