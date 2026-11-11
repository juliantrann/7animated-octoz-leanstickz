import FV7z.Glibc.Avx2Pick
/-!
# The IFUNC resolvers of `7zzs` that pick among `avx`, `sse42`, `ssse3`, `sse2` (PLAN.md G2, "Dispatch theo CPUID")

Four resolvers of `7zzs` (glibc 2.31's `sysdeps/x86_64/multiarch/ifunc-strcasecmp.h`: `strcasecmp`, `strncasecmp`,
their `_l` forms, …) are the same 72 bytes but for their `rip`-relative displacements:

```
 0  endbr64                                    34  lea rax, vSse42
 4  lea rax, vAvx                              41  test byte feature[1], 0x80  (Slow_SSE4_2)
11  test byte feature[0], 1  (AVX_Usable)      48  je 71
18  jne 71                                     50  and dh, 2                   (SSSE3)
20  mov edx, cpuid[1].ecx                      53  lea rax, vSse2
26  test edx, 0x100000  (SSE4_2)               60  lea rdx, vSsse3
32  je 50                                      67  cmovne rax, rdx
                                               71  ret
```

`Shape code e vAvx vSse42 vSse2 vSsse3`: `code`, at `e`, is such a resolver. `holds`: with `_dl_x86_cpu_features` as
`init_cpu_features` leaves it (`CpuOk`), on a consistent profile with H-CPU-chain, it returns `vSse2`, or `vSsse3` on
a processor with SSSE3, `vSse42` with SSE4.2 (so SSSE3), `vAvx` with AVX.
-/
namespace FV7z.Glibc.StrCaseCmp
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf
open Avx2Pick (RR PP QQ hr0)

/-- What the bytes `code` at `e` decode to, and where their operands point. -/
structure Shape (code : List Byte) (e vAvx vSse42 vSse2 vSsse3 : Addr) : Prop where
  len : code.length = 72
  d0 : ∀ feat, Dec feat code 0 (FV7z.mk .endbr64 32 [] 4)
  d4 : Lea code e 4 0 vAvx
  d11 : ∃ d, (∀ feat, Dec feat code 11 (FV7z.mk .test 8 [.mem (mrip d 8), .imm 8 1] 7)) ∧
    e.add (11 + 7) + BitVec.ofNat 64 d = cpuRgn.base.add 96
  d18 : ∀ feat, Dec feat code 18 (FV7z.mk (.jcc 5) 64 [.rel 51] 2)
  d20 : ∃ d, (∀ feat, Dec feat code 20 (FV7z.mk .mov 32 [gr 32 2, .mem (mrip d 32)] 6)) ∧
    e.add (20 + 6) + BitVec.ofNat 64 d = cpuRgn.base.add 8
  d26 : ∀ feat, Dec feat code 26 (FV7z.mk .test 32 [gr 32 2, .imm 32 1048576] 6)
  d32 : ∀ feat, Dec feat code 32 (FV7z.mk (.jcc 4) 64 [.rel 16] 2)
  d34 : Lea code e 34 0 vSse42
  d41 : ∃ d, (∀ feat, Dec feat code 41 (FV7z.mk .test 8 [.mem (mrip d 8), .imm 8 128] 7)) ∧
    e.add (41 + 7) + BitVec.ofNat 64 d = cpuRgn.base.add 100
  d48 : ∀ feat, Dec feat code 48 (FV7z.mk (.jcc 4) 64 [.rel 21] 2)
  d50 : ∀ feat, Dec feat code 50 (FV7z.mk .and 8 [gh 2, .imm 8 2] 3)
  d53 : Lea code e 53 0 vSse2
  d60 : Lea code e 60 2 vSsse3
  d67 : ∀ feat, Dec feat code 67 (FV7z.mk (.cmovcc 5) 64 [gr 64 0, gr 64 2] 4)
  d71 : ∀ feat, Dec feat code 71 (FV7z.mk .ret 64 [] 1)

/-- The variants. -/
abbrev variants (vAvx vSse42 vSse2 vSsse3 : Addr) : Variants :=
  [(vSse2, []), (vSsse3, [Features.ssse3]), (vSse42, [Features.sse42, Features.ssse3]), (vAvx, [Features.avx])]

variable {prof : Profile} {code : List Byte} {e vAvx vSse42 vSse2 vSsse3 : Addr} {L : List (Addr × List Byte)}
  {s₀ : State} {ra : Addr} {o : Oracle}

/-- From `50`, `rdx` the word `cpuid[1].ecx`: `vSsse3` with SSSE3, else `vSse2`. -/
theorem at50 (sh : Shape code e vAvx vSse42 vSse2 vSsse3)
    (c : Call prof RR (PP prof) (QQ prof (variants vAvx vSse42 vSse2 vSsse3)) code e L s₀ ra o) (hc : prof.Consistent)
    {X : State} {t : Nat} (hK : Kept s₀ X) (hC : Callee s₀ X) (hrip : X.cpu.rip = e.add 50)
    (hdx : X.cpu.gpr.rdx = (ecx1 s₀).setWidth 64) :
    Go prof RR (PP prof) (QQ prof (variants vAvx vSse42 vSse2 vSsse3)) L s₀ ra o X t := by
  have hok : CpuOk prof s₀.proc.mm.mem := c.call.pre
  have hk : ∀ k, k < 72 → k < code.length := fun k h => sh.len ▸ h
  obtain ⟨d53, hd53, ha53⟩ := sh.d53
  obtain ⟨d60, hd60, ha60⟩ := sh.d60
  obtain ⟨c1, c2, c3, c4, c5, c6, c7⟩ := hC
  refine c.s_and_h8i hK (hk 50 (by decide)) hrip (sh.d50 _) fun Y4 _ hK4 hr4 ⟨g4, z4⟩ => ?_
  refine c.s_lea_rip hK4 (hk 53 (by decide)) hr4 (hd53 _) ha53 fun Y5 _ hK5 hr5 ⟨g5, z5⟩ => ?_
  refine c.s_lea_rip hK5 (hk 60 (by decide)) hr5 (hd60 _) ha60 fun Y6 _ hK6 hr6 ⟨g6, z6⟩ => ?_
  refine c.s_cmov hK6 (hk 67 (by decide)) hr6 (sh.d67 _) fun Y7 _ hK7 hr7 g7 => ?_
  have hdx3 : X.cpu.gpr.get (regOf 2) = (ecx1 s₀).setWidth 64 := by simp [hdx]
  rw [cond5, z6, z5, z4, hdx3] at g7
  refine c.ret hK7 (calleeOf ?_) (hk 71 (by decide)) hr7 (sh.d71 _) ?_
  · rw [g7]
    split <;> simp [g6, g5, g4, c1, c2, c3, c4, c5, c6, c7]
  · show Returns prof _ Y7.cpu.gpr.rax
    rw [g7]
    split
    · next hz =>
      have hz' : (((ecx1 s₀).setWidth 64 >>> 8).setWidth 8 &&& BitVec.ofNat 8 2 == 0) = false := by simpa using hz
      have hb := getLsbD_of_and_pow (i := 1) _ hz'
      simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight] at hb
      have h3 : prof.feat.ssse3 = true := by
        refine (feat_of_ecx1 hc hok).1 ?_
        rw [← ecx1_bit s₀ (i := 9) (by omega)]; simpa using hb
      exact ⟨(vSsse3, [Features.ssse3]), by simp, by simp [g6], by simp [h3]⟩
    · exact ⟨(vSse2, []), by simp, by simp [g6, g5], by simp⟩

/-- The run of a call, from its first instruction. -/
theorem run (sh : Shape code e vAvx vSse42 vSse2 vSsse3)
    (c : Call prof RR (PP prof) (QQ prof (variants vAvx vSse42 vSse2 vSsse3)) code e L s₀ ra o)
    (hc : prof.Consistent) (hch : Chain prof) {t : Nat} :
    Go prof RR (PP prof) (QQ prof (variants vAvx vSse42 vSse2 vSsse3)) L s₀ ra o s₀ t := by
  have hok : CpuOk prof s₀.proc.mm.mem := c.call.pre
  have hk : ∀ k, k < 72 → k < code.length := fun k h => sh.len ▸ h
  obtain ⟨d4, hd4, ha4⟩ := sh.d4
  obtain ⟨d11, hd11, ha11⟩ := sh.d11
  obtain ⟨d20, hd20, ha20⟩ := sh.d20
  obtain ⟨d34, hd34, ha34⟩ := sh.d34
  obtain ⟨d41, hd41, ha41⟩ := sh.d41
  have hrip : s₀.cpu.rip = e.add 0 := by rw [c.call.shape.1]; simp [Addr.add]
  refine c.s_endbr (Kept.refl s₀) (hk 0 (by decide)) hrip (sh.d0 _) fun Y1 _ hK1 hr1 g1 => ?_
  refine c.s_lea_rip hK1 (hk 4 (by decide)) hr1 (hd4 _) ha4 fun Y2 _ hK2 hr2 ⟨g2, _⟩ => ?_
  refine c.s_test_m8i_rip hK2 (hk 11 (by decide)) hr2 (hd11 _) hr0 ha11 (by decide)
    fun Y3 _ hK3 hr3 ⟨g3, z3⟩ => ?_
  refine c.s_jcc hK3 (hk 18 (by decide)) hr3 (sh.d18 _) (tgt := 71) (by decide) (hk 71 (by decide))
    (fun hcc => ?_) (fun _ => ?_)
  · -- `AVX_Usable`: `vAvx`
    intro Y4 _ hK4 hr4 g4
    have hb : bit s₀.proc.mm.mem 96 0 = true := by
      have hz : (ofBytesLE 8 (readBytes s₀.proc.mm.mem (cpuRgn.base.add 96) 1) &&& BitVec.ofNat 8 1 == 0) = false := by
        rw [← z3]; simpa [cond5] using hcc
      have := getLsbD_of_and_pow (i := 0) _ hz
      rwa [getLsbD_word _ (by omega) (by omega)] at this
    refine c.ret hK4 (calleeOf (by simp [g4, g3, g2, g1])) (hk 71 (by decide)) hr4 (sh.d71 _) ?_
    exact ⟨(vAvx, [Features.avx]), by simp, by simp [g4, g3, g2], by simp [feat_avx hc hok hb]⟩
  · intro Y4 _ hK4 hr4 g4
    refine c.s_mov32_rip hK4 (hk 20 (by decide)) hr4 (hd20 _) hr0 ha20 (by decide) fun Y5 _ hK5 hr5 g5 => ?_
    have hdx : Y5.cpu.gpr.rdx = (ecx1 s₀).setWidth 64 := by simp [g5]
    refine c.s_test_ri32 hK5 (hk 26 (by decide)) hr5 (sh.d26 _) fun Y6 _ hK6 hr6 ⟨g6, z6⟩ => ?_
    refine c.s_jcc hK6 (hk 32 (by decide)) hr6 (sh.d32 _) (tgt := 50) (by decide) (hk 50 (by decide))
      (fun _ => ?_) (fun hcc => ?_)
    · intro Y7 _ hK7 hr7 g7
      exact at50 sh c hc hK7 (calleeOf (by simp [g7, g6, g5, g4, g3, g2, g1])) hr7 (by rw [g7, g6, hdx])
    · -- SSE4_2
      intro Y7 _ hK7 hr7 g7
      have h42 : prof.feat.sse42 = true := by
        have hz : (rv Y5 32 2 &&& BitVec.ofNat 32 1048576 == 0) = false := by
          rw [← z6]; simpa [cond4] using hcc
        have hb := getLsbD_of_and_pow (i := 20) _ hz
        simp only [rv, hdx, get_regOf_2, BitVec.getLsbD_setWidth] at hb
        refine (feat_of_ecx1 hc hok).2.2.1 ?_
        rw [← ecx1_bit s₀ (i := 20) (by omega)]; simpa using hb
      refine c.s_lea_rip hK7 (hk 34 (by decide)) hr7 (hd34 _) ha34 fun Y8 _ hK8 hr8 ⟨g8, _⟩ => ?_
      refine c.s_test_m8i_rip hK8 (hk 41 (by decide)) hr8 (hd41 _) hr0 ha41 (by decide)
        fun Y9 _ hK9 hr9 ⟨g9, _⟩ => ?_
      refine c.s_jcc hK9 (hk 48 (by decide)) hr9 (sh.d48 _) (tgt := 71) (by decide) (hk 71 (by decide))
        (fun _ => ?_) (fun _ => ?_)
      · intro Y10 _ hK10 hr10 g10
        refine c.ret hK10 (calleeOf (by simp [g10, g9, g8, g7, g6, g5, g4, g3, g2, g1])) (hk 71 (by decide)) hr10
          (sh.d71 _) ?_
        exact ⟨(vSse42, [Features.sse42, Features.ssse3]), by simp, by simp [g10, g9, g8],
          by simp [h42, hch.ssse3 h42]⟩
      · intro Y10 _ hK10 hr10 g10
        exact at50 sh c hc hK10 (calleeOf (by simp [g10, g9, g8, g7, g6, g5, g4, g3, g2, g1])) hr10
          (by simp [g10, g9, g8, g7, g6, hdx])

/-- Such a resolver, run at `e`: on a consistent profile with H-CPU-chain, with `_dl_x86_cpu_features` as
`init_cpu_features` leaves it, it returns `vSse2`, or `vSsse3` on a processor with SSSE3, `vSse42` with SSE4.2 and
SSSE3, `vAvx` with AVX. -/
theorem holds (sh : Shape code e vAvx vSse42 vSse2 vSsse3) (L : List (Addr × List Byte)) (prof : Profile)
    (hc : prof.Consistent) (hch : Chain prof) (hin : CodeIn L e code) :
    ImplementsCall prof e L (resolverK prof (variants vAvx vSse42 vSse2 vSsse3)) := by
  intro s₀ ra hcall
  exact reachOrEndsIn_of_runsFrom fun o ho t => run sh ⟨hcall, hin, ho⟩ hc hch

end FV7z.Glibc.StrCaseCmp
