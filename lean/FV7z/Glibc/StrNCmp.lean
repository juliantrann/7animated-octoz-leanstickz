import FV7z.Glibc.Avx2Pick
/-!
# The IFUNC resolver of `strncmp` in `7zzs`: `avx2`, `sse42`, `ssse3`, `sse2` (PLAN.md G2, "Dispatch theo CPUID")

glibc 2.31's `sysdeps/x86_64/multiarch/strncmp.c` resolver, 95 bytes of `7zzs`:

```
 0  endbr64                                 55  je 73
 4  movabs rdx, 0x90000000002               57  lea rax, vSse42
14  and rdx, feature[0..1]                  64  test byte feature[1], 0x80  (Slow_SSE4_2)
21  movabs rcx, 0x10000000002               71  je 94
31  lea rax, vAvx2                          73  and dh, 2                   (SSSE3)
38  cmp rdx, rcx  (AVX2_Usable, ...)        76  lea rax, vSse2
41  je 94                                   83  lea rdx, vSsse3
43  mov edx, cpuid[1].ecx                   90  cmovne rax, rdx
49  test edx, 0x100000  (SSE4_2)            94  ret
```

`holds`: with `_dl_x86_cpu_features` as `init_cpu_features` leaves it (`CpuOk`), on a consistent profile with
H-CPU-chain, it returns `vSse2`, or `vSsse3` on a processor with SSSE3, `vSse42` with SSE4.2 (so SSSE3), `vAvx2` with
AVX and AVX2.
-/
namespace FV7z.Glibc.StrNCmp
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf
open Avx2Pick (RR PP QQ hr0 avx2_of_eq)

/-- What the bytes `code` at `e` decode to, and where their operands point. -/
structure Shape (code : List Byte) (e vAvx2 vSse42 vSse2 vSsse3 : Addr) : Prop where
  len : code.length = 95
  d0 : ∀ feat, Dec feat code 0 (FV7z.mk .endbr64 32 [] 4)
  d4 : ∀ feat, Dec feat code 4 (FV7z.mk .mov 64 [gr 64 2, .imm 64 9895604649986] 10)
  d14 : ∃ d, (∀ feat, Dec feat code 14 (FV7z.mk .and 64 [gr 64 2, .mem (mrip d 64)] 7)) ∧
    e.add (14 + 7) + BitVec.ofNat 64 d = cpuRgn.base.add 96
  d21 : ∀ feat, Dec feat code 21 (FV7z.mk .mov 64 [gr 64 1, .imm 64 1099511627778] 10)
  d31 : Lea code e 31 0 vAvx2
  d38 : ∀ feat, Dec feat code 38 (FV7z.mk .cmp 64 [gr 64 2, gr 64 1] 3)
  d41 : ∀ feat, Dec feat code 41 (FV7z.mk (.jcc 4) 64 [.rel 51] 2)
  d43 : ∃ d, (∀ feat, Dec feat code 43 (FV7z.mk .mov 32 [gr 32 2, .mem (mrip d 32)] 6)) ∧
    e.add (43 + 6) + BitVec.ofNat 64 d = cpuRgn.base.add 8
  d49 : ∀ feat, Dec feat code 49 (FV7z.mk .test 32 [gr 32 2, .imm 32 1048576] 6)
  d55 : ∀ feat, Dec feat code 55 (FV7z.mk (.jcc 4) 64 [.rel 16] 2)
  d57 : Lea code e 57 0 vSse42
  d64 : ∃ d, (∀ feat, Dec feat code 64 (FV7z.mk .test 8 [.mem (mrip d 8), .imm 8 128] 7)) ∧
    e.add (64 + 7) + BitVec.ofNat 64 d = cpuRgn.base.add 100
  d71 : ∀ feat, Dec feat code 71 (FV7z.mk (.jcc 4) 64 [.rel 21] 2)
  d73 : ∀ feat, Dec feat code 73 (FV7z.mk .and 8 [gh 2, .imm 8 2] 3)
  d76 : Lea code e 76 0 vSse2
  d83 : Lea code e 83 2 vSsse3
  d90 : ∀ feat, Dec feat code 90 (FV7z.mk (.cmovcc 5) 64 [gr 64 0, gr 64 2] 4)
  d94 : ∀ feat, Dec feat code 94 (FV7z.mk .ret 64 [] 1)

/-- The variants. -/
abbrev variants (vAvx2 vSse42 vSse2 vSsse3 : Addr) : Variants :=
  [(vSse2, []), (vSsse3, [Features.ssse3]), (vSse42, [Features.sse42, Features.ssse3]),
    (vAvx2, [Features.avx, Features.avx2])]

variable {prof : Profile} {code : List Byte} {e vAvx2 vSse42 vSse2 vSsse3 : Addr} {L : List (Addr × List Byte)}
  {s₀ : State} {ra : Addr} {o : Oracle}

/-- From `73`, `rdx` the word `cpuid[1].ecx`: `vSsse3` with SSSE3, else `vSse2`. -/
theorem at73 (sh : Shape code e vAvx2 vSse42 vSse2 vSsse3)
    (c : Call prof RR (PP prof) (QQ prof (variants vAvx2 vSse42 vSse2 vSsse3)) code e L s₀ ra o) (hc : prof.Consistent)
    {X : State} {t : Nat} (hK : Kept s₀ X) (hC : Callee s₀ X) (hrip : X.cpu.rip = e.add 73)
    (hdx : X.cpu.gpr.rdx = (ecx1 s₀).setWidth 64) :
    Go prof RR (PP prof) (QQ prof (variants vAvx2 vSse42 vSse2 vSsse3)) L s₀ ra o X t := by
  have hok : CpuOk prof s₀.proc.mm.mem := c.call.pre
  have hk : ∀ k, k < 95 → k < code.length := fun k h => sh.len ▸ h
  obtain ⟨d76, hd76, ha76⟩ := sh.d76
  obtain ⟨d83, hd83, ha83⟩ := sh.d83
  obtain ⟨c1, c2, c3, c4, c5, c6, c7⟩ := hC
  refine c.s_and_h8i hK (hk 73 (by decide)) hrip (sh.d73 _) fun Y4 _ hK4 hr4 ⟨g4, z4⟩ => ?_
  refine c.s_lea_rip hK4 (hk 76 (by decide)) hr4 (hd76 _) ha76 fun Y5 _ hK5 hr5 ⟨g5, z5⟩ => ?_
  refine c.s_lea_rip hK5 (hk 83 (by decide)) hr5 (hd83 _) ha83 fun Y6 _ hK6 hr6 ⟨g6, z6⟩ => ?_
  refine c.s_cmov hK6 (hk 90 (by decide)) hr6 (sh.d90 _) fun Y7 _ hK7 hr7 g7 => ?_
  have hdx3 : X.cpu.gpr.get (regOf 2) = (ecx1 s₀).setWidth 64 := by simp [hdx]
  rw [cond5, z6, z5, z4, hdx3] at g7
  refine c.ret hK7 (calleeOf ?_) (hk 94 (by decide)) hr7 (sh.d94 _) ?_
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
theorem run (sh : Shape code e vAvx2 vSse42 vSse2 vSsse3)
    (c : Call prof RR (PP prof) (QQ prof (variants vAvx2 vSse42 vSse2 vSsse3)) code e L s₀ ra o)
    (hc : prof.Consistent) (hch : Chain prof) {t : Nat} :
    Go prof RR (PP prof) (QQ prof (variants vAvx2 vSse42 vSse2 vSsse3)) L s₀ ra o s₀ t := by
  have hok : CpuOk prof s₀.proc.mm.mem := c.call.pre
  have hk : ∀ k, k < 95 → k < code.length := fun k h => sh.len ▸ h
  obtain ⟨da, hda, haa⟩ := sh.d14
  obtain ⟨d31, hd31, ha31⟩ := sh.d31
  obtain ⟨d43, hd43, ha43⟩ := sh.d43
  obtain ⟨d57, hd57, ha57⟩ := sh.d57
  obtain ⟨d64, hd64, ha64⟩ := sh.d64
  have hrip : s₀.cpu.rip = e.add 0 := by rw [c.call.shape.1]; simp [Addr.add]
  refine c.s_endbr (Kept.refl s₀) (hk 0 (by decide)) hrip (sh.d0 _) fun Y1 _ hK1 hr1 g1 => ?_
  refine c.s_mov_ri64 hK1 (hk 4 (by decide)) hr1 (sh.d4 _) fun Y2 _ hK2 hr2 g2 => ?_
  refine c.s_and64_rip hK2 (hk 14 (by decide)) hr2 (hda _) hr0 haa (by decide) fun Y3 _ hK3 hr3 ⟨g3, _⟩ => ?_
  refine c.s_mov_ri64 hK3 (hk 21 (by decide)) hr3 (sh.d21 _) fun Y4 _ hK4 hr4 g4 => ?_
  refine c.s_lea_rip hK4 (hk 31 (by decide)) hr4 (hd31 _) ha31 fun Y5 _ hK5 hr5 ⟨g5, _⟩ => ?_
  refine c.s_cmp_rr hK5 (hk 38 (by decide)) hr5 (sh.d38 _) fun Y6 _ hK6 hr6 ⟨g6, f6⟩ => ?_
  have hC6 : Callee s₀ Y6 := calleeOf (by simp [g6, g5, g4, g3, g2, g1])
  refine c.s_jcc hK6 (hk 41 (by decide)) hr6 (sh.d41 _) (tgt := 94) (by decide) (hk 94 (by decide))
    (fun hcc => ?_) (fun _ => ?_)
  · -- `AVX2_Usable` (and not `Prefer_No_VZEROUPPER`, …): `vAvx2`
    intro Y7 _ hK7 hr7 g7
    have hW : bit s₀.proc.mm.mem 96 1 = true := by
      rw [cond4, f6, subF_zf, decide_eq_true_iff] at hcc
      simp only [rv, g5, g4, g3, g2, g1, get_regOf_1, get_regOf_2, set_rax, set_rcx, set_rdx,
        BitVec.setWidth_eq] at hcc
      rw [← getLsbD_word (a := 96) (w := 64) (n := 8) (i := 1) _ (by omega) (by omega)]
      exact avx2_of_eq _ hcc
    have h2 := feat_avx2 hc hok hW
    refine c.ret hK7 (calleeOf ?_) (hk 94 (by decide)) hr7 (sh.d94 _) ?_
    · rw [g7]; exact hC6
    · show Returns prof _ Y7.cpu.gpr.rax
      exact ⟨(vAvx2, [Features.avx, Features.avx2]), by simp, by simp [g7, g6, g5], by simp [h2.1, h2.2]⟩
  · intro Y7 _ hK7 hr7 g7
    obtain ⟨c1, c2, c3, c4, c5, c6, c7⟩ := hC6
    refine c.s_mov32_rip hK7 (hk 43 (by decide)) hr7 (hd43 _) hr0 ha43 (by decide) fun Y8 _ hK8 hr8 g8 => ?_
    have hdx : Y8.cpu.gpr.rdx = (ecx1 s₀).setWidth 64 := by simp [g8]
    refine c.s_test_ri32 hK8 (hk 49 (by decide)) hr8 (sh.d49 _) fun Y9 _ hK9 hr9 ⟨g9, z9⟩ => ?_
    refine c.s_jcc hK9 (hk 55 (by decide)) hr9 (sh.d55 _) (tgt := 73) (by decide) (hk 73 (by decide))
      (fun _ => ?_) (fun hcc => ?_)
    · intro Y10 _ hK10 hr10 g10
      exact at73 sh c hc hK10 (calleeOf (by simp [g10, g9, g8, g7, c1, c2, c3, c4, c5, c6, c7])) hr10
        (by rw [g10, g9, hdx])
    · -- SSE4_2
      intro Y10 _ hK10 hr10 g10
      have h42 : prof.feat.sse42 = true := by
        have hz : (rv Y8 32 2 &&& BitVec.ofNat 32 1048576 == 0) = false := by
          rw [← z9]; simpa [cond4] using hcc
        have hb := getLsbD_of_and_pow (i := 20) _ hz
        simp only [rv, hdx, get_regOf_2, BitVec.getLsbD_setWidth] at hb
        refine (feat_of_ecx1 hc hok).2.2.1 ?_
        rw [← ecx1_bit s₀ (i := 20) (by omega)]; simpa using hb
      refine c.s_lea_rip hK10 (hk 57 (by decide)) hr10 (hd57 _) ha57 fun Y11 _ hK11 hr11 ⟨g11, _⟩ => ?_
      refine c.s_test_m8i_rip hK11 (hk 64 (by decide)) hr11 (hd64 _) hr0 ha64 (by decide)
        fun Y12 _ hK12 hr12 ⟨g12, _⟩ => ?_
      refine c.s_jcc hK12 (hk 71 (by decide)) hr12 (sh.d71 _) (tgt := 94) (by decide) (hk 94 (by decide))
        (fun _ => ?_) (fun _ => ?_)
      · intro Y13 _ hK13 hr13 g13
        refine c.ret hK13 (calleeOf (by simp [g13, g12, g11, g10, g9, g8, g7, c1, c2, c3, c4, c5, c6, c7]))
          (hk 94 (by decide)) hr13 (sh.d94 _) ?_
        exact ⟨(vSse42, [Features.sse42, Features.ssse3]), by simp, by simp [g13, g12, g11],
          by simp [h42, hch.ssse3 h42]⟩
      · intro Y13 _ hK13 hr13 g13
        exact at73 sh c hc hK13
          (calleeOf (by simp [g13, g12, g11, g10, g9, g8, g7, c1, c2, c3, c4, c5, c6, c7])) hr13
          (by simp [g13, g12, g11, g10, g9, hdx])

/-- The resolver, run at `e`: on a consistent profile with H-CPU-chain, with `_dl_x86_cpu_features` as
`init_cpu_features` leaves it, it returns `vSse2`, or `vSsse3` on a processor with SSSE3, `vSse42` with SSE4.2 and
SSSE3, `vAvx2` with AVX and AVX2. -/
theorem holds (sh : Shape code e vAvx2 vSse42 vSse2 vSsse3) (L : List (Addr × List Byte)) (prof : Profile)
    (hc : prof.Consistent) (hch : Chain prof) (hin : CodeIn L e code) :
    ImplementsCall prof e L (resolverK prof (variants vAvx2 vSse42 vSse2 vSsse3)) := by
  intro s₀ ra hcall
  exact reachOrEndsIn_of_runsFrom fun o ho t => run sh ⟨hcall, hin, ho⟩ hc hch

end FV7z.Glibc.StrNCmp
