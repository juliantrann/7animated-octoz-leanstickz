import FV7z.Glibc.Pair
/-!
# The IFUNC resolvers of `memmove`, `memcpy`, `mempcpy` in `7zzs` (PLAN.md G2, "Dispatch theo CPUID")

Three resolvers of `7zzs` (glibc 2.31's `sysdeps/x86_64/multiarch/ifunc-memmove.h`) are the same 186 bytes but for
their `rip`-relative displacements:

```
  0  endbr64                                    80  test byte cpuid[1].ecx+1, 2   (SSSE3)
  4  mov edx, feature[1]                        87  je 160
 10  lea rax, erms                              89  test dl, 0x20                 (Fast_Unaligned_Copy)
 17  test dh, 0x30  (Prefer_ERMS, Prefer_FSRM)  92  jne 160
 20  jne 115                                    94  and edx, 8                    (Fast_Copy_Backward)
 22  movabs rax, 0x400000000004                 97  lea rax, ssse3 ; lea rdx, ssse3_back ; cmovne ; ret
 32  and rax, feature[0..1]
 39  cmp rax, 4   (AVX512F_Usable, not Prefer_No_AVX512)
 43  je 120                                    120  lea rax, avx512_no_vzeroupper
 45  test dh, 1   (AVX_Fast_Unaligned_Load)    127  and dh, 8                     (Prefer_No_VZEROUPPER)
 48  je 80                                     130  jne 115
 50  test byte cpuid[7].ebx+1, 2  (ERMS)       132  test byte cpuid[7].ebx+1, 2   (ERMS)
 57  lea rdx, avx ; lea rax, avx_erms ;        139  lea rdx, avx512 ; lea rax, avx512_erms ; cmove ; ret
     cmove ; ret                               160  test byte cpuid[7].ebx+1, 2   (ERMS)
                                               167  lea rdx, sse2 ; lea rax, sse2_erms ; cmove ; ret
```

`holds`: with `_dl_x86_cpu_features` as `init_cpu_features` leaves it (`CpuOk`), on a consistent profile with
H-CPU-chain, it returns an `erms` or `sse2` variant, an `ssse3` one on a processor with SSSE3 (so SSE3), an `avx`
one with AVX and AVX2 (`AVX_Fast_Unaligned_Load` is set only with `AVX2_Usable`), an `avx512` one with AVX-512F (so
AVX2 and AVX).
-/
namespace FV7z.Glibc.Memmove
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf
open Avx2Pick (RR PP QQ hr0)

/-- The variants' addresses. -/
structure Addrs where
  erms : Addr
  avxA : Addr
  avxB : Addr
  ssse3A : Addr
  ssse3B : Addr
  noVzu : Addr
  avx512A : Addr
  avx512B : Addr
  sse2A : Addr
  sse2B : Addr

/-- What the bytes `code` at `e` decode to, and where their operands point. -/
structure Shape (code : List Byte) (e : Addr) (v : Addrs) : Prop where
  len : code.length = 186
  d0 : ∀ feat, Dec feat code 0 (FV7z.mk .endbr64 32 [] 4)
  d4 : ∃ d, (∀ feat, Dec feat code 4 (FV7z.mk .mov 32 [gr 32 2, .mem (mrip d 32)] 6)) ∧
    e.add (4 + 6) + BitVec.ofNat 64 d = cpuRgn.base.add 100
  d10 : Lea code e 10 0 v.erms
  d17 : ∀ feat, Dec feat code 17 (FV7z.mk .test 8 [gh 2, .imm 8 48] 3)
  d20 : ∀ feat, Dec feat code 20 (FV7z.mk (.jcc 5) 64 [.rel 93] 2)
  d22 : ∀ feat, Dec feat code 22 (FV7z.mk .mov 64 [gr 64 0, .imm 64 70368744177668] 10)
  d32 : ∃ d, (∀ feat, Dec feat code 32 (FV7z.mk .and 64 [gr 64 0, .mem (mrip d 64)] 7)) ∧
    e.add (32 + 7) + BitVec.ofNat 64 d = cpuRgn.base.add 96
  d39 : ∀ feat, Dec feat code 39 (FV7z.mk .cmp 64 [gr 64 0, .imm 64 4] 4)
  d43 : ∀ feat, Dec feat code 43 (FV7z.mk (.jcc 4) 64 [.rel 75] 2)
  d45 : ∀ feat, Dec feat code 45 (FV7z.mk .test 8 [gh 2, .imm 8 1] 3)
  d48 : ∀ feat, Dec feat code 48 (FV7z.mk (.jcc 4) 64 [.rel 30] 2)
  d50 : ∃ d, (∀ feat, Dec feat code 50 (FV7z.mk .test 8 [.mem (mrip d 8), .imm 8 2] 7)) ∧
    e.add (50 + 7) + BitVec.ofNat 64 d = cpuRgn.base.add 21
  d57 : Lea code e 57 2 v.avxA
  d64 : Lea code e 64 0 v.avxB
  d71 : ∀ feat, Dec feat code 71 (FV7z.mk (.cmovcc 4) 64 [gr 64 0, gr 64 2] 4)
  d75 : ∀ feat, Dec feat code 75 (FV7z.mk .ret 64 [] 1)
  d80 : ∃ d, (∀ feat, Dec feat code 80 (FV7z.mk .test 8 [.mem (mrip d 8), .imm 8 2] 7)) ∧
    e.add (80 + 7) + BitVec.ofNat 64 d = cpuRgn.base.add 9
  d87 : ∀ feat, Dec feat code 87 (FV7z.mk (.jcc 4) 64 [.rel 71] 2)
  d89 : ∀ feat, Dec feat code 89 (FV7z.mk .test 8 [gr 8 2, .imm 8 32] 3)
  d92 : ∀ feat, Dec feat code 92 (FV7z.mk (.jcc 5) 64 [.rel 66] 2)
  d94 : ∀ feat, Dec feat code 94 (FV7z.mk .and 32 [gr 32 2, .imm 32 8] 3)
  d97 : Lea code e 97 0 v.ssse3A
  d104 : Lea code e 104 2 v.ssse3B
  d111 : ∀ feat, Dec feat code 111 (FV7z.mk (.cmovcc 5) 64 [gr 64 0, gr 64 2] 4)
  d115 : ∀ feat, Dec feat code 115 (FV7z.mk .ret 64 [] 1)
  d120 : Lea code e 120 0 v.noVzu
  d127 : ∀ feat, Dec feat code 127 (FV7z.mk .and 8 [gh 2, .imm 8 8] 3)
  d130 : ∀ feat, Dec feat code 130 (FV7z.mk (.jcc 5) 64 [.rel 18446744073709551599] 2)
  d132 : ∃ d, (∀ feat, Dec feat code 132 (FV7z.mk .test 8 [.mem (mrip d 8), .imm 8 2] 7)) ∧
    e.add (132 + 7) + BitVec.ofNat 64 d = cpuRgn.base.add 21
  d139 : Lea code e 139 2 v.avx512A
  d146 : Lea code e 146 0 v.avx512B
  d153 : ∀ feat, Dec feat code 153 (FV7z.mk (.cmovcc 4) 64 [gr 64 0, gr 64 2] 4)
  d157 : ∀ feat, Dec feat code 157 (FV7z.mk .ret 64 [] 1)
  d160 : ∃ d, (∀ feat, Dec feat code 160 (FV7z.mk .test 8 [.mem (mrip d 8), .imm 8 2] 7)) ∧
    e.add (160 + 7) + BitVec.ofNat 64 d = cpuRgn.base.add 21
  d167 : Lea code e 167 2 v.sse2A
  d174 : Lea code e 174 0 v.sse2B
  d181 : ∀ feat, Dec feat code 181 (FV7z.mk (.cmovcc 4) 64 [gr 64 0, gr 64 2] 4)
  d185 : ∀ feat, Dec feat code 185 (FV7z.mk .ret 64 [] 1)

abbrev S3 : List (Features → Bool) := [Features.ssse3, Features.sse3]
abbrev AV : List (Features → Bool) := [Features.avx, Features.avx2]
abbrev A5 : List (Features → Bool) := [Features.avx, Features.avx2, Features.avx512f]

/-- The variants. -/
abbrev variants (v : Addrs) : Variants :=
  [(v.erms, []), (v.sse2A, []), (v.sse2B, []), (v.ssse3A, S3), (v.ssse3B, S3), (v.avxA, AV), (v.avxB, AV),
    (v.noVzu, A5), (v.avx512A, A5), (v.avx512B, A5)]

/-- `feature[1]` at the call. -/
abbrev f1 (s₀ : State) : BitVec 32 := ofBytesLE 32 (readBytes s₀.proc.mm.mem (cpuRgn.base.add 100) 4)

variable {prof : Profile} {code : List Byte} {e : Addr} {v : Addrs} {L : List (Addr × List Byte)} {s₀ : State}
  {ra : Addr} {o : Oracle}

theorem at160 (sh : Shape code e v) (c : Call prof RR (PP prof) (QQ prof (variants v)) code e L s₀ ra o)
    {X : State} {t : Nat} (hK : Kept s₀ X) (hC : Callee s₀ X) (hrip : X.cpu.rip = e.add 160) :
    Go prof RR (PP prof) (QQ prof (variants v)) L s₀ ra o X t := by
  have hk : ∀ k, k < 186 → k < code.length := fun k h => sh.len ▸ h
  obtain ⟨d160, hd160, ha160⟩ := sh.d160
  obtain ⟨c1, c2, c3, c4, c5, c6, c7⟩ := hC
  refine c.s_test_m8i_rip hK (hk 160 (by decide)) hrip (hd160 _) hr0 ha160 (by decide)
    fun Y1 _ hK1 hr1 ⟨g1, _⟩ => ?_
  exact Pair.go c hK1 (calleeOf (by simp [g1, c1, c2, c3, c4, c5, c6, c7])) hr1 (hk _ (by decide))
    (Or.inl ⟨rfl, rfl⟩) sh.d167 sh.d174 sh.d181 sh.d185
    (Returns.of_mem (fs := []) (by simp) (by simp)) (Returns.of_mem (fs := []) (by simp) (by simp))

theorem at120 (sh : Shape code e v) (c : Call prof RR (PP prof) (QQ prof (variants v)) code e L s₀ ra o)
    (h5 : prof.feat.avx = true ∧ prof.feat.avx2 = true ∧ prof.feat.avx512f = true)
    {X : State} {t : Nat} (hK : Kept s₀ X) (hC : Callee s₀ X) (hrip : X.cpu.rip = e.add 120) :
    Go prof RR (PP prof) (QQ prof (variants v)) L s₀ ra o X t := by
  have hk : ∀ k, k < 186 → k < code.length := fun k h => sh.len ▸ h
  have p5 : ∀ f ∈ A5, f prof.feat = true := by simp [h5.1, h5.2.1, h5.2.2]
  obtain ⟨d120, hd120, ha120⟩ := sh.d120
  obtain ⟨d132, hd132, ha132⟩ := sh.d132
  obtain ⟨c1, c2, c3, c4, c5, c6, c7⟩ := hC
  refine c.s_lea_rip hK (hk 120 (by decide)) hrip (hd120 _) ha120 fun Y1 _ hK1 hr1 ⟨g1, _⟩ => ?_
  refine c.s_and_h8i hK1 (hk 127 (by decide)) hr1 (sh.d127 _) fun Y2 _ hK2 hr2 ⟨g2, _⟩ => ?_
  refine c.s_jcc hK2 (hk 130 (by decide)) hr2 (sh.d130 _) (tgt := 115) (by decide) (hk 115 (by decide))
    (fun _ => ?_) (fun _ => ?_)
  · intro Y3 _ hK3 hr3 g3
    refine c.ret hK3 (calleeOf (by simp [g3, g2, g1, c1, c2, c3, c4, c5, c6, c7])) (hk 115 (by decide)) hr3
      (sh.d115 _) ?_
    show Returns prof _ Y3.cpu.gpr.rax
    rw [show Y3.cpu.gpr.rax = v.noVzu by simp [g3, g2, g1]]
    exact Returns.of_mem (by simp) p5
  · intro Y3 _ hK3 hr3 g3
    refine c.s_test_m8i_rip hK3 (hk 132 (by decide)) hr3 (hd132 _) hr0 ha132 (by decide)
      fun Y4 _ hK4 hr4 ⟨g4, _⟩ => ?_
    exact Pair.go c hK4 (calleeOf (by simp [g4, g3, g2, g1, c1, c2, c3, c4, c5, c6, c7])) hr4 (hk _ (by decide))
      (Or.inl ⟨rfl, rfl⟩) sh.d139 sh.d146 sh.d153 sh.d157 (Returns.of_mem (by simp) p5) (Returns.of_mem (by simp) p5)

theorem at80 (sh : Shape code e v) (c : Call prof RR (PP prof) (QQ prof (variants v)) code e L s₀ ra o)
    (hc : prof.Consistent) (hch : Chain prof)
    {X : State} {t : Nat} (hK : Kept s₀ X) (hC : Callee s₀ X) (hrip : X.cpu.rip = e.add 80) :
    Go prof RR (PP prof) (QQ prof (variants v)) L s₀ ra o X t := by
  have hok : CpuOk prof s₀.proc.mm.mem := c.call.pre
  have hk : ∀ k, k < 186 → k < code.length := fun k h => sh.len ▸ h
  obtain ⟨d80, hd80, ha80⟩ := sh.d80
  have hC' := hC
  obtain ⟨c1, c2, c3, c4, c5, c6, c7⟩ := hC
  refine c.s_test_m8i_rip hK (hk 80 (by decide)) hrip (hd80 _) hr0 ha80 (by decide)
    fun Y1 _ hK1 hr1 ⟨g1, z1⟩ => ?_
  refine c.s_jcc hK1 (hk 87 (by decide)) hr1 (sh.d87 _) (tgt := 160) (by decide) (hk 160 (by decide))
    (fun _ => ?_) (fun hcc => ?_)
  · intro Y2 _ hK2 hr2 g2
    exact at160 sh c hK2 (calleeOf (by simp [g2, g1, c1, c2, c3, c4, c5, c6, c7])) hr2
  · intro Y2 _ hK2 hr2 g2
    have h3 : prof.feat.ssse3 = true := by
      have hz : (ofBytesLE 8 (readBytes s₀.proc.mm.mem (cpuRgn.base.add 9) 1) &&& BitVec.ofNat 8 2 == 0) = false := by
        rw [← z1]; simpa [cond4] using hcc
      have hb := getLsbD_of_and_pow (i := 1) _ hz
      rw [getLsbD_word _ (by omega) (by omega)] at hb
      exact (feat_of_ecx1 hc hok).1 hb
    have p3 : ∀ f ∈ S3, f prof.feat = true := by simp [h3, hch.sse3 h3]
    refine c.s_test_r8i hK2 (hk 89 (by decide)) hr2 (sh.d89 _) fun Y3 _ hK3 hr3 ⟨g3, _⟩ => ?_
    refine c.s_jcc hK3 (hk 92 (by decide)) hr3 (sh.d92 _) (tgt := 160) (by decide) (hk 160 (by decide))
      (fun _ => ?_) (fun _ => ?_)
    · intro Y4 _ hK4 hr4 g4
      exact at160 sh c hK4 (calleeOf (by simp [g4, g3, g2, g1, c1, c2, c3, c4, c5, c6, c7])) hr4
    · intro Y4 _ hK4 hr4 g4
      refine c.s_and_ri32 hK4 (hk 94 (by decide)) hr4 (sh.d94 _) fun Y5 _ hK5 hr5 ⟨g5, _⟩ => ?_
      exact Pair.go c hK5 (calleeOf (by simp [g5, g4, g3, g2, g1, c1, c2, c3, c4, c5, c6, c7])) hr5
        (hk _ (by decide)) (Or.inr ⟨rfl, rfl⟩) sh.d97 sh.d104 sh.d111 sh.d115
        (Returns.of_mem (by simp) p3) (Returns.of_mem (by simp) p3)

/-- The run of a call, from its first instruction. -/
theorem run (sh : Shape code e v) (c : Call prof RR (PP prof) (QQ prof (variants v)) code e L s₀ ra o)
    (hc : prof.Consistent) (hch : Chain prof) {t : Nat} : Go prof RR (PP prof) (QQ prof (variants v)) L s₀ ra o s₀ t := by
  have hok : CpuOk prof s₀.proc.mm.mem := c.call.pre
  have hk : ∀ k, k < 186 → k < code.length := fun k h => sh.len ▸ h
  obtain ⟨d4, hd4, ha4⟩ := sh.d4
  obtain ⟨d10, hd10, ha10⟩ := sh.d10
  obtain ⟨d32, hd32, ha32⟩ := sh.d32
  obtain ⟨d50, hd50, ha50⟩ := sh.d50
  have hrip : s₀.cpu.rip = e.add 0 := by rw [c.call.shape.1]; simp [Addr.add]
  refine c.s_endbr (Kept.refl s₀) (hk 0 (by decide)) hrip (sh.d0 _) fun Y1 _ hK1 hr1 g1 => ?_
  refine c.s_mov32_rip hK1 (hk 4 (by decide)) hr1 (hd4 _) hr0 ha4 (by decide) fun Y2 _ hK2 hr2 g2 => ?_
  have hdx2 : Y2.cpu.gpr.rdx = (f1 s₀).setWidth 64 := by simp [g2]
  refine c.s_lea_rip hK2 (hk 10 (by decide)) hr2 (hd10 _) ha10 fun Y3 _ hK3 hr3 ⟨g3, _⟩ => ?_
  refine c.s_test_h8i hK3 (hk 17 (by decide)) hr3 (sh.d17 _) fun Y4 _ hK4 hr4 ⟨g4, _⟩ => ?_
  refine c.s_jcc hK4 (hk 20 (by decide)) hr4 (sh.d20 _) (tgt := 115) (by decide) (hk 115 (by decide))
    (fun _ => ?_) (fun _ => ?_)
  · -- `Prefer_ERMS` or `Prefer_FSRM`: `erms`
    intro Y5 _ hK5 hr5 g5
    refine c.ret hK5 (calleeOf (by simp [g5, g4, g3, g2, g1])) (hk 115 (by decide)) hr5 (sh.d115 _) ?_
    show Returns prof _ Y5.cpu.gpr.rax
    rw [show Y5.cpu.gpr.rax = v.erms by simp [g5, g4, g3]]
    exact Returns.of_mem (fs := []) (by simp) (by simp)
  · intro Y5 _ hK5 hr5 g5
    refine c.s_mov_ri64 hK5 (hk 22 (by decide)) hr5 (sh.d22 _) fun Y6 _ hK6 hr6 g6 => ?_
    refine c.s_and64_rip hK6 (hk 32 (by decide)) hr6 (hd32 _) hr0 ha32 (by decide) fun Y7 _ hK7 hr7 ⟨g7, _⟩ => ?_
    refine c.s_cmp_ri hK7 (hk 39 (by decide)) hr7 (sh.d39 _) fun Y8 _ hK8 hr8 ⟨g8, f8⟩ => ?_
    have hdx8 : Y8.cpu.gpr.rdx = (f1 s₀).setWidth 64 := by simp [g8, g7, g6, g5, g4, g3, hdx2]
    refine c.s_jcc hK8 (hk 43 (by decide)) hr8 (sh.d43 _) (tgt := 120) (by decide) (hk 120 (by decide))
      (fun hcc => ?_) (fun _ => ?_)
    · -- `AVX512F_Usable`, not `Prefer_No_AVX512`
      intro Y9 _ hK9 hr9 g9
      have hb : bit s₀.proc.mm.mem 96 2 = true := by
        rw [cond4, f8, subF_zf, decide_eq_true_iff] at hcc
        simp only [rv, g7, g6, g5, g4, g3, g2, g1, get_regOf_0, set_rax, set_rdx, BitVec.setWidth_eq] at hcc
        rw [← getLsbD_word (a := 96) (w := 64) (n := 8) (i := 2) _ (by omega) (by omega)]
        exact avx512_of_eq' _ hcc
      exact at120 sh c (feat_avx512 hc hch hok hb) hK9
        (calleeOf (by simp [g9, g8, g7, g6, g5, g4, g3, g2, g1])) hr9
    · intro Y9 _ hK9 hr9 g9
      refine c.s_test_h8i hK9 (hk 45 (by decide)) hr9 (sh.d45 _) fun Y10 _ hK10 hr10 ⟨g10, z10⟩ => ?_
      refine c.s_jcc hK10 (hk 48 (by decide)) hr10 (sh.d48 _) (tgt := 80) (by decide) (hk 80 (by decide))
        (fun _ => ?_) (fun hcc => ?_)
      · intro Y11 _ hK11 hr11 g11
        exact at80 sh c hc hch hK11 (calleeOf (by simp [g11, g10, g9, g8, g7, g6, g5, g4, g3, g2, g1])) hr11
      · -- `AVX_Fast_Unaligned_Load`, so `AVX2_Usable`
        intro Y11 _ hK11 hr11 g11
        have hb : bit s₀.proc.mm.mem 100 8 = true := by
          have hz : ((Y9.cpu.gpr.get (regOf 2) >>> 8).setWidth 8 &&& BitVec.ofNat 8 1 == 0) = false := by
            rw [← z10]; simpa [cond4] using hcc
          rw [show Y9.cpu.gpr.get (regOf 2) = (f1 s₀).setWidth 64 by simp [g9, get_regOf_2, hdx8]] at hz
          have hb := getLsbD_of_and_pow (i := 0) _ hz
          simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight] at hb
          rw [← getLsbD_word (a := 100) (w := 32) (n := 4) (i := 8) _ (by omega) (by omega)]
          simpa using hb
        have h2 := feat_avx2 hc hok (hok.fastAvx hb)
        have p2 : ∀ f ∈ AV, f prof.feat = true := by simp [h2.1, h2.2]
        refine c.s_test_m8i_rip hK11 (hk 50 (by decide)) hr11 (hd50 _) hr0 ha50 (by decide)
          fun Y12 _ hK12 hr12 ⟨g12, _⟩ => ?_
        exact Pair.go c hK12 (calleeOf (by simp [g12, g11, g10, g9, g8, g7, g6, g5, g4, g3, g2, g1])) hr12
          (hk _ (by decide)) (Or.inl ⟨rfl, rfl⟩) sh.d57 sh.d64 sh.d71 sh.d75
          (Returns.of_mem (by simp) p2) (Returns.of_mem (by simp) p2)

/-- Such a resolver, run at `e`: on a consistent profile with H-CPU-chain, with `_dl_x86_cpu_features` as
`init_cpu_features` leaves it, it returns one of its variants the processor has. -/
theorem holds (sh : Shape code e v) (L : List (Addr × List Byte)) (prof : Profile) (hc : prof.Consistent)
    (hch : Chain prof) (hin : CodeIn L e code) : ImplementsCall prof e L (resolverK prof (variants v)) := by
  intro s₀ ra hcall
  exact reachOrEndsIn_of_runsFrom fun o ho t => run sh ⟨hcall, hin, ho⟩ hc hch

end FV7z.Glibc.Memmove
