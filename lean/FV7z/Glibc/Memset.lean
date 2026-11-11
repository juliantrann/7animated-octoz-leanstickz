import FV7z.Glibc.Pair
/-!
# The IFUNC resolver of `memset` in `7zzs` (PLAN.md G2, "Dispatch theo CPUID")

glibc 2.31's `sysdeps/x86_64/multiarch/ifunc-memset.h`, 158 bytes of `7zzs`:

```
  0  endbr64                                    65  test eax, eax
  4  mov edx, feature[1]                        67  lea rdx, avx2 ; lea rax, avx2_erms ; cmove ; ret
 10  lea rax, erms                              96  test eax, eax
 17  test dh, 0x10  (Prefer_ERMS)               98  lea rdx, sse2 ; lea rax, sse2_erms ; cmovne ; ret
 20  jne 116
 22  movabs rax, 0x400000000004                120  lea rax, avx512_no_vzeroupper
 32  and rax, feature[0..1]                    127  and dh, 8                     (Prefer_No_VZEROUPPER)
 39  cmp rax, 4   (AVX512F_Usable, not         130  jne 116
              Prefer_No_AVX512)                132  test byte cpuid[7].ebx+1, 2   (ERMS)
 43  je 120                                    139  lea rdx, avx512 ; lea rax, avx512_erms ; cmove ; ret
 45  mov eax, cpuid[7].ebx
 51  and eax, 0x200  (ERMS)
 56  test byte feature[0], 2  (AVX2_Usable)
 63  je 96
```

`holds`: with `_dl_x86_cpu_features` as `init_cpu_features` leaves it (`CpuOk`), on a consistent profile with
H-CPU-chain, it returns an `erms` or `sse2` variant, an `avx2` one with AVX and AVX2, an `avx512` one with AVX-512F
(so AVX2 and AVX).
-/
namespace FV7z.Glibc.Memset
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf
open Avx2Pick (RR PP QQ hr0)

/-- The variants' addresses. -/
structure Addrs where
  erms : Addr
  avx2A : Addr
  avx2B : Addr
  sse2A : Addr
  sse2B : Addr
  noVzu : Addr
  avx512A : Addr
  avx512B : Addr

/-- What the bytes `code` at `e` decode to, and where their operands point. -/
structure Shape (code : List Byte) (e : Addr) (v : Addrs) : Prop where
  len : code.length = 158
  d0 : ∀ feat, Dec feat code 0 (FV7z.mk .endbr64 32 [] 4)
  d4 : ∃ d, (∀ feat, Dec feat code 4 (FV7z.mk .mov 32 [gr 32 2, .mem (mrip d 32)] 6)) ∧
    e.add (4 + 6) + BitVec.ofNat 64 d = cpuRgn.base.add 100
  d10 : Lea code e 10 0 v.erms
  d17 : ∀ feat, Dec feat code 17 (FV7z.mk .test 8 [gh 2, .imm 8 16] 3)
  d20 : ∀ feat, Dec feat code 20 (FV7z.mk (.jcc 5) 64 [.rel 94] 2)
  d22 : ∀ feat, Dec feat code 22 (FV7z.mk .mov 64 [gr 64 0, .imm 64 70368744177668] 10)
  d32 : ∃ d, (∀ feat, Dec feat code 32 (FV7z.mk .and 64 [gr 64 0, .mem (mrip d 64)] 7)) ∧
    e.add (32 + 7) + BitVec.ofNat 64 d = cpuRgn.base.add 96
  d39 : ∀ feat, Dec feat code 39 (FV7z.mk .cmp 64 [gr 64 0, .imm 64 4] 4)
  d43 : ∀ feat, Dec feat code 43 (FV7z.mk (.jcc 4) 64 [.rel 75] 2)
  d45 : ∃ d, (∀ feat, Dec feat code 45 (FV7z.mk .mov 32 [gr 32 0, .mem (mrip d 32)] 6)) ∧
    e.add (45 + 6) + BitVec.ofNat 64 d = cpuRgn.base.add 20
  d51 : ∀ feat, Dec feat code 51 (FV7z.mk .and 32 [gr 32 0, .imm 32 512] 5)
  d56 : ∃ d, (∀ feat, Dec feat code 56 (FV7z.mk .test 8 [.mem (mrip d 8), .imm 8 2] 7)) ∧
    e.add (56 + 7) + BitVec.ofNat 64 d = cpuRgn.base.add 96
  d63 : ∀ feat, Dec feat code 63 (FV7z.mk (.jcc 4) 64 [.rel 31] 2)
  d65 : ∀ feat, Dec feat code 65 (FV7z.mk .test 32 [gr 32 0, gr 32 0] 2)
  d67 : Lea code e 67 2 v.avx2A
  d74 : Lea code e 74 0 v.avx2B
  d81 : ∀ feat, Dec feat code 81 (FV7z.mk (.cmovcc 4) 64 [gr 64 0, gr 64 2] 4)
  d85 : ∀ feat, Dec feat code 85 (FV7z.mk .ret 64 [] 1)
  d96 : ∀ feat, Dec feat code 96 (FV7z.mk .test 32 [gr 32 0, gr 32 0] 2)
  d98 : Lea code e 98 2 v.sse2A
  d105 : Lea code e 105 0 v.sse2B
  d112 : ∀ feat, Dec feat code 112 (FV7z.mk (.cmovcc 5) 64 [gr 64 0, gr 64 2] 4)
  d116 : ∀ feat, Dec feat code 116 (FV7z.mk .ret 64 [] 1)
  d120 : Lea code e 120 0 v.noVzu
  d127 : ∀ feat, Dec feat code 127 (FV7z.mk .and 8 [gh 2, .imm 8 8] 3)
  d130 : ∀ feat, Dec feat code 130 (FV7z.mk (.jcc 5) 64 [.rel 18446744073709551600] 2)
  d132 : ∃ d, (∀ feat, Dec feat code 132 (FV7z.mk .test 8 [.mem (mrip d 8), .imm 8 2] 7)) ∧
    e.add (132 + 7) + BitVec.ofNat 64 d = cpuRgn.base.add 21
  d139 : Lea code e 139 2 v.avx512A
  d146 : Lea code e 146 0 v.avx512B
  d153 : ∀ feat, Dec feat code 153 (FV7z.mk (.cmovcc 4) 64 [gr 64 0, gr 64 2] 4)
  d157 : ∀ feat, Dec feat code 157 (FV7z.mk .ret 64 [] 1)

abbrev AV : List (Features → Bool) := [Features.avx, Features.avx2]
abbrev A5 : List (Features → Bool) := [Features.avx, Features.avx2, Features.avx512f]

/-- The variants. -/
abbrev variants (v : Addrs) : Variants :=
  [(v.erms, []), (v.sse2A, []), (v.sse2B, []), (v.avx2A, AV), (v.avx2B, AV), (v.noVzu, A5), (v.avx512A, A5),
    (v.avx512B, A5)]

variable {prof : Profile} {code : List Byte} {e : Addr} {v : Addrs} {L : List (Addr × List Byte)} {s₀ : State}
  {ra : Addr} {o : Oracle}

theorem at120 (sh : Shape code e v) (c : Call prof RR (PP prof) (QQ prof (variants v)) code e L s₀ ra o)
    (h5 : prof.feat.avx = true ∧ prof.feat.avx2 = true ∧ prof.feat.avx512f = true)
    {X : State} {t : Nat} (hK : Kept s₀ X) (hC : Callee s₀ X) (hrip : X.cpu.rip = e.add 120) :
    Go prof RR (PP prof) (QQ prof (variants v)) L s₀ ra o X t := by
  have hk : ∀ k, k < 158 → k < code.length := fun k h => sh.len ▸ h
  have p5 : ∀ f ∈ A5, f prof.feat = true := by simp [h5.1, h5.2.1, h5.2.2]
  obtain ⟨d120, hd120, ha120⟩ := sh.d120
  obtain ⟨d132, hd132, ha132⟩ := sh.d132
  obtain ⟨c1, c2, c3, c4, c5, c6, c7⟩ := hC
  refine c.s_lea_rip hK (hk 120 (by decide)) hrip (hd120 _) ha120 fun Y1 _ hK1 hr1 ⟨g1, _⟩ => ?_
  refine c.s_and_h8i hK1 (hk 127 (by decide)) hr1 (sh.d127 _) fun Y2 _ hK2 hr2 ⟨g2, _⟩ => ?_
  refine c.s_jcc hK2 (hk 130 (by decide)) hr2 (sh.d130 _) (tgt := 116) (by decide) (hk 116 (by decide))
    (fun _ => ?_) (fun _ => ?_)
  · intro Y3 _ hK3 hr3 g3
    refine c.ret hK3 (calleeOf (by simp [g3, g2, g1, c1, c2, c3, c4, c5, c6, c7])) (hk 116 (by decide)) hr3
      (sh.d116 _) ?_
    show Returns prof _ Y3.cpu.gpr.rax
    rw [show Y3.cpu.gpr.rax = v.noVzu by simp [g3, g2, g1]]
    exact Returns.of_mem (by simp) p5
  · intro Y3 _ hK3 hr3 g3
    refine c.s_test_m8i_rip hK3 (hk 132 (by decide)) hr3 (hd132 _) hr0 ha132 (by decide)
      fun Y4 _ hK4 hr4 ⟨g4, _⟩ => ?_
    exact Pair.go c hK4 (calleeOf (by simp [g4, g3, g2, g1, c1, c2, c3, c4, c5, c6, c7])) hr4 (hk _ (by decide))
      (Or.inl ⟨rfl, rfl⟩) sh.d139 sh.d146 sh.d153 sh.d157 (Returns.of_mem (by simp) p5) (Returns.of_mem (by simp) p5)

/-- The run of a call, from its first instruction. -/
theorem run (sh : Shape code e v) (c : Call prof RR (PP prof) (QQ prof (variants v)) code e L s₀ ra o)
    (hc : prof.Consistent) (hch : Chain prof) {t : Nat} : Go prof RR (PP prof) (QQ prof (variants v)) L s₀ ra o s₀ t := by
  have hok : CpuOk prof s₀.proc.mm.mem := c.call.pre
  have hk : ∀ k, k < 158 → k < code.length := fun k h => sh.len ▸ h
  obtain ⟨d4, hd4, ha4⟩ := sh.d4
  obtain ⟨d10, hd10, ha10⟩ := sh.d10
  obtain ⟨d32, hd32, ha32⟩ := sh.d32
  obtain ⟨d45, hd45, ha45⟩ := sh.d45
  obtain ⟨d56, hd56, ha56⟩ := sh.d56
  have hrip : s₀.cpu.rip = e.add 0 := by rw [c.call.shape.1]; simp [Addr.add]
  refine c.s_endbr (Kept.refl s₀) (hk 0 (by decide)) hrip (sh.d0 _) fun Y1 _ hK1 hr1 g1 => ?_
  refine c.s_mov32_rip hK1 (hk 4 (by decide)) hr1 (hd4 _) hr0 ha4 (by decide) fun Y2 _ hK2 hr2 g2 => ?_
  refine c.s_lea_rip hK2 (hk 10 (by decide)) hr2 (hd10 _) ha10 fun Y3 _ hK3 hr3 ⟨g3, _⟩ => ?_
  refine c.s_test_h8i hK3 (hk 17 (by decide)) hr3 (sh.d17 _) fun Y4 _ hK4 hr4 ⟨g4, _⟩ => ?_
  refine c.s_jcc hK4 (hk 20 (by decide)) hr4 (sh.d20 _) (tgt := 116) (by decide) (hk 116 (by decide))
    (fun _ => ?_) (fun _ => ?_)
  · -- `Prefer_ERMS`: `erms`
    intro Y5 _ hK5 hr5 g5
    refine c.ret hK5 (calleeOf (by simp [g5, g4, g3, g2, g1])) (hk 116 (by decide)) hr5 (sh.d116 _) ?_
    show Returns prof _ Y5.cpu.gpr.rax
    rw [show Y5.cpu.gpr.rax = v.erms by simp [g5, g4, g3]]
    exact Returns.of_mem (fs := []) (by simp) (by simp)
  · intro Y5 _ hK5 hr5 g5
    refine c.s_mov_ri64 hK5 (hk 22 (by decide)) hr5 (sh.d22 _) fun Y6 _ hK6 hr6 g6 => ?_
    refine c.s_and64_rip hK6 (hk 32 (by decide)) hr6 (hd32 _) hr0 ha32 (by decide) fun Y7 _ hK7 hr7 ⟨g7, _⟩ => ?_
    refine c.s_cmp_ri hK7 (hk 39 (by decide)) hr7 (sh.d39 _) fun Y8 _ hK8 hr8 ⟨g8, f8⟩ => ?_
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
      refine c.s_mov32_rip hK9 (hk 45 (by decide)) hr9 (hd45 _) hr0 ha45 (by decide) fun Y10 _ hK10 hr10 g10 => ?_
      refine c.s_and_ri32 hK10 (hk 51 (by decide)) hr10 (sh.d51 _) fun Y11 _ hK11 hr11 ⟨g11, _⟩ => ?_
      refine c.s_test_m8i_rip hK11 (hk 56 (by decide)) hr11 (hd56 _) hr0 ha56 (by decide)
        fun Y12 _ hK12 hr12 ⟨g12, z12⟩ => ?_
      have hC12 : Callee s₀ Y12 := calleeOf (by simp [g12, g11, g10, g9, g8, g7, g6, g5, g4, g3, g2, g1])
      obtain ⟨c1, c2, c3, c4, c5, c6, c7⟩ := hC12
      refine c.s_jcc hK12 (hk 63 (by decide)) hr12 (sh.d63 _) (tgt := 96) (by decide) (hk 96 (by decide))
        (fun _ => ?_) (fun hcc => ?_)
      · -- not `AVX2_Usable`: `sse2`
        intro Y13 _ hK13 hr13 g13
        refine c.s_test_rr32 hK13 (hk 96 (by decide)) hr13 (sh.d96 _) fun Y14 _ hK14 hr14 g14 => ?_
        exact Pair.go c hK14 (calleeOf (by simp [g14, g13, c1, c2, c3, c4, c5, c6, c7])) hr14 (hk _ (by decide))
          (Or.inl ⟨rfl, rfl⟩) sh.d98 sh.d105 sh.d112 sh.d116
          (Returns.of_mem (fs := []) (by simp) (by simp)) (Returns.of_mem (fs := []) (by simp) (by simp))
      · -- `AVX2_Usable`: `avx2`
        intro Y13 _ hK13 hr13 g13
        have hb : bit s₀.proc.mm.mem 96 1 = true := by
          have hz : (ofBytesLE 8 (readBytes s₀.proc.mm.mem (cpuRgn.base.add 96) 1) &&& BitVec.ofNat 8 2 == 0) = false := by
            rw [← z12]; simpa [cond4] using hcc
          have := getLsbD_of_and_pow (i := 1) _ hz
          rwa [getLsbD_word _ (by omega) (by omega)] at this
        have h2 := feat_avx2 hc hok hb
        have p2 : ∀ f ∈ AV, f prof.feat = true := by simp [h2.1, h2.2]
        refine c.s_test_rr32 hK13 (hk 65 (by decide)) hr13 (sh.d65 _) fun Y14 _ hK14 hr14 g14 => ?_
        exact Pair.go c hK14 (calleeOf (by simp [g14, g13, c1, c2, c3, c4, c5, c6, c7])) hr14 (hk _ (by decide))
          (Or.inl ⟨rfl, rfl⟩) sh.d67 sh.d74 sh.d81 sh.d85 (Returns.of_mem (by simp) p2) (Returns.of_mem (by simp) p2)

/-- The resolver, run at `e`: on a consistent profile with H-CPU-chain, with `_dl_x86_cpu_features` as
`init_cpu_features` leaves it, it returns one of its variants the processor has. -/
theorem holds (sh : Shape code e v) (L : List (Addr × List Byte)) (prof : Profile) (hc : prof.Consistent)
    (hch : Chain prof) (hin : CodeIn L e code) : ImplementsCall prof e L (resolverK prof (variants v)) := by
  intro s₀ ra hcall
  exact reachOrEndsIn_of_runsFrom fun o ho t => run sh ⟨hcall, hin, ho⟩ hc hch

end FV7z.Glibc.Memset
