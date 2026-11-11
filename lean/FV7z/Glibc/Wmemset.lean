import FV7z.Glibc.Avx2Pick
/-!
# The IFUNC resolver of `wmemset` in `7zzs`: `avx512_unaligned`, `avx2_unaligned`, `sse2_unaligned` (PLAN.md G2,
"Dispatch theo CPUID")

glibc 2.31's `sysdeps/x86_64/multiarch/ifunc-wmemset.h`, 85 bytes of `7zzs`:

```
 0  endbr64                                 46  movabs rax, 0x400000000004  (AVX512F_Usable, Prefer_No_AVX512)
 4  mov rdx, feature[0..1]                  56  lea r8, vAvx512
11  lea r8, vSse2                           63  and rdx, rax
18  movabs rax, 0x90000000002               66  lea rax, vAvx2
28  movabs rcx, 0x10000000002               73  cmp rdx, 4
38  and rax, rdx                            77  cmovne r8, rax
41  cmp rax, rcx  (AVX2_Usable, ...)        81  mov rax, r8
44  jne 81                                  84  ret
```

`holds`: with `_dl_x86_cpu_features` as `init_cpu_features` leaves it (`CpuOk`), on a consistent profile, it returns
`vSse2`, or `vAvx2` on a processor with AVX and AVX2, or `vAvx512` with AVX, AVX2 and AVX-512F.
-/
namespace FV7z.Glibc.Wmemset
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf
open Avx2Pick (RR PP QQ hr0 avx2_of_eq)

/-- What the bytes `code` at `e` decode to, and where their operands point. -/
structure Shape (code : List Byte) (e vSse2 vAvx2 vAvx512 : Addr) : Prop where
  len : code.length = 85
  d0 : ∀ feat, Dec feat code 0 (FV7z.mk .endbr64 32 [] 4)
  d4 : ∃ d, (∀ feat, Dec feat code 4 (FV7z.mk .mov 64 [gr 64 2, .mem (mrip d 64)] 7)) ∧
    e.add (4 + 7) + BitVec.ofNat 64 d = cpuRgn.base.add 96
  d11 : Lea code e 11 8 vSse2
  d18 : ∀ feat, Dec feat code 18 (FV7z.mk .mov 64 [gr 64 0, .imm 64 9895604649986] 10)
  d28 : ∀ feat, Dec feat code 28 (FV7z.mk .mov 64 [gr 64 1, .imm 64 1099511627778] 10)
  d38 : ∀ feat, Dec feat code 38 (FV7z.mk .and 64 [gr 64 0, gr 64 2] 3)
  d41 : ∀ feat, Dec feat code 41 (FV7z.mk .cmp 64 [gr 64 0, gr 64 1] 3)
  d44 : ∀ feat, Dec feat code 44 (FV7z.mk (.jcc 5) 64 [.rel 35] 2)
  d46 : ∀ feat, Dec feat code 46 (FV7z.mk .mov 64 [gr 64 0, .imm 64 70368744177668] 10)
  d56 : Lea code e 56 8 vAvx512
  d63 : ∀ feat, Dec feat code 63 (FV7z.mk .and 64 [gr 64 2, gr 64 0] 3)
  d66 : Lea code e 66 0 vAvx2
  d73 : ∀ feat, Dec feat code 73 (FV7z.mk .cmp 64 [gr 64 2, .imm 64 4] 4)
  d77 : ∀ feat, Dec feat code 77 (FV7z.mk (.cmovcc 5) 64 [gr 64 8, gr 64 0] 4)
  d81 : ∀ feat, Dec feat code 81 (FV7z.mk .mov 64 [gr 64 0, gr 64 8] 3)
  d84 : ∀ feat, Dec feat code 84 (FV7z.mk .ret 64 [] 1)

/-- The variants. -/
abbrev variants (vSse2 vAvx2 vAvx512 : Addr) : Variants :=
  [(vSse2, []), (vAvx2, [Features.avx, Features.avx2]), (vAvx512, [Features.avx, Features.avx2, Features.avx512f])]

variable {prof : Profile} {code : List Byte} {e vSse2 vAvx2 vAvx512 : Addr} {L : List (Addr × List Byte)}
  {s₀ : State} {ra : Addr} {o : Oracle}

/-- The run of a call, from its first instruction. -/
theorem run (sh : Shape code e vSse2 vAvx2 vAvx512)
    (c : Call prof RR (PP prof) (QQ prof (variants vSse2 vAvx2 vAvx512)) code e L s₀ ra o)
    (hc : prof.Consistent) {t : Nat} : Go prof RR (PP prof) (QQ prof (variants vSse2 vAvx2 vAvx512)) L s₀ ra o s₀ t := by
  have hok : CpuOk prof s₀.proc.mm.mem := c.call.pre
  have hk : ∀ k, k < 85 → k < code.length := fun k h => sh.len ▸ h
  obtain ⟨d4, hd4, ha4⟩ := sh.d4
  obtain ⟨d11, hd11, ha11⟩ := sh.d11
  obtain ⟨d56, hd56, ha56⟩ := sh.d56
  obtain ⟨d66, hd66, ha66⟩ := sh.d66
  have hrip : s₀.cpu.rip = e.add 0 := by rw [c.call.shape.1]; simp [Addr.add]
  refine c.s_endbr (Kept.refl s₀) (hk 0 (by decide)) hrip (sh.d0 _) fun Y1 _ hK1 hr1 g1 => ?_
  refine c.s_mov64_rip hK1 (hk 4 (by decide)) hr1 (hd4 _) hr0 ha4 (by decide) fun Y2 _ hK2 hr2 ⟨g2, _⟩ => ?_
  refine c.s_lea_rip hK2 (hk 11 (by decide)) hr2 (hd11 _) ha11 fun Y3 _ hK3 hr3 ⟨g3, _⟩ => ?_
  refine c.s_mov_ri64 hK3 (hk 18 (by decide)) hr3 (sh.d18 _) fun Y4 _ hK4 hr4 g4 => ?_
  refine c.s_mov_ri64 hK4 (hk 28 (by decide)) hr4 (sh.d28 _) fun Y5 _ hK5 hr5 g5 => ?_
  refine c.s_and_rr64 hK5 (hk 38 (by decide)) hr5 (sh.d38 _) fun Y6 _ hK6 hr6 ⟨g6, _⟩ => ?_
  refine c.s_cmp_rr hK6 (hk 41 (by decide)) hr6 (sh.d41 _) fun Y7 _ hK7 hr7 ⟨g7, f7⟩ => ?_
  have hC7 : Callee s₀ Y7 := calleeOf (by simp [g7, g6, g5, g4, g3, g2, g1])
  obtain ⟨c1, c2, c3, c4, c5, c6, c7⟩ := hC7
  refine c.s_jcc hK7 (hk 44 (by decide)) hr7 (sh.d44 _) (tgt := 81) (by decide) (hk 81 (by decide))
    (fun _ => ?_) (fun hcc => ?_)
  · -- not `AVX2_Usable` (or `Prefer_No_VZEROUPPER`, …): `vSse2`
    intro Y8 _ hK8 hr8 g8
    refine c.s_mov_rr hK8 (hk 81 (by decide)) hr8 (sh.d81 _) fun Y9 _ hK9 hr9 g9 => ?_
    refine c.ret hK9 (calleeOf (by simp [g9, g8, c1, c2, c3, c4, c5, c6, c7])) (hk 84 (by decide)) hr9
      (sh.d84 _) ?_
    exact ⟨(vSse2, []), by simp, by simp [g9, g8, g7, g6, g5, g4, g3], by simp⟩
  · intro Y8 _ hK8 hr8 g8
    have hW : bit s₀.proc.mm.mem 96 1 = true := by
      have hcc' : decide (rv Y6 64 0 = rv Y6 64 1) = true := by
        revert hcc
        rw [cond5, f7, subF_zf]
        cases decide (rv Y6 64 0 = rv Y6 64 1) <;> simp
      have heq := of_decide_eq_true hcc'
      simp only [rv, g6, g5, g4, g3, g2, g1, get_regOf_0, get_regOf_1, get_regOf_2, set_rax, set_rcx, set_rdx,
        set_r8, BitVec.setWidth_eq] at heq
      rw [← getLsbD_word (a := 96) (w := 64) (n := 8) (i := 1) _ (by omega) (by omega)]
      exact avx2_of_eq _ heq
    have h2 := feat_avx2 hc hok hW
    refine c.s_mov_ri64 hK8 (hk 46 (by decide)) hr8 (sh.d46 _) fun Y9 _ hK9 hr9 g9 => ?_
    refine c.s_lea_rip hK9 (hk 56 (by decide)) hr9 (hd56 _) ha56 fun Y10 _ hK10 hr10 ⟨g10, _⟩ => ?_
    refine c.s_and_rr64 hK10 (hk 63 (by decide)) hr10 (sh.d63 _) fun Y11 _ hK11 hr11 ⟨g11, _⟩ => ?_
    refine c.s_lea_rip hK11 (hk 66 (by decide)) hr11 (hd66 _) ha66 fun Y12 _ hK12 hr12 ⟨g12, _⟩ => ?_
    refine c.s_cmp_ri hK12 (hk 73 (by decide)) hr12 (sh.d73 _) fun Y13 _ hK13 hr13 ⟨g13, f13⟩ => ?_
    refine c.s_cmov hK13 (hk 77 (by decide)) hr13 (sh.d77 _) fun Y14 _ hK14 hr14 g14 => ?_
    refine c.s_mov_rr hK14 (hk 81 (by decide)) hr14 (sh.d81 _) fun Y15 _ hK15 hr15 g15 => ?_
    have hax : Y15.cpu.gpr.rax = if Y13.cpu.rflags.cond 5 then vAvx2 else vAvx512 := by
      rw [g15, g14]
      split <;> simp [g13, g12, g11, g10]
    refine c.ret hK15 (calleeOf ?_) (hk 84 (by decide)) hr15 (sh.d84 _) ?_
    · rw [g15, g14]
      split <;> simp [g13, g12, g11, g10, g9, g8, c1, c2, c3, c4, c5, c6, c7]
    · show Returns prof _ Y15.cpu.gpr.rax
      rw [hax, cond5, f13, subF_zf]
      cases hz : decide (rv Y12 64 2 = BitVec.ofNat 64 4)
      · exact ⟨(vAvx2, [Features.avx, Features.avx2]), by simp, by simp, by simp [h2.1, h2.2]⟩
      · have h4 := of_decide_eq_true hz
        simp only [rv, g12, g11, g10, g9, g8, g7, g6, g5, g4, g3, g2, g1, get_regOf_0, get_regOf_1, get_regOf_2,
          get_regOf_8, set_rax, set_rcx, set_rdx, set_r8, BitVec.setWidth_eq] at h4
        have hb : bit s₀.proc.mm.mem 96 2 = true := by
          rw [← getLsbD_word (a := 96) (w := 64) (n := 8) (i := 2) _ (by omega) (by omega)]
          exact avx512_of_eq _ h4
        exact ⟨(vAvx512, [Features.avx, Features.avx2, Features.avx512f]), by simp, by simp,
          by simp [h2.1, h2.2, feat_avx512f hc hok hb]⟩

/-- The resolver, run at `e`: on a consistent profile, with `_dl_x86_cpu_features` as `init_cpu_features` leaves it,
it returns `vSse2`, or `vAvx2` on a processor with AVX and AVX2, or `vAvx512` with AVX, AVX2 and AVX-512F. -/
theorem holds (sh : Shape code e vSse2 vAvx2 vAvx512) (L : List (Addr × List Byte)) (prof : Profile)
    (hc : prof.Consistent) (hin : CodeIn L e code) :
    ImplementsCall prof e L (resolverK prof (variants vSse2 vAvx2 vAvx512)) := by
  intro s₀ ra hcall
  exact reachOrEndsIn_of_runsFrom fun o ho t => run sh ⟨hcall, hin, ho⟩ hc

end FV7z.Glibc.Wmemset
