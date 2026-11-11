import FV7z.Glibc.Avx2Pick
/-!
# The IFUNC resolvers of `7zzs` that pick among `avx2`, `sse2_unaligned`, `ssse3`, `sse2` (PLAN.md G2, "Dispatch theo
CPUID")

Four resolvers of `7zzs` (glibc 2.31's `sysdeps/x86_64/multiarch/ifunc-unaligned-ssse3.h`: `strcpy`, `stpcpy`,
`strncpy`, `strcat`, …) are the same 85 bytes but for their `rip`-relative displacements:

```
 0  endbr64                                 50  test byte feature[1], 0x10   (Fast_Unaligned_Load)
 4  movabs rdx, 0x90000000002               57  jne 84
14  and rdx, feature[0..1]                  59  test byte cpuid[1].ecx+1, 2  (SSSE3)
21  movabs rcx, 0x10000000002               66  lea rax, vSse2
31  lea rax, vAvx2                          73  lea rdx, vSsse3
38  cmp rdx, rcx  (AVX2_Usable, ...)        80  cmovne rax, rdx
41  je 84                                   84  ret
43  lea rax, vUnal
```

`Shape code e vAvx2 vUnal vSse2 vSsse3`: `code`, at `e`, is such a resolver. `holds`: with `_dl_x86_cpu_features` as
`init_cpu_features` leaves it (`CpuOk`), on a consistent profile, it returns `vSse2` or `vUnal`, or `vSsse3` on a
processor with SSSE3, or `vAvx2` with AVX and AVX2.
-/
namespace FV7z.Glibc.UnalignedSsse3
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf
open Avx2Pick (RR PP QQ hr0 avx2_of_eq)

/-- What the bytes `code` at `e` decode to, and where their operands point. -/
structure Shape (code : List Byte) (e vAvx2 vUnal vSse2 vSsse3 : Addr) : Prop where
  len : code.length = 85
  d0 : ∀ feat, Dec feat code 0 (FV7z.mk .endbr64 32 [] 4)
  d4 : ∀ feat, Dec feat code 4 (FV7z.mk .mov 64 [gr 64 2, .imm 64 9895604649986] 10)
  d14 : ∃ d, (∀ feat, Dec feat code 14 (FV7z.mk .and 64 [gr 64 2, .mem (mrip d 64)] 7)) ∧
    e.add (14 + 7) + BitVec.ofNat 64 d = cpuRgn.base.add 96
  d21 : ∀ feat, Dec feat code 21 (FV7z.mk .mov 64 [gr 64 1, .imm 64 1099511627778] 10)
  d31 : Lea code e 31 0 vAvx2
  d38 : ∀ feat, Dec feat code 38 (FV7z.mk .cmp 64 [gr 64 2, gr 64 1] 3)
  d41 : ∀ feat, Dec feat code 41 (FV7z.mk (.jcc 4) 64 [.rel 41] 2)
  d43 : Lea code e 43 0 vUnal
  d50 : ∃ d, (∀ feat, Dec feat code 50 (FV7z.mk .test 8 [.mem (mrip d 8), .imm 8 16] 7)) ∧
    e.add (50 + 7) + BitVec.ofNat 64 d = cpuRgn.base.add 100
  d57 : ∀ feat, Dec feat code 57 (FV7z.mk (.jcc 5) 64 [.rel 25] 2)
  d59 : ∃ d, (∀ feat, Dec feat code 59 (FV7z.mk .test 8 [.mem (mrip d 8), .imm 8 2] 7)) ∧
    e.add (59 + 7) + BitVec.ofNat 64 d = cpuRgn.base.add 9
  d66 : Lea code e 66 0 vSse2
  d73 : Lea code e 73 2 vSsse3
  d80 : ∀ feat, Dec feat code 80 (FV7z.mk (.cmovcc 5) 64 [gr 64 0, gr 64 2] 4)
  d84 : ∀ feat, Dec feat code 84 (FV7z.mk .ret 64 [] 1)

/-- The variants. -/
abbrev variants (vAvx2 vUnal vSse2 vSsse3 : Addr) : Variants :=
  [(vSse2, []), (vUnal, []), (vSsse3, [Features.ssse3]), (vAvx2, [Features.avx, Features.avx2])]

variable {prof : Profile} {code : List Byte} {e vAvx2 vUnal vSse2 vSsse3 : Addr} {L : List (Addr × List Byte)}
  {s₀ : State} {ra : Addr} {o : Oracle}

/-- The run of a call, from its first instruction. -/
theorem run (sh : Shape code e vAvx2 vUnal vSse2 vSsse3)
    (c : Call prof RR (PP prof) (QQ prof (variants vAvx2 vUnal vSse2 vSsse3)) code e L s₀ ra o)
    (hc : prof.Consistent) {t : Nat} : Go prof RR (PP prof) (QQ prof (variants vAvx2 vUnal vSse2 vSsse3)) L s₀ ra o s₀ t := by
  have hok : CpuOk prof s₀.proc.mm.mem := c.call.pre
  have hk : ∀ k, k < 85 → k < code.length := fun k h => sh.len ▸ h
  obtain ⟨da, hda, haa⟩ := sh.d14
  obtain ⟨d31, hd31, ha31⟩ := sh.d31
  obtain ⟨d43, hd43, ha43⟩ := sh.d43
  obtain ⟨d50, hd50, ha50⟩ := sh.d50
  obtain ⟨d59, hd59, ha59⟩ := sh.d59
  obtain ⟨d66, hd66, ha66⟩ := sh.d66
  obtain ⟨d73, hd73, ha73⟩ := sh.d73
  have hrip : s₀.cpu.rip = e.add 0 := by rw [c.call.shape.1]; simp [Addr.add]
  refine c.s_endbr (Kept.refl s₀) (hk 0 (by decide)) hrip (sh.d0 _) fun Y1 _ hK1 hr1 g1 => ?_
  refine c.s_mov_ri64 hK1 (hk 4 (by decide)) hr1 (sh.d4 _) fun Y2 _ hK2 hr2 g2 => ?_
  refine c.s_and64_rip hK2 (hk 14 (by decide)) hr2 (hda _) hr0 haa (by decide) fun Y3 _ hK3 hr3 ⟨g3, _⟩ => ?_
  refine c.s_mov_ri64 hK3 (hk 21 (by decide)) hr3 (sh.d21 _) fun Y4 _ hK4 hr4 g4 => ?_
  refine c.s_lea_rip hK4 (hk 31 (by decide)) hr4 (hd31 _) ha31 fun Y5 _ hK5 hr5 ⟨g5, _⟩ => ?_
  refine c.s_cmp_rr hK5 (hk 38 (by decide)) hr5 (sh.d38 _) fun Y6 _ hK6 hr6 ⟨g6, f6⟩ => ?_
  have hC6 : Callee s₀ Y6 := calleeOf (by simp [g6, g5, g4, g3, g2, g1])
  refine c.s_jcc hK6 (hk 41 (by decide)) hr6 (sh.d41 _) (tgt := 84) (by decide) (hk 84 (by decide))
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
    refine c.ret hK7 (calleeOf ?_) (hk 84 (by decide)) hr7 (sh.d84 _) ?_
    · rw [g7]; exact hC6
    · show Returns prof _ Y7.cpu.gpr.rax
      exact ⟨(vAvx2, [Features.avx, Features.avx2]), by simp, by simp [g7, g6, g5], by simp [h2.1, h2.2]⟩
  · intro Y7 _ hK7 hr7 g7
    refine c.s_lea_rip hK7 (hk 43 (by decide)) hr7 (hd43 _) ha43 fun Y8 _ hK8 hr8 ⟨g8, _⟩ => ?_
    refine c.s_test_m8i_rip hK8 (hk 50 (by decide)) hr8 (hd50 _) hr0 ha50 (by decide)
      fun Y9 _ hK9 hr9 ⟨g9, _⟩ => ?_
    have hC9 : Callee s₀ Y9 := by
      obtain ⟨c1, c2, c3, c4, c5, c6, c7⟩ := hC6
      exact calleeOf (by simp [g9, g8, g7, c1, c2, c3, c4, c5, c6, c7])
    refine c.s_jcc hK9 (hk 57 (by decide)) hr9 (sh.d57 _) (tgt := 84) (by decide) (hk 84 (by decide))
      (fun _ => ?_) (fun _ => ?_)
    · -- `Fast_Unaligned_Load`: `vUnal`
      intro Y10 _ hK10 hr10 g10
      refine c.ret hK10 (calleeOf ?_) (hk 84 (by decide)) hr10 (sh.d84 _) ?_
      · rw [g10]; exact hC9
      · show Returns prof _ Y10.cpu.gpr.rax
        exact ⟨(vUnal, []), by simp, by simp [g10, g9, g8], by simp⟩
    · intro Y10 _ hK10 hr10 g10
      refine c.s_test_m8i_rip hK10 (hk 59 (by decide)) hr10 (hd59 _) hr0 ha59 (by decide)
        fun Y11 _ hK11 hr11 ⟨g11, z11⟩ => ?_
      refine c.s_lea_rip hK11 (hk 66 (by decide)) hr11 (hd66 _) ha66 fun Y12 _ hK12 hr12 ⟨g12, z12⟩ => ?_
      refine c.s_lea_rip hK12 (hk 73 (by decide)) hr12 (hd73 _) ha73 fun Y13 _ hK13 hr13 ⟨g13, z13⟩ => ?_
      refine c.s_cmov hK13 (hk 80 (by decide)) hr13 (sh.d80 _) fun Y14 _ hK14 hr14 g14 => ?_
      have hax : Y14.cpu.gpr.rax = if Y13.cpu.rflags.cond 5 then vSsse3 else vSse2 := by
        rw [g14]
        split <;> simp [g13, g12]
      refine c.ret hK14 (calleeOf ?_) (hk 84 (by decide)) hr14 (sh.d84 _) ?_
      · obtain ⟨c1, c2, c3, c4, c5, c6, c7⟩ := hC9
        rw [g14]
        split <;> simp [g13, g12, g11, g10, c1, c2, c3, c4, c5, c6, c7]
      · show Returns prof _ Y14.cpu.gpr.rax
        rw [hax, cond5]
        cases hz : Y13.cpu.rflags.zf
        · -- SSSE3
          rw [z13, z12, z11] at hz
          have hb := getLsbD_of_and_pow (i := 1) _ hz
          rw [getLsbD_word _ (by omega) (by omega)] at hb
          exact ⟨(vSsse3, [Features.ssse3]), by simp, by simp, by simpa using (feat_of_ecx1 hc hok).1 hb⟩
        · exact ⟨(vSse2, []), by simp, by simp, by simp⟩

/-- Such a resolver, run at `e`: on a consistent profile, with `_dl_x86_cpu_features` as `init_cpu_features` leaves
it, it returns `vSse2` or `vUnal`, or `vSsse3` on a processor with SSSE3, or `vAvx2` with AVX and AVX2. -/
theorem holds (sh : Shape code e vAvx2 vUnal vSse2 vSsse3) (L : List (Addr × List Byte)) (prof : Profile)
    (hc : prof.Consistent) (hin : CodeIn L e code) :
    ImplementsCall prof e L (resolverK prof (variants vAvx2 vUnal vSse2 vSsse3)) := by
  intro s₀ ra hcall
  exact reachOrEndsIn_of_runsFrom fun o ho t => run sh ⟨hcall, hin, ho⟩ hc

end FV7z.Glibc.UnalignedSsse3
