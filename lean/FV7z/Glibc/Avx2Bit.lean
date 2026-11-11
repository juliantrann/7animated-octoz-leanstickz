import FV7z.Glibc.Avx2Pick
/-!
# The IFUNC resolvers of `7zzs` that pick an AVX2 variant, else one by a bit of `_dl_x86_cpu_features` (PLAN.md G2,
"Dispatch theo CPUID")

Two resolvers of `7zzs` (`wcsnlen`: `sse4_1` by `CPUID.01H:ECX.SSE4_1`; `strchr`: `sse2_no_bsf` by `Slow_BSF`) are the
same 69 bytes but for the bit they test and their `rip`-relative displacements:

```
 0  endbr64                                 38  cmp rdx, rcx  (AVX2_Usable, ...)
 4  movabs rdx, 0x90000000002               41  je 68
14  and rdx, feature[0..1]                  43  test byte [cpu + a], 2^i
21  movabs rcx, 0x10000000002               50  lea rax, va
31  lea rax, vAvx2                          57  lea rdx, vd
                                            64  cmovne rax, rdx
                                            68  ret
```

`holds`: with `_dl_x86_cpu_features` as `init_cpu_features` leaves it (`CpuOk`), on a consistent profile, it returns
`vAvx2` on a processor with AVX and AVX2, `va`, or `vd` with bit `i` of byte `a` set: so, given what that bit says
(`hfs`), only on a processor with the features `fs`.
-/
namespace FV7z.Glibc.Avx2Bit
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf
open Avx2Pick (RR PP QQ hr0 avx2_of_eq)

/-- What the bytes `code` at `e` decode to, and where their operands point. -/
structure Shape (code : List Byte) (e : Addr) (a i : Nat) (vAvx2 vd va : Addr) : Prop where
  len : code.length = 69
  d0 : ∀ feat, Dec feat code 0 (FV7z.mk .endbr64 32 [] 4)
  d4 : ∀ feat, Dec feat code 4 (FV7z.mk .mov 64 [gr 64 2, .imm 64 9895604649986] 10)
  d14 : ∃ d, (∀ feat, Dec feat code 14 (FV7z.mk .and 64 [gr 64 2, .mem (mrip d 64)] 7)) ∧
    e.add (14 + 7) + BitVec.ofNat 64 d = cpuRgn.base.add 96
  d21 : ∀ feat, Dec feat code 21 (FV7z.mk .mov 64 [gr 64 1, .imm 64 1099511627778] 10)
  d31 : Lea code e 31 0 vAvx2
  d38 : ∀ feat, Dec feat code 38 (FV7z.mk .cmp 64 [gr 64 2, gr 64 1] 3)
  d41 : ∀ feat, Dec feat code 41 (FV7z.mk (.jcc 4) 64 [.rel 25] 2)
  d43 : ∃ d imm, (∀ feat, Dec feat code 43 (FV7z.mk .test 8 [.mem (mrip d 8), .imm 8 imm] 7)) ∧
    e.add (43 + 7) + BitVec.ofNat 64 d = cpuRgn.base.add a ∧ imm = 2 ^ i
  hi : i < 8
  hn : a + 1 ≤ cpuRgn.len
  d50 : Lea code e 50 0 va
  d57 : Lea code e 57 2 vd
  d64 : ∀ feat, Dec feat code 64 (FV7z.mk (.cmovcc 5) 64 [gr 64 0, gr 64 2] 4)
  d68 : ∀ feat, Dec feat code 68 (FV7z.mk .ret 64 [] 1)

/-- The variants. -/
abbrev variants (vAvx2 vd va : Addr) (fs : List (Features → Bool)) : Variants :=
  [(va, []), (vd, fs), (vAvx2, [Features.avx, Features.avx2])]

variable {prof : Profile} {code : List Byte} {e vAvx2 vd va : Addr} {a i : Nat} {fs : List (Features → Bool)}
  {L : List (Addr × List Byte)} {s₀ : State} {ra : Addr} {o : Oracle}

/-- The run of a call, from its first instruction. -/
theorem run (sh : Shape code e a i vAvx2 vd va) (hfs : bit s₀.proc.mm.mem a i = true → ∀ f ∈ fs, f prof.feat = true)
    (c : Call prof RR (PP prof) (QQ prof (variants vAvx2 vd va fs)) code e L s₀ ra o)
    (hc : prof.Consistent) {t : Nat} : Go prof RR (PP prof) (QQ prof (variants vAvx2 vd va fs)) L s₀ ra o s₀ t := by
  have hok : CpuOk prof s₀.proc.mm.mem := c.call.pre
  have hk : ∀ k, k < 69 → k < code.length := fun k h => sh.len ▸ h
  obtain ⟨da, hda, haa⟩ := sh.d14
  obtain ⟨d31, hd31, ha31⟩ := sh.d31
  obtain ⟨dt, imm, hdt, hat, himm⟩ := sh.d43
  obtain ⟨d50, hd50, ha50⟩ := sh.d50
  obtain ⟨d57, hd57, ha57⟩ := sh.d57
  have hrip : s₀.cpu.rip = e.add 0 := by rw [c.call.shape.1]; simp [Addr.add]
  refine c.s_endbr (Kept.refl s₀) (hk 0 (by decide)) hrip (sh.d0 _) fun Y1 _ hK1 hr1 g1 => ?_
  refine c.s_mov_ri64 hK1 (hk 4 (by decide)) hr1 (sh.d4 _) fun Y2 _ hK2 hr2 g2 => ?_
  refine c.s_and64_rip hK2 (hk 14 (by decide)) hr2 (hda _) hr0 haa (by decide) fun Y3 _ hK3 hr3 ⟨g3, _⟩ => ?_
  refine c.s_mov_ri64 hK3 (hk 21 (by decide)) hr3 (sh.d21 _) fun Y4 _ hK4 hr4 g4 => ?_
  refine c.s_lea_rip hK4 (hk 31 (by decide)) hr4 (hd31 _) ha31 fun Y5 _ hK5 hr5 ⟨g5, _⟩ => ?_
  refine c.s_cmp_rr hK5 (hk 38 (by decide)) hr5 (sh.d38 _) fun Y6 _ hK6 hr6 ⟨g6, f6⟩ => ?_
  have hC6 : Callee s₀ Y6 := calleeOf (by simp [g6, g5, g4, g3, g2, g1])
  refine c.s_jcc hK6 (hk 41 (by decide)) hr6 (sh.d41 _) (tgt := 68) (by decide) (hk 68 (by decide))
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
    refine c.ret hK7 (calleeOf ?_) (hk 68 (by decide)) hr7 (sh.d68 _) ?_
    · rw [g7]; exact hC6
    · show Returns prof _ Y7.cpu.gpr.rax
      exact ⟨(vAvx2, [Features.avx, Features.avx2]), by simp, by simp [g7, g6, g5], by simp [h2.1, h2.2]⟩
  · intro Y7 _ hK7 hr7 g7
    refine c.s_test_m8i_rip hK7 (hk 43 (by decide)) hr7 (hdt _) hr0 hat sh.hn fun Y8 _ hK8 hr8 ⟨g8, z8⟩ => ?_
    refine c.s_lea_rip hK8 (hk 50 (by decide)) hr8 (hd50 _) ha50 fun Y9 _ hK9 hr9 ⟨g9, z9⟩ => ?_
    refine c.s_lea_rip hK9 (hk 57 (by decide)) hr9 (hd57 _) ha57 fun Y10 _ hK10 hr10 ⟨g10, z10⟩ => ?_
    refine c.s_cmov hK10 (hk 64 (by decide)) hr10 (sh.d64 _) fun Y11 _ hK11 hr11 g11 => ?_
    have hax : Y11.cpu.gpr.rax = if Y10.cpu.rflags.cond 5 then vd else va := by
      rw [g11]
      split <;> simp [g10, g9]
    refine c.ret hK11 (calleeOf ?_) (hk 68 (by decide)) hr11 (sh.d68 _) ?_
    · obtain ⟨c1, c2, c3, c4, c5, c6, c7⟩ := hC6
      rw [g11]
      split <;> simp [g10, g9, g8, g7, c1, c2, c3, c4, c5, c6, c7]
    · show Returns prof _ Y11.cpu.gpr.rax
      rw [hax, cond5]
      cases hz : Y10.cpu.rflags.zf
      · rw [z10, z9, z8, himm] at hz
        have hb := getLsbD_of_and_pow (i := i) _ hz
        rw [getLsbD_word _ (by have := sh.hi; omega) sh.hi] at hb
        exact ⟨(vd, fs), by simp, by simp, hfs hb⟩
      · exact ⟨(va, []), by simp, by simp, by simp⟩

/-- Such a resolver, run at `e`: on a consistent profile (with H-CPU-chain), with `_dl_x86_cpu_features` as
`init_cpu_features` leaves it, it returns `vAvx2` on a processor with AVX and AVX2, `va`, or `vd` on a processor with
the features `fs`, given that a set bit `i` of byte `a` says the processor has them (`hfs`). -/
theorem holds (sh : Shape code e a i vAvx2 vd va)
    (hfs : ∀ (prof : Profile) m, prof.Consistent → Chain prof → CpuOk prof m → bit m a i = true →
      ∀ f ∈ fs, f prof.feat = true)
    (L : List (Addr × List Byte)) (prof : Profile) (hc : prof.Consistent) (hch : Chain prof)
    (hin : CodeIn L e code) : ImplementsCall prof e L (resolverK prof (variants vAvx2 vd va fs)) := by
  intro s₀ ra hcall
  exact reachOrEndsIn_of_runsFrom fun o ho t => run sh (hfs prof _ hc hch hcall.pre) ⟨hcall, hin, ho⟩ hc

end FV7z.Glibc.Avx2Bit
