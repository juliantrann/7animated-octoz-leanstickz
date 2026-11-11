import FV7z.Glibc.Cpu
/-!
# The IFUNC resolvers of `7zzs` that pick an AVX2 variant or a base one (PLAN.md G2, "Dispatch theo CPUID")

Nine resolvers of `7zzs` (glibc 2.31's `sysdeps/x86_64/multiarch/ifunc-avx2.h`, folded into one body per pair of
variants: `memrchr`, `rawmemchr`, `strchrnul`, `strnlen`, …) are the same 53 bytes but for their `rip`-relative
displacements:

```
 0  endbr64
 4  movabs rdx, 0x10000000002   AVX2_Usable, AVX_Fast_Unaligned_Load
14  movabs rax, 0x90000000002   the same, and Prefer_No_VZEROUPPER
24  and rax, feature[0..1]
31  cmp rax, rdx
34  lea rdx, v1                 (the `avx2` variant)
41  lea rax, v0                 (the `sse2` variant)
48  cmove rax, rdx
52  ret
```

`Shape code e v0 v1`: `code`, at `e`, is such a resolver, `v0` and `v1` its variants: what a resolver's bytes decode
to (on every processor) and where its operands point. `holds`: with `_dl_x86_cpu_features` as `init_cpu_features`
leaves it (`CpuOk`), on a consistent profile, it returns `v0`, or `v1` on a processor with AVX and AVX2.
-/
namespace FV7z.Glibc.Avx2Pick
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- What the bytes `code` at `e` decode to, and where their operands point. -/
structure Shape (code : List Byte) (e v0 v1 : Addr) : Prop where
  len : code.length = 53
  d0 : ∀ feat, Dec feat code 0 (FV7z.mk .endbr64 32 [] 4)
  d4 : ∀ feat, Dec feat code 4 (FV7z.mk .mov 64 [gr 64 2, .imm 64 1099511627778] 10)
  d14 : ∀ feat, Dec feat code 14 (FV7z.mk .mov 64 [gr 64 0, .imm 64 9895604649986] 10)
  d24 : ∃ d, (∀ feat, Dec feat code 24 (FV7z.mk .and 64 [gr 64 0, .mem (mrip d 64)] 7)) ∧
    e.add (24 + 7) + BitVec.ofNat 64 d = cpuRgn.base.add 96
  d31 : ∀ feat, Dec feat code 31 (FV7z.mk .cmp 64 [gr 64 0, gr 64 2] 3)
  d34 : ∃ d, (∀ feat, Dec feat code 34 (FV7z.mk .lea 64 [gr 64 2, .mem (mrip d 0)] 7)) ∧
    e.add (34 + 7) + BitVec.ofNat 64 d = v1
  d41 : ∃ d, (∀ feat, Dec feat code 41 (FV7z.mk .lea 64 [gr 64 0, .mem (mrip d 0)] 7)) ∧
    e.add (41 + 7) + BitVec.ofNat 64 d = v0
  d48 : ∀ feat, Dec feat code 48 (FV7z.mk (.cmovcc 4) 64 [gr 64 0, gr 64 2] 4)
  d52 : ∀ feat, Dec feat code 52 (FV7z.mk .ret 64 [] 1)

/-- The variants: `v0` on every processor, `v1` with AVX and AVX2. -/
abbrev variants (v0 v1 : Addr) : Variants := [(v0, []), (v1, [Features.avx, Features.avx2])]

abbrev RR : State → List Rgn := fun _ => [cpuRgn]
abbrev PP (prof : Profile) : State → Prop := fun s => CpuOk prof s.proc.mm.mem
abbrev QQ (prof : Profile) (vs : Variants) : State → BitVec 64 → Prop := fun _ r => Returns prof vs r

theorem hr0 {s : State} : cpuRgn ∈ RR s := List.mem_singleton_self _

/-- `AVX2_Usable` set, from `cmp rax, rdx` finding them equal. -/
theorem avx2_of_eq (W : BitVec 64) (h : (BitVec.ofNat 64 9895604649986 &&& W) = BitVec.ofNat 64 1099511627778) :
    W.getLsbD 1 = true := by
  have := congrArg (fun x => x.getLsbD 1) h
  simp only [BitVec.getLsbD_and] at this
  have h1 : (BitVec.ofNat 64 9895604649986).getLsbD 1 = true := by decide
  have h2 : (BitVec.ofNat 64 1099511627778).getLsbD 1 = true := by decide
  rw [h1, h2, Bool.true_and] at this
  exact this

variable {prof : Profile} {code : List Byte} {e v0 v1 : Addr} {L : List (Addr × List Byte)} {s₀ : State} {ra : Addr}
  {o : Oracle}

/-- The run of a call, from its first instruction. -/
theorem run (sh : Shape code e v0 v1) (c : Call prof RR (PP prof) (QQ prof (variants v0 v1)) code e L s₀ ra o)
    (hc : prof.Consistent) {t : Nat} : Go prof RR (PP prof) (QQ prof (variants v0 v1)) L s₀ ra o s₀ t := by
  have hok : CpuOk prof s₀.proc.mm.mem := c.call.pre
  have hk : ∀ k, k < 53 → k < code.length := fun k h => sh.len ▸ h
  obtain ⟨da, hda, haa⟩ := sh.d24
  obtain ⟨d1, hd1, ha1⟩ := sh.d34
  obtain ⟨d0, hd0, ha0⟩ := sh.d41
  have hrip : s₀.cpu.rip = e.add 0 := by rw [c.call.shape.1]; simp [Addr.add]
  refine c.s_endbr (Kept.refl s₀) (hk 0 (by decide)) hrip (sh.d0 _) fun Y1 _ hK1 hr1 g1 => ?_
  refine c.s_mov_ri64 hK1 (hk 4 (by decide)) hr1 (sh.d4 _) fun Y2 _ hK2 hr2 g2 => ?_
  refine c.s_mov_ri64 hK2 (hk 14 (by decide)) hr2 (sh.d14 _) fun Y3 _ hK3 hr3 g3 => ?_
  refine c.s_and64_rip hK3 (hk 24 (by decide)) hr3 (hda _) hr0 haa (by decide) fun Y4 _ hK4 hr4 ⟨g4, _⟩ => ?_
  refine c.s_cmp_rr hK4 (hk 31 (by decide)) hr4 (sh.d31 _) fun Y5 _ hK5 hr5 ⟨g5, f5⟩ => ?_
  refine c.s_lea_rip hK5 (hk 34 (by decide)) hr5 (hd1 _) ha1 fun Y6 _ hK6 hr6 ⟨g6, z6⟩ => ?_
  refine c.s_lea_rip hK6 (hk 41 (by decide)) hr6 (hd0 _) ha0 fun Y7 _ hK7 hr7 ⟨g7, z7⟩ => ?_
  refine c.s_cmov hK7 (hk 48 (by decide)) hr7 (sh.d48 _) fun Y8 _ hK8 hr8 g8 => ?_
  rw [cond4, z7, z6, f5, subF_zf] at g8
  refine c.ret hK8 (calleeOf ?_) (hk 52 (by decide)) hr8 (sh.d52 _) ?_
  · rw [g8]
    split <;> simp [g7, g6, g5, g4, g3, g2, g1]
  · show Returns prof (variants v0 v1) Y8.cpu.gpr.rax
    rw [g8]
    split
    · next heq =>
      have heq := of_decide_eq_true heq
      simp only [rv, g5, g4, g3, g2, g1, get_regOf_0, get_regOf_2, set_rax, set_rdx, BitVec.setWidth_eq] at heq
      have hW : bit s₀.proc.mm.mem 96 1 = true := by
        rw [← getLsbD_word (a := 96) (w := 64) (n := 8) (i := 1) _ (by omega) (by omega)]
        exact avx2_of_eq _ heq
      have h2 := feat_avx2 hc hok hW
      refine ⟨(v1, [Features.avx, Features.avx2]), by simp, by simp [g7, g6], ?_⟩
      simp [h2.1, h2.2]
    · exact ⟨(v0, []), by simp, by simp [g7], by simp⟩

/-- Such a resolver, run at `e`: on a consistent profile, with `_dl_x86_cpu_features` as `init_cpu_features` leaves
it, it returns `v0`, or `v1` on a processor with AVX and AVX2. -/
theorem holds (sh : Shape code e v0 v1) (L : List (Addr × List Byte)) (prof : Profile) (hc : prof.Consistent)
    (hin : CodeIn L e code) : ImplementsCall prof e L (resolverK prof (variants v0 v1)) := by
  intro s₀ ra hcall
  exact reachOrEndsIn_of_runsFrom fun o ho t => run sh ⟨hcall, hin, ho⟩ hc

end FV7z.Glibc.Avx2Pick
