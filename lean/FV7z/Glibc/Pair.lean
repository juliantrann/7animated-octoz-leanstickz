import FV7z.Glibc.Avx2Pick
/-!
# The last four instructions of many IFUNC resolvers in `7zzs` (PLAN.md G2, "Dispatch theo CPUID")

`lea r1, [rip + A]; lea r2, [rip + B]; cmovcc rax, rdx; ret`, `r1` and `r2` being `rax` and `rdx` in either order:
whatever the flags, the resolver returns `A` or `B`; so, when both are variants the processor has, so is what it
returns.
-/
namespace FV7z.Glibc
open ZellicX86 Decode FV7z.Leaf
open Avx2Pick (RR PP QQ)

variable {prof : Profile} {vs : Variants} {code : List Byte} {e : Addr} {L : List (Addr × List Byte)} {s₀ : State}
  {ra : Addr} {o : Oracle}

theorem Pair.go (c : Call prof RR (PP prof) (QQ prof vs) code e L s₀ ra o) {X : State} {t k r1 r2 : Nat} {cc : Cond}
    {A B : Addr} (hK : Kept s₀ X) (hC : Callee s₀ X) (hrip : X.cpu.rip = e.add k) (hk : k + 18 < code.length)
    (hr : (r1 = 2 ∧ r2 = 0) ∨ (r1 = 0 ∧ r2 = 2)) (hA : Lea code e k r1 A) (hB : Lea code e (k + 7) r2 B)
    (hcm : ∀ feat, Dec feat code (k + 7 + 7) (FV7z.mk (.cmovcc cc) 64 [gr 64 0, gr 64 2] 4))
    (hret : ∀ feat, Dec feat code (k + 7 + 7 + 4) (FV7z.mk .ret 64 [] 1))
    (pA : Returns prof vs A) (pB : Returns prof vs B) : Go prof RR (PP prof) (QQ prof vs) L s₀ ra o X t := by
  obtain ⟨dA, hdA, haA⟩ := hA
  obtain ⟨dB, hdB, haB⟩ := hB
  obtain ⟨c1, c2, c3, c4, c5, c6, c7⟩ := hC
  refine c.s_lea_rip hK (by omega) hrip (hdA _) haA fun Y1 _ hK1 hr1 ⟨g1, _⟩ => ?_
  refine c.s_lea_rip hK1 (by omega) hr1 (hdB _) haB fun Y2 _ hK2 hr2 ⟨g2, _⟩ => ?_
  refine c.s_cmov hK2 (by omega) hr2 (hcm _) fun Y3 _ hK3 hr3 g3 => ?_
  refine c.ret hK3 (calleeOf ?_) (by omega) hr3 (hret _) ?_
  · rcases hr with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    · rw [g3]
      split <;> simp [g2, g1, c1, c2, c3, c4, c5, c6, c7]
  · show Returns prof vs Y3.cpu.gpr.rax
    rcases hr with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rw [g3]
      split
      · simpa [g2, g1] using pA
      · simpa [g2, g1] using pB
    · rw [g3]
      split
      · simpa [g2, g1] using pB
      · simpa [g2, g1] using pA

/-- A variant of the list, with features the processor has. -/
theorem Returns.of_mem {v : BitVec 64} {fs : List (Features → Bool)} (hm : (v, fs) ∈ vs)
    (hf : ∀ f ∈ fs, f prof.feat = true) : Returns prof vs v :=
  ⟨(v, fs), hm, rfl, hf⟩

end FV7z.Glibc
