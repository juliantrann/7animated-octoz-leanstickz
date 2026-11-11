import FV7z.Memcmp.Avx2Movbe.Large
import FV7z.Memcmp.Avx2Movbe.Small
/-!
# `__memcmp_avx2_movbe` of `7zzs` meets `memcmp`'s contract (PLAN.md G2.1)

From the entry: `ENDBR64`, `CMP rdx, 32`, `JB 432` (fewer than 32 bytes, `Small.lean`), else `14` (`Large.lean`).
The theorem: on a processor with AVX, AVX2 and MOVBE, the 980 bytes of `7zzs` at `0x63f660`, wherever they lie,
implement `memcmp` as Zellic's `Memcmp.contract` states it.
-/
namespace FV7z.MemcmpAvx2
open ZellicX86 Decode Memcmp MemcmpCall Order

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {ra : Addr} {o : Oracle} {e : Addr}

/-- The run of a call, from its first instruction. -/
theorem entry (x : Ctx prof L s₀ ra o e) {t : Nat} : Go prof L s₀ ra o s₀ t :=
  have hrip : s₀.cpu.rip = e.add 0 := by rw [x.c.call.shape.1]; simp [Addr.add]
  have hC0 : Callee s₀ s₀ := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  x.c.s_endbr (Kept.refl s₀) (by simp [avx2Movbe_length]) hrip (d0 _ x.f) fun Y1 _ hK1 hr1 ⟨g1, _⟩ =>
  x.c.s_cmp_ri hK1 (by simp [avx2Movbe_length]) hr1 (d4 _ x.f) fun Y2 _ hK2 hr2 ⟨g2, _, f2⟩ => by
    have hv := nn_lt s₀
    have hdx' : s₀.cpu.gpr.rdx = BitVec.ofNat 64 (nn s₀) := by simp [nn]
    have hf : Y2.cpu.rflags = subF (rf0 Y1) (BitVec.ofNat 64 (nn s₀)) (BitVec.ofNat 64 32) := by
      rw [f2]; simp only [rv, get_2, g1, BitVec.setWidth_eq, hdx']
    refine x.c.s_jcc hK2 (by simp [avx2Movbe_length]) hr2 (d8 _ x.f) (tgt := 432) (by decide)
      (by simp [avx2Movbe_length]) (fun hc => ?_) (fun hc => ?_)
    · rw [cond2, hf, cf64 _ hv (by decide), decide_eq_true_iff] at hc
      intro Y3 _ hK3 hr3 ⟨g3, _⟩
      have gY : Y3.cpu.gpr = s₀.cpu.gpr := by rw [g3, g2, g1]
      exact at432 x hK3 (hC0.of_gpr (by simp [gY])) hr3 (by rw [gY, addr_add_zero]) (by rw [gY, addr_add_zero])
        (by rw [gY, hdx']) hc
    · rw [cond2, hf, cf64 _ hv (by decide), decide_eq_false_iff_not] at hc
      intro Y3 _ hK3 hr3 ⟨g3, _⟩
      have gY : Y3.cpu.gpr = s₀.cpu.gpr := by rw [g3, g2, g1]
      exact at14 x hK3 (hC0.of_gpr (by simp [gY])) hr3 (by rw [gY]) (by rw [gY]) (by rw [gY]) (by omega)

/-- `__memcmp_avx2_movbe` of `7zzs` 26.06, on a processor with AVX, AVX2 and MOVBE, meets the C standard's contract
for `memcmp`, as Zellic's `Memcmp.contract` states it. -/
theorem avx2Movbe_holds (L : List (Addr × List Byte)) (prof : Profile) (e : Addr) (hF : Feat prof.feat)
    (hin : CodeIn L e avx2Movbe) : ImplementsCall prof e L contract := by
  intro s₀ ra hcall
  exact reachOrEndsIn_of_runsFrom fun o ho t => entry ⟨Call.mk hcall hin ho, hF⟩

end FV7z.MemcmpAvx2
