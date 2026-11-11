import FV7z.Glibc.Resolvers
/-!
# The theorem of `checks/ifunc-resolvers` (PLAN.md G2, "Dispatch theo CPUID")

Under the name and statement of `Challenges/V2606/Resolvers.lean`: each resolver of `Glibc.V2606.resolvers` is, at
its address in the file, bytes (`Res.rADDR_pin`) of a shape whose theorem says it picks a variant the processor has.
-/
namespace FV7z.V2606
open ZellicX86

/-- A resolver of the list, from its bytes in the file and its theorem. -/
theorem of_holds {a n : Nat} {c0 : List Byte} {vs : Glibc.Variants} (pin : Exe.bytesAt zzs.blob a n = some c0)
    (h : ∀ (L : List (Addr × List Byte)) (prof : Profile), prof.Consistent → Glibc.Chain prof →
      CodeIn L (BitVec.ofNat 64 a) c0 → ImplementsCall prof (BitVec.ofNat 64 a) L (Glibc.resolverK prof vs)) :
    ∀ code, Exe.bytesAt zzs.blob a n = some code →
    ∀ (L : List (Addr × List Byte)) (prof : Profile), prof.Consistent → Glibc.Chain prof →
      CodeIn L (BitVec.ofNat 64 a) code → ImplementsCall prof (BitVec.ofNat 64 a) L (Glibc.resolver prof vs) := by
  intro code hb L prof hc hch hin
  rw [pin] at hb
  obtain rfl := Option.some.inj hb
  exact Leaf.leaf_of_leafK (h L prof hc hch hin)

theorem resolvers_hold : ∀ r ∈ Glibc.V2606.resolvers, ∀ code, Exe.bytesAt zzs.blob r.1 r.2.1 = some code →
    ∀ (L : List (Addr × List Byte)) (prof : Profile), prof.Consistent → Glibc.Chain prof →
      CodeIn L (BitVec.ofNat 64 r.1) code → ImplementsCall prof (BitVec.ofNat 64 r.1) L (Glibc.resolver prof r.2.2) := by
  intro r hr
  simp only [Glibc.V2606.resolvers, List.mem_cons, List.mem_nil_iff, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact of_holds Glibc.Res.r636090_pin Glibc.Res.r636090_holds
  · exact of_holds Glibc.Res.r6a1250_pin Glibc.Res.r6a1250_holds
  · exact of_holds Glibc.Res.r6a1290_pin Glibc.Res.r6a1290_holds
  · exact of_holds Glibc.Res.r637440_pin Glibc.Res.r637440_holds
  · exact of_holds Glibc.Res.r6369b0_pin Glibc.Res.r6369b0_holds
  · exact of_holds Glibc.Res.r65d1f0_pin Glibc.Res.r65d1f0_holds
  · exact of_holds Glibc.Res.r6360d0_pin Glibc.Res.r6360d0_holds
  · exact of_holds Glibc.Res.r637480_pin Glibc.Res.r637480_holds
  · exact of_holds Glibc.Res.r636170_pin Glibc.Res.r636170_holds
  · exact of_holds Glibc.Res.r6652e0_pin Glibc.Res.r6652e0_holds
  · exact of_holds Glibc.Res.r6c7320_pin Glibc.Res.r6c7320_holds
  · exact of_holds Glibc.Res.r6c7300_pin Glibc.Res.r6c7300_holds
  · exact of_holds Glibc.Res.r635db0_pin Glibc.Res.r635db0_holds
  · exact of_holds Glibc.Res.r636990_pin Glibc.Res.r636990_holds
  · exact of_holds Glibc.Res.r635cf0_pin Glibc.Res.r635cf0_holds
  · exact of_holds Glibc.Res.r6cd120_pin Glibc.Res.r6cd120_holds
  · exact of_holds Glibc.Res.r635d50_pin Glibc.Res.r635d50_holds
  · exact of_holds Glibc.Res.r636c80_pin Glibc.Res.r636c80_holds
  · exact of_holds Glibc.Res.r6c7340_pin Glibc.Res.r6c7340_holds
  · exact of_holds Glibc.Res.r6c7390_pin Glibc.Res.r6c7390_holds
  · exact of_holds Glibc.Res.r636ce0_pin Glibc.Res.r636ce0_holds
  · exact of_holds Glibc.Res.r698c50_pin Glibc.Res.r698c50_holds
  · exact of_holds Glibc.Res.r65d650_pin Glibc.Res.r65d650_holds
  · exact of_holds Glibc.Res.r635ca0_pin Glibc.Res.r635ca0_holds
  · exact of_holds Glibc.Res.r636110_pin Glibc.Res.r636110_holds
  · exact of_holds Glibc.Res.r6c7810_pin Glibc.Res.r6c7810_holds
  · exact of_holds Glibc.Res.r636bc0_pin Glibc.Res.r636bc0_holds
  · exact of_holds Glibc.Res.r636d30_pin Glibc.Res.r636d30_holds
  · exact of_holds Glibc.Res.r636a60_pin Glibc.Res.r636a60_holds
  · exact of_holds Glibc.Res.r636b20_pin Glibc.Res.r636b20_holds
  · exact of_holds Glibc.Res.r6369f0_pin Glibc.Res.r6369f0_holds

/-- The same with `Glibc.resolverK`, which also says what the resolver kept: what `apply_irel`'s run goes on with
after each call (`CpuFeat/Irel.lean`). -/
theorem resolvers_holdK : ∀ r ∈ Glibc.V2606.resolvers, ∃ code, Exe.bytesAt zzs.blob r.1 r.2.1 = some code ∧
    0 < code.length ∧ ∀ (L : List (Addr × List Byte)) (prof : Profile), prof.Consistent → Glibc.Chain prof →
      CodeIn L (BitVec.ofNat 64 r.1) code →
      ImplementsCall prof (BitVec.ofNat 64 r.1) L (Glibc.resolverK prof r.2.2) := by
  intro r hr
  simp only [Glibc.V2606.resolvers, List.mem_cons, List.mem_nil_iff, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨_, Glibc.Res.r636090_pin, by decide +kernel, Glibc.Res.r636090_holds⟩
  · exact ⟨_, Glibc.Res.r6a1250_pin, by decide +kernel, Glibc.Res.r6a1250_holds⟩
  · exact ⟨_, Glibc.Res.r6a1290_pin, by decide +kernel, Glibc.Res.r6a1290_holds⟩
  · exact ⟨_, Glibc.Res.r637440_pin, by decide +kernel, Glibc.Res.r637440_holds⟩
  · exact ⟨_, Glibc.Res.r6369b0_pin, by decide +kernel, Glibc.Res.r6369b0_holds⟩
  · exact ⟨_, Glibc.Res.r65d1f0_pin, by decide +kernel, Glibc.Res.r65d1f0_holds⟩
  · exact ⟨_, Glibc.Res.r6360d0_pin, by decide +kernel, Glibc.Res.r6360d0_holds⟩
  · exact ⟨_, Glibc.Res.r637480_pin, by decide +kernel, Glibc.Res.r637480_holds⟩
  · exact ⟨_, Glibc.Res.r636170_pin, by decide +kernel, Glibc.Res.r636170_holds⟩
  · exact ⟨_, Glibc.Res.r6652e0_pin, by decide +kernel, Glibc.Res.r6652e0_holds⟩
  · exact ⟨_, Glibc.Res.r6c7320_pin, by decide +kernel, Glibc.Res.r6c7320_holds⟩
  · exact ⟨_, Glibc.Res.r6c7300_pin, by decide +kernel, Glibc.Res.r6c7300_holds⟩
  · exact ⟨_, Glibc.Res.r635db0_pin, by decide +kernel, Glibc.Res.r635db0_holds⟩
  · exact ⟨_, Glibc.Res.r636990_pin, by decide +kernel, Glibc.Res.r636990_holds⟩
  · exact ⟨_, Glibc.Res.r635cf0_pin, by decide +kernel, Glibc.Res.r635cf0_holds⟩
  · exact ⟨_, Glibc.Res.r6cd120_pin, by decide +kernel, Glibc.Res.r6cd120_holds⟩
  · exact ⟨_, Glibc.Res.r635d50_pin, by decide +kernel, Glibc.Res.r635d50_holds⟩
  · exact ⟨_, Glibc.Res.r636c80_pin, by decide +kernel, Glibc.Res.r636c80_holds⟩
  · exact ⟨_, Glibc.Res.r6c7340_pin, by decide +kernel, Glibc.Res.r6c7340_holds⟩
  · exact ⟨_, Glibc.Res.r6c7390_pin, by decide +kernel, Glibc.Res.r6c7390_holds⟩
  · exact ⟨_, Glibc.Res.r636ce0_pin, by decide +kernel, Glibc.Res.r636ce0_holds⟩
  · exact ⟨_, Glibc.Res.r698c50_pin, by decide +kernel, Glibc.Res.r698c50_holds⟩
  · exact ⟨_, Glibc.Res.r65d650_pin, by decide +kernel, Glibc.Res.r65d650_holds⟩
  · exact ⟨_, Glibc.Res.r635ca0_pin, by decide +kernel, Glibc.Res.r635ca0_holds⟩
  · exact ⟨_, Glibc.Res.r636110_pin, by decide +kernel, Glibc.Res.r636110_holds⟩
  · exact ⟨_, Glibc.Res.r6c7810_pin, by decide +kernel, Glibc.Res.r6c7810_holds⟩
  · exact ⟨_, Glibc.Res.r636bc0_pin, by decide +kernel, Glibc.Res.r636bc0_holds⟩
  · exact ⟨_, Glibc.Res.r636d30_pin, by decide +kernel, Glibc.Res.r636d30_holds⟩
  · exact ⟨_, Glibc.Res.r636a60_pin, by decide +kernel, Glibc.Res.r636a60_holds⟩
  · exact ⟨_, Glibc.Res.r636b20_pin, by decide +kernel, Glibc.Res.r636b20_holds⟩
  · exact ⟨_, Glibc.Res.r6369f0_pin, by decide +kernel, Glibc.Res.r6369f0_holds⟩

end FV7z.V2606
