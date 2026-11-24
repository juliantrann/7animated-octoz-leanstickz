import FV7z.Ctor.Inv
/-!
# `AtCtor` from the constructors not yet done (PLAN.md §M, constructors)

`at_ctor`: `AtCtor` with the invariant `Jc`, the 64 constructors of `leas` (`lea_runs`) and the 8 of `chains`
(`chain_runs`) done, from the `Csu.Runs` of the others for `Jc`, a table `spec` of their stores, and the run from
`main` on.
-/
namespace FV7z.Ctor
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn FV7z.Start

variable {prof : Profile} {F : Footprint} {Wl : List Rgn} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}

theorem add8_toNat (x : Addr) (h : (x - 8#64).toNat + 8 ≤ 2 ^ 64) : x.toNat = (x - 8#64).toNat + 8 := by bv_omega

/-- `AtCtor` from the constructors that are neither in `leas` nor in `chains`. -/
theorem at_ctor {K : Ctx} {fb : Addr} {V : Addr → Byte} {spec : Nat → CSpec} (c : Seg prof F Wl L s₀ o)
    (hC : Csu.Env F Wl L (K.bp + 112#64 - 8#64) csuTg) (hin : CodeIn L sti_at sti)
    (hR : ∀ r, RegSpec prof F Wl L s₀ o (regAt r) (regCnt r) (regTab r) (regMax r))
    (hinR : ∀ r, CodeIn L (regAt r) (regCode r))
    (hst : ∀ i < 8, Foot Wl (Addr.add (K.bp + 112#64 - 8#64 - 64#64 - 8 - 8) i))
    (hS : 8013728 + 136 ≤ (K.bp + 112#64 - 8#64).toNat) (hz : ∀ r < 3, rdd(V, regCnt r) = 0)
    (hD : ∀ k, (spec k).Dep) (hT : ∀ k, ∀ x ∈ (spec k).wr, x.2 ≤ 7981024 ∨ 7991300 ≤ x.1)
    (hB : ∀ k, ∀ x ∈ (spec k).wr, x.2 ≤ (K.bp + 112#64 - 8#64).toNat - 136)
    (hE : ∀ k, ∀ x ∈ (spec k).wr, x.2 ≤ 8013720 ∨ 8013728 ≤ x.1)
    (hs : ∀ m W, ((∃ x ∈ leas, x.1 = m) ∨ ∃ x ∈ chains, x.1 = m) → (spec m).post W)
    (hO : ∀ m, 3 ≤ m → m < 104 → (¬ ∃ x ∈ leas, x.1 = m) → (¬ ∃ x ∈ chains, x.1 = m) →
      Csu.Runs prof F Wl L s₀ o gev gP gE (Jc V (K.bp + 112#64 - 8#64).toNat spec) (K.bp + 112#64 - 8#64)
        (((K.argc.setWidth 64).setWidth 32).setWidth 64) K.argv rdq(V, 8013720#64) m (csuTg m))
    (hmain : ∀ (Vm V₁ : Addr → Byte) (Z' : State) (t' : Nat), KeptW Wl s₀ Z' → Agree F Z'.proc.mm.mem Vm →
      Jc V (K.bp + 112#64 - 8#64).toNat spec 104 V₁ →
      (∀ a : Addr, ¬ ((K.bp + 112#64).toNat - 16 ≤ a.toNat ∧ a.toNat < (K.bp + 112#64).toNat) →
        ¬ ((K.bp + 112#64).toNat + 112 ≤ a.toNat ∧ a.toNat < (K.bp + 112#64).toNat + 208) →
        ¬ (0x7a84c0 ≤ a.toNat ∧ a.toNat < 0x7a84e8) → ¬ (fb.toNat + 768 ≤ a.toNat ∧ a.toNat < fb.toNat + 776) →
        Vm a = V₁ a) →
      rdq(Vm, K.bp + 112#64 - 8#64) = lsm_at.add 1168 →
      Z'.cpu.rip = K.main → Z'.cpu.gpr.rsp = K.bp + 112#64 - 8#64 → Z'.cpu.gpr.rdi = K.argc.setWidth 64 →
      Z'.cpu.gpr.rsi = K.argv → Z'.cpu.gpr.rdx = rdq(V, 8013720#64) → GoG prof L o gev gP gE Z' t') :
    AtCtor prof F Wl L s₀ o gev gP gE K fb V := by
  have hs0 := hC.s0
  have hs8 := hC.s8
  have n := Csu.sp_n hs0
  have e8 := add8_toNat (K.bp + 112#64) hs8
  refine ⟨Jc V (K.bp + 112#64 - 8#64).toNat spec, fun m _ W W' hJ ho => Jc_out (by omega) hD hB hJ ho,
    fun W W' _ hN hd => Jc_three (by omega) hz hN hd, fun m hm hm' => ?_,
    fun W hJ a ha => Jc_end hS hB hE hJ a (by rw [e8] at ha; omega), hmain⟩
  have hF := fits_of (fits_all m hm')
  by_cases h1 : ∃ x ∈ leas, x.1 = m
  · obtain ⟨⟨m', j, r, A⟩, hx, e⟩ := h1
    dsimp only at e
    subst e
    have hc := calls_lea _ hx
    dsimp only at hc
    rw [hc] at hF
    have hci := cnt_in r
    refine lea_runs c hC hin hx (hR r) (hinR r) (by omega) fun W W' hJ hO' => ?_
    exact Jc_chain (S := K.bp + 112#64 - 8#64 - 64#64) hm (by rw [n]; omega) (by omega) hc hF hD hT hB
      (fun W => hs _ W (.inl ⟨_, hx, rfl⟩)) hJ hO'
  by_cases h2 : ∃ x ∈ chains, x.1 = m
  · obtain ⟨⟨m', j, cs⟩, hx, e⟩ := h2
    dsimp only at e
    subst e
    have hc := calls_chain _ hx
    obtain ⟨htg, hpro, hcs⟩ := chain_at prof _ hx
    dsimp only at hc htg hpro hcs
    rw [hc] at hF
    refine chain_runs c hC hin htg hpro hcs hR hinR hst (by omega) fun W W' hJ hO' => ?_
    exact Jc_chain hm (by rw [n]; omega) (by omega) hc hF hD hT hB (fun W => hs _ W (.inr ⟨_, hx, rfl⟩)) hJ hO'
  exact hO m hm hm' h1 h2

end FV7z.Ctor
