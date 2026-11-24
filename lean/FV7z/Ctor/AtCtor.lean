import FV7z.Ctor.Ret
/-!
# `AtCtor` from the constructors not yet done (PLAN.md §M, constructors)

`at_ctor`: `AtCtor` with the invariant `Jc`, the constructors done (`Done`: the 64 of `leas` by `lea_runs`, the 8
of `chains` by `chain_runs`, `csuTg 12` by `runs12`), from the `Csu.Runs` of the others for `Jc`, a table `spec` of
their stores, and the run from `main` on. `cnt_zero`: the registrars' counts are 0 at the start (its `hz`).
-/
namespace FV7z.Ctor
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn FV7z.Start

variable {prof : Profile} {F : Footprint} {Wl : List Rgn} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}

/-- The constructors done here. -/
def Done (m : Nat) : Prop := (∃ x ∈ leas, x.1 = m) ∨ (∃ x ∈ chains, x.1 = m) ∨ m = 12

theorem add8_toNat (b : Addr) (h : b.toNat + 392 ≤ 2 ^ 64) : (b + 112#64).toNat = (b + 112#64 - 8#64).toNat + 8 := by
  bv_omega

/-- Four bytes of counts in `.bss` that are the image's are 0. -/
theorem cnt_zero1 {V V₀ : Addr → Byte} (hV : ∀ x : Addr, Ndi.CntN x.toNat → V x = V₀ x) (hB : Bss V₀) {x : Nat}
    (hx : ∀ i < 4, Ndi.CntN (x + i)) (h1 : 0x7945d0 ≤ x) (h2 : x + 4 ≤ 0x7a86c0) : rdd(V, BitVec.ofNat 64 x) = 0 := by
  have hz : ∀ i < 4, V ((BitVec.ofNat 64 x).add i) = 0 := fun i hi => by
    have t := ofNat_add_toNat (x := x) hi (by omega)
    rw [hV _ (by rw [t]; exact hx i hi)]
    exact hB _ (by rw [t]; omega) (by rw [t]; omega)
  rw [rd_zero hz]
  rfl

/-- The registrars' counts are 0 in bytes whose counts are the image's (`RetAt.cnt`). -/
theorem cnt_zero {V V₀ : Addr → Byte} (hV : ∀ x : Addr, Ndi.CntN x.toNat → V x = V₀ x) (hB : Bss V₀) :
    ∀ r < 3, rdd(V, regCnt r) = 0
  | 0, _ => cnt_zero1 (x := 7991296) hV hB (fun i hi => by unfold Ndi.CntN; omega) (by decide) (by decide)
  | 1, _ => cnt_zero1 (x := 7981824) hV hB (fun i hi => by unfold Ndi.CntN; omega) (by decide) (by decide)
  | 2, _ => cnt_zero1 (x := 7981280) hV hB (fun i hi => by unfold Ndi.CntN; omega) (by decide) (by decide)
  | _ + 3, h => absurd h (by omega)

/-- `AtCtor` from the constructors not `Done`. -/
theorem at_ctor {K : Ctx} {fb : Addr} {V : Addr → Byte} {spec : Nat → CSpec} (c : Seg prof F Wl L s₀ o)
    (hC : Csu.Env F Wl L (K.bp + 112#64 - 8#64) csuTg) (hin : CodeIn L sti_at sti)
    (hR : ∀ r, RegSpec prof F Wl L s₀ o (regAt r) (regCnt r) (regTab r) (regMax r))
    (hinR : ∀ r, CodeIn L (regAt r) (regCode r)) (hinN : CodeIn L nret_at nret)
    (hst : ∀ i < 8, Foot Wl (Addr.add (K.bp + 112#64 - 8#64 - 64#64 - 8 - 8) i))
    (hbp : K.bp.toNat + 392 ≤ 2 ^ 64) (hS : 8013728 + 136 ≤ (K.bp + 112#64 - 8#64).toNat)
    (hz : ∀ r < 3, rdd(V, regCnt r) = 0)
    (hD : ∀ k, (spec k).Dep) (hT : ∀ k, ∀ x ∈ (spec k).wr, x.2 ≤ 7981024 ∨ 7991300 ≤ x.1)
    (hB : ∀ k, ∀ x ∈ (spec k).wr, x.2 ≤ (K.bp + 112#64 - 8#64).toNat - 136)
    (hE : ∀ k, ∀ x ∈ (spec k).wr, x.2 ≤ 8013720 ∨ 8013728 ≤ x.1)
    (hs : ∀ m W, Done m → (spec m).post W)
    (hO : ∀ m, 3 ≤ m → m < 104 → ¬ Done m →
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
  have e8 := add8_toNat K.bp hbp
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
    exact Jc_chain hm (by rw [n]; omega) (by omega) hc hF hD hT hB (fun W => hs _ W (.inr (.inl ⟨_, hx, rfl⟩))) hJ hO'
  by_cases h3 : m = 12
  · subst h3
    exact runs12 c hC hin hinN fun W hJ =>
      Jc_nop (S := K.bp + 112#64 - 8#64 - 64#64) hm (by rw [n]; omega) (by omega) calls12 hD hT hB
        (fun W => hs _ W (.inr (.inr rfl))) hJ
  exact hO m hm hm' fun h => h.elim h1 fun h => h.elim h2 h3

end FV7z.Ctor
