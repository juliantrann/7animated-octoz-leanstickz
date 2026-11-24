import FV7z.Ctor.Ret
/-!
# `AtCtor` from the constructors not yet done (PLAN.md §M, constructors)

`at_ctor`: `AtCtor` with the invariant `Jg` (`Jc` and a further `G`), the constructors done (`Done`: the 64 of
`leas` by `lea_runs`, the 8 of `chains` by `chain_runs`, `csuTg 12` by `runs12`), from the `Csu.Runs` of the others
for `Jg`, a table `spec` of their stores, and the run from `main` on. `cnt_zero`: the registrars' counts are 0 at
the start (its `hz`).
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
  have hz : ∀ i < 4, V (Addr.add (BitVec.ofNat 64 x) i) = 0 := fun i hi => by
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

/-- `Jc` and a further invariant `G` of the global state the constructors not `Done` need (the list of exit
functions, …). -/
def Jg (V : Addr → Byte) (sp : Nat) (spec : Nat → CSpec) (G : Nat → (Addr → Byte) → Prop) (m : Nat)
    (W : Addr → Byte) : Prop :=
  Jc V sp spec m W ∧ G m W

/-- `AtCtor` from the constructors not `Done`, for `Jg` with a `G` that `__libc_csu_init`'s stores to its frame
keep, `frame_dummy`'s stores give at `3`, and the constructors `Done` keep (they store only to the registrars' tables
and below `sp - 64`). -/
theorem at_ctor {K : Ctx} {fb : Addr} {V : Addr → Byte} {spec : Nat → CSpec} {G : Nat → (Addr → Byte) → Prop}
    {sp : Addr} (esp : K.bp + 112#64 - 8#64 = sp) (c : Seg prof F Wl L s₀ o)
    (hC : Csu.Env F Wl L sp csuTg) (hin : CodeIn L sti_at sti)
    (hR : ∀ r, RegSpec prof F Wl L s₀ o (regAt r) (regCnt r) (regTab r) (regMax r))
    (hinR : ∀ r, CodeIn L (regAt r) (regCode r)) (hinN : CodeIn L nret_at nret)
    (hst : ∀ i < 8, Foot Wl (Addr.add (K.bp + 112#64 - 8#64 - 64#64 - 8 - 8) i))
    (hbp : K.bp.toNat + 392 ≤ 2 ^ 64) (hS : 8013728 + 136 ≤ sp.toNat)
    (hz : ∀ r < 3, rdd(V, regCnt r) = 0)
    (hD : ∀ k, (spec k).Dep) (hT : ∀ k, ∀ x ∈ (spec k).wr, ∀ y ∈ tabs, x.2 ≤ y.1 ∨ y.2 ≤ x.1)
    (hB : ∀ k, ∀ x ∈ (spec k).wr, x.2 ≤ sp.toNat - 136)
    (hE : ∀ k, ∀ x ∈ (spec k).wr, x.2 ≤ 8013720 ∨ 8013728 ≤ x.1)
    (hs : ∀ m W, Done m → (spec m).post W)
    (hGo : ∀ m W W', G m W → Raf.Out (sp.toNat - 64) sp.toNat W W' → G m W')
    (hG3 : ∀ W W', Near (sp.toNat - 136) (sp.toNat + 8) V W →
      Rfi.Dat (sp.toNat - 64 - 72) (sp.toNat - 64) 7947808#64 7388000#64 W W' → G 3 W')
    (hGd : ∀ m W W', Done m → G m W → (∀ a : Addr, (a.toNat < 7981024 ∨ 7991300 ≤ a.toNat) →
      (a.toNat < sp.toNat - 64 - 16 ∨ sp.toNat - 64 - 8 ≤ a.toNat) → W' a = W a) →
      G (m + 1) W')
    (hO : ∀ m, 3 ≤ m → m < 104 → ¬ Done m →
      Csu.Runs prof F Wl L s₀ o gev gP gE (Jg V sp.toNat spec G) sp
        (((K.argc.setWidth 64).setWidth 32).setWidth 64) K.argv rdq(V, 8013720#64) m (csuTg m))
    (hmain : ∀ (Vm V₁ : Addr → Byte) (Z' : State) (t' : Nat), KeptW Wl s₀ Z' → Agree F Z'.proc.mm.mem Vm →
      Jg V sp.toNat spec G 104 V₁ →
      (∀ a : Addr, ¬ ((K.bp + 112#64).toNat - 16 ≤ a.toNat ∧ a.toNat < (K.bp + 112#64).toNat) →
        ¬ ((K.bp + 112#64).toNat + 112 ≤ a.toNat ∧ a.toNat < (K.bp + 112#64).toNat + 208) →
        ¬ (0x7a84c0 ≤ a.toNat ∧ a.toNat < 0x7a84e8) → ¬ (fb.toNat + 768 ≤ a.toNat ∧ a.toNat < fb.toNat + 776) →
        Vm a = V₁ a) →
      rdq(Vm, K.bp + 112#64 - 8#64) = lsm_at.add 1168 →
      Z'.cpu.rip = K.main → Z'.cpu.gpr.rsp = K.bp + 112#64 - 8#64 → Z'.cpu.gpr.rdi = K.argc.setWidth 64 →
      Z'.cpu.gpr.rsi = K.argv → Z'.cpu.gpr.rdx = rdq(V, 8013720#64) → GoG prof L o gev gP gE Z' t') :
    AtCtor prof F Wl L s₀ o gev gP gE K fb V := by
  subst esp
  have hs0 := hC.s0
  have hs8 := hC.s8
  have n := Csu.sp_n hs0
  have e8 := add8_toNat K.bp hbp
  have hout : ∀ m W W', ChainOut (K.bp + 112#64 - 8#64 - 64#64) (calls m) W W' → ∀ a : Addr,
      (a.toNat < 7981024 ∨ 7991300 ≤ a.toNat) →
      (a.toNat < (K.bp + 112#64 - 8#64).toNat - 64 - 16 ∨ (K.bp + 112#64 - 8#64).toNat - 64 - 8 ≤ a.toNat) →
      W' a = W a :=
    fun m W W' hO a h1 h2 => ChainOut.out (by rw [n]; omega) h1 (by rw [n]; exact h2) _ W W' hO
  refine ⟨Jg V (K.bp + 112#64 - 8#64).toNat spec G,
    fun m _ W W' hJ ho => ⟨Jc_out (by omega) hD hB hJ.1 ho, hGo m W W' hJ.2 ho⟩,
    fun W W' _ hN hd => ⟨Jc_three (by omega) hz hN hd, hG3 W W' hN hd⟩, fun m hm hm' => ?_,
    fun W hJ a ha => Jc_end hS hB hE hJ.1 a (by rw [e8] at ha; omega), hmain⟩
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
    refine ⟨Jc_chain (S := K.bp + 112#64 - 8#64 - 64#64) hm (by rw [n]; omega) (by omega) hc hF hD hT hB
      (fun W => hs _ W (.inl ⟨_, hx, rfl⟩)) hJ.1 hO', hGd _ W W' (.inl ⟨_, hx, rfl⟩) hJ.2 ?_⟩
    exact hout _ W W' (by rw [hc]; exact hO')
  by_cases h2 : ∃ x ∈ chains, x.1 = m
  · obtain ⟨⟨m', j, cs⟩, hx, e⟩ := h2
    dsimp only at e
    subst e
    have hc := calls_chain _ hx
    obtain ⟨htg, hpro, hcs⟩ := chain_at prof _ hx
    dsimp only at hc htg hpro hcs
    rw [hc] at hF
    refine chain_runs c hC hin htg hpro hcs hR hinR hst (by omega) fun W W' hJ hO' => ?_
    refine ⟨Jc_chain hm (by rw [n]; omega) (by omega) hc hF hD hT hB (fun W => hs _ W (.inr (.inl ⟨_, hx, rfl⟩)))
      hJ.1 hO', hGd _ W W' (.inr (.inl ⟨_, hx, rfl⟩)) hJ.2 ?_⟩
    exact hout _ W W' (by rw [hc]; exact hO')
  by_cases h3 : m = 12
  · subst h3
    exact runs12 c hC hin hinN fun W hJ =>
      ⟨Jc_nop (S := K.bp + 112#64 - 8#64 - 64#64) hm (by rw [n]; omega) (by omega) calls12 hD hT hB
        (fun W => hs _ W (.inr (.inr rfl))) hJ.1, hGd 12 W W (.inr (.inr rfl)) hJ.2 fun _ _ _ => rfl⟩
  exact hO m hm hm' fun h => h.elim h1 fun h => h.elim h2 h3

end FV7z.Ctor
