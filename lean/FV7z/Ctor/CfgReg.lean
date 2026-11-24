import FV7z.Ctor.BlkRet
import FV7z.Ctor.Runs
import FV7z.Ctor.StSpec
/-!
# Constructors with loops that end by jumping to a registrar (PLAN.md §M, constructors)

- `jmp_reg`: `jmp R` at offset `j` of `code` (at `e`), `R` a registrar and `rdi` the argument `A`: the run gets to the
  constructor's caller with `RegOut` of the bytes for `A` and the registers a call keeps.
- `cfg_reg_runs`: code with loops at `e.add j` up to such a `jmp` at `jl` is a function as `Csu.csu_ok` asks: by
  `Seg.cfg` over its cut points (as `cfg_runs`) up to the `jmp` with `rdi = A`, the registers a call keeps and bytes
  `R V₀`, then `jmp_reg`; the invariant goes from `m` to `m + 1` through `R` and then `RegOut`.
- `Jc_wreg`, `jg_wreg`: such a constructor (its `calls` the one call of `tails`) keeps `Jc` and `Jg` when it stores
  only to its `wr` before the call.
-/
namespace FV7z.Ctor
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn FV7z.Start

variable {prof : Profile} {F : Footprint} {Wl : List Rgn} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}

/-- `jmp R` with `rdi` the argument `A`, `R` a registrar: to the caller, `RegOut` of the bytes for `A`, the registers
a call keeps. -/
theorem jmp_reg {X : State} {t : Nat} {V : Addr → Byte} {j A rel : Nat} {e ra cnt tab : Addr} {max : Nat}
    {code codeR : List Byte} (hd : Dec prof.feat code j (FV7z.mk .jmp 64 [.rel rel] 5)) (hj : j < code.length)
    (htgt : e.add (j + 5) + BitVec.ofNat 64 rel = ra.add 0)
    (c : Seg prof F Wl L s₀ o) (hin : CodeIn L e code) (hinR : CodeIn L ra codeR) (hR0 : 0 < codeR.length)
    (hR : RegSpec prof F Wl L s₀ o ra cnt tab max)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = e.add j)
    (hdi : X.cpu.gpr.rdi = BitVec.ofNat 64 A)
    (hl : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsp i)) (hs8 : X.cpu.gpr.rsp.toNat + 8 ≤ 2 ^ 64)
    (hap : X.cpu.gpr.rsp.toNat + 8 ≤ tab.toNat ∨ cnt.toNat + 4 ≤ X.cpu.gpr.rsp.toNat)
    {e₂ : Addr} {code₂ : List Byte} {j₂ : Nat} (hin₂ : CodeIn L e₂ code₂) (h₂ : j₂ < code₂.length)
    (hra : rdq(V, X.cpu.gpr.rsp) = e₂.add j₂)
    (k : ∀ V' Z t', KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V' → RegOut cnt tab max (BitVec.ofNat 64 A) V V' →
      Z.cpu.rip = e₂.add j₂ → Osv.Back X.cpu.gpr Z.cpu.gpr → GoG prof L o gev gP gE Z t') :
    GoG prof L o gev gP gE X t := by
  refine c.s_jmp_x hK hA hin hj hrip hd hinR hR0 htgt ?_
  rintro Y t₁ hKY hAY ⟨hrY, hgY⟩
  have hsp : Y.cpu.gpr.rsp = X.cpu.gpr.rsp := by rw [hgY]
  have hdi' : Y.cpu.gpr.rdi = BitVec.ofNat 64 A := by rw [hgY]; exact hdi
  refine hR hKY hAY (by rw [hrY, addr_add_zero]) (by rw [hsp]; exact hl) (by rw [hsp]; exact hs8)
    (by rw [hsp]; exact hap) hin₂ h₂ (by rw [hsp]; exact hra) fun V' Z t' hKZ hAZ hO hrZ hbk => ?_
  rw [hdi'] at hO
  refine k V' Z t' hKZ hAZ hO hrZ ?_
  obtain ⟨b1, b2, b3, b4, b5, b6, b7⟩ := hbk
  rw [hgY] at b1 b2 b3 b4 b5 b6 b7
  exact ⟨b1, b2, b3, b4, b5, b6, b7⟩

/-- Code at offset `j` of `code` (at `e`) with loops, up to `jmp R` at `jl` with `rdi = A`, `R` a registrar, is a
function as `Csu.csu_ok` asks: `Seg.cfg` over cut points `W` with an invariant `Inv g₀ V₀` that holds at the entry
and reaches the `jmp` with `rdi = A`, the registers a call keeps and bytes `R V₀`; `R` keeps the frame of
`__libc_csu_init` and its arrays, the registrar's table lies apart from the frame, and the invariant goes from `m` to
`m + 1` through `R` and then `RegOut`. -/
theorem cfg_reg_runs {J : Nat → (Addr → Byte) → Prop} {sp : Addr} {tg : Nat → Addr} {a₀ a₁ a₂ : BitVec 64}
    {m j jl A rel : Nat} {W : Nat → Wpt} {a e ra cnt tab : Addr} {max : Nat} {code codeR : List Byte}
    (c : Seg prof F Wl L s₀ o) (hC : Csu.Env F Wl L sp tg) (hin : CodeIn L e code) (htg : a = e.add j)
    (hW : ∀ ℓ, Sp prof code e ℓ (W ℓ)) (hd : Dec prof.feat code jl (FV7z.mk .jmp 64 [.rel rel] 5))
    (hjl : jl < code.length) (htgt : e.add (jl + 5) + BitVec.ofNat 64 rel = ra.add 0)
    (hinR : CodeIn L ra codeR) (hR0 : 0 < codeR.length) (hR : RegSpec prof F Wl L s₀ o ra cnt tab max)
    (hL : Lay cnt tab max) (hA7 : 7830224 ≤ tab.toNat)
    (hfar : sp.toNat + 8 ≤ tab.toNat ∨ cnt.toNat + 4 ≤ sp.toNat - 64)
    (R : (Addr → Byte) → (Addr → Byte) → Prop)
    (Inv : Gprs → (Addr → Byte) → Nat → Nat → Gprs → Rflags → (Addr → Byte) → Prop)
    (h0 : ∀ g f V, ∃ n, Inv g V j n g f V)
    (vc : ∀ g₀ V₀ ℓ n g f V, Inv g₀ V₀ ℓ n g f V → W ℓ F Wl (fun j' g' f' V' =>
      (∃ n' < n, Inv g₀ V₀ j' n' g' f' V') ∨ (j' = jl ∧ Kp g₀ g' ∧ g'.rdi = BitVec.ofNat 64 A ∧ R V₀ V')) g f V)
    (hRk : ∀ V V', R V V' → ∀ a : Addr, (sp.toNat - 64 ≤ a.toNat ∧ a.toNat < sp.toNat + 8) ∨
      (7829400 ≤ a.toNat ∧ a.toNat < 7830224) → V' a = V a)
    (hJ : ∀ V V' V'', J m V → R V V' → RegOut cnt tab max (BitVec.ofNat 64 A) V' V'' → J (m + 1) V'') :
    Csu.Runs prof F Wl L s₀ o gev gP gE J sp a₀ a₁ a₂ m a := by
  intro X t V j₂ hK hA hI hr hsp _ hj₂ hra k
  obtain ⟨n₀, h₀⟩ := h0 X.cpu.gpr X.cpu.rflags V
  have hs0 := hC.s0
  have hs8 := hC.s8
  have n := Csu.sp_n hs0
  have ap := hL.ap
  refine c.cfg hin hW (Inv X.cpu.gpr V)
    (fun j' g' _ V' => j' = jl ∧ Kp X.cpu.gpr g' ∧ g'.rdi = BitVec.ofNat 64 A ∧ R V V')
    (vc X.cpu.gpr V) ?_ n₀ j hK hA (hr.trans htg) h₀
  rintro j' g fl V' ⟨rfl, hKp, hdi, hRV⟩ Y t₁ hKY hAY hrY rfl -
  have hsY : Y.cpu.gpr.rsp = sp - 64#64 := by rw [hKp.1]; exact hsp
  have hl : ∀ i < 8, Foot F.data (Addr.add Y.cpu.gpr.rsp i) := fun i hi => by
    rw [hsY]
    exact c.hws _ (hC.st i (by omega))
  have h8 : Y.cpu.gpr.rsp.toNat + 8 ≤ 2 ^ 64 := by rw [hsY, n]; omega
  have hap : Y.cpu.gpr.rsp.toNat + 8 ≤ tab.toNat ∨ cnt.toNat + 4 ≤ Y.cpu.gpr.rsp.toNat := by
    rw [hsY, n]
    omega
  have hraY : rdq(V', Y.cpu.gpr.rsp) = Csu.csu_at.add j₂ := by
    rw [hsY, ← hra]
    exact rdq_eq (by omega) fun a h1 h2 => hRk V V' hRV a (.inl ⟨by omega, by omega⟩)
  refine jmp_reg hd hjl htgt c hin hinR hR0 hR hKY hAY hrY hdi hl h8 hap hC.code hj₂ hraY ?_
  intro V'' Z t' hKZ hAZ hO hrZ hbk
  refine k Z t' V'' hKZ hAZ (hJ V V' V'' hI hRV hO) (fun a ha => ?_) (fun a ha => ?_) hrZ ?_
  · rw [hO.out hL (by omega)]
    exact hRk V V' hRV a (.inl ⟨by omega, ha.2⟩)
  · rw [hO.out hL (by omega)]
    exact hRk V V' hRV a (.inr ha)
  · obtain ⟨k1, k2, k3, k4, k5, k6, k7⟩ := hKp
    obtain ⟨b1, b2, b3, b4, b5, b6, b7⟩ := hbk
    exact ⟨by rw [b1, k1], b2.trans k2, b3.trans k3, b4.trans k4, b5.trans k5, b6.trans k6, b7.trans k7⟩

/-- A constructor whose one registrar call `(r, A)` (its `calls`, with room) comes after stores only to its `wr`
(apart from the tables and from the `wr` of the constructors before it) keeps `Jc`, its `post` true of any bytes. -/
theorem Jc_wreg {V W W' W'' : Addr → Byte} {sp m r A : Nat} {spec : Nat → CSpec} (hm : 3 ≤ m)
    (hc : calls m = [(r, A)]) (hF : Fits (regsAt m) [(r, A)]) (hD : ∀ k, (spec k).Dep)
    (hT : ∀ k, ∀ x ∈ (spec k).wr, ∀ y ∈ tabs, x.2 ≤ y.1 ∨ y.2 ≤ x.1)
    (hX : ∀ k, 3 ≤ k → k < m → ∀ x ∈ (spec k).wr, ∀ y ∈ (spec m).wr, x.2 ≤ y.1 ∨ y.2 ≤ x.1)
    (hs : ∀ W, (spec m).post W) (hJ : Jc V sp spec m W) (hW : ∀ a : Addr, ¬ InR (spec m).wr a.toNat → W' a = W a)
    (hO : RegOut (regCnt r) (regTab r) (regMax r) (BitVec.ofNat 64 A) W' W'') : Jc V sp spec (m + 1) W'' := by
  obtain ⟨hR, hK, hP⟩ := hJ
  have hO' : ChainOut 8000000#64 [(r, A)] W' W'' := hO
  have hi := reg_in r
  refine ⟨?_, fun a h1 h2 h3 h4 => ?_, fun k hk hkm => ?_⟩
  · rw [regsAt_succ hm, hc]
    exact RegsIn.chain (by decide) _ _ W' W'' (hR.far_t fun a ha => hW a fun hw => InR_sep hw (hT m) ha) hF hO'
  · rw [RegOut.out hO (reg_lay r) (by omega), hW a (h4 m hm (by omega))]
    exact hK a h1 h2 h3 fun k hk hkm => h4 k hk (by omega)
  · rcases Nat.lt_or_ge k m with hlt | hge
    · refine hD k W W'' (fun a ha => ?_) (hP k hk hlt)
      rw [RegOut.out hO (reg_lay r) (not_tab r (InR_sep ha (hT k)))]
      exact hW a (InR_sep ha (hX k hk hlt))
    · obtain rfl : k = m := by omega
      exact hs W''

/-- `Jg` from `m` to `m + 1` for `spec m = wrSpec wr`, when the constructor stores only to `wr` (apart from the
tables and the stores before) and then makes its one registrar call `(r, A)`. -/
theorem jg_wreg {V W W' W'' : Addr → Byte} {sp m r A : Nat} {spec : Nat → CSpec} {G : Nat → (Addr → Byte) → Prop}
    {wr : List (Nat × Nat)} (hm : 3 ≤ m) (hc : calls m = [(r, A)]) (hF : Fits (regsAt m) [(r, A)])
    (hspec : spec m = wrSpec wr) (hD : ∀ k, (spec k).Dep)
    (hT : ∀ k, ∀ x ∈ (spec k).wr, ∀ y ∈ tabs, x.2 ≤ y.1 ∨ y.2 ≤ x.1)
    (hXw : ∀ k, 3 ≤ k → k < m → ∀ x ∈ (spec k).wr, ∀ y ∈ wr, x.2 ≤ y.1 ∨ y.2 ≤ x.1)
    (hout : ∀ a : Addr, ¬ InR wr a.toNat → W' a = W a)
    (hO : RegOut (regCnt r) (regTab r) (regMax r) (BitVec.ofNat 64 A) W' W'') (hG : G m W → G (m + 1) W'')
    (hJ : Jg V sp spec G m W) : Jg V sp spec G (m + 1) W'' := by
  obtain ⟨hJc, hG'⟩ := hJ
  refine ⟨Jc_wreg hm hc hF hD hT (fun k hk hkm => ?_) (fun W => ?_) hJc (fun a ha => hout a ?_) hO, hG hG'⟩
  · rw [hspec]
    exact hXw k hk hkm
  · rw [hspec]
    trivial
  · rw [hspec] at ha
    exact ha

end FV7z.Ctor
