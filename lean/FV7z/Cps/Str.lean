import FV7z.Cps.Ev
/-!
# `NCommandLineParser::CParser::ParseString`: the `kString` path (PLAN.md §M, M1)

From 514 (`r12` = the switch result `e24 sp b`): the `UString` of the rest of `s` (`k529`), the growth check of
`PostStrings` (534; the `ja` at 551 to the throw), the new buffer (`k587`), the copy (`k804`), the old buffer freed
(`k621`), the new `_items` and `_capacity` (626), the item (`k641`, `k655`), `_size` + 1 (660), the slot (678), the
local freed (`k696`), to 317.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
open FV7z.Api (P6 Stk KS)
namespace FV7z.Cps
set_option linter.unusedVariables false

section Runs
variable {prof : Profile} {F : Footprint} {Wl : List Rgn} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {fb S : Addr} {g0 : Gprs} {e₂ : Addr} {code₂ : List Byte} {j₂ : Nat} {I : (Addr → Byte) → Prop}
  {Ok : Addr → Nat → Prop} {ch : Addr} {ln : BitVec 32} {sp : Addr} {kp : Nat → Addr}
  {Y : State} {t : Nat} {W : Addr → Byte}

/-- From 678: the slot `_items[_size]` = the item; the local's buffer null to 317, else `delete[]` (`k696`). -/
theorem from678 (E : Ev prof F Wl L s₀ o gev gP gE fb S g0 e₂ code₂ j₂ I Ok ch ln sp kp) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = cps_at.add 678) (hs : Y.cpu.gpr.rsp = aR S)
    (osl : Ok (Y.cpu.gpr.rdx + Y.cpu.gpr.rax * 8#64) 8) (hIW : I W) :
    GoG prof L o gev gP gE Y t := by
  refine (c_678 prof fb).run E.c E.hfs E.hin (fun j' g' _ V' => I V' ∧ g'.rsp = Y.cpu.gpr.rsp ∧
      (j' = 317 ∨ j' = 696)) hK hA hr
    (vc_678 (E.hok _ _ osl) osl (by rw [hs]; exact E.f32) hIW E.hcl (fun _ V' hI a1 _ => ⟨hI, a1, Or.inl rfl⟩)
      fun _ V' hI a1 _ => ⟨hI, a1, Or.inr rfl⟩) ?_
  rintro j' g fl V₁ ⟨hI1, gs, rfl | rfl⟩ U t₁ hKU hAU hrU hgU -
  · subst hgU
    exact from317 E hKU hAU hrU (gs.trans hs) hI1
  · subst hgU
    refine callK E hKU hAU hrU (gs.trans hs) (lt_len (by decide)) (call_696 _) tgt_696 E.cD (E.k696 _ hI1) trivial
      ?_
    intro Z W' t₃ hKZ hAZ hrZ hsZ _ _ hIZ
    exact from701 E hKZ hAZ hrZ hsZ hIZ

/-- From 660 (back from the item's constructor): `_size` + 1, to 678. -/
theorem from660 (E : Ev prof F Wl L s₀ o gev gP gE fb S g0 e₂ code₂ j₂ I Ok ch ln sp kp) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = cps_at.add 660) (hs : Y.cpu.gpr.rsp = aR S) {b : Nat}
    (hb : b < nS g0) (h12 : Y.cpu.gpr.r12 = e24 sp b) (hIW : I W) :
    GoG prof L o gev gP gE Y t := by
  have ro := E.hro b hb
  refine (c_660 prof fb).run E.c E.hfs E.hin (fun j' g' _ V' => j' = 678 ∧ I V' ∧ g'.rsp = Y.cpu.gpr.rsp ∧
      g'.rdx = rdq(W, Y.cpu.gpr.r12 + 8#64) ∧ g'.rax = BitVec.setWidth 64 rdd(W, Y.cpu.gpr.r12 + 16#64)) hK hA hr
    (vc_660 (by rw [h12]; exact E.fd ro.2.2.2.2.1) (by rw [h12]; exact E.fd ro.2.2.2.1)
      (by rw [h12]; exact E.hok _ _ ro.2.2.2.2.1) (by rw [h12]; exact ro.2.2.2.2.1) hIW E.hcl
      fun _ V' hI a1 _ _ a2 a3 _ => ⟨rfl, hI, a1, a2, a3⟩) ?_
  rintro j' g fl V₁ ⟨rfl, hI1, gs, gdx, gax⟩ U t₁ hKU hAU hrU hgU -
  subst hgU
  have osl : Ok (U.cpu.gpr.rdx + U.cpu.gpr.rax * 8#64) 8 := by
    rw [gdx, gax, h12]
    exact ro.2.2.2.2.2.2 W hIW
  exact from678 E hKU hAU hrU (gs.trans hs) osl hI1

/-- From 646 (back from `PostStrings`' item allocation): the item's constructor (`k655`), from its return 660. -/
theorem from646 (E : Ev prof F Wl L s₀ o gev gP gE fb S g0 e₂ code₂ j₂ I Ok ch ln sp kp) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = cps_at.add 646) (hs : Y.cpu.gpr.rsp = aR S) {b : Nat}
    (hb : b < nS g0) (h12 : Y.cpu.gpr.r12 = e24 sp b) (hIW : I W) :
    GoG prof L o gev gP gE Y t := by
  refine (c_646 prof fb).run E.c E.hfs E.hin (fun j' g' _ V' => j' = 655 ∧ V' = W ∧ g'.rsp = Y.cpu.gpr.rsp ∧
      g'.r12 = Y.cpu.gpr.r12) hK hA hr (vc_646 fun _ a1 a2 _ _ _ => ⟨rfl, rfl, a1, a2⟩) ?_
  rintro j' g fl V₁ ⟨rfl, hV₁, gs, g12⟩ U t₁ hKU hAU hrU hgU -
  subst V₁ hgU
  refine callK E hKU hAU hrU (gs.trans hs) (lt_len (by decide)) (call_655 _) tgt_655 E.cC (E.k655 _ hIW) trivial ?_
  intro Z W' t₃ hKZ hAZ hrZ hsZ hkZ _ hIZ
  exact from660 E hKZ hAZ hrZ hsZ hb (hkZ.2.2.1.trans (g12.trans h12)) hIZ

/-- From 636: the item's allocation (`k641`), from its return 646. -/
theorem from636 (E : Ev prof F Wl L s₀ o gev gP gE fb S g0 e₂ code₂ j₂ I Ok ch ln sp kp) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = cps_at.add 636) (hs : Y.cpu.gpr.rsp = aR S) {b : Nat}
    (hb : b < nS g0) (h12 : Y.cpu.gpr.r12 = e24 sp b) (hIW : I W) :
    GoG prof L o gev gP gE Y t := by
  refine (c_636 prof fb).run E.c E.hfs E.hin (fun j' g' _ V' => j' = 641 ∧ V' = W ∧ g'.rsp = Y.cpu.gpr.rsp ∧
      g'.r12 = Y.cpu.gpr.r12) hK hA hr (vc_636 fun _ a1 a2 _ _ => ⟨rfl, rfl, a1, a2⟩) ?_
  rintro j' g fl V₁ ⟨rfl, hV₁, gs, g12⟩ U t₁ hKU hAU hrU hgU -
  subst V₁ hgU
  refine callK E hKU hAU hrU (gs.trans hs) (lt_len (by decide)) (call_641 _) tgt_641 E.cN (E.k641 _ hIW) trivial ?_
  intro Z W' t₃ hKZ hAZ hrZ hsZ hkZ _ hIZ
  exact from646 E hKZ hAZ hrZ hsZ hb (hkZ.2.2.1.trans (g12.trans h12)) hIZ

/-- From 626: the new `_items` and `_capacity` stored, to 636. -/
theorem from626 (E : Ev prof F Wl L s₀ o gev gP gE fb S g0 e₂ code₂ j₂ I Ok ch ln sp kp) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = cps_at.add 626) (hs : Y.cpu.gpr.rsp = aR S) {b : Nat}
    (hb : b < nS g0) (h12 : Y.cpu.gpr.r12 = e24 sp b) (hIW : I W) :
    GoG prof L o gev gP gE Y t := by
  have ro := E.hro b hb
  refine (c_626 prof fb).run E.c E.hfs E.hin (fun j' g' _ V' => j' = 636 ∧ I V' ∧ g'.rsp = Y.cpu.gpr.rsp ∧
      g'.r12 = Y.cpu.gpr.r12) hK hA hr
    (vc_626 (by rw [h12]; exact E.hok _ _ ro.2.2.2.1) (by rw [h12]; exact E.hok _ _ ro.2.2.2.2.2.1)
      (by rw [h12]; exact ro.2.2.2.1) (by rw [h12]; exact ro.2.2.2.2.2.1) hIW E.hcl
      fun _ V' hI a1 a2 _ _ => ⟨rfl, hI, a1, a2⟩) ?_
  rintro j' g fl V₁ ⟨rfl, hI1, gs, g12⟩ U t₁ hKU hAU hrU hgU -
  subst hgU
  exact from636 E hKU hAU hrU (gs.trans hs) hb (g12.trans h12) hI1

/-- From 613: the old `_items` null to 626, else `delete[]` (`k621`), from its return 626. -/
theorem from613 (E : Ev prof F Wl L s₀ o gev gP gE fb S g0 e₂ code₂ j₂ I Ok ch ln sp kp) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = cps_at.add 613) (hs : Y.cpu.gpr.rsp = aR S) {b : Nat}
    (hb : b < nS g0) (h12 : Y.cpu.gpr.r12 = e24 sp b) (hIW : I W) :
    GoG prof L o gev gP gE Y t := by
  refine (c_613 prof fb).run E.c E.hfs E.hin (fun j' g' _ V' => V' = W ∧ g'.rsp = Y.cpu.gpr.rsp ∧
      g'.r12 = Y.cpu.gpr.r12 ∧ (j' = 626 ∨ j' = 621)) hK hA hr
    (vc_613 (fun _ a1 a2 _ _ => ⟨rfl, a1, a2, Or.inl rfl⟩) fun _ a1 a2 _ _ => ⟨rfl, a1, a2, Or.inr rfl⟩) ?_
  rintro j' g fl V₁ ⟨hV₁, gs, g12, rfl | rfl⟩ U t₁ hKU hAU hrU hgU -
  · subst V₁ hgU
    exact from626 E hKU hAU hrU (gs.trans hs) hb (g12.trans h12) hIW
  · subst V₁ hgU
    refine callK E hKU hAU hrU (gs.trans hs) (lt_len (by decide)) (call_621 _) tgt_621 E.cD (E.k621 _ hIW) trivial
      ?_
    intro Z W' t₃ hKZ hAZ hrZ hsZ hkZ _ hIZ
    exact from626 E hKZ hAZ hrZ hsZ hb (hkZ.2.2.1.trans (g12.trans h12)) hIZ

/-- From 809 (back from the copy): to 613. -/
theorem from809 (E : Ev prof F Wl L s₀ o gev gP gE fb S g0 e₂ code₂ j₂ I Ok ch ln sp kp) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = cps_at.add 809) (hs : Y.cpu.gpr.rsp = aR S) {b : Nat}
    (hb : b < nS g0) (h12 : Y.cpu.gpr.r12 = e24 sp b) (hIW : I W) :
    GoG prof L o gev gP gE Y t := by
  refine (c_809 prof fb).run E.c E.hfs E.hin (fun j' g' _ V' => j' = 613 ∧ V' = W ∧ g'.rsp = Y.cpu.gpr.rsp ∧
      g'.r12 = Y.cpu.gpr.r12) hK hA hr
    (vc_809 (by rw [h12]; exact E.fd (E.hro b hb).2.2.2.1) fun _ a1 a2 _ _ => ⟨rfl, rfl, a1, a2⟩) ?_
  rintro j' g fl V₁ ⟨rfl, hV₁, gs, g12⟩ U t₁ hKU hAU hrU hgU -
  subst V₁ hgU
  exact from613 E hKU hAU hrU (gs.trans hs) hb (g12.trans h12) hIW

/-- From 592 (back from the new buffer's allocation): `_size` 0 to 613, else the copy (`k804`), from its return 809.
-/
theorem from592 (E : Ev prof F Wl L s₀ o gev gP gE fb S g0 e₂ code₂ j₂ I Ok ch ln sp kp) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = cps_at.add 592) (hs : Y.cpu.gpr.rsp = aR S) {b : Nat}
    (hb : b < nS g0) (h12 : Y.cpu.gpr.r12 = e24 sp b) (hIW : I W) :
    GoG prof L o gev gP gE Y t := by
  have ro := E.hro b hb
  refine (c_592 prof fb).run E.c E.hfs E.hin (fun j' g' _ V' => V' = W ∧ g'.rsp = Y.cpu.gpr.rsp ∧
      g'.r12 = Y.cpu.gpr.r12 ∧ (j' = 804 ∨ j' = 613)) hK hA hr
    (vc_592 (by rw [h12]; exact E.fd ro.2.2.2.2.1) (by rw [h12]; exact E.fd ro.2.2.2.1)
      (fun _ a1 a2 _ _ => ⟨rfl, a1, a2, Or.inl rfl⟩) fun _ a1 a2 _ _ => ⟨rfl, a1, a2, Or.inr rfl⟩) ?_
  rintro j' g fl V₁ ⟨hV₁, gs, g12, rfl | rfl⟩ U t₁ hKU hAU hrU hgU -
  · subst V₁ hgU
    refine callK E hKU hAU hrU (gs.trans hs) (lt_len (by decide)) (call_804 _) tgt_804 E.cM (E.k804 _ hIW) trivial
      ?_
    intro Z W' t₃ hKZ hAZ hrZ hsZ hkZ _ hIZ
    exact from809 E hKZ hAZ hrZ hsZ hb (hkZ.2.2.1.trans (g12.trans h12)) hIZ
  · subst V₁ hgU
    exact from613 E hKU hAU hrU (gs.trans hs) hb (g12.trans h12) hIW

/-- From 580: the new buffer's allocation (`k587`), from its return 592. -/
theorem from580 (E : Ev prof F Wl L s₀ o gev gP gE fb S g0 e₂ code₂ j₂ I Ok ch ln sp kp) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = cps_at.add 580) (hs : Y.cpu.gpr.rsp = aR S) {b : Nat}
    (hb : b < nS g0) (h12 : Y.cpu.gpr.r12 = e24 sp b) (hIW : I W) :
    GoG prof L o gev gP gE Y t := by
  refine (c_580 prof fb).run E.c E.hfs E.hin (fun j' g' _ V' => j' = 587 ∧ V' = W ∧ g'.rsp = Y.cpu.gpr.rsp ∧
      g'.r12 = Y.cpu.gpr.r12) hK hA hr (vc_580 fun _ a1 a2 _ _ => ⟨rfl, rfl, a1, a2⟩) ?_
  rintro j' g fl V₁ ⟨rfl, hV₁, gs, g12⟩ U t₁ hKU hAU hrU hgU -
  subst V₁ hgU
  refine callK E hKU hAU hrU (gs.trans hs) (lt_len (by decide)) (call_587 _) tgt_587 E.cA (E.k587 _ hIW) trivial ?_
  intro Z W' t₃ hKZ hAZ hrZ hsZ hkZ _ hIZ
  exact from592 E hKZ hAZ hrZ hsZ hb (hkZ.2.2.1.trans (g12.trans h12)) hIZ

theorem from570 (E : Ev prof F Wl L s₀ o gev gP gE fb S g0 e₂ code₂ j₂ I Ok ch ln sp kp) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = cps_at.add 570) (hs : Y.cpu.gpr.rsp = aR S) {b : Nat}
    (hb : b < nS g0) (h12 : Y.cpu.gpr.r12 = e24 sp b) (hIW : I W) :
    GoG prof L o gev gP gE Y t := by
  refine (c_570 prof fb).run E.c E.hfs E.hin (fun j' g' _ V' => j' = 580 ∧ V' = W ∧ g'.rsp = Y.cpu.gpr.rsp ∧
      g'.r12 = Y.cpu.gpr.r12) hK hA hr (vc_570 fun _ a1 a2 _ _ => ⟨rfl, rfl, a1, a2⟩) ?_
  rintro j' g fl V₁ ⟨rfl, hV₁, gs, g12⟩ U t₁ hKU hAU hrU hgU -
  subst V₁ hgU
  exact from580 E hKU hAU hrU (gs.trans hs) hb (g12.trans h12) hIW

theorem from557 (E : Ev prof F Wl L s₀ o gev gP gE fb S g0 e₂ code₂ j₂ I Ok ch ln sp kp) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = cps_at.add 557) (hs : Y.cpu.gpr.rsp = aR S) {b : Nat}
    (hb : b < nS g0) (h12 : Y.cpu.gpr.r12 = e24 sp b) (hIW : I W) :
    GoG prof L o gev gP gE Y t := by
  refine (c_557 prof fb).run E.c E.hfs E.hin (fun j' g' _ V' => j' = 570 ∧ V' = W ∧ g'.rsp = Y.cpu.gpr.rsp ∧
      g'.r12 = Y.cpu.gpr.r12) hK hA hr (vc_557 fun _ a1 a2 _ _ => ⟨rfl, rfl, a1, a2⟩) ?_
  rintro j' g fl V₁ ⟨rfl, hV₁, gs, g12⟩ U t₁ hKU hAU hrU hgU -
  subst V₁ hgU
  exact from570 E hKU hAU hrU (gs.trans hs) hb (g12.trans h12) hIW

/-- From 534 (back from the `UString`): room in `PostStrings` to 636; else the new capacity, too big (the `ja` at
551) to the throw (`kt`), else to 557. -/
theorem from534 (E : Ev prof F Wl L s₀ o gev gP gE fb S g0 e₂ code₂ j₂ I Ok ch ln sp kp) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = cps_at.add 534) (hs : Y.cpu.gpr.rsp = aR S) {b : Nat}
    (hb : b < nS g0) (h12 : Y.cpu.gpr.r12 = e24 sp b) (hIW : I W) :
    GoG prof L o gev gP gE Y t := by
  have ro := E.hro b hb
  refine (c_534 prof fb).run E.c E.hfs E.hin (fun j' g' _ V' => V' = W ∧ g'.rsp = Y.cpu.gpr.rsp ∧
      g'.r12 = Y.cpu.gpr.r12 ∧ (j' = 636 ∨ j' = 551)) hK hA hr
    (vc_534 (by rw [h12]; exact E.fd ro.2.2.2.2.2.1) (by rw [h12]; exact E.fd ro.2.2.2.2.1)
      (fun _ a1 a2 _ _ => ⟨rfl, a1, a2, Or.inl rfl⟩) fun _ a1 a2 _ _ => ⟨rfl, a1, a2, Or.inr rfl⟩) ?_
  rintro j' g fl V₁ ⟨hV₁, gs, g12, rfl | rfl⟩ U t₁ hKU hAU hrU hgU -
  · subst V₁ hgU
    exact from636 E hKU hAU hrU (gs.trans hs) hb (g12.trans h12) hIW
  · subst V₁ hgU
    obtain ⟨cT, hinT, hT⟩ := E.cT
    refine E.c.s_jcc_x hKU hAU E.hin (lt_len (by decide)) hrU (ja_551 _) hinT hT (tgt := 0) (by decide) ?_ ?_
    · intro _ Y₁ t₂ hK₁ hA₁ ⟨hr₁, hg₁⟩
      exact E.kt W hIW Y₁ t₂ hK₁ hA₁ (by rw [hr₁, addr_add_zero]) (by rw [hg₁]; exact gs.trans hs)
    · intro _ Y₁ t₂ hK₁ hA₁ ⟨hr₁, hg₁⟩
      exact from557 E hK₁ hA₁ hr₁ (by rw [hg₁]; exact gs.trans hs) hb (by rw [hg₁]; exact g12.trans h12) hIW

/-- From 514 (`kString`): the `UString` of the rest of `s` (`k529`), from its return 534. -/
theorem from514 (E : Ev prof F Wl L s₀ o gev gP gE fb S g0 e₂ code₂ j₂ I Ok ch ln sp kp) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = cps_at.add 514) (hs : Y.cpu.gpr.rsp = aR S)
    (h14 : Y.cpu.gpr.r14 = g0.rsi) {b : Nat} (hb : b < nS g0) (h12 : Y.cpu.gpr.r12 = e24 sp b) (hIW : I W) :
    GoG prof L o gev gP gE Y t := by
  refine (c_514 prof fb).run E.c E.hfs E.hin (fun j' g' _ V' => j' = 529 ∧ V' = W ∧ g'.rsp = Y.cpu.gpr.rsp ∧
      g'.r12 = Y.cpu.gpr.r12) hK hA hr (vc_514 (by rw [h14]; exact E.fs0) fun _ a1 a2 _ _ _ => ⟨rfl, rfl, a1, a2⟩)
    ?_
  rintro j' g fl V₁ ⟨rfl, hV₁, gs, g12⟩ U t₁ hKU hAU hrU hgU -
  subst V₁ hgU
  refine callK E hKU hAU hrU (gs.trans hs) (lt_len (by decide)) (call_529 _) tgt_529 E.cU (E.k529 _ hIW) trivial ?_
  intro Z W' t₃ hKZ hAZ hrZ hsZ hkZ _ hIZ
  exact from534 E hKZ hAZ hrZ hsZ hb (hkZ.2.2.1.trans (g12.trans h12)) hIZ

end Runs

end FV7z.Cps
