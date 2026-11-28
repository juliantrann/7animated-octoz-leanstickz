import FV7z.Cps.Str
/-!
# `NCommandLineParser::CParser::ParseString`: from the longest match to the switch's type (PLAN.md §M, M1)

From 183 (after the switch loop): no match to "Unknown switch" (735); else the form and the result `b` (206),
"Multiple instances" (221 to 407), `ThereIs` (241), "Too short" (706), `WithMinus` and `PostCharIndex` (265), by
`Type`: `kString` (514), `kChar` (439), `kMinus` (302, the `sete` at 429), `kSimple` (307).

`p` = `pos` (`r15d`, the index after the key in `s`), `rax` = `rem` = `len - pos`.
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

/-- `s[pos]` readable when `rem` = 1. -/
theorem Ev.fc (E : Ev prof F Wl L s₀ o gev gP gE fb S g0 e₂ code₂ j₂ I Ok ch ln sp kp) {g : Gprs} {p : BitVec 32}
    (hIW : I W) (h14 : g.r14 = g0.rsi) (h15 : g.r15 = BitVec.setWidth 64 p)
    (hax : g.rax = BitVec.setWidth 64 (ln - p)) :
    BitVec.setWidth 32 g.rax = 1#32 → ∀ i < 4, Foot F.data (Addr.add (rdq(W, g.r14) + g.r15 * 4#64) i) := by
  intro h
  rw [hax, s64] at h
  rw [h14, (E.hs W hIW).1, h15]
  exact E.fch p h

/-- `kMinus` (302): `rem` 1 to the `sete` of `s[pos]` = '-' into `WithMinus` (429), from it to 435; else 307. -/
theorem from302 (E : Ev prof F Wl L s₀ o gev gP gE fb S g0 e₂ code₂ j₂ I Ok ch ln sp kp) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = cps_at.add 302) (hs : Y.cpu.gpr.rsp = aR S)
    (h14 : Y.cpu.gpr.r14 = g0.rsi) {p : BitVec 32} (h15 : Y.cpu.gpr.r15 = BitVec.setWidth 64 p)
    (hax : Y.cpu.gpr.rax = BitVec.setWidth 64 (ln - p)) {b : Nat} (hb : b < nS g0)
    (h12 : Y.cpu.gpr.r12 = e24 sp b) (hIW : I W) :
    GoG prof L o gev gP gE Y t := by
  refine (c_302 prof fb).run E.c E.hfs E.hin (fun j' g' _ V' => V' = W ∧
      ((j' = 307 ∧ g' = Y.cpu.gpr) ∨ (j' = 429 ∧ g'.rsp = Y.cpu.gpr.rsp ∧ g'.r12 = Y.cpu.gpr.r12))) hK hA hr
    (vc_302 (by rw [h14]; exact E.fs0) (E.fc hIW h14 h15 hax) (fun _ => ⟨rfl, Or.inl ⟨rfl, rfl⟩⟩)
      fun _ a1 a2 _ => ⟨rfl, Or.inr ⟨rfl, a1, a2⟩⟩) ?_
  rintro j' g fl V₁ ⟨hV₁, ⟨rfl, rfl⟩ | ⟨rfl, gs, g12⟩⟩ U t₁ hKU hAU hrU hgU -
  · subst V₁
    exact from307 E hKU hAU hrU (by rw [hgU]; exact hs) (by rw [hgU]; exact h14) hIW
  · subst V₁ hgU
    have he : eaD U 12 1 = U.cpu.gpr.r12 + 1#64 := by
      show U.cpu.gpr.get (regOf 12) + BitVec.ofNat 64 1 = _
      rfl
    have o1 : Ok (U.cpu.gpr.r12 + 1#64) 1 := by
      rw [g12, h12]
      exact (E.hro b hb).2.1
    refine E.c.s_setcc_m8 hKU hAU E.hin (lt_len (by decide)) hrU (set_429 _) (by rw [he]; exact E.hok _ _ o1) ?_
    rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂, -⟩
    rw [he] at hA₂
    exact from435 E hK₂ hA₂ hr₂ (by rw [hg₂]; exact gs.trans hs) (E.hcl _ _ _ _ (toBytesLE_length _ _) o1 hIW)

/-- `kChar` (439): `rem` 1 and `s[pos]` ASCII to `FindCharPosInString` (467), not ASCII to 485; else 307. -/
theorem from439 (E : Ev prof F Wl L s₀ o gev gP gE fb S g0 e₂ code₂ j₂ I Ok ch ln sp kp) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = cps_at.add 439) (hs : Y.cpu.gpr.rsp = aR S)
    (h14 : Y.cpu.gpr.r14 = g0.rsi) {p : BitVec 32} (h15 : Y.cpu.gpr.r15 = BitVec.setWidth 64 p)
    (hax : Y.cpu.gpr.rax = BitVec.setWidth 64 (ln - p)) {b : Nat} (hb : b < nS g0)
    (hbx : Y.cpu.gpr.rbx = e24 g0.rdx b) (h12 : Y.cpu.gpr.r12 = e24 sp b) (hIW : I W) :
    GoG prof L o gev gP gE Y t := by
  refine (c_439 prof fb).run E.c E.hfs E.hin (fun j' g' _ V' => V' = W ∧
      ((j' = 307 ∧ g' = Y.cpu.gpr) ∨ ((j' = 485 ∨ j' = 467) ∧ g'.rsp = Y.cpu.gpr.rsp ∧ g'.r12 = Y.cpu.gpr.r12)))
    hK hA hr
    (vc_439 (by rw [h14]; exact E.fs0) (E.fc hIW h14 h15 hax) (by rw [hbx]; exact (E.ffo b hb).2.2.2.2)
      (fun _ => ⟨rfl, Or.inl ⟨rfl, rfl⟩⟩) (fun _ a1 a2 _ => ⟨rfl, Or.inr ⟨Or.inl rfl, a1, a2⟩⟩)
      fun _ a1 a2 _ => ⟨rfl, Or.inr ⟨Or.inr rfl, a1, a2⟩⟩) ?_
  rintro j' g fl V₁ ⟨hV₁, ⟨rfl, rfl⟩ | ⟨rfl | rfl, gs, g12⟩⟩ U t₁ hKU hAU hrU hgU -
  · subst V₁
    exact from307 E hKU hAU hrU (by rw [hgU]; exact hs) (by rw [hgU]; exact h14) hIW
  · subst V₁ hgU
    exact from485 E hKU hAU hrU (gs.trans hs) hIW
  · subst V₁ hgU
    exact from467 E hKU hAU hrU (gs.trans hs) hb (g12.trans h12) hIW

/-- By `Type` (293): `kChar` to 439, else 302. -/
theorem from293 (E : Ev prof F Wl L s₀ o gev gP gE fb S g0 e₂ code₂ j₂ I Ok ch ln sp kp) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = cps_at.add 293) (hs : Y.cpu.gpr.rsp = aR S)
    (h14 : Y.cpu.gpr.r14 = g0.rsi) {p : BitVec 32} (h15 : Y.cpu.gpr.r15 = BitVec.setWidth 64 p)
    (hax : Y.cpu.gpr.rax = BitVec.setWidth 64 (ln - p)) {b : Nat} (hb : b < nS g0)
    (hbx : Y.cpu.gpr.rbx = e24 g0.rdx b) (h12 : Y.cpu.gpr.r12 = e24 sp b) (hIW : I W) :
    GoG prof L o gev gP gE Y t := by
  refine (c_293 prof fb).run E.c E.hfs E.hin (fun j' g' _ V' => g' = Y.cpu.gpr ∧ V' = W ∧ (j' = 439 ∨ j' = 302))
    hK hA hr (vc_293 (fun _ => ⟨rfl, rfl, Or.inl rfl⟩) fun _ => ⟨rfl, rfl, Or.inr rfl⟩) ?_
  rintro j' g fl V₁ ⟨rfl, hV₁, rfl | rfl⟩ U t₁ hKU hAU hrU hgU -
  · subst V₁
    exact from439 E hKU hAU hrU (by rw [hgU]; exact hs) (by rw [hgU]; exact h14) (by rw [hgU]; exact h15)
      (by rw [hgU]; exact hax) hb (by rw [hgU]; exact hbx) (by rw [hgU]; exact h12) hIW
  · subst V₁
    exact from302 E hKU hAU hrU (by rw [hgU]; exact hs) (by rw [hgU]; exact h14) (by rw [hgU]; exact h15)
      (by rw [hgU]; exact hax) hb (by rw [hgU]; exact h12) hIW

/-- From 265: `WithMinus` = 0, `PostCharIndex` = -1; `kString` to 514, else 293. -/
theorem from265 (E : Ev prof F Wl L s₀ o gev gP gE fb S g0 e₂ code₂ j₂ I Ok ch ln sp kp) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = cps_at.add 265) (hs : Y.cpu.gpr.rsp = aR S)
    (h14 : Y.cpu.gpr.r14 = g0.rsi) {p : BitVec 32} (h15 : Y.cpu.gpr.r15 = BitVec.setWidth 64 p)
    (hax : Y.cpu.gpr.rax = BitVec.setWidth 64 (ln - p)) {b : Nat} (hb : b < nS g0)
    (hbx : Y.cpu.gpr.rbx = e24 g0.rdx b) (h12 : Y.cpu.gpr.r12 = e24 sp b) (hIW : I W) :
    GoG prof L o gev gP gE Y t := by
  have ro := E.hro b hb
  refine (c_265 prof fb).run E.c E.hfs E.hin (fun j' g' _ V' => I V' ∧ g'.rsp = Y.cpu.gpr.rsp ∧
      g'.r14 = Y.cpu.gpr.r14 ∧ g'.r15 = Y.cpu.gpr.r15 ∧ g'.rbx = Y.cpu.gpr.rbx ∧ g'.r12 = Y.cpu.gpr.r12 ∧
      g'.rax = Y.cpu.gpr.rax ∧ (j' = 514 ∨ j' = 293)) hK hA hr
    (vc_265 (by rw [hbx]; exact (E.ffo b hb).2.1) (by rw [h12]; exact E.hok _ _ ro.2.1)
      (by rw [h12]; exact E.hok _ _ ro.2.2.1) (by rw [h12]; exact ro.2.1) (by rw [h12]; exact ro.2.2.1) hIW E.hcl
      (fun _ V' hI a1 a2 a3 a4 a5 a6 _ => ⟨hI, a1, a2, a3, a4, a5, a6, Or.inl rfl⟩)
      fun _ V' hI a1 a2 a3 a4 a5 a6 _ => ⟨hI, a1, a2, a3, a4, a5, a6, Or.inr rfl⟩) ?_
  rintro j' g fl V₁ ⟨hI1, gs, g14, g15, gx, g12, ga, rfl | rfl⟩ U t₁ hKU hAU hrU hgU -
  · subst hgU
    exact from514 E hKU hAU hrU (gs.trans hs) (g14.trans h14) hb (g12.trans h12) hI1
  · subst hgU
    exact from293 E hKU hAU hrU (gs.trans hs) (g14.trans h14) (g15.trans h15) (ga.trans hax) hb (gx.trans hbx)
      (g12.trans h12) hI1

/-- From 241: `ThereIs` = 1; the rest shorter than `MinLen` to "Too short" (706), else 265. -/
theorem from241 (E : Ev prof F Wl L s₀ o gev gP gE fb S g0 e₂ code₂ j₂ I Ok ch ln sp kp) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = cps_at.add 241) (hs : Y.cpu.gpr.rsp = aR S)
    (h14 : Y.cpu.gpr.r14 = g0.rsi) {p : BitVec 32} (h15 : Y.cpu.gpr.r15 = BitVec.setWidth 64 p) {b : Nat}
    (hb : b < nS g0) (hbx : Y.cpu.gpr.rbx = e24 g0.rdx b) (h12 : Y.cpu.gpr.r12 = e24 sp b) (hIW : I W) :
    GoG prof L o gev gP gE Y t := by
  have ro := E.hro b hb
  refine (c_241 prof fb).run E.c E.hfs E.hin (fun j' g' _ V' => I V' ∧ g'.rsp = Y.cpu.gpr.rsp ∧
      (j' = 706 ∨ (j' = 265 ∧ g'.r14 = Y.cpu.gpr.r14 ∧ g'.r15 = Y.cpu.gpr.r15 ∧ g'.rbx = Y.cpu.gpr.rbx ∧
        g'.r12 = Y.cpu.gpr.r12 ∧
        g'.rax = BitVec.setWidth 64 (rdd(W, Y.cpu.gpr.r14 + 8#64) - BitVec.setWidth 32 Y.cpu.gpr.r15)))) hK hA hr
    (vc_241 (by rw [h14]; exact E.fs8) (by rw [hbx]; exact (E.ffo b hb).2.2.2.1) (by rw [h12]; exact E.hok _ _ ro.1)
      (by rw [h12]; exact ro.1) hIW E.hcl (fun _ V' hI a1 _ => ⟨hI, a1, Or.inl rfl⟩)
      fun _ V' hI a1 a2 a3 a4 a5 a6 _ => ⟨hI, a1, Or.inr ⟨rfl, a2, a3, a4, a5, a6⟩⟩) ?_
  rintro j' g fl V₁ ⟨hI1, gs, rfl | ⟨rfl, g14, g15, gx, g12, ga⟩⟩ U t₁ hKU hAU hrU hgU -
  · subst hgU
    exact from706 E hKU hAU hrU (gs.trans hs) hI1
  · subst hgU
    have hax : U.cpu.gpr.rax = BitVec.setWidth 64 (ln - p) := by
      rw [ga, h14, (E.hs W hIW).2.1, h15, s64]
    exact from265 E hKU hAU hrU (gs.trans hs) (g14.trans h14) (g15.trans h15) hax hb (gx.trans hbx)
      (g12.trans h12) hI1

/-- From 221 (`rax` = `24 b`): `Multi` off and `ThereIs` set to "Multiple instances" (407), else 241. -/
theorem from221 (E : Ev prof F Wl L s₀ o gev gP gE fb S g0 e₂ code₂ j₂ I Ok ch ln sp kp) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = cps_at.add 221) (hs : Y.cpu.gpr.rsp = aR S)
    (h14 : Y.cpu.gpr.r14 = g0.rsi) {p : BitVec 32} (h15 : Y.cpu.gpr.r15 = BitVec.setWidth 64 p) {b : Nat}
    (hb : b < nS g0) (hbx : Y.cpu.gpr.rbx = g0.rdx) (hax : Y.cpu.gpr.rax = BitVec.ofNat 64 (24 * b))
    (h12 : Y.cpu.gpr.r12 = sp) (hIW : I W) :
    GoG prof L o gev gP gE Y t := by
  refine (c_221 prof fb).run E.c E.hfs E.hin (fun j' g' _ V' => V' = W ∧ g'.rsp = Y.cpu.gpr.rsp ∧
      ((j' = 241 ∧ g'.r14 = Y.cpu.gpr.r14 ∧ g'.r15 = Y.cpu.gpr.r15 ∧ g'.rbx = Y.cpu.gpr.rbx + Y.cpu.gpr.rax ∧
        g'.r12 = Y.cpu.gpr.r12 + Y.cpu.gpr.rax) ∨ j' = 407)) hK hA hr
    (vc_221 (by rw [hbx, hax]; exact (E.ffo b hb).2.2.1) (by rw [h12, hax]; exact E.fd (E.hro b hb).1)
      (fun _ a1 a2 a3 a4 a5 _ => ⟨rfl, a1, Or.inl ⟨rfl, a2, a3, a4, a5⟩⟩) fun _ a1 _ _ => ⟨rfl, a1, Or.inr rfl⟩) ?_
  rintro j' g fl V₁ ⟨hV₁, gs, ⟨rfl, g14, g15, gx, g12⟩ | rfl⟩ U t₁ hKU hAU hrU hgU -
  · subst V₁ hgU
    have ex : U.cpu.gpr.rbx = e24 g0.rdx b := by rw [gx, hbx, hax]
    have e12 : U.cpu.gpr.r12 = e24 sp b := by rw [g12, h12, hax]
    exact from241 E hKU hAU hrU (gs.trans hs) (g14.trans h14) (g15.trans h15) hb ex e12 hIW
  · subst V₁ hgU
    exact from407 E hKU hAU hrU (gs.trans hs) hIW

/-- From 206 (`r8` = `b`): `pos` = the key's length + 1, `rax` = `24 b`, `r12` = `_switches`, to 221. -/
theorem from206 (E : Ev prof F Wl L s₀ o gev gP gE fb S g0 e₂ code₂ j₂ I Ok ch ln sp kp) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = cps_at.add 206) (hs : Y.cpu.gpr.rsp = aR S)
    (h14 : Y.cpu.gpr.r14 = g0.rsi) {b : Nat} (hb : b < nS g0) (h8 : Y.cpu.gpr.r8 = BitVec.ofNat 64 b)
    (hbx : Y.cpu.gpr.rbx = g0.rdx) (hdi : Y.cpu.gpr.rdi = g0.rdi) (hIW : I W) :
    GoG prof L o gev gP gE Y t := by
  refine (c_206 prof fb).run E.c E.hfs E.hin (fun j' g' _ V' => j' = 221 ∧ V' = W ∧ g'.rsp = Y.cpu.gpr.rsp ∧
      g'.r14 = Y.cpu.gpr.r14 ∧ g'.rbx = Y.cpu.gpr.rbx ∧
      g'.r15 = BitVec.setWidth 64 (BitVec.setWidth 32 Y.cpu.gpr.r15 + 1#32) ∧ g'.rax = sz24 Y.cpu.gpr.r8 ∧
      g'.r12 = rdq(W, Y.cpu.gpr.rdi)) hK hA hr
    (vc_206 (by rw [hdi]; exact E.fth) fun _ a1 a2 a3 _ a5 a6 a7 _ => ⟨rfl, rfl, a1, a2, a3, a5, a6, a7⟩) ?_
  rintro j' g fl V₁ ⟨rfl, hV₁, gs, g14, gx, g15, ga, g12⟩ U t₁ hKU hAU hrU hgU -
  subst V₁ hgU
  have hn := nS_lt g0
  have hax : U.cpu.gpr.rax = BitVec.ofNat 64 (24 * b) := by
    rw [ga, h8]
    exact sz24_eq (by omega)
  have e12 : U.cpu.gpr.r12 = sp := by
    rw [g12, hdi]
    exact (E.hs W hIW).2.2
  exact from221 E hKU hAU hrU (gs.trans hs) (g14.trans h14) g15 hb (gx.trans hbx) hax e12 hIW

/-- From 183 (after the switch loop, `k + 1` forms): no match to "Unknown switch" (735), else 206. -/
theorem from183 (E : Ev prof F Wl L s₀ o gev gP gE fb S g0 e₂ code₂ j₂ I Ok ch ln sp kp) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = cps_at.add 183) (hs : Y.cpu.gpr.rsp = aR S)
    (h14 : Y.cpu.gpr.r14 = g0.rsi) {k : Nat} (hk : k + 1 = nS g0) (hbt : Bt (k + 1) Y.cpu.gpr) (hIW : I W) :
    GoG prof L o gev gP gE Y t := by
  refine (c_183 prof fb).run E.c E.hfs E.hin (fun j' g' _ V' => V' = W ∧ g'.rsp = Y.cpu.gpr.rsp ∧
      (j' = 735 ∨ (j' = 206 ∧ g'.r14 = Y.cpu.gpr.r14 ∧
        g'.r8 = BitVec.setWidth 64 (BitVec.setWidth 32 Y.cpu.gpr.rbp) ∧ g'.rbx = rdq(W, Y.cpu.gpr.rsp + 16#64) ∧
        g'.rdi = rdq(W, Y.cpu.gpr.rsp + 24#64) ∧ ¬BitVec.setWidth 32 Y.cpu.gpr.r15 = 4294967295#32))) hK hA hr
    (vc_183 (by rw [hs]; exact E.f16) (by rw [hs]; exact E.f24) (fun _ a1 _ => ⟨rfl, a1, Or.inl rfl⟩)
      fun _ a1 a2 _ a4 a5 a6 a7 _ => ⟨rfl, a1, Or.inr ⟨rfl, a2, a4, a5, a6, a7⟩⟩) ?_
  rintro j' g fl V₁ ⟨hV₁, gs, rfl | ⟨rfl, g14, g8, gx, gdi, gn⟩⟩ U t₁ hKU hAU hrU hgU -
  · subst V₁ hgU
    exact from735 E hKU hAU hrU (gs.trans hs) hIW
  · subst V₁ hgU
    rcases hbt with h | ⟨b, hb, e⟩
    · exact absurd h gn
    have hn := nS_lt g0
    have e8 : U.cpu.gpr.r8 = BitVec.ofNat 64 b := by
      rw [g8, e]
      exact w32 (by omega)
    have ex : U.cpu.gpr.rbx = g0.rdx := by
      rw [gx, hs]
      exact (E.hF W hIW).1
    have ed : U.cpu.gpr.rdi = g0.rdi := by
      rw [gdi, hs]
      exact (E.hF W hIW).2
    exact from206 E hKU hAU hrU (gs.trans hs) (g14.trans h14) (by omega) e8 ex ed hIW

end Runs

end FV7z.Cps
