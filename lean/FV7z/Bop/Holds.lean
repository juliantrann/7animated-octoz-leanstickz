import FV7z.Bop.Pieces
/-!
# `CExtractCallbackConsole::BeforeOpen` (0x5e7b70): from the entry to the return (PLAN.md §M, M1)

`CExtractCallbackConsole::BeforeOpen (name, testMode)`: `rdi` = `this`. One theorem for each hop: `fromN` runs the
piece at `N` (and the `call` that ends it, `callK`, with the callee as `Ev`'s continuation) and goes on by `fromM`,
from the `ret` (`from223`) back to the entry (`from35`, `bop_ok`). Each takes `rsp` = `aR S`, `rbx` = `this`, `r14`
and `r15` as at the entry (the code and the callees keep them) and `I` of the bytes; `from127` and `from135` the
stream `r13` = `_so` readable (`Ev.hso`: not null on the way there).

- `bop_ok`: from the entry (the hypotheses `E : Ev …` with `S` = the entry's `rsp`, `g0` = its registers, `I` of
  the bytes after the four pushes) to the return (`Ev.kr`: `rsp` 8 up, the callee-saved registers as at the entry,
  `I` of the bytes) or a callee's goal.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
open FV7z.Api (KS)
namespace FV7z.Bop
set_option linter.unusedVariables false

section Runs
variable {prof : Profile} {F : Footprint} {Wl : List Rgn} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {S : Addr} {g0 : Gprs} {e₂ : Addr} {code₂ : List Byte} {j₂ : Nat} {I : (Addr → Byte) → Prop}
  {Y : State} {t : Nat} {W : Addr → Byte}

/-- From 223 (`rsp` = `aR S`, the bytes `W` with `I`): the pops, the `ret`, to `kr`. -/
theorem from223 (E : Ev prof F Wl L s₀ o gev gP gE S g0 e₂ code₂ j₂ I) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = bop_at.add 223) (hs : Y.cpu.gpr.rsp = aR S)
    (h14 : Y.cpu.gpr.r14 = g0.r14) (h15 : Y.cpu.gpr.r15 = g0.r15) (hIW : I W) :
    GoG prof L o gev gP gE Y t := by
  obtain ⟨s1, s2, s3, s4, s5⟩ := E.hI W hIW
  have e1 : rdq(W, Y.cpu.gpr.rsp + 8#64) = g0.rbx := by rw [hs, r1]; exact s1
  have e2 : rdq(W, Y.cpu.gpr.rsp + 8#64 + 8) = g0.rbp := by rw [hs, r1, r2]; exact s2
  have e3 : rdq(W, Y.cpu.gpr.rsp + 8#64 + 8 + 8) = g0.r12 := by rw [hs, r1, r2, r3]; exact s3
  have e4 : rdq(W, Y.cpu.gpr.rsp + 8#64 + 8 + 8 + 8) = g0.r13 := by rw [hs, r1, r2, r3, r4]; exact s4
  have es : Y.cpu.gpr.rsp + 8#64 + 8 + 8 + 8 + 8 = S := by rw [hs, r1, r2, r3, r4, r5]
  refine (c_223 prof).run E.c E.hin (fun j' g' _ V' => j' = 233 ∧ V' = W ∧ g'.rsp = S ∧ KS g0 g') hK hA hr
    (vc_223 (by rw [hs, r1]; exact fun i hi => E.c.hws _ (E.hs4 i hi))
      (by rw [hs, r1, r2]; exact fun i hi => E.c.hws _ (E.hs3 i hi))
      (by rw [hs, r1, r2, r3]; exact fun i hi => E.c.hws _ (E.hs2 i hi))
      (by rw [hs, r1, r2, r3, r4]; exact fun i hi => E.c.hws _ (E.hs1 i hi))
      fun _ a1 a2 a3 a4 a5 a6 a7 _ => ⟨rfl, rfl, a1.trans es, a2.trans e1, a3.trans e2, a4.trans e3, a5.trans e4,
        a6.trans h14, a7.trans h15⟩) ?_
  rintro j' g fl V₁ ⟨rfl, hV₁, gs, gk⟩ Z t₁ hKZ hAZ hrZ hgZ -
  subst V₁ hgZ
  refine E.c.s_ret hKZ hAZ E.hin (lt_len (by decide)) hrZ (ret_233 _) (by rw [gs]; exact E.hl) E.hin₂ E.h₂
    (by rw [gs]; exact s5) ?_
  rintro Z' t₂ hKZ' hAZ' ⟨hrZ', hgZ'⟩
  refine E.kr W Z' t₂ hKZ' hAZ' hrZ' ?_ ?_ hIW
  · rw [hgZ']
    show Z.cpu.gpr.rsp + 8 = _
    rw [gs]
  · rw [hgZ']
    exact gk

/-- From 221: `eax` = 0, to 223. -/
theorem from221 (E : Ev prof F Wl L s₀ o gev gP gE S g0 e₂ code₂ j₂ I) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = bop_at.add 221) (hs : Y.cpu.gpr.rsp = aR S)
    (h14 : Y.cpu.gpr.r14 = g0.r14) (h15 : Y.cpu.gpr.r15 = g0.r15) (hIW : I W) :
    GoG prof L o gev gP gE Y t := by
  refine (c_221 prof).run E.c E.hin (fun j' g' _ V' => j' = 223 ∧ V' = W ∧ g'.rsp = Y.cpu.gpr.rsp ∧
      g'.r14 = Y.cpu.gpr.r14 ∧ g'.r15 = Y.cpu.gpr.r15) hK hA hr
    (vc_221 fun _ a1 a2 a3 a4 _ => ⟨rfl, rfl, a1, a3, a4⟩) ?_
  rintro j' g fl V₁ ⟨rfl, hV₁, gs, g14, g15⟩ U t₁ hKU hAU hrU hgU -
  subst V₁ hgU
  exact from223 E hKU hAU hrU (gs.trans hs) (g14.trans h14) (g15.trans h15) hIW

/-- From 205: `_tempA = ""` (216), to 221. -/
theorem from205 (E : Ev prof F Wl L s₀ o gev gP gE S g0 e₂ code₂ j₂ I) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = bop_at.add 205) (hs : Y.cpu.gpr.rsp = aR S)
    (hb : Y.cpu.gpr.rbx = g0.rdi) (h14 : Y.cpu.gpr.r14 = g0.r14) (h15 : Y.cpu.gpr.r15 = g0.r15) (hIW : I W) :
    GoG prof L o gev gP gE Y t := by
  refine (c_205 prof).run E.c E.hin (fun j' g' _ V' => j' = 216 ∧ V' = W ∧ g'.rsp = Y.cpu.gpr.rsp ∧
      g'.rbx = Y.cpu.gpr.rbx ∧ g'.r14 = Y.cpu.gpr.r14 ∧ g'.r15 = Y.cpu.gpr.r15) hK hA hr
    (vc_205 fun _ a1 a2 a3 a4 _ => ⟨rfl, rfl, a1, a2, a3, a4⟩) ?_
  rintro j' g fl V₁ ⟨rfl, hV₁, gs, gb, g14, g15⟩ U t₁ hKU hAU hrU hgU -
  subst V₁ hgU
  refine callK E hKU hAU hrU (gs.trans hs) (lt_len (by decide)) (call_216 _) tgt_216 E.cA (E.kA _ _ hIW) trivial
    ?_
  intro Z W' t₃ hKZ hAZ hrZ hsZ hkZ hBZ hIZ
  exact from221 E hKZ hAZ hrZ hsZ (hkZ.2.2.2.2.1.trans (g14.trans h14)) (hkZ.2.2.2.2.2.trans (g15.trans h15)) hIZ

/-- From 192 (back from `endl`): to 221, or 205. -/
theorem from192 (E : Ev prof F Wl L s₀ o gev gP gE S g0 e₂ code₂ j₂ I) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = bop_at.add 192) (hs : Y.cpu.gpr.rsp = aR S)
    (hb : Y.cpu.gpr.rbx = g0.rdi) (h14 : Y.cpu.gpr.r14 = g0.r14) (h15 : Y.cpu.gpr.r15 = g0.r15) (hIW : I W) :
    GoG prof L o gev gP gE Y t := by
  refine (c_192 prof).run E.c E.hin (fun j' g' _ V' => V' = W ∧ g'.rsp = Y.cpu.gpr.rsp ∧
      g'.rbx = Y.cpu.gpr.rbx ∧ g'.r14 = Y.cpu.gpr.r14 ∧ g'.r15 = Y.cpu.gpr.r15 ∧ (j' = 221 ∨ j' = 205)) hK hA hr
    (vc_192 (by rw [hb]; exact E.hrd) (fun _ a1 a2 a3 a4 _ => ⟨rfl, a1, a2, a3, a4, Or.inl rfl⟩)
      fun _ a1 a2 a3 a4 _ => ⟨rfl, a1, a2, a3, a4, Or.inr rfl⟩) ?_
  rintro j' g fl V₁ ⟨hV₁, gs, gb, g14, g15, hj⟩ U t₁ hKU hAU hrU hgU -
  subst V₁ hgU
  rcases hj with rfl | rfl
  · exact from221 E hKU hAU hrU (gs.trans hs) (g14.trans h14) (g15.trans h15) hIW
  · exact from205 E hKU hAU hrU (gs.trans hs) (gb.trans hb) (g14.trans h14) (g15.trans h15) hIW

/-- From 180 (back from `NormalizePrint_UString`): `endl (*_so)` (187), to 192. -/
theorem from180 (E : Ev prof F Wl L s₀ o gev gP gE S g0 e₂ code₂ j₂ I) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = bop_at.add 180) (hs : Y.cpu.gpr.rsp = aR S)
    (hb : Y.cpu.gpr.rbx = g0.rdi) (h14 : Y.cpu.gpr.r14 = g0.r14) (h15 : Y.cpu.gpr.r15 = g0.r15) (hIW : I W) :
    GoG prof L o gev gP gE Y t := by
  refine (c_180 prof).run E.c E.hin (fun j' g' _ V' => j' = 187 ∧ V' = W ∧ g'.rsp = Y.cpu.gpr.rsp ∧
      g'.rbx = Y.cpu.gpr.rbx ∧ g'.r14 = Y.cpu.gpr.r14 ∧ g'.r15 = Y.cpu.gpr.r15) hK hA hr
    (vc_180 (by rw [hb]; exact E.hrd) fun _ a1 a2 a3 a4 _ => ⟨rfl, rfl, a1, a2, a3, a4⟩) ?_
  rintro j' g fl V₁ ⟨rfl, hV₁, gs, gb, g14, g15⟩ U t₁ hKU hAU hrU hgU -
  subst V₁ hgU
  refine callK E hKU hAU hrU (gs.trans hs) (lt_len (by decide)) (call_187 _) tgt_187 E.cE (E.kE _ _ hIW) trivial
    ?_
  intro Z W' t₃ hKZ hAZ hrZ hsZ hkZ hBZ hIZ
  exact from192 E hKZ hAZ hrZ hsZ (hkZ.1.trans (gb.trans hb)) (hkZ.2.2.2.2.1.trans (g14.trans h14))
    (hkZ.2.2.2.2.2.trans (g15.trans h15)) hIZ

/-- From 165 (back from `fputs`): `NormalizePrint_UString (name)` (175), to 180. -/
theorem from165 (E : Ev prof F Wl L s₀ o gev gP gE S g0 e₂ code₂ j₂ I) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = bop_at.add 165) (hs : Y.cpu.gpr.rsp = aR S)
    (hb : Y.cpu.gpr.rbx = g0.rdi) (h14 : Y.cpu.gpr.r14 = g0.r14) (h15 : Y.cpu.gpr.r15 = g0.r15) (hIW : I W) :
    GoG prof L o gev gP gE Y t := by
  refine (c_165 prof).run E.c E.hin (fun j' g' _ V' => j' = 175 ∧ V' = W ∧ g'.rsp = Y.cpu.gpr.rsp ∧
      g'.rbx = Y.cpu.gpr.rbx ∧ g'.r14 = Y.cpu.gpr.r14 ∧ g'.r15 = Y.cpu.gpr.r15) hK hA hr
    (vc_165 (by rw [hb]; exact E.hrd) fun _ a1 a2 a3 a4 _ => ⟨rfl, rfl, a1, a2, a3, a4⟩) ?_
  rintro j' g fl V₁ ⟨rfl, hV₁, gs, gb, g14, g15⟩ U t₁ hKU hAU hrU hgU -
  subst V₁ hgU
  refine callK E hKU hAU hrU (gs.trans hs) (lt_len (by decide)) (call_175 _) tgt_175 E.cN (E.kN _ _ hIW) trivial
    ?_
  intro Z W' t₃ hKZ hAZ hrZ hsZ hkZ hBZ hIZ
  exact from180 E hKZ hAZ hrZ hsZ (hkZ.1.trans (gb.trans hb)) (hkZ.2.2.2.2.1.trans (g14.trans h14))
    (hkZ.2.2.2.2.2.trans (g15.trans h15)) hIZ

/-- From 135 (back from `endl`, `r13` = `_so` readable): `fputs (msg, *_so)` (160), to 165. -/
theorem from135 (E : Ev prof F Wl L s₀ o gev gP gE S g0 e₂ code₂ j₂ I) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = bop_at.add 135) (hs : Y.cpu.gpr.rsp = aR S)
    (hb : Y.cpu.gpr.rbx = g0.rdi) (h14 : Y.cpu.gpr.r14 = g0.r14) (h15 : Y.cpu.gpr.r15 = g0.r15)
    (h13 : ∀ i < 8, Foot F.data (Addr.add Y.cpu.gpr.r13 i)) (hIW : I W) :
    GoG prof L o gev gP gE Y t := by
  refine (c_135 prof).run E.c E.hin (fun j' g' _ V' => j' = 160 ∧ V' = W ∧ g'.rsp = Y.cpu.gpr.rsp ∧
      g'.rbx = Y.cpu.gpr.rbx ∧ g'.r14 = Y.cpu.gpr.r14 ∧ g'.r15 = Y.cpu.gpr.r15) hK hA hr
    (vc_135 h13 fun _ a1 a2 a3 a4 _ => ⟨rfl, rfl, a1, a2, a3, a4⟩) ?_
  rintro j' g fl V₁ ⟨rfl, hV₁, gs, gb, g14, g15⟩ U t₁ hKU hAU hrU hgU -
  subst V₁ hgU
  refine callK E hKU hAU hrU (gs.trans hs) (lt_len (by decide)) (call_160 _) tgt_160 E.cF (E.kF _ _ hIW) trivial
    ?_
  intro Z W' t₃ hKZ hAZ hrZ hsZ hkZ hBZ hIZ
  exact from165 E hKZ hAZ hrZ hsZ (hkZ.1.trans (gb.trans hb)) (hkZ.2.2.2.2.1.trans (g14.trans h14))
    (hkZ.2.2.2.2.2.trans (g15.trans h15)) hIZ

/-- From 127 (`r13` = `_so` readable): `endl (*_so)` (130), to 135 with `r13` kept. -/
theorem from127 (E : Ev prof F Wl L s₀ o gev gP gE S g0 e₂ code₂ j₂ I) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = bop_at.add 127) (hs : Y.cpu.gpr.rsp = aR S)
    (hb : Y.cpu.gpr.rbx = g0.rdi) (h14 : Y.cpu.gpr.r14 = g0.r14) (h15 : Y.cpu.gpr.r15 = g0.r15)
    (h13 : ∀ i < 8, Foot F.data (Addr.add Y.cpu.gpr.r13 i)) (hIW : I W) :
    GoG prof L o gev gP gE Y t := by
  refine (c_127 prof).run E.c E.hin (fun j' g' _ V' => j' = 130 ∧ V' = W ∧ g'.rsp = Y.cpu.gpr.rsp ∧
      g'.rbx = Y.cpu.gpr.rbx ∧ g'.r13 = Y.cpu.gpr.r13 ∧ g'.r14 = Y.cpu.gpr.r14 ∧ g'.r15 = Y.cpu.gpr.r15) hK hA hr
    (vc_127 fun _ a1 a2 a3 a4 a5 _ => ⟨rfl, rfl, a1, a2, a3, a4, a5⟩) ?_
  rintro j' g fl V₁ ⟨rfl, hV₁, gs, gb, g13, g14, g15⟩ U t₁ hKU hAU hrU hgU -
  subst V₁ hgU
  refine callK E hKU hAU hrU (gs.trans hs) (lt_len (by decide)) (call_130 _) tgt_130 E.cE (E.kE _ _ hIW) trivial
    ?_
  intro Z W' t₃ hKZ hAZ hrZ hsZ hkZ hBZ hIZ
  exact from135 E hKZ hAZ hrZ hsZ (hkZ.1.trans (gb.trans hb)) (hkZ.2.2.2.2.1.trans (g14.trans h14))
    (hkZ.2.2.2.2.2.trans (g15.trans h15)) (by rw [hkZ.2.2.2.1, g13]; exact h13) hIZ

/-- From 267 (back from `ClosePrint`): to 127 when `_so` is not null, else to 192. -/
theorem from267 (E : Ev prof F Wl L s₀ o gev gP gE S g0 e₂ code₂ j₂ I) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = bop_at.add 267) (hs : Y.cpu.gpr.rsp = aR S)
    (hb : Y.cpu.gpr.rbx = g0.rdi) (h14 : Y.cpu.gpr.r14 = g0.r14) (h15 : Y.cpu.gpr.r15 = g0.r15) (hIW : I W) :
    GoG prof L o gev gP gE Y t := by
  refine (c_267 prof).run E.c E.hin (fun j' g' _ V' => V' = W ∧ g'.rsp = Y.cpu.gpr.rsp ∧
      g'.rbx = Y.cpu.gpr.rbx ∧ g'.r14 = Y.cpu.gpr.r14 ∧ g'.r15 = Y.cpu.gpr.r15 ∧
      ((j' = 127 ∧ g'.r13 = rdq(W, Y.cpu.gpr.rbx + 264#64) ∧ g'.r13 ≠ 0) ∨ j' = 192)) hK hA hr
    (vc_267 (by rw [hb]; exact E.hrd) (fun _ a1 a2 a3 a4 a5 a6 _ => ⟨rfl, a1, a2, a3, a4, Or.inl ⟨rfl, a5, a6⟩⟩)
      fun _ a1 a2 a3 a4 _ => ⟨rfl, a1, a2, a3, a4, Or.inr rfl⟩) ?_
  rintro j' g fl V₁ ⟨hV₁, gs, gb, g14, g15, hj⟩ U t₁ hKU hAU hrU hgU -
  subst V₁ hgU
  rcases hj with ⟨rfl, g13, gnz⟩ | rfl
  · have e : U.cpu.gpr.r13 = rdq(W, g0.rdi + 264#64) := by rw [g13, hb]
    exact from127 E hKU hAU hrU (gs.trans hs) (gb.trans hb) (g14.trans h14) (g15.trans h15)
      (by rw [e]; exact E.hso W hIW (by rw [← e]; exact gnz)) hIW
  · exact from192 E hKU hAU hrU (gs.trans hs) (gb.trans hb) (g14.trans h14) (g15.trans h15) hIW

/-- From 240 (no printer, or quiet; `r13` = `_so`, readable when not null): to 127, or 221. -/
theorem from240 (E : Ev prof F Wl L s₀ o gev gP gE S g0 e₂ code₂ j₂ I) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = bop_at.add 240) (hs : Y.cpu.gpr.rsp = aR S)
    (hb : Y.cpu.gpr.rbx = g0.rdi) (h14 : Y.cpu.gpr.r14 = g0.r14) (h15 : Y.cpu.gpr.r15 = g0.r15)
    (hR : Y.cpu.gpr.r13 ≠ 0 → ∀ i < 8, Foot F.data (Addr.add Y.cpu.gpr.r13 i)) (hIW : I W) :
    GoG prof L o gev gP gE Y t := by
  refine (c_240 prof).run E.c E.hin (fun j' g' _ V' => V' = W ∧ g'.rsp = Y.cpu.gpr.rsp ∧
      g'.rbx = Y.cpu.gpr.rbx ∧ g'.r14 = Y.cpu.gpr.r14 ∧ g'.r15 = Y.cpu.gpr.r15 ∧
      ((j' = 127 ∧ g'.r13 = Y.cpu.gpr.r13 ∧ g'.r13 ≠ 0) ∨ j' = 221)) hK hA hr
    (vc_240 (fun _ a1 a2 a3 a4 a5 a6 _ => ⟨rfl, a1, a2, a3, a4, Or.inl ⟨rfl, a5, a6⟩⟩)
      fun _ a1 a2 a3 a4 _ => ⟨rfl, a1, a2, a3, a4, Or.inr rfl⟩) ?_
  rintro j' g fl V₁ ⟨hV₁, gs, gb, g14, g15, hj⟩ U t₁ hKU hAU hrU hgU -
  subst V₁ hgU
  rcases hj with ⟨rfl, g13, gnz⟩ | rfl
  · exact from127 E hKU hAU hrU (gs.trans hs) (gb.trans hb) (g14.trans h14) (g15.trans h15)
      (by rw [g13]; exact hR (by rw [← g13]; exact gnz)) hIW
  · exact from221 E hKU hAU hrU (gs.trans hs) (g14.trans h14) (g15.trans h15) hIW

/-- From 69 (after `NumTryArcs++`): to 240, `ClosePrint` (262) and 267, 205 or 127. -/
theorem from69 (E : Ev prof F Wl L s₀ o gev gP gE S g0 e₂ code₂ j₂ I) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = bop_at.add 69) (hs : Y.cpu.gpr.rsp = aR S)
    (hb : Y.cpu.gpr.rbx = g0.rdi) (h14 : Y.cpu.gpr.r14 = g0.r14) (h15 : Y.cpu.gpr.r15 = g0.r15) (hIW : I W) :
    GoG prof L o gev gP gE Y t := by
  refine (c_69 prof).run E.c E.hin (fun j' g' _ V' => I V' ∧ g'.rsp = Y.cpu.gpr.rsp ∧
      g'.rbx = Y.cpu.gpr.rbx ∧ g'.r14 = Y.cpu.gpr.r14 ∧ g'.r15 = Y.cpu.gpr.r15 ∧
      ((j' = 240 ∧ g'.r13 = rdq(W, Y.cpu.gpr.rbx + 264#64)) ∨ j' = 262 ∨ j' = 205 ∨
        (j' = 127 ∧ g'.r13 = rdq(W, Y.cpu.gpr.rbx + 264#64) ∧ g'.r13 ≠ 0))) hK hA hr
    (vc_69 (by rw [hb]; exact E.hob) (by rw [hb]; exact E.hrd) (by rw [hb]; exact E.hcl) hIW
      (fun _ _ a0 a1 a2 a3 a4 a5 _ => ⟨a0, a1, a2, a3, a4, Or.inl ⟨rfl, a5⟩⟩)
      (fun _ _ a0 a1 a2 a3 a4 _ => ⟨a0, a1, a2, a3, a4, Or.inr (Or.inl rfl)⟩)
      (fun _ _ a0 a1 a2 a3 a4 _ => ⟨a0, a1, a2, a3, a4, Or.inr (Or.inr (Or.inl rfl))⟩)
      fun _ _ a0 a1 a2 a3 a4 a5 a6 _ => ⟨a0, a1, a2, a3, a4, Or.inr (Or.inr (Or.inr ⟨rfl, a5, a6⟩))⟩) ?_
  rintro j' g fl V₁ ⟨hI1, gs, gb, g14, g15, hj⟩ U t₁ hKU hAU hrU hgU -
  subst hgU
  rcases hj with ⟨rfl, g13⟩ | rfl | rfl | ⟨rfl, g13, gnz⟩
  · have e : U.cpu.gpr.r13 = rdq(W, g0.rdi + 264#64) := by rw [g13, hb]
    exact from240 E hKU hAU hrU (gs.trans hs) (gb.trans hb) (g14.trans h14) (g15.trans h15)
      (fun hz => by rw [e]; exact E.hso W hIW (by rw [← e]; exact hz)) hI1
  · refine callK E hKU hAU hrU (gs.trans hs) (lt_len (by decide)) (call_262 _) tgt_262 E.cC (E.kC _ _ hI1)
      trivial ?_
    intro Z W' t₃ hKZ hAZ hrZ hsZ hkZ hBZ hIZ
    exact from267 E hKZ hAZ hrZ hsZ (hkZ.1.trans (gb.trans hb)) (hkZ.2.2.2.2.1.trans (g14.trans h14))
      (hkZ.2.2.2.2.2.trans (g15.trans h15)) hIZ
  · exact from205 E hKU hAU hrU (gs.trans hs) (gb.trans hb) (g14.trans h14) (g15.trans h15) hI1
  · have e : U.cpu.gpr.r13 = rdq(W, g0.rdi + 264#64) := by rw [g13, hb]
    exact from127 E hKU hAU hrU (gs.trans hs) (gb.trans hb) (g14.trans h14) (g15.trans h15)
      (by rw [e]; exact E.hso W hIW (by rw [← e]; exact gnz)) hI1

/-- From 61 (`rbx` = `this`): `add qword [rbx + 0x180], 1` (`NumTryArcs++`), to 69. -/
theorem from61 (E : Ev prof F Wl L s₀ o gev gP gE S g0 e₂ code₂ j₂ I) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = bop_at.add 61) (hs : Y.cpu.gpr.rsp = aR S)
    (hb : Y.cpu.gpr.rbx = g0.rdi) (h14 : Y.cpu.gpr.r14 = g0.r14) (h15 : Y.cpu.gpr.r15 = g0.r15) (hIW : I W) :
    GoG prof L o gev gP gE Y t := by
  have ea : eaD Y 3 384 = g0.rdi + 384#64 := by
    rw [eaD]
    show Y.cpu.gpr.rbx + _ = _
    rw [hb]
  refine E.c.s_add_mi64 hK hA E.hin (lt_len (by decide)) hr (add_61 _)
    (by rw [ea]; exact E.hob 384#64 8 (by decide)) ?_
  rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
  rw [ea] at hA₂
  exact from69 E hK₂ hA₂ hr₂ (by rw [hg₂]; exact hs) (by rw [hg₂]; exact hb) (by rw [hg₂]; exact h14)
    (by rw [hg₂]; exact h15) (E.hcl _ _ _ _ (toBytesLE_length _ _) (by decide) hIW)

/-- From 35 (back from `UString::operator=`): to the `add` at 61, or `E_ABORT` and 223. -/
theorem from35 (E : Ev prof F Wl L s₀ o gev gP gE S g0 e₂ code₂ j₂ I) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = bop_at.add 35) (hs : Y.cpu.gpr.rsp = aR S)
    (hb : Y.cpu.gpr.rbx = g0.rdi) (h14 : Y.cpu.gpr.r14 = g0.r14) (h15 : Y.cpu.gpr.r15 = g0.r15) (hIW : I W) :
    GoG prof L o gev gP gE Y t := by
  refine (c_35 prof).run E.c E.hin (fun j' g' _ V' => I V' ∧ g'.rsp = Y.cpu.gpr.rsp ∧
      g'.rbx = Y.cpu.gpr.rbx ∧ g'.r14 = Y.cpu.gpr.r14 ∧ g'.r15 = Y.cpu.gpr.r15 ∧ (j' = 61 ∨ j' = 223)) hK hA hr
    (vc_35 (by rw [hb]; exact E.hob) (by rw [hb]; exact E.hcl) hIW E.hbr
      (fun _ _ a0 a1 a2 a3 a4 _ => ⟨a0, a1, a2, a3, a4, Or.inl rfl⟩)
      fun _ _ a0 a1 a2 a3 a4 _ => ⟨a0, a1, a2, a3, a4, Or.inr rfl⟩) ?_
  rintro j' g fl V₁ ⟨hI1, gs, gb, g14, g15, hj⟩ U t₁ hKU hAU hrU hgU -
  subst hgU
  rcases hj with rfl | rfl
  · exact from61 E hKU hAU hrU (gs.trans hs) (gb.trans hb) (g14.trans h14) (g15.trans h15) hI1
  · exact from223 E hKU hAU hrU (gs.trans hs) (g14.trans h14) (g15.trans h15) hI1

end Runs

section Main
variable {prof : Profile} {F : Footprint} {Wl : List Rgn} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {e₂ : Addr} {code₂ : List Byte} {j₂ : Nat} {I : (Addr → Byte) → Prop}
  {X : State} {t : Nat} {V : Addr → Byte}

/-- `CExtractCallbackConsole::BeforeOpen` from its entry. -/
theorem bop_ok (E : Ev prof F Wl L s₀ o gev gP gE X.cpu.gpr.rsp X.cpu.gpr e₂ code₂ j₂ I)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = bop_at)
    (hI0 : I (P4 V X.cpu.gpr)) :
    GoG prof L o gev gP gE X t := by
  refine (c_0 prof).run E.c E.hin (fun j' g' _ V' => j' = 30 ∧ V' = P4 V X.cpu.gpr ∧
      g'.rsp = aR X.cpu.gpr.rsp ∧ g'.rbx = X.cpu.gpr.rdi ∧ g'.r14 = X.cpu.gpr.r14 ∧ g'.r15 = X.cpu.gpr.r15)
    hK hA (by rw [addr_add_zero]; exact hrip)
    (vc_0 E.hs1 E.hs2 E.hs3 E.hs4 fun _ a1 a2 a3 a4 _ => ⟨rfl, rfl, a1, a2, a3, a4⟩) ?_
  rintro j' g fl V₁ ⟨rfl, hV₁, gs, gb, g14, g15⟩ U t₁ hKU hAU hrU hgU -
  subst V₁ hgU
  refine callK E hKU hAU hrU gs (lt_len (by decide)) (call_30 _) tgt_30 E.cU (E.kU _ _ hI0) trivial ?_
  intro Z W' t₃ hKZ hAZ hrZ hsZ hkZ hBZ hIZ
  exact from35 E hKZ hAZ hrZ hsZ (hkZ.1.trans gb) (hkZ.2.2.2.2.1.trans g14) (hkZ.2.2.2.2.2.trans g15) hIZ

end Main

end FV7z.Bop
