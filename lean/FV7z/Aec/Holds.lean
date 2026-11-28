import FV7z.Aec.Pieces1
import FV7z.Aec.Pieces2
/-!
# `CArchiveExtractCallback::CArchiveExtractCallback` (0x5b0040): from the entry to the return (PLAN.md §M, M1)

`CArchiveExtractCallback::CArchiveExtractCallback ()`: `rdi` = `this`. One theorem for each hop: `fromN` runs the
piece at `N` (and the `call` that ends it, `callK`, with the callee as `Ev`'s continuation) and goes on by
`fromM`, from the `ret` (`from679`) back to the entry (`from23`, `aec_ok`). Each takes `rsp` = `aR S`, `rbx` = `this`
(from 61 on), `r15` as at the entry (the code and the callees keep it) and `I` of the bytes.

- `aec_ok`: from the entry (the hypotheses `E : Ev …` with `S` = the entry's `rsp`, `g0` = its registers, `I` of
  the bytes after the five pushes) to the return (`Ev.kr`: `rsp` 8 up, the callee-saved registers as at the entry,
  `I` of the bytes) or a callee's goal.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
open FV7z.Api (KS)
namespace FV7z.Aec
set_option linter.unusedVariables false

section Runs
variable {prof : Profile} {F : Footprint} {Wl : List Rgn} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {S : Addr} {g0 : Gprs} {e₂ : Addr} {code₂ : List Byte} {j₂ : Nat} {I : (Addr → Byte) → Prop}
  {Y : State} {t : Nat} {W : Addr → Byte}

/-- From 679 (`rsp` = `aR S`, the bytes `W` with `I`): the pops, the `ret`, to `kr`. -/
theorem from679 (E : Ev prof F Wl L s₀ o gev gP gE S g0 e₂ code₂ j₂ I) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = aec_at.add 679) (hs : Y.cpu.gpr.rsp = aR S)
    (h15 : Y.cpu.gpr.r15 = g0.r15) (hIW : I W) :
    GoG prof L o gev gP gE Y t := by
  obtain ⟨s1, s2, s3, s4, s5, s6⟩ := E.hI W hIW
  have e1 : rdq(W, Y.cpu.gpr.rsp) = g0.rbx := by rw [hs]; exact s1
  have e2 : rdq(W, Y.cpu.gpr.rsp + 8) = g0.rbp := by rw [hs, r1]; exact s2
  have e3 : rdq(W, Y.cpu.gpr.rsp + 8 + 8) = g0.r12 := by rw [hs, r1, r2]; exact s3
  have e4 : rdq(W, Y.cpu.gpr.rsp + 8 + 8 + 8) = g0.r13 := by rw [hs, r1, r2, r3]; exact s4
  have e5 : rdq(W, Y.cpu.gpr.rsp + 8 + 8 + 8 + 8) = g0.r14 := by rw [hs, r1, r2, r3, r4]; exact s5
  have es : Y.cpu.gpr.rsp + 8 + 8 + 8 + 8 + 8 = S := by rw [hs, r1, r2, r3, r4, r5]
  refine (c_679 prof).run E.c E.hin (fun j' g' _ V' => j' = 687 ∧ V' = W ∧ g'.rsp = S ∧ KS g0 g') hK hA hr
    (vc_679 (by rw [hs]; exact fun i hi => E.c.hws _ (E.hs5 i hi))
      (by rw [hs, r1]; exact fun i hi => E.c.hws _ (E.hs4 i hi))
      (by rw [hs, r1, r2]; exact fun i hi => E.c.hws _ (E.hs3 i hi))
      (by rw [hs, r1, r2, r3]; exact fun i hi => E.c.hws _ (E.hs2 i hi))
      (by rw [hs, r1, r2, r3, r4]; exact fun i hi => E.c.hws _ (E.hs1 i hi))
      fun _ a1 a2 a3 a4 a5 a6 a7 _ => ⟨rfl, rfl, a1.trans es, a2.trans e1, a3.trans e2, a4.trans e3, a5.trans e4,
        a6.trans e5, a7.trans h15⟩) ?_
  rintro j' g fl V₁ ⟨rfl, hV₁, gs, gk⟩ Z t₁ hKZ hAZ hrZ hgZ -
  subst V₁ hgZ
  refine E.c.s_ret hKZ hAZ E.hin (lt_len (by decide)) hrZ (ret_687 _) (by rw [gs]; exact E.hl) E.hin₂ E.h₂
    (by rw [gs]; exact s6) ?_
  rintro Z' t₂ hKZ' hAZ' ⟨hrZ', hgZ'⟩
  refine E.kr W Z' t₂ hKZ' hAZ' hrZ' ?_ ?_ hIW
  · rw [hgZ']
    show Z.cpu.gpr.rsp + 8 = _
    rw [gs]
  · rw [hgZ']
    exact gk

/-- From 657: the last two fields, to 679. -/
theorem from657 (E : Ev prof F Wl L s₀ o gev gP gE S g0 e₂ code₂ j₂ I) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = aec_at.add 657) (hs : Y.cpu.gpr.rsp = aR S)
    (hb : Y.cpu.gpr.rbx = g0.rdi) (h15 : Y.cpu.gpr.r15 = g0.r15) (hIW : I W) :
    GoG prof L o gev gP gE Y t := by
  refine (c_657 prof).run E.c E.hin (fun j' g' _ V' => j' = 679 ∧ I V' ∧ g'.rsp = Y.cpu.gpr.rsp ∧
      g'.rbx = Y.cpu.gpr.rbx ∧ g'.r15 = Y.cpu.gpr.r15) hK hA hr
    (vc_657 (by rw [hb]; exact E.hob) (by rw [hb]; exact E.hcl) hIW
      fun _ _ a1 a2 a3 a4 _ => ⟨rfl, a1, a2, a3, a4⟩) ?_
  rintro j' g fl V₁ ⟨rfl, hI1, gs, gb, g15⟩ U t₁ hKU hAU hrU hgU -
  subst hgU
  exact from679 E hKU hAU hrU (gs.trans hs) (g15.trans h15) hI1

/-- From 613: the fields to `this + 668`, the `UString` at `this + 672` (652). -/
theorem from613 (E : Ev prof F Wl L s₀ o gev gP gE S g0 e₂ code₂ j₂ I) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = aec_at.add 613) (hs : Y.cpu.gpr.rsp = aR S)
    (hb : Y.cpu.gpr.rbx = g0.rdi) (h15 : Y.cpu.gpr.r15 = g0.r15) (hIW : I W) :
    GoG prof L o gev gP gE Y t := by
  refine (c_613 prof).run E.c E.hin (fun j' g' _ V' => j' = 652 ∧ I V' ∧ g'.rsp = Y.cpu.gpr.rsp ∧
      g'.rbx = Y.cpu.gpr.rbx ∧ g'.r15 = Y.cpu.gpr.r15) hK hA hr
    (vc_613 (by rw [hb]; exact E.hob) (by rw [hb]; exact E.hcl) hIW
      fun _ _ a1 a2 a3 a4 _ => ⟨rfl, a1, a2, a3, a4⟩) ?_
  rintro j' g fl V₁ ⟨rfl, hI1, gs, gb, g15⟩ U t₁ hKU hAU hrU hgU -
  subst hgU
  refine callK E hKU hAU hrU (gs.trans hs) (lt_len (by decide)) (call_652 _) tgt_652 E.cU (E.kU _ _ hI1) trivial
    ?_
  intro Z W' t₃ hKZ hAZ hrZ hsZ hkZ hBZ hIZ
  exact from657 E hKZ hAZ hrZ hsZ (hkZ.1.trans (gb.trans hb)) (hkZ.2.2.2.2.2.trans (g15.trans h15)) hIZ

/-- From 560 (back from the `AString` at `this + 600`): the fields to `this + 640`, to 613. -/
theorem from560 (E : Ev prof F Wl L s₀ o gev gP gE S g0 e₂ code₂ j₂ I) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = aec_at.add 560) (hs : Y.cpu.gpr.rsp = aR S)
    (hb : Y.cpu.gpr.rbx = g0.rdi) (h15 : Y.cpu.gpr.r15 = g0.r15) (hIW : I W) :
    GoG prof L o gev gP gE Y t := by
  refine (c_560 prof).run E.c E.hin (fun j' g' _ V' => j' = 613 ∧ I V' ∧ g'.rsp = Y.cpu.gpr.rsp ∧
      g'.rbx = Y.cpu.gpr.rbx ∧ g'.r15 = Y.cpu.gpr.r15) hK hA hr
    (vc_560 (by rw [hb]; exact E.hob) (by rw [hb]; exact E.hcl) hIW
      fun _ _ a1 a2 a3 a4 _ => ⟨rfl, a1, a2, a3, a4⟩) ?_
  rintro j' g fl V₁ ⟨rfl, hI1, gs, gb, g15⟩ U t₁ hKU hAU hrU hgU -
  subst hgU
  exact from613 E hKU hAU hrU (gs.trans hs) (gb.trans hb) (g15.trans h15) hI1

/-- From 541: the new object at `this + 552`, the `AString` at `this + 600` (555). -/
theorem from541 (E : Ev prof F Wl L s₀ o gev gP gE S g0 e₂ code₂ j₂ I) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = aec_at.add 541) (hs : Y.cpu.gpr.rsp = aR S)
    (hb : Y.cpu.gpr.rbx = g0.rdi) (h15 : Y.cpu.gpr.r15 = g0.r15) (hIW : I W) :
    GoG prof L o gev gP gE Y t := by
  refine (c_541 prof).run E.c E.hin (fun j' g' _ V' => j' = 555 ∧ I V' ∧ g'.rsp = Y.cpu.gpr.rsp ∧
      g'.rbx = Y.cpu.gpr.rbx ∧ g'.r15 = Y.cpu.gpr.r15) hK hA hr
    (vc_541 (by rw [hb]; exact E.hob) (by rw [hb]; exact E.hcl) hIW
      fun _ _ a1 a2 a3 a4 _ => ⟨rfl, a1, a2, a3, a4⟩) ?_
  rintro j' g fl V₁ ⟨rfl, hI1, gs, gb, g15⟩ U t₁ hKU hAU hrU hgU -
  subst hgU
  refine callK E hKU hAU hrU (gs.trans hs) (lt_len (by decide)) (call_555 _) tgt_555 E.cA (E.kA _ _ hI1) trivial
    ?_
  intro Z W' t₃ hKZ hAZ hrZ hsZ hkZ hBZ hIZ
  exact from560 E hKZ hAZ hrZ hsZ (hkZ.1.trans (gb.trans hb)) (hkZ.2.2.2.2.2.trans (g15.trans h15)) hIZ

/-- From 537 (back from the `CLocalProgress` constructor, `rbp` = the new object `p`): `add dword [rbp + 8], 1`
(`AddRef`), to 541. -/
theorem from537 (E : Ev prof F Wl L s₀ o gev gP gE S g0 e₂ code₂ j₂ I) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = aec_at.add 537) (hs : Y.cpu.gpr.rsp = aR S)
    (hb : Y.cpu.gpr.rbx = g0.rdi) (h15 : Y.cpu.gpr.r15 = g0.r15) {p : Addr} (hp : Y.cpu.gpr.rbp = p)
    (hn : Nw Wl I p) (hIW : I W) :
    GoG prof L o gev gP gE Y t := by
  have ea : eaD Y 5 8 = p + 8#64 := by
    rw [eaD]
    show Y.cpu.gpr.rbp + _ = _
    rw [hp]
  refine E.c.s_add_mi32 hK hA E.hin (lt_len (by decide)) hr (add_537 _) (by rw [ea]; exact hn.1) ?_
  rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
  rw [ea] at hA₂
  exact from541 E hK₂ hA₂ hr₂ (by rw [hg₂]; exact hs) (by rw [hg₂]; exact hb) (by rw [hg₂]; exact h15)
    (hn.2 _ _ (toBytesLE_length _ _) hIW)

/-- From 526 (back from `operator new` with the new object `p` = `rax`): `rdi` = `rbp` = `p`, the
`CLocalProgress` constructor (532), to 537 with `rbp` kept. -/
theorem from526 (E : Ev prof F Wl L s₀ o gev gP gE S g0 e₂ code₂ j₂ I) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = aec_at.add 526) (hs : Y.cpu.gpr.rsp = aR S)
    (hb : Y.cpu.gpr.rbx = g0.rdi) (h15 : Y.cpu.gpr.r15 = g0.r15) (hn : Nw Wl I Y.cpu.gpr.rax) (hIW : I W) :
    GoG prof L o gev gP gE Y t := by
  refine (c_526 prof).run E.c E.hin (fun j' g' _ V' => j' = 532 ∧ V' = W ∧ g'.rsp = Y.cpu.gpr.rsp ∧
      g'.rbx = Y.cpu.gpr.rbx ∧ g'.r15 = Y.cpu.gpr.r15 ∧ g'.rbp = Y.cpu.gpr.rax) hK hA hr
    (vc_526 fun _ a1 a2 a3 a4 _ => ⟨rfl, rfl, a1, a2, a3, a4⟩) ?_
  rintro j' g fl V₁ ⟨rfl, hV₁, gs, gb, g15, gbp⟩ U t₁ hKU hAU hrU hgU -
  subst V₁ hgU
  refine callK E hKU hAU hrU (gs.trans hs) (lt_len (by decide)) (call_532 _) tgt_532 E.cL (E.kL _ _ hIW) trivial
    ?_
  intro Z W' t₃ hKZ hAZ hrZ hsZ hkZ hBZ hIZ
  exact from537 E hKZ hAZ hrZ hsZ (hkZ.1.trans (gb.trans hb)) (hkZ.2.2.2.2.2.trans (g15.trans h15))
    (hkZ.2.1.trans gbp) hn hIZ

/-- From 477: the fields to `this + 544`, `operator new (56)` (521). -/
theorem from477 (E : Ev prof F Wl L s₀ o gev gP gE S g0 e₂ code₂ j₂ I) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = aec_at.add 477) (hs : Y.cpu.gpr.rsp = aR S)
    (hb : Y.cpu.gpr.rbx = g0.rdi) (h15 : Y.cpu.gpr.r15 = g0.r15) (hIW : I W) :
    GoG prof L o gev gP gE Y t := by
  refine (c_477 prof).run E.c E.hin (fun j' g' _ V' => j' = 521 ∧ I V' ∧ g'.rsp = Y.cpu.gpr.rsp ∧
      g'.rbx = Y.cpu.gpr.rbx ∧ g'.r15 = Y.cpu.gpr.r15) hK hA hr
    (vc_477 (by rw [hb]; exact E.hob) (by rw [hb]; exact E.hcl) hIW
      fun _ _ a1 a2 a3 a4 _ => ⟨rfl, a1, a2, a3, a4⟩) ?_
  rintro j' g fl V₁ ⟨rfl, hI1, gs, gb, g15⟩ U t₁ hKU hAU hrU hgU -
  subst hgU
  refine callK E hKU hAU hrU (gs.trans hs) (lt_len (by decide)) (call_521 _) tgt_521 E.cN (E.kN _ _ hI1) trivial
    ?_
  intro Z W' t₃ hKZ hAZ hrZ hsZ hkZ hBZ hIZ
  exact from526 E hKZ hAZ hrZ hsZ (hkZ.1.trans (gb.trans hb)) (hkZ.2.2.2.2.2.trans (g15.trans h15)) hBZ hIZ

/-- From 417 (back from the `AString` at `this + 384`): the fields to `this + 488`, to 477. -/
theorem from417 (E : Ev prof F Wl L s₀ o gev gP gE S g0 e₂ code₂ j₂ I) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = aec_at.add 417) (hs : Y.cpu.gpr.rsp = aR S)
    (hb : Y.cpu.gpr.rbx = g0.rdi) (h15 : Y.cpu.gpr.r15 = g0.r15) (hIW : I W) :
    GoG prof L o gev gP gE Y t := by
  refine (c_417 prof).run E.c E.hin (fun j' g' _ V' => j' = 477 ∧ I V' ∧ g'.rsp = Y.cpu.gpr.rsp ∧
      g'.rbx = Y.cpu.gpr.rbx ∧ g'.r15 = Y.cpu.gpr.r15) hK hA hr
    (vc_417 (by rw [hb]; exact E.hob) (by rw [hb]; exact E.hcl) hIW
      fun _ _ a1 a2 a3 a4 _ => ⟨rfl, a1, a2, a3, a4⟩) ?_
  rintro j' g fl V₁ ⟨rfl, hI1, gs, gb, g15⟩ U t₁ hKU hAU hrU hgU -
  subst hgU
  exact from477 E hKU hAU hrU (gs.trans hs) (gb.trans hb) (g15.trans h15) hI1

/-- From 405: the `AString` at `this + 384` (412). -/
theorem from405 (E : Ev prof F Wl L s₀ o gev gP gE S g0 e₂ code₂ j₂ I) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = aec_at.add 405) (hs : Y.cpu.gpr.rsp = aR S)
    (hb : Y.cpu.gpr.rbx = g0.rdi) (h15 : Y.cpu.gpr.r15 = g0.r15) (hIW : I W) :
    GoG prof L o gev gP gE Y t := by
  refine (c_405 prof).run E.c E.hin (fun j' g' _ V' => j' = 412 ∧ V' = W ∧ g'.rsp = Y.cpu.gpr.rsp ∧
      g'.rbx = Y.cpu.gpr.rbx ∧ g'.r15 = Y.cpu.gpr.r15) hK hA hr
    (vc_405 fun _ a1 a2 a3 _ => ⟨rfl, rfl, a1, a2, a3⟩) ?_
  rintro j' g fl V₁ ⟨rfl, hV₁, gs, gb, g15⟩ U t₁ hKU hAU hrU hgU -
  subst V₁ hgU
  have hI1 := hIW
  refine callK E hKU hAU hrU (gs.trans hs) (lt_len (by decide)) (call_412 _) tgt_412 E.cA (E.kA _ _ hI1) trivial
    ?_
  intro Z W' t₃ hKZ hAZ hrZ hsZ hkZ hBZ hIZ
  exact from417 E hKZ hAZ hrZ hsZ (hkZ.1.trans (gb.trans hb)) (hkZ.2.2.2.2.2.trans (g15.trans h15)) hIZ

/-- From 339: the fields to `this + 336`, the `AString` at `this + 360` (400). -/
theorem from339 (E : Ev prof F Wl L s₀ o gev gP gE S g0 e₂ code₂ j₂ I) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = aec_at.add 339) (hs : Y.cpu.gpr.rsp = aR S)
    (hb : Y.cpu.gpr.rbx = g0.rdi) (h15 : Y.cpu.gpr.r15 = g0.r15) (hIW : I W) :
    GoG prof L o gev gP gE Y t := by
  refine (c_339 prof).run E.c E.hin (fun j' g' _ V' => j' = 400 ∧ I V' ∧ g'.rsp = Y.cpu.gpr.rsp ∧
      g'.rbx = Y.cpu.gpr.rbx ∧ g'.r15 = Y.cpu.gpr.r15) hK hA hr
    (vc_339 (by rw [hb]; exact E.hob) (by rw [hb]; exact E.hcl) hIW
      fun _ _ a1 a2 a3 a4 _ => ⟨rfl, a1, a2, a3, a4⟩) ?_
  rintro j' g fl V₁ ⟨rfl, hI1, gs, gb, g15⟩ U t₁ hKU hAU hrU hgU -
  subst hgU
  refine callK E hKU hAU hrU (gs.trans hs) (lt_len (by decide)) (call_400 _) tgt_400 E.cA (E.kA _ _ hI1) trivial
    ?_
  intro Z W' t₃ hKZ hAZ hrZ hsZ hkZ hBZ hIZ
  exact from405 E hKZ hAZ hrZ hsZ (hkZ.1.trans (gb.trans hb)) (hkZ.2.2.2.2.2.trans (g15.trans h15)) hIZ

/-- From 303: the fields at `this + 273` to `+ 284`, the `AString` at `this + 288` (334). -/
theorem from303 (E : Ev prof F Wl L s₀ o gev gP gE S g0 e₂ code₂ j₂ I) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = aec_at.add 303) (hs : Y.cpu.gpr.rsp = aR S)
    (hb : Y.cpu.gpr.rbx = g0.rdi) (h15 : Y.cpu.gpr.r15 = g0.r15) (hIW : I W) :
    GoG prof L o gev gP gE Y t := by
  refine (c_303 prof).run E.c E.hin (fun j' g' _ V' => j' = 334 ∧ I V' ∧ g'.rsp = Y.cpu.gpr.rsp ∧
      g'.rbx = Y.cpu.gpr.rbx ∧ g'.r15 = Y.cpu.gpr.r15) hK hA hr
    (vc_303 (by rw [hb]; exact E.hob) (by rw [hb]; exact E.hcl) hIW
      fun _ _ a1 a2 a3 a4 _ => ⟨rfl, a1, a2, a3, a4⟩) ?_
  rintro j' g fl V₁ ⟨rfl, hI1, gs, gb, g15⟩ U t₁ hKU hAU hrU hgU -
  subst hgU
  refine callK E hKU hAU hrU (gs.trans hs) (lt_len (by decide)) (call_334 _) tgt_334 E.cA (E.kA _ _ hI1) trivial
    ?_
  intro Z W' t₃ hKZ hAZ hrZ hsZ hkZ hBZ hIZ
  exact from339 E hKZ hAZ hrZ hsZ (hkZ.1.trans (gb.trans hb)) (hkZ.2.2.2.2.2.trans (g15.trans h15)) hIZ

/-- From 291: the `UString` at `this + 256` (298). -/
theorem from291 (E : Ev prof F Wl L s₀ o gev gP gE S g0 e₂ code₂ j₂ I) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = aec_at.add 291) (hs : Y.cpu.gpr.rsp = aR S)
    (hb : Y.cpu.gpr.rbx = g0.rdi) (h15 : Y.cpu.gpr.r15 = g0.r15) (hIW : I W) :
    GoG prof L o gev gP gE Y t := by
  refine (c_291 prof).run E.c E.hin (fun j' g' _ V' => j' = 298 ∧ V' = W ∧ g'.rsp = Y.cpu.gpr.rsp ∧
      g'.rbx = Y.cpu.gpr.rbx ∧ g'.r15 = Y.cpu.gpr.r15) hK hA hr
    (vc_291 fun _ a1 a2 a3 _ => ⟨rfl, rfl, a1, a2, a3⟩) ?_
  rintro j' g fl V₁ ⟨rfl, hV₁, gs, gb, g15⟩ U t₁ hKU hAU hrU hgU -
  subst V₁ hgU
  have hI1 := hIW
  refine callK E hKU hAU hrU (gs.trans hs) (lt_len (by decide)) (call_298 _) tgt_298 E.cU (E.kU _ _ hI1) trivial
    ?_
  intro Z W' t₃ hKZ hAZ hrZ hsZ hkZ hBZ hIZ
  exact from303 E hKZ hAZ hrZ hsZ (hkZ.1.trans (gb.trans hb)) (hkZ.2.2.2.2.2.trans (g15.trans h15)) hIZ

/-- From 257: the fields at `this + 224`, `+ 232`, the `UString` at `this + 240` (286). -/
theorem from257 (E : Ev prof F Wl L s₀ o gev gP gE S g0 e₂ code₂ j₂ I) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = aec_at.add 257) (hs : Y.cpu.gpr.rsp = aR S)
    (hb : Y.cpu.gpr.rbx = g0.rdi) (h15 : Y.cpu.gpr.r15 = g0.r15) (hIW : I W) :
    GoG prof L o gev gP gE Y t := by
  refine (c_257 prof).run E.c E.hin (fun j' g' _ V' => j' = 286 ∧ I V' ∧ g'.rsp = Y.cpu.gpr.rsp ∧
      g'.rbx = Y.cpu.gpr.rbx ∧ g'.r15 = Y.cpu.gpr.r15) hK hA hr
    (vc_257 (by rw [hb]; exact E.hob) (by rw [hb]; exact E.hcl) hIW
      fun _ _ a1 a2 a3 a4 _ => ⟨rfl, a1, a2, a3, a4⟩) ?_
  rintro j' g fl V₁ ⟨rfl, hI1, gs, gb, g15⟩ U t₁ hKU hAU hrU hgU -
  subst hgU
  refine callK E hKU hAU hrU (gs.trans hs) (lt_len (by decide)) (call_286 _) tgt_286 E.cU (E.kU _ _ hI1) trivial
    ?_
  intro Z W' t₃ hKZ hAZ hrZ hsZ hkZ hBZ hIZ
  exact from291 E hKZ hAZ hrZ hsZ (hkZ.1.trans (gb.trans hb)) (hkZ.2.2.2.2.2.trans (g15.trans h15)) hIZ

/-- From 220: the fields at `this + 192`, `+ 200`, the `UString` at `this + 208` (252). -/
theorem from220 (E : Ev prof F Wl L s₀ o gev gP gE S g0 e₂ code₂ j₂ I) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = aec_at.add 220) (hs : Y.cpu.gpr.rsp = aR S)
    (hb : Y.cpu.gpr.rbx = g0.rdi) (h15 : Y.cpu.gpr.r15 = g0.r15) (hIW : I W) :
    GoG prof L o gev gP gE Y t := by
  refine (c_220 prof).run E.c E.hin (fun j' g' _ V' => j' = 252 ∧ I V' ∧ g'.rsp = Y.cpu.gpr.rsp ∧
      g'.rbx = Y.cpu.gpr.rbx ∧ g'.r15 = Y.cpu.gpr.r15) hK hA hr
    (vc_220 (by rw [hb]; exact E.hob) (by rw [hb]; exact E.hcl) hIW
      fun _ _ a1 a2 a3 a4 _ => ⟨rfl, a1, a2, a3, a4⟩) ?_
  rintro j' g fl V₁ ⟨rfl, hI1, gs, gb, g15⟩ U t₁ hKU hAU hrU hgU -
  subst hgU
  refine callK E hKU hAU hrU (gs.trans hs) (lt_len (by decide)) (call_252 _) tgt_252 E.cU (E.kU _ _ hI1) trivial
    ?_
  intro Z W' t₃ hKZ hAZ hrZ hsZ hkZ hBZ hIZ
  exact from257 E hKZ hAZ hrZ hsZ (hkZ.1.trans (gb.trans hb)) (hkZ.2.2.2.2.2.trans (g15.trans h15)) hIZ

/-- From 208: the `AString` at `this + 176` (215). -/
theorem from208 (E : Ev prof F Wl L s₀ o gev gP gE S g0 e₂ code₂ j₂ I) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = aec_at.add 208) (hs : Y.cpu.gpr.rsp = aR S)
    (hb : Y.cpu.gpr.rbx = g0.rdi) (h15 : Y.cpu.gpr.r15 = g0.r15) (hIW : I W) :
    GoG prof L o gev gP gE Y t := by
  refine (c_208 prof).run E.c E.hin (fun j' g' _ V' => j' = 215 ∧ V' = W ∧ g'.rsp = Y.cpu.gpr.rsp ∧
      g'.rbx = Y.cpu.gpr.rbx ∧ g'.r15 = Y.cpu.gpr.r15) hK hA hr
    (vc_208 fun _ a1 a2 a3 _ => ⟨rfl, rfl, a1, a2, a3⟩) ?_
  rintro j' g fl V₁ ⟨rfl, hV₁, gs, gb, g15⟩ U t₁ hKU hAU hrU hgU -
  subst V₁ hgU
  have hI1 := hIW
  refine callK E hKU hAU hrU (gs.trans hs) (lt_len (by decide)) (call_215 _) tgt_215 E.cA (E.kA _ _ hI1) trivial
    ?_
  intro Z W' t₃ hKZ hAZ hrZ hsZ hkZ hBZ hIZ
  exact from220 E hKZ hAZ hrZ hsZ (hkZ.1.trans (gb.trans hb)) (hkZ.2.2.2.2.2.trans (g15.trans h15)) hIZ

/-- From 171 (`rdi` = `this + 160`): the fields to `this + 152`, the `AString` at `this + 160` (203). -/
theorem from171 (E : Ev prof F Wl L s₀ o gev gP gE S g0 e₂ code₂ j₂ I) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = aec_at.add 171) (hs : Y.cpu.gpr.rsp = aR S)
    (hb : Y.cpu.gpr.rbx = g0.rdi) (h15 : Y.cpu.gpr.r15 = g0.r15)
    (hdi : Y.cpu.gpr.rdi = Y.cpu.gpr.rbx + 160#64) (hIW : I W) :
    GoG prof L o gev gP gE Y t := by
  refine (c_171 prof).run E.c E.hin (fun j' g' _ V' => j' = 203 ∧ I V' ∧ g'.rsp = Y.cpu.gpr.rsp ∧
      g'.rbx = Y.cpu.gpr.rbx ∧ g'.r15 = Y.cpu.gpr.r15) hK hA hr
    (vc_171 hdi (by rw [hb]; exact E.hob) (by rw [hb]; exact E.hcl) hIW
      fun _ _ a1 a2 a3 a4 _ => ⟨rfl, a1, a2, a3, a4⟩) ?_
  rintro j' g fl V₁ ⟨rfl, hI1, gs, gb, g15⟩ U t₁ hKU hAU hrU hgU -
  subst hgU
  refine callK E hKU hAU hrU (gs.trans hs) (lt_len (by decide)) (call_203 _) tgt_203 E.cA (E.kA _ _ hI1) trivial
    ?_
  intro Z W' t₃ hKZ hAZ hrZ hsZ hkZ hBZ hIZ
  exact from208 E hKZ hAZ hrZ hsZ (hkZ.1.trans (gb.trans hb)) (hkZ.2.2.2.2.2.trans (g15.trans h15)) hIZ

/-- From 133 (`rdi` = `this + 160`): the fields at `this + 63` to `+ 96`, to 171. -/
theorem from133 (E : Ev prof F Wl L s₀ o gev gP gE S g0 e₂ code₂ j₂ I) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = aec_at.add 133) (hs : Y.cpu.gpr.rsp = aR S)
    (hb : Y.cpu.gpr.rbx = g0.rdi) (h15 : Y.cpu.gpr.r15 = g0.r15)
    (hdi : Y.cpu.gpr.rdi = Y.cpu.gpr.rbx + 160#64) (hIW : I W) :
    GoG prof L o gev gP gE Y t := by
  refine (c_133 prof).run E.c E.hin (fun j' g' _ V' => j' = 171 ∧ I V' ∧ g'.rsp = Y.cpu.gpr.rsp ∧
      g'.rbx = Y.cpu.gpr.rbx ∧ g'.r15 = Y.cpu.gpr.r15 ∧ g'.rdi = Y.cpu.gpr.rbx + 160#64) hK hA hr
    (vc_133 hdi (by rw [hb]; exact E.hob) (by rw [hb]; exact E.hcl) hIW
      fun _ _ a1 a2 a3 a4 a5 _ => ⟨rfl, a1, a2, a3, a4, a5⟩) ?_
  rintro j' g fl V₁ ⟨rfl, hI1, gs, gb, g15, gdi⟩ U t₁ hKU hAU hrU hgU -
  subst hgU
  exact from171 E hKU hAU hrU (gs.trans hs) (gb.trans hb) (g15.trans h15) (by rw [gdi, gb]) hI1

/-- From 100 (`rdi` = `this + 160`): the vtable pointers at `this + 40`, `+ 48`, to 133. -/
theorem from100 (E : Ev prof F Wl L s₀ o gev gP gE S g0 e₂ code₂ j₂ I) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = aec_at.add 100) (hs : Y.cpu.gpr.rsp = aR S)
    (hb : Y.cpu.gpr.rbx = g0.rdi) (h15 : Y.cpu.gpr.r15 = g0.r15)
    (hdi : Y.cpu.gpr.rdi = Y.cpu.gpr.rbx + 160#64) (hIW : I W) :
    GoG prof L o gev gP gE Y t := by
  refine (c_100 prof).run E.c E.hin (fun j' g' _ V' => j' = 133 ∧ I V' ∧ g'.rsp = Y.cpu.gpr.rsp ∧
      g'.rbx = Y.cpu.gpr.rbx ∧ g'.r15 = Y.cpu.gpr.r15 ∧ g'.rdi = Y.cpu.gpr.rbx + 160#64) hK hA hr
    (vc_100 hdi (by rw [hb]; exact E.hob) (by rw [hb]; exact E.hcl) hIW
      fun _ _ a1 a2 a3 a4 a5 _ => ⟨rfl, a1, a2, a3, a4, a5⟩) ?_
  rintro j' g fl V₁ ⟨rfl, hI1, gs, gb, g15, gdi⟩ U t₁ hKU hAU hrU hgU -
  subst hgU
  exact from133 E hKU hAU hrU (gs.trans hs) (gb.trans hb) (g15.trans h15) (by rw [gdi, gb]) hI1

/-- From 61 (`rdi` = `this + 160`): the vtable pointers at `this + 16` to `+ 32`, to 100. -/
theorem from61 (E : Ev prof F Wl L s₀ o gev gP gE S g0 e₂ code₂ j₂ I) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = aec_at.add 61) (hs : Y.cpu.gpr.rsp = aR S)
    (hb : Y.cpu.gpr.rbx = g0.rdi) (h15 : Y.cpu.gpr.r15 = g0.r15)
    (hdi : Y.cpu.gpr.rdi = Y.cpu.gpr.rbx + 160#64) (hIW : I W) :
    GoG prof L o gev gP gE Y t := by
  refine (c_61 prof).run E.c E.hin (fun j' g' _ V' => j' = 100 ∧ I V' ∧ g'.rsp = Y.cpu.gpr.rsp ∧
      g'.rbx = Y.cpu.gpr.rbx ∧ g'.r15 = Y.cpu.gpr.r15 ∧ g'.rdi = Y.cpu.gpr.rbx + 160#64) hK hA hr
    (vc_61 hdi (by rw [hb]; exact E.hob) (by rw [hb]; exact E.hcl) hIW
      fun _ _ a1 a2 a3 a4 a5 _ => ⟨rfl, a1, a2, a3, a4, a5⟩) ?_
  rintro j' g fl V₁ ⟨rfl, hI1, gs, gb, g15, gdi⟩ U t₁ hKU hAU hrU hgU -
  subst hgU
  exact from100 E hKU hAU hrU (gs.trans hs) (gb.trans hb) (g15.trans h15) (by rw [gdi, gb]) hI1

/-- From 23 (after the pushes, `rdi` = `this`): `rbx` = `this`, the first vtable pointers, to 61. -/
theorem from23 (E : Ev prof F Wl L s₀ o gev gP gE S g0 e₂ code₂ j₂ I) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = aec_at.add 23) (hs : Y.cpu.gpr.rsp = aR S)
    (h15 : Y.cpu.gpr.r15 = g0.r15) (hdi : Y.cpu.gpr.rdi = g0.rdi) (hIW : I W) :
    GoG prof L o gev gP gE Y t := by
  refine (c_23 prof).run E.c E.hin (fun j' g' _ V' => j' = 61 ∧ I V' ∧ g'.rsp = Y.cpu.gpr.rsp ∧
      g'.rbx = Y.cpu.gpr.rdi ∧ g'.r15 = Y.cpu.gpr.r15 ∧ g'.rdi = Y.cpu.gpr.rdi + 160#64) hK hA hr
    (vc_23 (by rw [hdi]; exact E.hob) (by rw [hdi]; exact E.hcl) hIW
      fun _ _ a1 a2 a3 a4 a5 _ => ⟨rfl, a1, a2, a3, a4, a5⟩) ?_
  rintro j' g fl V₁ ⟨rfl, hI1, gs, gb, g15, gdi⟩ U t₁ hKU hAU hrU hgU -
  subst hgU
  exact from61 E hKU hAU hrU (gs.trans hs) (gb.trans hdi) (g15.trans h15) (by rw [gdi, gb]) hI1

end Runs

section Main
variable {prof : Profile} {F : Footprint} {Wl : List Rgn} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {e₂ : Addr} {code₂ : List Byte} {j₂ : Nat} {I : (Addr → Byte) → Prop}
  {X : State} {t : Nat} {V : Addr → Byte}

/-- `CArchiveExtractCallback::CArchiveExtractCallback` from its entry. -/
theorem aec_ok (E : Ev prof F Wl L s₀ o gev gP gE X.cpu.gpr.rsp X.cpu.gpr e₂ code₂ j₂ I)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = aec_at)
    (hI0 : I (P5 V X.cpu.gpr)) :
    GoG prof L o gev gP gE X t := by
  refine (c_0 prof).run E.c E.hin (fun j' g' _ V' => j' = 23 ∧ V' = P5 V X.cpu.gpr ∧
      g'.rsp = aR X.cpu.gpr.rsp ∧ g'.r15 = X.cpu.gpr.r15 ∧ g'.rdi = X.cpu.gpr.rdi)
    hK hA (by rw [addr_add_zero]; exact hrip)
    (vc_0 E.hs1 E.hs2 E.hs3 E.hs4 E.hs5 fun _ a1 a2 a3 _ => ⟨rfl, rfl, a1, a2, a3⟩) ?_
  rintro j' g fl V₁ ⟨rfl, hV₁, gs, g15, gdi⟩ U t₁ hKU hAU hrU hgU -
  subst V₁ hgU
  exact from23 E hKU hAU hrU gs g15 gdi hI0

end Main

end FV7z.Aec
