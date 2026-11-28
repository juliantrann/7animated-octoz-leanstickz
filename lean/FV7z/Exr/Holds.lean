import FV7z.Exr.Pieces
/-!
# `CExtractCallbackConsole::ExtractResult` (0x5e82c0): from the entry to the return (PLAN.md §M, M1)

`CExtractCallbackConsole::ExtractResult (result)`: `rdi` = `this`. One theorem for each hop: `fromN` runs the piece
at `N` (and the `call` that ends it, `callK`, with the callee as `Ev`'s continuation, or the `add` after it, `atN`)
and goes on by `fromM`, from the guard's check and the `ret` (`from202`) back to the entry (`exr_ok`). Each takes the
frame (`Fm`: `rsp` = `aR S`, `rbx` = `this`, `r13`..`r15` as at the entry) and `I` of the bytes; `from273`,
`from286` and `at265` `rbp` = `_se`, `from286` and `from312` `_se` not null, `at110` and `from118` `rdi` = `_so`,
`from128` `_so` not null (as tested on the way there; `I` keeps both, `Ev.s264`, `Ev.s272`).

- `exr_ok`: from the entry (the hypotheses `E : Ev …` with `S` = the entry's `rsp`, `g0` = its registers, `I` of
  the bytes after the prologue, `V0`) to the return (`Ev.kr`: `rsp` 8 up, the callee-saved registers as at the
  entry, `I` of the bytes) or a callee's goal.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
open FV7z.Api (KS)
namespace FV7z.Exr
set_option linter.unusedVariables false

section Runs
variable {prof : Profile} {F : Footprint} {Wl : List Rgn} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {fb S : Addr} {g0 : Gprs} {e₂ : Addr} {code₂ : List Byte} {j₂ : Nat} {I : (Addr → Byte) → Prop}
  {so se p72 p88 : Addr} {Y : State} {t : Nat} {W : Addr → Byte}

/-- From 202: the guard's check, the epilogue, the `ret`, to `kr`. -/
theorem from202 (E : Ev prof F Wl L s₀ o gev gP gE fb S g0 e₂ code₂ j₂ I so se p72 p88) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = exr_at.add 202) (hm : Fm S g0 Y.cpu.gpr) (hIW : I W) :
    GoG prof L o gev gP gE Y t := by
  obtain ⟨s1, s2, s3, s4, s5⟩ := E.hI W hIW
  have ms := hm.1
  have e1 : rdq(W, Y.cpu.gpr.rsp + 32#64) = g0.rbx := by rw [ms, q1]; exact s1
  have e2 : rdq(W, Y.cpu.gpr.rsp + 32#64 + 8) = g0.rbp := by rw [ms, q2]; exact s2
  have e3 : rdq(W, Y.cpu.gpr.rsp + 32#64 + 8 + 8) = g0.r12 := by rw [ms, q3]; exact s3
  refine (c_202 prof fb).run E.c E.hfs E.hin (fun j' g' _ V' => j' = 233 ∧ V' = W ∧
      g'.rsp = Y.cpu.gpr.rsp + 32#64 + 8 + 8 + 8 ∧ g'.rbx = rdq(W, Y.cpu.gpr.rsp + 32#64) ∧
      g'.rbp = rdq(W, Y.cpu.gpr.rsp + 32#64 + 8) ∧ g'.r12 = rdq(W, Y.cpu.gpr.rsp + 32#64 + 8 + 8) ∧
      g'.r13 = Y.cpu.gpr.r13 ∧ g'.r14 = Y.cpu.gpr.r14 ∧ g'.r15 = Y.cpu.gpr.r15)
    hK hA hr
    (vc_202 (by rw [ms]; exact s5) (by rw [ms]; exact E.fg) E.hcl (by rw [ms, q1]; exact E.fb24)
      (by rw [ms, q2]; exact E.fb16) (by rw [ms, q3]; exact E.fb8)
      fun _ a b d e i m n _ => ⟨rfl, rfl, a, b, d, e, i, m, n⟩) ?_
  rintro j' g fl V₁ ⟨rfl, hV₁, gs, gb, gp, g12, g13, g14, g15⟩ U t₁ hKU hAU hrU hgU -
  subst V₁ hgU
  have hsU : U.cpu.gpr.rsp = S := by rw [gs, ms]; exact q4 S
  refine E.c.s_ret hKU hAU E.hin (lt_len (by decide)) hrU (ret_233 _) (by rw [hsU]; exact E.hl) E.hin₂ E.h₂
    (by rw [hsU]; exact s4) ?_
  rintro Z' t₂ hKZ' hAZ' ⟨hrZ', hgZ'⟩
  refine E.kr W Z' t₂ hKZ' hAZ' hrZ' ?_ ?_ hIW
  · rw [hgZ']
    show U.cpu.gpr.rsp + 8 = _
    rw [hsU]
  · rw [hgZ']
    exact ⟨gb.trans e1, gp.trans e2, g12.trans e3, g13.trans hm.2.2.1, g14.trans hm.2.2.2.1,
      g15.trans hm.2.2.2.2⟩

/-- From 190: `Leave` (197), to 202. -/
theorem from190 (E : Ev prof F Wl L s₀ o gev gP gE fb S g0 e₂ code₂ j₂ I so se p72 p88) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = exr_at.add 190) (hm : Fm S g0 Y.cpu.gpr) (hIW : I W) :
    GoG prof L o gev gP gE Y t := by
  refine (c_190 prof fb).run E.c E.hfs E.hin (fun j' g' _ V' => j' = 197 ∧ V' = W ∧ Fr Y.cpu.gpr g') hK hA hr
    (vc_190 fun _ a _ => ⟨rfl, rfl, a⟩) ?_
  rintro j' g fl V₁ ⟨rfl, hV₁, gf⟩ U t₁ hKU hAU hrU hgU -
  subst V₁ hgU
  have hmU := Fm.fr hm gf
  refine callK E hKU hAU hrU hmU.1 (lt_len (by decide)) (call_197 _) tgt_197 E.cL (E.kL _ _ hIW)
    trivial ?_
  intro Z W' t₃ hKZ hAZ hrZ hsZ hkZ hBZ hIZ
  exact from202 E hKZ hAZ hrZ (fm_ret hmU hsZ hkZ) hIZ

/-- From 167: the result by the break counter, to 190. -/
theorem from167 (E : Ev prof F Wl L s₀ o gev gP gE fb S g0 e₂ code₂ j₂ I so se p72 p88) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = exr_at.add 167) (hm : Fm S g0 Y.cpu.gpr) (hIW : I W) :
    GoG prof L o gev gP gE Y t := by
  refine (c_167 prof fb).run E.c E.hfs E.hin (fun j' g' _ V' => j' = 190 ∧ V' = W ∧ Fr Y.cpu.gpr g') hK hA hr
    (vc_167 E.hbr fun _ a _ => ⟨rfl, rfl, a⟩) ?_
  rintro j' g fl V₁ ⟨rfl, hV₁, gf⟩ U t₁ hKU hAU hrU hgU -
  subst V₁ hgU
  have hmU := Fm.fr hm gf
  exact from190 E hKU hAU hrU hmU hIW

/-- From 393 (back from `Flush`): to 167. -/
theorem from393 (E : Ev prof F Wl L s₀ o gev gP gE fb S g0 e₂ code₂ j₂ I so se p72 p88) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = exr_at.add 393) (hm : Fm S g0 Y.cpu.gpr) (hIW : I W) :
    GoG prof L o gev gP gE Y t := by
  refine (c_393 prof fb).run E.c E.hfs E.hin (fun j' g' _ V' => j' = 167 ∧ g' = Y.cpu.gpr ∧ V' = W) hK hA hr
    (vc_393 fun _ => ⟨rfl, rfl, rfl⟩) ?_
  rintro j' g fl V₁ ⟨rfl, rfl, hV₁⟩ U t₁ hKU hAU hrU hgU -
  subst V₁
  exact from167 E hKU hAU hrU (by rw [hgU]; exact hm) hIW

/-- At 388: `Flush`, to 393. -/
theorem at388 (E : Ev prof F Wl L s₀ o gev gP gE fb S g0 e₂ code₂ j₂ I so se p72 p88) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = exr_at.add 388) (hm : Fm S g0 Y.cpu.gpr) (hIW : I W) :
    GoG prof L o gev gP gE Y t := by
  refine callK E hK hA hr hm.1 (lt_len (by decide)) (call_388 _) tgt_388 E.cH (E.kH _ _ hIW) trivial ?_
  intro Z W' t₃ hKZ hAZ hrZ hsZ hkZ hBZ hIZ
  exact from393 E hKZ hAZ hrZ (fm_ret hm hsZ hkZ) hIZ

/-- From 381 (back from `endl`): to `Flush` at 388. -/
theorem from381 (E : Ev prof F Wl L s₀ o gev gP gE fb S g0 e₂ code₂ j₂ I so se p72 p88) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = exr_at.add 381) (hm : Fm S g0 Y.cpu.gpr) (hIW : I W) :
    GoG prof L o gev gP gE Y t := by
  refine (c_381 prof fb).run E.c E.hfs E.hin (fun j' g' _ V' => j' = 388 ∧ V' = W ∧ Fr Y.cpu.gpr g') hK hA hr
    (vc_381 (by rw [hm.2.1]; exact E.hrd) fun _ a _ => ⟨rfl, rfl, a⟩) ?_
  rintro j' g fl V₁ ⟨rfl, hV₁, gf⟩ U t₁ hKU hAU hrU hgU -
  subst V₁ hgU
  have hmU := Fm.fr hm gf
  exact at388 E hKU hAU hrU hmU hIW

/-- From 369: `endl (*_se)` (376), to 381. -/
theorem from369 (E : Ev prof F Wl L s₀ o gev gP gE fb S g0 e₂ code₂ j₂ I so se p72 p88) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = exr_at.add 369) (hm : Fm S g0 Y.cpu.gpr) (hIW : I W) :
    GoG prof L o gev gP gE Y t := by
  refine (c_369 prof fb).run E.c E.hfs E.hin (fun j' g' _ V' => j' = 376 ∧ V' = W ∧ Fr Y.cpu.gpr g') hK hA hr
    (vc_369 (by rw [hm.2.1]; exact E.hrd) fun _ a _ => ⟨rfl, rfl, a⟩) ?_
  rintro j' g fl V₁ ⟨rfl, hV₁, gf⟩ U t₁ hKU hAU hrU hgU -
  subst V₁ hgU
  have hmU := Fm.fr hm gf
  refine callK E hKU hAU hrU hmU.1 (lt_len (by decide)) (call_376 _) tgt_376 E.cE (E.kE _ _ hIW)
    trivial ?_
  intro Z W' t₃ hKZ hAZ hrZ hsZ hkZ hBZ hIZ
  exact from381 E hKZ hAZ hrZ (fm_ret hmU hsZ hkZ) hIZ

/-- From 355 (back from `operator<<`): `delete []` of the message's buffer (364) unless null, to 369. -/
theorem from355 (E : Ev prof F Wl L s₀ o gev gP gE fb S g0 e₂ code₂ j₂ I so se p72 p88) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = exr_at.add 355) (hm : Fm S g0 Y.cpu.gpr) (hIW : I W) :
    GoG prof L o gev gP gE Y t := by
  refine (c_355 prof fb).run E.c E.hfs E.hin (fun j' g' _ V' => V' = W ∧ Fr Y.cpu.gpr g' ∧
      (j' = 369 ∨ j' = 364)) hK hA hr
    (vc_355 (by rw [hm.1]; exact E.fl0)
      (fun _ a _ => ⟨rfl, a, Or.inl rfl⟩) fun _ a _ => ⟨rfl, a, Or.inr rfl⟩) ?_
  rintro j' g fl V₁ ⟨hV₁, gf, hj⟩ U t₁ hKU hAU hrU hgU -
  subst V₁ hgU
  have hmU := Fm.fr hm gf
  rcases hj with rfl | rfl
  · exact from369 E hKU hAU hrU hmU hIW
  · refine callK E hKU hAU hrU hmU.1 (lt_len (by decide)) (call_364 _) tgt_364 E.cD (E.kD _ _ hIW)
      trivial ?_
    intro Z W' t₃ hKZ hAZ hrZ hsZ hkZ hBZ hIZ
    exact from369 E hKZ hAZ hrZ (fm_ret hmU hsZ hkZ) hIZ

/-- From 343 (back from `HResultToMessage`): `*_se << message` (350), to 355. -/
theorem from343 (E : Ev prof F Wl L s₀ o gev gP gE fb S g0 e₂ code₂ j₂ I so se p72 p88) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = exr_at.add 343) (hm : Fm S g0 Y.cpu.gpr) (hIW : I W) :
    GoG prof L o gev gP gE Y t := by
  refine (c_343 prof fb).run E.c E.hfs E.hin (fun j' g' _ V' => j' = 350 ∧ V' = W ∧ Fr Y.cpu.gpr g') hK hA hr
    (vc_343 (by rw [hm.1]; exact E.fl0) fun _ a _ => ⟨rfl, rfl, a⟩) ?_
  rintro j' g fl V₁ ⟨rfl, hV₁, gf⟩ U t₁ hKU hAU hrU hgU -
  subst V₁ hgU
  have hmU := Fm.fr hm gf
  refine callK E hKU hAU hrU hmU.1 (lt_len (by decide)) (call_350 _) tgt_350 E.cO (E.kO _ _ hIW)
    trivial ?_
  intro Z W' t₃ hKZ hAZ hrZ hsZ hkZ hBZ hIZ
  exact from355 E hKZ hAZ hrZ (fm_ret hmU hsZ hkZ) hIZ

/-- From 658 (back from `fwrite`): to 369. -/
theorem from658 (E : Ev prof F Wl L s₀ o gev gP gE fb S g0 e₂ code₂ j₂ I so se p72 p88) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = exr_at.add 658) (hm : Fm S g0 Y.cpu.gpr) (hIW : I W) :
    GoG prof L o gev gP gE Y t := by
  refine (c_658 prof fb).run E.c E.hfs E.hin (fun j' g' _ V' => j' = 369 ∧ g' = Y.cpu.gpr ∧ V' = W) hK hA hr
    (vc_658 fun _ => ⟨rfl, rfl, rfl⟩) ?_
  rintro j' g fl V₁ ⟨rfl, rfl, hV₁⟩ U t₁ hKU hAU hrU hgU -
  subst V₁
  exact from369 E hKU hAU hrU (by rw [hgU]; exact hm) hIW

/-- From 312 (back from `fwrite`, `_se` not null): the out-of-memory message (`fwrite`, 653) and 658, or
`HResultToMessage` (338) and 343. -/
theorem from312 (E : Ev prof F Wl L s₀ o gev gP gE fb S g0 e₂ code₂ j₂ I so se p72 p88) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = exr_at.add 312) (hm : Fm S g0 Y.cpu.gpr)
    (hn : se ≠ 0) (hIW : I W) :
    GoG prof L o gev gP gE Y t := by
  refine (c_312 prof fb).run E.c E.hfs E.hin (fun j' g' _ V' => V' = W ∧ Fr Y.cpu.gpr g' ∧
      (j' = 653 ∨ j' = 338)) hK hA hr
    (vc_312 (by rw [hm.2.1]; exact E.hrd) (by rw [hm.2.1, E.s272 W hIW]; exact E.hse hn)
      (fun _ a _ => ⟨rfl, a, Or.inl rfl⟩) fun _ a _ => ⟨rfl, a, Or.inr rfl⟩) ?_
  rintro j' g fl V₁ ⟨hV₁, gf, hj⟩ U t₁ hKU hAU hrU hgU -
  subst V₁ hgU
  have hmU := Fm.fr hm gf
  rcases hj with rfl | rfl
  · refine callK E hKU hAU hrU hmU.1 (lt_len (by decide)) (call_653 _) tgt_653 E.cW (E.kW _ _ hIW)
      trivial ?_
    intro Z W' t₃ hKZ hAZ hrZ hsZ hkZ hBZ hIZ
    exact from658 E hKZ hAZ hrZ (fm_ret hmU hsZ hkZ) hIZ
  · refine callK E hKU hAU hrU hmU.1 (lt_len (by decide)) (call_338 _) tgt_338 E.cM (E.kM _ _ hIW)
      trivial ?_
    intro Z W' t₃ hKZ hAZ hrZ hsZ hkZ hBZ hIZ
    exact from343 E hKZ hAZ hrZ (fm_ret hmU hsZ hkZ) hIZ

/-- From 286 (back from `endl`, `rbp` = `_se`, not null): `fwrite` of the message (307), to 312. -/
theorem from286 (E : Ev prof F Wl L s₀ o gev gP gE fb S g0 e₂ code₂ j₂ I so se p72 p88) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = exr_at.add 286) (hm : Fm S g0 Y.cpu.gpr)
    (h5 : Y.cpu.gpr.rbp = se) (hn : se ≠ 0) (hIW : I W) :
    GoG prof L o gev gP gE Y t := by
  refine (c_286 prof fb).run E.c E.hfs E.hin (fun j' g' _ V' => j' = 307 ∧ V' = W ∧ Fr Y.cpu.gpr g') hK hA hr
    (vc_286 (by rw [h5]; exact E.hse hn) fun _ a _ => ⟨rfl, rfl, a⟩) ?_
  rintro j' g fl V₁ ⟨rfl, hV₁, gf⟩ U t₁ hKU hAU hrU hgU -
  subst V₁ hgU
  have hmU := Fm.fr hm gf
  refine callK E hKU hAU hrU hmU.1 (lt_len (by decide)) (call_307 _) tgt_307 E.cW (E.kW _ _ hIW)
    trivial ?_
  intro Z W' t₃ hKZ hAZ hrZ hsZ hkZ hBZ hIZ
  exact from312 E hKZ hAZ hrZ (fm_ret hmU hsZ hkZ) hn hIZ

/-- From 273 (`rbp` = `_se`): null to 167, else `endl (*_se)` (281) and 286. -/
theorem from273 (E : Ev prof F Wl L s₀ o gev gP gE fb S g0 e₂ code₂ j₂ I so se p72 p88) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = exr_at.add 273) (hm : Fm S g0 Y.cpu.gpr)
    (h5 : Y.cpu.gpr.rbp = se) (hIW : I W) :
    GoG prof L o gev gP gE Y t := by
  refine (c_273 prof fb).run E.c E.hfs E.hin (fun j' g' _ V' => V' = W ∧ Fr Y.cpu.gpr g' ∧
      (j' = 167 ∨ (j' = 281 ∧ Y.cpu.gpr.rbp ≠ 0 ∧ g'.rbp = Y.cpu.gpr.rbp))) hK hA hr
    (vc_273 (fun _ a _ => ⟨rfl, a, Or.inl rfl⟩) fun _ n b a _ => ⟨rfl, a, Or.inr ⟨rfl, n, b⟩⟩) ?_
  rintro j' g fl V₁ ⟨hV₁, gf, hj⟩ U t₁ hKU hAU hrU hgU -
  subst V₁ hgU
  have hmU := Fm.fr hm gf
  rcases hj with rfl | ⟨rfl, hn, gp⟩
  · exact from167 E hKU hAU hrU hmU hIW
  · refine callK E hKU hAU hrU hmU.1 (lt_len (by decide)) (call_281 _) tgt_281 E.cE (E.kE _ _ hIW) trivial ?_
    intro Z W' t₃ hKZ hAZ hrZ hsZ hkZ hBZ hIZ
    exact from286 E hKZ hAZ hrZ (fm_ret hmU hsZ hkZ) (hkZ.2.1.trans (gp.trans h5)) (by rw [← h5]; exact hn) hIZ

/-- At 265 (`rbp` = `_se`): the counter at `this + 408` up, to 273. -/
theorem at265 (E : Ev prof F Wl L s₀ o gev gP gE fb S g0 e₂ code₂ j₂ I so se p72 p88) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = exr_at.add 265) (hm : Fm S g0 Y.cpu.gpr)
    (h5 : Y.cpu.gpr.rbp = se) (hIW : I W) :
    GoG prof L o gev gP gE Y t := by
  have ea : eaD Y 3 408 = g0.rdi + 408#64 := by
    rw [eaD]
    show Y.cpu.gpr.rbx + _ = _
    rw [hm.2.1]
  refine E.c.s_add_mi64 hK hA E.hin (lt_len (by decide)) hr (add_265 _) (by rw [ea]; exact E.w408) ?_
  rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
  rw [ea] at hA₂
  exact from273 E hK₂ hA₂ hr₂ (by rw [hg₂]; exact hm) (by rw [hg₂]; exact h5)
    (E.c408 _ _ (toBytesLE_length _ _) hIW)

/-- From 142: to 167, or `Flush` at 388. -/
theorem from142 (E : Ev prof F Wl L s₀ o gev gP gE fb S g0 e₂ code₂ j₂ I so se p72 p88) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = exr_at.add 142) (hm : Fm S g0 Y.cpu.gpr) (hIW : I W) :
    GoG prof L o gev gP gE Y t := by
  refine (c_142 prof fb).run E.c E.hfs E.hin (fun j' g' _ V' => V' = W ∧ Fr Y.cpu.gpr g' ∧
      (j' = 167 ∨ j' = 388)) hK hA hr
    (vc_142 (by rw [hm.2.1]; exact E.hrd)
      (fun _ a _ => ⟨rfl, a, Or.inl rfl⟩) fun _ a _ => ⟨rfl, a, Or.inr rfl⟩) ?_
  rintro j' g fl V₁ ⟨hV₁, gf, hj⟩ U t₁ hKU hAU hrU hgU -
  subst V₁ hgU
  have hmU := Fm.fr hm gf
  rcases hj with rfl | rfl
  · exact from167 E hKU hAU hrU hmU hIW
  · exact at388 E hKU hAU hrU hmU hIW

/-- From 540 (back from `endl`): to 142. -/
theorem from540 (E : Ev prof F Wl L s₀ o gev gP gE fb S g0 e₂ code₂ j₂ I so se p72 p88) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = exr_at.add 540) (hm : Fm S g0 Y.cpu.gpr) (hIW : I W) :
    GoG prof L o gev gP gE Y t := by
  refine (c_540 prof fb).run E.c E.hfs E.hin (fun j' g' _ V' => j' = 142 ∧ g' = Y.cpu.gpr ∧ V' = W) hK hA hr
    (vc_540 fun _ => ⟨rfl, rfl, rfl⟩) ?_
  rintro j' g fl V₁ ⟨rfl, rfl, hV₁⟩ U t₁ hKU hAU hrU hgU -
  subst V₁
  exact from142 E hKU hAU hrU (by rw [hgU]; exact hm) hIW

/-- From 608 (back from `endl`): to 142. -/
theorem from608 (E : Ev prof F Wl L s₀ o gev gP gE fb S g0 e₂ code₂ j₂ I so se p72 p88) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = exr_at.add 608) (hm : Fm S g0 Y.cpu.gpr) (hIW : I W) :
    GoG prof L o gev gP gE Y t := by
  refine (c_608 prof fb).run E.c E.hfs E.hin (fun j' g' _ V' => j' = 142 ∧ g' = Y.cpu.gpr ∧ V' = W) hK hA hr
    (vc_608 fun _ => ⟨rfl, rfl, rfl⟩) ?_
  rintro j' g fl V₁ ⟨rfl, rfl, hV₁⟩ U t₁ hKU hAU hrU hgU -
  subst V₁
  exact from142 E hKU hAU hrU (by rw [hgU]; exact hm) hIW

/-- From 532 (back from `fwrite`): `endl (*_so)` (535), to 540. -/
theorem from532 (E : Ev prof F Wl L s₀ o gev gP gE fb S g0 e₂ code₂ j₂ I so se p72 p88) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = exr_at.add 532) (hm : Fm S g0 Y.cpu.gpr) (hIW : I W) :
    GoG prof L o gev gP gE Y t := by
  refine (c_532 prof fb).run E.c E.hfs E.hin (fun j' g' _ V' => j' = 535 ∧ V' = W ∧ Fr Y.cpu.gpr g') hK hA hr
    (vc_532 fun _ a _ => ⟨rfl, rfl, a⟩) ?_
  rintro j' g fl V₁ ⟨rfl, hV₁, gf⟩ U t₁ hKU hAU hrU hgU -
  subst V₁ hgU
  have hmU := Fm.fr hm gf
  refine callK E hKU hAU hrU hmU.1 (lt_len (by decide)) (call_535 _) tgt_535 E.cE (E.kE _ _ hIW)
    trivial ?_
  intro Z W' t₃ hKZ hAZ hrZ hsZ hkZ hBZ hIZ
  exact from540 E hKZ hAZ hrZ (fm_ret hmU hsZ hkZ) hIZ

/-- From 490: `_so` null to 167, else the error message (`fwrite`, 527) and 532. -/
theorem from490 (E : Ev prof F Wl L s₀ o gev gP gE fb S g0 e₂ code₂ j₂ I so se p72 p88) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = exr_at.add 490) (hm : Fm S g0 Y.cpu.gpr) (hIW : I W) :
    GoG prof L o gev gP gE Y t := by
  refine (c_490 prof fb).run E.c E.hfs E.hin (fun j' g' _ V' => V' = W ∧ Fr Y.cpu.gpr g' ∧
      (j' = 167 ∨ j' = 527)) hK hA hr
    (vc_490 (by rw [hm.2.1]; exact E.hrd) (by rw [hm.2.1, E.s264 W hIW]; exact E.hso)
      (fun _ a _ => ⟨rfl, a, Or.inl rfl⟩) fun _ a _ => ⟨rfl, a, Or.inr rfl⟩) ?_
  rintro j' g fl V₁ ⟨hV₁, gf, hj⟩ U t₁ hKU hAU hrU hgU -
  subst V₁ hgU
  have hmU := Fm.fr hm gf
  rcases hj with rfl | rfl
  · exact from167 E hKU hAU hrU hmU hIW
  · refine callK E hKU hAU hrU hmU.1 (lt_len (by decide)) (call_527 _) tgt_527 E.cW (E.kW _ _ hIW)
      trivial ?_
    intro Z W' t₃ hKZ hAZ hrZ hsZ hkZ hBZ hIZ
    exact from532 E hKZ hAZ hrZ (fm_ret hmU hsZ hkZ) hIZ

/-- From 624: to 490. -/
theorem from624 (E : Ev prof F Wl L s₀ o gev gP gE fb S g0 e₂ code₂ j₂ I so se p72 p88) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = exr_at.add 624) (hm : Fm S g0 Y.cpu.gpr) (hIW : I W) :
    GoG prof L o gev gP gE Y t := by
  refine (c_624 prof fb).run E.c E.hfs E.hin (fun j' g' _ V' => j' = 490 ∧ g' = Y.cpu.gpr ∧ V' = W) hK hA hr
    (vc_624 fun _ => ⟨rfl, rfl, rfl⟩) ?_
  rintro j' g fl V₁ ⟨rfl, rfl, hV₁⟩ U t₁ hKU hAU hrU hgU -
  subst V₁
  exact from490 E hKU hAU hrU (by rw [hgU]; exact hm) hIW

/-- At 616: the counter at `this + 392` up, to 624. -/
theorem at616 (E : Ev prof F Wl L s₀ o gev gP gE fb S g0 e₂ code₂ j₂ I so se p72 p88) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = exr_at.add 616) (hm : Fm S g0 Y.cpu.gpr) (hIW : I W) :
    GoG prof L o gev gP gE Y t := by
  have ea : eaD Y 3 392 = g0.rdi + 392#64 := by
    rw [eaD]
    show Y.cpu.gpr.rbx + _ = _
    rw [hm.2.1]
  refine E.c.s_add_mi64 hK hA E.hin (lt_len (by decide)) hr (add_616 _) (by rw [ea]; exact E.w392) ?_
  rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
  rw [ea] at hA₂
  exact from624 E hK₂ hA₂ hr₂ (by rw [hg₂]; exact hm)
    (E.c392 _ _ (toBytesLE_length _ _) hIW)

/-- At 482: the counter at `this + 416` up, to 490. -/
theorem at482 (E : Ev prof F Wl L s₀ o gev gP gE fb S g0 e₂ code₂ j₂ I so se p72 p88) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = exr_at.add 482) (hm : Fm S g0 Y.cpu.gpr) (hIW : I W) :
    GoG prof L o gev gP gE Y t := by
  have ea : eaD Y 3 416 = g0.rdi + 416#64 := by
    rw [eaD]
    show Y.cpu.gpr.rbx + _ = _
    rw [hm.2.1]
  refine E.c.s_add_mi64 hK hA E.hin (lt_len (by decide)) hr (add_482 _) (by rw [ea]; exact E.w416) ?_
  rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
  rw [ea] at hA₂
  exact from490 E hK₂ hA₂ hr₂ (by rw [hg₂]; exact hm)
    (E.c416 _ _ (toBytesLE_length _ _) hIW)

/-- From 600 (back from `operator<<`): `endl` (603), to 608. -/
theorem from600 (E : Ev prof F Wl L s₀ o gev gP gE fb S g0 e₂ code₂ j₂ I so se p72 p88) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = exr_at.add 600) (hm : Fm S g0 Y.cpu.gpr) (hIW : I W) :
    GoG prof L o gev gP gE Y t := by
  refine (c_600 prof fb).run E.c E.hfs E.hin (fun j' g' _ V' => j' = 603 ∧ V' = W ∧ Fr Y.cpu.gpr g') hK hA hr
    (vc_600 fun _ a _ => ⟨rfl, rfl, a⟩) ?_
  rintro j' g fl V₁ ⟨rfl, hV₁, gf⟩ U t₁ hKU hAU hrU hgU -
  subst V₁ hgU
  have hmU := Fm.fr hm gf
  refine callK E hKU hAU hrU hmU.1 (lt_len (by decide)) (call_603 _) tgt_603 E.cE (E.kE _ _ hIW)
    trivial ?_
  intro Z W' t₃ hKZ hAZ hrZ hsZ hkZ hBZ hIZ
  exact from608 E hKZ hAZ hrZ (fm_ret hmU hsZ hkZ) hIZ

/-- From 585 (back from `fwrite`): `*_so << count` (595), to 600. -/
theorem from585 (E : Ev prof F Wl L s₀ o gev gP gE fb S g0 e₂ code₂ j₂ I so se p72 p88) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = exr_at.add 585) (hm : Fm S g0 Y.cpu.gpr) (hIW : I W) :
    GoG prof L o gev gP gE Y t := by
  refine (c_585 prof fb).run E.c E.hfs E.hin (fun j' g' _ V' => j' = 595 ∧ V' = W ∧ Fr Y.cpu.gpr g') hK hA hr
    (vc_585 (by rw [hm.2.1]; exact E.hrd) fun _ a _ => ⟨rfl, rfl, a⟩) ?_
  rintro j' g fl V₁ ⟨rfl, hV₁, gf⟩ U t₁ hKU hAU hrU hgU -
  subst V₁ hgU
  have hmU := Fm.fr hm gf
  refine callK E hKU hAU hrU hmU.1 (lt_len (by decide)) (call_595 _) tgt_595 E.cQ (E.kQ _ _ hIW)
    trivial ?_
  intro Z W' t₃ hKZ hAZ hrZ hsZ hkZ hBZ hIZ
  exact from600 E hKZ hAZ hrZ (fm_ret hmU hsZ hkZ) hIZ

/-- From 128 (back from `endl`, `_so` not null): the message of the count (`fwrite`, 580) and 585, or 142. -/
theorem from128 (E : Ev prof F Wl L s₀ o gev gP gE fb S g0 e₂ code₂ j₂ I so se p72 p88) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = exr_at.add 128) (hm : Fm S g0 Y.cpu.gpr)
    (hn : so ≠ 0) (hIW : I W) :
    GoG prof L o gev gP gE Y t := by
  refine (c_128 prof fb).run E.c E.hfs E.hin (fun j' g' _ V' => V' = W ∧ Fr Y.cpu.gpr g' ∧
      (j' = 580 ∨ j' = 142)) hK hA hr
    (vc_128 (by rw [hm.2.1]; exact E.hrd) (by rw [hm.2.1, E.s264 W hIW]; exact E.hso hn)
      (fun _ a _ => ⟨rfl, a, Or.inl rfl⟩) fun _ a _ => ⟨rfl, a, Or.inr rfl⟩) ?_
  rintro j' g fl V₁ ⟨hV₁, gf, hj⟩ U t₁ hKU hAU hrU hgU -
  subst V₁ hgU
  have hmU := Fm.fr hm gf
  rcases hj with rfl | rfl
  · refine callK E hKU hAU hrU hmU.1 (lt_len (by decide)) (call_580 _) tgt_580 E.cW (E.kW _ _ hIW)
      trivial ?_
    intro Z W' t₃ hKZ hAZ hrZ hsZ hkZ hBZ hIZ
    exact from585 E hKZ hAZ hrZ (fm_ret hmU hsZ hkZ) hIZ
  · exact from142 E hKU hAU hrU hmU hIW

/-- From 118 (`rdi` = `_so`): null to 167, else `endl (*_so)` (123) and 128. -/
theorem from118 (E : Ev prof F Wl L s₀ o gev gP gE fb S g0 e₂ code₂ j₂ I so se p72 p88) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = exr_at.add 118) (hm : Fm S g0 Y.cpu.gpr)
    (hd : Y.cpu.gpr.rdi = so) (hIW : I W) :
    GoG prof L o gev gP gE Y t := by
  refine (c_118 prof fb).run E.c E.hfs E.hin (fun j' g' _ V' => V' = W ∧ Fr Y.cpu.gpr g' ∧
      (j' = 167 ∨ (j' = 123 ∧ Y.cpu.gpr.rdi ≠ 0))) hK hA hr
    (vc_118 (fun _ a _ => ⟨rfl, a, Or.inl rfl⟩) fun _ n a _ => ⟨rfl, a, Or.inr ⟨rfl, n⟩⟩) ?_
  rintro j' g fl V₁ ⟨hV₁, gf, hj⟩ U t₁ hKU hAU hrU hgU -
  subst V₁ hgU
  have hmU := Fm.fr hm gf
  rcases hj with rfl | ⟨rfl, hn⟩
  · exact from167 E hKU hAU hrU hmU hIW
  · refine callK E hKU hAU hrU hmU.1 (lt_len (by decide)) (call_123 _) tgt_123 E.cE (E.kE _ _ hIW) trivial ?_
    intro Z W' t₃ hKZ hAZ hrZ hsZ hkZ hBZ hIZ
    exact from128 E hKZ hAZ hrZ (fm_ret hmU hsZ hkZ) (by rw [← hd]; exact hn) hIZ

/-- At 110 (`rdi` = `_so`): the counter at `this + 408` up, to 118. -/
theorem at110 (E : Ev prof F Wl L s₀ o gev gP gE fb S g0 e₂ code₂ j₂ I so se p72 p88) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = exr_at.add 110) (hm : Fm S g0 Y.cpu.gpr)
    (hd : Y.cpu.gpr.rdi = so) (hIW : I W) :
    GoG prof L o gev gP gE Y t := by
  have ea : eaD Y 3 408 = g0.rdi + 408#64 := by
    rw [eaD]
    show Y.cpu.gpr.rbx + _ = _
    rw [hm.2.1]
  refine E.c.s_add_mi64 hK hA E.hin (lt_len (by decide)) hr (add_110 _) (by rw [ea]; exact E.w408) ?_
  rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
  rw [ea] at hA₂
  exact from118 E hK₂ hA₂ hr₂ (by rw [hg₂]; exact hm) (by rw [hg₂]; exact hd)
    (E.c408 _ _ (toBytesLE_length _ _) hIW)

/-- From 103: `rdi` = `_so`, to the `add` at 110. -/
theorem from103 (E : Ev prof F Wl L s₀ o gev gP gE fb S g0 e₂ code₂ j₂ I so se p72 p88) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = exr_at.add 103) (hm : Fm S g0 Y.cpu.gpr) (hIW : I W) :
    GoG prof L o gev gP gE Y t := by
  refine (c_103 prof fb).run E.c E.hfs E.hin (fun j' g' _ V' => j' = 110 ∧ V' = W ∧
      g'.rdi = rdq(W, Y.cpu.gpr.rbx + 264#64) ∧ Fr Y.cpu.gpr g') hK hA hr
    (vc_103 (by rw [hm.2.1]; exact E.hrd) fun _ a b _ => ⟨rfl, rfl, a, b⟩) ?_
  rintro j' g fl V₁ ⟨rfl, hV₁, gdi, gf⟩ U t₁ hKU hAU hrU hgU -
  subst V₁ hgU
  exact at110 E hKU hAU hrU (Fm.fr hm gf) (by rw [gdi, hm.2.1]; exact E.s264 W hIW) hIW

/-- From 80 (back from `Flush`, or `_so` null): to 190, the `add`s at 265, 616 or 482, or 103. -/
theorem from80 (E : Ev prof F Wl L s₀ o gev gP gE fb S g0 e₂ code₂ j₂ I so se p72 p88) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = exr_at.add 80) (hm : Fm S g0 Y.cpu.gpr) (hIW : I W) :
    GoG prof L o gev gP gE Y t := by
  refine (c_80 prof fb).run E.c E.hfs E.hin (fun j' g' _ V' => V' = W ∧ Fr Y.cpu.gpr g' ∧
      (j' = 190 ∨ (j' = 265 ∧ g'.rbp = rdq(W, Y.cpu.gpr.rbx + 272#64)) ∨ j' = 103 ∨ j' = 616 ∨ j' = 482))
    hK hA hr
    (vc_80 (by rw [hm.2.1]; exact E.hrd) (fun _ a _ => ⟨rfl, a, Or.inl rfl⟩)
      (fun _ b a _ => ⟨rfl, a, Or.inr (Or.inl ⟨rfl, b⟩)⟩)
      (fun _ a _ => ⟨rfl, a, Or.inr (Or.inr (Or.inl rfl))⟩)
      (fun _ a _ => ⟨rfl, a, Or.inr (Or.inr (Or.inr (Or.inl rfl)))⟩)
      fun _ a _ => ⟨rfl, a, Or.inr (Or.inr (Or.inr (Or.inr rfl)))⟩) ?_
  rintro j' g fl V₁ ⟨hV₁, gf, hj⟩ U t₁ hKU hAU hrU hgU -
  subst V₁ hgU
  have hmU := Fm.fr hm gf
  rcases hj with rfl | ⟨rfl, gp⟩ | rfl | rfl | rfl
  · exact from190 E hKU hAU hrU hmU hIW
  · exact at265 E hKU hAU hrU hmU (by rw [gp, hm.2.1]; exact E.s272 W hIW) hIW
  · exact from103 E hKU hAU hrU hmU hIW
  · exact at616 E hKU hAU hrU hmU hIW
  · exact at482 E hKU hAU hrU hmU hIW

/-- From 63: `_so` null to 80, else `Flush` (75) and 80. -/
theorem from63 (E : Ev prof F Wl L s₀ o gev gP gE fb S g0 e₂ code₂ j₂ I so se p72 p88) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = exr_at.add 63) (hm : Fm S g0 Y.cpu.gpr) (hIW : I W) :
    GoG prof L o gev gP gE Y t := by
  refine (c_63 prof fb).run E.c E.hfs E.hin (fun j' g' _ V' => V' = W ∧ Fr Y.cpu.gpr g' ∧
      (j' = 80 ∨ j' = 75)) hK hA hr
    (vc_63 (by rw [hm.2.1]; exact E.hrd)
      (fun _ a _ => ⟨rfl, a, Or.inl rfl⟩) fun _ a _ => ⟨rfl, a, Or.inr rfl⟩) ?_
  rintro j' g fl V₁ ⟨hV₁, gf, hj⟩ U t₁ hKU hAU hrU hgU -
  subst V₁ hgU
  have hmU := Fm.fr hm gf
  rcases hj with rfl | rfl
  · exact from80 E hKU hAU hrU hmU hIW
  · refine callK E hKU hAU hrU hmU.1 (lt_len (by decide)) (call_75 _) tgt_75 E.cH (E.kH _ _ hIW)
      trivial ?_
    intro Z W' t₃ hKZ hAZ hrZ hsZ hkZ hBZ hIZ
    exact from80 E hKZ hAZ hrZ (fm_ret hmU hsZ hkZ) hIZ

/-- From 414 (back from `ClosePrint`): the buffers cleared, to 63. -/
theorem from414 (E : Ev prof F Wl L s₀ o gev gP gE fb S g0 e₂ code₂ j₂ I so se p72 p88) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = exr_at.add 414) (hm : Fm S g0 Y.cpu.gpr) (hIW : I W) :
    GoG prof L o gev gP gE Y t := by
  have hI4 : ∀ a b c d : List Byte, a.length = 4 → b.length = 1 → c.length = 4 → d.length = 4 →
      I (Vst (Vst (Vst (Vst W (Y.cpu.gpr.rbx + 80#64) a) rdq(W, Y.cpu.gpr.rbx + 72#64) b) (Y.cpu.gpr.rbx + 96#64) c)
        rdq(Vst (Vst W (Y.cpu.gpr.rbx + 80#64) a) rdq(W, Y.cpu.gpr.rbx + 72#64) b, Y.cpu.gpr.rbx + 88#64) d) := by
    intro a b c d la lb lc ld
    rw [hm.2.1, E.s72 W hIW]
    have i2 : I (Vst (Vst W (g0.rdi + 80#64) a) p72 b) := E.c72 _ b lb (E.c80 W a la hIW)
    rw [E.s88 _ i2]
    exact E.c88 _ d ld (E.c96 _ c lc i2)
  have w88 : ∀ (a b : List Byte), a.length = 4 → b.length = 1 → ∀ i < 4,
      Foot Wl (Addr.add rdq(Vst (Vst W (Y.cpu.gpr.rbx + 80#64) a) rdq(W, Y.cpu.gpr.rbx + 72#64) b,
        Y.cpu.gpr.rbx + 88#64) i) := by
    intro a b la lb
    rw [hm.2.1, E.s72 W hIW, E.s88 _ (E.c72 _ b lb (E.c80 W a la hIW))]
    exact E.w88
  refine (c_414 prof fb).run E.c E.hfs E.hin (fun j' g' _ V' => j' = 63 ∧ I V' ∧ Fr Y.cpu.gpr g') hK hA hr
    (vc_414 (by rw [hm.2.1]; exact E.hrd) (by rw [hm.2.1]; exact E.w80) (by rw [hm.2.1]; exact E.w96)
      (by rw [hm.2.1, E.s72 W hIW]; exact E.w72) w88
      fun _ a b c d la lb lc ld gf _ => ⟨rfl, hI4 a b c d la lb lc ld, gf⟩) ?_
  rintro j' g fl V₁ ⟨rfl, hI1, gf⟩ U t₁ hKU hAU hrU hgU -
  subst hgU
  exact from63 E hKU hAU hrU (Fm.fr hm gf) hI1

/-- From 46 (back from `Enter`): to 63, or `ClosePrint` (409) and 414. -/
theorem from46 (E : Ev prof F Wl L s₀ o gev gP gE fb S g0 e₂ code₂ j₂ I so se p72 p88) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = exr_at.add 46) (hm : Fm S g0 Y.cpu.gpr) (hIW : I W) :
    GoG prof L o gev gP gE Y t := by
  refine (c_46 prof fb).run E.c E.hfs E.hin (fun j' g' _ V' => V' = W ∧ Fr Y.cpu.gpr g' ∧
      (j' = 63 ∨ j' = 409)) hK hA hr
    (vc_46 (by rw [hm.2.1]; exact E.hrd)
      (fun _ a _ => ⟨rfl, a, Or.inl rfl⟩) fun _ a _ => ⟨rfl, a, Or.inr rfl⟩) ?_
  rintro j' g fl V₁ ⟨hV₁, gf, hj⟩ U t₁ hKU hAU hrU hgU -
  subst V₁ hgU
  have hmU := Fm.fr hm gf
  rcases hj with rfl | rfl
  · exact from63 E hKU hAU hrU hmU hIW
  · refine callK E hKU hAU hrU hmU.1 (lt_len (by decide)) (call_409 _) tgt_409 E.cC (E.kC _ _ hIW)
      trivial ?_
    intro Z W' t₃ hKZ hAZ hrZ hsZ hkZ hBZ hIZ
    exact from414 E hKZ hAZ hrZ (fm_ret hmU hsZ hkZ) hIZ

end Runs


section Main
variable {prof : Profile} {F : Footprint} {Wl : List Rgn} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {fb : Addr} {e₂ : Addr} {code₂ : List Byte} {j₂ : Nat} {I : (Addr → Byte) → Prop} {so se p72 p88 : Addr}
  {X : State} {t : Nat} {V : Addr → Byte}

/-- `CExtractCallbackConsole::ExtractResult (this, result)` from its entry (`X`'s registers, `S` = their `rsp`, `fb`
the `fs` base; the pushes' slots and the guard's slot in what the run may store into, `I` of the bytes after the
prologue). -/
theorem exr_ok (E : Ev prof F Wl L s₀ o gev gP gE fb X.cpu.gpr.rsp X.cpu.gpr e₂ code₂ j₂ I so se p72 p88)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = exr_at)
    (hs1 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8) i))
    (hs2 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8 - 8) i))
    (hs3 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8 - 8 - 8) i))
    (hw : ∀ i < 8, Foot Wl (Addr.add (aR X.cpu.gpr.rsp + 24#64) i)) (hI0 : I (V0 fb V X.cpu.gpr)) :
    GoG prof L o gev gP gE X t := by
  refine (c_0 prof fb).run E.c E.hfs E.hin (fun j' g' _ V' => j' = 41 ∧ V' = V0 fb V X.cpu.gpr ∧
      Fm X.cpu.gpr.rsp X.cpu.gpr g') hK hA (by rw [addr_add_zero]; exact hrip)
    (vc_0 rfl hs1 hs2 hs3 E.hcl hw fun _ a b c d e _ => ⟨rfl, rfl, a, b, c, d, e⟩) ?_
  rintro j' g fl V₁ ⟨rfl, hV₁, hmY⟩ Y t₁ hKY hAY hrY hgY -
  subst V₁ hgY
  refine callK E hKY hAY hrY hmY.1 (lt_len (by decide)) (call_41 _) tgt_41 E.cS (E.kS _ _ hI0) trivial ?_
  intro Z W' t₃ hKZ hAZ hrZ hsZ hkZ hBZ hIZ
  exact from46 E hKZ hAZ hrZ (fm_ret hmY hsZ hkZ) hIZ

end Main

end FV7z.Exr
