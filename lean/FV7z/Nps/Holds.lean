import FV7z.Nps.Pieces
/-!
# `CStdOutStream::NormalizePrint_UString (const UString &)` (0x5a1870): from the entry to the return (PLAN.md §M, M1)

`CStdOutStream::NormalizePrint_UString (s)`: `rdi` = `this`, `rsi` = `s`. One theorem for each hop: `fromN` runs the
piece at `N` (and the `call` that ends it, `callK`, with the callee as `Ev`'s continuation) and goes on by `fromM`,
from the guard's check and the `ret` (`from110`) back to the entry (`nps_ok`). Each takes the frame (`Fm`: `rsp` =
`aR S`, `rbx`, `r14`, `r15` as at the entry) and `I` of the bytes.

- `nps_ok`: from the entry (the hypotheses `E : Ev …` with `S` = the entry's `rsp`, `g0` = its registers, `I` of
  the bytes after the prologue, `V0`) to the return (`Ev.kr`: `rsp` 8 up, the callee-saved registers as at the
  entry, `I` of the bytes) or a callee's goal.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
open FV7z.Api (KS)
namespace FV7z.Nps
set_option linter.unusedVariables false

section Runs
variable {prof : Profile} {F : Footprint} {Wl : List Rgn} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {fb S : Addr} {g0 : Gprs} {e₂ : Addr} {code₂ : List Byte} {j₂ : Nat} {I : (Addr → Byte) → Prop}
  {Y : State} {t : Nat} {W : Addr → Byte}

/-- From 110: the guard's check, the epilogue, the `ret`, to `kr`. -/
theorem from110 (E : Ev prof F Wl L s₀ o gev gP gE fb S g0 e₂ code₂ j₂ I) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = nps_at.add 110) (hm : Fm S g0 Y.cpu.gpr) (hIW : I W) :
    GoG prof L o gev gP gE Y t := by
  obtain ⟨s1, s2, s3, s4, s5⟩ := E.hI W hIW
  have ms := hm.1
  have e1 : rdq(W, Y.cpu.gpr.rsp + 48#64) = g0.rbp := by rw [ms, q1]; exact s1
  have e2 : rdq(W, Y.cpu.gpr.rsp + 48#64 + 8) = g0.r12 := by rw [ms, q2]; exact s2
  have e3 : rdq(W, Y.cpu.gpr.rsp + 48#64 + 8 + 8) = g0.r13 := by rw [ms, q3]; exact s3
  refine (c_110 prof fb).run E.c E.hfs E.hin (fun j' g' _ V' => j' = 135 ∧ V' = W ∧
      g'.rsp = Y.cpu.gpr.rsp + 48#64 + 8 + 8 + 8 ∧
      g'.rbp = rdq(W, Y.cpu.gpr.rsp + 48#64) ∧ g'.r12 = rdq(W, Y.cpu.gpr.rsp + 48#64 + 8) ∧
      g'.r13 = rdq(W, Y.cpu.gpr.rsp + 48#64 + 8 + 8) ∧
      g'.rbx = Y.cpu.gpr.rbx ∧ g'.r14 = Y.cpu.gpr.r14 ∧ g'.r15 = Y.cpu.gpr.r15)
    hK hA hr
    (vc_110 (by rw [ms]; exact s5) (by rw [ms]; exact E.fg) E.hcl (by rw [ms, q1]; exact E.fb24)
      (by rw [ms, q2]; exact E.fb16) (by rw [ms, q3]; exact E.fb8)
      fun _ a c d e m n p _ => ⟨rfl, rfl, a, c, d, e, m, n, p⟩) ?_
  rintro j' g fl V₁ ⟨rfl, hV₁, gs, gp, g12, g13, gb, g14, g15⟩ U t₁ hKU hAU hrU hgU -
  subst V₁ hgU
  have hsU : U.cpu.gpr.rsp = S := by rw [gs, ms]; exact q4 S
  refine E.c.s_ret hKU hAU E.hin (lt_len (by decide)) hrU (ret_135 _) (by rw [hsU]; exact E.hl) E.hin₂ E.h₂
    (by rw [hsU]; exact s4) ?_
  rintro Z' t₂ hKZ' hAZ' ⟨hrZ', hgZ'⟩
  refine E.kr W Z' t₂ hKZ' hAZ' hrZ' ?_ ?_ hIW
  · rw [hgZ']
    show U.cpu.gpr.rsp + 8 = _
    rw [hsU]
  · rw [hgZ']
    exact ⟨gb.trans hm.2.1, gp.trans e1, g12.trans e2, g13.trans e3, g14.trans hm.2.2.1, g15.trans hm.2.2.2⟩

/-- From 96: the `UString`'s characters freed (`delete []` at 105) when not null, to 110. -/
theorem from96 (E : Ev prof F Wl L s₀ o gev gP gE fb S g0 e₂ code₂ j₂ I) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = nps_at.add 96) (hm : Fm S g0 Y.cpu.gpr) (hIW : I W) :
    GoG prof L o gev gP gE Y t := by
  refine (c_96 prof fb).run E.c E.hfs E.hin (fun j' g' _ V' => V' = W ∧ Fr Y.cpu.gpr g' ∧
      (j' = 110 ∨ j' = 105)) hK hA hr
    (vc_96 (by rw [hm.1]; exact E.fl0) (fun _ a _ => ⟨rfl, a, Or.inl rfl⟩)
      fun _ a _ => ⟨rfl, a, Or.inr rfl⟩) ?_
  rintro j' g fl V₁ ⟨hV₁, gf, hj⟩ U t₁ hKU hAU hrU hgU -
  subst V₁ hgU
  have hmU := Fm.fr hm gf
  rcases hj with rfl | rfl
  · exact from110 E hKU hAU hrU hmU hIW
  · refine callK E hKU hAU hrU hmU.1 (lt_len (by decide)) (call_105 _) tgt_105 E.cD (E.kD _ _ hIW)
      trivial ?_
    intro Z W' t₃ hKZ hAZ hrZ hsZ hkZ hBZ hIZ
    exact from110 E hKZ hAZ hrZ (fm_ret hmU hsZ hkZ) hIZ

/-- From 81 (back from `PrintUString`): the `AString`'s characters freed (`delete []` at 91) when not null, to 96. -/
theorem from81 (E : Ev prof F Wl L s₀ o gev gP gE fb S g0 e₂ code₂ j₂ I) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = nps_at.add 81) (hm : Fm S g0 Y.cpu.gpr) (hIW : I W) :
    GoG prof L o gev gP gE Y t := by
  refine (c_81 prof fb).run E.c E.hfs E.hin (fun j' g' _ V' => V' = W ∧ Fr Y.cpu.gpr g' ∧
      (j' = 96 ∨ j' = 91)) hK hA hr
    (vc_81 (by rw [hm.1]; exact E.fl16) (fun _ a _ => ⟨rfl, a, Or.inl rfl⟩)
      fun _ a _ => ⟨rfl, a, Or.inr rfl⟩) ?_
  rintro j' g fl V₁ ⟨hV₁, gf, hj⟩ U t₁ hKU hAU hrU hgU -
  subst V₁ hgU
  have hmU := Fm.fr hm gf
  rcases hj with rfl | rfl
  · exact from96 E hKU hAU hrU hmU hIW
  · refine callK E hKU hAU hrU hmU.1 (lt_len (by decide)) (call_91 _) tgt_91 E.cD (E.kD _ _ hIW)
      trivial ?_
    intro Z W' t₃ hKZ hAZ hrZ hsZ hkZ hBZ hIZ
    exact from96 E hKZ hAZ hrZ (fm_ret hmU hsZ hkZ) hIZ

/-- From 67 (back from `AString::AString`): `PrintUString` (76), to 81. -/
theorem from67 (E : Ev prof F Wl L s₀ o gev gP gE fb S g0 e₂ code₂ j₂ I) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = nps_at.add 67) (hm : Fm S g0 Y.cpu.gpr) (hIW : I W) :
    GoG prof L o gev gP gE Y t := by
  refine (c_67 prof fb).run E.c E.hfs E.hin (fun j' g' _ V' => j' = 76 ∧ V' = W ∧ Fr Y.cpu.gpr g') hK hA hr
    (vc_67 fun _ a _ => ⟨rfl, rfl, a⟩) ?_
  rintro j' g fl V₁ ⟨rfl, hV₁, gf⟩ U t₁ hKU hAU hrU hgU -
  subst V₁ hgU
  have hmU := Fm.fr hm gf
  refine callK E hKU hAU hrU hmU.1 (lt_len (by decide)) (call_76 _) tgt_76 E.cP (E.kP _ _ hIW)
    trivial ?_
  intro Z W' t₃ hKZ hAZ hrZ hsZ hkZ hBZ hIZ
  exact from81 E hKZ hAZ hrZ (fm_ret hmU hsZ hkZ) hIZ

/-- From 54 (back from `Normalize_UString`): `AString::AString ()` (62), to 67. -/
theorem from54 (E : Ev prof F Wl L s₀ o gev gP gE fb S g0 e₂ code₂ j₂ I) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = nps_at.add 54) (hm : Fm S g0 Y.cpu.gpr) (hIW : I W) :
    GoG prof L o gev gP gE Y t := by
  refine (c_54 prof fb).run E.c E.hfs E.hin (fun j' g' _ V' => j' = 62 ∧ V' = W ∧ Fr Y.cpu.gpr g') hK hA hr
    (vc_54 fun _ a _ => ⟨rfl, rfl, a⟩) ?_
  rintro j' g fl V₁ ⟨rfl, hV₁, gf⟩ U t₁ hKU hAU hrU hgU -
  subst V₁ hgU
  have hmU := Fm.fr hm gf
  refine callK E hKU hAU hrU hmU.1 (lt_len (by decide)) (call_62 _) tgt_62 E.cA (E.kA _ _ hIW)
    trivial ?_
  intro Z W' t₃ hKZ hAZ hrZ hsZ hkZ hBZ hIZ
  exact from67 E hKZ hAZ hrZ (fm_ret hmU hsZ hkZ) hIZ

/-- From 43 (back from the copy constructor): `Normalize_UString` (49), to 54. -/
theorem from43 (E : Ev prof F Wl L s₀ o gev gP gE fb S g0 e₂ code₂ j₂ I) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = nps_at.add 43) (hm : Fm S g0 Y.cpu.gpr) (hIW : I W) :
    GoG prof L o gev gP gE Y t := by
  refine (c_43 prof fb).run E.c E.hfs E.hin (fun j' g' _ V' => j' = 49 ∧ V' = W ∧ Fr Y.cpu.gpr g') hK hA hr
    (vc_43 fun _ a _ => ⟨rfl, rfl, a⟩) ?_
  rintro j' g fl V₁ ⟨rfl, hV₁, gf⟩ U t₁ hKU hAU hrU hgU -
  subst V₁ hgU
  have hmU := Fm.fr hm gf
  refine callK E hKU hAU hrU hmU.1 (lt_len (by decide)) (call_49 _) tgt_49 E.cN (E.kN _ _ hIW)
    trivial ?_
  intro Z W' t₃ hKZ hAZ hrZ hsZ hkZ hBZ hIZ
  exact from54 E hKZ hAZ hrZ (fm_ret hmU hsZ hkZ) hIZ

end Runs

section Main
variable {prof : Profile} {F : Footprint} {Wl : List Rgn} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {fb : Addr} {e₂ : Addr} {code₂ : List Byte} {j₂ : Nat} {I : (Addr → Byte) → Prop}
  {X : State} {t : Nat} {V : Addr → Byte}

/-- `CStdOutStream::NormalizePrint_UString (this, s)` from its entry (`X`'s registers, `S` = their `rsp`, `fb` the
`fs` base; the pushes' slots and the guard's slot in what the run may store into, `I` of the bytes after the
prologue). -/
theorem nps_ok (E : Ev prof F Wl L s₀ o gev gP gE fb X.cpu.gpr.rsp X.cpu.gpr e₂ code₂ j₂ I)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = nps_at)
    (hs1 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8) i))
    (hs2 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8 - 8) i))
    (hs3 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8 - 8 - 8) i))
    (hw : ∀ i < 8, Foot Wl (Addr.add (aR X.cpu.gpr.rsp + 40#64) i)) (hI0 : I (V0 fb V X.cpu.gpr)) :
    GoG prof L o gev gP gE X t := by
  refine (c_0 prof fb).run E.c E.hfs E.hin (fun j' g' _ V' => j' = 38 ∧ V' = V0 fb V X.cpu.gpr ∧
      Fm X.cpu.gpr.rsp X.cpu.gpr g') hK hA (by rw [addr_add_zero]; exact hrip)
    (vc_0 rfl hs1 hs2 hs3 E.hcl hw fun _ a b c d _ => ⟨rfl, rfl, a, b, c, d⟩) ?_
  rintro j' g fl V₁ ⟨rfl, hV₁, hmY⟩ Y t₁ hKY hAY hrY hgY -
  subst V₁ hgY
  refine callK E hKY hAY hrY hmY.1 (lt_len (by decide)) (call_38 _) tgt_38 E.cU (E.kU _ _ hI0) trivial ?_
  intro Z W' t₃ hKZ hAZ hrZ hsZ hkZ hBZ hIZ
  exact from43 E hKZ hAZ hrZ (fm_ret hmY hsZ hkZ) hIZ

end Main

end FV7z.Nps
