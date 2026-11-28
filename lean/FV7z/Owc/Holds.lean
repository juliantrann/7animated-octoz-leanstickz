import FV7z.Owc.Pieces
/-!
# `CStdOutStream::operator<< (const wchar_t *)` (0x5a1530): from the entry to the return (PLAN.md §M, M1)

`CStdOutStream::operator<< (s)`: `rdi` = `this`, `rsi` = `s`. One theorem for each hop: `fromN` runs the piece at
`N` (and the `call` that ends it, `callK`, with the callee as `Ev`'s continuation) and goes on by `fromM`, from the
guard's check and the `ret` (`from107`) back to the entry (`owc_ok`). Each takes the frame (`Fm`: `rsp` = `aR S`,
`r12` = `this`, `rbx`, `r15` as at the entry) and `I` of the bytes.

- `owc_ok`: from the entry (the hypotheses `E : Ev …` with `S` = the entry's `rsp`, `g0` = its registers, `I` of
  the bytes after the prologue, `V0`) to the return (`Ev.kr`: `rsp` 8 up, the callee-saved registers as at the
  entry, `rax` = `this`, `I` of the bytes) or a callee's goal.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
open FV7z.Api (KS)
namespace FV7z.Owc
set_option linter.unusedVariables false

section Runs
variable {prof : Profile} {F : Footprint} {Wl : List Rgn} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {fb S : Addr} {g0 : Gprs} {e₂ : Addr} {code₂ : List Byte} {j₂ : Nat} {I : (Addr → Byte) → Prop}
  {Y : State} {t : Nat} {W : Addr → Byte}

/-- From 107: the guard's check, the epilogue, the `ret`, to `kr`. -/
theorem from107 (E : Ev prof F Wl L s₀ o gev gP gE fb S g0 e₂ code₂ j₂ I) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = owc_at.add 107) (hm : Fm S g0 Y.cpu.gpr) (hIW : I W) :
    GoG prof L o gev gP gE Y t := by
  obtain ⟨s1, s2, s3, s4, s5, s6⟩ := E.hI W hIW
  have ms := hm.1
  have e1 : rdq(W, Y.cpu.gpr.rsp + 56#64) = g0.rbp := by rw [ms, q1]; exact s1
  have e2 : rdq(W, Y.cpu.gpr.rsp + 56#64 + 8) = g0.r12 := by rw [ms, q2]; exact s2
  have e3 : rdq(W, Y.cpu.gpr.rsp + 56#64 + 8 + 8) = g0.r13 := by rw [ms, q3]; exact s3
  have e4 : rdq(W, Y.cpu.gpr.rsp + 56#64 + 8 + 8 + 8) = g0.r14 := by rw [ms, q4]; exact s4
  refine (c_107 prof fb).run E.c E.hfs E.hin (fun j' g' _ V' => j' = 137 ∧ V' = W ∧
      g'.rsp = Y.cpu.gpr.rsp + 56#64 + 8 + 8 + 8 + 8 ∧ g'.rax = Y.cpu.gpr.r12 ∧
      g'.rbp = rdq(W, Y.cpu.gpr.rsp + 56#64) ∧ g'.r12 = rdq(W, Y.cpu.gpr.rsp + 56#64 + 8) ∧
      g'.r13 = rdq(W, Y.cpu.gpr.rsp + 56#64 + 8 + 8) ∧ g'.r14 = rdq(W, Y.cpu.gpr.rsp + 56#64 + 8 + 8 + 8) ∧
      g'.rbx = Y.cpu.gpr.rbx ∧ g'.r15 = Y.cpu.gpr.r15)
    hK hA hr
    (vc_107 (by rw [ms]; exact s6) (by rw [ms]; exact E.fg) E.hcl (by rw [ms, q1]; exact E.fb32)
      (by rw [ms, q2]; exact E.fb24) (by rw [ms, q3]; exact E.fb16) (by rw [ms, q4]; exact E.fb8)
      fun _ a b c d e m n p _ => ⟨rfl, rfl, a, b, c, d, e, m, n, p⟩) ?_
  rintro j' g fl V₁ ⟨rfl, hV₁, gs, ga, gp, g12, g13, g14, gb, g15⟩ U t₁ hKU hAU hrU hgU -
  subst V₁ hgU
  have hsU : U.cpu.gpr.rsp = S := by rw [gs, ms]; exact q5 S
  refine E.c.s_ret hKU hAU E.hin (lt_len (by decide)) hrU (ret_137 _) (by rw [hsU]; exact E.hl) E.hin₂ E.h₂
    (by rw [hsU]; exact s5) ?_
  rintro Z' t₂ hKZ' hAZ' ⟨hrZ', hgZ'⟩
  refine E.kr W Z' t₂ hKZ' hAZ' hrZ' ?_ ?_ ?_ hIW
  · rw [hgZ']
    show U.cpu.gpr.rsp + 8 = _
    rw [hsU]
  · rw [hgZ']
    exact ⟨gb.trans hm.2.1, gp.trans e1, g12.trans e2, g13.trans e3, g14.trans e4, g15.trans hm.2.2.2⟩
  · rw [hgZ']
    exact ga.trans hm.2.2.1

/-- From 93: the `AString`'s characters freed (`delete []` at 102) when not null, to 107. -/
theorem from93 (E : Ev prof F Wl L s₀ o gev gP gE fb S g0 e₂ code₂ j₂ I) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = owc_at.add 93) (hm : Fm S g0 Y.cpu.gpr) (hIW : I W) :
    GoG prof L o gev gP gE Y t := by
  refine (c_93 prof fb).run E.c E.hfs E.hin (fun j' g' _ V' => V' = W ∧ Fr Y.cpu.gpr g' ∧
      (j' = 107 ∨ j' = 102)) hK hA hr
    (vc_93 (by rw [hm.1]; exact E.fl0) (fun _ a _ => ⟨rfl, a, Or.inl rfl⟩)
      fun _ a _ => ⟨rfl, a, Or.inr rfl⟩) ?_
  rintro j' g fl V₁ ⟨hV₁, gf, hj⟩ U t₁ hKU hAU hrU hgU -
  subst V₁ hgU
  have hmU := Fm.fr hm gf
  rcases hj with rfl | rfl
  · exact from107 E hKU hAU hrU hmU hIW
  · refine callK E hKU hAU hrU hmU.1 (lt_len (by decide)) (call_102 _) tgt_102 E.cD (E.kD _ _ hIW)
      trivial ?_
    intro Z W' t₃ hKZ hAZ hrZ hsZ hkZ hBZ hIZ
    exact from107 E hKZ hAZ hrZ (fm_ret hmU hsZ hkZ) hIZ

/-- From 78 (back from `PrintUString`): the `UString`'s characters freed (`delete []` at 88) when not null, to 93. -/
theorem from78 (E : Ev prof F Wl L s₀ o gev gP gE fb S g0 e₂ code₂ j₂ I) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = owc_at.add 78) (hm : Fm S g0 Y.cpu.gpr) (hIW : I W) :
    GoG prof L o gev gP gE Y t := by
  refine (c_78 prof fb).run E.c E.hfs E.hin (fun j' g' _ V' => V' = W ∧ Fr Y.cpu.gpr g' ∧
      (j' = 93 ∨ j' = 88)) hK hA hr
    (vc_78 (by rw [hm.1]; exact E.fl16) (fun _ a _ => ⟨rfl, a, Or.inl rfl⟩)
      fun _ a _ => ⟨rfl, a, Or.inr rfl⟩) ?_
  rintro j' g fl V₁ ⟨hV₁, gf, hj⟩ U t₁ hKU hAU hrU hgU -
  subst V₁ hgU
  have hmU := Fm.fr hm gf
  rcases hj with rfl | rfl
  · exact from93 E hKU hAU hrU hmU hIW
  · refine callK E hKU hAU hrU hmU.1 (lt_len (by decide)) (call_88 _) tgt_88 E.cD (E.kD _ _ hIW)
      trivial ?_
    intro Z W' t₃ hKZ hAZ hrZ hsZ hkZ hBZ hIZ
    exact from93 E hKZ hAZ hrZ (fm_ret hmU hsZ hkZ) hIZ

/-- From 64 (back from `UString::UString`): `PrintUString` (73), to 78. -/
theorem from64 (E : Ev prof F Wl L s₀ o gev gP gE fb S g0 e₂ code₂ j₂ I) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = owc_at.add 64) (hm : Fm S g0 Y.cpu.gpr) (hIW : I W) :
    GoG prof L o gev gP gE Y t := by
  refine (c_64 prof fb).run E.c E.hfs E.hin (fun j' g' _ V' => j' = 73 ∧ V' = W ∧ Fr Y.cpu.gpr g') hK hA hr
    (vc_64 fun _ a _ => ⟨rfl, rfl, a⟩) ?_
  rintro j' g fl V₁ ⟨rfl, hV₁, gf⟩ U t₁ hKU hAU hrU hgU -
  subst V₁ hgU
  have hmU := Fm.fr hm gf
  refine callK E hKU hAU hrU hmU.1 (lt_len (by decide)) (call_73 _) tgt_73 E.cP (E.kP _ _ hIW)
    trivial ?_
  intro Z W' t₃ hKZ hAZ hrZ hsZ hkZ hBZ hIZ
  exact from78 E hKZ hAZ hrZ (fm_ret hmU hsZ hkZ) hIZ

/-- From 53 (back from `AString::AString`): `UString::UString (s)` (59), to 64. -/
theorem from53 (E : Ev prof F Wl L s₀ o gev gP gE fb S g0 e₂ code₂ j₂ I) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = owc_at.add 53) (hm : Fm S g0 Y.cpu.gpr) (hIW : I W) :
    GoG prof L o gev gP gE Y t := by
  refine (c_53 prof fb).run E.c E.hfs E.hin (fun j' g' _ V' => j' = 59 ∧ V' = W ∧ Fr Y.cpu.gpr g') hK hA hr
    (vc_53 fun _ a _ => ⟨rfl, rfl, a⟩) ?_
  rintro j' g fl V₁ ⟨rfl, hV₁, gf⟩ U t₁ hKU hAU hrU hgU -
  subst V₁ hgU
  have hmU := Fm.fr hm gf
  refine callK E hKU hAU hrU hmU.1 (lt_len (by decide)) (call_59 _) tgt_59 E.cU (E.kU _ _ hIW)
    trivial ?_
  intro Z W' t₃ hKZ hAZ hrZ hsZ hkZ hBZ hIZ
  exact from64 E hKZ hAZ hrZ (fm_ret hmU hsZ hkZ) hIZ

end Runs


section Main
variable {prof : Profile} {F : Footprint} {Wl : List Rgn} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {fb : Addr} {e₂ : Addr} {code₂ : List Byte} {j₂ : Nat} {I : (Addr → Byte) → Prop}
  {X : State} {t : Nat} {V : Addr → Byte}

/-- `CStdOutStream::operator<< (this, s)` from its entry (`X`'s registers, `S` = their `rsp`, `fb` the `fs` base;
the pushes' slots and the guard's slot in what the run may store into, `I` of the bytes after the prologue). -/
theorem owc_ok (E : Ev prof F Wl L s₀ o gev gP gE fb X.cpu.gpr.rsp X.cpu.gpr e₂ code₂ j₂ I)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = owc_at)
    (hs1 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8) i))
    (hs2 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8 - 8) i))
    (hs3 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8 - 8 - 8) i))
    (hs4 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8 - 8 - 8 - 8) i))
    (hw : ∀ i < 8, Foot Wl (Addr.add (aR X.cpu.gpr.rsp + 40#64) i)) (hI0 : I (V0 fb V X.cpu.gpr)) :
    GoG prof L o gev gP gE X t := by
  refine (c_0 prof fb).run E.c E.hfs E.hin (fun j' g' _ V' => j' = 48 ∧ V' = V0 fb V X.cpu.gpr ∧
      Fm X.cpu.gpr.rsp X.cpu.gpr g') hK hA (by rw [addr_add_zero]; exact hrip)
    (vc_0 rfl hs1 hs2 hs3 hs4 E.hcl hw fun _ a b c d _ => ⟨rfl, rfl, a, b, c, d⟩) ?_
  rintro j' g fl V₁ ⟨rfl, hV₁, hmY⟩ Y t₁ hKY hAY hrY hgY -
  subst V₁ hgY
  refine callK E hKY hAY hrY hmY.1 (lt_len (by decide)) (call_48 _) tgt_48 E.cA (E.kA _ _ hI0) trivial ?_
  intro Z W' t₃ hKZ hAZ hrZ hsZ hkZ hBZ hIZ
  exact from53 E hKZ hAZ hrZ (fm_ret hmY hsZ hkZ) hIZ

end Main

end FV7z.Owc
