import FV7z.Pew.Pieces
/-!
# `Print_ErrorFormatIndex_Warning` (0x5e96e0): from the entry to the return (PLAN.md §M, M1)

`Print_ErrorFormatIndex_Warning (_so, codecs, arc)`: `rdi` = `_so`, `rsi` = `codecs`, `rdx` = `arc`. One theorem for
each hop: `fromN` runs the piece at `N` (and the `call` that ends it, `callK`, with the callee as `Ev`'s
continuation) and goes on by `fromM`, from the guard's check and the `ret` (`from228`) back to the entry (`pew_ok`).
Each takes the frame (`Fm`: `rsp` = `aR S`, `rbx` = `arc`, `r13` = `codecs`, `r14`, `r15` as at the entry) and `I`
of the bytes.

- `pew_ok`: from the entry (the hypotheses `E : Ev …` with `S` = the entry's `rsp`, `g0` = its registers, `I` of
  the bytes after the prologue, `V0`) to the return (`Ev.kr`: `rsp` 8 up, the callee-saved registers as at the
  entry, `I` of the bytes) or a callee's goal.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
open FV7z.Api (KS)
namespace FV7z.Pew
set_option linter.unusedVariables false

section Runs
variable {prof : Profile} {F : Footprint} {Wl : List Rgn} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {fb S : Addr} {g0 : Gprs} {e₂ : Addr} {code₂ : List Byte} {j₂ : Nat} {I : (Addr → Byte) → Prop}
  {Y : State} {t : Nat} {W : Addr → Byte}

/-- From 228: the guard's check, the epilogue, the `ret`, to `kr`. -/
theorem from228 (E : Ev prof F Wl L s₀ o gev gP gE fb S g0 e₂ code₂ j₂ I) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = pew_at.add 228) (hm : Fm S g0 Y.cpu.gpr) (hIW : I W) :
    GoG prof L o gev gP gE Y t := by
  obtain ⟨s1, s2, s3, s4, s5, s6⟩ := E.hI W hIW
  have ms := hm.1
  have e1 : rdq(W, Y.cpu.gpr.rsp + 40#64) = g0.rbx := by rw [ms, q1]; exact s1
  have e2 : rdq(W, Y.cpu.gpr.rsp + 40#64 + 8) = g0.rbp := by rw [ms, q2]; exact s2
  have e3 : rdq(W, Y.cpu.gpr.rsp + 40#64 + 8 + 8) = g0.r12 := by rw [ms, q3]; exact s3
  have e4 : rdq(W, Y.cpu.gpr.rsp + 40#64 + 8 + 8 + 8) = g0.r13 := by rw [ms, q4]; exact s4
  refine (c_228 prof fb).run E.c E.hfs E.hin (fun j' g' _ V' => j' = 254 ∧ V' = W ∧
      g'.rsp = Y.cpu.gpr.rsp + 40#64 + 8 + 8 + 8 + 8 ∧ g'.rbx = rdq(W, Y.cpu.gpr.rsp + 40#64) ∧
      g'.rbp = rdq(W, Y.cpu.gpr.rsp + 40#64 + 8) ∧ g'.r12 = rdq(W, Y.cpu.gpr.rsp + 40#64 + 8 + 8) ∧
      g'.r13 = rdq(W, Y.cpu.gpr.rsp + 40#64 + 8 + 8 + 8) ∧ g'.r14 = Y.cpu.gpr.r14 ∧ g'.r15 = Y.cpu.gpr.r15)
    hK hA hr
    (vc_228 (by rw [ms]; exact s6) (by rw [ms]; exact E.fg) E.hcl (by rw [ms, q1]; exact E.fb32)
      (by rw [ms, q2]; exact E.fb24) (by rw [ms, q3]; exact E.fb16) (by rw [ms, q4]; exact E.fb8)
      fun _ a b c d e m n _ => ⟨rfl, rfl, a, b, c, d, e, m, n⟩) ?_
  rintro j' g fl V₁ ⟨rfl, hV₁, gs, gb, gp, g12, g13, g14, g15⟩ U t₁ hKU hAU hrU hgU -
  subst V₁ hgU
  have hsU : U.cpu.gpr.rsp = S := by rw [gs, ms]; exact q5 S
  refine E.c.s_ret hKU hAU E.hin (lt_len (by decide)) hrU (ret_254 _) (by rw [hsU]; exact E.hl) E.hin₂ E.h₂
    (by rw [hsU]; exact s5) ?_
  rintro Z' t₂ hKZ' hAZ' ⟨hrZ', hgZ'⟩
  refine E.kr W Z' t₂ hKZ' hAZ' hrZ' ?_ ?_ hIW
  · rw [hgZ']
    show U.cpu.gpr.rsp + 8 = _
    rw [hsU]
  · rw [hgZ']
    exact ⟨gb.trans e1, gp.trans e2, g12.trans e3, g13.trans e4, g14.trans hm.2.2.2.1, g15.trans hm.2.2.2.2⟩

/-- From 214: the local `UString`'s characters freed (`delete []` at 223) when not null, to 228. -/
theorem from214 (E : Ev prof F Wl L s₀ o gev gP gE fb S g0 e₂ code₂ j₂ I) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = pew_at.add 214) (hm : Fm S g0 Y.cpu.gpr) (hIW : I W) :
    GoG prof L o gev gP gE Y t := by
  refine (c_214 prof fb).run E.c E.hfs E.hin (fun j' g' _ V' => V' = W ∧ Fr Y.cpu.gpr g' ∧
      (j' = 228 ∨ j' = 223)) hK hA hr
    (vc_214 (by rw [hm.1]; exact E.fl0) (fun _ a _ => ⟨rfl, a, Or.inl rfl⟩)
      fun _ a _ => ⟨rfl, a, Or.inr rfl⟩) ?_
  rintro j' g fl V₁ ⟨hV₁, gf, hj⟩ U t₁ hKU hAU hrU hgU -
  subst V₁ hgU
  have hmU := Fm.fr hm gf
  rcases hj with rfl | rfl
  · exact from228 E hKU hAU hrU hmU hIW
  · refine callK E hKU hAU hrU hmU.1 (lt_len (by decide)) (call_223 _) tgt_223 E.cD (E.kD _ _ hIW)
      trivial ?_
    intro Z W' t₃ hKZ hAZ hrZ hsZ hkZ hBZ hIZ
    exact from228 E hKZ hAZ hrZ (fm_ret hmU hsZ hkZ) hIZ

/-- From 206: `endl` (209), to 214. -/
theorem from206 (E : Ev prof F Wl L s₀ o gev gP gE fb S g0 e₂ code₂ j₂ I) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = pew_at.add 206) (hm : Fm S g0 Y.cpu.gpr) (hIW : I W) :
    GoG prof L o gev gP gE Y t := by
  refine (c_206 prof fb).run E.c E.hfs E.hin (fun j' g' _ V' => j' = 209 ∧ V' = W ∧ Fr Y.cpu.gpr g') hK hA hr
    (vc_206 fun _ a _ => ⟨rfl, rfl, a⟩) ?_
  rintro j' g fl V₁ ⟨rfl, hV₁, gf⟩ U t₁ hKU hAU hrU hgU -
  subst V₁ hgU
  have hmU := Fm.fr hm gf
  refine callK E hKU hAU hrU hmU.1 (lt_len (by decide)) (call_209 _) tgt_209 E.cE (E.kE _ _ hIW)
    trivial ?_
  intro Z W' t₃ hKZ hAZ hrZ hsZ hkZ hBZ hIZ
  exact from214 E hKZ hAZ hrZ (fm_ret hmU hsZ hkZ) hIZ

/-- From 195: `endl` (201), to 206. -/
theorem from195 (E : Ev prof F Wl L s₀ o gev gP gE fb S g0 e₂ code₂ j₂ I) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = pew_at.add 195) (hm : Fm S g0 Y.cpu.gpr) (hIW : I W) :
    GoG prof L o gev gP gE Y t := by
  refine (c_195 prof fb).run E.c E.hfs E.hin (fun j' g' _ V' => j' = 201 ∧ V' = W ∧ Fr Y.cpu.gpr g') hK hA hr
    (vc_195 fun _ a _ => ⟨rfl, rfl, a⟩) ?_
  rintro j' g fl V₁ ⟨rfl, hV₁, gf⟩ U t₁ hKU hAU hrU hgU -
  subst V₁ hgU
  have hmU := Fm.fr hm gf
  refine callK E hKU hAU hrU hmU.1 (lt_len (by decide)) (call_201 _) tgt_201 E.cE (E.kE _ _ hIW)
    trivial ?_
  intro Z W' t₃ hKZ hAZ hrZ hsZ hkZ hBZ hIZ
  exact from206 E hKZ hAZ hrZ (fm_ret hmU hsZ hkZ) hIZ

/-- From 183: `*_so << s` (190), to 195. -/
theorem from183 (E : Ev prof F Wl L s₀ o gev gP gE fb S g0 e₂ code₂ j₂ I) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = pew_at.add 183) (hm : Fm S g0 Y.cpu.gpr) (hIW : I W) :
    GoG prof L o gev gP gE Y t := by
  refine (c_183 prof fb).run E.c E.hfs E.hin (fun j' g' _ V' => j' = 190 ∧ V' = W ∧ Fr Y.cpu.gpr g') hK hA hr
    (vc_183 (by rw [hm.1]; exact E.fl0) fun _ a _ => ⟨rfl, rfl, a⟩) ?_
  rintro j' g fl V₁ ⟨rfl, hV₁, gf⟩ U t₁ hKU hAU hrU hgU -
  subst V₁ hgU
  have hmU := Fm.fr hm gf
  refine callK E hKU hAU hrU hmU.1 (lt_len (by decide)) (call_190 _) tgt_190 E.cO (E.kO _ _ hIW)
    trivial ?_
  intro Z W' t₃ hKZ hAZ hrZ hsZ hkZ hBZ hIZ
  exact from195 E hKZ hAZ hrZ (fm_ret hmU hsZ hkZ) hIZ

/-- From 279 (back from `operator+=`): to 183. -/
theorem from279 (E : Ev prof F Wl L s₀ o gev gP gE fb S g0 e₂ code₂ j₂ I) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = pew_at.add 279) (hm : Fm S g0 Y.cpu.gpr) (hIW : I W) :
    GoG prof L o gev gP gE Y t := by
  refine (c_279 prof fb).run E.c E.hfs E.hin (fun j' g' _ V' => j' = 183 ∧ g' = Y.cpu.gpr ∧ V' = W) hK hA hr
    (vc_279 fun _ => ⟨rfl, rfl, rfl⟩) ?_
  rintro j' g fl V₁ ⟨rfl, rfl, hV₁⟩ U t₁ hKU hAU hrU hgU -
  subst V₁
  exact from183 E hKU hAU hrU (by rw [hgU]; exact hm) hIW

/-- From 264 (back from `Add_LF`): `s += "…"` (274), to 279. -/
theorem from264 (E : Ev prof F Wl L s₀ o gev gP gE fb S g0 e₂ code₂ j₂ I) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = pew_at.add 264) (hm : Fm S g0 Y.cpu.gpr) (hIW : I W) :
    GoG prof L o gev gP gE Y t := by
  refine (c_264 prof fb).run E.c E.hfs E.hin (fun j' g' _ V' => j' = 274 ∧ V' = W ∧ Fr Y.cpu.gpr g') hK hA hr
    (vc_264 fun _ a _ => ⟨rfl, rfl, a⟩) ?_
  rintro j' g fl V₁ ⟨rfl, hV₁, gf⟩ U t₁ hKU hAU hrU hgU -
  subst V₁ hgU
  have hmU := Fm.fr hm gf
  refine callK E hKU hAU hrU hmU.1 (lt_len (by decide)) (call_274 _) tgt_274 E.cP (E.kP _ _ hIW)
    trivial ?_
  intro Z W' t₃ hKZ hAZ hrZ hsZ hkZ hBZ hIZ
  exact from279 E hKZ hAZ hrZ (fm_ret hmU hsZ hkZ) hIZ

/-- From 168: `Add_Messsage_Pre_ArcType` (178), to 183. -/
theorem from168 (E : Ev prof F Wl L s₀ o gev gP gE fb S g0 e₂ code₂ j₂ I) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = pew_at.add 168) (hm : Fm S g0 Y.cpu.gpr) (hIW : I W) :
    GoG prof L o gev gP gE Y t := by
  refine (c_168 prof fb).run E.c E.hfs E.hin (fun j' g' _ V' => j' = 178 ∧ V' = W ∧ Fr Y.cpu.gpr g') hK hA hr
    (vc_168 fun _ a _ => ⟨rfl, rfl, a⟩) ?_
  rintro j' g fl V₁ ⟨rfl, hV₁, gf⟩ U t₁ hKU hAU hrU hgU -
  subst V₁ hgU
  have hmU := Fm.fr hm gf
  refine callK E hKU hAU hrU hmU.1 (lt_len (by decide)) (call_178 _) tgt_178 E.cN (E.kN _ _ hIW)
    trivial ?_
  intro Z W' t₃ hKZ hAZ hrZ hsZ hkZ hBZ hIZ
  exact from183 E hKZ hAZ hrZ (fm_ret hmU hsZ hkZ) hIZ

/-- From 141: the name of the format `arc.FormatIndex`, to 168. -/
theorem from141 (E : Ev prof F Wl L s₀ o gev gP gE fb S g0 e₂ code₂ j₂ I) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = pew_at.add 141) (hm : Fm S g0 Y.cpu.gpr) (hIW : I W) :
    GoG prof L o gev gP gE Y t := by
  have fB := E.fe W hIW 88#64 (Or.inl rfl)
  rw [← hm.2.1, ← hm.2.2.1] at fB
  refine (c_141 prof fb).run E.c E.hfs E.hin (fun j' g' _ V' => j' = 168 ∧ V' = W ∧ Fr Y.cpu.gpr g') hK hA hr
    (vc_141 (by rw [hm.2.1]; exact E.f88) (by rw [hm.2.2.1]; exact E.f16) (fun hx => (fB hx).1)
      (fun hx => (fB hx).2) fun _ a _ => ⟨rfl, rfl, a⟩) ?_
  rintro j' g fl V₁ ⟨rfl, hV₁, gf⟩ U t₁ hKU hAU hrU hgU -
  subst V₁ hgU
  exact from168 E hKU hAU hrU (Fm.fr hm gf) hIW

/-- From 126: `Add_Messsage_Pre_ArcType` (136), to 141. -/
theorem from126 (E : Ev prof F Wl L s₀ o gev gP gE fb S g0 e₂ code₂ j₂ I) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = pew_at.add 126) (hm : Fm S g0 Y.cpu.gpr) (hIW : I W) :
    GoG prof L o gev gP gE Y t := by
  refine (c_126 prof fb).run E.c E.hfs E.hin (fun j' g' _ V' => j' = 136 ∧ V' = W ∧ Fr Y.cpu.gpr g') hK hA hr
    (vc_126 fun _ a _ => ⟨rfl, rfl, a⟩) ?_
  rintro j' g fl V₁ ⟨rfl, hV₁, gf⟩ U t₁ hKU hAU hrU hgU -
  subst V₁ hgU
  have hmU := Fm.fr hm gf
  refine callK E hKU hAU hrU hmU.1 (lt_len (by decide)) (call_136 _) tgt_136 E.cN (E.kN _ _ hIW)
    trivial ?_
  intro Z W' t₃ hKZ hAZ hrZ hsZ hkZ hBZ hIZ
  exact from141 E hKZ hAZ hrZ (fm_ret hmU hsZ hkZ) hIZ

/-- From 87: the two format indices equal, `Add_LF` (259) and 264; else 126. -/
theorem from87 (E : Ev prof F Wl L s₀ o gev gP gE fb S g0 e₂ code₂ j₂ I) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = pew_at.add 87) (hm : Fm S g0 Y.cpu.gpr) (hIW : I W) :
    GoG prof L o gev gP gE Y t := by
  have fA := E.fe W hIW 164#64 (Or.inr rfl)
  rw [← hm.2.1, ← hm.2.2.1] at fA
  refine (c_87 prof fb).run E.c E.hfs E.hin (fun j' g' _ V' => V' = W ∧ Fr Y.cpu.gpr g' ∧
      (j' = 259 ∨ j' = 126)) hK hA hr
    (vc_87 (by rw [hm.2.1]; exact E.f88) (by rw [hm.2.1]; exact E.f164) (by rw [hm.2.2.1]; exact E.f16)
      (fun hx => (fA hx).1) (fun hx => (fA hx).2)
      (fun _ a _ => ⟨rfl, a, Or.inl rfl⟩) fun _ a _ => ⟨rfl, a, Or.inr rfl⟩) ?_
  rintro j' g fl V₁ ⟨hV₁, gf, hj⟩ U t₁ hKU hAU hrU hgU -
  subst V₁ hgU
  have hmU := Fm.fr hm gf
  rcases hj with rfl | rfl
  · refine callK E hKU hAU hrU hmU.1 (lt_len (by decide)) (call_259 _) tgt_259 E.cB (E.kB _ _ hIW)
      trivial ?_
    intro Z W' t₃ hKZ hAZ hrZ hsZ hkZ hBZ hIZ
    exact from264 E hKZ hAZ hrZ (fm_ret hmU hsZ hkZ) hIZ
  · exact from126 E hKU hAU hrU hmU hIW

/-- From 79: `UString::UString ()` (82), to 87. -/
theorem from79 (E : Ev prof F Wl L s₀ o gev gP gE fb S g0 e₂ code₂ j₂ I) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = pew_at.add 79) (hm : Fm S g0 Y.cpu.gpr) (hIW : I W) :
    GoG prof L o gev gP gE Y t := by
  refine (c_79 prof fb).run E.c E.hfs E.hin (fun j' g' _ V' => j' = 82 ∧ V' = W ∧ Fr Y.cpu.gpr g') hK hA hr
    (vc_79 fun _ a _ => ⟨rfl, rfl, a⟩) ?_
  rintro j' g fl V₁ ⟨rfl, hV₁, gf⟩ U t₁ hKU hAU hrU hgU -
  subst V₁ hgU
  have hmU := Fm.fr hm gf
  refine callK E hKU hAU hrU hmU.1 (lt_len (by decide)) (call_82 _) tgt_82 E.cA (E.kA _ _ hIW)
    trivial ?_
  intro Z W' t₃ hKZ hAZ hrZ hsZ hkZ hBZ hIZ
  exact from87 E hKZ hAZ hrZ (fm_ret hmU hsZ hkZ) hIZ

/-- From 64 (back from `fwrite`): `NormalizePrint_UString_Path` (74), to 79. -/
theorem from64 (E : Ev prof F Wl L s₀ o gev gP gE fb S g0 e₂ code₂ j₂ I) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = pew_at.add 64) (hm : Fm S g0 Y.cpu.gpr) (hIW : I W) :
    GoG prof L o gev gP gE Y t := by
  refine (c_64 prof fb).run E.c E.hfs E.hin (fun j' g' _ V' => j' = 74 ∧ V' = W ∧ Fr Y.cpu.gpr g') hK hA hr
    (vc_64 fun _ a _ => ⟨rfl, rfl, a⟩) ?_
  rintro j' g fl V₁ ⟨rfl, hV₁, gf⟩ U t₁ hKU hAU hrU hgU -
  subst V₁ hgU
  have hmU := Fm.fr hm gf
  refine callK E hKU hAU hrU hmU.1 (lt_len (by decide)) (call_74 _) tgt_74 E.cU (E.kU _ _ hIW)
    trivial ?_
  intro Z W' t₃ hKZ hAZ hrZ hsZ hkZ hBZ hIZ
  exact from79 E hKZ hAZ hrZ (fm_ret hmU hsZ hkZ) hIZ

end Runs


section Main
variable {prof : Profile} {F : Footprint} {Wl : List Rgn} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {fb : Addr} {e₂ : Addr} {code₂ : List Byte} {j₂ : Nat} {I : (Addr → Byte) → Prop}
  {X : State} {t : Nat} {V : Addr → Byte}

/-- `Print_ErrorFormatIndex_Warning (_so, codecs, arc)` from its entry (`X`'s registers, `S` = their `rsp`, `fb` the
`fs` base; the pushes' slots and the guard's slot in what the run may store into, `I` of the bytes after the
prologue). -/
theorem pew_ok (E : Ev prof F Wl L s₀ o gev gP gE fb X.cpu.gpr.rsp X.cpu.gpr e₂ code₂ j₂ I)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = pew_at)
    (hs1 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8) i))
    (hs2 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8 - 8) i))
    (hs3 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8 - 8 - 8) i))
    (hs4 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8 - 8 - 8 - 8) i))
    (hw : ∀ i < 8, Foot Wl (Addr.add (aR X.cpu.gpr.rsp + 24#64) i)) (hI0 : I (V0 fb V X.cpu.gpr)) :
    GoG prof L o gev gP gE X t := by
  refine (c_0 prof fb).run E.c E.hfs E.hin (fun j' g' _ V' => j' = 59 ∧ V' = V0 fb V X.cpu.gpr ∧
      Fm X.cpu.gpr.rsp X.cpu.gpr g') hK hA (by rw [addr_add_zero]; exact hrip)
    (vc_0 rfl hs1 hs2 hs3 hs4 E.hso E.hcl hw fun _ a b c d e _ => ⟨rfl, rfl, a, b, c, d, e⟩) ?_
  rintro j' g fl V₁ ⟨rfl, hV₁, hmY⟩ Y t₁ hKY hAY hrY hgY -
  subst V₁ hgY
  refine callK E hKY hAY hrY hmY.1 (lt_len (by decide)) (call_59 _) tgt_59 E.cW (E.kW _ _ hI0) trivial ?_
  intro Z W' t₃ hKZ hAZ hrZ hsZ hkZ hBZ hIZ
  exact from64 E hKZ hAZ hrZ (fm_ret hmY hsZ hkZ) hIZ

end Main

end FV7z.Pew
