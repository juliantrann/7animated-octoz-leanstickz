import FV7z.Mbs.Pieces
/-!
# `MultiByteToUnicodeString (const AString &, UINT)` (0x450c60): from the entry to the return (PLAN.md §M, M1)

`MultiByteToUnicodeString (src, codePage)`: `rdi` = the result's `UString` slot, `rsi` = `src`, `edx` =
`codePage`. One theorem for each hop: `fromN` runs the piece at `N` (and the `call` that ends it, `callK`, with the
callee as `Ev`'s continuation) and goes on by `fromM`, from the `ret` (`from37`) back to the entry (`mbs_ok`). Each
takes the frame (`Fm`: `rsp` = `aR S`, `r12` = the slot, `rbx`, `r14`, `r15` as at the entry) and `I` of the bytes.

- `mbs_ok`: from the entry (the hypotheses `E : Ev …` with `S` = the entry's `rsp`, `g0` = its registers, `I` of
  the bytes after the pushes, `P3`) to the return (`Ev.kr`: `rsp` 8 up, the callee-saved registers as at the
  entry, `rax` = the slot, `I` of the bytes) or a callee's goal.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
open FV7z.Api (KS)
namespace FV7z.Mbs
set_option linter.unusedVariables false

section Runs
variable {prof : Profile} {F : Footprint} {Wl : List Rgn} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {fb S : Addr} {g0 : Gprs} {e₂ : Addr} {code₂ : List Byte} {j₂ : Nat} {I : (Addr → Byte) → Prop}
  {Y : State} {t : Nat} {W : Addr → Byte}

/-- From 37 (back from `MultiByteToUnicodeString2`): the epilogue, the `ret`, to `kr`. -/
theorem from37 (E : Ev prof F Wl L s₀ o gev gP gE fb S g0 e₂ code₂ j₂ I) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = mbs_at.add 37) (hm : Fm S g0 Y.cpu.gpr) (hIW : I W) :
    GoG prof L o gev gP gE Y t := by
  obtain ⟨s1, s2, s3, s4⟩ := E.hI W hIW
  have ms := hm.1
  have e1 : rdq(W, Y.cpu.gpr.rsp) = g0.rbp := by rw [ms]; exact s1
  have e2 : rdq(W, Y.cpu.gpr.rsp + 8) = g0.r12 := by rw [ms, q1]; exact s2
  have e3 : rdq(W, Y.cpu.gpr.rsp + 8 + 8) = g0.r13 := by rw [ms, q2]; exact s3
  refine (c_37 prof fb).run E.c E.hfs E.hin (fun j' g' _ V' => j' = 45 ∧ V' = W ∧
      g'.rsp = Y.cpu.gpr.rsp + 8 + 8 + 8 ∧ g'.rax = Y.cpu.gpr.r12 ∧ g'.rbp = rdq(W, Y.cpu.gpr.rsp) ∧
      g'.r12 = rdq(W, Y.cpu.gpr.rsp + 8) ∧ g'.r13 = rdq(W, Y.cpu.gpr.rsp + 8 + 8) ∧ g'.rbx = Y.cpu.gpr.rbx ∧
      g'.r14 = Y.cpu.gpr.r14 ∧ g'.r15 = Y.cpu.gpr.r15)
    hK hA hr
    (vc_37 (by rw [ms]; exact E.fb24) (by rw [ms, q1]; exact E.fb16) (by rw [ms, q2]; exact E.fb8)
      fun _ a b c d e m n p _ => ⟨rfl, rfl, a, b, c, d, e, m, n, p⟩) ?_
  rintro j' g fl V₁ ⟨rfl, hV₁, gs, ga, gp, g12, g13, gb, g14, g15⟩ U t₁ hKU hAU hrU hgU -
  subst V₁ hgU
  have hsU : U.cpu.gpr.rsp = S := by rw [gs, ms]; exact q3 S
  refine E.c.s_ret hKU hAU E.hin (lt_len (by decide)) hrU (ret_45 _) (by rw [hsU]; exact E.hl) E.hin₂ E.h₂
    (by rw [hsU]; exact s4) ?_
  rintro Z' t₂ hKZ' hAZ' ⟨hrZ', hgZ'⟩
  refine E.kr W Z' t₂ hKZ' hAZ' hrZ' ?_ ?_ ?_ hIW
  · rw [hgZ']
    show U.cpu.gpr.rsp + 8 = _
    rw [hsU]
  · rw [hgZ']
    exact ⟨gb.trans hm.2.1, gp.trans e1, g12.trans e2, g13.trans e3, g14.trans hm.2.2.2.1, g15.trans hm.2.2.2.2⟩
  · rw [hgZ']
    exact ga.trans hm.2.2.1

/-- From 23 (back from `UString::UString ()`): `MultiByteToUnicodeString2` (32), to 37. -/
theorem from23 (E : Ev prof F Wl L s₀ o gev gP gE fb S g0 e₂ code₂ j₂ I) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = mbs_at.add 23) (hm : Fm S g0 Y.cpu.gpr) (hIW : I W) :
    GoG prof L o gev gP gE Y t := by
  refine (c_23 prof fb).run E.c E.hfs E.hin (fun j' g' _ V' => j' = 32 ∧ V' = W ∧ Fr Y.cpu.gpr g') hK hA hr
    (vc_23 fun _ a _ => ⟨rfl, rfl, a⟩) ?_
  rintro j' g fl V₁ ⟨rfl, hV₁, gf⟩ U t₁ hKU hAU hrU hgU -
  subst V₁ hgU
  have hmU := Fm.fr hm gf
  refine callK E hKU hAU hrU hmU.1 (lt_len (by decide)) (call_32 _) tgt_32 E.cM (E.kM _ _ hIW)
    trivial ?_
  intro Z W' t₃ hKZ hAZ hrZ hsZ hkZ hBZ hIZ
  exact from37 E hKZ hAZ hrZ (fm_ret hmU hsZ hkZ) hIZ

end Runs

section Main
variable {prof : Profile} {F : Footprint} {Wl : List Rgn} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {fb : Addr} {e₂ : Addr} {code₂ : List Byte} {j₂ : Nat} {I : (Addr → Byte) → Prop}
  {X : State} {t : Nat} {V : Addr → Byte}

/-- `MultiByteToUnicodeString (src, codePage)` from its entry (`X`'s registers, `S` = their `rsp`; the pushes'
slots in what the run may store into, `I` of the bytes after the pushes). -/
theorem mbs_ok (E : Ev prof F Wl L s₀ o gev gP gE fb X.cpu.gpr.rsp X.cpu.gpr e₂ code₂ j₂ I)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = mbs_at)
    (hs1 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8) i))
    (hs2 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8 - 8) i))
    (hs3 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8 - 8 - 8) i)) (hI0 : I (P3 V X.cpu.gpr)) :
    GoG prof L o gev gP gE X t := by
  refine (c_0 prof fb).run E.c E.hfs E.hin (fun j' g' _ V' => j' = 18 ∧ V' = P3 V X.cpu.gpr ∧
      Fm X.cpu.gpr.rsp X.cpu.gpr g') hK hA (by rw [addr_add_zero]; exact hrip)
    (vc_0 hs1 hs2 hs3 fun _ a b c d e _ => ⟨rfl, rfl, a, b, c, d, e⟩) ?_
  rintro j' g fl V₁ ⟨rfl, hV₁, hmY⟩ Y t₁ hKY hAY hrY hgY -
  subst V₁ hgY
  refine callK E hKY hAY hrY hmY.1 (lt_len (by decide)) (call_18 _) tgt_18 E.cU (E.kU _ _ hI0) trivial ?_
  intro Z W' t₃ hKZ hAZ hrZ hsZ hkZ hBZ hIZ
  exact from23 E hKZ hAZ hrZ (fm_ret hmY hsZ hkZ) hIZ

end Main

end FV7z.Mbs
