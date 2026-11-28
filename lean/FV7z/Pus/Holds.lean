import FV7z.Pus.Pieces
/-!
# `CStdOutStream::PrintUString` (0x5a14f0): from the entry to the return (PLAN.md §M, M1)

`CStdOutStream::PrintUString (s, temp)`: `rdi` = `this`, `rsi` = `s`, `rdx` = `temp`. One theorem for each hop:
`fromN` runs the piece at `N` (and the `call` that ends it, `callK`, with the callee as `Ev`'s continuation) and goes
on by `fromM`, from the epilogue and the `ret` (`from33`) back to the entry (`pus_ok`). Each takes the frame (`Fm`:
`rsp` = `aR S`, `rbx` = `temp`, `rbp` = `this`, `r12`..`r15` as at the entry) and `I` of the bytes.

- `pus_ok`: from the entry (the hypotheses `E : Ev …` with `S` = the entry's `rsp`, `g0` = its registers, `I` of
  the bytes after the pushes, `V0`) to the return (`Ev.kr`: `rsp` 8 up, the callee-saved registers as at the entry,
  `I` of the bytes) or a callee's goal.

Not covered: the landing pad after the code (from 40).
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
open FV7z.Api (KS)
namespace FV7z.Pus
set_option linter.unusedVariables false

section Runs
variable {prof : Profile} {F : Footprint} {Wl : List Rgn} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {S : Addr} {g0 : Gprs} {e₂ : Addr} {code₂ : List Byte} {j₂ : Nat} {I : (Addr → Byte) → Prop}
  {Y : State} {t : Nat} {W : Addr → Byte}

/-- From 33 (back from `fputs`): the epilogue, the `ret`, to `kr`. -/
theorem from33 (E : Ev prof F Wl L s₀ o gev gP gE S g0 e₂ code₂ j₂ I) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = pus_at.add 33) (hm : Fm S g0 Y.cpu.gpr) (hIW : I W) :
    GoG prof L o gev gP gE Y t := by
  obtain ⟨s1, s2, s3⟩ := E.hI W hIW
  have ms := hm.1
  have e1 : rdq(W, Y.cpu.gpr.rsp + 8#64) = g0.rbx := by rw [ms, q1]; exact s1
  have e2 : rdq(W, Y.cpu.gpr.rsp + 8#64 + 8) = g0.rbp := by rw [ms, q2]; exact s2
  refine (c_33 prof).run E.c E.hin (fun j' g' _ V' => j' = 39 ∧ V' = W ∧
      g'.rsp = Y.cpu.gpr.rsp + 8#64 + 8 + 8 ∧ g'.rbx = rdq(W, Y.cpu.gpr.rsp + 8#64) ∧
      g'.rbp = rdq(W, Y.cpu.gpr.rsp + 8#64 + 8) ∧ g'.r12 = Y.cpu.gpr.r12 ∧ g'.r13 = Y.cpu.gpr.r13 ∧
      g'.r14 = Y.cpu.gpr.r14 ∧ g'.r15 = Y.cpu.gpr.r15)
    hK hA hr
    (vc_33 (by rw [ms, q1]; exact E.fb16) (by rw [ms, q2]; exact E.fb8)
      fun _ a b c d e m n _ => ⟨rfl, rfl, a, b, c, d, e, m, n⟩) ?_
  rintro j' g fl V₁ ⟨rfl, hV₁, gs, gb, gp, g12, g13, g14, g15⟩ U t₁ hKU hAU hrU hgU -
  subst V₁ hgU
  have hsU : U.cpu.gpr.rsp = S := by rw [gs, ms]; exact q3 S
  refine E.c.s_ret hKU hAU E.hin (lt_len (by decide)) hrU (ret_39 _) (by rw [hsU]; exact E.hl) E.hin₂ E.h₂
    (by rw [hsU]; exact s3) ?_
  rintro Z' t₂ hKZ' hAZ' ⟨hrZ', hgZ'⟩
  refine E.kr W Z' t₂ hKZ' hAZ' hrZ' ?_ ?_ hIW
  · rw [hgZ']
    show U.cpu.gpr.rsp + 8 = _
    rw [hsU]
  · rw [hgZ']
    exact ⟨gb.trans e1, gp.trans e2, g12.trans hm.2.2.2.1, g13.trans hm.2.2.2.2.1, g14.trans hm.2.2.2.2.2.1,
      g15.trans hm.2.2.2.2.2.2⟩

/-- From 21 (back from `Convert_UString_to_AString`): `fputs (temp._chars, _stream)` (28), to 33. -/
theorem from21 (E : Ev prof F Wl L s₀ o gev gP gE S g0 e₂ code₂ j₂ I) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = pus_at.add 21) (hm : Fm S g0 Y.cpu.gpr) (hIW : I W) :
    GoG prof L o gev gP gE Y t := by
  refine (c_21 prof).run E.c E.hin (fun j' g' _ V' => j' = 28 ∧ V' = W ∧ Fr Y.cpu.gpr g') hK hA hr
    (vc_21 (by rw [hm.2.2.1]; exact E.fth) (by rw [hm.2.1]; exact E.ftm) fun _ a _ => ⟨rfl, rfl, a⟩) ?_
  rintro j' g fl V₁ ⟨rfl, hV₁, gf⟩ U t₁ hKU hAU hrU hgU -
  subst V₁ hgU
  have hmU := Fm.fr hm gf
  refine callK E hKU hAU hrU hmU.1 (lt_len (by decide)) (call_28 _) tgt_28 E.cP (E.kP _ _ hIW)
    trivial ?_
  intro Z W' t₃ hKZ hAZ hrZ hsZ hkZ hBZ hIZ
  exact from33 E hKZ hAZ hrZ (fm_ret hmU hsZ hkZ) hIZ

end Runs

section Main
variable {prof : Profile} {F : Footprint} {Wl : List Rgn} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {e₂ : Addr} {code₂ : List Byte} {j₂ : Nat} {I : (Addr → Byte) → Prop}
  {X : State} {t : Nat} {V : Addr → Byte}

/-- `CStdOutStream::PrintUString (this, s, temp)` from its entry (`X`'s registers, `S` = their `rsp`; the pushes'
slots in what the run may store into, `I` of the bytes after the pushes). -/
theorem pus_ok (E : Ev prof F Wl L s₀ o gev gP gE X.cpu.gpr.rsp X.cpu.gpr e₂ code₂ j₂ I)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = pus_at)
    (hs1 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8) i))
    (hs2 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8 - 8) i)) (hI0 : I (V0 V X.cpu.gpr)) :
    GoG prof L o gev gP gE X t := by
  refine (c_0 prof).run E.c E.hin (fun j' g' _ V' => j' = 16 ∧ V' = V0 V X.cpu.gpr ∧
      Fm X.cpu.gpr.rsp X.cpu.gpr g') hK hA (by rw [addr_add_zero]; exact hrip)
    (vc_0 hs1 hs2 fun _ a b c d e m n _ => ⟨rfl, rfl, a, b, c, d, e, m, n⟩) ?_
  rintro j' g fl V₁ ⟨rfl, hV₁, hmY⟩ Y t₁ hKY hAY hrY hgY -
  subst V₁ hgY
  refine callK E hKY hAY hrY hmY.1 (lt_len (by decide)) (call_16 _) tgt_16 E.cC (E.kC _ _ hI0) trivial ?_
  intro Z W' t₃ hKZ hAZ hrZ hsZ hkZ hBZ hIZ
  exact from21 E hKZ hAZ hrZ (fm_ret hmY hsZ hkZ) hIZ

end Main

end FV7z.Pus
