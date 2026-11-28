import FV7z.Oun.Pieces
/-!
# `CStdOutStream::operator<< (unsigned)` (0x5a1a00): from the entry to the return (PLAN.md §M, M1)

`CStdOutStream::operator<< (number)`: `rdi` = `this`, `rsi` = `number`. One theorem for each hop: `fromN` runs the
piece at `N` (and the `call` that ends it, `callK`, with the callee as `Ev`'s continuation) and goes on by `fromM`,
from the guard's check and the `ret` (`from55`) back to the entry (`oun_ok`). Each takes the frame (`Fm`: `rsp` =
`aR S`, `r12` = `this`, `rbx`, `r13`..`r15` as at the entry) and `I` of the bytes.

- `oun_ok`: from the entry (the hypotheses `E : Ev …` with `S` = the entry's `rsp`, `g0` = its registers, `I` of
  the bytes after the prologue, `V0`) to the return (`Ev.kr`: `rsp` 8 up, the callee-saved registers as at the
  entry, `rax` = `this`, `I` of the bytes) or a callee's goal.

Not covered: the stack guard failing (`__stack_chk_fail`, 82), the landing pad after the code (from 87).
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
open FV7z.Olg (P2 Fr)
open FV7z.Api (KS)
namespace FV7z.Oun
set_option linter.unusedVariables false

section Runs
variable {prof : Profile} {F : Footprint} {Wl : List Rgn} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {fb S : Addr} {g0 : Gprs} {e₂ : Addr} {code₂ : List Byte} {j₂ : Nat} {I : (Addr → Byte) → Prop}
  {Y : State} {t : Nat} {W : Addr → Byte}

/-- From 55: the guard's check, the epilogue, the `ret`, to `kr`. -/
theorem from55 (E : Ev prof F Wl L s₀ o gev gP gE fb S g0 e₂ code₂ j₂ I) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = oun_at.add 55) (hm : Fm S g0 Y.cpu.gpr) (hIW : I W) :
    GoG prof L o gev gP gE Y t := by
  obtain ⟨s1, s2, s3, s4⟩ := E.hI W hIW
  have ms := hm.1
  have e1 : rdq(W, Y.cpu.gpr.rsp + 40#64) = g0.rbp := by rw [ms, q1]; exact s1
  have e2 : rdq(W, Y.cpu.gpr.rsp + 40#64 + 8) = g0.r12 := by rw [ms, q2]; exact s2
  refine (c_55 prof fb).run E.c E.hfs E.hin (fun j' g' _ V' => j' = 81 ∧ V' = W ∧
      g'.rsp = Y.cpu.gpr.rsp + 40#64 + 8 + 8 ∧ g'.rax = Y.cpu.gpr.r12 ∧
      g'.rbp = rdq(W, Y.cpu.gpr.rsp + 40#64) ∧ g'.r12 = rdq(W, Y.cpu.gpr.rsp + 40#64 + 8) ∧
      g'.rbx = Y.cpu.gpr.rbx ∧ g'.r13 = Y.cpu.gpr.r13 ∧ g'.r14 = Y.cpu.gpr.r14 ∧ g'.r15 = Y.cpu.gpr.r15)
    hK hA hr
    (vc_55 (by rw [ms]; exact s4) (by rw [ms]; exact E.fg) E.hcl (by rw [ms, q1]; exact E.fb16)
      (by rw [ms, q2]; exact E.fb8) fun _ a b c d e m n p _ => ⟨rfl, rfl, a, b, c, d, e, m, n, p⟩) ?_
  rintro j' g fl V₁ ⟨rfl, hV₁, gs, ga, gp, g12, gb, g13, g14, g15⟩ U t₁ hKU hAU hrU hgU -
  subst V₁ hgU
  have hsU : U.cpu.gpr.rsp = S := by rw [gs, ms]; exact q3 S
  refine E.c.s_ret hKU hAU E.hin (lt_len (by decide)) hrU (ret_81 _) (by rw [hsU]; exact E.hl) E.hin₂ E.h₂
    (by rw [hsU]; exact s3) ?_
  rintro Z' t₂ hKZ' hAZ' ⟨hrZ', hgZ'⟩
  refine E.kr W Z' t₂ hKZ' hAZ' hrZ' ?_ ?_ ?_ hIW
  · rw [hgZ']
    show U.cpu.gpr.rsp + 8 = _
    rw [hsU]
  · rw [hgZ']
    exact ⟨gb.trans hm.2.1, gp.trans e1, g12.trans e2, g13.trans hm.2.2.2.1, g14.trans hm.2.2.2.2.1,
      g15.trans hm.2.2.2.2.2⟩
  · rw [hgZ']
    exact ga.trans hm.2.2.1

/-- From 43 (back from `ConvertUInt32ToString`): `fputs (s, _stream)` (50), to 55. -/
theorem from43 (E : Ev prof F Wl L s₀ o gev gP gE fb S g0 e₂ code₂ j₂ I) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = oun_at.add 43) (hm : Fm S g0 Y.cpu.gpr) (hIW : I W) :
    GoG prof L o gev gP gE Y t := by
  refine (c_43 prof fb).run E.c E.hfs E.hin (fun j' g' _ V' => j' = 50 ∧ V' = W ∧ Fr Y.cpu.gpr g') hK hA hr
    (vc_43 (by rw [hm.2.2.1]; exact E.fth) fun _ a _ => ⟨rfl, rfl, a⟩) ?_
  rintro j' g fl V₁ ⟨rfl, hV₁, gf⟩ U t₁ hKU hAU hrU hgU -
  subst V₁ hgU
  have hmU := Fm.fr hm gf
  refine callK E hKU hAU hrU hmU.1 (lt_len (by decide)) (call_50 _) tgt_50 E.cP (E.kP _ _ hIW)
    trivial ?_
  intro Z W' t₃ hKZ hAZ hrZ hsZ hkZ hBZ hIZ
  exact from55 E hKZ hAZ hrZ (fm_ret hmU hsZ hkZ) hIZ

end Runs

section Main
variable {prof : Profile} {F : Footprint} {Wl : List Rgn} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {fb : Addr} {e₂ : Addr} {code₂ : List Byte} {j₂ : Nat} {I : (Addr → Byte) → Prop}
  {X : State} {t : Nat} {V : Addr → Byte}

/-- `CStdOutStream::operator<< (this, number)` from its entry (`X`'s registers, `S` = their `rsp`, `fb` the `fs`
base; the pushes' slots and the guard's slot in what the run may store into, `I` of the bytes after the
prologue). -/
theorem oun_ok (E : Ev prof F Wl L s₀ o gev gP gE fb X.cpu.gpr.rsp X.cpu.gpr e₂ code₂ j₂ I)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = oun_at)
    (hs1 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8) i))
    (hs2 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8 - 8) i))
    (hw : ∀ i < 8, Foot Wl (Addr.add (aR X.cpu.gpr.rsp + 24#64) i)) (hI0 : I (V0 fb V X.cpu.gpr)) :
    GoG prof L o gev gP gE X t := by
  refine (c_0 prof fb).run E.c E.hfs E.hin (fun j' g' _ V' => j' = 38 ∧ V' = V0 fb V X.cpu.gpr ∧
      Fm X.cpu.gpr.rsp X.cpu.gpr g') hK hA (by rw [addr_add_zero]; exact hrip)
    (vc_0 rfl hs1 hs2 E.hcl hw fun _ a b c d e m _ => ⟨rfl, rfl, a, b, c, d, e, m⟩) ?_
  rintro j' g fl V₁ ⟨rfl, hV₁, hmY⟩ Y t₁ hKY hAY hrY hgY -
  subst V₁ hgY
  refine callK E hKY hAY hrY hmY.1 (lt_len (by decide)) (call_38 _) tgt_38 E.cC (E.kC _ _ hI0) trivial ?_
  intro Z W' t₃ hKZ hAZ hrZ hsZ hkZ hBZ hIZ
  exact from43 E hKZ hAZ hrZ (fm_ret hmY hsZ hkZ) hIZ

end Main

end FV7z.Oun
