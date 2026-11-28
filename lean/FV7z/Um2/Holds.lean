import FV7z.Um2.Pieces
/-!
# `UnicodeStringToMultiByte2` (0x450d20): from the entry to the return (PLAN.md §M, M1)

`UnicodeStringToMultiByte2 (dest, src, codePage)`: the prologue and the `call` of `UnicodeStringToMultiByte`, its
return as `Ev`'s continuation (`kU`), then the guard's check and the `ret` (`from39`).

- `um2_ok`: from the entry (the hypotheses `E : Ev …` with `S` = the entry's `rsp`, `g0` = its registers, `I` of
  the bytes after the prologue, `V0`) to the return (`Ev.kr`: `rsp` 8 up, the callee-saved registers as at the
  entry, `I` of the bytes) or the callee's goal.

Not covered: the stack guard failing (`__stack_chk_fail`, 60).
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
open FV7z.Api (KS)
namespace FV7z.Um2
set_option linter.unusedVariables false

section Runs
variable {prof : Profile} {F : Footprint} {Wl : List Rgn} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {fb S : Addr} {g0 : Gprs} {e₂ : Addr} {code₂ : List Byte} {j₂ : Nat} {I : (Addr → Byte) → Prop}
  {Y : State} {t : Nat} {W : Addr → Byte}

/-- From 39 (back from `UnicodeStringToMultiByte`): the guard's check, the epilogue, the `ret`, to `kr`. -/
theorem from39 (E : Ev prof F Wl L s₀ o gev gP gE fb S g0 e₂ code₂ j₂ I) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = um2_at.add 39) (hm : Fm S g0 Y.cpu.gpr) (hIW : I W) :
    GoG prof L o gev gP gE Y t := by
  obtain ⟨s1, s2⟩ := E.hI W hIW
  have ms := hm.1
  refine (c_39 prof fb).run E.c E.hfs E.hin (fun j' g' _ V' => j' = 59 ∧ V' = W ∧
      g'.rsp = Y.cpu.gpr.rsp + 24#64 ∧ KS Y.cpu.gpr g') hK hA hr
    (vc_39 (by rw [ms]; exact s2) (by rw [ms]; exact E.fg) E.hcl fun _ a k _ => ⟨rfl, rfl, a, k⟩) ?_
  rintro j' g fl V₁ ⟨rfl, hV₁, gs, gk⟩ U t₁ hKU hAU hrU hgU -
  subst V₁ hgU
  have hsU : U.cpu.gpr.rsp = S := by rw [gs, ms]; exact q1 S
  refine E.c.s_ret hKU hAU E.hin (lt_len (by decide)) hrU (ret_59 _) (by rw [hsU]; exact E.hl) E.hin₂ E.h₂
    (by rw [hsU]; exact s1) ?_
  rintro Z' t₂ hKZ' hAZ' ⟨hrZ', hgZ'⟩
  refine E.kr W Z' t₂ hKZ' hAZ' hrZ' ?_ ?_ hIW
  · rw [hgZ']
    show U.cpu.gpr.rsp + 8 = _
    rw [hsU]
  · rw [hgZ']
    exact ⟨gk.1.trans hm.2.1, gk.2.1.trans hm.2.2.1, gk.2.2.1.trans hm.2.2.2.1, gk.2.2.2.1.trans hm.2.2.2.2.1,
      gk.2.2.2.2.1.trans hm.2.2.2.2.2.1, gk.2.2.2.2.2.trans hm.2.2.2.2.2.2⟩

end Runs

section Main
variable {prof : Profile} {F : Footprint} {Wl : List Rgn} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {fb : Addr} {e₂ : Addr} {code₂ : List Byte} {j₂ : Nat} {I : (Addr → Byte) → Prop}
  {X : State} {t : Nat} {V : Addr → Byte}

/-- `UnicodeStringToMultiByte2 (dest, src, codePage)` from its entry (`X`'s registers, `S` = their `rsp`, `fb` the
`fs` base; the guard's slot in what the run may store into, `I` of the bytes after the prologue). -/
theorem um2_ok (E : Ev prof F Wl L s₀ o gev gP gE fb X.cpu.gpr.rsp X.cpu.gpr e₂ code₂ j₂ I)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = um2_at)
    (hw : ∀ i < 8, Foot Wl (Addr.add (aR X.cpu.gpr.rsp + 8#64) i)) (hI0 : I (V0 fb V X.cpu.gpr)) :
    GoG prof L o gev gP gE X t := by
  refine (c_0 prof fb).run E.c E.hfs E.hin (fun j' g' _ V' => j' = 34 ∧ V' = V0 fb V X.cpu.gpr ∧
      Fm X.cpu.gpr.rsp X.cpu.gpr g') hK hA (by rw [addr_add_zero]; exact hrip)
    (vc_0 rfl E.hcl hw fun _ a k _ => ⟨rfl, rfl, a, k⟩) ?_
  rintro j' g fl V₁ ⟨rfl, hV₁, hmY⟩ Y t₁ hKY hAY hrY hgY -
  subst V₁ hgY
  obtain ⟨cc, hinc, hcc⟩ := E.cU
  have hU : Y.cpu.gpr.rsp - 8 = aR X.cpu.gpr.rsp - 8 := by rw [hmY.1]
  refine E.c.s_call hKY hAY E.hin (lt_len (by decide)) hrY (call_34 _) hinc hcc tgt_34 (by rw [hU]; exact E.hr8) ?_
  rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
  rw [hU] at hA₂
  refine E.kU _ _ hI0 Y₂ t₂ hK₂ hA₂ hr₂ (by rw [hg₂]; exact hU) trivial ?_
  intro Z W' t₃ hKZ hAZ hrZ hsZ hkZ hBZ hIZ
  rw [hg₂] at hkZ
  exact from39 E hKZ hAZ hrZ (fm_ret hmY hsZ hkZ) hIZ

end Main

end FV7z.Um2
