import FV7z.Fsv.Pieces
/-!
# `fs2us (const char *)`, the twin (0x44e600): from the entry to the return (PLAN.md §M, M1)

`fs2us (s)`: `rdi` = the result's `UString` slot, `rsi` = `s`. `from36` runs the guard's check and the `ret` to
`Ev.kr`; `fsv_ok` runs the prologue and the `call` of the conversion at `0x450c60` (`callK`, with the callee as
`Ev`'s continuation) and goes on by `from36`. Each takes the frame (`Fm`: `rsp` = `aR S`, `r12` = the slot, the
other callee-saved registers as at the entry) and `I` of the bytes.

- `fsv_ok`: from the entry (the hypotheses `E : Ev …` with `S` = the entry's `rsp`, `g0` = its registers, `I` of
  the bytes after the prologue, `V0`) to the return (`Ev.kr`: `rsp` 8 up, the callee-saved registers as at the
  entry, `rax` = the slot, `I` of the bytes) or the callee's goal.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
open FV7z.Api (KS)
namespace FV7z.Fsv
set_option linter.unusedVariables false

section Runs
variable {prof : Profile} {F : Footprint} {Wl : List Rgn} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {fb S : Addr} {g0 : Gprs} {e₂ : Addr} {code₂ : List Byte} {j₂ : Nat} {I : (Addr → Byte) → Prop}
  {Y : State} {t : Nat} {W : Addr → Byte}

/-- From 36 (back from the conversion): the guard's check, the epilogue, the `ret`, to `kr`. -/
theorem from36 (E : Ev prof F Wl L s₀ o gev gP gE fb S g0 e₂ code₂ j₂ I) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = fsv_at.add 36) (hm : Fm S g0 Y.cpu.gpr) (hIW : I W) :
    GoG prof L o gev gP gE Y t := by
  obtain ⟨s1, s2, s3⟩ := E.hI W hIW
  have ms := hm.1
  have e1 : rdq(W, Y.cpu.gpr.rsp + 16#64) = g0.r12 := by rw [ms, q1]; exact s1
  refine (c_36 prof fb).run E.c E.hfs E.hin (fun j' g' _ V' => j' = 61 ∧ V' = W ∧
      g'.rsp = Y.cpu.gpr.rsp + 16#64 + 8 ∧ g'.rax = Y.cpu.gpr.r12 ∧ g'.r12 = rdq(W, Y.cpu.gpr.rsp + 16#64) ∧
      g'.rbx = Y.cpu.gpr.rbx ∧ g'.rbp = Y.cpu.gpr.rbp ∧ g'.r13 = Y.cpu.gpr.r13 ∧ g'.r14 = Y.cpu.gpr.r14 ∧
      g'.r15 = Y.cpu.gpr.r15)
    hK hA hr
    (vc_36 (by rw [ms]; exact s3) (by rw [ms]; exact E.fg) E.hcl (by rw [ms, q1]; exact E.fb8)
      fun _ a b c d e m n p _ => ⟨rfl, rfl, a, b, c, d, e, m, n, p⟩) ?_
  rintro j' g fl V₁ ⟨rfl, hV₁, gs, ga, g12, gb, gp, g13, g14, g15⟩ U t₁ hKU hAU hrU hgU -
  subst V₁ hgU
  have hsU : U.cpu.gpr.rsp = S := by rw [gs, ms]; exact q2 S
  refine E.c.s_ret hKU hAU E.hin (lt_len (by decide)) hrU (ret_61 _) (by rw [hsU]; exact E.hl) E.hin₂ E.h₂
    (by rw [hsU]; exact s2) ?_
  rintro Z' t₂ hKZ' hAZ' ⟨hrZ', hgZ'⟩
  refine E.kr W Z' t₂ hKZ' hAZ' hrZ' ?_ ?_ ?_ hIW
  · rw [hgZ']
    show U.cpu.gpr.rsp + 8 = _
    rw [hsU]
  · rw [hgZ']
    exact ⟨gb.trans hm.2.1, gp.trans hm.2.2.1, g12.trans e1, g13.trans hm.2.2.2.2.1, g14.trans hm.2.2.2.2.2.1,
      g15.trans hm.2.2.2.2.2.2⟩
  · rw [hgZ']
    exact ga.trans hm.2.2.2.1

end Runs

section Main
variable {prof : Profile} {F : Footprint} {Wl : List Rgn} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {fb : Addr} {e₂ : Addr} {code₂ : List Byte} {j₂ : Nat} {I : (Addr → Byte) → Prop}
  {X : State} {t : Nat} {V : Addr → Byte}

/-- `fs2us (s)` from its entry (`X`'s registers, `S` = their `rsp`, `fb` the `fs` base; the push's slot and the
guard's slot in what the run may store into, `I` of the bytes after the prologue). -/
theorem fsv_ok (E : Ev prof F Wl L s₀ o gev gP gE fb X.cpu.gpr.rsp X.cpu.gpr e₂ code₂ j₂ I)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = fsv_at)
    (hs1 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8) i))
    (hw : ∀ i < 8, Foot Wl (Addr.add (aR X.cpu.gpr.rsp + 8#64) i)) (hI0 : I (V0 fb V X.cpu.gpr)) :
    GoG prof L o gev gP gE X t := by
  refine (c_0 prof fb).run E.c E.hfs E.hin (fun j' g' _ V' => j' = 31 ∧ V' = V0 fb V X.cpu.gpr ∧
      Fm X.cpu.gpr.rsp X.cpu.gpr g') hK hA (by rw [addr_add_zero]; exact hrip)
    (vc_0 rfl hs1 E.hcl hw fun _ a b c d e m n _ => ⟨rfl, rfl, a, b, c, d, e, m, n⟩) ?_
  rintro j' g fl V₁ ⟨rfl, hV₁, hmY⟩ Y t₁ hKY hAY hrY hgY -
  subst V₁ hgY
  refine callK E hKY hAY hrY hmY.1 (lt_len (by decide)) (call_31 _) tgt_31 E.cM (E.kM _ _ hI0) trivial ?_
  intro Z W' t₃ hKZ hAZ hrZ hsZ hkZ hBZ hIZ
  exact from36 E hKZ hAZ hrZ (fm_ret hmY hsZ hkZ) hIZ

end Main

end FV7z.Fsv
