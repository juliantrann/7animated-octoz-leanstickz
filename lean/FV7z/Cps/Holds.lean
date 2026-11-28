import FV7z.Cps.Loop
/-!
# `NCommandLineParser::CParser::ParseString` (0x5a0650): from the entry to the return (PLAN.md §M, M1)

`bool CParser::ParseString (const UString &s, const CSwitchForm *switchForms, unsigned numSwitches)`:
`rdi` = `this`, `rsi` = `s`, `rdx` = the forms, `ecx` = `numSwitches`.

- `V12`: the bytes after the six pushes and the stores of `rdi`, `rdx` into the frame.
- `cps_ok`: from the entry (the hypotheses `E : Ev …` with `S` = the entry's `rsp`, `g0` = its registers, the
  six saved registers' and the frame's slots writable, `I` of the bytes after the stack guard's store) to the
  return (`Ev.kr`), the throw (`Ev.kt`) or a callee's goal.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
open FV7z.Api (P6 Stk KS)
namespace FV7z.Cps
set_option linter.unusedVariables false

/-- The bytes after the pieces at 0 and 12 from `g`: `r15`, `r14`, `r13`, `r12`, `rbp`, `rbx` pushed, `rdi` and
`rdx` stored in the frame. -/
abbrev V12 (V : Addr → Byte) (g : Gprs) : Addr → Byte :=
  Vst (Vst (Vst (Vst (P4 V g) (g.rsp - 8 - 8 - 8 - 8 - 8) (toBytesLE g.rbp 8))
    (g.rsp - 8 - 8 - 8 - 8 - 8 - 8) (toBytesLE g.rbx 8)) (aR g.rsp + 24#64) (toBytesLE g.rdi 8))
    (aR g.rsp + 16#64) (toBytesLE g.rdx 8)

section Runs
variable {prof : Profile} {F : Footprint} {Wl : List Rgn} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {fb : Addr} {e₂ : Addr} {code₂ : List Byte} {j₂ : Nat} {I : (Addr → Byte) → Prop}
  {Ok : Addr → Nat → Prop} {ch : Addr} {ln : BitVec 32} {sp : Addr} {kp : Nat → Addr}
  {X : State} {t : Nat} {V : Addr → Byte}

/-- `CParser::ParseString` from its entry. -/
theorem cps_ok (E : Ev prof F Wl L s₀ o gev gP gE fb X.cpu.gpr.rsp X.cpu.gpr e₂ code₂ j₂ I Ok ch ln sp kp)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = cps_at)
    (hs1 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8) i))
    (hs2 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8 - 8) i))
    (hs3 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8 - 8 - 8) i))
    (hs4 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8 - 8 - 8 - 8) i))
    (hs5 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8 - 8 - 8 - 8 - 8) i))
    (hs6 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8 - 8 - 8 - 8 - 8 - 8) i))
    (w24 : ∀ i < 8, Foot Wl (Addr.add (aR X.cpu.gpr.rsp + 24#64) i))
    (w16 : ∀ i < 8, Foot Wl (Addr.add (aR X.cpu.gpr.rsp + 16#64) i))
    (hI0 : I (Vst (V12 V X.cpu.gpr) (aR X.cpu.gpr.rsp + 56#64)
      (toBytesLE rdq(V12 V X.cpu.gpr, fb + 40#64) 8))) :
    GoG prof L o gev gP gE X t := by
  refine (c_0 prof fb).run E.c E.hfs E.hin (fun j' g' _ V' => j' = 12 ∧ V' = P4 V X.cpu.gpr ∧
      g'.rsp = X.cpu.gpr.rsp - 8 - 8 - 8 - 8 ∧ g'.rbp = X.cpu.gpr.rbp ∧ g'.rbx = X.cpu.gpr.rbx ∧
      g'.rdi = X.cpu.gpr.rdi ∧ g'.rsi = X.cpu.gpr.rsi ∧ g'.rdx = X.cpu.gpr.rdx ∧ g'.rcx = X.cpu.gpr.rcx)
    hK hA (by rw [addr_add_zero]; exact hrip)
    (vc_0 hs1 hs2 hs3 hs4 fun _ a1 a2 a3 a4 a5 a6 a7 _ => ⟨rfl, rfl, a1, a2, a3, a4, a5, a6, a7⟩) ?_
  rintro j' g fl V₁ ⟨rfl, hV₁, gs, gbp, gbx, gdi, gsi, gdx, gcx⟩ U t₁ hKU hAU hrU hgU -
  subst V₁ hgU
  refine (c_12 prof fb).run E.c E.hfs E.hin (fun j' g' _ V' => j' = 28 ∧ V' = B12 (P4 V X.cpu.gpr) U.cpu.gpr ∧
      g'.rsp = U.cpu.gpr.rsp - 8 - 8 - 72#64 ∧ g'.rsi = U.cpu.gpr.rsi ∧ g'.rcx = U.cpu.gpr.rcx) hKU hAU hrU
    (vc_12 (by rw [gs]; exact hs5) (by rw [gs]; exact hs6) (by rw [gs]; exact w24) (by rw [gs]; exact w16)
      fun _ a1 a2 a3 _ => ⟨rfl, rfl, a1, a2, a3⟩) ?_
  rintro j' g fl V₂ ⟨rfl, hV₂, zs, zsi, zcx⟩ Z t₂ hKZ hAZ hrZ hgZ -
  subst V₂ hgZ
  have eV : B12 (P4 V X.cpu.gpr) U.cpu.gpr = V12 V X.cpu.gpr := by
    simp only [B12, V12, aR, gs, gbp, gbx, gdi, gdx]
  rw [eV] at hAZ
  have hsZ : Z.cpu.gpr.rsp = aR X.cpu.gpr.rsp := by
    rw [zs, gs]
  exact from28 E hKZ hAZ hrZ hsZ (zsi.trans gsi) (zcx.trans gcx) hI0

end Runs

end FV7z.Cps
