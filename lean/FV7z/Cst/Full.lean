import FV7z.Cst.Holds
import FV7z.Cfn.Holds

/-!
# `CompareStrings` to its return address

`cst_ok` (the entry to the tail jump) followed by `Cfn.cfn_ok` (`CompareFileNames` to the return address, `towupper`
a hypothesis): the registers at `Cfn`'s entry are `gS` of those at the entry (the two strings `s1`, `s2` of
`param`'s table in `rdi`, `rsi`), the bytes as they were. `Cfn`'s hypotheses are stated of `gS V X.cpu.gpr`.
-/

open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn

namespace FV7z.Cst

variable {F : Footprint} {Wl : List Rgn} {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State}
  {o : Oracle} {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {X : State} {t : Nat} {V : Addr → Byte}

/-- `CompareStrings (p1, p2, param)` from its entry to the return address: `Cfn.cfn_ok`'s ending for the strings of
`gS`. -/
theorem cst_full {U : BitVec 32 → BitVec 32} {N : Nat} {Tt : Gprs → (Addr → Byte) → Prop} {tcode : List Byte}
    (c : Seg prof F Wl L s₀ o) (hin : CodeIn L cst_at cst) (hinC : CodeIn L Cfn.cfn_at Cfn.cfn)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = cst_at) (hFt : Ft F V X.cpu.gpr)
    (hF : Cfn.Fr F Wl (gS V X.cpu.gpr).rsp) (hN : Sen.c1 (gS V X.cpu.gpr) V N = 0#32)
    (hw : ∀ k, Cfn.Pre (Cfn.Ci V) U (gS V X.cpu.gpr) V k → ∀ j < 4,
      Foot F.data (Addr.add (Addr.add (gS V X.cpu.gpr).rdi (4 * k)) j) ∧
      Foot F.data (Addr.add (Addr.add (gS V X.cpu.gpr).rsi (4 * k)) j))
    (hd : ∀ k, Cfn.Pre (Cfn.Ci V) U (gS V X.cpu.gpr) V k →
      Sen.Ok (gS V X.cpu.gpr).rsp (Addr.add (gS V X.cpu.gpr).rdi (4 * k)) ∧
      Sen.Ok (gS V X.cpu.gpr).rsp (Addr.add (gS V X.cpu.gpr).rsi (4 * k)))
    (hinT : CodeIn L Sen.tup_at tcode) (hlT : 0 < tcode.length)
    (hT : FnK prof F Wl L s₀ o Sen.tup_at Tt (Sen.Rt U)) (hTt : Cfn.TtOk (gS V X.cpu.gpr) V Tt)
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (hra : rdq(V, (gS V X.cpu.gpr).rsp) = e₂.add j₂)
    (k : ∀ (Z : State) (t' : Nat) (V' : Addr → Byte) (r : BitVec 32), KeptW Wl s₀ Z →
      Agree F Z.proc.mm.mem V' → Z.cpu.rip = e₂.add j₂ →
      (∀ y : Addr, y.toNat < (gS V X.cpu.gpr).rsp.toNat - 48 ∨ (gS V X.cpu.gpr).rsp.toNat ≤ y.toNat →
        V' y = V y) →
      Cfn.Ans (Cfn.Ci V) U (gS V X.cpu.gpr) V r →
      (∃ c d si di, Z.cpu.gpr = { gS V X.cpu.gpr with
                                  rax := BitVec.setWidth 64 r, rcx := c, rdx := d, rsi := si,
                                  rdi := di }.set 4 ((gS V X.cpu.gpr).rsp + 8)) →
      GoG prof L o gev gP gE Z t') :
    GoG prof L o gev gP gE X t := by
  refine cst_ok c hin hinC hK hA hrip hFt ?_
  intro Y t₁ hKY hAY hrY hgY
  rw [← hgY] at hF hN hw hd hTt hra k
  exact Cfn.cfn_ok c hinC hKY hAY hrY hF hN hw hd hinT hlT hT hTt hin₂ h₂ hra k

end FV7z.Cst
