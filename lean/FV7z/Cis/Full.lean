import FV7z.Cis.Holds
import FV7z.C64.Holds

/-!
# `ConvertInt64ToString` to its return address

`cis_ok` (the entry to the tail jump) followed by `C64.c64_ok` (`ConvertUInt64ToString` to the return address): the
registers at `C64`'s entry are `gC` of those at the entry (`rdi` negated and `rsi` one up for a negative value, the
rest as they were), the bytes `VC` (the `'-'` at `rsi` for a negative value). `C64`'s hypotheses (`Hy`, the return
address) are stated of `gC` and `VC`; the stack pointer and the kept registers are those at the entry (`gC_rsp`,
`gC_kp`).
-/

open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn

namespace FV7z.Cis

theorem gC_rsp (g : Gprs) : (gC g).rsp = g.rsp := by
  unfold gC; split <;> rfl

theorem gC_kp {a g : Gprs} (h : U2s.Kp a (gC g)) : U2s.Kp a g := by
  unfold gC at h; split at h <;> exact h

variable {F : Footprint} {Wl : List Rgn} {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State}
  {o : Oracle} {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {X : State} {t : Nat} {V : Addr → Byte}

/-- `ConvertInt64ToString (val, s)` from its entry to the return address: `C64.c64_ok`'s ending with `s` = `rsi` of
`gC` (one past the `'-'` for a negative value) and the bytes `VC` before. -/
theorem cis_full {fb : Addr} (c : Seg prof F Wl L s₀ o) (hfs : s₀.cpu.seg.fsBase = fb) (hin : CodeIn L cis_at cis)
    (hinC : CodeIn L C64.c64_at C64.c64) (hinU : CodeIn L U2s.u2s_at U2s.u2s)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = cis_at)
    (ws : X.cpu.gpr.rdi.msb = true → ∀ i < 1, Foot Wl (Addr.add X.cpu.gpr.rsi i))
    (H : C64.Hy F Wl (gC X.cpu.gpr) fb) (hl : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsp i))
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (hra : rdq(VC V X.cpu.gpr, X.cpu.gpr.rsp) = e₂.add j₂)
    (k : ∀ (Z : State) (t' : Nat) (len : Nat) (V' : Addr → Byte), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V' →
      Z.cpu.rip = e₂.add j₂ → Z.cpu.gpr.rsp = X.cpu.gpr.rsp + 8 → U2s.Kp Z.cpu.gpr X.cpu.gpr → 1 ≤ len →
      len ≤ 20 → Z.cpu.gpr.rax = (gC X.cpu.gpr).rsi + BitVec.ofNat 64 len →
      V' ((gC X.cpu.gpr).rsi + BitVec.ofNat 64 len) = 0#8 →
      (∀ a, C64.Out2 X.cpu.gpr.rsp (gC X.cpu.gpr).rsi a → V' a = VC V X.cpu.gpr a) →
      GoG prof L o gev gP gE Z t') :
    GoG prof L o gev gP gE X t := by
  refine cis_ok c hin hinC hK hA hrip ws ?_
  intro Y t₁ hKY hAY hrY hgY
  refine C64.c64_ok c hfs hinC hinU hKY hAY hrY (by rw [hgY]; exact H) (by rw [hgY, gC_rsp]; exact hl) hin₂ h₂
    (by rw [hgY, gC_rsp]; exact hra) ?_
  intro Z t₂ len V' hKZ hAZ hrZ hsZ hpZ h1 h20 hax h0 hout
  rw [hgY] at hsZ hpZ hax h0 hout
  rw [gC_rsp] at hsZ hout
  exact k Z t₂ len V' hKZ hAZ hrZ hsZ (gC_kp hpZ) h1 h20 hax h0 hout

end FV7z.Cis
