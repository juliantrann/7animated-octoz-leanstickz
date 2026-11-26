import FV7z.Strrchr.Cross
import FV7z.Startup.StrAt
/-!
# `__strrchr_sse2` meets `Str.RchrAt` (PLAN.md M, the PLT contracts)

`run`: from the first byte, `entry` with `path560` near a page's end and `path112` (to `from256`) else.
`rchrAt_sse2`: wherever the code of `__strrchr_sse2` (`Strrchr/Code.lean`) is in the list, a call there does what
`Str.RchrAt` says, for any `Pm`. The PLT stub jumping through the GOT to it is a separate step.
-/
namespace FV7z.Strrchr
open ZellicX86 Decode FV7z.Leaf FV7z.Fn FV7z.Strlen

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle} {F : Footprint} {Wl : List Rgn}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {e' : Addr} {V : Addr → Byte}

/-- `__strrchr_sse2` from its first byte, called with registers `g₀` (`rdi = p`, `rsi` the character), returns to
`RetR` with `rax` as `ROk` says. -/
theorem run (c : Seg prof F Wl L s₀ o) (hin : CodeIn L e' sr2) {X : State} {t : Nat} {g₀ : Gprs} {n : Nat}
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = e'.add 0) (hkp : KpR g₀ X.cpu.gpr)
    (hdi : X.cpu.gpr.rdi = g₀.rdi) (hsi : X.cpu.gpr.rsi = g₀.rsi) (hov : g₀.rdi.toNat + n < 2 ^ 64)
    (hnz : ∀ k < n, V (Addr.add g₀.rdi k) ≠ 0) (hz : V (Addr.add g₀.rdi n) = 0) (hch : g₀.rsi.setWidth 8 ≠ 0#8)
    (hft : ∀ x : Addr, g₀.rdi.toNat / 4096 ≤ x.toNat / 4096 → x.toNat / 4096 ≤ (g₀.rdi.toNat + n) / 4096 →
      Foot F.data x)
    (hR : RetR prof F Wl L s₀ o gev gP gE V g₀ n) : GoG prof L o gev gP gE X t :=
  entry c hin hK hA hrip hkp hdi hsi hnz hz hch hft (path560 c hin hov hnz hz hch hft hR)
    (fun _ _ hK₁ hA₁ hr₁ hkp₁ hdi₁ hcx₁ hx1₁ hx2₁ h16 hq =>
      path112 c hin hK₁ hA₁ hr₁ hkp₁ hdi₁ hcx₁ hx1₁ hx2₁ h16 hq hnz hz hch hft
        (from256 c hin hov hnz hz hch hft hR) hR) hR

theorem rchrAt_sse2 {prof : Profile} {L : List (Addr × List Byte)} {o : Oracle} {e : Addr}
    {Pm : (Addr → Byte) → Prop} (hin : CodeIn L e sr2) : Str.RchrAt prof L o e Pm := by
  intro F Wl s₀ gev gP gE X t V e' code j n c _ hK hA hrip _ hin₂ hj hra hl hov hnz hz hch hft K
  exact run (g₀ := X.cpu.gpr) c hin hK hA (by rw [hrip, addr_add_zero])
    (by unfold KpR; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩) rfl rfl hov hnz hz hch hft
    (by
      unfold RetR
      exact ⟨hl, e', code, j, hin₂, hj, hra, fun Z t' hK₁ hA₁ hr₁ hsp hok hb hp h12 h13 h14 h15 =>
        K Z t' hK₁ hA₁ hr₁ hsp hok.1 hok.2 hb hp h12 h13 h14 h15⟩)

end FV7z.Strrchr
