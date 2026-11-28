import FV7z.Upl.Holds
import FV7z.Uc4.Holds
/-!
# `operator+ (s1, s2)` (wide strings) through its constructor (PLAN.md  M, M2)

`upl_ok` leaves the call to the constructor at `Uc4.uc4_at` as a hypothesis (`kf`); here it is discharged by
`Uc4.uc4_ok` at the call's target, with the registers `Ga` and the bytes `Wa` there. The constructor's hypotheses are
those of `Uc4.uc4_ok` at that state (prefixed `u`); its tail jump to `wmemcpy` (`ukr`) also gets the way back to
`upl_at + 31` that `kf` offers.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Upl

/-- The registers at the callee's entry (as in `kf` of `upl_ok`). -/
abbrev Ga (V : Addr → Byte) (g : Gprs) : Gprs := (gC g (V0 V g)).set 4 (g.rsp - 16)

/-- The bytes at the callee's entry: `V0` with the return address `upl_at.add 31` pushed. -/
abbrev Wa (V : Addr → Byte) (g : Gprs) : Addr → Byte := Vst (V0 V g) (g.rsp - 16) (toBytesLE (upl_at.add 31) 8)

variable {F : Footprint} {Wl : List Rgn} {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {X : State} {t : Nat} {V : Addr → Byte}

/-- `operator+ (s1, s2)` (wide strings) from its entry with the constructor by `Uc4.uc4_ok`: the constructor's
hypotheses at `Ga`/`Wa`, its tail jump with the way back into `operator+`, and the return of `operator+` (`kr`). -/
theorem upl_uc4 {Pc : State → (Addr → Byte) → Prop} {Pu : State → (Addr → Byte) → Prop}
    {Pw : State → State → (Addr → Byte) → Prop}
    (c : Seg prof F Wl L s₀ o)
    (hin : CodeIn L upl_at upl)
    (hinC : CodeIn L Uc4.uc4_at Uc4.uc4)
    (hK : KeptW Wl s₀ X)
    (hA : Agree F X.proc.mm.mem V)
    (hrip : X.cpu.rip = upl_at)
    (hp : 16 ≤ X.cpu.gpr.rsp.toNat)
    (hs1 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8) i))
    (hs2 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 16) i))
    (hl : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsp i))
    (f1 : ∀ i < 4, Foot F.data (Addr.add (X.cpu.gpr.rsi + 8#64) i))
    (f2 : ∀ i < 4, Foot F.data (Addr.add (X.cpu.gpr.rdx + 8#64) i))
    (f3 : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rdx i))
    (f4 : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsi i))
    {e₂ : Addr}
    {code₂ : List Byte}
    (hin₂ : CodeIn L e₂ code₂)
    {j₂ : Nat}
    (h₂ : j₂ < code₂.length)
    (uhinU : CodeIn L Usl.usl_at Usl.usl)
    (uhinW : CodeIn L Wmc.wmc_at Wmc.wmc)
    (uhp : 48 ≤ (Ga V X.cpu.gpr).rsp.toNat)
    (uhs1 : ∀ i < 8, Foot Wl (Addr.add ((Ga V X.cpu.gpr).rsp - 8) i))
    (uhs2 : ∀ i < 8, Foot Wl (Addr.add ((Ga V X.cpu.gpr).rsp - 16) i))
    (uhs3 : ∀ i < 8, Foot Wl (Addr.add ((Ga V X.cpu.gpr).rsp - 24) i))
    (uhs4 : ∀ i < 8, Foot Wl (Addr.add ((Ga V X.cpu.gpr).rsp - 32) i))
    (uhs5 : ∀ i < 8, Foot Wl (Addr.add ((Ga V X.cpu.gpr).rsp - 40) i))
    (uhs6 : ∀ i < 8, Foot Wl (Addr.add ((Ga V X.cpu.gpr).rsp - 48) i))
    (ufd0 : ∀ i < 8, Foot F.data (Addr.add (Ga V X.cpu.gpr).rdi i))
    (uku : ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y →
      Agree F Y.proc.mm.mem
        (Vst (Uc4.V0 (Wa V X.cpu.gpr) (Ga V X.cpu.gpr)) ((Ga V X.cpu.gpr).rsp - 48) (toBytesLE (Uc4.uc4_at.add 35) 8)) →
      Y.cpu.rip = Usl.usl_at → Y.cpu.gpr = (Uc4.gC (Ga V X.cpu.gpr)).set 4 ((Ga V X.cpu.gpr).rsp - 48) →
      (∀ (Z : State) (V₁ : Addr → Byte) (t'' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V₁ →
        Z.cpu.rip = Uc4.uc4_at.add 35 → Z.cpu.gpr.rsp = (Ga V X.cpu.gpr).rsp - 40 →
          Z.cpu.gpr.r12 = (Ga V X.cpu.gpr).rdi →
        Uc4.Sv V₁ (Ga V X.cpu.gpr) → Pu Z V₁ → GoG prof L o gev gP gE Z t'') →
      GoG prof L o gev gP gE Y t')
    (ukw : ∀ (Z : State) (V₁ : Addr → Byte), Pu Z V₁ → ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y →
      Agree F Y.proc.mm.mem (Vst V₁ ((Ga V X.cpu.gpr).rsp - 48) (toBytesLE (Uc4.uc4_at.add 53) 8)) →
      Y.cpu.rip = Wmc.wmc_at → Y.cpu.gpr = (Uc4.gW V₁ Z.cpu.gpr (Ga V X.cpu.gpr)).set 4 ((Ga V X.cpu.gpr).rsp - 48) →
      (∀ (Zw : State) (V₂ : Addr → Byte) (t'' : Nat), KeptW Wl s₀ Zw → Agree F Zw.proc.mm.mem V₂ →
        Zw.cpu.rip = Uc4.uc4_at.add 53 → Zw.cpu.gpr.rsp = (Ga V X.cpu.gpr).rsp - 40 → Uc4.Sv V₂ (Ga V X.cpu.gpr) →
          Pw Z Zw V₂ →
        GoG prof L o gev gP gE Zw t'') →
      GoG prof L o gev gP gE Y t')
    (ukr : ∀ (Z Zw : State) (V₂ : Addr → Byte) (Y : State) (t' : Nat), Pw Z Zw V₂ → KeptW Wl s₀ Y →
      Agree F Y.proc.mm.mem V₂ → Y.cpu.rip = Wmc.wmc_at →
      Y.cpu.gpr = { Zw.cpu.gpr with
          rdi := Zw.cpu.gpr.r12 + Zw.cpu.gpr.rbx * 4#64,
          rdx := BitVec.setWidth 64 (BitVec.setWidth 32 (Zw.cpu.gpr.rbp + 1#64)),
          rbx := (Ga V X.cpu.gpr).rbx, rsi := Zw.cpu.gpr.r13, rbp := (Ga V X.cpu.gpr).rbp, r12 := (Ga V X.cpu.gpr).r12,
          r13 := (Ga V X.cpu.gpr).r13, r14 := (Ga V X.cpu.gpr).r14, rsp := (Ga V X.cpu.gpr).rsp } →
      (∀ (Z : State) (V' : Addr → Byte) (t'' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V' →
        Z.cpu.rip = upl_at.add 31 → Z.cpu.gpr.rsp = X.cpu.gpr.rsp - 8 → Z.cpu.gpr.r12 = X.cpu.gpr.rdi →
        rdq(V', X.cpu.gpr.rsp - 8) = X.cpu.gpr.r12 → rdq(V', X.cpu.gpr.rsp) = e₂.add j₂ →
        Pc Z V' → GoG prof L o gev gP gE Z t'') →
      GoG prof L o gev gP gE Y t')
    (kr : ∀ (Z : State) (V' : Addr → Byte) (Z' : State) (t' : Nat), Pc Z V' → KeptW Wl s₀ Z' →
      Agree F Z'.proc.mm.mem V' → Z'.cpu.rip = e₂.add j₂ →
      Z'.cpu.gpr = { Z.cpu.gpr with rax := X.cpu.gpr.rdi, rsp := X.cpu.gpr.rsp + 8, r12 := X.cpu.gpr.r12 } →
      GoG prof L o gev gP gE Z' t') :
    GoG prof L o gev gP gE X t := by
  refine upl_ok (Pc := Pc) c hin hinC hK hA hrip hp hs1 hs2 hl f1 f2 f3 f4 hin₂ h₂ ?_ kr
  intro Y t' hKY hAY hrY hgY kc
  have hgY' : Y.cpu.gpr = Ga V X.cpu.gpr := hgY
  refine Uc4.uc4_ok (Pu := Pu) (Pw := Pw) c hinC uhinU uhinW hKY (hAY : Agree F Y.proc.mm.mem (Wa V X.cpu.gpr))
    (by rw [hrY, addr_add_zero]) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  all_goals (try rw [hgY'])
  · exact uhp
  · exact uhs1
  · exact uhs2
  · exact uhs3
  · exact uhs4
  · exact uhs5
  · exact uhs6
  · exact ufd0
  · exact uku
  · exact ukw
  · exact fun a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 => ukr a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 kc

end FV7z.Upl
