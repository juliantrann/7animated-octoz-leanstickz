import FV7z.Apl.Holds
import FV7z.Acs.Holds
/-!
# `operator+ (s1, s2)` through its constructor (PLAN.md  M, M2)

`apl_ok` leaves the call to the constructor at `Acs.acs_at` as a hypothesis (`kf`); here it is discharged by
`Acs.acs_ok` at the call's target, with the registers `Ga` and the bytes `Wa` there. The constructor's hypotheses are
those of `Acs.acs_ok` at that state (prefixed `a`); its tail jump to `memcpy` (`akj`) also gets the way back to
`apl_at + 31` that `kf` offers (the return address `memcpy` returns to).
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Apl

/-- The registers at the callee's entry (as in `kf` of `apl_ok`). -/
abbrev Ga (V : Addr → Byte) (g : Gprs) : Gprs := (gC g (V0 V g)).set 4 (g.rsp - 16)

/-- The bytes at the callee's entry: `V0` with the return address `apl_at.add 31` pushed. -/
abbrev Wa (V : Addr → Byte) (g : Gprs) : Addr → Byte := Vst (V0 V g) (g.rsp - 16) (toBytesLE (apl_at.add 31) 8)

variable {F : Footprint} {Wl : List Rgn} {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {X : State} {t : Nat} {V : Addr → Byte}

/-- `operator+ (s1, s2)` from its entry with the constructor by `Acs.acs_ok`: the constructor's hypotheses at
`Ga`/`Wa`, its tail jump to `memcpy` with the way back into `operator+`, and the return of `operator+` (`kr`). -/
theorem apl_acs {Pc : State → (Addr → Byte) → Prop} {P1 P2 : State → (Addr → Byte) → Prop}
    (c : Seg prof F Wl L s₀ o)
    (hin : CodeIn L apl_at apl)
    (hinC : CodeIn L Acs.acs_at Acs.acs)
    (hK : KeptW Wl s₀ X)
    (hA : Agree F X.proc.mm.mem V)
    (hrip : X.cpu.rip = apl_at)
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
    (ahinS : CodeIn L Asl.asl_at Asl.asl)
    (ahinW : CodeIn L Onw.onw_at Onw.onw)
    {codeM : List Byte}
    (ahinM : CodeIn L 0x401070#64 codeM)
    (ahM : 0 < codeM.length)
    (ahp : 80 ≤ (Ga V X.cpu.gpr).rsp.toNat)
    (ahp8 : (Ga V X.cpu.gpr).rsp.toNat + 8 ≤ 2 ^ 64)
    (ahs1 : ∀ i < 8, Foot Wl (Addr.add ((Ga V X.cpu.gpr).rsp - 8) i))
    (ahs2 : ∀ i < 8, Foot Wl (Addr.add ((Ga V X.cpu.gpr).rsp - 16) i))
    (ahs3 : ∀ i < 8, Foot Wl (Addr.add ((Ga V X.cpu.gpr).rsp - 24) i))
    (ahs4 : ∀ i < 8, Foot Wl (Addr.add ((Ga V X.cpu.gpr).rsp - 32) i))
    (ahs5 : ∀ i < 8, Foot Wl (Addr.add ((Ga V X.cpu.gpr).rsp - 40) i))
    (ahs6 : ∀ i < 8, Foot Wl (Addr.add ((Ga V X.cpu.gpr).rsp - 48) i))
    (ahs7 : ∀ i < 8, Foot Wl (Addr.add ((Ga V X.cpu.gpr).rsp - 56) i))
    (ahs8 : ∀ i < 8, Foot Wl (Addr.add ((Ga V X.cpu.gpr).rsp - 64) i))
    (ahs10 : ∀ i < 8, Foot Wl (Addr.add ((Ga V X.cpu.gpr).rsp - 80) i))
    (afw0 : ∀ i < 8, Foot Wl (Addr.add (Ga V X.cpu.gpr).rdi i))
    (afw8 : ∀ i < 4, Foot Wl (Addr.add ((Ga V X.cpu.gpr).rdi + 8#64) i))
    (afw12 : ∀ i < 4, Foot Wl (Addr.add ((Ga V X.cpu.gpr).rdi + 12#64) i))
    (ahq : (Ga V X.cpu.gpr).rdi.toNat + 16 ≤ 2 ^ 64)
    (ahd : (Ga V X.cpu.gpr).rdi.toNat + 16 ≤ (Ga V X.cpu.gpr).rsp.toNat - 64 ∨
        (Ga V X.cpu.gpr).rsp.toNat + 8 ≤ (Ga V X.cpu.gpr).rdi.toNat)
    (akf : ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y →
      Agree F Y.proc.mm.mem
        (Vst (Asl.V0 (Acs.VY (Wa V X.cpu.gpr) (Ga V X.cpu.gpr)) (Acs.gY (Ga V X.cpu.gpr)))
            ((Acs.gY (Ga V X.cpu.gpr)).rsp - 32) (toBytesLE (Asl.asl_at.add 34) 8)) →
      Y.cpu.rip = Onw.onw_at.add 64 →
        Y.cpu.gpr = (Asl.gC (Acs.gY (Ga V X.cpu.gpr))).set 4 ((Acs.gY (Ga V X.cpu.gpr)).rsp - 32) →
      (∀ (Z : State) (V' : Addr → Byte) (t'' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V' →
        Z.cpu.rip = Asl.asl_at.add 34 → Z.cpu.gpr.rsp = (Acs.gY (Ga V X.cpu.gpr)).rsp - 24 →
        Z.cpu.gpr.rbx = (Acs.gY (Ga V X.cpu.gpr)).rdi → Z.cpu.gpr.rbp = Asl.zl (Acs.gY (Ga V X.cpu.gpr)) →
        rdq(V', (Acs.gY (Ga V X.cpu.gpr)).rsp - 16) = (Acs.gY (Ga V X.cpu.gpr)).rbx →
        rdq(V', (Acs.gY (Ga V X.cpu.gpr)).rsp - 8) = (Acs.gY (Ga V X.cpu.gpr)).rbp →
          rdq(V', (Acs.gY (Ga V X.cpu.gpr)).rsp) = Acs.acs_at.add 35 →
        (Z.cpu.gpr.r12 = (Ga V X.cpu.gpr).rdi ∧ Z.cpu.gpr.r13 = (Ga V X.cpu.gpr).rcx ∧
            Z.cpu.gpr.r14 = (Ga V X.cpu.gpr).rsi ∧
          P1 Z V') →
        GoG prof L o gev gP gE Z t'') →
      GoG prof L o gev gP gE Y t')
    (akm : ∀ (Z : State) (V' : Addr → Byte), P1 Z V' → ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y →
      Agree F Y.proc.mm.mem
        (Vst (Asl.V1 V' (Ga V X.cpu.gpr).rdi (Acs.nl (Ga V X.cpu.gpr)) Z.cpu.gpr.rax) ((Ga V X.cpu.gpr).rsp - 48)
          (toBytesLE (Acs.acs_at.add 50) 8)) →
      Y.cpu.rip = 0x401070#64 →
      Y.cpu.gpr =
        ({ Z.cpu.gpr with
            rbx := Acs.zd (Ga V X.cpu.gpr)
            rbp := Acs.zr (Ga V X.cpu.gpr)
            rdi := Z.cpu.gpr.rax
            rdx := Acs.zd (Ga V X.cpu.gpr)
            rsi := (Ga V X.cpu.gpr).rsi } : Gprs).set 4 ((Ga V X.cpu.gpr).rsp - 48) →
      (∀ (Z₂ : State) (V'' : Addr → Byte) (t'' : Nat), KeptW Wl s₀ Z₂ → Agree F Z₂.proc.mm.mem V'' →
        Z₂.cpu.rip = Acs.acs_at.add 50 → Z₂.cpu.gpr.rsp = (Ga V X.cpu.gpr).rsp - 40 →
          Z₂.cpu.gpr.rbx = Acs.zd (Ga V X.cpu.gpr) →
        Z₂.cpu.gpr.rbp = Acs.zr (Ga V X.cpu.gpr) → Z₂.cpu.gpr.r13 = (Ga V X.cpu.gpr).rcx →
          Acs.Sv V'' (Ga V X.cpu.gpr) → P2 Z₂ V'' →
        GoG prof L o gev gP gE Z₂ t'') →
      GoG prof L o gev gP gE Y t')
    (akj : ∀ (Z₂ : State) (V'' : Addr → Byte), P2 Z₂ V'' → ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y →
      Agree F Y.proc.mm.mem V'' → Y.cpu.rip = 0x401070#64 →
      Y.cpu.gpr =
        { Z₂.cpu.gpr with
            rdx := BitVec.setWidth 64 (BitVec.setWidth 32 (Ga V X.cpu.gpr).r8 + 1#32)
            rsi := (Ga V X.cpu.gpr).rcx
            rdi := Z₂.cpu.gpr.rax + Acs.zd (Ga V X.cpu.gpr)
            rbx := (Ga V X.cpu.gpr).rbx
            rbp := (Ga V X.cpu.gpr).rbp
            r12 := (Ga V X.cpu.gpr).r12
            r13 := (Ga V X.cpu.gpr).r13
            r14 := (Ga V X.cpu.gpr).r14
            rsp := (Ga V X.cpu.gpr).rsp } →
      (∀ (Z : State) (V' : Addr → Byte) (t'' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V' →
        Z.cpu.rip = apl_at.add 31 → Z.cpu.gpr.rsp = X.cpu.gpr.rsp - 8 → Z.cpu.gpr.r12 = X.cpu.gpr.rdi →
        rdq(V', X.cpu.gpr.rsp - 8) = X.cpu.gpr.r12 → rdq(V', X.cpu.gpr.rsp) = e₂.add j₂ →
        Pc Z V' → GoG prof L o gev gP gE Z t'') →
      GoG prof L o gev gP gE Y t')
    (kr : ∀ (Z : State) (V' : Addr → Byte) (Z' : State) (t' : Nat), Pc Z V' → KeptW Wl s₀ Z' →
      Agree F Z'.proc.mm.mem V' → Z'.cpu.rip = e₂.add j₂ →
      Z'.cpu.gpr = { Z.cpu.gpr with rax := X.cpu.gpr.rdi, rsp := X.cpu.gpr.rsp + 8, r12 := X.cpu.gpr.r12 } →
      GoG prof L o gev gP gE Z' t') :
    GoG prof L o gev gP gE X t := by
  refine apl_ok (Pc := Pc) c hin hinC hK hA hrip hp hs1 hs2 hl f1 f2 f3 f4 hin₂ h₂ ?_ kr
  intro Y t' hKY hAY hrY hgY kc
  have hgY' : Y.cpu.gpr = Ga V X.cpu.gpr := hgY
  refine Acs.acs_ok (P1 := P1) (P2 := P2) c hinC ahinS ahinW ahinM ahM hKY
    (hAY : Agree F Y.proc.mm.mem (Wa V X.cpu.gpr)) (by rw [hrY, addr_add_zero])
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  all_goals (try rw [hgY'])
  · exact ahp
  · exact ahp8
  · exact ahs1
  · exact ahs2
  · exact ahs3
  · exact ahs4
  · exact ahs5
  · exact ahs6
  · exact ahs7
  · exact ahs8
  · exact ahs10
  · exact afw0
  · exact afw8
  · exact afw12
  · exact ahq
  · exact ahd
  · exact akf
  · exact akm
  · exact fun a0 a1 a2 a3 a4 a5 a6 a7 a8 => akj a0 a1 a2 a3 a4 a5 a6 a7 a8 kc

end FV7z.Apl
