import FV7z.Agr.Holds
import FV7z.Arl.Holds
/-!
# `AString::Grow` through `AString::ReAlloc` (PLAN.md §M, M1)

`agr_ok` leaves the tail jump to `AString::ReAlloc` as a hypothesis (`kf`); here it is discharged by `Arl.arl_ok`
at the jump's target, as `FV7z/Ag1/Ok.lean` does for `AString::Grow_1`. `AString::Grow` writes no byte and leaves
`rsp`, `rdi`, `rbx`, `rbp`, `r12`, `r13` as they were; `AString::ReAlloc`'s hypotheses on its three calls and its
return are those of `Arl.arl_ok` with the registers `gb` at the jump, for every `next` (`nx`) that `Grow` can pass
(`_len < nx <= 0x3ffffffe`, `n <= nx - _len`) and every `rcx` (`cx`).
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Agr

/-- The registers at the tail jump: `rax` = `n`, `rcx` = `cx`, `rdx` = `_len`, `esi` = `next`. -/
abbrev gb (V : Addr → Byte) (g : Gprs) (cx : BitVec 64) (nx : BitVec 32) : Gprs :=
  { g with
    rax := BitVec.setWidth 64 (BitVec.setWidth 32 g.rsi), rcx := cx,
    rdx := BitVec.setWidth 64 rdd(V, g.rdi + 8#64), rsi := BitVec.setWidth 64 nx }

variable {F : Footprint} {Wl : List Rgn} {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {X : State} {t : Nat} {V : Addr → Byte}

open Arl in
/-- `AString::Grow (n)` from its entry, `AString::ReAlloc` by `Arl.arl_ok`: the return with `n <= _limit - _len`
(`kn₀`), the throw stub (`kt`), else `AString::ReAlloc`'s three calls and its return, as in `Arl.arl_ok`, with the
registers `gb`. -/
theorem agr_arl {P1 P2 P3 : State → (Addr → Byte) → Prop} (c : Seg prof F Wl L s₀ o) (hin : CodeIn L agr_at agr)
    (hinR : CodeIn L Arl.arl_at Arl.arl)
    {codeT : List Byte} (hinT : CodeIn L 0x401394#64 codeT) (hT : 0 < codeT.length)
    {codeN codeM codeD : List Byte} (hinN : CodeIn L 0x6029b0#64 codeN) (hN : 0 < codeN.length)
    (hinM : CodeIn L 0x401070#64 codeM) (hM : 0 < codeM.length)
    (hinD : CodeIn L 0x6014f0#64 codeD) (hD : 0 < codeD.length)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = agr_at)
    (hp : 48 ≤ X.cpu.gpr.rsp.toNat) (hp8 : X.cpu.gpr.rsp.toNat + 8 ≤ 2 ^ 64)
    (hs1 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8) i))
    (hs2 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 16) i))
    (hs3 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 24) i))
    (hs4 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 32) i))
    (hs6 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 48) i))
    (hl : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsp i))
    (f0 : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rdi i))
    (f8 : ∀ i < 4, Foot F.data (Addr.add (X.cpu.gpr.rdi + 8#64) i))
    (f12 : ∀ i < 4, Foot F.data (Addr.add (X.cpu.gpr.rdi + 12#64) i))
    (w0 : ∀ i < 8, Foot Wl (Addr.add X.cpu.gpr.rdi i))
    (w12 : ∀ i < 4, Foot Wl (Addr.add (X.cpu.gpr.rdi + 12#64) i))
    (hq : X.cpu.gpr.rdi.toNat + 16 ≤ 2 ^ 64)
    (hd : X.cpu.gpr.rdi.toNat + 16 ≤ X.cpu.gpr.rsp.toNat - 32 ∨ X.cpu.gpr.rsp.toNat + 8 ≤ X.cpu.gpr.rdi.toNat)
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (hra : rdq(V, X.cpu.gpr.rsp) = e₂.add j₂)
    (kn₀ : (BitVec.setWidth 32 X.cpu.gpr.rsi).toNat ≤
        (rdd(V, X.cpu.gpr.rdi + 12#64) - rdd(V, X.cpu.gpr.rdi + 8#64)).toNat →
      ∀ (Z : State) (t' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V → Z.cpu.rip = e₂.add j₂ →
      Z.cpu.gpr = { X.cpu.gpr with
        rcx := BitVec.setWidth 64 (rdd(V, X.cpu.gpr.rdi + 12#64) - rdd(V, X.cpu.gpr.rdi + 8#64)),
        rdx := BitVec.setWidth 64 rdd(V, X.cpu.gpr.rdi + 8#64),
        rsp := X.cpu.gpr.rsp + 8 } →
      GoG prof L o gev gP gE Z t')
    (kt : ∀ (Y : State) (t' : Nat) (cx s : BitVec 64), KeptW Wl s₀ Y → Agree F Y.proc.mm.mem V →
      Y.cpu.rip = 0x401394#64 →
      Y.cpu.gpr = { X.cpu.gpr with
        rax := BitVec.setWidth 64 (BitVec.setWidth 32 X.cpu.gpr.rsi), rcx := cx,
        rdx := BitVec.setWidth 64 rdd(V, X.cpu.gpr.rdi + 8#64), rsp := X.cpu.gpr.rsp - 8#64, rsi := s } →
      GoG prof L o gev gP gE Y t')
    (kn : ∀ (d : BitVec 64) (n : BitVec 32), (rdd(V, X.cpu.gpr.rdi + 8#64)).toNat < n.toNat →
      n.toNat ≤ 1073741822 → (BitVec.setWidth 32 X.cpu.gpr.rsi).toNat ≤ (n - rdd(V, X.cpu.gpr.rdi + 8#64)).toNat →
      ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y →
      Agree F Y.proc.mm.mem (Vst (V0 V X.cpu.gpr) (X.cpu.gpr.rsp - 48) (toBytesLE (arl_at.add 31) 8)) →
      Y.cpu.rip = 0x6029b0#64 → Y.cpu.gpr = (gN (gb V X.cpu.gpr d n)).set 4 (X.cpu.gpr.rsp - 48) →
      (∀ (Z : State) (V' : Addr → Byte) (t'' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V' →
        Z.cpu.rip = arl_at.add 31 → Z.cpu.gpr.rsp = X.cpu.gpr.rsp - 40 → Z.cpu.gpr.rbx = X.cpu.gpr.rdi →
        Z.cpu.gpr.rbp = zl (gb V X.cpu.gpr d n) → P1 Z V' → GoG prof L o gev gP gE Z t'') →
      GoG prof L o gev gP gE Y t')
    (km : ∀ (d : BitVec 64) (n : BitVec 32), (rdd(V, X.cpu.gpr.rdi + 8#64)).toNat < n.toNat →
      n.toNat ≤ 1073741822 → (BitVec.setWidth 32 X.cpu.gpr.rsi).toNat ≤ (n - rdd(V, X.cpu.gpr.rdi + 8#64)).toNat →
      ∀ (Z : State) (V' : Addr → Byte), P1 Z V' → ∀ (Y : State) (t' : Nat),
      KeptW Wl s₀ Y → Agree F Y.proc.mm.mem (Vst V' (X.cpu.gpr.rsp - 48) (toBytesLE (arl_at.add 55) 8)) →
      Y.cpu.rip = 0x401070#64 → Y.cpu.gpr = (gM V' Z.cpu.gpr).set 4 (X.cpu.gpr.rsp - 48) →
      (∀ (Z₂ : State) (V'' : Addr → Byte) (t'' : Nat), KeptW Wl s₀ Z₂ → Agree F Z₂.proc.mm.mem V'' →
        Z₂.cpu.rip = arl_at.add 55 → Z₂.cpu.gpr.rsp = X.cpu.gpr.rsp - 40 → Z₂.cpu.gpr.rbx = X.cpu.gpr.rdi →
        Z₂.cpu.gpr.rbp = zl (gb V X.cpu.gpr d n) → Z₂.cpu.gpr.r12 = Z.cpu.gpr.rax →
        Z₂.cpu.gpr.r13 = rdq(V', X.cpu.gpr.rdi) → P2 Z₂ V'' → GoG prof L o gev gP gE Z₂ t'') →
      GoG prof L o gev gP gE Y t')
    (kd : ∀ (d : BitVec 64) (n : BitVec 32), (rdd(V, X.cpu.gpr.rdi + 8#64)).toNat < n.toNat →
      n.toNat ≤ 1073741822 → (BitVec.setWidth 32 X.cpu.gpr.rsi).toNat ≤ (n - rdd(V, X.cpu.gpr.rdi + 8#64)).toNat →
      ∀ (Z₂ : State) (V'' : Addr → Byte), P2 Z₂ V'' → ∀ (Y : State) (t' : Nat),
      KeptW Wl s₀ Y → Agree F Y.proc.mm.mem (Vst V'' (X.cpu.gpr.rsp - 48) (toBytesLE (arl_at.add 63) 8)) →
      Y.cpu.rip = 0x6014f0#64 →
      Y.cpu.gpr = { Z₂.cpu.gpr with rdi := Z₂.cpu.gpr.r13 }.set 4 (X.cpu.gpr.rsp - 48) →
      (∀ (Z₃ : State) (V₃ : Addr → Byte) (t'' : Nat), KeptW Wl s₀ Z₃ → Agree F Z₃.proc.mm.mem V₃ →
        Z₃.cpu.rip = arl_at.add 63 → Z₃.cpu.gpr.rsp = X.cpu.gpr.rsp - 40 → Z₃.cpu.gpr.rbx = X.cpu.gpr.rdi →
        Z₃.cpu.gpr.rbp = zl (gb V X.cpu.gpr d n) → Z₃.cpu.gpr.r12 = Z₂.cpu.gpr.r12 →
        Sv V₃ (gb V X.cpu.gpr d n) (e₂.add j₂) → P3 Z₃ V₃ → GoG prof L o gev gP gE Z₃ t'') →
      GoG prof L o gev gP gE Y t')
    (kr : ∀ (d : BitVec 64) (n : BitVec 32), (rdd(V, X.cpu.gpr.rdi + 8#64)).toNat < n.toNat →
      n.toNat ≤ 1073741822 → (BitVec.setWidth 32 X.cpu.gpr.rsi).toNat ≤ (n - rdd(V, X.cpu.gpr.rdi + 8#64)).toNat →
      ∀ (Z₃ : State) (V₃ : Addr → Byte) (Z' : State) (t' : Nat), P3 Z₃ V₃ →
      KeptW Wl s₀ Z' →
      Agree F Z'.proc.mm.mem
        (W2 V₃ X.cpu.gpr.rdi Z₃.cpu.gpr.r12 (BitVec.setWidth 32 (gb V X.cpu.gpr d n).rsi)) →
      Z'.cpu.rip = e₂.add j₂ →
      Z'.cpu.gpr =
        { Z₃.cpu.gpr with
            rbx := X.cpu.gpr.rbx
            rbp := X.cpu.gpr.rbp
            r12 := X.cpu.gpr.r12
            r13 := X.cpu.gpr.r13
            rsp := X.cpu.gpr.rsp + 8 } →
      GoG prof L o gev gP gE Z' t') :
    GoG prof L o gev gP gE X t := by
  refine agr_ok c hin hinR hinT hT hK hA hrip f8 f12 hl hin₂ h₂ hra kn₀ kt ?_
  intro Y t' d n hlt hn hle hKY hAY hrY hgY
  have hgY' : Y.cpu.gpr = gb V X.cpu.gpr d n := hgY
  refine Arl.arl_ok (P1 := P1) (P2 := P2) (P3 := P3) c hinR hinN hN hinM hM hinD hD hKY hAY hrY ?_ ?_ ?_ ?_ ?_ ?_
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hin₂ h₂ ?_ ?_ ?_ ?_
  all_goals rw [hgY']
  exacts [hp, hp8, hs1, hs2, hs3, hs4, hs6, hl, f0, f8, w0, w12, hq, hd, kn d n hlt hn hle, km d n hlt hn hle,
    kd d n hlt hn hle, kr d n hlt hn hle]

end FV7z.Agr
