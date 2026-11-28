import FV7z.Ag1.Holds
import FV7z.Arl.Holds
/-!
# `AString::Grow_1` through `AString::ReAlloc` (PLAN.md §M, M1)

`ag1_ok` leaves the tail jump to `AString::ReAlloc` as a hypothesis (`kf`); here it is discharged by `Arl.arl_ok`
at the jump's target. `AString::Grow_1` writes no byte and leaves `rsp`, `rdi`, `rbx`, `rbp`, `r12`, `r13` as they
were, so `AString::ReAlloc`'s preconditions on the stack and on `this` are stated at `Grow_1`'s entry; its hypotheses
on the three calls (`kn`, `km`, `kd`) and on the return (`kr`) are those of `Arl.arl_ok` with the registers `ga` at
the jump, for every `next` (`n`) that `Grow_1` can pass, `_len < n <= 0x3ffffffe`, and every `rdx` (`d`).
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Ag1

/-- The registers at the tail jump: `rax` = `_len`, `rdx` = `d`, `esi` = `next`. -/
abbrev ga (V : Addr → Byte) (g : Gprs) (d : BitVec 64) (n : BitVec 32) : Gprs :=
  { g with rax := BitVec.setWidth 64 rdd(V, g.rdi + 8#64), rdx := d, rsi := BitVec.setWidth 64 n }

variable {F : Footprint} {Wl : List Rgn} {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {X : State} {t : Nat} {V : Addr → Byte}

open Arl in
/-- `AString::Grow_1 ()` from its entry, `AString::ReAlloc` by `Arl.arl_ok`: the throw stub with `next <= _len`
(`kt`), else `AString::ReAlloc`'s three calls and its return, as in `Arl.arl_ok`, with the registers `ga`. -/
theorem ag1_arl {P1 P2 P3 : State → (Addr → Byte) → Prop} (c : Seg prof F Wl L s₀ o) (hin : CodeIn L ag1_at ag1)
    (hinR : CodeIn L Arl.arl_at Arl.arl)
    {codeT : List Byte} (hinT : CodeIn L 0x401372#64 codeT) (hT : 0 < codeT.length)
    {codeN codeM codeD : List Byte} (hinN : CodeIn L 0x6029b0#64 codeN) (hN : 0 < codeN.length)
    (hinM : CodeIn L 0x401070#64 codeM) (hM : 0 < codeM.length)
    (hinD : CodeIn L 0x6014f0#64 codeD) (hD : 0 < codeD.length)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = ag1_at)
    (hp : 48 ≤ X.cpu.gpr.rsp.toNat) (hp8 : X.cpu.gpr.rsp.toNat + 8 ≤ 2 ^ 64)
    (hs1 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8) i))
    (hs2 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 16) i))
    (hs3 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 24) i))
    (hs4 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 32) i))
    (hs6 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 48) i))
    (hl : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsp i))
    (f0 : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rdi i))
    (f8 : ∀ i < 4, Foot F.data (Addr.add (X.cpu.gpr.rdi + 8#64) i))
    (w0 : ∀ i < 8, Foot Wl (Addr.add X.cpu.gpr.rdi i))
    (w12 : ∀ i < 4, Foot Wl (Addr.add (X.cpu.gpr.rdi + 12#64) i))
    (hq : X.cpu.gpr.rdi.toNat + 16 ≤ 2 ^ 64)
    (hd : X.cpu.gpr.rdi.toNat + 16 ≤ X.cpu.gpr.rsp.toNat - 32 ∨ X.cpu.gpr.rsp.toNat + 8 ≤ X.cpu.gpr.rdi.toNat)
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (kt : ∀ (Y : State) (t' : Nat) (d : BitVec 64) (n : BitVec 32),
      n.toNat ≤ (rdd(V, X.cpu.gpr.rdi + 8#64)).toNat → KeptW Wl s₀ Y → Agree F Y.proc.mm.mem V →
      Y.cpu.rip = 0x401372#64 → Y.cpu.gpr = gq V X.cpu.gpr n d → GoG prof L o gev gP gE Y t')
    (kn : ∀ (d : BitVec 64) (n : BitVec 32), (rdd(V, X.cpu.gpr.rdi + 8#64)).toNat < n.toNat →
      n.toNat ≤ 1073741822 → ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y →
      Agree F Y.proc.mm.mem (Vst (V0 V X.cpu.gpr) (X.cpu.gpr.rsp - 48) (toBytesLE (arl_at.add 31) 8)) →
      Y.cpu.rip = 0x6029b0#64 → Y.cpu.gpr = (gN (ga V X.cpu.gpr d n)).set 4 (X.cpu.gpr.rsp - 48) →
      (∀ (Z : State) (V' : Addr → Byte) (t'' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V' →
        Z.cpu.rip = arl_at.add 31 → Z.cpu.gpr.rsp = X.cpu.gpr.rsp - 40 → Z.cpu.gpr.rbx = X.cpu.gpr.rdi →
        Z.cpu.gpr.rbp = zl (ga V X.cpu.gpr d n) → P1 Z V' → GoG prof L o gev gP gE Z t'') →
      GoG prof L o gev gP gE Y t')
    (km : ∀ (d : BitVec 64) (n : BitVec 32), (rdd(V, X.cpu.gpr.rdi + 8#64)).toNat < n.toNat →
      n.toNat ≤ 1073741822 → ∀ (Z : State) (V' : Addr → Byte), P1 Z V' → ∀ (Y : State) (t' : Nat),
      KeptW Wl s₀ Y → Agree F Y.proc.mm.mem (Vst V' (X.cpu.gpr.rsp - 48) (toBytesLE (arl_at.add 55) 8)) →
      Y.cpu.rip = 0x401070#64 → Y.cpu.gpr = (gM V' Z.cpu.gpr).set 4 (X.cpu.gpr.rsp - 48) →
      (∀ (Z₂ : State) (V'' : Addr → Byte) (t'' : Nat), KeptW Wl s₀ Z₂ → Agree F Z₂.proc.mm.mem V'' →
        Z₂.cpu.rip = arl_at.add 55 → Z₂.cpu.gpr.rsp = X.cpu.gpr.rsp - 40 → Z₂.cpu.gpr.rbx = X.cpu.gpr.rdi →
        Z₂.cpu.gpr.rbp = zl (ga V X.cpu.gpr d n) → Z₂.cpu.gpr.r12 = Z.cpu.gpr.rax →
        Z₂.cpu.gpr.r13 = rdq(V', X.cpu.gpr.rdi) → P2 Z₂ V'' → GoG prof L o gev gP gE Z₂ t'') →
      GoG prof L o gev gP gE Y t')
    (kd : ∀ (d : BitVec 64) (n : BitVec 32), (rdd(V, X.cpu.gpr.rdi + 8#64)).toNat < n.toNat →
      n.toNat ≤ 1073741822 → ∀ (Z₂ : State) (V'' : Addr → Byte), P2 Z₂ V'' → ∀ (Y : State) (t' : Nat),
      KeptW Wl s₀ Y → Agree F Y.proc.mm.mem (Vst V'' (X.cpu.gpr.rsp - 48) (toBytesLE (arl_at.add 63) 8)) →
      Y.cpu.rip = 0x6014f0#64 →
      Y.cpu.gpr = { Z₂.cpu.gpr with rdi := Z₂.cpu.gpr.r13 }.set 4 (X.cpu.gpr.rsp - 48) →
      (∀ (Z₃ : State) (V₃ : Addr → Byte) (t'' : Nat), KeptW Wl s₀ Z₃ → Agree F Z₃.proc.mm.mem V₃ →
        Z₃.cpu.rip = arl_at.add 63 → Z₃.cpu.gpr.rsp = X.cpu.gpr.rsp - 40 → Z₃.cpu.gpr.rbx = X.cpu.gpr.rdi →
        Z₃.cpu.gpr.rbp = zl (ga V X.cpu.gpr d n) → Z₃.cpu.gpr.r12 = Z₂.cpu.gpr.r12 →
        Sv V₃ (ga V X.cpu.gpr d n) (e₂.add j₂) → P3 Z₃ V₃ → GoG prof L o gev gP gE Z₃ t'') →
      GoG prof L o gev gP gE Y t')
    (kr : ∀ (d : BitVec 64) (n : BitVec 32), (rdd(V, X.cpu.gpr.rdi + 8#64)).toNat < n.toNat →
      n.toNat ≤ 1073741822 → ∀ (Z₃ : State) (V₃ : Addr → Byte) (Z' : State) (t' : Nat), P3 Z₃ V₃ →
      KeptW Wl s₀ Z' →
      Agree F Z'.proc.mm.mem
        (W2 V₃ X.cpu.gpr.rdi Z₃.cpu.gpr.r12 (BitVec.setWidth 32 (ga V X.cpu.gpr d n).rsi)) →
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
  refine ag1_ok c hin hinR hinT hT hK hA hrip f8 kt ?_
  intro Y t' d n hlt hn hKY hAY hrY hgY
  have hgY' : Y.cpu.gpr = ga V X.cpu.gpr d n := hgY
  refine Arl.arl_ok (P1 := P1) (P2 := P2) (P3 := P3) c hinR hinN hN hinM hM hinD hD hKY hAY hrY ?_ ?_ ?_ ?_ ?_ ?_
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hin₂ h₂ ?_ ?_ ?_ ?_
  all_goals (try rw [hgY'])
  · exact hp
  · exact hp8
  · exact hs1
  · exact hs2
  · exact hs3
  · exact hs4
  · exact hs6
  · exact hl
  · exact f0
  · exact f8
  · exact w0
  · exact w12
  · exact hq
  · exact hd
  · exact kn d n hlt hn
  · exact km d n hlt hn
  · exact kd d n hlt hn
  · exact kr d n hlt hn

end FV7z.Ag1
