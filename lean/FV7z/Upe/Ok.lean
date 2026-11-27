import FV7z.Upe.Holds
import FV7z.Ugr.Holds
/-!
# `UString::operator+= (s)` through `UString::Grow` (PLAN.md §M)

`upe_ok` leaves the first call, to `UString::Grow` at `Ugr.ugr_at`, as a hypothesis (`k1`); here it is discharged by
`Ugr.ugr_ok` at the call's target, with the registers `Gb` and the bytes `Wb` there. `Grow`'s own hypotheses are
those of `Ugr.ugr_ok` at that state: the throw stub (`gkt`) and the tail jump to `UString::ReAlloc` (`gkf`). When
`Grow` returns without growing, the frame of `operator+=` is as `k1`'s continuation asks (the saved `rbx` and `r12`
and the return address, read through the three stores of `Wb`), and `hP1` gives `P1` there. The second call, to
`wmemcpy` (`k2`), stays a hypothesis.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Upe

theorem e24 (s : BitVec 64) : s - 32 + 8 = s - 24 := by bv_omega
theorem t32 (s : BitVec 64) (h : 32 ≤ s.toNat) : (s - 32).toNat = s.toNat - 32 := by bv_omega

/-- The registers at `UString::Grow`'s entry (as in `k1` of `upe_ok`). -/
abbrev Gb (V : Addr → Byte) (g : Gprs) : Gprs := (gE g V).set 4 (g.rsp - 32)

/-- The bytes at `UString::Grow`'s entry: `V0` with the return address `upe_at + 25` pushed. -/
abbrev Wb (V : Addr → Byte) (g : Gprs) : Addr → Byte := Vst (V0 V g) (g.rsp - 32) (toBytesLE (upe_at.add 25) 8)

variable {F : Footprint} {Wl : List Rgn} {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE' : Outcome → List Event → Prop}
  {X : State} {t : Nat} {V : Addr → Byte}

/-- `UString::operator+= (s)` from its entry with `UString::Grow` by `Ugr.ugr_ok`: `Grow`'s throw stub (`gkt`) and
tail jump (`gkf`) at `Gb`/`Wb`, `P1` after a return without growing (`hP1`), then the call to `wmemcpy` (`k2`) and
the return (`kr`) as in `upe_ok`. -/
theorem upe_ugr {P1 P2 : State → (Addr → Byte) → Prop} (c : Seg prof F Wl L s₀ o)
    (hin : CodeIn L upe_at upe)
    (hinG : CodeIn L Ugr.ugr_at Ugr.ugr)
    (hinM : CodeIn L Wmc.wmc_at Wmc.wmc)
    (hK : KeptW Wl s₀ X)
    (hA : Agree F X.proc.mm.mem V)
    (hrip : X.cpu.rip = upe_at)
    (hp : 32 ≤ X.cpu.gpr.rsp.toNat)
    (hp8 : X.cpu.gpr.rsp.toNat + 8 ≤ 2 ^ 64)
    (hs1 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8) i))
    (hs2 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 16) i))
    (hs4 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 32) i))
    (hl : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsp i))
    (fn : ∀ i < 4, Foot F.data (Addr.add (X.cpu.gpr.rsi + 8#64) i))
    (fb : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsi i))
    (fw : ∀ i < 4, Foot Wl (Addr.add (X.cpu.gpr.rdi + 8#64) i))
    (fc : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rdi i))
    (hq : X.cpu.gpr.rdi.toNat + 12 ≤ 2 ^ 64)
    (hd : X.cpu.gpr.rdi.toNat + 12 ≤ X.cpu.gpr.rsp.toNat - 16 ∨ X.cpu.gpr.rsp.toNat ≤ X.cpu.gpr.rdi.toNat)
    {e₂ : Addr}
    {code₂ : List Byte}
    (hin₂ : CodeIn L e₂ code₂)
    {j₂ : Nat}
    (h₂ : j₂ < code₂.length)
    (hra : rdq(V, X.cpu.gpr.rsp) = e₂.add j₂)
    (hinR : CodeIn L Ura.ura_at Ura.ura)
    {codeT : List Byte}
    (hinT : CodeIn L 0x401406#64 codeT)
    (hT : 0 < codeT.length)
    (f12 : ∀ i < 4, Foot F.data (Addr.add (X.cpu.gpr.rdi + 12#64) i))
    (hP1 : (BitVec.setWidth 32 (Gb V X.cpu.gpr).rsi).toNat ≤
        (rdd((Wb V X.cpu.gpr), (Gb V X.cpu.gpr).rdi + 12#64) - rdd((Wb V X.cpu.gpr),
            (Gb V X.cpu.gpr).rdi + 8#64)).toNat →
      ∀ (Z : State), Z.cpu.rip = upe_at.add 25 →
      Z.cpu.gpr = { (Gb V X.cpu.gpr) with
        rax := BitVec.setWidth 64 (rdd((Wb V X.cpu.gpr), (Gb V X.cpu.gpr).rdi + 12#64) - rdd((Wb V X.cpu.gpr),
          (Gb V X.cpu.gpr).rdi + 8#64)),
        rdx := BitVec.setWidth 64 rdd((Wb V X.cpu.gpr), (Gb V X.cpu.gpr).rdi + 8#64),
        rsp := (Gb V X.cpu.gpr).rsp + 8 } → P1 Z (Wb V X.cpu.gpr))
    (gkt : ∀ (Y : State) (t' : Nat) (a cx : BitVec 64), KeptW Wl s₀ Y → Agree F Y.proc.mm.mem (Wb V X.cpu.gpr) →
      Y.cpu.rip = 0x401406#64 →
      Y.cpu.gpr = { (Gb V X.cpu.gpr) with
        rax := a, rcx := cx, rdx := BitVec.setWidth 64 rdd((Wb V X.cpu.gpr), (Gb V X.cpu.gpr).rdi + 8#64),
          rsp := (Gb V X.cpu.gpr).rsp - 8#64 } →
      GoG prof L o gev gP gE' Y t')
    (gkf : ∀ (Y : State) (t' : Nat) (cx : BitVec 64) (nx : BitVec 32),
      (rdd((Wb V X.cpu.gpr), (Gb V X.cpu.gpr).rdi + 8#64)).toNat < nx.toNat → nx.toNat ≤ 1073741822 →
      (BitVec.setWidth 32 (Gb V X.cpu.gpr).rsi).toNat ≤ (nx - rdd((Wb V X.cpu.gpr),
          (Gb V X.cpu.gpr).rdi + 8#64)).toNat →
      KeptW Wl s₀ Y → Agree F Y.proc.mm.mem (Wb V X.cpu.gpr) → Y.cpu.rip = Ura.ura_at →
      Y.cpu.gpr = { (Gb V X.cpu.gpr) with
        rax := BitVec.setWidth 64 nx, rcx := cx, rdx := BitVec.setWidth 64 rdd((Wb V X.cpu.gpr),
          (Gb V X.cpu.gpr).rdi + 8#64),
        rsi := BitVec.setWidth 64 (nx - 1#32) } →
      GoG prof L o gev gP gE' Y t')
    (k2 : ∀ (Z : State) (V' : Addr → Byte), P1 Z V' → ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y →
      Agree F Y.proc.mm.mem (Vst V' (X.cpu.gpr.rsp - 32) (toBytesLE (upe_at.add 52) 8)) →
      Y.cpu.rip = Wmc.wmc_at → Y.cpu.gpr = (g47 Z.cpu.gpr V').set 4 (X.cpu.gpr.rsp - 32) →
      (∀ (Z₂ : State) (V₂ : Addr → Byte) (t'' : Nat), KeptW Wl s₀ Z₂ → Agree F Z₂.proc.mm.mem V₂ →
        Z₂.cpu.rip = upe_at.add 52 → Z₂.cpu.gpr.rsp = X.cpu.gpr.rsp - 24 → Z₂.cpu.gpr.rbx = X.cpu.gpr.rsi →
        Z₂.cpu.gpr.r12 = X.cpu.gpr.rdi → rdq(V₂, X.cpu.gpr.rsp - 16) = X.cpu.gpr.rbx →
        rdq(V₂, X.cpu.gpr.rsp - 8) = X.cpu.gpr.r12 → rdq(V₂, X.cpu.gpr.rsp) = e₂.add j₂ → P2 Z₂ V₂ →
        GoG prof L o gev gP gE' Z₂ t'') →
      GoG prof L o gev gP gE' Y t')
    (kr : ∀ (Z₂ : State) (V₂ : Addr → Byte) (Z' : State) (t' : Nat), P2 Z₂ V₂ → KeptW Wl s₀ Z' →
      Agree F Z'.proc.mm.mem (V3 V₂ X.cpu.gpr) → Z'.cpu.rip = e₂.add j₂ →
      Z'.cpu.gpr = { Z₂.cpu.gpr with
        rax := X.cpu.gpr.rdi
        rbx := X.cpu.gpr.rbx
        rsp := X.cpu.gpr.rsp + 8
        r12 := X.cpu.gpr.r12 } →
      GoG prof L o gev gP gE' Z' t') :
    GoG prof L o gev gP gE' X t := by
  have hlt := X.cpu.gpr.rsp.isLt
  have tn8 : (X.cpu.gpr.rsp - 8).toNat = X.cpu.gpr.rsp.toNat - 8 := pt8 _ hp
  have tn16 : (X.cpu.gpr.rsp - 16).toNat = X.cpu.gpr.rsp.toNat - 16 := pt16 _ hp
  have tn816 : (X.cpu.gpr.rsp - 8 - 8).toNat = X.cpu.gpr.rsp.toNat - 16 := by rw [pe16]; exact tn16
  have tn32 : (X.cpu.gpr.rsp - 32).toNat = X.cpu.gpr.rsp.toNat - 32 := t32 _ hp
  -- reads through the return address `Wb` stores
  have rdW : ∀ x : Addr, x.toNat + 8 ≤ 2 ^ 64 →
      (x.toNat + 8 ≤ X.cpu.gpr.rsp.toNat - 32 ∨ X.cpu.gpr.rsp.toNat - 24 ≤ x.toNat) →
      rdq(Wb V X.cpu.gpr, x) = rdq(Vst (Vst V (X.cpu.gpr.rsp - 8) (toBytesLE X.cpu.gpr.r12 8))
        (X.cpu.gpr.rsp - 8 - 8) (toBytesLE X.cpu.gpr.rbx 8), x) := fun x hx h =>
    congrArg (ofBytesLE 64)
      (Tun.rd_Vst _ (X.cpu.gpr.rsp - 32) _ x 8 (by rw [toBytesLE_length]; omega) hx
        (by rw [toBytesLE_length]; omega))
  have rA : rdq(Wb V X.cpu.gpr, X.cpu.gpr.rsp - 32) = upe_at.add 25 := by
    show ofBytesLE 64 ((byteAddrs (X.cpu.gpr.rsp - 32) 8).map
      (Vst (V0 V X.cpu.gpr) (X.cpu.gpr.rsp - 32) (toBytesLE (upe_at.add 25) 8))) = _
    rw [Tun.rd_Vst_self (V0 V X.cpu.gpr) (X.cpu.gpr.rsp - 32) (toBytesLE (upe_at.add 25) 8) (toBytesLE_length _ _)
      (by omega), ofBytesLE_toBytesLE (n := 8) rfl _]
  have r16 : rdq(Wb V X.cpu.gpr, X.cpu.gpr.rsp - 16) = X.cpu.gpr.rbx := by
    rw [← pe16 X.cpu.gpr.rsp, rdW (X.cpu.gpr.rsp - 8 - 8) (by omega) (by omega),
      Tun.rd_Vst_self (Vst V (X.cpu.gpr.rsp - 8) (toBytesLE X.cpu.gpr.r12 8)) (X.cpu.gpr.rsp - 8 - 8)
        (toBytesLE X.cpu.gpr.rbx 8) (toBytesLE_length _ _) (by omega),
      ofBytesLE_toBytesLE (n := 8) rfl _]
  have r8 : rdq(Wb V X.cpu.gpr, X.cpu.gpr.rsp - 8) = X.cpu.gpr.r12 := by
    rw [rdW (X.cpu.gpr.rsp - 8) (by omega) (by omega),
      Tun.rd_Vst (Vst V (X.cpu.gpr.rsp - 8) (toBytesLE X.cpu.gpr.r12 8)) (X.cpu.gpr.rsp - 8 - 8)
        (toBytesLE X.cpu.gpr.rbx 8) (X.cpu.gpr.rsp - 8) 8 (by rw [toBytesLE_length]; omega) (by omega)
        (by rw [toBytesLE_length]; omega),
      Tun.rd_Vst_self V (X.cpu.gpr.rsp - 8) (toBytesLE X.cpu.gpr.r12 8) (toBytesLE_length _ _) (by omega),
      ofBytesLE_toBytesLE (n := 8) rfl _]
  have r0 : rdq(Wb V X.cpu.gpr, X.cpu.gpr.rsp) = e₂.add j₂ := by
    rw [rdW X.cpu.gpr.rsp hp8 (by omega),
      Tun.rd_Vst (Vst V (X.cpu.gpr.rsp - 8) (toBytesLE X.cpu.gpr.r12 8)) (X.cpu.gpr.rsp - 8 - 8)
        (toBytesLE X.cpu.gpr.rbx 8) X.cpu.gpr.rsp 8 (by rw [toBytesLE_length]; omega) hp8
        (by rw [toBytesLE_length]; omega),
      Tun.rd_Vst V (X.cpu.gpr.rsp - 8) (toBytesLE X.cpu.gpr.r12 8) X.cpu.gpr.rsp 8
        (by rw [toBytesLE_length]; omega) hp8 (by rw [toBytesLE_length]; omega)]
    exact hra
  refine upe_ok (P1 := P1) (P2 := P2) c hin hinG hinM hK hA hrip hp hp8 hs1 hs2 hs4 hl fn fb fw fc hq hd hin₂ h₂
    ?_ k2 kr
  intro Y t' hKY hAY hrY hgY kc
  have hgY' : Y.cpu.gpr = Gb V X.cpu.gpr := hgY
  refine Ugr.ugr_ok c hinG hinR hinT hT hKY (hAY : Agree F Y.proc.mm.mem (Wb V X.cpu.gpr)) hrY ?_ ?_ ?_ hin
    (lt_len (j := 25) (by decide)) ?_ ?_ ?_ ?_
  all_goals (try rw [hgY'])
  · exact fun i hi => c.hws _ (fw i hi)
  · exact f12
  · exact fun i hi => c.hws _ (hs4 i hi)
  · exact rA
  · intro hle Z t₂ hKZ hAZ hrZ hgZ
    refine kc Z (Wb V X.cpu.gpr) t₂ hKZ hAZ hrZ ?_ ?_ ?_ r16 r8 r0 (hP1 hle Z hrZ hgZ)
    · rw [hgZ]; exact e24 _
    · rw [hgZ]; try rfl
    · rw [hgZ]; try rfl
  · exact gkt
  · exact gkf

end FV7z.Upe
