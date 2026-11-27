import FV7z.Ur2.Holds
import FV7z.Ura.New
/-!
# `UString::ReAlloc2 (newLimit)` with `operator new` (PLAN.md §M, M1)

`ur2_ok` takes the call of `operator new (4 n + 4)` as a hypothesis (`kn`); `ur2_okH` discharges it
by `Onw.onw_pnW`, with `Mal.MalB (4 n + 4) B`, `Mal.Hp` with a top of at least `m + B` bytes below `hi` at the entry,
`hi` 264 bytes below `rsp` and `[hi, rsp)` in what the run may store into. The post of `operator new` is `PnH`
(`Onw.PnW` from the bytes `VR` at its entry, `rsp - 32` up); the other callees stay hypotheses.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
open FV7z.Imm (imm imm_at)
open FV7z.Mnx (mnx mnx_at)
namespace FV7z.Ur2

variable {F : Footprint} {Wl : List Rgn} {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {X : State} {t : Nat} {V : Addr → Byte}

/-- The bytes at `operator new`'s entry: the return address `ur2_at + 40` pushed below the saved registers. -/
abbrev VR (V : Addr → Byte) (g : Gprs) : Addr → Byte := Vst (VN V g) (g.rsp - 32) (toBytesLE (ur2_at.add 40) 8)

/-- The post of `operator new` for the registers `g` and the bytes `V` at the entry: see the module doc. -/
abbrev PnH (F : Footprint) (Wl : List Rgn) (fb : Addr) (hi m : Nat) (g : Gprs) (V : Addr → Byte) :
    State → (Addr → Byte) → Prop :=
  Onw.PnW F Wl fb hi m (VR V g) (4 * (BitVec.setWidth 32 g.rsi).toNat + 4) (g.rsp.toNat - 32)

set_option maxHeartbeats 1000000 in
/-- `ur2_ok` with `operator new` by `Onw.onw_pnW`: see the module doc. -/
theorem ur2_okH {Pd : State → State → (Addr → Byte) → Prop}
    {fb : Addr} {hi m B : Nat}
    (c : Seg prof F Wl L s₀ o) (hin : CodeIn L ur2_at ur2) (hinN : CodeIn L Onw.onw_at Onw.onw)
    {codeT : List Byte} (hinT : CodeIn L 0x4013c2#64 codeT) (hT : 0 < codeT.length)
    {codeD : List Byte} (hinD : CodeIn L 0x6014f0#64 codeD) (hD : 0 < codeD.length)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = ur2_at)
    (hfs : s₀.cpu.seg.fsBase = fb) (hinM : CodeIn L mnx_at mnx) (hinI : CodeIn L imm_at imm)
    (hH : Mal.Hp F Wl fb hi (m + B) V) (hB : Mal.MalB (zl X.cpu.gpr * 4#64 + 4#64) B)
    (hhi : hi + 264 ≤ X.cpu.gpr.rsp.toNat)
    (hsw : ∀ a : Addr, hi ≤ a.toNat → a.toNat < X.cpu.gpr.rsp.toNat → Foot Wl a)
    (hp8 : X.cpu.gpr.rsp.toNat + 8 < 2 ^ 64)
    (hl : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsp i))
    (fr0 : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rdi i))
    (fw0 : ∀ i < 8, Foot Wl (Addr.add X.cpu.gpr.rdi i))
    (fw8 : ∀ i < 4, Foot Wl (Addr.add (X.cpu.gpr.rdi + 8#64) i))
    (fw12 : ∀ i < 4, Foot Wl (Addr.add (X.cpu.gpr.rdi + 12#64) i))
    (hq : X.cpu.gpr.rdi.toNat + 16 ≤ 2 ^ 64)
    (hd : X.cpu.gpr.rdi.toNat + 16 ≤ X.cpu.gpr.rsp.toNat - 24 ∨ X.cpu.gpr.rsp.toNat + 8 ≤ X.cpu.gpr.rdi.toNat)
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (hra : rdq(V, X.cpu.gpr.rsp) = e₂.add j₂)
    (kt : ∀ (Y : State) (t' : Nat), 1073741822 < (BitVec.setWidth 32 X.cpu.gpr.rsi).toNat → KeptW Wl s₀ Y →
      Agree F Y.proc.mm.mem (VN V X.cpu.gpr) → Y.cpu.rip = 0x4013c2#64 →
      Y.cpu.gpr = { X.cpu.gpr with rsp := X.cpu.gpr.rsp - 24 } → GoG prof L o gev gP gE Y t')
    (kd : ∀ (Zn : State) (V₁ : Addr → Byte), PnH F Wl fb hi m X.cpu.gpr V Zn V₁ → rdq(V₁, X.cpu.gpr.rdi) ≠ 0 →
      ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y →
      Agree F Y.proc.mm.mem (Vst (Vz V₁ Zn.cpu.gpr.rax) (X.cpu.gpr.rsp - 32) (toBytesLE (ur2_at.add 62) 8)) →
      Y.cpu.rip = 0x6014f0#64 →
      Y.cpu.gpr = { Zn.cpu.gpr with rdi := rdq(V₁, X.cpu.gpr.rdi), r12 := Zn.cpu.gpr.rax }.set 4
        (X.cpu.gpr.rsp - 32) →
      (∀ (Zd : State) (V₃ : Addr → Byte) (t'' : Nat), KeptW Wl s₀ Zd → Agree F Zd.proc.mm.mem V₃ →
        Zd.cpu.rip = ur2_at.add 62 → Zd.cpu.gpr.rsp = X.cpu.gpr.rsp - 24 → Zd.cpu.gpr.rbx = X.cpu.gpr.rdi →
        Zd.cpu.gpr.rbp = zl X.cpu.gpr → Zd.cpu.gpr.r12 = Zn.cpu.gpr.rax → Sv V₃ X.cpu.gpr (e₂.add j₂) →
        Pd Zn Zd V₃ → GoG prof L o gev gP gE Zd t'') →
      GoG prof L o gev gP gE Y t')
    (kr0 : ∀ (Zn : State) (V₁ : Addr → Byte) (Z' : State) (t' : Nat), PnH F Wl fb hi m X.cpu.gpr V Zn V₁ →
      rdq(V₁, X.cpu.gpr.rdi) = 0 → KeptW Wl s₀ Z' →
      Agree F Z'.proc.mm.mem
        (VE (Vz V₁ Zn.cpu.gpr.rax) X.cpu.gpr.rdi Zn.cpu.gpr.rax (BitVec.setWidth 32 X.cpu.gpr.rsi)) →
      Z'.cpu.rip = e₂.add j₂ →
      Z'.cpu.gpr = { Zn.cpu.gpr with
          rdi := rdq(V₁, X.cpu.gpr.rdi), rbx := X.cpu.gpr.rbx, rbp := X.cpu.gpr.rbp, r12 := X.cpu.gpr.r12,
          rsp := X.cpu.gpr.rsp + 8 } →
      GoG prof L o gev gP gE Z' t')
    (kr1 : ∀ (Zn Zd : State) (V₃ : Addr → Byte) (Z' : State) (t' : Nat), Pd Zn Zd V₃ → KeptW Wl s₀ Z' →
      Agree F Z'.proc.mm.mem (VE V₃ X.cpu.gpr.rdi Zn.cpu.gpr.rax (BitVec.setWidth 32 X.cpu.gpr.rsi)) →
      Z'.cpu.rip = e₂.add j₂ →
      Z'.cpu.gpr = { Zd.cpu.gpr with
          rbx := X.cpu.gpr.rbx, rbp := X.cpu.gpr.rbp, r12 := X.cpu.gpr.r12, rsp := X.cpu.gpr.rsp + 8 } →
      GoG prof L o gev gP gE Z' t') :
    GoG prof L o gev gP gE X t := by
  have hlt := X.cpu.gpr.rsp.isLt
  have hB3 : 64 ≤ B := hB.2.2
  have tn8 : (X.cpu.gpr.rsp - 8).toNat = X.cpu.gpr.rsp.toNat - 8 := by rw [BitVec.toNat_sub]; simp <;> omega
  have tn16 : (X.cpu.gpr.rsp - 16).toNat = X.cpu.gpr.rsp.toNat - 16 := by rw [BitVec.toNat_sub]; simp <;> omega
  have tn24 : (X.cpu.gpr.rsp - 24).toNat = X.cpu.gpr.rsp.toNat - 24 := by rw [BitVec.toNat_sub]; simp <;> omega
  have tn32 : (X.cpu.gpr.rsp - 32).toNat = X.cpu.gpr.rsp.toNat - 32 := by rw [BitVec.toNat_sub]; simp <;> omega
  have u2 : (X.cpu.gpr.rsp - 8 - 8).toNat = X.cpu.gpr.rsp.toNat - 16 := by
    rw [BitVec.toNat_sub, tn8]; simp <;> omega
  have u3 : (X.cpu.gpr.rsp - 8 - 8 - 8).toNat = X.cpu.gpr.rsp.toNat - 24 := by
    rw [BitVec.toNat_sub, u2]; simp <;> omega
  have l8 : ∀ x : BitVec 64, (toBytesLE x 8).length = 8 := fun x => toBytesLE_length _ _
  have hfw : ∀ (x : Addr) (d : Nat), x.toNat = X.cpu.gpr.rsp.toNat - d → 8 ≤ d → d ≤ 32 →
      ∀ i < 8, Foot Wl (Addr.add x i) := fun x d hx h1 h2 i hi' => by
    have e := toNat_add_of_fits (a := x) (i := i) (n := 8) hi' (by rw [hx]; omega)
    exact hsw _ (by rw [e, hx]; omega) (by rw [e, hx]; omega)
  have hz : (zl X.cpu.gpr * 4#64 + 4#64).toNat = 4 * (BitVec.setWidth 32 X.cpu.gpr.rsi).toNat + 4 := by
    have := (BitVec.setWidth 32 X.cpu.gpr.rsi).isLt
    show (BitVec.setWidth 64 (BitVec.setWidth 32 X.cpu.gpr.rsi) * 4#64 + 4#64).toNat = _
    rw [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    omega
  -- the bytes at `operator new`'s entry outside the frame
  have hVo : ∀ a : Addr, (a.toNat < X.cpu.gpr.rsp.toNat - 32 ∨ X.cpu.gpr.rsp.toNat ≤ a.toNat) →
      VR V X.cpu.gpr a = V a := by
    intro a h1
    have s0 := Tun.Vst_out (Vst (Vst (Vst (V) (X.cpu.gpr.rsp - 8) (toBytesLE X.cpu.gpr.r12 8)) (X.cpu.gpr.rsp - 8 - 8)
        (toBytesLE X.cpu.gpr.rbp 8)) (X.cpu.gpr.rsp - 8 - 8 - 8) (toBytesLE X.cpu.gpr.rbx 8)) (X.cpu.gpr.rsp - 32)
        (toBytesLE (ur2_at.add 40) 8) a
      (by rw [l8, tn32]; omega) (by rw [l8, tn32]; omega)
    have s3 := Tun.Vst_out (Vst (Vst (V) (X.cpu.gpr.rsp - 8) (toBytesLE X.cpu.gpr.r12 8)) (X.cpu.gpr.rsp - 8 - 8)
        (toBytesLE X.cpu.gpr.rbp 8)) (X.cpu.gpr.rsp - 8 - 8 - 8) (toBytesLE X.cpu.gpr.rbx 8) a
      (by rw [l8, u3]; omega) (by rw [l8, u3]; omega)
    have s2 := Tun.Vst_out (Vst (V) (X.cpu.gpr.rsp - 8)
        (toBytesLE X.cpu.gpr.r12 8)) (X.cpu.gpr.rsp - 8 - 8) (toBytesLE X.cpu.gpr.rbp 8) a
      (by rw [l8, u2]; omega) (by rw [l8, u2]; omega)
    have s1 := Tun.Vst_out (V) (X.cpu.gpr.rsp - 8) (toBytesLE X.cpu.gpr.r12 8) a
      (by rw [l8, tn8]; omega) (by rw [l8, tn8]; omega)
    exact s0.trans (s3.trans (s2.trans (s1)))
  have hH' : Mal.Hp F Wl fb hi (m + B) (VR V X.cpu.gpr) :=
    Mal.Hp.mv hH (by omega) fun a _ a2 => hVo a (.inl (by omega))
  refine ur2_ok (Pn := PnH F Wl fb hi m X.cpu.gpr V) (Pd := Pd) c hin hinN hinT hT hinD hD hK hA hrip (by
      omega) (Nat.le_of_lt hp8)
    (hfw _ 8 tn8 (by omega) (by omega)) (hfw _ 16 tn16 (by omega) (by omega)) (hfw _ 24 tn24 (by omega)
        (by omega)) (hfw _ 32 tn32 (by omega) (by omega))
    hl fr0 fw0 fw8 fw12 hq hd hin₂ h₂ kt ?_
    (fun Zn V₁ hP => by
      obtain ⟨-, -, h3, h4, -, -⟩ := hP
      refine ⟨fun i hi4 => ?_, by omega, .inl (by omega)⟩
      have e := toNat_add_of_fits (a := Zn.cpu.gpr.rax) (i := i) (n := 4) hi4 (by omega)
      exact (h4 _ (by rw [e]; omega) (by rw [e]; omega)).1) kd kr0 kr1
  intro Y t' hKY hAY hrY hgY k
  have hYs : Y.cpu.gpr.rsp = X.cpu.gpr.rsp - 32 := by rw [hgY]; try rfl
  have hYd : Y.cpu.gpr.rdi = zl X.cpu.gpr * 4#64 + 4#64 := by rw [hgY]; try rfl
  have hYb : Y.cpu.gpr.rbx = X.cpu.gpr.rdi := by rw [hgY]; try rfl
  have hYp : Y.cpu.gpr.rbp = zl X.cpu.gpr := by rw [hgY]; try rfl
  have hYt : Y.cpu.gpr.rsp.toNat = X.cpu.gpr.rsp.toNat - 32 := by rw [hYs, tn32]
  have hra' : rdq(VR V X.cpu.gpr, Y.cpu.gpr.rsp) = ur2_at.add 40 := by
    rw [hYs, Tun.rd_Vst_self (VN V X.cpu.gpr) (X.cpu.gpr.rsp - 32) (toBytesLE (ur2_at.add 40) 8) (l8 _)
      (by rw [tn32]; omega), ofBytesLE_toBytesLE (by rfl : (64 : Nat) = 8 * 8)]
  refine Onw.onw_pnW (B := B) (m := m) (n := 4 * (BitVec.setWidth 32 X.cpu.gpr.rsi).toNat + 4) c hfs hinN hinM
    hinI hKY hAY hrY hH' (by rw [hYd]; exact hz) (by omega) (by rw [hYd]; exact hB) (by rw [hYt]; omega)
    (by rw [hYt]; omega) (fun a h1 h2 => hsw a h1 (by rw [hYt] at h2; omega)) hin (j := 40) (lt_len (by decide)) hra' ?_
  intro Z V₂ t'' hKZ hAZ hrZ zsp zbx zbp _ _ _ _ hP
  rw [hYt] at hP
  have hsv : Sv (VN V X.cpu.gpr) X.cpu.gpr (e₂.add j₂) := Ura.sv3 (by omega) (Nat.le_of_lt hp8) hra
  obtain ⟨v24, v16, v8, v0⟩ := hsv
  have hrd : ∀ (x : Addr) (dx : Nat), x.toNat = X.cpu.gpr.rsp.toNat - dx → dx ≤ 24 →
      rdq(V₂, x) = rdq(VN V X.cpu.gpr, x) := fun x dx hx hdx => by
    rw [Sbrk.rd_eq (V := VN V X.cpu.gpr) (V' := V₂) (x := x) (n := 8) (by omega) fun a a1 a2 =>
      (hP.2.2.2.2.2 a (.inr (.inr (by omega)))).trans (Tun.Vst_out (VN V X.cpu.gpr) (X.cpu.gpr.rsp - 32)
        (toBytesLE (ur2_at.add 40) 8) a (by rw [l8, tn32]; omega) (.inr (by rw [l8, tn32]; omega)))]
  have zsp' : Z.cpu.gpr.rsp = X.cpu.gpr.rsp - 24 := by
    rw [zsp, hYs]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, tn32, tn24]
    simp <;> omega
  exact k Z V₂ t'' hKZ hAZ hrZ zsp' (zbx.trans hYb) (zbp.trans hYp)
    ⟨(hrd _ 24 tn24 (by omega)).trans v24, (hrd _ 16 tn16 (by omega)).trans v16,
      (hrd _ 8 tn8 (by omega)).trans v8, (hrd _ 0 (by omega) (by omega)).trans v0⟩ hP

end FV7z.Ur2
