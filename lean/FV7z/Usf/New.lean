import FV7z.Usf.Holds
import FV7z.OnwP
/-!
# `UString::SetFrom (s, len)` with `operator new` (PLAN.md §M, M1)

`usf_ok` takes the call of `operator new (4 n + 4)` as a hypothesis (`kn`); `usf_okH` discharges it
by `Onw.onw_pnW`, with `Mal.MalB (4 n + 4) B`, `Mal.Hp` with a top of at least `m + B` bytes below `hi` at the entry,
`hi` 280 bytes below `rsp` and `[hi, rsp)` in what the run may store into. The post of `operator new` is `PnH`
(`Onw.PnW` from the bytes `VR` at its entry, `rsp - 48` up); the other callees stay hypotheses.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
open FV7z.Imm (imm imm_at)
open FV7z.Mnx (mnx mnx_at)
open FV7z.Uau (zl)
namespace FV7z.Usf

variable {F : Footprint} {Wl : List Rgn} {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {X : State} {t : Nat} {V : Addr → Byte}

/-- The bytes at `operator new`'s entry: the return address `usf_at + 108` pushed below the saved registers. -/
abbrev VR (V : Addr → Byte) (g : Gprs) : Addr → Byte := Vst (V5 V g) (g.rsp - 48) (toBytesLE (usf_at.add 108) 8)

/-- The post of `operator new` for the registers `g` and the bytes `V` at the entry: see the module doc. -/
abbrev PnH (F : Footprint) (Wl : List Rgn) (fb : Addr) (hi m : Nat) (g : Gprs) (V : Addr → Byte) :
    State → (Addr → Byte) → Prop :=
  Onw.PnW F Wl fb hi m (VR V g) (4 * (lnd g).toNat + 4) (g.rsp.toNat - 48)

set_option maxHeartbeats 1000000 in
/-- `usf_ok` with `operator new` by `Onw.onw_pnW`: see the module doc. -/
theorem usf_okH {Pd : State → State → (Addr → Byte) → Prop} {Pw : State → State → (Addr → Byte) → Prop}
    {fb : Addr} {hi m B : Nat}
    (c : Seg prof F Wl L s₀ o) (hin : CodeIn L usf_at usf) (hinN : CodeIn L Onw.onw_at Onw.onw)
    (hinW : CodeIn L Wmc.wmc_at Wmc.wmc) {codeD : List Byte} (hinD : CodeIn L 0x6014f0#64 codeD)
    (hD : 0 < codeD.length) {codeT : List Byte} (hinT : CodeIn L 0x40140c#64 codeT) (hT : 0 < codeT.length)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = usf_at)
    (hfs : s₀.cpu.seg.fsBase = fb) (hinM : CodeIn L mnx_at mnx) (hinI : CodeIn L imm_at imm)
    (hH : Mal.Hp F Wl fb hi (m + B) V) (hB : Mal.MalB (zl (lnd X.cpu.gpr) * 4#64 + 4#64) B)
    (hhi : hi + 280 ≤ X.cpu.gpr.rsp.toNat)
    (hsw : ∀ a : Addr, hi ≤ a.toNat → a.toNat < X.cpu.gpr.rsp.toNat → Foot Wl a)
    (hp8 : X.cpu.gpr.rsp.toNat + 8 ≤ 2 ^ 64)
    (hl : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsp i))
    (fd0 : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rdi i))
    (fd12 : ∀ i < 4, Foot F.data (Addr.add (X.cpu.gpr.rdi + 12#64) i))
    (fw0 : ∀ i < 8, Foot Wl (Addr.add X.cpu.gpr.rdi i))
    (fw8 : ∀ i < 4, Foot Wl (Addr.add (X.cpu.gpr.rdi + 8#64) i))
    (fw12 : ∀ i < 4, Foot Wl (Addr.add (X.cpu.gpr.rdi + 12#64) i))
    (hqd : X.cpu.gpr.rdi.toNat + 16 ≤ 2 ^ 64)
    (hdd : X.cpu.gpr.rdi.toNat + 16 ≤ X.cpu.gpr.rsp.toNat - 40 ∨ X.cpu.gpr.rsp.toNat ≤ X.cpu.gpr.rdi.toNat)
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (hra : rdq(V, X.cpu.gpr.rsp) = e₂.add j₂)
    (hz4 : lnd X.cpu.gpr = 0 → Zs Wl X.cpu.gpr (rdq(V, X.cpu.gpr.rdi) + zl (lnd X.cpu.gpr) * 4#64))
    (kt : ∀ (Y : State) (t' : Nat), (tlm V X.cpu.gpr).toNat < (lnd X.cpu.gpr).toNat →
      1073741822 < (lnd X.cpu.gpr).toNat → KeptW Wl s₀ Y → Agree F Y.proc.mm.mem (V5 V X.cpu.gpr) →
      Y.cpu.rip = 0x40140c#64 → Y.cpu.gpr = g5 X.cpu.gpr → GoG prof L o gev gP gE Y t')
    (kd : ∀ (Zn : State) (V₁ : Addr → Byte), PnH F Wl fb hi m X.cpu.gpr V Zn V₁ → rdq(V₁, X.cpu.gpr.rdi) ≠ 0 →
      ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y →
      Agree F Y.proc.mm.mem (Vst V₁ (X.cpu.gpr.rsp - 48) (toBytesLE (usf_at.add 125) 8)) →
      Y.cpu.rip = 0x6014f0#64 →
      Y.cpu.gpr = { Zn.cpu.gpr with rdi := rdq(V₁, X.cpu.gpr.rdi), r12 := Zn.cpu.gpr.rax }.set 4
        (X.cpu.gpr.rsp - 48) →
      (∀ (Zd : State) (V₃ : Addr → Byte) (t'' : Nat), KeptW Wl s₀ Zd → Agree F Zd.proc.mm.mem V₃ →
        Zd.cpu.rip = usf_at.add 125 → Zd.cpu.gpr.rsp = X.cpu.gpr.rsp - 40 → Zd.cpu.gpr.rbp = X.cpu.gpr.rdi →
        Zd.cpu.gpr.rbx = zl (lnd X.cpu.gpr) → Zd.cpu.gpr.r12 = Zn.cpu.gpr.rax → Pd Zn Zd V₃ →
        GoG prof L o gev gP gE Zd t'') →
      GoG prof L o gev gP gE Y t')
    (kmA : lnd X.cpu.gpr ≠ 0 → ¬ (tlm V X.cpu.gpr).toNat < (lnd X.cpu.gpr).toNat →
      Kc prof L o gev gP gE F Wl s₀ X.cpu.gpr (e₂.add j₂) (lnd X.cpu.gpr) Pw
        (gA X.cpu.gpr (rdq(V, X.cpu.gpr.rdi))) (V5 V X.cpu.gpr))
    (km0 : ∀ (Zn : State) (V₁ : Addr → Byte), PnH F Wl fb hi m X.cpu.gpr V Zn V₁ → rdq(V₁, X.cpu.gpr.rdi) = 0 →
      Kc prof L o gev gP gE F Wl s₀ X.cpu.gpr (e₂.add j₂) (lnd X.cpu.gpr) Pw
        { Zn.cpu.gpr with rdi := rdq(V₁, X.cpu.gpr.rdi), r12 := Zn.cpu.gpr.rax }
        (VB V₁ X.cpu.gpr.rdi Zn.cpu.gpr.rax (lnd X.cpu.gpr)))
    (km1 : ∀ (Zn Zd : State) (V₃ : Addr → Byte), Pd Zn Zd V₃ →
      Kc prof L o gev gP gE F Wl s₀ X.cpu.gpr (e₂.add j₂) (lnd X.cpu.gpr) Pw Zd.cpu.gpr
        (VB V₃ X.cpu.gpr.rdi Zn.cpu.gpr.rax (lnd X.cpu.gpr)))
    (kr0 : lnd X.cpu.gpr = 0 → ∀ (Z' : State) (t' : Nat), KeptW Wl s₀ Z' →
      Agree F Z'.proc.mm.mem (VF (V5 V X.cpu.gpr) (rdq(V, X.cpu.gpr.rdi)) X.cpu.gpr.rdi (lnd X.cpu.gpr)) →
      Z'.cpu.rip = e₂.add j₂ → Z'.cpu.gpr = gR (gA X.cpu.gpr (rdq(V, X.cpu.gpr.rdi))) X.cpu.gpr →
      GoG prof L o gev gP gE Z' t')
    (kr1 : ∀ (Y Zw : State) (V₂ : Addr → Byte) (Z' : State) (t' : Nat), Pw Y Zw V₂ → KeptW Wl s₀ Z' →
      Agree F Z'.proc.mm.mem (VF V₂ (rdq(V₂, X.cpu.gpr.rdi)) X.cpu.gpr.rdi (lnd X.cpu.gpr)) →
      Z'.cpu.rip = e₂.add j₂ → Z'.cpu.gpr = gR { Zw.cpu.gpr with r12 := rdq(V₂, X.cpu.gpr.rdi) } X.cpu.gpr →
      GoG prof L o gev gP gE Z' t') :
    GoG prof L o gev gP gE X t := by
  have hlt := X.cpu.gpr.rsp.isLt
  have hB3 : 64 ≤ B := hB.2.2
  have tn8 : (X.cpu.gpr.rsp - 8).toNat = X.cpu.gpr.rsp.toNat - 8 := by rw [BitVec.toNat_sub]; simp <;> omega
  have tn16 : (X.cpu.gpr.rsp - 16).toNat = X.cpu.gpr.rsp.toNat - 16 := by rw [BitVec.toNat_sub]; simp <;> omega
  have tn24 : (X.cpu.gpr.rsp - 24).toNat = X.cpu.gpr.rsp.toNat - 24 := by rw [BitVec.toNat_sub]; simp <;> omega
  have tn32 : (X.cpu.gpr.rsp - 32).toNat = X.cpu.gpr.rsp.toNat - 32 := by rw [BitVec.toNat_sub]; simp <;> omega
  have tn40 : (X.cpu.gpr.rsp - 40).toNat = X.cpu.gpr.rsp.toNat - 40 := by rw [BitVec.toNat_sub]; simp <;> omega
  have tn48 : (X.cpu.gpr.rsp - 48).toNat = X.cpu.gpr.rsp.toNat - 48 := by rw [BitVec.toNat_sub]; simp <;> omega
  have u2 : (X.cpu.gpr.rsp - 8 - 8).toNat = X.cpu.gpr.rsp.toNat - 16 := by
    rw [BitVec.toNat_sub, tn8]; simp <;> omega
  have u3 : (X.cpu.gpr.rsp - 8 - 8 - 8).toNat = X.cpu.gpr.rsp.toNat - 24 := by
    rw [BitVec.toNat_sub, u2]; simp <;> omega
  have u4 : (X.cpu.gpr.rsp - 8 - 8 - 8 - 8).toNat = X.cpu.gpr.rsp.toNat - 32 := by
    rw [BitVec.toNat_sub, u3]; simp <;> omega
  have u5 : (X.cpu.gpr.rsp - 8 - 8 - 8 - 8 - 8).toNat = X.cpu.gpr.rsp.toNat - 40 := by
    rw [BitVec.toNat_sub, u4]; simp <;> omega
  have l8 : ∀ x : BitVec 64, (toBytesLE x 8).length = 8 := fun x => toBytesLE_length _ _
  have hfw : ∀ (x : Addr) (d : Nat), x.toNat = X.cpu.gpr.rsp.toNat - d → 8 ≤ d → d ≤ 48 →
      ∀ i < 8, Foot Wl (Addr.add x i) := fun x d hx h1 h2 i hi' => by
    have e := toNat_add_of_fits (a := x) (i := i) (n := 8) hi' (by rw [hx]; omega)
    exact hsw _ (by rw [e, hx]; omega) (by rw [e, hx]; omega)
  have hz : (zl (lnd X.cpu.gpr) * 4#64 + 4#64).toNat = 4 * (lnd X.cpu.gpr).toNat + 4 := by
    have := (lnd X.cpu.gpr).isLt
    show (BitVec.setWidth 64 (lnd X.cpu.gpr) * 4#64 + 4#64).toNat = _
    rw [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    omega
  -- the bytes at `operator new`'s entry outside the frame
  have hVo : ∀ a : Addr, (a.toNat < X.cpu.gpr.rsp.toNat - 48 ∨ X.cpu.gpr.rsp.toNat ≤ a.toNat) →
      VR V X.cpu.gpr a = V a := by
    intro a h1
    have s0 := Tun.Vst_out (Vst (Vst (Vst (Vst (Vst (V) (X.cpu.gpr.rsp - 8) (toBytesLE X.cpu.gpr.r14 8))
        (X.cpu.gpr.rsp - 8 - 8) (toBytesLE X.cpu.gpr.r13 8)) (X.cpu.gpr.rsp - 8 - 8 - 8) (toBytesLE X.cpu.gpr.r12 8))
        (X.cpu.gpr.rsp - 8 - 8 - 8 - 8) (toBytesLE X.cpu.gpr.rbp 8)) (X.cpu.gpr.rsp - 8 - 8 - 8 - 8 - 8)
        (toBytesLE X.cpu.gpr.rbx 8)) (X.cpu.gpr.rsp - 48) (toBytesLE (usf_at.add 108) 8) a
      (by rw [l8, tn48]; omega) (by rw [l8, tn48]; omega)
    have s5 := Tun.Vst_out (Vst (Vst (Vst (Vst (V) (X.cpu.gpr.rsp - 8) (toBytesLE X.cpu.gpr.r14 8))
        (X.cpu.gpr.rsp - 8 - 8) (toBytesLE X.cpu.gpr.r13 8)) (X.cpu.gpr.rsp - 8 - 8 - 8) (toBytesLE X.cpu.gpr.r12 8))
        (X.cpu.gpr.rsp - 8 - 8 - 8 - 8) (toBytesLE X.cpu.gpr.rbp 8)) (X.cpu.gpr.rsp - 8 - 8 - 8 - 8 - 8)
        (toBytesLE X.cpu.gpr.rbx 8) a
      (by rw [l8, u5]; omega) (by rw [l8, u5]; omega)
    have s4 := Tun.Vst_out (Vst (Vst (Vst (V) (X.cpu.gpr.rsp - 8) (toBytesLE X.cpu.gpr.r14 8)) (X.cpu.gpr.rsp - 8 - 8)
        (toBytesLE X.cpu.gpr.r13 8)) (X.cpu.gpr.rsp - 8 - 8 - 8) (toBytesLE X.cpu.gpr.r12 8))
        (X.cpu.gpr.rsp - 8 - 8 - 8 - 8) (toBytesLE X.cpu.gpr.rbp 8) a
      (by rw [l8, u4]; omega) (by rw [l8, u4]; omega)
    have s3 := Tun.Vst_out (Vst (Vst (V) (X.cpu.gpr.rsp - 8) (toBytesLE X.cpu.gpr.r14 8)) (X.cpu.gpr.rsp - 8 - 8)
        (toBytesLE X.cpu.gpr.r13 8)) (X.cpu.gpr.rsp - 8 - 8 - 8) (toBytesLE X.cpu.gpr.r12 8) a
      (by rw [l8, u3]; omega) (by rw [l8, u3]; omega)
    have s2 := Tun.Vst_out (Vst (V) (X.cpu.gpr.rsp - 8)
        (toBytesLE X.cpu.gpr.r14 8)) (X.cpu.gpr.rsp - 8 - 8) (toBytesLE X.cpu.gpr.r13 8) a
      (by rw [l8, u2]; omega) (by rw [l8, u2]; omega)
    have s1 := Tun.Vst_out (V) (X.cpu.gpr.rsp - 8) (toBytesLE X.cpu.gpr.r14 8) a
      (by rw [l8, tn8]; omega) (by rw [l8, tn8]; omega)
    exact s0.trans (s5.trans (s4.trans (s3.trans (s2.trans (s1)))))
  have hH' : Mal.Hp F Wl fb hi (m + B) (VR V X.cpu.gpr) :=
    Mal.Hp.mv hH (by omega) fun a _ a2 => hVo a (.inl (by omega))
  refine usf_ok (Pn := PnH F Wl fb hi m X.cpu.gpr V) (Pd := Pd) (Pw :=
      Pw) c hin hinN hinW hinD hD hinT hT hK hA hrip (by omega) hp8
    (hfw _ 8 tn8 (by omega) (by omega)) (hfw _ 16 tn16 (by omega) (by omega)) (hfw _ 24 tn24 (by omega)
        (by omega)) (hfw _ 32 tn32 (by omega) (by omega)) (hfw _ 40 tn40 (by omega) (by omega))
        (hfw _ 48 tn48 (by omega) (by omega))
    hl fd0 fd12 fw0 fw8 fw12 hqd hdd hin₂ h₂ hra hz4 kt ?_ kd kmA km0 km1 kr0 kr1
  intro Y t' _ _ hKY hAY hrY hgY k
  have hYs : Y.cpu.gpr.rsp = X.cpu.gpr.rsp - 48 := by rw [hgY]; try rfl
  have hYd : Y.cpu.gpr.rdi = zl (lnd X.cpu.gpr) * 4#64 + 4#64 := by rw [hgY]; try rfl
  have hYb : Y.cpu.gpr.rbx = zl (lnd X.cpu.gpr) := by rw [hgY]; try rfl
  have hYp : Y.cpu.gpr.rbp = X.cpu.gpr.rdi := by rw [hgY]; try rfl
  have hYt : Y.cpu.gpr.rsp.toNat = X.cpu.gpr.rsp.toNat - 48 := by rw [hYs, tn48]
  have hra' : rdq(VR V X.cpu.gpr, Y.cpu.gpr.rsp) = usf_at.add 108 := by
    rw [hYs, Tun.rd_Vst_self (V5 V X.cpu.gpr) (X.cpu.gpr.rsp - 48) (toBytesLE (usf_at.add 108) 8) (l8 _)
      (by rw [tn48]; omega), ofBytesLE_toBytesLE (by rfl : (64 : Nat) = 8 * 8)]
  refine Onw.onw_pnW (B := B) (m := m) (n := 4 * (lnd X.cpu.gpr).toNat + 4) c hfs hinN hinM
    hinI hKY hAY hrY hH' (by rw [hYd]; exact hz) (by omega) (by rw [hYd]; exact hB) (by rw [hYt]; omega)
    (by rw [hYt]; omega) (fun a h1 h2 => hsw a h1 (by rw [hYt] at h2; omega)) hin (j := 108) (by decide) hra' ?_
  intro Z V₂ t'' hKZ hAZ hrZ zsp zbx zbp _ _ _ _ hP
  rw [hYt] at hP
  have zsp' : Z.cpu.gpr.rsp = X.cpu.gpr.rsp - 40 := by
    rw [zsp, hYs]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, tn48, tn40]
    simp <;> omega
  exact k Z V₂ t'' hKZ hAZ hrZ zsp' (zbp.trans hYp) (zbx.trans hYb) hP

end FV7z.Usf
