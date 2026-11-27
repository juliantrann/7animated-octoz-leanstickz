import FV7z.Uau.Holds
/-!
# `UString::operator= (const UString &s)` with `operator new` (PLAN.md §M, M1)

`uau_ok` takes the call of `operator new (4 len + 4)` (`len` = `s._len`, when it is above `_limit`) as a
hypothesis (`kn`); `uau_okH` discharges it by `Onw.onw_hpWT`, with `Mal.MalB (4 len + 4) B`, `Mal.Hp` with a top of
at least `m + B` bytes below `hi` at the entry, `hi` 280 bytes below `rsp` and `[hi, rsp)` in what the run may store
into. The post of `operator new` is `PnH`; `delete []` (`kd`), the three ways to `wmemcpy` (`kmA`, `km0`, `km1`)
and the return (`kr`, `kself`) stay hypotheses.

- `PnH`: the block `rax` (16 above the old top `main_arena.top` or more, `4 len + 4` bytes below `hi`, in the
  footprint, above the TLS block's words), `Mal.Hp … m` for the bytes outside it, and the bytes outside the heap's
  words and the block, from the frame (`rsp - 48`) up, as at `operator new`'s entry (`VN`).
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
open FV7z.Imm (imm imm_at)
open FV7z.Mnx (mnx mnx_at)
namespace FV7z.Uau

variable {F : Footprint} {Wl : List Rgn} {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {X : State} {t : Nat} {V : Addr → Byte}

/-- The bytes at `operator new`'s entry: the return address `uau_at + 87` pushed below the frame. -/
abbrev VN (V : Addr → Byte) (g : Gprs) : Addr → Byte := Vst (V0 V g) (g.rsp - 48) (toBytesLE (uau_at.add 87) 8)

/-- The post of `operator new` for the registers `g` and the bytes `V` at the entry: see the module doc. -/
abbrev PnH (F : Footprint) (Wl : List Rgn) (fb : Addr) (hi m : Nat) (g : Gprs) (V : Addr → Byte) (Z : State)
    (V₁ : Addr → Byte) : Prop :=
  rdq(V, 7940768#64).toNat + 16 ≤ Z.cpu.gpr.rax.toNat ∧ fb.toNat + 64 ≤ Z.cpu.gpr.rax.toNat ∧
    Z.cpu.gpr.rax.toNat + (4 * (sln V g).toNat + 4) ≤ hi ∧
    (∀ a : Addr, Z.cpu.gpr.rax.toNat ≤ a.toNat → a.toNat < Z.cpu.gpr.rax.toNat + (4 * (sln V g).toNat + 4) →
      Foot Wl a ∧ Foot F.data a) ∧
    (∀ W : Addr → Byte, (∀ a : Addr, 7940480 ≤ a.toNat → a.toNat < hi →
      (a.toNat < Z.cpu.gpr.rax.toNat ∨ Z.cpu.gpr.rax.toNat + (4 * (sln V g).toNat + 4) ≤ a.toNat) →
      W a = V₁ a) →
      Mal.Hp F Wl fb hi m W) ∧
    (∀ a : Addr, (a.toNat < 7940768 ∨ 7940776 ≤ a.toNat ∧ a.toNat + 8 < Z.cpu.gpr.rax.toNat ∨
      g.rsp.toNat - 48 ≤ a.toNat) → V₁ a = VN V g a)

set_option maxHeartbeats 1000000 in
/-- `uau_ok` with `operator new` by `Onw.onw_hpWT`: see the module doc. -/
theorem uau_okH {Pd : State → State → (Addr → Byte) → Prop} {Pw : State → State → (Addr → Byte) → Prop}
    {fb : Addr} {hi m B : Nat}
    (c : Seg prof F Wl L s₀ o) (hfs : s₀.cpu.seg.fsBase = fb) (hin : CodeIn L uau_at uau)
    (hinN : CodeIn L Onw.onw_at Onw.onw) (hinM : CodeIn L mnx_at mnx) (hinI : CodeIn L imm_at imm)
    (hinW : CodeIn L Wmc.wmc_at Wmc.wmc) {codeD : List Byte} (hinD : CodeIn L 0x6014f0#64 codeD)
    (hD : 0 < codeD.length)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = uau_at)
    (hH : Mal.Hp F Wl fb hi (m + B) V) (hB : Mal.MalB (zl (sln V X.cpu.gpr) * 4#64 + 4#64) B)
    (hhi : hi + 280 ≤ X.cpu.gpr.rsp.toNat) (hp8 : X.cpu.gpr.rsp.toNat + 8 ≤ 2 ^ 64)
    (hsw : ∀ a : Addr, hi ≤ a.toNat → a.toNat < X.cpu.gpr.rsp.toNat → Foot Wl a)
    (hl : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsp i))
    (fd0 : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rdi i))
    (fd12 : ∀ i < 4, Foot F.data (Addr.add (X.cpu.gpr.rdi + 12#64) i))
    (fw0 : ∀ i < 8, Foot Wl (Addr.add X.cpu.gpr.rdi i))
    (fw8 : ∀ i < 4, Foot Wl (Addr.add (X.cpu.gpr.rdi + 8#64) i))
    (fw12 : ∀ i < 4, Foot Wl (Addr.add (X.cpu.gpr.rdi + 12#64) i))
    (fs0 : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsi i))
    (fs8 : ∀ i < 4, Foot F.data (Addr.add (X.cpu.gpr.rsi + 8#64) i))
    (hqd : X.cpu.gpr.rdi.toNat + 16 ≤ 2 ^ 64) (hqs : X.cpu.gpr.rsi.toNat + 16 ≤ 2 ^ 64)
    (hdd : X.cpu.gpr.rdi.toNat + 16 ≤ X.cpu.gpr.rsp.toNat - 32 ∨ X.cpu.gpr.rsp.toNat ≤ X.cpu.gpr.rdi.toNat)
    (hds : X.cpu.gpr.rsi.toNat + 16 ≤ X.cpu.gpr.rsp.toNat - 32 ∨ X.cpu.gpr.rsp.toNat ≤ X.cpu.gpr.rsi.toNat)
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (hra : rdq(V, X.cpu.gpr.rsp) = e₂.add j₂)
    (kself : X.cpu.gpr.rsi = X.cpu.gpr.rdi → ∀ (Z' : State) (t' : Nat), KeptW Wl s₀ Z' →
      Agree F Z'.proc.mm.mem (V0 V X.cpu.gpr) → Z'.cpu.rip = e₂.add j₂ →
      Z'.cpu.gpr = { X.cpu.gpr with rax := X.cpu.gpr.rdi, rsp := X.cpu.gpr.rsp + 8 } →
      GoG prof L o gev gP gE Z' t')
    (kd : ∀ (Zn : State) (V₁ : Addr → Byte), PnH F Wl fb hi m X.cpu.gpr V Zn V₁ →
      rdq(V₁, X.cpu.gpr.rdi) ≠ 0 →
      ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y →
      Agree F Y.proc.mm.mem (Vst V₁ (X.cpu.gpr.rsp - 48) (toBytesLE (uau_at.add 104) 8)) →
      Y.cpu.rip = 0x6014f0#64 →
      Y.cpu.gpr = { Zn.cpu.gpr with rdi := rdq(V₁, X.cpu.gpr.rdi), r13 := Zn.cpu.gpr.rax }.set 4
        (X.cpu.gpr.rsp - 48) →
      (∀ (Zd : State) (V₃ : Addr → Byte) (t'' : Nat), KeptW Wl s₀ Zd → Agree F Zd.proc.mm.mem V₃ →
        Zd.cpu.rip = uau_at.add 104 → Zd.cpu.gpr.rsp = X.cpu.gpr.rsp - 40 → Zd.cpu.gpr.r12 = X.cpu.gpr.rdi →
        Zd.cpu.gpr.rbx = X.cpu.gpr.rsi → Zd.cpu.gpr.rbp = zl (sln V X.cpu.gpr) →
        Zd.cpu.gpr.r13 = Zn.cpu.gpr.rax → Pd Zn Zd V₃ → GoG prof L o gev gP gE Zd t'') →
      GoG prof L o gev gP gE Y t')
    (kmA : X.cpu.gpr.rsi ≠ X.cpu.gpr.rdi → ¬ (tlm V X.cpu.gpr).toNat < (sln V X.cpu.gpr).toNat →
      Kc prof L o gev gP gE F Wl s₀ X.cpu.gpr (e₂.add j₂) (sln V X.cpu.gpr) Pw (gA X.cpu.gpr V) (V0 V X.cpu.gpr))
    (km0 : ∀ (Zn : State) (V₁ : Addr → Byte), PnH F Wl fb hi m X.cpu.gpr V Zn V₁ →
      rdq(V₁, X.cpu.gpr.rdi) = 0 →
      Kc prof L o gev gP gE F Wl s₀ X.cpu.gpr (e₂.add j₂) (sln V X.cpu.gpr) Pw
        { Zn.cpu.gpr with rdi := rdq(V₁, X.cpu.gpr.rdi), r13 := Zn.cpu.gpr.rax }
        (VB V₁ X.cpu.gpr.rdi Zn.cpu.gpr.rax (sln V X.cpu.gpr)))
    (km1 : ∀ (Zn Zd : State) (V₃ : Addr → Byte), Pd Zn Zd V₃ →
      Kc prof L o gev gP gE F Wl s₀ X.cpu.gpr (e₂.add j₂) (sln V X.cpu.gpr) Pw Zd.cpu.gpr
        (VB V₃ X.cpu.gpr.rdi Zn.cpu.gpr.rax (sln V X.cpu.gpr)))
    (kr : ∀ (Y Zw : State) (V₂ : Addr → Byte) (Z' : State) (t' : Nat), Pw Y Zw V₂ → KeptW Wl s₀ Z' →
      Agree F Z'.proc.mm.mem V₂ → Z'.cpu.rip = e₂.add j₂ → Z'.cpu.gpr = gR Zw.cpu.gpr X.cpu.gpr →
      GoG prof L o gev gP gE Z' t') :
    GoG prof L o gev gP gE X t := by
  have hlt := X.cpu.gpr.rsp.isLt
  have hTl : 8032256 ≤ hi ∧ hi < 2 ^ 64 := by
    obtain ⟨_, T, _, _, _, -, -, -, -, hT, hTh, hhi', -⟩ := hH
    omega
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
  have l8 : ∀ x : BitVec 64, (toBytesLE x 8).length = 8 := fun x => toBytesLE_length _ _
  have hfw : ∀ (x : Addr) (d : Nat), x.toNat = X.cpu.gpr.rsp.toNat - d → 8 ≤ d → d ≤ 48 →
      ∀ i < 8, Foot Wl (Addr.add x i) := fun x d hx h1 h2 i hi' => by
    have e := toNat_add_of_fits (a := x) (i := i) (n := 8) hi' (by rw [hx]; omega)
    exact hsw _ (by rw [e, hx]; omega) (by rw [e, hx]; omega)
  have hz : (zl (sln V X.cpu.gpr) * 4#64 + 4#64).toNat = 4 * (sln V X.cpu.gpr).toNat + 4 := by
    have := (sln V X.cpu.gpr).isLt
    show (BitVec.setWidth 64 (sln V X.cpu.gpr) * 4#64 + 4#64).toNat = _
    rw [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    omega
  -- the bytes at `operator new`'s entry outside the frame
  have hVo : ∀ a : Addr, (a.toNat < X.cpu.gpr.rsp.toNat - 48 ∨ X.cpu.gpr.rsp.toNat ≤ a.toNat) →
      VN V X.cpu.gpr a = V a := by
    intro a h1
    have s0 := Tun.Vst_out (V0 V X.cpu.gpr) (X.cpu.gpr.rsp - 48) (toBytesLE (uau_at.add 87) 8) a
      (by rw [l8, tn48]; omega) (by rw [l8, tn48]; omega)
    have s1 := Tun.Vst_out (Vst (Vst (Vst V (X.cpu.gpr.rsp - 8) (toBytesLE X.cpu.gpr.r13 8)) (X.cpu.gpr.rsp - 8 - 8)
      (toBytesLE X.cpu.gpr.r12 8)) (X.cpu.gpr.rsp - 8 - 8 - 8) (toBytesLE X.cpu.gpr.rbp 8))
      (X.cpu.gpr.rsp - 8 - 8 - 8 - 8) (toBytesLE X.cpu.gpr.rbx 8) a (by rw [l8, u4]; omega) (by rw [l8, u4]; omega)
    have s2 := Tun.Vst_out (Vst (Vst V (X.cpu.gpr.rsp - 8) (toBytesLE X.cpu.gpr.r13 8)) (X.cpu.gpr.rsp - 8 - 8)
      (toBytesLE X.cpu.gpr.r12 8)) (X.cpu.gpr.rsp - 8 - 8 - 8) (toBytesLE X.cpu.gpr.rbp 8) a
      (by rw [l8, u3]; omega) (by rw [l8, u3]; omega)
    have s3 := Tun.Vst_out (Vst V (X.cpu.gpr.rsp - 8) (toBytesLE X.cpu.gpr.r13 8)) (X.cpu.gpr.rsp - 8 - 8)
      (toBytesLE X.cpu.gpr.r12 8) a (by rw [l8, u2]; omega) (by rw [l8, u2]; omega)
    have s4 := Tun.Vst_out V (X.cpu.gpr.rsp - 8) (toBytesLE X.cpu.gpr.r13 8) a (by rw [l8, tn8]; omega)
      (by rw [l8, tn8]; omega)
    exact s0.trans (s1.trans (s2.trans (s3.trans s4)))
  have hH' : Mal.Hp F Wl fb hi (m + B) (VN V X.cpu.gpr) :=
    Mal.Hp.mv hH (by omega) fun a _ a2 => hVo a (.inl (by omega))
  have hTop : rdq(VN V X.cpu.gpr, 7940768#64) = rdq(V, 7940768#64) := by
    have et : (7940768#64 : Addr).toNat = 7940768 := rfl
    rw [Sbrk.rd_eq (V := V) (x := 7940768#64) (n := 8) (by rw [et]; omega) fun a _ a2 =>
      hVo a (.inl (by rw [et] at a2; omega))]
  refine uau_ok (Pn := PnH F Wl fb hi m X.cpu.gpr V) (Pd := Pd) (Pw := Pw) c hin hinN hinW hinD hD hK hA hrip
    (by omega) hp8 (hfw _ 8 tn8 (by omega) (by omega)) (hfw _ 16 tn16 (by omega) (by omega))
    (hfw _ 24 tn24 (by omega) (by omega)) (hfw _ 32 tn32 (by omega) (by omega)) (hfw _ 48 tn48 (by omega) (by omega))
    hl fd0 fd12 fw0 fw8 fw12 fs0 fs8 hqd hqs hdd hds hin₂ h₂ hra kself ?_ kd kmA km0 km1 kr
  intro Y t' _ _ hKY hAY hrY hgY k
  have hYs : Y.cpu.gpr.rsp = X.cpu.gpr.rsp - 48 := by rw [hgY]; try rfl
  have hYd : Y.cpu.gpr.rdi = zl (sln V X.cpu.gpr) * 4#64 + 4#64 := by rw [hgY]; try rfl
  have hYb : Y.cpu.gpr.rbx = X.cpu.gpr.rsi := by rw [hgY]; try rfl
  have hYp : Y.cpu.gpr.rbp = zl (sln V X.cpu.gpr) := by rw [hgY]; try rfl
  have hY12 : Y.cpu.gpr.r12 = X.cpu.gpr.rdi := by rw [hgY]; try rfl
  have hYt : Y.cpu.gpr.rsp.toNat = X.cpu.gpr.rsp.toNat - 48 := by rw [hYs, tn48]
  have hra' : rdq(VN V X.cpu.gpr, Y.cpu.gpr.rsp) = uau_at.add 87 := by
    rw [hYs, Tun.rd_Vst_self (V0 V X.cpu.gpr) (X.cpu.gpr.rsp - 48) (toBytesLE (uau_at.add 87) 8) (l8 _)
      (by rw [tn48]; omega), ofBytesLE_toBytesLE (by rfl : (64 : Nat) = 8 * 8)]
  refine Onw.onw_hpWT (B := B) (m := m) c hfs hinN hinM hinI hKY hAY hrY hH'
    (by rw [hYd]; intro h; have := congrArg BitVec.toNat h; rw [hz] at this; simp at this)
    (by rw [hYd]; exact hB) (by rw [hYt]; omega) (by rw [hYt]; omega)
    (fun a h1 h2 => hsw a h1 (by rw [hYt] at h2; omega)) hin (j := 87) (by decide) hra' ?_
  intro Z t'' V₂ p hKZ hAZ hrZ zsp zax zbx zbp z12 _ _ _ _ hpf hpe hfoot hV hPm hT
  rw [hYd, hz] at hpe hfoot hPm
  rw [hTop] at hT
  refine k Z V₂ t'' hKZ hAZ hrZ ?_ (by rw [z12, hY12]) (by rw [zbx, hYb]) (by rw [zbp, hYp])
    ⟨by rw [zax]; exact hT, by rw [zax]; exact hpf, by rw [zax]; omega, by rw [zax]; exact hfoot,
      by rw [zax]; exact hPm, ?_⟩
  · rw [zsp, hYs]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, tn48, tn40]
    simp <;> omega
  · intro a h1
    rw [zax] at h1
    rcases h1 with h1 | h1 | h1
    · exact hV a (.inl h1)
    · exact hV a (.inr (.inl h1))
    · exact hV a (.inr (.inr ⟨by omega, .inr (by rw [hYt]; exact h1)⟩))

end FV7z.Uau
