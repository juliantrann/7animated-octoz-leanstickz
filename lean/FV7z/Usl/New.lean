import FV7z.Usl.Holds
/-!
# `UString::SetStartLen` with `operator new` (PLAN.md §M, M1)

`usl_ok` takes the call of `operator new (4 len + 4)` as a hypothesis (`kf`); `usl_okH` discharges it by
`Onw.onw_hpW` for every `len` with `Mal.MalB (4 len + 4) B` (so `4 len + 4 ≤ 2 ^ 32`): with `Mal.Hp` with a top of
at least `m + B` bytes below `hi` at the entry, `hi` 264 bytes below `rsp` and `[hi, rsp)` in what the run may store
into, the object apart from the heap's bytes, the run reaches the return address with `_chars` = the block `p`
(`4 len + 4` bytes below `hi` in the footprint, above the TLS block's words), `Mal.Hp … m` for the bytes at the end,
the bytes outside the heap's words, the block, the frame and `_chars` as at the entry.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
open FV7z.Imm (imm imm_at)
open FV7z.Mnx (mnx mnx_at)
namespace FV7z.Usl

variable {F : Footprint} {Wl : List Rgn} {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {X : State} {t : Nat} {V : Addr → Byte}

/-- `4 len + 4` (`len` = `esi`) does not wrap. -/
theorem zl4 (g : Gprs) : (zl g * 4#64 + 4#64).toNat = 4 * (BitVec.setWidth 32 g.rsi).toNat + 4 := by
  have := (BitVec.setWidth 32 g.rsi).isLt
  show (BitVec.setWidth 64 (BitVec.setWidth 32 g.rsi) * 4#64 + 4#64).toNat = _
  rw [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega

set_option maxHeartbeats 1000000 in
/-- `usl_ok` with `operator new` by `Onw.onw_hpW`: see the module doc. -/
theorem usl_okH {fb : Addr} {hi m B : Nat} (c : Seg prof F Wl L s₀ o) (hfs : s₀.cpu.seg.fsBase = fb)
    (hin : CodeIn L usl_at usl) (hinW : CodeIn L Onw.onw_at Onw.onw) (hinM : CodeIn L mnx_at mnx)
    (hinI : CodeIn L imm_at imm) (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = usl_at)
    (hH : Mal.Hp F Wl fb hi (m + B) V) (hB : Mal.MalB (zl X.cpu.gpr * 4#64 + 4#64) B)
    (hhi : hi + 264 ≤ X.cpu.gpr.rsp.toNat) (hp8 : X.cpu.gpr.rsp.toNat + 8 ≤ 2 ^ 64)
    (hR : X.cpu.gpr.rsp.toNat + 8 < 2 ^ 64)
    (hsw : ∀ a : Addr, hi ≤ a.toNat → a.toNat < X.cpu.gpr.rsp.toNat → Foot Wl a)
    (hl : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsp i))
    (fw0 : ∀ i < 8, Foot Wl (Addr.add X.cpu.gpr.rdi i))
    (fw8 : ∀ i < 4, Foot Wl (Addr.add (X.cpu.gpr.rdi + 8#64) i))
    (fw12 : ∀ i < 4, Foot Wl (Addr.add (X.cpu.gpr.rdi + 12#64) i))
    (hq : X.cpu.gpr.rdi.toNat + 16 ≤ 2 ^ 64)
    (hd : X.cpu.gpr.rdi.toNat + 16 ≤ X.cpu.gpr.rsp.toNat - 16 ∨ X.cpu.gpr.rsp.toNat + 8 ≤ X.cpu.gpr.rdi.toNat)
    (hdh : X.cpu.gpr.rdi.toNat + 16 ≤ 7940480 ∨ hi ≤ X.cpu.gpr.rdi.toNat)
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (hra : rdq(V, X.cpu.gpr.rsp) = e₂.add j₂)
    (kr : ∀ (Z : State) (V' : Addr → Byte) (Z' : State) (t' : Nat), fb.toNat + 64 ≤ Z.cpu.gpr.rax.toNat →
      Z.cpu.gpr.rax.toNat + (4 * (BitVec.setWidth 32 X.cpu.gpr.rsi).toNat + 4) ≤ hi →
      (∀ a : Addr, Z.cpu.gpr.rax.toNat ≤ a.toNat →
        a.toNat < Z.cpu.gpr.rax.toNat + (4 * (BitVec.setWidth 32 X.cpu.gpr.rsi).toNat + 4) →
          Foot Wl a ∧ Foot F.data a) →
      Mal.Hp F Wl fb hi m (V1 V' X.cpu.gpr.rdi (BitVec.setWidth 32 X.cpu.gpr.rsi) Z.cpu.gpr.rax) →
      (∀ a : Addr, (a.toNat < 7940768 ∨ 7940776 ≤ a.toNat ∧ a.toNat + 8 < Z.cpu.gpr.rax.toNat ∨
        X.cpu.gpr.rsp.toNat ≤ a.toNat) → (a.toNat < X.cpu.gpr.rdi.toNat ∨ X.cpu.gpr.rdi.toNat + 8 ≤ a.toNat) →
        V' a = V a) →
      KeptW Wl s₀ Z' →
      Agree F Z'.proc.mm.mem (V1 V' X.cpu.gpr.rdi (BitVec.setWidth 32 X.cpu.gpr.rsi) Z.cpu.gpr.rax) →
      Z'.cpu.rip = e₂.add j₂ →
      Z'.cpu.gpr = { Z.cpu.gpr with rbx := X.cpu.gpr.rbx, rbp := X.cpu.gpr.rbp, rsp := X.cpu.gpr.rsp + 8 } →
      GoG prof L o gev gP gE Z' t') :
    GoG prof L o gev gP gE X t := by
  have hlt := X.cpu.gpr.rsp.isLt
  have hTl : 8032256 ≤ hi ∧ hi < 2 ^ 64 := by
    obtain ⟨_, T, _, _, _, -, -, -, -, hT, hTh, hhi', -⟩ := hH
    omega
  have hB3 : 64 ≤ B := hB.2.2
  have hz := zl4 X.cpu.gpr
  have tn8 : (X.cpu.gpr.rsp - 8).toNat = X.cpu.gpr.rsp.toNat - 8 := by rw [BitVec.toNat_sub]; simp <;> omega
  have tn16 : (X.cpu.gpr.rsp - 16).toNat = X.cpu.gpr.rsp.toNat - 16 := by rw [BitVec.toNat_sub]; simp <;> omega
  have tn24 : (X.cpu.gpr.rsp - 24).toNat = X.cpu.gpr.rsp.toNat - 24 := by rw [BitVec.toNat_sub]; simp <;> omega
  have tn32 : (X.cpu.gpr.rsp - 32).toNat = X.cpu.gpr.rsp.toNat - 32 := by rw [BitVec.toNat_sub]; simp <;> omega
  have e16 : X.cpu.gpr.rsp - 8 - 8 = X.cpu.gpr.rsp - 16 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, tn8, tn16]
    simp <;> omega
  have t8 : (X.cpu.gpr.rdi + 8#64).toNat = X.cpu.gpr.rdi.toNat + 8 := by
    rw [BitVec.toNat_add]; simp <;> omega
  have t12 : (X.cpu.gpr.rdi + 12#64).toNat = X.cpu.gpr.rdi.toNat + 12 := by
    rw [BitVec.toNat_add]; simp <;> omega
  have l8 : ∀ x : BitVec 64, (toBytesLE x 8).length = 8 := fun x => toBytesLE_length _ _
  have l4 : ∀ x : BitVec 32, (toBytesLE x 4).length = 4 := fun x => toBytesLE_length _ _
  have hfw : ∀ (x : Addr) (d : Nat), x.toNat = X.cpu.gpr.rsp.toNat - d → 8 ≤ d → d ≤ 32 →
      ∀ i < 8, Foot Wl (Addr.add x i) := fun x d hx h1 h2 i hi' => by
    have e := toNat_add_of_fits (a := x) (i := i) (n := 8) hi' (by rw [hx]; omega)
    exact hsw _ (by rw [e, hx]; omega) (by rw [e, hx]; omega)
  refine usl_ok (Pc := fun Z V' => fb.toNat + 64 ≤ Z.cpu.gpr.rax.toNat ∧
      Z.cpu.gpr.rax.toNat + (4 * (BitVec.setWidth 32 X.cpu.gpr.rsi).toNat + 4) ≤ hi ∧
      (∀ a : Addr, Z.cpu.gpr.rax.toNat ≤ a.toNat →
        a.toNat < Z.cpu.gpr.rax.toNat + (4 * (BitVec.setWidth 32 X.cpu.gpr.rsi).toNat + 4) →
          Foot Wl a ∧ Foot F.data a) ∧
      (∀ W : Addr → Byte, (∀ a : Addr, 7940480 ≤ a.toNat → a.toNat < hi →
        (a.toNat < Z.cpu.gpr.rax.toNat ∨
          Z.cpu.gpr.rax.toNat + (4 * (BitVec.setWidth 32 X.cpu.gpr.rsi).toNat + 4) ≤ a.toNat) → W a = V' a) →
        Mal.Hp F Wl fb hi m W) ∧
      (∀ a : Addr, (a.toNat < 7940768 ∨ 7940776 ≤ a.toNat ∧ a.toNat + 8 < Z.cpu.gpr.rax.toNat ∨
        X.cpu.gpr.rsp.toNat ≤ a.toNat) → (a.toNat < X.cpu.gpr.rdi.toNat ∨ X.cpu.gpr.rdi.toNat + 8 ≤ a.toNat) →
        V' a = V a))
    c hin hinW hK hA hrip (by omega) hp8 (hfw _ 8 tn8 (by omega) (by omega)) (hfw _ 16 tn16 (by omega) (by omega))
    (hfw _ 32 tn32 (by omega) (by omega)) hl fw0 fw8 fw12 hq hd hin₂ h₂ ?_ ?_
  · intro Y t' hKY hAY hrY hgY k
    have hYs : Y.cpu.gpr.rsp = X.cpu.gpr.rsp - 32 := by rw [hgY]; try rfl
    have hYd : Y.cpu.gpr.rdi = zl X.cpu.gpr * 4#64 + 4#64 := by rw [hgY]; try rfl
    have hYb : Y.cpu.gpr.rbx = X.cpu.gpr.rdi := by rw [hgY]; try rfl
    have hYp : Y.cpu.gpr.rbp = zl X.cpu.gpr := by rw [hgY]; try rfl
    have hYt : Y.cpu.gpr.rsp.toNat = X.cpu.gpr.rsp.toNat - 32 := by rw [hYs, tn32]
    -- the bytes at `operator new`'s entry outside the pushes and `_chars`
    have hVo : ∀ a : Addr, (a.toNat < X.cpu.gpr.rsp.toNat - 32 ∨ X.cpu.gpr.rsp.toNat ≤ a.toNat) →
        (a.toNat < X.cpu.gpr.rdi.toNat ∨ X.cpu.gpr.rdi.toNat + 8 ≤ a.toNat) →
        Vst (V0 V X.cpu.gpr) (X.cpu.gpr.rsp - 32) (toBytesLE (usl_at.add 38) 8) a = V a := by
      intro a h1 h2
      have s1 := Tun.Vst_out (V0 V X.cpu.gpr) (X.cpu.gpr.rsp - 32) (toBytesLE (usl_at.add 38) 8) a
        (by rw [l8, tn32]; omega) (by rw [l8, tn32]; omega)
      have s2 := Tun.Vst_out (Vst (Vst V (X.cpu.gpr.rsp - 8) (toBytesLE X.cpu.gpr.rbp 8)) (X.cpu.gpr.rsp - 8 - 8)
        (toBytesLE X.cpu.gpr.rbx 8)) X.cpu.gpr.rdi (toBytesLE 0#64 8) a (by rw [l8]; omega) (by rw [l8]; omega)
      have s3 := Tun.Vst_out (Vst V (X.cpu.gpr.rsp - 8) (toBytesLE X.cpu.gpr.rbp 8)) (X.cpu.gpr.rsp - 8 - 8)
        (toBytesLE X.cpu.gpr.rbx 8) a (by rw [l8, e16, tn16]; omega) (by rw [l8, e16, tn16]; omega)
      have s4 := Tun.Vst_out V (X.cpu.gpr.rsp - 8) (toBytesLE X.cpu.gpr.rbp 8) a (by rw [l8, tn8]; omega)
        (by rw [l8, tn8]; omega)
      exact s1.trans (s2.trans (s3.trans s4))
    have hH' : Mal.Hp F Wl fb hi (m + B)
        (Vst (V0 V X.cpu.gpr) (X.cpu.gpr.rsp - 32) (toBytesLE (usl_at.add 38) 8)) :=
      Mal.Hp.mv hH (by omega) fun a a1 a2 => hVo a (.inl (by omega)) (by rcases hdh with h | h <;> omega)
    have hra' : rdq(Vst (V0 V X.cpu.gpr) (X.cpu.gpr.rsp - 32) (toBytesLE (usl_at.add 38) 8), Y.cpu.gpr.rsp) =
        usl_at.add 38 := by
      rw [hYs, Tun.rd_Vst_self (V0 V X.cpu.gpr) (X.cpu.gpr.rsp - 32) (toBytesLE (usl_at.add 38) 8) (l8 _)
        (by rw [tn32]; omega), ofBytesLE_toBytesLE (by rfl : (64 : Nat) = 8 * 8)]
    refine Onw.onw_hpW (B := B) (m := m) c hfs hinW hinM hinI hKY hAY hrY hH'
      (by rw [hYd]; intro h; have e := congrArg BitVec.toNat h; rw [hz] at e; simp at e)
      (by rw [hYd]; exact hB) (by rw [hYt]; omega) (by rw [hYt]; omega)
      (fun a h1 h2 => hsw a h1 (by rw [hYt] at h2; omega)) hin (lt_len (by decide)) hra' ?_
    intro Z t'' V₂ p hKZ hAZ hrZ zsp zax zbx zbp _ _ _ _ _ hpf hpe hfoot hV hPm
    rw [hYd, hz] at hpe hfoot
    rw [hYd, hz] at hPm
    -- what `operator new` keeps from its return address up
    have hVr : ∀ a : Addr, X.cpu.gpr.rsp.toNat - 32 ≤ a.toNat →
        V₂ a = Vst (V0 V X.cpu.gpr) (X.cpu.gpr.rsp - 32) (toBytesLE (usl_at.add 38) 8) a := fun a ha =>
      hV a (.inr (.inr ⟨by omega, .inr (by rw [hYt]; exact ha)⟩))
    have hb1 : rdq(V₂, X.cpu.gpr.rsp - 16) = X.cpu.gpr.rbx := by
      rw [Sbrk.rd_eq (V := Vst (V0 V X.cpu.gpr) (X.cpu.gpr.rsp - 32) (toBytesLE (usl_at.add 38) 8))
        (x := X.cpu.gpr.rsp - 16) (n := 8) (by rw [tn16]; omega) fun a a1 _ => hVr a (by rw [tn16] at a1; omega)]
      rw [Tun.rd_Vst (V0 V X.cpu.gpr) (X.cpu.gpr.rsp - 32) (toBytesLE (usl_at.add 38) 8) (X.cpu.gpr.rsp - 16) 8
        (by rw [l8, tn32]; omega) (by rw [tn16]; omega) (by rw [l8, tn32, tn16]; omega)]
      rw [Tun.rd_Vst (Vst (Vst V (X.cpu.gpr.rsp - 8) (toBytesLE X.cpu.gpr.rbp 8)) (X.cpu.gpr.rsp - 8 - 8)
        (toBytesLE X.cpu.gpr.rbx 8)) X.cpu.gpr.rdi (toBytesLE 0#64 8) (X.cpu.gpr.rsp - 16) 8 (by rw [l8]; omega)
        (by rw [tn16]; omega) (by rw [l8, tn16]; omega)]
      rw [← e16, Tun.rd_Vst_self (Vst V (X.cpu.gpr.rsp - 8) (toBytesLE X.cpu.gpr.rbp 8)) (X.cpu.gpr.rsp - 8 - 8)
        (toBytesLE X.cpu.gpr.rbx 8) (l8 _) (by rw [e16, tn16]; omega),
        ofBytesLE_toBytesLE (by rfl : (64 : Nat) = 8 * 8)]
    have hb2 : rdq(V₂, X.cpu.gpr.rsp - 8) = X.cpu.gpr.rbp := by
      rw [Sbrk.rd_eq (V := Vst (V0 V X.cpu.gpr) (X.cpu.gpr.rsp - 32) (toBytesLE (usl_at.add 38) 8))
        (x := X.cpu.gpr.rsp - 8) (n := 8) (by rw [tn8]; omega) fun a a1 _ => hVr a (by rw [tn8] at a1; omega)]
      rw [Tun.rd_Vst (V0 V X.cpu.gpr) (X.cpu.gpr.rsp - 32) (toBytesLE (usl_at.add 38) 8) (X.cpu.gpr.rsp - 8) 8
        (by rw [l8, tn32]; omega) (by rw [tn8]; omega) (by rw [l8, tn32, tn8]; omega)]
      rw [Tun.rd_Vst (Vst (Vst V (X.cpu.gpr.rsp - 8) (toBytesLE X.cpu.gpr.rbp 8)) (X.cpu.gpr.rsp - 8 - 8)
        (toBytesLE X.cpu.gpr.rbx 8)) X.cpu.gpr.rdi (toBytesLE 0#64 8) (X.cpu.gpr.rsp - 8) 8 (by rw [l8]; omega)
        (by rw [tn8]; omega) (by rw [l8, tn8]; omega)]
      rw [Tun.rd_Vst (Vst V (X.cpu.gpr.rsp - 8) (toBytesLE X.cpu.gpr.rbp 8)) (X.cpu.gpr.rsp - 8 - 8)
        (toBytesLE X.cpu.gpr.rbx 8) (X.cpu.gpr.rsp - 8) 8 (by rw [l8, e16, tn16]; omega) (by rw [tn8]; omega)
        (by rw [l8, e16, tn16, tn8]; omega)]
      rw [Tun.rd_Vst_self V (X.cpu.gpr.rsp - 8) (toBytesLE X.cpu.gpr.rbp 8) (l8 _) (by rw [tn8]; omega),
        ofBytesLE_toBytesLE (by rfl : (64 : Nat) = 8 * 8)]
    have hr : rdq(V₂, X.cpu.gpr.rsp) = e₂.add j₂ := by
      rw [Sbrk.rd_eq (V := Vst (V0 V X.cpu.gpr) (X.cpu.gpr.rsp - 32) (toBytesLE (usl_at.add 38) 8))
        (x := X.cpu.gpr.rsp) (n := 8) hp8 fun a a1 _ => hVr a (by omega)]
      rw [Tun.rd_Vst (V0 V X.cpu.gpr) (X.cpu.gpr.rsp - 32) (toBytesLE (usl_at.add 38) 8) X.cpu.gpr.rsp 8
        (by rw [l8, tn32]; omega) hp8 (by rw [l8, tn32]; omega)]
      rw [Tun.rd_Vst (Vst (Vst V (X.cpu.gpr.rsp - 8) (toBytesLE X.cpu.gpr.rbp 8)) (X.cpu.gpr.rsp - 8 - 8)
        (toBytesLE X.cpu.gpr.rbx 8)) X.cpu.gpr.rdi (toBytesLE 0#64 8) X.cpu.gpr.rsp 8 (by rw [l8]; omega) hp8
        (by rw [l8]; omega)]
      rw [Tun.rd_Vst (Vst V (X.cpu.gpr.rsp - 8) (toBytesLE X.cpu.gpr.rbp 8)) (X.cpu.gpr.rsp - 8 - 8)
        (toBytesLE X.cpu.gpr.rbx 8) X.cpu.gpr.rsp 8 (by rw [l8, e16, tn16]; omega) hp8
        (by rw [l8, e16, tn16]; omega)]
      rw [Tun.rd_Vst V (X.cpu.gpr.rsp - 8) (toBytesLE X.cpu.gpr.rbp 8) X.cpu.gpr.rsp 8 (by rw [l8, tn8]; omega)
        hp8 (by rw [l8, tn8]; omega)]
      exact hra
    refine k Z V₂ t'' hKZ hAZ hrZ ?_ (by rw [zbx, hYb]) (by rw [zbp, hYp]) hb1 hb2 hr
      ⟨by rw [zax]; exact hpf, by rw [zax]; exact hpe, by rw [zax]; exact hfoot, by rw [zax]; exact hPm, ?_⟩
    · rw [zsp, hYs]
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_add, tn32, tn24]
      simp <;> omega
    · intro a h1 h2
      rw [zax] at h1
      have hva : V₂ a = Vst (V0 V X.cpu.gpr) (X.cpu.gpr.rsp - 32) (toBytesLE (usl_at.add 38) 8) a := by
        rcases h1 with h1 | h1 | h1
        · exact hV a (.inl h1)
        · exact hV a (.inr (.inl h1))
        · exact hVr a (by omega)
      rw [hva]
      exact hVo a (by rcases h1 with h1 | h1 | h1 <;> omega) h2
  · intro Z V' Z' t' ⟨hp1, hp2, hft, hPm, hfr⟩ hKZ' hAZ' hrZ' hgZ'
    refine kr Z V' Z' t' hp1 hp2 hft (hPm _ fun a a1 a2 a3 => ?_) hfr hKZ' hAZ' hrZ' hgZ'
    have s1 := Tun.Vst_out (Vst (Vst V' (X.cpu.gpr.rdi + 8#64) (toBytesLE (BitVec.setWidth 32 X.cpu.gpr.rsi) 4))
      (X.cpu.gpr.rdi + 12#64) (toBytesLE (BitVec.setWidth 32 X.cpu.gpr.rsi) 4)) X.cpu.gpr.rdi
      (toBytesLE Z.cpu.gpr.rax 8) a (by rw [l8]; omega) (by rw [l8]; rcases hdh with h | h <;> omega)
    have s2 := Tun.Vst_out (Vst V' (X.cpu.gpr.rdi + 8#64) (toBytesLE (BitVec.setWidth 32 X.cpu.gpr.rsi) 4))
      (X.cpu.gpr.rdi + 12#64) (toBytesLE (BitVec.setWidth 32 X.cpu.gpr.rsi) 4) a (by rw [l4, t12]; omega)
      (by rw [l4, t12]; rcases hdh with h | h <;> omega)
    have s3 := Tun.Vst_out V' (X.cpu.gpr.rdi + 8#64) (toBytesLE (BitVec.setWidth 32 X.cpu.gpr.rsi) 4) a
      (by rw [l4, t8]; omega) (by rw [l4, t8]; rcases hdh with h | h <;> omega)
    exact s1.trans (s2.trans s3)

end FV7z.Usl
