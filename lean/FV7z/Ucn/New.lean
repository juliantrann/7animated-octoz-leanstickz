import FV7z.Ucn.Holds
import FV7z.Ucw.New
/-!
# `UString::UString (unsigned num, const wchar_t *s)` with `SetStartLen` (PLAN.md §M, M1)

`ucn_ok` takes the call of `SetStartLen (m)` (`m` the smaller of `num` and the length `n` of `s`) as a hypothesis
(`ku`); `ucn_okH` discharges it by `Usl.usl_okH` (so `operator new (4 m + 4)` by `Onw.onw_hpW`), as `Ucw.ucw_okH`
does, with `Mal.MalB (4 m + 4) B` for every such `m`, `hi` 312 bytes below `rsp`, the return address's slot
(`rsp - 48`) in the footprint. The post of `SetStartLen` is `Ucw.Pu` for the length `m`; `wmemcpy` (`kw`) and the
return (`kr`) stay hypotheses.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
open FV7z.Imm (imm imm_at)
open FV7z.Mnx (mnx mnx_at)
namespace FV7z.Ucn
open FV7z.Uau (V0 Sv zl)

variable {F : Footprint} {Wl : List Rgn} {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {X : State} {t : Nat} {V : Addr → Byte}

set_option maxHeartbeats 1000000 in
/-- `ucn_ok` with `SetStartLen` by `Usl.usl_okH`: see the module doc. -/
theorem ucn_okH {Pw : BitVec 32 → State → (Addr → Byte) → Prop} {fb : Addr} {hi m B n : Nat}
    (c : Seg prof F Wl L s₀ o) (hfs : s₀.cpu.seg.fsBase = fb)
    (hin : CodeIn L ucn_at ucn) (hinU : CodeIn L Usl.usl_at Usl.usl) (hinWm : CodeIn L Wmc.wmc_at Wmc.wmc)
    (hinW : CodeIn L Onw.onw_at Onw.onw) (hinN : CodeIn L mnx_at mnx) (hinI : CodeIn L imm_at imm)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = ucn_at)
    (hH : Mal.Hp F Wl fb hi (m + B) V)
    (hB : ∀ cm : BitVec 32, Mn X.cpu.gpr n cm → Mal.MalB (zl cm * 4#64 + 4#64) B)
    (hhi : hi + 312 ≤ X.cpu.gpr.rsp.toNat) (hp8 : X.cpu.gpr.rsp.toNat + 8 ≤ 2 ^ 64)
    (hsw : ∀ a : Addr, hi ≤ a.toNat → a.toNat < X.cpu.gpr.rsp.toNat → Foot Wl a)
    (hl : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsp i))
    (hl6 : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rsp - 48) i))
    (fd0 : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rdi i))
    (fw0 : ∀ i < 8, Foot Wl (Addr.add X.cpu.gpr.rdi i))
    (fw8 : ∀ i < 4, Foot Wl (Addr.add (X.cpu.gpr.rdi + 8#64) i))
    (fw12 : ∀ i < 4, Foot Wl (Addr.add (X.cpu.gpr.rdi + 12#64) i))
    (hqd : X.cpu.gpr.rdi.toNat + 16 ≤ 2 ^ 64)
    (hdd : X.cpu.gpr.rdi.toNat + 16 ≤ X.cpu.gpr.rsp.toNat - 64 ∨ X.cpu.gpr.rsp.toNat + 8 ≤ X.cpu.gpr.rdi.toNat)
    (hdh : X.cpu.gpr.rdi.toNat + 16 ≤ 7940480 ∨ hi ≤ X.cpu.gpr.rdi.toNat)
    (hw : Ucw.Wz F V X.cpu.gpr.rdx n)
    (hsd : ∀ i ≤ n, (Addr.add X.cpu.gpr.rdx (4 * i)).toNat + 4 ≤ 2 ^ 64 ∧
      ((Addr.add X.cpu.gpr.rdx (4 * i)).toNat + 4 ≤ X.cpu.gpr.rsp.toNat - 32 ∨
        X.cpu.gpr.rsp.toNat ≤ (Addr.add X.cpu.gpr.rdx (4 * i)).toNat))
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (hra : rdq(V, X.cpu.gpr.rsp) = e₂.add j₂)
    (kw : ∀ (cm : BitVec 32) (Z : State) (V₁ : Addr → Byte), Ucw.Pu F Wl fb hi m X.cpu.gpr V cm.toNat V₁ →
      ∀ (Y : State) (t' : Nat),
      KeptW Wl s₀ Y → Agree F Y.proc.mm.mem (Vst V₁ (X.cpu.gpr.rsp - 48) (toBytesLE (ucn_at.add 84) 8)) →
      Y.cpu.rip = Wmc.wmc_at →
      Y.cpu.gpr = { Z.cpu.gpr with rdi := rdq(V₁, X.cpu.gpr.rdi), rdx := zl cm, rsi := X.cpu.gpr.rdx }.set 4
        (X.cpu.gpr.rsp - 48) →
      (∀ (Zw : State) (V₂ : Addr → Byte) (t'' : Nat), KeptW Wl s₀ Zw → Agree F Zw.proc.mm.mem V₂ →
        Zw.cpu.rip = ucn_at.add 84 → Zw.cpu.gpr.rsp = X.cpu.gpr.rsp - 40 → Zw.cpu.gpr.rbx = X.cpu.gpr.rdi →
        Zw.cpu.gpr.r13 = zl cm * 4#64 → Sv V₂ X.cpu.gpr (e₂.add j₂) →
        (∀ i < 4, Foot Wl (Addr.add (rdq(V₂, X.cpu.gpr.rdi) + zl cm * 4#64) i)) →
        (rdq(V₂, X.cpu.gpr.rdi) + zl cm * 4#64).toNat + 4 ≤ 2 ^ 64 →
        ((rdq(V₂, X.cpu.gpr.rdi) + zl cm * 4#64).toNat + 4 ≤ X.cpu.gpr.rsp.toNat - 32 ∨
          X.cpu.gpr.rsp.toNat + 8 ≤ (rdq(V₂, X.cpu.gpr.rdi) + zl cm * 4#64).toNat) →
        Pw cm Zw V₂ → GoG prof L o gev gP gE Zw t'') →
      GoG prof L o gev gP gE Y t')
    (kr : ∀ (cm : BitVec 32) (Zw : State) (V₂ : Addr → Byte) (Z' : State) (t' : Nat), Pw cm Zw V₂ →
      KeptW Wl s₀ Z' →
      Agree F Z'.proc.mm.mem (Vst V₂ (rdq(V₂, X.cpu.gpr.rdi) + zl cm * 4#64) (toBytesLE 0#32 4)) →
      Z'.cpu.rip = e₂.add j₂ →
      Z'.cpu.gpr = { Zw.cpu.gpr with
          rax := rdq(V₂, X.cpu.gpr.rdi), rbx := X.cpu.gpr.rbx, rbp := X.cpu.gpr.rbp, r12 := X.cpu.gpr.r12,
          r13 := X.cpu.gpr.r13, rsp := X.cpu.gpr.rsp + 8 } →
      GoG prof L o gev gP gE Z' t') :
    GoG prof L o gev gP gE X t := by
  have hlt := X.cpu.gpr.rsp.isLt
  have hTl : 8032256 ≤ hi ∧ hi < 2 ^ 64 := by
    obtain ⟨_, T, _, _, _, -, -, -, -, hT, hTh, hhi', -⟩ := hH
    omega
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
  have t8 : (X.cpu.gpr.rdi + 8#64).toNat = X.cpu.gpr.rdi.toNat + 8 := by
    rw [BitVec.toNat_add]; simp <;> omega
  have t12 : (X.cpu.gpr.rdi + 12#64).toNat = X.cpu.gpr.rdi.toNat + 12 := by
    rw [BitVec.toNat_add]; simp <;> omega
  have l8 : ∀ x : BitVec 64, (toBytesLE x 8).length = 8 := fun x => toBytesLE_length _ _
  have l4 : ∀ x : BitVec 32, (toBytesLE x 4).length = 4 := fun x => toBytesLE_length _ _
  have hfw : ∀ (x : Addr) (d : Nat), x.toNat = X.cpu.gpr.rsp.toNat - d → 8 ≤ d → d ≤ 48 →
      ∀ i < 8, Foot Wl (Addr.add x i) := fun x d hx h1 h2 i hi' => by
    have e := toNat_add_of_fits (a := x) (i := i) (n := 8) hi' (by rw [hx]; omega)
    exact hsw _ (by rw [e, hx]; omega) (by rw [e, hx]; omega)
  -- the bytes after the pushes outside them, and at `SetStartLen`'s entry outside the frame
  have hV0 : ∀ a : Addr, (a.toNat < X.cpu.gpr.rsp.toNat - 32 ∨ X.cpu.gpr.rsp.toNat ≤ a.toNat) →
      V0 V X.cpu.gpr a = V a := by
    intro a h1
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
    exact s1.trans (s2.trans (s3.trans s4))
  have hVo : ∀ a : Addr, (a.toNat < X.cpu.gpr.rsp.toNat - 48 ∨ X.cpu.gpr.rsp.toNat ≤ a.toNat) →
      Vst (V0 V X.cpu.gpr) (X.cpu.gpr.rsp - 48) (toBytesLE (ucn_at.add 70) 8) a = V a := fun a h1 =>
    (Tun.Vst_out (V0 V X.cpu.gpr) (X.cpu.gpr.rsp - 48) (toBytesLE (ucn_at.add 70) 8) a
      (by rw [l8, tn48]; omega) (by rw [l8, tn48]; omega)).trans (hV0 a (by omega))
  have hsv := Uau.sv0 (V := V) (g := X.cpu.gpr) (by omega) hp8 hra
  refine ucn_ok (Pu := fun cm _ V'' => Ucw.Pu F Wl fb hi m X.cpu.gpr V cm.toNat V'') (Pw := Pw) c hin hinU hinWm
    hK hA hrip (by omega) hp8
    (hfw _ 8 tn8 (by omega) (by omega)) (hfw _ 16 tn16 (by omega) (by omega)) (hfw _ 24 tn24 (by omega) (by omega))
    (hfw _ 32 tn32 (by omega) (by omega)) (hfw _ 48 tn48 (by omega) (by omega)) hl fd0 hw hsd hin₂ h₂ hra ?_ kw kr
  intro Y t' cm a cx d hMn hKY hAY hrY hgY k
  have hB' := hB cm hMn
  have hB3 : 64 ≤ B := hB'.2.2
  have hH' : Mal.Hp F Wl fb hi (m + B) (Vst (V0 V X.cpu.gpr) (X.cpu.gpr.rsp - 48) (toBytesLE (ucn_at.add 70) 8)) :=
    Mal.Hp.mv hH (by omega) fun a _ a2 => hVo a (.inl (by omega))
  have hYs : Y.cpu.gpr.rsp = X.cpu.gpr.rsp - 48 := by rw [hgY]; try rfl
  have hYd : Y.cpu.gpr.rdi = X.cpu.gpr.rdi := by rw [hgY]; try rfl
  have hYb : Y.cpu.gpr.rbx = X.cpu.gpr.rdi := by rw [hgY]; try rfl
  have hYp : Y.cpu.gpr.rbp = X.cpu.gpr.rdx := by rw [hgY]; try rfl
  have hY12 : Y.cpu.gpr.r12 = zl cm := by rw [hgY]; try rfl
  have hY13 : Y.cpu.gpr.r13 = zl cm * 4#64 := by rw [hgY]; try rfl
  have hYi : Y.cpu.gpr.rsi = BitVec.setWidth 64 cm := by rw [hgY]; try rfl
  have hYt : Y.cpu.gpr.rsp.toNat = X.cpu.gpr.rsp.toNat - 48 := by rw [hYs, tn48]
  have hYn : (BitVec.setWidth 32 Y.cpu.gpr.rsi).toNat = cm.toNat := by rw [hYi, sw_64_32]
  have hra' : rdq(Vst (V0 V X.cpu.gpr) (X.cpu.gpr.rsp - 48) (toBytesLE (ucn_at.add 70) 8), Y.cpu.gpr.rsp) =
      ucn_at.add 70 := by
    rw [hYs, Tun.rd_Vst_self (V0 V X.cpu.gpr) (X.cpu.gpr.rsp - 48) (toBytesLE (ucn_at.add 70) 8) (l8 _)
      (by rw [tn48]; omega), ofBytesLE_toBytesLE (by rfl : (64 : Nat) = 8 * 8)]
  refine Usl.usl_okH (B := B) (m := m) c hfs hinU hinW hinN hinI hKY hAY hrY hH'
    (by show Mal.MalB (BitVec.setWidth 64 (BitVec.setWidth 32 Y.cpu.gpr.rsi) * 4#64 + 4#64) B
        rw [hYi, sw_64_32]; exact hB')
    (by rw [hYt]; omega) (by rw [hYt]; omega) (by rw [hYt]; omega)
    (fun a h1 h2 => hsw a h1 (by rw [hYt] at h2; omega)) (by rw [hYs]; exact hl6)
    (by rw [hYd]; exact fw0) (by rw [hYd]; exact fw8) (by rw [hYd]; exact fw12) (by rw [hYd]; exact hqd)
    (by rw [hYd, hYt]; omega) (by rw [hYd]; exact hdh) hin (j₂ := 70) (by decide) hra' ?_
  intro Z V' Z' t'' h12 h13 hp1 hp2 hft hHp hfr hKZ' hAZ' hrZ' hgZ'
  rw [hYd] at hHp hAZ'
  rw [hYn] at hp2 hft
  rw [hYd] at hfr
  -- `_chars` = the block
  have hrax : rdq(Usl.V1 V' X.cpu.gpr.rdi (BitVec.setWidth 32 Y.cpu.gpr.rsi) Z.cpu.gpr.rax, X.cpu.gpr.rdi) =
      Z.cpu.gpr.rax := by
    have hb : X.cpu.gpr.rdi.toNat + 8 ≤ 2 ^ 64 := by omega
    rw [Tun.rd_Vst_self _ _ _ (toBytesLE_length _ _) hb, ofBytesLE_toBytesLE (n := 8) rfl]
  -- the bytes after the stores of `_len`, `_limit` and `_chars`, outside `this`'s 16 bytes
  have hV1 : ∀ a : Addr, (a.toNat < X.cpu.gpr.rdi.toNat ∨ X.cpu.gpr.rdi.toNat + 16 ≤ a.toNat) →
      Usl.V1 V' X.cpu.gpr.rdi (BitVec.setWidth 32 Y.cpu.gpr.rsi) Z.cpu.gpr.rax a = V' a := by
    intro a h
    have s1 := Tun.Vst_out (Vst (Vst V' (X.cpu.gpr.rdi + 8#64) (toBytesLE (BitVec.setWidth 32 Y.cpu.gpr.rsi) 4))
      (X.cpu.gpr.rdi + 12#64) (toBytesLE (BitVec.setWidth 32 Y.cpu.gpr.rsi) 4)) X.cpu.gpr.rdi
      (toBytesLE Z.cpu.gpr.rax 8) a (by rw [l8]; omega) (by rw [l8]; omega)
    have s2 := Tun.Vst_out (Vst V' (X.cpu.gpr.rdi + 8#64) (toBytesLE (BitVec.setWidth 32 Y.cpu.gpr.rsi) 4))
      (X.cpu.gpr.rdi + 12#64) (toBytesLE (BitVec.setWidth 32 Y.cpu.gpr.rsi) 4) a (by rw [l4, t12]; omega)
      (by rw [l4, t12]; omega)
    have s3 := Tun.Vst_out V' (X.cpu.gpr.rdi + 8#64) (toBytesLE (BitVec.setWidth 32 Y.cpu.gpr.rsi) 4) a
      (by rw [l4, t8]; omega) (by rw [l4, t8]; omega)
    exact s1.trans (s2.trans s3)
  -- the saved registers and the return address, as after the pushes
  have hV0r : ∀ a : Addr, X.cpu.gpr.rsp.toNat - 40 ≤ a.toNat → a.toNat < X.cpu.gpr.rsp.toNat + 8 →
      Usl.V1 V' X.cpu.gpr.rdi (BitVec.setWidth 32 Y.cpu.gpr.rsi) Z.cpu.gpr.rax a = V0 V X.cpu.gpr a := fun a a1 a2 =>
    (hV1 a (by omega)).trans ((hfr a (.inr (.inr (by rw [hYt]; omega))) (by omega)).trans
      (Tun.Vst_out (V0 V X.cpu.gpr) (X.cpu.gpr.rsp - 48) (toBytesLE (ucn_at.add 70) 8) a
        (by rw [l8, tn48]; omega) (by rw [l8, tn48]; omega)))
  have hrd : ∀ (x : Addr) (dx : Nat), x.toNat = X.cpu.gpr.rsp.toNat - dx → dx ≤ 32 →
      rdq(Usl.V1 V' X.cpu.gpr.rdi (BitVec.setWidth 32 Y.cpu.gpr.rsi) Z.cpu.gpr.rax, x) = rdq(V0 V X.cpu.gpr, x) :=
    fun x dx hx hd => by
      rw [Sbrk.rd_eq (V := V0 V X.cpu.gpr) (x := x) (n := 8) (by rw [hx]; omega)
        fun a a1 a2 => hV0r a (by rw [hx] at a1; omega) (by rw [hx] at a2; omega)]
  obtain ⟨v32, v24, v16, v8, v0⟩ := hsv
  have zsp : Z'.cpu.gpr.rsp = X.cpu.gpr.rsp - 40 := by
    rw [hgZ']
    show Y.cpu.gpr.rsp + 8 = _
    rw [hYs]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, tn48, tn40]
    simp <;> omega
  refine k Z' _ t'' hKZ' hAZ' hrZ' zsp (by rw [hgZ']; exact hYb) (by rw [hgZ']; exact hYp)
    (by rw [hgZ']; exact h12.trans hY12) (by rw [hgZ']; exact h13.trans hY13)
    ⟨(hrd _ 32 tn32 (by omega)).trans v32, (hrd _ 24 tn24 (by omega)).trans v24,
      (hrd _ 16 tn16 (by omega)).trans v16, (hrd _ 8 tn8 (by omega)).trans v8,
      (hrd _ 0 (by omega) (by omega)).trans v0⟩
    ⟨by rw [hrax]; exact hp1, by rw [hrax]; exact hp2, by rw [hrax]; exact hft, hHp, ?_⟩
  intro a h1 h2
  rw [hrax] at h1
  rw [hV1 a h2]
  have hva : V' a = Vst (V0 V X.cpu.gpr) (X.cpu.gpr.rsp - 48) (toBytesLE (ucn_at.add 70) 8) a := by
    rcases h1 with h1 | h1 | h1
    · exact hfr a (.inl h1) (by omega)
    · exact hfr a (.inr (.inl h1)) (by omega)
    · exact hfr a (.inr (.inr (by rw [hYt]; omega))) (by omega)
  rw [hva]
  exact hVo a (by rcases h1 with h1 | h1 | h1 <;> omega)

end FV7z.Ucn
