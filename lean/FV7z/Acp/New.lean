import FV7z.Acp.Holds
import FV7z.Acc.New
/-!
# `AString (const AString &s)` with `operator new` (PLAN.md §M, M1)

`acp_ok` takes `SetStartLen`'s call of `operator new (s._len + 1)` as a hypothesis (`kf`); `acp_okH` discharges it
by `Asl.kf_hpW` (`Onw.onw_hpWT`), with the registers `Acp.gY` and the bytes `Acp.VY` at `SetStartLen`'s entry, as
`Acc.acc_okH` does for `AString (const char *)`. `s._len` (`rdd(V, rsi + 8)`) is the length `n` of the string at
`s._chars` (`rdq(V, rsi)`). The object `s` and its string are in static data (below `main_arena.top`) or below the
old top plus 8 (older live blocks); the object may also be on the stack from `rsp` up. `malloc` stores only into the
heap's words from the old top up and the block, so both are as they were (`Mal.keep_low`'s case split).

- `acp_okH`: `acp_ok` with `Asl.kf_hpW`, the post `Acc.Pa`.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn FV7z.Mys
open FV7z.Imm (imm imm_at)
open FV7z.Mnx (mnx mnx_at)
namespace FV7z.Acp

variable {F : Footprint} {Wl : List Rgn} {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {X : State} {t : Nat} {V : Addr → Byte}

set_option maxHeartbeats 1000000 in
/-- `acp_ok` with `operator new` by `Asl.kf_hpW`: see the module doc. -/
theorem acp_okH {fb : Addr} {hi m B n : Nat} (c : Seg prof F Wl L s₀ o) (hfs : s₀.cpu.seg.fsBase = fb)
    (hin : CodeIn L acp_at acp) (hinS : CodeIn L Asl.asl_at Asl.asl) (hinW : CodeIn L Onw.onw_at Onw.onw)
    (hinN : CodeIn L mnx_at mnx) (hinI : CodeIn L imm_at imm)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = acp_at)
    (hH : Mal.Hp F Wl fb hi (m + B) V) (hB : Mal.MalB (BitVec.setWidth 64 rdd(V, X.cpu.gpr.rsi + 8#64) + 1#64) B)
    (hhi : hi + 296 ≤ X.cpu.gpr.rsp.toNat) (hp8 : X.cpu.gpr.rsp.toNat + 8 ≤ 2 ^ 64)
    (hsw : ∀ a : Addr, hi ≤ a.toNat → a.toNat < X.cpu.gpr.rsp.toNat → Foot Wl a)
    (hl : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsp i))
    (fw0 : ∀ i < 8, Foot Wl (Addr.add X.cpu.gpr.rdi i))
    (fw8 : ∀ i < 4, Foot Wl (Addr.add (X.cpu.gpr.rdi + 8#64) i))
    (fw12 : ∀ i < 4, Foot Wl (Addr.add (X.cpu.gpr.rdi + 12#64) i))
    (hq : X.cpu.gpr.rdi.toNat + 16 ≤ 2 ^ 64)
    (hd : X.cpu.gpr.rdi.toNat + 16 ≤ X.cpu.gpr.rsp.toNat - 48 ∨ X.cpu.gpr.rsp.toNat + 8 ≤ X.cpu.gpr.rdi.toNat)
    (hdh : X.cpu.gpr.rdi.toNat + 16 ≤ 7940480 ∨ hi ≤ X.cpu.gpr.rdi.toNat)
    (fs0 : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsi i))
    (fs8 : ∀ i < 4, Foot F.data (Addr.add (X.cpu.gpr.rsi + 8#64) i))
    (hsq : X.cpu.gpr.rsi.toNat + 12 ≤ 2 ^ 64)
    (hoT : X.cpu.gpr.rsi.toNat + 12 ≤ 7940768 ∨
      7940776 ≤ X.cpu.gpr.rsi.toNat ∧ X.cpu.gpr.rsi.toNat + 12 ≤ rdq(V, 7940768#64).toNat + 8 ∨
      X.cpu.gpr.rsp.toNat ≤ X.cpu.gpr.rsi.toNat)
    (hst : X.cpu.gpr.rsi.toNat + 8 ≤ X.cpu.gpr.rdi.toNat ∨ X.cpu.gpr.rdi.toNat + 16 ≤ X.cpu.gpr.rsi.toNat)
    (hnv : rdd(V, X.cpu.gpr.rsi + 8#64).toNat = n) (hnz : ∀ i < n, V (Addr.add (rdq(V, X.cpu.gpr.rsi)) i) ≠ 0)
    (hz : V (Addr.add (rdq(V, X.cpu.gpr.rsi)) n) = 0)
    (hf : ∀ i, i ≤ n → Foot F.data (Addr.add (rdq(V, X.cpu.gpr.rsi)) i))
    (hsT : (rdq(V, X.cpu.gpr.rsi)).toNat + n + 1 ≤ 7940768 ∨
      7940776 ≤ (rdq(V, X.cpu.gpr.rsi)).toNat ∧
        (rdq(V, X.cpu.gpr.rsi)).toNat + n + 1 ≤ rdq(V, 7940768#64).toNat + 8)
    (hpt : (rdq(V, X.cpu.gpr.rsi)).toNat + n + 1 ≤ X.cpu.gpr.rdi.toNat ∨
      X.cpu.gpr.rdi.toNat + 16 ≤ (rdq(V, X.cpu.gpr.rsi)).toNat)
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (hra : rdq(V, X.cpu.gpr.rsp) = e₂.add j₂)
    (k : ∀ (Z : State) (V' : Addr → Byte),
      Pk (Wl := Wl) X.cpu.gpr V n (e₂.add j₂) (Acc.Pa F Wl fb hi m X.cpu.gpr V n) Z V' →
      ∀ (Z' : State) (t' : Nat), KeptW Wl s₀ Z' →
      Agree F Z'.proc.mm.mem
        (Cp (Asl.V1 V' X.cpu.gpr.rdi rdd(V, X.cpu.gpr.rsi + 8#64) Z.cpu.gpr.rax) (rdq(V, X.cpu.gpr.rsi))
          Z.cpu.gpr.rax (n + 1)) →
      Z'.cpu.rip = e₂.add j₂ → Str.Back X.cpu.gpr Z'.cpu.gpr → GoG prof L o gev gP gE Z' t') :
    GoG prof L o gev gP gE X t := by
  have hlt := X.cpu.gpr.rsp.isLt
  have hB3 : 64 ≤ B := hB.2.2
  have hT0 : 8032256 ≤ rdq(V, 7940768#64).toNat ∧ rdq(V, 7940768#64).toNat + (m + B) ≤ hi ∧ hi < 2 ^ 64 := by
    obtain ⟨_, T, _, _, _, -, -, -, -, hT, hTh, hhi', hTe, -⟩ := hH
    rw [hTe]
    omega
  have hn32 : n < 2 ^ 32 := hnv ▸ (rdd(V, X.cpu.gpr.rsi + 8#64)).isLt
  have tn8 : (X.cpu.gpr.rsp - 8).toNat = X.cpu.gpr.rsp.toNat - 8 := by rw [BitVec.toNat_sub]; simp <;> omega
  have tn16 : (X.cpu.gpr.rsp - 16).toNat = X.cpu.gpr.rsp.toNat - 16 := by rw [BitVec.toNat_sub]; simp <;> omega
  have tn32 : (X.cpu.gpr.rsp - 32).toNat = X.cpu.gpr.rsp.toNat - 32 := by rw [BitVec.toNat_sub]; simp <;> omega
  have tn40 : (X.cpu.gpr.rsp - 40).toNat = X.cpu.gpr.rsp.toNat - 40 := by rw [BitVec.toNat_sub]; simp <;> omega
  have tn48 : (X.cpu.gpr.rsp - 48).toNat = X.cpu.gpr.rsp.toNat - 48 := by rw [BitVec.toNat_sub]; simp <;> omega
  have tn64 : (X.cpu.gpr.rsp - 64).toNat = X.cpu.gpr.rsp.toNat - 64 := by rw [BitVec.toNat_sub]; simp <;> omega
  have e16 : X.cpu.gpr.rsp - 8 - 8 = X.cpu.gpr.rsp - 16 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, tn8, tn16]
    simp <;> omega
  have l8 : ∀ x : BitVec 64, (toBytesLE x 8).length = 8 := fun x => toBytesLE_length _ _
  have hfw : ∀ (x : Addr) (d : Nat), x.toNat = X.cpu.gpr.rsp.toNat - d → 8 ≤ d → d ≤ 64 →
      ∀ i < 8, Foot Wl (Addr.add x i) := fun x d hx h1 h2 i hi' => by
    have e := toNat_add_of_fits (a := x) (i := i) (n := 8) hi' (by rw [hx]; omega)
    exact hsw _ (by rw [e, hx]; omega) (by rw [e, hx]; omega)
  -- the registers at `SetStartLen`'s entry
  have gYs : (gY X.cpu.gpr rdd(V, X.cpu.gpr.rsi + 8#64)).rsp = X.cpu.gpr.rsp - 32 := rfl
  have gYd : (gY X.cpu.gpr rdd(V, X.cpu.gpr.rsi + 8#64)).rdi = X.cpu.gpr.rdi := rfl
  have hsn : (BitVec.setWidth 32 (gY X.cpu.gpr rdd(V, X.cpu.gpr.rsi + 8#64)).rsi).toNat = n := by
    show (BitVec.setWidth 32 (BitVec.setWidth 64 rdd(V, X.cpu.gpr.rsi + 8#64))).toNat = n
    rw [sw_64_32]; exact hnv
  -- the bytes at `SetStartLen`'s entry outside the pushes
  have hVa : ∀ a : Addr, (a.toNat < X.cpu.gpr.rsp.toNat - 32 ∨ X.cpu.gpr.rsp.toNat ≤ a.toNat) →
      VY V X.cpu.gpr a = V a := by
    intro a h1
    have s1 := Tun.Vst_out (V0 V X.cpu.gpr) (X.cpu.gpr.rsp - 32) (toBytesLE (acp_at.add 24) 8) a
      (by rw [l8, tn32]; omega) (by rw [l8, tn32]; omega)
    have s3 := Tun.Vst_out (Vst V (X.cpu.gpr.rsp - 8) (toBytesLE X.cpu.gpr.rbp 8)) (X.cpu.gpr.rsp - 8 - 8)
      (toBytesLE X.cpu.gpr.rbx 8) a (by rw [l8, e16, tn16]; omega) (by rw [l8, e16, tn16]; omega)
    have s4 := Tun.Vst_out V (X.cpu.gpr.rsp - 8) (toBytesLE X.cpu.gpr.rbp 8) a (by rw [l8, tn8]; omega)
      (by rw [l8, tn8]; omega)
    exact s1.trans (s3.trans s4)
  have hH' : Mal.Hp F Wl fb hi (m + B) (VY V X.cpu.gpr) :=
    Mal.Hp.mv hH (by omega) fun a _ a2 => hVa a (.inl (by omega))
  have hTop : rdq(VY V X.cpu.gpr, 7940768#64) = rdq(V, 7940768#64) := by
    have et : (7940768#64 : Addr).toNat = 7940768 := rfl
    rw [Sbrk.rd_eq (V := V) (x := 7940768#64) (n := 8) (by rw [et]; omega) fun a _ a2 =>
      hVa a (.inl (by rw [et] at a2; omega))]
  have hsf : X.cpu.gpr.rsi.toNat + 12 ≤ X.cpu.gpr.rsp.toNat - 16 ∨ X.cpu.gpr.rsp.toNat ≤ X.cpu.gpr.rsi.toNat := by
    omega
  have hpw : (rdq(V, X.cpu.gpr.rsi)).toNat + n + 1 ≤ 2 ^ 64 := by omega
  refine acp_ok (P1 := Acc.Pa F Wl fb hi m X.cpu.gpr V n) c hin hinS hinW hK hA hrip (by omega) hp8
    (hfw _ 8 tn8 (by omega) (by omega)) (hfw _ 16 tn16 (by omega) (by omega)) (hfw _ 32 tn32 (by omega) (by omega))
    (hfw _ 40 tn40 (by omega) (by omega)) (hfw _ 48 tn48 (by omega) (by omega)) (hfw _ 64 tn64 (by omega) (by omega))
    hl fw0 fw8 fw12 hq hd fs0 fs8 hsq hsf hst (by omega) hnz hz hf hpw hpt hin₂ h₂ ?_ k
  intro Y t' hKY hAY hrY hgY k'
  refine Asl.kf_hpW (V := VY V X.cpu.gpr) (g := gY X.cpu.gpr rdd(V, X.cpu.gpr.rsi + 8#64)) (ra := acp_at.add 24)
    c hfs hinS hinW hinN hinI hH'
    (by show Mal.MalB (BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.setWidth 64 rdd(V, X.cpu.gpr.rsi + 8#64)))
      + 1#64) B; rw [sw_64_32]; exact hB)
    (by rw [gYs, tn32]; omega) (by rw [gYs, tn32]; omega)
    (fun a h1 h2 => hsw a h1 (by rw [gYs, tn32] at h2; omega))
    (by rw [gYd]; exact hq) (by rw [gYd, gYs, tn32]; omega) (by rw [gYd]; exact hdh) ?_ Y t' hKY hAY hrY hgY ?_
  · rw [gYs, Tun.rd_Vst_self (V0 V X.cpu.gpr) (X.cpu.gpr.rsp - 32) (toBytesLE (acp_at.add 24) 8) (l8 _)
      (by rw [tn32]; omega), ofBytesLE_toBytesLE (by rfl : (64 : Nat) = 8 * 8)]
  intro Z V' t'' h1 h2 h3 h4 h5 h6 h7 h8 h9 hPo
  obtain ⟨z12, z13, z14, z15, hT1, hp1, hpe, hft, hPm, hfr⟩ := hPo
  rw [hTop] at hT1
  rw [hsn] at hpe hft hPm
  rw [gYs, gYd, tn32] at hfr
  -- the bytes after `operator new` from `SetStartLen`'s return address to the caller's return address
  have hVr : ∀ a : Addr, X.cpu.gpr.rsp.toNat - 32 ≤ a.toNat → a.toNat < X.cpu.gpr.rsp.toNat + 8 →
      V' a = VY V X.cpu.gpr a := fun a ha hb => hfr a (.inr (.inr ha)) (by omega)
  have hb1 : rdq(V', X.cpu.gpr.rsp - 16) = X.cpu.gpr.rbx := by
    rw [Sbrk.rd_eq (V := VY V X.cpu.gpr) (x := X.cpu.gpr.rsp - 16) (n := 8) (by rw [tn16]; omega) fun a a1 a2 =>
      hVr a (by rw [tn16] at a1; omega) (by rw [tn16] at a2; omega)]
    rw [Tun.rd_Vst (V0 V X.cpu.gpr) (X.cpu.gpr.rsp - 32) (toBytesLE (acp_at.add 24) 8) (X.cpu.gpr.rsp - 16) 8
      (by rw [l8, tn32]; omega) (by rw [tn16]; omega) (by rw [l8, tn32, tn16]; omega)]
    rw [← e16, Tun.rd_Vst_self (Vst V (X.cpu.gpr.rsp - 8) (toBytesLE X.cpu.gpr.rbp 8)) (X.cpu.gpr.rsp - 8 - 8)
      (toBytesLE X.cpu.gpr.rbx 8) (l8 _) (by rw [e16, tn16]; omega),
      ofBytesLE_toBytesLE (by rfl : (64 : Nat) = 8 * 8)]
  have hb2 : rdq(V', X.cpu.gpr.rsp - 8) = X.cpu.gpr.rbp := by
    rw [Sbrk.rd_eq (V := VY V X.cpu.gpr) (x := X.cpu.gpr.rsp - 8) (n := 8) (by rw [tn8]; omega) fun a a1 a2 =>
      hVr a (by rw [tn8] at a1; omega) (by rw [tn8] at a2; omega)]
    rw [Tun.rd_Vst (V0 V X.cpu.gpr) (X.cpu.gpr.rsp - 32) (toBytesLE (acp_at.add 24) 8) (X.cpu.gpr.rsp - 8) 8
      (by rw [l8, tn32]; omega) (by rw [tn8]; omega) (by rw [l8, tn32, tn8]; omega)]
    rw [Tun.rd_Vst (Vst V (X.cpu.gpr.rsp - 8) (toBytesLE X.cpu.gpr.rbp 8)) (X.cpu.gpr.rsp - 8 - 8)
      (toBytesLE X.cpu.gpr.rbx 8) (X.cpu.gpr.rsp - 8) 8 (by rw [l8, e16, tn16]; omega) (by rw [tn8]; omega)
      (by rw [l8, e16, tn16, tn8]; omega)]
    rw [Tun.rd_Vst_self V (X.cpu.gpr.rsp - 8) (toBytesLE X.cpu.gpr.rbp 8) (l8 _) (by rw [tn8]; omega),
      ofBytesLE_toBytesLE (by rfl : (64 : Nat) = 8 * 8)]
  -- the object `s` (`_chars`): static data, below the old top plus 8, or on the stack from `rsp` up
  have hsrc : rdq(V', X.cpu.gpr.rsi) = rdq(V, X.cpu.gpr.rsi) := by
    rw [Sbrk.rd_eq (V := V) (x := X.cpu.gpr.rsi) (n := 8) (by omega) fun a a1 a2 => by
      rw [hfr a (by omega) (by omega)]; exact hVa a (by omega)]
  -- the string, below the old top plus 8 (`Mal.keep_low`)
  have hkl := Mal.keep_low (Q := fun a => X.cpu.gpr.rsp.toNat - 32 ≤ a.toNat)
    (R := fun a => a.toNat < X.cpu.gpr.rdi.toNat ∨ X.cpu.gpr.rdi.toNat + 8 ≤ a.toNat) hT1 hfr
  refine k' Z V' t'' h1 h2 h3 h4 h5 h6 h7 h8 h9 ?_
  unfold Pk
  refine ⟨hb1, hb2, ?_, by rw [z12], by rw [z13], by rw [z14], by rw [z15], hsrc, ?_, ?_,
    by omega, .inr (by omega), .inl (by omega), hT1, hp1, hpe, hft, hPm, ?_⟩
  · rw [Sbrk.rd_eq (V := VY V X.cpu.gpr) (x := X.cpu.gpr.rsp) (n := 8) hp8 fun a a1 a2 => hVr a (by omega) (by omega)]
    rw [Sbrk.rd_eq (V := V) (x := X.cpu.gpr.rsp) (n := 8) hp8 fun a a1 _ => hVa a (.inr a1)]
    exact hra
  · intro i hi'
    have e := toNat_add_of_fits (a := rdq(V, X.cpu.gpr.rsi)) (i := i) (n := n + 1) (by omega) (by omega)
    rw [hkl _ (by rw [e]; omega) (by rw [e]; omega) (by show _ ∨ _; rw [e]; omega)]
    exact hVa _ (.inl (by rw [e]; omega))
  · intro i hi'
    have e := toNat_add_of_fits (a := Z.cpu.gpr.rax) (i := i) (n := n + 1) (by omega) (by omega)
    exact (hft _ (by rw [e]; omega) (by rw [e]; omega)).1
  · intro a a1 a2
    rw [hfr a (by omega) a2]
    exact hVa a (by omega)

end FV7z.Acp
