import FV7z.Acc.Holds
import FV7z.Asl.New
import FV7z.Mal.Keep
/-!
# `AString (const char *s)` with `operator new` (PLAN.md §M, M1)

`acc_ok` takes `SetStartLen`'s call of `operator new (len + 1)` as a hypothesis (`kf`); `acc_okH` discharges it by
`Asl.kf_hpW` (`Onw.onw_hpWT`), with `Mal.MalB (len + 1) B`, `Mal.Hp` with a top of at least `m + B` bytes below `hi`
at the entry, `hi` 296 bytes below `rsp` and `[hi, rsp)` in what the run may store into. The string `s` is in static
data (below `main_arena.top`) or below the old top plus 8 (an older live block): `malloc` stores only into the heap's
words from the old top up and the block, so the string is as it was (`Mal.keep_low`).

- `Pa`: `P1` for `acc_ok`, in the entry's terms: the block `rax` (16 above the old top or more, `len + 1` bytes below
  `hi`, in the footprint, above the TLS block's words), `Mal.Hp … m` for the bytes outside it, and the bytes outside
  the heap's words, the block and `_chars` and from the return address up as at the entry.
- `acc_okH`: `acc_ok` with `Asl.kf_hpW`.

Status (2026-11-26): written, not built yet, and not imported in `FV7z.lean`. Next: add `import FV7z.Acc.New` after
`FV7z.Acs.New`, triage `FV7z.Acc.New -- FV7z.Acc.acc_okH`. Then `FV7z/Acp/New.lean` (`acp_okH`) the same way: `Acp`'s
`Pk` reads the source at `rdq(V, g.rsi)`, so `hsT` is on that pointer, and `Acp.V0`/`gY` replace `Acc.V0`. After that,
`…okH` wrappers for the other callers of `operator new` (`Ctor.*`, `Rdn`'s `ReserveDown`, `Ucw`/`Uau`/`Ucn`).
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn FV7z.Mys
open FV7z.Imm (imm imm_at)
open FV7z.Mnx (mnx mnx_at)
namespace FV7z.Acc

variable {F : Footprint} {Wl : List Rgn} {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {X : State} {t : Nat} {V : Addr → Byte}

/-- `acc_ok`'s `P1` that `acc_okH` gives, for the registers `g` and the bytes `V` at the entry and the length `n`: see
the module doc. -/
abbrev Pa (F : Footprint) (Wl : List Rgn) (fb : Addr) (hi m : Nat) (g : Gprs) (V : Addr → Byte) (n : Nat) (Z : State)
    (V' : Addr → Byte) : Prop :=
  rdq(V, 7940768#64).toNat + 16 ≤ Z.cpu.gpr.rax.toNat ∧
    fb.toNat + 64 ≤ Z.cpu.gpr.rax.toNat ∧ Z.cpu.gpr.rax.toNat + (n + 1) ≤ hi ∧
    (∀ a : Addr, Z.cpu.gpr.rax.toNat ≤ a.toNat → a.toNat < Z.cpu.gpr.rax.toNat + (n + 1) →
      Foot Wl a ∧ Foot F.data a) ∧
    (∀ W : Addr → Byte, (∀ a : Addr, 7940480 ≤ a.toNat → a.toNat < hi →
      (a.toNat < Z.cpu.gpr.rax.toNat ∨ Z.cpu.gpr.rax.toNat + (n + 1) ≤ a.toNat) → W a = V' a) →
      Mal.Hp F Wl fb hi m W) ∧
    (∀ a : Addr, (a.toNat < 7940768 ∨ 7940776 ≤ a.toNat ∧ a.toNat + 8 < Z.cpu.gpr.rax.toNat ∨
      g.rsp.toNat ≤ a.toNat) → (a.toNat < g.rdi.toNat ∨ g.rdi.toNat + 8 ≤ a.toNat) → V' a = V a)

set_option maxHeartbeats 1000000 in
/-- `acc_ok` with `operator new` by `Asl.kf_hpW`: see the module doc. -/
theorem acc_okH {fb : Addr} {hi m B n : Nat} (c : Seg prof F Wl L s₀ o) (hfs : s₀.cpu.seg.fsBase = fb)
    (hin : CodeIn L acc_at acc) (hinS : CodeIn L Asl.asl_at Asl.asl) (hinW : CodeIn L Onw.onw_at Onw.onw)
    (hinN : CodeIn L mnx_at mnx) (hinI : CodeIn L imm_at imm)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = acc_at)
    (hH : Mal.Hp F Wl fb hi (m + B) V) (hB : Mal.MalB (BitVec.ofNat 64 n + 1#64) B)
    (hhi : hi + 296 ≤ X.cpu.gpr.rsp.toNat) (hp8 : X.cpu.gpr.rsp.toNat + 8 ≤ 2 ^ 64)
    (hsw : ∀ a : Addr, hi ≤ a.toNat → a.toNat < X.cpu.gpr.rsp.toNat → Foot Wl a)
    (hl : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsp i))
    (fw0 : ∀ i < 8, Foot Wl (Addr.add X.cpu.gpr.rdi i))
    (fw8 : ∀ i < 4, Foot Wl (Addr.add (X.cpu.gpr.rdi + 8#64) i))
    (fw12 : ∀ i < 4, Foot Wl (Addr.add (X.cpu.gpr.rdi + 12#64) i))
    (hq : X.cpu.gpr.rdi.toNat + 16 ≤ 2 ^ 64)
    (hd : X.cpu.gpr.rdi.toNat + 16 ≤ X.cpu.gpr.rsp.toNat - 48 ∨ X.cpu.gpr.rsp.toNat + 8 ≤ X.cpu.gpr.rdi.toNat)
    (hdh : X.cpu.gpr.rdi.toNat + 16 ≤ 7940480 ∨ hi ≤ X.cpu.gpr.rdi.toNat)
    (hn : n < 2 ^ 32) (hnz : ∀ i < n, V (Addr.add X.cpu.gpr.rsi i) ≠ 0#8)
    (hz : V (Addr.add X.cpu.gpr.rsi n) = 0#8)
    (hf : ∀ i, i ≤ n → Foot F.data (Addr.add X.cpu.gpr.rsi i))
    (hsT : X.cpu.gpr.rsi.toNat + n + 1 ≤ 7940768 ∨
      7940776 ≤ X.cpu.gpr.rsi.toNat ∧ X.cpu.gpr.rsi.toNat + n + 1 ≤ rdq(V, 7940768#64).toNat + 8)
    (hpt : X.cpu.gpr.rsi.toNat + n + 1 ≤ X.cpu.gpr.rdi.toNat ∨ X.cpu.gpr.rdi.toNat + 16 ≤ X.cpu.gpr.rsi.toNat)
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (hra : rdq(V, X.cpu.gpr.rsp) = e₂.add j₂)
    (k : ∀ (Z : State) (V' : Addr → Byte),
      Pk (Wl := Wl) X.cpu.gpr V n (e₂.add j₂) (Pa F Wl fb hi m X.cpu.gpr V n) Z V' →
      ∀ (Z' : State) (t' : Nat), KeptW Wl s₀ Z' →
      Agree F Z'.proc.mm.mem
        (Acp.Cp (Asl.V1 V' X.cpu.gpr.rdi (BitVec.ofNat 32 n) Z.cpu.gpr.rax) X.cpu.gpr.rsi Z.cpu.gpr.rax (n + 1)) →
      Z'.cpu.rip = e₂.add j₂ → Str.Back X.cpu.gpr Z'.cpu.gpr → GoG prof L o gev gP gE Z' t') :
    GoG prof L o gev gP gE X t := by
  have hlt := X.cpu.gpr.rsp.isLt
  have hB3 : 64 ≤ B := hB.2.2
  have hT0 : 8032256 ≤ rdq(V, 7940768#64).toNat ∧ rdq(V, 7940768#64).toNat + (m + B) ≤ hi ∧ hi < 2 ^ 64 := by
    obtain ⟨_, T, _, _, _, -, -, -, -, hT, hTh, hhi', hTe, -⟩ := hH
    rw [hTe]
    omega
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
  have hsn : (BitVec.setWidth 32 (BitVec.ofNat 64 n)).toNat = n := by
    rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat]; omega
  have hzn : BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 64 n)) = BitVec.ofNat 64 n := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_setWidth, BitVec.toNat_setWidth, BitVec.toNat_ofNat]; omega
  -- the bytes at `SetStartLen`'s entry outside the pushes
  have hVa : ∀ a : Addr, (a.toNat < X.cpu.gpr.rsp.toNat - 32 ∨ X.cpu.gpr.rsp.toNat ≤ a.toNat) →
      Vst (V0 V X.cpu.gpr) (X.cpu.gpr.rsp - 32) (toBytesLE (acc_at.add 52) 8) a = V a := by
    intro a h1
    have s1 := Tun.Vst_out (V0 V X.cpu.gpr) (X.cpu.gpr.rsp - 32) (toBytesLE (acc_at.add 52) 8) a
      (by rw [l8, tn32]; omega) (by rw [l8, tn32]; omega)
    have s3 := Tun.Vst_out (Vst V (X.cpu.gpr.rsp - 8) (toBytesLE X.cpu.gpr.rbp 8)) (X.cpu.gpr.rsp - 8 - 8)
      (toBytesLE X.cpu.gpr.rbx 8) a (by rw [l8, e16, tn16]; omega) (by rw [l8, e16, tn16]; omega)
    have s4 := Tun.Vst_out V (X.cpu.gpr.rsp - 8) (toBytesLE X.cpu.gpr.rbp 8) a (by rw [l8, tn8]; omega)
      (by rw [l8, tn8]; omega)
    exact s1.trans (s3.trans s4)
  have hH' : Mal.Hp F Wl fb hi (m + B) (Vst (V0 V X.cpu.gpr) (X.cpu.gpr.rsp - 32) (toBytesLE (acc_at.add 52) 8)) :=
    Mal.Hp.mv hH (by omega) fun a _ a2 => hVa a (.inl (by omega))
  have hTop : rdq(Vst (V0 V X.cpu.gpr) (X.cpu.gpr.rsp - 32) (toBytesLE (acc_at.add 52) 8), 7940768#64) =
      rdq(V, 7940768#64) := by
    have et : (7940768#64 : Addr).toNat = 7940768 := rfl
    rw [Sbrk.rd_eq (V := V) (x := 7940768#64) (n := 8) (by rw [et]; omega) fun a _ a2 =>
      hVa a (.inl (by rw [et] at a2; omega))]
  have hpf : X.cpu.gpr.rsi.toNat + n + 1 ≤ X.cpu.gpr.rsp.toNat - 16 ∨
      X.cpu.gpr.rsp.toNat ≤ X.cpu.gpr.rsi.toNat := .inl (by omega)
  have hpw : X.cpu.gpr.rsi.toNat + n + 1 ≤ 2 ^ 64 := by omega
  refine acc_ok (P1 := Pa F Wl fb hi m X.cpu.gpr V n) c hin hinS hinW hK hA hrip (by omega) hp8
    (hfw _ 8 tn8 (by omega) (by omega)) (hfw _ 16 tn16 (by omega) (by omega)) (hfw _ 32 tn32 (by omega) (by omega))
    (hfw _ 40 tn40 (by omega) (by omega)) (hfw _ 48 tn48 (by omega) (by omega)) (hfw _ 64 tn64 (by omega) (by omega))
    hl fw0 fw8 fw12 hq hd hn hnz hz hf hpw hpf hpt hin₂ h₂ ?_ k
  intro G hGs hGd hGn hGb hGp hG12 hG13 hG14 hG15 Y t' hKY hAY hrY hgY k'
  refine Asl.kf_hpW (g := G) (ra := acc_at.add 52) c hfs hinS hinW hinN hinI hH'
    (by show Mal.MalB (BitVec.setWidth 64 (BitVec.setWidth 32 G.rsi) + 1#64) B; rw [hGn, hzn]; exact hB)
    (by rw [hGs, tn32]; omega) (by rw [hGs, tn32]; omega)
    (fun a h1 h2 => hsw a h1 (by rw [hGs, tn32] at h2; omega))
    (by rw [hGd]; exact hq) (by rw [hGd, hGs, tn32]; omega) (by rw [hGd]; exact hdh) ?_ Y t' hKY hAY hrY hgY ?_
  · rw [hGs, Tun.rd_Vst_self (V0 V X.cpu.gpr) (X.cpu.gpr.rsp - 32) (toBytesLE (acc_at.add 52) 8) (l8 _)
      (by rw [tn32]; omega), ofBytesLE_toBytesLE (by rfl : (64 : Nat) = 8 * 8)]
  intro Z V' t'' h1 h2 h3 h4 h5 h6 h7 h8 h9 hPo
  obtain ⟨z12, z13, z14, z15, hT1, hp1, hpe, hft, hPm, hfr⟩ := hPo
  rw [hTop] at hT1
  rw [hGn, hsn] at hpe hft hPm
  rw [hGs, hGd, tn32] at hfr
  -- the bytes after `operator new` from `SetStartLen`'s return address up
  have hVr : ∀ a : Addr, X.cpu.gpr.rsp.toNat - 32 ≤ a.toNat → a.toNat < X.cpu.gpr.rsp.toNat + 8 →
      V' a = Vst (V0 V X.cpu.gpr) (X.cpu.gpr.rsp - 32) (toBytesLE (acc_at.add 52) 8) a := fun a ha hb =>
    hfr a (.inr (.inr ha)) (by omega)
  have hb1 : rdq(V', X.cpu.gpr.rsp - 16) = X.cpu.gpr.rbx := by
    rw [Sbrk.rd_eq (V := Vst (V0 V X.cpu.gpr) (X.cpu.gpr.rsp - 32) (toBytesLE (acc_at.add 52) 8))
      (x := X.cpu.gpr.rsp - 16) (n := 8) (by rw [tn16]; omega) fun a a1 a2 =>
      hVr a (by rw [tn16] at a1; omega) (by rw [tn16] at a2; omega)]
    rw [Tun.rd_Vst (V0 V X.cpu.gpr) (X.cpu.gpr.rsp - 32) (toBytesLE (acc_at.add 52) 8) (X.cpu.gpr.rsp - 16) 8
      (by rw [l8, tn32]; omega) (by rw [tn16]; omega) (by rw [l8, tn32, tn16]; omega)]
    rw [← e16, Tun.rd_Vst_self (Vst V (X.cpu.gpr.rsp - 8) (toBytesLE X.cpu.gpr.rbp 8)) (X.cpu.gpr.rsp - 8 - 8)
      (toBytesLE X.cpu.gpr.rbx 8) (l8 _) (by rw [e16, tn16]; omega),
      ofBytesLE_toBytesLE (by rfl : (64 : Nat) = 8 * 8)]
  have hb2 : rdq(V', X.cpu.gpr.rsp - 8) = X.cpu.gpr.rbp := by
    rw [Sbrk.rd_eq (V := Vst (V0 V X.cpu.gpr) (X.cpu.gpr.rsp - 32) (toBytesLE (acc_at.add 52) 8))
      (x := X.cpu.gpr.rsp - 8) (n := 8) (by rw [tn8]; omega) fun a a1 a2 =>
      hVr a (by rw [tn8] at a1; omega) (by rw [tn8] at a2; omega)]
    rw [Tun.rd_Vst (V0 V X.cpu.gpr) (X.cpu.gpr.rsp - 32) (toBytesLE (acc_at.add 52) 8) (X.cpu.gpr.rsp - 8) 8
      (by rw [l8, tn32]; omega) (by rw [tn8]; omega) (by rw [l8, tn32, tn8]; omega)]
    rw [Tun.rd_Vst (Vst V (X.cpu.gpr.rsp - 8) (toBytesLE X.cpu.gpr.rbp 8)) (X.cpu.gpr.rsp - 8 - 8)
      (toBytesLE X.cpu.gpr.rbx 8) (X.cpu.gpr.rsp - 8) 8 (by rw [l8, e16, tn16]; omega) (by rw [tn8]; omega)
      (by rw [l8, e16, tn16, tn8]; omega)]
    rw [Tun.rd_Vst_self V (X.cpu.gpr.rsp - 8) (toBytesLE X.cpu.gpr.rbp 8) (l8 _) (by rw [tn8]; omega),
      ofBytesLE_toBytesLE (by rfl : (64 : Nat) = 8 * 8)]
  have hr : rdq(V', X.cpu.gpr.rsp) = e₂.add j₂ := by
    rw [Sbrk.rd_eq (V := Vst (V0 V X.cpu.gpr) (X.cpu.gpr.rsp - 32) (toBytesLE (acc_at.add 52) 8))
      (x := X.cpu.gpr.rsp) (n := 8) hp8 fun a a1 a2 => hVr a (by omega) (by omega)]
    rw [Sbrk.rd_eq (V := V) (x := X.cpu.gpr.rsp) (n := 8) hp8 fun a a1 _ => hVa a (.inr a1)]
    exact hra
  -- the string, below the old top plus 8 (`Mal.keep_low`)
  have hkl := Mal.keep_low (Q := fun a => X.cpu.gpr.rsp.toNat - 32 ≤ a.toNat)
    (R := fun a => a.toNat < X.cpu.gpr.rdi.toNat ∨ X.cpu.gpr.rdi.toNat + 8 ≤ a.toNat) hT1 hfr
  refine k' Z V' t'' h1 h2 h3 h4 h5 h6 h7 h8 h9 ?_
  unfold Pk
  refine ⟨hb1, hb2, hr, by rw [z12, hG12], by rw [z13, hG13], by rw [z14, hG14], by rw [z15, hG15], ?_, ?_,
    by omega, .inr (by omega), .inl (by omega), hT1, hp1, hpe, hft, hPm, ?_⟩
  · intro i hi'
    have e := toNat_add_of_fits (a := X.cpu.gpr.rsi) (i := i) (n := n + 1) (by omega) (by omega)
    rw [hkl _ (by rw [e]; omega) (by rw [e]; omega) (by show _ ∨ _; rw [e]; omega)]
    exact hVa _ (.inl (by rw [e]; omega))
  · intro i hi'
    have e := toNat_add_of_fits (a := Z.cpu.gpr.rax) (i := i) (n := n + 1) (by omega) (by omega)
    exact (hft _ (by rw [e]; omega) (by rw [e]; omega)).1
  · intro a a1 a2
    rw [hfr a (by omega) a2]
    exact hVa a (by omega)

end FV7z.Acc
