import FV7z.Ucw.Holds
import FV7z.Usl.New
/-!
# `UString::UString (const wchar_t *s)` with `SetStartLen` (PLAN.md §M, M1)

`ucw_ok` takes the call of `SetStartLen (n)` as a hypothesis (`ku`); `ucw_okH` discharges it by `Usl.usl_okH` (so
`operator new (4 n + 4)` by `Onw.onw_hpW`), as `Ucc.ucc_okH` does for `UString (const UString &)`: with
`Mal.MalB (4 n + 4) B`, `Mal.Hp` with a top of at least `m + B` bytes below `hi` at the entry, `hi` 296 bytes below
`rsp`, `[hi, rsp)` in what the run may store into, the return address's slot (`rsp - 32`) in the footprint, and
`this`'s 16 bytes apart from the frame and the heap's bytes. At `wmemcpy`'s entry (`kr`) the bytes have `Pu`:
- `Pu`: `_chars` (at `this`) is a block of `4 n + 4` bytes below `hi` in the footprint, above the TLS block's words;
  `Mal.Hp … m`; the bytes outside the heap's words, the block and `this`'s 16 bytes, and from `rsp` up, as at the
  entry.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
open FV7z.Imm (imm imm_at)
open FV7z.Mnx (mnx mnx_at)
namespace FV7z.Ucw

variable {F : Footprint} {Wl : List Rgn} {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {X : State} {t : Nat} {V : Addr → Byte}

/-- The bytes `V''` at `wmemcpy`'s entry for the registers `g` and the bytes `V` at the constructor's entry and the
length `n`: see the module doc. -/
abbrev Pu (F : Footprint) (Wl : List Rgn) (fb : Addr) (hi m : Nat) (g : Gprs) (V : Addr → Byte) (n : Nat)
    (V'' : Addr → Byte) : Prop :=
  fb.toNat + 64 ≤ (rdq(V'', g.rdi)).toNat ∧ (rdq(V'', g.rdi)).toNat + (4 * n + 4) ≤ hi ∧
    (∀ a : Addr, (rdq(V'', g.rdi)).toNat ≤ a.toNat → a.toNat < (rdq(V'', g.rdi)).toNat + (4 * n + 4) →
      Foot Wl a ∧ Foot F.data a) ∧
    Mal.Hp F Wl fb hi m V'' ∧
    (∀ a : Addr, (a.toNat < 7940768 ∨ 7940776 ≤ a.toNat ∧ a.toNat + 8 < (rdq(V'', g.rdi)).toNat ∨
      g.rsp.toNat ≤ a.toNat) → (a.toNat < g.rdi.toNat ∨ g.rdi.toNat + 16 ≤ a.toNat) → V'' a = V a)

set_option maxHeartbeats 1000000 in
/-- `ucw_ok` with `SetStartLen` by `Usl.usl_okH`: see the module doc. -/
theorem ucw_okH {fb : Addr} {hi m B n : Nat} (c : Seg prof F Wl L s₀ o) (hfs : s₀.cpu.seg.fsBase = fb)
    (hin : CodeIn L ucw_at ucw) (hinU : CodeIn L Usl.usl_at Usl.usl) (hinWm : CodeIn L Wmc.wmc_at Wmc.wmc)
    (hinW : CodeIn L Onw.onw_at Onw.onw) (hinN : CodeIn L mnx_at mnx) (hinI : CodeIn L imm_at imm)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = ucw_at)
    (hH : Mal.Hp F Wl fb hi (m + B) V) (hB : Mal.MalB (BitVec.ofNat 64 n * 4#64 + 4#64) B)
    (hhi : hi + 296 ≤ X.cpu.gpr.rsp.toNat) (hp8 : X.cpu.gpr.rsp.toNat + 8 ≤ 2 ^ 64)
    (hsw : ∀ a : Addr, hi ≤ a.toNat → a.toNat < X.cpu.gpr.rsp.toNat → Foot Wl a)
    (hl4 : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rsp - 32) i))
    (fd0 : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rdi i))
    (fw0 : ∀ i < 8, Foot Wl (Addr.add X.cpu.gpr.rdi i))
    (fw8 : ∀ i < 4, Foot Wl (Addr.add (X.cpu.gpr.rdi + 8#64) i))
    (fw12 : ∀ i < 4, Foot Wl (Addr.add (X.cpu.gpr.rdi + 12#64) i))
    (hqd : X.cpu.gpr.rdi.toNat + 16 ≤ 2 ^ 64)
    (hdd : X.cpu.gpr.rdi.toNat + 16 ≤ X.cpu.gpr.rsp.toNat - 48 ∨ X.cpu.gpr.rsp.toNat + 8 ≤ X.cpu.gpr.rdi.toNat)
    (hdh : X.cpu.gpr.rdi.toNat + 16 ≤ 7940480 ∨ hi ≤ X.cpu.gpr.rdi.toNat)
    (hw : Wz F V X.cpu.gpr.rsi n)
    (hsd : ∀ i ≤ n, (Addr.add X.cpu.gpr.rsi (4 * i)).toNat + 4 ≤ 2 ^ 64 ∧
      ((Addr.add X.cpu.gpr.rsi (4 * i)).toNat + 4 ≤ X.cpu.gpr.rsp.toNat - 24 ∨
        X.cpu.gpr.rsp.toNat ≤ (Addr.add X.cpu.gpr.rsi (4 * i)).toNat))
    (kr : ∀ (Z : State) (V'' : Addr → Byte) (Y : State) (t' : Nat), Pu F Wl fb hi m X.cpu.gpr V n V'' →
      KeptW Wl s₀ Y → Agree F Y.proc.mm.mem V'' → Y.cpu.rip = Wmc.wmc_at →
      Y.cpu.gpr = { Z.cpu.gpr with
          rdi := rdq(V'', X.cpu.gpr.rdi), rdx := BitVec.ofNat 64 (n + 1), rbx := X.cpu.gpr.rbx,
          rsi := X.cpu.gpr.rsi, rbp := X.cpu.gpr.rbp, r12 := X.cpu.gpr.r12, rsp := X.cpu.gpr.rsp } →
      GoG prof L o gev gP gE Y t') :
    GoG prof L o gev gP gE X t := by
  have hlt := X.cpu.gpr.rsp.isLt
  have hTl : 8032256 ≤ hi ∧ hi < 2 ^ 64 := by
    obtain ⟨_, T, _, _, _, -, -, -, -, hT, hTh, hhi', -⟩ := hH
    omega
  have hB3 : 64 ≤ B := hB.2.2
  have hn : n + 1 < 2 ^ 32 := hw.1
  have tn8 : (X.cpu.gpr.rsp - 8).toNat = X.cpu.gpr.rsp.toNat - 8 := by rw [BitVec.toNat_sub]; simp <;> omega
  have tn16 : (X.cpu.gpr.rsp - 16).toNat = X.cpu.gpr.rsp.toNat - 16 := by rw [BitVec.toNat_sub]; simp <;> omega
  have tn24 : (X.cpu.gpr.rsp - 24).toNat = X.cpu.gpr.rsp.toNat - 24 := by rw [BitVec.toNat_sub]; simp <;> omega
  have tn32 : (X.cpu.gpr.rsp - 32).toNat = X.cpu.gpr.rsp.toNat - 32 := by rw [BitVec.toNat_sub]; simp <;> omega
  have e16 : X.cpu.gpr.rsp - 8 - 8 = X.cpu.gpr.rsp - 16 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, tn8, tn16]
    simp <;> omega
  have e24 : X.cpu.gpr.rsp - 8 - 8 - 8 = X.cpu.gpr.rsp - 24 := by
    rw [e16]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, tn16, tn24]
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
  have hzn : BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 64 n)) = BitVec.ofNat 64 n := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_setWidth, BitVec.toNat_setWidth, BitVec.toNat_ofNat]; omega
  -- the bytes at `SetStartLen`'s entry outside the pushes
  have hVo : ∀ a : Addr, (a.toNat < X.cpu.gpr.rsp.toNat - 32 ∨ X.cpu.gpr.rsp.toNat ≤ a.toNat) →
      Vst (V0 V X.cpu.gpr) (X.cpu.gpr.rsp - 32) (toBytesLE (ucw_at.add 60) 8) a = V a := by
    intro a h1
    have s1 := Tun.Vst_out (V0 V X.cpu.gpr) (X.cpu.gpr.rsp - 32) (toBytesLE (ucw_at.add 60) 8) a
      (by rw [l8, tn32]; omega) (by rw [l8, tn32]; omega)
    have s2 := Tun.Vst_out (Vst (Vst V (X.cpu.gpr.rsp - 8) (toBytesLE X.cpu.gpr.r12 8)) (X.cpu.gpr.rsp - 8 - 8)
      (toBytesLE X.cpu.gpr.rbp 8)) (X.cpu.gpr.rsp - 8 - 8 - 8) (toBytesLE X.cpu.gpr.rbx 8) a
      (by rw [l8, e24, tn24]; omega) (by rw [l8, e24, tn24]; omega)
    have s3 := Tun.Vst_out (Vst V (X.cpu.gpr.rsp - 8) (toBytesLE X.cpu.gpr.r12 8)) (X.cpu.gpr.rsp - 8 - 8)
      (toBytesLE X.cpu.gpr.rbp 8) a (by rw [l8, e16, tn16]; omega) (by rw [l8, e16, tn16]; omega)
    have s4 := Tun.Vst_out V (X.cpu.gpr.rsp - 8) (toBytesLE X.cpu.gpr.r12 8) a (by rw [l8, tn8]; omega)
      (by rw [l8, tn8]; omega)
    exact s1.trans (s2.trans (s3.trans s4))
  have hH' : Mal.Hp F Wl fb hi (m + B) (Vst (V0 V X.cpu.gpr) (X.cpu.gpr.rsp - 32) (toBytesLE (ucw_at.add 60) 8)) :=
    Mal.Hp.mv hH (by omega) fun a _ a2 => hVo a (.inl (by omega))
  refine ucw_ok (Pu := fun _ V'' => Pu F Wl fb hi m X.cpu.gpr V n V'') c hin hinU hinWm hK hA hrip (by omega)
    (hfw _ 8 tn8 (by omega) (by omega)) (hfw _ 16 tn16 (by omega) (by omega)) (hfw _ 24 tn24 (by omega) (by omega))
    (hfw _ 32 tn32 (by omega) (by omega)) fd0 hw hsd ?_ kr
  intro Y t' a d hKY hAY hrY hgY k
  have hYs : Y.cpu.gpr.rsp = X.cpu.gpr.rsp - 32 := by rw [hgY]; try rfl
  have hYd : Y.cpu.gpr.rdi = X.cpu.gpr.rdi := by rw [hgY]; try rfl
  have hYb : Y.cpu.gpr.rbx = X.cpu.gpr.rdi := by rw [hgY]; try rfl
  have hYp : Y.cpu.gpr.rbp = X.cpu.gpr.rsi := by rw [hgY]; try rfl
  have hYr : Y.cpu.gpr.r12 = BitVec.ofNat 64 (n + 1) := by rw [hgY]; try rfl
  have hYi : Y.cpu.gpr.rsi = BitVec.ofNat 64 n := by rw [hgY]; try rfl
  have hYt : Y.cpu.gpr.rsp.toNat = X.cpu.gpr.rsp.toNat - 32 := by rw [hYs, tn32]
  have hYn : (BitVec.setWidth 32 Y.cpu.gpr.rsi).toNat = n := by
    rw [hYi, BitVec.toNat_setWidth, BitVec.toNat_ofNat]; omega
  have hra : rdq(Vst (V0 V X.cpu.gpr) (X.cpu.gpr.rsp - 32) (toBytesLE (ucw_at.add 60) 8), Y.cpu.gpr.rsp) =
      ucw_at.add 60 := by
    rw [hYs, Tun.rd_Vst_self (V0 V X.cpu.gpr) (X.cpu.gpr.rsp - 32) (toBytesLE (ucw_at.add 60) 8) (l8 _)
      (by rw [tn32]; omega), ofBytesLE_toBytesLE (by rfl : (64 : Nat) = 8 * 8)]
  refine Usl.usl_okH (B := B) (m := m) c hfs hinU hinW hinN hinI hKY hAY hrY hH'
    (by show Mal.MalB (BitVec.setWidth 64 (BitVec.setWidth 32 Y.cpu.gpr.rsi) * 4#64 + 4#64) B
        rw [hYi, hzn]; exact hB)
    (by rw [hYt]; omega) (by rw [hYt]; omega) (by rw [hYt]; omega)
    (fun a h1 h2 => hsw a h1 (by rw [hYt] at h2; omega)) (by rw [hYs]; exact hl4)
    (by rw [hYd]; exact fw0) (by rw [hYd]; exact fw8) (by rw [hYd]; exact fw12) (by rw [hYd]; exact hqd)
    (by rw [hYd, hYt]; omega) (by rw [hYd]; exact hdh) hin (j₂ := 60) (by decide) hra ?_
  intro Z V' Z' t'' h12 _ hp1 hp2 hft hHp hfr hKZ' hAZ' hrZ' hgZ'
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
  -- the frame at and above `SetStartLen`'s return address
  have hVr : ∀ a : Addr, X.cpu.gpr.rsp.toNat - 32 ≤ a.toNat → a.toNat < X.cpu.gpr.rsp.toNat →
      Usl.V1 V' X.cpu.gpr.rdi (BitVec.setWidth 32 Y.cpu.gpr.rsi) Z.cpu.gpr.rax a =
        Vst (V0 V X.cpu.gpr) (X.cpu.gpr.rsp - 32) (toBytesLE (ucw_at.add 60) 8) a := fun a a1 a2 =>
    (hV1 a (by omega)).trans (hfr a (.inr (.inr (by rw [hYt]; exact a1))) (by omega))
  have hb1 : rdq(Usl.V1 V' X.cpu.gpr.rdi (BitVec.setWidth 32 Y.cpu.gpr.rsi) Z.cpu.gpr.rax, X.cpu.gpr.rsp - 24) =
      X.cpu.gpr.rbx := by
    rw [Sbrk.rd_eq (V := Vst (V0 V X.cpu.gpr) (X.cpu.gpr.rsp - 32) (toBytesLE (ucw_at.add 60) 8))
      (x := X.cpu.gpr.rsp - 24) (n := 8) (by rw [tn24]; omega)
      fun a a1 a2 => hVr a (by rw [tn24] at a1; omega) (by rw [tn24] at a2; omega)]
    rw [Tun.rd_Vst (V0 V X.cpu.gpr) (X.cpu.gpr.rsp - 32) (toBytesLE (ucw_at.add 60) 8) (X.cpu.gpr.rsp - 24) 8
      (by rw [l8, tn32]; omega) (by rw [tn24]; omega) (by rw [l8, tn32, tn24]; omega)]
    rw [← e24, Tun.rd_Vst_self (Vst (Vst V (X.cpu.gpr.rsp - 8) (toBytesLE X.cpu.gpr.r12 8)) (X.cpu.gpr.rsp - 8 - 8)
      (toBytesLE X.cpu.gpr.rbp 8)) (X.cpu.gpr.rsp - 8 - 8 - 8) (toBytesLE X.cpu.gpr.rbx 8) (l8 _)
      (by rw [e24, tn24]; omega), ofBytesLE_toBytesLE (by rfl : (64 : Nat) = 8 * 8)]
  have hb2 : rdq(Usl.V1 V' X.cpu.gpr.rdi (BitVec.setWidth 32 Y.cpu.gpr.rsi) Z.cpu.gpr.rax, X.cpu.gpr.rsp - 16) =
      X.cpu.gpr.rbp := by
    rw [Sbrk.rd_eq (V := Vst (V0 V X.cpu.gpr) (X.cpu.gpr.rsp - 32) (toBytesLE (ucw_at.add 60) 8))
      (x := X.cpu.gpr.rsp - 16) (n := 8) (by rw [tn16]; omega)
      fun a a1 a2 => hVr a (by rw [tn16] at a1; omega) (by rw [tn16] at a2; omega)]
    rw [Tun.rd_Vst (V0 V X.cpu.gpr) (X.cpu.gpr.rsp - 32) (toBytesLE (ucw_at.add 60) 8) (X.cpu.gpr.rsp - 16) 8
      (by rw [l8, tn32]; omega) (by rw [tn16]; omega) (by rw [l8, tn32, tn16]; omega)]
    rw [Tun.rd_Vst (Vst (Vst V (X.cpu.gpr.rsp - 8) (toBytesLE X.cpu.gpr.r12 8)) (X.cpu.gpr.rsp - 8 - 8)
      (toBytesLE X.cpu.gpr.rbp 8)) (X.cpu.gpr.rsp - 8 - 8 - 8) (toBytesLE X.cpu.gpr.rbx 8) (X.cpu.gpr.rsp - 16) 8
      (by rw [l8, e24, tn24]; omega) (by rw [tn16]; omega) (by rw [l8, e24, tn24, tn16]; omega)]
    rw [← e16, Tun.rd_Vst_self (Vst V (X.cpu.gpr.rsp - 8) (toBytesLE X.cpu.gpr.r12 8)) (X.cpu.gpr.rsp - 8 - 8)
      (toBytesLE X.cpu.gpr.rbp 8) (l8 _) (by rw [e16, tn16]; omega),
      ofBytesLE_toBytesLE (by rfl : (64 : Nat) = 8 * 8)]
  have hb3 : rdq(Usl.V1 V' X.cpu.gpr.rdi (BitVec.setWidth 32 Y.cpu.gpr.rsi) Z.cpu.gpr.rax, X.cpu.gpr.rsp - 8) =
      X.cpu.gpr.r12 := by
    rw [Sbrk.rd_eq (V := Vst (V0 V X.cpu.gpr) (X.cpu.gpr.rsp - 32) (toBytesLE (ucw_at.add 60) 8))
      (x := X.cpu.gpr.rsp - 8) (n := 8) (by rw [tn8]; omega)
      fun a a1 a2 => hVr a (by rw [tn8] at a1; omega) (by rw [tn8] at a2; omega)]
    rw [Tun.rd_Vst (V0 V X.cpu.gpr) (X.cpu.gpr.rsp - 32) (toBytesLE (ucw_at.add 60) 8) (X.cpu.gpr.rsp - 8) 8
      (by rw [l8, tn32]; omega) (by rw [tn8]; omega) (by rw [l8, tn32, tn8]; omega)]
    rw [Tun.rd_Vst (Vst (Vst V (X.cpu.gpr.rsp - 8) (toBytesLE X.cpu.gpr.r12 8)) (X.cpu.gpr.rsp - 8 - 8)
      (toBytesLE X.cpu.gpr.rbp 8)) (X.cpu.gpr.rsp - 8 - 8 - 8) (toBytesLE X.cpu.gpr.rbx 8) (X.cpu.gpr.rsp - 8) 8
      (by rw [l8, e24, tn24]; omega) (by rw [tn8]; omega) (by rw [l8, e24, tn24, tn8]; omega)]
    rw [Tun.rd_Vst (Vst V (X.cpu.gpr.rsp - 8) (toBytesLE X.cpu.gpr.r12 8)) (X.cpu.gpr.rsp - 8 - 8)
      (toBytesLE X.cpu.gpr.rbp 8) (X.cpu.gpr.rsp - 8) 8 (by rw [l8, e16, tn16]; omega) (by rw [tn8]; omega)
      (by rw [l8, e16, tn16, tn8]; omega)]
    rw [Tun.rd_Vst_self V (X.cpu.gpr.rsp - 8) (toBytesLE X.cpu.gpr.r12 8) (l8 _) (by rw [tn8]; omega),
      ofBytesLE_toBytesLE (by rfl : (64 : Nat) = 8 * 8)]
  have zsp : Z'.cpu.gpr.rsp = X.cpu.gpr.rsp - 24 := by
    rw [hgZ']
    show Y.cpu.gpr.rsp + 8 = _
    rw [hYs]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, tn32, tn24]
    simp <;> omega
  refine k Z' _ t'' hKZ' hAZ' hrZ' zsp (by rw [hgZ']; exact hYb) (by rw [hgZ']; exact hYp)
    (by rw [hgZ']; exact h12.trans hYr) ⟨hb1, hb2, hb3⟩
    ⟨by rw [hrax]; exact hp1, by rw [hrax]; exact hp2, by rw [hrax]; exact hft, hHp, ?_⟩
  intro a h1 h2
  rw [hrax] at h1
  rw [hV1 a h2]
  have hva : V' a = Vst (V0 V X.cpu.gpr) (X.cpu.gpr.rsp - 32) (toBytesLE (ucw_at.add 60) 8) a := by
    rcases h1 with h1 | h1 | h1
    · exact hfr a (.inl h1) (by omega)
    · exact hfr a (.inr (.inl h1)) (by omega)
    · exact hfr a (.inr (.inr (by rw [hYt]; omega))) (by omega)
  rw [hva]
  exact hVo a (by rcases h1 with h1 | h1 | h1 <;> omega)

end FV7z.Ucw
