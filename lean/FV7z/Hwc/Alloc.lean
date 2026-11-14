import FV7z.Hwc.Call
/-!
# `_dl_important_hwcaps`: 1050 → the `ret` (PLAN.md G3, startup)

The block before the `call` of `malloc` (1050 → 1111, `vc_1050`): `total << (cnt - 3)`, the five stores `M5` (the
last entry of `temp` at `rbp - 0x68`, `cnt` at `rbp - 0x60`, `1 << cnt` at `rbp - 0x8c`, `*ncapstr` and
`rbp - 0x88`), then `from1111` (`Call`).

- `rem_3`, `rem_4`: the bytes of the strings for the lengths of `temp` on this path (`6`, `0`, `3`; `6`, `8`, `0`, `3`)
  fill what `malloc` is asked for past the table exactly (23, 64).
- `M5` and its loads; `from1050`.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn

namespace FV7z.Hwc

set_option maxRecDepth 100000

/-! ## The bytes of the strings -/

theorem rem_3 {ln : Nat → Addr} (h0 : (ln 0).toNat = 6) (h1 : (ln 1).toNat = 0) (h2 : (ln 2).toNat = 3) :
    rem 3 ln 4 = 23 := by
  have hw : ∀ n, wid 3 ln n = 3 + 1 + ((if n.testBit 1 then 0 + 1 else 0) + 0) + (6 + 1) := fun n => by
    show (ln 2).toNat + 1 + ((if n.testBit 1 then (ln 1).toNat + 1 else 0) + 0) + ((ln 0).toNat + 1) = _
    rw [h0, h1, h2]
  show wid 3 ln 2 + (wid 3 ln 0 + 0) = 23
  rw [hw, hw]
  decide

theorem rem_4 {ln : Nat → Addr} (h0 : (ln 0).toNat = 6) (h1 : (ln 1).toNat = 8) (h2 : (ln 2).toNat = 0)
    (h3 : (ln 3).toNat = 3) : rem 4 ln 8 = 64 := by
  have hw : ∀ n, wid 4 ln n = 3 + 1 + ((if n.testBit 2 then 0 + 1 else 0) +
      ((if n.testBit 1 then 8 + 1 else 0) + 0)) + (6 + 1) := fun n => by
    show (ln 3).toNat + 1 + ((if n.testBit 2 then (ln 2).toNat + 1 else 0) +
      ((if n.testBit 1 then (ln 1).toNat + 1 else 0) + 0)) + ((ln 0).toNat + 1) = _
    rw [h0, h1, h2, h3]
  show wid 4 ln 6 + (wid 4 ln 4 + (wid 4 ln 2 + (wid 4 ln 0 + 0))) = 64
  rw [hw, hw, hw, hw]
  decide

/-! ## Bytes kept but for `*ncapstr` -/

/-- `W` is `V` on `[lo, hi)` but for the 8 bytes at `N` (`*ncapstr`, a variable of the caller's: in `.bss` for
`_dl_init_paths`). -/
def SameO (V W : Addr → Byte) (lo hi : Nat) (N : Addr) : Prop :=
  ∀ a : Addr, lo ≤ a.toNat → a.toNat < hi → (a.toNat < N.toNat ∨ N.toNat + 8 ≤ a.toNat) → W a = V a

theorem SameO.trans {U V W : Addr → Byte} {lo hi : Nat} {N : Addr} (h1 : Same U V lo hi) (h2 : SameO V W lo hi N) :
    SameO U W lo hi N := fun a a1 a2 a3 => (h2 a a1 a2 a3).trans (h1 a a1 a2)

theorem SameO.mono {V W : Addr → Byte} {lo hi lo' hi' : Nat} {N : Addr} (h : SameO V W lo hi N) (h1 : lo ≤ lo')
    (h2 : hi' ≤ hi) : SameO V W lo' hi' N := fun a a1 a2 a3 => h a (by omega) (by omega) a3

/-! ## The five stores of 1050 -/

/-- The bytes at the `call` of `malloc`: `D` (the last entry of `temp`) at `rbp - 0x68`, `cnt` at `rbp - 0x60`,
`1 << cnt` at `rbp - 0x8c`, at `N` (`*ncapstr`) and at `rbp - 0x88`. -/
def M5 (V : Addr → Byte) (bp D N : Addr) (cnt : Nat) : Addr → Byte :=
  Vst (Vst (Vst (Vst (Vst V (bp + 18446744073709551512#64) (toBytesLE D 8))
    (bp + 18446744073709551520#64) (toBytesLE (BitVec.ofNat 32 cnt) 4))
    (bp + 18446744073709551476#64) (toBytesLE (BitVec.ofNat 32 (2 ^ cnt)) 4)) N
    (toBytesLE (BitVec.ofNat 64 (2 ^ cnt)) 8)) (bp + 18446744073709551480#64)
    (toBytesLE (BitVec.ofNat 64 (2 ^ cnt)) 8)

section
variable (V : Addr → Byte) (bp D N : Addr) (cnt : Nat)
  (hfb : (bp + 18446744073709551448#64).toNat + 176 ≤ 2 ^ 64)
  (hN : N.toNat + 8 ≤ (bp + 18446744073709551448#64).toNat ∨ (bp + 18446744073709551448#64).toNat + 176 ≤ N.toNat)
  (hN64 : N.toNat + 8 ≤ 2 ^ 64)
include hfb hN hN64

/-- The bytes `M5` keeps: all but `rbp - 0x8c .. rbp - 0x80`, `rbp - 0x68 .. rbp - 0x5c` and `N .. N + 8`. -/
theorem M5.same {lo hi : Nat} (h1 : hi ≤ (bp + 18446744073709551448#64).toNat + 28 ∨
      (bp + 18446744073709551448#64).toNat + 40 ≤ lo ∧ hi ≤ (bp + 18446744073709551448#64).toNat + 64 ∨
      (bp + 18446744073709551448#64).toNat + 76 ≤ lo) (h2 : hi ≤ N.toNat ∨ N.toNat + 8 ≤ lo) :
    Same V (M5 V bp D N cnt) lo hi := by
  unfold M5
  iterate 5 refine Same.st ?_ (by fomega) (by fomega)
  exact Same.refl _ _ _

theorem M5.rd60 : rdd(M5 V bp D N cnt, bp + 18446744073709551520#64) = BitVec.ofNat 32 cnt := by
  unfold M5
  vpeel
  rw [Tun.rd_Vst_self _ _ _ (toBytesLE_length _ _) (by fomega), ofBytesLE_toBytesLE (n := 4) rfl]

theorem M5.rd68 : rdq(M5 V bp D N cnt, bp + 18446744073709551512#64) = D := by
  unfold M5
  vpeel
  rw [Tun.rd_Vst_self _ _ _ (toBytesLE_length _ _) (by fomega), ofBytesLE_toBytesLE (n := 8) rfl]

theorem M5.rd8c : rdd(M5 V bp D N cnt, bp + 18446744073709551476#64) = BitVec.ofNat 32 (2 ^ cnt) := by
  unfold M5
  vpeel
  rw [Tun.rd_Vst_self _ _ _ (toBytesLE_length _ _) (by fomega), ofBytesLE_toBytesLE (n := 4) rfl]

omit hN hN64 in
theorem M5.rd88 : rdq(M5 V bp D N cnt, bp + 18446744073709551480#64) = BitVec.ofNat 64 (2 ^ cnt) := by
  unfold M5
  rw [Tun.rd_Vst_self _ _ _ (toBytesLE_length _ _) (by fomega), ofBytesLE_toBytesLE (n := 8) rfl]

theorem M5.rdN : rdq(M5 V bp D N cnt, N) = BitVec.ofNat 64 (2 ^ cnt) := by
  unfold M5
  vpeel
  rw [Tun.rd_Vst_self _ _ _ (toBytesLE_length _ _) (by fomega), ofBytesLE_toBytesLE (n := 8) rfl]

end

/-! ## 1050 → 1681 -/

variable {prof : Profile} {F : Footprint} {Wl : List Rgn} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop} {fb : Addr}
  {cpy mlc : List Byte} {Pm Pa : (Addr → Byte) → Prop}

set_option maxHeartbeats 4000000 in
/-- From 1050 (`rsi = cnt`, `rax` the total `t` of the lengths, `rdx` the last entry of `temp`): the stores `M5`, the
`call` of `malloc (s)` and on to the `ret` (1681). `N` (`ncapstr`) is below the allocator's bytes (`.bss`) or above
this frame. -/
theorem from1050 (c : Seg prof F Wl L s₀ o) (hfs : s₀.cpu.seg.fsBase = fb) (hin : CodeIn L hwc_at hwc)
    (hinc : CodeIn L 4198592#64 cpy) (hc0 : 0 < cpy.length) (hcpy : Gor.PcpyAt prof L o 4198592#64 Pm)
    (hinm : CodeIn L 6500704#64 mlc) (hm0 : 0 < mlc.length) (hmal : Mal.At prof L o 6500704#64 Pa)
    {V : Addr → Byte} {cnt E H t s : Nat} {R bp sp Q N : Addr} {ln st : Nat → Addr}
    (hPm : ∀ W : Addr → Byte, (∀ a : Addr, a.toNat < 7940480 → (a.toNat < N.toNat ∨ N.toNat + 8 ≤ a.toNat) →
      W a = V a) → Pm W)
    (hPa : ∀ W : Addr → Byte, (∀ a : Addr, a.toNat < sp.toNat - 8 → (a.toNat < N.toNat ∨ N.toNat + 8 ≤ a.toNat) →
      W a = V a) → Pa W)
    (hn : cnt = 3 ∧ E = 8 ∧ H = 4 ∧ t = 23 ∧ s = 151 ∨ cnt = 4 ∧ E = 16 ∧ H = 8 ∧ t = 32 ∧ s = 320)
    (hlv : cnt = 3 ∧ (ln 0).toNat = 6 ∧ (ln 1).toNat = 0 ∧ (ln 2).toNat = 3 ∨
      cnt = 4 ∧ (ln 0).toNat = 6 ∧ (ln 1).toNat = 8 ∧ (ln 2).toNat = 0 ∧ (ln 3).toNat = 3)
    (hspl : 7940480 ≤ sp.toNat)
    (hRs : sp.toNat ≤ R.toNat) (hRF : R.toNat + 16 * cnt ≤ (bp + 18446744073709551448#64).toNat)
    (hfb : (bp + 18446744073709551448#64).toNat + 176 ≤ 2 ^ 64)
    (hst : ∀ i < 8, Foot Wl (Addr.add (sp - 8) i))
    (hFr : ∀ a : Addr, (bp + 18446744073709551448#64).toNat ≤ a.toNat →
      a.toNat < (bp + 18446744073709551448#64).toNat + 176 → Foot Wl a ∧ Foot F.data a)
    (hFT : ∀ a : Addr, R.toNat ≤ a.toNat → a.toNat < R.toNat + 16 * cnt → Foot F.data a)
    (hT : ∀ m < cnt, rdq(V, R + BitVec.ofNat 64 (16 * m)) = st m ∧ rdq(V, R + BitVec.ofNat 64 (16 * m + 8)) = ln m)
    (hsrc : ∀ m < cnt, ∀ i < (ln m).toNat, Foot F.data ((st m).add i))
    (hs64 : ∀ m < cnt, (st m).toNat + (ln m).toNat ≤ 2 ^ 64)
    (hsd : ∀ m < cnt, (st m).toNat + (ln m).toNat ≤ 7940480 ∨ sp.toNat ≤ (st m).toNat)
    (hNv : rdq(V, bp + 18446744073709551528#64) = N)
    (hND : N.toNat + 8 ≤ 7940480 ∨ (bp + 18446744073709551448#64).toNat + 176 ≤ N.toNat)
    (hN64 : N.toNat + 8 ≤ 2 ^ 64) (hsN : ∀ i < 8, Foot Wl (Addr.add N i))
    (hD8 : rdq(V, bp + 18446744073709551464#64) = BitVec.ofNat 64 (16 * cnt))
    (hL : rdq(V, bp + 18446744073709551536#64) = ln (cnt - 1))
    (hl : rdq(V, bp + 18446744073709551544#64) = ln 0)
    (hQ : rdq(V, bp + 18446744073709551504#64) = Q) (hsQ : ∀ i < 8, Foot Wl (Addr.add Q i))
    (hQ64 : Q.toNat + 8 ≤ 2 ^ 64)
    (hQd : Q.toNat + 8 ≤ (bp + 18446744073709551448#64).toNat + 128 ∨
      (bp + 18446744073709551448#64).toNat + 176 ≤ Q.toNat)
    (k : ∀ Y t' (W : Addr → Byte) (P : Addr), KeptW Wl s₀ Y →
      Agree F Y.proc.mm.mem (Vst W Q (toBytesLE (caps E (tlen V R) cnt (fun _ => 0#64) 0) 8)) →
      Y.cpu.rip = hwc_at.add 1681 → Y.cpu.gpr.rax = P → 7940480 ≤ P.toNat → P.toNat + s ≤ sp.toNat - 8 →
      (∀ a : Addr, P.toNat ≤ a.toNat → a.toNat < P.toNat + s → Foot Wl a ∧ Foot F.data a) →
      Y.cpu.gpr.rsp = bp + 8#64 →
      Y.cpu.gpr.rbx = rdq(V, bp + 18446744073709551576#64) → Y.cpu.gpr.r12 = rdq(V, bp + 18446744073709551584#64) →
      Y.cpu.gpr.r13 = rdq(V, bp + 18446744073709551592#64) → Y.cpu.gpr.r14 = rdq(V, bp + 18446744073709551600#64) →
      Y.cpu.gpr.r15 = rdq(V, bp + 18446744073709551608#64) → Y.cpu.gpr.rbp = rdq(V, bp) →
      Tab W P E (pt (fun _ => P + BitVec.ofNat 64 (16 * E)) (caps E (tlen V R) cnt (fun _ => 0#64)) H (ln (cnt - 1)))
        (caps E (tlen V R) cnt (fun _ => 0#64)) →
      SameO V W 0 7940480 N → Same V W sp.toNat (bp + 18446744073709551448#64).toNat →
      SameO V W ((bp + 18446744073709551448#64).toNat + 88) (2 ^ 64) N → rdq(W, N) = BitVec.ofNat 64 E →
      GoG prof L o gev gP gE Y t') :
    ∀ (X : State) (t₀ : Nat), KeptW Wl s₀ X → Agree F X.proc.mm.mem V → X.cpu.rip = hwc_at.add 1050 →
      X.cpu.gpr.rsi = BitVec.ofNat 64 cnt → X.cpu.gpr.rax = BitVec.ofNat 64 t →
      X.cpu.gpr.rdx = R + BitVec.ofNat 64 (16 * (cnt - 1)) → X.cpu.gpr.r12 = BitVec.ofNat 64 cnt →
      X.cpu.gpr.rbx = R → X.cpu.gpr.rbp = bp → X.cpu.gpr.rsp = sp → GoG prof L o gev gP gE X t₀ := by
  intro X t₀ hK hA hrip hsi hax hdx h12 hbx hbp hsp
  have h2E : 2 ^ cnt = E := by rcases hn with ⟨rfl, rfl, -⟩ | ⟨rfl, rfl, -⟩ <;> rfl
  have hsz : 16 * E + rem cnt ln H ≤ s := by
    rcases hn with ⟨rfl, rfl, rfl, -, rfl⟩ | ⟨rfl, rfl, rfl, -, rfl⟩
    · obtain ⟨-, h0, h1, h2⟩ | ⟨h, -⟩ := hlv
      · have := rem_3 h0 h1 h2
        omega
      · omega
    · obtain ⟨h, -⟩ | ⟨-, h0, h1, h2, h3⟩ := hlv
      · omega
      · have := rem_4 h0 h1 h2 h3
        omega
  have hFrW : ∀ a : Addr, (bp + 18446744073709551448#64).toNat ≤ a.toNat →
      a.toNat < (bp + 18446744073709551448#64).toNat + 176 → Foot Wl a := fun a h1 h2 => (hFr a h1 h2).1
  have hFrD : ∀ a : Addr, (bp + 18446744073709551448#64).toNat ≤ a.toNat →
      a.toNat < (bp + 18446744073709551448#64).toNat + 176 → Foot F.data a := fun a h1 h2 => (hFr a h1 h2).2
  -- 1050 → 1111
  refine (c_1050 prof fb).run c hfs hin _ hK hA hrip
    (vc_1050 (n := cnt) (t := t) (t' := s - 16 * E) (r := 16 * E) (s := s) (N := N) (by omega) hsi hax
      (by rw [hbp]; vpeel; exact hNv)
      (by rw [hbp]; exact rng hFrW (by fomega) (by fomega) (by fomega))
      (by rw [hbp]; exact rng hFrW (by fomega) (by fomega) (by fomega))
      (by rw [hbp]; exact rng hFrW (by fomega) (by fomega) (by fomega))
      hsN
      (by rw [hbp]; exact rng hFrW (by fomega) (by fomega) (by fomega))
      (by rw [hbp]; exact rng hFrD (by fomega) (by fomega) (by fomega))) ?_
  rintro j' g fl V' ⟨rfl, rfl, rfl⟩ Y t' hKY hAY hrY hgY -
  have hAY' : Agree F Y.proc.mm.mem (M5 V bp (R + BitVec.ofNat 64 (16 * (cnt - 1))) N cnt) := by
    rw [hbp, hdx] at hAY
    exact hAY
  have hN' : N.toNat + 8 ≤ (bp + 18446744073709551448#64).toNat ∨
      (bp + 18446744073709551448#64).toNat + 176 ≤ N.toNat := by omega
  have hSm := @M5.same V bp (R + BitVec.ofNat 64 (16 * (cnt - 1))) N cnt hfb hN' hN64
  have hS1 : ∀ {x : Addr} {n : Nat}, x.toNat + n ≤ 2 ^ 64 →
      (x.toNat + n ≤ (bp + 18446744073709551448#64).toNat + 28 ∨
        (bp + 18446744073709551448#64).toNat + 40 ≤ x.toNat ∧
          x.toNat + n ≤ (bp + 18446744073709551448#64).toNat + 64 ∨
        (bp + 18446744073709551448#64).toNat + 76 ≤ x.toNat) →
      (x.toNat + n ≤ N.toNat ∨ N.toNat + 8 ≤ x.toNat) →
      List.map (M5 V bp (R + BitVec.ofNat 64 (16 * (cnt - 1))) N cnt) (byteAddrs x n) =
        List.map V (byteAddrs x n) :=
    fun {x n} hx h1 h2 => (hSm (lo := x.toNat) (hi := x.toNat + n) h1 h2).rd (Nat.le_refl _) (Nat.le_refl _) hx
  refine from1111 c hfs hin hinc hc0 hcpy hinm hm0 hmal (V := M5 V bp (R + BitVec.ofNat 64 (16 * (cnt - 1))) N cnt)
    (fun W hW => hPm W fun a ha hn => (hW a ha).trans (hSm (lo := a.toNat) (hi := a.toNat + 1) (by fomega)
      (by fomega) a (Nat.le_refl _) (by omega)))
    (fun W hW => hPa W fun a ha hn => (hW a ha).trans (hSm (lo := a.toNat) (hi := a.toNat + 1) (by fomega)
      (by fomega) a (Nat.le_refl _) (by omega)))
    (H := H) (sp := sp) (ln := ln) (st := st) (by omega) hsz (by omega) (by fomega) hRs hRF hfb hst hFr hFT
    (fun m hm => by
      have e1 : (R + BitVec.ofNat 64 (16 * m + 8)).toNat = R.toNat + (16 * m + 8) := addO (by fomega)
      have e2 : (R + BitVec.ofNat 64 (16 * m)).toNat = R.toNat + 16 * m := addO (by fomega)
      rw [hS1 (by fomega) (by fomega) (by fomega), hS1 (by fomega) (by fomega) (by fomega)]
      exact hT m hm)
    hsrc hs64 hsd (M5.rd60 V bp _ N cnt hfb hN' hN64) (M5.rd68 V bp _ N cnt hfb hN' hN64)
    (by rw [M5.rd88 V bp _ N cnt hfb, h2E])
    (by rw [hS1 (by fomega) (by fomega) (by fomega)]; exact hD8)
    (by rw [M5.rd8c V bp _ N cnt hfb hN' hN64, h2E])
    (by rw [hS1 (by fomega) (by fomega) (by fomega)]; exact hL)
    (by rw [hS1 (by fomega) (by fomega) (by fomega)]; exact hl)
    (by rw [hS1 (by fomega) (by fomega) (by fomega)]; exact hQ) hsQ hQ64 hQd ?_ Y t' hKY hAY' hrY
    (by rw [hgY]) (by rw [hgY]; exact h12) (by rw [hgY]) (by rw [hgY]; exact hbx) (by rw [hgY]; exact hbp)
    (by rw [hgY]; exact hsp)
  intro Z t₂ W P hKZ hAZ hrZ haxZ hlo hpe hWP hspZ hbxZ h12Z h13Z h14Z h15Z hbpZ hTab hS0 hSs hSh
  have htl : ∀ j < cnt, tlen (M5 V bp (R + BitVec.ofNat 64 (16 * (cnt - 1))) N cnt) R j = tlen V R j :=
    fun j hj => by
      have e : (R + BitVec.ofNat 64 (16 * j + 8)).toNat = R.toNat + (16 * j + 8) := addO (by fomega)
      unfold tlen
      rw [hS1 (by fomega) (by fomega) (by fomega)]
  have hcp := caps_congr (E := E) cnt (fun _ => 0#64) htl
  rw [hcp] at hAZ hTab
  rw [hS1 (by fomega) (by fomega) (by fomega)] at hbxZ h12Z h13Z h14Z h15Z
  rw [hS1 (by fomega) (by fomega) (by fomega)] at hbpZ
  have hWN : rdq(W, N) = BitVec.ofNat 64 E := by
    rcases hND with hN | hN
    · rw [hS0.rd (Nat.zero_le _) hN hN64, M5.rdN V bp _ N cnt hfb hN' hN64, h2E]
    · rw [hSh.rd (by fomega) (by fomega) hN64, M5.rdN V bp _ N cnt hfb hN' hN64, h2E]
  exact k Z t₂ W P hKZ hAZ hrZ haxZ hlo hpe hWP hspZ hbxZ h12Z h13Z h14Z h15Z hbpZ hTab
    (fun a h1 h2 hn => (hS0 a h1 h2).trans (hSm (lo := a.toNat) (hi := a.toNat + 1) (by fomega) (by fomega) a
      (Nat.le_refl _) (by omega)))
    (fun a h1 h2 => (hSs a h1 h2).trans (hSm (lo := a.toNat) (hi := a.toNat + 1) (by fomega) (by fomega) a
      (Nat.le_refl _) (by omega)))
    (fun a h1 h2 hn => (hSh a (by omega) h2).trans (hSm (lo := a.toNat) (hi := a.toNat + 1) (by fomega)
      (by fomega) a (Nat.le_refl _) (by omega)))
    hWN

end FV7z.Hwc
