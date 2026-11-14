import FV7z.Hwc.Alloc
/-!
# `_dl_important_hwcaps`: 682 → the `ret` (PLAN.md G3, startup)

At 682 the entries of `temp` for the bits of `_dl_hwcap` are there (`x86_64`, and `avx512_1` when `cnt = 4`); 682
puts the platform (`rbp - 0x60`, length `0`: `_dl_platformlen` is set after `_dl_init_paths`) in the next one, 716
`tls` in the last and adds up the lengths (23 or 32), 1010 (`cnt = 4`) checks `cnt ≤ 63`; then `from1050`.

- `hl_st`, `hl_ln`: the entries of `temp` on this path.
- `mid1050`: `from1050` from bytes `V₂` that differ from `V` only in the last two entries of `temp` and three
  slots of the frame.
- `from682`: the two cases.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn

namespace FV7z.Hwc

set_option maxRecDepth 100000

/-- The lengths of the entries of `temp`: `x86_64`, `avx512_1` (`cnt = 4`), the platform (0), `tls`. -/
def hl_ln (cnt m : Nat) : Addr :=
  if m = 0 then 6#64 else if m = cnt - 1 then 3#64 else if m = cnt - 2 then 0#64 else 8#64

/-- The strings of the entries of `temp`: `S0`, `S1` (`cnt = 4`), the platform `p`, `tls` (`0x7065da`). -/
def hl_st (cnt : Nat) (S0 S1 p : Addr) (m : Nat) : Addr :=
  if m = 0 then S0 else if m = cnt - 1 then 7366106#64 else if m = cnt - 2 then p else S1

theorem r168 (R : Addr) : R + 16#64 + 8#64 = R + 24#64 := by bv_omega
theorem r328 (R : Addr) : R + 32#64 + 8#64 = R + 40#64 := by bv_omega
theorem sh_add (R c d : Addr) (h : c = d) : c + R = R + d := by rw [h, BitVec.add_comm]

set_option hygiene false in
/-- A load of the 8 bytes a store put there. -/
macro "vself" : tactic => `(tactic| (rw [Tun.rd_Vst_self _ _ _ (toBytesLE_length _ _) (by fomega),
  ofBytesLE_toBytesLE (n := 8) rfl]; try rfl))

variable {prof : Profile} {F : Footprint} {Wl : List Rgn} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop} {fb : Addr}
  {cpy mlc : List Byte} {Pm Pa : (Addr → Byte) → Prop}

/-! ## From 1050 with the bytes of 682 -/

set_option maxHeartbeats 4000000 in
/-- `from1050` with the bytes `V₂` at 1050, as `V` but the last two entries of `temp` and three slots of the frame
(`rbp - 0x98`, `rbp - 0x50`, `rbp - 0x48`); what is left of the frame after the `ret`, from `rbp - 0x40`, as in `V`. -/
theorem mid1050 (c : Seg prof F Wl L s₀ o) (hfs : s₀.cpu.seg.fsBase = fb) (hin : CodeIn L hwc_at hwc)
    (hinc : CodeIn L 4198592#64 cpy) (hc0 : 0 < cpy.length) (hcpy : Gor.PcpyAt prof L o 4198592#64 Pm)
    (hinm : CodeIn L 6500704#64 mlc) (hm0 : 0 < mlc.length) (hmal : Mal.At prof L o 6500704#64 Pa)
    {V V₂ : Addr → Byte} {cnt E H t s : Nat} {R bp sp Q N : Addr} {ln st : Nat → Addr}
    (hPm : ∀ W : Addr → Byte, (∀ a : Addr, a.toNat < 7940480 → W a = V a) → Pm W)
    (hPa : ∀ W : Addr → Byte, (∀ a : Addr, a.toNat < sp.toNat - 8 → W a = V a) → Pa W)
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
    (hSV : ∀ a : Addr, (a.toNat < R.toNat + 16 * (cnt - 2) ∨ R.toNat + 16 * cnt ≤ a.toNat) →
      (a.toNat < (bp + 18446744073709551448#64).toNat + 16 ∨ (bp + 18446744073709551448#64).toNat + 24 ≤ a.toNat) →
      (a.toNat < (bp + 18446744073709551448#64).toNat + 88 ∨ (bp + 18446744073709551448#64).toNat + 104 ≤ a.toNat) →
      V₂ a = V a)
    (hT : ∀ m < cnt, rdq(V₂, R + BitVec.ofNat 64 (16 * m)) = st m ∧
      rdq(V₂, R + BitVec.ofNat 64 (16 * m + 8)) = ln m)
    (hsrc : ∀ m < cnt, ∀ i < (ln m).toNat, Foot F.data ((st m).add i))
    (hs64 : ∀ m < cnt, (st m).toNat + (ln m).toNat ≤ 2 ^ 64)
    (hsd : ∀ m < cnt, (st m).toNat + (ln m).toNat ≤ 7940480 ∨ sp.toNat ≤ (st m).toNat)
    (hD8 : rdq(V₂, bp + 18446744073709551464#64) = BitVec.ofNat 64 (16 * cnt))
    (hL : rdq(V₂, bp + 18446744073709551536#64) = ln (cnt - 1))
    (hl : rdq(V₂, bp + 18446744073709551544#64) = ln 0)
    (hNv : rdq(V, bp + 18446744073709551528#64) = N) (hND : (bp + 18446744073709551448#64).toNat + 176 ≤ N.toNat)
    (hN64 : N.toNat + 8 ≤ 2 ^ 64) (hsN : ∀ i < 8, Foot Wl (Addr.add N i))
    (hQ : rdq(V, bp + 18446744073709551504#64) = Q) (hsQ : ∀ i < 8, Foot Wl (Addr.add Q i))
    (hQ64 : Q.toNat + 8 ≤ 2 ^ 64)
    (hQd : Q.toNat + 8 ≤ (bp + 18446744073709551448#64).toNat + 128 ∨
      (bp + 18446744073709551448#64).toNat + 176 ≤ Q.toNat)
    (k : ∀ Y t' (W : Addr → Byte) (P : Addr), KeptW Wl s₀ Y →
      Agree F Y.proc.mm.mem (Vst W Q (toBytesLE (caps E ln cnt (fun _ => 0#64) 0) 8)) →
      Y.cpu.rip = hwc_at.add 1681 → Y.cpu.gpr.rax = P → 7940480 ≤ P.toNat → P.toNat + s ≤ sp.toNat - 8 →
      (∀ a : Addr, P.toNat ≤ a.toNat → a.toNat < P.toNat + s → Foot Wl a ∧ Foot F.data a) →
      Y.cpu.gpr.rsp = bp + 8#64 →
      Y.cpu.gpr.rbx = rdq(V, bp + 18446744073709551576#64) → Y.cpu.gpr.r12 = rdq(V, bp + 18446744073709551584#64) →
      Y.cpu.gpr.r13 = rdq(V, bp + 18446744073709551592#64) → Y.cpu.gpr.r14 = rdq(V, bp + 18446744073709551600#64) →
      Y.cpu.gpr.r15 = rdq(V, bp + 18446744073709551608#64) → Y.cpu.gpr.rbp = rdq(V, bp) →
      Tab W P E (pt (fun _ => P + BitVec.ofNat 64 (16 * E)) (caps E ln cnt (fun _ => 0#64)) H (ln (cnt - 1)))
        (caps E ln cnt (fun _ => 0#64)) →
      Same V W 0 7940480 → Same V W ((bp + 18446744073709551448#64).toNat + 104) N.toNat →
      rdq(W, N) = BitVec.ofNat 64 E → Same V W (N.toNat + 8) (2 ^ 64) → GoG prof L o gev gP gE Y t') :
    ∀ (X : State) (t₀ : Nat), KeptW Wl s₀ X → Agree F X.proc.mm.mem V₂ → X.cpu.rip = hwc_at.add 1050 →
      X.cpu.gpr.rsi = BitVec.ofNat 64 cnt → X.cpu.gpr.rax = BitVec.ofNat 64 t →
      X.cpu.gpr.rdx = R + BitVec.ofNat 64 (16 * (cnt - 1)) → X.cpu.gpr.r12 = BitVec.ofNat 64 cnt →
      X.cpu.gpr.rbx = R → X.cpu.gpr.rbp = bp → X.cpu.gpr.rsp = sp → GoG prof L o gev gP gE X t₀ := by
  intro X t₀ hK hA hrip hsi hax hdx h12 hbx hbp hsp
  have hSm : ∀ lo hi : Nat, (hi ≤ R.toNat + 16 * (cnt - 2) ∨ R.toNat + 16 * cnt ≤ lo) →
      (hi ≤ (bp + 18446744073709551448#64).toNat + 16 ∨ (bp + 18446744073709551448#64).toNat + 24 ≤ lo) →
      (hi ≤ (bp + 18446744073709551448#64).toNat + 88 ∨ (bp + 18446744073709551448#64).toNat + 104 ≤ lo) →
      Same V V₂ lo hi := fun lo hi h1 h2 h3 a a1 a2 => hSV a (by omega) (by omega) (by omega)
  have hS1 : ∀ {x : Addr} {n : Nat}, x.toNat + n ≤ 2 ^ 64 →
      (x.toNat + n ≤ R.toNat + 16 * (cnt - 2) ∨ R.toNat + 16 * cnt ≤ x.toNat) →
      (x.toNat + n ≤ (bp + 18446744073709551448#64).toNat + 16 ∨
        (bp + 18446744073709551448#64).toNat + 24 ≤ x.toNat) →
      (x.toNat + n ≤ (bp + 18446744073709551448#64).toNat + 88 ∨
        (bp + 18446744073709551448#64).toNat + 104 ≤ x.toNat) →
      List.map V₂ (byteAddrs x n) = List.map V (byteAddrs x n) :=
    fun {x n} hx h1 h2 h3 => (hSm x.toNat (x.toNat + n) h1 h2 h3).rd (Nat.le_refl _) (Nat.le_refl _) hx
  refine from1050 c hfs hin hinc hc0 hcpy hinm hm0 hmal (V := V₂)
    (fun W hW => hPm W fun a ha => (hW a ha).trans (hSV a (by fomega) (by fomega) (by fomega)))
    (fun W hW => hPa W fun a ha => (hW a ha).trans (hSV a (by fomega) (by fomega) (by fomega)))
    hn hlv hspl hRs hRF hfb hst hFr hFT hT hsrc hs64 hsd
    (by rw [hS1 (by fomega) (by fomega) (by fomega) (by fomega)]; exact hNv) hND hN64 hsN hD8 hL hl
    (by rw [hS1 (by fomega) (by fomega) (by fomega) (by fomega)]; exact hQ) hsQ hQ64 hQd ?_
    X t₀ hK hA hrip hsi hax hdx h12 hbx hbp hsp
  intro Y t' W P hKY hAY hrY haxY hlo hpe hWP hspY hbxY h12Y h13Y h14Y h15Y hbpY hTab hS0 _ hSh hWN hSN
  have hcp := caps_congr (E := E) (Tl := tlen V₂ R) (Tl' := ln) cnt (fun _ => 0#64) (fun j hj => (hT j hj).2)
  rw [hcp] at hAY hTab
  rw [hS1 (by fomega) (by fomega) (by fomega) (by fomega)] at hbxY h12Y h13Y h14Y h15Y
  rw [hS1 (by fomega) (by fomega) (by fomega) (by fomega)] at hbpY
  exact k Y t' W P hKY hAY hrY haxY hlo hpe hWP hspY hbxY h12Y h13Y h14Y h15Y hbpY hTab
    (fun a h1 h2 => (hS0 a h1 h2).trans (hSV a (by fomega) (by fomega) (by fomega)))
    (fun a h1 h2 => (hSh a (by fomega) h2).trans (hSV a (by fomega) (by fomega) (by fomega)))
    hWN
    (fun a h1 h2 => (hSN a h1 h2).trans (hSV a (by fomega) (by fomega) (by fomega)))

/-! ## 682 → 1050 -/

set_option maxHeartbeats 8000000 in
/-- From 682 (`rax` the entry `cnt - 2` of `temp` at `R`, `rcx = cnt - 1`): the platform `p` (length `0`) and `tls`
to the last two entries, the total, on to the `ret` (1681). `S0` (`x86_64`, entry 0) and `S1` (`avx512_1`, entry 1
when `cnt = 4`) in `.rodata`; `p` below `0x792980` or in the stack. -/
theorem from682 (c : Seg prof F Wl L s₀ o) (hfs : s₀.cpu.seg.fsBase = fb) (hin : CodeIn L hwc_at hwc)
    (hinc : CodeIn L 4198592#64 cpy) (hc0 : 0 < cpy.length) (hcpy : Gor.PcpyAt prof L o 4198592#64 Pm)
    (hinm : CodeIn L 6500704#64 mlc) (hm0 : 0 < mlc.length) (hmal : Mal.At prof L o 6500704#64 Pa)
    {V : Addr → Byte} {cnt E H t s : Nat} {R bp sp Q N p S0 S1 : Addr}
    (hPm : ∀ W : Addr → Byte, (∀ a : Addr, a.toNat < 7940480 → W a = V a) → Pm W)
    (hPa : ∀ W : Addr → Byte, (∀ a : Addr, a.toNat < sp.toNat - 8 → W a = V a) → Pa W)
    (hn : cnt = 3 ∧ E = 8 ∧ H = 4 ∧ t = 23 ∧ s = 151 ∨ cnt = 4 ∧ E = 16 ∧ H = 8 ∧ t = 32 ∧ s = 320)
    (hspl : 7940480 ≤ sp.toNat)
    (hRs : sp.toNat ≤ R.toNat) (hRF : R.toNat + 16 * cnt ≤ (bp + 18446744073709551448#64).toNat)
    (hfb : (bp + 18446744073709551448#64).toNat + 176 ≤ 2 ^ 64)
    (hst : ∀ i < 8, Foot Wl (Addr.add (sp - 8) i))
    (hFr : ∀ a : Addr, (bp + 18446744073709551448#64).toNat ≤ a.toNat →
      a.toNat < (bp + 18446744073709551448#64).toNat + 176 → Foot Wl a ∧ Foot F.data a)
    (hFT : ∀ a : Addr, R.toNat ≤ a.toNat → a.toNat < R.toNat + 16 * cnt → Foot F.data a)
    (hFTW : ∀ a : Addr, R.toNat ≤ a.toNat → a.toNat < R.toNat + 16 * cnt → Foot Wl a)
    (hS0 : rdq(V, R) = S0) (hL0 : rdq(V, R + 8#64) = 6#64)
    (hS1 : cnt = 4 → rdq(V, R + 16#64) = S1 ∧ rdq(V, R + 24#64) = 8#64)
    (hS0f : ∀ i < 6, Foot F.data (S0.add i)) (hS0l : S0.toNat + 6 ≤ 7940480)
    (hS1f : cnt = 4 → ∀ i < 8, Foot F.data (S1.add i)) (hS1l : cnt = 4 → S1.toNat + 8 ≤ 7940480)
    (htls : ∀ i < 3, Foot F.data ((7366106#64).add i))
    (hp : rdq(V, bp + 18446744073709551520#64) = p) (hp0 : p ≠ 0#64)
    (hpl : rdq(V, bp + 18446744073709551512#64) = 0#64) (hpd : p.toNat ≤ 7940480 ∨ sp.toNat ≤ p.toNat)
    (hNv : rdq(V, bp + 18446744073709551528#64) = N) (hND : (bp + 18446744073709551448#64).toNat + 176 ≤ N.toNat)
    (hN64 : N.toNat + 8 ≤ 2 ^ 64) (hsN : ∀ i < 8, Foot Wl (Addr.add N i))
    (hQ : rdq(V, bp + 18446744073709551504#64) = Q) (hsQ : ∀ i < 8, Foot Wl (Addr.add Q i))
    (hQ64 : Q.toNat + 8 ≤ 2 ^ 64)
    (hQd : Q.toNat + 8 ≤ (bp + 18446744073709551448#64).toNat + 128 ∨
      (bp + 18446744073709551448#64).toNat + 176 ≤ Q.toNat)
    (k : ∀ Y t' (W : Addr → Byte) (P : Addr), KeptW Wl s₀ Y →
      Agree F Y.proc.mm.mem (Vst W Q (toBytesLE (caps E (hl_ln cnt) cnt (fun _ => 0#64) 0) 8)) →
      Y.cpu.rip = hwc_at.add 1681 → Y.cpu.gpr.rax = P → 7940480 ≤ P.toNat → P.toNat + s ≤ sp.toNat - 8 →
      (∀ a : Addr, P.toNat ≤ a.toNat → a.toNat < P.toNat + s → Foot Wl a ∧ Foot F.data a) →
      Y.cpu.gpr.rsp = bp + 8#64 →
      Y.cpu.gpr.rbx = rdq(V, bp + 18446744073709551576#64) → Y.cpu.gpr.r12 = rdq(V, bp + 18446744073709551584#64) →
      Y.cpu.gpr.r13 = rdq(V, bp + 18446744073709551592#64) → Y.cpu.gpr.r14 = rdq(V, bp + 18446744073709551600#64) →
      Y.cpu.gpr.r15 = rdq(V, bp + 18446744073709551608#64) → Y.cpu.gpr.rbp = rdq(V, bp) →
      Tab W P E (pt (fun _ => P + BitVec.ofNat 64 (16 * E)) (caps E (hl_ln cnt) cnt (fun _ => 0#64)) H
        (hl_ln cnt (cnt - 1))) (caps E (hl_ln cnt) cnt (fun _ => 0#64)) →
      Same V W 0 7940480 → Same V W ((bp + 18446744073709551448#64).toNat + 104) N.toNat →
      rdq(W, N) = BitVec.ofNat 64 E → Same V W (N.toNat + 8) (2 ^ 64) → GoG prof L o gev gP gE Y t') :
    ∀ (X : State) (t₀ : Nat), KeptW Wl s₀ X → Agree F X.proc.mm.mem V → X.cpu.rip = hwc_at.add 682 →
      X.cpu.gpr.rax = R + BitVec.ofNat 64 (16 * (cnt - 2)) → X.cpu.gpr.rcx = BitVec.ofNat 64 (cnt - 1) →
      X.cpu.gpr.r12 = BitVec.ofNat 64 cnt → X.cpu.gpr.rbx = R → X.cpu.gpr.rbp = bp → X.cpu.gpr.rsp = sp →
      GoG prof L o gev gP gE X t₀ := by
  intro X t₀ hK hA hrip hax hcx h12 hbx hbp hsp
  have hFrW : ∀ a : Addr, (bp + 18446744073709551448#64).toNat ≤ a.toNat →
      a.toNat < (bp + 18446744073709551448#64).toNat + 176 → Foot Wl a := fun a h1 h2 => (hFr a h1 h2).1
  have hFrD : ∀ a : Addr, (bp + 18446744073709551448#64).toNat ≤ a.toNat →
      a.toNat < (bp + 18446744073709551448#64).toNat + 176 → Foot F.data a := fun a h1 h2 => (hFr a h1 h2).2
  rcases hn with ⟨rfl, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, rfl⟩
  · -- `cnt = 3`: the platform to entry 1, `tls` to entry 2
    simp only [Nat.reduceSub, Nat.reduceMul] at hax hcx
    have e8 : (R + 8#64).toNat = R.toNat + 8 := addO (by fomega)
    have e16 : (R + 16#64).toNat = R.toNat + 16 := addO (by fomega)
    have e24 : (R + 24#64).toNat = R.toNat + 24 := addO (by fomega)
    have e32 : (R + 32#64).toNat = R.toNat + 32 := addO (by fomega)
    have e40 : (R + 40#64).toNat = R.toNat + 40 := addO (by fomega)
    refine (c_682 prof fb).run c hfs hin _ hK hA hrip
      (vc_682 (p := p) (l := 0#64) (by rw [hbp]; exact hp) hp0
        (by rw [hbp, hax]; vpeel; exact hpl)
        (by rw [hax]; exact rng hFTW (by fomega) (by fomega) (by fomega))
        (by rw [hax, r168]; exact rng hFTW (by fomega) (by fomega) (by fomega))
        (by rw [hbp]; exact rng hFrD (by fomega) (by fomega) (by fomega))
        (by rw [hbp]; exact rng hFrD (by fomega) (by fomega) (by fomega))) ?_
    rintro j' g fl V' ⟨rfl, rfl, rfl⟩ Y t₁ hKY hAY hrY hgY -
    rw [hax, r168] at hAY
    have hbxY : Y.cpu.gpr.rbx = R := by rw [hgY]; exact hbx
    have hbpY : Y.cpu.gpr.rbp = bp := by rw [hgY]; exact hbp
    have hspY : Y.cpu.gpr.rsp = sp := by rw [hgY]; exact hsp
    have h12Y : Y.cpu.gpr.r12 = 3#64 := by rw [hgY]; exact h12
    have hcxY : Y.cpu.gpr.rcx = 3#64 := by
      rw [hgY]
      show X.cpu.gpr.rcx + 1#64 = _
      rw [hcx]
      try decide
    have haxY : Y.cpu.gpr.rax = Y.cpu.gpr.rbx + 32#64 := by
      rw [hbxY, hgY]
      show X.cpu.gpr.rcx <<< 4 + X.cpu.gpr.rbx = _
      rw [hcx, hbx]
      exact sh_add R _ _ (by decide)
    refine (c_716 prof fb).run c hfs hin _ hKY hAY hrY
      (vc_716_3 h12Y hcxY haxY
        (by rw [hbxY]; vpeel; exact hL0)
        (by rw [hbxY, hbpY]; vpeel; vself)
        (by rw [hbxY, hbpY]; vpeel; vself)
        (by rw [hbxY]; exact rng hFTW (by fomega) (by fomega) (by fomega))
        (by rw [hbxY]; exact rng hFTW (by fomega) (by fomega) (by fomega))
        (by rw [hbpY]; exact rng hFrW (by fomega) (by fomega) (by fomega))
        (by rw [hbpY]; exact rng hFrW (by fomega) (by fomega) (by fomega))
        (by rw [hbpY]; exact rng hFrW (by fomega) (by fomega) (by fomega))
        (by rw [hbxY]; exact rng hFT (by fomega) (by fomega) (by fomega))
        (by rw [hbxY]; exact rng hFT (by fomega) (by fomega) (by fomega))
        (by rw [hbxY]; exact rng hFT (by fomega) (by fomega) (by fomega))) ?_
    rintro j' g fl V' ⟨rfl, rfl, rfl⟩ Z t₂ hKZ hAZ hrZ hgZ -
    rw [hbxY, hbpY] at hAZ
    refine mid1050 c hfs hin hinc hc0 hcpy hinm hm0 hmal (st := hl_st 3 S0 S1 p) (ln := hl_ln 3) hPm hPa
      (.inl ⟨rfl, rfl, rfl, rfl, rfl⟩) (.inl ⟨rfl, by decide, by decide, by decide⟩) hspl hRs hRF hfb hst hFr hFT
      (fun a h1 h2 h3 => by repeat (focus (rw [Tun.Vst_out _ _ _ _ ?_ ?_]; rotate_left; iterate 2 fomega)))
      (fun m hm => by
        obtain rfl | rfl | rfl : m = 0 ∨ m = 1 ∨ m = 2 := by omega
        all_goals simp only [Nat.reduceMul, Nat.reduceAdd, BitVec.add_zero]
        · exact ⟨by vpeel; exact hS0, by vpeel; exact hL0⟩
        · exact ⟨by vpeel; vself, by vpeel; vself⟩
        · exact ⟨by vpeel; vself, by vpeel; vself⟩)
      (fun m hm i hi => by
        obtain rfl | rfl | rfl : m = 0 ∨ m = 1 ∨ m = 2 := by omega
        · exact hS0f i hi
        · exact absurd hi (Nat.not_lt_zero i)
        · exact htls i (by simpa [hl_ln] using hi))
      (fun m hm => by
        obtain rfl | rfl | rfl : m = 0 ∨ m = 1 ∨ m = 2 := by omega
        · show S0.toNat + 6 ≤ 2 ^ 64
          omega
        · show p.toNat + 0 ≤ 2 ^ 64
          have := p.isLt
          omega
        · show (7366106#64).toNat + 3 ≤ 2 ^ 64
          decide)
      (fun m hm => by
        obtain rfl | rfl | rfl : m = 0 ∨ m = 1 ∨ m = 2 := by omega
        · show S0.toNat + 6 ≤ 7940480 ∨ sp.toNat ≤ S0.toNat
          omega
        · show p.toNat + 0 ≤ 7940480 ∨ sp.toNat ≤ p.toNat
          omega
        · show (7366106#64).toNat + 3 ≤ 7940480 ∨ sp.toNat ≤ (7366106#64).toNat
          exact .inl (by decide))
      (by vpeel; vself) (by vpeel; vself) (by vpeel; vself)
      hNv hND hN64 hsN hQ hsQ hQ64 hQd k Z t₂ hKZ hAZ hrZ (by rw [hgZ]) (by rw [hgZ])
      (by rw [hgZ]; show Y.cpu.gpr.rbx + 32#64 = _; rw [hbxY]; try rfl)
      (by rw [hgZ]; exact h12Y) (by rw [hgZ]; exact hbxY) (by rw [hgZ]; exact hbpY) (by rw [hgZ]; exact hspY)
  · -- `cnt = 4`: the platform to entry 2, `tls` to entry 3, then 1010
    simp only [Nat.reduceSub, Nat.reduceMul] at hax hcx
    obtain ⟨hS1v, hL1⟩ := hS1 rfl
    have e8 : (R + 8#64).toNat = R.toNat + 8 := addO (by fomega)
    have e16 : (R + 16#64).toNat = R.toNat + 16 := addO (by fomega)
    have e24 : (R + 24#64).toNat = R.toNat + 24 := addO (by fomega)
    have e32 : (R + 32#64).toNat = R.toNat + 32 := addO (by fomega)
    have e40 : (R + 40#64).toNat = R.toNat + 40 := addO (by fomega)
    have e48 : (R + 48#64).toNat = R.toNat + 48 := addO (by fomega)
    have e56 : (R + 56#64).toNat = R.toNat + 56 := addO (by fomega)
    refine (c_682 prof fb).run c hfs hin _ hK hA hrip
      (vc_682 (p := p) (l := 0#64) (by rw [hbp]; exact hp) hp0
        (by rw [hbp, hax]; vpeel; exact hpl)
        (by rw [hax]; exact rng hFTW (by fomega) (by fomega) (by fomega))
        (by rw [hax, r328]; exact rng hFTW (by fomega) (by fomega) (by fomega))
        (by rw [hbp]; exact rng hFrD (by fomega) (by fomega) (by fomega))
        (by rw [hbp]; exact rng hFrD (by fomega) (by fomega) (by fomega))) ?_
    rintro j' g fl V' ⟨rfl, rfl, rfl⟩ Y t₁ hKY hAY hrY hgY -
    rw [hax, r328] at hAY
    have hbxY : Y.cpu.gpr.rbx = R := by rw [hgY]; exact hbx
    have hbpY : Y.cpu.gpr.rbp = bp := by rw [hgY]; exact hbp
    have hspY : Y.cpu.gpr.rsp = sp := by rw [hgY]; exact hsp
    have h12Y : Y.cpu.gpr.r12 = 4#64 := by rw [hgY]; exact h12
    have hcxY : Y.cpu.gpr.rcx = 4#64 := by
      rw [hgY]
      show X.cpu.gpr.rcx + 1#64 = _
      rw [hcx]
      try decide
    have haxY : Y.cpu.gpr.rax = Y.cpu.gpr.rbx + 48#64 := by
      rw [hbxY, hgY]
      show X.cpu.gpr.rcx <<< 4 + X.cpu.gpr.rbx = _
      rw [hcx, hbx]
      exact sh_add R _ _ (by decide)
    refine (c_716 prof fb).run c hfs hin _ hKY hAY hrY
      (vc_716_4 h12Y hcxY haxY
        (by rw [hbxY]; vpeel; exact hL0)
        (by rw [hbxY, hbpY]; vpeel; vself)
        (by rw [hbxY, hbpY]; vpeel; exact hL1)
        (by rw [hbxY, hbpY]; vpeel; vself)
        (by rw [hbxY]; exact rng hFTW (by fomega) (by fomega) (by fomega))
        (by rw [hbxY]; exact rng hFTW (by fomega) (by fomega) (by fomega))
        (by rw [hbpY]; exact rng hFrW (by fomega) (by fomega) (by fomega))
        (by rw [hbpY]; exact rng hFrW (by fomega) (by fomega) (by fomega))
        (by rw [hbpY]; exact rng hFrW (by fomega) (by fomega) (by fomega))
        (by rw [hbxY]; exact rng hFT (by fomega) (by fomega) (by fomega))
        (by rw [hbxY]; exact rng hFT (by fomega) (by fomega) (by fomega))
        (by rw [hbxY]; exact rng hFT (by fomega) (by fomega) (by fomega))
        (by rw [hbxY]; exact rng hFT (by fomega) (by fomega) (by fomega))) ?_
    rintro j' g fl V' ⟨rfl, rfl, rfl⟩ Z t₂ hKZ hAZ hrZ hgZ -
    rw [hbxY, hbpY] at hAZ
    refine (c_1010 prof fb).run c hfs hin _ hKZ hAZ hrZ
      (vc_1010 (by rw [hgZ]; exact h12Y) (by rw [hgZ])) ?_
    rintro j' g fl V' ⟨rfl, rfl, rfl⟩ U t₃ hKU hAU hrU hgU -
    refine mid1050 c hfs hin hinc hc0 hcpy hinm hm0 hmal (st := hl_st 4 S0 S1 p) (ln := hl_ln 4) hPm hPa
      (.inr ⟨rfl, rfl, rfl, rfl, rfl⟩) (.inr ⟨rfl, by decide, by decide, by decide, by decide⟩) hspl hRs hRF hfb
      hst hFr hFT
      (fun a h1 h2 h3 => by repeat (focus (rw [Tun.Vst_out _ _ _ _ ?_ ?_]; rotate_left; iterate 2 fomega)))
      (fun m hm => by
        obtain rfl | rfl | rfl | rfl : m = 0 ∨ m = 1 ∨ m = 2 ∨ m = 3 := by omega
        all_goals simp only [Nat.reduceMul, Nat.reduceAdd, BitVec.add_zero]
        · exact ⟨by vpeel; exact hS0, by vpeel; exact hL0⟩
        · exact ⟨by vpeel; exact hS1v, by vpeel; exact hL1⟩
        · exact ⟨by vpeel; vself, by vpeel; vself⟩
        · exact ⟨by vpeel; vself, by vpeel; vself⟩)
      (fun m hm i hi => by
        obtain rfl | rfl | rfl | rfl : m = 0 ∨ m = 1 ∨ m = 2 ∨ m = 3 := by omega
        · exact hS0f i hi
        · exact hS1f rfl i hi
        · exact absurd hi (Nat.not_lt_zero i)
        · exact htls i (by simpa [hl_ln] using hi))
      (fun m hm => by
        have := hS1l rfl
        obtain rfl | rfl | rfl | rfl : m = 0 ∨ m = 1 ∨ m = 2 ∨ m = 3 := by omega
        · show S0.toNat + 6 ≤ 2 ^ 64
          omega
        · show S1.toNat + 8 ≤ 2 ^ 64
          omega
        · show p.toNat + 0 ≤ 2 ^ 64
          have := p.isLt
          omega
        · show (7366106#64).toNat + 3 ≤ 2 ^ 64
          decide)
      (fun m hm => by
        have := hS1l rfl
        obtain rfl | rfl | rfl | rfl : m = 0 ∨ m = 1 ∨ m = 2 ∨ m = 3 := by omega
        · show S0.toNat + 6 ≤ 7940480 ∨ sp.toNat ≤ S0.toNat
          omega
        · show S1.toNat + 8 ≤ 7940480 ∨ sp.toNat ≤ S1.toNat
          omega
        · show p.toNat + 0 ≤ 7940480 ∨ sp.toNat ≤ p.toNat
          omega
        · show (7366106#64).toNat + 3 ≤ 7940480 ∨ sp.toNat ≤ (7366106#64).toNat
          exact .inl (by decide))
      (by vpeel; vself) (by vpeel; vself) (by vpeel; vself)
      hNv hND hN64 hsN hQ hsQ hQ64 hQd k U t₃ hKU hAU hrU (by rw [hgU])
      (by rw [hgU]; show Z.cpu.gpr.rax = _; rw [hgZ])
      (by rw [hgU]; show Z.cpu.gpr.rdx = _; rw [hgZ]; show Y.cpu.gpr.rbx + 48#64 = _; rw [hbxY]; try rfl)
      (by rw [hgU]; show Z.cpu.gpr.r12 = _; rw [hgZ]; exact h12Y)
      (by rw [hgU]; show Z.cpu.gpr.rbx = _; rw [hgZ]; exact hbxY)
      (by rw [hgU]; show Z.cpu.gpr.rbp = _; rw [hgZ]; exact hbpY)
      (by rw [hgU]; show Z.cpu.gpr.rsp = _; rw [hgZ]; exact hspY)

end FV7z.Hwc
