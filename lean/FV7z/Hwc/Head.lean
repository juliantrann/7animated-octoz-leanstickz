import FV7z.Hwc.Plat
import FV7z.Startup.StrAt
/-!
# `_dl_important_hwcaps`: 1778 → the `ret` (PLAN.md G3, startup)

At 1778 the `alloca` of `temp` (`R`, 16-aligned, `16 cnt + 16` bytes under the frame) is done. The loop over the
bits of `_dl_hwcap` (`h` = 2: bit 1; `h` = 6: bits 1, 2) puts `x86_64` (`0x6f3879`) and, when `h = 6`, `avx512_1`
(`0x6f3882`) in the first entries, each with its length from `strlen` (PLT `0x401108`, the contract `Str.LenAt`);
then 682 (`from682`).

- `At1681`: what the caller gets at the `ret` (as `from682`'s continuation, with the bytes at 1778).
- `from1778_3` (`h = 2`, `cnt = 3`), `from1778_4` (`h = 6`, `cnt = 4`).
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn

namespace FV7z.Hwc

set_option maxRecDepth 100000

/-! ## The `call` of `strlen` at 1890, small facts -/

theorem tgt_1890 : hwc_at.add (1890 + 5) + BitVec.ofNat 64 18446744073706748001 = 4198664#64 := by decide

/-- The string of bit `b` as `vc_1840s` leaves it: `x86_64`, `avx512_1`. -/
theorem ex1 : BitVec.ofNat 64 1 + (BitVec.ofNat 64 1 * 8#64 + 7288944#64) = 7288953#64 := by decide
theorem ex2 : BitVec.ofNat 64 2 + (BitVec.ofNat 64 2 * 8#64 + 7288944#64) = 7288962#64 := by decide

theorem sh0 (R : Addr) : R + 0#64 <<< 4 = R := by
  rw [show (0#64 <<< 4 : BitVec 64) = 0#64 from rfl, BitVec.add_zero]
theorem sh1 (R : Addr) : R + 1#64 <<< 4 = R + 16#64 := by
  rw [show (1#64 <<< 4 : BitVec 64) = 16#64 from rfl]
theorem add_lit (R : Addr) {a b : Addr} (h : a = b) : R + a = R + b := by rw [h]

/-- A byte of a string in `.rodata`. -/
theorem lit_add {c n k : Nat} (hk : k ≤ n) (h : c + n < 2 ^ 64) : (Addr.add (BitVec.ofNat 64 c) k).toNat = c + k := by
  simp only [Addr.add, BitVec.toNat_add, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (a := c) (by omega), Nat.mod_eq_of_lt (a := k) (by omega), Nat.mod_eq_of_lt (by omega)]

set_option hygiene false in
/-- A byte apart from all the stores over it (each apart by `fomega`). -/
macro "vout" : tactic =>
  `(tactic| repeat (focus (rw [FV7z.Tun.Vst_out _ _ _ _ ?_ ?_]; rotate_left; iterate 2 fomega)))

variable {prof : Profile} {F : Footprint} {Wl : List Rgn} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop} {fb : Addr}
  {cpy mlc sl : List Byte} {Pm Pa Pl : (Addr → Byte) → Prop}

/-- What `from682` gives at the `ret` (1681), with `V` the bytes before the loop over the bits and `R` the `rsp` of
`temp`. -/
def At1681 (prof : Profile) (L : List (Addr × List Byte)) (o : Oracle) (gev : List Event)
    (gP : State → Nat → List Event → Prop) (gE : Outcome → List Event → Prop) (F : Footprint) (Wl : List Rgn)
    (s₀ : State) (V : Addr → Byte) (bp R Q N : Addr) (cnt E H s : Nat) : Prop :=
  ∀ Y t' (W : Addr → Byte) (P : Addr), KeptW Wl s₀ Y →
    Agree F Y.proc.mm.mem (Vst W Q (toBytesLE (caps E (hl_ln cnt) cnt (fun _ => 0#64) 0) 8)) →
    Y.cpu.rip = hwc_at.add 1681 → Y.cpu.gpr.rax = P → 7940480 ≤ P.toNat → P.toNat + s ≤ R.toNat - 8 →
    (∀ a : Addr, P.toNat ≤ a.toNat → a.toNat < P.toNat + s → Foot Wl a ∧ Foot F.data a) →
    Y.cpu.gpr.rsp = bp + 8#64 →
    Y.cpu.gpr.rbx = rdq(V, bp + 18446744073709551576#64) → Y.cpu.gpr.r12 = rdq(V, bp + 18446744073709551584#64) →
    Y.cpu.gpr.r13 = rdq(V, bp + 18446744073709551592#64) → Y.cpu.gpr.r14 = rdq(V, bp + 18446744073709551600#64) →
    Y.cpu.gpr.r15 = rdq(V, bp + 18446744073709551608#64) → Y.cpu.gpr.rbp = rdq(V, bp) →
    Tab W P E (pt (fun _ => P + BitVec.ofNat 64 (16 * E)) (caps E (hl_ln cnt) cnt (fun _ => 0#64)) H
      (hl_ln cnt (cnt - 1))) (caps E (hl_ln cnt) cnt (fun _ => 0#64)) →
    Same V W 0 7940480 → Same V W ((bp + 18446744073709551448#64).toNat + 104) N.toNat →
    rdq(W, N) = BitVec.ofNat 64 E → Same V W (N.toNat + 8) (2 ^ 64) → GoG prof L o gev gP gE Y t'

/-! ## `h = 2`: `x86_64` -/

set_option maxHeartbeats 8000000 in
/-- From 1778 with `h = 2` (`cnt = 3`, `temp` at `R = bp - 0xa8 - 72`): `x86_64` (length 6) to entry 0, on to 682
and the `ret`. -/
theorem from1778_3 (c : Seg prof F Wl L s₀ o) (hfs : s₀.cpu.seg.fsBase = fb) (hin : CodeIn L hwc_at hwc)
    (hinc : CodeIn L 4198592#64 cpy) (hc0 : 0 < cpy.length) (hcpy : Gor.PcpyAt prof L o 4198592#64 Pm)
    (hinm : CodeIn L 6500704#64 mlc) (hm0 : 0 < mlc.length) (hmal : Mal.At prof L o 6500704#64 Pa)
    (hins : CodeIn L 4198664#64 sl) (hs0 : 0 < sl.length) (hlen : Str.LenAt prof L o 4198664#64 Pl)
    {V : Addr → Byte} {R bp Q N p : Addr}
    (hPm : ∀ W : Addr → Byte, (∀ a : Addr, a.toNat < 7940480 → W a = V a) → Pm W)
    (hPa : ∀ W : Addr → Byte, (∀ a : Addr, a.toNat < R.toNat - 8 → W a = V a) → Pa W)
    (hPl : ∀ W : Addr → Byte, (∀ a : Addr, a.toNat < 7940480 → W a = V a) → Pl W)
    (hRl : 7940488 ≤ R.toNat) (hRF : R.toNat + 72 = (bp + 18446744073709551448#64).toNat)
    (hfb : (bp + 18446744073709551448#64).toNat + 176 ≤ 2 ^ 64)
    (hal : (R + 15#64) &&& 18446744073709551600#64 = R)
    (hFs : ∀ a : Addr, R.toNat - 8 ≤ a.toNat → a.toNat < (bp + 18446744073709551448#64).toNat + 176 →
      Foot Wl a ∧ Foot F.data a)
    (hpg : ∀ x : Addr, 7286784 ≤ x.toNat → x.toNat < 7290880 → Foot F.data x)
    (hx1 : ∀ k < 6, V (Addr.add 7288953#64 k) ≠ 0) (hx1z : V (Addr.add 7288953#64 6) = 0)
    (htls : ∀ i < 3, Foot F.data ((7366106#64).add i))
    (hp : rdq(V, bp + 18446744073709551520#64) = p) (hp0 : p ≠ 0#64)
    (hpl : rdq(V, bp + 18446744073709551512#64) = 0#64) (hpd : p.toNat ≤ 7940480 ∨ R.toNat ≤ p.toNat)
    (hNv : rdq(V, bp + 18446744073709551528#64) = N) (hND : (bp + 18446744073709551448#64).toNat + 176 ≤ N.toNat)
    (hN64 : N.toNat + 8 ≤ 2 ^ 64) (hsN : ∀ i < 8, Foot Wl (Addr.add N i))
    (hQ : rdq(V, bp + 18446744073709551504#64) = Q) (hsQ : ∀ i < 8, Foot Wl (Addr.add Q i))
    (hQ64 : Q.toNat + 8 ≤ 2 ^ 64)
    (hQd : Q.toNat + 8 ≤ (bp + 18446744073709551448#64).toNat + 128 ∨
      (bp + 18446744073709551448#64).toNat + 176 ≤ Q.toNat)
    (k : At1681 prof L o gev gP gE F Wl s₀ V bp R Q N 3 8 4 151) :
    ∀ (X : State) (t₀ : Nat), KeptW Wl s₀ X → Agree F X.proc.mm.mem V → X.cpu.rip = hwc_at.add 1778 →
      X.cpu.gpr.r8 = 2#64 → X.cpu.gpr.r12 = BitVec.ofNat 64 3 → X.cpu.gpr.rbp = bp → X.cpu.gpr.rsp = R →
      GoG prof L o gev gP gE X t₀ := by
  intro X t₀ hK hA hrip h8 h12 hbp hsp
  have hFW : ∀ a : Addr, R.toNat - 8 ≤ a.toNat → a.toNat < (bp + 18446744073709551448#64).toNat + 176 →
      Foot Wl a := fun a h1 h2 => (hFs a h1 h2).1
  have hFD : ∀ a : Addr, R.toNat - 8 ≤ a.toNat → a.toNat < (bp + 18446744073709551448#64).toNat + 176 →
      Foot F.data a := fun a h1 h2 => (hFs a h1 h2).2
  have eRm : (R - 8).toNat = R.toNat - 8 := sub8 (by omega)
  have e8 : (R + 8#64).toNat = R.toNat + 8 := addO (by fomega)
  -- 1778: `cnt` to `rbp - 0x78`, the loop from bit 0
  refine (c_1778 prof fb).run c hfs hin _ hK hA hrip
    (vc_1778 (h := 2#64) (.inl rfl) h8 (by rw [hsp]; exact hal)
      (by rw [hbp]; exact rng hFW (by fomega) (by fomega) (by fomega))) ?_
  rintro j' g fl V' ⟨rfl, rfl, rfl⟩ Y₁ t₁ hK₁ hA₁ hr₁ hg₁ -
  rw [hbp, h12] at hA₁
  have b₁ : Y₁.cpu.gpr.rbp = bp := by rw [hg₁]; exact hbp
  have s₁ : Y₁.cpu.gpr.rsp = R := by rw [hg₁]; exact hsp
  have d₁ : Y₁.cpu.gpr.rdx = R := by rw [hg₁]; exact hsp
  have x₁ : Y₁.cpu.gpr.rbx = 0#64 := by rw [hg₁]; try rfl
  have r14₁ : Y₁.cpu.gpr.r14 = 2#64 := by rw [hg₁]; try rfl
  have r15₁ : Y₁.cpu.gpr.r15 = 0#64 := by rw [hg₁]; try rfl
  have r8₁ : Y₁.cpu.gpr.r8 = 1#64 := by rw [hg₁]; try rfl
  -- 1840: bit 0 clear
  refine (c_1840 prof fb).run c hfs hin _ hK₁ hA₁ hr₁ (vc_1840c (by rw [r14₁, r15₁]; try decide)) ?_
  rintro j' g fl V' ⟨rfl, rfl, rfl⟩ Y₂ t₂ hK₂ hA₂ hr₂ hg₂ -
  have b₂ : Y₂.cpu.gpr.rbp = bp := by rw [hg₂]; exact b₁
  have s₂ : Y₂.cpu.gpr.rsp = R := by rw [hg₂]; exact s₁
  have d₂ : Y₂.cpu.gpr.rdx = R := by rw [hg₂]; exact d₁
  have x₂ : Y₂.cpu.gpr.rbx = 0#64 := by rw [hg₂]; exact x₁
  have r14₂ : Y₂.cpu.gpr.r14 = 2#64 := by rw [hg₂]; exact r14₁
  have r8₂ : Y₂.cpu.gpr.r8 = 1#64 := by rw [hg₂]; exact r8₁
  have r15₂ : Y₂.cpu.gpr.r15 = BitVec.ofNat 64 1 := by
    rw [hg₂]
    show Y₁.cpu.gpr.r15 + 1#64 = _
    rw [r15₁]
    try decide
  -- 1840: bit 1 set, `x86_64` to entry 0, to the `call` of `strlen`
  refine (c_1840 prof fb).run c hfs hin _ hK₂ hA₂ hr₂
    (vc_1840s (b := 1) (.inl rfl) r15₂ (by rw [r14₂]; try decide)
      (by rw [b₂]; exact rng hFW (by fomega) (by fomega) (by fomega))
      (by rw [b₂]; exact rng hFW (by fomega) (by fomega) (by fomega))
      (by rw [d₂, x₂, sh0]; exact rng hFW (by fomega) (by fomega) (by fomega))) ?_
  rintro j' g fl V' ⟨rfl, rfl, rfl⟩ Y₃ t₃ hK₃ hA₃ hr₃ hg₃ -
  rw [b₂, r8₂, d₂, x₂, sh0, ex1] at hA₃
  have b₃ : Y₃.cpu.gpr.rbp = bp := by rw [hg₃]; exact b₂
  have s₃ : Y₃.cpu.gpr.rsp = R := by rw [hg₃]; exact s₂
  have x₃ : Y₃.cpu.gpr.rbx = 0#64 := by rw [hg₃]; exact x₂
  have r14₃ : Y₃.cpu.gpr.r14 = 2#64 := by rw [hg₃]; exact r14₂
  have r15₃ : Y₃.cpu.gpr.r15 = BitVec.ofNat 64 1 := by rw [hg₃]; exact r15₂
  have di₃ : Y₃.cpu.gpr.rdi = 7288953#64 := by rw [hg₃]; try exact ex1
  have r12₃ : Y₃.cpu.gpr.r12 = R := by
    rw [hg₃]
    show Y₂.cpu.gpr.rdx + Y₂.cpu.gpr.rbx <<< 4 = R
    rw [d₂, x₂, sh0]
  have r13₃ : Y₃.cpu.gpr.r13 = 0#64 := by
    rw [hg₃]
    show Y₂.cpu.gpr.rbx <<< 4 = _
    rw [x₂]
    try decide
  -- 1890: `strlen ("x86_64")`
  refine c.s_call hK₃ hA₃ hin (lt_len (by omega)) hr₃ (call_1890 _) hins hs0 tgt_1890
    (fun i hi => by rw [s₃]; exact rng hFW (by fomega) (by fomega) (by fomega) i hi) ?_
  rintro Y₄ t₄ hK₄ hA₄ ⟨hr₄, hg₄⟩
  rw [s₃] at hA₄ hg₄
  have s₄ : Y₄.cpu.gpr.rsp = R - 8 := by rw [hg₄]; rfl
  have di₄ : Y₄.cpu.gpr.rdi = 7288953#64 := by rw [hg₄]; exact di₃
  refine hlen 6 c hK₄ hA₄ hr₄ (hPl _ fun a ha => by vout) hin (j := 1895) (lt_len (by omega)) ?_
    (fun i hi => by rw [s₄]; exact rng hFD (by fomega) (by fomega) (by fomega) i hi)
    (by rw [di₄]; decide) (fun q hq => ?_) ?_ (fun x h1 h2 => ?_) ?_
  · rw [s₄]
    vself
  · have := lit_add (c := 7288953) (n := 6) (k := q) (by omega) (by decide)
    rw [di₄]
    vout
    exact hx1 q hq
  · have := lit_add (c := 7288953) (n := 6) (k := 6) (by omega) (by decide)
    rw [di₄]
    vout
    exact hx1z
  · rw [di₄] at h1 h2
    simp only [BitVec.reduceToNat] at h1 h2
    exact hpg x (by omega) (by omega)
  intro Z t₅ hK₅ hA₅ hr₅ hsp₅ hax₅ hbx₅ hbp₅ h12₅ h13₅ h14₅ h15₅
  have s₅ : Z.cpu.gpr.rsp = R := by rw [hsp₅, s₄]; exact sub8_add R
  have b₅ : Z.cpu.gpr.rbp = bp := by rw [hbp₅, hg₄]; exact b₃
  have x₅ : Z.cpu.gpr.rbx = 0#64 := by rw [hbx₅, hg₄]; exact x₃
  have r12₅ : Z.cpu.gpr.r12 = R := by rw [h12₅, hg₄]; exact r12₃
  have r13₅ : Z.cpu.gpr.r13 = 0#64 := by rw [h13₅, hg₄]; exact r13₃
  have r14₅ : Z.cpu.gpr.r14 = 2#64 := by rw [h14₅, hg₄]; exact r14₃
  have r15₅ : Z.cpu.gpr.r15 = BitVec.ofNat 64 1 := by rw [h15₅, hg₄]; exact r15₃
  -- 1895: the length to entry 0; bit 1 the last: to 682
  refine (c_1895 prof fb).run c hfs hin _ hK₅ hA₅ hr₅
    (vc_1895 (b := 1) (m := 2#64) (T := R) (e := 1#64) (k := BitVec.ofNat 64 3) (.inl ⟨rfl, rfl⟩) r15₅ r14₅
      (by rw [b₅]; vpeel; vself)
      (by rw [r12₅, hax₅, b₅]; vpeel; vself)
      (by rw [r12₅, hax₅, b₅]; vpeel; vself)
      (by rw [r12₅]; exact rng hFW (by fomega) (by fomega) (by fomega))
      (by rw [b₅]; exact rng hFD (by fomega) (by fomega) (by fomega))
      (by rw [b₅]; exact rng hFD (by fomega) (by fomega) (by fomega))
      (by rw [b₅]; exact rng hFD (by fomega) (by fomega) (by fomega))) ?_
  rintro j' g fl V' ⟨rfl, hc⟩ Y₆ t₆ hK₆ hA₆ hr₆ hg₆ -
  rcases hc with ⟨-, rfl, rfl⟩ | ⟨hne, -, -⟩
  rotate_left
  · exact (hne (by decide)).elim
  rw [r12₅, hax₅] at hA₆
  -- 682 on
  refine from682 (V := _) c hfs hin hinc hc0 hcpy hinm hm0 hmal (cnt := 3) (E := 8) (H := 4) (t := 23) (s := 151)
    (R := R) (bp := bp) (sp := R) (Q := Q) (N := N) (p := p) (S0 := 7288953#64) (S1 := 0#64)
    (fun W hW => hPm W fun a ha => (hW a ha).trans (by vout))
    (fun W hW => hPa W fun a ha => (hW a ha).trans (by vout))
    (.inl ⟨rfl, rfl, rfl, rfl, rfl⟩) (by omega) (Nat.le_refl _) (by omega) hfb
    (fun i hi => rng hFW (by fomega) (by fomega) (by fomega) i hi)
    (fun a h1 h2 => hFs a (by omega) h2) (fun a h1 h2 => hFD a (by omega) (by omega))
    (fun a h1 h2 => hFW a (by omega) (by omega))
    (by vpeel; vself) (by vself) (fun h => absurd h (by decide))
    (rng hpg (by decide) (by decide) (by decide)) (by decide) (fun h => absurd h (by decide))
    (fun h => absurd h (by decide)) htls (by vpeel; exact hp) hp0 (by vpeel; exact hpl) hpd
    (by vpeel; exact hNv) hND hN64 hsN (by vpeel; exact hQ) hsQ hQ64 hQd ?_ Y₆ t₆ hK₆ hA₆ hr₆ ?_ ?_ ?_ ?_ ?_ ?_
  · intro Y t' W P hKY hAY hrY haxY hlo hpe hWP hspY hbxY h12Y h13Y h14Y h15Y hbpY hTab hS0 hSs hNE hSh
    exact k Y t' W P hKY hAY hrY haxY hlo hpe hWP hspY (hbxY.trans (by vpeel)) (h12Y.trans (by vpeel))
      (h13Y.trans (by vpeel)) (h14Y.trans (by vpeel)) (h15Y.trans (by vpeel)) (hbpY.trans (by vpeel)) hTab
      (Same.trans (fun a _ h2 => by vout) hS0) (Same.trans (fun a h1 h2 => by vout) hSs) hNE
      (Same.trans (fun a h1 h2 => by vout) hSh)
  · rw [hg₆]
    show R + (Z.cpu.gpr.r13 + 16#64) = _
    rw [r13₅]
    try exact add_lit R (by decide)
  · rw [hg₆]
    show Z.cpu.gpr.rbx + 2#64 = _
    rw [x₅]
    try decide
  · rw [hg₆]; try rfl
  · rw [hg₆]; try rfl
  · rw [hg₆]; exact b₅
  · rw [hg₆]; exact s₅

/-! ## `h = 6`: `x86_64`, `avx512_1` -/

set_option maxHeartbeats 16000000 in
/-- From 1778 with `h = 6` (`cnt = 4`, `temp` at `R = bp - 0xa8 - 88`): `x86_64` (length 6) to entry 0, `avx512_1`
(length 8) to entry 1, on to 682 and the `ret`. -/
theorem from1778_4 (c : Seg prof F Wl L s₀ o) (hfs : s₀.cpu.seg.fsBase = fb) (hin : CodeIn L hwc_at hwc)
    (hinc : CodeIn L 4198592#64 cpy) (hc0 : 0 < cpy.length) (hcpy : Gor.PcpyAt prof L o 4198592#64 Pm)
    (hinm : CodeIn L 6500704#64 mlc) (hm0 : 0 < mlc.length) (hmal : Mal.At prof L o 6500704#64 Pa)
    (hins : CodeIn L 4198664#64 sl) (hs0 : 0 < sl.length) (hlen : Str.LenAt prof L o 4198664#64 Pl)
    {V : Addr → Byte} {R bp Q N p : Addr}
    (hPm : ∀ W : Addr → Byte, (∀ a : Addr, a.toNat < 7940480 → W a = V a) → Pm W)
    (hPa : ∀ W : Addr → Byte, (∀ a : Addr, a.toNat < R.toNat - 8 → W a = V a) → Pa W)
    (hPl : ∀ W : Addr → Byte, (∀ a : Addr, a.toNat < 7940480 → W a = V a) → Pl W)
    (hRl : 7940488 ≤ R.toNat) (hRF : R.toNat + 88 = (bp + 18446744073709551448#64).toNat)
    (hfb : (bp + 18446744073709551448#64).toNat + 176 ≤ 2 ^ 64)
    (hal : (R + 15#64) &&& 18446744073709551600#64 = R)
    (hFs : ∀ a : Addr, R.toNat - 8 ≤ a.toNat → a.toNat < (bp + 18446744073709551448#64).toNat + 176 →
      Foot Wl a ∧ Foot F.data a)
    (hpg : ∀ x : Addr, 7286784 ≤ x.toNat → x.toNat < 7290880 → Foot F.data x)
    (hx1 : ∀ k < 6, V (Addr.add 7288953#64 k) ≠ 0) (hx1z : V (Addr.add 7288953#64 6) = 0)
    (hx2 : ∀ k < 8, V (Addr.add 7288962#64 k) ≠ 0) (hx2z : V (Addr.add 7288962#64 8) = 0)
    (htls : ∀ i < 3, Foot F.data ((7366106#64).add i))
    (hp : rdq(V, bp + 18446744073709551520#64) = p) (hp0 : p ≠ 0#64)
    (hpl : rdq(V, bp + 18446744073709551512#64) = 0#64) (hpd : p.toNat ≤ 7940480 ∨ R.toNat ≤ p.toNat)
    (hNv : rdq(V, bp + 18446744073709551528#64) = N) (hND : (bp + 18446744073709551448#64).toNat + 176 ≤ N.toNat)
    (hN64 : N.toNat + 8 ≤ 2 ^ 64) (hsN : ∀ i < 8, Foot Wl (Addr.add N i))
    (hQ : rdq(V, bp + 18446744073709551504#64) = Q) (hsQ : ∀ i < 8, Foot Wl (Addr.add Q i))
    (hQ64 : Q.toNat + 8 ≤ 2 ^ 64)
    (hQd : Q.toNat + 8 ≤ (bp + 18446744073709551448#64).toNat + 128 ∨
      (bp + 18446744073709551448#64).toNat + 176 ≤ Q.toNat)
    (k : At1681 prof L o gev gP gE F Wl s₀ V bp R Q N 4 16 8 320) :
    ∀ (X : State) (t₀ : Nat), KeptW Wl s₀ X → Agree F X.proc.mm.mem V → X.cpu.rip = hwc_at.add 1778 →
      X.cpu.gpr.r8 = 6#64 → X.cpu.gpr.r12 = BitVec.ofNat 64 4 → X.cpu.gpr.rbp = bp → X.cpu.gpr.rsp = R →
      GoG prof L o gev gP gE X t₀ := by
  intro X t₀ hK hA hrip h8 h12 hbp hsp
  have hFW : ∀ a : Addr, R.toNat - 8 ≤ a.toNat → a.toNat < (bp + 18446744073709551448#64).toNat + 176 →
      Foot Wl a := fun a h1 h2 => (hFs a h1 h2).1
  have hFD : ∀ a : Addr, R.toNat - 8 ≤ a.toNat → a.toNat < (bp + 18446744073709551448#64).toNat + 176 →
      Foot F.data a := fun a h1 h2 => (hFs a h1 h2).2
  have eRm : (R - 8).toNat = R.toNat - 8 := sub8 (by omega)
  have e8 : (R + 8#64).toNat = R.toNat + 8 := addO (by fomega)
  have e16 : (R + 16#64).toNat = R.toNat + 16 := addO (by fomega)
  have e24 : (R + 24#64).toNat = R.toNat + 24 := addO (by fomega)
  -- 1778: `cnt` to `rbp - 0x78`, the loop from bit 0
  refine (c_1778 prof fb).run c hfs hin _ hK hA hrip
    (vc_1778 (h := 6#64) (.inr rfl) h8 (by rw [hsp]; exact hal)
      (by rw [hbp]; exact rng hFW (by fomega) (by fomega) (by fomega))) ?_
  rintro j' g fl V' ⟨rfl, rfl, rfl⟩ Y₁ t₁ hK₁ hA₁ hr₁ hg₁ -
  rw [hbp, h12] at hA₁
  have b₁ : Y₁.cpu.gpr.rbp = bp := by rw [hg₁]; exact hbp
  have s₁ : Y₁.cpu.gpr.rsp = R := by rw [hg₁]; exact hsp
  have d₁ : Y₁.cpu.gpr.rdx = R := by rw [hg₁]; exact hsp
  have x₁ : Y₁.cpu.gpr.rbx = 0#64 := by rw [hg₁]; try rfl
  have r14₁ : Y₁.cpu.gpr.r14 = 6#64 := by rw [hg₁]; try rfl
  have r15₁ : Y₁.cpu.gpr.r15 = 0#64 := by rw [hg₁]; try rfl
  have r8₁ : Y₁.cpu.gpr.r8 = 1#64 := by rw [hg₁]; try rfl
  -- 1840: bit 0 clear
  refine (c_1840 prof fb).run c hfs hin _ hK₁ hA₁ hr₁ (vc_1840c (by rw [r14₁, r15₁]; try decide)) ?_
  rintro j' g fl V' ⟨rfl, rfl, rfl⟩ Y₂ t₂ hK₂ hA₂ hr₂ hg₂ -
  have b₂ : Y₂.cpu.gpr.rbp = bp := by rw [hg₂]; exact b₁
  have s₂ : Y₂.cpu.gpr.rsp = R := by rw [hg₂]; exact s₁
  have d₂ : Y₂.cpu.gpr.rdx = R := by rw [hg₂]; exact d₁
  have x₂ : Y₂.cpu.gpr.rbx = 0#64 := by rw [hg₂]; exact x₁
  have r14₂ : Y₂.cpu.gpr.r14 = 6#64 := by rw [hg₂]; exact r14₁
  have r8₂ : Y₂.cpu.gpr.r8 = 1#64 := by rw [hg₂]; exact r8₁
  have r15₂ : Y₂.cpu.gpr.r15 = BitVec.ofNat 64 1 := by
    rw [hg₂]
    show Y₁.cpu.gpr.r15 + 1#64 = _
    rw [r15₁]
    try decide
  -- 1840: bit 1 set, `x86_64` to entry 0
  refine (c_1840 prof fb).run c hfs hin _ hK₂ hA₂ hr₂
    (vc_1840s (b := 1) (.inl rfl) r15₂ (by rw [r14₂]; try decide)
      (by rw [b₂]; exact rng hFW (by fomega) (by fomega) (by fomega))
      (by rw [b₂]; exact rng hFW (by fomega) (by fomega) (by fomega))
      (by rw [d₂, x₂, sh0]; exact rng hFW (by fomega) (by fomega) (by fomega))) ?_
  rintro j' g fl V' ⟨rfl, rfl, rfl⟩ Y₃ t₃ hK₃ hA₃ hr₃ hg₃ -
  rw [b₂, r8₂, d₂, x₂, sh0, ex1] at hA₃
  have b₃ : Y₃.cpu.gpr.rbp = bp := by rw [hg₃]; exact b₂
  have s₃ : Y₃.cpu.gpr.rsp = R := by rw [hg₃]; exact s₂
  have x₃ : Y₃.cpu.gpr.rbx = 0#64 := by rw [hg₃]; exact x₂
  have r14₃ : Y₃.cpu.gpr.r14 = 6#64 := by rw [hg₃]; exact r14₂
  have r15₃ : Y₃.cpu.gpr.r15 = BitVec.ofNat 64 1 := by rw [hg₃]; exact r15₂
  have di₃ : Y₃.cpu.gpr.rdi = 7288953#64 := by rw [hg₃]; try exact ex1
  have r12₃ : Y₃.cpu.gpr.r12 = R := by
    rw [hg₃]
    show Y₂.cpu.gpr.rdx + Y₂.cpu.gpr.rbx <<< 4 = R
    rw [d₂, x₂, sh0]
  have r13₃ : Y₃.cpu.gpr.r13 = 0#64 := by
    rw [hg₃]
    show Y₂.cpu.gpr.rbx <<< 4 = _
    rw [x₂]
    try decide
  -- 1890: `strlen ("x86_64")`
  refine c.s_call hK₃ hA₃ hin (lt_len (by omega)) hr₃ (call_1890 _) hins hs0 tgt_1890
    (fun i hi => by rw [s₃]; exact rng hFW (by fomega) (by fomega) (by fomega) i hi) ?_
  rintro Y₄ t₄ hK₄ hA₄ ⟨hr₄, hg₄⟩
  rw [s₃] at hA₄ hg₄
  have s₄ : Y₄.cpu.gpr.rsp = R - 8 := by rw [hg₄]; rfl
  have di₄ : Y₄.cpu.gpr.rdi = 7288953#64 := by rw [hg₄]; exact di₃
  refine hlen 6 c hK₄ hA₄ hr₄ (hPl _ fun a ha => by vout) hin (j := 1895) (lt_len (by omega)) ?_
    (fun i hi => by rw [s₄]; exact rng hFD (by fomega) (by fomega) (by fomega) i hi)
    (by rw [di₄]; decide) (fun q hq => ?_) ?_ (fun x h1 h2 => ?_) ?_
  · rw [s₄]
    vself
  · have := lit_add (c := 7288953) (n := 6) (k := q) (by omega) (by decide)
    rw [di₄]
    vout
    exact hx1 q hq
  · have := lit_add (c := 7288953) (n := 6) (k := 6) (by omega) (by decide)
    rw [di₄]
    vout
    exact hx1z
  · rw [di₄] at h1 h2
    simp only [BitVec.reduceToNat] at h1 h2
    exact hpg x (by omega) (by omega)
  intro Z t₅ hK₅ hA₅ hr₅ hsp₅ hax₅ hbx₅ hbp₅ h12₅ h13₅ h14₅ h15₅
  have s₅ : Z.cpu.gpr.rsp = R := by rw [hsp₅, s₄]; exact sub8_add R
  have b₅ : Z.cpu.gpr.rbp = bp := by rw [hbp₅, hg₄]; exact b₃
  have x₅ : Z.cpu.gpr.rbx = 0#64 := by rw [hbx₅, hg₄]; exact x₃
  have r12₅ : Z.cpu.gpr.r12 = R := by rw [h12₅, hg₄]; exact r12₃
  have r13₅ : Z.cpu.gpr.r13 = 0#64 := by rw [h13₅, hg₄]; exact r13₃
  have r14₅ : Z.cpu.gpr.r14 = 6#64 := by rw [h14₅, hg₄]; exact r14₃
  have r15₅ : Z.cpu.gpr.r15 = BitVec.ofNat 64 1 := by rw [h15₅, hg₄]; exact r15₃
  -- 1895: the length to entry 0; bit 2 left: back to 1840
  refine (c_1895 prof fb).run c hfs hin _ hK₅ hA₅ hr₅
    (vc_1895 (b := 1) (m := 6#64) (T := R) (e := 1#64) (k := BitVec.ofNat 64 4) (.inr (.inl ⟨rfl, rfl⟩)) r15₅
      r14₅
      (by rw [b₅]; vpeel; vself)
      (by rw [r12₅, hax₅, b₅]; vpeel; vself)
      (by rw [r12₅, hax₅, b₅]; vpeel; vself)
      (by rw [r12₅]; exact rng hFW (by fomega) (by fomega) (by fomega))
      (by rw [b₅]; exact rng hFD (by fomega) (by fomega) (by fomega))
      (by rw [b₅]; exact rng hFD (by fomega) (by fomega) (by fomega))
      (by rw [b₅]; exact rng hFD (by fomega) (by fomega) (by fomega))) ?_
  rintro j' g fl V' ⟨rfl, hc⟩ Y₆ t₆ hK₆ hA₆ hr₆ hg₆ -
  rcases hc with ⟨hm, -, -⟩ | ⟨-, rfl, rfl⟩
  · exact absurd hm (by decide)
  rw [r12₅, hax₅] at hA₆
  have b₆ : Y₆.cpu.gpr.rbp = bp := by rw [hg₆]; exact b₅
  have s₆ : Y₆.cpu.gpr.rsp = R := by rw [hg₆]; exact s₅
  have d₆ : Y₆.cpu.gpr.rdx = R := by rw [hg₆]; try rfl
  have x₆ : Y₆.cpu.gpr.rbx = 1#64 := by rw [hg₆]; try rfl
  have r8₆ : Y₆.cpu.gpr.r8 = 2#64 := by rw [hg₆]; try decide
  have r14₆ : Y₆.cpu.gpr.r14 = 4#64 := by rw [hg₆]; try decide
  have r15₆ : Y₆.cpu.gpr.r15 = BitVec.ofNat 64 2 := by rw [hg₆]; try decide
  -- 1840: bit 2 set, `avx512_1` to entry 1
  refine (c_1840 prof fb).run c hfs hin _ hK₆ hA₆ hr₆
    (vc_1840s (b := 2) (.inr rfl) r15₆ (by rw [r14₆]; try decide)
      (by rw [b₆]; exact rng hFW (by fomega) (by fomega) (by fomega))
      (by rw [b₆]; exact rng hFW (by fomega) (by fomega) (by fomega))
      (by rw [d₆, x₆, sh1]; exact rng hFW (by fomega) (by fomega) (by fomega))) ?_
  rintro j' g fl V' ⟨rfl, rfl, rfl⟩ Y₇ t₇ hK₇ hA₇ hr₇ hg₇ -
  rw [b₆, r8₆, d₆, x₆, sh1, ex2] at hA₇
  have b₇ : Y₇.cpu.gpr.rbp = bp := by rw [hg₇]; exact b₆
  have s₇ : Y₇.cpu.gpr.rsp = R := by rw [hg₇]; exact s₆
  have x₇ : Y₇.cpu.gpr.rbx = 1#64 := by rw [hg₇]; exact x₆
  have r14₇ : Y₇.cpu.gpr.r14 = 4#64 := by rw [hg₇]; exact r14₆
  have r15₇ : Y₇.cpu.gpr.r15 = BitVec.ofNat 64 2 := by rw [hg₇]; exact r15₆
  have di₇ : Y₇.cpu.gpr.rdi = 7288962#64 := by rw [hg₇]; try exact ex2
  have r12₇ : Y₇.cpu.gpr.r12 = R + 16#64 := by
    rw [hg₇]
    show Y₆.cpu.gpr.rdx + Y₆.cpu.gpr.rbx <<< 4 = _
    rw [d₆, x₆, sh1]
  have r13₇ : Y₇.cpu.gpr.r13 = 16#64 := by
    rw [hg₇]
    show Y₆.cpu.gpr.rbx <<< 4 = _
    rw [x₆]
    try decide
  -- 1890: `strlen ("avx512_1")`
  refine c.s_call hK₇ hA₇ hin (lt_len (by omega)) hr₇ (call_1890 _) hins hs0 tgt_1890
    (fun i hi => by rw [s₇]; exact rng hFW (by fomega) (by fomega) (by fomega) i hi) ?_
  rintro Y₈ t₈ hK₈ hA₈ ⟨hr₈, hg₈⟩
  rw [s₇] at hA₈ hg₈
  have s₈ : Y₈.cpu.gpr.rsp = R - 8 := by rw [hg₈]; rfl
  have di₈ : Y₈.cpu.gpr.rdi = 7288962#64 := by rw [hg₈]; exact di₇
  refine hlen 8 c hK₈ hA₈ hr₈ (hPl _ fun a ha => by vout) hin (j := 1895) (lt_len (by omega)) ?_
    (fun i hi => by rw [s₈]; exact rng hFD (by fomega) (by fomega) (by fomega) i hi)
    (by rw [di₈]; decide) (fun q hq => ?_) ?_ (fun x h1 h2 => ?_) ?_
  · rw [s₈]
    vself
  · have := lit_add (c := 7288962) (n := 8) (k := q) (by omega) (by decide)
    rw [di₈]
    vout
    exact hx2 q hq
  · have := lit_add (c := 7288962) (n := 8) (k := 8) (by omega) (by decide)
    rw [di₈]
    vout
    exact hx2z
  · rw [di₈] at h1 h2
    simp only [BitVec.reduceToNat] at h1 h2
    exact hpg x (by omega) (by omega)
  intro Z₂ t₉ hK₉ hA₉ hr₉ hsp₉ hax₉ hbx₉ hbp₉ h12₉ h13₉ h14₉ h15₉
  have s₉ : Z₂.cpu.gpr.rsp = R := by rw [hsp₉, s₈]; exact sub8_add R
  have b₉ : Z₂.cpu.gpr.rbp = bp := by rw [hbp₉, hg₈]; exact b₇
  have x₉ : Z₂.cpu.gpr.rbx = 1#64 := by rw [hbx₉, hg₈]; exact x₇
  have r12₉ : Z₂.cpu.gpr.r12 = R + 16#64 := by rw [h12₉, hg₈]; exact r12₇
  have r13₉ : Z₂.cpu.gpr.r13 = 16#64 := by rw [h13₉, hg₈]; exact r13₇
  have r14₉ : Z₂.cpu.gpr.r14 = 4#64 := by rw [h14₉, hg₈]; exact r14₇
  have r15₉ : Z₂.cpu.gpr.r15 = BitVec.ofNat 64 2 := by rw [h15₉, hg₈]; exact r15₇
  -- 1895: the length to entry 1; bit 2 the last: to 682
  refine (c_1895 prof fb).run c hfs hin _ hK₉ hA₉ hr₉
    (vc_1895 (b := 2) (m := 4#64) (T := R) (e := 2#64) (k := BitVec.ofNat 64 4) (.inr (.inr ⟨rfl, rfl⟩)) r15₉
      r14₉
      (by rw [b₉]; vpeel; vself)
      (by rw [r12₉, hax₉, b₉, r168]; vpeel; vself)
      (by rw [r12₉, hax₉, b₉, r168]; vpeel; vself)
      (by rw [r12₉, r168]; exact rng hFW (by fomega) (by fomega) (by fomega))
      (by rw [b₉]; exact rng hFD (by fomega) (by fomega) (by fomega))
      (by rw [b₉]; exact rng hFD (by fomega) (by fomega) (by fomega))
      (by rw [b₉]; exact rng hFD (by fomega) (by fomega) (by fomega))) ?_
  rintro j' g fl V' ⟨rfl, hc⟩ Y₁₀ t₁₀ hK₁₀ hA₁₀ hr₁₀ hg₁₀ -
  rcases hc with ⟨-, rfl, rfl⟩ | ⟨hne, -, -⟩
  rotate_left
  · exact (hne (by decide)).elim
  rw [r12₉, hax₉, r168] at hA₁₀
  -- 682 on
  refine from682 (V := _) c hfs hin hinc hc0 hcpy hinm hm0 hmal (cnt := 4) (E := 16) (H := 8) (t := 32)
    (s := 320) (R := R) (bp := bp) (sp := R) (Q := Q) (N := N) (p := p) (S0 := 7288953#64) (S1 := 7288962#64)
    (fun W hW => hPm W fun a ha => (hW a ha).trans (by vout))
    (fun W hW => hPa W fun a ha => (hW a ha).trans (by vout))
    (.inr ⟨rfl, rfl, rfl, rfl, rfl⟩) (by omega) (Nat.le_refl _) (by omega) hfb
    (fun i hi => rng hFW (by fomega) (by fomega) (by fomega) i hi)
    (fun a h1 h2 => hFs a (by omega) h2) (fun a h1 h2 => hFD a (by omega) (by omega))
    (fun a h1 h2 => hFW a (by omega) (by omega))
    (by vpeel; vself) (by vpeel; vself) (fun _ => ⟨by vpeel; vself, by vself⟩)
    (rng hpg (by decide) (by decide) (by decide)) (by decide) (fun _ => rng hpg (by decide) (by decide) (by decide))
    (fun _ => by decide) htls (by vpeel; exact hp) hp0 (by vpeel; exact hpl) hpd
    (by vpeel; exact hNv) hND hN64 hsN (by vpeel; exact hQ) hsQ hQ64 hQd ?_ Y₁₀ t₁₀ hK₁₀ hA₁₀ hr₁₀
    ?_ ?_ ?_ ?_ ?_ ?_
  · intro Y t' W P hKY hAY hrY haxY hlo hpe hWP hspY hbxY h12Y h13Y h14Y h15Y hbpY hTab hS0 hSs hNE hSh
    exact k Y t' W P hKY hAY hrY haxY hlo hpe hWP hspY (hbxY.trans (by vpeel)) (h12Y.trans (by vpeel))
      (h13Y.trans (by vpeel)) (h14Y.trans (by vpeel)) (h15Y.trans (by vpeel)) (hbpY.trans (by vpeel)) hTab
      (Same.trans (fun a _ h2 => by vout) hS0) (Same.trans (fun a h1 h2 => by vout) hSs) hNE
      (Same.trans (fun a h1 h2 => by vout) hSh)
  · rw [hg₁₀]
    show R + (Z₂.cpu.gpr.r13 + 16#64) = _
    rw [r13₉]
    try exact add_lit R (by decide)
  · rw [hg₁₀]
    show Z₂.cpu.gpr.rbx + 2#64 = _
    rw [x₉]
    try decide
  · rw [hg₁₀]; try rfl
  · rw [hg₁₀]; try rfl
  · rw [hg₁₀]; exact b₉
  · rw [hg₁₀]; exact s₉

end FV7z.Hwc
