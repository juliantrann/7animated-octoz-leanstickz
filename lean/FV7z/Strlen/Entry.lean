import FV7z.Strlen.Loop
/-!
# `__strlen_sse2`, the way in (PLAN.md M, the PLT contracts)

From `+0`: `xmm0`–`xmm3` zeroed, `rax = rcx = p`, `ecx &= 4095`, `cmp ecx, 4047`, `ja +144`.

- `+144` (the first 64 bytes from `p` might cross a page): `rax` rounded down to 64, the four masks of the 64-byte block
  `B` joined into `rdx` and shifted right by `p - B`; a bit set: `bsf`, `ret`; none: `xmm1`–`xmm3` zeroed again, the
  loop (`Strlen/Loop.lean`) from `B`.
- `+42` (they do not): the 16 bytes from `p` unaligned; a 0: `bsf`, `ret`. Else `rax` rounded down to 16 (`B`), the
  masks of `[B + 16, B + 64)` joined, shifted by `p - B`; a bit: `bsf`, `ret`; none: the loop from `B` rounded down to
  64, `xmm1`–`xmm3` 0 since none of these 48 bytes is.
-/
namespace FV7z.Strlen
open ZellicX86 Decode FV7z.Leaf FV7z.Fn

/-! ## Numbers -/

theorem nat_and_hi (n k : Nat) (hk : k ≤ 64) (h : n < 2 ^ 64) : n &&& (2 ^ (64 - k) - 1) <<< k = n / 2 ^ k * 2 ^ k := by
  have hr : n / 2 ^ k * 2 ^ k = (n >>> k) <<< k := by rw [Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
  rw [hr]
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and, Nat.testBit_shiftLeft, Nat.testBit_shiftLeft, Nat.testBit_shiftRight,
    Nat.testBit_two_pow_sub_one]
  by_cases h1 : i ≥ k
  · have e : k + (i - k) = i := by omega
    rw [e]
    by_cases h2 : i < 64
    · have : i - k < 64 - k := by omega
      simp [h1, this]
    · have h3 : n.testBit i = false :=
        Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le h (Nat.pow_le_pow_right (by decide) (by omega)))
      simp [h3]
  · simp [h1]

/-- `x &&& -64`. -/
theorem and_m64 (x : BitVec 64) : (x &&& BitVec.ofNat 64 18446744073709551552).toNat = x.toNat / 64 * 64 := by
  rw [BitVec.toNat_and, BitVec.toNat_ofNat, show 18446744073709551552 % 2 ^ 64 = (2 ^ (64 - 6) - 1) <<< 6 by decide]
  exact nat_and_hi _ 6 (by decide) x.isLt

/-- `x &&& -16`. -/
theorem and_m16' (x : BitVec 64) : (x &&& BitVec.ofNat 64 18446744073709551600).toNat = x.toNat / 16 * 16 := by
  rw [BitVec.toNat_and, BitVec.toNat_ofNat, show 18446744073709551600 % 2 ^ 64 = (2 ^ (64 - 4) - 1) <<< 4 by decide]
  exact nat_and_hi _ 4 (by decide) x.isLt

theorem and_low {B : Addr} (h : B.toNat % 64 = 0) : B &&& BitVec.ofNat 64 18446744073709551552 = B := by
  apply BitVec.eq_of_toNat_eq
  rw [and_m64]
  omega

theorem and_4095 (x : BitVec 64) : (x &&& BitVec.ofNat 64 4095).toNat = x.toNat % 4096 := by
  rw [BitVec.toNat_and, BitVec.toNat_ofNat]
  exact Nat.and_two_pow_sub_one_eq_mod _ 12

theorem nat_xor_floor (a k : Nat) : a ^^^ a / 2 ^ k * 2 ^ k = a % 2 ^ k := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_xor, Nat.testBit_mul_two_pow, Nat.testBit_div_two_pow, Nat.testBit_mod_two_pow]
  by_cases h : k ≤ i
  · rw [decide_eq_true h, Nat.sub_add_cancel h, Bool.true_and, Bool.xor_self, decide_eq_false (by omega),
      Bool.false_and]
  · rw [decide_eq_false h, Bool.false_and, Bool.xor_false, decide_eq_true (by omega), Bool.true_and]

/-- `sar`'s count `cl` from `rcx = a ^^^ b`, `b` the 64-aligned `a`. -/
theorem cnt64 {a b : BitVec 64} (hb : b.toNat = a.toNat / 64 * 64) :
    ((a ^^^ b).setWidth 8).toNat % 64 = a.toNat % 64 := by
  have h := nat_xor_floor a.toNat 6
  rw [show (2 : Nat) ^ 6 = 64 from rfl] at h
  rw [BitVec.toNat_setWidth, BitVec.toNat_xor, hb, h, show (2 : Nat) ^ 8 = 256 from rfl]
  omega

/-- The same, `b` the 16-aligned `a`. -/
theorem cnt16 {a b : BitVec 64} (hb : b.toNat = a.toNat / 16 * 16) :
    ((a ^^^ b).setWidth 8).toNat % 64 = a.toNat % 16 := by
  have h := nat_xor_floor a.toNat 4
  rw [show (2 : Nat) ^ 4 = 16 from rfl] at h
  rw [BitVec.toNat_setWidth, BitVec.toNat_xor, hb, h, show (2 : Nat) ^ 8 = 256 from rfl]
  omega

theorem ofNat32_64 {n : Nat} (h : n < 2 ^ 32) : (BitVec.ofNat 32 n).setWidth 64 = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  omega

theorem xor_self' {w : Nat} (a : BitVec w) : a ^^^ a = 0 := BitVec.xor_self

theorem al16b {B : Addr} (hB : B.toNat % 16 = 0) {d : Nat} (hd : d % 16 = 0) :
    (B + BitVec.ofNat 64 d).toNat % 16 = 0 := by
  have := B.isLt
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

/-! ## Flags -/

theorem cond4_mask {w : Nat} {f fl : Rflags} {M : BitVec w} (h : LogF f M fl) : fl.cond 4 = (M == 0) := by
  obtain ⟨af, rfl⟩ := h
  rw [cond4, arith_zf]

/-- `ja` not taken after `cmp a, b`. -/
theorem ja_false {a b : BitVec 64} (h : (!(decide (a.toNat < b.toNat) || decide (a = b))) = false) :
    a.toNat ≤ b.toNat := by
  by_cases h1 : a.toNat < b.toNat
  · exact Nat.le_of_lt h1
  · by_cases h2 : a = b
    · rw [h2]; exact Nat.le_refl _
    · rw [decide_eq_false h1, decide_eq_false h2] at h
      exact absurd h (by decide)

/-! ## Bytes -/

/-- 16 bytes from `B + d` on the string's first page are to read. -/
theorem foot_pg {F : Footprint} {p : Addr} {n : Nat}
    (hft : ∀ x : Addr, p.toNat / 4096 ≤ x.toNat / 4096 → x.toNat / 4096 ≤ (p.toNat + n) / 4096 → Foot F.data x)
    {B : Addr} {d : Nat} (hlo : (B.toNat + d) / 4096 = p.toNat / 4096)
    (hhi : (B.toNat + d + 15) / 4096 = p.toNat / 4096) (hov : B.toNat + d + 15 < 2 ^ 64) :
    ∀ i < 16, Foot F.data (Addr.add (B + BitVec.ofNat 64 d) i) := by
  intro i hi
  have := B.isLt
  have e : (Addr.add (B + BitVec.ofNat 64 d) i).toNat = B.toNat + d + i := by
    simp only [Addr.add, BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  apply hft <;> rw [e] <;> omega

/-- Bit `i` of the mask of the 16 bytes at `B + d` compared with 0 (`pcmpeqb` with the bytes first). -/
theorem zbit' (V : Addr → Byte) (B : Addr) (d i : Nat) :
    (pmsk (peqb (rd16 V (B + BitVec.ofNat 64 d)) 0)).getLsbD i =
      (decide (i < 16) && decide (V (Addr.add B (i + d)) = 0)) := by
  rw [getLsbD_zmask]
  by_cases hi : i < 16
  · rw [lane_rd16 _ _ hi, show B + BitVec.ofNat 64 d = Addr.add B d from rfl, addr_add_add, Nat.add_comm d i]
  · rw [decide_eq_false hi, Bool.false_and, Bool.false_and]

/-- The mask of the 16 bytes from `p`: 0 iff the string is 16 bytes or more, else its lowest bit the length. -/
theorem m16 {V : Addr → Byte} {a p : Addr} {n : Nat} (ha : a = p) (hnz : ∀ k < n, V (Addr.add p k) ≠ 0)
    (hz : V (Addr.add p n) = 0) :
    (pmsk (peqb (rd16 V (a + BitVec.ofNat 64 0)) 0) = 0 ↔ 16 ≤ n) ∧
      (n < 16 → lowestSetBit (pmsk (peqb (rd16 V (a + BitVec.ofNat 64 0)) 0)) = n) := by
  rw [← ha] at hnz hz
  refine ⟨⟨fun h0 => ?_, fun h16 => ?_⟩, fun hn => ?_⟩
  · refine Classical.byContradiction fun hlt => ?_
    have h := zbit' V a 0 n
    rw [h0, getLsbD_zero', decide_eq_true (by omega : n < 16), Nat.add_zero, hz] at h
    exact absurd h (by decide)
  · apply BitVec.eq_of_getLsbD_eq
    intro i _
    rw [zbit', getLsbD_zero']
    by_cases hi : i < 16
    · rw [decide_eq_true hi, Bool.true_and, Nat.add_zero]
      exact decide_eq_false (hnz i (by omega))
    · rw [decide_eq_false hi, Bool.false_and]
  · apply lowestSetBit_eq (by omega : n < 32)
    · rw [zbit', decide_eq_true hn, Nat.add_zero, hz]
      rfl
    · intro i hi
      rw [zbit', decide_eq_true (by omega : i < 16), Nat.add_zero, Bool.true_and]
      exact decide_eq_false (hnz i hi)

/-- `pcmpeqb` of 0 with a vector none of whose bytes is 0. -/
theorem peqb0_eq_zero (a : BitVec 128) (h : ∀ j < 16, lane 8 a j ≠ 0) : peqb 0 a = 0 := by
  have e : ∀ j < 16, (if lane 8 (0 : BitVec 128) j = lane 8 a j then BitVec.allOnes 8 else (0 : BitVec 8)) = 0 :=
    fun j hj => by rw [lane_zero, if_neg (Ne.symm (h j hj))]
  simp only [peqb, ofBytes, e 0 (by decide), e 1 (by decide), e 2 (by decide), e 3 (by decide), e 4 (by decide),
    e 5 (by decide), e 6 (by decide), e 7 (by decide), e 8 (by decide), e 9 (by decide), e 10 (by decide),
    e 11 (by decide), e 12 (by decide), e 13 (by decide), e 14 (by decide), e 15 (by decide)] <;> rfl

/-- The same, the 16 bytes at `B + d` within the string. -/
theorem peqb_rd16_zero {V : Addr → Byte} {p B : Addr} {n d : Nat} (hnz : ∀ k < n, V (Addr.add p k) ≠ 0)
    (hlo : p.toNat ≤ B.toNat + d) (hhi : B.toNat + d + 16 ≤ p.toNat + n) :
    peqb 0 (rd16 V (B + BitVec.ofNat 64 d)) = 0 := by
  apply peqb0_eq_zero
  intro j hj
  rw [lane_rd16 _ _ hj, show Addr.add (B + BitVec.ofNat 64 d) j = Addr.add B (d + j) from addr_add_add B d j,
    addr_eq (a := B) (b := p) (i := d + j) (j := B.toNat + d + j - p.toNat) (by omega)]
  exact hnz _ (by omega)

/-- The joined mask of the block `B` shifted right by `p - B`: 0 iff the string goes past the block, else its lowest
bit the length. Only its bits from `p - B` on matter. -/
theorem sar_spec {V : Addr → Byte} {p B : Addr} {n r : Nat} {J : BitVec 64}
    (hbit : ∀ i < 64, p.toNat - B.toNat ≤ i → J.getLsbD i = decide (V (Addr.add B i) = 0))
    (hr : r = p.toNat - B.toNat)
    (hBp : B.toNat ≤ p.toNat) (hpB : p.toNat < B.toNat + 64)
    (hnz : ∀ k < n, V (Addr.add p k) ≠ 0) (hz : V (Addr.add p n) = 0) :
    (J.sshiftRight r = 0 ↔ B.toNat + 64 ≤ p.toNat + n) ∧
      (p.toNat + n < B.toNat + 64 → lowestSetBit (J.sshiftRight r) = n) := by
  subst hr
  refine ⟨⟨fun h0 => Classical.byContradiction fun hlt => ?_, fun hge => ?_⟩, fun hlt => ?_⟩
  · have h1 : (J.sshiftRight (p.toNat - B.toNat)).getLsbD n = true := by
      rw [BitVec.getLsbD_sshiftRight, if_pos (by omega), Nat.add_comm (p.toNat - B.toNat) n,
        hbit (n + (p.toNat - B.toNat)) (by omega) (by omega),
        addr_eq (a := B) (b := p) (i := n + (p.toNat - B.toNat)) (j := n) (by omega), hz, decide_eq_false (by omega)]
      rfl
    rw [h0, getLsbD_zero'] at h1
    exact Bool.false_ne_true h1
  · apply sar_eq_zero (by omega)
    intro i h1 h2
    rw [hbit i h2 h1, addr_eq (a := B) (b := p) (i := i) (j := B.toNat + i - p.toNat) (by omega)]
    exact decide_eq_false (hnz _ (by omega))
  · apply lsb_sar (by omega)
    · rw [hbit (n + (p.toNat - B.toNat)) (by omega) (by omega),
        addr_eq (a := B) (b := p) (i := n + (p.toNat - B.toNat)) (j := n) (by omega), hz]
      rfl
    · intro i hi
      rw [hbit (i + (p.toNat - B.toNat)) (by omega) (by omega),
        addr_eq (a := B) (b := p) (i := i + (p.toNat - B.toNat)) (j := i) (by omega)]
      exact decide_eq_false (hnz i hi)

/-- From `+62`: the bits below 16 of the joined mask are clear, as the bytes there from `p` on are not 0. -/
theorem bit3 {V : Addr → Byte} {p B : Addr} {n i : Nat} (hnz : ∀ k < n, V (Addr.add p k) ≠ 0) (h16 : 16 ≤ n)
    (hB : B.toNat = p.toNat / 16 * 16) (hri : p.toNat - B.toNat ≤ i) :
    (decide (16 ≤ i) && decide (V (Addr.add B i) = 0)) = decide (V (Addr.add B i) = 0) := by
  by_cases h : 16 ≤ i
  · rw [decide_eq_true h, Bool.true_and]
  · rw [decide_eq_false h, Bool.false_and, addr_eq (a := B) (b := p) (i := i) (j := B.toNat + i - p.toNat) (by omega)]
    exact (decide_eq_false (hnz _ (by omega))).symm

/-- `xmm0`–`xmm3` are 0. -/
abbrev X4 (x : XRegs) : Prop := x (xmmOf 0) = 0 ∧ Z3 x

/-! ## The paths -/

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle} {F : Footprint} {Wl : List Rgn}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {e' : Addr} {V : Addr → Byte}

set_option maxHeartbeats 4000000 in
/-- From `+144`, `rax = p`, `xmm0`–`xmm3` 0. -/
theorem pathB_1 (c : Seg prof F Wl L s₀ o) (hin : CodeIn L e' sl2) {X : State} {t : Nat} {g₀ : Gprs} {n : Nat}
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = e'.add 144)
    (hax : X.cpu.gpr.rax = g₀.rdi) (hkp : Kp g₀ X.cpu.gpr) (hx : X4 (xsOf X.cpu.vec.zmm))
    (hov : g₀.rdi.toNat + n < 2 ^ 64)
    (hnz : ∀ k < n, V (Addr.add g₀.rdi k) ≠ 0) (hz : V (Addr.add g₀.rdi n) = 0)
    (hft : ∀ x : Addr, g₀.rdi.toNat / 4096 ≤ x.toNat / 4096 → x.toNat / 4096 ≤ (g₀.rdi.toNat + n) / 4096 →
      Foot F.data x)
    (hR : Ret prof F Wl L s₀ o gev gP gE V g₀ n) : GoG prof L o gev gP gE X t := by
  obtain ⟨hx0, hx1, hx2, hx3⟩ := hx
  -- `and rax, -64`
  refine c.s_blkV hin (b144 prof) hK hA hrip ?_
  refine wpV_reg fun _ _ => wpV_nil ?_
  intro Y₁ t₁ hK₁ hA₁ hr₁ hg₁ _ hv₁
  simp only [wr, gv, Src.val, set_rax, get0, BitVec.setWidth_eq] at hg₁
  have hB₁ : Y₁.cpu.gpr.rax.toNat = g₀.rdi.toNat / 64 * 64 := by simp only [hg₁]; rw [hax]; exact and_m64 _
  have hkp₁ : Kp g₀ Y₁.cpu.gpr := by simp only [Kp, hg₁]; exact hkp
  have hdi₁ : Y₁.cpu.gpr.rdi = g₀.rdi := hkp₁.1
  rw [← hv₁] at hx0 hx1 hx2 hx3
  -- the block's four masks joined, shifted right by `p - B`
  have hF := foot64 hft (B := Y₁.cpu.gpr.rax) (by omega) (by omega) (by omega)
  have hal : ∀ d, d % 16 = 0 → true = true → (Y₁.cpu.gpr.rax + BitVec.ofNat 64 d).toNat % 16 = 0 :=
    fun d h1 _ => al16 (by omega) h1
  refine c.s_blkV hin (b148 prof) hK₁ hA₁ hr₁ ?_
  refine wpV_v (foot16 hF (d := 0) (by omega)) (hal 0 rfl)
    (wpV_v (foot16 hF (d := 16) (by omega)) (hal 16 rfl)
    (wpV_v (foot16 hF (d := 32) (by omega)) (hal 32 rfl)
    (wpV_v (foot16 hF (d := 48) (by omega)) (hal 48 rfl)
    (wpV_v0 (wpV_v0 (wpV_v0 (wpV_v0 (wpV_reg fun _ _ => wpV_reg fun _ _ => wpV_reg fun _ _ => wpV_reg fun _ _ =>
      wpV_reg fun _ _ => wpV_reg fun _ _ => wpV_reg fun _ _ => wpV_reg fun _ _ => wpV_reg fun _ _ =>
      wpV_reg fun _ _ => wpV_reg fun fl hP => wpV_nil ?_))))))))
  intro Y₂ t₂ hK₂ hA₂ hr₂ hg₂ hf₂ _
  generalize hxd : xsOf Y₁.cpu.vec.zmm = x at hg₂ hP hx0 hx1 hx2 hx3
  simp (disch := decide) only [wr, gv, Src.val, eaB, set_rax, set_rcx, set_rdx, set_rsi, set_r8, get0, get1, get2,
    get6, get7, get8, xset_same, xset_ne, BitVec.setWidth_eq, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod,
    BitVec.and_self, hx0, hx1, hx2, hx3] at hg₂ hP
  have hkp₂ : Kp g₀ Y₂.cpu.gpr := by simp only [Kp, hg₂]; exact hkp₁
  generalize hBd : Y₁.cpu.gpr.rax = B at hg₂ hP hB₁
  trace_state
  sorry

set_option maxHeartbeats 4000000 in
/-- From `+144`, `rax = p`, `xmm0`–`xmm3` 0. -/
theorem pathB_r (c : Seg prof F Wl L s₀ o) (hin : CodeIn L e' sl2) {X : State} {t : Nat} {g₀ : Gprs} {n : Nat}
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = e'.add 144)
    (hax : X.cpu.gpr.rax = g₀.rdi) (hkp : Kp g₀ X.cpu.gpr) (hx : X4 (xsOf X.cpu.vec.zmm))
    (hov : g₀.rdi.toNat + n < 2 ^ 64)
    (hnz : ∀ k < n, V (Addr.add g₀.rdi k) ≠ 0) (hz : V (Addr.add g₀.rdi n) = 0)
    (hft : ∀ x : Addr, g₀.rdi.toNat / 4096 ≤ x.toNat / 4096 → x.toNat / 4096 ≤ (g₀.rdi.toNat + n) / 4096 →
      Foot F.data x)
    (hR : Ret prof F Wl L s₀ o gev gP gE V g₀ n) : GoG prof L o gev gP gE X t := by
  obtain ⟨hx0, hx1, hx2, hx3⟩ := hx
  -- `and rax, -64`
  refine c.s_blkV hin (b144 prof) hK hA hrip ?_
  refine wpV_reg fun _ _ => wpV_nil ?_
  intro Y₁ t₁ hK₁ hA₁ hr₁ hg₁ _ hv₁
  simp only [wr, gv, Src.val, set_rax, get0, BitVec.setWidth_eq] at hg₁
  have hB₁ : Y₁.cpu.gpr.rax.toNat = g₀.rdi.toNat / 64 * 64 := by simp only [hg₁]; rw [hax]; exact and_m64 _
  have hkp₁ : Kp g₀ Y₁.cpu.gpr := by simp only [Kp, hg₁]; exact hkp
  have hdi₁ : Y₁.cpu.gpr.rdi = g₀.rdi := hkp₁.1
  rw [← hv₁] at hx0 hx1 hx2 hx3
  -- the block's four masks joined, shifted right by `p - B`
  have hF := foot64 hft (B := Y₁.cpu.gpr.rax) (by omega) (by omega) (by omega)
  have hal : ∀ d, d % 16 = 0 → true = true → (Y₁.cpu.gpr.rax + BitVec.ofNat 64 d).toNat % 16 = 0 :=
    fun d h1 _ => al16 (by omega) h1
  refine c.s_blkV hin (b148 prof) hK₁ hA₁ hr₁ ?_
  refine wpV_v (foot16 hF (d := 0) (by omega)) (hal 0 rfl)
    (wpV_v (foot16 hF (d := 16) (by omega)) (hal 16 rfl)
    (wpV_v (foot16 hF (d := 32) (by omega)) (hal 32 rfl)
    (wpV_v (foot16 hF (d := 48) (by omega)) (hal 48 rfl)
    (wpV_v0 (wpV_v0 (wpV_v0 (wpV_v0 (wpV_reg fun _ _ => wpV_reg fun _ _ => wpV_reg fun _ _ => wpV_reg fun _ _ =>
      wpV_reg fun _ _ => wpV_reg fun _ _ => wpV_reg fun _ _ => wpV_reg fun _ _ => wpV_reg fun _ _ =>
      wpV_reg fun _ _ => wpV_reg fun fl hP => wpV_nil ?_))))))))
  intro Y₂ t₂ hK₂ hA₂ hr₂ hg₂ hf₂ _
  generalize hxd : xsOf Y₁.cpu.vec.zmm = x at hg₂ hP hx0 hx1 hx2 hx3
  simp (disch := decide) only [wr, gv, Src.val, eaB, set_rax, set_rcx, set_rdx, set_rsi, set_r8, get0, get1, get2,
    get6, get7, get8, xset_same, xset_ne, BitVec.setWidth_eq, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod,
    BitVec.and_self, hx0, hx1, hx2, hx3] at hg₂ hP
  have hkp₂ : Kp g₀ Y₂.cpu.gpr := by simp only [Kp, hg₂]; exact hkp₁
  generalize hBd : Y₁.cpu.gpr.rax = B at hg₂ hP hB₁
  have hax₂ : Y₂.cpu.gpr.rax = B := by simp only [hg₂]; exact and_low (by omega)
  have hS : (Y₂.cpu.gpr.rdx = 0 ↔ B.toNat + 64 ≤ g₀.rdi.toNat + n) ∧
      (g₀.rdi.toNat + n < B.toNat + 64 → lowestSetBit Y₂.cpu.gpr.rdx = n) := by
    simp only [hg₂]
    exact sar_spec (fun i hi _ => by
        rw [getLsbD_join _ _ _ _ (fun i => decide (V (Addr.add B i) = 0)) (zbit V B 0) (zbit V B 16) (zbit V B 32)
          (zbit V B 48) hi])
      (by rw [hdi₁, cnt64 hB₁]; omega) (by omega) (by omega) hnz hz
  have hc : fl.cond 4 = (Y₂.cpu.gpr.rdx == 0) := by rw [cond4_mask hP]; simp only [hg₂]
  refine c.s_jccV hK₂ hA₂ hin (by rw [sl2_length]; omega) hr₂ (d221 prof.feat) (tgt := 240) rfl
    (by rw [sl2_length]; omega) ?_ ?_
  · -- none: `xmm1`–`xmm3` zeroed, the loop from `B`
    intro htk Y₃ t₃ hK₃ hA₃ ⟨hr₃, hg₃, _⟩
    rw [hf₂, hc] at htk
    have hge := hS.1.1 (eq_of_beq htk)
    refine c.s_blkV hin (b240 prof) hK₃ hA₃ hr₃ ?_
    refine wpV_v0 (wpV_v0 (wpV_v0 (wpV_reg fun _ _ => wpV_nil ?_)))
    intro Y₄ t₄ hK₄ hA₄ hr₄ hg₄ _ hv₄
    have hz₄ : Z3 (xsOf Y₄.cpu.vec.zmm) := by
      rw [hv₄]
      refine ⟨?_, ?_, ?_⟩ <;> simp (disch := decide) only [xset_same, xset_ne, xor_self']
    have hax₄ : Y₄.cpu.gpr.rax = B := by rw [hg₄, hg₃]; exact hax₂
    have hkp₄ : Kp g₀ Y₄.cpu.gpr := by rw [hg₄, hg₃]; exact hkp₂
    exact loop c hin hov hnz hz hft hR _ Y₄ t₄ B (Nat.lt_succ_self _) hK₄ hA₄ hr₄ hax₄ hkp₄ hz₄ (by omega)
      (by omega) hge
  · -- a bit: `bsf rax, rdx`, `ret`
    intro hfa Y₃ t₃ hK₃ hA₃ ⟨hr₃, hg₃, _⟩
    rw [hf₂, hc] at hfa
    have hne : Y₂.cpu.gpr.rdx ≠ 0 := ne_of_beq_false hfa
    have hlt : g₀.rdi.toNat + n < B.toNat + 64 := Classical.byContradiction fun h => hne (hS.1.2 (by omega))
    have hlow : lowestSetBit (rv Y₃ 64 2) = n := by
      simp only [rv, get2, BitVec.setWidth_eq, hg₃]; exact hS.2 hlt
    refine c.s_bsf64 hK₃ hA₃ hin (by rw [sl2_length]; omega) hr₃ (d223 prof.feat)
      (by simp only [rv, get2, BitVec.setWidth_eq, hg₃]; exact hne) ?_
    rintro Y₄ t₄ hK₄ hA₄ ⟨hr₄, hg₄⟩
    have hkp₄ : Kp g₀ Y₄.cpu.gpr := by simp only [Kp, hg₄, set_rax, hg₃]; exact hkp₂
    have hax₄ : Y₄.cpu.gpr.rax = BitVec.ofNat 64 n := by simp only [hg₄, set_rax, hlow]
    exact ret_at c hin (by rw [sl2_length]; omega) (d227 prof.feat) hK₄ hA₄ hr₄ hkp₄ hax₄ hR

set_option maxHeartbeats 4000000 in
/-- From `+144`, `rax = p`, `xmm0`–`xmm3` 0. -/
theorem pathB (c : Seg prof F Wl L s₀ o) (hin : CodeIn L e' sl2) {X : State} {t : Nat} {g₀ : Gprs} {n : Nat}
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = e'.add 144)
    (hax : X.cpu.gpr.rax = g₀.rdi) (hkp : Kp g₀ X.cpu.gpr) (hx : X4 (xsOf X.cpu.vec.zmm))
    (hov : g₀.rdi.toNat + n < 2 ^ 64)
    (hnz : ∀ k < n, V (Addr.add g₀.rdi k) ≠ 0) (hz : V (Addr.add g₀.rdi n) = 0)
    (hft : ∀ x : Addr, g₀.rdi.toNat / 4096 ≤ x.toNat / 4096 → x.toNat / 4096 ≤ (g₀.rdi.toNat + n) / 4096 →
      Foot F.data x)
    (hR : Ret prof F Wl L s₀ o gev gP gE V g₀ n) : GoG prof L o gev gP gE X t := by
  sorry

set_option maxHeartbeats 4000000 in
/-- From `+62`, `rax = p`, `xmm0`–`xmm3` 0, the first 16 bytes from `p` not 0, on a page with 48 more after them. -/
theorem pathA2 (c : Seg prof F Wl L s₀ o) (hin : CodeIn L e' sl2) {X : State} {t : Nat} {g₀ : Gprs} {n : Nat}
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = e'.add 62)
    (hax : X.cpu.gpr.rax = g₀.rdi) (hkp : Kp g₀ X.cpu.gpr) (hx : X4 (xsOf X.cpu.vec.zmm))
    (hq : g₀.rdi.toNat % 4096 ≤ 4047) (h16 : 16 ≤ n) (hov : g₀.rdi.toNat + n < 2 ^ 64)
    (hnz : ∀ k < n, V (Addr.add g₀.rdi k) ≠ 0) (hz : V (Addr.add g₀.rdi n) = 0)
    (hft : ∀ x : Addr, g₀.rdi.toNat / 4096 ≤ x.toNat / 4096 → x.toNat / 4096 ≤ (g₀.rdi.toNat + n) / 4096 →
      Foot F.data x)
    (hR : Ret prof F Wl L s₀ o gev gP gE V g₀ n) : GoG prof L o gev gP gE X t := by
  obtain ⟨hx0, hx1, hx2, hx3⟩ := hx
  have hp := g₀.rdi.isLt
  -- `and rax, -16`
  refine c.s_blkV hin (b62 prof) hK hA hrip ?_
  refine wpV_reg fun _ _ => wpV_nil ?_
  intro Y₁ t₁ hK₁ hA₁ hr₁ hg₁ _ hv₁
  simp only [wr, gv, Src.val, set_rax, get0, BitVec.setWidth_eq] at hg₁
  have hB₁ : Y₁.cpu.gpr.rax.toNat = g₀.rdi.toNat / 16 * 16 := by simp only [hg₁]; rw [hax]; exact and_m16' _
  have hkp₁ : Kp g₀ Y₁.cpu.gpr := by simp only [Kp, hg₁]; exact hkp
  have hdi₁ : Y₁.cpu.gpr.rdi = g₀.rdi := hkp₁.1
  rw [← hv₁] at hx0 hx1 hx2 hx3
  -- the masks of `[B + 16, B + 64)` joined, shifted right by `p - B`
  have hal : ∀ d, d % 16 = 0 → true = true → (Y₁.cpu.gpr.rax + BitVec.ofNat 64 d).toNat % 16 = 0 :=
    fun d h1 _ => al16b (by omega) h1
  refine c.s_blkV hin (b66 prof) hK₁ hA₁ hr₁ ?_
  refine wpV_v (foot_pg hft (B := Y₁.cpu.gpr.rax) (d := 16) (by omega) (by omega) (by omega)) (hal 16 rfl)
    (wpV_v (foot_pg hft (B := Y₁.cpu.gpr.rax) (d := 32) (by omega) (by omega) (by omega)) (hal 32 rfl)
    (wpV_v (foot_pg hft (B := Y₁.cpu.gpr.rax) (d := 48) (by omega) (by omega) (by omega)) (hal 48 rfl)
    (wpV_v0 (wpV_v0 (wpV_v0 (wpV_reg fun _ _ => wpV_reg fun _ _ => wpV_reg fun _ _ => wpV_reg fun _ _ =>
      wpV_reg fun _ _ => wpV_reg fun _ _ => wpV_reg fun _ _ => wpV_reg fun _ _ => wpV_reg fun _ _ =>
      wpV_reg fun fl hP => wpV_nil ?_))))))
  intro Y₂ t₂ hK₂ hA₂ hr₂ hg₂ hf₂ hv₂
  generalize hxd : xsOf Y₁.cpu.vec.zmm = x at hg₂ hP hv₂ hx0 hx1 hx2 hx3
  simp (disch := decide) only [wr, gv, Src.val, eaB, set_rax, set_rcx, set_rdx, set_r8, get0, get1, get2, get7,
    get8, xset_same, xset_ne, BitVec.setWidth_eq, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, BitVec.and_self,
    hx1, hx2, hx3] at hg₂ hP hv₂
  have hkp₂ : Kp g₀ Y₂.cpu.gpr := by simp only [Kp, hg₂]; exact hkp₁
  generalize hBd : Y₁.cpu.gpr.rax = B at hg₂ hP hv₂ hB₁
  have hC : Y₂.cpu.gpr.rax.toNat = B.toNat / 64 * 64 := by simp only [hg₂]; exact and_m64 _
  have hS : (Y₂.cpu.gpr.rdx = 0 ↔ B.toNat + 64 ≤ g₀.rdi.toNat + n) ∧
      (g₀.rdi.toNat + n < B.toNat + 64 → lowestSetBit Y₂.cpu.gpr.rdx = n) := by
    simp only [hg₂]
    exact sar_spec (fun i hi hri => by
        rw [getLsbD_join3 _ _ _ (fun i => decide (V (Addr.add B i) = 0)) (zbit V B 16) (zbit V B 32) (zbit V B 48) hi]
        exact bit3 hnz h16 hB₁ hri)
      (by rw [hdi₁, cnt16 hB₁]; omega) (by omega) (by omega) hnz hz
  have hc : fl.cond 4 = (Y₂.cpu.gpr.rdx == 0) := by rw [cond4_mask hP]; simp only [hg₂]
  refine c.s_jccV hK₂ hA₂ hin (by rw [sl2_length]; omega) hr₂ (d128 prof.feat) (tgt := 256) rfl
    (by rw [sl2_length]; omega) ?_ ?_
  · -- none: the loop from `B` rounded down to 64; `xmm1`–`xmm3` are 0 as none of the 48 bytes is
    intro htk Y₃ t₃ hK₃ hA₃ ⟨hr₃, hg₃, hv₃⟩
    rw [hf₂, hc] at htk
    have hge := hS.1.1 (eq_of_beq htk)
    have hz₃ : Z3 (xsOf Y₃.cpu.vec.zmm) := by
      rw [hv₃, hv₂]
      refine ⟨?_, ?_, ?_⟩ <;> simp (disch := decide) only [xset_same, xset_ne] <;>
        exact peqb_rd16_zero hnz (by omega) (by omega)
    exact loop c hin hov hnz hz hft hR _ Y₃ t₃ Y₃.cpu.gpr.rax (Nat.lt_succ_self _) hK₃ hA₃ hr₃ rfl
      (by rw [hg₃]; exact hkp₂) hz₃ (by rw [hg₃]; omega) (by rw [hg₃]; omega) (by rw [hg₃]; omega)
  · -- a bit: `bsf rax, rdx`, `ret`
    intro hfa Y₃ t₃ hK₃ hA₃ ⟨hr₃, hg₃, _⟩
    rw [hf₂, hc] at hfa
    have hne : Y₂.cpu.gpr.rdx ≠ 0 := ne_of_beq_false hfa
    have hlt : g₀.rdi.toNat + n < B.toNat + 64 := Classical.byContradiction fun h => hne (hS.1.2 (by omega))
    have hlow : lowestSetBit (rv Y₃ 64 2) = n := by
      simp only [rv, get2, BitVec.setWidth_eq, hg₃]; exact hS.2 hlt
    refine c.s_bsf64 hK₃ hA₃ hin (by rw [sl2_length]; omega) hr₃ (d130 prof.feat)
      (by simp only [rv, get2, BitVec.setWidth_eq, hg₃]; exact hne) ?_
    rintro Y₄ t₄ hK₄ hA₄ ⟨hr₄, hg₄⟩
    have hkp₄ : Kp g₀ Y₄.cpu.gpr := by simp only [Kp, hg₄, set_rax, hg₃]; exact hkp₂
    have hax₄ : Y₄.cpu.gpr.rax = BitVec.ofNat 64 n := by simp only [hg₄, set_rax, hlow]
    exact ret_at c hin (by rw [sl2_length]; omega) (d134 prof.feat) hK₄ hA₄ hr₄ hkp₄ hax₄ hR

/-- From `+42`, `rax = p`, `xmm0`–`xmm3` 0, `p` 49 bytes or more before its page's end. -/
theorem pathA (c : Seg prof F Wl L s₀ o) (hin : CodeIn L e' sl2) {X : State} {t : Nat} {g₀ : Gprs} {n : Nat}
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = e'.add 42)
    (hax : X.cpu.gpr.rax = g₀.rdi) (hkp : Kp g₀ X.cpu.gpr) (hx : X4 (xsOf X.cpu.vec.zmm))
    (hq : g₀.rdi.toNat % 4096 ≤ 4047) (hov : g₀.rdi.toNat + n < 2 ^ 64)
    (hnz : ∀ k < n, V (Addr.add g₀.rdi k) ≠ 0) (hz : V (Addr.add g₀.rdi n) = 0)
    (hft : ∀ x : Addr, g₀.rdi.toNat / 4096 ≤ x.toNat / 4096 → x.toNat / 4096 ≤ (g₀.rdi.toNat + n) / 4096 →
      Foot F.data x)
    (hR : Ret prof F Wl L s₀ o gev gP gE V g₀ n) : GoG prof L o gev gP gE X t := by
  obtain ⟨hx0, hx1, hx2, hx3⟩ := hx
  have hp := g₀.rdi.isLt
  -- `movdqu xmm4, [rax]`, `pcmpeqb xmm4, xmm0`, `pmovmskb edx, xmm4`, `test edx, edx`
  refine c.s_blkV hin (b42 prof) hK hA hrip ?_
  refine wpV_v (foot_pg hft (B := X.cpu.gpr.rax) (d := 0) (by rw [hax]; omega) (by rw [hax]; omega)
    (by rw [hax]; omega)) (fun h => nomatch h) (wpV_v0 (wpV_v0 (wpV_reg fun fl hP => wpV_nil ?_)))
  intro Y₁ t₁ hK₁ hA₁ hr₁ hg₁ hf₁ hv₁
  generalize hxd : xsOf X.cpu.vec.zmm = x at hg₁ hP hv₁ hx0 hx1 hx2 hx3
  simp (disch := decide) only [eaB, gv, Src.val, set_rdx, get0, get2, xset_same, xset_ne, hx0, BitVec.setWidth_eq,
    BitVec.setWidth_setWidth_of_le _ (show 32 ≤ 64 by decide), BitVec.and_self] at hg₁ hP
  have hM := m16 (V := V) hax hnz hz
  have hkp₁ : Kp g₀ Y₁.cpu.gpr := by simp only [Kp, hg₁]; exact hkp
  have hax₁ : Y₁.cpu.gpr.rax = g₀.rdi := by simp only [hg₁]; exact hax
  have hx₁ : X4 (xsOf Y₁.cpu.vec.zmm) := by
    rw [hv₁]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp (disch := decide) only [xset_ne, hx0, hx1, hx2, hx3]
  refine c.s_jccV hK₁ hA₁ hin (by rw [sl2_length]; omega) hr₁ (d56 prof.feat) (tgt := 62) rfl
    (by rw [sl2_length]; omega) ?_ ?_
  · -- no 0 in the 16 bytes
    intro htk Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂, hv₂⟩
    rw [hf₁, cond4_mask hP] at htk
    have h16 : 16 ≤ n := hM.1.1 (eq_of_beq htk)
    exact pathA2 c hin hK₂ hA₂ hr₂ (by rw [hg₂]; exact hax₁) (by rw [hg₂]; exact hkp₁) (by rw [hv₂]; exact hx₁) hq
      h16 hov hnz hz hft hR
  · -- a 0: `bsf eax, edx`, `ret`
    intro hfa Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂, _⟩
    rw [hf₁, cond4_mask hP] at hfa
    have hne := ne_of_beq_false hfa
    have hn16 : n < 16 := Classical.byContradiction fun h => hne (hM.1.2 (by omega))
    have hlow : lowestSetBit (rv Y₂ 32 2) = n := by
      simp only [rv, get2, hg₂, hg₁, BitVec.setWidth_setWidth_of_le _ (show 32 ≤ 64 by decide),
        BitVec.setWidth_eq]
      exact hM.2 hn16
    refine c.s_bsf32 hK₂ hA₂ hin (by rw [sl2_length]; omega) hr₂ (d58 prof.feat)
      (by simp only [rv, get2, hg₂, hg₁, BitVec.setWidth_setWidth_of_le _ (show 32 ≤ 64 by decide),
        BitVec.setWidth_eq]; exact hne) ?_
    rintro Y₃ t₃ hK₃ hA₃ ⟨hr₃, hg₃⟩
    have hkp₃ : Kp g₀ Y₃.cpu.gpr := by simp only [Kp, hg₃, set_rax, hg₂]; exact hkp₁
    have hax₃ : Y₃.cpu.gpr.rax = BitVec.ofNat 64 n := by
      simp only [hg₃, set_rax, hlow]
      exact ofNat32_64 (by omega)
    exact ret_at c hin (by rw [sl2_length]; omega) (d61 prof.feat) hK₃ hA₃ hr₃ hkp₃ hax₃ hR

/-! ## The run -/

/-- `__strlen_sse2` from its first byte, called with registers `g₀` (`rdi = p`), returns `n` to `Ret`. -/
theorem run (c : Seg prof F Wl L s₀ o) (hin : CodeIn L e' sl2) {X : State} {t : Nat} {g₀ : Gprs} {n : Nat}
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = e'.add 0) (hkp : Kp g₀ X.cpu.gpr)
    (hov : g₀.rdi.toNat + n < 2 ^ 64)
    (hnz : ∀ k < n, V (Addr.add g₀.rdi k) ≠ 0) (hz : V (Addr.add g₀.rdi n) = 0)
    (hft : ∀ x : Addr, g₀.rdi.toNat / 4096 ≤ x.toNat / 4096 → x.toNat / 4096 ≤ (g₀.rdi.toNat + n) / 4096 →
      Foot F.data x)
    (hR : Ret prof F Wl L s₀ o gev gP gE V g₀ n) : GoG prof L o gev gP gE X t := by
  refine c.s_blkV hin (b0 prof) hK hA hrip ?_
  refine wpV_reg fun _ _ => wpV_v0 (wpV_v0 (wpV_v0 (wpV_v0 (wpV_reg fun _ _ => wpV_reg fun _ _ =>
    wpV_reg fun _ _ => wpV_reg fun fl hP => wpV_nil ?_))))
  intro Y₁ t₁ hK₁ hA₁ hr₁ hg₁ hf₁ hv₁
  simp only [wr, gv, Src.val, set_rax, set_rcx, get1, get7, BitVec.setWidth_eq] at hg₁ hP
  have hkp₁ : Kp g₀ Y₁.cpu.gpr := by simp only [Kp, hg₁]; exact hkp
  have hax₁ : Y₁.cpu.gpr.rax = g₀.rdi := by simp only [hg₁]; exact hkp.1
  have hx₁ : X4 (xsOf Y₁.cpu.vec.zmm) := by
    rw [hv₁]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp (disch := decide) only [xset_same, xset_ne, xor_self']
  refine c.s_jccV hK₁ hA₁ hin (by rw [sl2_length]; omega) hr₁ (d40 prof.feat) (tgt := 144) rfl
    (by rw [sl2_length]; omega) ?_ ?_
  · intro _ Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂, hv₂⟩
    exact pathB c hin hK₂ hA₂ hr₂ (by rw [hg₂]; exact hax₁) (by rw [hg₂]; exact hkp₁) (by rw [hv₂]; exact hx₁) hov
      hnz hz hft hR
  · intro hfa Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂, hv₂⟩
    rw [hf₁, hP, cond_7, subF_cf, subF_zf] at hfa
    have hq := ja_false hfa
    rw [and_4095, hkp.1] at hq
    exact pathA c hin hK₂ hA₂ hr₂ (by rw [hg₂]; exact hax₁) (by rw [hg₂]; exact hkp₁) (by rw [hv₂]; exact hx₁) hq hov
      hnz hz hft hR

end FV7z.Strlen
