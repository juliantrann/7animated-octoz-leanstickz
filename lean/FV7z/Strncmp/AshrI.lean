import FV7z.Strncmp.Ashr0
import FV7z.Strncmp.AshrT
import FV7z.Lemmas.Signed
/-!
# The shifted loops of `__strncmp_sse2`: numbers, addresses and masks (PLAN.md G3, `strncmp`)

The loop shifting by `k` keeps in `r10` where the next 16 bytes of `rdi`'s string are in their page, less 4096, plus
`k` (`lea r10, [rdi + k]; and r10, 4095; sub r10, 4096`, `r10_init`): `add r10, 16; jg` is taken just when the next
16 bytes begin a page (`jg_r10`, `r10_add`), and then `sub r10, 4096` starts the count again (`r10_cross`). Before
it reads them it checks that the bytes it still has of `rdi`'s string, from byte `k` of `xmm3`, have no 0
(`pcmpeqb xmm0, xmm3; pmovmskb edx, xmm0; test edx, 0x10000 - 2 ^ k`, `test_hi`). At the end, from `352`, the bytes it
has are lined up with `rsi`'s (`psrldq xmm3, k`) and compared at `6144` (`pcmpeqb xmm1, xmm3; psubb xmm1, xmm0;
pmovmskb edx, xmm1; not edx`): the mask's bits below `16 - k` are where they are not the same or 0 (`tail_lo`), and bit
16 is set (`tail_low_stop`, `tail_low_none`).

- `addr_shift`: the same address two ways.
-/
namespace FV7z.Strncmp
open ZellicX86 Decode FV7z.Leaf FV7z.Fn FV7z.Strlen

attribute [-simp] BitVec.getLsbD_eq_getElem

/-! ## Addresses -/

/-- `r + A` is `z + B`: so is `r + A'` `z + B'` when `A' + B = A + B'`. -/
theorem addr_shift {r z : Addr} {A B A' B' : Nat} (h : Addr.add r A = z.add B) (he : A' + B = A + B') :
    Addr.add r A' = z.add B' := by
  have e1 : Addr.add r A' + BitVec.ofNat 64 B = Addr.add r A + BitVec.ofNat 64 B' := by
    simp only [Addr.add, BitVec.add_assoc, BitVec.ofNat_add_ofNat, he]
  rw [h] at e1
  have e2 : Addr.add r A' + BitVec.ofNat 64 B = z.add B' + BitVec.ofNat 64 B := by
    rw [e1]
    simp only [Addr.add, BitVec.add_assoc, BitVec.ofNat_add_ofNat, Nat.add_comm B B']
  have e3 := congrArg (fun w : Addr => w - BitVec.ofNat 64 B) e2
  simp only [BitVec.add_sub_cancel] at e3
  exact e3

/-! ## The page count in `r10` -/

/-- `lea r10, [rdi + k]; and r10, 4095; sub r10, 4096`, `rdi` aligned, `k < 16`. -/
theorem r10_init {r : Addr} {k : Nat} (hr : r.toNat % 16 = 0) (hk : k < 16) :
    ((r + BitVec.ofNat 64 k) &&& BitVec.ofNat 64 4095) - BitVec.ofNat 64 4096 =
      BitVec.ofNat 64 (2 ^ 64 - 4096 + r.toNat % 4096 + k) := by
  have hr' := r.isLt
  have e : ((r + BitVec.ofNat 64 k) &&& BitVec.ofNat 64 4095).toNat = r.toNat % 4096 + k := by
    rw [BitVec.toNat_and, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      show (4095 % 2 ^ 64 : Nat) = 2 ^ 12 - 1 by decide, Nat.and_two_pow_sub_one_eq_mod]
    omega
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub, e, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  omega

/-- `add r10, 16; jg`: taken just when the 16 bytes after those at `w` in their page begin the next. -/
theorem jg_r10 {w k : Nat} (f : Rflags) (hw : w < 4096) (hw16 : w % 16 = 0) (hk1 : 1 ≤ k) (hk : k < 16) :
    (addF f (BitVec.ofNat 64 (2 ^ 64 - 4096 + w + k)) (BitVec.ofNat 64 16)).cond 15 = decide (w = 4080) := by
  have e : BitVec.ofNat 64 (2 ^ 64 - 4096 + w + k) + BitVec.ofNat 64 16 =
      BitVec.ofNat 64 (2 ^ 64 - 4096 + w + k + 16) := BitVec.ofNat_add_ofNat _ _
  have hsf : (addF f (BitVec.ofNat 64 (2 ^ 64 - 4096 + w + k)) (BitVec.ofNat 64 16)).sf =
      (BitVec.ofNat 64 (2 ^ 64 - 4096 + w + k) + BitVec.ofNat 64 16).msb := by
    simp [addF, Rflags.arith]
  have hof : (addF f (BitVec.ofNat 64 (2 ^ 64 - 4096 + w + k)) (BitVec.ofNat 64 16)).of =
      overflowAdd (BitVec.ofNat 64 (2 ^ 64 - 4096 + w + k)) (BitVec.ofNat 64 16)
        (BitVec.ofNat 64 (2 ^ 64 - 4096 + w + k) + BitVec.ofNat 64 16) := by
    simp [addF, Rflags.arith]
  have hx : (BitVec.ofNat 64 (2 ^ 64 - 4096 + w + k)).msb = true := by
    rw [BitVec.msb_eq_decide, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    exact decide_eq_true (by omega)
  have h16 : (BitVec.ofNat 64 16).msb = false := by decide
  rw [cond_15, addF_zf, hsf, hof, overflowAdd, e, hx, h16]
  by_cases h : w = 4080
  · subst h
    have e2 : BitVec.ofNat 64 (2 ^ 64 - 4096 + 4080 + k + 16) = BitVec.ofNat 64 k := by
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_ofNat]
      omega
    have hk' : (BitVec.ofNat 64 k).msb = false := by
      rw [BitVec.msb_eq_decide, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      exact decide_eq_false (by omega)
    rw [e2, hk', ofNat_beq_zero (by omega), decide_eq_false (by omega)]
    rfl
  · have hr : (BitVec.ofNat 64 (2 ^ 64 - 4096 + w + k + 16)).msb = true := by
      rw [BitVec.msb_eq_decide, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      exact decide_eq_true (by omega)
    rw [hr, ofNat_beq_zero (by omega), decide_eq_false (by omega), decide_eq_false h]
    rfl

/-- `add r10, 16`, not taken: the next 16 bytes in the same page. -/
theorem r10_add {w k : Nat} :
    BitVec.ofNat 64 (2 ^ 64 - 4096 + w + k) + BitVec.ofNat 64 16 = BitVec.ofNat 64 (2 ^ 64 - 4096 + (w + 16) + k) := by
  rw [BitVec.ofNat_add_ofNat]
  congr 1
  omega

/-- `add r10, 16; jg` taken, then `sub r10, 4096`: the next 16 bytes at 0 in their page. -/
theorem r10_cross {k : Nat} :
    BitVec.ofNat 64 (2 ^ 64 - 4096 + 4080 + k) + BitVec.ofNat 64 16 - BitVec.ofNat 64 4096 =
      BitVec.ofNat 64 (2 ^ 64 - 4096 + 0 + k) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

/-- The place in its page of the 16 bytes after aligned `z`: 16 more, or 0 when `z`'s are the page's last. -/
theorem pg_next {z : Addr} (hz : z.toNat % 16 = 0) :
    (z.add 16).toNat % 4096 = if z.toNat % 4096 = 4080 then 0 else z.toNat % 4096 + 16 := by
  have := z.isLt
  simp only [Addr.add, BitVec.toNat_add, BitVec.toNat_ofNat]
  split <;> omega

/-- 16 bytes after aligned `z`, not the last of their page: the same page. -/
theorem pg_same {z : Addr} (hz : z.toNat % 16 = 0) (h : z.toNat % 4096 ≠ 4080) :
    (z.add 16).toNat / 4096 = z.toNat / 4096 := by
  have := z.isLt
  simp only [Addr.add, BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

/-! ## Masks -/

theorem msb_peqb0 (X : BitVec 128) {i : Nat} (hi : i < 16) :
    (lane 8 (peqb 0 X) i).msb = decide (lane 8 X i = 0) := by
  simp only [peqb, lane_ofBytes _ hi, Strlen.lane_zero]
  split
  · rename_i h
    rw [← h]
    decide
  · rename_i h
    rw [decide_eq_false (fun e => h e.symm)]
    decide

theorem getLsbD_hi {k i : Nat} (hk : k ≤ 16) :
    (BitVec.ofNat 32 (65536 - 2 ^ k)).getLsbD i = (decide (k ≤ i) && decide (i < 16)) := by
  have e : 65536 - 2 ^ k = (2 ^ (16 - k) - 1) <<< k := by
    rw [Nat.shiftLeft_eq, Nat.sub_mul, ← Nat.pow_add, Nat.sub_add_cancel hk, Nat.one_mul]
  rw [BitVec.getLsbD_ofNat, e, Nat.testBit_shiftLeft, Nat.testBit_two_pow_sub_one]
  by_cases h1 : k ≤ i <;> by_cases h2 : i < 16
  · rw [decide_eq_true (by omega : i < 32), decide_eq_true (by omega : i ≥ k),
      decide_eq_true (by omega : i - k < 16 - k), decide_eq_true h2]
    rfl
  · rw [decide_eq_false (by omega : ¬ i - k < 16 - k), decide_eq_false h2]
    cases decide (i < 32) <;> cases decide (i ≥ k) <;> rfl
  · rw [decide_eq_false (by omega : ¬ i ≥ k)]
    cases decide (i < 32) <;> rfl
  · rw [decide_eq_false (by omega : ¬ i ≥ k)]
    cases decide (i < 32) <;> rfl

/-- `pcmpeqb xmm0, xmm3; pmovmskb edx, xmm0; test edx, 0x10000 - 2 ^ k` (`xmm0` 0): 0 just when the bytes of `xmm3`
from `k` on are not 0. -/
theorem test_hi (X : BitVec 128) {k : Nat} (hk : k ≤ 16) :
    pmsk (peqb 0 X) &&& BitVec.ofNat 32 (65536 - 2 ^ k) = 0 ↔ ∀ i, k ≤ i → i < 16 → lane 8 X i ≠ 0 := by
  constructor
  · intro h i hki hi h0
    have e := congrArg (fun z : BitVec 32 => z.getLsbD i) h
    simp only [BitVec.getLsbD_and, getLsbD_pmsk, getLsbD_hi hk, Strlen.getLsbD_zero'] at e
    rw [msb_peqb0 X hi, decide_eq_true h0, decide_eq_true hi, decide_eq_true hki] at e
    exact absurd e (by decide)
  · intro h
    apply BitVec.eq_of_getLsbD_eq
    intro i _
    rw [BitVec.getLsbD_and, getLsbD_pmsk, getLsbD_hi hk, Strlen.getLsbD_zero']
    by_cases hi : i < 16
    · by_cases hki : k ≤ i
      · rw [msb_peqb0 X hi, decide_eq_false (h i hki hi)]
        cases decide (i < 16) <;> cases decide (k ≤ i) <;> rfl
      · rw [decide_eq_false hki]
        cases decide (i < 16) <;> cases (lane 8 (peqb 0 X) i).msb <;> rfl
    · rw [decide_eq_false hi]
      rfl

/-- The tail's bytes: `rsi`'s 16 against `xmm3` from byte `k` on, the 0s of `xmm3` from `k` on in `xmm0`. -/
theorem msb_tail (Y X : BitVec 128) {k i : Nat} (hi : i < 16) (hik : i + k < 16) :
    (lane 8 (psb (peqb Y (X >>> (8 * k))) ((peqb 0 X) >>> (8 * k))) i).msb =
      decide (lane 8 Y i = lane 8 X (i + k) ∧ lane 8 X (i + k) ≠ 0) := by
  simp only [psb, peqb, lane_ofBytes _ hi, lane_shr _ k hi, hik, ↓reduceIte, lane_ofBytes _ hik, Strlen.lane_zero]
  generalize lane 8 Y i = y
  generalize lane 8 X (i + k) = x
  by_cases h1 : y = x <;> by_cases h2 : (0 : BitVec 8) = x
  · subst h1 h2
    decide
  · subst h1
    have h3 : y ≠ 0 := fun h => h2 h.symm
    simp only [h2, eq_self_iff_true, ↓reduceIte, h3, ne_eq, not_false_eq_true, and_self, decide_true]
    all_goals decide
  · subst h2
    simp only [h1, ↓reduceIte, false_and, decide_false]
    all_goals decide
  · simp only [h1, h2, ↓reduceIte, false_and, decide_false]
    all_goals decide

/-- The tail's mask after `not edx`. -/
abbrev tmask (Y X : BitVec 128) (k : Nat) : BitVec 32 :=
  ~~~ pmsk (psb (peqb Y (X >>> (8 * k))) ((peqb 0 X) >>> (8 * k)))

theorem tail_lo (Y X : BitVec 128) {k i : Nat} (hik : i + k < 16) :
    (tmask Y X k).getLsbD i = !decide (lane 8 Y i = lane 8 X (i + k) ∧ lane 8 X (i + k) ≠ 0) := by
  rw [tmask, BitVec.getLsbD_not, getLsbD_pmsk, msb_tail Y X (by omega) hik, decide_eq_true (by omega : i < 32),
    decide_eq_true (by omega : i < 16)]
  rfl

theorem tail_16 (Y X : BitVec 128) (k : Nat) : (tmask Y X k).getLsbD 16 = true := by
  rw [tmask, BitVec.getLsbD_not, getLsbD_pmsk]
  rfl

/-- A stop at `p` below `16 - k`, none before: the tail's mask, as `rdx`, has `p` as lowest set bit. -/
theorem tail_low_stop (Y X : BitVec 128) {k p : Nat} (hp : p + k < 16)
    (hf : ¬ (lane 8 Y p = lane 8 X (p + k) ∧ lane 8 X (p + k) ≠ 0))
    (ht : ∀ i < p, lane 8 Y i = lane 8 X (i + k) ∧ lane 8 X (i + k) ≠ 0) :
    (tmask Y X k).setWidth 64 ≠ 0 ∧ lowestSetBit ((tmask Y X k).setWidth 64) = p := by
  have h1 : (tmask Y X k).getLsbD p = true := by
    rw [tail_lo Y X hp, decide_eq_false hf]
    rfl
  have hnz : tmask Y X k ≠ 0 := fun h => by
    rw [h, Strlen.getLsbD_zero'] at h1
    exact absurd h1 (by decide)
  refine ⟨sw64_ne_zero hnz, ?_⟩
  rw [lsb_sw hnz]
  refine lowestSetBit_eq (by omega) h1 fun i hi => ?_
  rw [tail_lo Y X (by omega), decide_eq_true (ht i hi)]
  rfl

/-- No stop below `16 - k`: the tail's mask, as `rdx`, is not 0, with lowest set bit from `16 - k` on, below 64. -/
theorem tail_low_none (Y X : BitVec 128) {k : Nat}
    (ht : ∀ i, i + k < 16 → lane 8 Y i = lane 8 X (i + k) ∧ lane 8 X (i + k) ≠ 0) :
    (tmask Y X k).setWidth 64 ≠ 0 ∧ 16 - k ≤ lowestSetBit ((tmask Y X k).setWidth 64) ∧
      lowestSetBit ((tmask Y X k).setWidth 64) < 64 := by
  have hnz : tmask Y X k ≠ 0 := fun h => by
    have h1 := tail_16 Y X k
    rw [h, Strlen.getLsbD_zero'] at h1
    exact absurd h1 (by decide)
  obtain ⟨p, hp, h1, h0⟩ := first_set hnz
  refine ⟨sw64_ne_zero hnz, ?_⟩
  rw [lsb_sw hnz, lowestSetBit_eq hp h1 h0]
  refine ⟨Nat.le_of_not_lt fun hlt => ?_, by omega⟩
  rw [tail_lo Y X (by omega), decide_eq_true (ht p (by omega))] at h1
  exact absurd h1 (by decide)

end FV7z.Strncmp
