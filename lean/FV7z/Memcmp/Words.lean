import FV7z.Memcmp.Order
import FV7z.Lemmas.Ins
/-!
# Bytes as words (PLAN.md G2.1)

The short cases of `__memcmp_avx2_movbe` load up to eight bytes of each string into a register, most significant
first (`MOVBE`, or `MOVZX` then `SHL` and `BSWAP`), and compare the registers as numbers. Here: the value of a load
(`toNat_ofBytesLE`, the little-endian value `leV`, which is the big-endian value `beV` of the bytes reversed), what
`BSWAP`, `SHL`, `OR` and a byte move do to loaded bytes, and the sign of a 32-bit difference (`compare_sub`).
-/
namespace FV7z.Order
open ZellicX86 Memcmp

attribute [-simp] BitVec.getLsbD_eq_getElem

/-- The value of bytes read as a little-endian number. -/
def leV : List Byte → Nat
  | [] => 0
  | b :: bs => b.toNat + 256 * leV bs

theorem leV_lt : ∀ bs : List Byte, leV bs < 256 ^ bs.length
  | [] => by simp [leV]
  | b :: bs => by
    have := leV_lt bs; have hb := b.isLt
    simp only [leV, List.length_cons, Nat.pow_succ]
    omega

theorem beV_snoc : ∀ (xs : List Byte) (x : Byte), beV (xs ++ [x]) = beV xs * 256 + x.toNat
  | [], x => by simp [beV]
  | y :: ys, x => by
    simp only [List.cons_append, beV, List.length_append, List.length_cons, List.length_nil, beV_snoc ys x,
      Nat.pow_succ, Nat.zero_add]
    rw [Nat.add_mul, Nat.mul_assoc]
    omega

theorem leV_eq_beV : ∀ xs : List Byte, leV xs = beV xs.reverse
  | [] => rfl
  | b :: bs => by
    rw [List.reverse_cons, beV_snoc, ← leV_eq_beV bs, leV]
    omega

theorem leV_append : ∀ (l l' : List Byte), leV (l ++ l') = leV l + 256 ^ l.length * leV l'
  | [], l' => by simp [leV]
  | b :: l, l' => by
    simp only [List.cons_append, leV, leV_append l l', List.length_cons, Nat.pow_succ]
    rw [Nat.mul_add, Nat.mul_comm (256 ^ l.length) 256, Nat.mul_assoc]
    omega

/-- The value of a load of bytes into a register wide enough. -/
theorem toNat_ofBytesLE {w : Nat} : ∀ bs : List Byte, 8 * bs.length ≤ w → (ofBytesLE w bs).toNat = leV bs
  | [], _ => by simp [ofBytesLE, leV]
  | b :: bs, h => by
    simp only [List.length_cons] at h
    have ih := toNat_ofBytesLE (w := w) bs (by omega)
    have hdis : b.setWidth w &&& (ofBytesLE w bs <<< 8) = 0#w := by
      apply BitVec.eq_of_getLsbD_eq
      intro i _
      simp only [BitVec.getLsbD_and, BitVec.getLsbD_setWidth, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_zero]
      by_cases h8 : i < 8
      · simp [h8]
      · simp [BitVec.getLsbD_of_ge b i (by omega)]
    rw [ofBytesLE, ← BitVec.add_eq_or_of_and_eq_zero _ _ hdis, BitVec.toNat_add, BitVec.toNat_setWidth,
      BitVec.toNat_shiftLeft, ih, leV]
    have hb := b.isLt
    have hl := leV_lt bs
    have hp : 256 ^ bs.length * 256 ≤ 2 ^ w := by
      rw [show (256 : Nat) = 2 ^ 8 from rfl, ← Nat.pow_mul, ← Nat.pow_add]
      exact Nat.pow_le_pow_right (by decide) (by omega)
    have h256 : 256 ≤ 2 ^ w := by
      have : 0 < 256 ^ bs.length := Nat.pow_pos (by decide)
      have := Nat.mul_le_mul_right 256 this
      omega
    rw [Nat.shiftLeft_eq, show 2 ^ 8 = 256 from rfl, Nat.mod_eq_of_lt (by omega : b.toNat < 2 ^ w)]
    rw [Nat.mod_eq_of_lt (a := leV bs * 256) (by have := Nat.mul_lt_mul_of_pos_right hl (by decide : 0 < 256); omega)]
    rw [Nat.mod_eq_of_lt (by have := Nat.mul_le_mul_right 256 (Nat.succ_le_of_lt hl); rw [Nat.succ_mul] at this; omega)]
    omega

theorem ofBytesLE_one (c : Byte) : ofBytesLE 8 [c] = c := by
  simp [ofBytesLE]

theorem ofBytesLE_cons_zero {w : Nat} (bs : List Byte) : ofBytesLE w (0 :: bs) = ofBytesLE w bs <<< 8 := by
  simp [ofBytesLE]

theorem ofBytesLE_snoc_zero {w : Nat} (bs : List Byte) : ofBytesLE w (bs ++ [0]) = ofBytesLE w bs := by
  apply BitVec.eq_of_getLsbD_eq
  intro i _
  rw [getLsbD_ofBytesLE, getLsbD_ofBytesLE]
  simp only [List.length_append, List.length_cons, List.length_nil, Nat.zero_add]
  by_cases h : i / 8 < bs.length
  · simp [h, show i / 8 < bs.length + 1 by omega, List.getD_eq_getElem?_getD, List.getElem?_append_left h]
  · by_cases h' : i / 8 = bs.length
    · simp [h, h', List.getD_eq_getElem?_getD]
    · simp [h, show ¬ i / 8 < bs.length + 1 by omega]

theorem setWidth_ofBytesLE {w w' : Nat} {bs : List Byte} (h : 8 * bs.length ≤ w) :
    (ofBytesLE w bs).setWidth w' = ofBytesLE w' bs := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_setWidth, getLsbD_ofBytesLE, getLsbD_ofBytesLE]
  by_cases hb : i / 8 < bs.length
  · simp [hi, hb, show i < w by omega]
  · simp [hb]

theorem toBytesLE_ofBytesLE {w n : Nat} {bs : List Byte} (hl : bs.length = n) (hw : 8 * n ≤ w) :
    toBytesLE (ofBytesLE w bs) n = bs := by
  apply List.ext_getElem (by simp [toBytesLE, hl])
  intro j h₁ h₂
  simp only [toBytesLE, List.getElem_map, List.getElem_range]
  apply BitVec.eq_of_getLsbD_eq
  intro t ht
  rw [BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, getLsbD_ofBytesLE]
  have h1 : (8 * j + t) / 8 = j := by omega
  have h2 : (8 * j + t) % 8 = t := by omega
  simp [ht, h1, h2, h₂, show 8 * j + t < w by omega, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h₂]

/-- `BSWAP` of four loaded bytes: the bytes reversed. -/
theorem bswap_ofBytesLE {bs : List Byte} (hl : bs.length = 4) : bswap (ofBytesLE 32 bs) = ofBytesLE 32 bs.reverse := by
  unfold bswap
  rw [toBytesLE_ofBytesLE hl (by omega)]

/-- A move into the low byte of a register (`MOV AL, …`) of loaded bytes: the first byte replaced. -/
theorem setLow8 (z c : Byte) (l : List Byte) :
    (ofBytesLE 64 (z :: l) &&& ~~~(BitVec.ofNat 64 ((2 ^ 8 - 1) * 2 ^ 0))) ||| ((ofBytesLE 8 [c]).setWidth 64 <<< 0) =
      ofBytesLE 64 (c :: l) := by
  rw [ofBytesLE_one]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [ofBytesLE, BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_not, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ofNat, Nat.pow_zero, Nat.mul_one, Nat.testBit_two_pow_sub_one, hi,
    decide_true, Bool.true_and, Nat.sub_zero, Nat.not_lt_zero, decide_false, Bool.not_false]
  by_cases h8 : i < 8
  · simp [h8]
  · simp [h8, BitVec.getLsbD_of_ge z i (by omega), BitVec.getLsbD_of_ge c i (by omega)]

/-- Two loads of four bytes, the first shifted to the high half (`SHL r64, 32; OR`). -/
theorem toNat_hilo {L₁ L₂ : List Byte} (h₁ : L₁.length = 4) (h₂ : L₂.length = 4) :
    (((ofBytesLE 32 L₁).setWidth 64 <<< 32) ||| (ofBytesLE 32 L₂).setWidth 64).toNat = leV (L₂ ++ L₁) := by
  rw [setWidth_ofBytesLE (by omega), setWidth_ofBytesLE (by omega)]
  have hdis : ofBytesLE 64 L₂ &&& (ofBytesLE 64 L₁ <<< 32) = 0#64 := by
    apply BitVec.eq_of_getLsbD_eq
    intro i _
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_shiftLeft, getLsbD_ofBytesLE, h₂, BitVec.getLsbD_zero]
    by_cases h : i < 32
    · simp [h]
    · simp [show ¬ i / 8 < 4 by omega]
  rw [BitVec.or_comm, ← BitVec.add_eq_or_of_and_eq_zero _ _ hdis, BitVec.toNat_add, BitVec.toNat_shiftLeft,
    toNat_ofBytesLE _ (by omega), toNat_ofBytesLE _ (by omega), leV_append, h₂, Nat.shiftLeft_eq]
  have := leV_lt L₁; have := leV_lt L₂
  rw [h₁] at *; rw [h₂] at *
  simp only [show (256 : Nat) ^ 4 = 2 ^ 32 from rfl] at *
  rw [Nat.mod_eq_of_lt (a := leV L₁ * 2 ^ 32) (by omega), Nat.mod_eq_of_lt (by omega)]
  omega

/-- The sign of a 32-bit difference of numbers below `2 ^ 31`. -/
theorem compare_sub {x y : BitVec 32} (hx : x.toNat < 2 ^ 31) (hy : y.toNat < 2 ^ 31) :
    compare (x - y).toInt 0 = compare x.toNat y.toNat := by
  simp only [BitVec.toInt_eq_toNat_cond, BitVec.toNat_sub]
  rcases Nat.lt_trichotomy x.toNat y.toNat with h | h | h
  · rw [Nat.compare_eq_lt.2 h, Int.compare_eq_lt.2]
    split <;> omega
  · rw [Nat.compare_eq_eq.2 h, Int.compare_eq_eq.2]
    split <;> omega
  · rw [Nat.compare_eq_gt.2 h, Int.compare_eq_gt.2]
    split <;> omega

end FV7z.Order
