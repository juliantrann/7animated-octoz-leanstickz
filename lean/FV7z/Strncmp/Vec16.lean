import FV7z.Strncmp.Mask
import FV7z.Lemmas.Mask
/-!
# 16 bytes of `__strncmp_sse2` (PLAN.md G3, `strncmp`)

- `lohi_lane`: `movlpd x, [a]; movhpd x, [a + 8]` loads the 16 bytes at `a`.
- `cmask_ofBits`: the mask of 16 bytes as bits; `cmask_sub_zero`, `cmask_sub_low`: `sub edx, 0xffff` of it, as
  `rdx`, is 0 just when all 16 bytes are the same and not 0, and otherwise has the first that is not as lowest set
  bit, as `bsf` finds it (`first_set`, `lsb_sw`).
-/
namespace FV7z
open ZellicX86

attribute [-simp] BitVec.getLsbD_eq_getElem

namespace Strncmp

/-- Byte `j` of two halves. -/
theorem lane_app (A B : BitVec 64) {j : Nat} (hj : j < 16) :
    lane 8 (A ++ B) j = if j < 8 then elem 8 B j else elem 8 A (j - 8) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  unfold lane elem
  split
  · simp [BitVec.getLsbD_extractLsb', BitVec.getLsbD_append, hi, show 8 * j + i < 64 by omega]
  · simp [BitVec.getLsbD_extractLsb', BitVec.getLsbD_append, hi, show ¬ 8 * j + i < 64 by omega,
      show 8 * j + i - 64 = 8 * (j - 8) + i by omega]

/-- The low half of two halves. -/
theorem lane64_app (A B : BitVec 64) : lane 64 (A ++ B) 0 = B := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  unfold lane
  simp [BitVec.getLsbD_extractLsb', BitVec.getLsbD_append, hi]

/-- Byte `j` of 8 bytes at `a`. -/
theorem elem8 (V : Addr → Byte) (a : Addr) {j : Nat} (hj : j < 8) :
    elem 8 (ofBytesLE 64 ((byteAddrs a 8).map V)) j = V (a.add j) := by
  rw [elem_ofBytesLE (by simp [byteAddrs]; omega) (by simp [byteAddrs])]
  simp [byteAddrs]

/-- `movlpd x, [a]; movhpd x, [a + 8]`: the 16 bytes at `a`. -/
theorem lohi_lane (V : Addr → Byte) (a : Addr) (x : BitVec 128) {j : Nat} (hj : j < 16) :
    lane 8 (ofBytesLE 64 ((byteAddrs (a + BitVec.ofNat 64 8) 8).map V) ++
      lane 64 (lane 64 x 1 ++ ofBytesLE 64 ((byteAddrs (a + BitVec.ofNat 64 0) 8).map V)) 0) j = V (a.add j) := by
  rw [lane_app _ _ hj, lane64_app]
  split
  · rw [elem8 V _ (by omega), show a + BitVec.ofNat 64 0 = a.add 0 from rfl, addr_add_add, Nat.zero_add]
  · rw [elem8 V _ (by omega), show a + BitVec.ofNat 64 8 = a.add 8 from rfl, addr_add_add,
      show 8 + (j - 8) = j by omega]

/-- The mask of 16 bytes as bits. -/
theorem cmask_ofBits (a b : BitVec 128) :
    cmask a b = ofBits 32 (fun j => decide (j < 16) && decide (lane 8 a j = lane 8 b j ∧ lane 8 a j ≠ 0)) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [getLsbD_cmask, getLsbD_ofBits, decide_eq_true hi, Bool.true_and]

/-- A bit vector not 0 has a first set bit. -/
theorem first_set {w : Nat} {x : BitVec w} (hx : x ≠ 0) :
    ∃ p < w, x.getLsbD p = true ∧ ∀ i < p, x.getLsbD i = false := by
  have h : ∃ j < w, (!x.getLsbD j) = false := by
    refine Classical.byContradiction fun hn => hx ?_
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    rw [Strlen.getLsbD_zero']
    cases hb : x.getLsbD i
    · rfl
    · exact absurd ⟨i, hi, by simp [hb]⟩ hn
  obtain ⟨p, hp, hf, ht⟩ := exists_first (fun j => !x.getLsbD j) h
  exact ⟨p, hp, by simpa using hf, fun i hi => by simpa using ht i hi⟩

/-- `bsf` of a 32-bit value zero-extended. -/
theorem lsb_sw {x : BitVec 32} (hx : x ≠ 0) : lowestSetBit (x.setWidth 64) = lowestSetBit x := by
  obtain ⟨p, hp, h1, h0⟩ := first_set hx
  rw [lowestSetBit_eq hp h1 h0]
  apply lowestSetBit_eq (by omega)
  · simp [BitVec.getLsbD_setWidth, h1, show p < 64 by omega]
  · intro i hi
    simp [BitVec.getLsbD_setWidth, h0 i hi]

theorem sw64_ne_zero {x : BitVec 32} (hx : x ≠ 0) : x.setWidth 64 ≠ 0 := fun h => hx (by
  apply BitVec.eq_of_toNat_eq
  have e := congrArg BitVec.toNat h
  rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_trans x.isLt (by decide))] at e
  exact e)

/-- `sub edx, 0xffff` of the mask: 0 when all 16 bytes are the same and not 0. -/
theorem cmask_sub_zero (a b : BitVec 128) :
    cmask a b - BitVec.ofNat 32 65535 = 0 ↔ ∀ j < 16, lane 8 a j = lane 8 b j ∧ lane 8 a j ≠ 0 := by
  rw [cmask_ofBits, show BitVec.ofNat 32 65535 = BitVec.ofNat 32 (2 ^ 16 - 1) from rfl,
    mask_sub_eq_zero (by decide)]
  exact ⟨fun h j hj => of_decide_eq_true (h j hj), fun h j hj => decide_eq_true (h j hj)⟩

/-- `sub edx, 0xffff` of the mask, as `rdx`, a byte not the same or 0 at `p` and none before: not 0, with `p` the
lowest set bit. -/
theorem cmask_sub_low (a b : BitVec 128) {p : Nat} (hp : p < 16)
    (hf : ¬ (lane 8 a p = lane 8 b p ∧ lane 8 a p ≠ 0))
    (ht : ∀ i < p, lane 8 a i = lane 8 b i ∧ lane 8 a i ≠ 0) :
    (cmask a b - BitVec.ofNat 32 65535).setWidth 64 ≠ 0 ∧
      lowestSetBit ((cmask a b - BitVec.ofNat 32 65535).setWidth 64) = p := by
  have hnz : cmask a b - BitVec.ofNat 32 65535 ≠ 0 := fun h => hf ((cmask_sub_zero a b).1 h p hp)
  refine ⟨sw64_ne_zero hnz, ?_⟩
  rw [lsb_sw hnz, cmask_ofBits, show BitVec.ofNat 32 65535 = BitVec.ofNat 32 (2 ^ 16 - 1) from rfl]
  exact mask_sub_lowest (by decide) _ hp (decide_eq_false hf) (fun i hi => decide_eq_true (ht i hi))

end Strncmp
end FV7z
