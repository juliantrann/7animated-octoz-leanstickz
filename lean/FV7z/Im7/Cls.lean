import FV7z.Im5.Cls
/-!
# `malloc`: the request class `4105 ≤ n ≤ 2 ^ 32` (PLAN.md G3, `malloc`)

- `ClsG n nb`: `nb` the chunk size of a request `4105 ≤ n ≤ 2 ^ 32` (`Im7.secG` its second call, `Im5.SecA`).
- `ClsW n nb`: `Im5.ClsN` or `ClsG`, the class `Mnx.mal_tail` takes; `ClsW.bnd`.
- `ClsG.tc`: the tcache index `(nb - 17) >> 4` not below `mp_.tcache_bins` (64).
- `sz_bits`: the size word `nb | 1` of a chunk (`16 ∣ nb`): its bits 2 (`IS_MMAPPED`), 4 (`NON_MAIN_ARENA`) and 8 clear.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn FV7z.Start
open FV7z.Im2 (and_m16)
namespace FV7z.Im7

/-- `nb` the chunk size of a request `4105 ≤ n ≤ 2 ^ 32`. -/
def ClsG (n nb : Addr) : Prop := 4105 ≤ n.toNat ∧ n.toNat ≤ 2 ^ 32 ∧ n + 23#64 &&& 18446744073709551600#64 = nb

/-- The class of `Mnx.mal_tail`: `Im5.ClsN` (`n ≤ 4104` or 72704) or `ClsG`. -/
def ClsW (n nb : Addr) : Prop := Im5.ClsN n nb ∨ ClsG n nb

theorem ClsG.nb {n nb : Addr} (h : ClsG n nb) : nb.toNat = (n.toNat + 23) / 16 * 16 := by
  obtain ⟨-, h2, rfl⟩ := h
  have e : (n + 23#64).toNat = n.toNat + 23 := by rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  rw [and_m16, e]

theorem ClsG.bnd {n nb : Addr} (h : ClsG n nb) : 4128 ≤ nb.toNat ∧ nb.toNat ≤ 2 ^ 33 ∧ nb.toNat % 16 = 0 := by
  have := h.nb
  have := h.1
  have := h.2.1
  omega

theorem ClsW.bnd {n nb : Addr} (h : ClsW n nb) : 32 ≤ nb.toNat ∧ nb.toNat ≤ 2 ^ 33 := by
  rcases h with h | h
  · have := h.bnd
    omega
  · have := h.bnd
    omega

theorem ClsG.tc {n nb : Addr} (h : ClsG n nb) :
    decide (((nb + 18446744073709551599#64) >>> 4).toNat < 64) = false := by
  have hb := h.bnd
  have e : (nb + 18446744073709551599#64).toNat = nb.toNat - 17 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have e4 : ((nb + 18446744073709551599#64) >>> 4).toNat = (nb + 18446744073709551599#64).toNat / 16 := by
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]; rfl
  rw [e4, e]
  exact decide_eq_false (by omega)

/-- The low byte of `nb | 1` for `16 ∣ nb`. -/
theorem sz_lo {nb : Addr} (h : nb.toNat % 16 = 0) :
    BitVec.setWidth 8 (nb ||| 1#64) = BitVec.ofNat 8 (16 * (nb.toNat % 256 / 16)) ||| 1#8 := by
  rw [BitVec.setWidth_or, show BitVec.setWidth 8 (1#64) = 1#8 by decide]
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.reducePow]
  omega

/-- The size word `nb | 1` (`16 ∣ nb`): the bits 2, 4 and 8 of its low byte clear. -/
theorem sz_bits {nb : Addr} (h : nb.toNat % 16 = 0) :
    BitVec.setWidth 8 (nb ||| 1#64) &&& 2#8 = 0 ∧ BitVec.setWidth 8 (nb ||| 1#64) &&& 4#8 = 0 ∧
      BitVec.setWidth 8 (nb ||| 1#64) &&& 8#8 = 0 := by
  have key : ∀ r < 16, (BitVec.ofNat 8 (16 * r) ||| 1#8) &&& 2#8 = 0 ∧
      (BitVec.ofNat 8 (16 * r) ||| 1#8) &&& 4#8 = 0 ∧ (BitVec.ofNat 8 (16 * r) ||| 1#8) &&& 8#8 = 0 := by
    decide
  rw [sz_lo h]
  exact key _ (by omega)

end FV7z.Im7
