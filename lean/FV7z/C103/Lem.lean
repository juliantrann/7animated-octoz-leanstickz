import FV7z.C103.Inv
/-!
# `init_cacheinfo`: bit facts for the cut points' conditions (PLAN.md M, ctor 103)

Zero-extensions, the subleaf counters' increments, `1 << k` not 0, the cache type's bits after `cpuid(4)`, and the
leaf-`0xB` loop's flags in `r8` from the two flags before it.
-/
namespace FV7z.C103
open ZellicX86 FV7z

theorem xs (x : BitVec 32) : (x ^^^ x).toNat = 0 := by simp

/-- A subleaf counter's increment, below 65. -/
theorem inc64 (x : BitVec 64) (h : (x.setWidth 32).toNat ≤ 64) :
    ((x + 1#64).setWidth 32).toNat = (x.setWidth 32).toNat + 1 := by bv_omega

theorem sw_ne (x : BitVec 32) (h : x ≠ 0#32) : x.setWidth 64 ≠ 0#64 := by bv_omega

theorem sw_msb (x : BitVec 32) : (x.setWidth 64).msb = false := by
  have := x.isLt
  rw [BitVec.msb_eq_decide]
  simp only [BitVec.toNat_setWidth, decide_eq_false_iff_not]
  omega

theorem sw_lt (x : BitVec 32) : (x.setWidth 64).toNat < 2 ^ 32 := by
  have := x.isLt
  simp only [BitVec.toNat_setWidth]
  omega

/-- `1 << k` (32 bits) is not 0. -/
theorem sh1 (k : Nat) : (1#32 <<< (k % 32)) ≠ 0#32 := by
  have h : k % 32 < 32 := Nat.mod_lt _ (by decide)
  generalize k % 32 = m at h ⊢
  revert m
  decide

/-- The cache type `EAX[4:0]` in `al`. -/
theorem and31 (x : BitVec 32) (h : x &&& 31#32 = 0#32) : (x.setWidth 64).setWidth 8 &&& 31#8 = 0#8 := by
  have h' := congrArg BitVec.toNat h
  have e : ∀ y : Nat, y &&& 31 = y % 32 := fun y => Nat.and_two_pow_sub_one_eq_mod y 5
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_and, BitVec.toNat_setWidth, BitVec.toNat_ofNat, e] at h' ⊢
  omega

/-- The leaf-`0xB` loop's flags `r8 = 2 * eax | edx` from the two flags before it. -/
theorem bits06 {a d r15 r9 rdi : BitVec 64} (ha : a = 0#64 ∨ a = 1#64) (hd : d = 0#64 ∨ d = 1#64)
    (hd1 : d = 1#64 → r15 = 3#64 ∧ r9.setWidth 32 ≠ 0#32)
    (ha1 : a = 1#64 → (r15 = 3#64 → rdi.setWidth 32 ≠ 0#32) ∧ (r15 = 2#64 → r9.setWidth 32 ≠ 0#32)) :
    (((a + a).setWidth 32 ||| d.setWidth 32).setWidth 64 = 0#64 ∨
      ((a + a).setWidth 32 ||| d.setWidth 32).setWidth 64 = 1#64 ∨
      ((a + a).setWidth 32 ||| d.setWidth 32).setWidth 64 = 2#64 ∨
      ((a + a).setWidth 32 ||| d.setWidth 32).setWidth 64 = 3#64) ∧
    (((a + a).setWidth 32 ||| d.setWidth 32).setWidth 64 = 1#64 ∨
      ((a + a).setWidth 32 ||| d.setWidth 32).setWidth 64 = 3#64 → r15 = 3#64 ∧ r9.setWidth 32 ≠ 0#32) ∧
    (((a + a).setWidth 32 ||| d.setWidth 32).setWidth 64 = 2#64 ∨
      ((a + a).setWidth 32 ||| d.setWidth 32).setWidth 64 = 3#64 →
      (r15 = 3#64 → rdi.setWidth 32 ≠ 0#32) ∧ (r15 = 2#64 → r9.setWidth 32 ≠ 0#32)) := by
  rcases ha with rfl | rfl <;> rcases hd with rfl | rfl <;> refine ⟨by decide, fun h => ?_, fun h => ?_⟩ <;>
    first | exact hd1 rfl | exact ha1 rfl | exact absurd h (by decide)

end FV7z.C103
