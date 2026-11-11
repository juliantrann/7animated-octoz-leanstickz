import FV7z.Lemmas.Wp
/-!
# `jg` after `cmp` (PLAN.md G3, startup)

- `subF_g32`: the condition of `jg` after a 32-bit `cmp x, y` is `y < x` as signed numbers (`__libc_start_main`'s
  check of the kernel's version).
-/
namespace FV7z
open ZellicX86 Decode FV7z.Leaf

theorem cond_15 (f : Rflags) : f.cond 15 = !(f.zf || (f.sf != f.of)) := rfl
theorem subF_of {w : Nat} (f : Rflags) (x y : BitVec w) : (subF f x y).of = overflowSub x y (x - y) := by
  simp [subF, Rflags.arith]

/-- `jg` after `cmp x, y` (32 bits): signed greater. -/
theorem subF_g32 (f : Rflags) (x y : BitVec 32) : (subF f x y).cond 15 = decide (y.toInt < x.toInt) := by
  rw [cond_15, subF_zf', subF_sf, subF_of, overflowSub]
  have ex := BitVec.msb_eq_decide x
  have ey := BitVec.msb_eq_decide y
  have er := BitVec.msb_eq_decide (x - y)
  have hz : (x - y == 0) = decide (x.toNat = y.toNat) := by
    rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_eq]
    exact ⟨fun h => by bv_omega, fun h => by bv_omega⟩
  rw [hz, BitVec.toInt_eq_toNat_cond, BitVec.toInt_eq_toNat_cond]
  rw [BitVec.toNat_sub] at er
  have hx := x.isLt
  have hy := y.isLt
  cases hmx : x.msb <;> cases hmy : y.msb <;> cases hmr : (x - y).msb <;> rw [hmx] at ex <;> rw [hmy] at ey <;>
    rw [hmr] at er <;>
    simp only [Bool.false_eq, Bool.true_eq, decide_eq_false_iff_not, decide_eq_true_eq] at ex ey er <;>
    rw [Bool.eq_iff_iff] <;> simp <;> omega

end FV7z
