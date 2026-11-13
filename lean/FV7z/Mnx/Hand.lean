import FV7z.Mnx.Cuts
import FV7z.Mhi.Hand
/-!
# `malloc` after the first call: the instructions outside the blocks (PLAN.md G3, `malloc`)

Decoded at their offsets: `call_109`, the `call` of `_int_malloc` (`0x630be0`), with its target `tgt_109`; `ret_171`,
the `ret`.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Mnx

/-- `call _int_malloc`. -/
def pc109 : List Byte := [0xe8, 0x0e, 0xda, 0xff, 0xff]
theorem pc109_0 : ∀ feat, Dec feat pc109 0 (FV7z.mk .call 64 [.rel 18446744073709541902] 5) := by dec_rfl
theorem w_109 : pc109 <+: mnx.drop 109 := by decide +kernel
theorem call_109 (feat : Features) : Dec feat mnx 109 (FV7z.mk .call 64 [.rel 18446744073709541902] 5) :=
  Dec.shift (j := 109) (k := 0) (pc109_0 feat) w_109 (Nat.zero_le _)

/-- The `call` at 109 goes to `_int_malloc`. -/
theorem tgt_109 : mnx_at.add (109 + 5) + BitVec.ofNat 64 18446744073709541902 = Imm.imm_at := by decide

theorem w_171 : Sbrk.pret <+: mnx.drop 171 := by decide +kernel
theorem ret_171 (feat : Features) : Dec feat mnx 171 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 171) (k := 0) (Sbrk.pret_0 feat) w_171 (Nat.zero_le _)

end FV7z.Mnx
