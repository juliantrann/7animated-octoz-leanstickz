import FV7z.Imm.Cuts
import FV7z.Smm.Holds
/-!
# `_int_malloc`: the `call` and the `ret` of the way of the first call (PLAN.md G3, `malloc`)

The two instructions of that way the blocks do not hold, decoded at their offsets:

- `call_3280`: the `call` of `sysmalloc`, with its target `tgt_3280`;
- `ret_950`: the `ret`.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Imm

/-- The `call` of `sysmalloc`. -/
def pc3280 : List Byte := [0xe8, 0xab, 0xea, 0xff, 0xff]
theorem pc3280_0 : ∀ feat, Dec feat pc3280 0 (FV7z.mk .call 64 [.rel 18446744073709546155] 5) := by dec_rfl
theorem wc3280 : pc3280 <+: imm.drop 3280 := by decide +kernel
theorem call_3280 (feat : Features) : Dec feat imm 3280 (FV7z.mk .call 64 [.rel 18446744073709546155] 5) :=
  Dec.shift (j := 3280) (k := 0) (pc3280_0 feat) wc3280 (Nat.zero_le _)

/-- The `call` at 3280 goes to `sysmalloc`. -/
theorem tgt_3280 : imm_at.add (3280 + 5) + BitVec.ofNat 64 18446744073709546155 = Smm.smm_at := by decide

theorem w_950 : Sbrk.pret <+: imm.drop 950 := by decide +kernel
theorem ret_950 (feat : Features) : Dec feat imm 950 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 950) (k := 0) (Sbrk.pret_0 feat) w_950 (Nat.zero_le _)

end FV7z.Imm
