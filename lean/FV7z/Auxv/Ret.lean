import FV7z.Auxv.Code
import FV7z.Auxv.Pats
/-!
# The `ret` of `_dl_aux_init` (PLAN.md G3, startup)

The byte at 493, where the epilogue ends. In a file of its own, as `Lzma/Ret.lean`.
-/
open ZellicX86 Decode FV7z FV7z.Leaf
namespace FV7z.Auxv

/-- The `ret`. -/
def pret : List Byte := [0xc3]
theorem pret_0 : ∀ feat, Dec feat pret 0 (FV7z.mk .ret 64 [] 1) := by dec_rfl
set_option maxRecDepth 100000 in
theorem w_493 : pret <+: aux.drop 493 := by decide +kernel
theorem ret_493 (feat : Features) : Dec feat aux 493 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 493) (k := 0) (pret_0 feat) w_493 (Nat.zero_le _)

end FV7z.Auxv
