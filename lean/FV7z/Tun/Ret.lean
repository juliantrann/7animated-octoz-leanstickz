import FV7z.Tun.Code
import FV7z.Tun.Pats
/-!
# The `ret` of `__tunables_init` (PLAN.md G3, startup)

The byte at 344, where the epilogue ends. In a file of its own, as `Lzma/Ret.lean`.
-/
open ZellicX86 Decode FV7z FV7z.Leaf
namespace FV7z.Tun

/-- The `ret`. -/
def pret : List Byte := [0xc3]
theorem pret_0 : ∀ feat, Dec feat pret 0 (FV7z.mk .ret 64 [] 1) := by dec_rfl
set_option maxRecDepth 100000 in
theorem w_344 : pret <+: tin.drop 344 := by decide +kernel
theorem ret_344 (feat : Features) : Dec feat tin 344 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 344) (k := 0) (pret_0 feat) w_344 (Nat.zero_le _)

end FV7z.Tun
