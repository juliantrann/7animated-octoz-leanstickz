import FV7z.Lzma.Code
import FV7z.Lzma.Pats
/-!
# The `ret` of `LzmaDec_DecodeReal_3` (PLAN.md G2.2)

The code's last byte, at 4718, where the epilogue ends. In a file of its own: the kernel's memory for the evaluation of
the code from an offset adds to that of the file's other proofs.
-/
open ZellicX86 Decode FV7z FV7z.Leaf
namespace FV7z.Lzma

/-- The `ret`, the code's last byte. -/
def pret : List Byte := [0xc3]
theorem pret_0 : ∀ feat, Dec feat pret 0 (FV7z.mk .ret 64 [] 1) := by dec_rfl
set_option maxRecDepth 100000 in
theorem w_4718 : pret <+: dr3.drop 4718 := by decide +kernel
theorem ret_4718 (feat : Features) : Dec feat dr3 4718 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 4718) (k := 0) (pret_0 feat) w_4718 (Nat.zero_le _)

end FV7z.Lzma
