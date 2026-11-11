import FV7z.Lemmas.Sp
import FV7z.Lemmas.BlkOps2
/-!
# The stretches of straight-line code of `__uname` (PLAN.md G3, startup)

Each distinct stretch between labels and jumps (`p*`, 2 of them) and each distinct jump (`j*`, 1) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.Uname
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The stretch at `0`. -/
def p0 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0xb8, 0x3f, 0x00, 0x00, 0x00]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem p0_4 : ∀ feat, Dec feat p0 4 (FV7z.mk .mov 32 [gr 32 0, Src.opd 32 (.i 63)] 5) := by dec_rfl

/-- What the stretch does. -/
def o0 : List Op := [
  Op.nop,
  Op.mov 32 0 (.i 63)]

theorem b0 (prof : Profile) : Blk prof p0 0 9 o0 :=
  .cons (p0_0 _) (OpI.endbr) (by decide) <|
  .cons (p0_4 _) (OpI.mov (.i 63) (.inl rfl)) (by decide) <|
  .nil 9

/-- The stretch at `11`. -/
def p1 : List Byte := [
  0x48, 0x3d, 0x01, 0xf0, 0xff, 0xff]

theorem p1_0 : ∀ feat, Dec feat p1 0 (FV7z.mk .cmp 64 [gr 64 0, Src.opd 64 (.i 18446744073709547521)] 6) := by dec_rfl

/-- What the stretch does. -/
def o1 : List Op := [
  Op.cmp 64 0 (.i 18446744073709547521)]

theorem b1 (prof : Profile) : Blk prof p1 0 6 o1 :=
  .cons (p1_0 _) (OpI.cmp (.i 18446744073709547521) (.inr rfl)) (by decide) <|
  .nil 6

def j0 : List Byte := [0x73, 0x01]
theorem j0_0 : ∀ feat, Dec feat j0 0 (FV7z.mk (.jcc 3) 64 [.rel 1] 2) := by dec_rfl

end FV7z.Uname
