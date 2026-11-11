import FV7z.Lemmas.Sp
import FV7z.Lemmas.BlkOps2
/-!
# The stretches of straight-line code of `__getrlimit` (PLAN.md G3, startup)

Each distinct stretch between labels and jumps (`p*`, 2 of them) and each distinct jump (`j*`, 1) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.Grl
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The stretch at `0`. -/
def p0 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0x49, 0x89, 0xf2, 0x31, 0xd2, 0x89, 0xfe, 0xb8, 0x2e, 0x01, 0x00, 0x00,
  0x31, 0xff]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem p0_4 : ∀ feat, Dec feat p0 4 (FV7z.mk .mov 64 [gr 64 10, Src.opd 64 (.r 6)] 3) := by dec_rfl
theorem p0_7 : ∀ feat, Dec feat p0 7 (FV7z.mk .xor 32 [gr 32 2, Src.opd 32 (.r 2)] 2) := by dec_rfl
theorem p0_9 : ∀ feat, Dec feat p0 9 (FV7z.mk .mov 32 [gr 32 6, Src.opd 32 (.r 7)] 2) := by dec_rfl
theorem p0_11 : ∀ feat, Dec feat p0 11 (FV7z.mk .mov 32 [gr 32 0, Src.opd 32 (.i 302)] 5) := by dec_rfl
theorem p0_16 : ∀ feat, Dec feat p0 16 (FV7z.mk .xor 32 [gr 32 7, Src.opd 32 (.r 7)] 2) := by dec_rfl

/-- What the stretch does. -/
def o0 : List Op := [
  Op.nop,
  Op.mov 64 10 (.r 6),
  Op.xor 32 2 (.r 2),
  Op.mov 32 6 (.r 7),
  Op.mov 32 0 (.i 302),
  Op.xor 32 7 (.r 7)]

theorem b0 (prof : Profile) : Blk prof p0 0 18 o0 :=
  .cons (p0_0 _) (OpI.endbr) (by decide) <|
  .cons (p0_4 _) (OpI.mov (.r 6) (.inr rfl)) (by decide) <|
  .cons (p0_7 _) (OpI.xor (.r 2) (.inl rfl)) (by decide) <|
  .cons (p0_9 _) (OpI.mov (.r 7) (.inl rfl)) (by decide) <|
  .cons (p0_11 _) (OpI.mov (.i 302) (.inl rfl)) (by decide) <|
  .cons (p0_16 _) (OpI.xor (.r 7) (.inl rfl)) (by decide) <|
  .nil 18

/-- The stretch at `20`. -/
def p1 : List Byte := [
  0x48, 0x3d, 0x00, 0xf0, 0xff, 0xff]

theorem p1_0 : ∀ feat, Dec feat p1 0 (FV7z.mk .cmp 64 [gr 64 0, Src.opd 64 (.i 18446744073709547520)] 6) := by dec_rfl

/-- What the stretch does. -/
def o1 : List Op := [
  Op.cmp 64 0 (.i 18446744073709547520)]

theorem b1 (prof : Profile) : Blk prof p1 0 6 o1 :=
  .cons (p1_0 _) (OpI.cmp (.i 18446744073709547520) (.inr rfl)) (by decide) <|
  .nil 6

def j0 : List Byte := [0x77, 0x04]
theorem j0_0 : ∀ feat, Dec feat j0 0 (FV7z.mk (.jcc 7) 64 [.rel 4] 2) := by dec_rfl

end FV7z.Grl
