import FV7z.Lemmas.Sp
import FV7z.Lemmas.BlkOps2
/-!
# The stretches of straight-line code of `__default_morecore` (PLAN.md G3, `malloc`)

Each distinct stretch between labels and jumps (`p*`, 2 of them) and each distinct jump (`j*`, 0) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.Dmc
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The stretch at `0`. -/
def p0 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0x48, 0x83, 0xec, 0x08]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem p0_4 : ∀ feat, Dec feat p0 4 (FV7z.mk .sub 64 [gr 64 4, Src.opd 64 (.i 8)] 4) := by dec_rfl

/-- What the stretch does. -/
def o0 : List Op := [
  Op.nop,
  Op.sub 64 4 (.i 8)]

theorem b0 (prof : Profile) : Blk prof p0 0 8 o0 :=
  .cons (p0_0 _) (OpI.endbr) (by decide) <|
  .cons (p0_4 _) (OpI.sub (.i 8) (.inr rfl)) (by decide) <|
  .nil 8

/-- The stretch at `13`. -/
def p1 : List Byte := [
  0xba, 0x00, 0x00, 0x00, 0x00, 0x48, 0x83, 0xf8, 0xff, 0x48, 0x0f, 0x44, 0xc2, 0x48, 0x83, 0xc4,
  0x08]

theorem p1_0 : ∀ feat, Dec feat p1 0 (FV7z.mk .mov 32 [gr 32 2, Src.opd 32 (.i 0)] 5) := by dec_rfl
theorem p1_5 : ∀ feat, Dec feat p1 5 (FV7z.mk .cmp 64 [gr 64 0, Src.opd 64 (.i 18446744073709551615)] 4) := by dec_rfl
theorem p1_9 : ∀ feat, Dec feat p1 9 (FV7z.mk (.cmovcc 4) 64 [gr 64 0, gr 64 2] 4) := by dec_rfl
theorem p1_13 : ∀ feat, Dec feat p1 13 (FV7z.mk .add 64 [gr 64 4, Src.opd 64 (.i 8)] 4) := by dec_rfl

/-- What the stretch does. -/
def o1 : List Op := [
  Op.mov 32 2 (.i 0),
  Op.cmp 64 0 (.i 18446744073709551615),
  Op.cmov64 4 0 2,
  Op.add 64 4 (.i 8)]

theorem b1 (prof : Profile) : Blk prof p1 0 17 o1 :=
  .cons (p1_0 _) (OpI.mov (.i 0) (.inl rfl)) (by decide) <|
  .cons (p1_5 _) (OpI.cmp (.i 18446744073709551615) (.inr rfl)) (by decide) <|
  .cons (p1_9 _) (OpI.cmov64) (by decide) <|
  .cons (p1_13 _) (OpI.add (.i 8) (.inr rfl)) (by decide) <|
  .nil 17

end FV7z.Dmc
