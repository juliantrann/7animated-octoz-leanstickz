import FV7z.Lemmas.Sp
import FV7z.Lemmas.BlkOps2
/-!
# The stretches of straight-line code of `_start` (PLAN.md G3, startup)

Each distinct stretch between labels and jumps (`p*`, 1 of them) and each distinct jump (`j*`, 0) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.Entry
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The stretch at `0`. -/
def p0 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0x31, 0xed, 0x49, 0x89, 0xd1, 0x5e, 0x48, 0x89, 0xe2, 0x48, 0x83, 0xe4,
  0xf0, 0x50, 0x54, 0x49, 0xc7, 0xc0, 0x40, 0x3d, 0x61, 0x00, 0x48, 0xc7, 0xc1, 0xa0, 0x3c, 0x61,
  0x00, 0x48, 0xc7, 0xc7, 0x90, 0xcd, 0x41, 0x00]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem p0_4 : ∀ feat, Dec feat p0 4 (FV7z.mk .xor 32 [gr 32 5, Src.opd 32 (.r 5)] 2) := by dec_rfl
theorem p0_6 : ∀ feat, Dec feat p0 6 (FV7z.mk .mov 64 [gr 64 9, Src.opd 64 (.r 2)] 3) := by dec_rfl
theorem p0_9 : ∀ feat, Dec feat p0 9 (FV7z.mk .pop 64 [gr 64 6] 1) := by dec_rfl
theorem p0_10 : ∀ feat, Dec feat p0 10 (FV7z.mk .mov 64 [gr 64 2, Src.opd 64 (.r 4)] 3) := by dec_rfl
theorem p0_13 : ∀ feat, Dec feat p0 13 (FV7z.mk .and 64 [gr 64 4, Src.opd 64 (.i 18446744073709551600)] 4) := by dec_rfl
theorem p0_17 : ∀ feat, Dec feat p0 17 (FV7z.mk .push 64 [gr 64 0] 1) := by dec_rfl
theorem p0_18 : ∀ feat, Dec feat p0 18 (FV7z.mk .push 64 [gr 64 4] 1) := by dec_rfl
theorem p0_19 : ∀ feat, Dec feat p0 19 (FV7z.mk .mov 64 [gr 64 8, Src.opd 64 (.i 6372672)] 7) := by dec_rfl
theorem p0_26 : ∀ feat, Dec feat p0 26 (FV7z.mk .mov 64 [gr 64 1, Src.opd 64 (.i 6372512)] 7) := by dec_rfl
theorem p0_33 : ∀ feat, Dec feat p0 33 (FV7z.mk .mov 64 [gr 64 7, Src.opd 64 (.i 4312464)] 7) := by dec_rfl

/-- What the stretch does. -/
def o0 : List Op := [
  Op.nop,
  Op.xor 32 5 (.r 5),
  Op.mov 64 9 (.r 2),
  Op.pop 6,
  Op.mov 64 2 (.r 4),
  Op.and 64 4 (.i 18446744073709551600),
  Op.push 0,
  Op.push 4,
  Op.mov 64 8 (.i 6372672),
  Op.mov 64 1 (.i 6372512),
  Op.mov 64 7 (.i 4312464)]

theorem b0 (prof : Profile) : Blk prof p0 0 40 o0 :=
  .cons (p0_0 _) (OpI.endbr) (by decide) <|
  .cons (p0_4 _) (OpI.xor (.r 5) (.inl rfl)) (by decide) <|
  .cons (p0_6 _) (OpI.mov (.r 2) (.inr rfl)) (by decide) <|
  .cons (p0_9 _) (OpI.pop) (by decide) <|
  .cons (p0_10 _) (OpI.mov (.r 4) (.inr rfl)) (by decide) <|
  .cons (p0_13 _) (OpI.and (.i 18446744073709551600) (.inr rfl)) (by decide) <|
  .cons (p0_17 _) (OpI.push) (by decide) <|
  .cons (p0_18 _) (OpI.push) (by decide) <|
  .cons (p0_19 _) (OpI.mov (.i 6372672) (.inr rfl)) (by decide) <|
  .cons (p0_26 _) (OpI.mov (.i 6372512) (.inr rfl)) (by decide) <|
  .cons (p0_33 _) (OpI.mov (.i 4312464) (.inr rfl)) (by decide) <|
  .nil 40

end FV7z.Entry
