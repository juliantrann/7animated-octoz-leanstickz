import FV7z.Lemmas.Sp
import FV7z.Lemmas.BlkOps2
/-!
# The stretches of straight-line code of `malloc_printerr` (PLAN.md §M, M1)

Each distinct stretch between labels and jumps (`p*`, 1 of them) and each distinct jump (`j*`, 0) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.Mpe
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The stretch at `0`. -/
def p0 : List Byte := [
  0x50, 0x58, 0x48, 0x8d, 0x35, 0x06, 0x83, 0x0d, 0x00, 0x31, 0xc0, 0x48, 0x89, 0xfa, 0x48, 0x83,
  0xec, 0x08, 0xbf, 0x01, 0x00, 0x00, 0x00]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .push 64 [gr 64 0] 1) := by dec_rfl
theorem p0_1 : ∀ feat, Dec feat p0 1 (FV7z.mk .pop 64 [gr 64 0] 1) := by dec_rfl
theorem p0_2 : ∀ feat, Dec feat p0 2 (FV7z.mk .lea 64 [gr 64 6, .mem (mrip 885510 0)] 7) := by dec_rfl
theorem p0_9 : ∀ feat, Dec feat p0 9 (FV7z.mk .xor 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl
theorem p0_11 : ∀ feat, Dec feat p0 11 (FV7z.mk .mov 64 [gr 64 2, Src.opd 64 (.r 7)] 3) := by dec_rfl
theorem p0_14 : ∀ feat, Dec feat p0 14 (FV7z.mk .sub 64 [gr 64 4, Src.opd 64 (.i 8)] 4) := by dec_rfl
theorem p0_18 : ∀ feat, Dec feat p0 18 (FV7z.mk .mov 32 [gr 32 7, Src.opd 32 (.i 1)] 5) := by dec_rfl

/-- What the stretch does. -/
def o0 : List Op := [
  Op.push 0,
  Op.pop 0,
  Op.mov 64 6 (.i 7366559),
  Op.xor 32 0 (.r 0),
  Op.mov 64 2 (.r 7),
  Op.sub 64 4 (.i 8),
  Op.mov 32 7 (.i 1)]

theorem b0 (prof : Profile) : BlkA prof p0 (0x62e490 : Addr) 0 23 o0 :=
  .cons (p0_0 _) ((OpI.push).at _) (by decide) <|
  .cons (p0_1 _) ((OpI.pop).at _) (by decide) <|
  .cons (p0_2 _) (OpIA.lea_rip (by decide)) (by decide) <|
  .cons (p0_9 _) ((OpI.xor (.r 0) (.inl rfl)).at _) (by decide) <|
  .cons (p0_11 _) ((OpI.mov (.r 7) (.inr rfl)).at _) (by decide) <|
  .cons (p0_14 _) ((OpI.sub (.i 8) (.inr rfl)).at _) (by decide) <|
  .cons (p0_18 _) ((OpI.mov (.i 1) (.inl rfl)).at _) (by decide) <|
  .nil 23

end FV7z.Mpe
