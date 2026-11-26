import FV7z.Lemmas.Sp
import FV7z.Lemmas.BlkOps2
/-!
# The stretches of straight-line code of `CArcCommand::GetPathMode` (PLAN.md §M, M1)

Each distinct stretch between labels and jumps (`p*`, 1 of them) and each distinct jump (`j*`, 0) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.Gpm
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The stretch at `0`. -/
def p0 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0x8b, 0x07, 0xba, 0x02, 0x00, 0x00, 0x00, 0x83, 0xe8, 0x03, 0x83, 0xe0,
  0xfd, 0x0f, 0x45, 0xc2]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem p0_4 : ∀ feat, Dec feat p0 4 (FV7z.mk .mov 32 [gr 32 0, .mem (mg (some 7) none 1 0 32)] 2) := by dec_rfl
theorem p0_6 : ∀ feat, Dec feat p0 6 (FV7z.mk .mov 32 [gr 32 2, Src.opd 32 (.i 2)] 5) := by dec_rfl
theorem p0_11 : ∀ feat, Dec feat p0 11 (FV7z.mk .sub 32 [gr 32 0, Src.opd 32 (.i 3)] 3) := by dec_rfl
theorem p0_14 : ∀ feat, Dec feat p0 14 (FV7z.mk .and 32 [gr 32 0, Src.opd 32 (.i 4294967293)] 3) := by dec_rfl
theorem p0_17 : ∀ feat, Dec feat p0 17 (FV7z.mk (.cmovcc 5) 32 [gr 32 0, gr 32 2] 3) := by dec_rfl

/-- What the stretch does. -/
def o0 : List Op := [
  Op.nop,
  Op.ld 32 0 (some 7) none 1 0,
  Op.mov 32 2 (.i 2),
  Op.sub 32 0 (.i 3),
  Op.and 32 0 (.i 4294967293),
  Op.cmov32 5 0 2]

theorem b0 (prof : Profile) : Blk prof p0 0 20 o0 :=
  .cons (p0_0 _) (OpI.endbr) (by decide) <|
  .cons (p0_4 _) (OpI.ld (.inl rfl)) (by decide) <|
  .cons (p0_6 _) (OpI.mov (.i 2) (.inl rfl)) (by decide) <|
  .cons (p0_11 _) (OpI.sub (.i 3) (.inl rfl)) (by decide) <|
  .cons (p0_14 _) (OpI.and (.i 4294967293) (.inl rfl)) (by decide) <|
  .cons (p0_17 _) (OpI.cmov32) (by decide) <|
  .nil 20

end FV7z.Gpm
