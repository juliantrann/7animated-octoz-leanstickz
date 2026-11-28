import FV7z.Lemmas.Sp
import FV7z.Lemmas.BlkOps2
/-!
# The stretches of straight-line code of `NWindows::NFile::NIO::COutFile::Create_ALWAYS_or_Open_ALWAYS(char const*, bool)` (PLAN.md §M, M1)

Each distinct stretch between labels and jumps (`p*`, 1 of them) and each distinct jump (`j*`, 0) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.Cao
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The stretch at `0`. -/
def p0 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0x80, 0xfa, 0x01, 0x19, 0xd2, 0x81, 0xe2, 0x00, 0xfe, 0xff, 0xff, 0x81,
  0xc2, 0x41, 0x02, 0x00, 0x00]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem p0_4 : ∀ feat, Dec feat p0 4 (FV7z.mk .cmp 8 [gr 8 2, Src.opd 8 (.i 1)] 3) := by dec_rfl
theorem p0_7 : ∀ feat, Dec feat p0 7 (FV7z.mk .sbb 32 [gr 32 2, Src.opd 32 (.r 2)] 2) := by dec_rfl
theorem p0_9 : ∀ feat, Dec feat p0 9 (FV7z.mk .and 32 [gr 32 2, Src.opd 32 (.i 4294966784)] 6) := by dec_rfl
theorem p0_15 : ∀ feat, Dec feat p0 15 (FV7z.mk .add 32 [gr 32 2, Src.opd 32 (.i 577)] 6) := by dec_rfl

/-- What the stretch does. -/
def o0 : List Op := [
  Op.nop,
  Op.cmp 8 2 (.i 1),
  Op.sbb 32 2 (.r 2),
  Op.and 32 2 (.i 4294966784),
  Op.add 32 2 (.i 577)]

theorem b0 (prof : Profile) : Blk prof p0 0 21 o0 :=
  .cons (p0_0 _) (OpI.endbr) (by decide) <|
  .cons (p0_4 _) (OpI.cmp8 (.i 1)) (by decide) <|
  .cons (p0_7 _) (OpI.sbb (.r 2) (.inl rfl)) (by decide) <|
  .cons (p0_9 _) (OpI.and (.i 4294966784) (.inl rfl)) (by decide) <|
  .cons (p0_15 _) (OpI.add (.i 577) (.inl rfl)) (by decide) <|
  .nil 21

end FV7z.Cao
