import FV7z.Lemmas.Sp
import FV7z.Lemmas.BlkOps20
import FV7z.Lemmas.BlkOps2
/-!
# The stretches of straight-line code of `NWindows::NFile::NDir::C_umask::C_umask()` (PLAN.md §M, M1)

Each distinct stretch between labels and jumps (`p*`, 2 of them) and each distinct jump (`j*`, 0) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.Cum
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The stretch at `0`. -/
def p0 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0x53, 0x48, 0x89, 0xfb, 0x31, 0xff]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem p0_4 : ∀ feat, Dec feat p0 4 (FV7z.mk .push 64 [gr 64 3] 1) := by dec_rfl
theorem p0_5 : ∀ feat, Dec feat p0 5 (FV7z.mk .mov 64 [gr 64 3, Src.opd 64 (.r 7)] 3) := by dec_rfl
theorem p0_8 : ∀ feat, Dec feat p0 8 (FV7z.mk .xor 32 [gr 32 7, Src.opd 32 (.r 7)] 2) := by dec_rfl

/-- What the stretch does. -/
def o0 : List Op := [
  Op.nop,
  Op.push 3,
  Op.mov 64 3 (.r 7),
  Op.xor 32 7 (.r 7)]

theorem b0 (prof : Profile) : Blk prof p0 0 10 o0 :=
  .cons (p0_0 _) (OpI.endbr) (by decide) <|
  .cons (p0_4 _) (OpI.push) (by decide) <|
  .cons (p0_5 _) (OpI.mov (.r 7) (.inr rfl)) (by decide) <|
  .cons (p0_8 _) (OpI.xor (.r 7) (.inl rfl)) (by decide) <|
  .nil 10

/-- The stretch at `15`. -/
def p1 : List Byte := [
  0x89, 0xc7, 0xf7, 0xd0, 0x25, 0xff, 0x01, 0x00, 0x00, 0x89, 0x03, 0x5b]

theorem p1_0 : ∀ feat, Dec feat p1 0 (FV7z.mk .mov 32 [gr 32 7, Src.opd 32 (.r 0)] 2) := by dec_rfl
theorem p1_2 : ∀ feat, Dec feat p1 2 (FV7z.mk .not 32 [gr 32 0] 2) := by dec_rfl
theorem p1_4 : ∀ feat, Dec feat p1 4 (FV7z.mk .and 32 [gr 32 0, Src.opd 32 (.i 511)] 5) := by dec_rfl
theorem p1_9 : ∀ feat, Dec feat p1 9 (FV7z.mk .mov 32 [.mem (mg (some 3) none 1 0 32), gr 32 0] 2) := by dec_rfl
theorem p1_11 : ∀ feat, Dec feat p1 11 (FV7z.mk .pop 64 [gr 64 3] 1) := by dec_rfl

/-- What the stretch does. -/
def o1 : List Op := [
  Op.mov 32 7 (.r 0),
  Op.not32 0,
  Op.and 32 0 (.i 511),
  Op.st 32 (some 3) none 1 0 0,
  Op.pop 3]

theorem b1 (prof : Profile) : Blk prof p1 0 12 o1 :=
  .cons (p1_0 _) (OpI.mov (.r 0) (.inl rfl)) (by decide) <|
  .cons (p1_2 _) (OpI.not32) (by decide) <|
  .cons (p1_4 _) (OpI.and (.i 511) (.inl rfl)) (by decide) <|
  .cons (p1_9 _) (OpI.st (.inr (.inr (.inl rfl)))) (by decide) <|
  .cons (p1_11 _) (OpI.pop) (by decide) <|
  .nil 12

end FV7z.Cum
