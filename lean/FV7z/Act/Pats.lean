import FV7z.Lemmas.Sp
import FV7z.Lemmas.BlkOps2
/-!
# The stretches of straight-line code of `AString::AString()` (PLAN.md §M, M1)

Each distinct stretch between labels and jumps (`p*`, 2 of them) and each distinct jump (`j*`, 0) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.Act
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The stretch at `0`. -/
def p0 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0x53, 0x48, 0x89, 0xfb, 0x48, 0xc7, 0x07, 0x00, 0x00, 0x00, 0x00, 0xbf,
  0x04, 0x00, 0x00, 0x00]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem p0_4 : ∀ feat, Dec feat p0 4 (FV7z.mk .push 64 [gr 64 3] 1) := by dec_rfl
theorem p0_5 : ∀ feat, Dec feat p0 5 (FV7z.mk .mov 64 [gr 64 3, Src.opd 64 (.r 7)] 3) := by dec_rfl
theorem p0_8 : ∀ feat, Dec feat p0 8 (FV7z.mk .mov 64 [.mem (mg (some 7) none 1 0 64), .imm 64 0] 7) := by dec_rfl
theorem p0_15 : ∀ feat, Dec feat p0 15 (FV7z.mk .mov 32 [gr 32 7, Src.opd 32 (.i 4)] 5) := by dec_rfl

/-- What the stretch does. -/
def o0 : List Op := [
  Op.nop,
  Op.push 3,
  Op.mov 64 3 (.r 7),
  Op.sti 64 (some 7) none 1 0 0,
  Op.mov 32 7 (.i 4)]

theorem b0 (prof : Profile) : Blk prof p0 0 20 o0 :=
  .cons (p0_0 _) (OpI.endbr) (by decide) <|
  .cons (p0_4 _) (OpI.push) (by decide) <|
  .cons (p0_5 _) (OpI.mov (.r 7) (.inr rfl)) (by decide) <|
  .cons (p0_8 _) (OpI.sti (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p0_15 _) (OpI.mov (.i 4) (.inl rfl)) (by decide) <|
  .nil 20

/-- The stretch at `25`. -/
def p1 : List Byte := [
  0x48, 0xba, 0x00, 0x00, 0x00, 0x00, 0x03, 0x00, 0x00, 0x00, 0x48, 0x89, 0x03, 0x48, 0x89, 0x53,
  0x08, 0xc6, 0x00, 0x00, 0x5b]

theorem p1_0 : ∀ feat, Dec feat p1 0 (FV7z.mk .mov 64 [gr 64 2, Src.opd 64 (.i 12884901888)] 10) := by dec_rfl
theorem p1_10 : ∀ feat, Dec feat p1 10 (FV7z.mk .mov 64 [.mem (mg (some 3) none 1 0 64), gr 64 0] 3) := by dec_rfl
theorem p1_13 : ∀ feat, Dec feat p1 13 (FV7z.mk .mov 64 [.mem (mg (some 3) none 1 8 64), gr 64 2] 4) := by dec_rfl
theorem p1_17 : ∀ feat, Dec feat p1 17 (FV7z.mk .mov 8 [.mem (mg (some 0) none 1 0 8), .imm 8 0] 3) := by dec_rfl
theorem p1_20 : ∀ feat, Dec feat p1 20 (FV7z.mk .pop 64 [gr 64 3] 1) := by dec_rfl

/-- What the stretch does. -/
def o1 : List Op := [
  Op.mov 64 2 (.i 12884901888),
  Op.st 64 (some 3) none 1 0 0,
  Op.st 64 (some 3) none 1 8 2,
  Op.sti 8 (some 0) none 1 0 0,
  Op.pop 3]

theorem b1 (prof : Profile) : Blk prof p1 0 21 o1 :=
  .cons (p1_0 _) (OpI.mov (.i 12884901888) (.inr rfl)) (by decide) <|
  .cons (p1_10 _) (OpI.st (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p1_13 _) (OpI.st (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p1_17 _) (OpI.sti (.inl rfl)) (by decide) <|
  .cons (p1_20 _) (OpI.pop) (by decide) <|
  .nil 21

end FV7z.Act
