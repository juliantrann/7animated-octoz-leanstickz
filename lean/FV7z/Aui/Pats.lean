import FV7z.Lemmas.Sp
import FV7z.Lemmas.BlkOps2
/-!
# The stretches of straight-line code of `AString::Add_UInt32` (PLAN.md §M, M1)

Each distinct stretch between labels and jumps (`p*`, 3 of them) and each distinct jump (`j*`, 0) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.Aui
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The stretch at `0`. -/
def p0 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0x55, 0x89, 0xf5, 0xbe, 0x0a, 0x00, 0x00, 0x00, 0x53, 0x48, 0x89, 0xfb,
  0x48, 0x83, 0xec, 0x08]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem p0_4 : ∀ feat, Dec feat p0 4 (FV7z.mk .push 64 [gr 64 5] 1) := by dec_rfl
theorem p0_5 : ∀ feat, Dec feat p0 5 (FV7z.mk .mov 32 [gr 32 5, Src.opd 32 (.r 6)] 2) := by dec_rfl
theorem p0_7 : ∀ feat, Dec feat p0 7 (FV7z.mk .mov 32 [gr 32 6, Src.opd 32 (.i 10)] 5) := by dec_rfl
theorem p0_12 : ∀ feat, Dec feat p0 12 (FV7z.mk .push 64 [gr 64 3] 1) := by dec_rfl
theorem p0_13 : ∀ feat, Dec feat p0 13 (FV7z.mk .mov 64 [gr 64 3, Src.opd 64 (.r 7)] 3) := by dec_rfl
theorem p0_16 : ∀ feat, Dec feat p0 16 (FV7z.mk .sub 64 [gr 64 4, Src.opd 64 (.i 8)] 4) := by dec_rfl

/-- What the stretch does. -/
def o0 : List Op := [
  Op.nop,
  Op.push 5,
  Op.mov 32 5 (.r 6),
  Op.mov 32 6 (.i 10),
  Op.push 3,
  Op.mov 64 3 (.r 7),
  Op.sub 64 4 (.i 8)]

theorem b0 (prof : Profile) : Blk prof p0 0 20 o0 :=
  .cons (p0_0 _) (OpI.endbr) (by decide) <|
  .cons (p0_4 _) (OpI.push) (by decide) <|
  .cons (p0_5 _) (OpI.mov (.r 6) (.inl rfl)) (by decide) <|
  .cons (p0_7 _) (OpI.mov (.i 10) (.inl rfl)) (by decide) <|
  .cons (p0_12 _) (OpI.push) (by decide) <|
  .cons (p0_13 _) (OpI.mov (.r 7) (.inr rfl)) (by decide) <|
  .cons (p0_16 _) (OpI.sub (.i 8) (.inr rfl)) (by decide) <|
  .nil 20

/-- The stretch at `25`. -/
def p1 : List Byte := [
  0x8b, 0x73, 0x08, 0x89, 0xef, 0x48, 0x03, 0x33]

theorem p1_0 : ∀ feat, Dec feat p1 0 (FV7z.mk .mov 32 [gr 32 6, .mem (mg (some 3) none 1 8 32)] 3) := by dec_rfl
theorem p1_3 : ∀ feat, Dec feat p1 3 (FV7z.mk .mov 32 [gr 32 7, Src.opd 32 (.r 5)] 2) := by dec_rfl
theorem p1_5 : ∀ feat, Dec feat p1 5 (FV7z.mk .add 64 [gr 64 6, .mem (mg (some 3) none 1 0 64)] 3) := by dec_rfl

/-- What the stretch does. -/
def o1 : List Op := [
  Op.ld 32 6 (some 3) none 1 8,
  Op.mov 32 7 (.r 5),
  Op.addm 64 6 (some 3) none 1 0]

theorem b1 (prof : Profile) : Blk prof p1 0 8 o1 :=
  .cons (p1_0 _) (OpI.ld (.inl rfl)) (by decide) <|
  .cons (p1_3 _) (OpI.mov (.r 5) (.inl rfl)) (by decide) <|
  .cons (p1_5 _) (OpI.addm (.inr rfl)) (by decide) <|
  .nil 8

/-- The stretch at `38`. -/
def p2 : List Byte := [
  0x48, 0x2b, 0x03, 0x89, 0x43, 0x08, 0x48, 0x83, 0xc4, 0x08, 0x5b, 0x5d]

theorem p2_0 : ∀ feat, Dec feat p2 0 (FV7z.mk .sub 64 [gr 64 0, .mem (mg (some 3) none 1 0 64)] 3) := by dec_rfl
theorem p2_3 : ∀ feat, Dec feat p2 3 (FV7z.mk .mov 32 [.mem (mg (some 3) none 1 8 32), gr 32 0] 3) := by dec_rfl
theorem p2_6 : ∀ feat, Dec feat p2 6 (FV7z.mk .add 64 [gr 64 4, Src.opd 64 (.i 8)] 4) := by dec_rfl
theorem p2_10 : ∀ feat, Dec feat p2 10 (FV7z.mk .pop 64 [gr 64 3] 1) := by dec_rfl
theorem p2_11 : ∀ feat, Dec feat p2 11 (FV7z.mk .pop 64 [gr 64 5] 1) := by dec_rfl

/-- What the stretch does. -/
def o2 : List Op := [
  Op.subm 64 0 (some 3) none 1 0,
  Op.st 32 (some 3) none 1 8 0,
  Op.add 64 4 (.i 8),
  Op.pop 3,
  Op.pop 5]

theorem b2 (prof : Profile) : Blk prof p2 0 12 o2 :=
  .cons (p2_0 _) (OpI.subm (.inr rfl)) (by decide) <|
  .cons (p2_3 _) (OpI.st (.inr (.inr (.inl rfl)))) (by decide) <|
  .cons (p2_6 _) (OpI.add (.i 8) (.inr rfl)) (by decide) <|
  .cons (p2_10 _) (OpI.pop) (by decide) <|
  .cons (p2_11 _) (OpI.pop) (by decide) <|
  .nil 12

end FV7z.Aui
