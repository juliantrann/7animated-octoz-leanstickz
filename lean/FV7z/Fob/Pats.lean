import FV7z.Lemmas.Sp
import FV7z.Lemmas.BlkOps2
/-!
# The stretches of straight-line code of `NWindows::NFile::NIO::CFileBase::OpenBinary` (PLAN.md §M, M1)

Each distinct stretch between labels and jumps (`p*`, 3 of them) and each distinct jump (`j*`, 0) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.Fob
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The stretch at `0`. -/
def p0 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0x41, 0x55, 0x41, 0x89, 0xcd, 0x41, 0x54, 0x41, 0x89, 0xd4, 0x55, 0x48,
  0x89, 0xf5, 0x53, 0x48, 0x89, 0xfb, 0x48, 0x83, 0xec, 0x08]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem p0_4 : ∀ feat, Dec feat p0 4 (FV7z.mk .push 64 [gr 64 13] 2) := by dec_rfl
theorem p0_6 : ∀ feat, Dec feat p0 6 (FV7z.mk .mov 32 [gr 32 13, Src.opd 32 (.r 1)] 3) := by dec_rfl
theorem p0_9 : ∀ feat, Dec feat p0 9 (FV7z.mk .push 64 [gr 64 12] 2) := by dec_rfl
theorem p0_11 : ∀ feat, Dec feat p0 11 (FV7z.mk .mov 32 [gr 32 12, Src.opd 32 (.r 2)] 3) := by dec_rfl
theorem p0_14 : ∀ feat, Dec feat p0 14 (FV7z.mk .push 64 [gr 64 5] 1) := by dec_rfl
theorem p0_15 : ∀ feat, Dec feat p0 15 (FV7z.mk .mov 64 [gr 64 5, Src.opd 64 (.r 6)] 3) := by dec_rfl
theorem p0_18 : ∀ feat, Dec feat p0 18 (FV7z.mk .push 64 [gr 64 3] 1) := by dec_rfl
theorem p0_19 : ∀ feat, Dec feat p0 19 (FV7z.mk .mov 64 [gr 64 3, Src.opd 64 (.r 7)] 3) := by dec_rfl
theorem p0_22 : ∀ feat, Dec feat p0 22 (FV7z.mk .sub 64 [gr 64 4, Src.opd 64 (.i 8)] 4) := by dec_rfl

/-- What the stretch does. -/
def o0 : List Op := [
  Op.nop,
  Op.push 13,
  Op.mov 32 13 (.r 1),
  Op.push 12,
  Op.mov 32 12 (.r 2),
  Op.push 5,
  Op.mov 64 5 (.r 6),
  Op.push 3,
  Op.mov 64 3 (.r 7),
  Op.sub 64 4 (.i 8)]

theorem b0 (prof : Profile) : Blk prof p0 0 26 o0 :=
  .cons (p0_0 _) (OpI.endbr) (by decide) <|
  .cons (p0_4 _) (OpI.push) (by decide) <|
  .cons (p0_6 _) (OpI.mov (.r 1) (.inl rfl)) (by decide) <|
  .cons (p0_9 _) (OpI.push) (by decide) <|
  .cons (p0_11 _) (OpI.mov (.r 2) (.inl rfl)) (by decide) <|
  .cons (p0_14 _) (OpI.push) (by decide) <|
  .cons (p0_15 _) (OpI.mov (.r 6) (.inr rfl)) (by decide) <|
  .cons (p0_18 _) (OpI.push) (by decide) <|
  .cons (p0_19 _) (OpI.mov (.r 7) (.inr rfl)) (by decide) <|
  .cons (p0_22 _) (OpI.sub (.i 8) (.inr rfl)) (by decide) <|
  .nil 26

/-- The stretch at `31`. -/
def p1 : List Byte := [
  0x44, 0x89, 0xea, 0x44, 0x89, 0xe6, 0x48, 0x89, 0xef, 0x31, 0xc0]

theorem p1_0 : ∀ feat, Dec feat p1 0 (FV7z.mk .mov 32 [gr 32 2, Src.opd 32 (.r 13)] 3) := by dec_rfl
theorem p1_3 : ∀ feat, Dec feat p1 3 (FV7z.mk .mov 32 [gr 32 6, Src.opd 32 (.r 12)] 3) := by dec_rfl
theorem p1_6 : ∀ feat, Dec feat p1 6 (FV7z.mk .mov 64 [gr 64 7, Src.opd 64 (.r 5)] 3) := by dec_rfl
theorem p1_9 : ∀ feat, Dec feat p1 9 (FV7z.mk .xor 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl

/-- What the stretch does. -/
def o1 : List Op := [
  Op.mov 32 2 (.r 13),
  Op.mov 32 6 (.r 12),
  Op.mov 64 7 (.r 5),
  Op.xor 32 0 (.r 0)]

theorem b1 (prof : Profile) : Blk prof p1 0 11 o1 :=
  .cons (p1_0 _) (OpI.mov (.r 13) (.inl rfl)) (by decide) <|
  .cons (p1_3 _) (OpI.mov (.r 12) (.inl rfl)) (by decide) <|
  .cons (p1_6 _) (OpI.mov (.r 5) (.inr rfl)) (by decide) <|
  .cons (p1_9 _) (OpI.xor (.r 0) (.inl rfl)) (by decide) <|
  .nil 11

/-- The stretch at `47`. -/
def p2 : List Byte := [
  0x83, 0xf8, 0xff, 0x89, 0x03, 0x0f, 0x95, 0xc0, 0x48, 0x83, 0xc4, 0x08, 0x5b, 0x5d, 0x41, 0x5c,
  0x41, 0x5d]

theorem p2_0 : ∀ feat, Dec feat p2 0 (FV7z.mk .cmp 32 [gr 32 0, Src.opd 32 (.i 4294967295)] 3) := by dec_rfl
theorem p2_3 : ∀ feat, Dec feat p2 3 (FV7z.mk .mov 32 [.mem (mg (some 3) none 1 0 32), gr 32 0] 2) := by dec_rfl
theorem p2_5 : ∀ feat, Dec feat p2 5 (FV7z.mk (.setcc 5) 8 [gr 8 0] 3) := by dec_rfl
theorem p2_8 : ∀ feat, Dec feat p2 8 (FV7z.mk .add 64 [gr 64 4, Src.opd 64 (.i 8)] 4) := by dec_rfl
theorem p2_12 : ∀ feat, Dec feat p2 12 (FV7z.mk .pop 64 [gr 64 3] 1) := by dec_rfl
theorem p2_13 : ∀ feat, Dec feat p2 13 (FV7z.mk .pop 64 [gr 64 5] 1) := by dec_rfl
theorem p2_14 : ∀ feat, Dec feat p2 14 (FV7z.mk .pop 64 [gr 64 12] 2) := by dec_rfl
theorem p2_16 : ∀ feat, Dec feat p2 16 (FV7z.mk .pop 64 [gr 64 13] 2) := by dec_rfl

/-- What the stretch does. -/
def o2 : List Op := [
  Op.cmp 32 0 (.i 4294967295),
  Op.st 32 (some 3) none 1 0 0,
  Op.setcc 5 0,
  Op.add 64 4 (.i 8),
  Op.pop 3,
  Op.pop 5,
  Op.pop 12,
  Op.pop 13]

theorem b2 (prof : Profile) : Blk prof p2 0 18 o2 :=
  .cons (p2_0 _) (OpI.cmp (.i 4294967295) (.inl rfl)) (by decide) <|
  .cons (p2_3 _) (OpI.st (.inr (.inr (.inl rfl)))) (by decide) <|
  .cons (p2_5 _) (OpI.setcc) (by decide) <|
  .cons (p2_8 _) (OpI.add (.i 8) (.inr rfl)) (by decide) <|
  .cons (p2_12 _) (OpI.pop) (by decide) <|
  .cons (p2_13 _) (OpI.pop) (by decide) <|
  .cons (p2_14 _) (OpI.pop) (by decide) <|
  .cons (p2_16 _) (OpI.pop) (by decide) <|
  .nil 18

end FV7z.Fob
