import FV7z.Lemmas.Sp
import FV7z.Lemmas.BlkOps2
/-!
# The stretches of straight-line code of `Get_Correct_FsFile_Name` (PLAN.md §M, M1)

Each distinct stretch between labels and jumps (`p*`, 6 of them) and each distinct jump (`j*`, 2) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.Gcf
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The stretch at `0`. -/
def p0 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0x41, 0x54, 0x49, 0x89, 0xfc, 0x55, 0x48, 0x83, 0xec, 0x08]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem p0_4 : ∀ feat, Dec feat p0 4 (FV7z.mk .push 64 [gr 64 12] 2) := by dec_rfl
theorem p0_6 : ∀ feat, Dec feat p0 6 (FV7z.mk .mov 64 [gr 64 12, Src.opd 64 (.r 7)] 3) := by dec_rfl
theorem p0_9 : ∀ feat, Dec feat p0 9 (FV7z.mk .push 64 [gr 64 5] 1) := by dec_rfl
theorem p0_10 : ∀ feat, Dec feat p0 10 (FV7z.mk .sub 64 [gr 64 4, Src.opd 64 (.i 8)] 4) := by dec_rfl

/-- What the stretch does. -/
def o0 : List Op := [
  Op.nop,
  Op.push 12,
  Op.mov 64 12 (.r 7),
  Op.push 5,
  Op.sub 64 4 (.i 8)]

theorem b0 (prof : Profile) : Blk prof p0 0 14 o0 :=
  .cons (p0_0 _) (OpI.endbr) (by decide) <|
  .cons (p0_4 _) (OpI.push) (by decide) <|
  .cons (p0_6 _) (OpI.mov (.r 7) (.inr rfl)) (by decide) <|
  .cons (p0_9 _) (OpI.push) (by decide) <|
  .cons (p0_10 _) (OpI.sub (.i 8) (.inr rfl)) (by decide) <|
  .nil 14

/-- The stretch at `19`. -/
def p1 : List Byte := [
  0x41, 0x8b, 0x54, 0x24, 0x08, 0x85, 0xd2]

theorem p1_0 : ∀ feat, Dec feat p1 0 (FV7z.mk .mov 32 [gr 32 2, .mem (mg (some 12) none 1 8 32)] 5) := by dec_rfl
theorem p1_5 : ∀ feat, Dec feat p1 5 (FV7z.mk .test 32 [gr 32 2, Src.opd 32 (.r 2)] 2) := by dec_rfl

/-- What the stretch does. -/
def o1 : List Op := [
  Op.ld 32 2 (some 12) none 1 8,
  Op.test 32 2 (.r 2)]

theorem b1 (prof : Profile) : Blk prof p1 0 7 o1 :=
  .cons (p1_0 _) (OpI.ld (.inl rfl)) (by decide) <|
  .cons (p1_5 _) (OpI.test (.r 2) (.inl rfl)) (by decide) <|
  .nil 7

def j0 : List Byte := [0x74, 0x24]
theorem j0_0 : ∀ feat, Dec feat j0 0 (FV7z.mk (.jcc 4) 64 [.rel 36] 2) := by dec_rfl

/-- The stretch at `28`. -/
def p2 : List Byte := [
  0x4c, 0x89, 0xe7]

theorem p2_0 : ∀ feat, Dec feat p2 0 (FV7z.mk .mov 64 [gr 64 7, Src.opd 64 (.r 12)] 3) := by dec_rfl

/-- What the stretch does. -/
def o2 : List Op := [
  Op.mov 64 7 (.r 12)]

theorem b2 (prof : Profile) : Blk prof p2 0 3 o2 :=
  .cons (p2_0 _) (OpI.mov (.r 12) (.inr rfl)) (by decide) <|
  .nil 3

/-- The stretch at `36`. -/
def p3 : List Byte := [
  0x41, 0x8b, 0x44, 0x24, 0x08, 0x85, 0xc0]

theorem p3_0 : ∀ feat, Dec feat p3 0 (FV7z.mk .mov 32 [gr 32 0, .mem (mg (some 12) none 1 8 32)] 5) := by dec_rfl
theorem p3_5 : ∀ feat, Dec feat p3 5 (FV7z.mk .test 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl

/-- What the stretch does. -/
def o3 : List Op := [
  Op.ld 32 0 (some 12) none 1 8,
  Op.test 32 0 (.r 0)]

theorem b3 (prof : Profile) : Blk prof p3 0 7 o3 :=
  .cons (p3_0 _) (OpI.ld (.inl rfl)) (by decide) <|
  .cons (p3_5 _) (OpI.test (.r 0) (.inl rfl)) (by decide) <|
  .nil 7

def j1 : List Byte := [0x74, 0x13]
theorem j1_0 : ∀ feat, Dec feat j1 0 (FV7z.mk (.jcc 4) 64 [.rel 19] 2) := by dec_rfl

/-- The stretch at `45`. -/
def p4 : List Byte := [
  0x48, 0x83, 0xc4, 0x08, 0x4c, 0x89, 0xe0, 0x5d, 0x41, 0x5c]

theorem p4_0 : ∀ feat, Dec feat p4 0 (FV7z.mk .add 64 [gr 64 4, Src.opd 64 (.i 8)] 4) := by dec_rfl
theorem p4_4 : ∀ feat, Dec feat p4 4 (FV7z.mk .mov 64 [gr 64 0, Src.opd 64 (.r 12)] 3) := by dec_rfl
theorem p4_7 : ∀ feat, Dec feat p4 7 (FV7z.mk .pop 64 [gr 64 5] 1) := by dec_rfl
theorem p4_8 : ∀ feat, Dec feat p4 8 (FV7z.mk .pop 64 [gr 64 12] 2) := by dec_rfl

/-- What the stretch does. -/
def o4 : List Op := [
  Op.add 64 4 (.i 8),
  Op.mov 64 0 (.r 12),
  Op.pop 5,
  Op.pop 12]

theorem b4 (prof : Profile) : Blk prof p4 0 10 o4 :=
  .cons (p4_0 _) (OpI.add (.i 8) (.inr rfl)) (by decide) <|
  .cons (p4_4 _) (OpI.mov (.r 12) (.inr rfl)) (by decide) <|
  .cons (p4_7 _) (OpI.pop) (by decide) <|
  .cons (p4_8 _) (OpI.pop) (by decide) <|
  .nil 10

/-- The stretch at `64`. -/
def p5 : List Byte := [
  0xbe, 0x5f, 0x00, 0x00, 0x00, 0x4c, 0x89, 0xe7]

theorem p5_0 : ∀ feat, Dec feat p5 0 (FV7z.mk .mov 32 [gr 32 6, Src.opd 32 (.i 95)] 5) := by dec_rfl
theorem p5_5 : ∀ feat, Dec feat p5 5 (FV7z.mk .mov 64 [gr 64 7, Src.opd 64 (.r 12)] 3) := by dec_rfl

/-- What the stretch does. -/
def o5 : List Op := [
  Op.mov 32 6 (.i 95),
  Op.mov 64 7 (.r 12)]

theorem b5 (prof : Profile) : Blk prof p5 0 8 o5 :=
  .cons (p5_0 _) (OpI.mov (.i 95) (.inl rfl)) (by decide) <|
  .cons (p5_5 _) (OpI.mov (.r 12) (.inr rfl)) (by decide) <|
  .nil 8

end FV7z.Gcf
