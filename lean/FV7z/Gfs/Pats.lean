import FV7z.Lemmas.Sp
import FV7z.Lemmas.BlkOps2
/-!
# The stretches of straight-line code of `NWindows::NFile::NDir::GetFullPathAndSplit` (PLAN.md §M, M1)

Each distinct stretch between labels and jumps (`p*`, 8 of them) and each distinct jump (`j*`, 3) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.Gfs
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The stretch at `0`. -/
def p0 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0x41, 0x56, 0x41, 0x55, 0x49, 0x89, 0xd5, 0x41, 0x54, 0x55, 0x48, 0x89,
  0xfd, 0x53, 0x48, 0x89, 0xf3]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem p0_4 : ∀ feat, Dec feat p0 4 (FV7z.mk .push 64 [gr 64 14] 2) := by dec_rfl
theorem p0_6 : ∀ feat, Dec feat p0 6 (FV7z.mk .push 64 [gr 64 13] 2) := by dec_rfl
theorem p0_8 : ∀ feat, Dec feat p0 8 (FV7z.mk .mov 64 [gr 64 13, Src.opd 64 (.r 2)] 3) := by dec_rfl
theorem p0_11 : ∀ feat, Dec feat p0 11 (FV7z.mk .push 64 [gr 64 12] 2) := by dec_rfl
theorem p0_13 : ∀ feat, Dec feat p0 13 (FV7z.mk .push 64 [gr 64 5] 1) := by dec_rfl
theorem p0_14 : ∀ feat, Dec feat p0 14 (FV7z.mk .mov 64 [gr 64 5, Src.opd 64 (.r 7)] 3) := by dec_rfl
theorem p0_17 : ∀ feat, Dec feat p0 17 (FV7z.mk .push 64 [gr 64 3] 1) := by dec_rfl
theorem p0_18 : ∀ feat, Dec feat p0 18 (FV7z.mk .mov 64 [gr 64 3, Src.opd 64 (.r 6)] 3) := by dec_rfl

/-- What the stretch does. -/
def o0 : List Op := [
  Op.nop,
  Op.push 14,
  Op.push 13,
  Op.mov 64 13 (.r 2),
  Op.push 12,
  Op.push 5,
  Op.mov 64 5 (.r 7),
  Op.push 3,
  Op.mov 64 3 (.r 6)]

theorem b0 (prof : Profile) : Blk prof p0 0 21 o0 :=
  .cons (p0_0 _) (OpI.endbr) (by decide) <|
  .cons (p0_4 _) (OpI.push) (by decide) <|
  .cons (p0_6 _) (OpI.push) (by decide) <|
  .cons (p0_8 _) (OpI.mov (.r 2) (.inr rfl)) (by decide) <|
  .cons (p0_11 _) (OpI.push) (by decide) <|
  .cons (p0_13 _) (OpI.push) (by decide) <|
  .cons (p0_14 _) (OpI.mov (.r 7) (.inr rfl)) (by decide) <|
  .cons (p0_17 _) (OpI.push) (by decide) <|
  .cons (p0_18 _) (OpI.mov (.r 6) (.inr rfl)) (by decide) <|
  .nil 21

/-- The stretch at `26`. -/
def p1 : List Byte := [
  0x41, 0x89, 0xc4, 0x84, 0xc0]

theorem p1_0 : ∀ feat, Dec feat p1 0 (FV7z.mk .mov 32 [gr 32 12, Src.opd 32 (.r 0)] 3) := by dec_rfl
theorem p1_3 : ∀ feat, Dec feat p1 3 (FV7z.mk .test 8 [gr 8 0, Src.opd 8 (.r 0)] 2) := by dec_rfl

/-- What the stretch does. -/
def o1 : List Op := [
  Op.mov 32 12 (.r 0),
  Op.test 8 0 (.r 0)]

theorem b1 (prof : Profile) : Blk prof p1 0 5 o1 :=
  .cons (p1_0 _) (OpI.mov (.r 0) (.inl rfl)) (by decide) <|
  .cons (p1_3 _) (OpI.test8 (.r 0)) (by decide) <|
  .nil 5

def j0 : List Byte := [0x74, 0x3f]
theorem j0_0 : ∀ feat, Dec feat j0 0 (FV7z.mk (.jcc 4) 64 [.rel 63] 2) := by dec_rfl

/-- The stretch at `33`. -/
def p2 : List Byte := [
  0x48, 0x89, 0xdf]

theorem p2_0 : ∀ feat, Dec feat p2 0 (FV7z.mk .mov 64 [gr 64 7, Src.opd 64 (.r 3)] 3) := by dec_rfl

/-- What the stretch does. -/
def o2 : List Op := [
  Op.mov 64 7 (.r 3)]

theorem b2 (prof : Profile) : Blk prof p2 0 3 o2 :=
  .cons (p2_0 _) (OpI.mov (.r 3) (.inr rfl)) (by decide) <|
  .nil 3

/-- The stretch at `41`. -/
def p3 : List Byte := [
  0x48, 0x8b, 0x33, 0x4c, 0x89, 0xef, 0x44, 0x8d, 0x70, 0x01, 0x4c, 0x01, 0xf6]

theorem p3_0 : ∀ feat, Dec feat p3 0 (FV7z.mk .mov 64 [gr 64 6, .mem (mg (some 3) none 1 0 64)] 3) := by dec_rfl
theorem p3_3 : ∀ feat, Dec feat p3 3 (FV7z.mk .mov 64 [gr 64 7, Src.opd 64 (.r 13)] 3) := by dec_rfl
theorem p3_6 : ∀ feat, Dec feat p3 6 (FV7z.mk .lea 32 [gr 32 14, .mem (mg (some 0) none 1 1 0)] 4) := by dec_rfl
theorem p3_10 : ∀ feat, Dec feat p3 10 (FV7z.mk .add 64 [gr 64 6, Src.opd 64 (.r 14)] 3) := by dec_rfl

/-- What the stretch does. -/
def o3 : List Op := [
  Op.ld 64 6 (some 3) none 1 0,
  Op.mov 64 7 (.r 13),
  Op.lea 32 14 (some 0) none 1 1,
  Op.add 64 6 (.r 14)]

theorem b3 (prof : Profile) : Blk prof p3 0 13 o3 :=
  .cons (p3_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p3_3 _) (OpI.mov (.r 13) (.inr rfl)) (by decide) <|
  .cons (p3_6 _) (OpI.lea (.inl rfl)) (by decide) <|
  .cons (p3_10 _) (OpI.add (.r 14) (.inr rfl)) (by decide) <|
  .nil 13

/-- The stretch at `59`. -/
def p4 : List Byte := [
  0x44, 0x3b, 0x73, 0x08]

theorem p4_0 : ∀ feat, Dec feat p4 0 (FV7z.mk .cmp 32 [gr 32 14, .mem (mg (some 3) none 1 8 32)] 4) := by dec_rfl

/-- What the stretch does. -/
def o4 : List Op := [
  Op.cmpm 32 14 (some 3) none 1 8]

theorem b4 (prof : Profile) : Blk prof p4 0 4 o4 :=
  .cons (p4_0 _) (OpI.cmpm (.inl rfl)) (by decide) <|
  .nil 4

def j1 : List Byte := [0x73, 0x0c]
theorem j1_0 : ∀ feat, Dec feat j1 0 (FV7z.mk (.jcc 3) 64 [.rel 12] 2) := by dec_rfl

/-- The stretch at `65`. -/
def p5 : List Byte := [
  0x48, 0x8b, 0x03, 0x44, 0x89, 0x73, 0x08, 0x42, 0xc6, 0x04, 0x30, 0x00]

theorem p5_0 : ∀ feat, Dec feat p5 0 (FV7z.mk .mov 64 [gr 64 0, .mem (mg (some 3) none 1 0 64)] 3) := by dec_rfl
theorem p5_3 : ∀ feat, Dec feat p5 3 (FV7z.mk .mov 32 [.mem (mg (some 3) none 1 8 32), gr 32 14] 4) := by dec_rfl
theorem p5_7 : ∀ feat, Dec feat p5 7 (FV7z.mk .mov 8 [.mem (mg (some 0) (some 14) 1 0 8), .imm 8 0] 5) := by dec_rfl

/-- What the stretch does. -/
def o5 : List Op := [
  Op.ld 64 0 (some 3) none 1 0,
  Op.st 32 (some 3) none 1 8 14,
  Op.sti 8 (some 0) (some 14) 1 0 0]

theorem b5 (prof : Profile) : Blk prof p5 0 12 o5 :=
  .cons (p5_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p5_3 _) (OpI.st (.inr (.inr (.inl rfl)))) (by decide) <|
  .cons (p5_7 _) (OpI.sti (.inl rfl)) (by decide) <|
  .nil 12

/-- The stretch at `77`. -/
def p6 : List Byte := [
  0x5b, 0x44, 0x89, 0xe0, 0x5d, 0x41, 0x5c, 0x41, 0x5d, 0x41, 0x5e]

theorem p6_0 : ∀ feat, Dec feat p6 0 (FV7z.mk .pop 64 [gr 64 3] 1) := by dec_rfl
theorem p6_1 : ∀ feat, Dec feat p6 1 (FV7z.mk .mov 32 [gr 32 0, Src.opd 32 (.r 12)] 3) := by dec_rfl
theorem p6_4 : ∀ feat, Dec feat p6 4 (FV7z.mk .pop 64 [gr 64 5] 1) := by dec_rfl
theorem p6_5 : ∀ feat, Dec feat p6 5 (FV7z.mk .pop 64 [gr 64 12] 2) := by dec_rfl
theorem p6_7 : ∀ feat, Dec feat p6 7 (FV7z.mk .pop 64 [gr 64 13] 2) := by dec_rfl
theorem p6_9 : ∀ feat, Dec feat p6 9 (FV7z.mk .pop 64 [gr 64 14] 2) := by dec_rfl

/-- What the stretch does. -/
def o6 : List Op := [
  Op.pop 3,
  Op.mov 32 0 (.r 12),
  Op.pop 5,
  Op.pop 12,
  Op.pop 13,
  Op.pop 14]

theorem b6 (prof : Profile) : Blk prof p6 0 11 o6 :=
  .cons (p6_0 _) (OpI.pop) (by decide) <|
  .cons (p6_1 _) (OpI.mov (.r 12) (.inl rfl)) (by decide) <|
  .cons (p6_4 _) (OpI.pop) (by decide) <|
  .cons (p6_5 _) (OpI.pop) (by decide) <|
  .cons (p6_7 _) (OpI.pop) (by decide) <|
  .cons (p6_9 _) (OpI.pop) (by decide) <|
  .nil 11

/-- The stretch at `96`. -/
def p7 : List Byte := [
  0x48, 0x89, 0xee, 0x48, 0x89, 0xdf]

theorem p7_0 : ∀ feat, Dec feat p7 0 (FV7z.mk .mov 64 [gr 64 6, Src.opd 64 (.r 5)] 3) := by dec_rfl
theorem p7_3 : ∀ feat, Dec feat p7 3 (FV7z.mk .mov 64 [gr 64 7, Src.opd 64 (.r 3)] 3) := by dec_rfl

/-- What the stretch does. -/
def o7 : List Op := [
  Op.mov 64 6 (.r 5),
  Op.mov 64 7 (.r 3)]

theorem b7 (prof : Profile) : Blk prof p7 0 6 o7 :=
  .cons (p7_0 _) (OpI.mov (.r 5) (.inr rfl)) (by decide) <|
  .cons (p7_3 _) (OpI.mov (.r 3) (.inr rfl)) (by decide) <|
  .nil 6

def j2 : List Byte := [0xeb, 0xb4]
theorem j2_0 : ∀ feat, Dec feat j2 0 (FV7z.mk .jmp 64 [.rel 18446744073709551540] 2) := by dec_rfl

end FV7z.Gfs
