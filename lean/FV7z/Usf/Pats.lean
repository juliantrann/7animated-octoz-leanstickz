import FV7z.Lemmas.Sp
import FV7z.Lemmas.BlkOps12
import FV7z.Lemmas.BlkOps2
/-!
# The stretches of straight-line code of `UString::SetFrom` (PLAN.md §M, M1)

Each distinct stretch between labels and jumps (`p*`, 10 of them) and each distinct jump (`j*`, 4) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.Usf
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The stretch at `0`. -/
def p0 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0x41, 0x56, 0x41, 0x55, 0x49, 0x89, 0xf5, 0x41, 0x54, 0x55, 0x48, 0x89,
  0xfd, 0x53, 0x89, 0xd3, 0x39, 0x57, 0x0c]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem p0_4 : ∀ feat, Dec feat p0 4 (FV7z.mk .push 64 [gr 64 14] 2) := by dec_rfl
theorem p0_6 : ∀ feat, Dec feat p0 6 (FV7z.mk .push 64 [gr 64 13] 2) := by dec_rfl
theorem p0_8 : ∀ feat, Dec feat p0 8 (FV7z.mk .mov 64 [gr 64 13, Src.opd 64 (.r 6)] 3) := by dec_rfl
theorem p0_11 : ∀ feat, Dec feat p0 11 (FV7z.mk .push 64 [gr 64 12] 2) := by dec_rfl
theorem p0_13 : ∀ feat, Dec feat p0 13 (FV7z.mk .push 64 [gr 64 5] 1) := by dec_rfl
theorem p0_14 : ∀ feat, Dec feat p0 14 (FV7z.mk .mov 64 [gr 64 5, Src.opd 64 (.r 7)] 3) := by dec_rfl
theorem p0_17 : ∀ feat, Dec feat p0 17 (FV7z.mk .push 64 [gr 64 3] 1) := by dec_rfl
theorem p0_18 : ∀ feat, Dec feat p0 18 (FV7z.mk .mov 32 [gr 32 3, Src.opd 32 (.r 2)] 2) := by dec_rfl
theorem p0_20 : ∀ feat, Dec feat p0 20 (FV7z.mk .cmp 32 [.mem (mg (some 7) none 1 12 32), gr 32 2] 3) := by dec_rfl

/-- What the stretch does. -/
def o0 : List Op := [
  Op.nop,
  Op.push 14,
  Op.push 13,
  Op.mov 64 13 (.r 6),
  Op.push 12,
  Op.push 5,
  Op.mov 64 5 (.r 7),
  Op.push 3,
  Op.mov 32 3 (.r 2),
  Op.cmpmr 32 (some 7) none 1 12 2]

theorem b0 (prof : Profile) : Blk prof p0 0 23 o0 :=
  .cons (p0_0 _) (OpI.endbr) (by decide) <|
  .cons (p0_4 _) (OpI.push) (by decide) <|
  .cons (p0_6 _) (OpI.push) (by decide) <|
  .cons (p0_8 _) (OpI.mov (.r 6) (.inr rfl)) (by decide) <|
  .cons (p0_11 _) (OpI.push) (by decide) <|
  .cons (p0_13 _) (OpI.push) (by decide) <|
  .cons (p0_14 _) (OpI.mov (.r 7) (.inr rfl)) (by decide) <|
  .cons (p0_17 _) (OpI.push) (by decide) <|
  .cons (p0_18 _) (OpI.mov (.r 2) (.inl rfl)) (by decide) <|
  .cons (p0_20 _) (OpI.cmpmr (.inl rfl)) (by decide) <|
  .nil 23

def j0 : List Byte := [0x72, 0x37]
theorem j0_0 : ∀ feat, Dec feat j0 0 (FV7z.mk (.jcc 2) 64 [.rel 55] 2) := by dec_rfl

/-- The stretch at `25`. -/
def p1 : List Byte := [
  0x4c, 0x8b, 0x27, 0x41, 0x89, 0xd6]

theorem p1_0 : ∀ feat, Dec feat p1 0 (FV7z.mk .mov 64 [gr 64 12, .mem (mg (some 7) none 1 0 64)] 3) := by dec_rfl
theorem p1_3 : ∀ feat, Dec feat p1 3 (FV7z.mk .mov 32 [gr 32 14, Src.opd 32 (.r 2)] 3) := by dec_rfl

/-- What the stretch does. -/
def o1 : List Op := [
  Op.ld 64 12 (some 7) none 1 0,
  Op.mov 32 14 (.r 2)]

theorem b1 (prof : Profile) : Blk prof p1 0 6 o1 :=
  .cons (p1_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p1_3 _) (OpI.mov (.r 2) (.inl rfl)) (by decide) <|
  .nil 6

/-- The stretch at `31`. -/
def p2 : List Byte := [
  0x85, 0xdb]

theorem p2_0 : ∀ feat, Dec feat p2 0 (FV7z.mk .test 32 [gr 32 3, Src.opd 32 (.r 3)] 2) := by dec_rfl

/-- What the stretch does. -/
def o2 : List Op := [
  Op.test 32 3 (.r 3)]

theorem b2 (prof : Profile) : Blk prof p2 0 2 o2 :=
  .cons (p2_0 _) (OpI.test (.r 3) (.inl rfl)) (by decide) <|
  .nil 2

def j1 : List Byte := [0x74, 0x12]
theorem j1_0 : ∀ feat, Dec feat j1 0 (FV7z.mk (.jcc 4) 64 [.rel 18] 2) := by dec_rfl

/-- The stretch at `35`. -/
def p3 : List Byte := [
  0x4c, 0x89, 0xe7, 0x4c, 0x89, 0xf2, 0x4c, 0x89, 0xee]

theorem p3_0 : ∀ feat, Dec feat p3 0 (FV7z.mk .mov 64 [gr 64 7, Src.opd 64 (.r 12)] 3) := by dec_rfl
theorem p3_3 : ∀ feat, Dec feat p3 3 (FV7z.mk .mov 64 [gr 64 2, Src.opd 64 (.r 14)] 3) := by dec_rfl
theorem p3_6 : ∀ feat, Dec feat p3 6 (FV7z.mk .mov 64 [gr 64 6, Src.opd 64 (.r 13)] 3) := by dec_rfl

/-- What the stretch does. -/
def o3 : List Op := [
  Op.mov 64 7 (.r 12),
  Op.mov 64 2 (.r 14),
  Op.mov 64 6 (.r 13)]

theorem b3 (prof : Profile) : Blk prof p3 0 9 o3 :=
  .cons (p3_0 _) (OpI.mov (.r 12) (.inr rfl)) (by decide) <|
  .cons (p3_3 _) (OpI.mov (.r 14) (.inr rfl)) (by decide) <|
  .cons (p3_6 _) (OpI.mov (.r 13) (.inr rfl)) (by decide) <|
  .nil 9

/-- The stretch at `49`. -/
def p4 : List Byte := [
  0x4c, 0x8b, 0x65, 0x00]

theorem p4_0 : ∀ feat, Dec feat p4 0 (FV7z.mk .mov 64 [gr 64 12, .mem (mg (some 5) none 1 0 64)] 4) := by dec_rfl

/-- What the stretch does. -/
def o4 : List Op := [
  Op.ld 64 12 (some 5) none 1 0]

theorem b4 (prof : Profile) : Blk prof p4 0 4 o4 :=
  .cons (p4_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .nil 4

/-- The stretch at `53`. -/
def p5 : List Byte := [
  0x43, 0xc7, 0x04, 0xb4, 0x00, 0x00, 0x00, 0x00, 0x89, 0x5d, 0x08, 0x5b, 0x5d, 0x41, 0x5c, 0x41,
  0x5d, 0x41, 0x5e]

theorem p5_0 : ∀ feat, Dec feat p5 0 (FV7z.mk .mov 32 [.mem (mg (some 12) (some 14) 4 0 32), .imm 32 0] 8) := by dec_rfl
theorem p5_8 : ∀ feat, Dec feat p5 8 (FV7z.mk .mov 32 [.mem (mg (some 5) none 1 8 32), gr 32 3] 3) := by dec_rfl
theorem p5_11 : ∀ feat, Dec feat p5 11 (FV7z.mk .pop 64 [gr 64 3] 1) := by dec_rfl
theorem p5_12 : ∀ feat, Dec feat p5 12 (FV7z.mk .pop 64 [gr 64 5] 1) := by dec_rfl
theorem p5_13 : ∀ feat, Dec feat p5 13 (FV7z.mk .pop 64 [gr 64 12] 2) := by dec_rfl
theorem p5_15 : ∀ feat, Dec feat p5 15 (FV7z.mk .pop 64 [gr 64 13] 2) := by dec_rfl
theorem p5_17 : ∀ feat, Dec feat p5 17 (FV7z.mk .pop 64 [gr 64 14] 2) := by dec_rfl

/-- What the stretch does. -/
def o5 : List Op := [
  Op.sti 32 (some 12) (some 14) 4 0 0,
  Op.st 32 (some 5) none 1 8 3,
  Op.pop 3,
  Op.pop 5,
  Op.pop 12,
  Op.pop 13,
  Op.pop 14]

theorem b5 (prof : Profile) : Blk prof p5 0 19 o5 :=
  .cons (p5_0 _) (OpI.sti (.inr (.inr (.inl rfl)))) (by decide) <|
  .cons (p5_8 _) (OpI.st (.inr (.inr (.inl rfl)))) (by decide) <|
  .cons (p5_11 _) (OpI.pop) (by decide) <|
  .cons (p5_12 _) (OpI.pop) (by decide) <|
  .cons (p5_13 _) (OpI.pop) (by decide) <|
  .cons (p5_15 _) (OpI.pop) (by decide) <|
  .cons (p5_17 _) (OpI.pop) (by decide) <|
  .nil 19

/-- The stretch at `80`. -/
def p6 : List Byte := [
  0x81, 0xfa, 0xfe, 0xff, 0xff, 0x3f]

theorem p6_0 : ∀ feat, Dec feat p6 0 (FV7z.mk .cmp 32 [gr 32 2, Src.opd 32 (.i 1073741822)] 6) := by dec_rfl

/-- What the stretch does. -/
def o6 : List Op := [
  Op.cmp 32 2 (.i 1073741822)]

theorem b6 (prof : Profile) : Blk prof p6 0 6 o6 :=
  .cons (p6_0 _) (OpI.cmp (.i 1073741822) (.inl rfl)) (by decide) <|
  .nil 6

/-- The stretch at `92`. -/
def p7 : List Byte := [
  0x41, 0x89, 0xd6, 0x4a, 0x8d, 0x3c, 0xb5, 0x04, 0x00, 0x00, 0x00]

theorem p7_0 : ∀ feat, Dec feat p7 0 (FV7z.mk .mov 32 [gr 32 14, Src.opd 32 (.r 2)] 3) := by dec_rfl
theorem p7_3 : ∀ feat, Dec feat p7 3 (FV7z.mk .lea 64 [gr 64 7, .mem (mg none (some 14) 4 4 0)] 8) := by dec_rfl

/-- What the stretch does. -/
def o7 : List Op := [
  Op.mov 32 14 (.r 2),
  Op.lea 64 7 none (some 14) 4 4]

theorem b7 (prof : Profile) : Blk prof p7 0 11 o7 :=
  .cons (p7_0 _) (OpI.mov (.r 2) (.inl rfl)) (by decide) <|
  .cons (p7_3 _) (OpI.lea (.inr rfl)) (by decide) <|
  .nil 11

/-- The stretch at `108`. -/
def p8 : List Byte := [
  0x48, 0x8b, 0x7d, 0x00, 0x49, 0x89, 0xc4, 0x48, 0x85, 0xff]

theorem p8_0 : ∀ feat, Dec feat p8 0 (FV7z.mk .mov 64 [gr 64 7, .mem (mg (some 5) none 1 0 64)] 4) := by dec_rfl
theorem p8_4 : ∀ feat, Dec feat p8 4 (FV7z.mk .mov 64 [gr 64 12, Src.opd 64 (.r 0)] 3) := by dec_rfl
theorem p8_7 : ∀ feat, Dec feat p8 7 (FV7z.mk .test 64 [gr 64 7, Src.opd 64 (.r 7)] 3) := by dec_rfl

/-- What the stretch does. -/
def o8 : List Op := [
  Op.ld 64 7 (some 5) none 1 0,
  Op.mov 64 12 (.r 0),
  Op.test 64 7 (.r 7)]

theorem b8 (prof : Profile) : Blk prof p8 0 10 o8 :=
  .cons (p8_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p8_4 _) (OpI.mov (.r 0) (.inr rfl)) (by decide) <|
  .cons (p8_7 _) (OpI.test (.r 7) (.inr rfl)) (by decide) <|
  .nil 10

def j2 : List Byte := [0x74, 0x05]
theorem j2_0 : ∀ feat, Dec feat j2 0 (FV7z.mk (.jcc 4) 64 [.rel 5] 2) := by dec_rfl

/-- The stretch at `125`. -/
def p9 : List Byte := [
  0x4c, 0x89, 0x65, 0x00, 0x89, 0x5d, 0x0c]

theorem p9_0 : ∀ feat, Dec feat p9 0 (FV7z.mk .mov 64 [.mem (mg (some 5) none 1 0 64), gr 64 12] 4) := by dec_rfl
theorem p9_4 : ∀ feat, Dec feat p9 4 (FV7z.mk .mov 32 [.mem (mg (some 5) none 1 12 32), gr 32 3] 3) := by dec_rfl

/-- What the stretch does. -/
def o9 : List Op := [
  Op.st 64 (some 5) none 1 0 12,
  Op.st 32 (some 5) none 1 12 3]

theorem b9 (prof : Profile) : Blk prof p9 0 7 o9 :=
  .cons (p9_0 _) (OpI.st (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p9_4 _) (OpI.st (.inr (.inr (.inl rfl)))) (by decide) <|
  .nil 7

def j3 : List Byte := [0xeb, 0x99]
theorem j3_0 : ∀ feat, Dec feat j3 0 (FV7z.mk .jmp 64 [.rel 18446744073709551513] 2) := by dec_rfl

end FV7z.Usf
