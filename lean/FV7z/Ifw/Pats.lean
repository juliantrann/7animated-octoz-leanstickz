import FV7z.Lemmas.Sp
import FV7z.Lemmas.BlkOps12
import FV7z.Lemmas.BlkOps2
/-!
# The stretches of straight-line code of `_IO_new_file_write` (PLAN.md §M, M1)

Each distinct stretch between labels and jumps (`p*`, 11 of them) and each distinct jump (`j*`, 9) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.Ifw
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The stretch at `0`. -/
def p0 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0x41, 0x55, 0x49, 0x89, 0xfd, 0x41, 0x54, 0x55, 0x53, 0x48, 0x83, 0xec,
  0x08, 0x48, 0x85, 0xd2]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem p0_4 : ∀ feat, Dec feat p0 4 (FV7z.mk .push 64 [gr 64 13] 2) := by dec_rfl
theorem p0_6 : ∀ feat, Dec feat p0 6 (FV7z.mk .mov 64 [gr 64 13, Src.opd 64 (.r 7)] 3) := by dec_rfl
theorem p0_9 : ∀ feat, Dec feat p0 9 (FV7z.mk .push 64 [gr 64 12] 2) := by dec_rfl
theorem p0_11 : ∀ feat, Dec feat p0 11 (FV7z.mk .push 64 [gr 64 5] 1) := by dec_rfl
theorem p0_12 : ∀ feat, Dec feat p0 12 (FV7z.mk .push 64 [gr 64 3] 1) := by dec_rfl
theorem p0_13 : ∀ feat, Dec feat p0 13 (FV7z.mk .sub 64 [gr 64 4, Src.opd 64 (.i 8)] 4) := by dec_rfl
theorem p0_17 : ∀ feat, Dec feat p0 17 (FV7z.mk .test 64 [gr 64 2, Src.opd 64 (.r 2)] 3) := by dec_rfl

/-- What the stretch does. -/
def o0 : List Op := [
  Op.nop,
  Op.push 13,
  Op.mov 64 13 (.r 7),
  Op.push 12,
  Op.push 5,
  Op.push 3,
  Op.sub 64 4 (.i 8),
  Op.test 64 2 (.r 2)]

theorem b0 (prof : Profile) : Blk prof p0 0 20 o0 :=
  .cons (p0_0 _) (OpI.endbr) (by decide) <|
  .cons (p0_4 _) (OpI.push) (by decide) <|
  .cons (p0_6 _) (OpI.mov (.r 7) (.inr rfl)) (by decide) <|
  .cons (p0_9 _) (OpI.push) (by decide) <|
  .cons (p0_11 _) (OpI.push) (by decide) <|
  .cons (p0_12 _) (OpI.push) (by decide) <|
  .cons (p0_13 _) (OpI.sub (.i 8) (.inr rfl)) (by decide) <|
  .cons (p0_17 _) (OpI.test (.r 2) (.inr rfl)) (by decide) <|
  .nil 20

def j0 : List Byte := [0x0f, 0x8e, 0x7e, 0x00, 0x00, 0x00]
theorem j0_0 : ∀ feat, Dec feat j0 0 (FV7z.mk (.jcc 14) 64 [.rel 126] 6) := by dec_rfl

/-- The stretch at `26`. -/
def p1 : List Byte := [
  0x48, 0x89, 0xf5, 0x49, 0x89, 0xd4, 0x48, 0x89, 0xd3]

theorem p1_0 : ∀ feat, Dec feat p1 0 (FV7z.mk .mov 64 [gr 64 5, Src.opd 64 (.r 6)] 3) := by dec_rfl
theorem p1_3 : ∀ feat, Dec feat p1 3 (FV7z.mk .mov 64 [gr 64 12, Src.opd 64 (.r 2)] 3) := by dec_rfl
theorem p1_6 : ∀ feat, Dec feat p1 6 (FV7z.mk .mov 64 [gr 64 3, Src.opd 64 (.r 2)] 3) := by dec_rfl

/-- What the stretch does. -/
def o1 : List Op := [
  Op.mov 64 5 (.r 6),
  Op.mov 64 12 (.r 2),
  Op.mov 64 3 (.r 2)]

theorem b1 (prof : Profile) : Blk prof p1 0 9 o1 :=
  .cons (p1_0 _) (OpI.mov (.r 6) (.inr rfl)) (by decide) <|
  .cons (p1_3 _) (OpI.mov (.r 2) (.inr rfl)) (by decide) <|
  .cons (p1_6 _) (OpI.mov (.r 2) (.inr rfl)) (by decide) <|
  .nil 9

def j1 : List Byte := [0xeb, 0x18]
theorem j1_0 : ∀ feat, Dec feat j1 0 (FV7z.mk .jmp 64 [.rel 24] 2) := by dec_rfl

/-- The stretch at `45`. -/
def p2 : List Byte := [
  0x48, 0x85, 0xc0]

theorem p2_0 : ∀ feat, Dec feat p2 0 (FV7z.mk .test 64 [gr 64 0, Src.opd 64 (.r 0)] 3) := by dec_rfl

/-- What the stretch does. -/
def o2 : List Op := [
  Op.test 64 0 (.r 0)]

theorem b2 (prof : Profile) : Blk prof p2 0 3 o2 :=
  .cons (p2_0 _) (OpI.test (.r 0) (.inr rfl)) (by decide) <|
  .nil 3

def j2 : List Byte := [0x78, 0x2e]
theorem j2_0 : ∀ feat, Dec feat j2 0 (FV7z.mk (.jcc 8) 64 [.rel 46] 2) := by dec_rfl

/-- The stretch at `50`. -/
def p3 : List Byte := [
  0x48, 0x29, 0xc3, 0x48, 0x01, 0xc5, 0x48, 0x85, 0xdb]

theorem p3_0 : ∀ feat, Dec feat p3 0 (FV7z.mk .sub 64 [gr 64 3, Src.opd 64 (.r 0)] 3) := by dec_rfl
theorem p3_3 : ∀ feat, Dec feat p3 3 (FV7z.mk .add 64 [gr 64 5, Src.opd 64 (.r 0)] 3) := by dec_rfl
theorem p3_6 : ∀ feat, Dec feat p3 6 (FV7z.mk .test 64 [gr 64 3, Src.opd 64 (.r 3)] 3) := by dec_rfl

/-- What the stretch does. -/
def o3 : List Op := [
  Op.sub 64 3 (.r 0),
  Op.add 64 5 (.r 0),
  Op.test 64 3 (.r 3)]

theorem b3 (prof : Profile) : Blk prof p3 0 9 o3 :=
  .cons (p3_0 _) (OpI.sub (.r 0) (.inr rfl)) (by decide) <|
  .cons (p3_3 _) (OpI.add (.r 0) (.inr rfl)) (by decide) <|
  .cons (p3_6 _) (OpI.test (.r 3) (.inr rfl)) (by decide) <|
  .nil 9

def j3 : List Byte := [0x7e, 0x53]
theorem j3_0 : ∀ feat, Dec feat j3 0 (FV7z.mk (.jcc 14) 64 [.rel 83] 2) := by dec_rfl

/-- The stretch at `61`. -/
def p4 : List Byte := [
  0x41, 0x8b, 0x7d, 0x70, 0x48, 0x89, 0xda, 0x48, 0x89, 0xee, 0x41, 0xf6, 0x45, 0x74, 0x02]

theorem p4_0 : ∀ feat, Dec feat p4 0 (FV7z.mk .mov 32 [gr 32 7, .mem (mg (some 13) none 1 112 32)] 4) := by dec_rfl
theorem p4_4 : ∀ feat, Dec feat p4 4 (FV7z.mk .mov 64 [gr 64 2, Src.opd 64 (.r 3)] 3) := by dec_rfl
theorem p4_7 : ∀ feat, Dec feat p4 7 (FV7z.mk .mov 64 [gr 64 6, Src.opd 64 (.r 5)] 3) := by dec_rfl
theorem p4_10 : ∀ feat, Dec feat p4 10 (FV7z.mk .test 8 [.mem (mg (some 13) none 1 116 8), .imm 8 2] 5) := by dec_rfl

/-- What the stretch does. -/
def o4 : List Op := [
  Op.ld 32 7 (some 13) none 1 112,
  Op.mov 64 2 (.r 3),
  Op.mov 64 6 (.r 5),
  Op.testmi 8 (some 13) none 1 116 2]

theorem b4 (prof : Profile) : Blk prof p4 0 15 o4 :=
  .cons (p4_0 _) (OpI.ld (.inl rfl)) (by decide) <|
  .cons (p4_4 _) (OpI.mov (.r 3) (.inr rfl)) (by decide) <|
  .cons (p4_7 _) (OpI.mov (.r 5) (.inr rfl)) (by decide) <|
  .cons (p4_10 _) (OpI.testmi8) (by decide) <|
  .nil 15

def j4 : List Byte := [0x74, 0xda]
theorem j4_0 : ∀ feat, Dec feat j4 0 (FV7z.mk (.jcc 4) 64 [.rel 18446744073709551578] 2) := by dec_rfl

def j5 : List Byte := [0x79, 0xda]
theorem j5_0 : ∀ feat, Dec feat j5 0 (FV7z.mk (.jcc 9) 64 [.rel 18446744073709551578] 2) := by dec_rfl

/-- The stretch at `88`. -/
def p5 : List Byte := [
  0x0f, 0x1f, 0x84, 0x00, 0x00, 0x00, 0x00, 0x00]

theorem p5_0 : ∀ feat, Dec feat p5 0 (FV7z.mk .nop 32 [.mem (mg (some 0) (some 0) 1 0 32)] 8) := by dec_rfl

/-- What the stretch does. -/
def o5 : List Op := [
  Op.nop]

theorem b5 (prof : Profile) : Blk prof p5 0 8 o5 :=
  .cons (p5_0 _) (OpI.nop) (by decide) <|
  .nil 8

/-- The stretch at `101`. -/
def p6 : List Byte := [
  0x4c, 0x89, 0xe0, 0x48, 0x29, 0xd8]

theorem p6_0 : ∀ feat, Dec feat p6 0 (FV7z.mk .mov 64 [gr 64 0, Src.opd 64 (.r 12)] 3) := by dec_rfl
theorem p6_3 : ∀ feat, Dec feat p6 3 (FV7z.mk .sub 64 [gr 64 0, Src.opd 64 (.r 3)] 3) := by dec_rfl

/-- What the stretch does. -/
def o6 : List Op := [
  Op.mov 64 0 (.r 12),
  Op.sub 64 0 (.r 3)]

theorem b6 (prof : Profile) : Blk prof p6 0 6 o6 :=
  .cons (p6_0 _) (OpI.mov (.r 12) (.inr rfl)) (by decide) <|
  .cons (p6_3 _) (OpI.sub (.r 3) (.inr rfl)) (by decide) <|
  .nil 6

/-- The stretch at `107`. -/
def p7 : List Byte := [
  0x49, 0x8b, 0x95, 0x90, 0x00, 0x00, 0x00, 0x48, 0x85, 0xd2]

theorem p7_0 : ∀ feat, Dec feat p7 0 (FV7z.mk .mov 64 [gr 64 2, .mem (mg (some 13) none 1 144 64)] 7) := by dec_rfl
theorem p7_7 : ∀ feat, Dec feat p7 7 (FV7z.mk .test 64 [gr 64 2, Src.opd 64 (.r 2)] 3) := by dec_rfl

/-- What the stretch does. -/
def o7 : List Op := [
  Op.ld 64 2 (some 13) none 1 144,
  Op.test 64 2 (.r 2)]

theorem b7 (prof : Profile) : Blk prof p7 0 10 o7 :=
  .cons (p7_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p7_7 _) (OpI.test (.r 2) (.inr rfl)) (by decide) <|
  .nil 10

def j6 : List Byte := [0x78, 0x0a]
theorem j6_0 : ∀ feat, Dec feat j6 0 (FV7z.mk (.jcc 8) 64 [.rel 10] 2) := by dec_rfl

/-- The stretch at `119`. -/
def p8 : List Byte := [
  0x48, 0x01, 0xc2, 0x49, 0x89, 0x95, 0x90, 0x00, 0x00, 0x00]

theorem p8_0 : ∀ feat, Dec feat p8 0 (FV7z.mk .add 64 [gr 64 2, Src.opd 64 (.r 0)] 3) := by dec_rfl
theorem p8_3 : ∀ feat, Dec feat p8 3 (FV7z.mk .mov 64 [.mem (mg (some 13) none 1 144 64), gr 64 2] 7) := by dec_rfl

/-- What the stretch does. -/
def o8 : List Op := [
  Op.add 64 2 (.r 0),
  Op.st 64 (some 13) none 1 144 2]

theorem b8 (prof : Profile) : Blk prof p8 0 10 o8 :=
  .cons (p8_0 _) (OpI.add (.r 0) (.inr rfl)) (by decide) <|
  .cons (p8_3 _) (OpI.st (.inr (.inr (.inr rfl)))) (by decide) <|
  .nil 10

/-- The stretch at `129`. -/
def p9 : List Byte := [
  0x48, 0x83, 0xc4, 0x08, 0x5b, 0x5d, 0x41, 0x5c, 0x41, 0x5d]

theorem p9_0 : ∀ feat, Dec feat p9 0 (FV7z.mk .add 64 [gr 64 4, Src.opd 64 (.i 8)] 4) := by dec_rfl
theorem p9_4 : ∀ feat, Dec feat p9 4 (FV7z.mk .pop 64 [gr 64 3] 1) := by dec_rfl
theorem p9_5 : ∀ feat, Dec feat p9 5 (FV7z.mk .pop 64 [gr 64 5] 1) := by dec_rfl
theorem p9_6 : ∀ feat, Dec feat p9 6 (FV7z.mk .pop 64 [gr 64 12] 2) := by dec_rfl
theorem p9_8 : ∀ feat, Dec feat p9 8 (FV7z.mk .pop 64 [gr 64 13] 2) := by dec_rfl

/-- What the stretch does. -/
def o9 : List Op := [
  Op.add 64 4 (.i 8),
  Op.pop 3,
  Op.pop 5,
  Op.pop 12,
  Op.pop 13]

theorem b9 (prof : Profile) : Blk prof p9 0 10 o9 :=
  .cons (p9_0 _) (OpI.add (.i 8) (.inr rfl)) (by decide) <|
  .cons (p9_4 _) (OpI.pop) (by decide) <|
  .cons (p9_5 _) (OpI.pop) (by decide) <|
  .cons (p9_6 _) (OpI.pop) (by decide) <|
  .cons (p9_8 _) (OpI.pop) (by decide) <|
  .nil 10

def j7 : List Byte := [0xeb, 0xd3]
theorem j7_0 : ∀ feat, Dec feat j7 0 (FV7z.mk .jmp 64 [.rel 18446744073709551571] 2) := by dec_rfl

/-- The stretch at `152`. -/
def p10 : List Byte := [
  0x31, 0xc0]

theorem p10_0 : ∀ feat, Dec feat p10 0 (FV7z.mk .xor 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl

/-- What the stretch does. -/
def o10 : List Op := [
  Op.xor 32 0 (.r 0)]

theorem b10 (prof : Profile) : Blk prof p10 0 2 o10 :=
  .cons (p10_0 _) (OpI.xor (.r 0) (.inl rfl)) (by decide) <|
  .nil 2

def j8 : List Byte := [0xeb, 0xcf]
theorem j8_0 : ∀ feat, Dec feat j8 0 (FV7z.mk .jmp 64 [.rel 18446744073709551567] 2) := by dec_rfl

end FV7z.Ifw
