import FV7z.Lemmas.Sp
import FV7z.Lemmas.BlkOps18
import FV7z.Lemmas.BlkOps14
import FV7z.Lemmas.BlkOps2
/-!
# The stretches of straight-line code of `CInFileStream::Read` (PLAN.md §M, M1)

Each distinct stretch between labels and jumps (`p*`, 11 of them) and each distinct jump (`j*`, 7) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.Ird
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The stretch at `0`. -/
def p0 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0x55, 0x89, 0xd2, 0x48, 0x89, 0xfd, 0x48, 0x83, 0xc7, 0x2c, 0x53, 0x48,
  0x83, 0xec, 0x08, 0x48, 0x85, 0xc9]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem p0_4 : ∀ feat, Dec feat p0 4 (FV7z.mk .push 64 [gr 64 5] 1) := by dec_rfl
theorem p0_5 : ∀ feat, Dec feat p0 5 (FV7z.mk .mov 32 [gr 32 2, Src.opd 32 (.r 2)] 2) := by dec_rfl
theorem p0_7 : ∀ feat, Dec feat p0 7 (FV7z.mk .mov 64 [gr 64 5, Src.opd 64 (.r 7)] 3) := by dec_rfl
theorem p0_10 : ∀ feat, Dec feat p0 10 (FV7z.mk .add 64 [gr 64 7, Src.opd 64 (.i 44)] 4) := by dec_rfl
theorem p0_14 : ∀ feat, Dec feat p0 14 (FV7z.mk .push 64 [gr 64 3] 1) := by dec_rfl
theorem p0_15 : ∀ feat, Dec feat p0 15 (FV7z.mk .sub 64 [gr 64 4, Src.opd 64 (.i 8)] 4) := by dec_rfl
theorem p0_19 : ∀ feat, Dec feat p0 19 (FV7z.mk .test 64 [gr 64 1, Src.opd 64 (.r 1)] 3) := by dec_rfl

/-- What the stretch does. -/
def o0 : List Op := [
  Op.nop,
  Op.push 5,
  Op.mov 32 2 (.r 2),
  Op.mov 64 5 (.r 7),
  Op.add 64 7 (.i 44),
  Op.push 3,
  Op.sub 64 4 (.i 8),
  Op.test 64 1 (.r 1)]

theorem b0 (prof : Profile) : Blk prof p0 0 22 o0 :=
  .cons (p0_0 _) (OpI.endbr) (by decide) <|
  .cons (p0_4 _) (OpI.push) (by decide) <|
  .cons (p0_5 _) (OpI.mov (.r 2) (.inl rfl)) (by decide) <|
  .cons (p0_7 _) (OpI.mov (.r 7) (.inr rfl)) (by decide) <|
  .cons (p0_10 _) (OpI.add (.i 44) (.inr rfl)) (by decide) <|
  .cons (p0_14 _) (OpI.push) (by decide) <|
  .cons (p0_15 _) (OpI.sub (.i 8) (.inr rfl)) (by decide) <|
  .cons (p0_19 _) (OpI.test (.r 1) (.inr rfl)) (by decide) <|
  .nil 22

def j0 : List Byte := [0x74, 0x28]
theorem j0_0 : ∀ feat, Dec feat j0 0 (FV7z.mk (.jcc 4) 64 [.rel 40] 2) := by dec_rfl

/-- The stretch at `24`. -/
def p1 : List Byte := [
  0xc7, 0x01, 0x00, 0x00, 0x00, 0x00, 0x48, 0x89, 0xcb]

theorem p1_0 : ∀ feat, Dec feat p1 0 (FV7z.mk .mov 32 [.mem (mg (some 1) none 1 0 32), .imm 32 0] 6) := by dec_rfl
theorem p1_6 : ∀ feat, Dec feat p1 6 (FV7z.mk .mov 64 [gr 64 3, Src.opd 64 (.r 1)] 3) := by dec_rfl

/-- What the stretch does. -/
def o1 : List Op := [
  Op.sti 32 (some 1) none 1 0 0,
  Op.mov 64 3 (.r 1)]

theorem b1 (prof : Profile) : Blk prof p1 0 9 o1 :=
  .cons (p1_0 _) (OpI.sti (.inr (.inr (.inl rfl)))) (by decide) <|
  .cons (p1_6 _) (OpI.mov (.r 1) (.inr rfl)) (by decide) <|
  .nil 9

/-- The stretch at `38`. -/
def p2 : List Byte := [
  0x48, 0x83, 0xf8, 0xff]

theorem p2_0 : ∀ feat, Dec feat p2 0 (FV7z.mk .cmp 64 [gr 64 0, Src.opd 64 (.i 18446744073709551615)] 4) := by dec_rfl

/-- What the stretch does. -/
def o2 : List Op := [
  Op.cmp 64 0 (.i 18446744073709551615)]

theorem b2 (prof : Profile) : Blk prof p2 0 4 o2 :=
  .cons (p2_0 _) (OpI.cmp (.i 18446744073709551615) (.inr rfl)) (by decide) <|
  .nil 4

def j1 : List Byte := [0x74, 0x24]
theorem j1_0 : ∀ feat, Dec feat j1 0 (FV7z.mk (.jcc 4) 64 [.rel 36] 2) := by dec_rfl

/-- The stretch at `44`. -/
def p3 : List Byte := [
  0x89, 0x03, 0x31, 0xc0]

theorem p3_0 : ∀ feat, Dec feat p3 0 (FV7z.mk .mov 32 [.mem (mg (some 3) none 1 0 32), gr 32 0] 2) := by dec_rfl
theorem p3_2 : ∀ feat, Dec feat p3 2 (FV7z.mk .xor 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl

/-- What the stretch does. -/
def o3 : List Op := [
  Op.st 32 (some 3) none 1 0 0,
  Op.xor 32 0 (.r 0)]

theorem b3 (prof : Profile) : Blk prof p3 0 4 o3 :=
  .cons (p3_0 _) (OpI.st (.inr (.inr (.inl rfl)))) (by decide) <|
  .cons (p3_2 _) (OpI.xor (.r 0) (.inl rfl)) (by decide) <|
  .nil 4

/-- The stretch at `48`. -/
def p4 : List Byte := [
  0x48, 0x83, 0xc4, 0x08, 0x5b, 0x5d]

theorem p4_0 : ∀ feat, Dec feat p4 0 (FV7z.mk .add 64 [gr 64 4, Src.opd 64 (.i 8)] 4) := by dec_rfl
theorem p4_4 : ∀ feat, Dec feat p4 4 (FV7z.mk .pop 64 [gr 64 3] 1) := by dec_rfl
theorem p4_5 : ∀ feat, Dec feat p4 5 (FV7z.mk .pop 64 [gr 64 5] 1) := by dec_rfl

/-- What the stretch does. -/
def o4 : List Op := [
  Op.add 64 4 (.i 8),
  Op.pop 3,
  Op.pop 5]

theorem b4 (prof : Profile) : Blk prof p4 0 6 o4 :=
  .cons (p4_0 _) (OpI.add (.i 8) (.inr rfl)) (by decide) <|
  .cons (p4_4 _) (OpI.pop) (by decide) <|
  .cons (p4_5 _) (OpI.pop) (by decide) <|
  .nil 6

/-- The stretch at `69`. -/
def p5 : List Byte := [
  0x49, 0x89, 0xc0, 0x31, 0xc0, 0x49, 0x83, 0xf8, 0xff]

theorem p5_0 : ∀ feat, Dec feat p5 0 (FV7z.mk .mov 64 [gr 64 8, Src.opd 64 (.r 0)] 3) := by dec_rfl
theorem p5_3 : ∀ feat, Dec feat p5 3 (FV7z.mk .xor 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl
theorem p5_5 : ∀ feat, Dec feat p5 5 (FV7z.mk .cmp 64 [gr 64 8, Src.opd 64 (.i 18446744073709551615)] 4) := by dec_rfl

/-- What the stretch does. -/
def o5 : List Op := [
  Op.mov 64 8 (.r 0),
  Op.xor 32 0 (.r 0),
  Op.cmp 64 8 (.i 18446744073709551615)]

theorem b5 (prof : Profile) : Blk prof p5 0 9 o5 :=
  .cons (p5_0 _) (OpI.mov (.r 0) (.inr rfl)) (by decide) <|
  .cons (p5_3 _) (OpI.xor (.r 0) (.inl rfl)) (by decide) <|
  .cons (p5_5 _) (OpI.cmp (.i 18446744073709551615) (.inr rfl)) (by decide) <|
  .nil 9

def j2 : List Byte := [0x75, 0xe0]
theorem j2_0 : ∀ feat, Dec feat j2 0 (FV7z.mk (.jcc 5) 64 [.rel 18446744073709551584] 2) := by dec_rfl

/-- The stretch at `85`. -/
def p6 : List Byte := [
  0x48, 0x8b, 0xbd, 0xf8, 0x00, 0x00, 0x00, 0x41, 0x89, 0xc0, 0x48, 0x85, 0xff]

theorem p6_0 : ∀ feat, Dec feat p6 0 (FV7z.mk .mov 64 [gr 64 7, .mem (mg (some 5) none 1 248 64)] 7) := by dec_rfl
theorem p6_7 : ∀ feat, Dec feat p6 7 (FV7z.mk .mov 32 [gr 32 8, Src.opd 32 (.r 0)] 3) := by dec_rfl
theorem p6_10 : ∀ feat, Dec feat p6 10 (FV7z.mk .test 64 [gr 64 7, Src.opd 64 (.r 7)] 3) := by dec_rfl

/-- What the stretch does. -/
def o6 : List Op := [
  Op.ld 64 7 (some 5) none 1 248,
  Op.mov 32 8 (.r 0),
  Op.test 64 7 (.r 7)]

theorem b6 (prof : Profile) : Blk prof p6 0 13 o6 :=
  .cons (p6_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p6_7 _) (OpI.mov (.r 0) (.inl rfl)) (by decide) <|
  .cons (p6_10 _) (OpI.test (.r 7) (.inr rfl)) (by decide) <|
  .nil 13

def j3 : List Byte := [0x74, 0x1c]
theorem j3_0 : ∀ feat, Dec feat j3 0 (FV7z.mk (.jcc 4) 64 [.rel 28] 2) := by dec_rfl

/-- The stretch at `100`. -/
def p7 : List Byte := [
  0x48, 0x8b, 0x07, 0x48, 0x8b, 0xb5, 0x00, 0x01, 0x00, 0x00, 0x44, 0x89, 0xc2]

theorem p7_0 : ∀ feat, Dec feat p7 0 (FV7z.mk .mov 64 [gr 64 0, .mem (mg (some 7) none 1 0 64)] 3) := by dec_rfl
theorem p7_3 : ∀ feat, Dec feat p7 3 (FV7z.mk .mov 64 [gr 64 6, .mem (mg (some 5) none 1 256 64)] 7) := by dec_rfl
theorem p7_10 : ∀ feat, Dec feat p7 10 (FV7z.mk .mov 32 [gr 32 2, Src.opd 32 (.r 8)] 3) := by dec_rfl

/-- What the stretch does. -/
def o7 : List Op := [
  Op.ld 64 0 (some 7) none 1 0,
  Op.ld 64 6 (some 5) none 1 256,
  Op.mov 32 2 (.r 8)]

theorem b7 (prof : Profile) : Blk prof p7 0 13 o7 :=
  .cons (p7_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p7_3 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p7_10 _) (OpI.mov (.r 8) (.inl rfl)) (by decide) <|
  .nil 13

/-- The stretch at `128`. -/
def p8 : List Byte := [
  0x85, 0xc0]

theorem p8_0 : ∀ feat, Dec feat p8 0 (FV7z.mk .test 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl

/-- What the stretch does. -/
def o8 : List Op := [
  Op.test 32 0 (.r 0)]

theorem b8 (prof : Profile) : Blk prof p8 0 2 o8 :=
  .cons (p8_0 _) (OpI.test (.r 0) (.inl rfl)) (by decide) <|
  .nil 2

def j4 : List Byte := [0x74, 0x15]
theorem j4_0 : ∀ feat, Dec feat j4 0 (FV7z.mk (.jcc 4) 64 [.rel 21] 2) := by dec_rfl

/-- The stretch at `132`. -/
def p9 : List Byte := [
  0x0f, 0xb7, 0xc0, 0x0d, 0x00, 0x00, 0x00, 0x88, 0x45, 0x85, 0xc0, 0x89, 0xc2, 0x44, 0x89, 0xc0,
  0x0f, 0x4f, 0xc2]

theorem p9_0 : ∀ feat, Dec feat p9 0 (FV7z.mk .movzx 32 [gr 32 0, gr 16 0] 3) := by dec_rfl
theorem p9_3 : ∀ feat, Dec feat p9 3 (FV7z.mk .or 32 [gr 32 0, Src.opd 32 (.i 2281701376)] 5) := by dec_rfl
theorem p9_8 : ∀ feat, Dec feat p9 8 (FV7z.mk .test 32 [gr 32 8, Src.opd 32 (.r 8)] 3) := by dec_rfl
theorem p9_11 : ∀ feat, Dec feat p9 11 (FV7z.mk .mov 32 [gr 32 2, Src.opd 32 (.r 0)] 2) := by dec_rfl
theorem p9_13 : ∀ feat, Dec feat p9 13 (FV7z.mk .mov 32 [gr 32 0, Src.opd 32 (.r 8)] 3) := by dec_rfl
theorem p9_16 : ∀ feat, Dec feat p9 16 (FV7z.mk (.cmovcc 15) 32 [gr 32 0, gr 32 2] 3) := by dec_rfl

/-- What the stretch does. -/
def o9 : List Op := [
  Op.zxr16 0 0,
  Op.or 32 0 (.i 2281701376),
  Op.test 32 8 (.r 8),
  Op.mov 32 2 (.r 0),
  Op.mov 32 0 (.r 8),
  Op.cmov32 15 0 2]

theorem b9 (prof : Profile) : Blk prof p9 0 19 o9 :=
  .cons (p9_0 _) (OpI.zxr16) (by decide) <|
  .cons (p9_3 _) (OpI.or (.i 2281701376) (.inl rfl)) (by decide) <|
  .cons (p9_8 _) (OpI.test (.r 8) (.inl rfl)) (by decide) <|
  .cons (p9_11 _) (OpI.mov (.r 0) (.inl rfl)) (by decide) <|
  .cons (p9_13 _) (OpI.mov (.r 8) (.inl rfl)) (by decide) <|
  .cons (p9_16 _) (OpI.cmov32) (by decide) <|
  .nil 19

def j5 : List Byte := [0xeb, 0x97]
theorem j5_0 : ∀ feat, Dec feat j5 0 (FV7z.mk .jmp 64 [.rel 18446744073709551511] 2) := by dec_rfl

/-- The stretch at `153`. -/
def p10 : List Byte := [
  0xb8, 0x05, 0x40, 0x00, 0x80]

theorem p10_0 : ∀ feat, Dec feat p10 0 (FV7z.mk .mov 32 [gr 32 0, Src.opd 32 (.i 2147500037)] 5) := by dec_rfl

/-- What the stretch does. -/
def o10 : List Op := [
  Op.mov 32 0 (.i 2147500037)]

theorem b10 (prof : Profile) : Blk prof p10 0 5 o10 :=
  .cons (p10_0 _) (OpI.mov (.i 2147500037) (.inl rfl)) (by decide) <|
  .nil 5

def j6 : List Byte := [0xeb, 0x90]
theorem j6_0 : ∀ feat, Dec feat j6 0 (FV7z.mk .jmp 64 [.rel 18446744073709551504] 2) := by dec_rfl

end FV7z.Ird
