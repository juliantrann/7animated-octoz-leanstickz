import FV7z.Lemmas.Sp
import FV7z.Lemmas.BlkOps3
/-!
# The stretches of straight-line code of `CArchiveLink::Release` (PLAN.md §M, M1)

Each distinct stretch between labels and jumps (`p*`, 34 of them) and each distinct jump (`j*`, 12) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.Alr
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The stretch at `0`. -/
def p0 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0x41, 0x56, 0x41, 0x55, 0x49, 0x89, 0xfd, 0x48, 0x83, 0xc7, 0x40, 0x41,
  0x54, 0x55, 0x53]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem p0_4 : ∀ feat, Dec feat p0 4 (FV7z.mk .push 64 [gr 64 14] 2) := by dec_rfl
theorem p0_6 : ∀ feat, Dec feat p0 6 (FV7z.mk .push 64 [gr 64 13] 2) := by dec_rfl
theorem p0_8 : ∀ feat, Dec feat p0 8 (FV7z.mk .mov 64 [gr 64 13, Src.opd 64 (.r 7)] 3) := by dec_rfl
theorem p0_11 : ∀ feat, Dec feat p0 11 (FV7z.mk .add 64 [gr 64 7, Src.opd 64 (.i 64)] 4) := by dec_rfl
theorem p0_15 : ∀ feat, Dec feat p0 15 (FV7z.mk .push 64 [gr 64 12] 2) := by dec_rfl
theorem p0_17 : ∀ feat, Dec feat p0 17 (FV7z.mk .push 64 [gr 64 5] 1) := by dec_rfl
theorem p0_18 : ∀ feat, Dec feat p0 18 (FV7z.mk .push 64 [gr 64 3] 1) := by dec_rfl

/-- What the stretch does. -/
def o0 : List Op := [
  Op.nop,
  Op.push 14,
  Op.push 13,
  Op.mov 64 13 (.r 7),
  Op.add 64 7 (.i 64),
  Op.push 12,
  Op.push 5,
  Op.push 3]

theorem b0 (prof : Profile) : Blk prof p0 0 19 o0 :=
  .cons (p0_0 _) (OpI.endbr) (by decide) <|
  .cons (p0_4 _) (OpI.push) (by decide) <|
  .cons (p0_6 _) (OpI.push) (by decide) <|
  .cons (p0_8 _) (OpI.mov (.r 7) (.inr rfl)) (by decide) <|
  .cons (p0_11 _) (OpI.add (.i 64) (.inr rfl)) (by decide) <|
  .cons (p0_15 _) (OpI.push) (by decide) <|
  .cons (p0_17 _) (OpI.push) (by decide) <|
  .cons (p0_18 _) (OpI.push) (by decide) <|
  .nil 19

/-- The stretch at `24`. -/
def p1 : List Byte := [
  0x49, 0x8b, 0x45, 0x30, 0x41, 0xc7, 0x45, 0x38, 0x00, 0x00, 0x00, 0x00, 0xc7, 0x00, 0x00, 0x00,
  0x00, 0x00, 0x41, 0x8b, 0x45, 0x08, 0x85, 0xc0]

theorem p1_0 : ∀ feat, Dec feat p1 0 (FV7z.mk .mov 64 [gr 64 0, .mem (mg (some 13) none 1 48 64)] 4) := by dec_rfl
theorem p1_4 : ∀ feat, Dec feat p1 4 (FV7z.mk .mov 32 [.mem (mg (some 13) none 1 56 32), .imm 32 0] 8) := by dec_rfl
theorem p1_12 : ∀ feat, Dec feat p1 12 (FV7z.mk .mov 32 [.mem (mg (some 0) none 1 0 32), .imm 32 0] 6) := by dec_rfl
theorem p1_18 : ∀ feat, Dec feat p1 18 (FV7z.mk .mov 32 [gr 32 0, .mem (mg (some 13) none 1 8 32)] 4) := by dec_rfl
theorem p1_22 : ∀ feat, Dec feat p1 22 (FV7z.mk .test 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl

/-- What the stretch does. -/
def o1 : List Op := [
  Op.ld 64 0 (some 13) none 1 48,
  Op.sti 32 (some 13) none 1 56 0,
  Op.sti 32 (some 0) none 1 0 0,
  Op.ld 32 0 (some 13) none 1 8,
  Op.test 32 0 (.r 0)]

theorem b1 (prof : Profile) : Blk prof p1 0 24 o1 :=
  .cons (p1_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p1_4 _) (OpI.sti (.inr (.inr (.inl rfl)))) (by decide) <|
  .cons (p1_12 _) (OpI.sti (.inr (.inr (.inl rfl)))) (by decide) <|
  .cons (p1_18 _) (OpI.ld (.inl rfl)) (by decide) <|
  .cons (p1_22 _) (OpI.test (.r 0) (.inl rfl)) (by decide) <|
  .nil 24

def j0 : List Byte := [0x0f, 0x84, 0xb7, 0x01, 0x00, 0x00]
theorem j0_0 : ∀ feat, Dec feat j0 0 (FV7z.mk (.jcc 4) 64 [.rel 439] 6) := by dec_rfl

/-- The stretch at `54`. -/
def p2 : List Byte := [
  0x66, 0x2e, 0x0f, 0x1f, 0x84, 0x00, 0x00, 0x00, 0x00, 0x00]

theorem p2_0 : ∀ feat, Dec feat p2 0 (FV7z.mk .nop 16 [.mem (mg (some 0) (some 0) 1 0 16)] 10) := by dec_rfl

/-- What the stretch does. -/
def o2 : List Op := [
  Op.nop]

theorem b2 (prof : Profile) : Blk prof p2 0 10 o2 :=
  .cons (p2_0 _) (OpI.nop) (by decide) <|
  .nil 10

/-- The stretch at `64`. -/
def p3 : List Byte := [
  0x49, 0x8b, 0x55, 0x00, 0x48, 0x8b, 0x6c, 0xc2, 0xf8, 0x48, 0x85, 0xed]

theorem p3_0 : ∀ feat, Dec feat p3 0 (FV7z.mk .mov 64 [gr 64 2, .mem (mg (some 13) none 1 0 64)] 4) := by dec_rfl
theorem p3_4 : ∀ feat, Dec feat p3 4 (FV7z.mk .mov 64 [gr 64 5, .mem (mg (some 2) (some 0) 8 18446744073709551608 64)] 5) := by dec_rfl
theorem p3_9 : ∀ feat, Dec feat p3 9 (FV7z.mk .test 64 [gr 64 5, Src.opd 64 (.r 5)] 3) := by dec_rfl

/-- What the stretch does. -/
def o3 : List Op := [
  Op.ld 64 2 (some 13) none 1 0,
  Op.ld 64 5 (some 2) (some 0) 8 18446744073709551608,
  Op.test 64 5 (.r 5)]

theorem b3 (prof : Profile) : Blk prof p3 0 12 o3 :=
  .cons (p3_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p3_4 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p3_9 _) (OpI.test (.r 5) (.inr rfl)) (by decide) <|
  .nil 12

def j1 : List Byte := [0x0f, 0x84, 0x8a, 0x01, 0x00, 0x00]
theorem j1_0 : ∀ feat, Dec feat j1 0 (FV7z.mk (.jcc 4) 64 [.rel 394] 6) := by dec_rfl

/-- The stretch at `82`. -/
def p4 : List Byte := [
  0x48, 0x8b, 0xbd, 0xf8, 0x00, 0x00, 0x00, 0x48, 0x85, 0xff]

theorem p4_0 : ∀ feat, Dec feat p4 0 (FV7z.mk .mov 64 [gr 64 7, .mem (mg (some 5) none 1 248 64)] 7) := by dec_rfl
theorem p4_7 : ∀ feat, Dec feat p4 7 (FV7z.mk .test 64 [gr 64 7, Src.opd 64 (.r 7)] 3) := by dec_rfl

/-- What the stretch does. -/
def o4 : List Op := [
  Op.ld 64 7 (some 5) none 1 248,
  Op.test 64 7 (.r 7)]

theorem b4 (prof : Profile) : Blk prof p4 0 10 o4 :=
  .cons (p4_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p4_7 _) (OpI.test (.r 7) (.inr rfl)) (by decide) <|
  .nil 10

def j2 : List Byte := [0x74, 0x05]
theorem j2_0 : ∀ feat, Dec feat j2 0 (FV7z.mk (.jcc 4) 64 [.rel 5] 2) := by dec_rfl

/-- The stretch at `99`. -/
def p5 : List Byte := [
  0x48, 0x8b, 0xbd, 0xe8, 0x00, 0x00, 0x00, 0x48, 0x85, 0xff]

theorem p5_0 : ∀ feat, Dec feat p5 0 (FV7z.mk .mov 64 [gr 64 7, .mem (mg (some 5) none 1 232 64)] 7) := by dec_rfl
theorem p5_7 : ∀ feat, Dec feat p5 7 (FV7z.mk .test 64 [gr 64 7, Src.opd 64 (.r 7)] 3) := by dec_rfl

/-- What the stretch does. -/
def o5 : List Op := [
  Op.ld 64 7 (some 5) none 1 232,
  Op.test 64 7 (.r 7)]

theorem b5 (prof : Profile) : Blk prof p5 0 10 o5 :=
  .cons (p5_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p5_7 _) (OpI.test (.r 7) (.inr rfl)) (by decide) <|
  .nil 10

/-- The stretch at `116`. -/
def p6 : List Byte := [
  0x48, 0x8b, 0xbd, 0xc0, 0x00, 0x00, 0x00, 0x48, 0x85, 0xff]

theorem p6_0 : ∀ feat, Dec feat p6 0 (FV7z.mk .mov 64 [gr 64 7, .mem (mg (some 5) none 1 192 64)] 7) := by dec_rfl
theorem p6_7 : ∀ feat, Dec feat p6 7 (FV7z.mk .test 64 [gr 64 7, Src.opd 64 (.r 7)] 3) := by dec_rfl

/-- What the stretch does. -/
def o6 : List Op := [
  Op.ld 64 7 (some 5) none 1 192,
  Op.test 64 7 (.r 7)]

theorem b6 (prof : Profile) : Blk prof p6 0 10 o6 :=
  .cons (p6_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p6_7 _) (OpI.test (.r 7) (.inr rfl)) (by decide) <|
  .nil 10

/-- The stretch at `133`. -/
def p7 : List Byte := [
  0x48, 0x8b, 0xbd, 0xb0, 0x00, 0x00, 0x00, 0x48, 0x85, 0xff]

theorem p7_0 : ∀ feat, Dec feat p7 0 (FV7z.mk .mov 64 [gr 64 7, .mem (mg (some 5) none 1 176 64)] 7) := by dec_rfl
theorem p7_7 : ∀ feat, Dec feat p7 7 (FV7z.mk .test 64 [gr 64 7, Src.opd 64 (.r 7)] 3) := by dec_rfl

/-- What the stretch does. -/
def o7 : List Op := [
  Op.ld 64 7 (some 5) none 1 176,
  Op.test 64 7 (.r 7)]

theorem b7 (prof : Profile) : Blk prof p7 0 10 o7 :=
  .cons (p7_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p7_7 _) (OpI.test (.r 7) (.inr rfl)) (by decide) <|
  .nil 10

/-- The stretch at `150`. -/
def p8 : List Byte := [
  0x48, 0x8b, 0x7d, 0x48, 0x48, 0x85, 0xff]

theorem p8_0 : ∀ feat, Dec feat p8 0 (FV7z.mk .mov 64 [gr 64 7, .mem (mg (some 5) none 1 72 64)] 4) := by dec_rfl
theorem p8_4 : ∀ feat, Dec feat p8 4 (FV7z.mk .test 64 [gr 64 7, Src.opd 64 (.r 7)] 3) := by dec_rfl

/-- What the stretch does. -/
def o8 : List Op := [
  Op.ld 64 7 (some 5) none 1 72,
  Op.test 64 7 (.r 7)]

theorem b8 (prof : Profile) : Blk prof p8 0 7 o8 :=
  .cons (p8_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p8_4 _) (OpI.test (.r 7) (.inr rfl)) (by decide) <|
  .nil 7

/-- The stretch at `164`. -/
def p9 : List Byte := [
  0x48, 0x8b, 0x7d, 0x38, 0x48, 0x85, 0xff]

theorem p9_0 : ∀ feat, Dec feat p9 0 (FV7z.mk .mov 64 [gr 64 7, .mem (mg (some 5) none 1 56 64)] 4) := by dec_rfl
theorem p9_4 : ∀ feat, Dec feat p9 4 (FV7z.mk .test 64 [gr 64 7, Src.opd 64 (.r 7)] 3) := by dec_rfl

/-- What the stretch does. -/
def o9 : List Op := [
  Op.ld 64 7 (some 5) none 1 56,
  Op.test 64 7 (.r 7)]

theorem b9 (prof : Profile) : Blk prof p9 0 7 o9 :=
  .cons (p9_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p9_4 _) (OpI.test (.r 7) (.inr rfl)) (by decide) <|
  .nil 7

/-- The stretch at `178`. -/
def p10 : List Byte := [
  0x48, 0x8b, 0x7d, 0x28, 0x48, 0x85, 0xff]

theorem p10_0 : ∀ feat, Dec feat p10 0 (FV7z.mk .mov 64 [gr 64 7, .mem (mg (some 5) none 1 40 64)] 4) := by dec_rfl
theorem p10_4 : ∀ feat, Dec feat p10 4 (FV7z.mk .test 64 [gr 64 7, Src.opd 64 (.r 7)] 3) := by dec_rfl

/-- What the stretch does. -/
def o10 : List Op := [
  Op.ld 64 7 (some 5) none 1 40,
  Op.test 64 7 (.r 7)]

theorem b10 (prof : Profile) : Blk prof p10 0 7 o10 :=
  .cons (p10_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p10_4 _) (OpI.test (.r 7) (.inr rfl)) (by decide) <|
  .nil 7

/-- The stretch at `192`. -/
def p11 : List Byte := [
  0x48, 0x8b, 0x7d, 0x18, 0x48, 0x85, 0xff]

theorem p11_0 : ∀ feat, Dec feat p11 0 (FV7z.mk .mov 64 [gr 64 7, .mem (mg (some 5) none 1 24 64)] 4) := by dec_rfl
theorem p11_4 : ∀ feat, Dec feat p11 4 (FV7z.mk .test 64 [gr 64 7, Src.opd 64 (.r 7)] 3) := by dec_rfl

/-- What the stretch does. -/
def o11 : List Op := [
  Op.ld 64 7 (some 5) none 1 24,
  Op.test 64 7 (.r 7)]

theorem b11 (prof : Profile) : Blk prof p11 0 7 o11 :=
  .cons (p11_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p11_4 _) (OpI.test (.r 7) (.inr rfl)) (by decide) <|
  .nil 7

def j3 : List Byte := [0x74, 0x06]
theorem j3_0 : ∀ feat, Dec feat j3 0 (FV7z.mk (.jcc 4) 64 [.rel 6] 2) := by dec_rfl

/-- The stretch at `201`. -/
def p12 : List Byte := [
  0x48, 0x8b, 0x07]

theorem p12_0 : ∀ feat, Dec feat p12 0 (FV7z.mk .mov 64 [gr 64 0, .mem (mg (some 7) none 1 0 64)] 3) := by dec_rfl

/-- What the stretch does. -/
def o12 : List Op := [
  Op.ld 64 0 (some 7) none 1 0]

theorem b12 (prof : Profile) : Blk prof p12 0 3 o12 :=
  .cons (p12_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .nil 3

/-- The stretch at `207`. -/
def p13 : List Byte := [
  0x48, 0x8b, 0x7d, 0x10, 0x48, 0x85, 0xff]

theorem p13_0 : ∀ feat, Dec feat p13 0 (FV7z.mk .mov 64 [gr 64 7, .mem (mg (some 5) none 1 16 64)] 4) := by dec_rfl
theorem p13_4 : ∀ feat, Dec feat p13 4 (FV7z.mk .test 64 [gr 64 7, Src.opd 64 (.r 7)] 3) := by dec_rfl

/-- What the stretch does. -/
def o13 : List Op := [
  Op.ld 64 7 (some 5) none 1 16,
  Op.test 64 7 (.r 7)]

theorem b13 (prof : Profile) : Blk prof p13 0 7 o13 :=
  .cons (p13_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p13_4 _) (OpI.test (.r 7) (.inr rfl)) (by decide) <|
  .nil 7

/-- The stretch at `222`. -/
def p14 : List Byte := [
  0x48, 0x8b, 0x7d, 0x08, 0x48, 0x85, 0xff]

theorem p14_0 : ∀ feat, Dec feat p14 0 (FV7z.mk .mov 64 [gr 64 7, .mem (mg (some 5) none 1 8 64)] 4) := by dec_rfl
theorem p14_4 : ∀ feat, Dec feat p14 4 (FV7z.mk .test 64 [gr 64 7, Src.opd 64 (.r 7)] 3) := by dec_rfl

/-- What the stretch does. -/
def o14 : List Op := [
  Op.ld 64 7 (some 5) none 1 8,
  Op.test 64 7 (.r 7)]

theorem b14 (prof : Profile) : Blk prof p14 0 7 o14 :=
  .cons (p14_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p14_4 _) (OpI.test (.r 7) (.inr rfl)) (by decide) <|
  .nil 7

/-- The stretch at `237`. -/
def p15 : List Byte := [
  0x4c, 0x8b, 0x75, 0x00, 0x4d, 0x85, 0xf6]

theorem p15_0 : ∀ feat, Dec feat p15 0 (FV7z.mk .mov 64 [gr 64 14, .mem (mg (some 5) none 1 0 64)] 4) := by dec_rfl
theorem p15_4 : ∀ feat, Dec feat p15 4 (FV7z.mk .test 64 [gr 64 14, Src.opd 64 (.r 14)] 3) := by dec_rfl

/-- What the stretch does. -/
def o15 : List Op := [
  Op.ld 64 14 (some 5) none 1 0,
  Op.test 64 14 (.r 14)]

theorem b15 (prof : Profile) : Blk prof p15 0 7 o15 :=
  .cons (p15_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p15_4 _) (OpI.test (.r 14) (.inr rfl)) (by decide) <|
  .nil 7

def j4 : List Byte := [0x0f, 0x84, 0xd5, 0x00, 0x00, 0x00]
theorem j4_0 : ∀ feat, Dec feat j4 0 (FV7z.mk (.jcc 4) 64 [.rel 213] 6) := by dec_rfl

/-- The stretch at `250`. -/
def p16 : List Byte := [
  0x49, 0x8b, 0x06, 0x48, 0x8b, 0x40, 0x10, 0x48, 0x81, 0xf8, 0xe0, 0xb1, 0x5d, 0x00]

theorem p16_0 : ∀ feat, Dec feat p16 0 (FV7z.mk .mov 64 [gr 64 0, .mem (mg (some 14) none 1 0 64)] 3) := by dec_rfl
theorem p16_3 : ∀ feat, Dec feat p16 3 (FV7z.mk .mov 64 [gr 64 0, .mem (mg (some 0) none 1 16 64)] 4) := by dec_rfl
theorem p16_7 : ∀ feat, Dec feat p16 7 (FV7z.mk .cmp 64 [gr 64 0, Src.opd 64 (.i 6140384)] 7) := by dec_rfl

/-- What the stretch does. -/
def o16 : List Op := [
  Op.ld 64 0 (some 14) none 1 0,
  Op.ld 64 0 (some 0) none 1 16,
  Op.cmp 64 0 (.i 6140384)]

theorem b16 (prof : Profile) : Blk prof p16 0 14 o16 :=
  .cons (p16_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p16_3 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p16_7 _) (OpI.cmp (.i 6140384) (.inr rfl)) (by decide) <|
  .nil 14

def j5 : List Byte := [0x0f, 0x85, 0xf2, 0x00, 0x00, 0x00]
theorem j5_0 : ∀ feat, Dec feat j5 0 (FV7z.mk (.jcc 5) 64 [.rel 242] 6) := by dec_rfl

def j6 : List Byte := [0x0f, 0x85, 0xb6, 0x00, 0x00, 0x00]
theorem j6_0 : ∀ feat, Dec feat j6 0 (FV7z.mk (.jcc 5) 64 [.rel 182] 6) := by dec_rfl

/-- The stretch at `281`. -/
def p17 : List Byte := [
  0x48, 0xc7, 0xc0, 0x98, 0xf5, 0x78, 0x00, 0x49, 0x8b, 0x7e, 0x30, 0x48, 0x8d, 0x50, 0x10, 0x48,
  0x05, 0x90, 0x00, 0x00, 0x00, 0x49, 0x89, 0x16, 0x49, 0x89, 0x46, 0x08, 0x48, 0x85, 0xff]

theorem p17_0 : ∀ feat, Dec feat p17 0 (FV7z.mk .mov 64 [gr 64 0, Src.opd 64 (.i 7927192)] 7) := by dec_rfl
theorem p17_7 : ∀ feat, Dec feat p17 7 (FV7z.mk .mov 64 [gr 64 7, .mem (mg (some 14) none 1 48 64)] 4) := by dec_rfl
theorem p17_11 : ∀ feat, Dec feat p17 11 (FV7z.mk .lea 64 [gr 64 2, .mem (mg (some 0) none 1 16 0)] 4) := by dec_rfl
theorem p17_15 : ∀ feat, Dec feat p17 15 (FV7z.mk .add 64 [gr 64 0, Src.opd 64 (.i 144)] 6) := by dec_rfl
theorem p17_21 : ∀ feat, Dec feat p17 21 (FV7z.mk .mov 64 [.mem (mg (some 14) none 1 0 64), gr 64 2] 3) := by dec_rfl
theorem p17_24 : ∀ feat, Dec feat p17 24 (FV7z.mk .mov 64 [.mem (mg (some 14) none 1 8 64), gr 64 0] 4) := by dec_rfl
theorem p17_28 : ∀ feat, Dec feat p17 28 (FV7z.mk .test 64 [gr 64 7, Src.opd 64 (.r 7)] 3) := by dec_rfl

/-- What the stretch does. -/
def o17 : List Op := [
  Op.mov 64 0 (.i 7927192),
  Op.ld 64 7 (some 14) none 1 48,
  Op.lea 64 2 (some 0) none 1 16,
  Op.add 64 0 (.i 144),
  Op.st 64 (some 14) none 1 0 2,
  Op.st 64 (some 14) none 1 8 0,
  Op.test 64 7 (.r 7)]

theorem b17 (prof : Profile) : Blk prof p17 0 31 o17 :=
  .cons (p17_0 _) (OpI.mov (.i 7927192) (.inr rfl)) (by decide) <|
  .cons (p17_7 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p17_11 _) (OpI.lea (.inr rfl)) (by decide) <|
  .cons (p17_15 _) (OpI.add (.i 144) (.inr rfl)) (by decide) <|
  .cons (p17_21 _) (OpI.st (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p17_24 _) (OpI.st (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p17_28 _) (OpI.test (.r 7) (.inr rfl)) (by decide) <|
  .nil 31

/-- The stretch at `320`. -/
def p18 : List Byte := [
  0x41, 0x8b, 0x46, 0x20, 0x49, 0x8b, 0x7e, 0x18, 0x85, 0xc0]

theorem p18_0 : ∀ feat, Dec feat p18 0 (FV7z.mk .mov 32 [gr 32 0, .mem (mg (some 14) none 1 32 32)] 4) := by dec_rfl
theorem p18_4 : ∀ feat, Dec feat p18 4 (FV7z.mk .mov 64 [gr 64 7, .mem (mg (some 14) none 1 24 64)] 4) := by dec_rfl
theorem p18_8 : ∀ feat, Dec feat p18 8 (FV7z.mk .test 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl

/-- What the stretch does. -/
def o18 : List Op := [
  Op.ld 32 0 (some 14) none 1 32,
  Op.ld 64 7 (some 14) none 1 24,
  Op.test 32 0 (.r 0)]

theorem b18 (prof : Profile) : Blk prof p18 0 10 o18 :=
  .cons (p18_0 _) (OpI.ld (.inl rfl)) (by decide) <|
  .cons (p18_4 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p18_8 _) (OpI.test (.r 0) (.inl rfl)) (by decide) <|
  .nil 10

def j7 : List Byte := [0x74, 0x6c]
theorem j7_0 : ∀ feat, Dec feat j7 0 (FV7z.mk (.jcc 4) 64 [.rel 108] 2) := by dec_rfl

/-- The stretch at `332`. -/
def p19 : List Byte := [
  0x8d, 0x58, 0xff, 0x48, 0xc1, 0xe3, 0x03, 0x0f, 0x1f, 0x44, 0x00, 0x00]

theorem p19_0 : ∀ feat, Dec feat p19 0 (FV7z.mk .lea 32 [gr 32 3, .mem (mg (some 0) none 1 18446744073709551615 0)] 3) := by dec_rfl
theorem p19_3 : ∀ feat, Dec feat p19 3 (FV7z.mk .shl 64 [gr 64 3, Src.opd 8 (.i 3)] 4) := by dec_rfl
theorem p19_7 : ∀ feat, Dec feat p19 7 (FV7z.mk .nop 32 [.mem (mg (some 0) (some 0) 1 0 32)] 5) := by dec_rfl

/-- What the stretch does. -/
def o19 : List Op := [
  Op.lea 32 3 (some 0) none 1 18446744073709551615,
  Op.shl64 3 (.i 3),
  Op.nop]

theorem b19 (prof : Profile) : Blk prof p19 0 12 o19 :=
  .cons (p19_0 _) (OpI.lea (.inl rfl)) (by decide) <|
  .cons (p19_3 _) (OpI.shl64 (.i 3)) (by decide) <|
  .cons (p19_7 _) (OpI.nop) (by decide) <|
  .nil 12

/-- The stretch at `344`. -/
def p20 : List Byte := [
  0x4c, 0x8b, 0x24, 0x1f, 0x4d, 0x85, 0xe4]

theorem p20_0 : ∀ feat, Dec feat p20 0 (FV7z.mk .mov 64 [gr 64 12, .mem (mg (some 7) (some 3) 1 0 64)] 4) := by dec_rfl
theorem p20_4 : ∀ feat, Dec feat p20 4 (FV7z.mk .test 64 [gr 64 12, Src.opd 64 (.r 12)] 3) := by dec_rfl

/-- What the stretch does. -/
def o20 : List Op := [
  Op.ld 64 12 (some 7) (some 3) 1 0,
  Op.test 64 12 (.r 12)]

theorem b20 (prof : Profile) : Blk prof p20 0 7 o20 :=
  .cons (p20_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p20_4 _) (OpI.test (.r 12) (.inr rfl)) (by decide) <|
  .nil 7

def j8 : List Byte := [0x74, 0x4d]
theorem j8_0 : ∀ feat, Dec feat j8 0 (FV7z.mk (.jcc 4) 64 [.rel 77] 2) := by dec_rfl

/-- The stretch at `353`. -/
def p21 : List Byte := [
  0x49, 0x8b, 0x7c, 0x24, 0x48, 0x48, 0x85, 0xff]

theorem p21_0 : ∀ feat, Dec feat p21 0 (FV7z.mk .mov 64 [gr 64 7, .mem (mg (some 12) none 1 72 64)] 5) := by dec_rfl
theorem p21_5 : ∀ feat, Dec feat p21 5 (FV7z.mk .test 64 [gr 64 7, Src.opd 64 (.r 7)] 3) := by dec_rfl

/-- What the stretch does. -/
def o21 : List Op := [
  Op.ld 64 7 (some 12) none 1 72,
  Op.test 64 7 (.r 7)]

theorem b21 (prof : Profile) : Blk prof p21 0 8 o21 :=
  .cons (p21_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p21_5 _) (OpI.test (.r 7) (.inr rfl)) (by decide) <|
  .nil 8

/-- The stretch at `368`. -/
def p22 : List Byte := [
  0x49, 0x8b, 0x7c, 0x24, 0x38, 0x48, 0x85, 0xff]

theorem p22_0 : ∀ feat, Dec feat p22 0 (FV7z.mk .mov 64 [gr 64 7, .mem (mg (some 12) none 1 56 64)] 5) := by dec_rfl
theorem p22_5 : ∀ feat, Dec feat p22 5 (FV7z.mk .test 64 [gr 64 7, Src.opd 64 (.r 7)] 3) := by dec_rfl

/-- What the stretch does. -/
def o22 : List Op := [
  Op.ld 64 7 (some 12) none 1 56,
  Op.test 64 7 (.r 7)]

theorem b22 (prof : Profile) : Blk prof p22 0 8 o22 :=
  .cons (p22_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p22_5 _) (OpI.test (.r 7) (.inr rfl)) (by decide) <|
  .nil 8

/-- The stretch at `383`. -/
def p23 : List Byte := [
  0x49, 0x8b, 0x7c, 0x24, 0x20, 0x48, 0x85, 0xff]

theorem p23_0 : ∀ feat, Dec feat p23 0 (FV7z.mk .mov 64 [gr 64 7, .mem (mg (some 12) none 1 32 64)] 5) := by dec_rfl
theorem p23_5 : ∀ feat, Dec feat p23 5 (FV7z.mk .test 64 [gr 64 7, Src.opd 64 (.r 7)] 3) := by dec_rfl

/-- What the stretch does. -/
def o23 : List Op := [
  Op.ld 64 7 (some 12) none 1 32,
  Op.test 64 7 (.r 7)]

theorem b23 (prof : Profile) : Blk prof p23 0 8 o23 :=
  .cons (p23_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p23_5 _) (OpI.test (.r 7) (.inr rfl)) (by decide) <|
  .nil 8

/-- The stretch at `398`. -/
def p24 : List Byte := [
  0x49, 0x8b, 0x7c, 0x24, 0x10, 0x48, 0x85, 0xff]

theorem p24_0 : ∀ feat, Dec feat p24 0 (FV7z.mk .mov 64 [gr 64 7, .mem (mg (some 12) none 1 16 64)] 5) := by dec_rfl
theorem p24_5 : ∀ feat, Dec feat p24 5 (FV7z.mk .test 64 [gr 64 7, Src.opd 64 (.r 7)] 3) := by dec_rfl

/-- What the stretch does. -/
def o24 : List Op := [
  Op.ld 64 7 (some 12) none 1 16,
  Op.test 64 7 (.r 7)]

theorem b24 (prof : Profile) : Blk prof p24 0 8 o24 :=
  .cons (p24_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p24_5 _) (OpI.test (.r 7) (.inr rfl)) (by decide) <|
  .nil 8

/-- The stretch at `413`. -/
def p25 : List Byte := [
  0x4c, 0x89, 0xe7, 0xbe, 0x80, 0x00, 0x00, 0x00]

theorem p25_0 : ∀ feat, Dec feat p25 0 (FV7z.mk .mov 64 [gr 64 7, Src.opd 64 (.r 12)] 3) := by dec_rfl
theorem p25_3 : ∀ feat, Dec feat p25 3 (FV7z.mk .mov 32 [gr 32 6, Src.opd 32 (.i 128)] 5) := by dec_rfl

/-- What the stretch does. -/
def o25 : List Op := [
  Op.mov 64 7 (.r 12),
  Op.mov 32 6 (.i 128)]

theorem b25 (prof : Profile) : Blk prof p25 0 8 o25 :=
  .cons (p25_0 _) (OpI.mov (.r 12) (.inr rfl)) (by decide) <|
  .cons (p25_3 _) (OpI.mov (.i 128) (.inl rfl)) (by decide) <|
  .nil 8

/-- The stretch at `426`. -/
def p26 : List Byte := [
  0x49, 0x8b, 0x7e, 0x18]

theorem p26_0 : ∀ feat, Dec feat p26 0 (FV7z.mk .mov 64 [gr 64 7, .mem (mg (some 14) none 1 24 64)] 4) := by dec_rfl

/-- What the stretch does. -/
def o26 : List Op := [
  Op.ld 64 7 (some 14) none 1 24]

theorem b26 (prof : Profile) : Blk prof p26 0 4 o26 :=
  .cons (p26_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .nil 4

/-- The stretch at `430`. -/
def p27 : List Byte := [
  0x48, 0x83, 0xeb, 0x08, 0x48, 0x83, 0xfb, 0xf8]

theorem p27_0 : ∀ feat, Dec feat p27 0 (FV7z.mk .sub 64 [gr 64 3, Src.opd 64 (.i 8)] 4) := by dec_rfl
theorem p27_4 : ∀ feat, Dec feat p27 4 (FV7z.mk .cmp 64 [gr 64 3, Src.opd 64 (.i 18446744073709551608)] 4) := by dec_rfl

/-- What the stretch does. -/
def o27 : List Op := [
  Op.sub 64 3 (.i 8),
  Op.cmp 64 3 (.i 18446744073709551608)]

theorem b27 (prof : Profile) : Blk prof p27 0 8 o27 :=
  .cons (p27_0 _) (OpI.sub (.i 8) (.inr rfl)) (by decide) <|
  .cons (p27_4 _) (OpI.cmp (.i 18446744073709551608) (.inr rfl)) (by decide) <|
  .nil 8

def j9 : List Byte := [0x75, 0xa0]
theorem j9_0 : ∀ feat, Dec feat j9 0 (FV7z.mk (.jcc 5) 64 [.rel 18446744073709551520] 2) := by dec_rfl

/-- The stretch at `440`. -/
def p28 : List Byte := [
  0x48, 0x85, 0xff]

theorem p28_0 : ∀ feat, Dec feat p28 0 (FV7z.mk .test 64 [gr 64 7, Src.opd 64 (.r 7)] 3) := by dec_rfl

/-- What the stretch does. -/
def o28 : List Op := [
  Op.test 64 7 (.r 7)]

theorem b28 (prof : Profile) : Blk prof p28 0 3 o28 :=
  .cons (p28_0 _) (OpI.test (.r 7) (.inr rfl)) (by decide) <|
  .nil 3

/-- The stretch at `450`. -/
def p29 : List Byte := [
  0xbe, 0x38, 0x00, 0x00, 0x00, 0x4c, 0x89, 0xf7]

theorem p29_0 : ∀ feat, Dec feat p29 0 (FV7z.mk .mov 32 [gr 32 6, Src.opd 32 (.i 56)] 5) := by dec_rfl
theorem p29_5 : ∀ feat, Dec feat p29 5 (FV7z.mk .mov 64 [gr 64 7, Src.opd 64 (.r 14)] 3) := by dec_rfl

/-- What the stretch does. -/
def o29 : List Op := [
  Op.mov 32 6 (.i 56),
  Op.mov 64 7 (.r 14)]

theorem b29 (prof : Profile) : Blk prof p29 0 8 o29 :=
  .cons (p29_0 _) (OpI.mov (.i 56) (.inl rfl)) (by decide) <|
  .cons (p29_5 _) (OpI.mov (.r 14) (.inr rfl)) (by decide) <|
  .nil 8

/-- The stretch at `463`. -/
def p30 : List Byte := [
  0xbe, 0x10, 0x01, 0x00, 0x00, 0x48, 0x89, 0xef]

theorem p30_0 : ∀ feat, Dec feat p30 0 (FV7z.mk .mov 32 [gr 32 6, Src.opd 32 (.i 272)] 5) := by dec_rfl
theorem p30_5 : ∀ feat, Dec feat p30 5 (FV7z.mk .mov 64 [gr 64 7, Src.opd 64 (.r 5)] 3) := by dec_rfl

/-- What the stretch does. -/
def o30 : List Op := [
  Op.mov 32 6 (.i 272),
  Op.mov 64 7 (.r 5)]

theorem b30 (prof : Profile) : Blk prof p30 0 8 o30 :=
  .cons (p30_0 _) (OpI.mov (.i 272) (.inl rfl)) (by decide) <|
  .cons (p30_5 _) (OpI.mov (.r 5) (.inr rfl)) (by decide) <|
  .nil 8

/-- The stretch at `476`. -/
def p31 : List Byte := [
  0x41, 0x8b, 0x45, 0x08, 0x83, 0xe8, 0x01, 0x41, 0x89, 0x45, 0x08]

theorem p31_0 : ∀ feat, Dec feat p31 0 (FV7z.mk .mov 32 [gr 32 0, .mem (mg (some 13) none 1 8 32)] 4) := by dec_rfl
theorem p31_4 : ∀ feat, Dec feat p31 4 (FV7z.mk .sub 32 [gr 32 0, Src.opd 32 (.i 1)] 3) := by dec_rfl
theorem p31_7 : ∀ feat, Dec feat p31 7 (FV7z.mk .mov 32 [.mem (mg (some 13) none 1 8 32), gr 32 0] 4) := by dec_rfl

/-- What the stretch does. -/
def o31 : List Op := [
  Op.ld 32 0 (some 13) none 1 8,
  Op.sub 32 0 (.i 1),
  Op.st 32 (some 13) none 1 8 0]

theorem b31 (prof : Profile) : Blk prof p31 0 11 o31 :=
  .cons (p31_0 _) (OpI.ld (.inl rfl)) (by decide) <|
  .cons (p31_4 _) (OpI.sub (.i 1) (.inl rfl)) (by decide) <|
  .cons (p31_7 _) (OpI.st (.inr (.inr (.inl rfl)))) (by decide) <|
  .nil 11

def j10 : List Byte := [0x0f, 0x85, 0x53, 0xfe, 0xff, 0xff]
theorem j10_0 : ∀ feat, Dec feat j10 0 (FV7z.mk (.jcc 5) 64 [.rel 18446744073709551187] 6) := by dec_rfl

/-- The stretch at `493`. -/
def p32 : List Byte := [
  0x5b, 0x5d, 0x41, 0x5c, 0x41, 0x5d, 0x41, 0x5e]

theorem p32_0 : ∀ feat, Dec feat p32 0 (FV7z.mk .pop 64 [gr 64 3] 1) := by dec_rfl
theorem p32_1 : ∀ feat, Dec feat p32 1 (FV7z.mk .pop 64 [gr 64 5] 1) := by dec_rfl
theorem p32_2 : ∀ feat, Dec feat p32 2 (FV7z.mk .pop 64 [gr 64 12] 2) := by dec_rfl
theorem p32_4 : ∀ feat, Dec feat p32 4 (FV7z.mk .pop 64 [gr 64 13] 2) := by dec_rfl
theorem p32_6 : ∀ feat, Dec feat p32 6 (FV7z.mk .pop 64 [gr 64 14] 2) := by dec_rfl

/-- What the stretch does. -/
def o32 : List Op := [
  Op.pop 3,
  Op.pop 5,
  Op.pop 12,
  Op.pop 13,
  Op.pop 14]

theorem b32 (prof : Profile) : Blk prof p32 0 8 o32 :=
  .cons (p32_0 _) (OpI.pop) (by decide) <|
  .cons (p32_1 _) (OpI.pop) (by decide) <|
  .cons (p32_2 _) (OpI.pop) (by decide) <|
  .cons (p32_4 _) (OpI.pop) (by decide) <|
  .cons (p32_6 _) (OpI.pop) (by decide) <|
  .nil 8

/-- The stretch at `512`. -/
def p33 : List Byte := [
  0x4c, 0x89, 0xf7]

theorem p33_0 : ∀ feat, Dec feat p33 0 (FV7z.mk .mov 64 [gr 64 7, Src.opd 64 (.r 14)] 3) := by dec_rfl

/-- What the stretch does. -/
def o33 : List Op := [
  Op.mov 64 7 (.r 14)]

theorem b33 (prof : Profile) : Blk prof p33 0 3 o33 :=
  .cons (p33_0 _) (OpI.mov (.r 14) (.inr rfl)) (by decide) <|
  .nil 3

def j11 : List Byte := [0xeb, 0xc8]
theorem j11_0 : ∀ feat, Dec feat j11 0 (FV7z.mk .jmp 64 [.rel 18446744073709551560] 2) := by dec_rfl

end FV7z.Alr
