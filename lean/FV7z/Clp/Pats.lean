import FV7z.Lemmas.Sp
import FV7z.Lemmas.BlkOps2
/-!
# The stretches of straight-line code of `CLocalProgress::Init` (PLAN.md §M, M1)

Each distinct stretch between labels and jumps (`p*`, 30 of them) and each distinct jump (`j*`, 20) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.Clp
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The stretch at `0`. -/
def p0 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0x41, 0x57, 0x41, 0x56, 0x41, 0x55, 0x41, 0x89, 0xd5, 0x41, 0x54, 0x55,
  0x48, 0x89, 0xf5, 0x53, 0x48, 0x89, 0xfb, 0x48, 0x83, 0xec, 0x18, 0x4c, 0x8b, 0x67, 0x18, 0x4d,
  0x85, 0xe4]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem p0_4 : ∀ feat, Dec feat p0 4 (FV7z.mk .push 64 [gr 64 15] 2) := by dec_rfl
theorem p0_6 : ∀ feat, Dec feat p0 6 (FV7z.mk .push 64 [gr 64 14] 2) := by dec_rfl
theorem p0_8 : ∀ feat, Dec feat p0 8 (FV7z.mk .push 64 [gr 64 13] 2) := by dec_rfl
theorem p0_10 : ∀ feat, Dec feat p0 10 (FV7z.mk .mov 32 [gr 32 13, Src.opd 32 (.r 2)] 3) := by dec_rfl
theorem p0_13 : ∀ feat, Dec feat p0 13 (FV7z.mk .push 64 [gr 64 12] 2) := by dec_rfl
theorem p0_15 : ∀ feat, Dec feat p0 15 (FV7z.mk .push 64 [gr 64 5] 1) := by dec_rfl
theorem p0_16 : ∀ feat, Dec feat p0 16 (FV7z.mk .mov 64 [gr 64 5, Src.opd 64 (.r 6)] 3) := by dec_rfl
theorem p0_19 : ∀ feat, Dec feat p0 19 (FV7z.mk .push 64 [gr 64 3] 1) := by dec_rfl
theorem p0_20 : ∀ feat, Dec feat p0 20 (FV7z.mk .mov 64 [gr 64 3, Src.opd 64 (.r 7)] 3) := by dec_rfl
theorem p0_23 : ∀ feat, Dec feat p0 23 (FV7z.mk .sub 64 [gr 64 4, Src.opd 64 (.i 24)] 4) := by dec_rfl
theorem p0_27 : ∀ feat, Dec feat p0 27 (FV7z.mk .mov 64 [gr 64 12, .mem (mg (some 7) none 1 24 64)] 4) := by dec_rfl
theorem p0_31 : ∀ feat, Dec feat p0 31 (FV7z.mk .test 64 [gr 64 12, Src.opd 64 (.r 12)] 3) := by dec_rfl

/-- What the stretch does. -/
def o0 : List Op := [
  Op.nop,
  Op.push 15,
  Op.push 14,
  Op.push 13,
  Op.mov 32 13 (.r 2),
  Op.push 12,
  Op.push 5,
  Op.mov 64 5 (.r 6),
  Op.push 3,
  Op.mov 64 3 (.r 7),
  Op.sub 64 4 (.i 24),
  Op.ld 64 12 (some 7) none 1 24,
  Op.test 64 12 (.r 12)]

theorem b0 (prof : Profile) : Blk prof p0 0 34 o0 :=
  .cons (p0_0 _) (OpI.endbr) (by decide) <|
  .cons (p0_4 _) (OpI.push) (by decide) <|
  .cons (p0_6 _) (OpI.push) (by decide) <|
  .cons (p0_8 _) (OpI.push) (by decide) <|
  .cons (p0_10 _) (OpI.mov (.r 2) (.inl rfl)) (by decide) <|
  .cons (p0_13 _) (OpI.push) (by decide) <|
  .cons (p0_15 _) (OpI.push) (by decide) <|
  .cons (p0_16 _) (OpI.mov (.r 6) (.inr rfl)) (by decide) <|
  .cons (p0_19 _) (OpI.push) (by decide) <|
  .cons (p0_20 _) (OpI.mov (.r 7) (.inr rfl)) (by decide) <|
  .cons (p0_23 _) (OpI.sub (.i 24) (.inr rfl)) (by decide) <|
  .cons (p0_27 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p0_31 _) (OpI.test (.r 12) (.inr rfl)) (by decide) <|
  .nil 34

def j0 : List Byte := [0x74, 0x28]
theorem j0_0 : ∀ feat, Dec feat j0 0 (FV7z.mk (.jcc 4) 64 [.rel 40] 2) := by dec_rfl

/-- The stretch at `36`. -/
def p1 : List Byte := [
  0x49, 0x8b, 0x04, 0x24, 0x48, 0xc7, 0xc2, 0x90, 0x22, 0x46, 0x00, 0x48, 0x8b, 0x40, 0x10, 0x48,
  0x39, 0xd0]

theorem p1_0 : ∀ feat, Dec feat p1 0 (FV7z.mk .mov 64 [gr 64 0, .mem (mg (some 12) none 1 0 64)] 4) := by dec_rfl
theorem p1_4 : ∀ feat, Dec feat p1 4 (FV7z.mk .mov 64 [gr 64 2, Src.opd 64 (.i 4596368)] 7) := by dec_rfl
theorem p1_11 : ∀ feat, Dec feat p1 11 (FV7z.mk .mov 64 [gr 64 0, .mem (mg (some 0) none 1 16 64)] 4) := by dec_rfl
theorem p1_15 : ∀ feat, Dec feat p1 15 (FV7z.mk .cmp 64 [gr 64 0, Src.opd 64 (.r 2)] 3) := by dec_rfl

/-- What the stretch does. -/
def o1 : List Op := [
  Op.ld 64 0 (some 12) none 1 0,
  Op.mov 64 2 (.i 4596368),
  Op.ld 64 0 (some 0) none 1 16,
  Op.cmp 64 0 (.r 2)]

theorem b1 (prof : Profile) : Blk prof p1 0 18 o1 :=
  .cons (p1_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p1_4 _) (OpI.mov (.i 4596368) (.inr rfl)) (by decide) <|
  .cons (p1_11 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p1_15 _) (OpI.cmp (.r 2) (.inr rfl)) (by decide) <|
  .nil 18

def j1 : List Byte := [0x0f, 0x85, 0x84, 0x01, 0x00, 0x00]
theorem j1_0 : ∀ feat, Dec feat j1 0 (FV7z.mk (.jcc 5) 64 [.rel 388] 6) := by dec_rfl

def j2 : List Byte := [0x74, 0x54]
theorem j2_0 : ∀ feat, Dec feat j2 0 (FV7z.mk (.jcc 4) 64 [.rel 84] 2) := by dec_rfl

/-- The stretch at `68`. -/
def p2 : List Byte := [
  0x48, 0xc7, 0x43, 0x18, 0x00, 0x00, 0x00, 0x00]

theorem p2_0 : ∀ feat, Dec feat p2 0 (FV7z.mk .mov 64 [.mem (mg (some 3) none 1 24 64), .imm 64 0] 8) := by dec_rfl

/-- What the stretch does. -/
def o2 : List Op := [
  Op.sti 64 (some 3) none 1 24 0]

theorem b2 (prof : Profile) : Blk prof p2 0 8 o2 :=
  .cons (p2_0 _) (OpI.sti (.inr (.inr (.inr rfl)))) (by decide) <|
  .nil 8

/-- The stretch at `76`. -/
def p3 : List Byte := [
  0x48, 0x85, 0xed]

theorem p3_0 : ∀ feat, Dec feat p3 0 (FV7z.mk .test 64 [gr 64 5, Src.opd 64 (.r 5)] 3) := by dec_rfl

/-- What the stretch does. -/
def o3 : List Op := [
  Op.test 64 5 (.r 5)]

theorem b3 (prof : Profile) : Blk prof p3 0 3 o3 :=
  .cons (p3_0 _) (OpI.test (.r 5) (.inr rfl)) (by decide) <|
  .nil 3

def j3 : List Byte := [0x74, 0x0a]
theorem j3_0 : ∀ feat, Dec feat j3 0 (FV7z.mk (.jcc 4) 64 [.rel 10] 2) := by dec_rfl

/-- The stretch at `81`. -/
def p4 : List Byte := [
  0x48, 0x8b, 0x45, 0x00, 0x48, 0x89, 0xef]

theorem p4_0 : ∀ feat, Dec feat p4 0 (FV7z.mk .mov 64 [gr 64 0, .mem (mg (some 5) none 1 0 64)] 4) := by dec_rfl
theorem p4_4 : ∀ feat, Dec feat p4 4 (FV7z.mk .mov 64 [gr 64 7, Src.opd 64 (.r 5)] 3) := by dec_rfl

/-- What the stretch does. -/
def o4 : List Op := [
  Op.ld 64 0 (some 5) none 1 0,
  Op.mov 64 7 (.r 5)]

theorem b4 (prof : Profile) : Blk prof p4 0 7 o4 :=
  .cons (p4_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p4_4 _) (OpI.mov (.r 5) (.inr rfl)) (by decide) <|
  .nil 7

/-- The stretch at `91`. -/
def p5 : List Byte := [
  0x48, 0x8b, 0x7b, 0x10, 0x48, 0x85, 0xff]

theorem p5_0 : ∀ feat, Dec feat p5 0 (FV7z.mk .mov 64 [gr 64 7, .mem (mg (some 3) none 1 16 64)] 4) := by dec_rfl
theorem p5_4 : ∀ feat, Dec feat p5 4 (FV7z.mk .test 64 [gr 64 7, Src.opd 64 (.r 7)] 3) := by dec_rfl

/-- What the stretch does. -/
def o5 : List Op := [
  Op.ld 64 7 (some 3) none 1 16,
  Op.test 64 7 (.r 7)]

theorem b5 (prof : Profile) : Blk prof p5 0 7 o5 :=
  .cons (p5_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p5_4 _) (OpI.test (.r 7) (.inr rfl)) (by decide) <|
  .nil 7

def j4 : List Byte := [0x74, 0x06]
theorem j4_0 : ∀ feat, Dec feat j4 0 (FV7z.mk (.jcc 4) 64 [.rel 6] 2) := by dec_rfl

/-- The stretch at `100`. -/
def p6 : List Byte := [
  0x48, 0x8b, 0x07]

theorem p6_0 : ∀ feat, Dec feat p6 0 (FV7z.mk .mov 64 [gr 64 0, .mem (mg (some 7) none 1 0 64)] 3) := by dec_rfl

/-- What the stretch does. -/
def o6 : List Op := [
  Op.ld 64 0 (some 7) none 1 0]

theorem b6 (prof : Profile) : Blk prof p6 0 3 o6 :=
  .cons (p6_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .nil 3

/-- The stretch at `106`. -/
def p7 : List Byte := [
  0x48, 0x8b, 0x45, 0x00, 0x48, 0x89, 0x6b, 0x10, 0x48, 0x8d, 0x53, 0x18, 0x48, 0x89, 0xef, 0x48,
  0xc7, 0xc6, 0x60, 0xb7, 0x6e, 0x00]

theorem p7_0 : ∀ feat, Dec feat p7 0 (FV7z.mk .mov 64 [gr 64 0, .mem (mg (some 5) none 1 0 64)] 4) := by dec_rfl
theorem p7_4 : ∀ feat, Dec feat p7 4 (FV7z.mk .mov 64 [.mem (mg (some 3) none 1 16 64), gr 64 5] 4) := by dec_rfl
theorem p7_8 : ∀ feat, Dec feat p7 8 (FV7z.mk .lea 64 [gr 64 2, .mem (mg (some 3) none 1 24 0)] 4) := by dec_rfl
theorem p7_12 : ∀ feat, Dec feat p7 12 (FV7z.mk .mov 64 [gr 64 7, Src.opd 64 (.r 5)] 3) := by dec_rfl
theorem p7_15 : ∀ feat, Dec feat p7 15 (FV7z.mk .mov 64 [gr 64 6, Src.opd 64 (.i 7255904)] 7) := by dec_rfl

/-- What the stretch does. -/
def o7 : List Op := [
  Op.ld 64 0 (some 5) none 1 0,
  Op.st 64 (some 3) none 1 16 5,
  Op.lea 64 2 (some 3) none 1 24,
  Op.mov 64 7 (.r 5),
  Op.mov 64 6 (.i 7255904)]

theorem b7 (prof : Profile) : Blk prof p7 0 22 o7 :=
  .cons (p7_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p7_4 _) (OpI.st (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p7_8 _) (OpI.lea (.inr rfl)) (by decide) <|
  .cons (p7_12 _) (OpI.mov (.r 5) (.inr rfl)) (by decide) <|
  .cons (p7_15 _) (OpI.mov (.i 7255904) (.inr rfl)) (by decide) <|
  .nil 22

/-- The stretch at `130`. -/
def p8 : List Byte := [
  0x44, 0x88, 0x6b, 0x0e, 0x48, 0x83, 0xc4, 0x18, 0x5b, 0x5d, 0x41, 0x5c, 0x41, 0x5d, 0x41, 0x5e,
  0x41, 0x5f]

theorem p8_0 : ∀ feat, Dec feat p8 0 (FV7z.mk .mov 8 [.mem (mg (some 3) none 1 14 8), gr 8 13] 4) := by dec_rfl
theorem p8_4 : ∀ feat, Dec feat p8 4 (FV7z.mk .add 64 [gr 64 4, Src.opd 64 (.i 24)] 4) := by dec_rfl
theorem p8_8 : ∀ feat, Dec feat p8 8 (FV7z.mk .pop 64 [gr 64 3] 1) := by dec_rfl
theorem p8_9 : ∀ feat, Dec feat p8 9 (FV7z.mk .pop 64 [gr 64 5] 1) := by dec_rfl
theorem p8_10 : ∀ feat, Dec feat p8 10 (FV7z.mk .pop 64 [gr 64 12] 2) := by dec_rfl
theorem p8_12 : ∀ feat, Dec feat p8 12 (FV7z.mk .pop 64 [gr 64 13] 2) := by dec_rfl
theorem p8_14 : ∀ feat, Dec feat p8 14 (FV7z.mk .pop 64 [gr 64 14] 2) := by dec_rfl
theorem p8_16 : ∀ feat, Dec feat p8 16 (FV7z.mk .pop 64 [gr 64 15] 2) := by dec_rfl

/-- What the stretch does. -/
def o8 : List Op := [
  Op.st 8 (some 3) none 1 14 13,
  Op.add 64 4 (.i 24),
  Op.pop 3,
  Op.pop 5,
  Op.pop 12,
  Op.pop 13,
  Op.pop 14,
  Op.pop 15]

theorem b8 (prof : Profile) : Blk prof p8 0 18 o8 :=
  .cons (p8_0 _) (OpI.st (.inl rfl)) (by decide) <|
  .cons (p8_4 _) (OpI.add (.i 24) (.inr rfl)) (by decide) <|
  .cons (p8_8 _) (OpI.pop) (by decide) <|
  .cons (p8_9 _) (OpI.pop) (by decide) <|
  .cons (p8_10 _) (OpI.pop) (by decide) <|
  .cons (p8_12 _) (OpI.pop) (by decide) <|
  .cons (p8_14 _) (OpI.pop) (by decide) <|
  .cons (p8_16 _) (OpI.pop) (by decide) <|
  .nil 18

/-- The stretch at `152`. -/
def p9 : List Byte := [
  0x48, 0xc7, 0xc6, 0xd0, 0x3b, 0x78, 0x00, 0x4d, 0x8b, 0x74, 0x24, 0x18, 0x48, 0x8d, 0x4e, 0x10,
  0x49, 0x89, 0x0c, 0x24, 0x4d, 0x85, 0xf6]

theorem p9_0 : ∀ feat, Dec feat p9 0 (FV7z.mk .mov 64 [gr 64 6, Src.opd 64 (.i 7879632)] 7) := by dec_rfl
theorem p9_7 : ∀ feat, Dec feat p9 7 (FV7z.mk .mov 64 [gr 64 14, .mem (mg (some 12) none 1 24 64)] 5) := by dec_rfl
theorem p9_12 : ∀ feat, Dec feat p9 12 (FV7z.mk .lea 64 [gr 64 1, .mem (mg (some 6) none 1 16 0)] 4) := by dec_rfl
theorem p9_16 : ∀ feat, Dec feat p9 16 (FV7z.mk .mov 64 [.mem (mg (some 12) none 1 0 64), gr 64 1] 4) := by dec_rfl
theorem p9_20 : ∀ feat, Dec feat p9 20 (FV7z.mk .test 64 [gr 64 14, Src.opd 64 (.r 14)] 3) := by dec_rfl

/-- What the stretch does. -/
def o9 : List Op := [
  Op.mov 64 6 (.i 7879632),
  Op.ld 64 14 (some 12) none 1 24,
  Op.lea 64 1 (some 6) none 1 16,
  Op.st 64 (some 12) none 1 0 1,
  Op.test 64 14 (.r 14)]

theorem b9 (prof : Profile) : Blk prof p9 0 23 o9 :=
  .cons (p9_0 _) (OpI.mov (.i 7879632) (.inr rfl)) (by decide) <|
  .cons (p9_7 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p9_12 _) (OpI.lea (.inr rfl)) (by decide) <|
  .cons (p9_16 _) (OpI.st (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p9_20 _) (OpI.test (.r 14) (.inr rfl)) (by decide) <|
  .nil 23

def j5 : List Byte := [0x0f, 0x84, 0xe3, 0x00, 0x00, 0x00]
theorem j5_0 : ∀ feat, Dec feat j5 0 (FV7z.mk (.jcc 4) 64 [.rel 227] 6) := by dec_rfl

/-- The stretch at `181`. -/
def p10 : List Byte := [
  0x49, 0x8b, 0x06, 0x48, 0x8b, 0x40, 0x10, 0x48, 0x39, 0xd0]

theorem p10_0 : ∀ feat, Dec feat p10 0 (FV7z.mk .mov 64 [gr 64 0, .mem (mg (some 14) none 1 0 64)] 3) := by dec_rfl
theorem p10_3 : ∀ feat, Dec feat p10 3 (FV7z.mk .mov 64 [gr 64 0, .mem (mg (some 0) none 1 16 64)] 4) := by dec_rfl
theorem p10_7 : ∀ feat, Dec feat p10 7 (FV7z.mk .cmp 64 [gr 64 0, Src.opd 64 (.r 2)] 3) := by dec_rfl

/-- What the stretch does. -/
def o10 : List Op := [
  Op.ld 64 0 (some 14) none 1 0,
  Op.ld 64 0 (some 0) none 1 16,
  Op.cmp 64 0 (.r 2)]

theorem b10 (prof : Profile) : Blk prof p10 0 10 o10 :=
  .cons (p10_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p10_3 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p10_7 _) (OpI.cmp (.r 2) (.inr rfl)) (by decide) <|
  .nil 10

def j6 : List Byte := [0x0f, 0x85, 0x1b, 0x01, 0x00, 0x00]
theorem j6_0 : ∀ feat, Dec feat j6 0 (FV7z.mk (.jcc 5) 64 [.rel 283] 6) := by dec_rfl

def j7 : List Byte := [0x0f, 0x85, 0xc8, 0x00, 0x00, 0x00]
theorem j7_0 : ∀ feat, Dec feat j7 0 (FV7z.mk (.jcc 5) 64 [.rel 200] 6) := by dec_rfl

/-- The stretch at `208`. -/
def p11 : List Byte := [
  0x4d, 0x8b, 0x7e, 0x18, 0x49, 0x89, 0x0e, 0x4d, 0x85, 0xff]

theorem p11_0 : ∀ feat, Dec feat p11 0 (FV7z.mk .mov 64 [gr 64 15, .mem (mg (some 14) none 1 24 64)] 4) := by dec_rfl
theorem p11_4 : ∀ feat, Dec feat p11 4 (FV7z.mk .mov 64 [.mem (mg (some 14) none 1 0 64), gr 64 1] 3) := by dec_rfl
theorem p11_7 : ∀ feat, Dec feat p11 7 (FV7z.mk .test 64 [gr 64 15, Src.opd 64 (.r 15)] 3) := by dec_rfl

/-- What the stretch does. -/
def o11 : List Op := [
  Op.ld 64 15 (some 14) none 1 24,
  Op.st 64 (some 14) none 1 0 1,
  Op.test 64 15 (.r 15)]

theorem b11 (prof : Profile) : Blk prof p11 0 10 o11 :=
  .cons (p11_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p11_4 _) (OpI.st (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p11_7 _) (OpI.test (.r 15) (.inr rfl)) (by decide) <|
  .nil 10

def j8 : List Byte := [0x0f, 0x84, 0x9c, 0x00, 0x00, 0x00]
theorem j8_0 : ∀ feat, Dec feat j8 0 (FV7z.mk (.jcc 4) 64 [.rel 156] 6) := by dec_rfl

/-- The stretch at `224`. -/
def p12 : List Byte := [
  0x49, 0x8b, 0x07, 0x48, 0x8b, 0x40, 0x10, 0x48, 0x39, 0xd0]

theorem p12_0 : ∀ feat, Dec feat p12 0 (FV7z.mk .mov 64 [gr 64 0, .mem (mg (some 15) none 1 0 64)] 3) := by dec_rfl
theorem p12_3 : ∀ feat, Dec feat p12 3 (FV7z.mk .mov 64 [gr 64 0, .mem (mg (some 0) none 1 16 64)] 4) := by dec_rfl
theorem p12_7 : ∀ feat, Dec feat p12 7 (FV7z.mk .cmp 64 [gr 64 0, Src.opd 64 (.r 2)] 3) := by dec_rfl

/-- What the stretch does. -/
def o12 : List Op := [
  Op.ld 64 0 (some 15) none 1 0,
  Op.ld 64 0 (some 0) none 1 16,
  Op.cmp 64 0 (.r 2)]

theorem b12 (prof : Profile) : Blk prof p12 0 10 o12 :=
  .cons (p12_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p12_3 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p12_7 _) (OpI.cmp (.r 2) (.inr rfl)) (by decide) <|
  .nil 10

def j9 : List Byte := [0x0f, 0x85, 0xe0, 0x00, 0x00, 0x00]
theorem j9_0 : ∀ feat, Dec feat j9 0 (FV7z.mk (.jcc 5) 64 [.rel 224] 6) := by dec_rfl

def j10 : List Byte := [0x0f, 0x85, 0x81, 0x00, 0x00, 0x00]
theorem j10_0 : ∀ feat, Dec feat j10 0 (FV7z.mk (.jcc 5) 64 [.rel 129] 6) := by dec_rfl

/-- The stretch at `251`. -/
def p13 : List Byte := [
  0x4d, 0x8b, 0x47, 0x18, 0x49, 0x89, 0x0f, 0x4d, 0x85, 0xc0]

theorem p13_0 : ∀ feat, Dec feat p13 0 (FV7z.mk .mov 64 [gr 64 8, .mem (mg (some 15) none 1 24 64)] 4) := by dec_rfl
theorem p13_4 : ∀ feat, Dec feat p13 4 (FV7z.mk .mov 64 [.mem (mg (some 15) none 1 0 64), gr 64 1] 3) := by dec_rfl
theorem p13_7 : ∀ feat, Dec feat p13 7 (FV7z.mk .test 64 [gr 64 8, Src.opd 64 (.r 8)] 3) := by dec_rfl

/-- What the stretch does. -/
def o13 : List Op := [
  Op.ld 64 8 (some 15) none 1 24,
  Op.st 64 (some 15) none 1 0 1,
  Op.test 64 8 (.r 8)]

theorem b13 (prof : Profile) : Blk prof p13 0 10 o13 :=
  .cons (p13_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p13_4 _) (OpI.st (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p13_7 _) (OpI.test (.r 8) (.inr rfl)) (by decide) <|
  .nil 10

def j11 : List Byte := [0x74, 0x59]
theorem j11_0 : ∀ feat, Dec feat j11 0 (FV7z.mk (.jcc 4) 64 [.rel 89] 2) := by dec_rfl

/-- The stretch at `263`. -/
def p14 : List Byte := [
  0x49, 0x8b, 0x00, 0x48, 0x8b, 0x40, 0x10, 0x48, 0x39, 0xd0]

theorem p14_0 : ∀ feat, Dec feat p14 0 (FV7z.mk .mov 64 [gr 64 0, .mem (mg (some 8) none 1 0 64)] 3) := by dec_rfl
theorem p14_3 : ∀ feat, Dec feat p14 3 (FV7z.mk .mov 64 [gr 64 0, .mem (mg (some 0) none 1 16 64)] 4) := by dec_rfl
theorem p14_7 : ∀ feat, Dec feat p14 7 (FV7z.mk .cmp 64 [gr 64 0, Src.opd 64 (.r 2)] 3) := by dec_rfl

/-- What the stretch does. -/
def o14 : List Op := [
  Op.ld 64 0 (some 8) none 1 0,
  Op.ld 64 0 (some 0) none 1 16,
  Op.cmp 64 0 (.r 2)]

theorem b14 (prof : Profile) : Blk prof p14 0 10 o14 :=
  .cons (p14_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p14_3 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p14_7 _) (OpI.cmp (.r 2) (.inr rfl)) (by decide) <|
  .nil 10

def j12 : List Byte := [0x0f, 0x85, 0xd0, 0x00, 0x00, 0x00]
theorem j12_0 : ∀ feat, Dec feat j12 0 (FV7z.mk (.jcc 5) 64 [.rel 208] 6) := by dec_rfl

def j13 : List Byte := [0x75, 0x42]
theorem j13_0 : ∀ feat, Dec feat j13 0 (FV7z.mk (.jcc 5) 64 [.rel 66] 2) := by dec_rfl

/-- The stretch at `286`. -/
def p15 : List Byte := [
  0x49, 0x8b, 0x78, 0x18, 0x49, 0x89, 0x08, 0x48, 0x85, 0xff]

theorem p15_0 : ∀ feat, Dec feat p15 0 (FV7z.mk .mov 64 [gr 64 7, .mem (mg (some 8) none 1 24 64)] 4) := by dec_rfl
theorem p15_4 : ∀ feat, Dec feat p15 4 (FV7z.mk .mov 64 [.mem (mg (some 8) none 1 0 64), gr 64 1] 3) := by dec_rfl
theorem p15_7 : ∀ feat, Dec feat p15 7 (FV7z.mk .test 64 [gr 64 7, Src.opd 64 (.r 7)] 3) := by dec_rfl

/-- What the stretch does. -/
def o15 : List Op := [
  Op.ld 64 7 (some 8) none 1 24,
  Op.st 64 (some 8) none 1 0 1,
  Op.test 64 7 (.r 7)]

theorem b15 (prof : Profile) : Blk prof p15 0 10 o15 :=
  .cons (p15_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p15_4 _) (OpI.st (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p15_7 _) (OpI.test (.r 7) (.inr rfl)) (by decide) <|
  .nil 10

def j14 : List Byte := [0x74, 0x10]
theorem j14_0 : ∀ feat, Dec feat j14 0 (FV7z.mk (.jcc 4) 64 [.rel 16] 2) := by dec_rfl

/-- The stretch at `298`. -/
def p16 : List Byte := [
  0x48, 0x8b, 0x07, 0x4c, 0x89, 0x44, 0x24, 0x08]

theorem p16_0 : ∀ feat, Dec feat p16 0 (FV7z.mk .mov 64 [gr 64 0, .mem (mg (some 7) none 1 0 64)] 3) := by dec_rfl
theorem p16_3 : ∀ feat, Dec feat p16 3 (FV7z.mk .mov 64 [.mem (mg (some 4) none 1 8 64), gr 64 8] 5) := by dec_rfl

/-- What the stretch does. -/
def o16 : List Op := [
  Op.ld 64 0 (some 7) none 1 0,
  Op.st 64 (some 4) none 1 8 8]

theorem b16 (prof : Profile) : Blk prof p16 0 8 o16 :=
  .cons (p16_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p16_3 _) (OpI.st (.inr (.inr (.inr rfl)))) (by decide) <|
  .nil 8

/-- The stretch at `309`. -/
def p17 : List Byte := [
  0x4c, 0x8b, 0x44, 0x24, 0x08]

theorem p17_0 : ∀ feat, Dec feat p17 0 (FV7z.mk .mov 64 [gr 64 8, .mem (mg (some 4) none 1 8 64)] 5) := by dec_rfl

/-- What the stretch does. -/
def o17 : List Op := [
  Op.ld 64 8 (some 4) none 1 8]

theorem b17 (prof : Profile) : Blk prof p17 0 5 o17 :=
  .cons (p17_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .nil 5

/-- The stretch at `314`. -/
def p18 : List Byte := [
  0x49, 0x8b, 0x78, 0x10, 0x48, 0x85, 0xff]

theorem p18_0 : ∀ feat, Dec feat p18 0 (FV7z.mk .mov 64 [gr 64 7, .mem (mg (some 8) none 1 16 64)] 4) := by dec_rfl
theorem p18_4 : ∀ feat, Dec feat p18 4 (FV7z.mk .test 64 [gr 64 7, Src.opd 64 (.r 7)] 3) := by dec_rfl

/-- What the stretch does. -/
def o18 : List Op := [
  Op.ld 64 7 (some 8) none 1 16,
  Op.test 64 7 (.r 7)]

theorem b18 (prof : Profile) : Blk prof p18 0 7 o18 :=
  .cons (p18_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p18_4 _) (OpI.test (.r 7) (.inr rfl)) (by decide) <|
  .nil 7

/-- The stretch at `339`. -/
def p19 : List Byte := [
  0xbe, 0x38, 0x00, 0x00, 0x00, 0x4c, 0x89, 0xc7]

theorem p19_0 : ∀ feat, Dec feat p19 0 (FV7z.mk .mov 32 [gr 32 6, Src.opd 32 (.i 56)] 5) := by dec_rfl
theorem p19_5 : ∀ feat, Dec feat p19 5 (FV7z.mk .mov 64 [gr 64 7, Src.opd 64 (.r 8)] 3) := by dec_rfl

/-- What the stretch does. -/
def o19 : List Op := [
  Op.mov 32 6 (.i 56),
  Op.mov 64 7 (.r 8)]

theorem b19 (prof : Profile) : Blk prof p19 0 8 o19 :=
  .cons (p19_0 _) (OpI.mov (.i 56) (.inl rfl)) (by decide) <|
  .cons (p19_5 _) (OpI.mov (.r 8) (.inr rfl)) (by decide) <|
  .nil 8

/-- The stretch at `352`. -/
def p20 : List Byte := [
  0x49, 0x8b, 0x7f, 0x10, 0x48, 0x85, 0xff]

theorem p20_0 : ∀ feat, Dec feat p20 0 (FV7z.mk .mov 64 [gr 64 7, .mem (mg (some 15) none 1 16 64)] 4) := by dec_rfl
theorem p20_4 : ∀ feat, Dec feat p20 4 (FV7z.mk .test 64 [gr 64 7, Src.opd 64 (.r 7)] 3) := by dec_rfl

/-- What the stretch does. -/
def o20 : List Op := [
  Op.ld 64 7 (some 15) none 1 16,
  Op.test 64 7 (.r 7)]

theorem b20 (prof : Profile) : Blk prof p20 0 7 o20 :=
  .cons (p20_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p20_4 _) (OpI.test (.r 7) (.inr rfl)) (by decide) <|
  .nil 7

/-- The stretch at `367`. -/
def p21 : List Byte := [
  0xbe, 0x38, 0x00, 0x00, 0x00, 0x4c, 0x89, 0xff]

theorem p21_0 : ∀ feat, Dec feat p21 0 (FV7z.mk .mov 32 [gr 32 6, Src.opd 32 (.i 56)] 5) := by dec_rfl
theorem p21_5 : ∀ feat, Dec feat p21 5 (FV7z.mk .mov 64 [gr 64 7, Src.opd 64 (.r 15)] 3) := by dec_rfl

/-- What the stretch does. -/
def o21 : List Op := [
  Op.mov 32 6 (.i 56),
  Op.mov 64 7 (.r 15)]

theorem b21 (prof : Profile) : Blk prof p21 0 8 o21 :=
  .cons (p21_0 _) (OpI.mov (.i 56) (.inl rfl)) (by decide) <|
  .cons (p21_5 _) (OpI.mov (.r 15) (.inr rfl)) (by decide) <|
  .nil 8

/-- The stretch at `380`. -/
def p22 : List Byte := [
  0x49, 0x8b, 0x7e, 0x10, 0x48, 0x85, 0xff]

theorem p22_0 : ∀ feat, Dec feat p22 0 (FV7z.mk .mov 64 [gr 64 7, .mem (mg (some 14) none 1 16 64)] 4) := by dec_rfl
theorem p22_4 : ∀ feat, Dec feat p22 4 (FV7z.mk .test 64 [gr 64 7, Src.opd 64 (.r 7)] 3) := by dec_rfl

/-- What the stretch does. -/
def o22 : List Op := [
  Op.ld 64 7 (some 14) none 1 16,
  Op.test 64 7 (.r 7)]

theorem b22 (prof : Profile) : Blk prof p22 0 7 o22 :=
  .cons (p22_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p22_4 _) (OpI.test (.r 7) (.inr rfl)) (by decide) <|
  .nil 7

/-- The stretch at `395`. -/
def p23 : List Byte := [
  0xbe, 0x38, 0x00, 0x00, 0x00, 0x4c, 0x89, 0xf7]

theorem p23_0 : ∀ feat, Dec feat p23 0 (FV7z.mk .mov 32 [gr 32 6, Src.opd 32 (.i 56)] 5) := by dec_rfl
theorem p23_5 : ∀ feat, Dec feat p23 5 (FV7z.mk .mov 64 [gr 64 7, Src.opd 64 (.r 14)] 3) := by dec_rfl

/-- What the stretch does. -/
def o23 : List Op := [
  Op.mov 32 6 (.i 56),
  Op.mov 64 7 (.r 14)]

theorem b23 (prof : Profile) : Blk prof p23 0 8 o23 :=
  .cons (p23_0 _) (OpI.mov (.i 56) (.inl rfl)) (by decide) <|
  .cons (p23_5 _) (OpI.mov (.r 14) (.inr rfl)) (by decide) <|
  .nil 8

/-- The stretch at `408`. -/
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

/-- The stretch at `424`. -/
def p25 : List Byte := [
  0xbe, 0x38, 0x00, 0x00, 0x00, 0x4c, 0x89, 0xe7]

theorem p25_0 : ∀ feat, Dec feat p25 0 (FV7z.mk .mov 32 [gr 32 6, Src.opd 32 (.i 56)] 5) := by dec_rfl
theorem p25_5 : ∀ feat, Dec feat p25 5 (FV7z.mk .mov 64 [gr 64 7, Src.opd 64 (.r 12)] 3) := by dec_rfl

/-- What the stretch does. -/
def o25 : List Op := [
  Op.mov 32 6 (.i 56),
  Op.mov 64 7 (.r 12)]

theorem b25 (prof : Profile) : Blk prof p25 0 8 o25 :=
  .cons (p25_0 _) (OpI.mov (.i 56) (.inl rfl)) (by decide) <|
  .cons (p25_5 _) (OpI.mov (.r 12) (.inr rfl)) (by decide) <|
  .nil 8

def j15 : List Byte := [0xe9, 0x8a, 0xfe, 0xff, 0xff]
theorem j15_0 : ∀ feat, Dec feat j15 0 (FV7z.mk .jmp 64 [.rel 18446744073709551242] 5) := by dec_rfl

/-- The stretch at `448`. -/
def p26 : List Byte := [
  0x4c, 0x89, 0xe7]

theorem p26_0 : ∀ feat, Dec feat p26 0 (FV7z.mk .mov 64 [gr 64 7, Src.opd 64 (.r 12)] 3) := by dec_rfl

/-- What the stretch does. -/
def o26 : List Op := [
  Op.mov 64 7 (.r 12)]

theorem b26 (prof : Profile) : Blk prof p26 0 3 o26 :=
  .cons (p26_0 _) (OpI.mov (.r 12) (.inr rfl)) (by decide) <|
  .nil 3

def j16 : List Byte := [0xe9, 0x7a, 0xfe, 0xff, 0xff]
theorem j16_0 : ∀ feat, Dec feat j16 0 (FV7z.mk .jmp 64 [.rel 18446744073709551226] 5) := by dec_rfl

/-- The stretch at `464`. -/
def p27 : List Byte := [
  0x4c, 0x89, 0xff]

theorem p27_0 : ∀ feat, Dec feat p27 0 (FV7z.mk .mov 64 [gr 64 7, Src.opd 64 (.r 15)] 3) := by dec_rfl

/-- What the stretch does. -/
def o27 : List Op := [
  Op.mov 64 7 (.r 15)]

theorem b27 (prof : Profile) : Blk prof p27 0 3 o27 :=
  .cons (p27_0 _) (OpI.mov (.r 15) (.inr rfl)) (by decide) <|
  .nil 3

def j17 : List Byte := [0xeb, 0xa5]
theorem j17_0 : ∀ feat, Dec feat j17 0 (FV7z.mk .jmp 64 [.rel 18446744073709551525] 2) := by dec_rfl

/-- The stretch at `480`. -/
def p28 : List Byte := [
  0x4c, 0x89, 0xf7]

theorem p28_0 : ∀ feat, Dec feat p28 0 (FV7z.mk .mov 64 [gr 64 7, Src.opd 64 (.r 14)] 3) := by dec_rfl

/-- What the stretch does. -/
def o28 : List Op := [
  Op.mov 64 7 (.r 14)]

theorem b28 (prof : Profile) : Blk prof p28 0 3 o28 :=
  .cons (p28_0 _) (OpI.mov (.r 14) (.inr rfl)) (by decide) <|
  .nil 3

def j18 : List Byte := [0xeb, 0xb1]
theorem j18_0 : ∀ feat, Dec feat j18 0 (FV7z.mk .jmp 64 [.rel 18446744073709551537] 2) := by dec_rfl

/-- The stretch at `487`. -/
def p29 : List Byte := [
  0x4c, 0x89, 0xc7]

theorem p29_0 : ∀ feat, Dec feat p29 0 (FV7z.mk .mov 64 [gr 64 7, Src.opd 64 (.r 8)] 3) := by dec_rfl

/-- What the stretch does. -/
def o29 : List Op := [
  Op.mov 64 7 (.r 8)]

theorem b29 (prof : Profile) : Blk prof p29 0 3 o29 :=
  .cons (p29_0 _) (OpI.mov (.r 8) (.inr rfl)) (by decide) <|
  .nil 3

def j19 : List Byte := [0xe9, 0x6f, 0xff, 0xff, 0xff]
theorem j19_0 : ∀ feat, Dec feat j19 0 (FV7z.mk .jmp 64 [.rel 18446744073709551471] 5) := by dec_rfl

end FV7z.Clp
