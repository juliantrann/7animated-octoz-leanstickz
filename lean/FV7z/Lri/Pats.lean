import FV7z.Lemmas.Sp
import FV7z.Lemmas.BlkOps2
/-!
# The stretches of straight-line code of `NCompress::NLzma::CDecoder::ReadFromInputStream` (PLAN.md §M, M1)

Each distinct stretch between labels and jumps (`p*`, 14 of them) and each distinct jump (`j*`, 10) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.Lri
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The stretch at `0`. -/
def p0 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0x41, 0x57, 0x41, 0x89, 0xd7, 0x41, 0x56, 0x49, 0x89, 0xfe, 0x41, 0x55,
  0x49, 0x89, 0xf5, 0x41, 0x54, 0x55, 0x48, 0x89, 0xcd, 0x53, 0x48, 0x83, 0xec, 0x18]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem p0_4 : ∀ feat, Dec feat p0 4 (FV7z.mk .push 64 [gr 64 15] 2) := by dec_rfl
theorem p0_6 : ∀ feat, Dec feat p0 6 (FV7z.mk .mov 32 [gr 32 15, Src.opd 32 (.r 2)] 3) := by dec_rfl
theorem p0_9 : ∀ feat, Dec feat p0 9 (FV7z.mk .push 64 [gr 64 14] 2) := by dec_rfl
theorem p0_11 : ∀ feat, Dec feat p0 11 (FV7z.mk .mov 64 [gr 64 14, Src.opd 64 (.r 7)] 3) := by dec_rfl
theorem p0_14 : ∀ feat, Dec feat p0 14 (FV7z.mk .push 64 [gr 64 13] 2) := by dec_rfl
theorem p0_16 : ∀ feat, Dec feat p0 16 (FV7z.mk .mov 64 [gr 64 13, Src.opd 64 (.r 6)] 3) := by dec_rfl
theorem p0_19 : ∀ feat, Dec feat p0 19 (FV7z.mk .push 64 [gr 64 12] 2) := by dec_rfl
theorem p0_21 : ∀ feat, Dec feat p0 21 (FV7z.mk .push 64 [gr 64 5] 1) := by dec_rfl
theorem p0_22 : ∀ feat, Dec feat p0 22 (FV7z.mk .mov 64 [gr 64 5, Src.opd 64 (.r 1)] 3) := by dec_rfl
theorem p0_25 : ∀ feat, Dec feat p0 25 (FV7z.mk .push 64 [gr 64 3] 1) := by dec_rfl
theorem p0_26 : ∀ feat, Dec feat p0 26 (FV7z.mk .sub 64 [gr 64 4, Src.opd 64 (.i 24)] 4) := by dec_rfl

/-- What the stretch does. -/
def o0 : List Op := [
  Op.nop,
  Op.push 15,
  Op.mov 32 15 (.r 2),
  Op.push 14,
  Op.mov 64 14 (.r 7),
  Op.push 13,
  Op.mov 64 13 (.r 6),
  Op.push 12,
  Op.push 5,
  Op.mov 64 5 (.r 1),
  Op.push 3,
  Op.sub 64 4 (.i 24)]

theorem b0 (prof : Profile) : Blk prof p0 0 30 o0 :=
  .cons (p0_0 _) (OpI.endbr) (by decide) <|
  .cons (p0_4 _) (OpI.push) (by decide) <|
  .cons (p0_6 _) (OpI.mov (.r 2) (.inl rfl)) (by decide) <|
  .cons (p0_9 _) (OpI.push) (by decide) <|
  .cons (p0_11 _) (OpI.mov (.r 7) (.inr rfl)) (by decide) <|
  .cons (p0_14 _) (OpI.push) (by decide) <|
  .cons (p0_16 _) (OpI.mov (.r 6) (.inr rfl)) (by decide) <|
  .cons (p0_19 _) (OpI.push) (by decide) <|
  .cons (p0_21 _) (OpI.push) (by decide) <|
  .cons (p0_22 _) (OpI.mov (.r 1) (.inr rfl)) (by decide) <|
  .cons (p0_25 _) (OpI.push) (by decide) <|
  .cons (p0_26 _) (OpI.sub (.i 24) (.inr rfl)) (by decide) <|
  .nil 30

/-- The stretch at `35`. -/
def p1 : List Byte := [
  0x89, 0x44, 0x24, 0x0c, 0x85, 0xc0]

theorem p1_0 : ∀ feat, Dec feat p1 0 (FV7z.mk .mov 32 [.mem (mg (some 4) none 1 12 32), gr 32 0] 4) := by dec_rfl
theorem p1_4 : ∀ feat, Dec feat p1 4 (FV7z.mk .test 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl

/-- What the stretch does. -/
def o1 : List Op := [
  Op.st 32 (some 4) none 1 12 0,
  Op.test 32 0 (.r 0)]

theorem b1 (prof : Profile) : Blk prof p1 0 6 o1 :=
  .cons (p1_0 _) (OpI.st (.inr (.inr (.inl rfl)))) (by decide) <|
  .cons (p1_4 _) (OpI.test (.r 0) (.inl rfl)) (by decide) <|
  .nil 6

def j0 : List Byte := [0x75, 0x36]
theorem j0_0 : ∀ feat, Dec feat j0 0 (FV7z.mk (.jcc 5) 64 [.rel 54] 2) := by dec_rfl

/-- The stretch at `43`. -/
def p2 : List Byte := [
  0x48, 0x85, 0xed]

theorem p2_0 : ∀ feat, Dec feat p2 0 (FV7z.mk .test 64 [gr 64 5, Src.opd 64 (.r 5)] 3) := by dec_rfl

/-- What the stretch does. -/
def o2 : List Op := [
  Op.test 64 5 (.r 5)]

theorem b2 (prof : Profile) : Blk prof p2 0 3 o2 :=
  .cons (p2_0 _) (OpI.test (.r 5) (.inr rfl)) (by decide) <|
  .nil 3

def j1 : List Byte := [0x74, 0x10]
theorem j1_0 : ∀ feat, Dec feat j1 0 (FV7z.mk (.jcc 4) 64 [.rel 16] 2) := by dec_rfl

/-- The stretch at `48`. -/
def p3 : List Byte := [
  0xc7, 0x45, 0x00, 0x00, 0x00, 0x00, 0x00, 0x66, 0x0f, 0x1f, 0x84, 0x00, 0x00, 0x00, 0x00, 0x00]

theorem p3_0 : ∀ feat, Dec feat p3 0 (FV7z.mk .mov 32 [.mem (mg (some 5) none 1 0 32), .imm 32 0] 7) := by dec_rfl
theorem p3_7 : ∀ feat, Dec feat p3 7 (FV7z.mk .nop 16 [.mem (mg (some 0) (some 0) 1 0 16)] 9) := by dec_rfl

/-- What the stretch does. -/
def o3 : List Op := [
  Op.sti 32 (some 5) none 1 0 0,
  Op.nop]

theorem b3 (prof : Profile) : Blk prof p3 0 16 o3 :=
  .cons (p3_0 _) (OpI.sti (.inr (.inr (.inl rfl)))) (by decide) <|
  .cons (p3_7 _) (OpI.nop) (by decide) <|
  .nil 16

/-- The stretch at `64`. -/
def p4 : List Byte := [
  0x45, 0x85, 0xff]

theorem p4_0 : ∀ feat, Dec feat p4 0 (FV7z.mk .test 32 [gr 32 15, Src.opd 32 (.r 15)] 3) := by dec_rfl

/-- What the stretch does. -/
def o4 : List Op := [
  Op.test 32 15 (.r 15)]

theorem b4 (prof : Profile) : Blk prof p4 0 3 o4 :=
  .cons (p4_0 _) (OpI.test (.r 15) (.inl rfl)) (by decide) <|
  .nil 3

def j2 : List Byte := [0x74, 0x1c]
theorem j2_0 : ∀ feat, Dec feat j2 0 (FV7z.mk (.jcc 4) 64 [.rel 28] 2) := by dec_rfl

/-- The stretch at `69`. -/
def p5 : List Byte := [
  0x41, 0x8b, 0x76, 0x58, 0x41, 0x8b, 0x5e, 0x5c, 0x39, 0xde]

theorem p5_0 : ∀ feat, Dec feat p5 0 (FV7z.mk .mov 32 [gr 32 6, .mem (mg (some 14) none 1 88 32)] 4) := by dec_rfl
theorem p5_4 : ∀ feat, Dec feat p5 4 (FV7z.mk .mov 32 [gr 32 3, .mem (mg (some 14) none 1 92 32)] 4) := by dec_rfl
theorem p5_8 : ∀ feat, Dec feat p5 8 (FV7z.mk .cmp 32 [gr 32 6, Src.opd 32 (.r 3)] 2) := by dec_rfl

/-- What the stretch does. -/
def o5 : List Op := [
  Op.ld 32 6 (some 14) none 1 88,
  Op.ld 32 3 (some 14) none 1 92,
  Op.cmp 32 6 (.r 3)]

theorem b5 (prof : Profile) : Blk prof p5 0 10 o5 :=
  .cons (p5_0 _) (OpI.ld (.inl rfl)) (by decide) <|
  .cons (p5_4 _) (OpI.ld (.inl rfl)) (by decide) <|
  .cons (p5_8 _) (OpI.cmp (.r 3) (.inl rfl)) (by decide) <|
  .nil 10

def j3 : List Byte := [0x75, 0x66]
theorem j3_0 : ∀ feat, Dec feat j3 0 (FV7z.mk (.jcc 5) 64 [.rel 102] 2) := by dec_rfl

/-- The stretch at `81`. -/
def p6 : List Byte := [
  0x8b, 0x44, 0x24, 0x0c, 0x49, 0xc7, 0x46, 0x58, 0x00, 0x00, 0x00, 0x00, 0x85, 0xc0]

theorem p6_0 : ∀ feat, Dec feat p6 0 (FV7z.mk .mov 32 [gr 32 0, .mem (mg (some 4) none 1 12 32)] 4) := by dec_rfl
theorem p6_4 : ∀ feat, Dec feat p6 4 (FV7z.mk .mov 64 [.mem (mg (some 14) none 1 88 64), .imm 64 0] 8) := by dec_rfl
theorem p6_12 : ∀ feat, Dec feat p6 12 (FV7z.mk .test 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl

/-- What the stretch does. -/
def o6 : List Op := [
  Op.ld 32 0 (some 4) none 1 12,
  Op.sti 64 (some 14) none 1 88 0,
  Op.test 32 0 (.r 0)]

theorem b6 (prof : Profile) : Blk prof p6 0 14 o6 :=
  .cons (p6_0 _) (OpI.ld (.inl rfl)) (by decide) <|
  .cons (p6_4 _) (OpI.sti (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p6_12 _) (OpI.test (.r 0) (.inl rfl)) (by decide) <|
  .nil 14

def j4 : List Byte := [0x74, 0x17]
theorem j4_0 : ∀ feat, Dec feat j4 0 (FV7z.mk (.jcc 4) 64 [.rel 23] 2) := by dec_rfl

/-- The stretch at `97`. -/
def p7 : List Byte := [
  0x8b, 0x44, 0x24, 0x0c, 0x48, 0x83, 0xc4, 0x18, 0x5b, 0x5d, 0x41, 0x5c, 0x41, 0x5d, 0x41, 0x5e,
  0x41, 0x5f]

theorem p7_0 : ∀ feat, Dec feat p7 0 (FV7z.mk .mov 32 [gr 32 0, .mem (mg (some 4) none 1 12 32)] 4) := by dec_rfl
theorem p7_4 : ∀ feat, Dec feat p7 4 (FV7z.mk .add 64 [gr 64 4, Src.opd 64 (.i 24)] 4) := by dec_rfl
theorem p7_8 : ∀ feat, Dec feat p7 8 (FV7z.mk .pop 64 [gr 64 3] 1) := by dec_rfl
theorem p7_9 : ∀ feat, Dec feat p7 9 (FV7z.mk .pop 64 [gr 64 5] 1) := by dec_rfl
theorem p7_10 : ∀ feat, Dec feat p7 10 (FV7z.mk .pop 64 [gr 64 12] 2) := by dec_rfl
theorem p7_12 : ∀ feat, Dec feat p7 12 (FV7z.mk .pop 64 [gr 64 13] 2) := by dec_rfl
theorem p7_14 : ∀ feat, Dec feat p7 14 (FV7z.mk .pop 64 [gr 64 14] 2) := by dec_rfl
theorem p7_16 : ∀ feat, Dec feat p7 16 (FV7z.mk .pop 64 [gr 64 15] 2) := by dec_rfl

/-- What the stretch does. -/
def o7 : List Op := [
  Op.ld 32 0 (some 4) none 1 12,
  Op.add 64 4 (.i 24),
  Op.pop 3,
  Op.pop 5,
  Op.pop 12,
  Op.pop 13,
  Op.pop 14,
  Op.pop 15]

theorem b7 (prof : Profile) : Blk prof p7 0 18 o7 :=
  .cons (p7_0 _) (OpI.ld (.inl rfl)) (by decide) <|
  .cons (p7_4 _) (OpI.add (.i 24) (.inr rfl)) (by decide) <|
  .cons (p7_8 _) (OpI.pop) (by decide) <|
  .cons (p7_9 _) (OpI.pop) (by decide) <|
  .cons (p7_10 _) (OpI.pop) (by decide) <|
  .cons (p7_12 _) (OpI.pop) (by decide) <|
  .cons (p7_14 _) (OpI.pop) (by decide) <|
  .cons (p7_16 _) (OpI.pop) (by decide) <|
  .nil 18

/-- The stretch at `120`. -/
def p8 : List Byte := [
  0x49, 0x8b, 0xbe, 0x00, 0x01, 0x00, 0x00, 0x48, 0x8d, 0x1d, 0xea, 0xf8, 0xff, 0xff, 0x41, 0x8b,
  0x56, 0x4c, 0x49, 0x8d, 0x4e, 0x5c, 0x49, 0x8b, 0x76, 0x60, 0x48, 0x8b, 0x07, 0x48, 0x8b, 0x40,
  0x18, 0x48, 0x39, 0xd8]

theorem p8_0 : ∀ feat, Dec feat p8 0 (FV7z.mk .mov 64 [gr 64 7, .mem (mg (some 14) none 1 256 64)] 7) := by dec_rfl
theorem p8_7 : ∀ feat, Dec feat p8 7 (FV7z.mk .lea 64 [gr 64 3, .mem (mrip 18446744073709549802 0)] 7) := by dec_rfl
theorem p8_14 : ∀ feat, Dec feat p8 14 (FV7z.mk .mov 32 [gr 32 2, .mem (mg (some 14) none 1 76 32)] 4) := by dec_rfl
theorem p8_18 : ∀ feat, Dec feat p8 18 (FV7z.mk .lea 64 [gr 64 1, .mem (mg (some 14) none 1 92 0)] 4) := by dec_rfl
theorem p8_22 : ∀ feat, Dec feat p8 22 (FV7z.mk .mov 64 [gr 64 6, .mem (mg (some 14) none 1 96 64)] 4) := by dec_rfl
theorem p8_26 : ∀ feat, Dec feat p8 26 (FV7z.mk .mov 64 [gr 64 0, .mem (mg (some 7) none 1 0 64)] 3) := by dec_rfl
theorem p8_29 : ∀ feat, Dec feat p8 29 (FV7z.mk .mov 64 [gr 64 0, .mem (mg (some 0) none 1 24 64)] 4) := by dec_rfl
theorem p8_33 : ∀ feat, Dec feat p8 33 (FV7z.mk .cmp 64 [gr 64 0, Src.opd 64 (.r 3)] 3) := by dec_rfl

/-- What the stretch does. -/
def o8 : List Op := [
  Op.ld 64 7 (some 14) none 1 256,
  Op.mov 64 3 (.i 5765984),
  Op.ld 32 2 (some 14) none 1 76,
  Op.lea 64 1 (some 14) none 1 92,
  Op.ld 64 6 (some 14) none 1 96,
  Op.ld 64 0 (some 7) none 1 0,
  Op.ld 64 0 (some 0) none 1 24,
  Op.cmp 64 0 (.r 3)]

theorem b8 (prof : Profile) : BlkA prof p8 (0x580268 : Addr) 0 36 o8 :=
  .cons (p8_0 _) ((OpI.ld (.inr rfl)).at _) (by decide) <|
  .cons (p8_7 _) (OpIA.lea_rip (by decide)) (by decide) <|
  .cons (p8_14 _) ((OpI.ld (.inl rfl)).at _) (by decide) <|
  .cons (p8_18 _) ((OpI.lea (.inr rfl)).at _) (by decide) <|
  .cons (p8_22 _) ((OpI.ld (.inr rfl)).at _) (by decide) <|
  .cons (p8_26 _) ((OpI.ld (.inr rfl)).at _) (by decide) <|
  .cons (p8_29 _) ((OpI.ld (.inr rfl)).at _) (by decide) <|
  .cons (p8_33 _) ((OpI.cmp (.r 3) (.inr rfl)).at _) (by decide) <|
  .nil 36

def j5 : List Byte := [0x75, 0x5a]
theorem j5_0 : ∀ feat, Dec feat j5 0 (FV7z.mk (.jcc 5) 64 [.rel 90] 2) := by dec_rfl

/-- The stretch at `158`. -/
def p9 : List Byte := [
  0x48, 0x83, 0xef, 0x38]

theorem p9_0 : ∀ feat, Dec feat p9 0 (FV7z.mk .sub 64 [gr 64 7, Src.opd 64 (.i 56)] 4) := by dec_rfl

/-- What the stretch does. -/
def o9 : List Op := [
  Op.sub 64 7 (.i 56)]

theorem b9 (prof : Profile) : Blk prof p9 0 4 o9 :=
  .cons (p9_0 _) (OpI.sub (.i 56) (.inr rfl)) (by decide) <|
  .nil 4

/-- The stretch at `167`. -/
def p10 : List Byte := [
  0x89, 0x44, 0x24, 0x0c]

theorem p10_0 : ∀ feat, Dec feat p10 0 (FV7z.mk .mov 32 [.mem (mg (some 4) none 1 12 32), gr 32 0] 4) := by dec_rfl

/-- What the stretch does. -/
def o10 : List Op := [
  Op.st 32 (some 4) none 1 12 0]

theorem b10 (prof : Profile) : Blk prof p10 0 4 o10 :=
  .cons (p10_0 _) (OpI.st (.inr (.inr (.inl rfl)))) (by decide) <|
  .nil 4

/-- The stretch at `171`. -/
def p11 : List Byte := [
  0x41, 0x8b, 0x5e, 0x5c, 0x85, 0xdb]

theorem p11_0 : ∀ feat, Dec feat p11 0 (FV7z.mk .mov 32 [gr 32 3, .mem (mg (some 14) none 1 92 32)] 4) := by dec_rfl
theorem p11_4 : ∀ feat, Dec feat p11 4 (FV7z.mk .test 32 [gr 32 3, Src.opd 32 (.r 3)] 2) := by dec_rfl

/-- What the stretch does. -/
def o11 : List Op := [
  Op.ld 32 3 (some 14) none 1 92,
  Op.test 32 3 (.r 3)]

theorem b11 (prof : Profile) : Blk prof p11 0 6 o11 :=
  .cons (p11_0 _) (OpI.ld (.inl rfl)) (by decide) <|
  .cons (p11_4 _) (OpI.test (.r 3) (.inl rfl)) (by decide) <|
  .nil 6

def j6 : List Byte := [0x74, 0xae]
theorem j6_0 : ∀ feat, Dec feat j6 0 (FV7z.mk (.jcc 4) 64 [.rel 18446744073709551534] 2) := by dec_rfl

/-- The stretch at `179`. -/
def p12 : List Byte := [
  0x41, 0x8b, 0x76, 0x58]

theorem p12_0 : ∀ feat, Dec feat p12 0 (FV7z.mk .mov 32 [gr 32 6, .mem (mg (some 14) none 1 88 32)] 4) := by dec_rfl

/-- What the stretch does. -/
def o12 : List Op := [
  Op.ld 32 6 (some 14) none 1 88]

theorem b12 (prof : Profile) : Blk prof p12 0 4 o12 :=
  .cons (p12_0 _) (OpI.ld (.inl rfl)) (by decide) <|
  .nil 4

/-- The stretch at `183`. -/
def p13 : List Byte := [
  0x29, 0xf3, 0x4c, 0x89, 0xef, 0x41, 0x39, 0xdf, 0x41, 0x0f, 0x46, 0xdf, 0x49, 0x03, 0x76, 0x60,
  0x41, 0x89, 0xdc, 0x41, 0x29, 0xdf, 0x4c, 0x89, 0xe2, 0x4d, 0x01, 0xe5]

theorem p13_0 : ∀ feat, Dec feat p13 0 (FV7z.mk .sub 32 [gr 32 3, Src.opd 32 (.r 6)] 2) := by dec_rfl
theorem p13_2 : ∀ feat, Dec feat p13 2 (FV7z.mk .mov 64 [gr 64 7, Src.opd 64 (.r 13)] 3) := by dec_rfl
theorem p13_5 : ∀ feat, Dec feat p13 5 (FV7z.mk .cmp 32 [gr 32 15, Src.opd 32 (.r 3)] 3) := by dec_rfl
theorem p13_8 : ∀ feat, Dec feat p13 8 (FV7z.mk (.cmovcc 6) 32 [gr 32 3, gr 32 15] 4) := by dec_rfl
theorem p13_12 : ∀ feat, Dec feat p13 12 (FV7z.mk .add 64 [gr 64 6, .mem (mg (some 14) none 1 96 64)] 4) := by dec_rfl
theorem p13_16 : ∀ feat, Dec feat p13 16 (FV7z.mk .mov 32 [gr 32 12, Src.opd 32 (.r 3)] 3) := by dec_rfl
theorem p13_19 : ∀ feat, Dec feat p13 19 (FV7z.mk .sub 32 [gr 32 15, Src.opd 32 (.r 3)] 3) := by dec_rfl
theorem p13_22 : ∀ feat, Dec feat p13 22 (FV7z.mk .mov 64 [gr 64 2, Src.opd 64 (.r 12)] 3) := by dec_rfl
theorem p13_25 : ∀ feat, Dec feat p13 25 (FV7z.mk .add 64 [gr 64 13, Src.opd 64 (.r 12)] 3) := by dec_rfl

/-- What the stretch does. -/
def o13 : List Op := [
  Op.sub 32 3 (.r 6),
  Op.mov 64 7 (.r 13),
  Op.cmp 32 15 (.r 3),
  Op.cmov32 6 3 15,
  Op.addm 64 6 (some 14) none 1 96,
  Op.mov 32 12 (.r 3),
  Op.sub 32 15 (.r 3),
  Op.mov 64 2 (.r 12),
  Op.add 64 13 (.r 12)]

theorem b13 (prof : Profile) : Blk prof p13 0 28 o13 :=
  .cons (p13_0 _) (OpI.sub (.r 6) (.inl rfl)) (by decide) <|
  .cons (p13_2 _) (OpI.mov (.r 13) (.inr rfl)) (by decide) <|
  .cons (p13_5 _) (OpI.cmp (.r 3) (.inl rfl)) (by decide) <|
  .cons (p13_8 _) (OpI.cmov32) (by decide) <|
  .cons (p13_12 _) (OpI.addm (.inr rfl)) (by decide) <|
  .cons (p13_16 _) (OpI.mov (.r 3) (.inl rfl)) (by decide) <|
  .cons (p13_19 _) (OpI.sub (.r 3) (.inl rfl)) (by decide) <|
  .cons (p13_22 _) (OpI.mov (.r 12) (.inr rfl)) (by decide) <|
  .cons (p13_25 _) (OpI.add (.r 12) (.inr rfl)) (by decide) <|
  .nil 28

def j7 : List Byte := [0x0f, 0x84, 0x57, 0xff, 0xff, 0xff]
theorem j7_0 : ∀ feat, Dec feat j7 0 (FV7z.mk (.jcc 4) 64 [.rel 18446744073709551447] 6) := by dec_rfl

def j8 : List Byte := [0xe9, 0x4f, 0xff, 0xff, 0xff]
theorem j8_0 : ∀ feat, Dec feat j8 0 (FV7z.mk .jmp 64 [.rel 18446744073709551439] 5) := by dec_rfl

def j9 : List Byte := [0xeb, 0xab]
theorem j9_0 : ∀ feat, Dec feat j9 0 (FV7z.mk .jmp 64 [.rel 18446744073709551531] 2) := by dec_rfl

end FV7z.Lri
