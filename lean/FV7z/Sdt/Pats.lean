import FV7z.Lemmas.Sp
import FV7z.Lemmas.BlkOps12
import FV7z.Lemmas.BlkOps3
/-!
# The stretches of straight-line code of `CArchiveExtractCallback::SetDirsTimes` (PLAN.md §M, M1)

Each distinct stretch between labels and jumps (`p*`, 50 of them) and each distinct jump (`j*`, 34) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.Sdt
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The stretch at `0`. -/
def p0 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0x48, 0x83, 0x7f, 0x40, 0x00]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem p0_4 : ∀ feat, Dec feat p0 4 (FV7z.mk .cmp 64 [.mem (mg (some 7) none 1 64 64), .imm 64 0] 5) := by dec_rfl

/-- What the stretch does. -/
def o0 : List Op := [
  Op.nop,
  Op.cmpmi 64 (some 7) none 1 64 0]

theorem b0 (prof : Profile) : Blk prof p0 0 9 o0 :=
  .cons (p0_0 _) (OpI.endbr) (by decide) <|
  .cons (p0_4 _) (OpI.cmpmi64) (by decide) <|
  .nil 9

def j0 : List Byte := [0x0f, 0x84, 0xa1, 0x02, 0x00, 0x00]
theorem j0_0 : ∀ feat, Dec feat j0 0 (FV7z.mk (.jcc 4) 64 [.rel 673] 6) := by dec_rfl

/-- The stretch at `15`. -/
def p1 : List Byte := [
  0x41, 0x57, 0x41, 0x56, 0x41, 0x55, 0x41, 0x54, 0x55, 0x53, 0x48, 0x89, 0xfb, 0x48, 0x83, 0xec,
  0x18, 0x8b, 0x87, 0x20, 0x02, 0x00, 0x00, 0x89, 0x44, 0x24, 0x0c, 0x85, 0xc0]

theorem p1_0 : ∀ feat, Dec feat p1 0 (FV7z.mk .push 64 [gr 64 15] 2) := by dec_rfl
theorem p1_2 : ∀ feat, Dec feat p1 2 (FV7z.mk .push 64 [gr 64 14] 2) := by dec_rfl
theorem p1_4 : ∀ feat, Dec feat p1 4 (FV7z.mk .push 64 [gr 64 13] 2) := by dec_rfl
theorem p1_6 : ∀ feat, Dec feat p1 6 (FV7z.mk .push 64 [gr 64 12] 2) := by dec_rfl
theorem p1_8 : ∀ feat, Dec feat p1 8 (FV7z.mk .push 64 [gr 64 5] 1) := by dec_rfl
theorem p1_9 : ∀ feat, Dec feat p1 9 (FV7z.mk .push 64 [gr 64 3] 1) := by dec_rfl
theorem p1_10 : ∀ feat, Dec feat p1 10 (FV7z.mk .mov 64 [gr 64 3, Src.opd 64 (.r 7)] 3) := by dec_rfl
theorem p1_13 : ∀ feat, Dec feat p1 13 (FV7z.mk .sub 64 [gr 64 4, Src.opd 64 (.i 24)] 4) := by dec_rfl
theorem p1_17 : ∀ feat, Dec feat p1 17 (FV7z.mk .mov 32 [gr 32 0, .mem (mg (some 7) none 1 544 32)] 6) := by dec_rfl
theorem p1_23 : ∀ feat, Dec feat p1 23 (FV7z.mk .mov 32 [.mem (mg (some 4) none 1 12 32), gr 32 0] 4) := by dec_rfl
theorem p1_27 : ∀ feat, Dec feat p1 27 (FV7z.mk .test 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl

/-- What the stretch does. -/
def o1 : List Op := [
  Op.push 15,
  Op.push 14,
  Op.push 13,
  Op.push 12,
  Op.push 5,
  Op.push 3,
  Op.mov 64 3 (.r 7),
  Op.sub 64 4 (.i 24),
  Op.ld 32 0 (some 7) none 1 544,
  Op.st 32 (some 4) none 1 12 0,
  Op.test 32 0 (.r 0)]

theorem b1 (prof : Profile) : Blk prof p1 0 29 o1 :=
  .cons (p1_0 _) (OpI.push) (by decide) <|
  .cons (p1_2 _) (OpI.push) (by decide) <|
  .cons (p1_4 _) (OpI.push) (by decide) <|
  .cons (p1_6 _) (OpI.push) (by decide) <|
  .cons (p1_8 _) (OpI.push) (by decide) <|
  .cons (p1_9 _) (OpI.push) (by decide) <|
  .cons (p1_10 _) (OpI.mov (.r 7) (.inr rfl)) (by decide) <|
  .cons (p1_13 _) (OpI.sub (.i 24) (.inr rfl)) (by decide) <|
  .cons (p1_17 _) (OpI.ld (.inl rfl)) (by decide) <|
  .cons (p1_23 _) (OpI.st (.inr (.inr (.inl rfl)))) (by decide) <|
  .cons (p1_27 _) (OpI.test (.r 0) (.inl rfl)) (by decide) <|
  .nil 29

def j1 : List Byte := [0x0f, 0x84, 0xca, 0x01, 0x00, 0x00]
theorem j1_0 : ∀ feat, Dec feat j1 0 (FV7z.mk (.jcc 4) 64 [.rel 458] 6) := by dec_rfl

/-- The stretch at `56`. -/
def p2 : List Byte := [
  0x44, 0x8b, 0x6c, 0x24, 0x0c, 0x4a, 0x8d, 0x3c, 0xed, 0x00, 0x00, 0x00, 0x00]

theorem p2_0 : ∀ feat, Dec feat p2 0 (FV7z.mk .mov 32 [gr 32 13, .mem (mg (some 4) none 1 12 32)] 5) := by dec_rfl
theorem p2_5 : ∀ feat, Dec feat p2 5 (FV7z.mk .lea 64 [gr 64 7, .mem (mg none (some 13) 8 0 0)] 8) := by dec_rfl

/-- What the stretch does. -/
def o2 : List Op := [
  Op.ld 32 13 (some 4) none 1 12,
  Op.lea 64 7 none (some 13) 8 0]

theorem b2 (prof : Profile) : Blk prof p2 0 13 o2 :=
  .cons (p2_0 _) (OpI.ld (.inl rfl)) (by decide) <|
  .cons (p2_5 _) (OpI.lea (.inr rfl)) (by decide) <|
  .nil 13

/-- The stretch at `74`. -/
def p3 : List Byte := [
  0x48, 0x89, 0xc5, 0x8b, 0x83, 0x20, 0x02, 0x00, 0x00, 0x85, 0xc0]

theorem p3_0 : ∀ feat, Dec feat p3 0 (FV7z.mk .mov 64 [gr 64 5, Src.opd 64 (.r 0)] 3) := by dec_rfl
theorem p3_3 : ∀ feat, Dec feat p3 3 (FV7z.mk .mov 32 [gr 32 0, .mem (mg (some 3) none 1 544 32)] 6) := by dec_rfl
theorem p3_9 : ∀ feat, Dec feat p3 9 (FV7z.mk .test 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl

/-- What the stretch does. -/
def o3 : List Op := [
  Op.mov 64 5 (.r 0),
  Op.ld 32 0 (some 3) none 1 544,
  Op.test 32 0 (.r 0)]

theorem b3 (prof : Profile) : Blk prof p3 0 11 o3 :=
  .cons (p3_0 _) (OpI.mov (.r 0) (.inr rfl)) (by decide) <|
  .cons (p3_3 _) (OpI.ld (.inl rfl)) (by decide) <|
  .cons (p3_9 _) (OpI.test (.r 0) (.inl rfl)) (by decide) <|
  .nil 11

def j2 : List Byte := [0x74, 0x36]
theorem j2_0 : ∀ feat, Dec feat j2 0 (FV7z.mk (.jcc 4) 64 [.rel 54] 2) := by dec_rfl

/-- The stretch at `87`. -/
def p4 : List Byte := [
  0x45, 0x31, 0xe4, 0x66, 0x0f, 0x1f, 0x44, 0x00, 0x00]

theorem p4_0 : ∀ feat, Dec feat p4 0 (FV7z.mk .xor 32 [gr 32 12, Src.opd 32 (.r 12)] 3) := by dec_rfl
theorem p4_3 : ∀ feat, Dec feat p4 3 (FV7z.mk .nop 16 [.mem (mg (some 0) (some 0) 1 0 16)] 6) := by dec_rfl

/-- What the stretch does. -/
def o4 : List Op := [
  Op.xor 32 12 (.r 12),
  Op.nop]

theorem b4 (prof : Profile) : Blk prof p4 0 9 o4 :=
  .cons (p4_0 _) (OpI.xor (.r 12) (.inl rfl)) (by decide) <|
  .cons (p4_3 _) (OpI.nop) (by decide) <|
  .nil 9

/-- The stretch at `96`. -/
def p5 : List Byte := [
  0x48, 0x8b, 0x93, 0x18, 0x02, 0x00, 0x00, 0x44, 0x89, 0xe0, 0x48, 0x8d, 0x7c, 0xc5, 0x00, 0x48,
  0x8b, 0x04, 0xc2, 0x44, 0x89, 0x67, 0x04, 0x48, 0x8b, 0x70, 0x38]

theorem p5_0 : ∀ feat, Dec feat p5 0 (FV7z.mk .mov 64 [gr 64 2, .mem (mg (some 3) none 1 536 64)] 7) := by dec_rfl
theorem p5_7 : ∀ feat, Dec feat p5 7 (FV7z.mk .mov 32 [gr 32 0, Src.opd 32 (.r 12)] 3) := by dec_rfl
theorem p5_10 : ∀ feat, Dec feat p5 10 (FV7z.mk .lea 64 [gr 64 7, .mem (mg (some 5) (some 0) 8 0 0)] 5) := by dec_rfl
theorem p5_15 : ∀ feat, Dec feat p5 15 (FV7z.mk .mov 64 [gr 64 0, .mem (mg (some 2) (some 0) 8 0 64)] 4) := by dec_rfl
theorem p5_19 : ∀ feat, Dec feat p5 19 (FV7z.mk .mov 32 [.mem (mg (some 7) none 1 4 32), gr 32 12] 4) := by dec_rfl
theorem p5_23 : ∀ feat, Dec feat p5 23 (FV7z.mk .mov 64 [gr 64 6, .mem (mg (some 0) none 1 56 64)] 4) := by dec_rfl

/-- What the stretch does. -/
def o5 : List Op := [
  Op.ld 64 2 (some 3) none 1 536,
  Op.mov 32 0 (.r 12),
  Op.lea 64 7 (some 5) (some 0) 8 0,
  Op.ld 64 0 (some 2) (some 0) 8 0,
  Op.st 32 (some 7) none 1 4 12,
  Op.ld 64 6 (some 0) none 1 56]

theorem b5 (prof : Profile) : Blk prof p5 0 27 o5 :=
  .cons (p5_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p5_7 _) (OpI.mov (.r 12) (.inl rfl)) (by decide) <|
  .cons (p5_10 _) (OpI.lea (.inr rfl)) (by decide) <|
  .cons (p5_15 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p5_19 _) (OpI.st (.inr (.inr (.inl rfl)))) (by decide) <|
  .cons (p5_23 _) (OpI.ld (.inr rfl)) (by decide) <|
  .nil 27

/-- The stretch at `128`. -/
def p6 : List Byte := [
  0x41, 0x83, 0xc4, 0x01, 0x44, 0x39, 0xa3, 0x20, 0x02, 0x00, 0x00]

theorem p6_0 : ∀ feat, Dec feat p6 0 (FV7z.mk .add 32 [gr 32 12, Src.opd 32 (.i 1)] 4) := by dec_rfl
theorem p6_4 : ∀ feat, Dec feat p6 4 (FV7z.mk .cmp 32 [.mem (mg (some 3) none 1 544 32), gr 32 12] 7) := by dec_rfl

/-- What the stretch does. -/
def o6 : List Op := [
  Op.add 32 12 (.i 1),
  Op.cmpmr 32 (some 3) none 1 544 12]

theorem b6 (prof : Profile) : Blk prof p6 0 11 o6 :=
  .cons (p6_0 _) (OpI.add (.i 1) (.inl rfl)) (by decide) <|
  .cons (p6_4 _) (OpI.cmpmr (.inl rfl)) (by decide) <|
  .nil 11

def j3 : List Byte := [0x77, 0xd3]
theorem j3_0 : ∀ feat, Dec feat j3 0 (FV7z.mk (.jcc 7) 64 [.rel 18446744073709551571] 2) := by dec_rfl

/-- The stretch at `141`. -/
def p7 : List Byte := [
  0x49, 0x83, 0xfd, 0x01]

theorem p7_0 : ∀ feat, Dec feat p7 0 (FV7z.mk .cmp 64 [gr 64 13, Src.opd 64 (.i 1)] 4) := by dec_rfl

/-- What the stretch does. -/
def o7 : List Op := [
  Op.cmp 64 13 (.i 1)]

theorem b7 (prof : Profile) : Blk prof p7 0 4 o7 :=
  .cons (p7_0 _) (OpI.cmp (.i 1) (.inr rfl)) (by decide) <|
  .nil 4

def j4 : List Byte := [0x0f, 0x84, 0xc9, 0x00, 0x00, 0x00]
theorem j4_0 : ∀ feat, Dec feat j4 0 (FV7z.mk (.jcc 4) 64 [.rel 201] 6) := by dec_rfl

/-- The stretch at `151`. -/
def p8 : List Byte := [
  0x49, 0x8d, 0x45, 0xff, 0x49, 0xd1, 0xed, 0x49, 0x8d, 0x7d, 0xff, 0x4c, 0x8d, 0x4c, 0xfd, 0x00,
  0x4c, 0x8d, 0x5c, 0x3f, 0x01]

theorem p8_0 : ∀ feat, Dec feat p8 0 (FV7z.mk .lea 64 [gr 64 0, .mem (mg (some 13) none 1 18446744073709551615 0)] 4) := by dec_rfl
theorem p8_4 : ∀ feat, Dec feat p8 4 (FV7z.mk .shr 64 [gr 64 13, Src.opd 8 (.i 1)] 3) := by dec_rfl
theorem p8_7 : ∀ feat, Dec feat p8 7 (FV7z.mk .lea 64 [gr 64 7, .mem (mg (some 13) none 1 18446744073709551615 0)] 4) := by dec_rfl
theorem p8_11 : ∀ feat, Dec feat p8 11 (FV7z.mk .lea 64 [gr 64 9, .mem (mg (some 5) (some 7) 8 0 0)] 5) := by dec_rfl
theorem p8_16 : ∀ feat, Dec feat p8 16 (FV7z.mk .lea 64 [gr 64 11, .mem (mg (some 7) (some 7) 1 1 0)] 5) := by dec_rfl

/-- What the stretch does. -/
def o8 : List Op := [
  Op.lea 64 0 (some 13) none 1 18446744073709551615,
  Op.shr64 13 (.i 1),
  Op.lea 64 7 (some 13) none 1 18446744073709551615,
  Op.lea 64 9 (some 5) (some 7) 8 0,
  Op.lea 64 11 (some 7) (some 7) 1 1]

theorem b8 (prof : Profile) : Blk prof p8 0 21 o8 :=
  .cons (p8_0 _) (OpI.lea (.inr rfl)) (by decide) <|
  .cons (p8_4 _) (OpI.shr64 (.i 1)) (by decide) <|
  .cons (p8_7 _) (OpI.lea (.inr rfl)) (by decide) <|
  .cons (p8_11 _) (OpI.lea (.inr rfl)) (by decide) <|
  .cons (p8_16 _) (OpI.lea (.inr rfl)) (by decide) <|
  .nil 21

def j5 : List Byte := [0xeb, 0x2d]
theorem j5_0 : ∀ feat, Dec feat j5 0 (FV7z.mk .jmp 64 [.rel 45] 2) := by dec_rfl

/-- The stretch at `176`. -/
def p9 : List Byte := [
  0x44, 0x3b, 0x6a, 0x04]

theorem p9_0 : ∀ feat, Dec feat p9 0 (FV7z.mk .cmp 32 [gr 32 13, .mem (mg (some 2) none 1 4 32)] 4) := by dec_rfl

/-- What the stretch does. -/
def o9 : List Op := [
  Op.cmpm 32 13 (some 2) none 1 4]

theorem b9 (prof : Profile) : Blk prof p9 0 4 o9 :=
  .cons (p9_0 _) (OpI.cmpm (.inl rfl)) (by decide) <|
  .nil 4

def j6 : List Byte := [0x72, 0x7f]
theorem j6_0 : ∀ feat, Dec feat j6 0 (FV7z.mk (.jcc 2) 64 [.rel 127] 2) := by dec_rfl

/-- The stretch at `182`. -/
def p10 : List Byte := [
  0x48, 0x8b, 0x3c, 0x24, 0x4a, 0x8d, 0x54, 0xc5, 0x00]

theorem p10_0 : ∀ feat, Dec feat p10 0 (FV7z.mk .mov 64 [gr 64 7, .mem (mg (some 4) none 1 0 64)] 4) := by dec_rfl
theorem p10_4 : ∀ feat, Dec feat p10 4 (FV7z.mk .lea 64 [gr 64 2, .mem (mg (some 5) (some 8) 8 0 0)] 5) := by dec_rfl

/-- What the stretch does. -/
def o10 : List Op := [
  Op.ld 64 7 (some 4) none 1 0,
  Op.lea 64 2 (some 5) (some 8) 8 0]

theorem b10 (prof : Profile) : Blk prof p10 0 9 o10 :=
  .cons (p10_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p10_4 _) (OpI.lea (.inr rfl)) (by decide) <|
  .nil 9

/-- The stretch at `191`. -/
def p11 : List Byte := [
  0x44, 0x89, 0x22, 0x49, 0x83, 0xe9, 0x08, 0x49, 0x83, 0xeb, 0x02, 0x44, 0x89, 0x6a, 0x04, 0x48,
  0x85, 0xff]

theorem p11_0 : ∀ feat, Dec feat p11 0 (FV7z.mk .mov 32 [.mem (mg (some 2) none 1 0 32), gr 32 12] 3) := by dec_rfl
theorem p11_3 : ∀ feat, Dec feat p11 3 (FV7z.mk .sub 64 [gr 64 9, Src.opd 64 (.i 8)] 4) := by dec_rfl
theorem p11_7 : ∀ feat, Dec feat p11 7 (FV7z.mk .sub 64 [gr 64 11, Src.opd 64 (.i 2)] 4) := by dec_rfl
theorem p11_11 : ∀ feat, Dec feat p11 11 (FV7z.mk .mov 32 [.mem (mg (some 2) none 1 4 32), gr 32 13] 4) := by dec_rfl
theorem p11_15 : ∀ feat, Dec feat p11 15 (FV7z.mk .test 64 [gr 64 7, Src.opd 64 (.r 7)] 3) := by dec_rfl

/-- What the stretch does. -/
def o11 : List Op := [
  Op.st 32 (some 2) none 1 0 12,
  Op.sub 64 9 (.i 8),
  Op.sub 64 11 (.i 2),
  Op.st 32 (some 2) none 1 4 13,
  Op.test 64 7 (.r 7)]

theorem b11 (prof : Profile) : Blk prof p11 0 18 o11 :=
  .cons (p11_0 _) (OpI.st (.inr (.inr (.inl rfl)))) (by decide) <|
  .cons (p11_3 _) (OpI.sub (.i 8) (.inr rfl)) (by decide) <|
  .cons (p11_7 _) (OpI.sub (.i 2) (.inr rfl)) (by decide) <|
  .cons (p11_11 _) (OpI.st (.inr (.inr (.inl rfl)))) (by decide) <|
  .cons (p11_15 _) (OpI.test (.r 7) (.inr rfl)) (by decide) <|
  .nil 18

def j7 : List Byte := [0x0f, 0x84, 0x49, 0x01, 0x00, 0x00]
theorem j7_0 : ∀ feat, Dec feat j7 0 (FV7z.mk (.jcc 4) 64 [.rel 329] 6) := by dec_rfl

/-- The stretch at `215`. -/
def p12 : List Byte := [
  0x48, 0x83, 0xef, 0x01]

theorem p12_0 : ∀ feat, Dec feat p12 0 (FV7z.mk .sub 64 [gr 64 7, Src.opd 64 (.i 1)] 4) := by dec_rfl

/-- What the stretch does. -/
def o12 : List Op := [
  Op.sub 64 7 (.i 1)]

theorem b12 (prof : Profile) : Blk prof p12 0 4 o12 :=
  .cons (p12_0 _) (OpI.sub (.i 1) (.inr rfl)) (by decide) <|
  .nil 4

/-- The stretch at `219`. -/
def p13 : List Byte := [
  0x45, 0x8b, 0x21, 0x45, 0x8b, 0x69, 0x04, 0x4c, 0x89, 0xca, 0x48, 0x8d, 0x34, 0x3f, 0x4c, 0x39,
  0xd8]

theorem p13_0 : ∀ feat, Dec feat p13 0 (FV7z.mk .mov 32 [gr 32 12, .mem (mg (some 9) none 1 0 32)] 3) := by dec_rfl
theorem p13_3 : ∀ feat, Dec feat p13 3 (FV7z.mk .mov 32 [gr 32 13, .mem (mg (some 9) none 1 4 32)] 4) := by dec_rfl
theorem p13_7 : ∀ feat, Dec feat p13 7 (FV7z.mk .mov 64 [gr 64 2, Src.opd 64 (.r 9)] 3) := by dec_rfl
theorem p13_10 : ∀ feat, Dec feat p13 10 (FV7z.mk .lea 64 [gr 64 6, .mem (mg (some 7) (some 7) 1 0 0)] 4) := by dec_rfl
theorem p13_14 : ∀ feat, Dec feat p13 14 (FV7z.mk .cmp 64 [gr 64 0, Src.opd 64 (.r 11)] 3) := by dec_rfl

/-- What the stretch does. -/
def o13 : List Op := [
  Op.ld 32 12 (some 9) none 1 0,
  Op.ld 32 13 (some 9) none 1 4,
  Op.mov 64 2 (.r 9),
  Op.lea 64 6 (some 7) (some 7) 1 0,
  Op.cmp 64 0 (.r 11)]

theorem b13 (prof : Profile) : Blk prof p13 0 17 o13 :=
  .cons (p13_0 _) (OpI.ld (.inl rfl)) (by decide) <|
  .cons (p13_3 _) (OpI.ld (.inl rfl)) (by decide) <|
  .cons (p13_7 _) (OpI.mov (.r 9) (.inr rfl)) (by decide) <|
  .cons (p13_10 _) (OpI.lea (.inr rfl)) (by decide) <|
  .cons (p13_14 _) (OpI.cmp (.r 11) (.inr rfl)) (by decide) <|
  .nil 17

def j8 : List Byte := [0x72, 0xd1]
theorem j8_0 : ∀ feat, Dec feat j8 0 (FV7z.mk (.jcc 2) 64 [.rel 18446744073709551569] 2) := by dec_rfl

/-- The stretch at `238`. -/
def p14 : List Byte := [
  0x48, 0x89, 0x3c, 0x24, 0x4c, 0x89, 0xd9, 0x49, 0x89, 0xf8]

theorem p14_0 : ∀ feat, Dec feat p14 0 (FV7z.mk .mov 64 [.mem (mg (some 4) none 1 0 64), gr 64 7] 4) := by dec_rfl
theorem p14_4 : ∀ feat, Dec feat p14 4 (FV7z.mk .mov 64 [gr 64 1, Src.opd 64 (.r 11)] 3) := by dec_rfl
theorem p14_7 : ∀ feat, Dec feat p14 7 (FV7z.mk .mov 64 [gr 64 8, Src.opd 64 (.r 7)] 3) := by dec_rfl

/-- What the stretch does. -/
def o14 : List Op := [
  Op.st 64 (some 4) none 1 0 7,
  Op.mov 64 1 (.r 11),
  Op.mov 64 8 (.r 7)]

theorem b14 (prof : Profile) : Blk prof p14 0 10 o14 :=
  .cons (p14_0 _) (OpI.st (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p14_4 _) (OpI.mov (.r 11) (.inr rfl)) (by decide) <|
  .cons (p14_7 _) (OpI.mov (.r 7) (.inr rfl)) (by decide) <|
  .nil 10

/-- The stretch at `248`. -/
def p15 : List Byte := [
  0x48, 0x8d, 0x54, 0xcd, 0x00, 0x44, 0x8b, 0x12, 0x48, 0x39, 0xc8]

theorem p15_0 : ∀ feat, Dec feat p15 0 (FV7z.mk .lea 64 [gr 64 2, .mem (mg (some 5) (some 1) 8 0 0)] 5) := by dec_rfl
theorem p15_5 : ∀ feat, Dec feat p15 5 (FV7z.mk .mov 32 [gr 32 10, .mem (mg (some 2) none 1 0 32)] 3) := by dec_rfl
theorem p15_8 : ∀ feat, Dec feat p15 8 (FV7z.mk .cmp 64 [gr 64 0, Src.opd 64 (.r 1)] 3) := by dec_rfl

/-- What the stretch does. -/
def o15 : List Op := [
  Op.lea 64 2 (some 5) (some 1) 8 0,
  Op.ld 32 10 (some 2) none 1 0,
  Op.cmp 64 0 (.r 1)]

theorem b15 (prof : Profile) : Blk prof p15 0 11 o15 :=
  .cons (p15_0 _) (OpI.lea (.inr rfl)) (by decide) <|
  .cons (p15_5 _) (OpI.ld (.inl rfl)) (by decide) <|
  .cons (p15_8 _) (OpI.cmp (.r 1) (.inr rfl)) (by decide) <|
  .nil 11

def j9 : List Byte := [0x76, 0x25]
theorem j9_0 : ∀ feat, Dec feat j9 0 (FV7z.mk (.jcc 6) 64 [.rel 37] 2) := by dec_rfl

/-- The stretch at `261`. -/
def p16 : List Byte := [
  0x48, 0x83, 0xc6, 0x02, 0x4c, 0x8d, 0x74, 0xf5, 0x00, 0x45, 0x8b, 0x3e, 0x45, 0x39, 0xd7]

theorem p16_0 : ∀ feat, Dec feat p16 0 (FV7z.mk .add 64 [gr 64 6, Src.opd 64 (.i 2)] 4) := by dec_rfl
theorem p16_4 : ∀ feat, Dec feat p16 4 (FV7z.mk .lea 64 [gr 64 14, .mem (mg (some 5) (some 6) 8 0 0)] 5) := by dec_rfl
theorem p16_9 : ∀ feat, Dec feat p16 9 (FV7z.mk .mov 32 [gr 32 15, .mem (mg (some 14) none 1 0 32)] 3) := by dec_rfl
theorem p16_12 : ∀ feat, Dec feat p16 12 (FV7z.mk .cmp 32 [gr 32 15, Src.opd 32 (.r 10)] 3) := by dec_rfl

/-- What the stretch does. -/
def o16 : List Op := [
  Op.add 64 6 (.i 2),
  Op.lea 64 14 (some 5) (some 6) 8 0,
  Op.ld 32 15 (some 14) none 1 0,
  Op.cmp 32 15 (.r 10)]

theorem b16 (prof : Profile) : Blk prof p16 0 15 o16 :=
  .cons (p16_0 _) (OpI.add (.i 2) (.inr rfl)) (by decide) <|
  .cons (p16_4 _) (OpI.lea (.inr rfl)) (by decide) <|
  .cons (p16_9 _) (OpI.ld (.inl rfl)) (by decide) <|
  .cons (p16_12 _) (OpI.cmp (.r 10) (.inl rfl)) (by decide) <|
  .nil 15

def j10 : List Byte := [0x72, 0x0b]
theorem j10_0 : ∀ feat, Dec feat j10 0 (FV7z.mk (.jcc 2) 64 [.rel 11] 2) := by dec_rfl

def j11 : List Byte := [0x77, 0x12]
theorem j11_0 : ∀ feat, Dec feat j11 0 (FV7z.mk (.jcc 7) 64 [.rel 18] 2) := by dec_rfl

/-- The stretch at `280`. -/
def p17 : List Byte := [
  0x8b, 0x7a, 0x04, 0x41, 0x39, 0x7e, 0x04]

theorem p17_0 : ∀ feat, Dec feat p17 0 (FV7z.mk .mov 32 [gr 32 7, .mem (mg (some 2) none 1 4 32)] 3) := by dec_rfl
theorem p17_3 : ∀ feat, Dec feat p17 3 (FV7z.mk .cmp 32 [.mem (mg (some 14) none 1 4 32), gr 32 7] 4) := by dec_rfl

/-- What the stretch does. -/
def o17 : List Op := [
  Op.ld 32 7 (some 2) none 1 4,
  Op.cmpmr 32 (some 14) none 1 4 7]

theorem b17 (prof : Profile) : Blk prof p17 0 7 o17 :=
  .cons (p17_0 _) (OpI.ld (.inl rfl)) (by decide) <|
  .cons (p17_3 _) (OpI.cmpmr (.inl rfl)) (by decide) <|
  .nil 7

def j12 : List Byte := [0x76, 0x09]
theorem j12_0 : ∀ feat, Dec feat j12 0 (FV7z.mk (.jcc 6) 64 [.rel 9] 2) := by dec_rfl

/-- The stretch at `289`. -/
def p18 : List Byte := [
  0x45, 0x89, 0xfa, 0x4c, 0x89, 0xf2, 0x48, 0x89, 0xf1]

theorem p18_0 : ∀ feat, Dec feat p18 0 (FV7z.mk .mov 32 [gr 32 10, Src.opd 32 (.r 15)] 3) := by dec_rfl
theorem p18_3 : ∀ feat, Dec feat p18 3 (FV7z.mk .mov 64 [gr 64 2, Src.opd 64 (.r 14)] 3) := by dec_rfl
theorem p18_6 : ∀ feat, Dec feat p18 6 (FV7z.mk .mov 64 [gr 64 1, Src.opd 64 (.r 6)] 3) := by dec_rfl

/-- What the stretch does. -/
def o18 : List Op := [
  Op.mov 32 10 (.r 15),
  Op.mov 64 2 (.r 14),
  Op.mov 64 1 (.r 6)]

theorem b18 (prof : Profile) : Blk prof p18 0 9 o18 :=
  .cons (p18_0 _) (OpI.mov (.r 15) (.inl rfl)) (by decide) <|
  .cons (p18_3 _) (OpI.mov (.r 14) (.inr rfl)) (by decide) <|
  .cons (p18_6 _) (OpI.mov (.r 6) (.inr rfl)) (by decide) <|
  .nil 9

/-- The stretch at `298`. -/
def p19 : List Byte := [
  0x45, 0x39, 0xd4]

theorem p19_0 : ∀ feat, Dec feat p19 0 (FV7z.mk .cmp 32 [gr 32 12, Src.opd 32 (.r 10)] 3) := by dec_rfl

/-- What the stretch does. -/
def o19 : List Op := [
  Op.cmp 32 12 (.r 10)]

theorem b19 (prof : Profile) : Blk prof p19 0 3 o19 :=
  .cons (p19_0 _) (OpI.cmp (.r 10) (.inl rfl)) (by decide) <|
  .nil 3

def j13 : List Byte := [0x72, 0x87]
theorem j13_0 : ∀ feat, Dec feat j13 0 (FV7z.mk (.jcc 2) 64 [.rel 18446744073709551495] 2) := by dec_rfl

def j14 : List Byte := [0x0f, 0x86, 0x7b, 0xff, 0xff, 0xff]
theorem j14_0 : ∀ feat, Dec feat j14 0 (FV7z.mk (.jcc 6) 64 [.rel 18446744073709551483] 6) := by dec_rfl

/-- The stretch at `309`. -/
def p20 : List Byte := [
  0x48, 0x8b, 0x32, 0x4a, 0x89, 0x74, 0xc5, 0x00, 0x48, 0x8d, 0x34, 0x09, 0x4c, 0x8d, 0x56, 0x01,
  0x4c, 0x39, 0xd0]

theorem p20_0 : ∀ feat, Dec feat p20 0 (FV7z.mk .mov 64 [gr 64 6, .mem (mg (some 2) none 1 0 64)] 3) := by dec_rfl
theorem p20_3 : ∀ feat, Dec feat p20 3 (FV7z.mk .mov 64 [.mem (mg (some 5) (some 8) 8 0 64), gr 64 6] 5) := by dec_rfl
theorem p20_8 : ∀ feat, Dec feat p20 8 (FV7z.mk .lea 64 [gr 64 6, .mem (mg (some 1) (some 1) 1 0 0)] 4) := by dec_rfl
theorem p20_12 : ∀ feat, Dec feat p20 12 (FV7z.mk .lea 64 [gr 64 10, .mem (mg (some 6) none 1 1 0)] 4) := by dec_rfl
theorem p20_16 : ∀ feat, Dec feat p20 16 (FV7z.mk .cmp 64 [gr 64 0, Src.opd 64 (.r 10)] 3) := by dec_rfl

/-- What the stretch does. -/
def o20 : List Op := [
  Op.ld 64 6 (some 2) none 1 0,
  Op.st 64 (some 5) (some 8) 8 0 6,
  Op.lea 64 6 (some 1) (some 1) 1 0,
  Op.lea 64 10 (some 6) none 1 1,
  Op.cmp 64 0 (.r 10)]

theorem b20 (prof : Profile) : Blk prof p20 0 19 o20 :=
  .cons (p20_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p20_3 _) (OpI.st (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p20_8 _) (OpI.lea (.inr rfl)) (by decide) <|
  .cons (p20_12 _) (OpI.lea (.inr rfl)) (by decide) <|
  .cons (p20_16 _) (OpI.cmp (.r 10) (.inr rfl)) (by decide) <|
  .nil 19

def j15 : List Byte := [0x0f, 0x82, 0x6a, 0x01, 0x00, 0x00]
theorem j15_0 : ∀ feat, Dec feat j15 0 (FV7z.mk (.jcc 2) 64 [.rel 362] 6) := by dec_rfl

/-- The stretch at `334`. -/
def p21 : List Byte := [
  0x49, 0x89, 0xc8, 0x4c, 0x89, 0xd1]

theorem p21_0 : ∀ feat, Dec feat p21 0 (FV7z.mk .mov 64 [gr 64 8, Src.opd 64 (.r 1)] 3) := by dec_rfl
theorem p21_3 : ∀ feat, Dec feat p21 3 (FV7z.mk .mov 64 [gr 64 1, Src.opd 64 (.r 10)] 3) := by dec_rfl

/-- What the stretch does. -/
def o21 : List Op := [
  Op.mov 64 8 (.r 1),
  Op.mov 64 1 (.r 10)]

theorem b21 (prof : Profile) : Blk prof p21 0 6 o21 :=
  .cons (p21_0 _) (OpI.mov (.r 1) (.inr rfl)) (by decide) <|
  .cons (p21_3 _) (OpI.mov (.r 10) (.inr rfl)) (by decide) <|
  .nil 6

def j16 : List Byte := [0xeb, 0xa2]
theorem j16_0 : ∀ feat, Dec feat j16 0 (FV7z.mk .jmp 64 [.rel 18446744073709551522] 2) := by dec_rfl

/-- The stretch at `352`. -/
def p22 : List Byte := [
  0x8b, 0x4d, 0x04]

theorem p22_0 : ∀ feat, Dec feat p22 0 (FV7z.mk .mov 32 [gr 32 1, .mem (mg (some 5) none 1 4 32)] 3) := by dec_rfl

/-- What the stretch does. -/
def o22 : List Op := [
  Op.ld 32 1 (some 5) none 1 4]

theorem b22 (prof : Profile) : Blk prof p22 0 3 o22 :=
  .cons (p22_0 _) (OpI.ld (.inl rfl)) (by decide) <|
  .nil 3

/-- The stretch at `355`. -/
def p23 : List Byte := [
  0x45, 0x31, 0xe4]

theorem p23_0 : ∀ feat, Dec feat p23 0 (FV7z.mk .xor 32 [gr 32 12, Src.opd 32 (.r 12)] 3) := by dec_rfl

/-- What the stretch does. -/
def o23 : List Op := [
  Op.xor 32 12 (.r 12)]

theorem b23 (prof : Profile) : Blk prof p23 0 3 o23 :=
  .cons (p23_0 _) (OpI.xor (.r 12) (.inl rfl)) (by decide) <|
  .nil 3

def j17 : List Byte := [0xeb, 0x0d]
theorem j17_0 : ∀ feat, Dec feat j17 0 (FV7z.mk .jmp 64 [.rel 13] 2) := by dec_rfl

/-- The stretch at `368`. -/
def p24 : List Byte := [
  0x42, 0x8b, 0x4c, 0xe5, 0x04]

theorem p24_0 : ∀ feat, Dec feat p24 0 (FV7z.mk .mov 32 [gr 32 1, .mem (mg (some 5) (some 12) 8 4 32)] 5) := by dec_rfl

/-- What the stretch does. -/
def o24 : List Op := [
  Op.ld 32 1 (some 5) (some 12) 8 4]

theorem b24 (prof : Profile) : Blk prof p24 0 5 o24 :=
  .cons (p24_0 _) (OpI.ld (.inl rfl)) (by decide) <|
  .nil 5

/-- The stretch at `373`. -/
def p25 : List Byte := [
  0x48, 0x8b, 0x83, 0x18, 0x02, 0x00, 0x00, 0x48, 0x8b, 0x3c, 0xc8, 0x48, 0x8b, 0x77, 0x38]

theorem p25_0 : ∀ feat, Dec feat p25 0 (FV7z.mk .mov 64 [gr 64 0, .mem (mg (some 3) none 1 536 64)] 7) := by dec_rfl
theorem p25_7 : ∀ feat, Dec feat p25 7 (FV7z.mk .mov 64 [gr 64 7, .mem (mg (some 0) (some 1) 8 0 64)] 4) := by dec_rfl
theorem p25_11 : ∀ feat, Dec feat p25 11 (FV7z.mk .mov 64 [gr 64 6, .mem (mg (some 7) none 1 56 64)] 4) := by dec_rfl

/-- What the stretch does. -/
def o25 : List Op := [
  Op.ld 64 0 (some 3) none 1 536,
  Op.ld 64 7 (some 0) (some 1) 8 0,
  Op.ld 64 6 (some 7) none 1 56]

theorem b25 (prof : Profile) : Blk prof p25 0 15 o25 :=
  .cons (p25_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p25_7 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p25_11 _) (OpI.ld (.inr rfl)) (by decide) <|
  .nil 15

/-- The stretch at `393`. -/
def p26 : List Byte := [
  0x49, 0x83, 0xc4, 0x01, 0x44, 0x39, 0x64, 0x24, 0x0c]

theorem p26_0 : ∀ feat, Dec feat p26 0 (FV7z.mk .add 64 [gr 64 12, Src.opd 64 (.i 1)] 4) := by dec_rfl
theorem p26_4 : ∀ feat, Dec feat p26 4 (FV7z.mk .cmp 32 [.mem (mg (some 4) none 1 12 32), gr 32 12] 5) := by dec_rfl

/-- What the stretch does. -/
def o26 : List Op := [
  Op.add 64 12 (.i 1),
  Op.cmpmr 32 (some 4) none 1 12 12]

theorem b26 (prof : Profile) : Blk prof p26 0 9 o26 :=
  .cons (p26_0 _) (OpI.add (.i 1) (.inr rfl)) (by decide) <|
  .cons (p26_4 _) (OpI.cmpmr (.inl rfl)) (by decide) <|
  .nil 9

def j18 : List Byte := [0x77, 0xdc]
theorem j18_0 : ∀ feat, Dec feat j18 0 (FV7z.mk (.jcc 7) 64 [.rel 18446744073709551580] 2) := by dec_rfl

/-- The stretch at `404`. -/
def p27 : List Byte := [
  0x8b, 0x83, 0x20, 0x02, 0x00, 0x00, 0x85, 0xc0]

theorem p27_0 : ∀ feat, Dec feat p27 0 (FV7z.mk .mov 32 [gr 32 0, .mem (mg (some 3) none 1 544 32)] 6) := by dec_rfl
theorem p27_6 : ∀ feat, Dec feat p27 6 (FV7z.mk .test 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl

/-- What the stretch does. -/
def o27 : List Op := [
  Op.ld 32 0 (some 3) none 1 544,
  Op.test 32 0 (.r 0)]

theorem b27 (prof : Profile) : Blk prof p27 0 8 o27 :=
  .cons (p27_0 _) (OpI.ld (.inl rfl)) (by decide) <|
  .cons (p27_6 _) (OpI.test (.r 0) (.inl rfl)) (by decide) <|
  .nil 8

def j19 : List Byte := [0x74, 0x56]
theorem j19_0 : ∀ feat, Dec feat j19 0 (FV7z.mk (.jcc 4) 64 [.rel 86] 2) := by dec_rfl

/-- The stretch at `414`. -/
def p28 : List Byte := [
  0x44, 0x8d, 0x60, 0xff, 0x49, 0xc1, 0xe4, 0x03, 0x66, 0x2e, 0x0f, 0x1f, 0x84, 0x00, 0x00, 0x00,
  0x00, 0x00]

theorem p28_0 : ∀ feat, Dec feat p28 0 (FV7z.mk .lea 32 [gr 32 12, .mem (mg (some 0) none 1 18446744073709551615 0)] 4) := by dec_rfl
theorem p28_4 : ∀ feat, Dec feat p28 4 (FV7z.mk .shl 64 [gr 64 12, Src.opd 8 (.i 3)] 4) := by dec_rfl
theorem p28_8 : ∀ feat, Dec feat p28 8 (FV7z.mk .nop 16 [.mem (mg (some 0) (some 0) 1 0 16)] 10) := by dec_rfl

/-- What the stretch does. -/
def o28 : List Op := [
  Op.lea 32 12 (some 0) none 1 18446744073709551615,
  Op.shl64 12 (.i 3),
  Op.nop]

theorem b28 (prof : Profile) : Blk prof p28 0 18 o28 :=
  .cons (p28_0 _) (OpI.lea (.inl rfl)) (by decide) <|
  .cons (p28_4 _) (OpI.shl64 (.i 3)) (by decide) <|
  .cons (p28_8 _) (OpI.nop) (by decide) <|
  .nil 18

/-- The stretch at `432`. -/
def p29 : List Byte := [
  0x48, 0x8b, 0x83, 0x18, 0x02, 0x00, 0x00, 0x4e, 0x8b, 0x2c, 0x20, 0x4d, 0x85, 0xed]

theorem p29_0 : ∀ feat, Dec feat p29 0 (FV7z.mk .mov 64 [gr 64 0, .mem (mg (some 3) none 1 536 64)] 7) := by dec_rfl
theorem p29_7 : ∀ feat, Dec feat p29 7 (FV7z.mk .mov 64 [gr 64 13, .mem (mg (some 0) (some 12) 1 0 64)] 4) := by dec_rfl
theorem p29_11 : ∀ feat, Dec feat p29 11 (FV7z.mk .test 64 [gr 64 13, Src.opd 64 (.r 13)] 3) := by dec_rfl

/-- What the stretch does. -/
def o29 : List Op := [
  Op.ld 64 0 (some 3) none 1 536,
  Op.ld 64 13 (some 0) (some 12) 1 0,
  Op.test 64 13 (.r 13)]

theorem b29 (prof : Profile) : Blk prof p29 0 14 o29 :=
  .cons (p29_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p29_7 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p29_11 _) (OpI.test (.r 13) (.inr rfl)) (by decide) <|
  .nil 14

def j20 : List Byte := [0x74, 0x1b]
theorem j20_0 : ∀ feat, Dec feat j20 0 (FV7z.mk (.jcc 4) 64 [.rel 27] 2) := by dec_rfl

/-- The stretch at `448`. -/
def p30 : List Byte := [
  0x49, 0x8b, 0x7d, 0x38, 0x48, 0x85, 0xff]

theorem p30_0 : ∀ feat, Dec feat p30 0 (FV7z.mk .mov 64 [gr 64 7, .mem (mg (some 13) none 1 56 64)] 4) := by dec_rfl
theorem p30_4 : ∀ feat, Dec feat p30 4 (FV7z.mk .test 64 [gr 64 7, Src.opd 64 (.r 7)] 3) := by dec_rfl

/-- What the stretch does. -/
def o30 : List Op := [
  Op.ld 64 7 (some 13) none 1 56,
  Op.test 64 7 (.r 7)]

theorem b30 (prof : Profile) : Blk prof p30 0 7 o30 :=
  .cons (p30_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p30_4 _) (OpI.test (.r 7) (.inr rfl)) (by decide) <|
  .nil 7

def j21 : List Byte := [0x74, 0x05]
theorem j21_0 : ∀ feat, Dec feat j21 0 (FV7z.mk (.jcc 4) 64 [.rel 5] 2) := by dec_rfl

/-- The stretch at `462`. -/
def p31 : List Byte := [
  0xbe, 0x48, 0x00, 0x00, 0x00, 0x4c, 0x89, 0xef]

theorem p31_0 : ∀ feat, Dec feat p31 0 (FV7z.mk .mov 32 [gr 32 6, Src.opd 32 (.i 72)] 5) := by dec_rfl
theorem p31_5 : ∀ feat, Dec feat p31 5 (FV7z.mk .mov 64 [gr 64 7, Src.opd 64 (.r 13)] 3) := by dec_rfl

/-- What the stretch does. -/
def o31 : List Op := [
  Op.mov 32 6 (.i 72),
  Op.mov 64 7 (.r 13)]

theorem b31 (prof : Profile) : Blk prof p31 0 8 o31 :=
  .cons (p31_0 _) (OpI.mov (.i 72) (.inl rfl)) (by decide) <|
  .cons (p31_5 _) (OpI.mov (.r 13) (.inr rfl)) (by decide) <|
  .nil 8

/-- The stretch at `475`. -/
def p32 : List Byte := [
  0x49, 0x83, 0xec, 0x08, 0x49, 0x83, 0xfc, 0xf8]

theorem p32_0 : ∀ feat, Dec feat p32 0 (FV7z.mk .sub 64 [gr 64 12, Src.opd 64 (.i 8)] 4) := by dec_rfl
theorem p32_4 : ∀ feat, Dec feat p32 4 (FV7z.mk .cmp 64 [gr 64 12, Src.opd 64 (.i 18446744073709551608)] 4) := by dec_rfl

/-- What the stretch does. -/
def o32 : List Op := [
  Op.sub 64 12 (.i 8),
  Op.cmp 64 12 (.i 18446744073709551608)]

theorem b32 (prof : Profile) : Blk prof p32 0 8 o32 :=
  .cons (p32_0 _) (OpI.sub (.i 8) (.inr rfl)) (by decide) <|
  .cons (p32_4 _) (OpI.cmp (.i 18446744073709551608) (.inr rfl)) (by decide) <|
  .nil 8

def j22 : List Byte := [0x75, 0xcb]
theorem j22_0 : ∀ feat, Dec feat j22 0 (FV7z.mk (.jcc 5) 64 [.rel 18446744073709551563] 2) := by dec_rfl

/-- The stretch at `485`. -/
def p33 : List Byte := [
  0xc7, 0x83, 0x20, 0x02, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x48, 0x85, 0xed]

theorem p33_0 : ∀ feat, Dec feat p33 0 (FV7z.mk .mov 32 [.mem (mg (some 3) none 1 544 32), .imm 32 0] 10) := by dec_rfl
theorem p33_10 : ∀ feat, Dec feat p33 10 (FV7z.mk .test 64 [gr 64 5, Src.opd 64 (.r 5)] 3) := by dec_rfl

/-- What the stretch does. -/
def o33 : List Op := [
  Op.sti 32 (some 3) none 1 544 0,
  Op.test 64 5 (.r 5)]

theorem b33 (prof : Profile) : Blk prof p33 0 13 o33 :=
  .cons (p33_0 _) (OpI.sti (.inr (.inr (.inl rfl)))) (by decide) <|
  .cons (p33_10 _) (OpI.test (.r 5) (.inr rfl)) (by decide) <|
  .nil 13

def j23 : List Byte := [0x74, 0x08]
theorem j23_0 : ∀ feat, Dec feat j23 0 (FV7z.mk (.jcc 4) 64 [.rel 8] 2) := by dec_rfl

/-- The stretch at `500`. -/
def p34 : List Byte := [
  0x48, 0x89, 0xef]

theorem p34_0 : ∀ feat, Dec feat p34 0 (FV7z.mk .mov 64 [gr 64 7, Src.opd 64 (.r 5)] 3) := by dec_rfl

/-- What the stretch does. -/
def o34 : List Op := [
  Op.mov 64 7 (.r 5)]

theorem b34 (prof : Profile) : Blk prof p34 0 3 o34 :=
  .cons (p34_0 _) (OpI.mov (.r 5) (.inr rfl)) (by decide) <|
  .nil 3

/-- The stretch at `508`. -/
def p35 : List Byte := [
  0x48, 0x83, 0xc4, 0x18, 0x31, 0xc0, 0x5b, 0x5d, 0x41, 0x5c, 0x41, 0x5d, 0x41, 0x5e, 0x41, 0x5f]

theorem p35_0 : ∀ feat, Dec feat p35 0 (FV7z.mk .add 64 [gr 64 4, Src.opd 64 (.i 24)] 4) := by dec_rfl
theorem p35_4 : ∀ feat, Dec feat p35 4 (FV7z.mk .xor 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl
theorem p35_6 : ∀ feat, Dec feat p35 6 (FV7z.mk .pop 64 [gr 64 3] 1) := by dec_rfl
theorem p35_7 : ∀ feat, Dec feat p35 7 (FV7z.mk .pop 64 [gr 64 5] 1) := by dec_rfl
theorem p35_8 : ∀ feat, Dec feat p35 8 (FV7z.mk .pop 64 [gr 64 12] 2) := by dec_rfl
theorem p35_10 : ∀ feat, Dec feat p35 10 (FV7z.mk .pop 64 [gr 64 13] 2) := by dec_rfl
theorem p35_12 : ∀ feat, Dec feat p35 12 (FV7z.mk .pop 64 [gr 64 14] 2) := by dec_rfl
theorem p35_14 : ∀ feat, Dec feat p35 14 (FV7z.mk .pop 64 [gr 64 15] 2) := by dec_rfl

/-- What the stretch does. -/
def o35 : List Op := [
  Op.add 64 4 (.i 24),
  Op.xor 32 0 (.r 0),
  Op.pop 3,
  Op.pop 5,
  Op.pop 12,
  Op.pop 13,
  Op.pop 14,
  Op.pop 15]

theorem b35 (prof : Profile) : Blk prof p35 0 16 o35 :=
  .cons (p35_0 _) (OpI.add (.i 24) (.inr rfl)) (by decide) <|
  .cons (p35_4 _) (OpI.xor (.r 0) (.inl rfl)) (by decide) <|
  .cons (p35_6 _) (OpI.pop) (by decide) <|
  .cons (p35_7 _) (OpI.pop) (by decide) <|
  .cons (p35_8 _) (OpI.pop) (by decide) <|
  .cons (p35_10 _) (OpI.pop) (by decide) <|
  .cons (p35_12 _) (OpI.pop) (by decide) <|
  .cons (p35_14 _) (OpI.pop) (by decide) <|
  .nil 16

/-- The stretch at `528`. -/
def p36 : List Byte := [
  0x3b, 0x4a, 0x04]

theorem p36_0 : ∀ feat, Dec feat p36 0 (FV7z.mk .cmp 32 [gr 32 1, .mem (mg (some 2) none 1 4 32)] 3) := by dec_rfl

/-- What the stretch does. -/
def o36 : List Op := [
  Op.cmpm 32 1 (some 2) none 1 4]

theorem b36 (prof : Profile) : Blk prof p36 0 3 o36 :=
  .cons (p36_0 _) (OpI.cmpm (.inl rfl)) (by decide) <|
  .nil 3

def j24 : List Byte := [0x72, 0x72]
theorem j24_0 : ∀ feat, Dec feat j24 0 (FV7z.mk (.jcc 2) 64 [.rel 114] 2) := by dec_rfl

/-- The stretch at `533`. -/
def p37 : List Byte := [
  0x4a, 0x8d, 0x54, 0xc5, 0x00]

theorem p37_0 : ∀ feat, Dec feat p37 0 (FV7z.mk .lea 64 [gr 64 2, .mem (mg (some 5) (some 8) 8 0 0)] 5) := by dec_rfl

/-- What the stretch does. -/
def o37 : List Op := [
  Op.lea 64 2 (some 5) (some 8) 8 0]

theorem b37 (prof : Profile) : Blk prof p37 0 5 o37 :=
  .cons (p37_0 _) (OpI.lea (.inr rfl)) (by decide) <|
  .nil 5

/-- The stretch at `538`. -/
def p38 : List Byte := [
  0x44, 0x89, 0x12, 0x89, 0x4a, 0x04]

theorem p38_0 : ∀ feat, Dec feat p38 0 (FV7z.mk .mov 32 [.mem (mg (some 2) none 1 0 32), gr 32 10] 3) := by dec_rfl
theorem p38_3 : ∀ feat, Dec feat p38 3 (FV7z.mk .mov 32 [.mem (mg (some 2) none 1 4 32), gr 32 1] 3) := by dec_rfl

/-- What the stretch does. -/
def o38 : List Op := [
  Op.st 32 (some 2) none 1 0 10,
  Op.st 32 (some 2) none 1 4 1]

theorem b38 (prof : Profile) : Blk prof p38 0 6 o38 :=
  .cons (p38_0 _) (OpI.st (.inr (.inr (.inl rfl)))) (by decide) <|
  .cons (p38_3 _) (OpI.st (.inr (.inr (.inl rfl)))) (by decide) <|
  .nil 6

/-- The stretch at `544`. -/
def p39 : List Byte := [
  0x44, 0x8b, 0x54, 0xc5, 0x00, 0x8b, 0x4c, 0xc5, 0x04, 0x48, 0x8b, 0x55, 0x00, 0x48, 0x89, 0x54,
  0xc5, 0x00, 0x44, 0x89, 0x55, 0x00, 0x89, 0x4d, 0x04, 0x48, 0x83, 0xe8, 0x01]

theorem p39_0 : ∀ feat, Dec feat p39 0 (FV7z.mk .mov 32 [gr 32 10, .mem (mg (some 5) (some 0) 8 0 32)] 5) := by dec_rfl
theorem p39_5 : ∀ feat, Dec feat p39 5 (FV7z.mk .mov 32 [gr 32 1, .mem (mg (some 5) (some 0) 8 4 32)] 4) := by dec_rfl
theorem p39_9 : ∀ feat, Dec feat p39 9 (FV7z.mk .mov 64 [gr 64 2, .mem (mg (some 5) none 1 0 64)] 4) := by dec_rfl
theorem p39_13 : ∀ feat, Dec feat p39 13 (FV7z.mk .mov 64 [.mem (mg (some 5) (some 0) 8 0 64), gr 64 2] 5) := by dec_rfl
theorem p39_18 : ∀ feat, Dec feat p39 18 (FV7z.mk .mov 32 [.mem (mg (some 5) none 1 0 32), gr 32 10] 4) := by dec_rfl
theorem p39_22 : ∀ feat, Dec feat p39 22 (FV7z.mk .mov 32 [.mem (mg (some 5) none 1 4 32), gr 32 1] 3) := by dec_rfl
theorem p39_25 : ∀ feat, Dec feat p39 25 (FV7z.mk .sub 64 [gr 64 0, Src.opd 64 (.i 1)] 4) := by dec_rfl

/-- What the stretch does. -/
def o39 : List Op := [
  Op.ld 32 10 (some 5) (some 0) 8 0,
  Op.ld 32 1 (some 5) (some 0) 8 4,
  Op.ld 64 2 (some 5) none 1 0,
  Op.st 64 (some 5) (some 0) 8 0 2,
  Op.st 32 (some 5) none 1 0 10,
  Op.st 32 (some 5) none 1 4 1,
  Op.sub 64 0 (.i 1)]

theorem b39 (prof : Profile) : Blk prof p39 0 29 o39 :=
  .cons (p39_0 _) (OpI.ld (.inl rfl)) (by decide) <|
  .cons (p39_5 _) (OpI.ld (.inl rfl)) (by decide) <|
  .cons (p39_9 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p39_13 _) (OpI.st (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p39_18 _) (OpI.st (.inr (.inr (.inl rfl)))) (by decide) <|
  .cons (p39_22 _) (OpI.st (.inr (.inr (.inl rfl)))) (by decide) <|
  .cons (p39_25 _) (OpI.sub (.i 1) (.inr rfl)) (by decide) <|
  .nil 29

def j25 : List Byte := [0x0f, 0x84, 0x20, 0xff, 0xff, 0xff]
theorem j25_0 : ∀ feat, Dec feat j25 0 (FV7z.mk (.jcc 4) 64 [.rel 18446744073709551392] 6) := by dec_rfl

/-- The stretch at `579`. -/
def p40 : List Byte := [
  0x31, 0xff, 0x45, 0x31, 0xc0, 0xbe, 0x01, 0x00, 0x00, 0x00]

theorem p40_0 : ∀ feat, Dec feat p40 0 (FV7z.mk .xor 32 [gr 32 7, Src.opd 32 (.r 7)] 2) := by dec_rfl
theorem p40_2 : ∀ feat, Dec feat p40 2 (FV7z.mk .xor 32 [gr 32 8, Src.opd 32 (.r 8)] 3) := by dec_rfl
theorem p40_5 : ∀ feat, Dec feat p40 5 (FV7z.mk .mov 32 [gr 32 6, Src.opd 32 (.i 1)] 5) := by dec_rfl

/-- What the stretch does. -/
def o40 : List Op := [
  Op.xor 32 7 (.r 7),
  Op.xor 32 8 (.r 8),
  Op.mov 32 6 (.i 1)]

theorem b40 (prof : Profile) : Blk prof p40 0 10 o40 :=
  .cons (p40_0 _) (OpI.xor (.r 7) (.inl rfl)) (by decide) <|
  .cons (p40_2 _) (OpI.xor (.r 8) (.inl rfl)) (by decide) <|
  .cons (p40_5 _) (OpI.mov (.i 1) (.inl rfl)) (by decide) <|
  .nil 10

/-- The stretch at `589`. -/
def p41 : List Byte := [
  0x48, 0x8d, 0x54, 0xf5, 0x00, 0x44, 0x8b, 0x0a, 0x48, 0x39, 0xf0]

theorem p41_0 : ∀ feat, Dec feat p41 0 (FV7z.mk .lea 64 [gr 64 2, .mem (mg (some 5) (some 6) 8 0 0)] 5) := by dec_rfl
theorem p41_5 : ∀ feat, Dec feat p41 5 (FV7z.mk .mov 32 [gr 32 9, .mem (mg (some 2) none 1 0 32)] 3) := by dec_rfl
theorem p41_8 : ∀ feat, Dec feat p41 8 (FV7z.mk .cmp 64 [gr 64 0, Src.opd 64 (.r 6)] 3) := by dec_rfl

/-- What the stretch does. -/
def o41 : List Op := [
  Op.lea 64 2 (some 5) (some 6) 8 0,
  Op.ld 32 9 (some 2) none 1 0,
  Op.cmp 64 0 (.r 6)]

theorem b41 (prof : Profile) : Blk prof p41 0 11 o41 :=
  .cons (p41_0 _) (OpI.lea (.inr rfl)) (by decide) <|
  .cons (p41_5 _) (OpI.ld (.inl rfl)) (by decide) <|
  .cons (p41_8 _) (OpI.cmp (.r 6) (.inr rfl)) (by decide) <|
  .nil 11

def j26 : List Byte := [0x76, 0x26]
theorem j26_0 : ∀ feat, Dec feat j26 0 (FV7z.mk (.jcc 6) 64 [.rel 38] 2) := by dec_rfl

/-- The stretch at `602`. -/
def p42 : List Byte := [
  0x48, 0x83, 0xc7, 0x02, 0x4c, 0x8d, 0x5c, 0xfd, 0x00, 0x45, 0x8b, 0x23, 0x45, 0x39, 0xcc]

theorem p42_0 : ∀ feat, Dec feat p42 0 (FV7z.mk .add 64 [gr 64 7, Src.opd 64 (.i 2)] 4) := by dec_rfl
theorem p42_4 : ∀ feat, Dec feat p42 4 (FV7z.mk .lea 64 [gr 64 11, .mem (mg (some 5) (some 7) 8 0 0)] 5) := by dec_rfl
theorem p42_9 : ∀ feat, Dec feat p42 9 (FV7z.mk .mov 32 [gr 32 12, .mem (mg (some 11) none 1 0 32)] 3) := by dec_rfl
theorem p42_12 : ∀ feat, Dec feat p42 12 (FV7z.mk .cmp 32 [gr 32 12, Src.opd 32 (.r 9)] 3) := by dec_rfl

/-- What the stretch does. -/
def o42 : List Op := [
  Op.add 64 7 (.i 2),
  Op.lea 64 11 (some 5) (some 7) 8 0,
  Op.ld 32 12 (some 11) none 1 0,
  Op.cmp 32 12 (.r 9)]

theorem b42 (prof : Profile) : Blk prof p42 0 15 o42 :=
  .cons (p42_0 _) (OpI.add (.i 2) (.inr rfl)) (by decide) <|
  .cons (p42_4 _) (OpI.lea (.inr rfl)) (by decide) <|
  .cons (p42_9 _) (OpI.ld (.inl rfl)) (by decide) <|
  .cons (p42_12 _) (OpI.cmp (.r 9) (.inl rfl)) (by decide) <|
  .nil 15

def j27 : List Byte := [0x72, 0x0c]
theorem j27_0 : ∀ feat, Dec feat j27 0 (FV7z.mk (.jcc 2) 64 [.rel 12] 2) := by dec_rfl

def j28 : List Byte := [0x77, 0x13]
theorem j28_0 : ∀ feat, Dec feat j28 0 (FV7z.mk (.jcc 7) 64 [.rel 19] 2) := by dec_rfl

/-- The stretch at `621`. -/
def p43 : List Byte := [
  0x44, 0x8b, 0x7a, 0x04, 0x45, 0x39, 0x7b, 0x04]

theorem p43_0 : ∀ feat, Dec feat p43 0 (FV7z.mk .mov 32 [gr 32 15, .mem (mg (some 2) none 1 4 32)] 4) := by dec_rfl
theorem p43_4 : ∀ feat, Dec feat p43 4 (FV7z.mk .cmp 32 [.mem (mg (some 11) none 1 4 32), gr 32 15] 4) := by dec_rfl

/-- What the stretch does. -/
def o43 : List Op := [
  Op.ld 32 15 (some 2) none 1 4,
  Op.cmpmr 32 (some 11) none 1 4 15]

theorem b43 (prof : Profile) : Blk prof p43 0 8 o43 :=
  .cons (p43_0 _) (OpI.ld (.inl rfl)) (by decide) <|
  .cons (p43_4 _) (OpI.cmpmr (.inl rfl)) (by decide) <|
  .nil 8

/-- The stretch at `631`. -/
def p44 : List Byte := [
  0x45, 0x89, 0xe1, 0x4c, 0x89, 0xda, 0x48, 0x89, 0xfe]

theorem p44_0 : ∀ feat, Dec feat p44 0 (FV7z.mk .mov 32 [gr 32 9, Src.opd 32 (.r 12)] 3) := by dec_rfl
theorem p44_3 : ∀ feat, Dec feat p44 3 (FV7z.mk .mov 64 [gr 64 2, Src.opd 64 (.r 11)] 3) := by dec_rfl
theorem p44_6 : ∀ feat, Dec feat p44 6 (FV7z.mk .mov 64 [gr 64 6, Src.opd 64 (.r 7)] 3) := by dec_rfl

/-- What the stretch does. -/
def o44 : List Op := [
  Op.mov 32 9 (.r 12),
  Op.mov 64 2 (.r 11),
  Op.mov 64 6 (.r 7)]

theorem b44 (prof : Profile) : Blk prof p44 0 9 o44 :=
  .cons (p44_0 _) (OpI.mov (.r 12) (.inl rfl)) (by decide) <|
  .cons (p44_3 _) (OpI.mov (.r 11) (.inr rfl)) (by decide) <|
  .cons (p44_6 _) (OpI.mov (.r 7) (.inr rfl)) (by decide) <|
  .nil 9

/-- The stretch at `640`. -/
def p45 : List Byte := [
  0x45, 0x39, 0xca]

theorem p45_0 : ∀ feat, Dec feat p45 0 (FV7z.mk .cmp 32 [gr 32 10, Src.opd 32 (.r 9)] 3) := by dec_rfl

/-- What the stretch does. -/
def o45 : List Op := [
  Op.cmp 32 10 (.r 9)]

theorem b45 (prof : Profile) : Blk prof p45 0 3 o45 :=
  .cons (p45_0 _) (OpI.cmp (.r 9) (.inl rfl)) (by decide) <|
  .nil 3

def j29 : List Byte := [0x72, 0x90]
theorem j29_0 : ∀ feat, Dec feat j29 0 (FV7z.mk (.jcc 2) 64 [.rel 18446744073709551504] 2) := by dec_rfl

def j30 : List Byte := [0x76, 0x89]
theorem j30_0 : ∀ feat, Dec feat j30 0 (FV7z.mk (.jcc 6) 64 [.rel 18446744073709551497] 2) := by dec_rfl

/-- The stretch at `647`. -/
def p46 : List Byte := [
  0x48, 0x8b, 0x3a, 0x4a, 0x89, 0x7c, 0xc5, 0x00, 0x48, 0x8d, 0x3c, 0x36, 0x4c, 0x8d, 0x4f, 0x01,
  0x4c, 0x39, 0xc8]

theorem p46_0 : ∀ feat, Dec feat p46 0 (FV7z.mk .mov 64 [gr 64 7, .mem (mg (some 2) none 1 0 64)] 3) := by dec_rfl
theorem p46_3 : ∀ feat, Dec feat p46 3 (FV7z.mk .mov 64 [.mem (mg (some 5) (some 8) 8 0 64), gr 64 7] 5) := by dec_rfl
theorem p46_8 : ∀ feat, Dec feat p46 8 (FV7z.mk .lea 64 [gr 64 7, .mem (mg (some 6) (some 6) 1 0 0)] 4) := by dec_rfl
theorem p46_12 : ∀ feat, Dec feat p46 12 (FV7z.mk .lea 64 [gr 64 9, .mem (mg (some 7) none 1 1 0)] 4) := by dec_rfl
theorem p46_16 : ∀ feat, Dec feat p46 16 (FV7z.mk .cmp 64 [gr 64 0, Src.opd 64 (.r 9)] 3) := by dec_rfl

/-- What the stretch does. -/
def o46 : List Op := [
  Op.ld 64 7 (some 2) none 1 0,
  Op.st 64 (some 5) (some 8) 8 0 7,
  Op.lea 64 7 (some 6) (some 6) 1 0,
  Op.lea 64 9 (some 7) none 1 1,
  Op.cmp 64 0 (.r 9)]

theorem b46 (prof : Profile) : Blk prof p46 0 19 o46 :=
  .cons (p46_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p46_3 _) (OpI.st (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p46_8 _) (OpI.lea (.inr rfl)) (by decide) <|
  .cons (p46_12 _) (OpI.lea (.inr rfl)) (by decide) <|
  .cons (p46_16 _) (OpI.cmp (.r 9) (.inr rfl)) (by decide) <|
  .nil 19

def j31 : List Byte := [0x0f, 0x82, 0x7a, 0xff, 0xff, 0xff]
theorem j31_0 : ∀ feat, Dec feat j31 0 (FV7z.mk (.jcc 2) 64 [.rel 18446744073709551482] 6) := by dec_rfl

/-- The stretch at `672`. -/
def p47 : List Byte := [
  0x49, 0x89, 0xf0, 0x4c, 0x89, 0xce]

theorem p47_0 : ∀ feat, Dec feat p47 0 (FV7z.mk .mov 64 [gr 64 8, Src.opd 64 (.r 6)] 3) := by dec_rfl
theorem p47_3 : ∀ feat, Dec feat p47 3 (FV7z.mk .mov 64 [gr 64 6, Src.opd 64 (.r 9)] 3) := by dec_rfl

/-- What the stretch does. -/
def o47 : List Op := [
  Op.mov 64 8 (.r 6),
  Op.mov 64 6 (.r 9)]

theorem b47 (prof : Profile) : Blk prof p47 0 6 o47 :=
  .cons (p47_0 _) (OpI.mov (.r 6) (.inr rfl)) (by decide) <|
  .cons (p47_3 _) (OpI.mov (.r 9) (.inr rfl)) (by decide) <|
  .nil 6

def j32 : List Byte := [0xeb, 0xa5]
theorem j32_0 : ∀ feat, Dec feat j32 0 (FV7z.mk .jmp 64 [.rel 18446744073709551525] 2) := by dec_rfl

/-- The stretch at `688`. -/
def p48 : List Byte := [
  0x31, 0xc0]

theorem p48_0 : ∀ feat, Dec feat p48 0 (FV7z.mk .xor 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl

/-- What the stretch does. -/
def o48 : List Op := [
  Op.xor 32 0 (.r 0)]

theorem b48 (prof : Profile) : Blk prof p48 0 2 o48 :=
  .cons (p48_0 _) (OpI.xor (.r 0) (.inl rfl)) (by decide) <|
  .nil 2

/-- The stretch at `696`. -/
def p49 : List Byte := [
  0x48, 0x8b, 0x3c, 0x24]

theorem p49_0 : ∀ feat, Dec feat p49 0 (FV7z.mk .mov 64 [gr 64 7, .mem (mg (some 4) none 1 0 64)] 4) := by dec_rfl

/-- What the stretch does. -/
def o49 : List Op := [
  Op.ld 64 7 (some 4) none 1 0]

theorem b49 (prof : Profile) : Blk prof p49 0 4 o49 :=
  .cons (p49_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .nil 4

def j33 : List Byte := [0xe9, 0xfe, 0xfd, 0xff, 0xff]
theorem j33_0 : ∀ feat, Dec feat j33 0 (FV7z.mk .jmp 64 [.rel 18446744073709551102] 5) := by dec_rfl

end FV7z.Sdt
