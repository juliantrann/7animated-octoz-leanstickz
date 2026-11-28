import FV7z.Lemmas.Sp
import FV7z.Lemmas.BlkOps3
/-!
# The stretches of straight-line code of `CDirItems::ReserveDown` (PLAN.md §M, M1)

Each distinct stretch between labels and jumps (`p*`, 26 of them) and each distinct jump (`j*`, 19) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.Rsv
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The stretch at `0`. -/
def p0 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0x41, 0x54, 0x55, 0x53, 0x48, 0x89, 0xfb, 0x8b, 0x7f, 0x08, 0x3b, 0x7b,
  0x0c]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem p0_4 : ∀ feat, Dec feat p0 4 (FV7z.mk .push 64 [gr 64 12] 2) := by dec_rfl
theorem p0_6 : ∀ feat, Dec feat p0 6 (FV7z.mk .push 64 [gr 64 5] 1) := by dec_rfl
theorem p0_7 : ∀ feat, Dec feat p0 7 (FV7z.mk .push 64 [gr 64 3] 1) := by dec_rfl
theorem p0_8 : ∀ feat, Dec feat p0 8 (FV7z.mk .mov 64 [gr 64 3, Src.opd 64 (.r 7)] 3) := by dec_rfl
theorem p0_11 : ∀ feat, Dec feat p0 11 (FV7z.mk .mov 32 [gr 32 7, .mem (mg (some 7) none 1 8 32)] 3) := by dec_rfl
theorem p0_14 : ∀ feat, Dec feat p0 14 (FV7z.mk .cmp 32 [gr 32 7, .mem (mg (some 3) none 1 12 32)] 3) := by dec_rfl

/-- What the stretch does. -/
def o0 : List Op := [
  Op.nop,
  Op.push 12,
  Op.push 5,
  Op.push 3,
  Op.mov 64 3 (.r 7),
  Op.ld 32 7 (some 7) none 1 8,
  Op.cmpm 32 7 (some 3) none 1 12]

theorem b0 (prof : Profile) : Blk prof p0 0 17 o0 :=
  .cons (p0_0 _) (OpI.endbr) (by decide) <|
  .cons (p0_4 _) (OpI.push) (by decide) <|
  .cons (p0_6 _) (OpI.push) (by decide) <|
  .cons (p0_7 _) (OpI.push) (by decide) <|
  .cons (p0_8 _) (OpI.mov (.r 7) (.inr rfl)) (by decide) <|
  .cons (p0_11 _) (OpI.ld (.inl rfl)) (by decide) <|
  .cons (p0_14 _) (OpI.cmpm (.inl rfl)) (by decide) <|
  .nil 17

def j0 : List Byte := [0x74, 0x1a]
theorem j0_0 : ∀ feat, Dec feat j0 0 (FV7z.mk (.jcc 4) 64 [.rel 26] 2) := by dec_rfl

/-- The stretch at `19`. -/
def p1 : List Byte := [
  0x85, 0xff]

theorem p1_0 : ∀ feat, Dec feat p1 0 (FV7z.mk .test 32 [gr 32 7, Src.opd 32 (.r 7)] 2) := by dec_rfl

/-- What the stretch does. -/
def o1 : List Op := [
  Op.test 32 7 (.r 7)]

theorem b1 (prof : Profile) : Blk prof p1 0 2 o1 :=
  .cons (p1_0 _) (OpI.test (.r 7) (.inl rfl)) (by decide) <|
  .nil 2

def j1 : List Byte := [0x0f, 0x85, 0xbd, 0x00, 0x00, 0x00]
theorem j1_0 : ∀ feat, Dec feat j1 0 (FV7z.mk (.jcc 5) 64 [.rel 189] 6) := by dec_rfl

/-- The stretch at `27`. -/
def p2 : List Byte := [
  0x48, 0x8b, 0x2b, 0x48, 0x85, 0xed]

theorem p2_0 : ∀ feat, Dec feat p2 0 (FV7z.mk .mov 64 [gr 64 5, .mem (mg (some 3) none 1 0 64)] 3) := by dec_rfl
theorem p2_3 : ∀ feat, Dec feat p2 3 (FV7z.mk .test 64 [gr 64 5, Src.opd 64 (.r 5)] 3) := by dec_rfl

/-- What the stretch does. -/
def o2 : List Op := [
  Op.ld 64 5 (some 3) none 1 0,
  Op.test 64 5 (.r 5)]

theorem b2 (prof : Profile) : Blk prof p2 0 6 o2 :=
  .cons (p2_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p2_3 _) (OpI.test (.r 5) (.inr rfl)) (by decide) <|
  .nil 6

def j2 : List Byte := [0x0f, 0x85, 0x69, 0x01, 0x00, 0x00]
theorem j2_0 : ∀ feat, Dec feat j2 0 (FV7z.mk (.jcc 5) 64 [.rel 361] 6) := by dec_rfl

/-- The stretch at `39`. -/
def p3 : List Byte := [
  0x48, 0x89, 0x2b, 0x89, 0x7b, 0x0c]

theorem p3_0 : ∀ feat, Dec feat p3 0 (FV7z.mk .mov 64 [.mem (mg (some 3) none 1 0 64), gr 64 5] 3) := by dec_rfl
theorem p3_3 : ∀ feat, Dec feat p3 3 (FV7z.mk .mov 32 [.mem (mg (some 3) none 1 12 32), gr 32 7] 3) := by dec_rfl

/-- What the stretch does. -/
def o3 : List Op := [
  Op.st 64 (some 3) none 1 0 5,
  Op.st 32 (some 3) none 1 12 7]

theorem b3 (prof : Profile) : Blk prof p3 0 6 o3 :=
  .cons (p3_0 _) (OpI.st (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p3_3 _) (OpI.st (.inr (.inr (.inl rfl)))) (by decide) <|
  .nil 6

/-- The stretch at `45`. -/
def p4 : List Byte := [
  0x8b, 0x7b, 0x18, 0x3b, 0x7b, 0x1c]

theorem p4_0 : ∀ feat, Dec feat p4 0 (FV7z.mk .mov 32 [gr 32 7, .mem (mg (some 3) none 1 24 32)] 3) := by dec_rfl
theorem p4_3 : ∀ feat, Dec feat p4 3 (FV7z.mk .cmp 32 [gr 32 7, .mem (mg (some 3) none 1 28 32)] 3) := by dec_rfl

/-- What the stretch does. -/
def o4 : List Op := [
  Op.ld 32 7 (some 3) none 1 24,
  Op.cmpm 32 7 (some 3) none 1 28]

theorem b4 (prof : Profile) : Blk prof p4 0 6 o4 :=
  .cons (p4_0 _) (OpI.ld (.inl rfl)) (by decide) <|
  .cons (p4_3 _) (OpI.cmpm (.inl rfl)) (by decide) <|
  .nil 6

def j3 : List Byte := [0x74, 0x18]
theorem j3_0 : ∀ feat, Dec feat j3 0 (FV7z.mk (.jcc 4) 64 [.rel 24] 2) := by dec_rfl

def j4 : List Byte := [0x75, 0x67]
theorem j4_0 : ∀ feat, Dec feat j4 0 (FV7z.mk (.jcc 5) 64 [.rel 103] 2) := by dec_rfl

/-- The stretch at `57`. -/
def p5 : List Byte := [
  0x48, 0x8b, 0x6b, 0x10, 0x48, 0x85, 0xed]

theorem p5_0 : ∀ feat, Dec feat p5 0 (FV7z.mk .mov 64 [gr 64 5, .mem (mg (some 3) none 1 16 64)] 4) := by dec_rfl
theorem p5_4 : ∀ feat, Dec feat p5 4 (FV7z.mk .test 64 [gr 64 5, Src.opd 64 (.r 5)] 3) := by dec_rfl

/-- What the stretch does. -/
def o5 : List Op := [
  Op.ld 64 5 (some 3) none 1 16,
  Op.test 64 5 (.r 5)]

theorem b5 (prof : Profile) : Blk prof p5 0 7 o5 :=
  .cons (p5_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p5_4 _) (OpI.test (.r 5) (.inr rfl)) (by decide) <|
  .nil 7

def j5 : List Byte := [0x0f, 0x85, 0x5a, 0x01, 0x00, 0x00]
theorem j5_0 : ∀ feat, Dec feat j5 0 (FV7z.mk (.jcc 5) 64 [.rel 346] 6) := by dec_rfl

/-- The stretch at `70`. -/
def p6 : List Byte := [
  0x48, 0x89, 0x6b, 0x10, 0x89, 0x7b, 0x1c]

theorem p6_0 : ∀ feat, Dec feat p6 0 (FV7z.mk .mov 64 [.mem (mg (some 3) none 1 16 64), gr 64 5] 4) := by dec_rfl
theorem p6_4 : ∀ feat, Dec feat p6 4 (FV7z.mk .mov 32 [.mem (mg (some 3) none 1 28 32), gr 32 7] 3) := by dec_rfl

/-- What the stretch does. -/
def o6 : List Op := [
  Op.st 64 (some 3) none 1 16 5,
  Op.st 32 (some 3) none 1 28 7]

theorem b6 (prof : Profile) : Blk prof p6 0 7 o6 :=
  .cons (p6_0 _) (OpI.st (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p6_4 _) (OpI.st (.inr (.inr (.inl rfl)))) (by decide) <|
  .nil 7

/-- The stretch at `77`. -/
def p7 : List Byte := [
  0x8b, 0x7b, 0x28, 0x3b, 0x7b, 0x2c]

theorem p7_0 : ∀ feat, Dec feat p7 0 (FV7z.mk .mov 32 [gr 32 7, .mem (mg (some 3) none 1 40 32)] 3) := by dec_rfl
theorem p7_3 : ∀ feat, Dec feat p7 3 (FV7z.mk .cmp 32 [gr 32 7, .mem (mg (some 3) none 1 44 32)] 3) := by dec_rfl

/-- What the stretch does. -/
def o7 : List Op := [
  Op.ld 32 7 (some 3) none 1 40,
  Op.cmpm 32 7 (some 3) none 1 44]

theorem b7 (prof : Profile) : Blk prof p7 0 6 o7 :=
  .cons (p7_0 _) (OpI.ld (.inl rfl)) (by decide) <|
  .cons (p7_3 _) (OpI.cmpm (.inl rfl)) (by decide) <|
  .nil 6

def j6 : List Byte := [0x74, 0x1c]
theorem j6_0 : ∀ feat, Dec feat j6 0 (FV7z.mk (.jcc 4) 64 [.rel 28] 2) := by dec_rfl

def j7 : List Byte := [0x0f, 0x85, 0xeb, 0x00, 0x00, 0x00]
theorem j7_0 : ∀ feat, Dec feat j7 0 (FV7z.mk (.jcc 5) 64 [.rel 235] 6) := by dec_rfl

/-- The stretch at `93`. -/
def p8 : List Byte := [
  0x48, 0x8b, 0x6b, 0x20, 0x48, 0x85, 0xed]

theorem p8_0 : ∀ feat, Dec feat p8 0 (FV7z.mk .mov 64 [gr 64 5, .mem (mg (some 3) none 1 32 64)] 4) := by dec_rfl
theorem p8_4 : ∀ feat, Dec feat p8 4 (FV7z.mk .test 64 [gr 64 5, Src.opd 64 (.r 5)] 3) := by dec_rfl

/-- What the stretch does. -/
def o8 : List Op := [
  Op.ld 64 5 (some 3) none 1 32,
  Op.test 64 5 (.r 5)]

theorem b8 (prof : Profile) : Blk prof p8 0 7 o8 :=
  .cons (p8_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p8_4 _) (OpI.test (.r 5) (.inr rfl)) (by decide) <|
  .nil 7

def j8 : List Byte := [0x0f, 0x85, 0x46, 0x01, 0x00, 0x00]
theorem j8_0 : ∀ feat, Dec feat j8 0 (FV7z.mk (.jcc 5) 64 [.rel 326] 6) := by dec_rfl

/-- The stretch at `106`. -/
def p9 : List Byte := [
  0x48, 0x89, 0x6b, 0x20, 0x89, 0x7b, 0x2c]

theorem p9_0 : ∀ feat, Dec feat p9 0 (FV7z.mk .mov 64 [.mem (mg (some 3) none 1 32 64), gr 64 5] 4) := by dec_rfl
theorem p9_4 : ∀ feat, Dec feat p9 4 (FV7z.mk .mov 32 [.mem (mg (some 3) none 1 44 32), gr 32 7] 3) := by dec_rfl

/-- What the stretch does. -/
def o9 : List Op := [
  Op.st 64 (some 3) none 1 32 5,
  Op.st 32 (some 3) none 1 44 7]

theorem b9 (prof : Profile) : Blk prof p9 0 7 o9 :=
  .cons (p9_0 _) (OpI.st (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p9_4 _) (OpI.st (.inr (.inr (.inl rfl)))) (by decide) <|
  .nil 7

/-- The stretch at `113`. -/
def p10 : List Byte := [
  0x8b, 0x7b, 0x38, 0x3b, 0x7b, 0x3c]

theorem p10_0 : ∀ feat, Dec feat p10 0 (FV7z.mk .mov 32 [gr 32 7, .mem (mg (some 3) none 1 56 32)] 3) := by dec_rfl
theorem p10_3 : ∀ feat, Dec feat p10 3 (FV7z.mk .cmp 32 [gr 32 7, .mem (mg (some 3) none 1 60 32)] 3) := by dec_rfl

/-- What the stretch does. -/
def o10 : List Op := [
  Op.ld 32 7 (some 3) none 1 56,
  Op.cmpm 32 7 (some 3) none 1 60]

theorem b10 (prof : Profile) : Blk prof p10 0 6 o10 :=
  .cons (p10_0 _) (OpI.ld (.inl rfl)) (by decide) <|
  .cons (p10_3 _) (OpI.cmpm (.inl rfl)) (by decide) <|
  .nil 6

def j9 : List Byte := [0x0f, 0x85, 0x8f, 0x00, 0x00, 0x00]
theorem j9_0 : ∀ feat, Dec feat j9 0 (FV7z.mk (.jcc 5) 64 [.rel 143] 6) := by dec_rfl

/-- The stretch at `129`. -/
def p11 : List Byte := [
  0x48, 0x8b, 0x6b, 0x30, 0x48, 0x85, 0xed]

theorem p11_0 : ∀ feat, Dec feat p11 0 (FV7z.mk .mov 64 [gr 64 5, .mem (mg (some 3) none 1 48 64)] 4) := by dec_rfl
theorem p11_4 : ∀ feat, Dec feat p11 4 (FV7z.mk .test 64 [gr 64 5, Src.opd 64 (.r 5)] 3) := by dec_rfl

/-- What the stretch does. -/
def o11 : List Op := [
  Op.ld 64 5 (some 3) none 1 48,
  Op.test 64 5 (.r 5)]

theorem b11 (prof : Profile) : Blk prof p11 0 7 o11 :=
  .cons (p11_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p11_4 _) (OpI.test (.r 5) (.inr rfl)) (by decide) <|
  .nil 7

def j10 : List Byte := [0x0f, 0x85, 0xf2, 0x00, 0x00, 0x00]
theorem j10_0 : ∀ feat, Dec feat j10 0 (FV7z.mk (.jcc 5) 64 [.rel 242] 6) := by dec_rfl

/-- The stretch at `142`. -/
def p12 : List Byte := [
  0x48, 0x89, 0x6b, 0x30, 0x89, 0x7b, 0x3c]

theorem p12_0 : ∀ feat, Dec feat p12 0 (FV7z.mk .mov 64 [.mem (mg (some 3) none 1 48 64), gr 64 5] 4) := by dec_rfl
theorem p12_4 : ∀ feat, Dec feat p12 4 (FV7z.mk .mov 32 [.mem (mg (some 3) none 1 60 32), gr 32 7] 3) := by dec_rfl

/-- What the stretch does. -/
def o12 : List Op := [
  Op.st 64 (some 3) none 1 48 5,
  Op.st 32 (some 3) none 1 60 7]

theorem b12 (prof : Profile) : Blk prof p12 0 7 o12 :=
  .cons (p12_0 _) (OpI.st (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p12_4 _) (OpI.st (.inr (.inr (.inl rfl)))) (by decide) <|
  .nil 7

/-- The stretch at `149`. -/
def p13 : List Byte := [
  0x5b, 0x5d, 0x41, 0x5c]

theorem p13_0 : ∀ feat, Dec feat p13 0 (FV7z.mk .pop 64 [gr 64 3] 1) := by dec_rfl
theorem p13_1 : ∀ feat, Dec feat p13 1 (FV7z.mk .pop 64 [gr 64 5] 1) := by dec_rfl
theorem p13_2 : ∀ feat, Dec feat p13 2 (FV7z.mk .pop 64 [gr 64 12] 2) := by dec_rfl

/-- What the stretch does. -/
def o13 : List Op := [
  Op.pop 3,
  Op.pop 5,
  Op.pop 12]

theorem b13 (prof : Profile) : Blk prof p13 0 4 o13 :=
  .cons (p13_0 _) (OpI.pop) (by decide) <|
  .cons (p13_1 _) (OpI.pop) (by decide) <|
  .cons (p13_2 _) (OpI.pop) (by decide) <|
  .nil 4

/-- The stretch at `160`. -/
def p14 : List Byte := [
  0x48, 0xc1, 0xe7, 0x02]

theorem p14_0 : ∀ feat, Dec feat p14 0 (FV7z.mk .shl 64 [gr 64 7, Src.opd 8 (.i 2)] 4) := by dec_rfl

/-- What the stretch does. -/
def o14 : List Op := [
  Op.shl64 7 (.i 2)]

theorem b14 (prof : Profile) : Blk prof p14 0 4 o14 :=
  .cons (p14_0 _) (OpI.shl64 (.i 2)) (by decide) <|
  .nil 4

/-- The stretch at `169`. -/
def p15 : List Byte := [
  0x4c, 0x8b, 0x63, 0x10, 0x8b, 0x53, 0x18, 0x48, 0x89, 0xc7, 0x48, 0x89, 0xc5, 0x48, 0xc1, 0xe2,
  0x02, 0x4c, 0x89, 0xe6]

theorem p15_0 : ∀ feat, Dec feat p15 0 (FV7z.mk .mov 64 [gr 64 12, .mem (mg (some 3) none 1 16 64)] 4) := by dec_rfl
theorem p15_4 : ∀ feat, Dec feat p15 4 (FV7z.mk .mov 32 [gr 32 2, .mem (mg (some 3) none 1 24 32)] 3) := by dec_rfl
theorem p15_7 : ∀ feat, Dec feat p15 7 (FV7z.mk .mov 64 [gr 64 7, Src.opd 64 (.r 0)] 3) := by dec_rfl
theorem p15_10 : ∀ feat, Dec feat p15 10 (FV7z.mk .mov 64 [gr 64 5, Src.opd 64 (.r 0)] 3) := by dec_rfl
theorem p15_13 : ∀ feat, Dec feat p15 13 (FV7z.mk .shl 64 [gr 64 2, Src.opd 8 (.i 2)] 4) := by dec_rfl
theorem p15_17 : ∀ feat, Dec feat p15 17 (FV7z.mk .mov 64 [gr 64 6, Src.opd 64 (.r 12)] 3) := by dec_rfl

/-- What the stretch does. -/
def o15 : List Op := [
  Op.ld 64 12 (some 3) none 1 16,
  Op.ld 32 2 (some 3) none 1 24,
  Op.mov 64 7 (.r 0),
  Op.mov 64 5 (.r 0),
  Op.shl64 2 (.i 2),
  Op.mov 64 6 (.r 12)]

theorem b15 (prof : Profile) : Blk prof p15 0 20 o15 :=
  .cons (p15_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p15_4 _) (OpI.ld (.inl rfl)) (by decide) <|
  .cons (p15_7 _) (OpI.mov (.r 0) (.inr rfl)) (by decide) <|
  .cons (p15_10 _) (OpI.mov (.r 0) (.inr rfl)) (by decide) <|
  .cons (p15_13 _) (OpI.shl64 (.i 2)) (by decide) <|
  .cons (p15_17 _) (OpI.mov (.r 12) (.inr rfl)) (by decide) <|
  .nil 20

/-- The stretch at `194`. -/
def p16 : List Byte := [
  0x4c, 0x89, 0xe7]

theorem p16_0 : ∀ feat, Dec feat p16 0 (FV7z.mk .mov 64 [gr 64 7, Src.opd 64 (.r 12)] 3) := by dec_rfl

/-- What the stretch does. -/
def o16 : List Op := [
  Op.mov 64 7 (.r 12)]

theorem b16 (prof : Profile) : Blk prof p16 0 3 o16 :=
  .cons (p16_0 _) (OpI.mov (.r 12) (.inr rfl)) (by decide) <|
  .nil 3

/-- The stretch at `202`. -/
def p17 : List Byte := [
  0x8b, 0x7b, 0x18]

theorem p17_0 : ∀ feat, Dec feat p17 0 (FV7z.mk .mov 32 [gr 32 7, .mem (mg (some 3) none 1 24 32)] 3) := by dec_rfl

/-- What the stretch does. -/
def o17 : List Op := [
  Op.ld 32 7 (some 3) none 1 24]

theorem b17 (prof : Profile) : Blk prof p17 0 3 o17 :=
  .cons (p17_0 _) (OpI.ld (.inl rfl)) (by decide) <|
  .nil 3

def j11 : List Byte := [0xe9, 0x74, 0xff, 0xff, 0xff]
theorem j11_0 : ∀ feat, Dec feat j11 0 (FV7z.mk .jmp 64 [.rel 18446744073709551476] 5) := by dec_rfl

/-- The stretch at `216`. -/
def p18 : List Byte := [
  0x48, 0xc1, 0xe7, 0x03]

theorem p18_0 : ∀ feat, Dec feat p18 0 (FV7z.mk .shl 64 [gr 64 7, Src.opd 8 (.i 3)] 4) := by dec_rfl

/-- What the stretch does. -/
def o18 : List Op := [
  Op.shl64 7 (.i 3)]

theorem b18 (prof : Profile) : Blk prof p18 0 4 o18 :=
  .cons (p18_0 _) (OpI.shl64 (.i 3)) (by decide) <|
  .nil 4

/-- The stretch at `225`. -/
def p19 : List Byte := [
  0x4c, 0x8b, 0x23, 0x8b, 0x53, 0x08, 0x48, 0x89, 0xc7, 0x48, 0x89, 0xc5, 0x48, 0xc1, 0xe2, 0x03,
  0x4c, 0x89, 0xe6]

theorem p19_0 : ∀ feat, Dec feat p19 0 (FV7z.mk .mov 64 [gr 64 12, .mem (mg (some 3) none 1 0 64)] 3) := by dec_rfl
theorem p19_3 : ∀ feat, Dec feat p19 3 (FV7z.mk .mov 32 [gr 32 2, .mem (mg (some 3) none 1 8 32)] 3) := by dec_rfl
theorem p19_6 : ∀ feat, Dec feat p19 6 (FV7z.mk .mov 64 [gr 64 7, Src.opd 64 (.r 0)] 3) := by dec_rfl
theorem p19_9 : ∀ feat, Dec feat p19 9 (FV7z.mk .mov 64 [gr 64 5, Src.opd 64 (.r 0)] 3) := by dec_rfl
theorem p19_12 : ∀ feat, Dec feat p19 12 (FV7z.mk .shl 64 [gr 64 2, Src.opd 8 (.i 3)] 4) := by dec_rfl
theorem p19_16 : ∀ feat, Dec feat p19 16 (FV7z.mk .mov 64 [gr 64 6, Src.opd 64 (.r 12)] 3) := by dec_rfl

/-- What the stretch does. -/
def o19 : List Op := [
  Op.ld 64 12 (some 3) none 1 0,
  Op.ld 32 2 (some 3) none 1 8,
  Op.mov 64 7 (.r 0),
  Op.mov 64 5 (.r 0),
  Op.shl64 2 (.i 3),
  Op.mov 64 6 (.r 12)]

theorem b19 (prof : Profile) : Blk prof p19 0 19 o19 :=
  .cons (p19_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p19_3 _) (OpI.ld (.inl rfl)) (by decide) <|
  .cons (p19_6 _) (OpI.mov (.r 0) (.inr rfl)) (by decide) <|
  .cons (p19_9 _) (OpI.mov (.r 0) (.inr rfl)) (by decide) <|
  .cons (p19_12 _) (OpI.shl64 (.i 3)) (by decide) <|
  .cons (p19_16 _) (OpI.mov (.r 12) (.inr rfl)) (by decide) <|
  .nil 19

/-- The stretch at `257`. -/
def p20 : List Byte := [
  0x8b, 0x7b, 0x08]

theorem p20_0 : ∀ feat, Dec feat p20 0 (FV7z.mk .mov 32 [gr 32 7, .mem (mg (some 3) none 1 8 32)] 3) := by dec_rfl

/-- What the stretch does. -/
def o20 : List Op := [
  Op.ld 32 7 (some 3) none 1 8]

theorem b20 (prof : Profile) : Blk prof p20 0 3 o20 :=
  .cons (p20_0 _) (OpI.ld (.inl rfl)) (by decide) <|
  .nil 3

def j12 : List Byte := [0xe9, 0x1e, 0xff, 0xff, 0xff]
theorem j12_0 : ∀ feat, Dec feat j12 0 (FV7z.mk .jmp 64 [.rel 18446744073709551390] 5) := by dec_rfl

/-- The stretch at `281`. -/
def p21 : List Byte := [
  0x4c, 0x8b, 0x63, 0x30, 0x8b, 0x53, 0x38, 0x48, 0x89, 0xc7, 0x48, 0x89, 0xc5, 0x48, 0xc1, 0xe2,
  0x03, 0x4c, 0x89, 0xe6]

theorem p21_0 : ∀ feat, Dec feat p21 0 (FV7z.mk .mov 64 [gr 64 12, .mem (mg (some 3) none 1 48 64)] 4) := by dec_rfl
theorem p21_4 : ∀ feat, Dec feat p21 4 (FV7z.mk .mov 32 [gr 32 2, .mem (mg (some 3) none 1 56 32)] 3) := by dec_rfl
theorem p21_7 : ∀ feat, Dec feat p21 7 (FV7z.mk .mov 64 [gr 64 7, Src.opd 64 (.r 0)] 3) := by dec_rfl
theorem p21_10 : ∀ feat, Dec feat p21 10 (FV7z.mk .mov 64 [gr 64 5, Src.opd 64 (.r 0)] 3) := by dec_rfl
theorem p21_13 : ∀ feat, Dec feat p21 13 (FV7z.mk .shl 64 [gr 64 2, Src.opd 8 (.i 3)] 4) := by dec_rfl
theorem p21_17 : ∀ feat, Dec feat p21 17 (FV7z.mk .mov 64 [gr 64 6, Src.opd 64 (.r 12)] 3) := by dec_rfl

/-- What the stretch does. -/
def o21 : List Op := [
  Op.ld 64 12 (some 3) none 1 48,
  Op.ld 32 2 (some 3) none 1 56,
  Op.mov 64 7 (.r 0),
  Op.mov 64 5 (.r 0),
  Op.shl64 2 (.i 3),
  Op.mov 64 6 (.r 12)]

theorem b21 (prof : Profile) : Blk prof p21 0 20 o21 :=
  .cons (p21_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p21_4 _) (OpI.ld (.inl rfl)) (by decide) <|
  .cons (p21_7 _) (OpI.mov (.r 0) (.inr rfl)) (by decide) <|
  .cons (p21_10 _) (OpI.mov (.r 0) (.inr rfl)) (by decide) <|
  .cons (p21_13 _) (OpI.shl64 (.i 3)) (by decide) <|
  .cons (p21_17 _) (OpI.mov (.r 12) (.inr rfl)) (by decide) <|
  .nil 20

/-- The stretch at `314`. -/
def p22 : List Byte := [
  0x8b, 0x7b, 0x38]

theorem p22_0 : ∀ feat, Dec feat p22 0 (FV7z.mk .mov 32 [gr 32 7, .mem (mg (some 3) none 1 56 32)] 3) := by dec_rfl

/-- What the stretch does. -/
def o22 : List Op := [
  Op.ld 32 7 (some 3) none 1 56]

theorem b22 (prof : Profile) : Blk prof p22 0 3 o22 :=
  .cons (p22_0 _) (OpI.ld (.inl rfl)) (by decide) <|
  .nil 3

def j13 : List Byte := [0xe9, 0x4c, 0xff, 0xff, 0xff]
theorem j13_0 : ∀ feat, Dec feat j13 0 (FV7z.mk .jmp 64 [.rel 18446744073709551436] 5) := by dec_rfl

/-- The stretch at `337`. -/
def p23 : List Byte := [
  0x4c, 0x8b, 0x63, 0x20, 0x8b, 0x53, 0x28, 0x48, 0x89, 0xc7, 0x48, 0x89, 0xc5, 0x48, 0xc1, 0xe2,
  0x02, 0x4c, 0x89, 0xe6]

theorem p23_0 : ∀ feat, Dec feat p23 0 (FV7z.mk .mov 64 [gr 64 12, .mem (mg (some 3) none 1 32 64)] 4) := by dec_rfl
theorem p23_4 : ∀ feat, Dec feat p23 4 (FV7z.mk .mov 32 [gr 32 2, .mem (mg (some 3) none 1 40 32)] 3) := by dec_rfl
theorem p23_7 : ∀ feat, Dec feat p23 7 (FV7z.mk .mov 64 [gr 64 7, Src.opd 64 (.r 0)] 3) := by dec_rfl
theorem p23_10 : ∀ feat, Dec feat p23 10 (FV7z.mk .mov 64 [gr 64 5, Src.opd 64 (.r 0)] 3) := by dec_rfl
theorem p23_13 : ∀ feat, Dec feat p23 13 (FV7z.mk .shl 64 [gr 64 2, Src.opd 8 (.i 2)] 4) := by dec_rfl
theorem p23_17 : ∀ feat, Dec feat p23 17 (FV7z.mk .mov 64 [gr 64 6, Src.opd 64 (.r 12)] 3) := by dec_rfl

/-- What the stretch does. -/
def o23 : List Op := [
  Op.ld 64 12 (some 3) none 1 32,
  Op.ld 32 2 (some 3) none 1 40,
  Op.mov 64 7 (.r 0),
  Op.mov 64 5 (.r 0),
  Op.shl64 2 (.i 2),
  Op.mov 64 6 (.r 12)]

theorem b23 (prof : Profile) : Blk prof p23 0 20 o23 :=
  .cons (p23_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p23_4 _) (OpI.ld (.inl rfl)) (by decide) <|
  .cons (p23_7 _) (OpI.mov (.r 0) (.inr rfl)) (by decide) <|
  .cons (p23_10 _) (OpI.mov (.r 0) (.inr rfl)) (by decide) <|
  .cons (p23_13 _) (OpI.shl64 (.i 2)) (by decide) <|
  .cons (p23_17 _) (OpI.mov (.r 12) (.inr rfl)) (by decide) <|
  .nil 20

/-- The stretch at `370`. -/
def p24 : List Byte := [
  0x8b, 0x7b, 0x28]

theorem p24_0 : ∀ feat, Dec feat p24 0 (FV7z.mk .mov 32 [gr 32 7, .mem (mg (some 3) none 1 40 32)] 3) := by dec_rfl

/-- What the stretch does. -/
def o24 : List Op := [
  Op.ld 32 7 (some 3) none 1 40]

theorem b24 (prof : Profile) : Blk prof p24 0 3 o24 :=
  .cons (p24_0 _) (OpI.ld (.inl rfl)) (by decide) <|
  .nil 3

def j14 : List Byte := [0xe9, 0xf0, 0xfe, 0xff, 0xff]
theorem j14_0 : ∀ feat, Dec feat j14 0 (FV7z.mk .jmp 64 [.rel 18446744073709551344] 5) := by dec_rfl

/-- The stretch at `384`. -/
def p25 : List Byte := [
  0x49, 0x89, 0xec, 0x31, 0xed]

theorem p25_0 : ∀ feat, Dec feat p25 0 (FV7z.mk .mov 64 [gr 64 12, Src.opd 64 (.r 5)] 3) := by dec_rfl
theorem p25_3 : ∀ feat, Dec feat p25 3 (FV7z.mk .xor 32 [gr 32 5, Src.opd 32 (.r 5)] 2) := by dec_rfl

/-- What the stretch does. -/
def o25 : List Op := [
  Op.mov 64 12 (.r 5),
  Op.xor 32 5 (.r 5)]

theorem b25 (prof : Profile) : Blk prof p25 0 5 o25 :=
  .cons (p25_0 _) (OpI.mov (.r 5) (.inr rfl)) (by decide) <|
  .cons (p25_3 _) (OpI.xor (.r 5) (.inl rfl)) (by decide) <|
  .nil 5

def j15 : List Byte := [0xeb, 0xab]
theorem j15_0 : ∀ feat, Dec feat j15 0 (FV7z.mk .jmp 64 [.rel 18446744073709551531] 2) := by dec_rfl

def j16 : List Byte := [0xe9, 0x5f, 0xff, 0xff, 0xff]
theorem j16_0 : ∀ feat, Dec feat j16 0 (FV7z.mk .jmp 64 [.rel 18446744073709551455] 5) := by dec_rfl

def j17 : List Byte := [0xe9, 0x18, 0xff, 0xff, 0xff]
theorem j17_0 : ∀ feat, Dec feat j17 0 (FV7z.mk .jmp 64 [.rel 18446744073709551384] 5) := by dec_rfl

def j18 : List Byte := [0xeb, 0xb3]
theorem j18_0 : ∀ feat, Dec feat j18 0 (FV7z.mk .jmp 64 [.rel 18446744073709551539] 2) := by dec_rfl

end FV7z.Rsv
