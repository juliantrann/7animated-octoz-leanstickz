import FV7z.Lemmas.Sp
import FV7z.Lemmas.BlkOps2
/-!
# The stretches of straight-line code of `__tunables_init` (PLAN.md G3, startup)

Each distinct stretch between labels and jumps (`p*`, 28 of them) and each distinct jump (`j*`, 23) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.Tun
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The stretch at `0`. -/
def p0 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0x41, 0x57, 0x49, 0x89, 0xf8, 0x41, 0x56, 0x41, 0x55, 0x41, 0x54, 0x55,
  0x53, 0x48, 0x83, 0xec, 0x38, 0x8b, 0x15, 0xb5, 0x2e, 0x12, 0x00, 0x85, 0xd2]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem p0_4 : ∀ feat, Dec feat p0 4 (FV7z.mk .push 64 [gr 64 15] 2) := by dec_rfl
theorem p0_6 : ∀ feat, Dec feat p0 6 (FV7z.mk .mov 64 [gr 64 8, Src.opd 64 (.r 7)] 3) := by dec_rfl
theorem p0_9 : ∀ feat, Dec feat p0 9 (FV7z.mk .push 64 [gr 64 14] 2) := by dec_rfl
theorem p0_11 : ∀ feat, Dec feat p0 11 (FV7z.mk .push 64 [gr 64 13] 2) := by dec_rfl
theorem p0_13 : ∀ feat, Dec feat p0 13 (FV7z.mk .push 64 [gr 64 12] 2) := by dec_rfl
theorem p0_15 : ∀ feat, Dec feat p0 15 (FV7z.mk .push 64 [gr 64 5] 1) := by dec_rfl
theorem p0_16 : ∀ feat, Dec feat p0 16 (FV7z.mk .push 64 [gr 64 3] 1) := by dec_rfl
theorem p0_17 : ∀ feat, Dec feat p0 17 (FV7z.mk .sub 64 [gr 64 4, Src.opd 64 (.i 56)] 4) := by dec_rfl
theorem p0_21 : ∀ feat, Dec feat p0 21 (FV7z.mk .mov 32 [gr 32 2, .mem (mrip 1191605 32)] 6) := by dec_rfl
theorem p0_27 : ∀ feat, Dec feat p0 27 (FV7z.mk .test 32 [gr 32 2, Src.opd 32 (.r 2)] 2) := by dec_rfl

/-- What the stretch does. -/
def o0 : List Op := [
  Op.nop,
  Op.push 15,
  Op.mov 64 8 (.r 7),
  Op.push 14,
  Op.push 13,
  Op.push 12,
  Op.push 5,
  Op.push 3,
  Op.sub 64 4 (.i 56),
  Op.lda 32 2 7937248,
  Op.test 32 2 (.r 2)]

theorem b0 (prof : Profile) : BlkA prof p0 (0x66ee10 : Addr) 0 29 o0 :=
  .cons (p0_0 _) ((OpI.endbr).at _) (by decide) <|
  .cons (p0_4 _) ((OpI.push).at _) (by decide) <|
  .cons (p0_6 _) ((OpI.mov (.r 7) (.inr rfl)).at _) (by decide) <|
  .cons (p0_9 _) ((OpI.push).at _) (by decide) <|
  .cons (p0_11 _) ((OpI.push).at _) (by decide) <|
  .cons (p0_13 _) ((OpI.push).at _) (by decide) <|
  .cons (p0_15 _) ((OpI.push).at _) (by decide) <|
  .cons (p0_16 _) ((OpI.push).at _) (by decide) <|
  .cons (p0_17 _) ((OpI.sub (.i 56) (.inr rfl)).at _) (by decide) <|
  .cons (p0_21 _) (OpIA.ld_rip (.inl rfl) (by decide)) (by decide) <|
  .cons (p0_27 _) ((OpI.test (.r 2) (.inl rfl)).at _) (by decide) <|
  .nil 29

def j0 : List Byte := [0x0f, 0x85, 0x0b, 0x05, 0x00, 0x00]
theorem j0_0 : ∀ feat, Dec feat j0 0 (FV7z.mk (.jcc 5) 64 [.rel 1291] 6) := by dec_rfl

/-- The stretch at `35`. -/
def p1 : List Byte := [
  0x4d, 0x89, 0xc5, 0x66, 0x2e, 0x0f, 0x1f, 0x84, 0x00, 0x00, 0x00, 0x00, 0x00]

theorem p1_0 : ∀ feat, Dec feat p1 0 (FV7z.mk .mov 64 [gr 64 13, Src.opd 64 (.r 8)] 3) := by dec_rfl
theorem p1_3 : ∀ feat, Dec feat p1 3 (FV7z.mk .nop 16 [.mem (mg (some 0) (some 0) 1 0 16)] 10) := by dec_rfl

/-- What the stretch does. -/
def o1 : List Op := [
  Op.mov 64 13 (.r 8),
  Op.nop]

theorem b1 (prof : Profile) : Blk prof p1 0 13 o1 :=
  .cons (p1_0 _) (OpI.mov (.r 8) (.inr rfl)) (by decide) <|
  .cons (p1_3 _) (OpI.nop) (by decide) <|
  .nil 13

/-- The stretch at `48`. -/
def p2 : List Byte := [
  0x4d, 0x85, 0xed]

theorem p2_0 : ∀ feat, Dec feat p2 0 (FV7z.mk .test 64 [gr 64 13, Src.opd 64 (.r 13)] 3) := by dec_rfl

/-- What the stretch does. -/
def o2 : List Op := [
  Op.test 64 13 (.r 13)]

theorem b2 (prof : Profile) : Blk prof p2 0 3 o2 :=
  .cons (p2_0 _) (OpI.test (.r 13) (.inr rfl)) (by decide) <|
  .nil 3

def j1 : List Byte := [0x0f, 0x84, 0x11, 0x01, 0x00, 0x00]
theorem j1_0 : ∀ feat, Dec feat j1 0 (FV7z.mk (.jcc 4) 64 [.rel 273] 6) := by dec_rfl

/-- The stretch at `57`. -/
def p3 : List Byte := [
  0x49, 0x8b, 0x5d, 0x00, 0x48, 0x85, 0xdb]

theorem p3_0 : ∀ feat, Dec feat p3 0 (FV7z.mk .mov 64 [gr 64 3, .mem (mg (some 13) none 1 0 64)] 4) := by dec_rfl
theorem p3_4 : ∀ feat, Dec feat p3 4 (FV7z.mk .test 64 [gr 64 3, Src.opd 64 (.r 3)] 3) := by dec_rfl

/-- What the stretch does. -/
def o3 : List Op := [
  Op.ld 64 3 (some 13) none 1 0,
  Op.test 64 3 (.r 3)]

theorem b3 (prof : Profile) : Blk prof p3 0 7 o3 :=
  .cons (p3_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p3_4 _) (OpI.test (.r 3) (.inr rfl)) (by decide) <|
  .nil 7

def j2 : List Byte := [0x0f, 0x84, 0x04, 0x01, 0x00, 0x00]
theorem j2_0 : ∀ feat, Dec feat j2 0 (FV7z.mk (.jcc 4) 64 [.rel 260] 6) := by dec_rfl

/-- The stretch at `70`. -/
def p4 : List Byte := [
  0x0f, 0xb6, 0x13, 0x4d, 0x8d, 0x7d, 0x08, 0x80, 0xfa, 0x3d]

theorem p4_0 : ∀ feat, Dec feat p4 0 (FV7z.mk .movzx 32 [gr 32 2, .mem (mg (some 3) none 1 0 8)] 3) := by dec_rfl
theorem p4_3 : ∀ feat, Dec feat p4 3 (FV7z.mk .lea 64 [gr 64 15, .mem (mg (some 13) none 1 8 0)] 4) := by dec_rfl
theorem p4_7 : ∀ feat, Dec feat p4 7 (FV7z.mk .cmp 8 [gr 8 2, Src.opd 8 (.i 61)] 3) := by dec_rfl

/-- What the stretch does. -/
def o4 : List Op := [
  Op.ldzx 8 2 (some 3) none 1 0,
  Op.lea 64 15 (some 13) none 1 8,
  Op.cmp 8 2 (.i 61)]

theorem b4 (prof : Profile) : Blk prof p4 0 10 o4 :=
  .cons (p4_0 _) (OpI.ldzx (.inl rfl)) (by decide) <|
  .cons (p4_3 _) (OpI.lea (.inr rfl)) (by decide) <|
  .cons (p4_7 _) (OpI.cmp8 (.i 61)) (by decide) <|
  .nil 10

def j3 : List Byte := [0x0f, 0x84, 0x5f, 0x04, 0x00, 0x00]
theorem j3_0 : ∀ feat, Dec feat j3 0 (FV7z.mk (.jcc 4) 64 [.rel 1119] 6) := by dec_rfl

/-- The stretch at `86`. -/
def p5 : List Byte := [
  0x84, 0xd2]

theorem p5_0 : ∀ feat, Dec feat p5 0 (FV7z.mk .test 8 [gr 8 2, Src.opd 8 (.r 2)] 2) := by dec_rfl

/-- What the stretch does. -/
def o5 : List Op := [
  Op.test 8 2 (.r 2)]

theorem b5 (prof : Profile) : Blk prof p5 0 2 o5 :=
  .cons (p5_0 _) (OpI.test8 (.r 2)) (by decide) <|
  .nil 2

def j4 : List Byte := [0x0f, 0x84, 0x57, 0x04, 0x00, 0x00]
theorem j4_0 : ∀ feat, Dec feat j4 0 (FV7z.mk (.jcc 4) 64 [.rel 1111] 6) := by dec_rfl

/-- The stretch at `94`. -/
def p6 : List Byte := [
  0xb8, 0x01, 0x00, 0x00, 0x00, 0x0f, 0x1f, 0x44, 0x00, 0x00]

theorem p6_0 : ∀ feat, Dec feat p6 0 (FV7z.mk .mov 32 [gr 32 0, Src.opd 32 (.i 1)] 5) := by dec_rfl
theorem p6_5 : ∀ feat, Dec feat p6 5 (FV7z.mk .nop 32 [.mem (mg (some 0) (some 0) 1 0 32)] 5) := by dec_rfl

/-- What the stretch does. -/
def o6 : List Op := [
  Op.mov 32 0 (.i 1),
  Op.nop]

theorem b6 (prof : Profile) : Blk prof p6 0 10 o6 :=
  .cons (p6_0 _) (OpI.mov (.i 1) (.inl rfl)) (by decide) <|
  .cons (p6_5 _) (OpI.nop) (by decide) <|
  .nil 10

/-- The stretch at `104`. -/
def p7 : List Byte := [
  0x0f, 0xb6, 0x14, 0x03, 0x48, 0x89, 0xc1, 0x48, 0x83, 0xc0, 0x01, 0x84, 0xd2]

theorem p7_0 : ∀ feat, Dec feat p7 0 (FV7z.mk .movzx 32 [gr 32 2, .mem (mg (some 3) (some 0) 1 0 8)] 4) := by dec_rfl
theorem p7_4 : ∀ feat, Dec feat p7 4 (FV7z.mk .mov 64 [gr 64 1, Src.opd 64 (.r 0)] 3) := by dec_rfl
theorem p7_7 : ∀ feat, Dec feat p7 7 (FV7z.mk .add 64 [gr 64 0, Src.opd 64 (.i 1)] 4) := by dec_rfl
theorem p7_11 : ∀ feat, Dec feat p7 11 (FV7z.mk .test 8 [gr 8 2, Src.opd 8 (.r 2)] 2) := by dec_rfl

/-- What the stretch does. -/
def o7 : List Op := [
  Op.ldzx 8 2 (some 3) (some 0) 1 0,
  Op.mov 64 1 (.r 0),
  Op.add 64 0 (.i 1),
  Op.test 8 2 (.r 2)]

theorem b7 (prof : Profile) : Blk prof p7 0 13 o7 :=
  .cons (p7_0 _) (OpI.ldzx (.inl rfl)) (by decide) <|
  .cons (p7_4 _) (OpI.mov (.r 0) (.inr rfl)) (by decide) <|
  .cons (p7_7 _) (OpI.add (.i 1) (.inr rfl)) (by decide) <|
  .cons (p7_11 _) (OpI.test8 (.r 2)) (by decide) <|
  .nil 13

def j5 : List Byte := [0x0f, 0x84, 0xc3, 0x00, 0x00, 0x00]
theorem j5_0 : ∀ feat, Dec feat j5 0 (FV7z.mk (.jcc 4) 64 [.rel 195] 6) := by dec_rfl

/-- The stretch at `123`. -/
def p8 : List Byte := [
  0x80, 0xfa, 0x3d]

theorem p8_0 : ∀ feat, Dec feat p8 0 (FV7z.mk .cmp 8 [gr 8 2, Src.opd 8 (.i 61)] 3) := by dec_rfl

/-- What the stretch does. -/
def o8 : List Op := [
  Op.cmp 8 2 (.i 61)]

theorem b8 (prof : Profile) : Blk prof p8 0 3 o8 :=
  .cons (p8_0 _) (OpI.cmp8 (.i 61)) (by decide) <|
  .nil 3

def j6 : List Byte := [0x75, 0xe8]
theorem j6_0 : ∀ feat, Dec feat j6 0 (FV7z.mk (.jcc 5) 64 [.rel 18446744073709551592] 2) := by dec_rfl

def j7 : List Byte := [0x0f, 0x84, 0xb6, 0x00, 0x00, 0x00]
theorem j7_0 : ∀ feat, Dec feat j7 0 (FV7z.mk (.jcc 4) 64 [.rel 182] 6) := by dec_rfl

/-- The stretch at `136`. -/
def p9 : List Byte := [
  0x48, 0x8d, 0x69, 0x01, 0x48, 0x8d, 0x35, 0x10, 0x44, 0x08, 0x00, 0xba, 0x47, 0x00, 0x00, 0x00,
  0x48, 0x8d, 0x04, 0x2b, 0x48, 0x89, 0x44, 0x24, 0x08, 0x48, 0x89, 0xd8]

theorem p9_0 : ∀ feat, Dec feat p9 0 (FV7z.mk .lea 64 [gr 64 5, .mem (mg (some 1) none 1 1 0)] 4) := by dec_rfl
theorem p9_4 : ∀ feat, Dec feat p9 4 (FV7z.mk .lea 64 [gr 64 6, .mem (mrip 541712 0)] 7) := by dec_rfl
theorem p9_11 : ∀ feat, Dec feat p9 11 (FV7z.mk .mov 32 [gr 32 2, Src.opd 32 (.i 71)] 5) := by dec_rfl
theorem p9_16 : ∀ feat, Dec feat p9 16 (FV7z.mk .lea 64 [gr 64 0, .mem (mg (some 3) (some 5) 1 0 0)] 4) := by dec_rfl
theorem p9_20 : ∀ feat, Dec feat p9 20 (FV7z.mk .mov 64 [.mem (mg (some 4) none 1 8 64), gr 64 0] 5) := by dec_rfl
theorem p9_25 : ∀ feat, Dec feat p9 25 (FV7z.mk .mov 64 [gr 64 0, Src.opd 64 (.r 3)] 3) := by dec_rfl

/-- What the stretch does. -/
def o9 : List Op := [
  Op.lea 64 5 (some 1) none 1 1,
  Op.mov 64 6 (.i 7287475),
  Op.mov 32 2 (.i 71),
  Op.lea 64 0 (some 3) (some 5) 1 0,
  Op.st 64 (some 4) none 1 8 0,
  Op.mov 64 0 (.r 3)]

theorem b9 (prof : Profile) : BlkA prof p9 (0x66ee98 : Addr) 0 28 o9 :=
  .cons (p9_0 _) ((OpI.lea (.inr rfl)).at _) (by decide) <|
  .cons (p9_4 _) (OpIA.lea_rip (by decide)) (by decide) <|
  .cons (p9_11 _) ((OpI.mov (.i 71) (.inl rfl)).at _) (by decide) <|
  .cons (p9_16 _) ((OpI.lea (.inr rfl)).at _) (by decide) <|
  .cons (p9_20 _) ((OpI.st (.inr (.inr (.inr rfl)))).at _) (by decide) <|
  .cons (p9_25 _) ((OpI.mov (.r 3) (.inr rfl)).at _) (by decide) <|
  .nil 28

def j8 : List Byte := [0xeb, 0x25]
theorem j8_0 : ∀ feat, Dec feat j8 0 (FV7z.mk .jmp 64 [.rel 37] 2) := by dec_rfl

/-- The stretch at `176`. -/
def p10 : List Byte := [
  0x84, 0xc9]

theorem p10_0 : ∀ feat, Dec feat p10 0 (FV7z.mk .test 8 [gr 8 1, Src.opd 8 (.r 1)] 2) := by dec_rfl

/-- What the stretch does. -/
def o10 : List Op := [
  Op.test 8 1 (.r 1)]

theorem b10 (prof : Profile) : Blk prof p10 0 2 o10 :=
  .cons (p10_0 _) (OpI.test8 (.r 1)) (by decide) <|
  .nil 2

def j9 : List Byte := [0x74, 0x1e]
theorem j9_0 : ∀ feat, Dec feat j9 0 (FV7z.mk (.jcc 4) 64 [.rel 30] 2) := by dec_rfl

/-- The stretch at `180`. -/
def p11 : List Byte := [
  0x0f, 0xb6, 0x56, 0x01, 0x48, 0x83, 0xc6, 0x01, 0x48, 0x8d, 0x48, 0x01, 0x84, 0xd2]

theorem p11_0 : ∀ feat, Dec feat p11 0 (FV7z.mk .movzx 32 [gr 32 2, .mem (mg (some 6) none 1 1 8)] 4) := by dec_rfl
theorem p11_4 : ∀ feat, Dec feat p11 4 (FV7z.mk .add 64 [gr 64 6, Src.opd 64 (.i 1)] 4) := by dec_rfl
theorem p11_8 : ∀ feat, Dec feat p11 8 (FV7z.mk .lea 64 [gr 64 1, .mem (mg (some 0) none 1 1 0)] 4) := by dec_rfl
theorem p11_12 : ∀ feat, Dec feat p11 12 (FV7z.mk .test 8 [gr 8 2, Src.opd 8 (.r 2)] 2) := by dec_rfl

/-- What the stretch does. -/
def o11 : List Op := [
  Op.ldzx 8 2 (some 6) none 1 1,
  Op.add 64 6 (.i 1),
  Op.lea 64 1 (some 0) none 1 1,
  Op.test 8 2 (.r 2)]

theorem b11 (prof : Profile) : Blk prof p11 0 14 o11 :=
  .cons (p11_0 _) (OpI.ldzx (.inl rfl)) (by decide) <|
  .cons (p11_4 _) (OpI.add (.i 1) (.inr rfl)) (by decide) <|
  .cons (p11_8 _) (OpI.lea (.inr rfl)) (by decide) <|
  .cons (p11_12 _) (OpI.test8 (.r 2)) (by decide) <|
  .nil 14

def j10 : List Byte := [0x0f, 0x84, 0x19, 0x01, 0x00, 0x00]
theorem j10_0 : ∀ feat, Dec feat j10 0 (FV7z.mk (.jcc 4) 64 [.rel 281] 6) := by dec_rfl

/-- The stretch at `200`. -/
def p12 : List Byte := [
  0x48, 0x89, 0xc8]

theorem p12_0 : ∀ feat, Dec feat p12 0 (FV7z.mk .mov 64 [gr 64 0, Src.opd 64 (.r 1)] 3) := by dec_rfl

/-- What the stretch does. -/
def o12 : List Op := [
  Op.mov 64 0 (.r 1)]

theorem b12 (prof : Profile) : Blk prof p12 0 3 o12 :=
  .cons (p12_0 _) (OpI.mov (.r 1) (.inr rfl)) (by decide) <|
  .nil 3

/-- The stretch at `203`. -/
def p13 : List Byte := [
  0x0f, 0xb6, 0x08, 0x38, 0xd1]

theorem p13_0 : ∀ feat, Dec feat p13 0 (FV7z.mk .movzx 32 [gr 32 1, .mem (mg (some 0) none 1 0 8)] 3) := by dec_rfl
theorem p13_3 : ∀ feat, Dec feat p13 3 (FV7z.mk .cmp 8 [gr 8 1, Src.opd 8 (.r 2)] 2) := by dec_rfl

/-- What the stretch does. -/
def o13 : List Op := [
  Op.ldzx 8 1 (some 0) none 1 0,
  Op.cmp 8 1 (.r 2)]

theorem b13 (prof : Profile) : Blk prof p13 0 5 o13 :=
  .cons (p13_0 _) (OpI.ldzx (.inl rfl)) (by decide) <|
  .cons (p13_3 _) (OpI.cmp8 (.r 2)) (by decide) <|
  .nil 5

def j11 : List Byte := [0x74, 0xde]
theorem j11_0 : ∀ feat, Dec feat j11 0 (FV7z.mk (.jcc 4) 64 [.rel 18446744073709551582] 2) := by dec_rfl

/-- The stretch at `210`. -/
def p14 : List Byte := [
  0x44, 0x8b, 0x1d, 0xf7, 0x2d, 0x12, 0x00, 0x4c, 0x8d, 0x05, 0x98, 0x27, 0x12, 0x00, 0x45, 0x31,
  0xc9, 0x0f, 0x1f, 0x44, 0x00, 0x00]

theorem p14_0 : ∀ feat, Dec feat p14 0 (FV7z.mk .mov 32 [gr 32 11, .mem (mrip 1191415 32)] 7) := by dec_rfl
theorem p14_7 : ∀ feat, Dec feat p14 7 (FV7z.mk .lea 64 [gr 64 8, .mem (mrip 1189784 0)] 7) := by dec_rfl
theorem p14_14 : ∀ feat, Dec feat p14 14 (FV7z.mk .xor 32 [gr 32 9, Src.opd 32 (.r 9)] 3) := by dec_rfl
theorem p14_17 : ∀ feat, Dec feat p14 17 (FV7z.mk .nop 32 [.mem (mg (some 0) (some 0) 1 0 32)] 5) := by dec_rfl

/-- What the stretch does. -/
def o14 : List Op := [
  Op.lda 32 11 7937248,
  Op.mov 64 8 (.i 7935624),
  Op.xor 32 9 (.r 9),
  Op.nop]

theorem b14 (prof : Profile) : BlkA prof p14 (0x66eee2 : Addr) 0 22 o14 :=
  .cons (p14_0 _) (OpIA.ld_rip (.inl rfl) (by decide)) (by decide) <|
  .cons (p14_7 _) (OpIA.lea_rip (by decide)) (by decide) <|
  .cons (p14_14 _) ((OpI.xor (.r 9) (.inl rfl)).at _) (by decide) <|
  .cons (p14_17 _) ((OpI.nop).at _) (by decide) <|
  .nil 22

/-- The stretch at `232`. -/
def p15 : List Byte := [
  0x41, 0x80, 0x38, 0x00]

theorem p15_0 : ∀ feat, Dec feat p15 0 (FV7z.mk .cmp 8 [.mem (mg (some 8) none 1 0 8), .imm 8 0] 4) := by dec_rfl

/-- What the stretch does. -/
def o15 : List Op := [
  Op.cmpmi 8 (some 8) none 1 0 0]

theorem b15 (prof : Profile) : Blk prof p15 0 4 o15 :=
  .cons (p15_0 _) (OpI.cmpmi (.inl rfl)) (by decide) <|
  .nil 4

def j12 : List Byte := [0x75, 0x42]
theorem j12_0 : ∀ feat, Dec feat j12 0 (FV7z.mk (.jcc 5) 64 [.rel 66] 2) := by dec_rfl

/-- The stretch at `238`. -/
def p16 : List Byte := [
  0x4d, 0x8b, 0x50, 0x08, 0x4d, 0x85, 0xd2]

theorem p16_0 : ∀ feat, Dec feat p16 0 (FV7z.mk .mov 64 [gr 64 10, .mem (mg (some 8) none 1 8 64)] 4) := by dec_rfl
theorem p16_4 : ∀ feat, Dec feat p16 4 (FV7z.mk .test 64 [gr 64 10, Src.opd 64 (.r 10)] 3) := by dec_rfl

/-- What the stretch does. -/
def o16 : List Op := [
  Op.ld 64 10 (some 8) none 1 8,
  Op.test 64 10 (.r 10)]

theorem b16 (prof : Profile) : Blk prof p16 0 7 o16 :=
  .cons (p16_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p16_4 _) (OpI.test (.r 10) (.inr rfl)) (by decide) <|
  .nil 7

def j13 : List Byte := [0x74, 0x39]
theorem j13_0 : ∀ feat, Dec feat j13 0 (FV7z.mk (.jcc 4) 64 [.rel 57] 2) := by dec_rfl

/-- The stretch at `247`. -/
def p17 : List Byte := [
  0x41, 0x0f, 0xb6, 0x3a, 0x4c, 0x89, 0xd6, 0x48, 0x89, 0xd8, 0x89, 0xf9, 0x40, 0x84, 0xff]

theorem p17_0 : ∀ feat, Dec feat p17 0 (FV7z.mk .movzx 32 [gr 32 7, .mem (mg (some 10) none 1 0 8)] 4) := by dec_rfl
theorem p17_4 : ∀ feat, Dec feat p17 4 (FV7z.mk .mov 64 [gr 64 6, Src.opd 64 (.r 10)] 3) := by dec_rfl
theorem p17_7 : ∀ feat, Dec feat p17 7 (FV7z.mk .mov 64 [gr 64 0, Src.opd 64 (.r 3)] 3) := by dec_rfl
theorem p17_10 : ∀ feat, Dec feat p17 10 (FV7z.mk .mov 32 [gr 32 1, Src.opd 32 (.r 7)] 2) := by dec_rfl
theorem p17_12 : ∀ feat, Dec feat p17 12 (FV7z.mk .test 8 [gr 8 7, Src.opd 8 (.r 7)] 3) := by dec_rfl

/-- What the stretch does. -/
def o17 : List Op := [
  Op.ldzx 8 7 (some 10) none 1 0,
  Op.mov 64 6 (.r 10),
  Op.mov 64 0 (.r 3),
  Op.mov 32 1 (.r 7),
  Op.test 8 7 (.r 7)]

theorem b17 (prof : Profile) : Blk prof p17 0 15 o17 :=
  .cons (p17_0 _) (OpI.ldzx (.inl rfl)) (by decide) <|
  .cons (p17_4 _) (OpI.mov (.r 10) (.inr rfl)) (by decide) <|
  .cons (p17_7 _) (OpI.mov (.r 3) (.inr rfl)) (by decide) <|
  .cons (p17_10 _) (OpI.mov (.r 7) (.inl rfl)) (by decide) <|
  .cons (p17_12 _) (OpI.test8 (.r 7)) (by decide) <|
  .nil 15

def j14 : List Byte := [0x75, 0x1c]
theorem j14_0 : ∀ feat, Dec feat j14 0 (FV7z.mk (.jcc 5) 64 [.rel 28] 2) := by dec_rfl

def j15 : List Byte := [0xeb, 0x56]
theorem j15_0 : ∀ feat, Dec feat j15 0 (FV7z.mk .jmp 64 [.rel 86] 2) := by dec_rfl

/-- The stretch at `272`. -/
def p18 : List Byte := [
  0x38, 0xca]

theorem p18_0 : ∀ feat, Dec feat p18 0 (FV7z.mk .cmp 8 [gr 8 2, Src.opd 8 (.r 1)] 2) := by dec_rfl

/-- What the stretch does. -/
def o18 : List Op := [
  Op.cmp 8 2 (.r 1)]

theorem b18 (prof : Profile) : Blk prof p18 0 2 o18 :=
  .cons (p18_0 _) (OpI.cmp8 (.r 1)) (by decide) <|
  .nil 2

/-- The stretch at `276`. -/
def p19 : List Byte := [
  0x0f, 0xb6, 0x4e, 0x01, 0x48, 0x83, 0xc6, 0x01, 0x48, 0x83, 0xc0, 0x01, 0x84, 0xc9]

theorem p19_0 : ∀ feat, Dec feat p19 0 (FV7z.mk .movzx 32 [gr 32 1, .mem (mg (some 6) none 1 1 8)] 4) := by dec_rfl
theorem p19_4 : ∀ feat, Dec feat p19 4 (FV7z.mk .add 64 [gr 64 6, Src.opd 64 (.i 1)] 4) := by dec_rfl
theorem p19_8 : ∀ feat, Dec feat p19 8 (FV7z.mk .add 64 [gr 64 0, Src.opd 64 (.i 1)] 4) := by dec_rfl
theorem p19_12 : ∀ feat, Dec feat p19 12 (FV7z.mk .test 8 [gr 8 1, Src.opd 8 (.r 1)] 2) := by dec_rfl

/-- What the stretch does. -/
def o19 : List Op := [
  Op.ldzx 8 1 (some 6) none 1 1,
  Op.add 64 6 (.i 1),
  Op.add 64 0 (.i 1),
  Op.test 8 1 (.r 1)]

theorem b19 (prof : Profile) : Blk prof p19 0 14 o19 :=
  .cons (p19_0 _) (OpI.ldzx (.inl rfl)) (by decide) <|
  .cons (p19_4 _) (OpI.add (.i 1) (.inr rfl)) (by decide) <|
  .cons (p19_8 _) (OpI.add (.i 1) (.inr rfl)) (by decide) <|
  .cons (p19_12 _) (OpI.test8 (.r 1)) (by decide) <|
  .nil 14

def j16 : List Byte := [0x74, 0x3c]
theorem j16_0 : ∀ feat, Dec feat j16 0 (FV7z.mk (.jcc 4) 64 [.rel 60] 2) := by dec_rfl

/-- The stretch at `292`. -/
def p20 : List Byte := [
  0x0f, 0xb6, 0x10, 0x84, 0xd2]

theorem p20_0 : ∀ feat, Dec feat p20 0 (FV7z.mk .movzx 32 [gr 32 2, .mem (mg (some 0) none 1 0 8)] 3) := by dec_rfl
theorem p20_3 : ∀ feat, Dec feat p20 3 (FV7z.mk .test 8 [gr 8 2, Src.opd 8 (.r 2)] 2) := by dec_rfl

/-- What the stretch does. -/
def o20 : List Op := [
  Op.ldzx 8 2 (some 0) none 1 0,
  Op.test 8 2 (.r 2)]

theorem b20 (prof : Profile) : Blk prof p20 0 5 o20 :=
  .cons (p20_0 _) (OpI.ldzx (.inl rfl)) (by decide) <|
  .cons (p20_3 _) (OpI.test8 (.r 2)) (by decide) <|
  .nil 5

def j17 : List Byte := [0x75, 0xe5]
theorem j17_0 : ∀ feat, Dec feat j17 0 (FV7z.mk (.jcc 5) 64 [.rel 18446744073709551589] 2) := by dec_rfl

/-- The stretch at `299`. -/
def p21 : List Byte := [
  0x0f, 0x1f, 0x44, 0x00, 0x00]

theorem p21_0 : ∀ feat, Dec feat p21 0 (FV7z.mk .nop 32 [.mem (mg (some 0) (some 0) 1 0 32)] 5) := by dec_rfl

/-- What the stretch does. -/
def o21 : List Op := [
  Op.nop]

theorem b21 (prof : Profile) : Blk prof p21 0 5 o21 :=
  .cons (p21_0 _) (OpI.nop) (by decide) <|
  .nil 5

/-- The stretch at `304`. -/
def p22 : List Byte := [
  0x41, 0x83, 0xc1, 0x01, 0x49, 0x83, 0xc0, 0x38, 0x41, 0x83, 0xf9, 0x1a]

theorem p22_0 : ∀ feat, Dec feat p22 0 (FV7z.mk .add 32 [gr 32 9, Src.opd 32 (.i 1)] 4) := by dec_rfl
theorem p22_4 : ∀ feat, Dec feat p22 4 (FV7z.mk .add 64 [gr 64 8, Src.opd 64 (.i 56)] 4) := by dec_rfl
theorem p22_8 : ∀ feat, Dec feat p22 8 (FV7z.mk .cmp 32 [gr 32 9, Src.opd 32 (.i 26)] 4) := by dec_rfl

/-- What the stretch does. -/
def o22 : List Op := [
  Op.add 32 9 (.i 1),
  Op.add 64 8 (.i 56),
  Op.cmp 32 9 (.i 26)]

theorem b22 (prof : Profile) : Blk prof p22 0 12 o22 :=
  .cons (p22_0 _) (OpI.add (.i 1) (.inl rfl)) (by decide) <|
  .cons (p22_4 _) (OpI.add (.i 56) (.inr rfl)) (by decide) <|
  .cons (p22_8 _) (OpI.cmp (.i 26) (.inl rfl)) (by decide) <|
  .nil 12

def j18 : List Byte := [0x75, 0xaa]
theorem j18_0 : ∀ feat, Dec feat j18 0 (FV7z.mk (.jcc 5) 64 [.rel 18446744073709551530] 2) := by dec_rfl

/-- The stretch at `318`. -/
def p23 : List Byte := [
  0x4d, 0x89, 0xfd, 0x4d, 0x85, 0xed]

theorem p23_0 : ∀ feat, Dec feat p23 0 (FV7z.mk .mov 64 [gr 64 13, Src.opd 64 (.r 15)] 3) := by dec_rfl
theorem p23_3 : ∀ feat, Dec feat p23 3 (FV7z.mk .test 64 [gr 64 13, Src.opd 64 (.r 13)] 3) := by dec_rfl

/-- What the stretch does. -/
def o23 : List Op := [
  Op.mov 64 13 (.r 15),
  Op.test 64 13 (.r 13)]

theorem b23 (prof : Profile) : Blk prof p23 0 6 o23 :=
  .cons (p23_0 _) (OpI.mov (.r 15) (.inr rfl)) (by decide) <|
  .cons (p23_3 _) (OpI.test (.r 13) (.inr rfl)) (by decide) <|
  .nil 6

def j19 : List Byte := [0x0f, 0x85, 0xef, 0xfe, 0xff, 0xff]
theorem j19_0 : ∀ feat, Dec feat j19 0 (FV7z.mk (.jcc 5) 64 [.rel 18446744073709551343] 6) := by dec_rfl

/-- The stretch at `330`. -/
def p24 : List Byte := [
  0x48, 0x83, 0xc4, 0x38, 0x5b, 0x5d, 0x41, 0x5c, 0x41, 0x5d, 0x41, 0x5e, 0x41, 0x5f]

theorem p24_0 : ∀ feat, Dec feat p24 0 (FV7z.mk .add 64 [gr 64 4, Src.opd 64 (.i 56)] 4) := by dec_rfl
theorem p24_4 : ∀ feat, Dec feat p24 4 (FV7z.mk .pop 64 [gr 64 3] 1) := by dec_rfl
theorem p24_5 : ∀ feat, Dec feat p24 5 (FV7z.mk .pop 64 [gr 64 5] 1) := by dec_rfl
theorem p24_6 : ∀ feat, Dec feat p24 6 (FV7z.mk .pop 64 [gr 64 12] 2) := by dec_rfl
theorem p24_8 : ∀ feat, Dec feat p24 8 (FV7z.mk .pop 64 [gr 64 13] 2) := by dec_rfl
theorem p24_10 : ∀ feat, Dec feat p24 10 (FV7z.mk .pop 64 [gr 64 14] 2) := by dec_rfl
theorem p24_12 : ∀ feat, Dec feat p24 12 (FV7z.mk .pop 64 [gr 64 15] 2) := by dec_rfl

/-- What the stretch does. -/
def o24 : List Op := [
  Op.add 64 4 (.i 56),
  Op.pop 3,
  Op.pop 5,
  Op.pop 12,
  Op.pop 13,
  Op.pop 14,
  Op.pop 15]

theorem b24 (prof : Profile) : Blk prof p24 0 14 o24 :=
  .cons (p24_0 _) (OpI.add (.i 56) (.inr rfl)) (by decide) <|
  .cons (p24_4 _) (OpI.pop) (by decide) <|
  .cons (p24_5 _) (OpI.pop) (by decide) <|
  .cons (p24_6 _) (OpI.pop) (by decide) <|
  .cons (p24_8 _) (OpI.pop) (by decide) <|
  .cons (p24_10 _) (OpI.pop) (by decide) <|
  .cons (p24_12 _) (OpI.pop) (by decide) <|
  .nil 14

/-- The stretch at `352`. -/
def p25 : List Byte := [
  0x80, 0x38, 0x3d]

theorem p25_0 : ∀ feat, Dec feat p25 0 (FV7z.mk .cmp 8 [.mem (mg (some 0) none 1 0 8), .imm 8 61] 3) := by dec_rfl

/-- What the stretch does. -/
def o25 : List Op := [
  Op.cmpmi 8 (some 0) none 1 0 61]

theorem b25 (prof : Profile) : Blk prof p25 0 3 o25 :=
  .cons (p25_0 _) (OpI.cmpmi (.inl rfl)) (by decide) <|
  .nil 3

def j20 : List Byte := [0x75, 0xcb]
theorem j20_0 : ∀ feat, Dec feat j20 0 (FV7z.mk (.jcc 5) 64 [.rel 18446744073709551563] 2) := by dec_rfl

/-- The stretch at `481`. -/
def p26 : List Byte := [
  0x80, 0x78, 0x01, 0x3d]

theorem p26_0 : ∀ feat, Dec feat p26 0 (FV7z.mk .cmp 8 [.mem (mg (some 0) none 1 1 8), .imm 8 61] 4) := by dec_rfl

/-- What the stretch does. -/
def o26 : List Op := [
  Op.cmpmi 8 (some 0) none 1 1 61]

theorem b26 (prof : Profile) : Blk prof p26 0 4 o26 :=
  .cons (p26_0 _) (OpI.cmpmi (.inl rfl)) (by decide) <|
  .nil 4

def j21 : List Byte := [0x0f, 0x85, 0xe7, 0xfe, 0xff, 0xff]
theorem j21_0 : ∀ feat, Dec feat j21 0 (FV7z.mk (.jcc 5) 64 [.rel 18446744073709551335] 6) := by dec_rfl

/-- The stretch at `1205`. -/
def p27 : List Byte := [
  0x31, 0xc9]

theorem p27_0 : ∀ feat, Dec feat p27 0 (FV7z.mk .xor 32 [gr 32 1, Src.opd 32 (.r 1)] 2) := by dec_rfl

/-- What the stretch does. -/
def o27 : List Op := [
  Op.xor 32 1 (.r 1)]

theorem b27 (prof : Profile) : Blk prof p27 0 2 o27 :=
  .cons (p27_0 _) (OpI.xor (.r 1) (.inl rfl)) (by decide) <|
  .nil 2

def j22 : List Byte := [0xe9, 0xc4, 0xfb, 0xff, 0xff]
theorem j22_0 : ∀ feat, Dec feat j22 0 (FV7z.mk .jmp 64 [.rel 18446744073709550532] 5) := by dec_rfl

end FV7z.Tun
