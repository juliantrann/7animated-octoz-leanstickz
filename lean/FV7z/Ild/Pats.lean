import FV7z.Lemmas.SpFs
import FV7z.Lemmas.BlkOps15
import FV7z.Lemmas.BlkOps6
import FV7z.Lemmas.BlkOps2
/-!
# The stretches of straight-line code of `_nl_intern_locale_data` (PLAN.md §M, M1)

Each distinct stretch between labels and jumps (`p*`, 36 of them) and each distinct jump (`j*`, 36) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.Ild
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The stretch at `0`. -/
def p0 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0x41, 0x57, 0x41, 0x56, 0x41, 0x55, 0x41, 0x54, 0x55, 0x53, 0x48, 0x83,
  0xec, 0x08, 0x48, 0x83, 0xfa, 0x07]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem p0_4 : ∀ feat, Dec feat p0 4 (FV7z.mk .push 64 [gr 64 15] 2) := by dec_rfl
theorem p0_6 : ∀ feat, Dec feat p0 6 (FV7z.mk .push 64 [gr 64 14] 2) := by dec_rfl
theorem p0_8 : ∀ feat, Dec feat p0 8 (FV7z.mk .push 64 [gr 64 13] 2) := by dec_rfl
theorem p0_10 : ∀ feat, Dec feat p0 10 (FV7z.mk .push 64 [gr 64 12] 2) := by dec_rfl
theorem p0_12 : ∀ feat, Dec feat p0 12 (FV7z.mk .push 64 [gr 64 5] 1) := by dec_rfl
theorem p0_13 : ∀ feat, Dec feat p0 13 (FV7z.mk .push 64 [gr 64 3] 1) := by dec_rfl
theorem p0_14 : ∀ feat, Dec feat p0 14 (FV7z.mk .sub 64 [gr 64 4, Src.opd 64 (.i 8)] 4) := by dec_rfl
theorem p0_18 : ∀ feat, Dec feat p0 18 (FV7z.mk .cmp 64 [gr 64 2, Src.opd 64 (.i 7)] 4) := by dec_rfl

/-- What the stretch does. -/
def o0 : List Op := [
  Op.nop,
  Op.push 15,
  Op.push 14,
  Op.push 13,
  Op.push 12,
  Op.push 5,
  Op.push 3,
  Op.sub 64 4 (.i 8),
  Op.cmp 64 2 (.i 7)]

theorem b0 (prof : Profile) : Blk prof p0 0 22 o0 :=
  .cons (p0_0 _) (OpI.endbr) (by decide) <|
  .cons (p0_4 _) (OpI.push) (by decide) <|
  .cons (p0_6 _) (OpI.push) (by decide) <|
  .cons (p0_8 _) (OpI.push) (by decide) <|
  .cons (p0_10 _) (OpI.push) (by decide) <|
  .cons (p0_12 _) (OpI.push) (by decide) <|
  .cons (p0_13 _) (OpI.push) (by decide) <|
  .cons (p0_14 _) (OpI.sub (.i 8) (.inr rfl)) (by decide) <|
  .cons (p0_18 _) (OpI.cmp (.i 7) (.inr rfl)) (by decide) <|
  .nil 22

def j0 : List Byte := [0x0f, 0x86, 0xdc, 0x00, 0x00, 0x00]
theorem j0_0 : ∀ feat, Dec feat j0 0 (FV7z.mk (.jcc 6) 64 [.rel 220] 6) := by dec_rfl

/-- The stretch at `28`. -/
def p1 : List Byte := [
  0x49, 0x89, 0xd4, 0x89, 0xfd, 0x8b, 0x16, 0x48, 0x89, 0xf3, 0xb8, 0x17, 0x10, 0x05, 0x20, 0x83,
  0xff, 0x03]

theorem p1_0 : ∀ feat, Dec feat p1 0 (FV7z.mk .mov 64 [gr 64 12, Src.opd 64 (.r 2)] 3) := by dec_rfl
theorem p1_3 : ∀ feat, Dec feat p1 3 (FV7z.mk .mov 32 [gr 32 5, Src.opd 32 (.r 7)] 2) := by dec_rfl
theorem p1_5 : ∀ feat, Dec feat p1 5 (FV7z.mk .mov 32 [gr 32 2, .mem (mg (some 6) none 1 0 32)] 2) := by dec_rfl
theorem p1_7 : ∀ feat, Dec feat p1 7 (FV7z.mk .mov 64 [gr 64 3, Src.opd 64 (.r 6)] 3) := by dec_rfl
theorem p1_10 : ∀ feat, Dec feat p1 10 (FV7z.mk .mov 32 [gr 32 0, Src.opd 32 (.i 537202711)] 5) := by dec_rfl
theorem p1_15 : ∀ feat, Dec feat p1 15 (FV7z.mk .cmp 32 [gr 32 7, Src.opd 32 (.i 3)] 3) := by dec_rfl

/-- What the stretch does. -/
def o1 : List Op := [
  Op.mov 64 12 (.r 2),
  Op.mov 32 5 (.r 7),
  Op.ld 32 2 (some 6) none 1 0,
  Op.mov 64 3 (.r 6),
  Op.mov 32 0 (.i 537202711),
  Op.cmp 32 7 (.i 3)]

theorem b1 (prof : Profile) : Blk prof p1 0 18 o1 :=
  .cons (p1_0 _) (OpI.mov (.r 2) (.inr rfl)) (by decide) <|
  .cons (p1_3 _) (OpI.mov (.r 7) (.inl rfl)) (by decide) <|
  .cons (p1_5 _) (OpI.ld (.inl rfl)) (by decide) <|
  .cons (p1_7 _) (OpI.mov (.r 6) (.inr rfl)) (by decide) <|
  .cons (p1_10 _) (OpI.mov (.i 537202711) (.inl rfl)) (by decide) <|
  .cons (p1_15 _) (OpI.cmp (.i 3) (.inl rfl)) (by decide) <|
  .nil 18

def j1 : List Byte := [0x74, 0x11]
theorem j1_0 : ∀ feat, Dec feat j1 0 (FV7z.mk (.jcc 4) 64 [.rel 17] 2) := by dec_rfl

/-- The stretch at `48`. -/
def p2 : List Byte := [
  0x89, 0xf8, 0xb9, 0x20, 0x07, 0x09, 0x20, 0x35, 0x15, 0x11, 0x03, 0x20, 0x85, 0xff, 0x0f, 0x44,
  0xc1]

theorem p2_0 : ∀ feat, Dec feat p2 0 (FV7z.mk .mov 32 [gr 32 0, Src.opd 32 (.r 7)] 2) := by dec_rfl
theorem p2_2 : ∀ feat, Dec feat p2 2 (FV7z.mk .mov 32 [gr 32 1, Src.opd 32 (.i 537462560)] 5) := by dec_rfl
theorem p2_7 : ∀ feat, Dec feat p2 7 (FV7z.mk .xor 32 [gr 32 0, Src.opd 32 (.i 537071893)] 5) := by dec_rfl
theorem p2_12 : ∀ feat, Dec feat p2 12 (FV7z.mk .test 32 [gr 32 7, Src.opd 32 (.r 7)] 2) := by dec_rfl
theorem p2_14 : ∀ feat, Dec feat p2 14 (FV7z.mk (.cmovcc 4) 32 [gr 32 0, gr 32 1] 3) := by dec_rfl

/-- What the stretch does. -/
def o2 : List Op := [
  Op.mov 32 0 (.r 7),
  Op.mov 32 1 (.i 537462560),
  Op.xor 32 0 (.i 537071893),
  Op.test 32 7 (.r 7),
  Op.cmov32 4 0 1]

theorem b2 (prof : Profile) : Blk prof p2 0 17 o2 :=
  .cons (p2_0 _) (OpI.mov (.r 7) (.inl rfl)) (by decide) <|
  .cons (p2_2 _) (OpI.mov (.i 537462560) (.inl rfl)) (by decide) <|
  .cons (p2_7 _) (OpI.xor (.i 537071893) (.inl rfl)) (by decide) <|
  .cons (p2_12 _) (OpI.test (.r 7) (.inl rfl)) (by decide) <|
  .cons (p2_14 _) (OpI.cmov32) (by decide) <|
  .nil 17

/-- The stretch at `65`. -/
def p3 : List Byte := [
  0x39, 0xc2]

theorem p3_0 : ∀ feat, Dec feat p3 0 (FV7z.mk .cmp 32 [gr 32 2, Src.opd 32 (.r 0)] 2) := by dec_rfl

/-- What the stretch does. -/
def o3 : List Op := [
  Op.cmp 32 2 (.r 0)]

theorem b3 (prof : Profile) : Blk prof p3 0 2 o3 :=
  .cons (p3_0 _) (OpI.cmp (.r 0) (.inl rfl)) (by decide) <|
  .nil 2

def j2 : List Byte := [0x0f, 0x85, 0xaf, 0x00, 0x00, 0x00]
theorem j2_0 : ∀ feat, Dec feat j2 0 (FV7z.mk (.jcc 5) 64 [.rel 175] 6) := by dec_rfl

/-- The stretch at `73`. -/
def p4 : List Byte := [
  0x4c, 0x63, 0xf5, 0x48, 0x8d, 0x05, 0xbd, 0x9d, 0x0d, 0x00, 0x44, 0x8b, 0x6b, 0x04, 0x4e, 0x3b,
  0x2c, 0xf0]

theorem p4_0 : ∀ feat, Dec feat p4 0 (FV7z.mk .movsxd 64 [gr 64 14, gr 32 5] 3) := by dec_rfl
theorem p4_3 : ∀ feat, Dec feat p4 3 (FV7z.mk .lea 64 [gr 64 0, .mem (mrip 892349 0)] 7) := by dec_rfl
theorem p4_10 : ∀ feat, Dec feat p4 10 (FV7z.mk .mov 32 [gr 32 13, .mem (mg (some 3) none 1 4 32)] 4) := by dec_rfl
theorem p4_14 : ∀ feat, Dec feat p4 14 (FV7z.mk .cmp 64 [gr 64 13, .mem (mg (some 0) (some 14) 8 0 64)] 4) := by dec_rfl

/-- What the stretch does. -/
def o4 : List Op := [
  Op.sxr 14 5,
  Op.mov 64 0 (.i 7270432),
  Op.ld 32 13 (some 3) none 1 4,
  Op.cmpm 64 13 (some 0) (some 14) 8 0]

theorem b4 (prof : Profile) : BlkA prof p4 (0x615259 : Addr) 0 18 o4 :=
  .cons (p4_0 _) ((OpI.sxr).at _) (by decide) <|
  .cons (p4_3 _) (OpIA.lea_rip (by decide)) (by decide) <|
  .cons (p4_10 _) ((OpI.ld (.inl rfl)).at _) (by decide) <|
  .cons (p4_14 _) ((OpI.cmpm (.inr rfl)).at _) (by decide) <|
  .nil 18

def j3 : List Byte := [0x0f, 0x82, 0x97, 0x00, 0x00, 0x00]
theorem j3_0 : ∀ feat, Dec feat j3 0 (FV7z.mk (.jcc 2) 64 [.rel 151] 6) := by dec_rfl

/-- The stretch at `97`. -/
def p5 : List Byte := [
  0x4a, 0x8d, 0x04, 0xad, 0x08, 0x00, 0x00, 0x00, 0x4c, 0x39, 0xe0]

theorem p5_0 : ∀ feat, Dec feat p5 0 (FV7z.mk .lea 64 [gr 64 0, .mem (mg none (some 13) 4 8 0)] 8) := by dec_rfl
theorem p5_8 : ∀ feat, Dec feat p5 8 (FV7z.mk .cmp 64 [gr 64 0, Src.opd 64 (.r 12)] 3) := by dec_rfl

/-- What the stretch does. -/
def o5 : List Op := [
  Op.lea 64 0 none (some 13) 4 8,
  Op.cmp 64 0 (.r 12)]

theorem b5 (prof : Profile) : Blk prof p5 0 11 o5 :=
  .cons (p5_0 _) (OpI.lea (.inr rfl)) (by decide) <|
  .cons (p5_8 _) (OpI.cmp (.r 12) (.inr rfl)) (by decide) <|
  .nil 11

def j4 : List Byte := [0x0f, 0x83, 0x86, 0x00, 0x00, 0x00]
theorem j4_0 : ∀ feat, Dec feat j4 0 (FV7z.mk (.jcc 3) 64 [.rel 134] 6) := by dec_rfl

/-- The stretch at `114`. -/
def p6 : List Byte := [
  0x4a, 0x8d, 0x3c, 0xed, 0x40, 0x00, 0x00, 0x00]

theorem p6_0 : ∀ feat, Dec feat p6 0 (FV7z.mk .lea 64 [gr 64 7, .mem (mg none (some 13) 8 64 0)] 8) := by dec_rfl

/-- What the stretch does. -/
def o6 : List Op := [
  Op.lea 64 7 none (some 13) 8 64]

theorem b6 (prof : Profile) : Blk prof p6 0 8 o6 :=
  .cons (p6_0 _) (OpI.lea (.inr rfl)) (by decide) <|
  .nil 8

/-- The stretch at `127`. -/
def p7 : List Byte := [
  0x48, 0x85, 0xc0]

theorem p7_0 : ∀ feat, Dec feat p7 0 (FV7z.mk .test 64 [gr 64 0, Src.opd 64 (.r 0)] 3) := by dec_rfl

/-- What the stretch does. -/
def o7 : List Op := [
  Op.test 64 0 (.r 0)]

theorem b7 (prof : Profile) : Blk prof p7 0 3 o7 :=
  .cons (p7_0 _) (OpI.test (.r 0) (.inr rfl)) (by decide) <|
  .nil 3

def j5 : List Byte := [0x0f, 0x84, 0x80, 0x00, 0x00, 0x00]
theorem j5_0 : ∀ feat, Dec feat j5 0 (FV7z.mk (.jcc 4) 64 [.rel 128] 6) := by dec_rfl

/-- The stretch at `136`. -/
def p8 : List Byte := [
  0x48, 0x89, 0x58, 0x08, 0x4c, 0x89, 0x60, 0x10, 0x48, 0xc7, 0x40, 0x20, 0x00, 0x00, 0x00, 0x00,
  0x48, 0xc7, 0x40, 0x28, 0x00, 0x00, 0x00, 0x00, 0x48, 0xc7, 0x40, 0x30, 0x00, 0x00, 0x00, 0x00,
  0x44, 0x89, 0x68, 0x38, 0x4d, 0x85, 0xed]

theorem p8_0 : ∀ feat, Dec feat p8 0 (FV7z.mk .mov 64 [.mem (mg (some 0) none 1 8 64), gr 64 3] 4) := by dec_rfl
theorem p8_4 : ∀ feat, Dec feat p8 4 (FV7z.mk .mov 64 [.mem (mg (some 0) none 1 16 64), gr 64 12] 4) := by dec_rfl
theorem p8_8 : ∀ feat, Dec feat p8 8 (FV7z.mk .mov 64 [.mem (mg (some 0) none 1 32 64), .imm 64 0] 8) := by dec_rfl
theorem p8_16 : ∀ feat, Dec feat p8 16 (FV7z.mk .mov 64 [.mem (mg (some 0) none 1 40 64), .imm 64 0] 8) := by dec_rfl
theorem p8_24 : ∀ feat, Dec feat p8 24 (FV7z.mk .mov 64 [.mem (mg (some 0) none 1 48 64), .imm 64 0] 8) := by dec_rfl
theorem p8_32 : ∀ feat, Dec feat p8 32 (FV7z.mk .mov 32 [.mem (mg (some 0) none 1 56 32), gr 32 13] 4) := by dec_rfl
theorem p8_36 : ∀ feat, Dec feat p8 36 (FV7z.mk .test 64 [gr 64 13, Src.opd 64 (.r 13)] 3) := by dec_rfl

/-- What the stretch does. -/
def o8 : List Op := [
  Op.st 64 (some 0) none 1 8 3,
  Op.st 64 (some 0) none 1 16 12,
  Op.sti 64 (some 0) none 1 32 0,
  Op.sti 64 (some 0) none 1 40 0,
  Op.sti 64 (some 0) none 1 48 0,
  Op.st 32 (some 0) none 1 56 13,
  Op.test 64 13 (.r 13)]

theorem b8 (prof : Profile) : Blk prof p8 0 39 o8 :=
  .cons (p8_0 _) (OpI.st (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p8_4 _) (OpI.st (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p8_8 _) (OpI.sti (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p8_16 _) (OpI.sti (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p8_24 _) (OpI.sti (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p8_32 _) (OpI.st (.inr (.inr (.inl rfl)))) (by decide) <|
  .cons (p8_36 _) (OpI.test (.r 13) (.inr rfl)) (by decide) <|
  .nil 39

def j6 : List Byte := [0x74, 0x57]
theorem j6_0 : ∀ feat, Dec feat j6 0 (FV7z.mk (.jcc 4) 64 [.rel 87] 2) := by dec_rfl

/-- The stretch at `177`. -/
def p9 : List Byte := [
  0x31, 0xc9, 0x4c, 0x8d, 0x15, 0xf6, 0xb1, 0x16, 0x00, 0x41, 0x89, 0xe9, 0x48, 0x8d, 0x15, 0x0c,
  0x97, 0x0d, 0x00]

theorem p9_0 : ∀ feat, Dec feat p9 0 (FV7z.mk .xor 32 [gr 32 1, Src.opd 32 (.r 1)] 2) := by dec_rfl
theorem p9_2 : ∀ feat, Dec feat p9 2 (FV7z.mk .lea 64 [gr 64 10, .mem (mrip 1487350 0)] 7) := by dec_rfl
theorem p9_9 : ∀ feat, Dec feat p9 9 (FV7z.mk .mov 32 [gr 32 9, Src.opd 32 (.r 5)] 3) := by dec_rfl
theorem p9_12 : ∀ feat, Dec feat p9 12 (FV7z.mk .lea 64 [gr 64 2, .mem (mrip 890636 0)] 7) := by dec_rfl

/-- What the stretch does. -/
def o9 : List Op := [
  Op.xor 32 1 (.r 1),
  Op.mov 64 10 (.i 7865536),
  Op.mov 32 9 (.r 5),
  Op.mov 64 2 (.i 7268832)]

theorem b9 (prof : Profile) : BlkA prof p9 (0x6152c1 : Addr) 0 19 o9 :=
  .cons (p9_0 _) ((OpI.xor (.r 1) (.inl rfl)).at _) (by decide) <|
  .cons (p9_2 _) (OpIA.lea_rip (by decide)) (by decide) <|
  .cons (p9_9 _) ((OpI.mov (.r 5) (.inl rfl)).at _) (by decide) <|
  .cons (p9_12 _) (OpIA.lea_rip (by decide)) (by decide) <|
  .nil 19

/-- The stretch at `196`. -/
def p10 : List Byte := [
  0x8b, 0x7c, 0x8b, 0x08, 0x48, 0x89, 0xfe, 0x49, 0x39, 0xfc]

theorem p10_0 : ∀ feat, Dec feat p10 0 (FV7z.mk .mov 32 [gr 32 7, .mem (mg (some 3) (some 1) 4 8 32)] 4) := by dec_rfl
theorem p10_4 : ∀ feat, Dec feat p10 4 (FV7z.mk .mov 64 [gr 64 6, Src.opd 64 (.r 7)] 3) := by dec_rfl
theorem p10_7 : ∀ feat, Dec feat p10 7 (FV7z.mk .cmp 64 [gr 64 12, Src.opd 64 (.r 7)] 3) := by dec_rfl

/-- What the stretch does. -/
def o10 : List Op := [
  Op.ld 32 7 (some 3) (some 1) 4 8,
  Op.mov 64 6 (.r 7),
  Op.cmp 64 12 (.r 7)]

theorem b10 (prof : Profile) : Blk prof p10 0 10 o10 :=
  .cons (p10_0 _) (OpI.ld (.inl rfl)) (by decide) <|
  .cons (p10_4 _) (OpI.mov (.r 7) (.inr rfl)) (by decide) <|
  .cons (p10_7 _) (OpI.cmp (.r 7) (.inr rfl)) (by decide) <|
  .nil 10

def j7 : List Byte := [0x72, 0x20]
theorem j7_0 : ∀ feat, Dec feat j7 0 (FV7z.mk (.jcc 2) 64 [.rel 32] 2) := by dec_rfl

/-- The stretch at `208`. -/
def p11 : List Byte := [
  0x83, 0xfd, 0x0c]

theorem p11_0 : ∀ feat, Dec feat p11 0 (FV7z.mk .cmp 32 [gr 32 5, Src.opd 32 (.i 12)] 3) := by dec_rfl

/-- What the stretch does. -/
def o11 : List Op := [
  Op.cmp 32 5 (.i 12)]

theorem b11 (prof : Profile) : Blk prof p11 0 3 o11 :=
  .cons (p11_0 _) (OpI.cmp (.i 12) (.inl rfl)) (by decide) <|
  .nil 3

def j8 : List Byte := [0x0f, 0x87, 0xda, 0x00, 0x00, 0x00]
theorem j8_0 : ∀ feat, Dec feat j8 0 (FV7z.mk (.jcc 7) 64 [.rel 218] 6) := by dec_rfl

/-- The stretch at `217`. -/
def p12 : List Byte := [
  0x4e, 0x63, 0x04, 0x8a, 0x49, 0x01, 0xd0]

theorem p12_0 : ∀ feat, Dec feat p12 0 (FV7z.mk .movsxd 64 [gr 64 8, .mem (mg (some 2) (some 9) 4 0 32)] 4) := by dec_rfl
theorem p12_4 : ∀ feat, Dec feat p12 4 (FV7z.mk .add 64 [gr 64 8, Src.opd 64 (.r 2)] 3) := by dec_rfl

/-- What the stretch does. -/
def o12 : List Op := [
  Op.ldsx 8 (some 2) (some 9) 4 0,
  Op.add 64 8 (.r 2)]

theorem b12 (prof : Profile) : Blk prof p12 0 7 o12 :=
  .cons (p12_0 _) (OpI.ldsx) (by decide) <|
  .cons (p12_4 _) (OpI.add (.r 2) (.inr rfl)) (by decide) <|
  .nil 7

def j9 : List Byte := [0x3e, 0x41, 0xff, 0xe0]
theorem j9_0 : ∀ feat, Dec feat j9 0 (FV7z.mk .jmp 64 [gr 64 8] 4) := by dec_rfl

/-- The stretch at `228`. -/
def p13 : List Byte := [
  0x48, 0x83, 0xf9, 0x01]

theorem p13_0 : ∀ feat, Dec feat p13 0 (FV7z.mk .cmp 64 [gr 64 1, Src.opd 64 (.i 1)] 4) := by dec_rfl

/-- What the stretch does. -/
def o13 : List Op := [
  Op.cmp 64 1 (.i 1)]

theorem b13 (prof : Profile) : Blk prof p13 0 4 o13 :=
  .cons (p13_0 _) (OpI.cmp (.i 1) (.inr rfl)) (by decide) <|
  .nil 4

def j10 : List Byte := [0x76, 0x36]
theorem j10_0 : ∀ feat, Dec feat j10 0 (FV7z.mk (.jcc 6) 64 [.rel 54] 2) := by dec_rfl

/-- The stretch at `234`. -/
def p14 : List Byte := [
  0x66, 0x0f, 0x1f, 0x44, 0x00, 0x00]

theorem p14_0 : ∀ feat, Dec feat p14 0 (FV7z.mk .nop 16 [.mem (mg (some 0) (some 0) 1 0 16)] 6) := by dec_rfl

/-- What the stretch does. -/
def o14 : List Op := [
  Op.nop]

theorem b14 (prof : Profile) : Blk prof p14 0 6 o14 :=
  .cons (p14_0 _) (OpI.nop) (by decide) <|
  .nil 6

/-- The stretch at `240`. -/
def p15 : List Byte := [
  0x48, 0x89, 0xc7]

theorem p15_0 : ∀ feat, Dec feat p15 0 (FV7z.mk .mov 64 [gr 64 7, Src.opd 64 (.r 0)] 3) := by dec_rfl

/-- What the stretch does. -/
def o15 : List Op := [
  Op.mov 64 7 (.r 0)]

theorem b15 (prof : Profile) : Blk prof p15 0 3 o15 :=
  .cons (p15_0 _) (OpI.mov (.r 0) (.inr rfl)) (by decide) <|
  .nil 3

/-- The stretch at `248`. -/
def p16 : List Byte := [
  0x48, 0xc7, 0xc0, 0xb8, 0xff, 0xff, 0xff, 0x64, 0xc7, 0x00, 0x16, 0x00, 0x00, 0x00, 0x31, 0xc0]

theorem p16_0 : ∀ feat, Dec feat p16 0 (FV7z.mk .mov 64 [gr 64 0, Src.opd 64 (.i 18446744073709551544)] 7) := by dec_rfl
theorem p16_7 : ∀ feat, Dec feat p16 7 (FV7z.mk .mov 32 [.mem (mf (some 0) none 1 0 32), .imm 32 22] 7) := by dec_rfl
theorem p16_14 : ∀ feat, Dec feat p16 14 (FV7z.mk .xor 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl

/-- What the stretch does. -/
def o16 (fb : Addr) : List Op := [
  Op.mov 64 0 (.i 18446744073709551544),
  Op.stfi fb 32 (some 0) none 1 0 22,
  Op.xor 32 0 (.r 0)]

theorem b16 (prof : Profile) (fb : Addr) : BlkF prof p16 (0x615308 : Addr) fb 0 16 (o16 fb) :=
  .cons (p16_0 _) (((OpI.mov (.i 18446744073709551544) (.inr rfl)).at _).fs _) (by decide) <|
  .cons (p16_7 _) (OpIF.stfi (.inr (.inr (.inl rfl)))) (by decide) <|
  .cons (p16_14 _) (((OpI.xor (.r 0) (.inl rfl)).at _).fs _) (by decide) <|
  .nil 16

/-- The stretch at `264`. -/
def p17 : List Byte := [
  0x48, 0x83, 0xc4, 0x08, 0x5b, 0x5d, 0x41, 0x5c, 0x41, 0x5d, 0x41, 0x5e, 0x41, 0x5f]

theorem p17_0 : ∀ feat, Dec feat p17 0 (FV7z.mk .add 64 [gr 64 4, Src.opd 64 (.i 8)] 4) := by dec_rfl
theorem p17_4 : ∀ feat, Dec feat p17 4 (FV7z.mk .pop 64 [gr 64 3] 1) := by dec_rfl
theorem p17_5 : ∀ feat, Dec feat p17 5 (FV7z.mk .pop 64 [gr 64 5] 1) := by dec_rfl
theorem p17_6 : ∀ feat, Dec feat p17 6 (FV7z.mk .pop 64 [gr 64 12] 2) := by dec_rfl
theorem p17_8 : ∀ feat, Dec feat p17 8 (FV7z.mk .pop 64 [gr 64 13] 2) := by dec_rfl
theorem p17_10 : ∀ feat, Dec feat p17 10 (FV7z.mk .pop 64 [gr 64 14] 2) := by dec_rfl
theorem p17_12 : ∀ feat, Dec feat p17 12 (FV7z.mk .pop 64 [gr 64 15] 2) := by dec_rfl

/-- What the stretch does. -/
def o17 : List Op := [
  Op.add 64 4 (.i 8),
  Op.pop 3,
  Op.pop 5,
  Op.pop 12,
  Op.pop 13,
  Op.pop 14,
  Op.pop 15]

theorem b17 (prof : Profile) : Blk prof p17 0 14 o17 :=
  .cons (p17_0 _) (OpI.add (.i 8) (.inr rfl)) (by decide) <|
  .cons (p17_4 _) (OpI.pop) (by decide) <|
  .cons (p17_5 _) (OpI.pop) (by decide) <|
  .cons (p17_6 _) (OpI.pop) (by decide) <|
  .cons (p17_8 _) (OpI.pop) (by decide) <|
  .cons (p17_10 _) (OpI.pop) (by decide) <|
  .cons (p17_12 _) (OpI.pop) (by decide) <|
  .nil 14

/-- The stretch at `279`. -/
def p18 : List Byte := [
  0x48, 0x83, 0xf9, 0x04]

theorem p18_0 : ∀ feat, Dec feat p18 0 (FV7z.mk .cmp 64 [gr 64 1, Src.opd 64 (.i 4)] 4) := by dec_rfl

/-- What the stretch does. -/
def o18 : List Op := [
  Op.cmp 64 1 (.i 4)]

theorem b18 (prof : Profile) : Blk prof p18 0 4 o18 :=
  .cons (p18_0 _) (OpI.cmp (.i 4) (.inr rfl)) (by decide) <|
  .nil 4

def j11 : List Byte := [0x77, 0xd3]
theorem j11_0 : ∀ feat, Dec feat j11 0 (FV7z.mk (.jcc 7) 64 [.rel 18446744073709551571] 2) := by dec_rfl

/-- The stretch at `285`. -/
def p19 : List Byte := [
  0x0f, 0x1f, 0x00]

theorem p19_0 : ∀ feat, Dec feat p19 0 (FV7z.mk .nop 32 [.mem (mg (some 0) none 1 0 32)] 3) := by dec_rfl

/-- What the stretch does. -/
def o19 : List Op := [
  Op.nop]

theorem b19 (prof : Profile) : Blk prof p19 0 3 o19 :=
  .cons (p19_0 _) (OpI.nop) (by decide) <|
  .nil 3

/-- The stretch at `288`. -/
def p20 : List Byte := [
  0x4f, 0x8b, 0x04, 0xf2, 0x41, 0x83, 0x3c, 0x88, 0x05]

theorem p20_0 : ∀ feat, Dec feat p20 0 (FV7z.mk .mov 64 [gr 64 8, .mem (mg (some 10) (some 14) 8 0 64)] 4) := by dec_rfl
theorem p20_4 : ∀ feat, Dec feat p20 4 (FV7z.mk .cmp 32 [.mem (mg (some 8) (some 1) 4 0 32), .imm 32 5] 5) := by dec_rfl

/-- What the stretch does. -/
def o20 : List Op := [
  Op.ld 64 8 (some 10) (some 14) 8 0,
  Op.cmpmi 32 (some 8) (some 1) 4 0 5]

theorem b20 (prof : Profile) : Blk prof p20 0 9 o20 :=
  .cons (p20_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p20_4 _) (OpI.cmpmi (.inr rfl)) (by decide) <|
  .nil 9

def j12 : List Byte := [0x74, 0x25]
theorem j12_0 : ∀ feat, Dec feat j12 0 (FV7z.mk (.jcc 4) 64 [.rel 37] 2) := by dec_rfl

/-- The stretch at `299`. -/
def p21 : List Byte := [
  0x48, 0x01, 0xdf, 0x48, 0x89, 0x7c, 0xc8, 0x40]

theorem p21_0 : ∀ feat, Dec feat p21 0 (FV7z.mk .add 64 [gr 64 7, Src.opd 64 (.r 3)] 3) := by dec_rfl
theorem p21_3 : ∀ feat, Dec feat p21 3 (FV7z.mk .mov 64 [.mem (mg (some 0) (some 1) 8 64 64), gr 64 7] 5) := by dec_rfl

/-- What the stretch does. -/
def o21 : List Op := [
  Op.add 64 7 (.r 3),
  Op.st 64 (some 0) (some 1) 8 64 7]

theorem b21 (prof : Profile) : Blk prof p21 0 8 o21 :=
  .cons (p21_0 _) (OpI.add (.r 3) (.inr rfl)) (by decide) <|
  .cons (p21_3 _) (OpI.st (.inr (.inr (.inr rfl)))) (by decide) <|
  .nil 8

/-- The stretch at `307`. -/
def p22 : List Byte := [
  0x48, 0x83, 0xc1, 0x01, 0x49, 0x39, 0xcd]

theorem p22_0 : ∀ feat, Dec feat p22 0 (FV7z.mk .add 64 [gr 64 1, Src.opd 64 (.i 1)] 4) := by dec_rfl
theorem p22_4 : ∀ feat, Dec feat p22 4 (FV7z.mk .cmp 64 [gr 64 13, Src.opd 64 (.r 1)] 3) := by dec_rfl

/-- What the stretch does. -/
def o22 : List Op := [
  Op.add 64 1 (.i 1),
  Op.cmp 64 13 (.r 1)]

theorem b22 (prof : Profile) : Blk prof p22 0 7 o22 :=
  .cons (p22_0 _) (OpI.add (.i 1) (.inr rfl)) (by decide) <|
  .cons (p22_4 _) (OpI.cmp (.r 1) (.inr rfl)) (by decide) <|
  .nil 7

def j13 : List Byte := [0x75, 0x88]
theorem j13_0 : ∀ feat, Dec feat j13 0 (FV7z.mk (.jcc 5) 64 [.rel 18446744073709551496] 2) := by dec_rfl

def j14 : List Byte := [0xeb, 0xca]
theorem j14_0 : ∀ feat, Dec feat j14 0 (FV7z.mk .jmp 64 [.rel 18446744073709551562] 2) := by dec_rfl

/-- The stretch at `318`. -/
def p23 : List Byte := [
  0x48, 0x83, 0xf9, 0x0c]

theorem p23_0 : ∀ feat, Dec feat p23 0 (FV7z.mk .cmp 64 [gr 64 1, Src.opd 64 (.i 12)] 4) := by dec_rfl

/-- What the stretch does. -/
def o23 : List Op := [
  Op.cmp 64 1 (.i 12)]

theorem b23 (prof : Profile) : Blk prof p23 0 4 o23 :=
  .cons (p23_0 _) (OpI.cmp (.i 12) (.inr rfl)) (by decide) <|
  .nil 4

def j15 : List Byte := [0x77, 0xac]
theorem j15_0 : ∀ feat, Dec feat j15 0 (FV7z.mk (.jcc 7) 64 [.rel 18446744073709551532] 2) := by dec_rfl

def j16 : List Byte := [0x75, 0xdc]
theorem j16_0 : ∀ feat, Dec feat j16 0 (FV7z.mk (.jcc 5) 64 [.rel 18446744073709551580] 2) := by dec_rfl

/-- The stretch at `335`. -/
def p24 : List Byte := [
  0x90]

theorem p24_0 : ∀ feat, Dec feat p24 0 (FV7z.mk .nop 32 [] 1) := by dec_rfl

/-- What the stretch does. -/
def o24 : List Op := [
  Op.nop]

theorem b24 (prof : Profile) : Blk prof p24 0 1 o24 :=
  .cons (p24_0 _) (OpI.nop) (by decide) <|
  .nil 1

/-- The stretch at `336`. -/
def p25 : List Byte := [
  0x83, 0xe6, 0x03]

theorem p25_0 : ∀ feat, Dec feat p25 0 (FV7z.mk .and 32 [gr 32 6, Src.opd 32 (.i 3)] 3) := by dec_rfl

/-- What the stretch does. -/
def o25 : List Op := [
  Op.and 32 6 (.i 3)]

theorem b25 (prof : Profile) : Blk prof p25 0 3 o25 :=
  .cons (p25_0 _) (OpI.and (.i 3) (.inl rfl)) (by decide) <|
  .nil 3

def j17 : List Byte := [0x75, 0x9b]
theorem j17_0 : ∀ feat, Dec feat j17 0 (FV7z.mk (.jcc 5) 64 [.rel 18446744073709551515] 2) := by dec_rfl

/-- The stretch at `341`. -/
def p26 : List Byte := [
  0x8b, 0x34, 0x3b, 0x89, 0x74, 0xc8, 0x40]

theorem p26_0 : ∀ feat, Dec feat p26 0 (FV7z.mk .mov 32 [gr 32 6, .mem (mg (some 3) (some 7) 1 0 32)] 3) := by dec_rfl
theorem p26_3 : ∀ feat, Dec feat p26 3 (FV7z.mk .mov 32 [.mem (mg (some 0) (some 1) 8 64 32), gr 32 6] 4) := by dec_rfl

/-- What the stretch does. -/
def o26 : List Op := [
  Op.ld 32 6 (some 3) (some 7) 1 0,
  Op.st 32 (some 0) (some 1) 8 64 6]

theorem b26 (prof : Profile) : Blk prof p26 0 7 o26 :=
  .cons (p26_0 _) (OpI.ld (.inl rfl)) (by decide) <|
  .cons (p26_3 _) (OpI.st (.inr (.inr (.inl rfl)))) (by decide) <|
  .nil 7

def j18 : List Byte := [0xeb, 0xd5]
theorem j18_0 : ∀ feat, Dec feat j18 0 (FV7z.mk .jmp 64 [.rel 18446744073709551573] 2) := by dec_rfl

/-- The stretch at `350`. -/
def p27 : List Byte := [
  0x48, 0x83, 0xf9, 0x06]

theorem p27_0 : ∀ feat, Dec feat p27 0 (FV7z.mk .cmp 64 [gr 64 1, Src.opd 64 (.i 6)] 4) := by dec_rfl

/-- What the stretch does. -/
def o27 : List Op := [
  Op.cmp 64 1 (.i 6)]

theorem b27 (prof : Profile) : Blk prof p27 0 4 o27 :=
  .cons (p27_0 _) (OpI.cmp (.i 6) (.inr rfl)) (by decide) <|
  .nil 4

def j19 : List Byte := [0x76, 0xbc]
theorem j19_0 : ∀ feat, Dec feat j19 0 (FV7z.mk (.jcc 6) 64 [.rel 18446744073709551548] 2) := by dec_rfl

def j20 : List Byte := [0xeb, 0x8a]
theorem j20_0 : ∀ feat, Dec feat j20 0 (FV7z.mk .jmp 64 [.rel 18446744073709551498] 2) := by dec_rfl

/-- The stretch at `358`. -/
def p28 : List Byte := [
  0x48, 0x83, 0xf9, 0x02]

theorem p28_0 : ∀ feat, Dec feat p28 0 (FV7z.mk .cmp 64 [gr 64 1, Src.opd 64 (.i 2)] 4) := by dec_rfl

/-- What the stretch does. -/
def o28 : List Op := [
  Op.cmp 64 1 (.i 2)]

theorem b28 (prof : Profile) : Blk prof p28 0 4 o28 :=
  .cons (p28_0 _) (OpI.cmp (.i 2) (.inr rfl)) (by decide) <|
  .nil 4

def j21 : List Byte := [0x76, 0xb4]
theorem j21_0 : ∀ feat, Dec feat j21 0 (FV7z.mk (.jcc 6) 64 [.rel 18446744073709551540] 2) := by dec_rfl

def j22 : List Byte := [0xe9, 0x7f, 0xff, 0xff, 0xff]
theorem j22_0 : ∀ feat, Dec feat j22 0 (FV7z.mk .jmp 64 [.rel 18446744073709551487] 5) := by dec_rfl

/-- The stretch at `369`. -/
def p29 : List Byte := [
  0x48, 0x83, 0xf9, 0x0f]

theorem p29_0 : ∀ feat, Dec feat p29 0 (FV7z.mk .cmp 64 [gr 64 1, Src.opd 64 (.i 15)] 4) := by dec_rfl

/-- What the stretch does. -/
def o29 : List Op := [
  Op.cmp 64 1 (.i 15)]

theorem b29 (prof : Profile) : Blk prof p29 0 4 o29 :=
  .cons (p29_0 _) (OpI.cmp (.i 15) (.inr rfl)) (by decide) <|
  .nil 4

def j23 : List Byte := [0x76, 0xa9]
theorem j23_0 : ∀ feat, Dec feat j23 0 (FV7z.mk (.jcc 6) 64 [.rel 18446744073709551529] 2) := by dec_rfl

def j24 : List Byte := [0xe9, 0x74, 0xff, 0xff, 0xff]
theorem j24_0 : ∀ feat, Dec feat j24 0 (FV7z.mk .jmp 64 [.rel 18446744073709551476] 5) := by dec_rfl

/-- The stretch at `380`. -/
def p30 : List Byte := [
  0x48, 0x83, 0xf9, 0x2d]

theorem p30_0 : ∀ feat, Dec feat p30 0 (FV7z.mk .cmp 64 [gr 64 1, Src.opd 64 (.i 45)] 4) := by dec_rfl

/-- What the stretch does. -/
def o30 : List Op := [
  Op.cmp 64 1 (.i 45)]

theorem b30 (prof : Profile) : Blk prof p30 0 4 o30 :=
  .cons (p30_0 _) (OpI.cmp (.i 45) (.inr rfl)) (by decide) <|
  .nil 4

def j25 : List Byte := [0x76, 0x9e]
theorem j25_0 : ∀ feat, Dec feat j25 0 (FV7z.mk (.jcc 6) 64 [.rel 18446744073709551518] 2) := by dec_rfl

def j26 : List Byte := [0xe9, 0x69, 0xff, 0xff, 0xff]
theorem j26_0 : ∀ feat, Dec feat j26 0 (FV7z.mk .jmp 64 [.rel 18446744073709551465] 5) := by dec_rfl

/-- The stretch at `391`. -/
def p31 : List Byte := [
  0x48, 0x83, 0xf9, 0x12]

theorem p31_0 : ∀ feat, Dec feat p31 0 (FV7z.mk .cmp 64 [gr 64 1, Src.opd 64 (.i 18)] 4) := by dec_rfl

/-- What the stretch does. -/
def o31 : List Op := [
  Op.cmp 64 1 (.i 18)]

theorem b31 (prof : Profile) : Blk prof p31 0 4 o31 :=
  .cons (p31_0 _) (OpI.cmp (.i 18) (.inr rfl)) (by decide) <|
  .nil 4

def j27 : List Byte := [0x76, 0x93]
theorem j27_0 : ∀ feat, Dec feat j27 0 (FV7z.mk (.jcc 6) 64 [.rel 18446744073709551507] 2) := by dec_rfl

def j28 : List Byte := [0xe9, 0x5e, 0xff, 0xff, 0xff]
theorem j28_0 : ∀ feat, Dec feat j28 0 (FV7z.mk .jmp 64 [.rel 18446744073709551454] 5) := by dec_rfl

/-- The stretch at `402`. -/
def p32 : List Byte := [
  0x48, 0x81, 0xf9, 0x9e, 0x00, 0x00, 0x00]

theorem p32_0 : ∀ feat, Dec feat p32 0 (FV7z.mk .cmp 64 [gr 64 1, Src.opd 64 (.i 158)] 7) := by dec_rfl

/-- What the stretch does. -/
def o32 : List Op := [
  Op.cmp 64 1 (.i 158)]

theorem b32 (prof : Profile) : Blk prof p32 0 7 o32 :=
  .cons (p32_0 _) (OpI.cmp (.i 158) (.inr rfl)) (by decide) <|
  .nil 7

def j29 : List Byte := [0x0f, 0x86, 0x81, 0xff, 0xff, 0xff]
theorem j29_0 : ∀ feat, Dec feat j29 0 (FV7z.mk (.jcc 6) 64 [.rel 18446744073709551489] 6) := by dec_rfl

def j30 : List Byte := [0xe9, 0x4c, 0xff, 0xff, 0xff]
theorem j30_0 : ∀ feat, Dec feat j30 0 (FV7z.mk .jmp 64 [.rel 18446744073709551436] 5) := by dec_rfl

/-- The stretch at `420`. -/
def p33 : List Byte := [
  0x48, 0x83, 0xf9, 0x05]

theorem p33_0 : ∀ feat, Dec feat p33 0 (FV7z.mk .cmp 64 [gr 64 1, Src.opd 64 (.i 5)] 4) := by dec_rfl

/-- What the stretch does. -/
def o33 : List Op := [
  Op.cmp 64 1 (.i 5)]

theorem b33 (prof : Profile) : Blk prof p33 0 4 o33 :=
  .cons (p33_0 _) (OpI.cmp (.i 5) (.inr rfl)) (by decide) <|
  .nil 4

def j31 : List Byte := [0x0f, 0x86, 0x72, 0xff, 0xff, 0xff]
theorem j31_0 : ∀ feat, Dec feat j31 0 (FV7z.mk (.jcc 6) 64 [.rel 18446744073709551474] 6) := by dec_rfl

def j32 : List Byte := [0xe9, 0x3d, 0xff, 0xff, 0xff]
theorem j32_0 : ∀ feat, Dec feat j32 0 (FV7z.mk .jmp 64 [.rel 18446744073709551421] 5) := by dec_rfl

/-- The stretch at `435`. -/
def p34 : List Byte := [
  0x85, 0xed]

theorem p34_0 : ∀ feat, Dec feat p34 0 (FV7z.mk .test 32 [gr 32 5, Src.opd 32 (.r 5)] 2) := by dec_rfl

/-- What the stretch does. -/
def o34 : List Op := [
  Op.test 32 5 (.r 5)]

theorem b34 (prof : Profile) : Blk prof p34 0 2 o34 :=
  .cons (p34_0 _) (OpI.test (.r 5) (.inl rfl)) (by decide) <|
  .nil 2

def j33 : List Byte := [0x75, 0x0f]
theorem j33_0 : ∀ feat, Dec feat j33 0 (FV7z.mk (.jcc 5) 64 [.rel 15] 2) := by dec_rfl

/-- The stretch at `439`. -/
def p35 : List Byte := [
  0x48, 0x83, 0xf9, 0x55]

theorem p35_0 : ∀ feat, Dec feat p35 0 (FV7z.mk .cmp 64 [gr 64 1, Src.opd 64 (.i 85)] 4) := by dec_rfl

/-- What the stretch does. -/
def o35 : List Op := [
  Op.cmp 64 1 (.i 85)]

theorem b35 (prof : Profile) : Blk prof p35 0 4 o35 :=
  .cons (p35_0 _) (OpI.cmp (.i 85) (.inr rfl)) (by decide) <|
  .nil 4

def j34 : List Byte := [0x0f, 0x87, 0x6a, 0xff, 0xff, 0xff]
theorem j34_0 : ∀ feat, Dec feat j34 0 (FV7z.mk (.jcc 7) 64 [.rel 18446744073709551466] 6) := by dec_rfl

def j35 : List Byte := [0xe9, 0x5a, 0xff, 0xff, 0xff]
theorem j35_0 : ∀ feat, Dec feat j35 0 (FV7z.mk .jmp 64 [.rel 18446744073709551450] 5) := by dec_rfl

end FV7z.Ild
