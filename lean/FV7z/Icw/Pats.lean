import FV7z.Lemmas.Sp
import FV7z.Lemmas.BlkOps20
import FV7z.Lemmas.BlkOps15
import FV7z.Lemmas.BlkOps14
import FV7z.Lemmas.BlkOps3
/-!
# The stretches of straight-line code of `intel_check_word` (PLAN.md M, ctor 103)

Each distinct stretch between labels and jumps (`p*`, 51 of them) and each distinct jump (`j*`, 58) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.Icw
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The stretch at `464`. -/
def p0 : List Byte := [
  0x85, 0xf6]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .test 32 [gr 32 6, Src.opd 32 (.r 6)] 2) := by dec_rfl

/-- What the stretch does. -/
def o0 : List Op := [
  Op.test 32 6 (.r 6)]

theorem b0 (prof : Profile) : Blk prof p0 0 2 o0 :=
  .cons (p0_0 _) (OpI.test (.r 6) (.inl rfl)) (by decide) <|
  .nil 2

def j0 : List Byte := [0x0f, 0x88, 0x23, 0x01, 0x00, 0x00]
theorem j0_0 : ∀ feat, Dec feat j0 0 (FV7z.mk (.jcc 8) 64 [.rel 291] 6) := by dec_rfl

/-- The stretch at `472`. -/
def p1 : List Byte := [
  0x41, 0x55, 0x4d, 0x89, 0xcd, 0x41, 0x54, 0x55, 0x53, 0x48, 0x89, 0xd3, 0x8d, 0x97, 0x47, 0xff,
  0xff, 0xff, 0x48, 0x63, 0xc2, 0xc1, 0xfa, 0x1f, 0x48, 0x69, 0xc0, 0x56, 0x55, 0x55, 0x55, 0x48,
  0x83, 0xec, 0x08, 0x48, 0xc1, 0xe8, 0x20, 0x29, 0xd0, 0x44, 0x8d, 0x0c, 0x40, 0x85, 0xf6]

theorem p1_0 : ∀ feat, Dec feat p1 0 (FV7z.mk .push 64 [gr 64 13] 2) := by dec_rfl
theorem p1_2 : ∀ feat, Dec feat p1 2 (FV7z.mk .mov 64 [gr 64 13, Src.opd 64 (.r 9)] 3) := by dec_rfl
theorem p1_5 : ∀ feat, Dec feat p1 5 (FV7z.mk .push 64 [gr 64 12] 2) := by dec_rfl
theorem p1_7 : ∀ feat, Dec feat p1 7 (FV7z.mk .push 64 [gr 64 5] 1) := by dec_rfl
theorem p1_8 : ∀ feat, Dec feat p1 8 (FV7z.mk .push 64 [gr 64 3] 1) := by dec_rfl
theorem p1_9 : ∀ feat, Dec feat p1 9 (FV7z.mk .mov 64 [gr 64 3, Src.opd 64 (.r 2)] 3) := by dec_rfl
theorem p1_12 : ∀ feat, Dec feat p1 12 (FV7z.mk .lea 32 [gr 32 2, .mem (mg (some 7) none 1 18446744073709551431 0)] 6) := by dec_rfl
theorem p1_18 : ∀ feat, Dec feat p1 18 (FV7z.mk .movsxd 64 [gr 64 0, gr 32 2] 3) := by dec_rfl
theorem p1_21 : ∀ feat, Dec feat p1 21 (FV7z.mk .sar 32 [gr 32 2, Src.opd 8 (.i 31)] 3) := by dec_rfl
theorem p1_24 : ∀ feat, Dec feat p1 24 (FV7z.mk .imul 64 [gr 64 0, gr 64 0, .imm 64 1431655766] 7) := by dec_rfl
theorem p1_31 : ∀ feat, Dec feat p1 31 (FV7z.mk .sub 64 [gr 64 4, Src.opd 64 (.i 8)] 4) := by dec_rfl
theorem p1_35 : ∀ feat, Dec feat p1 35 (FV7z.mk .shr 64 [gr 64 0, Src.opd 8 (.i 32)] 4) := by dec_rfl
theorem p1_39 : ∀ feat, Dec feat p1 39 (FV7z.mk .sub 32 [gr 32 0, Src.opd 32 (.r 2)] 2) := by dec_rfl
theorem p1_41 : ∀ feat, Dec feat p1 41 (FV7z.mk .lea 32 [gr 32 9, .mem (mg (some 0) (some 0) 2 0 0)] 4) := by dec_rfl
theorem p1_45 : ∀ feat, Dec feat p1 45 (FV7z.mk .test 32 [gr 32 6, Src.opd 32 (.r 6)] 2) := by dec_rfl

/-- What the stretch does. -/
def o1 : List Op := [
  Op.push 13,
  Op.mov 64 13 (.r 9),
  Op.push 12,
  Op.push 5,
  Op.push 3,
  Op.mov 64 3 (.r 2),
  Op.lea 32 2 (some 7) none 1 18446744073709551431,
  Op.sxr 0 2,
  Op.sar 2 (.i 31),
  Op.imul3 0 0 1431655766,
  Op.sub 64 4 (.i 8),
  Op.shr64 0 (.i 32),
  Op.sub 32 0 (.r 2),
  Op.lea 32 9 (some 0) (some 0) 2 0,
  Op.test 32 6 (.r 6)]

theorem b1 (prof : Profile) : Blk prof p1 0 47 o1 :=
  .cons (p1_0 _) (OpI.push) (by decide) <|
  .cons (p1_2 _) (OpI.mov (.r 9) (.inr rfl)) (by decide) <|
  .cons (p1_5 _) (OpI.push) (by decide) <|
  .cons (p1_7 _) (OpI.push) (by decide) <|
  .cons (p1_8 _) (OpI.push) (by decide) <|
  .cons (p1_9 _) (OpI.mov (.r 2) (.inr rfl)) (by decide) <|
  .cons (p1_12 _) (OpI.lea (.inl rfl)) (by decide) <|
  .cons (p1_18 _) (OpI.sxr) (by decide) <|
  .cons (p1_21 _) (OpI.sar (.i 31)) (by decide) <|
  .cons (p1_24 _) (OpI.imul3) (by decide) <|
  .cons (p1_31 _) (OpI.sub (.i 8) (.inr rfl)) (by decide) <|
  .cons (p1_35 _) (OpI.shr64 (.i 32)) (by decide) <|
  .cons (p1_39 _) (OpI.sub (.r 2) (.inl rfl)) (by decide) <|
  .cons (p1_41 _) (OpI.lea (.inl rfl)) (by decide) <|
  .cons (p1_45 _) (OpI.test (.r 6) (.inl rfl)) (by decide) <|
  .nil 47

def j1 : List Byte := [0x0f, 0x84, 0xc0, 0x00, 0x00, 0x00]
theorem j1_0 : ∀ feat, Dec feat j1 0 (FV7z.mk (.jcc 4) 64 [.rel 192] 6) := by dec_rfl

/-- The stretch at `525`. -/
def p2 : List Byte := [
  0x4d, 0x89, 0xc4, 0x48, 0x89, 0xcd, 0x4c, 0x8d, 0x05, 0x16, 0x54, 0x09, 0x00]

theorem p2_0 : ∀ feat, Dec feat p2 0 (FV7z.mk .mov 64 [gr 64 12, Src.opd 64 (.r 8)] 3) := by dec_rfl
theorem p2_3 : ∀ feat, Dec feat p2 3 (FV7z.mk .mov 64 [gr 64 5, Src.opd 64 (.r 1)] 3) := by dec_rfl
theorem p2_6 : ∀ feat, Dec feat p2 6 (FV7z.mk .lea 64 [gr 64 8, .mem (mrip 611350 0)] 7) := by dec_rfl

/-- What the stretch does. -/
def o2 : List Op := [
  Op.mov 64 12 (.r 8),
  Op.mov 64 5 (.r 1),
  Op.mov 64 8 (.i 7283008)]

theorem b2 (prof : Profile) : BlkA prof p2 (0x65cd1d : Addr) 0 13 o2 :=
  .cons (p2_0 _) ((OpI.mov (.r 8) (.inr rfl)).at _) (by decide) <|
  .cons (p2_3 _) ((OpI.mov (.r 1) (.inr rfl)).at _) (by decide) <|
  .cons (p2_6 _) (OpIA.lea_rip (by decide)) (by decide) <|
  .nil 13

def j2 : List Byte := [0xeb, 0x1b]
theorem j2_0 : ∀ feat, Dec feat j2 0 (FV7z.mk .jmp 64 [.rel 27] 2) := by dec_rfl

/-- The stretch at `544`. -/
def p3 : List Byte := [
  0xc6, 0x45, 0x00, 0x01, 0x41, 0x83, 0xf9, 0x09]

theorem p3_0 : ∀ feat, Dec feat p3 0 (FV7z.mk .mov 8 [.mem (mg (some 5) none 1 0 8), .imm 8 1] 4) := by dec_rfl
theorem p3_4 : ∀ feat, Dec feat p3 4 (FV7z.mk .cmp 32 [gr 32 9, Src.opd 32 (.i 9)] 4) := by dec_rfl

/-- What the stretch does. -/
def o3 : List Op := [
  Op.sti 8 (some 5) none 1 0 1,
  Op.cmp 32 9 (.i 9)]

theorem b3 (prof : Profile) : Blk prof p3 0 8 o3 :=
  .cons (p3_0 _) (OpI.sti (.inl rfl)) (by decide) <|
  .cons (p3_4 _) (OpI.cmp (.i 9) (.inl rfl)) (by decide) <|
  .nil 8

def j3 : List Byte := [0x0f, 0x84, 0x9f, 0x00, 0x00, 0x00]
theorem j3_0 : ∀ feat, Dec feat j3 0 (FV7z.mk (.jcc 4) 64 [.rel 159] 6) := by dec_rfl

/-- The stretch at `558`. -/
def p4 : List Byte := [
  0xc1, 0xee, 0x08]

theorem p4_0 : ∀ feat, Dec feat p4 0 (FV7z.mk .shr 32 [gr 32 6, Src.opd 8 (.i 8)] 3) := by dec_rfl

/-- What the stretch does. -/
def o4 : List Op := [
  Op.shr 6 (.i 8)]

theorem b4 (prof : Profile) : Blk prof p4 0 3 o4 :=
  .cons (p4_0 _) (OpI.shr (.i 8)) (by decide) <|
  .nil 3

def j4 : List Byte := [0x0f, 0x84, 0x96, 0x00, 0x00, 0x00]
theorem j4_0 : ∀ feat, Dec feat j4 0 (FV7z.mk (.jcc 4) 64 [.rel 150] 6) := by dec_rfl

/-- The stretch at `567`. -/
def p5 : List Byte := [
  0x40, 0x0f, 0xb6, 0xc6, 0x40, 0x80, 0xfe, 0x40]

theorem p5_0 : ∀ feat, Dec feat p5 0 (FV7z.mk .movzx 32 [gr 32 0, gr 8 6] 4) := by dec_rfl
theorem p5_4 : ∀ feat, Dec feat p5 4 (FV7z.mk .cmp 8 [gr 8 6, Src.opd 8 (.i 64)] 4) := by dec_rfl

/-- What the stretch does. -/
def o5 : List Op := [
  Op.zxr 0 6,
  Op.cmp 8 6 (.i 64)]

theorem b5 (prof : Profile) : Blk prof p5 0 8 o5 :=
  .cons (p5_0 _) (OpI.zxr) (by decide) <|
  .cons (p5_4 _) (OpI.cmp8 (.i 64)) (by decide) <|
  .nil 8

def j5 : List Byte := [0x74, 0xdf]
theorem j5_0 : ∀ feat, Dec feat j5 0 (FV7z.mk (.jcc 4) 64 [.rel 18446744073709551583] 2) := by dec_rfl

/-- The stretch at `577`. -/
def p6 : List Byte := [
  0x3d, 0xff, 0x00, 0x00, 0x00]

theorem p6_0 : ∀ feat, Dec feat p6 0 (FV7z.mk .cmp 32 [gr 32 0, Src.opd 32 (.i 255)] 5) := by dec_rfl

/-- What the stretch does. -/
def o6 : List Op := [
  Op.cmp 32 0 (.i 255)]

theorem b6 (prof : Profile) : Blk prof p6 0 5 o6 :=
  .cons (p6_0 _) (OpI.cmp (.i 255) (.inl rfl)) (by decide) <|
  .nil 5

def j6 : List Byte := [0x0f, 0x84, 0xb2, 0x00, 0x00, 0x00]
theorem j6_0 : ∀ feat, Dec feat j6 0 (FV7z.mk (.jcc 4) 64 [.rel 178] 6) := by dec_rfl

/-- The stretch at `588`. -/
def p7 : List Byte := [
  0x83, 0xf8, 0x49]

theorem p7_0 : ∀ feat, Dec feat p7 0 (FV7z.mk .cmp 32 [gr 32 0, Src.opd 32 (.i 73)] 3) := by dec_rfl

/-- What the stretch does. -/
def o7 : List Op := [
  Op.cmp 32 0 (.i 73)]

theorem b7 (prof : Profile) : Blk prof p7 0 3 o7 :=
  .cons (p7_0 _) (OpI.cmp (.i 73) (.inl rfl)) (by decide) <|
  .nil 3

def j7 : List Byte := [0x75, 0x25]
theorem j7_0 : ∀ feat, Dec feat j7 0 (FV7z.mk (.jcc 5) 64 [.rel 37] 2) := by dec_rfl

/-- The stretch at `593`. -/
def p8 : List Byte := [
  0x41, 0x83, 0xf9, 0x09]

theorem p8_0 : ∀ feat, Dec feat p8 0 (FV7z.mk .cmp 32 [gr 32 9, Src.opd 32 (.i 9)] 4) := by dec_rfl

/-- What the stretch does. -/
def o8 : List Op := [
  Op.cmp 32 9 (.i 9)]

theorem b8 (prof : Profile) : Blk prof p8 0 4 o8 :=
  .cons (p8_0 _) (OpI.cmp (.i 9) (.inl rfl)) (by decide) <|
  .nil 4

def j8 : List Byte := [0x75, 0x1f]
theorem j8_0 : ∀ feat, Dec feat j8 0 (FV7z.mk (.jcc 5) 64 [.rel 31] 2) := by dec_rfl

/-- The stretch at `599`. -/
def p9 : List Byte := [
  0x41, 0x83, 0x3c, 0x24, 0x0f]

theorem p9_0 : ∀ feat, Dec feat p9 0 (FV7z.mk .cmp 32 [.mem (mg (some 12) none 1 0 32), .imm 32 15] 5) := by dec_rfl

/-- What the stretch does. -/
def o9 : List Op := [
  Op.cmpmi 32 (some 12) none 1 0 15]

theorem b9 (prof : Profile) : Blk prof p9 0 5 o9 :=
  .cons (p9_0 _) (OpI.cmpmi (.inr rfl)) (by decide) <|
  .nil 5

def j9 : List Byte := [0x0f, 0x85, 0x8e, 0x00, 0x00, 0x00]
theorem j9_0 : ∀ feat, Dec feat j9 0 (FV7z.mk (.jcc 5) 64 [.rel 142] 6) := by dec_rfl

/-- The stretch at `610`. -/
def p10 : List Byte := [
  0x41, 0x83, 0x7d, 0x00, 0x06]

theorem p10_0 : ∀ feat, Dec feat p10 0 (FV7z.mk .cmp 32 [.mem (mg (some 13) none 1 0 32), .imm 32 6] 5) := by dec_rfl

/-- What the stretch does. -/
def o10 : List Op := [
  Op.cmpmi 32 (some 13) none 1 0 6]

theorem b10 (prof : Profile) : Blk prof p10 0 5 o10 :=
  .cons (p10_0 _) (OpI.cmpmi (.inr rfl)) (by decide) <|
  .nil 5

def j10 : List Byte := [0x0f, 0x85, 0x83, 0x00, 0x00, 0x00]
theorem j10_0 : ∀ feat, Dec feat j10 0 (FV7z.mk (.jcc 5) 64 [.rel 131] 6) := by dec_rfl

/-- The stretch at `621`. -/
def p11 : List Byte := [
  0x83, 0xef, 0x03, 0x41, 0xb9, 0x06, 0x00, 0x00, 0x00]

theorem p11_0 : ∀ feat, Dec feat p11 0 (FV7z.mk .sub 32 [gr 32 7, Src.opd 32 (.i 3)] 3) := by dec_rfl
theorem p11_3 : ∀ feat, Dec feat p11 3 (FV7z.mk .mov 32 [gr 32 9, Src.opd 32 (.i 6)] 6) := by dec_rfl

/-- What the stretch does. -/
def o11 : List Op := [
  Op.sub 32 7 (.i 3),
  Op.mov 32 9 (.i 6)]

theorem b11 (prof : Profile) : Blk prof p11 0 9 o11 :=
  .cons (p11_0 _) (OpI.sub (.i 3) (.inl rfl)) (by decide) <|
  .cons (p11_3 _) (OpI.mov (.i 6) (.inl rfl)) (by decide) <|
  .nil 9

/-- The stretch at `630`. -/
def p12 : List Byte := [
  0x89, 0xf1, 0xba, 0x44, 0x00, 0x00, 0x00, 0x45, 0x31, 0xd2]

theorem p12_0 : ∀ feat, Dec feat p12 0 (FV7z.mk .mov 32 [gr 32 1, Src.opd 32 (.r 6)] 2) := by dec_rfl
theorem p12_2 : ∀ feat, Dec feat p12 2 (FV7z.mk .mov 32 [gr 32 2, Src.opd 32 (.i 68)] 5) := by dec_rfl
theorem p12_7 : ∀ feat, Dec feat p12 7 (FV7z.mk .xor 32 [gr 32 10, Src.opd 32 (.r 10)] 3) := by dec_rfl

/-- What the stretch does. -/
def o12 : List Op := [
  Op.mov 32 1 (.r 6),
  Op.mov 32 2 (.i 68),
  Op.xor 32 10 (.r 10)]

theorem b12 (prof : Profile) : Blk prof p12 0 10 o12 :=
  .cons (p12_0 _) (OpI.mov (.r 6) (.inl rfl)) (by decide) <|
  .cons (p12_2 _) (OpI.mov (.i 68) (.inl rfl)) (by decide) <|
  .cons (p12_7 _) (OpI.xor (.r 10) (.inl rfl)) (by decide) <|
  .nil 10

/-- The stretch at `640`. -/
def p13 : List Byte := [
  0x49, 0x8d, 0x04, 0x12, 0x48, 0xd1, 0xe8, 0x4d, 0x8d, 0x1c, 0xc0, 0x41, 0x3a, 0x0b]

theorem p13_0 : ∀ feat, Dec feat p13 0 (FV7z.mk .lea 64 [gr 64 0, .mem (mg (some 10) (some 2) 1 0 0)] 4) := by dec_rfl
theorem p13_4 : ∀ feat, Dec feat p13 4 (FV7z.mk .shr 64 [gr 64 0, Src.opd 8 (.i 1)] 3) := by dec_rfl
theorem p13_7 : ∀ feat, Dec feat p13 7 (FV7z.mk .lea 64 [gr 64 11, .mem (mg (some 8) (some 0) 8 0 0)] 4) := by dec_rfl
theorem p13_11 : ∀ feat, Dec feat p13 11 (FV7z.mk .cmp 8 [gr 8 1, .mem (mg (some 11) none 1 0 8)] 3) := by dec_rfl

/-- What the stretch does. -/
def o13 : List Op := [
  Op.lea 64 0 (some 10) (some 2) 1 0,
  Op.shr64 0 (.i 1),
  Op.lea 64 11 (some 8) (some 0) 8 0,
  Op.cmpm 8 1 (some 11) none 1 0]

theorem b13 (prof : Profile) : Blk prof p13 0 14 o13 :=
  .cons (p13_0 _) (OpI.lea (.inr rfl)) (by decide) <|
  .cons (p13_4 _) (OpI.shr64 (.i 1)) (by decide) <|
  .cons (p13_7 _) (OpI.lea (.inr rfl)) (by decide) <|
  .cons (p13_11 _) (OpI.cmpm8) (by decide) <|
  .nil 14

def j11 : List Byte := [0x74, 0x1a]
theorem j11_0 : ∀ feat, Dec feat j11 0 (FV7z.mk (.jcc 4) 64 [.rel 26] 2) := by dec_rfl

def j12 : List Byte := [0x73, 0x4e]
theorem j12_0 : ∀ feat, Dec feat j12 0 (FV7z.mk (.jcc 3) 64 [.rel 78] 2) := by dec_rfl

/-- The stretch at `658`. -/
def p14 : List Byte := [
  0x4c, 0x39, 0xd0]

theorem p14_0 : ∀ feat, Dec feat p14 0 (FV7z.mk .cmp 64 [gr 64 0, Src.opd 64 (.r 10)] 3) := by dec_rfl

/-- What the stretch does. -/
def o14 : List Op := [
  Op.cmp 64 0 (.r 10)]

theorem b14 (prof : Profile) : Blk prof p14 0 3 o14 :=
  .cons (p14_0 _) (OpI.cmp (.r 10) (.inr rfl)) (by decide) <|
  .nil 3

def j13 : List Byte := [0x76, 0x97]
theorem j13_0 : ∀ feat, Dec feat j13 0 (FV7z.mk (.jcc 6) 64 [.rel 18446744073709551511] 2) := by dec_rfl

/-- The stretch at `663`. -/
def p15 : List Byte := [
  0x48, 0x89, 0xc2, 0x49, 0x8d, 0x04, 0x12, 0x48, 0xd1, 0xe8, 0x4d, 0x8d, 0x1c, 0xc0, 0x41, 0x3a,
  0x0b]

theorem p15_0 : ∀ feat, Dec feat p15 0 (FV7z.mk .mov 64 [gr 64 2, Src.opd 64 (.r 0)] 3) := by dec_rfl
theorem p15_3 : ∀ feat, Dec feat p15 3 (FV7z.mk .lea 64 [gr 64 0, .mem (mg (some 10) (some 2) 1 0 0)] 4) := by dec_rfl
theorem p15_7 : ∀ feat, Dec feat p15 7 (FV7z.mk .shr 64 [gr 64 0, Src.opd 8 (.i 1)] 3) := by dec_rfl
theorem p15_10 : ∀ feat, Dec feat p15 10 (FV7z.mk .lea 64 [gr 64 11, .mem (mg (some 8) (some 0) 8 0 0)] 4) := by dec_rfl
theorem p15_14 : ∀ feat, Dec feat p15 14 (FV7z.mk .cmp 8 [gr 8 1, .mem (mg (some 11) none 1 0 8)] 3) := by dec_rfl

/-- What the stretch does. -/
def o15 : List Op := [
  Op.mov 64 2 (.r 0),
  Op.lea 64 0 (some 10) (some 2) 1 0,
  Op.shr64 0 (.i 1),
  Op.lea 64 11 (some 8) (some 0) 8 0,
  Op.cmpm 8 1 (some 11) none 1 0]

theorem b15 (prof : Profile) : Blk prof p15 0 17 o15 :=
  .cons (p15_0 _) (OpI.mov (.r 0) (.inr rfl)) (by decide) <|
  .cons (p15_3 _) (OpI.lea (.inr rfl)) (by decide) <|
  .cons (p15_7 _) (OpI.shr64 (.i 1)) (by decide) <|
  .cons (p15_10 _) (OpI.lea (.inr rfl)) (by decide) <|
  .cons (p15_14 _) (OpI.cmpm8) (by decide) <|
  .nil 17

def j14 : List Byte := [0x75, 0xe6]
theorem j14_0 : ∀ feat, Dec feat j14 0 (FV7z.mk (.jcc 5) 64 [.rel 18446744073709551590] 2) := by dec_rfl

/-- The stretch at `682`. -/
def p16 : List Byte := [
  0x41, 0x0f, 0xb6, 0x53, 0x03, 0x44, 0x39, 0xca]

theorem p16_0 : ∀ feat, Dec feat p16 0 (FV7z.mk .movzx 32 [gr 32 2, .mem (mg (some 11) none 1 3 8)] 5) := by dec_rfl
theorem p16_5 : ∀ feat, Dec feat p16 5 (FV7z.mk .cmp 32 [gr 32 2, Src.opd 32 (.r 9)] 3) := by dec_rfl

/-- What the stretch does. -/
def o16 : List Op := [
  Op.ldzx 8 2 (some 11) none 1 3,
  Op.cmp 32 2 (.r 9)]

theorem b16 (prof : Profile) : Blk prof p16 0 8 o16 :=
  .cons (p16_0 _) (OpI.ldzx (.inl rfl)) (by decide) <|
  .cons (p16_5 _) (OpI.cmp (.r 9) (.inl rfl)) (by decide) <|
  .nil 8

def j15 : List Byte := [0x0f, 0x84, 0xe9, 0x00, 0x00, 0x00]
theorem j15_0 : ∀ feat, Dec feat j15 0 (FV7z.mk (.jcc 4) 64 [.rel 233] 6) := by dec_rfl

/-- The stretch at `696`. -/
def p17 : List Byte := [
  0x80, 0xfa, 0x06]

theorem p17_0 : ∀ feat, Dec feat p17 0 (FV7z.mk .cmp 8 [gr 8 2, Src.opd 8 (.i 6)] 3) := by dec_rfl

/-- What the stretch does. -/
def o17 : List Op := [
  Op.cmp 8 2 (.i 6)]

theorem b17 (prof : Profile) : Blk prof p17 0 3 o17 :=
  .cons (p17_0 _) (OpI.cmp8 (.i 6)) (by decide) <|
  .nil 3

def j16 : List Byte := [0x0f, 0x85, 0x6d, 0xff, 0xff, 0xff]
theorem j16_0 : ∀ feat, Dec feat j16 0 (FV7z.mk (.jcc 5) 64 [.rel 18446744073709551469] 6) := by dec_rfl

/-- The stretch at `705`. -/
def p18 : List Byte := [
  0xc1, 0xee, 0x08, 0xc6, 0x03, 0x01]

theorem p18_0 : ∀ feat, Dec feat p18 0 (FV7z.mk .shr 32 [gr 32 6, Src.opd 8 (.i 8)] 3) := by dec_rfl
theorem p18_3 : ∀ feat, Dec feat p18 3 (FV7z.mk .mov 8 [.mem (mg (some 3) none 1 0 8), .imm 8 1] 3) := by dec_rfl

/-- What the stretch does. -/
def o18 : List Op := [
  Op.shr 6 (.i 8),
  Op.sti 8 (some 3) none 1 0 1]

theorem b18 (prof : Profile) : Blk prof p18 0 6 o18 :=
  .cons (p18_0 _) (OpI.shr (.i 8)) (by decide) <|
  .cons (p18_3 _) (OpI.sti (.inl rfl)) (by decide) <|
  .nil 6

def j17 : List Byte := [0x0f, 0x85, 0x6a, 0xff, 0xff, 0xff]
theorem j17_0 : ∀ feat, Dec feat j17 0 (FV7z.mk (.jcc 5) 64 [.rel 18446744073709551466] 6) := by dec_rfl

/-- The stretch at `717`. -/
def p19 : List Byte := [
  0x31, 0xc0]

theorem p19_0 : ∀ feat, Dec feat p19 0 (FV7z.mk .xor 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl

/-- What the stretch does. -/
def o19 : List Op := [
  Op.xor 32 0 (.r 0)]

theorem b19 (prof : Profile) : Blk prof p19 0 2 o19 :=
  .cons (p19_0 _) (OpI.xor (.r 0) (.inl rfl)) (by decide) <|
  .nil 2

/-- The stretch at `719`. -/
def p20 : List Byte := [
  0x48, 0x83, 0xc4, 0x08, 0x5b, 0x5d, 0x41, 0x5c, 0x41, 0x5d]

theorem p20_0 : ∀ feat, Dec feat p20 0 (FV7z.mk .add 64 [gr 64 4, Src.opd 64 (.i 8)] 4) := by dec_rfl
theorem p20_4 : ∀ feat, Dec feat p20 4 (FV7z.mk .pop 64 [gr 64 3] 1) := by dec_rfl
theorem p20_5 : ∀ feat, Dec feat p20 5 (FV7z.mk .pop 64 [gr 64 5] 1) := by dec_rfl
theorem p20_6 : ∀ feat, Dec feat p20 6 (FV7z.mk .pop 64 [gr 64 12] 2) := by dec_rfl
theorem p20_8 : ∀ feat, Dec feat p20 8 (FV7z.mk .pop 64 [gr 64 13] 2) := by dec_rfl

/-- What the stretch does. -/
def o20 : List Op := [
  Op.add 64 4 (.i 8),
  Op.pop 3,
  Op.pop 5,
  Op.pop 12,
  Op.pop 13]

theorem b20 (prof : Profile) : Blk prof p20 0 10 o20 :=
  .cons (p20_0 _) (OpI.add (.i 8) (.inr rfl)) (by decide) <|
  .cons (p20_4 _) (OpI.pop) (by decide) <|
  .cons (p20_5 _) (OpI.pop) (by decide) <|
  .cons (p20_6 _) (OpI.pop) (by decide) <|
  .cons (p20_8 _) (OpI.pop) (by decide) <|
  .nil 10

/-- The stretch at `736`. -/
def p21 : List Byte := [
  0x4c, 0x8d, 0x50, 0x01, 0x49, 0x39, 0xd2]

theorem p21_0 : ∀ feat, Dec feat p21 0 (FV7z.mk .lea 64 [gr 64 10, .mem (mg (some 0) none 1 1 0)] 4) := by dec_rfl
theorem p21_4 : ∀ feat, Dec feat p21 4 (FV7z.mk .cmp 64 [gr 64 10, Src.opd 64 (.r 2)] 3) := by dec_rfl

/-- What the stretch does. -/
def o21 : List Op := [
  Op.lea 64 10 (some 0) none 1 1,
  Op.cmp 64 10 (.r 2)]

theorem b21 (prof : Profile) : Blk prof p21 0 7 o21 :=
  .cons (p21_0 _) (OpI.lea (.inr rfl)) (by decide) <|
  .cons (p21_4 _) (OpI.cmp (.r 2) (.inr rfl)) (by decide) <|
  .nil 7

def j18 : List Byte := [0x72, 0x97]
theorem j18_0 : ∀ feat, Dec feat j18 0 (FV7z.mk (.jcc 2) 64 [.rel 18446744073709551511] 2) := by dec_rfl

def j19 : List Byte := [0xe9, 0x40, 0xff, 0xff, 0xff]
theorem j19_0 : ∀ feat, Dec feat j19 0 (FV7z.mk .jmp 64 [.rel 18446744073709551424] 5) := by dec_rfl

/-- The stretch at `752`. -/
def p22 : List Byte := [
  0x41, 0xb9, 0x09, 0x00, 0x00, 0x00]

theorem p22_0 : ∀ feat, Dec feat p22 0 (FV7z.mk .mov 32 [gr 32 9, Src.opd 32 (.i 9)] 6) := by dec_rfl

/-- What the stretch does. -/
def o22 : List Op := [
  Op.mov 32 9 (.i 9)]

theorem b22 (prof : Profile) : Blk prof p22 0 6 o22 :=
  .cons (p22_0 _) (OpI.mov (.i 9) (.inl rfl)) (by decide) <|
  .nil 6

def j20 : List Byte := [0xe9, 0x7b, 0xff, 0xff, 0xff]
theorem j20_0 : ∀ feat, Dec feat j20 0 (FV7z.mk .jmp 64 [.rel 18446744073709551483] 5) := by dec_rfl

/-- The stretch at `766`. -/
def p23 : List Byte := [
  0xb8, 0x04, 0x00, 0x00, 0x00, 0x31, 0xc9]

theorem p23_0 : ∀ feat, Dec feat p23 0 (FV7z.mk .mov 32 [gr 32 0, Src.opd 32 (.i 4)] 5) := by dec_rfl
theorem p23_5 : ∀ feat, Dec feat p23 5 (FV7z.mk .xor 32 [gr 32 1, Src.opd 32 (.r 1)] 2) := by dec_rfl

/-- What the stretch does. -/
def o23 : List Op := [
  Op.mov 32 0 (.i 4),
  Op.xor 32 1 (.r 1)]

theorem b23 (prof : Profile) : Blk prof p23 0 7 o23 :=
  .cons (p23_0 _) (OpI.mov (.i 4) (.inl rfl)) (by decide) <|
  .cons (p23_5 _) (OpI.xor (.r 1) (.inl rfl)) (by decide) <|
  .nil 7

/-- The stretch at `775`. -/
def p24 : List Byte := [
  0x89, 0xc2, 0x83, 0xe2, 0x1f]

theorem p24_0 : ∀ feat, Dec feat p24 0 (FV7z.mk .mov 32 [gr 32 2, Src.opd 32 (.r 0)] 2) := by dec_rfl
theorem p24_2 : ∀ feat, Dec feat p24 2 (FV7z.mk .and 32 [gr 32 2, Src.opd 32 (.i 31)] 3) := by dec_rfl

/-- What the stretch does. -/
def o24 : List Op := [
  Op.mov 32 2 (.r 0),
  Op.and 32 2 (.i 31)]

theorem b24 (prof : Profile) : Blk prof p24 0 5 o24 :=
  .cons (p24_0 _) (OpI.mov (.r 0) (.inl rfl)) (by decide) <|
  .cons (p24_2 _) (OpI.and (.i 31) (.inl rfl)) (by decide) <|
  .nil 5

def j21 : List Byte := [0x74, 0xbf]
theorem j21_0 : ∀ feat, Dec feat j21 0 (FV7z.mk (.jcc 4) 64 [.rel 18446744073709551551] 2) := by dec_rfl

/-- The stretch at `782`. -/
def p25 : List Byte := [
  0x31, 0xf6, 0x41, 0x83, 0xf9, 0x03]

theorem p25_0 : ∀ feat, Dec feat p25 0 (FV7z.mk .xor 32 [gr 32 6, Src.opd 32 (.r 6)] 2) := by dec_rfl
theorem p25_2 : ∀ feat, Dec feat p25 2 (FV7z.mk .cmp 32 [gr 32 9, Src.opd 32 (.i 3)] 4) := by dec_rfl

/-- What the stretch does. -/
def o25 : List Op := [
  Op.xor 32 6 (.r 6),
  Op.cmp 32 9 (.i 3)]

theorem b25 (prof : Profile) : Blk prof p25 0 6 o25 :=
  .cons (p25_0 _) (OpI.xor (.r 6) (.inl rfl)) (by decide) <|
  .cons (p25_2 _) (OpI.cmp (.i 3) (.inl rfl)) (by decide) <|
  .nil 6

def j22 : List Byte := [0x0f, 0x84, 0xae, 0x01, 0x00, 0x00]
theorem j22_0 : ∀ feat, Dec feat j22 0 (FV7z.mk (.jcc 4) 64 [.rel 430] 6) := by dec_rfl

/-- The stretch at `794`. -/
def p26 : List Byte := [
  0x45, 0x85, 0xc9]

theorem p26_0 : ∀ feat, Dec feat p26 0 (FV7z.mk .test 32 [gr 32 9, Src.opd 32 (.r 9)] 3) := by dec_rfl

/-- What the stretch does. -/
def o26 : List Op := [
  Op.test 32 9 (.r 9)]

theorem b26 (prof : Profile) : Blk prof p26 0 3 o26 :=
  .cons (p26_0 _) (OpI.test (.r 9) (.inl rfl)) (by decide) <|
  .nil 3

def j23 : List Byte := [0x0f, 0x84, 0x5d, 0x01, 0x00, 0x00]
theorem j23_0 : ∀ feat, Dec feat j23 0 (FV7z.mk (.jcc 4) 64 [.rel 349] 6) := by dec_rfl

/-- The stretch at `803`. -/
def p27 : List Byte := [
  0x41, 0xba, 0x04, 0x00, 0x00, 0x00]

theorem p27_0 : ∀ feat, Dec feat p27 0 (FV7z.mk .mov 32 [gr 32 10, Src.opd 32 (.i 4)] 6) := by dec_rfl

/-- What the stretch does. -/
def o27 : List Op := [
  Op.mov 32 10 (.i 4)]

theorem b27 (prof : Profile) : Blk prof p27 0 6 o27 :=
  .cons (p27_0 _) (OpI.mov (.i 4) (.inl rfl)) (by decide) <|
  .nil 6

/-- The stretch at `816`. -/
def p28 : List Byte := [
  0x45, 0x84, 0xc0]

theorem p28_0 : ∀ feat, Dec feat p28 0 (FV7z.mk .test 8 [gr 8 8, Src.opd 8 (.r 8)] 3) := by dec_rfl

/-- What the stretch does. -/
def o28 : List Op := [
  Op.test 8 8 (.r 8)]

theorem b28 (prof : Profile) : Blk prof p28 0 3 o28 :=
  .cons (p28_0 _) (OpI.test8 (.r 8)) (by decide) <|
  .nil 3

def j24 : List Byte := [0x74, 0x23]
theorem j24_0 : ∀ feat, Dec feat j24 0 (FV7z.mk (.jcc 4) 64 [.rel 35] 2) := by dec_rfl

/-- The stretch at `821`. -/
def p29 : List Byte := [
  0x83, 0xc6, 0x01, 0x44, 0x89, 0xd0, 0x89, 0xf1]

theorem p29_0 : ∀ feat, Dec feat p29 0 (FV7z.mk .add 32 [gr 32 6, Src.opd 32 (.i 1)] 3) := by dec_rfl
theorem p29_3 : ∀ feat, Dec feat p29 3 (FV7z.mk .mov 32 [gr 32 0, Src.opd 32 (.r 10)] 3) := by dec_rfl
theorem p29_6 : ∀ feat, Dec feat p29 6 (FV7z.mk .mov 32 [gr 32 1, Src.opd 32 (.r 6)] 2) := by dec_rfl

/-- What the stretch does. -/
def o29 : List Op := [
  Op.add 32 6 (.i 1),
  Op.mov 32 0 (.r 10),
  Op.mov 32 1 (.r 6)]

theorem b29 (prof : Profile) : Blk prof p29 0 8 o29 :=
  .cons (p29_0 _) (OpI.add (.i 1) (.inl rfl)) (by decide) <|
  .cons (p29_3 _) (OpI.mov (.r 10) (.inl rfl)) (by decide) <|
  .cons (p29_6 _) (OpI.mov (.r 6) (.inl rfl)) (by decide) <|
  .nil 8

def j25 : List Byte := [0x74, 0x87]
theorem j25_0 : ∀ feat, Dec feat j25 0 (FV7z.mk (.jcc 4) 64 [.rel 18446744073709551495] 2) := by dec_rfl

/-- The stretch at `838`. -/
def p30 : List Byte := [
  0xc1, 0xe8, 0x05, 0x83, 0xe0, 0x07, 0x83, 0xf8, 0x01, 0x41, 0x0f, 0x94, 0xc0, 0x83, 0xfa, 0x01]

theorem p30_0 : ∀ feat, Dec feat p30 0 (FV7z.mk .shr 32 [gr 32 0, Src.opd 8 (.i 5)] 3) := by dec_rfl
theorem p30_3 : ∀ feat, Dec feat p30 3 (FV7z.mk .and 32 [gr 32 0, Src.opd 32 (.i 7)] 3) := by dec_rfl
theorem p30_6 : ∀ feat, Dec feat p30 6 (FV7z.mk .cmp 32 [gr 32 0, Src.opd 32 (.i 1)] 3) := by dec_rfl
theorem p30_9 : ∀ feat, Dec feat p30 9 (FV7z.mk (.setcc 4) 8 [gr 8 8] 4) := by dec_rfl
theorem p30_13 : ∀ feat, Dec feat p30 13 (FV7z.mk .cmp 32 [gr 32 2, Src.opd 32 (.i 1)] 3) := by dec_rfl

/-- What the stretch does. -/
def o30 : List Op := [
  Op.shr 0 (.i 5),
  Op.and 32 0 (.i 7),
  Op.cmp 32 0 (.i 1),
  Op.setcc 4 8,
  Op.cmp 32 2 (.i 1)]

theorem b30 (prof : Profile) : Blk prof p30 0 16 o30 :=
  .cons (p30_0 _) (OpI.shr (.i 5)) (by decide) <|
  .cons (p30_3 _) (OpI.and (.i 7) (.inl rfl)) (by decide) <|
  .cons (p30_6 _) (OpI.cmp (.i 1) (.inl rfl)) (by decide) <|
  .cons (p30_9 _) (OpI.setcc) (by decide) <|
  .cons (p30_13 _) (OpI.cmp (.i 1) (.inl rfl)) (by decide) <|
  .nil 16

def j26 : List Byte := [0x74, 0xd8]
theorem j26_0 : ∀ feat, Dec feat j26 0 (FV7z.mk (.jcc 4) 64 [.rel 18446744073709551576] 2) := by dec_rfl

/-- The stretch at `856`. -/
def p31 : List Byte := [
  0x83, 0xfa, 0x02]

theorem p31_0 : ∀ feat, Dec feat p31 0 (FV7z.mk .cmp 32 [gr 32 2, Src.opd 32 (.i 2)] 3) := by dec_rfl

/-- What the stretch does. -/
def o31 : List Op := [
  Op.cmp 32 2 (.i 2)]

theorem b31 (prof : Profile) : Blk prof p31 0 3 o31 :=
  .cons (p31_0 _) (OpI.cmp (.i 2) (.inl rfl)) (by decide) <|
  .nil 3

def j27 : List Byte := [0x75, 0x05]
theorem j27_0 : ∀ feat, Dec feat j27 0 (FV7z.mk (.jcc 5) 64 [.rel 5] 2) := by dec_rfl

def j28 : List Byte := [0x75, 0xd3]
theorem j28_0 : ∀ feat, Dec feat j28 0 (FV7z.mk (.jcc 5) 64 [.rel 18446744073709551571] 2) := by dec_rfl

/-- The stretch at `866`. -/
def p32 : List Byte := [
  0x83, 0xf8, 0x02]

theorem p32_0 : ∀ feat, Dec feat p32 0 (FV7z.mk .cmp 32 [gr 32 0, Src.opd 32 (.i 2)] 3) := by dec_rfl

/-- What the stretch does. -/
def o32 : List Op := [
  Op.cmp 32 0 (.i 2)]

theorem b32 (prof : Profile) : Blk prof p32 0 3 o32 :=
  .cons (p32_0 _) (OpI.cmp (.i 2) (.inl rfl)) (by decide) <|
  .nil 3

def j29 : List Byte := [0x0f, 0x85, 0x9e, 0x00, 0x00, 0x00]
theorem j29_0 : ∀ feat, Dec feat j29 0 (FV7z.mk (.jcc 5) 64 [.rel 158] 6) := by dec_rfl

/-- The stretch at `875`. -/
def p33 : List Byte := [
  0x41, 0x83, 0xf9, 0x06]

theorem p33_0 : ∀ feat, Dec feat p33 0 (FV7z.mk .cmp 32 [gr 32 9, Src.opd 32 (.i 6)] 4) := by dec_rfl

/-- What the stretch does. -/
def o33 : List Op := [
  Op.cmp 32 9 (.i 6)]

theorem b33 (prof : Profile) : Blk prof p33 0 4 o33 :=
  .cons (p33_0 _) (OpI.cmp (.i 6) (.inl rfl)) (by decide) <|
  .nil 4

def j30 : List Byte := [0x0f, 0x85, 0x94, 0x00, 0x00, 0x00]
theorem j30_0 : ∀ feat, Dec feat j30 0 (FV7z.mk (.jcc 5) 64 [.rel 148] 6) := by dec_rfl

/-- The stretch at `885`. -/
def p34 : List Byte := [
  0x8d, 0x87, 0x47, 0xff, 0xff, 0xff, 0x44, 0x29, 0xc8]

theorem p34_0 : ∀ feat, Dec feat p34 0 (FV7z.mk .lea 32 [gr 32 0, .mem (mg (some 7) none 1 18446744073709551431 0)] 6) := by dec_rfl
theorem p34_6 : ∀ feat, Dec feat p34 6 (FV7z.mk .sub 32 [gr 32 0, Src.opd 32 (.r 9)] 3) := by dec_rfl

/-- What the stretch does. -/
def o34 : List Op := [
  Op.lea 32 0 (some 7) none 1 18446744073709551431,
  Op.sub 32 0 (.r 9)]

theorem b34 (prof : Profile) : Blk prof p34 0 9 o34 :=
  .cons (p34_0 _) (OpI.lea (.inl rfl)) (by decide) <|
  .cons (p34_6 _) (OpI.sub (.r 9) (.inl rfl)) (by decide) <|
  .nil 9

def j31 : List Byte := [0x74, 0x4e]
theorem j31_0 : ∀ feat, Dec feat j31 0 (FV7z.mk (.jcc 4) 64 [.rel 78] 2) := by dec_rfl

/-- The stretch at `896`. -/
def p35 : List Byte := [
  0x83, 0xf8, 0x01]

theorem p35_0 : ∀ feat, Dec feat p35 0 (FV7z.mk .cmp 32 [gr 32 0, Src.opd 32 (.i 1)] 3) := by dec_rfl

/-- What the stretch does. -/
def o35 : List Op := [
  Op.cmp 32 0 (.i 1)]

theorem b35 (prof : Profile) : Blk prof p35 0 3 o35 :=
  .cons (p35_0 _) (OpI.cmp (.i 1) (.inl rfl)) (by decide) <|
  .nil 3

def j32 : List Byte := [0x0f, 0x84, 0xa7, 0x00, 0x00, 0x00]
theorem j32_0 : ∀ feat, Dec feat j32 0 (FV7z.mk (.jcc 4) 64 [.rel 167] 6) := by dec_rfl

def j33 : List Byte := [0x0f, 0x85, 0xca, 0x00, 0x00, 0x00]
theorem j33_0 : ∀ feat, Dec feat j33 0 (FV7z.mk (.jcc 5) 64 [.rel 202] 6) := by dec_rfl

/-- The stretch at `914`. -/
def p36 : List Byte := [
  0x81, 0xe3, 0xff, 0x0f, 0x00, 0x00, 0x48, 0x8d, 0x43, 0x01]

theorem p36_0 : ∀ feat, Dec feat p36 0 (FV7z.mk .and 32 [gr 32 3, Src.opd 32 (.i 4095)] 6) := by dec_rfl
theorem p36_6 : ∀ feat, Dec feat p36 6 (FV7z.mk .lea 64 [gr 64 0, .mem (mg (some 3) none 1 1 0)] 4) := by dec_rfl

/-- What the stretch does. -/
def o36 : List Op := [
  Op.and 32 3 (.i 4095),
  Op.lea 64 0 (some 3) none 1 1]

theorem b36 (prof : Profile) : Blk prof p36 0 10 o36 :=
  .cons (p36_0 _) (OpI.and (.i 4095) (.inl rfl)) (by decide) <|
  .cons (p36_6 _) (OpI.lea (.inr rfl)) (by decide) <|
  .nil 10

def j34 : List Byte := [0xe9, 0x2e, 0xff, 0xff, 0xff]
theorem j34_0 : ∀ feat, Dec feat j34 0 (FV7z.mk .jmp 64 [.rel 18446744073709551406] 5) := by dec_rfl

def j35 : List Byte := [0x74, 0x54]
theorem j35_0 : ∀ feat, Dec feat j35 0 (FV7z.mk (.jcc 4) 64 [.rel 84] 2) := by dec_rfl

def j36 : List Byte := [0x74, 0x13]
theorem j36_0 : ∀ feat, Dec feat j36 0 (FV7z.mk (.jcc 4) 64 [.rel 19] 2) := by dec_rfl

/-- The stretch at `954`. -/
def p37 : List Byte := [
  0x41, 0x0f, 0xb6, 0x43, 0x02]

theorem p37_0 : ∀ feat, Dec feat p37 0 (FV7z.mk .movzx 32 [gr 32 0, .mem (mg (some 11) none 1 2 8)] 5) := by dec_rfl

/-- What the stretch does. -/
def o37 : List Op := [
  Op.ldzx 8 0 (some 11) none 1 2]

theorem b37 (prof : Profile) : Blk prof p37 0 5 o37 :=
  .cons (p37_0 _) (OpI.ldzx (.inl rfl)) (by decide) <|
  .nil 5

def j37 : List Byte := [0xe9, 0x0b, 0xff, 0xff, 0xff]
theorem j37_0 : ∀ feat, Dec feat j37 0 (FV7z.mk .jmp 64 [.rel 18446744073709551371] 5) := by dec_rfl

/-- The stretch at `964`. -/
def p38 : List Byte := [
  0x41, 0x0f, 0xb6, 0x43, 0x01]

theorem p38_0 : ∀ feat, Dec feat p38 0 (FV7z.mk .movzx 32 [gr 32 0, .mem (mg (some 11) none 1 1 8)] 5) := by dec_rfl

/-- What the stretch does. -/
def o38 : List Op := [
  Op.ldzx 8 0 (some 11) none 1 1]

theorem b38 (prof : Profile) : Blk prof p38 0 5 o38 :=
  .cons (p38_0 _) (OpI.ldzx (.inl rfl)) (by decide) <|
  .nil 5

def j38 : List Byte := [0xe9, 0x01, 0xff, 0xff, 0xff]
theorem j38_0 : ∀ feat, Dec feat j38 0 (FV7z.mk .jmp 64 [.rel 18446744073709551361] 5) := by dec_rfl

/-- The stretch at `974`. -/
def p39 : List Byte := [
  0x89, 0xd8, 0x89, 0xda, 0xc1, 0xeb, 0x0c, 0xc1, 0xe8, 0x16, 0x81, 0xe2, 0xff, 0x0f, 0x00, 0x00,
  0x83, 0xc2, 0x01, 0x83, 0xc0, 0x01, 0x0f, 0xaf, 0xc2, 0x8d, 0x51, 0x01, 0x0f, 0xaf, 0xc2, 0x89,
  0xda, 0x81, 0xe2, 0xff, 0x03, 0x00, 0x00, 0x83, 0xc2, 0x01, 0x0f, 0xaf, 0xc2]

theorem p39_0 : ∀ feat, Dec feat p39 0 (FV7z.mk .mov 32 [gr 32 0, Src.opd 32 (.r 3)] 2) := by dec_rfl
theorem p39_2 : ∀ feat, Dec feat p39 2 (FV7z.mk .mov 32 [gr 32 2, Src.opd 32 (.r 3)] 2) := by dec_rfl
theorem p39_4 : ∀ feat, Dec feat p39 4 (FV7z.mk .shr 32 [gr 32 3, Src.opd 8 (.i 12)] 3) := by dec_rfl
theorem p39_7 : ∀ feat, Dec feat p39 7 (FV7z.mk .shr 32 [gr 32 0, Src.opd 8 (.i 22)] 3) := by dec_rfl
theorem p39_10 : ∀ feat, Dec feat p39 10 (FV7z.mk .and 32 [gr 32 2, Src.opd 32 (.i 4095)] 6) := by dec_rfl
theorem p39_16 : ∀ feat, Dec feat p39 16 (FV7z.mk .add 32 [gr 32 2, Src.opd 32 (.i 1)] 3) := by dec_rfl
theorem p39_19 : ∀ feat, Dec feat p39 19 (FV7z.mk .add 32 [gr 32 0, Src.opd 32 (.i 1)] 3) := by dec_rfl
theorem p39_22 : ∀ feat, Dec feat p39 22 (FV7z.mk .imul 32 [gr 32 0, gr 32 2] 3) := by dec_rfl
theorem p39_25 : ∀ feat, Dec feat p39 25 (FV7z.mk .lea 32 [gr 32 2, .mem (mg (some 1) none 1 1 0)] 3) := by dec_rfl
theorem p39_28 : ∀ feat, Dec feat p39 28 (FV7z.mk .imul 32 [gr 32 0, gr 32 2] 3) := by dec_rfl
theorem p39_31 : ∀ feat, Dec feat p39 31 (FV7z.mk .mov 32 [gr 32 2, Src.opd 32 (.r 3)] 2) := by dec_rfl
theorem p39_33 : ∀ feat, Dec feat p39 33 (FV7z.mk .and 32 [gr 32 2, Src.opd 32 (.i 1023)] 6) := by dec_rfl
theorem p39_39 : ∀ feat, Dec feat p39 39 (FV7z.mk .add 32 [gr 32 2, Src.opd 32 (.i 1)] 3) := by dec_rfl
theorem p39_42 : ∀ feat, Dec feat p39 42 (FV7z.mk .imul 32 [gr 32 0, gr 32 2] 3) := by dec_rfl

/-- What the stretch does. -/
def o39 : List Op := [
  Op.mov 32 0 (.r 3),
  Op.mov 32 2 (.r 3),
  Op.shr 3 (.i 12),
  Op.shr 0 (.i 22),
  Op.and 32 2 (.i 4095),
  Op.add 32 2 (.i 1),
  Op.add 32 0 (.i 1),
  Op.imul 0 2,
  Op.lea 32 2 (some 1) none 1 1,
  Op.imul 0 2,
  Op.mov 32 2 (.r 3),
  Op.and 32 2 (.i 1023),
  Op.add 32 2 (.i 1),
  Op.imul 0 2]

theorem b39 (prof : Profile) : Blk prof p39 0 45 o39 :=
  .cons (p39_0 _) (OpI.mov (.r 3) (.inl rfl)) (by decide) <|
  .cons (p39_2 _) (OpI.mov (.r 3) (.inl rfl)) (by decide) <|
  .cons (p39_4 _) (OpI.shr (.i 12)) (by decide) <|
  .cons (p39_7 _) (OpI.shr (.i 22)) (by decide) <|
  .cons (p39_10 _) (OpI.and (.i 4095) (.inl rfl)) (by decide) <|
  .cons (p39_16 _) (OpI.add (.i 1) (.inl rfl)) (by decide) <|
  .cons (p39_19 _) (OpI.add (.i 1) (.inl rfl)) (by decide) <|
  .cons (p39_22 _) (OpI.imul) (by decide) <|
  .cons (p39_25 _) (OpI.lea (.inl rfl)) (by decide) <|
  .cons (p39_28 _) (OpI.imul) (by decide) <|
  .cons (p39_31 _) (OpI.mov (.r 3) (.inl rfl)) (by decide) <|
  .cons (p39_33 _) (OpI.and (.i 1023) (.inl rfl)) (by decide) <|
  .cons (p39_39 _) (OpI.add (.i 1) (.inl rfl)) (by decide) <|
  .cons (p39_42 _) (OpI.imul) (by decide) <|
  .nil 45

def j39 : List Byte := [0xe9, 0xcf, 0xfe, 0xff, 0xff]
theorem j39_0 : ∀ feat, Dec feat j39 0 (FV7z.mk .jmp 64 [.rel 18446744073709551311] 5) := by dec_rfl

/-- The stretch at `1024`. -/
def p40 : List Byte := [
  0x41, 0x8b, 0x43, 0x04]

theorem p40_0 : ∀ feat, Dec feat p40 0 (FV7z.mk .mov 32 [gr 32 0, .mem (mg (some 11) none 1 4 32)] 4) := by dec_rfl

/-- What the stretch does. -/
def o40 : List Op := [
  Op.ld 32 0 (some 11) none 1 4]

theorem b40 (prof : Profile) : Blk prof p40 0 4 o40 :=
  .cons (p40_0 _) (OpI.ld (.inl rfl)) (by decide) <|
  .nil 4

def j40 : List Byte := [0xe9, 0xc6, 0xfe, 0xff, 0xff]
theorem j40_0 : ∀ feat, Dec feat j40 0 (FV7z.mk .jmp 64 [.rel 18446744073709551302] 5) := by dec_rfl

/-- The stretch at `1033`. -/
def p41 : List Byte := [
  0x83, 0xf8, 0x03]

theorem p41_0 : ∀ feat, Dec feat p41 0 (FV7z.mk .cmp 32 [gr 32 0, Src.opd 32 (.i 3)] 3) := by dec_rfl

/-- What the stretch does. -/
def o41 : List Op := [
  Op.cmp 32 0 (.i 3)]

theorem b41 (prof : Profile) : Blk prof p41 0 3 o41 :=
  .cons (p41_0 _) (OpI.cmp (.i 3) (.inl rfl)) (by decide) <|
  .nil 3

def j41 : List Byte := [0x75, 0x0a]
theorem j41_0 : ∀ feat, Dec feat j41 0 (FV7z.mk (.jcc 5) 64 [.rel 10] 2) := by dec_rfl

def j42 : List Byte := [0x0f, 0x84, 0x5d, 0xff, 0xff, 0xff]
theorem j42_0 : ∀ feat, Dec feat j42 0 (FV7z.mk (.jcc 4) 64 [.rel 18446744073709551453] 6) := by dec_rfl

/-- The stretch at `1048`. -/
def p42 : List Byte := [
  0x83, 0xf8, 0x04]

theorem p42_0 : ∀ feat, Dec feat p42 0 (FV7z.mk .cmp 32 [gr 32 0, Src.opd 32 (.i 4)] 3) := by dec_rfl

/-- What the stretch does. -/
def o42 : List Op := [
  Op.cmp 32 0 (.i 4)]

theorem b42 (prof : Profile) : Blk prof p42 0 3 o42 :=
  .cons (p42_0 _) (OpI.cmp (.i 4) (.inl rfl)) (by decide) <|
  .nil 3

def j43 : List Byte := [0x0f, 0x85, 0x14, 0xff, 0xff, 0xff]
theorem j43_0 : ∀ feat, Dec feat j43 0 (FV7z.mk (.jcc 5) 64 [.rel 18446744073709551380] 6) := by dec_rfl

/-- The stretch at `1057`. -/
def p43 : List Byte := [
  0x41, 0x83, 0xf9, 0x0c]

theorem p43_0 : ∀ feat, Dec feat p43 0 (FV7z.mk .cmp 32 [gr 32 9, Src.opd 32 (.i 12)] 4) := by dec_rfl

/-- What the stretch does. -/
def o43 : List Op := [
  Op.cmp 32 9 (.i 12)]

theorem b43 (prof : Profile) : Blk prof p43 0 4 o43 :=
  .cons (p43_0 _) (OpI.cmp (.i 12) (.inl rfl)) (by decide) <|
  .nil 4

def j44 : List Byte := [0x0f, 0x84, 0x4a, 0xff, 0xff, 0xff]
theorem j44_0 : ∀ feat, Dec feat j44 0 (FV7z.mk (.jcc 4) 64 [.rel 18446744073709551434] 6) := by dec_rfl

def j45 : List Byte := [0xe9, 0x05, 0xff, 0xff, 0xff]
theorem j45_0 : ∀ feat, Dec feat j45 0 (FV7z.mk .jmp 64 [.rel 18446744073709551365] 5) := by dec_rfl

/-- The stretch at `1072`. -/
def p44 : List Byte := [
  0x89, 0xd8, 0xc1, 0xe8, 0x16, 0x83, 0xc0, 0x01]

theorem p44_0 : ∀ feat, Dec feat p44 0 (FV7z.mk .mov 32 [gr 32 0, Src.opd 32 (.r 3)] 2) := by dec_rfl
theorem p44_2 : ∀ feat, Dec feat p44 2 (FV7z.mk .shr 32 [gr 32 0, Src.opd 8 (.i 22)] 3) := by dec_rfl
theorem p44_5 : ∀ feat, Dec feat p44 5 (FV7z.mk .add 32 [gr 32 0, Src.opd 32 (.i 1)] 3) := by dec_rfl

/-- What the stretch does. -/
def o44 : List Op := [
  Op.mov 32 0 (.r 3),
  Op.shr 0 (.i 22),
  Op.add 32 0 (.i 1)]

theorem b44 (prof : Profile) : Blk prof p44 0 8 o44 :=
  .cons (p44_0 _) (OpI.mov (.r 3) (.inl rfl)) (by decide) <|
  .cons (p44_2 _) (OpI.shr (.i 22)) (by decide) <|
  .cons (p44_5 _) (OpI.add (.i 1) (.inl rfl)) (by decide) <|
  .nil 8

def j46 : List Byte := [0xe9, 0x92, 0xfe, 0xff, 0xff]
theorem j46_0 : ∀ feat, Dec feat j46 0 (FV7z.mk .jmp 64 [.rel 18446744073709551250] 5) := by dec_rfl

/-- The stretch at `1152`. -/
def p45 : List Byte := [
  0x41, 0xb8, 0x04, 0x00, 0x00, 0x00]

theorem p45_0 : ∀ feat, Dec feat p45 0 (FV7z.mk .mov 32 [gr 32 8, Src.opd 32 (.i 4)] 6) := by dec_rfl

/-- What the stretch does. -/
def o45 : List Op := [
  Op.mov 32 8 (.i 4)]

theorem b45 (prof : Profile) : Blk prof p45 0 6 o45 :=
  .cons (p45_0 _) (OpI.mov (.i 4) (.inl rfl)) (by decide) <|
  .nil 6

def j47 : List Byte := [0xeb, 0x19]
theorem j47_0 : ∀ feat, Dec feat j47 0 (FV7z.mk .jmp 64 [.rel 25] 2) := by dec_rfl

/-- The stretch at `1160`. -/
def p46 : List Byte := [
  0x84, 0xc0]

theorem p46_0 : ∀ feat, Dec feat p46 0 (FV7z.mk .test 8 [gr 8 0, Src.opd 8 (.r 0)] 2) := by dec_rfl

/-- What the stretch does. -/
def o46 : List Op := [
  Op.test 8 0 (.r 0)]

theorem b46 (prof : Profile) : Blk prof p46 0 2 o46 :=
  .cons (p46_0 _) (OpI.test8 (.r 0)) (by decide) <|
  .nil 2

def j48 : List Byte := [0x74, 0x26]
theorem j48_0 : ∀ feat, Dec feat j48 0 (FV7z.mk (.jcc 4) 64 [.rel 38] 2) := by dec_rfl

/-- The stretch at `1164`. -/
def p47 : List Byte := [
  0x83, 0xc6, 0x01, 0x44, 0x89, 0xc0, 0x89, 0xf1]

theorem p47_0 : ∀ feat, Dec feat p47 0 (FV7z.mk .add 32 [gr 32 6, Src.opd 32 (.i 1)] 3) := by dec_rfl
theorem p47_3 : ∀ feat, Dec feat p47 3 (FV7z.mk .mov 32 [gr 32 0, Src.opd 32 (.r 8)] 3) := by dec_rfl
theorem p47_6 : ∀ feat, Dec feat p47 6 (FV7z.mk .mov 32 [gr 32 1, Src.opd 32 (.r 6)] 2) := by dec_rfl

/-- What the stretch does. -/
def o47 : List Op := [
  Op.add 32 6 (.i 1),
  Op.mov 32 0 (.r 8),
  Op.mov 32 1 (.r 6)]

theorem b47 (prof : Profile) : Blk prof p47 0 8 o47 :=
  .cons (p47_0 _) (OpI.add (.i 1) (.inl rfl)) (by decide) <|
  .cons (p47_3 _) (OpI.mov (.r 8) (.inl rfl)) (by decide) <|
  .cons (p47_6 _) (OpI.mov (.r 6) (.inl rfl)) (by decide) <|
  .nil 8

def j49 : List Byte := [0x0f, 0x84, 0x2c, 0xfe, 0xff, 0xff]
theorem j49_0 : ∀ feat, Dec feat j49 0 (FV7z.mk (.jcc 4) 64 [.rel 18446744073709551148] 6) := by dec_rfl

/-- The stretch at `1185`. -/
def p48 : List Byte := [
  0xc1, 0xe8, 0x05, 0x83, 0xe0, 0x07, 0x83, 0xf8, 0x01, 0x0f, 0x94, 0xc0, 0x83, 0xfa, 0x01]

theorem p48_0 : ∀ feat, Dec feat p48 0 (FV7z.mk .shr 32 [gr 32 0, Src.opd 8 (.i 5)] 3) := by dec_rfl
theorem p48_3 : ∀ feat, Dec feat p48 3 (FV7z.mk .and 32 [gr 32 0, Src.opd 32 (.i 7)] 3) := by dec_rfl
theorem p48_6 : ∀ feat, Dec feat p48 6 (FV7z.mk .cmp 32 [gr 32 0, Src.opd 32 (.i 1)] 3) := by dec_rfl
theorem p48_9 : ∀ feat, Dec feat p48 9 (FV7z.mk (.setcc 4) 8 [gr 8 0] 3) := by dec_rfl
theorem p48_12 : ∀ feat, Dec feat p48 12 (FV7z.mk .cmp 32 [gr 32 2, Src.opd 32 (.i 1)] 3) := by dec_rfl

/-- What the stretch does. -/
def o48 : List Op := [
  Op.shr 0 (.i 5),
  Op.and 32 0 (.i 7),
  Op.cmp 32 0 (.i 1),
  Op.setcc 4 0,
  Op.cmp 32 2 (.i 1)]

theorem b48 (prof : Profile) : Blk prof p48 0 15 o48 :=
  .cons (p48_0 _) (OpI.shr (.i 5)) (by decide) <|
  .cons (p48_3 _) (OpI.and (.i 7) (.inl rfl)) (by decide) <|
  .cons (p48_6 _) (OpI.cmp (.i 1) (.inl rfl)) (by decide) <|
  .cons (p48_9 _) (OpI.setcc) (by decide) <|
  .cons (p48_12 _) (OpI.cmp (.i 1) (.inl rfl)) (by decide) <|
  .nil 15

def j50 : List Byte := [0x74, 0xd6]
theorem j50_0 : ∀ feat, Dec feat j50 0 (FV7z.mk (.jcc 4) 64 [.rel 18446744073709551574] 2) := by dec_rfl

def j51 : List Byte := [0x75, 0xd5]
theorem j51_0 : ∀ feat, Dec feat j51 0 (FV7z.mk (.jcc 5) 64 [.rel 18446744073709551573] 2) := by dec_rfl

def j52 : List Byte := [0x0f, 0x85, 0xb6, 0xfe, 0xff, 0xff]
theorem j52_0 : ∀ feat, Dec feat j52 0 (FV7z.mk (.jcc 5) 64 [.rel 18446744073709551286] 6) := by dec_rfl

def j53 : List Byte := [0xeb, 0xcb]
theorem j53_0 : ∀ feat, Dec feat j53 0 (FV7z.mk .jmp 64 [.rel 18446744073709551563] 2) := by dec_rfl

/-- The stretch at `1230`. -/
def p49 : List Byte := [
  0xc1, 0xe8, 0x05, 0x83, 0xe0, 0x07, 0x83, 0xf8, 0x01]

theorem p49_0 : ∀ feat, Dec feat p49 0 (FV7z.mk .shr 32 [gr 32 0, Src.opd 8 (.i 5)] 3) := by dec_rfl
theorem p49_3 : ∀ feat, Dec feat p49 3 (FV7z.mk .and 32 [gr 32 0, Src.opd 32 (.i 7)] 3) := by dec_rfl
theorem p49_6 : ∀ feat, Dec feat p49 6 (FV7z.mk .cmp 32 [gr 32 0, Src.opd 32 (.i 1)] 3) := by dec_rfl

/-- What the stretch does. -/
def o49 : List Op := [
  Op.shr 0 (.i 5),
  Op.and 32 0 (.i 7),
  Op.cmp 32 0 (.i 1)]

theorem b49 (prof : Profile) : Blk prof p49 0 9 o49 :=
  .cons (p49_0 _) (OpI.shr (.i 5)) (by decide) <|
  .cons (p49_3 _) (OpI.and (.i 7) (.inl rfl)) (by decide) <|
  .cons (p49_6 _) (OpI.cmp (.i 1) (.inl rfl)) (by decide) <|
  .nil 9

def j54 : List Byte := [0x75, 0x09]
theorem j54_0 : ∀ feat, Dec feat j54 0 (FV7z.mk (.jcc 5) 64 [.rel 9] 2) := by dec_rfl

/-- The stretch at `1241`. -/
def p50 : List Byte := [
  0x83, 0xfa, 0x01]

theorem p50_0 : ∀ feat, Dec feat p50 0 (FV7z.mk .cmp 32 [gr 32 2, Src.opd 32 (.i 1)] 3) := by dec_rfl

/-- What the stretch does. -/
def o50 : List Op := [
  Op.cmp 32 2 (.i 1)]

theorem b50 (prof : Profile) : Blk prof p50 0 3 o50 :=
  .cons (p50_0 _) (OpI.cmp (.i 1) (.inl rfl)) (by decide) <|
  .nil 3

def j55 : List Byte := [0x0f, 0x84, 0x93, 0xfe, 0xff, 0xff]
theorem j55_0 : ∀ feat, Dec feat j55 0 (FV7z.mk (.jcc 4) 64 [.rel 18446744073709551251] 6) := by dec_rfl

def j56 : List Byte := [0x75, 0xdb]
theorem j56_0 : ∀ feat, Dec feat j56 0 (FV7z.mk (.jcc 5) 64 [.rel 18446744073709551579] 2) := by dec_rfl

def j57 : List Byte := [0xe9, 0xd5, 0xfd, 0xff, 0xff]
theorem j57_0 : ∀ feat, Dec feat j57 0 (FV7z.mk .jmp 64 [.rel 18446744073709551061] 5) := by dec_rfl

end FV7z.Icw
