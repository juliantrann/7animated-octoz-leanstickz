import FV7z.Lemmas.Sp
import FV7z.Lemmas.BlkOps14
import FV7z.Lemmas.BlkOps12
import FV7z.Lemmas.BlkOps2
/-!
# The stretches of straight-line code of `_nl_normalize_codeset` (PLAN.md §M, M1)

Each distinct stretch between labels and jumps (`p*`, 22 of them) and each distinct jump (`j*`, 14) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.Nlc
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The stretch at `0`. -/
def p0 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0x41, 0x54, 0x55, 0x53, 0x48, 0x85, 0xf6]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem p0_4 : ∀ feat, Dec feat p0 4 (FV7z.mk .push 64 [gr 64 12] 2) := by dec_rfl
theorem p0_6 : ∀ feat, Dec feat p0 6 (FV7z.mk .push 64 [gr 64 5] 1) := by dec_rfl
theorem p0_7 : ∀ feat, Dec feat p0 7 (FV7z.mk .push 64 [gr 64 3] 1) := by dec_rfl
theorem p0_8 : ∀ feat, Dec feat p0 8 (FV7z.mk .test 64 [gr 64 6, Src.opd 64 (.r 6)] 3) := by dec_rfl

/-- What the stretch does. -/
def o0 : List Op := [
  Op.nop,
  Op.push 12,
  Op.push 5,
  Op.push 3,
  Op.test 64 6 (.r 6)]

theorem b0 (prof : Profile) : Blk prof p0 0 11 o0 :=
  .cons (p0_0 _) (OpI.endbr) (by decide) <|
  .cons (p0_4 _) (OpI.push) (by decide) <|
  .cons (p0_6 _) (OpI.push) (by decide) <|
  .cons (p0_7 _) (OpI.push) (by decide) <|
  .cons (p0_8 _) (OpI.test (.r 6) (.inr rfl)) (by decide) <|
  .nil 11

def j0 : List Byte := [0x0f, 0x84, 0xdf, 0x00, 0x00, 0x00]
theorem j0_0 : ∀ feat, Dec feat j0 0 (FV7z.mk (.jcc 4) 64 [.rel 223] 6) := by dec_rfl

/-- The stretch at `17`. -/
def p1 : List Byte := [
  0x48, 0x8b, 0x1d, 0x80, 0x75, 0x17, 0x00, 0x48, 0x89, 0xfd, 0x49, 0x89, 0xf4, 0x48, 0x89, 0xfa,
  0x4c, 0x8d, 0x04, 0x3e, 0x45, 0x31, 0xc9, 0xbe, 0x01, 0x00, 0x00, 0x00, 0x31, 0xff, 0x90]

theorem p1_0 : ∀ feat, Dec feat p1 0 (FV7z.mk .mov 64 [gr 64 3, .mem (mrip 1537408 64)] 7) := by dec_rfl
theorem p1_7 : ∀ feat, Dec feat p1 7 (FV7z.mk .mov 64 [gr 64 5, Src.opd 64 (.r 7)] 3) := by dec_rfl
theorem p1_10 : ∀ feat, Dec feat p1 10 (FV7z.mk .mov 64 [gr 64 12, Src.opd 64 (.r 6)] 3) := by dec_rfl
theorem p1_13 : ∀ feat, Dec feat p1 13 (FV7z.mk .mov 64 [gr 64 2, Src.opd 64 (.r 7)] 3) := by dec_rfl
theorem p1_16 : ∀ feat, Dec feat p1 16 (FV7z.mk .lea 64 [gr 64 8, .mem (mg (some 6) (some 7) 1 0 0)] 4) := by dec_rfl
theorem p1_20 : ∀ feat, Dec feat p1 20 (FV7z.mk .xor 32 [gr 32 9, Src.opd 32 (.r 9)] 3) := by dec_rfl
theorem p1_23 : ∀ feat, Dec feat p1 23 (FV7z.mk .mov 32 [gr 32 6, Src.opd 32 (.i 1)] 5) := by dec_rfl
theorem p1_28 : ∀ feat, Dec feat p1 28 (FV7z.mk .xor 32 [gr 32 7, Src.opd 32 (.r 7)] 2) := by dec_rfl
theorem p1_30 : ∀ feat, Dec feat p1 30 (FV7z.mk .nop 32 [] 1) := by dec_rfl

/-- What the stretch does. -/
def o1 : List Op := [
  Op.lda 64 3 7935176,
  Op.mov 64 5 (.r 7),
  Op.mov 64 12 (.r 6),
  Op.mov 64 2 (.r 7),
  Op.lea 64 8 (some 6) (some 7) 1 0,
  Op.xor 32 9 (.r 9),
  Op.mov 32 6 (.i 1),
  Op.xor 32 7 (.r 7),
  Op.nop]

theorem b1 (prof : Profile) : BlkA prof p1 (0x619f41 : Addr) 0 31 o1 :=
  .cons (p1_0 _) (OpIA.ld_rip (.inr rfl) (by decide)) (by decide) <|
  .cons (p1_7 _) ((OpI.mov (.r 7) (.inr rfl)).at _) (by decide) <|
  .cons (p1_10 _) ((OpI.mov (.r 6) (.inr rfl)).at _) (by decide) <|
  .cons (p1_13 _) ((OpI.mov (.r 7) (.inr rfl)).at _) (by decide) <|
  .cons (p1_16 _) ((OpI.lea (.inr rfl)).at _) (by decide) <|
  .cons (p1_20 _) ((OpI.xor (.r 9) (.inl rfl)).at _) (by decide) <|
  .cons (p1_23 _) ((OpI.mov (.i 1) (.inl rfl)).at _) (by decide) <|
  .cons (p1_28 _) ((OpI.xor (.r 7) (.inl rfl)).at _) (by decide) <|
  .cons (p1_30 _) ((OpI.nop).at _) (by decide) <|
  .nil 31

/-- The stretch at `48`. -/
def p2 : List Byte := [
  0x0f, 0xb6, 0x0a, 0x48, 0x89, 0xc8, 0xf6, 0x04, 0x4b, 0x08]

theorem p2_0 : ∀ feat, Dec feat p2 0 (FV7z.mk .movzx 32 [gr 32 1, .mem (mg (some 2) none 1 0 8)] 3) := by dec_rfl
theorem p2_3 : ∀ feat, Dec feat p2 3 (FV7z.mk .mov 64 [gr 64 0, Src.opd 64 (.r 1)] 3) := by dec_rfl
theorem p2_6 : ∀ feat, Dec feat p2 6 (FV7z.mk .test 8 [.mem (mg (some 3) (some 1) 2 0 8), .imm 8 8] 4) := by dec_rfl

/-- What the stretch does. -/
def o2 : List Op := [
  Op.ldzx 8 1 (some 2) none 1 0,
  Op.mov 64 0 (.r 1),
  Op.testmi 8 (some 3) (some 1) 2 0 8]

theorem b2 (prof : Profile) : Blk prof p2 0 10 o2 :=
  .cons (p2_0 _) (OpI.ldzx (.inl rfl)) (by decide) <|
  .cons (p2_3 _) (OpI.mov (.r 1) (.inr rfl)) (by decide) <|
  .cons (p2_6 _) (OpI.testmi8) (by decide) <|
  .nil 10

def j1 : List Byte := [0x74, 0x0e]
theorem j1_0 : ∀ feat, Dec feat j1 0 (FV7z.mk (.jcc 4) 64 [.rel 14] 2) := by dec_rfl

/-- The stretch at `60`. -/
def p3 : List Byte := [
  0x83, 0xe8, 0x30, 0x48, 0x83, 0xc7, 0x01, 0x83, 0xf8, 0x0a, 0x41, 0x0f, 0x43, 0xf1]

theorem p3_0 : ∀ feat, Dec feat p3 0 (FV7z.mk .sub 32 [gr 32 0, Src.opd 32 (.i 48)] 3) := by dec_rfl
theorem p3_3 : ∀ feat, Dec feat p3 3 (FV7z.mk .add 64 [gr 64 7, Src.opd 64 (.i 1)] 4) := by dec_rfl
theorem p3_7 : ∀ feat, Dec feat p3 7 (FV7z.mk .cmp 32 [gr 32 0, Src.opd 32 (.i 10)] 3) := by dec_rfl
theorem p3_10 : ∀ feat, Dec feat p3 10 (FV7z.mk (.cmovcc 3) 32 [gr 32 6, gr 32 9] 4) := by dec_rfl

/-- What the stretch does. -/
def o3 : List Op := [
  Op.sub 32 0 (.i 48),
  Op.add 64 7 (.i 1),
  Op.cmp 32 0 (.i 10),
  Op.cmov32 3 6 9]

theorem b3 (prof : Profile) : Blk prof p3 0 14 o3 :=
  .cons (p3_0 _) (OpI.sub (.i 48) (.inl rfl)) (by decide) <|
  .cons (p3_3 _) (OpI.add (.i 1) (.inr rfl)) (by decide) <|
  .cons (p3_7 _) (OpI.cmp (.i 10) (.inl rfl)) (by decide) <|
  .cons (p3_10 _) (OpI.cmov32) (by decide) <|
  .nil 14

/-- The stretch at `74`. -/
def p4 : List Byte := [
  0x48, 0x83, 0xc2, 0x01, 0x49, 0x39, 0xd0]

theorem p4_0 : ∀ feat, Dec feat p4 0 (FV7z.mk .add 64 [gr 64 2, Src.opd 64 (.i 1)] 4) := by dec_rfl
theorem p4_4 : ∀ feat, Dec feat p4 4 (FV7z.mk .cmp 64 [gr 64 8, Src.opd 64 (.r 2)] 3) := by dec_rfl

/-- What the stretch does. -/
def o4 : List Op := [
  Op.add 64 2 (.i 1),
  Op.cmp 64 8 (.r 2)]

theorem b4 (prof : Profile) : Blk prof p4 0 7 o4 :=
  .cons (p4_0 _) (OpI.add (.i 1) (.inr rfl)) (by decide) <|
  .cons (p4_4 _) (OpI.cmp (.r 2) (.inr rfl)) (by decide) <|
  .nil 7

def j2 : List Byte := [0x75, 0xdd]
theorem j2_0 : ∀ feat, Dec feat j2 0 (FV7z.mk (.jcc 5) 64 [.rel 18446744073709551581] 2) := by dec_rfl

/-- The stretch at `83`. -/
def p5 : List Byte := [
  0x85, 0xf6]

theorem p5_0 : ∀ feat, Dec feat p5 0 (FV7z.mk .test 32 [gr 32 6, Src.opd 32 (.r 6)] 2) := by dec_rfl

/-- What the stretch does. -/
def o5 : List Op := [
  Op.test 32 6 (.r 6)]

theorem b5 (prof : Profile) : Blk prof p5 0 2 o5 :=
  .cons (p5_0 _) (OpI.test (.r 6) (.inl rfl)) (by decide) <|
  .nil 2

def j3 : List Byte := [0x75, 0x69]
theorem j3_0 : ∀ feat, Dec feat j3 0 (FV7z.mk (.jcc 5) 64 [.rel 105] 2) := by dec_rfl

/-- The stretch at `87`. -/
def p6 : List Byte := [
  0x48, 0x83, 0xc7, 0x01]

theorem p6_0 : ∀ feat, Dec feat p6 0 (FV7z.mk .add 64 [gr 64 7, Src.opd 64 (.i 1)] 4) := by dec_rfl

/-- What the stretch does. -/
def o6 : List Op := [
  Op.add 64 7 (.i 1)]

theorem b6 (prof : Profile) : Blk prof p6 0 4 o6 :=
  .cons (p6_0 _) (OpI.add (.i 1) (.inr rfl)) (by decide) <|
  .nil 4

/-- The stretch at `96`. -/
def p7 : List Byte := [
  0x48, 0x85, 0xc0]

theorem p7_0 : ∀ feat, Dec feat p7 0 (FV7z.mk .test 64 [gr 64 0, Src.opd 64 (.r 0)] 3) := by dec_rfl

/-- What the stretch does. -/
def o7 : List Op := [
  Op.test 64 0 (.r 0)]

theorem b7 (prof : Profile) : Blk prof p7 0 3 o7 :=
  .cons (p7_0 _) (OpI.test (.r 0) (.inr rfl)) (by decide) <|
  .nil 3

def j4 : List Byte := [0x74, 0x7b]
theorem j4_0 : ∀ feat, Dec feat j4 0 (FV7z.mk (.jcc 4) 64 [.rel 123] 2) := by dec_rfl

/-- The stretch at `101`. -/
def p8 : List Byte := [
  0x49, 0x89, 0xc1]

theorem p8_0 : ∀ feat, Dec feat p8 0 (FV7z.mk .mov 64 [gr 64 9, Src.opd 64 (.r 0)] 3) := by dec_rfl

/-- What the stretch does. -/
def o8 : List Op := [
  Op.mov 64 9 (.r 0)]

theorem b8 (prof : Profile) : Blk prof p8 0 3 o8 :=
  .cons (p8_0 _) (OpI.mov (.r 0) (.inr rfl)) (by decide) <|
  .nil 3

/-- The stretch at `104`. -/
def p9 : List Byte := [
  0x4c, 0x8b, 0x05, 0x31, 0x75, 0x17, 0x00, 0x31, 0xd2]

theorem p9_0 : ∀ feat, Dec feat p9 0 (FV7z.mk .mov 64 [gr 64 8, .mem (mrip 1537329 64)] 7) := by dec_rfl
theorem p9_7 : ∀ feat, Dec feat p9 7 (FV7z.mk .xor 32 [gr 32 2, Src.opd 32 (.r 2)] 2) := by dec_rfl

/-- What the stretch does. -/
def o9 : List Op := [
  Op.lda 64 8 7935184,
  Op.xor 32 2 (.r 2)]

theorem b9 (prof : Profile) : BlkA prof p9 (0x619f98 : Addr) 0 9 o9 :=
  .cons (p9_0 _) (OpIA.ld_rip (.inr rfl) (by decide)) (by decide) <|
  .cons (p9_7 _) ((OpI.xor (.r 2) (.inl rfl)).at _) (by decide) <|
  .nil 9

def j5 : List Byte := [0xeb, 0x19]
theorem j5_0 : ∀ feat, Dec feat j5 0 (FV7z.mk .jmp 64 [.rel 25] 2) := by dec_rfl

/-- The stretch at `120`. -/
def p10 : List Byte := [
  0x41, 0x8b, 0x0c, 0xb8, 0x48, 0x83, 0xc0, 0x01, 0x88, 0x48, 0xff]

theorem p10_0 : ∀ feat, Dec feat p10 0 (FV7z.mk .mov 32 [gr 32 1, .mem (mg (some 8) (some 7) 4 0 32)] 4) := by dec_rfl
theorem p10_4 : ∀ feat, Dec feat p10 4 (FV7z.mk .add 64 [gr 64 0, Src.opd 64 (.i 1)] 4) := by dec_rfl
theorem p10_8 : ∀ feat, Dec feat p10 8 (FV7z.mk .mov 8 [.mem (mg (some 0) none 1 18446744073709551615 8), gr 8 1] 3) := by dec_rfl

/-- What the stretch does. -/
def o10 : List Op := [
  Op.ld 32 1 (some 8) (some 7) 4 0,
  Op.add 64 0 (.i 1),
  Op.st 8 (some 0) none 1 18446744073709551615 1]

theorem b10 (prof : Profile) : Blk prof p10 0 11 o10 :=
  .cons (p10_0 _) (OpI.ld (.inl rfl)) (by decide) <|
  .cons (p10_4 _) (OpI.add (.i 1) (.inr rfl)) (by decide) <|
  .cons (p10_8 _) (OpI.st (.inl rfl)) (by decide) <|
  .nil 11

/-- The stretch at `131`. -/
def p11 : List Byte := [
  0x48, 0x83, 0xc2, 0x01, 0x49, 0x39, 0xd4]

theorem p11_0 : ∀ feat, Dec feat p11 0 (FV7z.mk .add 64 [gr 64 2, Src.opd 64 (.i 1)] 4) := by dec_rfl
theorem p11_4 : ∀ feat, Dec feat p11 4 (FV7z.mk .cmp 64 [gr 64 12, Src.opd 64 (.r 2)] 3) := by dec_rfl

/-- What the stretch does. -/
def o11 : List Op := [
  Op.add 64 2 (.i 1),
  Op.cmp 64 12 (.r 2)]

theorem b11 (prof : Profile) : Blk prof p11 0 7 o11 :=
  .cons (p11_0 _) (OpI.add (.i 1) (.inr rfl)) (by decide) <|
  .cons (p11_4 _) (OpI.cmp (.r 2) (.inr rfl)) (by decide) <|
  .nil 7

def j6 : List Byte := [0x76, 0x28]
theorem j6_0 : ∀ feat, Dec feat j6 0 (FV7z.mk (.jcc 6) 64 [.rel 40] 2) := by dec_rfl

/-- The stretch at `140`. -/
def p12 : List Byte := [
  0x0f, 0xb6, 0x7c, 0x15, 0x00, 0xf6, 0x44, 0x7b, 0x01, 0x04]

theorem p12_0 : ∀ feat, Dec feat p12 0 (FV7z.mk .movzx 32 [gr 32 7, .mem (mg (some 5) (some 2) 1 0 8)] 5) := by dec_rfl
theorem p12_5 : ∀ feat, Dec feat p12 5 (FV7z.mk .test 8 [.mem (mg (some 3) (some 7) 2 1 8), .imm 8 4] 5) := by dec_rfl

/-- What the stretch does. -/
def o12 : List Op := [
  Op.ldzx 8 7 (some 5) (some 2) 1 0,
  Op.testmi 8 (some 3) (some 7) 2 1 4]

theorem b12 (prof : Profile) : Blk prof p12 0 10 o12 :=
  .cons (p12_0 _) (OpI.ldzx (.inl rfl)) (by decide) <|
  .cons (p12_5 _) (OpI.testmi8) (by decide) <|
  .nil 10

def j7 : List Byte := [0x75, 0xe0]
theorem j7_0 : ∀ feat, Dec feat j7 0 (FV7z.mk (.jcc 5) 64 [.rel 18446744073709551584] 2) := by dec_rfl

/-- The stretch at `152`. -/
def p13 : List Byte := [
  0x40, 0x0f, 0xb6, 0xf7, 0x83, 0xee, 0x30, 0x83, 0xfe, 0x09]

theorem p13_0 : ∀ feat, Dec feat p13 0 (FV7z.mk .movzx 32 [gr 32 6, gr 8 7] 4) := by dec_rfl
theorem p13_4 : ∀ feat, Dec feat p13 4 (FV7z.mk .sub 32 [gr 32 6, Src.opd 32 (.i 48)] 3) := by dec_rfl
theorem p13_7 : ∀ feat, Dec feat p13 7 (FV7z.mk .cmp 32 [gr 32 6, Src.opd 32 (.i 9)] 3) := by dec_rfl

/-- What the stretch does. -/
def o13 : List Op := [
  Op.zxr 6 7,
  Op.sub 32 6 (.i 48),
  Op.cmp 32 6 (.i 9)]

theorem b13 (prof : Profile) : Blk prof p13 0 10 o13 :=
  .cons (p13_0 _) (OpI.zxr) (by decide) <|
  .cons (p13_4 _) (OpI.sub (.i 48) (.inl rfl)) (by decide) <|
  .cons (p13_7 _) (OpI.cmp (.i 9) (.inl rfl)) (by decide) <|
  .nil 10

def j8 : List Byte := [0x77, 0xdf]
theorem j8_0 : ∀ feat, Dec feat j8 0 (FV7z.mk (.jcc 7) 64 [.rel 18446744073709551583] 2) := by dec_rfl

/-- The stretch at `164`. -/
def p14 : List Byte := [
  0x48, 0x83, 0xc2, 0x01, 0x40, 0x88, 0x38, 0x48, 0x83, 0xc0, 0x01, 0x49, 0x39, 0xd4]

theorem p14_0 : ∀ feat, Dec feat p14 0 (FV7z.mk .add 64 [gr 64 2, Src.opd 64 (.i 1)] 4) := by dec_rfl
theorem p14_4 : ∀ feat, Dec feat p14 4 (FV7z.mk .mov 8 [.mem (mg (some 0) none 1 0 8), gr 8 7] 3) := by dec_rfl
theorem p14_7 : ∀ feat, Dec feat p14 7 (FV7z.mk .add 64 [gr 64 0, Src.opd 64 (.i 1)] 4) := by dec_rfl
theorem p14_11 : ∀ feat, Dec feat p14 11 (FV7z.mk .cmp 64 [gr 64 12, Src.opd 64 (.r 2)] 3) := by dec_rfl

/-- What the stretch does. -/
def o14 : List Op := [
  Op.add 64 2 (.i 1),
  Op.st 8 (some 0) none 1 0 7,
  Op.add 64 0 (.i 1),
  Op.cmp 64 12 (.r 2)]

theorem b14 (prof : Profile) : Blk prof p14 0 14 o14 :=
  .cons (p14_0 _) (OpI.add (.i 1) (.inr rfl)) (by decide) <|
  .cons (p14_4 _) (OpI.st (.inl rfl)) (by decide) <|
  .cons (p14_7 _) (OpI.add (.i 1) (.inr rfl)) (by decide) <|
  .cons (p14_11 _) (OpI.cmp (.r 2) (.inr rfl)) (by decide) <|
  .nil 14

def j9 : List Byte := [0x77, 0xd8]
theorem j9_0 : ∀ feat, Dec feat j9 0 (FV7z.mk (.jcc 7) 64 [.rel 18446744073709551576] 2) := by dec_rfl

/-- The stretch at `180`. -/
def p15 : List Byte := [
  0xc6, 0x00, 0x00, 0x4c, 0x89, 0xc8, 0x5b, 0x5d, 0x41, 0x5c]

theorem p15_0 : ∀ feat, Dec feat p15 0 (FV7z.mk .mov 8 [.mem (mg (some 0) none 1 0 8), .imm 8 0] 3) := by dec_rfl
theorem p15_3 : ∀ feat, Dec feat p15 3 (FV7z.mk .mov 64 [gr 64 0, Src.opd 64 (.r 9)] 3) := by dec_rfl
theorem p15_6 : ∀ feat, Dec feat p15 6 (FV7z.mk .pop 64 [gr 64 3] 1) := by dec_rfl
theorem p15_7 : ∀ feat, Dec feat p15 7 (FV7z.mk .pop 64 [gr 64 5] 1) := by dec_rfl
theorem p15_8 : ∀ feat, Dec feat p15 8 (FV7z.mk .pop 64 [gr 64 12] 2) := by dec_rfl

/-- What the stretch does. -/
def o15 : List Op := [
  Op.sti 8 (some 0) none 1 0 0,
  Op.mov 64 0 (.r 9),
  Op.pop 3,
  Op.pop 5,
  Op.pop 12]

theorem b15 (prof : Profile) : Blk prof p15 0 10 o15 :=
  .cons (p15_0 _) (OpI.sti (.inl rfl)) (by decide) <|
  .cons (p15_3 _) (OpI.mov (.r 9) (.inr rfl)) (by decide) <|
  .cons (p15_6 _) (OpI.pop) (by decide) <|
  .cons (p15_7 _) (OpI.pop) (by decide) <|
  .cons (p15_8 _) (OpI.pop) (by decide) <|
  .nil 10

/-- The stretch at `192`. -/
def p16 : List Byte := [
  0x48, 0x83, 0xc7, 0x04]

theorem p16_0 : ∀ feat, Dec feat p16 0 (FV7z.mk .add 64 [gr 64 7, Src.opd 64 (.i 4)] 4) := by dec_rfl

/-- What the stretch does. -/
def o16 : List Op := [
  Op.add 64 7 (.i 4)]

theorem b16 (prof : Profile) : Blk prof p16 0 4 o16 :=
  .cons (p16_0 _) (OpI.add (.i 4) (.inr rfl)) (by decide) <|
  .nil 4

/-- The stretch at `201`. -/
def p17 : List Byte := [
  0x49, 0x89, 0xc1, 0x48, 0x85, 0xc0]

theorem p17_0 : ∀ feat, Dec feat p17 0 (FV7z.mk .mov 64 [gr 64 9, Src.opd 64 (.r 0)] 3) := by dec_rfl
theorem p17_3 : ∀ feat, Dec feat p17 3 (FV7z.mk .test 64 [gr 64 0, Src.opd 64 (.r 0)] 3) := by dec_rfl

/-- What the stretch does. -/
def o17 : List Op := [
  Op.mov 64 9 (.r 0),
  Op.test 64 0 (.r 0)]

theorem b17 (prof : Profile) : Blk prof p17 0 6 o17 :=
  .cons (p17_0 _) (OpI.mov (.r 0) (.inr rfl)) (by decide) <|
  .cons (p17_3 _) (OpI.test (.r 0) (.inr rfl)) (by decide) <|
  .nil 6

def j10 : List Byte := [0x74, 0x0f]
theorem j10_0 : ∀ feat, Dec feat j10 0 (FV7z.mk (.jcc 4) 64 [.rel 15] 2) := by dec_rfl

/-- The stretch at `209`. -/
def p18 : List Byte := [
  0xc7, 0x00, 0x69, 0x73, 0x6f, 0x00, 0x48, 0x8d, 0x40, 0x03]

theorem p18_0 : ∀ feat, Dec feat p18 0 (FV7z.mk .mov 32 [.mem (mg (some 0) none 1 0 32), .imm 32 7304041] 6) := by dec_rfl
theorem p18_6 : ∀ feat, Dec feat p18 6 (FV7z.mk .lea 64 [gr 64 0, .mem (mg (some 0) none 1 3 0)] 4) := by dec_rfl

/-- What the stretch does. -/
def o18 : List Op := [
  Op.sti 32 (some 0) none 1 0 7304041,
  Op.lea 64 0 (some 0) none 1 3]

theorem b18 (prof : Profile) : Blk prof p18 0 10 o18 :=
  .cons (p18_0 _) (OpI.sti (.inr (.inr (.inl rfl)))) (by decide) <|
  .cons (p18_6 _) (OpI.lea (.inr rfl)) (by decide) <|
  .nil 10

def j11 : List Byte := [0xeb, 0x8b]
theorem j11_0 : ∀ feat, Dec feat j11 0 (FV7z.mk .jmp 64 [.rel 18446744073709551499] 2) := by dec_rfl

/-- The stretch at `224`. -/
def p19 : List Byte := [
  0x45, 0x31, 0xc9, 0x5b, 0x5d, 0x4c, 0x89, 0xc8, 0x41, 0x5c]

theorem p19_0 : ∀ feat, Dec feat p19 0 (FV7z.mk .xor 32 [gr 32 9, Src.opd 32 (.r 9)] 3) := by dec_rfl
theorem p19_3 : ∀ feat, Dec feat p19 3 (FV7z.mk .pop 64 [gr 64 3] 1) := by dec_rfl
theorem p19_4 : ∀ feat, Dec feat p19 4 (FV7z.mk .pop 64 [gr 64 5] 1) := by dec_rfl
theorem p19_5 : ∀ feat, Dec feat p19 5 (FV7z.mk .mov 64 [gr 64 0, Src.opd 64 (.r 9)] 3) := by dec_rfl
theorem p19_8 : ∀ feat, Dec feat p19 8 (FV7z.mk .pop 64 [gr 64 12] 2) := by dec_rfl

/-- What the stretch does. -/
def o19 : List Op := [
  Op.xor 32 9 (.r 9),
  Op.pop 3,
  Op.pop 5,
  Op.mov 64 0 (.r 9),
  Op.pop 12]

theorem b19 (prof : Profile) : Blk prof p19 0 10 o19 :=
  .cons (p19_0 _) (OpI.xor (.r 9) (.inl rfl)) (by decide) <|
  .cons (p19_3 _) (OpI.pop) (by decide) <|
  .cons (p19_4 _) (OpI.pop) (by decide) <|
  .cons (p19_5 _) (OpI.mov (.r 9) (.inr rfl)) (by decide) <|
  .cons (p19_8 _) (OpI.pop) (by decide) <|
  .nil 10

/-- The stretch at `240`. -/
def p20 : List Byte := [
  0xbf, 0x04, 0x00, 0x00, 0x00]

theorem p20_0 : ∀ feat, Dec feat p20 0 (FV7z.mk .mov 32 [gr 32 7, Src.opd 32 (.i 4)] 5) := by dec_rfl

/-- What the stretch does. -/
def o20 : List Op := [
  Op.mov 32 7 (.i 4)]

theorem b20 (prof : Profile) : Blk prof p20 0 5 o20 :=
  .cons (p20_0 _) (OpI.mov (.i 4) (.inl rfl)) (by decide) <|
  .nil 5

def j12 : List Byte := [0x74, 0xde]
theorem j12_0 : ∀ feat, Dec feat j12 0 (FV7z.mk (.jcc 4) 64 [.rel 18446744073709551582] 2) := by dec_rfl

/-- The stretch at `258`. -/
def p21 : List Byte := [
  0x41, 0xc7, 0x01, 0x69, 0x73, 0x6f, 0x00, 0x49, 0x8d, 0x41, 0x03]

theorem p21_0 : ∀ feat, Dec feat p21 0 (FV7z.mk .mov 32 [.mem (mg (some 9) none 1 0 32), .imm 32 7304041] 7) := by dec_rfl
theorem p21_7 : ∀ feat, Dec feat p21 7 (FV7z.mk .lea 64 [gr 64 0, .mem (mg (some 9) none 1 3 0)] 4) := by dec_rfl

/-- What the stretch does. -/
def o21 : List Op := [
  Op.sti 32 (some 9) none 1 0 7304041,
  Op.lea 64 0 (some 9) none 1 3]

theorem b21 (prof : Profile) : Blk prof p21 0 11 o21 :=
  .cons (p21_0 _) (OpI.sti (.inr (.inr (.inl rfl)))) (by decide) <|
  .cons (p21_7 _) (OpI.lea (.inr rfl)) (by decide) <|
  .nil 11

def j13 : List Byte := [0xeb, 0xa5]
theorem j13_0 : ∀ feat, Dec feat j13 0 (FV7z.mk .jmp 64 [.rel 18446744073709551525] 2) := by dec_rfl

end FV7z.Nlc
