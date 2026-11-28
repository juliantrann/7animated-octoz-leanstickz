import FV7z.Lemmas.SpFs
import FV7z.Lemmas.BlkOps28
import FV7z.Lemmas.BlkOps12
import FV7z.Lemmas.BlkOps6
import FV7z.Lemmas.BlkOps3
/-!
# The stretches of straight-line code of `NCommandLineParser::CParser::ParseString` (PLAN.md §M, M1)

Each distinct stretch between labels and jumps (`p*`, 57 of them) and each distinct jump (`j*`, 36) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.Cps
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The stretch at `0`. -/
def p0 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0x41, 0x57, 0x41, 0x56, 0x41, 0x55, 0x41, 0x54]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem p0_4 : ∀ feat, Dec feat p0 4 (FV7z.mk .push 64 [gr 64 15] 2) := by dec_rfl
theorem p0_6 : ∀ feat, Dec feat p0 6 (FV7z.mk .push 64 [gr 64 14] 2) := by dec_rfl
theorem p0_8 : ∀ feat, Dec feat p0 8 (FV7z.mk .push 64 [gr 64 13] 2) := by dec_rfl
theorem p0_10 : ∀ feat, Dec feat p0 10 (FV7z.mk .push 64 [gr 64 12] 2) := by dec_rfl

/-- What the stretch does. -/
def o0 : List Op := [
  Op.nop,
  Op.push 15,
  Op.push 14,
  Op.push 13,
  Op.push 12]

theorem b0 (prof : Profile) : Blk prof p0 0 12 o0 :=
  .cons (p0_0 _) (OpI.endbr) (by decide) <|
  .cons (p0_4 _) (OpI.push) (by decide) <|
  .cons (p0_6 _) (OpI.push) (by decide) <|
  .cons (p0_8 _) (OpI.push) (by decide) <|
  .cons (p0_10 _) (OpI.push) (by decide) <|
  .nil 12

/-- The stretch at `12`. -/
def p1 : List Byte := [
  0x55, 0x53, 0x48, 0x83, 0xec, 0x48, 0x48, 0x89, 0x7c, 0x24, 0x18, 0x48, 0x89, 0x54, 0x24, 0x10]

theorem p1_0 : ∀ feat, Dec feat p1 0 (FV7z.mk .push 64 [gr 64 5] 1) := by dec_rfl
theorem p1_1 : ∀ feat, Dec feat p1 1 (FV7z.mk .push 64 [gr 64 3] 1) := by dec_rfl
theorem p1_2 : ∀ feat, Dec feat p1 2 (FV7z.mk .sub 64 [gr 64 4, Src.opd 64 (.i 72)] 4) := by dec_rfl
theorem p1_6 : ∀ feat, Dec feat p1 6 (FV7z.mk .mov 64 [.mem (mg (some 4) none 1 24 64), gr 64 7] 5) := by dec_rfl
theorem p1_11 : ∀ feat, Dec feat p1 11 (FV7z.mk .mov 64 [.mem (mg (some 4) none 1 16 64), gr 64 2] 5) := by dec_rfl

/-- What the stretch does. -/
def o1 : List Op := [
  Op.push 5,
  Op.push 3,
  Op.sub 64 4 (.i 72),
  Op.st 64 (some 4) none 1 24 7,
  Op.st 64 (some 4) none 1 16 2]

theorem b1 (prof : Profile) : Blk prof p1 0 16 o1 :=
  .cons (p1_0 _) (OpI.push) (by decide) <|
  .cons (p1_1 _) (OpI.push) (by decide) <|
  .cons (p1_2 _) (OpI.sub (.i 72) (.inr rfl)) (by decide) <|
  .cons (p1_6 _) (OpI.st (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p1_11 _) (OpI.st (.inr (.inr (.inr rfl)))) (by decide) <|
  .nil 16

/-- The stretch at `28`. -/
def p2 : List Byte := [
  0x64, 0x48, 0x8b, 0x04, 0x25, 0x28, 0x00, 0x00, 0x00, 0x48, 0x89, 0x44, 0x24, 0x38, 0x31, 0xc0,
  0x8b, 0x46, 0x08, 0x85, 0xc0]

theorem p2_0 : ∀ feat, Dec feat p2 0 (FV7z.mk .mov 64 [gr 64 0, .mem (mf none none 1 40 64)] 9) := by dec_rfl
theorem p2_9 : ∀ feat, Dec feat p2 9 (FV7z.mk .mov 64 [.mem (mg (some 4) none 1 56 64), gr 64 0] 5) := by dec_rfl
theorem p2_14 : ∀ feat, Dec feat p2 14 (FV7z.mk .xor 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl
theorem p2_16 : ∀ feat, Dec feat p2 16 (FV7z.mk .mov 32 [gr 32 0, .mem (mg (some 6) none 1 8 32)] 3) := by dec_rfl
theorem p2_19 : ∀ feat, Dec feat p2 19 (FV7z.mk .test 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl

/-- What the stretch does. -/
def o2 (fb : Addr) : List Op := [
  Op.ldf fb 64 0 none none 1 40,
  Op.st 64 (some 4) none 1 56 0,
  Op.xor 32 0 (.r 0),
  Op.ld 32 0 (some 6) none 1 8,
  Op.test 32 0 (.r 0)]

theorem b2 (prof : Profile) (fb : Addr) : BlkF prof p2 (0x5a066c : Addr) fb 0 21 (o2 fb) :=
  .cons (p2_0 _) (OpIF.ldf (.inr rfl)) (by decide) <|
  .cons (p2_9 _) (((OpI.st (.inr (.inr (.inr rfl)))).at _).fs _) (by decide) <|
  .cons (p2_14 _) (((OpI.xor (.r 0) (.inl rfl)).at _).fs _) (by decide) <|
  .cons (p2_16 _) (((OpI.ld (.inl rfl)).at _).fs _) (by decide) <|
  .cons (p2_19 _) (((OpI.test (.r 0) (.inl rfl)).at _).fs _) (by decide) <|
  .nil 21

def j0 : List Byte := [0x0f, 0x84, 0x11, 0x01, 0x00, 0x00]
theorem j0_0 : ∀ feat, Dec feat j0 0 (FV7z.mk (.jcc 4) 64 [.rel 273] 6) := by dec_rfl

/-- The stretch at `55`. -/
def p3 : List Byte := [
  0x48, 0x8b, 0x06, 0x49, 0x89, 0xf6, 0x83, 0x38, 0x2d]

theorem p3_0 : ∀ feat, Dec feat p3 0 (FV7z.mk .mov 64 [gr 64 0, .mem (mg (some 6) none 1 0 64)] 3) := by dec_rfl
theorem p3_3 : ∀ feat, Dec feat p3 3 (FV7z.mk .mov 64 [gr 64 14, Src.opd 64 (.r 6)] 3) := by dec_rfl
theorem p3_6 : ∀ feat, Dec feat p3 6 (FV7z.mk .cmp 32 [.mem (mg (some 0) none 1 0 32), .imm 32 45] 3) := by dec_rfl

/-- What the stretch does. -/
def o3 : List Op := [
  Op.ld 64 0 (some 6) none 1 0,
  Op.mov 64 14 (.r 6),
  Op.cmpmi 32 (some 0) none 1 0 45]

theorem b3 (prof : Profile) : Blk prof p3 0 9 o3 :=
  .cons (p3_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p3_3 _) (OpI.mov (.r 6) (.inr rfl)) (by decide) <|
  .cons (p3_6 _) (OpI.cmpmi (.inr rfl)) (by decide) <|
  .nil 9

def j1 : List Byte := [0x0f, 0x85, 0x02, 0x01, 0x00, 0x00]
theorem j1_0 : ∀ feat, Dec feat j1 0 (FV7z.mk (.jcc 5) 64 [.rel 258] 6) := by dec_rfl

/-- The stretch at `70`. -/
def p4 : List Byte := [
  0x85, 0xc9]

theorem p4_0 : ∀ feat, Dec feat p4 0 (FV7z.mk .test 32 [gr 32 1, Src.opd 32 (.r 1)] 2) := by dec_rfl

/-- What the stretch does. -/
def o4 : List Op := [
  Op.test 32 1 (.r 1)]

theorem b4 (prof : Profile) : Blk prof p4 0 2 o4 :=
  .cons (p4_0 _) (OpI.test (.r 1) (.inl rfl)) (by decide) <|
  .nil 2

def j2 : List Byte := [0x0f, 0x84, 0x91, 0x02, 0x00, 0x00]
theorem j2_0 : ∀ feat, Dec feat j2 0 (FV7z.mk (.jcc 4) 64 [.rel 657] 6) := by dec_rfl

/-- The stretch at `78`. -/
def p5 : List Byte := [
  0x4c, 0x8b, 0x6c, 0x24, 0x10, 0x45, 0x31, 0xe4, 0x41, 0xbf, 0xff, 0xff, 0xff, 0xff, 0x31, 0xed,
  0x66, 0x90]

theorem p5_0 : ∀ feat, Dec feat p5 0 (FV7z.mk .mov 64 [gr 64 13, .mem (mg (some 4) none 1 16 64)] 5) := by dec_rfl
theorem p5_5 : ∀ feat, Dec feat p5 5 (FV7z.mk .xor 32 [gr 32 12, Src.opd 32 (.r 12)] 3) := by dec_rfl
theorem p5_8 : ∀ feat, Dec feat p5 8 (FV7z.mk .mov 32 [gr 32 15, Src.opd 32 (.i 4294967295)] 6) := by dec_rfl
theorem p5_14 : ∀ feat, Dec feat p5 14 (FV7z.mk .xor 32 [gr 32 5, Src.opd 32 (.r 5)] 2) := by dec_rfl
theorem p5_16 : ∀ feat, Dec feat p5 16 (FV7z.mk .nop 16 [] 2) := by dec_rfl

/-- What the stretch does. -/
def o5 : List Op := [
  Op.ld 64 13 (some 4) none 1 16,
  Op.xor 32 12 (.r 12),
  Op.mov 32 15 (.i 4294967295),
  Op.xor 32 5 (.r 5),
  Op.nop]

theorem b5 (prof : Profile) : Blk prof p5 0 18 o5 :=
  .cons (p5_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p5_5 _) (OpI.xor (.r 12) (.inl rfl)) (by decide) <|
  .cons (p5_8 _) (OpI.mov (.i 4294967295) (.inl rfl)) (by decide) <|
  .cons (p5_14 _) (OpI.xor (.r 5) (.inl rfl)) (by decide) <|
  .cons (p5_16 _) (OpI.nop) (by decide) <|
  .nil 18

/-- The stretch at `96`. -/
def p6 : List Byte := [
  0x49, 0x8b, 0x75, 0x00, 0x80, 0x3e, 0x00]

theorem p6_0 : ∀ feat, Dec feat p6 0 (FV7z.mk .mov 64 [gr 64 6, .mem (mg (some 13) none 1 0 64)] 4) := by dec_rfl
theorem p6_4 : ∀ feat, Dec feat p6 4 (FV7z.mk .cmp 8 [.mem (mg (some 6) none 1 0 8), .imm 8 0] 3) := by dec_rfl

/-- What the stretch does. -/
def o6 : List Op := [
  Op.ld 64 6 (some 13) none 1 0,
  Op.cmpmi 8 (some 6) none 1 0 0]

theorem b6 (prof : Profile) : Blk prof p6 0 7 o6 :=
  .cons (p6_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p6_4 _) (OpI.cmpmi (.inl rfl)) (by decide) <|
  .nil 7

def j3 : List Byte := [0x0f, 0x84, 0x0b, 0x01, 0x00, 0x00]
theorem j3_0 : ∀ feat, Dec feat j3 0 (FV7z.mk (.jcc 4) 64 [.rel 267] 6) := by dec_rfl

/-- The stretch at `109`. -/
def p7 : List Byte := [
  0x31, 0xc0, 0x90]

theorem p7_0 : ∀ feat, Dec feat p7 0 (FV7z.mk .xor 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl
theorem p7_2 : ∀ feat, Dec feat p7 2 (FV7z.mk .nop 32 [] 1) := by dec_rfl

/-- What the stretch does. -/
def o7 : List Op := [
  Op.xor 32 0 (.r 0),
  Op.nop]

theorem b7 (prof : Profile) : Blk prof p7 0 3 o7 :=
  .cons (p7_0 _) (OpI.xor (.r 0) (.inl rfl)) (by decide) <|
  .cons (p7_2 _) (OpI.nop) (by decide) <|
  .nil 3

/-- The stretch at `112`. -/
def p8 : List Byte := [
  0x8d, 0x50, 0x01, 0x80, 0x3c, 0x16, 0x00, 0x48, 0x89, 0xd0]

theorem p8_0 : ∀ feat, Dec feat p8 0 (FV7z.mk .lea 32 [gr 32 2, .mem (mg (some 0) none 1 1 0)] 3) := by dec_rfl
theorem p8_3 : ∀ feat, Dec feat p8 3 (FV7z.mk .cmp 8 [.mem (mg (some 6) (some 2) 1 0 8), .imm 8 0] 4) := by dec_rfl
theorem p8_7 : ∀ feat, Dec feat p8 7 (FV7z.mk .mov 64 [gr 64 0, Src.opd 64 (.r 2)] 3) := by dec_rfl

/-- What the stretch does. -/
def o8 : List Op := [
  Op.lea 32 2 (some 0) none 1 1,
  Op.cmpmi 8 (some 6) (some 2) 1 0 0,
  Op.mov 64 0 (.r 2)]

theorem b8 (prof : Profile) : Blk prof p8 0 10 o8 :=
  .cons (p8_0 _) (OpI.lea (.inl rfl)) (by decide) <|
  .cons (p8_3 _) (OpI.cmpmi (.inl rfl)) (by decide) <|
  .cons (p8_7 _) (OpI.mov (.r 2) (.inr rfl)) (by decide) <|
  .nil 10

def j4 : List Byte := [0x75, 0xf4]
theorem j4_0 : ∀ feat, Dec feat j4 0 (FV7z.mk (.jcc 5) 64 [.rel 18446744073709551604] 2) := by dec_rfl

/-- The stretch at `124`. -/
def p9 : List Byte := [
  0x89, 0xd3]

theorem p9_0 : ∀ feat, Dec feat p9 0 (FV7z.mk .mov 32 [gr 32 3, Src.opd 32 (.r 2)] 2) := by dec_rfl

/-- What the stretch does. -/
def o9 : List Op := [
  Op.mov 32 3 (.r 2)]

theorem b9 (prof : Profile) : Blk prof p9 0 2 o9 :=
  .cons (p9_0 _) (OpI.mov (.r 2) (.inl rfl)) (by decide) <|
  .nil 2

/-- The stretch at `126`. -/
def p10 : List Byte := [
  0x44, 0x39, 0xfb]

theorem p10_0 : ∀ feat, Dec feat p10 0 (FV7z.mk .cmp 32 [gr 32 3, Src.opd 32 (.r 15)] 3) := by dec_rfl

/-- What the stretch does. -/
def o10 : List Op := [
  Op.cmp 32 3 (.r 15)]

theorem b10 (prof : Profile) : Blk prof p10 0 3 o10 :=
  .cons (p10_0 _) (OpI.cmp (.r 15) (.inl rfl)) (by decide) <|
  .nil 3

def j5 : List Byte := [0x7e, 0x27]
theorem j5_0 : ∀ feat, Dec feat j5 0 (FV7z.mk (.jcc 14) 64 [.rel 39] 2) := by dec_rfl

/-- The stretch at `131`. -/
def p11 : List Byte := [
  0x83, 0xc0, 0x01, 0x41, 0x3b, 0x46, 0x08]

theorem p11_0 : ∀ feat, Dec feat p11 0 (FV7z.mk .add 32 [gr 32 0, Src.opd 32 (.i 1)] 3) := by dec_rfl
theorem p11_3 : ∀ feat, Dec feat p11 3 (FV7z.mk .cmp 32 [gr 32 0, .mem (mg (some 14) none 1 8 32)] 4) := by dec_rfl

/-- What the stretch does. -/
def o11 : List Op := [
  Op.add 32 0 (.i 1),
  Op.cmpm 32 0 (some 14) none 1 8]

theorem b11 (prof : Profile) : Blk prof p11 0 7 o11 :=
  .cons (p11_0 _) (OpI.add (.i 1) (.inl rfl)) (by decide) <|
  .cons (p11_3 _) (OpI.cmpm (.inl rfl)) (by decide) <|
  .nil 7

def j6 : List Byte := [0x77, 0x1e]
theorem j6_0 : ∀ feat, Dec feat j6 0 (FV7z.mk (.jcc 7) 64 [.rel 30] 2) := by dec_rfl

/-- The stretch at `140`. -/
def p12 : List Byte := [
  0x49, 0x8b, 0x06, 0x89, 0x4c, 0x24, 0x0c, 0x48, 0x8d, 0x78, 0x04]

theorem p12_0 : ∀ feat, Dec feat p12 0 (FV7z.mk .mov 64 [gr 64 0, .mem (mg (some 14) none 1 0 64)] 3) := by dec_rfl
theorem p12_3 : ∀ feat, Dec feat p12 3 (FV7z.mk .mov 32 [.mem (mg (some 4) none 1 12 32), gr 32 1] 4) := by dec_rfl
theorem p12_7 : ∀ feat, Dec feat p12 7 (FV7z.mk .lea 64 [gr 64 7, .mem (mg (some 0) none 1 4 0)] 4) := by dec_rfl

/-- What the stretch does. -/
def o12 : List Op := [
  Op.ld 64 0 (some 14) none 1 0,
  Op.st 32 (some 4) none 1 12 1,
  Op.lea 64 7 (some 0) none 1 4]

theorem b12 (prof : Profile) : Blk prof p12 0 11 o12 :=
  .cons (p12_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p12_3 _) (OpI.st (.inr (.inr (.inl rfl)))) (by decide) <|
  .cons (p12_7 _) (OpI.lea (.inr rfl)) (by decide) <|
  .nil 11

/-- The stretch at `156`. -/
def p13 : List Byte := [
  0x8b, 0x4c, 0x24, 0x0c, 0x84, 0xc0, 0x44, 0x0f, 0x45, 0xfb, 0x41, 0x0f, 0x45, 0xec]

theorem p13_0 : ∀ feat, Dec feat p13 0 (FV7z.mk .mov 32 [gr 32 1, .mem (mg (some 4) none 1 12 32)] 4) := by dec_rfl
theorem p13_4 : ∀ feat, Dec feat p13 4 (FV7z.mk .test 8 [gr 8 0, Src.opd 8 (.r 0)] 2) := by dec_rfl
theorem p13_6 : ∀ feat, Dec feat p13 6 (FV7z.mk (.cmovcc 5) 32 [gr 32 15, gr 32 3] 4) := by dec_rfl
theorem p13_10 : ∀ feat, Dec feat p13 10 (FV7z.mk (.cmovcc 5) 32 [gr 32 5, gr 32 12] 4) := by dec_rfl

/-- What the stretch does. -/
def o13 : List Op := [
  Op.ld 32 1 (some 4) none 1 12,
  Op.test 8 0 (.r 0),
  Op.cmov32 5 15 3,
  Op.cmov32 5 5 12]

theorem b13 (prof : Profile) : Blk prof p13 0 14 o13 :=
  .cons (p13_0 _) (OpI.ld (.inl rfl)) (by decide) <|
  .cons (p13_4 _) (OpI.test8 (.r 0)) (by decide) <|
  .cons (p13_6 _) (OpI.cmov32) (by decide) <|
  .cons (p13_10 _) (OpI.cmov32) (by decide) <|
  .nil 14

/-- The stretch at `170`. -/
def p14 : List Byte := [
  0x41, 0x83, 0xc4, 0x01, 0x49, 0x83, 0xc5, 0x18, 0x44, 0x39, 0xe1]

theorem p14_0 : ∀ feat, Dec feat p14 0 (FV7z.mk .add 32 [gr 32 12, Src.opd 32 (.i 1)] 4) := by dec_rfl
theorem p14_4 : ∀ feat, Dec feat p14 4 (FV7z.mk .add 64 [gr 64 13, Src.opd 64 (.i 24)] 4) := by dec_rfl
theorem p14_8 : ∀ feat, Dec feat p14 8 (FV7z.mk .cmp 32 [gr 32 1, Src.opd 32 (.r 12)] 3) := by dec_rfl

/-- What the stretch does. -/
def o14 : List Op := [
  Op.add 32 12 (.i 1),
  Op.add 64 13 (.i 24),
  Op.cmp 32 1 (.r 12)]

theorem b14 (prof : Profile) : Blk prof p14 0 11 o14 :=
  .cons (p14_0 _) (OpI.add (.i 1) (.inl rfl)) (by decide) <|
  .cons (p14_4 _) (OpI.add (.i 24) (.inr rfl)) (by decide) <|
  .cons (p14_8 _) (OpI.cmp (.r 12) (.inl rfl)) (by decide) <|
  .nil 11

def j7 : List Byte := [0x75, 0xa9]
theorem j7_0 : ∀ feat, Dec feat j7 0 (FV7z.mk (.jcc 5) 64 [.rel 18446744073709551529] 2) := by dec_rfl

/-- The stretch at `183`. -/
def p15 : List Byte := [
  0x41, 0x83, 0xff, 0xff]

theorem p15_0 : ∀ feat, Dec feat p15 0 (FV7z.mk .cmp 32 [gr 32 15, Src.opd 32 (.i 4294967295)] 4) := by dec_rfl

/-- What the stretch does. -/
def o15 : List Op := [
  Op.cmp 32 15 (.i 4294967295)]

theorem b15 (prof : Profile) : Blk prof p15 0 4 o15 :=
  .cons (p15_0 _) (OpI.cmp (.i 4294967295) (.inl rfl)) (by decide) <|
  .nil 4

def j8 : List Byte := [0x0f, 0x84, 0x1e, 0x02, 0x00, 0x00]
theorem j8_0 : ∀ feat, Dec feat j8 0 (FV7z.mk (.jcc 4) 64 [.rel 542] 6) := by dec_rfl

/-- The stretch at `193`. -/
def p16 : List Byte := [
  0x41, 0x89, 0xe8, 0x48, 0x8b, 0x5c, 0x24, 0x10, 0x48, 0x8b, 0x7c, 0x24, 0x18]

theorem p16_0 : ∀ feat, Dec feat p16 0 (FV7z.mk .mov 32 [gr 32 8, Src.opd 32 (.r 5)] 3) := by dec_rfl
theorem p16_3 : ∀ feat, Dec feat p16 3 (FV7z.mk .mov 64 [gr 64 3, .mem (mg (some 4) none 1 16 64)] 5) := by dec_rfl
theorem p16_8 : ∀ feat, Dec feat p16 8 (FV7z.mk .mov 64 [gr 64 7, .mem (mg (some 4) none 1 24 64)] 5) := by dec_rfl

/-- What the stretch does. -/
def o16 : List Op := [
  Op.mov 32 8 (.r 5),
  Op.ld 64 3 (some 4) none 1 16,
  Op.ld 64 7 (some 4) none 1 24]

theorem b16 (prof : Profile) : Blk prof p16 0 13 o16 :=
  .cons (p16_0 _) (OpI.mov (.r 5) (.inl rfl)) (by decide) <|
  .cons (p16_3 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p16_8 _) (OpI.ld (.inr rfl)) (by decide) <|
  .nil 13

/-- The stretch at `206`. -/
def p17 : List Byte := [
  0x41, 0x83, 0xc7, 0x01, 0x4b, 0x8d, 0x04, 0x40, 0x48, 0xc1, 0xe0, 0x03, 0x4c, 0x8b, 0x27]

theorem p17_0 : ∀ feat, Dec feat p17 0 (FV7z.mk .add 32 [gr 32 15, Src.opd 32 (.i 1)] 4) := by dec_rfl
theorem p17_4 : ∀ feat, Dec feat p17 4 (FV7z.mk .lea 64 [gr 64 0, .mem (mg (some 8) (some 8) 2 0 0)] 4) := by dec_rfl
theorem p17_8 : ∀ feat, Dec feat p17 8 (FV7z.mk .shl 64 [gr 64 0, Src.opd 8 (.i 3)] 4) := by dec_rfl
theorem p17_12 : ∀ feat, Dec feat p17 12 (FV7z.mk .mov 64 [gr 64 12, .mem (mg (some 7) none 1 0 64)] 3) := by dec_rfl

/-- What the stretch does. -/
def o17 : List Op := [
  Op.add 32 15 (.i 1),
  Op.lea 64 0 (some 8) (some 8) 2 0,
  Op.shl64 0 (.i 3),
  Op.ld 64 12 (some 7) none 1 0]

theorem b17 (prof : Profile) : Blk prof p17 0 15 o17 :=
  .cons (p17_0 _) (OpI.add (.i 1) (.inl rfl)) (by decide) <|
  .cons (p17_4 _) (OpI.lea (.inr rfl)) (by decide) <|
  .cons (p17_8 _) (OpI.shl64 (.i 3)) (by decide) <|
  .cons (p17_12 _) (OpI.ld (.inr rfl)) (by decide) <|
  .nil 15

/-- The stretch at `221`. -/
def p18 : List Byte := [
  0x48, 0x01, 0xc3, 0x44, 0x0f, 0xb6, 0x6b, 0x09, 0x49, 0x01, 0xc4, 0x45, 0x84, 0xed]

theorem p18_0 : ∀ feat, Dec feat p18 0 (FV7z.mk .add 64 [gr 64 3, Src.opd 64 (.r 0)] 3) := by dec_rfl
theorem p18_3 : ∀ feat, Dec feat p18 3 (FV7z.mk .movzx 32 [gr 32 13, .mem (mg (some 3) none 1 9 8)] 5) := by dec_rfl
theorem p18_8 : ∀ feat, Dec feat p18 8 (FV7z.mk .add 64 [gr 64 12, Src.opd 64 (.r 0)] 3) := by dec_rfl
theorem p18_11 : ∀ feat, Dec feat p18 11 (FV7z.mk .test 8 [gr 8 13, Src.opd 8 (.r 13)] 3) := by dec_rfl

/-- What the stretch does. -/
def o18 : List Op := [
  Op.add 64 3 (.r 0),
  Op.ldzx 8 13 (some 3) none 1 9,
  Op.add 64 12 (.r 0),
  Op.test 8 13 (.r 13)]

theorem b18 (prof : Profile) : Blk prof p18 0 14 o18 :=
  .cons (p18_0 _) (OpI.add (.r 0) (.inr rfl)) (by decide) <|
  .cons (p18_3 _) (OpI.ldzx (.inl rfl)) (by decide) <|
  .cons (p18_8 _) (OpI.add (.r 0) (.inr rfl)) (by decide) <|
  .cons (p18_11 _) (OpI.test8 (.r 13)) (by decide) <|
  .nil 14

def j9 : List Byte := [0x0f, 0x84, 0x90, 0x00, 0x00, 0x00]
theorem j9_0 : ∀ feat, Dec feat j9 0 (FV7z.mk (.jcc 4) 64 [.rel 144] 6) := by dec_rfl

/-- The stretch at `241`. -/
def p19 : List Byte := [
  0x41, 0x8b, 0x46, 0x08, 0x41, 0xc6, 0x04, 0x24, 0x01, 0x0f, 0xb6, 0x53, 0x0a, 0x44, 0x29, 0xf8,
  0x39, 0xc2]

theorem p19_0 : ∀ feat, Dec feat p19 0 (FV7z.mk .mov 32 [gr 32 0, .mem (mg (some 14) none 1 8 32)] 4) := by dec_rfl
theorem p19_4 : ∀ feat, Dec feat p19 4 (FV7z.mk .mov 8 [.mem (mg (some 12) none 1 0 8), .imm 8 1] 5) := by dec_rfl
theorem p19_9 : ∀ feat, Dec feat p19 9 (FV7z.mk .movzx 32 [gr 32 2, .mem (mg (some 3) none 1 10 8)] 4) := by dec_rfl
theorem p19_13 : ∀ feat, Dec feat p19 13 (FV7z.mk .sub 32 [gr 32 0, Src.opd 32 (.r 15)] 3) := by dec_rfl
theorem p19_16 : ∀ feat, Dec feat p19 16 (FV7z.mk .cmp 32 [gr 32 2, Src.opd 32 (.r 0)] 2) := by dec_rfl

/-- What the stretch does. -/
def o19 : List Op := [
  Op.ld 32 0 (some 14) none 1 8,
  Op.sti 8 (some 12) none 1 0 1,
  Op.ldzx 8 2 (some 3) none 1 10,
  Op.sub 32 0 (.r 15),
  Op.cmp 32 2 (.r 0)]

theorem b19 (prof : Profile) : Blk prof p19 0 18 o19 :=
  .cons (p19_0 _) (OpI.ld (.inl rfl)) (by decide) <|
  .cons (p19_4 _) (OpI.sti (.inl rfl)) (by decide) <|
  .cons (p19_9 _) (OpI.ldzx (.inl rfl)) (by decide) <|
  .cons (p19_13 _) (OpI.sub (.r 15) (.inl rfl)) (by decide) <|
  .cons (p19_16 _) (OpI.cmp (.r 0) (.inl rfl)) (by decide) <|
  .nil 18

def j10 : List Byte := [0x0f, 0x87, 0xb9, 0x01, 0x00, 0x00]
theorem j10_0 : ∀ feat, Dec feat j10 0 (FV7z.mk (.jcc 7) 64 [.rel 441] 6) := by dec_rfl

/-- The stretch at `265`. -/
def p20 : List Byte := [
  0x41, 0xc6, 0x44, 0x24, 0x01, 0x00, 0x41, 0xc7, 0x44, 0x24, 0x04, 0xff, 0xff, 0xff, 0xff, 0x0f,
  0xb6, 0x53, 0x08, 0x80, 0xfa, 0x02]

theorem p20_0 : ∀ feat, Dec feat p20 0 (FV7z.mk .mov 8 [.mem (mg (some 12) none 1 1 8), .imm 8 0] 6) := by dec_rfl
theorem p20_6 : ∀ feat, Dec feat p20 6 (FV7z.mk .mov 32 [.mem (mg (some 12) none 1 4 32), .imm 32 4294967295] 9) := by dec_rfl
theorem p20_15 : ∀ feat, Dec feat p20 15 (FV7z.mk .movzx 32 [gr 32 2, .mem (mg (some 3) none 1 8 8)] 4) := by dec_rfl
theorem p20_19 : ∀ feat, Dec feat p20 19 (FV7z.mk .cmp 8 [gr 8 2, Src.opd 8 (.i 2)] 3) := by dec_rfl

/-- What the stretch does. -/
def o20 : List Op := [
  Op.sti 8 (some 12) none 1 1 0,
  Op.sti 32 (some 12) none 1 4 4294967295,
  Op.ldzx 8 2 (some 3) none 1 8,
  Op.cmp 8 2 (.i 2)]

theorem b20 (prof : Profile) : Blk prof p20 0 22 o20 :=
  .cons (p20_0 _) (OpI.sti (.inl rfl)) (by decide) <|
  .cons (p20_6 _) (OpI.sti (.inr (.inr (.inl rfl)))) (by decide) <|
  .cons (p20_15 _) (OpI.ldzx (.inl rfl)) (by decide) <|
  .cons (p20_19 _) (OpI.cmp8 (.i 2)) (by decide) <|
  .nil 22

def j11 : List Byte := [0x0f, 0x84, 0xdd, 0x00, 0x00, 0x00]
theorem j11_0 : ∀ feat, Dec feat j11 0 (FV7z.mk (.jcc 4) 64 [.rel 221] 6) := by dec_rfl

/-- The stretch at `293`. -/
def p21 : List Byte := [
  0x80, 0xfa, 0x03]

theorem p21_0 : ∀ feat, Dec feat p21 0 (FV7z.mk .cmp 8 [gr 8 2, Src.opd 8 (.i 3)] 3) := by dec_rfl

/-- What the stretch does. -/
def o21 : List Op := [
  Op.cmp 8 2 (.i 3)]

theorem b21 (prof : Profile) : Blk prof p21 0 3 o21 :=
  .cons (p21_0 _) (OpI.cmp8 (.i 3)) (by decide) <|
  .nil 3

def j12 : List Byte := [0x0f, 0x84, 0x89, 0x00, 0x00, 0x00]
theorem j12_0 : ∀ feat, Dec feat j12 0 (FV7z.mk (.jcc 4) 64 [.rel 137] 6) := by dec_rfl

/-- The stretch at `302`. -/
def p22 : List Byte := [
  0x80, 0xfa, 0x01]

theorem p22_0 : ∀ feat, Dec feat p22 0 (FV7z.mk .cmp 8 [gr 8 2, Src.opd 8 (.i 1)] 3) := by dec_rfl

/-- What the stretch does. -/
def o22 : List Op := [
  Op.cmp 8 2 (.i 1)]

theorem b22 (prof : Profile) : Blk prof p22 0 3 o22 :=
  .cons (p22_0 _) (OpI.cmp8 (.i 1)) (by decide) <|
  .nil 3

def j13 : List Byte := [0x74, 0x6b]
theorem j13_0 : ∀ feat, Dec feat j13 0 (FV7z.mk (.jcc 4) 64 [.rel 107] 2) := by dec_rfl

/-- The stretch at `307`. -/
def p23 : List Byte := [
  0x45, 0x3b, 0x7e, 0x08]

theorem p23_0 : ∀ feat, Dec feat p23 0 (FV7z.mk .cmp 32 [gr 32 15, .mem (mg (some 14) none 1 8 32)] 4) := by dec_rfl

/-- What the stretch does. -/
def o23 : List Op := [
  Op.cmpm 32 15 (some 14) none 1 8]

theorem b23 (prof : Profile) : Blk prof p23 0 4 o23 :=
  .cons (p23_0 _) (OpI.cmpm (.inl rfl)) (by decide) <|
  .nil 4

def j14 : List Byte := [0x0f, 0x85, 0xbf, 0x01, 0x00, 0x00]
theorem j14_0 : ∀ feat, Dec feat j14 0 (FV7z.mk (.jcc 5) 64 [.rel 447] 6) := by dec_rfl

/-- The stretch at `317`. -/
def p24 : List Byte := [
  0x41, 0xbd, 0x01, 0x00, 0x00, 0x00]

theorem p24_0 : ∀ feat, Dec feat p24 0 (FV7z.mk .mov 32 [gr 32 13, Src.opd 32 (.i 1)] 6) := by dec_rfl

/-- What the stretch does. -/
def o24 : List Op := [
  Op.mov 32 13 (.i 1)]

theorem b24 (prof : Profile) : Blk prof p24 0 6 o24 :=
  .cons (p24_0 _) (OpI.mov (.i 1) (.inl rfl)) (by decide) <|
  .nil 6

def j15 : List Byte := [0xeb, 0x06]
theorem j15_0 : ∀ feat, Dec feat j15 0 (FV7z.mk .jmp 64 [.rel 6] 2) := by dec_rfl

/-- The stretch at `328`. -/
def p25 : List Byte := [
  0x45, 0x31, 0xed]

theorem p25_0 : ∀ feat, Dec feat p25 0 (FV7z.mk .xor 32 [gr 32 13, Src.opd 32 (.r 13)] 3) := by dec_rfl

/-- What the stretch does. -/
def o25 : List Op := [
  Op.xor 32 13 (.r 13)]

theorem b25 (prof : Profile) : Blk prof p25 0 3 o25 :=
  .cons (p25_0 _) (OpI.xor (.r 13) (.inl rfl)) (by decide) <|
  .nil 3

/-- The stretch at `331`. -/
def p26 : List Byte := [
  0x48, 0x8b, 0x44, 0x24, 0x38, 0x64, 0x48, 0x33, 0x04, 0x25, 0x28, 0x00, 0x00, 0x00]

theorem p26_0 : ∀ feat, Dec feat p26 0 (FV7z.mk .mov 64 [gr 64 0, .mem (mg (some 4) none 1 56 64)] 5) := by dec_rfl
theorem p26_5 : ∀ feat, Dec feat p26 5 (FV7z.mk .xor 64 [gr 64 0, .mem (mf none none 1 40 64)] 9) := by dec_rfl

/-- What the stretch does. -/
def o26 (fb : Addr) : List Op := [
  Op.ld 64 0 (some 4) none 1 56,
  Op.xormf fb 64 0 none none 1 40]

theorem b26 (prof : Profile) (fb : Addr) : BlkF prof p26 (0x5a079b : Addr) fb 0 14 (o26 fb) :=
  .cons (p26_0 _) (((OpI.ld (.inr rfl)).at _).fs _) (by decide) <|
  .cons (p26_5 _) (OpIF.xormf (.inr rfl)) (by decide) <|
  .nil 14

def j16 : List Byte := [0x0f, 0x85, 0xd4, 0x01, 0x00, 0x00]
theorem j16_0 : ∀ feat, Dec feat j16 0 (FV7z.mk (.jcc 5) 64 [.rel 468] 6) := by dec_rfl

/-- The stretch at `351`. -/
def p27 : List Byte := [
  0x48, 0x83, 0xc4, 0x48, 0x44, 0x89, 0xe8, 0x5b]

theorem p27_0 : ∀ feat, Dec feat p27 0 (FV7z.mk .add 64 [gr 64 4, Src.opd 64 (.i 72)] 4) := by dec_rfl
theorem p27_4 : ∀ feat, Dec feat p27 4 (FV7z.mk .mov 32 [gr 32 0, Src.opd 32 (.r 13)] 3) := by dec_rfl
theorem p27_7 : ∀ feat, Dec feat p27 7 (FV7z.mk .pop 64 [gr 64 3] 1) := by dec_rfl

/-- What the stretch does. -/
def o27 : List Op := [
  Op.add 64 4 (.i 72),
  Op.mov 32 0 (.r 13),
  Op.pop 3]

theorem b27 (prof : Profile) : Blk prof p27 0 8 o27 :=
  .cons (p27_0 _) (OpI.add (.i 72) (.inr rfl)) (by decide) <|
  .cons (p27_4 _) (OpI.mov (.r 13) (.inl rfl)) (by decide) <|
  .cons (p27_7 _) (OpI.pop) (by decide) <|
  .nil 8

/-- The stretch at `359`. -/
def p28 : List Byte := [
  0x5d, 0x41, 0x5c, 0x41, 0x5d, 0x41, 0x5e, 0x41, 0x5f]

theorem p28_0 : ∀ feat, Dec feat p28 0 (FV7z.mk .pop 64 [gr 64 5] 1) := by dec_rfl
theorem p28_1 : ∀ feat, Dec feat p28 1 (FV7z.mk .pop 64 [gr 64 12] 2) := by dec_rfl
theorem p28_3 : ∀ feat, Dec feat p28 3 (FV7z.mk .pop 64 [gr 64 13] 2) := by dec_rfl
theorem p28_5 : ∀ feat, Dec feat p28 5 (FV7z.mk .pop 64 [gr 64 14] 2) := by dec_rfl
theorem p28_7 : ∀ feat, Dec feat p28 7 (FV7z.mk .pop 64 [gr 64 15] 2) := by dec_rfl

/-- What the stretch does. -/
def o28 : List Op := [
  Op.pop 5,
  Op.pop 12,
  Op.pop 13,
  Op.pop 14,
  Op.pop 15]

theorem b28 (prof : Profile) : Blk prof p28 0 9 o28 :=
  .cons (p28_0 _) (OpI.pop) (by decide) <|
  .cons (p28_1 _) (OpI.pop) (by decide) <|
  .cons (p28_3 _) (OpI.pop) (by decide) <|
  .cons (p28_5 _) (OpI.pop) (by decide) <|
  .cons (p28_7 _) (OpI.pop) (by decide) <|
  .nil 9

/-- The stretch at `376`. -/
def p29 : List Byte := [
  0x31, 0xdb, 0x31, 0xc0]

theorem p29_0 : ∀ feat, Dec feat p29 0 (FV7z.mk .xor 32 [gr 32 3, Src.opd 32 (.r 3)] 2) := by dec_rfl
theorem p29_2 : ∀ feat, Dec feat p29 2 (FV7z.mk .xor 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl

/-- What the stretch does. -/
def o29 : List Op := [
  Op.xor 32 3 (.r 3),
  Op.xor 32 0 (.r 0)]

theorem b29 (prof : Profile) : Blk prof p29 0 4 o29 :=
  .cons (p29_0 _) (OpI.xor (.r 3) (.inl rfl)) (by decide) <|
  .cons (p29_2 _) (OpI.xor (.r 0) (.inl rfl)) (by decide) <|
  .nil 4

def j17 : List Byte := [0xe9, 0xfd, 0xfe, 0xff, 0xff]
theorem j17_0 : ∀ feat, Dec feat j17 0 (FV7z.mk .jmp 64 [.rel 18446744073709551357] 5) := by dec_rfl

/-- The stretch at `385`. -/
def p30 : List Byte := [
  0x41, 0x80, 0x3c, 0x24, 0x00]

theorem p30_0 : ∀ feat, Dec feat p30 0 (FV7z.mk .cmp 8 [.mem (mg (some 12) none 1 0 8), .imm 8 0] 5) := by dec_rfl

/-- What the stretch does. -/
def o30 : List Op := [
  Op.cmpmi 8 (some 12) none 1 0 0]

theorem b30 (prof : Profile) : Blk prof p30 0 5 o30 :=
  .cons (p30_0 _) (OpI.cmpmi (.inl rfl)) (by decide) <|
  .nil 5

def j18 : List Byte := [0x0f, 0x84, 0x65, 0xff, 0xff, 0xff]
theorem j18_0 : ∀ feat, Dec feat j18 0 (FV7z.mk (.jcc 4) 64 [.rel 18446744073709551461] 6) := by dec_rfl

/-- The stretch at `396`. -/
def p31 : List Byte := [
  0x48, 0x83, 0xc7, 0x20, 0x48, 0x8d, 0x35, 0x21, 0x6c, 0x14, 0x00]

theorem p31_0 : ∀ feat, Dec feat p31 0 (FV7z.mk .add 64 [gr 64 7, Src.opd 64 (.i 32)] 4) := by dec_rfl
theorem p31_4 : ∀ feat, Dec feat p31 4 (FV7z.mk .lea 64 [gr 64 6, .mem (mrip 1338401 0)] 7) := by dec_rfl

/-- What the stretch does. -/
def o31 : List Op := [
  Op.add 64 7 (.i 32),
  Op.mov 64 6 (.i 7238664)]

theorem b31 (prof : Profile) : BlkA prof p31 (0x5a07dc : Addr) 0 11 o31 :=
  .cons (p31_0 _) ((OpI.add (.i 32) (.inr rfl)).at _) (by decide) <|
  .cons (p31_4 _) (OpIA.lea_rip (by decide)) (by decide) <|
  .nil 11

def j19 : List Byte := [0xeb, 0xad]
theorem j19_0 : ∀ feat, Dec feat j19 0 (FV7z.mk .jmp 64 [.rel 18446744073709551533] 2) := by dec_rfl

/-- The stretch at `414`. -/
def p32 : List Byte := [
  0x83, 0xf8, 0x01]

theorem p32_0 : ∀ feat, Dec feat p32 0 (FV7z.mk .cmp 32 [gr 32 0, Src.opd 32 (.i 1)] 3) := by dec_rfl

/-- What the stretch does. -/
def o32 : List Op := [
  Op.cmp 32 0 (.i 1)]

theorem b32 (prof : Profile) : Blk prof p32 0 3 o32 :=
  .cons (p32_0 _) (OpI.cmp (.i 1) (.inl rfl)) (by decide) <|
  .nil 3

def j20 : List Byte := [0x75, 0x90]
theorem j20_0 : ∀ feat, Dec feat j20 0 (FV7z.mk (.jcc 5) 64 [.rel 18446744073709551504] 2) := by dec_rfl

/-- The stretch at `419`. -/
def p33 : List Byte := [
  0x49, 0x8b, 0x06, 0x42, 0x8b, 0x04, 0xb8, 0x83, 0xf8, 0x2d]

theorem p33_0 : ∀ feat, Dec feat p33 0 (FV7z.mk .mov 64 [gr 64 0, .mem (mg (some 14) none 1 0 64)] 3) := by dec_rfl
theorem p33_3 : ∀ feat, Dec feat p33 3 (FV7z.mk .mov 32 [gr 32 0, .mem (mg (some 0) (some 15) 4 0 32)] 4) := by dec_rfl
theorem p33_7 : ∀ feat, Dec feat p33 7 (FV7z.mk .cmp 32 [gr 32 0, Src.opd 32 (.i 45)] 3) := by dec_rfl

/-- What the stretch does. -/
def o33 : List Op := [
  Op.ld 64 0 (some 14) none 1 0,
  Op.ld 32 0 (some 0) (some 15) 4 0,
  Op.cmp 32 0 (.i 45)]

theorem b33 (prof : Profile) : Blk prof p33 0 10 o33 :=
  .cons (p33_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p33_3 _) (OpI.ld (.inl rfl)) (by decide) <|
  .cons (p33_7 _) (OpI.cmp (.i 45) (.inl rfl)) (by decide) <|
  .nil 10

def j21 : List Byte := [0x74, 0x88]
theorem j21_0 : ∀ feat, Dec feat j21 0 (FV7z.mk (.jcc 4) 64 [.rel 18446744073709551496] 2) := by dec_rfl

def j22 : List Byte := [0xeb, 0x2e]
theorem j22_0 : ∀ feat, Dec feat j22 0 (FV7z.mk .jmp 64 [.rel 46] 2) := by dec_rfl

def j23 : List Byte := [0x0f, 0x85, 0x73, 0xff, 0xff, 0xff]
theorem j23_0 : ∀ feat, Dec feat j23 0 (FV7z.mk (.jcc 5) 64 [.rel 18446744073709551475] 6) := by dec_rfl

/-- The stretch at `448`. -/
def p34 : List Byte := [
  0x49, 0x8b, 0x06, 0x42, 0x8b, 0x04, 0xb8, 0x83, 0xf8, 0x7f]

theorem p34_0 : ∀ feat, Dec feat p34 0 (FV7z.mk .mov 64 [gr 64 0, .mem (mg (some 14) none 1 0 64)] 3) := by dec_rfl
theorem p34_3 : ∀ feat, Dec feat p34 3 (FV7z.mk .mov 32 [gr 32 0, .mem (mg (some 0) (some 15) 4 0 32)] 4) := by dec_rfl
theorem p34_7 : ∀ feat, Dec feat p34 7 (FV7z.mk .cmp 32 [gr 32 0, Src.opd 32 (.i 127)] 3) := by dec_rfl

/-- What the stretch does. -/
def o34 : List Op := [
  Op.ld 64 0 (some 14) none 1 0,
  Op.ld 32 0 (some 0) (some 15) 4 0,
  Op.cmp 32 0 (.i 127)]

theorem b34 (prof : Profile) : Blk prof p34 0 10 o34 :=
  .cons (p34_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p34_3 _) (OpI.ld (.inl rfl)) (by decide) <|
  .cons (p34_7 _) (OpI.cmp (.i 127) (.inl rfl)) (by decide) <|
  .nil 10

def j24 : List Byte := [0x7f, 0x19]
theorem j24_0 : ∀ feat, Dec feat j24 0 (FV7z.mk (.jcc 15) 64 [.rel 25] 2) := by dec_rfl

/-- The stretch at `460`. -/
def p35 : List Byte := [
  0x48, 0x8b, 0x7b, 0x10, 0x0f, 0xbe, 0xf0]

theorem p35_0 : ∀ feat, Dec feat p35 0 (FV7z.mk .mov 64 [gr 64 7, .mem (mg (some 3) none 1 16 64)] 4) := by dec_rfl
theorem p35_4 : ∀ feat, Dec feat p35 4 (FV7z.mk .movsx 32 [gr 32 6, gr 8 0] 3) := by dec_rfl

/-- What the stretch does. -/
def o35 : List Op := [
  Op.ld 64 7 (some 3) none 1 16,
  Op.sxb32 6 0]

theorem b35 (prof : Profile) : Blk prof p35 0 7 o35 :=
  .cons (p35_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p35_4 _) (OpI.sxb32) (by decide) <|
  .nil 7

/-- The stretch at `472`. -/
def p36 : List Byte := [
  0x41, 0x89, 0x44, 0x24, 0x04, 0x85, 0xc0]

theorem p36_0 : ∀ feat, Dec feat p36 0 (FV7z.mk .mov 32 [.mem (mg (some 12) none 1 4 32), gr 32 0] 5) := by dec_rfl
theorem p36_5 : ∀ feat, Dec feat p36 5 (FV7z.mk .test 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl

/-- What the stretch does. -/
def o36 : List Op := [
  Op.st 32 (some 12) none 1 4 0,
  Op.test 32 0 (.r 0)]

theorem b36 (prof : Profile) : Blk prof p36 0 7 o36 :=
  .cons (p36_0 _) (OpI.st (.inr (.inr (.inl rfl)))) (by decide) <|
  .cons (p36_5 _) (OpI.test (.r 0) (.inl rfl)) (by decide) <|
  .nil 7

def j25 : List Byte := [0x0f, 0x89, 0x58, 0xff, 0xff, 0xff]
theorem j25_0 : ∀ feat, Dec feat j25 0 (FV7z.mk (.jcc 9) 64 [.rel 18446744073709551448] 6) := by dec_rfl

/-- The stretch at `485`. -/
def p37 : List Byte := [
  0x48, 0x8b, 0x7c, 0x24, 0x18, 0x48, 0x8d, 0x35, 0x9b, 0x6b, 0x14, 0x00, 0x45, 0x31, 0xed, 0x48,
  0x83, 0xc7, 0x20]

theorem p37_0 : ∀ feat, Dec feat p37 0 (FV7z.mk .mov 64 [gr 64 7, .mem (mg (some 4) none 1 24 64)] 5) := by dec_rfl
theorem p37_5 : ∀ feat, Dec feat p37 5 (FV7z.mk .lea 64 [gr 64 6, .mem (mrip 1338267 0)] 7) := by dec_rfl
theorem p37_12 : ∀ feat, Dec feat p37 12 (FV7z.mk .xor 32 [gr 32 13, Src.opd 32 (.r 13)] 3) := by dec_rfl
theorem p37_15 : ∀ feat, Dec feat p37 15 (FV7z.mk .add 64 [gr 64 7, Src.opd 64 (.i 32)] 4) := by dec_rfl

/-- What the stretch does. -/
def o37 : List Op := [
  Op.ld 64 7 (some 4) none 1 24,
  Op.mov 64 6 (.i 7238620),
  Op.xor 32 13 (.r 13),
  Op.add 64 7 (.i 32)]

theorem b37 (prof : Profile) : BlkA prof p37 (0x5a0835 : Addr) 0 19 o37 :=
  .cons (p37_0 _) ((OpI.ld (.inr rfl)).at _) (by decide) <|
  .cons (p37_5 _) (OpIA.lea_rip (by decide)) (by decide) <|
  .cons (p37_12 _) ((OpI.xor (.r 13) (.inl rfl)).at _) (by decide) <|
  .cons (p37_15 _) ((OpI.add (.i 32) (.inr rfl)).at _) (by decide) <|
  .nil 19

def j26 : List Byte := [0xe9, 0x49, 0xff, 0xff, 0xff]
theorem j26_0 : ∀ feat, Dec feat j26 0 (FV7z.mk .jmp 64 [.rel 18446744073709551433] 5) := by dec_rfl

/-- The stretch at `514`. -/
def p38 : List Byte := [
  0x49, 0x8b, 0x06, 0x4c, 0x8d, 0x6c, 0x24, 0x20, 0x4c, 0x89, 0xef, 0x4a, 0x8d, 0x34, 0xb8]

theorem p38_0 : ∀ feat, Dec feat p38 0 (FV7z.mk .mov 64 [gr 64 0, .mem (mg (some 14) none 1 0 64)] 3) := by dec_rfl
theorem p38_3 : ∀ feat, Dec feat p38 3 (FV7z.mk .lea 64 [gr 64 13, .mem (mg (some 4) none 1 32 0)] 5) := by dec_rfl
theorem p38_8 : ∀ feat, Dec feat p38 8 (FV7z.mk .mov 64 [gr 64 7, Src.opd 64 (.r 13)] 3) := by dec_rfl
theorem p38_11 : ∀ feat, Dec feat p38 11 (FV7z.mk .lea 64 [gr 64 6, .mem (mg (some 0) (some 15) 4 0 0)] 4) := by dec_rfl

/-- What the stretch does. -/
def o38 : List Op := [
  Op.ld 64 0 (some 14) none 1 0,
  Op.lea 64 13 (some 4) none 1 32,
  Op.mov 64 7 (.r 13),
  Op.lea 64 6 (some 0) (some 15) 4 0]

theorem b38 (prof : Profile) : Blk prof p38 0 15 o38 :=
  .cons (p38_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p38_3 _) (OpI.lea (.inr rfl)) (by decide) <|
  .cons (p38_8 _) (OpI.mov (.r 13) (.inr rfl)) (by decide) <|
  .cons (p38_11 _) (OpI.lea (.inr rfl)) (by decide) <|
  .nil 15

/-- The stretch at `534`. -/
def p39 : List Byte := [
  0x41, 0x8b, 0x44, 0x24, 0x14, 0x41, 0x39, 0x44, 0x24, 0x10]

theorem p39_0 : ∀ feat, Dec feat p39 0 (FV7z.mk .mov 32 [gr 32 0, .mem (mg (some 12) none 1 20 32)] 5) := by dec_rfl
theorem p39_5 : ∀ feat, Dec feat p39 5 (FV7z.mk .cmp 32 [.mem (mg (some 12) none 1 16 32), gr 32 0] 5) := by dec_rfl

/-- What the stretch does. -/
def o39 : List Op := [
  Op.ld 32 0 (some 12) none 1 20,
  Op.cmpmr 32 (some 12) none 1 16 0]

theorem b39 (prof : Profile) : Blk prof p39 0 10 o39 :=
  .cons (p39_0 _) (OpI.ld (.inl rfl)) (by decide) <|
  .cons (p39_5 _) (OpI.cmpmr (.inl rfl)) (by decide) <|
  .nil 10

def j27 : List Byte := [0x75, 0x5a]
theorem j27_0 : ∀ feat, Dec feat j27 0 (FV7z.mk (.jcc 5) 64 [.rel 90] 2) := by dec_rfl

/-- The stretch at `546`. -/
def p40 : List Byte := [
  0x3d, 0xfe, 0xff, 0xff, 0x7f]

theorem p40_0 : ∀ feat, Dec feat p40 0 (FV7z.mk .cmp 32 [gr 32 0, Src.opd 32 (.i 2147483646)] 5) := by dec_rfl

/-- What the stretch does. -/
def o40 : List Op := [
  Op.cmp 32 0 (.i 2147483646)]

theorem b40 (prof : Profile) : Blk prof p40 0 5 o40 :=
  .cons (p40_0 _) (OpI.cmp (.i 2147483646) (.inl rfl)) (by decide) <|
  .nil 5

/-- The stretch at `557`. -/
def p41 : List Byte := [
  0x89, 0xc2, 0xc1, 0xea, 0x02, 0x8d, 0x5a, 0x01, 0xba, 0xff, 0xff, 0xff, 0x7f]

theorem p41_0 : ∀ feat, Dec feat p41 0 (FV7z.mk .mov 32 [gr 32 2, Src.opd 32 (.r 0)] 2) := by dec_rfl
theorem p41_2 : ∀ feat, Dec feat p41 2 (FV7z.mk .shr 32 [gr 32 2, Src.opd 8 (.i 2)] 3) := by dec_rfl
theorem p41_5 : ∀ feat, Dec feat p41 5 (FV7z.mk .lea 32 [gr 32 3, .mem (mg (some 2) none 1 1 0)] 3) := by dec_rfl
theorem p41_8 : ∀ feat, Dec feat p41 8 (FV7z.mk .mov 32 [gr 32 2, Src.opd 32 (.i 2147483647)] 5) := by dec_rfl

/-- What the stretch does. -/
def o41 : List Op := [
  Op.mov 32 2 (.r 0),
  Op.shr 2 (.i 2),
  Op.lea 32 3 (some 2) none 1 1,
  Op.mov 32 2 (.i 2147483647)]

theorem b41 (prof : Profile) : Blk prof p41 0 13 o41 :=
  .cons (p41_0 _) (OpI.mov (.r 0) (.inl rfl)) (by decide) <|
  .cons (p41_2 _) (OpI.shr (.i 2)) (by decide) <|
  .cons (p41_5 _) (OpI.lea (.inl rfl)) (by decide) <|
  .cons (p41_8 _) (OpI.mov (.i 2147483647) (.inl rfl)) (by decide) <|
  .nil 13

/-- The stretch at `570`. -/
def p42 : List Byte := [
  0x29, 0xc2, 0x39, 0xda, 0x0f, 0x47, 0xd3, 0x8d, 0x3c, 0x02]

theorem p42_0 : ∀ feat, Dec feat p42 0 (FV7z.mk .sub 32 [gr 32 2, Src.opd 32 (.r 0)] 2) := by dec_rfl
theorem p42_2 : ∀ feat, Dec feat p42 2 (FV7z.mk .cmp 32 [gr 32 2, Src.opd 32 (.r 3)] 2) := by dec_rfl
theorem p42_4 : ∀ feat, Dec feat p42 4 (FV7z.mk (.cmovcc 7) 32 [gr 32 2, gr 32 3] 3) := by dec_rfl
theorem p42_7 : ∀ feat, Dec feat p42 7 (FV7z.mk .lea 32 [gr 32 7, .mem (mg (some 2) (some 0) 1 0 0)] 3) := by dec_rfl

/-- What the stretch does. -/
def o42 : List Op := [
  Op.sub 32 2 (.r 0),
  Op.cmp 32 2 (.r 3),
  Op.cmov32 7 2 3,
  Op.lea 32 7 (some 2) (some 0) 1 0]

theorem b42 (prof : Profile) : Blk prof p42 0 10 o42 :=
  .cons (p42_0 _) (OpI.sub (.r 0) (.inl rfl)) (by decide) <|
  .cons (p42_2 _) (OpI.cmp (.r 3) (.inl rfl)) (by decide) <|
  .cons (p42_4 _) (OpI.cmov32) (by decide) <|
  .cons (p42_7 _) (OpI.lea (.inl rfl)) (by decide) <|
  .nil 10

/-- The stretch at `580`. -/
def p43 : List Byte := [
  0x48, 0x89, 0xfb, 0x48, 0xc1, 0xe7, 0x03]

theorem p43_0 : ∀ feat, Dec feat p43 0 (FV7z.mk .mov 64 [gr 64 3, Src.opd 64 (.r 7)] 3) := by dec_rfl
theorem p43_3 : ∀ feat, Dec feat p43 3 (FV7z.mk .shl 64 [gr 64 7, Src.opd 8 (.i 3)] 4) := by dec_rfl

/-- What the stretch does. -/
def o43 : List Op := [
  Op.mov 64 3 (.r 7),
  Op.shl64 7 (.i 3)]

theorem b43 (prof : Profile) : Blk prof p43 0 7 o43 :=
  .cons (p43_0 _) (OpI.mov (.r 7) (.inr rfl)) (by decide) <|
  .cons (p43_3 _) (OpI.shl64 (.i 3)) (by decide) <|
  .nil 7

/-- The stretch at `592`. -/
def p44 : List Byte := [
  0x48, 0x89, 0xc5, 0x41, 0x8b, 0x44, 0x24, 0x10, 0x49, 0x8b, 0x74, 0x24, 0x08, 0x85, 0xc0]

theorem p44_0 : ∀ feat, Dec feat p44 0 (FV7z.mk .mov 64 [gr 64 5, Src.opd 64 (.r 0)] 3) := by dec_rfl
theorem p44_3 : ∀ feat, Dec feat p44 3 (FV7z.mk .mov 32 [gr 32 0, .mem (mg (some 12) none 1 16 32)] 5) := by dec_rfl
theorem p44_8 : ∀ feat, Dec feat p44 8 (FV7z.mk .mov 64 [gr 64 6, .mem (mg (some 12) none 1 8 64)] 5) := by dec_rfl
theorem p44_13 : ∀ feat, Dec feat p44 13 (FV7z.mk .test 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl

/-- What the stretch does. -/
def o44 : List Op := [
  Op.mov 64 5 (.r 0),
  Op.ld 32 0 (some 12) none 1 16,
  Op.ld 64 6 (some 12) none 1 8,
  Op.test 32 0 (.r 0)]

theorem b44 (prof : Profile) : Blk prof p44 0 15 o44 :=
  .cons (p44_0 _) (OpI.mov (.r 0) (.inr rfl)) (by decide) <|
  .cons (p44_3 _) (OpI.ld (.inl rfl)) (by decide) <|
  .cons (p44_8 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p44_13 _) (OpI.test (.r 0) (.inl rfl)) (by decide) <|
  .nil 15

def j28 : List Byte := [0x0f, 0x85, 0xb4, 0x00, 0x00, 0x00]
theorem j28_0 : ∀ feat, Dec feat j28 0 (FV7z.mk (.jcc 5) 64 [.rel 180] 6) := by dec_rfl

/-- The stretch at `613`. -/
def p45 : List Byte := [
  0x48, 0x85, 0xf6]

theorem p45_0 : ∀ feat, Dec feat p45 0 (FV7z.mk .test 64 [gr 64 6, Src.opd 64 (.r 6)] 3) := by dec_rfl

/-- What the stretch does. -/
def o45 : List Op := [
  Op.test 64 6 (.r 6)]

theorem b45 (prof : Profile) : Blk prof p45 0 3 o45 :=
  .cons (p45_0 _) (OpI.test (.r 6) (.inr rfl)) (by decide) <|
  .nil 3

def j29 : List Byte := [0x74, 0x08]
theorem j29_0 : ∀ feat, Dec feat j29 0 (FV7z.mk (.jcc 4) 64 [.rel 8] 2) := by dec_rfl

/-- The stretch at `618`. -/
def p46 : List Byte := [
  0x48, 0x89, 0xf7]

theorem p46_0 : ∀ feat, Dec feat p46 0 (FV7z.mk .mov 64 [gr 64 7, Src.opd 64 (.r 6)] 3) := by dec_rfl

/-- What the stretch does. -/
def o46 : List Op := [
  Op.mov 64 7 (.r 6)]

theorem b46 (prof : Profile) : Blk prof p46 0 3 o46 :=
  .cons (p46_0 _) (OpI.mov (.r 6) (.inr rfl)) (by decide) <|
  .nil 3

/-- The stretch at `626`. -/
def p47 : List Byte := [
  0x49, 0x89, 0x6c, 0x24, 0x08, 0x41, 0x89, 0x5c, 0x24, 0x14]

theorem p47_0 : ∀ feat, Dec feat p47 0 (FV7z.mk .mov 64 [.mem (mg (some 12) none 1 8 64), gr 64 5] 5) := by dec_rfl
theorem p47_5 : ∀ feat, Dec feat p47 5 (FV7z.mk .mov 32 [.mem (mg (some 12) none 1 20 32), gr 32 3] 5) := by dec_rfl

/-- What the stretch does. -/
def o47 : List Op := [
  Op.st 64 (some 12) none 1 8 5,
  Op.st 32 (some 12) none 1 20 3]

theorem b47 (prof : Profile) : Blk prof p47 0 10 o47 :=
  .cons (p47_0 _) (OpI.st (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p47_5 _) (OpI.st (.inr (.inr (.inl rfl)))) (by decide) <|
  .nil 10

/-- The stretch at `636`. -/
def p48 : List Byte := [
  0xbf, 0x10, 0x00, 0x00, 0x00]

theorem p48_0 : ∀ feat, Dec feat p48 0 (FV7z.mk .mov 32 [gr 32 7, Src.opd 32 (.i 16)] 5) := by dec_rfl

/-- What the stretch does. -/
def o48 : List Op := [
  Op.mov 32 7 (.i 16)]

theorem b48 (prof : Profile) : Blk prof p48 0 5 o48 :=
  .cons (p48_0 _) (OpI.mov (.i 16) (.inl rfl)) (by decide) <|
  .nil 5

/-- The stretch at `646`. -/
def p49 : List Byte := [
  0x4c, 0x89, 0xee, 0x48, 0x89, 0xc7, 0x48, 0x89, 0xc5]

theorem p49_0 : ∀ feat, Dec feat p49 0 (FV7z.mk .mov 64 [gr 64 6, Src.opd 64 (.r 13)] 3) := by dec_rfl
theorem p49_3 : ∀ feat, Dec feat p49 3 (FV7z.mk .mov 64 [gr 64 7, Src.opd 64 (.r 0)] 3) := by dec_rfl
theorem p49_6 : ∀ feat, Dec feat p49 6 (FV7z.mk .mov 64 [gr 64 5, Src.opd 64 (.r 0)] 3) := by dec_rfl

/-- What the stretch does. -/
def o49 : List Op := [
  Op.mov 64 6 (.r 13),
  Op.mov 64 7 (.r 0),
  Op.mov 64 5 (.r 0)]

theorem b49 (prof : Profile) : Blk prof p49 0 9 o49 :=
  .cons (p49_0 _) (OpI.mov (.r 13) (.inr rfl)) (by decide) <|
  .cons (p49_3 _) (OpI.mov (.r 0) (.inr rfl)) (by decide) <|
  .cons (p49_6 _) (OpI.mov (.r 0) (.inr rfl)) (by decide) <|
  .nil 9

/-- The stretch at `660`. -/
def p50 : List Byte := [
  0x41, 0x8b, 0x44, 0x24, 0x10, 0x49, 0x8b, 0x54, 0x24, 0x08, 0x8d, 0x48, 0x01, 0x41, 0x89, 0x4c,
  0x24, 0x10]

theorem p50_0 : ∀ feat, Dec feat p50 0 (FV7z.mk .mov 32 [gr 32 0, .mem (mg (some 12) none 1 16 32)] 5) := by dec_rfl
theorem p50_5 : ∀ feat, Dec feat p50 5 (FV7z.mk .mov 64 [gr 64 2, .mem (mg (some 12) none 1 8 64)] 5) := by dec_rfl
theorem p50_10 : ∀ feat, Dec feat p50 10 (FV7z.mk .lea 32 [gr 32 1, .mem (mg (some 0) none 1 1 0)] 3) := by dec_rfl
theorem p50_13 : ∀ feat, Dec feat p50 13 (FV7z.mk .mov 32 [.mem (mg (some 12) none 1 16 32), gr 32 1] 5) := by dec_rfl

/-- What the stretch does. -/
def o50 : List Op := [
  Op.ld 32 0 (some 12) none 1 16,
  Op.ld 64 2 (some 12) none 1 8,
  Op.lea 32 1 (some 0) none 1 1,
  Op.st 32 (some 12) none 1 16 1]

theorem b50 (prof : Profile) : Blk prof p50 0 18 o50 :=
  .cons (p50_0 _) (OpI.ld (.inl rfl)) (by decide) <|
  .cons (p50_5 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p50_10 _) (OpI.lea (.inl rfl)) (by decide) <|
  .cons (p50_13 _) (OpI.st (.inr (.inr (.inl rfl)))) (by decide) <|
  .nil 18

/-- The stretch at `678`. -/
def p51 : List Byte := [
  0x48, 0x89, 0x2c, 0xc2, 0x48, 0x8b, 0x7c, 0x24, 0x20, 0x48, 0x85, 0xff]

theorem p51_0 : ∀ feat, Dec feat p51 0 (FV7z.mk .mov 64 [.mem (mg (some 2) (some 0) 8 0 64), gr 64 5] 4) := by dec_rfl
theorem p51_4 : ∀ feat, Dec feat p51 4 (FV7z.mk .mov 64 [gr 64 7, .mem (mg (some 4) none 1 32 64)] 5) := by dec_rfl
theorem p51_9 : ∀ feat, Dec feat p51 9 (FV7z.mk .test 64 [gr 64 7, Src.opd 64 (.r 7)] 3) := by dec_rfl

/-- What the stretch does. -/
def o51 : List Op := [
  Op.st 64 (some 2) (some 0) 8 0 5,
  Op.ld 64 7 (some 4) none 1 32,
  Op.test 64 7 (.r 7)]

theorem b51 (prof : Profile) : Blk prof p51 0 12 o51 :=
  .cons (p51_0 _) (OpI.st (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p51_4 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p51_9 _) (OpI.test (.r 7) (.inr rfl)) (by decide) <|
  .nil 12

def j30 : List Byte := [0x0f, 0x84, 0x85, 0xfe, 0xff, 0xff]
theorem j30_0 : ∀ feat, Dec feat j30 0 (FV7z.mk (.jcc 4) 64 [.rel 18446744073709551237] 6) := by dec_rfl

def j31 : List Byte := [0xe9, 0x7b, 0xfe, 0xff, 0xff]
theorem j31_0 : ∀ feat, Dec feat j31 0 (FV7z.mk .jmp 64 [.rel 18446744073709551227] 5) := by dec_rfl

/-- The stretch at `706`. -/
def p52 : List Byte := [
  0x48, 0x8b, 0x7c, 0x24, 0x18, 0x48, 0x8d, 0x35, 0xac, 0x6a, 0x14, 0x00, 0x45, 0x31, 0xed, 0x48,
  0x83, 0xc7, 0x20]

theorem p52_0 : ∀ feat, Dec feat p52 0 (FV7z.mk .mov 64 [gr 64 7, .mem (mg (some 4) none 1 24 64)] 5) := by dec_rfl
theorem p52_5 : ∀ feat, Dec feat p52 5 (FV7z.mk .lea 64 [gr 64 6, .mem (mrip 1338028 0)] 7) := by dec_rfl
theorem p52_12 : ∀ feat, Dec feat p52 12 (FV7z.mk .xor 32 [gr 32 13, Src.opd 32 (.r 13)] 3) := by dec_rfl
theorem p52_15 : ∀ feat, Dec feat p52 15 (FV7z.mk .add 64 [gr 64 7, Src.opd 64 (.i 32)] 4) := by dec_rfl

/-- What the stretch does. -/
def o52 : List Op := [
  Op.ld 64 7 (some 4) none 1 24,
  Op.mov 64 6 (.i 7238602),
  Op.xor 32 13 (.r 13),
  Op.add 64 7 (.i 32)]

theorem b52 (prof : Profile) : BlkA prof p52 (0x5a0912 : Addr) 0 19 o52 :=
  .cons (p52_0 _) ((OpI.ld (.inr rfl)).at _) (by decide) <|
  .cons (p52_5 _) (OpIA.lea_rip (by decide)) (by decide) <|
  .cons (p52_12 _) ((OpI.xor (.r 13) (.inl rfl)).at _) (by decide) <|
  .cons (p52_15 _) ((OpI.add (.i 32) (.inr rfl)).at _) (by decide) <|
  .nil 19

def j32 : List Byte := [0xe9, 0x6c, 0xfe, 0xff, 0xff]
theorem j32_0 : ∀ feat, Dec feat j32 0 (FV7z.mk .jmp 64 [.rel 18446744073709551212] 5) := by dec_rfl

/-- The stretch at `735`. -/
def p53 : List Byte := [
  0x48, 0x8b, 0x7c, 0x24, 0x18, 0x48, 0x8d, 0x35, 0x7f, 0x6a, 0x14, 0x00, 0x45, 0x31, 0xed, 0x48,
  0x83, 0xc7, 0x20]

theorem p53_0 : ∀ feat, Dec feat p53 0 (FV7z.mk .mov 64 [gr 64 7, .mem (mg (some 4) none 1 24 64)] 5) := by dec_rfl
theorem p53_5 : ∀ feat, Dec feat p53 5 (FV7z.mk .lea 64 [gr 64 6, .mem (mrip 1337983 0)] 7) := by dec_rfl
theorem p53_12 : ∀ feat, Dec feat p53 12 (FV7z.mk .xor 32 [gr 32 13, Src.opd 32 (.r 13)] 3) := by dec_rfl
theorem p53_15 : ∀ feat, Dec feat p53 15 (FV7z.mk .add 64 [gr 64 7, Src.opd 64 (.i 32)] 4) := by dec_rfl

/-- What the stretch does. -/
def o53 : List Op := [
  Op.ld 64 7 (some 4) none 1 24,
  Op.mov 64 6 (.i 7238586),
  Op.xor 32 13 (.r 13),
  Op.add 64 7 (.i 32)]

theorem b53 (prof : Profile) : BlkA prof p53 (0x5a092f : Addr) 0 19 o53 :=
  .cons (p53_0 _) ((OpI.ld (.inr rfl)).at _) (by decide) <|
  .cons (p53_5 _) (OpIA.lea_rip (by decide)) (by decide) <|
  .cons (p53_12 _) ((OpI.xor (.r 13) (.inl rfl)).at _) (by decide) <|
  .cons (p53_15 _) ((OpI.add (.i 32) (.inr rfl)).at _) (by decide) <|
  .nil 19

def j33 : List Byte := [0xe9, 0x4f, 0xfe, 0xff, 0xff]
theorem j33_0 : ∀ feat, Dec feat j33 0 (FV7z.mk .jmp 64 [.rel 18446744073709551183] 5) := by dec_rfl

/-- The stretch at `764`. -/
def p54 : List Byte := [
  0x48, 0x8b, 0x7c, 0x24, 0x18, 0x48, 0x8d, 0x35, 0x9e, 0x6a, 0x14, 0x00, 0x45, 0x31, 0xed, 0x48,
  0x83, 0xc7, 0x20]

theorem p54_0 : ∀ feat, Dec feat p54 0 (FV7z.mk .mov 64 [gr 64 7, .mem (mg (some 4) none 1 24 64)] 5) := by dec_rfl
theorem p54_5 : ∀ feat, Dec feat p54 5 (FV7z.mk .lea 64 [gr 64 6, .mem (mrip 1338014 0)] 7) := by dec_rfl
theorem p54_12 : ∀ feat, Dec feat p54 12 (FV7z.mk .xor 32 [gr 32 13, Src.opd 32 (.r 13)] 3) := by dec_rfl
theorem p54_15 : ∀ feat, Dec feat p54 15 (FV7z.mk .add 64 [gr 64 7, Src.opd 64 (.i 32)] 4) := by dec_rfl

/-- What the stretch does. -/
def o54 : List Op := [
  Op.ld 64 7 (some 4) none 1 24,
  Op.mov 64 6 (.i 7238646),
  Op.xor 32 13 (.r 13),
  Op.add 64 7 (.i 32)]

theorem b54 (prof : Profile) : BlkA prof p54 (0x5a094c : Addr) 0 19 o54 :=
  .cons (p54_0 _) ((OpI.ld (.inr rfl)).at _) (by decide) <|
  .cons (p54_5 _) (OpIA.lea_rip (by decide)) (by decide) <|
  .cons (p54_12 _) ((OpI.xor (.r 13) (.inl rfl)).at _) (by decide) <|
  .cons (p54_15 _) ((OpI.add (.i 32) (.inr rfl)).at _) (by decide) <|
  .nil 19

def j34 : List Byte := [0xe9, 0x32, 0xfe, 0xff, 0xff]
theorem j34_0 : ∀ feat, Dec feat j34 0 (FV7z.mk .jmp 64 [.rel 18446744073709551154] 5) := by dec_rfl

/-- The stretch at `793`. -/
def p55 : List Byte := [
  0x48, 0x8d, 0x14, 0xc5, 0x00, 0x00, 0x00, 0x00, 0x48, 0x89, 0xef]

theorem p55_0 : ∀ feat, Dec feat p55 0 (FV7z.mk .lea 64 [gr 64 2, .mem (mg none (some 0) 8 0 0)] 8) := by dec_rfl
theorem p55_8 : ∀ feat, Dec feat p55 8 (FV7z.mk .mov 64 [gr 64 7, Src.opd 64 (.r 5)] 3) := by dec_rfl

/-- What the stretch does. -/
def o55 : List Op := [
  Op.lea 64 2 none (some 0) 8 0,
  Op.mov 64 7 (.r 5)]

theorem b55 (prof : Profile) : Blk prof p55 0 11 o55 :=
  .cons (p55_0 _) (OpI.lea (.inr rfl)) (by decide) <|
  .cons (p55_8 _) (OpI.mov (.r 5) (.inr rfl)) (by decide) <|
  .nil 11

/-- The stretch at `809`. -/
def p56 : List Byte := [
  0x49, 0x8b, 0x74, 0x24, 0x08]

theorem p56_0 : ∀ feat, Dec feat p56 0 (FV7z.mk .mov 64 [gr 64 6, .mem (mg (some 12) none 1 8 64)] 5) := by dec_rfl

/-- What the stretch does. -/
def o56 : List Op := [
  Op.ld 64 6 (some 12) none 1 8]

theorem b56 (prof : Profile) : Blk prof p56 0 5 o56 :=
  .cons (p56_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .nil 5

def j35 : List Byte := [0xe9, 0x32, 0xff, 0xff, 0xff]
theorem j35_0 : ∀ feat, Dec feat j35 0 (FV7z.mk .jmp 64 [.rel 18446744073709551410] 5) := by dec_rfl

end FV7z.Cps
