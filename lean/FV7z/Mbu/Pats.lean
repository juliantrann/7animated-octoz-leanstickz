import FV7z.Lemmas.SpFs
import FV7z.Lemmas.BlkOps14
import FV7z.Lemmas.BlkOps6
import FV7z.Lemmas.BlkOps2
/-!
# The stretches of straight-line code of `MultiByteToUnicodeString2` (PLAN.md §M, M1)

Each distinct stretch between labels and jumps (`p*`, 30 of them) and each distinct jump (`j*`, 23) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.Mbu
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The stretch at `0`. -/
def p0 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0x41, 0x55, 0x41, 0x54, 0x55, 0x53, 0x48, 0x83, 0xec, 0x28, 0x48, 0x8b,
  0x1f, 0x64, 0x48, 0x8b, 0x04, 0x25, 0x28, 0x00, 0x00, 0x00, 0x48, 0x89, 0x44, 0x24, 0x18, 0x31,
  0xc0, 0xc7, 0x47, 0x08, 0x00, 0x00, 0x00, 0x00, 0x8b, 0x46, 0x08, 0xc7, 0x03, 0x00, 0x00, 0x00,
  0x00, 0x85, 0xc0]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem p0_4 : ∀ feat, Dec feat p0 4 (FV7z.mk .push 64 [gr 64 13] 2) := by dec_rfl
theorem p0_6 : ∀ feat, Dec feat p0 6 (FV7z.mk .push 64 [gr 64 12] 2) := by dec_rfl
theorem p0_8 : ∀ feat, Dec feat p0 8 (FV7z.mk .push 64 [gr 64 5] 1) := by dec_rfl
theorem p0_9 : ∀ feat, Dec feat p0 9 (FV7z.mk .push 64 [gr 64 3] 1) := by dec_rfl
theorem p0_10 : ∀ feat, Dec feat p0 10 (FV7z.mk .sub 64 [gr 64 4, Src.opd 64 (.i 40)] 4) := by dec_rfl
theorem p0_14 : ∀ feat, Dec feat p0 14 (FV7z.mk .mov 64 [gr 64 3, .mem (mg (some 7) none 1 0 64)] 3) := by dec_rfl
theorem p0_17 : ∀ feat, Dec feat p0 17 (FV7z.mk .mov 64 [gr 64 0, .mem (mf none none 1 40 64)] 9) := by dec_rfl
theorem p0_26 : ∀ feat, Dec feat p0 26 (FV7z.mk .mov 64 [.mem (mg (some 4) none 1 24 64), gr 64 0] 5) := by dec_rfl
theorem p0_31 : ∀ feat, Dec feat p0 31 (FV7z.mk .xor 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl
theorem p0_33 : ∀ feat, Dec feat p0 33 (FV7z.mk .mov 32 [.mem (mg (some 7) none 1 8 32), .imm 32 0] 7) := by dec_rfl
theorem p0_40 : ∀ feat, Dec feat p0 40 (FV7z.mk .mov 32 [gr 32 0, .mem (mg (some 6) none 1 8 32)] 3) := by dec_rfl
theorem p0_43 : ∀ feat, Dec feat p0 43 (FV7z.mk .mov 32 [.mem (mg (some 3) none 1 0 32), .imm 32 0] 6) := by dec_rfl
theorem p0_49 : ∀ feat, Dec feat p0 49 (FV7z.mk .test 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl

/-- What the stretch does. -/
def o0 (fb : Addr) : List Op := [
  Op.nop,
  Op.push 13,
  Op.push 12,
  Op.push 5,
  Op.push 3,
  Op.sub 64 4 (.i 40),
  Op.ld 64 3 (some 7) none 1 0,
  Op.ldf fb 64 0 none none 1 40,
  Op.st 64 (some 4) none 1 24 0,
  Op.xor 32 0 (.r 0),
  Op.sti 32 (some 7) none 1 8 0,
  Op.ld 32 0 (some 6) none 1 8,
  Op.sti 32 (some 3) none 1 0 0,
  Op.test 32 0 (.r 0)]

theorem b0 (prof : Profile) (fb : Addr) : BlkF prof p0 (0x450a60 : Addr) fb 0 51 (o0 fb) :=
  .cons (p0_0 _) (((OpI.endbr).at _).fs _) (by decide) <|
  .cons (p0_4 _) (((OpI.push).at _).fs _) (by decide) <|
  .cons (p0_6 _) (((OpI.push).at _).fs _) (by decide) <|
  .cons (p0_8 _) (((OpI.push).at _).fs _) (by decide) <|
  .cons (p0_9 _) (((OpI.push).at _).fs _) (by decide) <|
  .cons (p0_10 _) (((OpI.sub (.i 40) (.inr rfl)).at _).fs _) (by decide) <|
  .cons (p0_14 _) (((OpI.ld (.inr rfl)).at _).fs _) (by decide) <|
  .cons (p0_17 _) (OpIF.ldf (.inr rfl)) (by decide) <|
  .cons (p0_26 _) (((OpI.st (.inr (.inr (.inr rfl)))).at _).fs _) (by decide) <|
  .cons (p0_31 _) (((OpI.xor (.r 0) (.inl rfl)).at _).fs _) (by decide) <|
  .cons (p0_33 _) (((OpI.sti (.inr (.inr (.inl rfl)))).at _).fs _) (by decide) <|
  .cons (p0_40 _) (((OpI.ld (.inl rfl)).at _).fs _) (by decide) <|
  .cons (p0_43 _) (((OpI.sti (.inr (.inr (.inl rfl)))).at _).fs _) (by decide) <|
  .cons (p0_49 _) (((OpI.test (.r 0) (.inl rfl)).at _).fs _) (by decide) <|
  .nil 51

def j0 : List Byte := [0x0f, 0x84, 0x57, 0x01, 0x00, 0x00]
theorem j0_0 : ∀ feat, Dec feat j0 0 (FV7z.mk (.jcc 4) 64 [.rel 343] 6) := by dec_rfl

/-- The stretch at `57`. -/
def p1 : List Byte := [
  0x48, 0x89, 0xfd, 0x49, 0x89, 0xf4, 0x81, 0xfa, 0xe9, 0xfd, 0x00, 0x00]

theorem p1_0 : ∀ feat, Dec feat p1 0 (FV7z.mk .mov 64 [gr 64 5, Src.opd 64 (.r 7)] 3) := by dec_rfl
theorem p1_3 : ∀ feat, Dec feat p1 3 (FV7z.mk .mov 64 [gr 64 12, Src.opd 64 (.r 6)] 3) := by dec_rfl
theorem p1_6 : ∀ feat, Dec feat p1 6 (FV7z.mk .cmp 32 [gr 32 2, Src.opd 32 (.i 65001)] 6) := by dec_rfl

/-- What the stretch does. -/
def o1 : List Op := [
  Op.mov 64 5 (.r 7),
  Op.mov 64 12 (.r 6),
  Op.cmp 32 2 (.i 65001)]

theorem b1 (prof : Profile) : Blk prof p1 0 12 o1 :=
  .cons (p1_0 _) (OpI.mov (.r 7) (.inr rfl)) (by decide) <|
  .cons (p1_3 _) (OpI.mov (.r 6) (.inr rfl)) (by decide) <|
  .cons (p1_6 _) (OpI.cmp (.i 65001) (.inl rfl)) (by decide) <|
  .nil 12

def j1 : List Byte := [0x0f, 0x84, 0x65, 0x01, 0x00, 0x00]
theorem j1_0 : ∀ feat, Dec feat j1 0 (FV7z.mk (.jcc 4) 64 [.rel 357] 6) := by dec_rfl

/-- The stretch at `75`. -/
def p2 : List Byte := [
  0x48, 0xc7, 0xc2, 0x78, 0x21, 0x79, 0x00, 0x80, 0x3a, 0x00]

theorem p2_0 : ∀ feat, Dec feat p2 0 (FV7z.mk .mov 64 [gr 64 2, Src.opd 64 (.i 7938424)] 7) := by dec_rfl
theorem p2_7 : ∀ feat, Dec feat p2 7 (FV7z.mk .cmp 8 [.mem (mg (some 2) none 1 0 8), .imm 8 0] 3) := by dec_rfl

/-- What the stretch does. -/
def o2 : List Op := [
  Op.mov 64 2 (.i 7938424),
  Op.cmpmi 8 (some 2) none 1 0 0]

theorem b2 (prof : Profile) : Blk prof p2 0 10 o2 :=
  .cons (p2_0 _) (OpI.mov (.i 7938424) (.inr rfl)) (by decide) <|
  .cons (p2_7 _) (OpI.cmpmi (.inl rfl)) (by decide) <|
  .nil 10

def j2 : List Byte := [0x0f, 0x85, 0x55, 0x01, 0x00, 0x00]
theorem j2_0 : ∀ feat, Dec feat j2 0 (FV7z.mk (.jcc 5) 64 [.rel 341] 6) := by dec_rfl

/-- The stretch at `91`. -/
def p3 : List Byte := [
  0x4c, 0x8d, 0x6c, 0x00, 0x02, 0x44, 0x3b, 0x6f, 0x0c]

theorem p3_0 : ∀ feat, Dec feat p3 0 (FV7z.mk .lea 64 [gr 64 13, .mem (mg (some 0) (some 0) 1 2 0)] 5) := by dec_rfl
theorem p3_5 : ∀ feat, Dec feat p3 5 (FV7z.mk .cmp 32 [gr 32 13, .mem (mg (some 7) none 1 12 32)] 4) := by dec_rfl

/-- What the stretch does. -/
def o3 : List Op := [
  Op.lea 64 13 (some 0) (some 0) 1 2,
  Op.cmpm 32 13 (some 7) none 1 12]

theorem b3 (prof : Profile) : Blk prof p3 0 9 o3 :=
  .cons (p3_0 _) (OpI.lea (.inr rfl)) (by decide) <|
  .cons (p3_5 _) (OpI.cmpm (.inl rfl)) (by decide) <|
  .nil 9

def j3 : List Byte := [0x0f, 0x87, 0x56, 0x01, 0x00, 0x00]
theorem j3_0 : ∀ feat, Dec feat j3 0 (FV7z.mk (.jcc 7) 64 [.rel 342] 6) := by dec_rfl

/-- The stretch at `106`. -/
def p4 : List Byte := [
  0x49, 0x8b, 0x34, 0x24, 0x4c, 0x89, 0xea, 0x48, 0x89, 0xdf]

theorem p4_0 : ∀ feat, Dec feat p4 0 (FV7z.mk .mov 64 [gr 64 6, .mem (mg (some 12) none 1 0 64)] 4) := by dec_rfl
theorem p4_4 : ∀ feat, Dec feat p4 4 (FV7z.mk .mov 64 [gr 64 2, Src.opd 64 (.r 13)] 3) := by dec_rfl
theorem p4_7 : ∀ feat, Dec feat p4 7 (FV7z.mk .mov 64 [gr 64 7, Src.opd 64 (.r 3)] 3) := by dec_rfl

/-- What the stretch does. -/
def o4 : List Op := [
  Op.ld 64 6 (some 12) none 1 0,
  Op.mov 64 2 (.r 13),
  Op.mov 64 7 (.r 3)]

theorem b4 (prof : Profile) : Blk prof p4 0 10 o4 :=
  .cons (p4_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p4_4 _) (OpI.mov (.r 13) (.inr rfl)) (by decide) <|
  .cons (p4_7 _) (OpI.mov (.r 3) (.inr rfl)) (by decide) <|
  .nil 10

/-- The stretch at `121`. -/
def p5 : List Byte := [
  0x48, 0x83, 0xf8, 0xff]

theorem p5_0 : ∀ feat, Dec feat p5 0 (FV7z.mk .cmp 64 [gr 64 0, Src.opd 64 (.i 18446744073709551615)] 4) := by dec_rfl

/-- What the stretch does. -/
def o5 : List Op := [
  Op.cmp 64 0 (.i 18446744073709551615)]

theorem b5 (prof : Profile) : Blk prof p5 0 4 o5 :=
  .cons (p5_0 _) (OpI.cmp (.i 18446744073709551615) (.inr rfl)) (by decide) <|
  .nil 4

def j4 : List Byte := [0x0f, 0x84, 0xd5, 0x00, 0x00, 0x00]
theorem j4_0 : ∀ feat, Dec feat j4 0 (FV7z.mk (.jcc 4) 64 [.rel 213] 6) := by dec_rfl

/-- The stretch at `131`. -/
def p6 : List Byte := [
  0x4c, 0x8b, 0x65, 0x00, 0x89, 0x45, 0x08, 0x89, 0xc0, 0x41, 0xc7, 0x04, 0x84, 0x00, 0x00, 0x00,
  0x00, 0x41, 0x8b, 0x04, 0x24, 0x85, 0xc0]

theorem p6_0 : ∀ feat, Dec feat p6 0 (FV7z.mk .mov 64 [gr 64 12, .mem (mg (some 5) none 1 0 64)] 4) := by dec_rfl
theorem p6_4 : ∀ feat, Dec feat p6 4 (FV7z.mk .mov 32 [.mem (mg (some 5) none 1 8 32), gr 32 0] 3) := by dec_rfl
theorem p6_7 : ∀ feat, Dec feat p6 7 (FV7z.mk .mov 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl
theorem p6_9 : ∀ feat, Dec feat p6 9 (FV7z.mk .mov 32 [.mem (mg (some 12) (some 0) 4 0 32), .imm 32 0] 8) := by dec_rfl
theorem p6_17 : ∀ feat, Dec feat p6 17 (FV7z.mk .mov 32 [gr 32 0, .mem (mg (some 12) none 1 0 32)] 4) := by dec_rfl
theorem p6_21 : ∀ feat, Dec feat p6 21 (FV7z.mk .test 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl

/-- What the stretch does. -/
def o6 : List Op := [
  Op.ld 64 12 (some 5) none 1 0,
  Op.st 32 (some 5) none 1 8 0,
  Op.mov 32 0 (.r 0),
  Op.sti 32 (some 12) (some 0) 4 0 0,
  Op.ld 32 0 (some 12) none 1 0,
  Op.test 32 0 (.r 0)]

theorem b6 (prof : Profile) : Blk prof p6 0 23 o6 :=
  .cons (p6_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p6_4 _) (OpI.st (.inr (.inr (.inl rfl)))) (by decide) <|
  .cons (p6_7 _) (OpI.mov (.r 0) (.inl rfl)) (by decide) <|
  .cons (p6_9 _) (OpI.sti (.inr (.inr (.inl rfl)))) (by decide) <|
  .cons (p6_17 _) (OpI.ld (.inl rfl)) (by decide) <|
  .cons (p6_21 _) (OpI.test (.r 0) (.inl rfl)) (by decide) <|
  .nil 23

def j5 : List Byte := [0x0f, 0x84, 0xf0, 0x00, 0x00, 0x00]
theorem j5_0 : ∀ feat, Dec feat j5 0 (FV7z.mk (.jcc 4) 64 [.rel 240] 6) := by dec_rfl

/-- The stretch at `160`. -/
def p7 : List Byte := [
  0x4c, 0x89, 0xe6, 0x31, 0xdb]

theorem p7_0 : ∀ feat, Dec feat p7 0 (FV7z.mk .mov 64 [gr 64 6, Src.opd 64 (.r 12)] 3) := by dec_rfl
theorem p7_3 : ∀ feat, Dec feat p7 3 (FV7z.mk .xor 32 [gr 32 3, Src.opd 32 (.r 3)] 2) := by dec_rfl

/-- What the stretch does. -/
def o7 : List Op := [
  Op.mov 64 6 (.r 12),
  Op.xor 32 3 (.r 3)]

theorem b7 (prof : Profile) : Blk prof p7 0 5 o7 :=
  .cons (p7_0 _) (OpI.mov (.r 12) (.inr rfl)) (by decide) <|
  .cons (p7_3 _) (OpI.xor (.r 3) (.inl rfl)) (by decide) <|
  .nil 5

def j6 : List Byte := [0xeb, 0x1c]
theorem j6_0 : ∀ feat, Dec feat j6 0 (FV7z.mk .jmp 64 [.rel 28] 2) := by dec_rfl

/-- The stretch at `176`. -/
def p8 : List Byte := [
  0x8b, 0x46, 0x04, 0x48, 0x83, 0xc6, 0x04, 0x48, 0x83, 0xc3, 0x01, 0x85, 0xc0]

theorem p8_0 : ∀ feat, Dec feat p8 0 (FV7z.mk .mov 32 [gr 32 0, .mem (mg (some 6) none 1 4 32)] 3) := by dec_rfl
theorem p8_3 : ∀ feat, Dec feat p8 3 (FV7z.mk .add 64 [gr 64 6, Src.opd 64 (.i 4)] 4) := by dec_rfl
theorem p8_7 : ∀ feat, Dec feat p8 7 (FV7z.mk .add 64 [gr 64 3, Src.opd 64 (.i 1)] 4) := by dec_rfl
theorem p8_11 : ∀ feat, Dec feat p8 11 (FV7z.mk .test 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl

/-- What the stretch does. -/
def o8 : List Op := [
  Op.ld 32 0 (some 6) none 1 4,
  Op.add 64 6 (.i 4),
  Op.add 64 3 (.i 1),
  Op.test 32 0 (.r 0)]

theorem b8 (prof : Profile) : Blk prof p8 0 13 o8 :=
  .cons (p8_0 _) (OpI.ld (.inl rfl)) (by decide) <|
  .cons (p8_3 _) (OpI.add (.i 4) (.inr rfl)) (by decide) <|
  .cons (p8_7 _) (OpI.add (.i 1) (.inr rfl)) (by decide) <|
  .cons (p8_11 _) (OpI.test (.r 0) (.inl rfl)) (by decide) <|
  .nil 13

def j7 : List Byte := [0x0f, 0x84, 0xcd, 0x00, 0x00, 0x00]
theorem j7_0 : ∀ feat, Dec feat j7 0 (FV7z.mk (.jcc 4) 64 [.rel 205] 6) := by dec_rfl

/-- The stretch at `195`. -/
def p9 : List Byte := [
  0x2d, 0x00, 0x00, 0x01, 0x00, 0x3d, 0xff, 0xff, 0x0f, 0x00]

theorem p9_0 : ∀ feat, Dec feat p9 0 (FV7z.mk .sub 32 [gr 32 0, Src.opd 32 (.i 65536)] 5) := by dec_rfl
theorem p9_5 : ∀ feat, Dec feat p9 5 (FV7z.mk .cmp 32 [gr 32 0, Src.opd 32 (.i 1048575)] 5) := by dec_rfl

/-- What the stretch does. -/
def o9 : List Op := [
  Op.sub 32 0 (.i 65536),
  Op.cmp 32 0 (.i 1048575)]

theorem b9 (prof : Profile) : Blk prof p9 0 10 o9 :=
  .cons (p9_0 _) (OpI.sub (.i 65536) (.inl rfl)) (by decide) <|
  .cons (p9_5 _) (OpI.cmp (.i 1048575) (.inl rfl)) (by decide) <|
  .nil 10

def j8 : List Byte := [0x77, 0xe1]
theorem j8_0 : ∀ feat, Dec feat j8 0 (FV7z.mk (.jcc 7) 64 [.rel 18446744073709551585] 2) := by dec_rfl

/-- The stretch at `207`. -/
def p10 : List Byte := [
  0x48, 0x89, 0xe7]

theorem p10_0 : ∀ feat, Dec feat p10 0 (FV7z.mk .mov 64 [gr 64 7, Src.opd 64 (.r 4)] 3) := by dec_rfl

/-- What the stretch does. -/
def o10 : List Op := [
  Op.mov 64 7 (.r 4)]

theorem b10 (prof : Profile) : Blk prof p10 0 3 o10 :=
  .cons (p10_0 _) (OpI.mov (.r 4) (.inr rfl)) (by decide) <|
  .nil 3

/-- The stretch at `215`. -/
def p11 : List Byte := [
  0x48, 0x8b, 0x3c, 0x24, 0x8b, 0x07, 0x48, 0x8d, 0x77, 0x04, 0x85, 0xc0]

theorem p11_0 : ∀ feat, Dec feat p11 0 (FV7z.mk .mov 64 [gr 64 7, .mem (mg (some 4) none 1 0 64)] 4) := by dec_rfl
theorem p11_4 : ∀ feat, Dec feat p11 4 (FV7z.mk .mov 32 [gr 32 0, .mem (mg (some 7) none 1 0 32)] 2) := by dec_rfl
theorem p11_6 : ∀ feat, Dec feat p11 6 (FV7z.mk .lea 64 [gr 64 6, .mem (mg (some 7) none 1 4 0)] 4) := by dec_rfl
theorem p11_10 : ∀ feat, Dec feat p11 10 (FV7z.mk .test 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl

/-- What the stretch does. -/
def o11 : List Op := [
  Op.ld 64 7 (some 4) none 1 0,
  Op.ld 32 0 (some 7) none 1 0,
  Op.lea 64 6 (some 7) none 1 4,
  Op.test 32 0 (.r 0)]

theorem b11 (prof : Profile) : Blk prof p11 0 12 o11 :=
  .cons (p11_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p11_4 _) (OpI.ld (.inl rfl)) (by decide) <|
  .cons (p11_6 _) (OpI.lea (.inr rfl)) (by decide) <|
  .cons (p11_10 _) (OpI.test (.r 0) (.inl rfl)) (by decide) <|
  .nil 12

def j9 : List Byte := [0x0f, 0x84, 0xef, 0x00, 0x00, 0x00]
theorem j9_0 : ∀ feat, Dec feat j9 0 (FV7z.mk (.jcc 4) 64 [.rel 239] 6) := by dec_rfl

/-- The stretch at `233`. -/
def p12 : List Byte := [
  0x49, 0x39, 0xdd]

theorem p12_0 : ∀ feat, Dec feat p12 0 (FV7z.mk .cmp 64 [gr 64 13, Src.opd 64 (.r 3)] 3) := by dec_rfl

/-- What the stretch does. -/
def o12 : List Op := [
  Op.cmp 64 13 (.r 3)]

theorem b12 (prof : Profile) : Blk prof p12 0 3 o12 :=
  .cons (p12_0 _) (OpI.cmp (.r 3) (.inr rfl)) (by decide) <|
  .nil 3

def j10 : List Byte := [0x75, 0x4a]
theorem j10_0 : ∀ feat, Dec feat j10 0 (FV7z.mk (.jcc 5) 64 [.rel 74] 2) := by dec_rfl

def j11 : List Byte := [0xe9, 0xe5, 0x00, 0x00, 0x00]
theorem j11_0 : ∀ feat, Dec feat j11 0 (FV7z.mk .jmp 64 [.rel 229] 5) := by dec_rfl

/-- The stretch at `248`. -/
def p13 : List Byte := [
  0x49, 0x39, 0xcd]

theorem p13_0 : ∀ feat, Dec feat p13 0 (FV7z.mk .cmp 64 [gr 64 13, Src.opd 64 (.r 1)] 3) := by dec_rfl

/-- What the stretch does. -/
def o13 : List Op := [
  Op.cmp 64 13 (.r 1)]

theorem b13 (prof : Profile) : Blk prof p13 0 3 o13 :=
  .cons (p13_0 _) (OpI.cmp (.r 1) (.inr rfl)) (by decide) <|
  .nil 3

def j12 : List Byte := [0x0f, 0x84, 0xd7, 0x00, 0x00, 0x00]
theorem j12_0 : ∀ feat, Dec feat j12 0 (FV7z.mk (.jcc 4) 64 [.rel 215] 6) := by dec_rfl

/-- The stretch at `257`. -/
def p14 : List Byte := [
  0xc1, 0xea, 0x0a, 0x25, 0xff, 0x03, 0x00, 0x00, 0x81, 0xc2, 0x00, 0xd8, 0x00, 0x00, 0x05, 0x00,
  0xdc, 0x00, 0x00, 0x41, 0x89, 0x14, 0x9c, 0x48, 0x83, 0xc3, 0x02]

theorem p14_0 : ∀ feat, Dec feat p14 0 (FV7z.mk .shr 32 [gr 32 2, Src.opd 8 (.i 10)] 3) := by dec_rfl
theorem p14_3 : ∀ feat, Dec feat p14 3 (FV7z.mk .and 32 [gr 32 0, Src.opd 32 (.i 1023)] 5) := by dec_rfl
theorem p14_8 : ∀ feat, Dec feat p14 8 (FV7z.mk .add 32 [gr 32 2, Src.opd 32 (.i 55296)] 6) := by dec_rfl
theorem p14_14 : ∀ feat, Dec feat p14 14 (FV7z.mk .add 32 [gr 32 0, Src.opd 32 (.i 56320)] 5) := by dec_rfl
theorem p14_19 : ∀ feat, Dec feat p14 19 (FV7z.mk .mov 32 [.mem (mg (some 12) (some 3) 4 0 32), gr 32 2] 4) := by dec_rfl
theorem p14_23 : ∀ feat, Dec feat p14 23 (FV7z.mk .add 64 [gr 64 3, Src.opd 64 (.i 2)] 4) := by dec_rfl

/-- What the stretch does. -/
def o14 : List Op := [
  Op.shr 2 (.i 10),
  Op.and 32 0 (.i 1023),
  Op.add 32 2 (.i 55296),
  Op.add 32 0 (.i 56320),
  Op.st 32 (some 12) (some 3) 4 0 2,
  Op.add 64 3 (.i 2)]

theorem b14 (prof : Profile) : Blk prof p14 0 27 o14 :=
  .cons (p14_0 _) (OpI.shr (.i 10)) (by decide) <|
  .cons (p14_3 _) (OpI.and (.i 1023) (.inl rfl)) (by decide) <|
  .cons (p14_8 _) (OpI.add (.i 55296) (.inl rfl)) (by decide) <|
  .cons (p14_14 _) (OpI.add (.i 56320) (.inl rfl)) (by decide) <|
  .cons (p14_19 _) (OpI.st (.inr (.inr (.inl rfl)))) (by decide) <|
  .cons (p14_23 _) (OpI.add (.i 2) (.inr rfl)) (by decide) <|
  .nil 27

/-- The stretch at `284`. -/
def p15 : List Byte := [
  0x48, 0x83, 0xc6, 0x04, 0x41, 0x89, 0x04, 0x8c, 0x8b, 0x46, 0xfc, 0x49, 0x39, 0xdd]

theorem p15_0 : ∀ feat, Dec feat p15 0 (FV7z.mk .add 64 [gr 64 6, Src.opd 64 (.i 4)] 4) := by dec_rfl
theorem p15_4 : ∀ feat, Dec feat p15 4 (FV7z.mk .mov 32 [.mem (mg (some 12) (some 1) 4 0 32), gr 32 0] 4) := by dec_rfl
theorem p15_8 : ∀ feat, Dec feat p15 8 (FV7z.mk .mov 32 [gr 32 0, .mem (mg (some 6) none 1 18446744073709551612 32)] 3) := by dec_rfl
theorem p15_11 : ∀ feat, Dec feat p15 11 (FV7z.mk .cmp 64 [gr 64 13, Src.opd 64 (.r 3)] 3) := by dec_rfl

/-- What the stretch does. -/
def o15 : List Op := [
  Op.add 64 6 (.i 4),
  Op.st 32 (some 12) (some 1) 4 0 0,
  Op.ld 32 0 (some 6) none 1 18446744073709551612,
  Op.cmp 64 13 (.r 3)]

theorem b15 (prof : Profile) : Blk prof p15 0 14 o15 :=
  .cons (p15_0 _) (OpI.add (.i 4) (.inr rfl)) (by decide) <|
  .cons (p15_4 _) (OpI.st (.inr (.inr (.inl rfl)))) (by decide) <|
  .cons (p15_8 _) (OpI.ld (.inl rfl)) (by decide) <|
  .cons (p15_11 _) (OpI.cmp (.r 3) (.inr rfl)) (by decide) <|
  .nil 14

def j13 : List Byte := [0x0f, 0x84, 0xa8, 0x00, 0x00, 0x00]
theorem j13_0 : ∀ feat, Dec feat j13 0 (FV7z.mk (.jcc 4) 64 [.rel 168] 6) := by dec_rfl

/-- The stretch at `304`. -/
def p16 : List Byte := [
  0x85, 0xc0]

theorem p16_0 : ∀ feat, Dec feat p16 0 (FV7z.mk .test 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl

/-- What the stretch does. -/
def o16 : List Op := [
  Op.test 32 0 (.r 0)]

theorem b16 (prof : Profile) : Blk prof p16 0 2 o16 :=
  .cons (p16_0 _) (OpI.test (.r 0) (.inl rfl)) (by decide) <|
  .nil 2

def j14 : List Byte := [0x0f, 0x84, 0xa0, 0x00, 0x00, 0x00]
theorem j14_0 : ∀ feat, Dec feat j14 0 (FV7z.mk (.jcc 4) 64 [.rel 160] 6) := by dec_rfl

/-- The stretch at `312`. -/
def p17 : List Byte := [
  0x8d, 0x90, 0x00, 0x00, 0xff, 0xff, 0x48, 0x8d, 0x4b, 0x01, 0x81, 0xfa, 0xff, 0xff, 0x0f, 0x00]

theorem p17_0 : ∀ feat, Dec feat p17 0 (FV7z.mk .lea 32 [gr 32 2, .mem (mg (some 0) none 1 18446744073709486080 0)] 6) := by dec_rfl
theorem p17_6 : ∀ feat, Dec feat p17 6 (FV7z.mk .lea 64 [gr 64 1, .mem (mg (some 3) none 1 1 0)] 4) := by dec_rfl
theorem p17_10 : ∀ feat, Dec feat p17 10 (FV7z.mk .cmp 32 [gr 32 2, Src.opd 32 (.i 1048575)] 6) := by dec_rfl

/-- What the stretch does. -/
def o17 : List Op := [
  Op.lea 32 2 (some 0) none 1 18446744073709486080,
  Op.lea 64 1 (some 3) none 1 1,
  Op.cmp 32 2 (.i 1048575)]

theorem b17 (prof : Profile) : Blk prof p17 0 16 o17 :=
  .cons (p17_0 _) (OpI.lea (.inl rfl)) (by decide) <|
  .cons (p17_6 _) (OpI.lea (.inr rfl)) (by decide) <|
  .cons (p17_10 _) (OpI.cmp (.i 1048575) (.inl rfl)) (by decide) <|
  .nil 16

def j15 : List Byte := [0x76, 0xae]
theorem j15_0 : ∀ feat, Dec feat j15 0 (FV7z.mk (.jcc 6) 64 [.rel 18446744073709551534] 2) := by dec_rfl

/-- The stretch at `330`. -/
def p18 : List Byte := [
  0x48, 0x89, 0xca, 0x48, 0x89, 0xd9, 0x48, 0x89, 0xd3]

theorem p18_0 : ∀ feat, Dec feat p18 0 (FV7z.mk .mov 64 [gr 64 2, Src.opd 64 (.r 1)] 3) := by dec_rfl
theorem p18_3 : ∀ feat, Dec feat p18 3 (FV7z.mk .mov 64 [gr 64 1, Src.opd 64 (.r 3)] 3) := by dec_rfl
theorem p18_6 : ∀ feat, Dec feat p18 6 (FV7z.mk .mov 64 [gr 64 3, Src.opd 64 (.r 2)] 3) := by dec_rfl

/-- What the stretch does. -/
def o18 : List Op := [
  Op.mov 64 2 (.r 1),
  Op.mov 64 1 (.r 3),
  Op.mov 64 3 (.r 2)]

theorem b18 (prof : Profile) : Blk prof p18 0 9 o18 :=
  .cons (p18_0 _) (OpI.mov (.r 1) (.inr rfl)) (by decide) <|
  .cons (p18_3 _) (OpI.mov (.r 3) (.inr rfl)) (by decide) <|
  .cons (p18_6 _) (OpI.mov (.r 2) (.inr rfl)) (by decide) <|
  .nil 9

def j16 : List Byte := [0xeb, 0xc7]
theorem j16_0 : ∀ feat, Dec feat j16 0 (FV7z.mk .jmp 64 [.rel 18446744073709551559] 2) := by dec_rfl

/-- The stretch at `344`. -/
def p19 : List Byte := [
  0x49, 0x8b, 0x34, 0x24, 0x31, 0xd2, 0x0f, 0xb6, 0x06, 0x84, 0xc0]

theorem p19_0 : ∀ feat, Dec feat p19 0 (FV7z.mk .mov 64 [gr 64 6, .mem (mg (some 12) none 1 0 64)] 4) := by dec_rfl
theorem p19_4 : ∀ feat, Dec feat p19 4 (FV7z.mk .xor 32 [gr 32 2, Src.opd 32 (.r 2)] 2) := by dec_rfl
theorem p19_6 : ∀ feat, Dec feat p19 6 (FV7z.mk .movzx 32 [gr 32 0, .mem (mg (some 6) none 1 0 8)] 3) := by dec_rfl
theorem p19_9 : ∀ feat, Dec feat p19 9 (FV7z.mk .test 8 [gr 8 0, Src.opd 8 (.r 0)] 2) := by dec_rfl

/-- What the stretch does. -/
def o19 : List Op := [
  Op.ld 64 6 (some 12) none 1 0,
  Op.xor 32 2 (.r 2),
  Op.ldzx 8 0 (some 6) none 1 0,
  Op.test 8 0 (.r 0)]

theorem b19 (prof : Profile) : Blk prof p19 0 11 o19 :=
  .cons (p19_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p19_4 _) (OpI.xor (.r 2) (.inl rfl)) (by decide) <|
  .cons (p19_6 _) (OpI.ldzx (.inl rfl)) (by decide) <|
  .cons (p19_9 _) (OpI.test8 (.r 0)) (by decide) <|
  .nil 11

def j17 : List Byte := [0x74, 0x22]
theorem j17_0 : ∀ feat, Dec feat j17 0 (FV7z.mk (.jcc 4) 64 [.rel 34] 2) := by dec_rfl

/-- The stretch at `357`. -/
def p20 : List Byte := [
  0x31, 0xc9, 0x66, 0x0f, 0x1f, 0x84, 0x00, 0x00, 0x00, 0x00, 0x00]

theorem p20_0 : ∀ feat, Dec feat p20 0 (FV7z.mk .xor 32 [gr 32 1, Src.opd 32 (.r 1)] 2) := by dec_rfl
theorem p20_2 : ∀ feat, Dec feat p20 2 (FV7z.mk .nop 16 [.mem (mg (some 0) (some 0) 1 0 16)] 9) := by dec_rfl

/-- What the stretch does. -/
def o20 : List Op := [
  Op.xor 32 1 (.r 1),
  Op.nop]

theorem b20 (prof : Profile) : Blk prof p20 0 11 o20 :=
  .cons (p20_0 _) (OpI.xor (.r 1) (.inl rfl)) (by decide) <|
  .cons (p20_2 _) (OpI.nop) (by decide) <|
  .nil 11

/-- The stretch at `368`. -/
def p21 : List Byte := [
  0x0f, 0xb6, 0xc0, 0x83, 0xc2, 0x01, 0x89, 0x04, 0x8b, 0x89, 0xd1, 0x0f, 0xb6, 0x04, 0x0e, 0x84,
  0xc0]

theorem p21_0 : ∀ feat, Dec feat p21 0 (FV7z.mk .movzx 32 [gr 32 0, gr 8 0] 3) := by dec_rfl
theorem p21_3 : ∀ feat, Dec feat p21 3 (FV7z.mk .add 32 [gr 32 2, Src.opd 32 (.i 1)] 3) := by dec_rfl
theorem p21_6 : ∀ feat, Dec feat p21 6 (FV7z.mk .mov 32 [.mem (mg (some 3) (some 1) 4 0 32), gr 32 0] 3) := by dec_rfl
theorem p21_9 : ∀ feat, Dec feat p21 9 (FV7z.mk .mov 32 [gr 32 1, Src.opd 32 (.r 2)] 2) := by dec_rfl
theorem p21_11 : ∀ feat, Dec feat p21 11 (FV7z.mk .movzx 32 [gr 32 0, .mem (mg (some 6) (some 1) 1 0 8)] 4) := by dec_rfl
theorem p21_15 : ∀ feat, Dec feat p21 15 (FV7z.mk .test 8 [gr 8 0, Src.opd 8 (.r 0)] 2) := by dec_rfl

/-- What the stretch does. -/
def o21 : List Op := [
  Op.zxr 0 0,
  Op.add 32 2 (.i 1),
  Op.st 32 (some 3) (some 1) 4 0 0,
  Op.mov 32 1 (.r 2),
  Op.ldzx 8 0 (some 6) (some 1) 1 0,
  Op.test 8 0 (.r 0)]

theorem b21 (prof : Profile) : Blk prof p21 0 17 o21 :=
  .cons (p21_0 _) (OpI.zxr) (by decide) <|
  .cons (p21_3 _) (OpI.add (.i 1) (.inl rfl)) (by decide) <|
  .cons (p21_6 _) (OpI.st (.inr (.inr (.inl rfl)))) (by decide) <|
  .cons (p21_9 _) (OpI.mov (.r 2) (.inl rfl)) (by decide) <|
  .cons (p21_11 _) (OpI.ldzx (.inl rfl)) (by decide) <|
  .cons (p21_15 _) (OpI.test8 (.r 0)) (by decide) <|
  .nil 17

def j18 : List Byte := [0x75, 0xed]
theorem j18_0 : ∀ feat, Dec feat j18 0 (FV7z.mk (.jcc 5) 64 [.rel 18446744073709551597] 2) := by dec_rfl

/-- The stretch at `387`. -/
def p22 : List Byte := [
  0x48, 0x8d, 0x1c, 0x8b]

theorem p22_0 : ∀ feat, Dec feat p22 0 (FV7z.mk .lea 64 [gr 64 3, .mem (mg (some 3) (some 1) 4 0 0)] 4) := by dec_rfl

/-- What the stretch does. -/
def o22 : List Op := [
  Op.lea 64 3 (some 3) (some 1) 4 0]

theorem b22 (prof : Profile) : Blk prof p22 0 4 o22 :=
  .cons (p22_0 _) (OpI.lea (.inr rfl)) (by decide) <|
  .nil 4

/-- The stretch at `391`. -/
def p23 : List Byte := [
  0xc7, 0x03, 0x00, 0x00, 0x00, 0x00, 0x89, 0x55, 0x08]

theorem p23_0 : ∀ feat, Dec feat p23 0 (FV7z.mk .mov 32 [.mem (mg (some 3) none 1 0 32), .imm 32 0] 6) := by dec_rfl
theorem p23_6 : ∀ feat, Dec feat p23 6 (FV7z.mk .mov 32 [.mem (mg (some 5) none 1 8 32), gr 32 2] 3) := by dec_rfl

/-- What the stretch does. -/
def o23 : List Op := [
  Op.sti 32 (some 3) none 1 0 0,
  Op.st 32 (some 5) none 1 8 2]

theorem b23 (prof : Profile) : Blk prof p23 0 9 o23 :=
  .cons (p23_0 _) (OpI.sti (.inr (.inr (.inl rfl)))) (by decide) <|
  .cons (p23_6 _) (OpI.st (.inr (.inr (.inl rfl)))) (by decide) <|
  .nil 9

/-- The stretch at `400`. -/
def p24 : List Byte := [
  0x48, 0x8b, 0x44, 0x24, 0x18, 0x64, 0x48, 0x33, 0x04, 0x25, 0x28, 0x00, 0x00, 0x00]

theorem p24_0 : ∀ feat, Dec feat p24 0 (FV7z.mk .mov 64 [gr 64 0, .mem (mg (some 4) none 1 24 64)] 5) := by dec_rfl
theorem p24_5 : ∀ feat, Dec feat p24 5 (FV7z.mk .xor 64 [gr 64 0, .mem (mf none none 1 40 64)] 9) := by dec_rfl

/-- What the stretch does. -/
def o24 (fb : Addr) : List Op := [
  Op.ld 64 0 (some 4) none 1 24,
  Op.xormf fb 64 0 none none 1 40]

theorem b24 (prof : Profile) (fb : Addr) : BlkF prof p24 (0x450bf0 : Addr) fb 0 14 (o24 fb) :=
  .cons (p24_0 _) (((OpI.ld (.inr rfl)).at _).fs _) (by decide) <|
  .cons (p24_5 _) (OpIF.xormf (.inr rfl)) (by decide) <|
  .nil 14

def j19 : List Byte := [0x75, 0x4f]
theorem j19_0 : ∀ feat, Dec feat j19 0 (FV7z.mk (.jcc 5) 64 [.rel 79] 2) := by dec_rfl

/-- The stretch at `416`. -/
def p25 : List Byte := [
  0x48, 0x83, 0xc4, 0x28, 0x5b, 0x5d, 0x41, 0x5c, 0x41, 0x5d]

theorem p25_0 : ∀ feat, Dec feat p25 0 (FV7z.mk .add 64 [gr 64 4, Src.opd 64 (.i 40)] 4) := by dec_rfl
theorem p25_4 : ∀ feat, Dec feat p25 4 (FV7z.mk .pop 64 [gr 64 3] 1) := by dec_rfl
theorem p25_5 : ∀ feat, Dec feat p25 5 (FV7z.mk .pop 64 [gr 64 5] 1) := by dec_rfl
theorem p25_6 : ∀ feat, Dec feat p25 6 (FV7z.mk .pop 64 [gr 64 12] 2) := by dec_rfl
theorem p25_8 : ∀ feat, Dec feat p25 8 (FV7z.mk .pop 64 [gr 64 13] 2) := by dec_rfl

/-- What the stretch does. -/
def o25 : List Op := [
  Op.add 64 4 (.i 40),
  Op.pop 3,
  Op.pop 5,
  Op.pop 12,
  Op.pop 13]

theorem b25 (prof : Profile) : Blk prof p25 0 10 o25 :=
  .cons (p25_0 _) (OpI.add (.i 40) (.inr rfl)) (by decide) <|
  .cons (p25_4 _) (OpI.pop) (by decide) <|
  .cons (p25_5 _) (OpI.pop) (by decide) <|
  .cons (p25_6 _) (OpI.pop) (by decide) <|
  .cons (p25_8 _) (OpI.pop) (by decide) <|
  .nil 10

/-- The stretch at `432`. -/
def p26 : List Byte := [
  0x48, 0x89, 0xee, 0x4c, 0x89, 0xe7]

theorem p26_0 : ∀ feat, Dec feat p26 0 (FV7z.mk .mov 64 [gr 64 6, Src.opd 64 (.r 5)] 3) := by dec_rfl
theorem p26_3 : ∀ feat, Dec feat p26 3 (FV7z.mk .mov 64 [gr 64 7, Src.opd 64 (.r 12)] 3) := by dec_rfl

/-- What the stretch does. -/
def o26 : List Op := [
  Op.mov 64 6 (.r 5),
  Op.mov 64 7 (.r 12)]

theorem b26 (prof : Profile) : Blk prof p26 0 6 o26 :=
  .cons (p26_0 _) (OpI.mov (.r 5) (.inr rfl)) (by decide) <|
  .cons (p26_3 _) (OpI.mov (.r 12) (.inr rfl)) (by decide) <|
  .nil 6

def j20 : List Byte := [0xeb, 0xd3]
theorem j20_0 : ∀ feat, Dec feat j20 0 (FV7z.mk .jmp 64 [.rel 18446744073709551571] 2) := by dec_rfl

/-- The stretch at `448`. -/
def p27 : List Byte := [
  0x44, 0x89, 0xee]

theorem p27_0 : ∀ feat, Dec feat p27 0 (FV7z.mk .mov 32 [gr 32 6, Src.opd 32 (.r 13)] 3) := by dec_rfl

/-- What the stretch does. -/
def o27 : List Op := [
  Op.mov 32 6 (.r 13)]

theorem b27 (prof : Profile) : Blk prof p27 0 3 o27 :=
  .cons (p27_0 _) (OpI.mov (.r 13) (.inl rfl)) (by decide) <|
  .nil 3

/-- The stretch at `456`. -/
def p28 : List Byte := [
  0x48, 0x8b, 0x5d, 0x00]

theorem p28_0 : ∀ feat, Dec feat p28 0 (FV7z.mk .mov 64 [gr 64 3, .mem (mg (some 5) none 1 0 64)] 4) := by dec_rfl

/-- What the stretch does. -/
def o28 : List Op := [
  Op.ld 64 3 (some 5) none 1 0]

theorem b28 (prof : Profile) : Blk prof p28 0 4 o28 :=
  .cons (p28_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .nil 4

def j21 : List Byte := [0xe9, 0x99, 0xfe, 0xff, 0xff]
theorem j21_0 : ∀ feat, Dec feat j21 0 (FV7z.mk .jmp 64 [.rel 18446744073709551257] 5) := by dec_rfl

/-- The stretch at `472`. -/
def p29 : List Byte := [
  0x48, 0x8b, 0x45, 0x00, 0x89, 0x5d, 0x08, 0x89, 0xdb, 0xc7, 0x04, 0x98, 0x00, 0x00, 0x00, 0x00]

theorem p29_0 : ∀ feat, Dec feat p29 0 (FV7z.mk .mov 64 [gr 64 0, .mem (mg (some 5) none 1 0 64)] 4) := by dec_rfl
theorem p29_4 : ∀ feat, Dec feat p29 4 (FV7z.mk .mov 32 [.mem (mg (some 5) none 1 8 32), gr 32 3] 3) := by dec_rfl
theorem p29_7 : ∀ feat, Dec feat p29 7 (FV7z.mk .mov 32 [gr 32 3, Src.opd 32 (.r 3)] 2) := by dec_rfl
theorem p29_9 : ∀ feat, Dec feat p29 9 (FV7z.mk .mov 32 [.mem (mg (some 0) (some 3) 4 0 32), .imm 32 0] 7) := by dec_rfl

/-- What the stretch does. -/
def o29 : List Op := [
  Op.ld 64 0 (some 5) none 1 0,
  Op.st 32 (some 5) none 1 8 3,
  Op.mov 32 3 (.r 3),
  Op.sti 32 (some 0) (some 3) 4 0 0]

theorem b29 (prof : Profile) : Blk prof p29 0 16 o29 :=
  .cons (p29_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p29_4 _) (OpI.st (.inr (.inr (.inl rfl)))) (by decide) <|
  .cons (p29_7 _) (OpI.mov (.r 3) (.inl rfl)) (by decide) <|
  .cons (p29_9 _) (OpI.sti (.inr (.inr (.inl rfl)))) (by decide) <|
  .nil 16

def j22 : List Byte := [0xeb, 0xa1]
theorem j22_0 : ∀ feat, Dec feat j22 0 (FV7z.mk .jmp 64 [.rel 18446744073709551521] 2) := by dec_rfl

end FV7z.Mbu
