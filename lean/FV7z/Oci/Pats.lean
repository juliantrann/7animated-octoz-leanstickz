import FV7z.Lemmas.SpFs
import FV7z.Lemmas.BlkOps6
import FV7z.Lemmas.BlkOps3
/-!
# The stretches of straight-line code of `COpenCallbackImp::Init2` (PLAN.md §M, M1)

Each distinct stretch between labels and jumps (`p*`, 14 of them) and each distinct jump (`j*`, 7) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.Oci
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The stretch at `0`. -/
def p0 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0x41, 0x56, 0x41, 0x55, 0x49, 0x89, 0xf5, 0x41, 0x54, 0x49, 0x89, 0xd4,
  0x55, 0x53, 0x48, 0x89, 0xfb, 0x48, 0x81, 0xc7, 0x08, 0x01, 0x00, 0x00, 0x48, 0x83, 0xec, 0x20,
  0x64, 0x48, 0x8b, 0x04, 0x25, 0x28, 0x00, 0x00, 0x00, 0x48, 0x89, 0x44, 0x24, 0x18, 0x31, 0xc0]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem p0_4 : ∀ feat, Dec feat p0 4 (FV7z.mk .push 64 [gr 64 14] 2) := by dec_rfl
theorem p0_6 : ∀ feat, Dec feat p0 6 (FV7z.mk .push 64 [gr 64 13] 2) := by dec_rfl
theorem p0_8 : ∀ feat, Dec feat p0 8 (FV7z.mk .mov 64 [gr 64 13, Src.opd 64 (.r 6)] 3) := by dec_rfl
theorem p0_11 : ∀ feat, Dec feat p0 11 (FV7z.mk .push 64 [gr 64 12] 2) := by dec_rfl
theorem p0_13 : ∀ feat, Dec feat p0 13 (FV7z.mk .mov 64 [gr 64 12, Src.opd 64 (.r 2)] 3) := by dec_rfl
theorem p0_16 : ∀ feat, Dec feat p0 16 (FV7z.mk .push 64 [gr 64 5] 1) := by dec_rfl
theorem p0_17 : ∀ feat, Dec feat p0 17 (FV7z.mk .push 64 [gr 64 3] 1) := by dec_rfl
theorem p0_18 : ∀ feat, Dec feat p0 18 (FV7z.mk .mov 64 [gr 64 3, Src.opd 64 (.r 7)] 3) := by dec_rfl
theorem p0_21 : ∀ feat, Dec feat p0 21 (FV7z.mk .add 64 [gr 64 7, Src.opd 64 (.i 264)] 7) := by dec_rfl
theorem p0_28 : ∀ feat, Dec feat p0 28 (FV7z.mk .sub 64 [gr 64 4, Src.opd 64 (.i 32)] 4) := by dec_rfl
theorem p0_32 : ∀ feat, Dec feat p0 32 (FV7z.mk .mov 64 [gr 64 0, .mem (mf none none 1 40 64)] 9) := by dec_rfl
theorem p0_41 : ∀ feat, Dec feat p0 41 (FV7z.mk .mov 64 [.mem (mg (some 4) none 1 24 64), gr 64 0] 5) := by dec_rfl
theorem p0_46 : ∀ feat, Dec feat p0 46 (FV7z.mk .xor 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl

/-- What the stretch does. -/
def o0 (fb : Addr) : List Op := [
  Op.nop,
  Op.push 14,
  Op.push 13,
  Op.mov 64 13 (.r 6),
  Op.push 12,
  Op.mov 64 12 (.r 2),
  Op.push 5,
  Op.push 3,
  Op.mov 64 3 (.r 7),
  Op.add 64 7 (.i 264),
  Op.sub 64 4 (.i 32),
  Op.ldf fb 64 0 none none 1 40,
  Op.st 64 (some 4) none 1 24 0,
  Op.xor 32 0 (.r 0)]

theorem b0 (prof : Profile) (fb : Addr) : BlkF prof p0 (0x5b32e0 : Addr) fb 0 48 (o0 fb) :=
  .cons (p0_0 _) (((OpI.endbr).at _).fs _) (by decide) <|
  .cons (p0_4 _) (((OpI.push).at _).fs _) (by decide) <|
  .cons (p0_6 _) (((OpI.push).at _).fs _) (by decide) <|
  .cons (p0_8 _) (((OpI.mov (.r 6) (.inr rfl)).at _).fs _) (by decide) <|
  .cons (p0_11 _) (((OpI.push).at _).fs _) (by decide) <|
  .cons (p0_13 _) (((OpI.mov (.r 2) (.inr rfl)).at _).fs _) (by decide) <|
  .cons (p0_16 _) (((OpI.push).at _).fs _) (by decide) <|
  .cons (p0_17 _) (((OpI.push).at _).fs _) (by decide) <|
  .cons (p0_18 _) (((OpI.mov (.r 7) (.inr rfl)).at _).fs _) (by decide) <|
  .cons (p0_21 _) (((OpI.add (.i 264) (.inr rfl)).at _).fs _) (by decide) <|
  .cons (p0_28 _) (((OpI.sub (.i 32) (.inr rfl)).at _).fs _) (by decide) <|
  .cons (p0_32 _) (OpIF.ldf (.inr rfl)) (by decide) <|
  .cons (p0_41 _) (((OpI.st (.inr (.inr (.inr rfl)))).at _).fs _) (by decide) <|
  .cons (p0_46 _) (((OpI.xor (.r 0) (.inl rfl)).at _).fs _) (by decide) <|
  .nil 48

/-- The stretch at `53`. -/
def p1 : List Byte := [
  0x8b, 0x43, 0x38, 0x85, 0xc0]

theorem p1_0 : ∀ feat, Dec feat p1 0 (FV7z.mk .mov 32 [gr 32 0, .mem (mg (some 3) none 1 56 32)] 3) := by dec_rfl
theorem p1_3 : ∀ feat, Dec feat p1 3 (FV7z.mk .test 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl

/-- What the stretch does. -/
def o1 : List Op := [
  Op.ld 32 0 (some 3) none 1 56,
  Op.test 32 0 (.r 0)]

theorem b1 (prof : Profile) : Blk prof p1 0 5 o1 :=
  .cons (p1_0 _) (OpI.ld (.inl rfl)) (by decide) <|
  .cons (p1_3 _) (OpI.test (.r 0) (.inl rfl)) (by decide) <|
  .nil 5

def j0 : List Byte := [0x74, 0x3d]
theorem j0_0 : ∀ feat, Dec feat j0 0 (FV7z.mk (.jcc 4) 64 [.rel 61] 2) := by dec_rfl

/-- The stretch at `60`. -/
def p2 : List Byte := [
  0x8d, 0x68, 0xff, 0x48, 0xc1, 0xe5, 0x03, 0x0f, 0x1f, 0x44, 0x00, 0x00]

theorem p2_0 : ∀ feat, Dec feat p2 0 (FV7z.mk .lea 32 [gr 32 5, .mem (mg (some 0) none 1 18446744073709551615 0)] 3) := by dec_rfl
theorem p2_3 : ∀ feat, Dec feat p2 3 (FV7z.mk .shl 64 [gr 64 5, Src.opd 8 (.i 3)] 4) := by dec_rfl
theorem p2_7 : ∀ feat, Dec feat p2 7 (FV7z.mk .nop 32 [.mem (mg (some 0) (some 0) 1 0 32)] 5) := by dec_rfl

/-- What the stretch does. -/
def o2 : List Op := [
  Op.lea 32 5 (some 0) none 1 18446744073709551615,
  Op.shl64 5 (.i 3),
  Op.nop]

theorem b2 (prof : Profile) : Blk prof p2 0 12 o2 :=
  .cons (p2_0 _) (OpI.lea (.inl rfl)) (by decide) <|
  .cons (p2_3 _) (OpI.shl64 (.i 3)) (by decide) <|
  .cons (p2_7 _) (OpI.nop) (by decide) <|
  .nil 12

/-- The stretch at `72`. -/
def p3 : List Byte := [
  0x48, 0x8b, 0x43, 0x30, 0x4c, 0x8b, 0x34, 0x28, 0x4d, 0x85, 0xf6]

theorem p3_0 : ∀ feat, Dec feat p3 0 (FV7z.mk .mov 64 [gr 64 0, .mem (mg (some 3) none 1 48 64)] 4) := by dec_rfl
theorem p3_4 : ∀ feat, Dec feat p3 4 (FV7z.mk .mov 64 [gr 64 14, .mem (mg (some 0) (some 5) 1 0 64)] 4) := by dec_rfl
theorem p3_8 : ∀ feat, Dec feat p3 8 (FV7z.mk .test 64 [gr 64 14, Src.opd 64 (.r 14)] 3) := by dec_rfl

/-- What the stretch does. -/
def o3 : List Op := [
  Op.ld 64 0 (some 3) none 1 48,
  Op.ld 64 14 (some 0) (some 5) 1 0,
  Op.test 64 14 (.r 14)]

theorem b3 (prof : Profile) : Blk prof p3 0 11 o3 :=
  .cons (p3_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p3_4 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p3_8 _) (OpI.test (.r 14) (.inr rfl)) (by decide) <|
  .nil 11

def j1 : List Byte := [0x74, 0x1a]
theorem j1_0 : ∀ feat, Dec feat j1 0 (FV7z.mk (.jcc 4) 64 [.rel 26] 2) := by dec_rfl

/-- The stretch at `85`. -/
def p4 : List Byte := [
  0x49, 0x8b, 0x3e, 0x48, 0x85, 0xff]

theorem p4_0 : ∀ feat, Dec feat p4 0 (FV7z.mk .mov 64 [gr 64 7, .mem (mg (some 14) none 1 0 64)] 3) := by dec_rfl
theorem p4_3 : ∀ feat, Dec feat p4 3 (FV7z.mk .test 64 [gr 64 7, Src.opd 64 (.r 7)] 3) := by dec_rfl

/-- What the stretch does. -/
def o4 : List Op := [
  Op.ld 64 7 (some 14) none 1 0,
  Op.test 64 7 (.r 7)]

theorem b4 (prof : Profile) : Blk prof p4 0 6 o4 :=
  .cons (p4_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p4_3 _) (OpI.test (.r 7) (.inr rfl)) (by decide) <|
  .nil 6

def j2 : List Byte := [0x74, 0x05]
theorem j2_0 : ∀ feat, Dec feat j2 0 (FV7z.mk (.jcc 4) 64 [.rel 5] 2) := by dec_rfl

/-- The stretch at `98`. -/
def p5 : List Byte := [
  0xbe, 0x10, 0x00, 0x00, 0x00, 0x4c, 0x89, 0xf7]

theorem p5_0 : ∀ feat, Dec feat p5 0 (FV7z.mk .mov 32 [gr 32 6, Src.opd 32 (.i 16)] 5) := by dec_rfl
theorem p5_5 : ∀ feat, Dec feat p5 5 (FV7z.mk .mov 64 [gr 64 7, Src.opd 64 (.r 14)] 3) := by dec_rfl

/-- What the stretch does. -/
def o5 : List Op := [
  Op.mov 32 6 (.i 16),
  Op.mov 64 7 (.r 14)]

theorem b5 (prof : Profile) : Blk prof p5 0 8 o5 :=
  .cons (p5_0 _) (OpI.mov (.i 16) (.inl rfl)) (by decide) <|
  .cons (p5_5 _) (OpI.mov (.r 14) (.inr rfl)) (by decide) <|
  .nil 8

/-- The stretch at `111`. -/
def p6 : List Byte := [
  0x48, 0x83, 0xed, 0x08, 0x48, 0x83, 0xfd, 0xf8]

theorem p6_0 : ∀ feat, Dec feat p6 0 (FV7z.mk .sub 64 [gr 64 5, Src.opd 64 (.i 8)] 4) := by dec_rfl
theorem p6_4 : ∀ feat, Dec feat p6 4 (FV7z.mk .cmp 64 [gr 64 5, Src.opd 64 (.i 18446744073709551608)] 4) := by dec_rfl

/-- What the stretch does. -/
def o6 : List Op := [
  Op.sub 64 5 (.i 8),
  Op.cmp 64 5 (.i 18446744073709551608)]

theorem b6 (prof : Profile) : Blk prof p6 0 8 o6 :=
  .cons (p6_0 _) (OpI.sub (.i 8) (.inr rfl)) (by decide) <|
  .cons (p6_4 _) (OpI.cmp (.i 18446744073709551608) (.inr rfl)) (by decide) <|
  .nil 8

def j3 : List Byte := [0x75, 0xcf]
theorem j3_0 : ∀ feat, Dec feat j3 0 (FV7z.mk (.jcc 5) 64 [.rel 18446744073709551567] 2) := by dec_rfl

/-- The stretch at `121`. -/
def p7 : List Byte := [
  0x31, 0xc0, 0xc7, 0x43, 0x38, 0x00, 0x00, 0x00, 0x00, 0x48, 0x8d, 0x6b, 0x70, 0x4c, 0x89, 0xee,
  0xc7, 0x43, 0x48, 0x00, 0x00, 0x00, 0x00, 0x48, 0x89, 0xef, 0xc7, 0x43, 0x58, 0x00, 0x00, 0x00,
  0x00, 0x66, 0x89, 0x43, 0x2c]

theorem p7_0 : ∀ feat, Dec feat p7 0 (FV7z.mk .xor 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl
theorem p7_2 : ∀ feat, Dec feat p7 2 (FV7z.mk .mov 32 [.mem (mg (some 3) none 1 56 32), .imm 32 0] 7) := by dec_rfl
theorem p7_9 : ∀ feat, Dec feat p7 9 (FV7z.mk .lea 64 [gr 64 5, .mem (mg (some 3) none 1 112 0)] 4) := by dec_rfl
theorem p7_13 : ∀ feat, Dec feat p7 13 (FV7z.mk .mov 64 [gr 64 6, Src.opd 64 (.r 13)] 3) := by dec_rfl
theorem p7_16 : ∀ feat, Dec feat p7 16 (FV7z.mk .mov 32 [.mem (mg (some 3) none 1 72 32), .imm 32 0] 7) := by dec_rfl
theorem p7_23 : ∀ feat, Dec feat p7 23 (FV7z.mk .mov 64 [gr 64 7, Src.opd 64 (.r 5)] 3) := by dec_rfl
theorem p7_26 : ∀ feat, Dec feat p7 26 (FV7z.mk .mov 32 [.mem (mg (some 3) none 1 88 32), .imm 32 0] 7) := by dec_rfl
theorem p7_33 : ∀ feat, Dec feat p7 33 (FV7z.mk .mov 16 [.mem (mg (some 3) none 1 44 16), gr 16 0] 4) := by dec_rfl

/-- What the stretch does. -/
def o7 : List Op := [
  Op.xor 32 0 (.r 0),
  Op.sti 32 (some 3) none 1 56 0,
  Op.lea 64 5 (some 3) none 1 112,
  Op.mov 64 6 (.r 13),
  Op.sti 32 (some 3) none 1 72 0,
  Op.mov 64 7 (.r 5),
  Op.sti 32 (some 3) none 1 88 0,
  Op.st 16 (some 3) none 1 44 0]

theorem b7 (prof : Profile) : Blk prof p7 0 37 o7 :=
  .cons (p7_0 _) (OpI.xor (.r 0) (.inl rfl)) (by decide) <|
  .cons (p7_2 _) (OpI.sti (.inr (.inr (.inl rfl)))) (by decide) <|
  .cons (p7_9 _) (OpI.lea (.inr rfl)) (by decide) <|
  .cons (p7_13 _) (OpI.mov (.r 13) (.inr rfl)) (by decide) <|
  .cons (p7_16 _) (OpI.sti (.inr (.inr (.inl rfl)))) (by decide) <|
  .cons (p7_23 _) (OpI.mov (.r 5) (.inr rfl)) (by decide) <|
  .cons (p7_26 _) (OpI.sti (.inr (.inr (.inl rfl)))) (by decide) <|
  .cons (p7_33 _) (OpI.st (.inr (.inl rfl))) (by decide) <|
  .nil 37

/-- The stretch at `163`. -/
def p8 : List Byte := [
  0x48, 0x89, 0xe7, 0x4c, 0x89, 0xe2, 0x48, 0x89, 0xee]

theorem p8_0 : ∀ feat, Dec feat p8 0 (FV7z.mk .mov 64 [gr 64 7, Src.opd 64 (.r 4)] 3) := by dec_rfl
theorem p8_3 : ∀ feat, Dec feat p8 3 (FV7z.mk .mov 64 [gr 64 2, Src.opd 64 (.r 12)] 3) := by dec_rfl
theorem p8_6 : ∀ feat, Dec feat p8 6 (FV7z.mk .mov 64 [gr 64 6, Src.opd 64 (.r 5)] 3) := by dec_rfl

/-- What the stretch does. -/
def o8 : List Op := [
  Op.mov 64 7 (.r 4),
  Op.mov 64 2 (.r 12),
  Op.mov 64 6 (.r 5)]

theorem b8 (prof : Profile) : Blk prof p8 0 9 o8 :=
  .cons (p8_0 _) (OpI.mov (.r 4) (.inr rfl)) (by decide) <|
  .cons (p8_3 _) (OpI.mov (.r 12) (.inr rfl)) (by decide) <|
  .cons (p8_6 _) (OpI.mov (.r 5) (.inr rfl)) (by decide) <|
  .nil 9

/-- The stretch at `177`. -/
def p9 : List Byte := [
  0x48, 0x8b, 0x34, 0x24, 0xba, 0x01, 0x00, 0x00, 0x00, 0x48, 0x8d, 0xbb, 0x90, 0x00, 0x00, 0x00]

theorem p9_0 : ∀ feat, Dec feat p9 0 (FV7z.mk .mov 64 [gr 64 6, .mem (mg (some 4) none 1 0 64)] 4) := by dec_rfl
theorem p9_4 : ∀ feat, Dec feat p9 4 (FV7z.mk .mov 32 [gr 32 2, Src.opd 32 (.i 1)] 5) := by dec_rfl
theorem p9_9 : ∀ feat, Dec feat p9 9 (FV7z.mk .lea 64 [gr 64 7, .mem (mg (some 3) none 1 144 0)] 7) := by dec_rfl

/-- What the stretch does. -/
def o9 : List Op := [
  Op.ld 64 6 (some 4) none 1 0,
  Op.mov 32 2 (.i 1),
  Op.lea 64 7 (some 3) none 1 144]

theorem b9 (prof : Profile) : Blk prof p9 0 16 o9 :=
  .cons (p9_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p9_4 _) (OpI.mov (.i 1) (.inl rfl)) (by decide) <|
  .cons (p9_9 _) (OpI.lea (.inr rfl)) (by decide) <|
  .nil 16

/-- The stretch at `198`. -/
def p10 : List Byte := [
  0x48, 0x8b, 0x3c, 0x24, 0x89, 0xc3, 0x48, 0x85, 0xff]

theorem p10_0 : ∀ feat, Dec feat p10 0 (FV7z.mk .mov 64 [gr 64 7, .mem (mg (some 4) none 1 0 64)] 4) := by dec_rfl
theorem p10_4 : ∀ feat, Dec feat p10 4 (FV7z.mk .mov 32 [gr 32 3, Src.opd 32 (.r 0)] 2) := by dec_rfl
theorem p10_6 : ∀ feat, Dec feat p10 6 (FV7z.mk .test 64 [gr 64 7, Src.opd 64 (.r 7)] 3) := by dec_rfl

/-- What the stretch does. -/
def o10 : List Op := [
  Op.ld 64 7 (some 4) none 1 0,
  Op.mov 32 3 (.r 0),
  Op.test 64 7 (.r 7)]

theorem b10 (prof : Profile) : Blk prof p10 0 9 o10 :=
  .cons (p10_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p10_4 _) (OpI.mov (.r 0) (.inl rfl)) (by decide) <|
  .cons (p10_6 _) (OpI.test (.r 7) (.inr rfl)) (by decide) <|
  .nil 9

/-- The stretch at `214`. -/
def p11 : List Byte := [
  0x31, 0xc0, 0x84, 0xdb]

theorem p11_0 : ∀ feat, Dec feat p11 0 (FV7z.mk .xor 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl
theorem p11_2 : ∀ feat, Dec feat p11 2 (FV7z.mk .test 8 [gr 8 3, Src.opd 8 (.r 3)] 2) := by dec_rfl

/-- What the stretch does. -/
def o11 : List Op := [
  Op.xor 32 0 (.r 0),
  Op.test 8 3 (.r 3)]

theorem b11 (prof : Profile) : Blk prof p11 0 4 o11 :=
  .cons (p11_0 _) (OpI.xor (.r 0) (.inl rfl)) (by decide) <|
  .cons (p11_2 _) (OpI.test8 (.r 3)) (by decide) <|
  .nil 4

def j4 : List Byte := [0x74, 0x24]
theorem j4_0 : ∀ feat, Dec feat j4 0 (FV7z.mk (.jcc 4) 64 [.rel 36] 2) := by dec_rfl

/-- The stretch at `220`. -/
def p12 : List Byte := [
  0x48, 0x8b, 0x4c, 0x24, 0x18, 0x64, 0x48, 0x33, 0x0c, 0x25, 0x28, 0x00, 0x00, 0x00]

theorem p12_0 : ∀ feat, Dec feat p12 0 (FV7z.mk .mov 64 [gr 64 1, .mem (mg (some 4) none 1 24 64)] 5) := by dec_rfl
theorem p12_5 : ∀ feat, Dec feat p12 5 (FV7z.mk .xor 64 [gr 64 1, .mem (mf none none 1 40 64)] 9) := by dec_rfl

/-- What the stretch does. -/
def o12 (fb : Addr) : List Op := [
  Op.ld 64 1 (some 4) none 1 24,
  Op.xormf fb 64 1 none none 1 40]

theorem b12 (prof : Profile) (fb : Addr) : BlkF prof p12 (0x5b33bc : Addr) fb 0 14 (o12 fb) :=
  .cons (p12_0 _) (((OpI.ld (.inr rfl)).at _).fs _) (by decide) <|
  .cons (p12_5 _) (OpIF.xormf (.inr rfl)) (by decide) <|
  .nil 14

def j5 : List Byte := [0x75, 0x1b]
theorem j5_0 : ∀ feat, Dec feat j5 0 (FV7z.mk (.jcc 5) 64 [.rel 27] 2) := by dec_rfl

/-- The stretch at `236`. -/
def p13 : List Byte := [
  0x48, 0x83, 0xc4, 0x20, 0x5b, 0x5d, 0x41, 0x5c, 0x41, 0x5d, 0x41, 0x5e]

theorem p13_0 : ∀ feat, Dec feat p13 0 (FV7z.mk .add 64 [gr 64 4, Src.opd 64 (.i 32)] 4) := by dec_rfl
theorem p13_4 : ∀ feat, Dec feat p13 4 (FV7z.mk .pop 64 [gr 64 3] 1) := by dec_rfl
theorem p13_5 : ∀ feat, Dec feat p13 5 (FV7z.mk .pop 64 [gr 64 5] 1) := by dec_rfl
theorem p13_6 : ∀ feat, Dec feat p13 6 (FV7z.mk .pop 64 [gr 64 12] 2) := by dec_rfl
theorem p13_8 : ∀ feat, Dec feat p13 8 (FV7z.mk .pop 64 [gr 64 13] 2) := by dec_rfl
theorem p13_10 : ∀ feat, Dec feat p13 10 (FV7z.mk .pop 64 [gr 64 14] 2) := by dec_rfl

/-- What the stretch does. -/
def o13 : List Op := [
  Op.add 64 4 (.i 32),
  Op.pop 3,
  Op.pop 5,
  Op.pop 12,
  Op.pop 13,
  Op.pop 14]

theorem b13 (prof : Profile) : Blk prof p13 0 12 o13 :=
  .cons (p13_0 _) (OpI.add (.i 32) (.inr rfl)) (by decide) <|
  .cons (p13_4 _) (OpI.pop) (by decide) <|
  .cons (p13_5 _) (OpI.pop) (by decide) <|
  .cons (p13_6 _) (OpI.pop) (by decide) <|
  .cons (p13_8 _) (OpI.pop) (by decide) <|
  .cons (p13_10 _) (OpI.pop) (by decide) <|
  .nil 12

def j6 : List Byte := [0xeb, 0xd5]
theorem j6_0 : ∀ feat, Dec feat j6 0 (FV7z.mk .jmp 64 [.rel 18446744073709551573] 2) := by dec_rfl

end FV7z.Oci
