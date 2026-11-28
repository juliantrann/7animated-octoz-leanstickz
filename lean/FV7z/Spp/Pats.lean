import FV7z.Lemmas.SpFs
import FV7z.Lemmas.BlkOps12
import FV7z.Lemmas.BlkOps6
import FV7z.Lemmas.BlkOps3
/-!
# The stretches of straight-line code of `SplitPathToParts` (PLAN.md §M, M1)

Each distinct stretch between labels and jumps (`p*`, 36 of them) and each distinct jump (`j*`, 20) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.Spp
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The stretch at `0`. -/
def p0 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0x41, 0x57, 0x41, 0x56, 0x41, 0x55, 0x41, 0x54, 0x55, 0x48, 0x89, 0xf5,
  0x53, 0x48, 0x83, 0xec, 0x48, 0x48, 0x89, 0x7c, 0x24, 0x08, 0x64, 0x48, 0x8b, 0x04, 0x25, 0x28,
  0x00, 0x00, 0x00, 0x48, 0x89, 0x44, 0x24, 0x38, 0x31, 0xc0, 0x8b, 0x46, 0x08, 0x85, 0xc0]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem p0_4 : ∀ feat, Dec feat p0 4 (FV7z.mk .push 64 [gr 64 15] 2) := by dec_rfl
theorem p0_6 : ∀ feat, Dec feat p0 6 (FV7z.mk .push 64 [gr 64 14] 2) := by dec_rfl
theorem p0_8 : ∀ feat, Dec feat p0 8 (FV7z.mk .push 64 [gr 64 13] 2) := by dec_rfl
theorem p0_10 : ∀ feat, Dec feat p0 10 (FV7z.mk .push 64 [gr 64 12] 2) := by dec_rfl
theorem p0_12 : ∀ feat, Dec feat p0 12 (FV7z.mk .push 64 [gr 64 5] 1) := by dec_rfl
theorem p0_13 : ∀ feat, Dec feat p0 13 (FV7z.mk .mov 64 [gr 64 5, Src.opd 64 (.r 6)] 3) := by dec_rfl
theorem p0_16 : ∀ feat, Dec feat p0 16 (FV7z.mk .push 64 [gr 64 3] 1) := by dec_rfl
theorem p0_17 : ∀ feat, Dec feat p0 17 (FV7z.mk .sub 64 [gr 64 4, Src.opd 64 (.i 72)] 4) := by dec_rfl
theorem p0_21 : ∀ feat, Dec feat p0 21 (FV7z.mk .mov 64 [.mem (mg (some 4) none 1 8 64), gr 64 7] 5) := by dec_rfl
theorem p0_26 : ∀ feat, Dec feat p0 26 (FV7z.mk .mov 64 [gr 64 0, .mem (mf none none 1 40 64)] 9) := by dec_rfl
theorem p0_35 : ∀ feat, Dec feat p0 35 (FV7z.mk .mov 64 [.mem (mg (some 4) none 1 56 64), gr 64 0] 5) := by dec_rfl
theorem p0_40 : ∀ feat, Dec feat p0 40 (FV7z.mk .xor 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl
theorem p0_42 : ∀ feat, Dec feat p0 42 (FV7z.mk .mov 32 [gr 32 0, .mem (mg (some 6) none 1 8 32)] 3) := by dec_rfl
theorem p0_45 : ∀ feat, Dec feat p0 45 (FV7z.mk .test 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl

/-- What the stretch does. -/
def o0 (fb : Addr) : List Op := [
  Op.nop,
  Op.push 15,
  Op.push 14,
  Op.push 13,
  Op.push 12,
  Op.push 5,
  Op.mov 64 5 (.r 6),
  Op.push 3,
  Op.sub 64 4 (.i 72),
  Op.st 64 (some 4) none 1 8 7,
  Op.ldf fb 64 0 none none 1 40,
  Op.st 64 (some 4) none 1 56 0,
  Op.xor 32 0 (.r 0),
  Op.ld 32 0 (some 6) none 1 8,
  Op.test 32 0 (.r 0)]

theorem b0 (prof : Profile) (fb : Addr) : BlkF prof p0 (0x452500 : Addr) fb 0 47 (o0 fb) :=
  .cons (p0_0 _) (((OpI.endbr).at _).fs _) (by decide) <|
  .cons (p0_4 _) (((OpI.push).at _).fs _) (by decide) <|
  .cons (p0_6 _) (((OpI.push).at _).fs _) (by decide) <|
  .cons (p0_8 _) (((OpI.push).at _).fs _) (by decide) <|
  .cons (p0_10 _) (((OpI.push).at _).fs _) (by decide) <|
  .cons (p0_12 _) (((OpI.push).at _).fs _) (by decide) <|
  .cons (p0_13 _) (((OpI.mov (.r 6) (.inr rfl)).at _).fs _) (by decide) <|
  .cons (p0_16 _) (((OpI.push).at _).fs _) (by decide) <|
  .cons (p0_17 _) (((OpI.sub (.i 72) (.inr rfl)).at _).fs _) (by decide) <|
  .cons (p0_21 _) (((OpI.st (.inr (.inr (.inr rfl)))).at _).fs _) (by decide) <|
  .cons (p0_26 _) (OpIF.ldf (.inr rfl)) (by decide) <|
  .cons (p0_35 _) (((OpI.st (.inr (.inr (.inr rfl)))).at _).fs _) (by decide) <|
  .cons (p0_40 _) (((OpI.xor (.r 0) (.inl rfl)).at _).fs _) (by decide) <|
  .cons (p0_42 _) (((OpI.ld (.inl rfl)).at _).fs _) (by decide) <|
  .cons (p0_45 _) (((OpI.test (.r 0) (.inl rfl)).at _).fs _) (by decide) <|
  .nil 47

def j0 : List Byte := [0x74, 0x41]
theorem j0_0 : ∀ feat, Dec feat j0 0 (FV7z.mk (.jcc 4) 64 [.rel 65] 2) := by dec_rfl

/-- The stretch at `49`. -/
def p1 : List Byte := [
  0x8d, 0x58, 0xff, 0x48, 0xc1, 0xe3, 0x03, 0x0f, 0x1f, 0x84, 0x00, 0x00, 0x00, 0x00, 0x00]

theorem p1_0 : ∀ feat, Dec feat p1 0 (FV7z.mk .lea 32 [gr 32 3, .mem (mg (some 0) none 1 18446744073709551615 0)] 3) := by dec_rfl
theorem p1_3 : ∀ feat, Dec feat p1 3 (FV7z.mk .shl 64 [gr 64 3, Src.opd 8 (.i 3)] 4) := by dec_rfl
theorem p1_7 : ∀ feat, Dec feat p1 7 (FV7z.mk .nop 32 [.mem (mg (some 0) (some 0) 1 0 32)] 8) := by dec_rfl

/-- What the stretch does. -/
def o1 : List Op := [
  Op.lea 32 3 (some 0) none 1 18446744073709551615,
  Op.shl64 3 (.i 3),
  Op.nop]

theorem b1 (prof : Profile) : Blk prof p1 0 15 o1 :=
  .cons (p1_0 _) (OpI.lea (.inl rfl)) (by decide) <|
  .cons (p1_3 _) (OpI.shl64 (.i 3)) (by decide) <|
  .cons (p1_7 _) (OpI.nop) (by decide) <|
  .nil 15

/-- The stretch at `64`. -/
def p2 : List Byte := [
  0x48, 0x8b, 0x45, 0x00, 0x4c, 0x8b, 0x24, 0x18, 0x4d, 0x85, 0xe4]

theorem p2_0 : ∀ feat, Dec feat p2 0 (FV7z.mk .mov 64 [gr 64 0, .mem (mg (some 5) none 1 0 64)] 4) := by dec_rfl
theorem p2_4 : ∀ feat, Dec feat p2 4 (FV7z.mk .mov 64 [gr 64 12, .mem (mg (some 0) (some 3) 1 0 64)] 4) := by dec_rfl
theorem p2_8 : ∀ feat, Dec feat p2 8 (FV7z.mk .test 64 [gr 64 12, Src.opd 64 (.r 12)] 3) := by dec_rfl

/-- What the stretch does. -/
def o2 : List Op := [
  Op.ld 64 0 (some 5) none 1 0,
  Op.ld 64 12 (some 0) (some 3) 1 0,
  Op.test 64 12 (.r 12)]

theorem b2 (prof : Profile) : Blk prof p2 0 11 o2 :=
  .cons (p2_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p2_4 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p2_8 _) (OpI.test (.r 12) (.inr rfl)) (by decide) <|
  .nil 11

def j1 : List Byte := [0x74, 0x1b]
theorem j1_0 : ∀ feat, Dec feat j1 0 (FV7z.mk (.jcc 4) 64 [.rel 27] 2) := by dec_rfl

/-- The stretch at `77`. -/
def p3 : List Byte := [
  0x49, 0x8b, 0x3c, 0x24, 0x48, 0x85, 0xff]

theorem p3_0 : ∀ feat, Dec feat p3 0 (FV7z.mk .mov 64 [gr 64 7, .mem (mg (some 12) none 1 0 64)] 4) := by dec_rfl
theorem p3_4 : ∀ feat, Dec feat p3 4 (FV7z.mk .test 64 [gr 64 7, Src.opd 64 (.r 7)] 3) := by dec_rfl

/-- What the stretch does. -/
def o3 : List Op := [
  Op.ld 64 7 (some 12) none 1 0,
  Op.test 64 7 (.r 7)]

theorem b3 (prof : Profile) : Blk prof p3 0 7 o3 :=
  .cons (p3_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p3_4 _) (OpI.test (.r 7) (.inr rfl)) (by decide) <|
  .nil 7

def j2 : List Byte := [0x74, 0x05]
theorem j2_0 : ∀ feat, Dec feat j2 0 (FV7z.mk (.jcc 4) 64 [.rel 5] 2) := by dec_rfl

/-- The stretch at `91`. -/
def p4 : List Byte := [
  0xbe, 0x10, 0x00, 0x00, 0x00, 0x4c, 0x89, 0xe7]

theorem p4_0 : ∀ feat, Dec feat p4 0 (FV7z.mk .mov 32 [gr 32 6, Src.opd 32 (.i 16)] 5) := by dec_rfl
theorem p4_5 : ∀ feat, Dec feat p4 5 (FV7z.mk .mov 64 [gr 64 7, Src.opd 64 (.r 12)] 3) := by dec_rfl

/-- What the stretch does. -/
def o4 : List Op := [
  Op.mov 32 6 (.i 16),
  Op.mov 64 7 (.r 12)]

theorem b4 (prof : Profile) : Blk prof p4 0 8 o4 :=
  .cons (p4_0 _) (OpI.mov (.i 16) (.inl rfl)) (by decide) <|
  .cons (p4_5 _) (OpI.mov (.r 12) (.inr rfl)) (by decide) <|
  .nil 8

/-- The stretch at `104`. -/
def p5 : List Byte := [
  0x48, 0x83, 0xeb, 0x08, 0x48, 0x83, 0xfb, 0xf8]

theorem p5_0 : ∀ feat, Dec feat p5 0 (FV7z.mk .sub 64 [gr 64 3, Src.opd 64 (.i 8)] 4) := by dec_rfl
theorem p5_4 : ∀ feat, Dec feat p5 4 (FV7z.mk .cmp 64 [gr 64 3, Src.opd 64 (.i 18446744073709551608)] 4) := by dec_rfl

/-- What the stretch does. -/
def o5 : List Op := [
  Op.sub 64 3 (.i 8),
  Op.cmp 64 3 (.i 18446744073709551608)]

theorem b5 (prof : Profile) : Blk prof p5 0 8 o5 :=
  .cons (p5_0 _) (OpI.sub (.i 8) (.inr rfl)) (by decide) <|
  .cons (p5_4 _) (OpI.cmp (.i 18446744073709551608) (.inr rfl)) (by decide) <|
  .nil 8

def j3 : List Byte := [0x75, 0xce]
theorem j3_0 : ∀ feat, Dec feat j3 0 (FV7z.mk (.jcc 5) 64 [.rel 18446744073709551566] 2) := by dec_rfl

/-- The stretch at `114`. -/
def p6 : List Byte := [
  0x48, 0x8b, 0x5c, 0x24, 0x08, 0xc7, 0x45, 0x08, 0x00, 0x00, 0x00, 0x00, 0x44, 0x8b, 0x63, 0x08,
  0x45, 0x85, 0xe4]

theorem p6_0 : ∀ feat, Dec feat p6 0 (FV7z.mk .mov 64 [gr 64 3, .mem (mg (some 4) none 1 8 64)] 5) := by dec_rfl
theorem p6_5 : ∀ feat, Dec feat p6 5 (FV7z.mk .mov 32 [.mem (mg (some 5) none 1 8 32), .imm 32 0] 7) := by dec_rfl
theorem p6_12 : ∀ feat, Dec feat p6 12 (FV7z.mk .mov 32 [gr 32 12, .mem (mg (some 3) none 1 8 32)] 4) := by dec_rfl
theorem p6_16 : ∀ feat, Dec feat p6 16 (FV7z.mk .test 32 [gr 32 12, Src.opd 32 (.r 12)] 3) := by dec_rfl

/-- What the stretch does. -/
def o6 : List Op := [
  Op.ld 64 3 (some 4) none 1 8,
  Op.sti 32 (some 5) none 1 8 0,
  Op.ld 32 12 (some 3) none 1 8,
  Op.test 32 12 (.r 12)]

theorem b6 (prof : Profile) : Blk prof p6 0 19 o6 :=
  .cons (p6_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p6_5 _) (OpI.sti (.inr (.inr (.inl rfl)))) (by decide) <|
  .cons (p6_12 _) (OpI.ld (.inl rfl)) (by decide) <|
  .cons (p6_16 _) (OpI.test (.r 12) (.inl rfl)) (by decide) <|
  .nil 19

def j4 : List Byte := [0x75, 0x29]
theorem j4_0 : ∀ feat, Dec feat j4 0 (FV7z.mk (.jcc 5) 64 [.rel 41] 2) := by dec_rfl

/-- The stretch at `135`. -/
def p7 : List Byte := [
  0x48, 0x8b, 0x44, 0x24, 0x38, 0x64, 0x48, 0x33, 0x04, 0x25, 0x28, 0x00, 0x00, 0x00]

theorem p7_0 : ∀ feat, Dec feat p7 0 (FV7z.mk .mov 64 [gr 64 0, .mem (mg (some 4) none 1 56 64)] 5) := by dec_rfl
theorem p7_5 : ∀ feat, Dec feat p7 5 (FV7z.mk .xor 64 [gr 64 0, .mem (mf none none 1 40 64)] 9) := by dec_rfl

/-- What the stretch does. -/
def o7 (fb : Addr) : List Op := [
  Op.ld 64 0 (some 4) none 1 56,
  Op.xormf fb 64 0 none none 1 40]

theorem b7 (prof : Profile) (fb : Addr) : BlkF prof p7 (0x452587 : Addr) fb 0 14 (o7 fb) :=
  .cons (p7_0 _) (((OpI.ld (.inr rfl)).at _).fs _) (by decide) <|
  .cons (p7_5 _) (OpIF.xormf (.inr rfl)) (by decide) <|
  .nil 14

def j5 : List Byte := [0x0f, 0x85, 0x25, 0x02, 0x00, 0x00]
theorem j5_0 : ∀ feat, Dec feat j5 0 (FV7z.mk (.jcc 5) 64 [.rel 549] 6) := by dec_rfl

/-- The stretch at `155`. -/
def p8 : List Byte := [
  0x48, 0x83, 0xc4, 0x48, 0x5b, 0x5d, 0x41, 0x5c, 0x41, 0x5d, 0x41, 0x5e, 0x41, 0x5f]

theorem p8_0 : ∀ feat, Dec feat p8 0 (FV7z.mk .add 64 [gr 64 4, Src.opd 64 (.i 72)] 4) := by dec_rfl
theorem p8_4 : ∀ feat, Dec feat p8 4 (FV7z.mk .pop 64 [gr 64 3] 1) := by dec_rfl
theorem p8_5 : ∀ feat, Dec feat p8 5 (FV7z.mk .pop 64 [gr 64 5] 1) := by dec_rfl
theorem p8_6 : ∀ feat, Dec feat p8 6 (FV7z.mk .pop 64 [gr 64 12] 2) := by dec_rfl
theorem p8_8 : ∀ feat, Dec feat p8 8 (FV7z.mk .pop 64 [gr 64 13] 2) := by dec_rfl
theorem p8_10 : ∀ feat, Dec feat p8 10 (FV7z.mk .pop 64 [gr 64 14] 2) := by dec_rfl
theorem p8_12 : ∀ feat, Dec feat p8 12 (FV7z.mk .pop 64 [gr 64 15] 2) := by dec_rfl

/-- What the stretch does. -/
def o8 : List Op := [
  Op.add 64 4 (.i 72),
  Op.pop 3,
  Op.pop 5,
  Op.pop 12,
  Op.pop 13,
  Op.pop 14,
  Op.pop 15]

theorem b8 (prof : Profile) : Blk prof p8 0 14 o8 :=
  .cons (p8_0 _) (OpI.add (.i 72) (.inr rfl)) (by decide) <|
  .cons (p8_4 _) (OpI.pop) (by decide) <|
  .cons (p8_5 _) (OpI.pop) (by decide) <|
  .cons (p8_6 _) (OpI.pop) (by decide) <|
  .cons (p8_8 _) (OpI.pop) (by decide) <|
  .cons (p8_10 _) (OpI.pop) (by decide) <|
  .cons (p8_12 _) (OpI.pop) (by decide) <|
  .nil 14

/-- The stretch at `176`. -/
def p9 : List Byte := [
  0x4c, 0x8d, 0x7c, 0x24, 0x20, 0x4c, 0x89, 0xff]

theorem p9_0 : ∀ feat, Dec feat p9 0 (FV7z.mk .lea 64 [gr 64 15, .mem (mg (some 4) none 1 32 0)] 5) := by dec_rfl
theorem p9_5 : ∀ feat, Dec feat p9 5 (FV7z.mk .mov 64 [gr 64 7, Src.opd 64 (.r 15)] 3) := by dec_rfl

/-- What the stretch does. -/
def o9 : List Op := [
  Op.lea 64 15 (some 4) none 1 32,
  Op.mov 64 7 (.r 15)]

theorem b9 (prof : Profile) : Blk prof p9 0 8 o9 :=
  .cons (p9_0 _) (OpI.lea (.inr rfl)) (by decide) <|
  .cons (p9_5 _) (OpI.mov (.r 15) (.inr rfl)) (by decide) <|
  .nil 8

/-- The stretch at `189`. -/
def p10 : List Byte := [
  0x48, 0x8b, 0x03, 0x31, 0xc9, 0x31, 0xdb]

theorem p10_0 : ∀ feat, Dec feat p10 0 (FV7z.mk .mov 64 [gr 64 0, .mem (mg (some 3) none 1 0 64)] 3) := by dec_rfl
theorem p10_3 : ∀ feat, Dec feat p10 3 (FV7z.mk .xor 32 [gr 32 1, Src.opd 32 (.r 1)] 2) := by dec_rfl
theorem p10_5 : ∀ feat, Dec feat p10 5 (FV7z.mk .xor 32 [gr 32 3, Src.opd 32 (.r 3)] 2) := by dec_rfl

/-- What the stretch does. -/
def o10 : List Op := [
  Op.ld 64 0 (some 3) none 1 0,
  Op.xor 32 1 (.r 1),
  Op.xor 32 3 (.r 3)]

theorem b10 (prof : Profile) : Blk prof p10 0 7 o10 :=
  .cons (p10_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p10_3 _) (OpI.xor (.r 1) (.inl rfl)) (by decide) <|
  .cons (p10_5 _) (OpI.xor (.r 3) (.inl rfl)) (by decide) <|
  .nil 7

def j6 : List Byte := [0xeb, 0x17]
theorem j6_0 : ∀ feat, Dec feat j6 0 (FV7z.mk .jmp 64 [.rel 23] 2) := by dec_rfl

/-- The stretch at `208`. -/
def p11 : List Byte := [
  0x48, 0x83, 0xc3, 0x01, 0x41, 0x39, 0xd4]

theorem p11_0 : ∀ feat, Dec feat p11 0 (FV7z.mk .add 64 [gr 64 3, Src.opd 64 (.i 1)] 4) := by dec_rfl
theorem p11_4 : ∀ feat, Dec feat p11 4 (FV7z.mk .cmp 32 [gr 32 12, Src.opd 32 (.r 2)] 3) := by dec_rfl

/-- What the stretch does. -/
def o11 : List Op := [
  Op.add 64 3 (.i 1),
  Op.cmp 32 12 (.r 2)]

theorem b11 (prof : Profile) : Blk prof p11 0 7 o11 :=
  .cons (p11_0 _) (OpI.add (.i 1) (.inr rfl)) (by decide) <|
  .cons (p11_4 _) (OpI.cmp (.r 2) (.inl rfl)) (by decide) <|
  .nil 7

def j7 : List Byte := [0x0f, 0x86, 0xd3, 0x00, 0x00, 0x00]
theorem j7_0 : ∀ feat, Dec feat j7 0 (FV7z.mk (.jcc 6) 64 [.rel 211] 6) := by dec_rfl

/-- The stretch at `221`. -/
def p12 : List Byte := [
  0x89, 0xca, 0x83, 0x3c, 0x98, 0x2f, 0x41, 0x89, 0xde, 0x48, 0x8d, 0x34, 0x90, 0x4c, 0x8d, 0x2c,
  0x9d, 0x00, 0x00, 0x00, 0x00, 0x8d, 0x53, 0x01]

theorem p12_0 : ∀ feat, Dec feat p12 0 (FV7z.mk .mov 32 [gr 32 2, Src.opd 32 (.r 1)] 2) := by dec_rfl
theorem p12_2 : ∀ feat, Dec feat p12 2 (FV7z.mk .cmp 32 [.mem (mg (some 0) (some 3) 4 0 32), .imm 32 47] 4) := by dec_rfl
theorem p12_6 : ∀ feat, Dec feat p12 6 (FV7z.mk .mov 32 [gr 32 14, Src.opd 32 (.r 3)] 3) := by dec_rfl
theorem p12_9 : ∀ feat, Dec feat p12 9 (FV7z.mk .lea 64 [gr 64 6, .mem (mg (some 0) (some 2) 4 0 0)] 4) := by dec_rfl
theorem p12_13 : ∀ feat, Dec feat p12 13 (FV7z.mk .lea 64 [gr 64 13, .mem (mg none (some 3) 4 0 0)] 8) := by dec_rfl
theorem p12_21 : ∀ feat, Dec feat p12 21 (FV7z.mk .lea 32 [gr 32 2, .mem (mg (some 3) none 1 1 0)] 3) := by dec_rfl

/-- What the stretch does. -/
def o12 : List Op := [
  Op.mov 32 2 (.r 1),
  Op.cmpmi 32 (some 0) (some 3) 4 0 47,
  Op.mov 32 14 (.r 3),
  Op.lea 64 6 (some 0) (some 2) 4 0,
  Op.lea 64 13 none (some 3) 4 0,
  Op.lea 32 2 (some 3) none 1 1]

theorem b12 (prof : Profile) : Blk prof p12 0 24 o12 :=
  .cons (p12_0 _) (OpI.mov (.r 1) (.inl rfl)) (by decide) <|
  .cons (p12_2 _) (OpI.cmpmi (.inr rfl)) (by decide) <|
  .cons (p12_6 _) (OpI.mov (.r 3) (.inl rfl)) (by decide) <|
  .cons (p12_9 _) (OpI.lea (.inr rfl)) (by decide) <|
  .cons (p12_13 _) (OpI.lea (.inr rfl)) (by decide) <|
  .cons (p12_21 _) (OpI.lea (.inl rfl)) (by decide) <|
  .nil 24

def j8 : List Byte := [0x75, 0xd9]
theorem j8_0 : ∀ feat, Dec feat j8 0 (FV7z.mk (.jcc 5) 64 [.rel 18446744073709551577] 2) := by dec_rfl

/-- The stretch at `247`. -/
def p13 : List Byte := [
  0x89, 0xda, 0x4c, 0x89, 0xff, 0x29, 0xca]

theorem p13_0 : ∀ feat, Dec feat p13 0 (FV7z.mk .mov 32 [gr 32 2, Src.opd 32 (.r 3)] 2) := by dec_rfl
theorem p13_2 : ∀ feat, Dec feat p13 2 (FV7z.mk .mov 64 [gr 64 7, Src.opd 64 (.r 15)] 3) := by dec_rfl
theorem p13_5 : ∀ feat, Dec feat p13 5 (FV7z.mk .sub 32 [gr 32 2, Src.opd 32 (.r 1)] 2) := by dec_rfl

/-- What the stretch does. -/
def o13 : List Op := [
  Op.mov 32 2 (.r 3),
  Op.mov 64 7 (.r 15),
  Op.sub 32 2 (.r 1)]

theorem b13 (prof : Profile) : Blk prof p13 0 7 o13 :=
  .cons (p13_0 _) (OpI.mov (.r 3) (.inl rfl)) (by decide) <|
  .cons (p13_2 _) (OpI.mov (.r 15) (.inr rfl)) (by decide) <|
  .cons (p13_5 _) (OpI.sub (.r 1) (.inl rfl)) (by decide) <|
  .nil 7

/-- The stretch at `259`. -/
def p14 : List Byte := [
  0x8b, 0x45, 0x0c, 0x39, 0x45, 0x08]

theorem p14_0 : ∀ feat, Dec feat p14 0 (FV7z.mk .mov 32 [gr 32 0, .mem (mg (some 5) none 1 12 32)] 3) := by dec_rfl
theorem p14_3 : ∀ feat, Dec feat p14 3 (FV7z.mk .cmp 32 [.mem (mg (some 5) none 1 8 32), gr 32 0] 3) := by dec_rfl

/-- What the stretch does. -/
def o14 : List Op := [
  Op.ld 32 0 (some 5) none 1 12,
  Op.cmpmr 32 (some 5) none 1 8 0]

theorem b14 (prof : Profile) : Blk prof p14 0 6 o14 :=
  .cons (p14_0 _) (OpI.ld (.inl rfl)) (by decide) <|
  .cons (p14_3 _) (OpI.cmpmr (.inl rfl)) (by decide) <|
  .nil 6

def j9 : List Byte := [0x75, 0x55]
theorem j9_0 : ∀ feat, Dec feat j9 0 (FV7z.mk (.jcc 5) 64 [.rel 85] 2) := by dec_rfl

/-- The stretch at `267`. -/
def p15 : List Byte := [
  0x3d, 0xfe, 0xff, 0xff, 0x7f]

theorem p15_0 : ∀ feat, Dec feat p15 0 (FV7z.mk .cmp 32 [gr 32 0, Src.opd 32 (.i 2147483646)] 5) := by dec_rfl

/-- What the stretch does. -/
def o15 : List Op := [
  Op.cmp 32 0 (.i 2147483646)]

theorem b15 (prof : Profile) : Blk prof p15 0 5 o15 :=
  .cons (p15_0 _) (OpI.cmp (.i 2147483646) (.inl rfl)) (by decide) <|
  .nil 5

/-- The stretch at `278`. -/
def p16 : List Byte := [
  0x89, 0xc2, 0xc1, 0xea, 0x02, 0x8d, 0x4a, 0x01, 0xba, 0xff, 0xff, 0xff, 0x7f, 0x29, 0xc2, 0x39,
  0xca, 0x0f, 0x47, 0xd1, 0x8d, 0x3c, 0x02, 0x89, 0x7c, 0x24, 0x10, 0x48, 0xc1, 0xe7, 0x03]

theorem p16_0 : ∀ feat, Dec feat p16 0 (FV7z.mk .mov 32 [gr 32 2, Src.opd 32 (.r 0)] 2) := by dec_rfl
theorem p16_2 : ∀ feat, Dec feat p16 2 (FV7z.mk .shr 32 [gr 32 2, Src.opd 8 (.i 2)] 3) := by dec_rfl
theorem p16_5 : ∀ feat, Dec feat p16 5 (FV7z.mk .lea 32 [gr 32 1, .mem (mg (some 2) none 1 1 0)] 3) := by dec_rfl
theorem p16_8 : ∀ feat, Dec feat p16 8 (FV7z.mk .mov 32 [gr 32 2, Src.opd 32 (.i 2147483647)] 5) := by dec_rfl
theorem p16_13 : ∀ feat, Dec feat p16 13 (FV7z.mk .sub 32 [gr 32 2, Src.opd 32 (.r 0)] 2) := by dec_rfl
theorem p16_15 : ∀ feat, Dec feat p16 15 (FV7z.mk .cmp 32 [gr 32 2, Src.opd 32 (.r 1)] 2) := by dec_rfl
theorem p16_17 : ∀ feat, Dec feat p16 17 (FV7z.mk (.cmovcc 7) 32 [gr 32 2, gr 32 1] 3) := by dec_rfl
theorem p16_20 : ∀ feat, Dec feat p16 20 (FV7z.mk .lea 32 [gr 32 7, .mem (mg (some 2) (some 0) 1 0 0)] 3) := by dec_rfl
theorem p16_23 : ∀ feat, Dec feat p16 23 (FV7z.mk .mov 32 [.mem (mg (some 4) none 1 16 32), gr 32 7] 4) := by dec_rfl
theorem p16_27 : ∀ feat, Dec feat p16 27 (FV7z.mk .shl 64 [gr 64 7, Src.opd 8 (.i 3)] 4) := by dec_rfl

/-- What the stretch does. -/
def o16 : List Op := [
  Op.mov 32 2 (.r 0),
  Op.shr 2 (.i 2),
  Op.lea 32 1 (some 2) none 1 1,
  Op.mov 32 2 (.i 2147483647),
  Op.sub 32 2 (.r 0),
  Op.cmp 32 2 (.r 1),
  Op.cmov32 7 2 1,
  Op.lea 32 7 (some 2) (some 0) 1 0,
  Op.st 32 (some 4) none 1 16 7,
  Op.shl64 7 (.i 3)]

theorem b16 (prof : Profile) : Blk prof p16 0 31 o16 :=
  .cons (p16_0 _) (OpI.mov (.r 0) (.inl rfl)) (by decide) <|
  .cons (p16_2 _) (OpI.shr (.i 2)) (by decide) <|
  .cons (p16_5 _) (OpI.lea (.inl rfl)) (by decide) <|
  .cons (p16_8 _) (OpI.mov (.i 2147483647) (.inl rfl)) (by decide) <|
  .cons (p16_13 _) (OpI.sub (.r 0) (.inl rfl)) (by decide) <|
  .cons (p16_15 _) (OpI.cmp (.r 1) (.inl rfl)) (by decide) <|
  .cons (p16_17 _) (OpI.cmov32) (by decide) <|
  .cons (p16_20 _) (OpI.lea (.inl rfl)) (by decide) <|
  .cons (p16_23 _) (OpI.st (.inr (.inr (.inl rfl)))) (by decide) <|
  .cons (p16_27 _) (OpI.shl64 (.i 3)) (by decide) <|
  .nil 31

/-- The stretch at `314`. -/
def p17 : List Byte := [
  0x48, 0x89, 0xc1, 0x8b, 0x45, 0x08, 0x4c, 0x8b, 0x45, 0x00, 0x85, 0xc0]

theorem p17_0 : ∀ feat, Dec feat p17 0 (FV7z.mk .mov 64 [gr 64 1, Src.opd 64 (.r 0)] 3) := by dec_rfl
theorem p17_3 : ∀ feat, Dec feat p17 3 (FV7z.mk .mov 32 [gr 32 0, .mem (mg (some 5) none 1 8 32)] 3) := by dec_rfl
theorem p17_6 : ∀ feat, Dec feat p17 6 (FV7z.mk .mov 64 [gr 64 8, .mem (mg (some 5) none 1 0 64)] 4) := by dec_rfl
theorem p17_10 : ∀ feat, Dec feat p17 10 (FV7z.mk .test 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl

/-- What the stretch does. -/
def o17 : List Op := [
  Op.mov 64 1 (.r 0),
  Op.ld 32 0 (some 5) none 1 8,
  Op.ld 64 8 (some 5) none 1 0,
  Op.test 32 0 (.r 0)]

theorem b17 (prof : Profile) : Blk prof p17 0 12 o17 :=
  .cons (p17_0 _) (OpI.mov (.r 0) (.inr rfl)) (by decide) <|
  .cons (p17_3 _) (OpI.ld (.inl rfl)) (by decide) <|
  .cons (p17_6 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p17_10 _) (OpI.test (.r 0) (.inl rfl)) (by decide) <|
  .nil 12

def j10 : List Byte := [0x0f, 0x85, 0x14, 0x01, 0x00, 0x00]
theorem j10_0 : ∀ feat, Dec feat j10 0 (FV7z.mk (.jcc 5) 64 [.rel 276] 6) := by dec_rfl

/-- The stretch at `332`. -/
def p18 : List Byte := [
  0x4d, 0x85, 0xc0]

theorem p18_0 : ∀ feat, Dec feat p18 0 (FV7z.mk .test 64 [gr 64 8, Src.opd 64 (.r 8)] 3) := by dec_rfl

/-- What the stretch does. -/
def o18 : List Op := [
  Op.test 64 8 (.r 8)]

theorem b18 (prof : Profile) : Blk prof p18 0 3 o18 :=
  .cons (p18_0 _) (OpI.test (.r 8) (.inr rfl)) (by decide) <|
  .nil 3

def j11 : List Byte := [0x0f, 0x85, 0x2b, 0x01, 0x00, 0x00]
theorem j11_0 : ∀ feat, Dec feat j11 0 (FV7z.mk (.jcc 5) 64 [.rel 299] 6) := by dec_rfl

/-- The stretch at `341`. -/
def p19 : List Byte := [
  0x8b, 0x44, 0x24, 0x10, 0x48, 0x89, 0x4d, 0x00, 0x89, 0x45, 0x0c]

theorem p19_0 : ∀ feat, Dec feat p19 0 (FV7z.mk .mov 32 [gr 32 0, .mem (mg (some 4) none 1 16 32)] 4) := by dec_rfl
theorem p19_4 : ∀ feat, Dec feat p19 4 (FV7z.mk .mov 64 [.mem (mg (some 5) none 1 0 64), gr 64 1] 4) := by dec_rfl
theorem p19_8 : ∀ feat, Dec feat p19 8 (FV7z.mk .mov 32 [.mem (mg (some 5) none 1 12 32), gr 32 0] 3) := by dec_rfl

/-- What the stretch does. -/
def o19 : List Op := [
  Op.ld 32 0 (some 4) none 1 16,
  Op.st 64 (some 5) none 1 0 1,
  Op.st 32 (some 5) none 1 12 0]

theorem b19 (prof : Profile) : Blk prof p19 0 11 o19 :=
  .cons (p19_0 _) (OpI.ld (.inl rfl)) (by decide) <|
  .cons (p19_4 _) (OpI.st (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p19_8 _) (OpI.st (.inr (.inr (.inl rfl)))) (by decide) <|
  .nil 11

/-- The stretch at `352`. -/
def p20 : List Byte := [
  0xbf, 0x10, 0x00, 0x00, 0x00]

theorem p20_0 : ∀ feat, Dec feat p20 0 (FV7z.mk .mov 32 [gr 32 7, Src.opd 32 (.i 16)] 5) := by dec_rfl

/-- What the stretch does. -/
def o20 : List Op := [
  Op.mov 32 7 (.i 16)]

theorem b20 (prof : Profile) : Blk prof p20 0 5 o20 :=
  .cons (p20_0 _) (OpI.mov (.i 16) (.inl rfl)) (by decide) <|
  .nil 5

/-- The stretch at `362`. -/
def p21 : List Byte := [
  0x4c, 0x89, 0xfe, 0x48, 0x89, 0xc7, 0x48, 0x89, 0x44, 0x24, 0x10]

theorem p21_0 : ∀ feat, Dec feat p21 0 (FV7z.mk .mov 64 [gr 64 6, Src.opd 64 (.r 15)] 3) := by dec_rfl
theorem p21_3 : ∀ feat, Dec feat p21 3 (FV7z.mk .mov 64 [gr 64 7, Src.opd 64 (.r 0)] 3) := by dec_rfl
theorem p21_6 : ∀ feat, Dec feat p21 6 (FV7z.mk .mov 64 [.mem (mg (some 4) none 1 16 64), gr 64 0] 5) := by dec_rfl

/-- What the stretch does. -/
def o21 : List Op := [
  Op.mov 64 6 (.r 15),
  Op.mov 64 7 (.r 0),
  Op.st 64 (some 4) none 1 16 0]

theorem b21 (prof : Profile) : Blk prof p21 0 11 o21 :=
  .cons (p21_0 _) (OpI.mov (.r 15) (.inr rfl)) (by decide) <|
  .cons (p21_3 _) (OpI.mov (.r 0) (.inr rfl)) (by decide) <|
  .cons (p21_6 _) (OpI.st (.inr (.inr (.inr rfl)))) (by decide) <|
  .nil 11

/-- The stretch at `378`. -/
def p22 : List Byte := [
  0x8b, 0x45, 0x08, 0x48, 0x8b, 0x55, 0x00, 0x48, 0x83, 0xc3, 0x01, 0x8d, 0x48, 0x01, 0x89, 0x4d,
  0x08, 0x48, 0x8b, 0x4c, 0x24, 0x10, 0x48, 0x89, 0x0c, 0xc2, 0x48, 0x8b, 0x44, 0x24, 0x08, 0x41,
  0x8d, 0x4e, 0x01, 0x89, 0xca, 0x48, 0x8b, 0x00, 0x4a, 0x8d, 0x74, 0x28, 0x04, 0x41, 0x39, 0xd4]

theorem p22_0 : ∀ feat, Dec feat p22 0 (FV7z.mk .mov 32 [gr 32 0, .mem (mg (some 5) none 1 8 32)] 3) := by dec_rfl
theorem p22_3 : ∀ feat, Dec feat p22 3 (FV7z.mk .mov 64 [gr 64 2, .mem (mg (some 5) none 1 0 64)] 4) := by dec_rfl
theorem p22_7 : ∀ feat, Dec feat p22 7 (FV7z.mk .add 64 [gr 64 3, Src.opd 64 (.i 1)] 4) := by dec_rfl
theorem p22_11 : ∀ feat, Dec feat p22 11 (FV7z.mk .lea 32 [gr 32 1, .mem (mg (some 0) none 1 1 0)] 3) := by dec_rfl
theorem p22_14 : ∀ feat, Dec feat p22 14 (FV7z.mk .mov 32 [.mem (mg (some 5) none 1 8 32), gr 32 1] 3) := by dec_rfl
theorem p22_17 : ∀ feat, Dec feat p22 17 (FV7z.mk .mov 64 [gr 64 1, .mem (mg (some 4) none 1 16 64)] 5) := by dec_rfl
theorem p22_22 : ∀ feat, Dec feat p22 22 (FV7z.mk .mov 64 [.mem (mg (some 2) (some 0) 8 0 64), gr 64 1] 4) := by dec_rfl
theorem p22_26 : ∀ feat, Dec feat p22 26 (FV7z.mk .mov 64 [gr 64 0, .mem (mg (some 4) none 1 8 64)] 5) := by dec_rfl
theorem p22_31 : ∀ feat, Dec feat p22 31 (FV7z.mk .lea 32 [gr 32 1, .mem (mg (some 14) none 1 1 0)] 4) := by dec_rfl
theorem p22_35 : ∀ feat, Dec feat p22 35 (FV7z.mk .mov 32 [gr 32 2, Src.opd 32 (.r 1)] 2) := by dec_rfl
theorem p22_37 : ∀ feat, Dec feat p22 37 (FV7z.mk .mov 64 [gr 64 0, .mem (mg (some 0) none 1 0 64)] 3) := by dec_rfl
theorem p22_40 : ∀ feat, Dec feat p22 40 (FV7z.mk .lea 64 [gr 64 6, .mem (mg (some 0) (some 13) 1 4 0)] 5) := by dec_rfl
theorem p22_45 : ∀ feat, Dec feat p22 45 (FV7z.mk .cmp 32 [gr 32 12, Src.opd 32 (.r 2)] 3) := by dec_rfl

/-- What the stretch does. -/
def o22 : List Op := [
  Op.ld 32 0 (some 5) none 1 8,
  Op.ld 64 2 (some 5) none 1 0,
  Op.add 64 3 (.i 1),
  Op.lea 32 1 (some 0) none 1 1,
  Op.st 32 (some 5) none 1 8 1,
  Op.ld 64 1 (some 4) none 1 16,
  Op.st 64 (some 2) (some 0) 8 0 1,
  Op.ld 64 0 (some 4) none 1 8,
  Op.lea 32 1 (some 14) none 1 1,
  Op.mov 32 2 (.r 1),
  Op.ld 64 0 (some 0) none 1 0,
  Op.lea 64 6 (some 0) (some 13) 1 4,
  Op.cmp 32 12 (.r 2)]

theorem b22 (prof : Profile) : Blk prof p22 0 48 o22 :=
  .cons (p22_0 _) (OpI.ld (.inl rfl)) (by decide) <|
  .cons (p22_3 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p22_7 _) (OpI.add (.i 1) (.inr rfl)) (by decide) <|
  .cons (p22_11 _) (OpI.lea (.inl rfl)) (by decide) <|
  .cons (p22_14 _) (OpI.st (.inr (.inr (.inl rfl)))) (by decide) <|
  .cons (p22_17 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p22_22 _) (OpI.st (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p22_26 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p22_31 _) (OpI.lea (.inl rfl)) (by decide) <|
  .cons (p22_35 _) (OpI.mov (.r 1) (.inl rfl)) (by decide) <|
  .cons (p22_37 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p22_40 _) (OpI.lea (.inr rfl)) (by decide) <|
  .cons (p22_45 _) (OpI.cmp (.r 2) (.inl rfl)) (by decide) <|
  .nil 48

def j12 : List Byte := [0x0f, 0x87, 0x2d, 0xff, 0xff, 0xff]
theorem j12_0 : ∀ feat, Dec feat j12 0 (FV7z.mk (.jcc 7) 64 [.rel 18446744073709551405] 6) := by dec_rfl

/-- The stretch at `432`. -/
def p23 : List Byte := [
  0x44, 0x89, 0xe2, 0x4c, 0x89, 0xff, 0x29, 0xca]

theorem p23_0 : ∀ feat, Dec feat p23 0 (FV7z.mk .mov 32 [gr 32 2, Src.opd 32 (.r 12)] 3) := by dec_rfl
theorem p23_3 : ∀ feat, Dec feat p23 3 (FV7z.mk .mov 64 [gr 64 7, Src.opd 64 (.r 15)] 3) := by dec_rfl
theorem p23_6 : ∀ feat, Dec feat p23 6 (FV7z.mk .sub 32 [gr 32 2, Src.opd 32 (.r 1)] 2) := by dec_rfl

/-- What the stretch does. -/
def o23 : List Op := [
  Op.mov 32 2 (.r 12),
  Op.mov 64 7 (.r 15),
  Op.sub 32 2 (.r 1)]

theorem b23 (prof : Profile) : Blk prof p23 0 8 o23 :=
  .cons (p23_0 _) (OpI.mov (.r 12) (.inl rfl)) (by decide) <|
  .cons (p23_3 _) (OpI.mov (.r 15) (.inr rfl)) (by decide) <|
  .cons (p23_6 _) (OpI.sub (.r 1) (.inl rfl)) (by decide) <|
  .nil 8

def j13 : List Byte := [0x75, 0x50]
theorem j13_0 : ∀ feat, Dec feat j13 0 (FV7z.mk (.jcc 5) 64 [.rel 80] 2) := by dec_rfl

/-- The stretch at `464`. -/
def p24 : List Byte := [
  0x89, 0xc3, 0xc1, 0xeb, 0x02, 0x8d, 0x53, 0x01, 0xbb, 0xff, 0xff, 0xff, 0x7f, 0x29, 0xc3, 0x39,
  0xd3, 0x0f, 0x47, 0xda, 0x8d, 0x3c, 0x03, 0x48, 0x89, 0xfb, 0x48, 0xc1, 0xe7, 0x03]

theorem p24_0 : ∀ feat, Dec feat p24 0 (FV7z.mk .mov 32 [gr 32 3, Src.opd 32 (.r 0)] 2) := by dec_rfl
theorem p24_2 : ∀ feat, Dec feat p24 2 (FV7z.mk .shr 32 [gr 32 3, Src.opd 8 (.i 2)] 3) := by dec_rfl
theorem p24_5 : ∀ feat, Dec feat p24 5 (FV7z.mk .lea 32 [gr 32 2, .mem (mg (some 3) none 1 1 0)] 3) := by dec_rfl
theorem p24_8 : ∀ feat, Dec feat p24 8 (FV7z.mk .mov 32 [gr 32 3, Src.opd 32 (.i 2147483647)] 5) := by dec_rfl
theorem p24_13 : ∀ feat, Dec feat p24 13 (FV7z.mk .sub 32 [gr 32 3, Src.opd 32 (.r 0)] 2) := by dec_rfl
theorem p24_15 : ∀ feat, Dec feat p24 15 (FV7z.mk .cmp 32 [gr 32 3, Src.opd 32 (.r 2)] 2) := by dec_rfl
theorem p24_17 : ∀ feat, Dec feat p24 17 (FV7z.mk (.cmovcc 7) 32 [gr 32 3, gr 32 2] 3) := by dec_rfl
theorem p24_20 : ∀ feat, Dec feat p24 20 (FV7z.mk .lea 32 [gr 32 7, .mem (mg (some 3) (some 0) 1 0 0)] 3) := by dec_rfl
theorem p24_23 : ∀ feat, Dec feat p24 23 (FV7z.mk .mov 64 [gr 64 3, Src.opd 64 (.r 7)] 3) := by dec_rfl
theorem p24_26 : ∀ feat, Dec feat p24 26 (FV7z.mk .shl 64 [gr 64 7, Src.opd 8 (.i 3)] 4) := by dec_rfl

/-- What the stretch does. -/
def o24 : List Op := [
  Op.mov 32 3 (.r 0),
  Op.shr 3 (.i 2),
  Op.lea 32 2 (some 3) none 1 1,
  Op.mov 32 3 (.i 2147483647),
  Op.sub 32 3 (.r 0),
  Op.cmp 32 3 (.r 2),
  Op.cmov32 7 3 2,
  Op.lea 32 7 (some 3) (some 0) 1 0,
  Op.mov 64 3 (.r 7),
  Op.shl64 7 (.i 3)]

theorem b24 (prof : Profile) : Blk prof p24 0 30 o24 :=
  .cons (p24_0 _) (OpI.mov (.r 0) (.inl rfl)) (by decide) <|
  .cons (p24_2 _) (OpI.shr (.i 2)) (by decide) <|
  .cons (p24_5 _) (OpI.lea (.inl rfl)) (by decide) <|
  .cons (p24_8 _) (OpI.mov (.i 2147483647) (.inl rfl)) (by decide) <|
  .cons (p24_13 _) (OpI.sub (.r 0) (.inl rfl)) (by decide) <|
  .cons (p24_15 _) (OpI.cmp (.r 2) (.inl rfl)) (by decide) <|
  .cons (p24_17 _) (OpI.cmov32) (by decide) <|
  .cons (p24_20 _) (OpI.lea (.inl rfl)) (by decide) <|
  .cons (p24_23 _) (OpI.mov (.r 7) (.inr rfl)) (by decide) <|
  .cons (p24_26 _) (OpI.shl64 (.i 3)) (by decide) <|
  .nil 30

/-- The stretch at `499`. -/
def p25 : List Byte := [
  0x49, 0x89, 0xc4, 0x8b, 0x45, 0x08, 0x4c, 0x8b, 0x6d, 0x00, 0x85, 0xc0]

theorem p25_0 : ∀ feat, Dec feat p25 0 (FV7z.mk .mov 64 [gr 64 12, Src.opd 64 (.r 0)] 3) := by dec_rfl
theorem p25_3 : ∀ feat, Dec feat p25 3 (FV7z.mk .mov 32 [gr 32 0, .mem (mg (some 5) none 1 8 32)] 3) := by dec_rfl
theorem p25_6 : ∀ feat, Dec feat p25 6 (FV7z.mk .mov 64 [gr 64 13, .mem (mg (some 5) none 1 0 64)] 4) := by dec_rfl
theorem p25_10 : ∀ feat, Dec feat p25 10 (FV7z.mk .test 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl

/-- What the stretch does. -/
def o25 : List Op := [
  Op.mov 64 12 (.r 0),
  Op.ld 32 0 (some 5) none 1 8,
  Op.ld 64 13 (some 5) none 1 0,
  Op.test 32 0 (.r 0)]

theorem b25 (prof : Profile) : Blk prof p25 0 12 o25 :=
  .cons (p25_0 _) (OpI.mov (.r 0) (.inr rfl)) (by decide) <|
  .cons (p25_3 _) (OpI.ld (.inl rfl)) (by decide) <|
  .cons (p25_6 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p25_10 _) (OpI.test (.r 0) (.inl rfl)) (by decide) <|
  .nil 12

def j14 : List Byte := [0x0f, 0x85, 0x9b, 0x00, 0x00, 0x00]
theorem j14_0 : ∀ feat, Dec feat j14 0 (FV7z.mk (.jcc 5) 64 [.rel 155] 6) := by dec_rfl

/-- The stretch at `517`. -/
def p26 : List Byte := [
  0x4d, 0x85, 0xed]

theorem p26_0 : ∀ feat, Dec feat p26 0 (FV7z.mk .test 64 [gr 64 13, Src.opd 64 (.r 13)] 3) := by dec_rfl

/-- What the stretch does. -/
def o26 : List Op := [
  Op.test 64 13 (.r 13)]

theorem b26 (prof : Profile) : Blk prof p26 0 3 o26 :=
  .cons (p26_0 _) (OpI.test (.r 13) (.inr rfl)) (by decide) <|
  .nil 3

def j15 : List Byte := [0x0f, 0x85, 0xa5, 0x00, 0x00, 0x00]
theorem j15_0 : ∀ feat, Dec feat j15 0 (FV7z.mk (.jcc 5) 64 [.rel 165] 6) := by dec_rfl

/-- The stretch at `526`. -/
def p27 : List Byte := [
  0x4c, 0x89, 0x65, 0x00, 0x89, 0x5d, 0x0c]

theorem p27_0 : ∀ feat, Dec feat p27 0 (FV7z.mk .mov 64 [.mem (mg (some 5) none 1 0 64), gr 64 12] 4) := by dec_rfl
theorem p27_4 : ∀ feat, Dec feat p27 4 (FV7z.mk .mov 32 [.mem (mg (some 5) none 1 12 32), gr 32 3] 3) := by dec_rfl

/-- What the stretch does. -/
def o27 : List Op := [
  Op.st 64 (some 5) none 1 0 12,
  Op.st 32 (some 5) none 1 12 3]

theorem b27 (prof : Profile) : Blk prof p27 0 7 o27 :=
  .cons (p27_0 _) (OpI.st (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p27_4 _) (OpI.st (.inr (.inr (.inl rfl)))) (by decide) <|
  .nil 7

/-- The stretch at `543`. -/
def p28 : List Byte := [
  0x4c, 0x89, 0xfe, 0x48, 0x89, 0xc7, 0x49, 0x89, 0xc4]

theorem p28_0 : ∀ feat, Dec feat p28 0 (FV7z.mk .mov 64 [gr 64 6, Src.opd 64 (.r 15)] 3) := by dec_rfl
theorem p28_3 : ∀ feat, Dec feat p28 3 (FV7z.mk .mov 64 [gr 64 7, Src.opd 64 (.r 0)] 3) := by dec_rfl
theorem p28_6 : ∀ feat, Dec feat p28 6 (FV7z.mk .mov 64 [gr 64 12, Src.opd 64 (.r 0)] 3) := by dec_rfl

/-- What the stretch does. -/
def o28 : List Op := [
  Op.mov 64 6 (.r 15),
  Op.mov 64 7 (.r 0),
  Op.mov 64 12 (.r 0)]

theorem b28 (prof : Profile) : Blk prof p28 0 9 o28 :=
  .cons (p28_0 _) (OpI.mov (.r 15) (.inr rfl)) (by decide) <|
  .cons (p28_3 _) (OpI.mov (.r 0) (.inr rfl)) (by decide) <|
  .cons (p28_6 _) (OpI.mov (.r 0) (.inr rfl)) (by decide) <|
  .nil 9

/-- The stretch at `557`. -/
def p29 : List Byte := [
  0x8b, 0x45, 0x08, 0x48, 0x8b, 0x55, 0x00, 0x8d, 0x48, 0x01, 0x89, 0x4d, 0x08, 0x4c, 0x89, 0x24,
  0xc2, 0x48, 0x8b, 0x7c, 0x24, 0x20, 0x48, 0x85, 0xff]

theorem p29_0 : ∀ feat, Dec feat p29 0 (FV7z.mk .mov 32 [gr 32 0, .mem (mg (some 5) none 1 8 32)] 3) := by dec_rfl
theorem p29_3 : ∀ feat, Dec feat p29 3 (FV7z.mk .mov 64 [gr 64 2, .mem (mg (some 5) none 1 0 64)] 4) := by dec_rfl
theorem p29_7 : ∀ feat, Dec feat p29 7 (FV7z.mk .lea 32 [gr 32 1, .mem (mg (some 0) none 1 1 0)] 3) := by dec_rfl
theorem p29_10 : ∀ feat, Dec feat p29 10 (FV7z.mk .mov 32 [.mem (mg (some 5) none 1 8 32), gr 32 1] 3) := by dec_rfl
theorem p29_13 : ∀ feat, Dec feat p29 13 (FV7z.mk .mov 64 [.mem (mg (some 2) (some 0) 8 0 64), gr 64 12] 4) := by dec_rfl
theorem p29_17 : ∀ feat, Dec feat p29 17 (FV7z.mk .mov 64 [gr 64 7, .mem (mg (some 4) none 1 32 64)] 5) := by dec_rfl
theorem p29_22 : ∀ feat, Dec feat p29 22 (FV7z.mk .test 64 [gr 64 7, Src.opd 64 (.r 7)] 3) := by dec_rfl

/-- What the stretch does. -/
def o29 : List Op := [
  Op.ld 32 0 (some 5) none 1 8,
  Op.ld 64 2 (some 5) none 1 0,
  Op.lea 32 1 (some 0) none 1 1,
  Op.st 32 (some 5) none 1 8 1,
  Op.st 64 (some 2) (some 0) 8 0 12,
  Op.ld 64 7 (some 4) none 1 32,
  Op.test 64 7 (.r 7)]

theorem b29 (prof : Profile) : Blk prof p29 0 25 o29 :=
  .cons (p29_0 _) (OpI.ld (.inl rfl)) (by decide) <|
  .cons (p29_3 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p29_7 _) (OpI.lea (.inl rfl)) (by decide) <|
  .cons (p29_10 _) (OpI.st (.inr (.inr (.inl rfl)))) (by decide) <|
  .cons (p29_13 _) (OpI.st (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p29_17 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p29_22 _) (OpI.test (.r 7) (.inr rfl)) (by decide) <|
  .nil 25

def j16 : List Byte := [0x0f, 0x84, 0x3b, 0xfe, 0xff, 0xff]
theorem j16_0 : ∀ feat, Dec feat j16 0 (FV7z.mk (.jcc 4) 64 [.rel 18446744073709551163] 6) := by dec_rfl

def j17 : List Byte := [0xe9, 0x31, 0xfe, 0xff, 0xff]
theorem j17_0 : ∀ feat, Dec feat j17 0 (FV7z.mk .jmp 64 [.rel 18446744073709551153] 5) := by dec_rfl

/-- The stretch at `608`. -/
def p30 : List Byte := [
  0x4c, 0x89, 0xc6, 0x48, 0x89, 0xcf, 0x4c, 0x89, 0x44, 0x24, 0x18, 0x48, 0x8d, 0x14, 0xc5, 0x00,
  0x00, 0x00, 0x00]

theorem p30_0 : ∀ feat, Dec feat p30 0 (FV7z.mk .mov 64 [gr 64 6, Src.opd 64 (.r 8)] 3) := by dec_rfl
theorem p30_3 : ∀ feat, Dec feat p30 3 (FV7z.mk .mov 64 [gr 64 7, Src.opd 64 (.r 1)] 3) := by dec_rfl
theorem p30_6 : ∀ feat, Dec feat p30 6 (FV7z.mk .mov 64 [.mem (mg (some 4) none 1 24 64), gr 64 8] 5) := by dec_rfl
theorem p30_11 : ∀ feat, Dec feat p30 11 (FV7z.mk .lea 64 [gr 64 2, .mem (mg none (some 0) 8 0 0)] 8) := by dec_rfl

/-- What the stretch does. -/
def o30 : List Op := [
  Op.mov 64 6 (.r 8),
  Op.mov 64 7 (.r 1),
  Op.st 64 (some 4) none 1 24 8,
  Op.lea 64 2 none (some 0) 8 0]

theorem b30 (prof : Profile) : Blk prof p30 0 19 o30 :=
  .cons (p30_0 _) (OpI.mov (.r 8) (.inr rfl)) (by decide) <|
  .cons (p30_3 _) (OpI.mov (.r 1) (.inr rfl)) (by decide) <|
  .cons (p30_6 _) (OpI.st (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p30_11 _) (OpI.lea (.inr rfl)) (by decide) <|
  .nil 19

/-- The stretch at `632`. -/
def p31 : List Byte := [
  0x4c, 0x8b, 0x44, 0x24, 0x18, 0x48, 0x89, 0xc1]

theorem p31_0 : ∀ feat, Dec feat p31 0 (FV7z.mk .mov 64 [gr 64 8, .mem (mg (some 4) none 1 24 64)] 5) := by dec_rfl
theorem p31_5 : ∀ feat, Dec feat p31 5 (FV7z.mk .mov 64 [gr 64 1, Src.opd 64 (.r 0)] 3) := by dec_rfl

/-- What the stretch does. -/
def o31 : List Op := [
  Op.ld 64 8 (some 4) none 1 24,
  Op.mov 64 1 (.r 0)]

theorem b31 (prof : Profile) : Blk prof p31 0 8 o31 :=
  .cons (p31_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p31_5 _) (OpI.mov (.r 0) (.inr rfl)) (by decide) <|
  .nil 8

/-- The stretch at `640`. -/
def p32 : List Byte := [
  0x4c, 0x89, 0xc7, 0x48, 0x89, 0x4c, 0x24, 0x18]

theorem p32_0 : ∀ feat, Dec feat p32 0 (FV7z.mk .mov 64 [gr 64 7, Src.opd 64 (.r 8)] 3) := by dec_rfl
theorem p32_3 : ∀ feat, Dec feat p32 3 (FV7z.mk .mov 64 [.mem (mg (some 4) none 1 24 64), gr 64 1] 5) := by dec_rfl

/-- What the stretch does. -/
def o32 : List Op := [
  Op.mov 64 7 (.r 8),
  Op.st 64 (some 4) none 1 24 1]

theorem b32 (prof : Profile) : Blk prof p32 0 8 o32 :=
  .cons (p32_0 _) (OpI.mov (.r 8) (.inr rfl)) (by decide) <|
  .cons (p32_3 _) (OpI.st (.inr (.inr (.inr rfl)))) (by decide) <|
  .nil 8

/-- The stretch at `653`. -/
def p33 : List Byte := [
  0x48, 0x8b, 0x4c, 0x24, 0x18]

theorem p33_0 : ∀ feat, Dec feat p33 0 (FV7z.mk .mov 64 [gr 64 1, .mem (mg (some 4) none 1 24 64)] 5) := by dec_rfl

/-- What the stretch does. -/
def o33 : List Op := [
  Op.ld 64 1 (some 4) none 1 24]

theorem b33 (prof : Profile) : Blk prof p33 0 5 o33 :=
  .cons (p33_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .nil 5

def j18 : List Byte := [0xe9, 0xbe, 0xfe, 0xff, 0xff]
theorem j18_0 : ∀ feat, Dec feat j18 0 (FV7z.mk .jmp 64 [.rel 18446744073709551294] 5) := by dec_rfl

/-- The stretch at `672`. -/
def p34 : List Byte := [
  0x48, 0x8d, 0x14, 0xc5, 0x00, 0x00, 0x00, 0x00, 0x4c, 0x89, 0xee, 0x4c, 0x89, 0xe7]

theorem p34_0 : ∀ feat, Dec feat p34 0 (FV7z.mk .lea 64 [gr 64 2, .mem (mg none (some 0) 8 0 0)] 8) := by dec_rfl
theorem p34_8 : ∀ feat, Dec feat p34 8 (FV7z.mk .mov 64 [gr 64 6, Src.opd 64 (.r 13)] 3) := by dec_rfl
theorem p34_11 : ∀ feat, Dec feat p34 11 (FV7z.mk .mov 64 [gr 64 7, Src.opd 64 (.r 12)] 3) := by dec_rfl

/-- What the stretch does. -/
def o34 : List Op := [
  Op.lea 64 2 none (some 0) 8 0,
  Op.mov 64 6 (.r 13),
  Op.mov 64 7 (.r 12)]

theorem b34 (prof : Profile) : Blk prof p34 0 14 o34 :=
  .cons (p34_0 _) (OpI.lea (.inr rfl)) (by decide) <|
  .cons (p34_8 _) (OpI.mov (.r 13) (.inr rfl)) (by decide) <|
  .cons (p34_11 _) (OpI.mov (.r 12) (.inr rfl)) (by decide) <|
  .nil 14

/-- The stretch at `691`. -/
def p35 : List Byte := [
  0x4c, 0x89, 0xef]

theorem p35_0 : ∀ feat, Dec feat p35 0 (FV7z.mk .mov 64 [gr 64 7, Src.opd 64 (.r 13)] 3) := by dec_rfl

/-- What the stretch does. -/
def o35 : List Op := [
  Op.mov 64 7 (.r 13)]

theorem b35 (prof : Profile) : Blk prof p35 0 3 o35 :=
  .cons (p35_0 _) (OpI.mov (.r 13) (.inr rfl)) (by decide) <|
  .nil 3

def j19 : List Byte := [0xe9, 0x4e, 0xff, 0xff, 0xff]
theorem j19_0 : ∀ feat, Dec feat j19 0 (FV7z.mk .jmp 64 [.rel 18446744073709551438] 5) := by dec_rfl

end FV7z.Spp
