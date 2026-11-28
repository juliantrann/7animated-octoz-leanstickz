import FV7z.Lemmas.SpFs
import FV7z.Lemmas.BlkOps14
import FV7z.Lemmas.BlkOps12
import FV7z.Lemmas.BlkOps6
import FV7z.Lemmas.BlkOps3
/-!
# The stretches of straight-line code of `NWildcard::CCensorNode::CheckPathToRoot` (PLAN.md §M, M1)

Each distinct stretch between labels and jumps (`p*`, 35 of them) and each distinct jump (`j*`, 18) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.Cpr
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The stretch at `0`. -/
def p0 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0x41, 0x57, 0x41, 0x56, 0x44, 0x0f, 0xb6, 0xf1, 0x41, 0x55, 0x44, 0x0f,
  0xb6, 0xee, 0x44, 0x89, 0xf1, 0x41, 0x54, 0x44, 0x89, 0xee, 0x55, 0x48, 0x89, 0xd5, 0x53, 0x48,
  0x89, 0xfb, 0x48, 0x83, 0xec, 0x48, 0x64, 0x48, 0x8b, 0x04, 0x25, 0x28, 0x00, 0x00, 0x00, 0x48,
  0x89, 0x44, 0x24, 0x38, 0x31, 0xc0]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem p0_4 : ∀ feat, Dec feat p0 4 (FV7z.mk .push 64 [gr 64 15] 2) := by dec_rfl
theorem p0_6 : ∀ feat, Dec feat p0 6 (FV7z.mk .push 64 [gr 64 14] 2) := by dec_rfl
theorem p0_8 : ∀ feat, Dec feat p0 8 (FV7z.mk .movzx 32 [gr 32 14, gr 8 1] 4) := by dec_rfl
theorem p0_12 : ∀ feat, Dec feat p0 12 (FV7z.mk .push 64 [gr 64 13] 2) := by dec_rfl
theorem p0_14 : ∀ feat, Dec feat p0 14 (FV7z.mk .movzx 32 [gr 32 13, gr 8 6] 4) := by dec_rfl
theorem p0_18 : ∀ feat, Dec feat p0 18 (FV7z.mk .mov 32 [gr 32 1, Src.opd 32 (.r 14)] 3) := by dec_rfl
theorem p0_21 : ∀ feat, Dec feat p0 21 (FV7z.mk .push 64 [gr 64 12] 2) := by dec_rfl
theorem p0_23 : ∀ feat, Dec feat p0 23 (FV7z.mk .mov 32 [gr 32 6, Src.opd 32 (.r 13)] 3) := by dec_rfl
theorem p0_26 : ∀ feat, Dec feat p0 26 (FV7z.mk .push 64 [gr 64 5] 1) := by dec_rfl
theorem p0_27 : ∀ feat, Dec feat p0 27 (FV7z.mk .mov 64 [gr 64 5, Src.opd 64 (.r 2)] 3) := by dec_rfl
theorem p0_30 : ∀ feat, Dec feat p0 30 (FV7z.mk .push 64 [gr 64 3] 1) := by dec_rfl
theorem p0_31 : ∀ feat, Dec feat p0 31 (FV7z.mk .mov 64 [gr 64 3, Src.opd 64 (.r 7)] 3) := by dec_rfl
theorem p0_34 : ∀ feat, Dec feat p0 34 (FV7z.mk .sub 64 [gr 64 4, Src.opd 64 (.i 72)] 4) := by dec_rfl
theorem p0_38 : ∀ feat, Dec feat p0 38 (FV7z.mk .mov 64 [gr 64 0, .mem (mf none none 1 40 64)] 9) := by dec_rfl
theorem p0_47 : ∀ feat, Dec feat p0 47 (FV7z.mk .mov 64 [.mem (mg (some 4) none 1 56 64), gr 64 0] 5) := by dec_rfl
theorem p0_52 : ∀ feat, Dec feat p0 52 (FV7z.mk .xor 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl

/-- What the stretch does. -/
def o0 (fb : Addr) : List Op := [
  Op.nop,
  Op.push 15,
  Op.push 14,
  Op.zxr 14 1,
  Op.push 13,
  Op.zxr 13 6,
  Op.mov 32 1 (.r 14),
  Op.push 12,
  Op.mov 32 6 (.r 13),
  Op.push 5,
  Op.mov 64 5 (.r 2),
  Op.push 3,
  Op.mov 64 3 (.r 7),
  Op.sub 64 4 (.i 72),
  Op.ldf fb 64 0 none none 1 40,
  Op.st 64 (some 4) none 1 56 0,
  Op.xor 32 0 (.r 0)]

theorem b0 (prof : Profile) (fb : Addr) : BlkF prof p0 (0x454330 : Addr) fb 0 54 (o0 fb) :=
  .cons (p0_0 _) (((OpI.endbr).at _).fs _) (by decide) <|
  .cons (p0_4 _) (((OpI.push).at _).fs _) (by decide) <|
  .cons (p0_6 _) (((OpI.push).at _).fs _) (by decide) <|
  .cons (p0_8 _) (((OpI.zxr).at _).fs _) (by decide) <|
  .cons (p0_12 _) (((OpI.push).at _).fs _) (by decide) <|
  .cons (p0_14 _) (((OpI.zxr).at _).fs _) (by decide) <|
  .cons (p0_18 _) (((OpI.mov (.r 14) (.inl rfl)).at _).fs _) (by decide) <|
  .cons (p0_21 _) (((OpI.push).at _).fs _) (by decide) <|
  .cons (p0_23 _) (((OpI.mov (.r 13) (.inl rfl)).at _).fs _) (by decide) <|
  .cons (p0_26 _) (((OpI.push).at _).fs _) (by decide) <|
  .cons (p0_27 _) (((OpI.mov (.r 2) (.inr rfl)).at _).fs _) (by decide) <|
  .cons (p0_30 _) (((OpI.push).at _).fs _) (by decide) <|
  .cons (p0_31 _) (((OpI.mov (.r 7) (.inr rfl)).at _).fs _) (by decide) <|
  .cons (p0_34 _) (((OpI.sub (.i 72) (.inr rfl)).at _).fs _) (by decide) <|
  .cons (p0_38 _) (OpIF.ldf (.inr rfl)) (by decide) <|
  .cons (p0_47 _) (((OpI.st (.inr (.inr (.inr rfl)))).at _).fs _) (by decide) <|
  .cons (p0_52 _) (((OpI.xor (.r 0) (.inl rfl)).at _).fs _) (by decide) <|
  .nil 54

/-- The stretch at `59`. -/
def p1 : List Byte := [
  0x41, 0x89, 0xc4, 0x84, 0xc0]

theorem p1_0 : ∀ feat, Dec feat p1 0 (FV7z.mk .mov 32 [gr 32 12, Src.opd 32 (.r 0)] 3) := by dec_rfl
theorem p1_3 : ∀ feat, Dec feat p1 3 (FV7z.mk .test 8 [gr 8 0, Src.opd 8 (.r 0)] 2) := by dec_rfl

/-- What the stretch does. -/
def o1 : List Op := [
  Op.mov 32 12 (.r 0),
  Op.test 8 0 (.r 0)]

theorem b1 (prof : Profile) : Blk prof p1 0 5 o1 :=
  .cons (p1_0 _) (OpI.mov (.r 0) (.inl rfl)) (by decide) <|
  .cons (p1_3 _) (OpI.test8 (.r 0)) (by decide) <|
  .nil 5

def j0 : List Byte := [0x0f, 0x85, 0x07, 0x01, 0x00, 0x00]
theorem j0_0 : ∀ feat, Dec feat j0 0 (FV7z.mk (.jcc 5) 64 [.rel 263] 6) := by dec_rfl

/-- The stretch at `70`. -/
def p2 : List Byte := [
  0x48, 0x83, 0x3b, 0x00]

theorem p2_0 : ∀ feat, Dec feat p2 0 (FV7z.mk .cmp 64 [.mem (mg (some 3) none 1 0 64), .imm 64 0] 4) := by dec_rfl

/-- What the stretch does. -/
def o2 : List Op := [
  Op.cmpmi 64 (some 3) none 1 0 0]

theorem b2 (prof : Profile) : Blk prof p2 0 4 o2 :=
  .cons (p2_0 _) (OpI.cmpmi64) (by decide) <|
  .nil 4

def j1 : List Byte := [0x0f, 0x84, 0xfd, 0x00, 0x00, 0x00]
theorem j1_0 : ∀ feat, Dec feat j1 0 (FV7z.mk (.jcc 4) 64 [.rel 253] 6) := by dec_rfl

/-- The stretch at `80`. -/
def p3 : List Byte := [
  0xbf, 0x08, 0x00, 0x00, 0x00, 0x4c, 0x8d, 0x7b, 0x08, 0x4c, 0x8d, 0x64, 0x24, 0x20, 0x48, 0xc7,
  0x44, 0x24, 0x20, 0x00, 0x00, 0x00, 0x00, 0x48, 0xc7, 0x44, 0x24, 0x28, 0x00, 0x00, 0x00, 0x00]

theorem p3_0 : ∀ feat, Dec feat p3 0 (FV7z.mk .mov 32 [gr 32 7, Src.opd 32 (.i 8)] 5) := by dec_rfl
theorem p3_5 : ∀ feat, Dec feat p3 5 (FV7z.mk .lea 64 [gr 64 15, .mem (mg (some 3) none 1 8 0)] 4) := by dec_rfl
theorem p3_9 : ∀ feat, Dec feat p3 9 (FV7z.mk .lea 64 [gr 64 12, .mem (mg (some 4) none 1 32 0)] 5) := by dec_rfl
theorem p3_14 : ∀ feat, Dec feat p3 14 (FV7z.mk .mov 64 [.mem (mg (some 4) none 1 32 64), .imm 64 0] 9) := by dec_rfl
theorem p3_23 : ∀ feat, Dec feat p3 23 (FV7z.mk .mov 64 [.mem (mg (some 4) none 1 40 64), .imm 64 0] 9) := by dec_rfl

/-- What the stretch does. -/
def o3 : List Op := [
  Op.mov 32 7 (.i 8),
  Op.lea 64 15 (some 3) none 1 8,
  Op.lea 64 12 (some 4) none 1 32,
  Op.sti 64 (some 4) none 1 32 0,
  Op.sti 64 (some 4) none 1 40 0]

theorem b3 (prof : Profile) : Blk prof p3 0 32 o3 :=
  .cons (p3_0 _) (OpI.mov (.i 8) (.inl rfl)) (by decide) <|
  .cons (p3_5 _) (OpI.lea (.inr rfl)) (by decide) <|
  .cons (p3_9 _) (OpI.lea (.inr rfl)) (by decide) <|
  .cons (p3_14 _) (OpI.sti (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p3_23 _) (OpI.sti (.inr (.inr (.inr rfl)))) (by decide) <|
  .nil 32

/-- The stretch at `117`. -/
def p4 : List Byte := [
  0x8b, 0x54, 0x24, 0x28, 0x4c, 0x8b, 0x44, 0x24, 0x20, 0x49, 0x89, 0xc4, 0x85, 0xd2]

theorem p4_0 : ∀ feat, Dec feat p4 0 (FV7z.mk .mov 32 [gr 32 2, .mem (mg (some 4) none 1 40 32)] 4) := by dec_rfl
theorem p4_4 : ∀ feat, Dec feat p4 4 (FV7z.mk .mov 64 [gr 64 8, .mem (mg (some 4) none 1 32 64)] 5) := by dec_rfl
theorem p4_9 : ∀ feat, Dec feat p4 9 (FV7z.mk .mov 64 [gr 64 12, Src.opd 64 (.r 0)] 3) := by dec_rfl
theorem p4_12 : ∀ feat, Dec feat p4 12 (FV7z.mk .test 32 [gr 32 2, Src.opd 32 (.r 2)] 2) := by dec_rfl

/-- What the stretch does. -/
def o4 : List Op := [
  Op.ld 32 2 (some 4) none 1 40,
  Op.ld 64 8 (some 4) none 1 32,
  Op.mov 64 12 (.r 0),
  Op.test 32 2 (.r 2)]

theorem b4 (prof : Profile) : Blk prof p4 0 14 o4 :=
  .cons (p4_0 _) (OpI.ld (.inl rfl)) (by decide) <|
  .cons (p4_4 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p4_9 _) (OpI.mov (.r 0) (.inr rfl)) (by decide) <|
  .cons (p4_12 _) (OpI.test (.r 2) (.inl rfl)) (by decide) <|
  .nil 14

def j2 : List Byte := [0x0f, 0x85, 0xef, 0x00, 0x00, 0x00]
theorem j2_0 : ∀ feat, Dec feat j2 0 (FV7z.mk (.jcc 5) 64 [.rel 239] 6) := by dec_rfl

/-- The stretch at `137`. -/
def p5 : List Byte := [
  0x4d, 0x85, 0xc0]

theorem p5_0 : ∀ feat, Dec feat p5 0 (FV7z.mk .test 64 [gr 64 8, Src.opd 64 (.r 8)] 3) := by dec_rfl

/-- What the stretch does. -/
def o5 : List Op := [
  Op.test 64 8 (.r 8)]

theorem b5 (prof : Profile) : Blk prof p5 0 3 o5 :=
  .cons (p5_0 _) (OpI.test (.r 8) (.inr rfl)) (by decide) <|
  .nil 3

def j3 : List Byte := [0x0f, 0x85, 0xff, 0x00, 0x00, 0x00]
theorem j3_0 : ∀ feat, Dec feat j3 0 (FV7z.mk (.jcc 5) 64 [.rel 255] 6) := by dec_rfl

/-- The stretch at `146`. -/
def p6 : List Byte := [
  0xbf, 0x10, 0x00, 0x00, 0x00, 0x4c, 0x89, 0x64, 0x24, 0x20, 0x4c, 0x8d, 0x64, 0x24, 0x20, 0xc7,
  0x44, 0x24, 0x2c, 0x01, 0x00, 0x00, 0x00]

theorem p6_0 : ∀ feat, Dec feat p6 0 (FV7z.mk .mov 32 [gr 32 7, Src.opd 32 (.i 16)] 5) := by dec_rfl
theorem p6_5 : ∀ feat, Dec feat p6 5 (FV7z.mk .mov 64 [.mem (mg (some 4) none 1 32 64), gr 64 12] 5) := by dec_rfl
theorem p6_10 : ∀ feat, Dec feat p6 10 (FV7z.mk .lea 64 [gr 64 12, .mem (mg (some 4) none 1 32 0)] 5) := by dec_rfl
theorem p6_15 : ∀ feat, Dec feat p6 15 (FV7z.mk .mov 32 [.mem (mg (some 4) none 1 44 32), .imm 32 1] 8) := by dec_rfl

/-- What the stretch does. -/
def o6 : List Op := [
  Op.mov 32 7 (.i 16),
  Op.st 64 (some 4) none 1 32 12,
  Op.lea 64 12 (some 4) none 1 32,
  Op.sti 32 (some 4) none 1 44 1]

theorem b6 (prof : Profile) : Blk prof p6 0 23 o6 :=
  .cons (p6_0 _) (OpI.mov (.i 16) (.inl rfl)) (by decide) <|
  .cons (p6_5 _) (OpI.st (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p6_10 _) (OpI.lea (.inr rfl)) (by decide) <|
  .cons (p6_15 _) (OpI.sti (.inr (.inr (.inl rfl)))) (by decide) <|
  .nil 23

/-- The stretch at `174`. -/
def p7 : List Byte := [
  0x4c, 0x89, 0xfe, 0x48, 0x89, 0xc7, 0x49, 0x89, 0xc4]

theorem p7_0 : ∀ feat, Dec feat p7 0 (FV7z.mk .mov 64 [gr 64 6, Src.opd 64 (.r 15)] 3) := by dec_rfl
theorem p7_3 : ∀ feat, Dec feat p7 3 (FV7z.mk .mov 64 [gr 64 7, Src.opd 64 (.r 0)] 3) := by dec_rfl
theorem p7_6 : ∀ feat, Dec feat p7 6 (FV7z.mk .mov 64 [gr 64 12, Src.opd 64 (.r 0)] 3) := by dec_rfl

/-- What the stretch does. -/
def o7 : List Op := [
  Op.mov 64 6 (.r 15),
  Op.mov 64 7 (.r 0),
  Op.mov 64 12 (.r 0)]

theorem b7 (prof : Profile) : Blk prof p7 0 9 o7 :=
  .cons (p7_0 _) (OpI.mov (.r 15) (.inr rfl)) (by decide) <|
  .cons (p7_3 _) (OpI.mov (.r 0) (.inr rfl)) (by decide) <|
  .cons (p7_6 _) (OpI.mov (.r 0) (.inr rfl)) (by decide) <|
  .nil 9

/-- The stretch at `188`. -/
def p8 : List Byte := [
  0x8b, 0x44, 0x24, 0x28, 0x48, 0x8b, 0x4c, 0x24, 0x20, 0x44, 0x8b, 0x7d, 0x08, 0x8d, 0x50, 0x01,
  0x89, 0x54, 0x24, 0x28, 0x4c, 0x89, 0x24, 0xc1, 0x45, 0x85, 0xff]

theorem p8_0 : ∀ feat, Dec feat p8 0 (FV7z.mk .mov 32 [gr 32 0, .mem (mg (some 4) none 1 40 32)] 4) := by dec_rfl
theorem p8_4 : ∀ feat, Dec feat p8 4 (FV7z.mk .mov 64 [gr 64 1, .mem (mg (some 4) none 1 32 64)] 5) := by dec_rfl
theorem p8_9 : ∀ feat, Dec feat p8 9 (FV7z.mk .mov 32 [gr 32 15, .mem (mg (some 5) none 1 8 32)] 4) := by dec_rfl
theorem p8_13 : ∀ feat, Dec feat p8 13 (FV7z.mk .lea 32 [gr 32 2, .mem (mg (some 0) none 1 1 0)] 3) := by dec_rfl
theorem p8_16 : ∀ feat, Dec feat p8 16 (FV7z.mk .mov 32 [.mem (mg (some 4) none 1 40 32), gr 32 2] 4) := by dec_rfl
theorem p8_20 : ∀ feat, Dec feat p8 20 (FV7z.mk .mov 64 [.mem (mg (some 1) (some 0) 8 0 64), gr 64 12] 4) := by dec_rfl
theorem p8_24 : ∀ feat, Dec feat p8 24 (FV7z.mk .test 32 [gr 32 15, Src.opd 32 (.r 15)] 3) := by dec_rfl

/-- What the stretch does. -/
def o8 : List Op := [
  Op.ld 32 0 (some 4) none 1 40,
  Op.ld 64 1 (some 4) none 1 32,
  Op.ld 32 15 (some 5) none 1 8,
  Op.lea 32 2 (some 0) none 1 1,
  Op.st 32 (some 4) none 1 40 2,
  Op.st 64 (some 1) (some 0) 8 0 12,
  Op.test 32 15 (.r 15)]

theorem b8 (prof : Profile) : Blk prof p8 0 27 o8 :=
  .cons (p8_0 _) (OpI.ld (.inl rfl)) (by decide) <|
  .cons (p8_4 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p8_9 _) (OpI.ld (.inl rfl)) (by decide) <|
  .cons (p8_13 _) (OpI.lea (.inl rfl)) (by decide) <|
  .cons (p8_16 _) (OpI.st (.inr (.inr (.inl rfl)))) (by decide) <|
  .cons (p8_20 _) (OpI.st (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p8_24 _) (OpI.test (.r 15) (.inl rfl)) (by decide) <|
  .nil 27

def j4 : List Byte := [0x0f, 0x85, 0xc3, 0x00, 0x00, 0x00]
theorem j4_0 : ∀ feat, Dec feat j4 0 (FV7z.mk (.jcc 5) 64 [.rel 195] 6) := by dec_rfl

/-- The stretch at `221`. -/
def p9 : List Byte := [
  0x4c, 0x8d, 0x64, 0x24, 0x20, 0x48, 0x8b, 0x3b, 0x44, 0x89, 0xf1, 0x44, 0x89, 0xee, 0x4c, 0x89,
  0xe2]

theorem p9_0 : ∀ feat, Dec feat p9 0 (FV7z.mk .lea 64 [gr 64 12, .mem (mg (some 4) none 1 32 0)] 5) := by dec_rfl
theorem p9_5 : ∀ feat, Dec feat p9 5 (FV7z.mk .mov 64 [gr 64 7, .mem (mg (some 3) none 1 0 64)] 3) := by dec_rfl
theorem p9_8 : ∀ feat, Dec feat p9 8 (FV7z.mk .mov 32 [gr 32 1, Src.opd 32 (.r 14)] 3) := by dec_rfl
theorem p9_11 : ∀ feat, Dec feat p9 11 (FV7z.mk .mov 32 [gr 32 6, Src.opd 32 (.r 13)] 3) := by dec_rfl
theorem p9_14 : ∀ feat, Dec feat p9 14 (FV7z.mk .mov 64 [gr 64 2, Src.opd 64 (.r 12)] 3) := by dec_rfl

/-- What the stretch does. -/
def o9 : List Op := [
  Op.lea 64 12 (some 4) none 1 32,
  Op.ld 64 7 (some 3) none 1 0,
  Op.mov 32 1 (.r 14),
  Op.mov 32 6 (.r 13),
  Op.mov 64 2 (.r 12)]

theorem b9 (prof : Profile) : Blk prof p9 0 17 o9 :=
  .cons (p9_0 _) (OpI.lea (.inr rfl)) (by decide) <|
  .cons (p9_5 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p9_8 _) (OpI.mov (.r 14) (.inl rfl)) (by decide) <|
  .cons (p9_11 _) (OpI.mov (.r 13) (.inl rfl)) (by decide) <|
  .cons (p9_14 _) (OpI.mov (.r 12) (.inr rfl)) (by decide) <|
  .nil 17

/-- The stretch at `243`. -/
def p10 : List Byte := [
  0x41, 0x89, 0xc4, 0x8b, 0x44, 0x24, 0x28, 0x48, 0x8b, 0x7c, 0x24, 0x20, 0x85, 0xc0]

theorem p10_0 : ∀ feat, Dec feat p10 0 (FV7z.mk .mov 32 [gr 32 12, Src.opd 32 (.r 0)] 3) := by dec_rfl
theorem p10_3 : ∀ feat, Dec feat p10 3 (FV7z.mk .mov 32 [gr 32 0, .mem (mg (some 4) none 1 40 32)] 4) := by dec_rfl
theorem p10_7 : ∀ feat, Dec feat p10 7 (FV7z.mk .mov 64 [gr 64 7, .mem (mg (some 4) none 1 32 64)] 5) := by dec_rfl
theorem p10_12 : ∀ feat, Dec feat p10 12 (FV7z.mk .test 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl

/-- What the stretch does. -/
def o10 : List Op := [
  Op.mov 32 12 (.r 0),
  Op.ld 32 0 (some 4) none 1 40,
  Op.ld 64 7 (some 4) none 1 32,
  Op.test 32 0 (.r 0)]

theorem b10 (prof : Profile) : Blk prof p10 0 14 o10 :=
  .cons (p10_0 _) (OpI.mov (.r 0) (.inl rfl)) (by decide) <|
  .cons (p10_3 _) (OpI.ld (.inl rfl)) (by decide) <|
  .cons (p10_7 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p10_12 _) (OpI.test (.r 0) (.inl rfl)) (by decide) <|
  .nil 14

def j5 : List Byte := [0x74, 0x40]
theorem j5_0 : ∀ feat, Dec feat j5 0 (FV7z.mk (.jcc 4) 64 [.rel 64] 2) := by dec_rfl

/-- The stretch at `259`. -/
def p11 : List Byte := [
  0x8d, 0x58, 0xff, 0x48, 0xc1, 0xe3, 0x03, 0x66, 0x0f, 0x1f, 0x44, 0x00, 0x00]

theorem p11_0 : ∀ feat, Dec feat p11 0 (FV7z.mk .lea 32 [gr 32 3, .mem (mg (some 0) none 1 18446744073709551615 0)] 3) := by dec_rfl
theorem p11_3 : ∀ feat, Dec feat p11 3 (FV7z.mk .shl 64 [gr 64 3, Src.opd 8 (.i 3)] 4) := by dec_rfl
theorem p11_7 : ∀ feat, Dec feat p11 7 (FV7z.mk .nop 16 [.mem (mg (some 0) (some 0) 1 0 16)] 6) := by dec_rfl

/-- What the stretch does. -/
def o11 : List Op := [
  Op.lea 32 3 (some 0) none 1 18446744073709551615,
  Op.shl64 3 (.i 3),
  Op.nop]

theorem b11 (prof : Profile) : Blk prof p11 0 13 o11 :=
  .cons (p11_0 _) (OpI.lea (.inl rfl)) (by decide) <|
  .cons (p11_3 _) (OpI.shl64 (.i 3)) (by decide) <|
  .cons (p11_7 _) (OpI.nop) (by decide) <|
  .nil 13

/-- The stretch at `272`. -/
def p12 : List Byte := [
  0x48, 0x8b, 0x2c, 0x1f, 0x48, 0x85, 0xed]

theorem p12_0 : ∀ feat, Dec feat p12 0 (FV7z.mk .mov 64 [gr 64 5, .mem (mg (some 7) (some 3) 1 0 64)] 4) := by dec_rfl
theorem p12_4 : ∀ feat, Dec feat p12 4 (FV7z.mk .test 64 [gr 64 5, Src.opd 64 (.r 5)] 3) := by dec_rfl

/-- What the stretch does. -/
def o12 : List Op := [
  Op.ld 64 5 (some 7) (some 3) 1 0,
  Op.test 64 5 (.r 5)]

theorem b12 (prof : Profile) : Blk prof p12 0 7 o12 :=
  .cons (p12_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p12_4 _) (OpI.test (.r 5) (.inr rfl)) (by decide) <|
  .nil 7

def j6 : List Byte := [0x74, 0x20]
theorem j6_0 : ∀ feat, Dec feat j6 0 (FV7z.mk (.jcc 4) 64 [.rel 32] 2) := by dec_rfl

/-- The stretch at `281`. -/
def p13 : List Byte := [
  0x48, 0x8b, 0x7d, 0x00, 0x48, 0x85, 0xff]

theorem p13_0 : ∀ feat, Dec feat p13 0 (FV7z.mk .mov 64 [gr 64 7, .mem (mg (some 5) none 1 0 64)] 4) := by dec_rfl
theorem p13_4 : ∀ feat, Dec feat p13 4 (FV7z.mk .test 64 [gr 64 7, Src.opd 64 (.r 7)] 3) := by dec_rfl

/-- What the stretch does. -/
def o13 : List Op := [
  Op.ld 64 7 (some 5) none 1 0,
  Op.test 64 7 (.r 7)]

theorem b13 (prof : Profile) : Blk prof p13 0 7 o13 :=
  .cons (p13_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p13_4 _) (OpI.test (.r 7) (.inr rfl)) (by decide) <|
  .nil 7

def j7 : List Byte := [0x74, 0x05]
theorem j7_0 : ∀ feat, Dec feat j7 0 (FV7z.mk (.jcc 4) 64 [.rel 5] 2) := by dec_rfl

/-- The stretch at `295`. -/
def p14 : List Byte := [
  0x48, 0x89, 0xef, 0xbe, 0x10, 0x00, 0x00, 0x00]

theorem p14_0 : ∀ feat, Dec feat p14 0 (FV7z.mk .mov 64 [gr 64 7, Src.opd 64 (.r 5)] 3) := by dec_rfl
theorem p14_3 : ∀ feat, Dec feat p14 3 (FV7z.mk .mov 32 [gr 32 6, Src.opd 32 (.i 16)] 5) := by dec_rfl

/-- What the stretch does. -/
def o14 : List Op := [
  Op.mov 64 7 (.r 5),
  Op.mov 32 6 (.i 16)]

theorem b14 (prof : Profile) : Blk prof p14 0 8 o14 :=
  .cons (p14_0 _) (OpI.mov (.r 5) (.inr rfl)) (by decide) <|
  .cons (p14_3 _) (OpI.mov (.i 16) (.inl rfl)) (by decide) <|
  .nil 8

/-- The stretch at `308`. -/
def p15 : List Byte := [
  0x48, 0x8b, 0x7c, 0x24, 0x20]

theorem p15_0 : ∀ feat, Dec feat p15 0 (FV7z.mk .mov 64 [gr 64 7, .mem (mg (some 4) none 1 32 64)] 5) := by dec_rfl

/-- What the stretch does. -/
def o15 : List Op := [
  Op.ld 64 7 (some 4) none 1 32]

theorem b15 (prof : Profile) : Blk prof p15 0 5 o15 :=
  .cons (p15_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .nil 5

/-- The stretch at `313`. -/
def p16 : List Byte := [
  0x48, 0x83, 0xeb, 0x08, 0x48, 0x83, 0xfb, 0xf8]

theorem p16_0 : ∀ feat, Dec feat p16 0 (FV7z.mk .sub 64 [gr 64 3, Src.opd 64 (.i 8)] 4) := by dec_rfl
theorem p16_4 : ∀ feat, Dec feat p16 4 (FV7z.mk .cmp 64 [gr 64 3, Src.opd 64 (.i 18446744073709551608)] 4) := by dec_rfl

/-- What the stretch does. -/
def o16 : List Op := [
  Op.sub 64 3 (.i 8),
  Op.cmp 64 3 (.i 18446744073709551608)]

theorem b16 (prof : Profile) : Blk prof p16 0 8 o16 :=
  .cons (p16_0 _) (OpI.sub (.i 8) (.inr rfl)) (by decide) <|
  .cons (p16_4 _) (OpI.cmp (.i 18446744073709551608) (.inr rfl)) (by decide) <|
  .nil 8

def j8 : List Byte := [0x75, 0xcd]
theorem j8_0 : ∀ feat, Dec feat j8 0 (FV7z.mk (.jcc 5) 64 [.rel 18446744073709551565] 2) := by dec_rfl

/-- The stretch at `323`. -/
def p17 : List Byte := [
  0x48, 0x85, 0xff]

theorem p17_0 : ∀ feat, Dec feat p17 0 (FV7z.mk .test 64 [gr 64 7, Src.opd 64 (.r 7)] 3) := by dec_rfl

/-- What the stretch does. -/
def o17 : List Op := [
  Op.test 64 7 (.r 7)]

theorem b17 (prof : Profile) : Blk prof p17 0 3 o17 :=
  .cons (p17_0 _) (OpI.test (.r 7) (.inr rfl)) (by decide) <|
  .nil 3

/-- The stretch at `333`. -/
def p18 : List Byte := [
  0x48, 0x8b, 0x44, 0x24, 0x38, 0x64, 0x48, 0x33, 0x04, 0x25, 0x28, 0x00, 0x00, 0x00]

theorem p18_0 : ∀ feat, Dec feat p18 0 (FV7z.mk .mov 64 [gr 64 0, .mem (mg (some 4) none 1 56 64)] 5) := by dec_rfl
theorem p18_5 : ∀ feat, Dec feat p18 5 (FV7z.mk .xor 64 [gr 64 0, .mem (mf none none 1 40 64)] 9) := by dec_rfl

/-- What the stretch does. -/
def o18 (fb : Addr) : List Op := [
  Op.ld 64 0 (some 4) none 1 56,
  Op.xormf fb 64 0 none none 1 40]

theorem b18 (prof : Profile) (fb : Addr) : BlkF prof p18 (0x45447d : Addr) fb 0 14 (o18 fb) :=
  .cons (p18_0 _) (((OpI.ld (.inr rfl)).at _).fs _) (by decide) <|
  .cons (p18_5 _) (OpIF.xormf (.inr rfl)) (by decide) <|
  .nil 14

def j9 : List Byte := [0x0f, 0x85, 0x46, 0x01, 0x00, 0x00]
theorem j9_0 : ∀ feat, Dec feat j9 0 (FV7z.mk (.jcc 5) 64 [.rel 326] 6) := by dec_rfl

/-- The stretch at `353`. -/
def p19 : List Byte := [
  0x48, 0x83, 0xc4, 0x48, 0x44, 0x89, 0xe0, 0x5b, 0x5d, 0x41, 0x5c, 0x41, 0x5d, 0x41, 0x5e, 0x41,
  0x5f]

theorem p19_0 : ∀ feat, Dec feat p19 0 (FV7z.mk .add 64 [gr 64 4, Src.opd 64 (.i 72)] 4) := by dec_rfl
theorem p19_4 : ∀ feat, Dec feat p19 4 (FV7z.mk .mov 32 [gr 32 0, Src.opd 32 (.r 12)] 3) := by dec_rfl
theorem p19_7 : ∀ feat, Dec feat p19 7 (FV7z.mk .pop 64 [gr 64 3] 1) := by dec_rfl
theorem p19_8 : ∀ feat, Dec feat p19 8 (FV7z.mk .pop 64 [gr 64 5] 1) := by dec_rfl
theorem p19_9 : ∀ feat, Dec feat p19 9 (FV7z.mk .pop 64 [gr 64 12] 2) := by dec_rfl
theorem p19_11 : ∀ feat, Dec feat p19 11 (FV7z.mk .pop 64 [gr 64 13] 2) := by dec_rfl
theorem p19_13 : ∀ feat, Dec feat p19 13 (FV7z.mk .pop 64 [gr 64 14] 2) := by dec_rfl
theorem p19_15 : ∀ feat, Dec feat p19 15 (FV7z.mk .pop 64 [gr 64 15] 2) := by dec_rfl

/-- What the stretch does. -/
def o19 : List Op := [
  Op.add 64 4 (.i 72),
  Op.mov 32 0 (.r 12),
  Op.pop 3,
  Op.pop 5,
  Op.pop 12,
  Op.pop 13,
  Op.pop 14,
  Op.pop 15]

theorem b19 (prof : Profile) : Blk prof p19 0 17 o19 :=
  .cons (p19_0 _) (OpI.add (.i 72) (.inr rfl)) (by decide) <|
  .cons (p19_4 _) (OpI.mov (.r 12) (.inl rfl)) (by decide) <|
  .cons (p19_7 _) (OpI.pop) (by decide) <|
  .cons (p19_8 _) (OpI.pop) (by decide) <|
  .cons (p19_9 _) (OpI.pop) (by decide) <|
  .cons (p19_11 _) (OpI.pop) (by decide) <|
  .cons (p19_13 _) (OpI.pop) (by decide) <|
  .cons (p19_15 _) (OpI.pop) (by decide) <|
  .nil 17

/-- The stretch at `376`. -/
def p20 : List Byte := [
  0x4c, 0x89, 0xc6, 0x48, 0xc1, 0xe2, 0x03, 0x48, 0x89, 0xc7, 0x4c, 0x89, 0x44, 0x24, 0x08]

theorem p20_0 : ∀ feat, Dec feat p20 0 (FV7z.mk .mov 64 [gr 64 6, Src.opd 64 (.r 8)] 3) := by dec_rfl
theorem p20_3 : ∀ feat, Dec feat p20 3 (FV7z.mk .shl 64 [gr 64 2, Src.opd 8 (.i 3)] 4) := by dec_rfl
theorem p20_7 : ∀ feat, Dec feat p20 7 (FV7z.mk .mov 64 [gr 64 7, Src.opd 64 (.r 0)] 3) := by dec_rfl
theorem p20_10 : ∀ feat, Dec feat p20 10 (FV7z.mk .mov 64 [.mem (mg (some 4) none 1 8 64), gr 64 8] 5) := by dec_rfl

/-- What the stretch does. -/
def o20 : List Op := [
  Op.mov 64 6 (.r 8),
  Op.shl64 2 (.i 3),
  Op.mov 64 7 (.r 0),
  Op.st 64 (some 4) none 1 8 8]

theorem b20 (prof : Profile) : Blk prof p20 0 15 o20 :=
  .cons (p20_0 _) (OpI.mov (.r 8) (.inr rfl)) (by decide) <|
  .cons (p20_3 _) (OpI.shl64 (.i 3)) (by decide) <|
  .cons (p20_7 _) (OpI.mov (.r 0) (.inr rfl)) (by decide) <|
  .cons (p20_10 _) (OpI.st (.inr (.inr (.inr rfl)))) (by decide) <|
  .nil 15

/-- The stretch at `396`. -/
def p21 : List Byte := [
  0x4c, 0x8b, 0x44, 0x24, 0x08]

theorem p21_0 : ∀ feat, Dec feat p21 0 (FV7z.mk .mov 64 [gr 64 8, .mem (mg (some 4) none 1 8 64)] 5) := by dec_rfl

/-- What the stretch does. -/
def o21 : List Op := [
  Op.ld 64 8 (some 4) none 1 8]

theorem b21 (prof : Profile) : Blk prof p21 0 5 o21 :=
  .cons (p21_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .nil 5

/-- The stretch at `401`. -/
def p22 : List Byte := [
  0x4c, 0x89, 0xc7]

theorem p22_0 : ∀ feat, Dec feat p22 0 (FV7z.mk .mov 64 [gr 64 7, Src.opd 64 (.r 8)] 3) := by dec_rfl

/-- What the stretch does. -/
def o22 : List Op := [
  Op.mov 64 7 (.r 8)]

theorem b22 (prof : Profile) : Blk prof p22 0 3 o22 :=
  .cons (p22_0 _) (OpI.mov (.r 8) (.inr rfl)) (by decide) <|
  .nil 3

def j10 : List Byte := [0xe9, 0xf4, 0xfe, 0xff, 0xff]
theorem j10_0 : ∀ feat, Dec feat j10 0 (FV7z.mk .jmp 64 [.rel 18446744073709551348] 5) := by dec_rfl

/-- The stretch at `416`. -/
def p23 : List Byte := [
  0xb8, 0xff, 0xff, 0xff, 0x7f, 0x29, 0xd0, 0x85, 0xd2]

theorem p23_0 : ∀ feat, Dec feat p23 0 (FV7z.mk .mov 32 [gr 32 0, Src.opd 32 (.i 2147483647)] 5) := by dec_rfl
theorem p23_5 : ∀ feat, Dec feat p23 5 (FV7z.mk .sub 32 [gr 32 0, Src.opd 32 (.r 2)] 2) := by dec_rfl
theorem p23_7 : ∀ feat, Dec feat p23 7 (FV7z.mk .test 32 [gr 32 2, Src.opd 32 (.r 2)] 2) := by dec_rfl

/-- What the stretch does. -/
def o23 : List Op := [
  Op.mov 32 0 (.i 2147483647),
  Op.sub 32 0 (.r 2),
  Op.test 32 2 (.r 2)]

theorem b23 (prof : Profile) : Blk prof p23 0 9 o23 :=
  .cons (p23_0 _) (OpI.mov (.i 2147483647) (.inl rfl)) (by decide) <|
  .cons (p23_5 _) (OpI.sub (.r 2) (.inl rfl)) (by decide) <|
  .cons (p23_7 _) (OpI.test (.r 2) (.inl rfl)) (by decide) <|
  .nil 9

/-- The stretch at `431`. -/
def p24 : List Byte := [
  0x41, 0x39, 0xc7]

theorem p24_0 : ∀ feat, Dec feat p24 0 (FV7z.mk .cmp 32 [gr 32 15, Src.opd 32 (.r 0)] 3) := by dec_rfl

/-- What the stretch does. -/
def o24 : List Op := [
  Op.cmp 32 15 (.r 0)]

theorem b24 (prof : Profile) : Blk prof p24 0 3 o24 :=
  .cons (p24_0 _) (OpI.cmp (.r 0) (.inl rfl)) (by decide) <|
  .nil 3

/-- The stretch at `440`. -/
def p25 : List Byte := [
  0x42, 0x8d, 0x0c, 0x3a, 0x3b, 0x4c, 0x24, 0x2c]

theorem p25_0 : ∀ feat, Dec feat p25 0 (FV7z.mk .lea 32 [gr 32 1, .mem (mg (some 2) (some 15) 1 0 0)] 4) := by dec_rfl
theorem p25_4 : ∀ feat, Dec feat p25 4 (FV7z.mk .cmp 32 [gr 32 1, .mem (mg (some 4) none 1 44 32)] 4) := by dec_rfl

/-- What the stretch does. -/
def o25 : List Op := [
  Op.lea 32 1 (some 2) (some 15) 1 0,
  Op.cmpm 32 1 (some 4) none 1 44]

theorem b25 (prof : Profile) : Blk prof p25 0 8 o25 :=
  .cons (p25_0 _) (OpI.lea (.inl rfl)) (by decide) <|
  .cons (p25_4 _) (OpI.cmpm (.inl rfl)) (by decide) <|
  .nil 8

def j11 : List Byte := [0x77, 0x6e]
theorem j11_0 : ∀ feat, Dec feat j11 0 (FV7z.mk (.jcc 7) 64 [.rel 110] 2) := by dec_rfl

/-- The stretch at `450`. -/
def p26 : List Byte := [
  0x41, 0x8d, 0x47, 0xff, 0x45, 0x31, 0xff, 0x48, 0x8d, 0x04, 0xc5, 0x08, 0x00, 0x00, 0x00, 0x48,
  0x89, 0x44, 0x24, 0x10, 0x48, 0x8d, 0x44, 0x24, 0x20, 0x48, 0x89, 0x44, 0x24, 0x18]

theorem p26_0 : ∀ feat, Dec feat p26 0 (FV7z.mk .lea 32 [gr 32 0, .mem (mg (some 15) none 1 18446744073709551615 0)] 4) := by dec_rfl
theorem p26_4 : ∀ feat, Dec feat p26 4 (FV7z.mk .xor 32 [gr 32 15, Src.opd 32 (.r 15)] 3) := by dec_rfl
theorem p26_7 : ∀ feat, Dec feat p26 7 (FV7z.mk .lea 64 [gr 64 0, .mem (mg none (some 0) 8 8 0)] 8) := by dec_rfl
theorem p26_15 : ∀ feat, Dec feat p26 15 (FV7z.mk .mov 64 [.mem (mg (some 4) none 1 16 64), gr 64 0] 5) := by dec_rfl
theorem p26_20 : ∀ feat, Dec feat p26 20 (FV7z.mk .lea 64 [gr 64 0, .mem (mg (some 4) none 1 32 0)] 5) := by dec_rfl
theorem p26_25 : ∀ feat, Dec feat p26 25 (FV7z.mk .mov 64 [.mem (mg (some 4) none 1 24 64), gr 64 0] 5) := by dec_rfl

/-- What the stretch does. -/
def o26 : List Op := [
  Op.lea 32 0 (some 15) none 1 18446744073709551615,
  Op.xor 32 15 (.r 15),
  Op.lea 64 0 none (some 0) 8 8,
  Op.st 64 (some 4) none 1 16 0,
  Op.lea 64 0 (some 4) none 1 32,
  Op.st 64 (some 4) none 1 24 0]

theorem b26 (prof : Profile) : Blk prof p26 0 30 o26 :=
  .cons (p26_0 _) (OpI.lea (.inl rfl)) (by decide) <|
  .cons (p26_4 _) (OpI.xor (.r 15) (.inl rfl)) (by decide) <|
  .cons (p26_7 _) (OpI.lea (.inr rfl)) (by decide) <|
  .cons (p26_15 _) (OpI.st (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p26_20 _) (OpI.lea (.inr rfl)) (by decide) <|
  .cons (p26_25 _) (OpI.st (.inr (.inr (.inr rfl)))) (by decide) <|
  .nil 30

/-- The stretch at `480`. -/
def p27 : List Byte := [
  0x48, 0x8b, 0x45, 0x00, 0xbf, 0x10, 0x00, 0x00, 0x00, 0x4c, 0x8b, 0x64, 0x24, 0x18, 0x4a, 0x8b,
  0x04, 0x38, 0x48, 0x89, 0x44, 0x24, 0x08]

theorem p27_0 : ∀ feat, Dec feat p27 0 (FV7z.mk .mov 64 [gr 64 0, .mem (mg (some 5) none 1 0 64)] 4) := by dec_rfl
theorem p27_4 : ∀ feat, Dec feat p27 4 (FV7z.mk .mov 32 [gr 32 7, Src.opd 32 (.i 16)] 5) := by dec_rfl
theorem p27_9 : ∀ feat, Dec feat p27 9 (FV7z.mk .mov 64 [gr 64 12, .mem (mg (some 4) none 1 24 64)] 5) := by dec_rfl
theorem p27_14 : ∀ feat, Dec feat p27 14 (FV7z.mk .mov 64 [gr 64 0, .mem (mg (some 0) (some 15) 1 0 64)] 4) := by dec_rfl
theorem p27_18 : ∀ feat, Dec feat p27 18 (FV7z.mk .mov 64 [.mem (mg (some 4) none 1 8 64), gr 64 0] 5) := by dec_rfl

/-- What the stretch does. -/
def o27 : List Op := [
  Op.ld 64 0 (some 5) none 1 0,
  Op.mov 32 7 (.i 16),
  Op.ld 64 12 (some 4) none 1 24,
  Op.ld 64 0 (some 0) (some 15) 1 0,
  Op.st 64 (some 4) none 1 8 0]

theorem b27 (prof : Profile) : Blk prof p27 0 23 o27 :=
  .cons (p27_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p27_4 _) (OpI.mov (.i 16) (.inl rfl)) (by decide) <|
  .cons (p27_9 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p27_14 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p27_18 _) (OpI.st (.inr (.inr (.inr rfl)))) (by decide) <|
  .nil 23

/-- The stretch at `508`. -/
def p28 : List Byte := [
  0x48, 0x8b, 0x74, 0x24, 0x08, 0x48, 0x89, 0xc7, 0x49, 0x89, 0xc4]

theorem p28_0 : ∀ feat, Dec feat p28 0 (FV7z.mk .mov 64 [gr 64 6, .mem (mg (some 4) none 1 8 64)] 5) := by dec_rfl
theorem p28_5 : ∀ feat, Dec feat p28 5 (FV7z.mk .mov 64 [gr 64 7, Src.opd 64 (.r 0)] 3) := by dec_rfl
theorem p28_8 : ∀ feat, Dec feat p28 8 (FV7z.mk .mov 64 [gr 64 12, Src.opd 64 (.r 0)] 3) := by dec_rfl

/-- What the stretch does. -/
def o28 : List Op := [
  Op.ld 64 6 (some 4) none 1 8,
  Op.mov 64 7 (.r 0),
  Op.mov 64 12 (.r 0)]

theorem b28 (prof : Profile) : Blk prof p28 0 11 o28 :=
  .cons (p28_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p28_5 _) (OpI.mov (.r 0) (.inr rfl)) (by decide) <|
  .cons (p28_8 _) (OpI.mov (.r 0) (.inr rfl)) (by decide) <|
  .nil 11

/-- The stretch at `524`. -/
def p29 : List Byte := [
  0x8b, 0x44, 0x24, 0x28, 0x49, 0x83, 0xc7, 0x08, 0x8d, 0x50, 0x01, 0x89, 0x54, 0x24, 0x28, 0x48,
  0x8b, 0x54, 0x24, 0x20, 0x4c, 0x89, 0x24, 0xc2, 0x4c, 0x39, 0x7c, 0x24, 0x10]

theorem p29_0 : ∀ feat, Dec feat p29 0 (FV7z.mk .mov 32 [gr 32 0, .mem (mg (some 4) none 1 40 32)] 4) := by dec_rfl
theorem p29_4 : ∀ feat, Dec feat p29 4 (FV7z.mk .add 64 [gr 64 15, Src.opd 64 (.i 8)] 4) := by dec_rfl
theorem p29_8 : ∀ feat, Dec feat p29 8 (FV7z.mk .lea 32 [gr 32 2, .mem (mg (some 0) none 1 1 0)] 3) := by dec_rfl
theorem p29_11 : ∀ feat, Dec feat p29 11 (FV7z.mk .mov 32 [.mem (mg (some 4) none 1 40 32), gr 32 2] 4) := by dec_rfl
theorem p29_15 : ∀ feat, Dec feat p29 15 (FV7z.mk .mov 64 [gr 64 2, .mem (mg (some 4) none 1 32 64)] 5) := by dec_rfl
theorem p29_20 : ∀ feat, Dec feat p29 20 (FV7z.mk .mov 64 [.mem (mg (some 2) (some 0) 8 0 64), gr 64 12] 4) := by dec_rfl
theorem p29_24 : ∀ feat, Dec feat p29 24 (FV7z.mk .cmp 64 [.mem (mg (some 4) none 1 16 64), gr 64 15] 5) := by dec_rfl

/-- What the stretch does. -/
def o29 : List Op := [
  Op.ld 32 0 (some 4) none 1 40,
  Op.add 64 15 (.i 8),
  Op.lea 32 2 (some 0) none 1 1,
  Op.st 32 (some 4) none 1 40 2,
  Op.ld 64 2 (some 4) none 1 32,
  Op.st 64 (some 2) (some 0) 8 0 12,
  Op.cmpmr 64 (some 4) none 1 16 15]

theorem b29 (prof : Profile) : Blk prof p29 0 29 o29 :=
  .cons (p29_0 _) (OpI.ld (.inl rfl)) (by decide) <|
  .cons (p29_4 _) (OpI.add (.i 8) (.inr rfl)) (by decide) <|
  .cons (p29_8 _) (OpI.lea (.inl rfl)) (by decide) <|
  .cons (p29_11 _) (OpI.st (.inr (.inr (.inl rfl)))) (by decide) <|
  .cons (p29_15 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p29_20 _) (OpI.st (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p29_24 _) (OpI.cmpmr (.inr rfl)) (by decide) <|
  .nil 29

def j12 : List Byte := [0x75, 0xb5]
theorem j12_0 : ∀ feat, Dec feat j12 0 (FV7z.mk (.jcc 5) 64 [.rel 18446744073709551541] 2) := by dec_rfl

def j13 : List Byte := [0xe9, 0xad, 0xfe, 0xff, 0xff]
theorem j13_0 : ∀ feat, Dec feat j13 0 (FV7z.mk .jmp 64 [.rel 18446744073709551277] 5) := by dec_rfl

/-- The stretch at `560`. -/
def p30 : List Byte := [
  0x89, 0xd1, 0x4c, 0x8d, 0x64, 0x24, 0x20, 0xc1, 0xe9, 0x02, 0x41, 0x39, 0xcf, 0x41, 0x0f, 0x43,
  0xcf, 0x39, 0xc8, 0x0f, 0x47, 0xc1, 0x8d, 0x3c, 0x10, 0x89, 0x7c, 0x24, 0x08, 0x48, 0xc1, 0xe7,
  0x03]

theorem p30_0 : ∀ feat, Dec feat p30 0 (FV7z.mk .mov 32 [gr 32 1, Src.opd 32 (.r 2)] 2) := by dec_rfl
theorem p30_2 : ∀ feat, Dec feat p30 2 (FV7z.mk .lea 64 [gr 64 12, .mem (mg (some 4) none 1 32 0)] 5) := by dec_rfl
theorem p30_7 : ∀ feat, Dec feat p30 7 (FV7z.mk .shr 32 [gr 32 1, Src.opd 8 (.i 2)] 3) := by dec_rfl
theorem p30_10 : ∀ feat, Dec feat p30 10 (FV7z.mk .cmp 32 [gr 32 15, Src.opd 32 (.r 1)] 3) := by dec_rfl
theorem p30_13 : ∀ feat, Dec feat p30 13 (FV7z.mk (.cmovcc 3) 32 [gr 32 1, gr 32 15] 4) := by dec_rfl
theorem p30_17 : ∀ feat, Dec feat p30 17 (FV7z.mk .cmp 32 [gr 32 0, Src.opd 32 (.r 1)] 2) := by dec_rfl
theorem p30_19 : ∀ feat, Dec feat p30 19 (FV7z.mk (.cmovcc 7) 32 [gr 32 0, gr 32 1] 3) := by dec_rfl
theorem p30_22 : ∀ feat, Dec feat p30 22 (FV7z.mk .lea 32 [gr 32 7, .mem (mg (some 0) (some 2) 1 0 0)] 3) := by dec_rfl
theorem p30_25 : ∀ feat, Dec feat p30 25 (FV7z.mk .mov 32 [.mem (mg (some 4) none 1 8 32), gr 32 7] 4) := by dec_rfl
theorem p30_29 : ∀ feat, Dec feat p30 29 (FV7z.mk .shl 64 [gr 64 7, Src.opd 8 (.i 3)] 4) := by dec_rfl

/-- What the stretch does. -/
def o30 : List Op := [
  Op.mov 32 1 (.r 2),
  Op.lea 64 12 (some 4) none 1 32,
  Op.shr 1 (.i 2),
  Op.cmp 32 15 (.r 1),
  Op.cmov32 3 1 15,
  Op.cmp 32 0 (.r 1),
  Op.cmov32 7 0 1,
  Op.lea 32 7 (some 0) (some 2) 1 0,
  Op.st 32 (some 4) none 1 8 7,
  Op.shl64 7 (.i 3)]

theorem b30 (prof : Profile) : Blk prof p30 0 33 o30 :=
  .cons (p30_0 _) (OpI.mov (.r 2) (.inl rfl)) (by decide) <|
  .cons (p30_2 _) (OpI.lea (.inr rfl)) (by decide) <|
  .cons (p30_7 _) (OpI.shr (.i 2)) (by decide) <|
  .cons (p30_10 _) (OpI.cmp (.r 1) (.inl rfl)) (by decide) <|
  .cons (p30_13 _) (OpI.cmov32) (by decide) <|
  .cons (p30_17 _) (OpI.cmp (.r 1) (.inl rfl)) (by decide) <|
  .cons (p30_19 _) (OpI.cmov32) (by decide) <|
  .cons (p30_22 _) (OpI.lea (.inl rfl)) (by decide) <|
  .cons (p30_25 _) (OpI.st (.inr (.inr (.inl rfl)))) (by decide) <|
  .cons (p30_29 _) (OpI.shl64 (.i 3)) (by decide) <|
  .nil 33

/-- The stretch at `598`. -/
def p31 : List Byte := [
  0x49, 0x89, 0xc4, 0x8b, 0x44, 0x24, 0x28, 0x4c, 0x8b, 0x44, 0x24, 0x20, 0x85, 0xc0]

theorem p31_0 : ∀ feat, Dec feat p31 0 (FV7z.mk .mov 64 [gr 64 12, Src.opd 64 (.r 0)] 3) := by dec_rfl
theorem p31_3 : ∀ feat, Dec feat p31 3 (FV7z.mk .mov 32 [gr 32 0, .mem (mg (some 4) none 1 40 32)] 4) := by dec_rfl
theorem p31_7 : ∀ feat, Dec feat p31 7 (FV7z.mk .mov 64 [gr 64 8, .mem (mg (some 4) none 1 32 64)] 5) := by dec_rfl
theorem p31_12 : ∀ feat, Dec feat p31 12 (FV7z.mk .test 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl

/-- What the stretch does. -/
def o31 : List Op := [
  Op.mov 64 12 (.r 0),
  Op.ld 32 0 (some 4) none 1 40,
  Op.ld 64 8 (some 4) none 1 32,
  Op.test 32 0 (.r 0)]

theorem b31 (prof : Profile) : Blk prof p31 0 14 o31 :=
  .cons (p31_0 _) (OpI.mov (.r 0) (.inr rfl)) (by decide) <|
  .cons (p31_3 _) (OpI.ld (.inl rfl)) (by decide) <|
  .cons (p31_7 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p31_12 _) (OpI.test (.r 0) (.inl rfl)) (by decide) <|
  .nil 14

def j14 : List Byte := [0x75, 0x1a]
theorem j14_0 : ∀ feat, Dec feat j14 0 (FV7z.mk (.jcc 5) 64 [.rel 26] 2) := by dec_rfl

def j15 : List Byte := [0x75, 0x32]
theorem j15_0 : ∀ feat, Dec feat j15 0 (FV7z.mk (.jcc 5) 64 [.rel 50] 2) := by dec_rfl

/-- The stretch at `619`. -/
def p32 : List Byte := [
  0x8b, 0x44, 0x24, 0x08, 0x4c, 0x89, 0x64, 0x24, 0x20, 0x89, 0x44, 0x24, 0x2c]

theorem p32_0 : ∀ feat, Dec feat p32 0 (FV7z.mk .mov 32 [gr 32 0, .mem (mg (some 4) none 1 8 32)] 4) := by dec_rfl
theorem p32_4 : ∀ feat, Dec feat p32 4 (FV7z.mk .mov 64 [.mem (mg (some 4) none 1 32 64), gr 64 12] 5) := by dec_rfl
theorem p32_9 : ∀ feat, Dec feat p32 9 (FV7z.mk .mov 32 [.mem (mg (some 4) none 1 44 32), gr 32 0] 4) := by dec_rfl

/-- What the stretch does. -/
def o32 : List Op := [
  Op.ld 32 0 (some 4) none 1 8,
  Op.st 64 (some 4) none 1 32 12,
  Op.st 32 (some 4) none 1 44 0]

theorem b32 (prof : Profile) : Blk prof p32 0 13 o32 :=
  .cons (p32_0 _) (OpI.ld (.inl rfl)) (by decide) <|
  .cons (p32_4 _) (OpI.st (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p32_9 _) (OpI.st (.inr (.inr (.inl rfl)))) (by decide) <|
  .nil 13

def j16 : List Byte := [0xe9, 0x45, 0xff, 0xff, 0xff]
theorem j16_0 : ∀ feat, Dec feat j16 0 (FV7z.mk .jmp 64 [.rel 18446744073709551429] 5) := by dec_rfl

/-- The stretch at `640`. -/
def p33 : List Byte := [
  0x4c, 0x89, 0xc6, 0x48, 0x8d, 0x14, 0xc5, 0x00, 0x00, 0x00, 0x00, 0x4c, 0x89, 0xe7, 0x4c, 0x89,
  0x44, 0x24, 0x10]

theorem p33_0 : ∀ feat, Dec feat p33 0 (FV7z.mk .mov 64 [gr 64 6, Src.opd 64 (.r 8)] 3) := by dec_rfl
theorem p33_3 : ∀ feat, Dec feat p33 3 (FV7z.mk .lea 64 [gr 64 2, .mem (mg none (some 0) 8 0 0)] 8) := by dec_rfl
theorem p33_11 : ∀ feat, Dec feat p33 11 (FV7z.mk .mov 64 [gr 64 7, Src.opd 64 (.r 12)] 3) := by dec_rfl
theorem p33_14 : ∀ feat, Dec feat p33 14 (FV7z.mk .mov 64 [.mem (mg (some 4) none 1 16 64), gr 64 8] 5) := by dec_rfl

/-- What the stretch does. -/
def o33 : List Op := [
  Op.mov 64 6 (.r 8),
  Op.lea 64 2 none (some 0) 8 0,
  Op.mov 64 7 (.r 12),
  Op.st 64 (some 4) none 1 16 8]

theorem b33 (prof : Profile) : Blk prof p33 0 19 o33 :=
  .cons (p33_0 _) (OpI.mov (.r 8) (.inr rfl)) (by decide) <|
  .cons (p33_3 _) (OpI.lea (.inr rfl)) (by decide) <|
  .cons (p33_11 _) (OpI.mov (.r 12) (.inr rfl)) (by decide) <|
  .cons (p33_14 _) (OpI.st (.inr (.inr (.inr rfl)))) (by decide) <|
  .nil 19

/-- The stretch at `664`. -/
def p34 : List Byte := [
  0x4c, 0x8b, 0x44, 0x24, 0x10]

theorem p34_0 : ∀ feat, Dec feat p34 0 (FV7z.mk .mov 64 [gr 64 8, .mem (mg (some 4) none 1 16 64)] 5) := by dec_rfl

/-- What the stretch does. -/
def o34 : List Op := [
  Op.ld 64 8 (some 4) none 1 16]

theorem b34 (prof : Profile) : Blk prof p34 0 5 o34 :=
  .cons (p34_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .nil 5

def j17 : List Byte := [0xeb, 0xc4]
theorem j17_0 : ∀ feat, Dec feat j17 0 (FV7z.mk .jmp 64 [.rel 18446744073709551556] 2) := by dec_rfl

end FV7z.Cpr
