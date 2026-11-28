import FV7z.Lemmas.SpFs
import FV7z.Lemmas.BlkOps12
import FV7z.Lemmas.BlkOps6
import FV7z.Lemmas.BlkOps2
/-!
# The stretches of straight-line code of `LzmaDec_Allocate` (PLAN.md §M, M1)

Each distinct stretch between labels and jumps (`p*`, 15 of them) and each distinct jump (`j*`, 9) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.Lza
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The stretch at `0`. -/
def p0 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0x41, 0x55, 0x49, 0x89, 0xcd, 0x41, 0x54, 0x55, 0x48, 0x89, 0xfd, 0x53,
  0x48, 0x83, 0xec, 0x18, 0x64, 0x48, 0x8b, 0x04, 0x25, 0x28, 0x00, 0x00, 0x00, 0x48, 0x89, 0x44,
  0x24, 0x08, 0x31, 0xc0, 0x48, 0x89, 0xe7]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem p0_4 : ∀ feat, Dec feat p0 4 (FV7z.mk .push 64 [gr 64 13] 2) := by dec_rfl
theorem p0_6 : ∀ feat, Dec feat p0 6 (FV7z.mk .mov 64 [gr 64 13, Src.opd 64 (.r 1)] 3) := by dec_rfl
theorem p0_9 : ∀ feat, Dec feat p0 9 (FV7z.mk .push 64 [gr 64 12] 2) := by dec_rfl
theorem p0_11 : ∀ feat, Dec feat p0 11 (FV7z.mk .push 64 [gr 64 5] 1) := by dec_rfl
theorem p0_12 : ∀ feat, Dec feat p0 12 (FV7z.mk .mov 64 [gr 64 5, Src.opd 64 (.r 7)] 3) := by dec_rfl
theorem p0_15 : ∀ feat, Dec feat p0 15 (FV7z.mk .push 64 [gr 64 3] 1) := by dec_rfl
theorem p0_16 : ∀ feat, Dec feat p0 16 (FV7z.mk .sub 64 [gr 64 4, Src.opd 64 (.i 24)] 4) := by dec_rfl
theorem p0_20 : ∀ feat, Dec feat p0 20 (FV7z.mk .mov 64 [gr 64 0, .mem (mf none none 1 40 64)] 9) := by dec_rfl
theorem p0_29 : ∀ feat, Dec feat p0 29 (FV7z.mk .mov 64 [.mem (mg (some 4) none 1 8 64), gr 64 0] 5) := by dec_rfl
theorem p0_34 : ∀ feat, Dec feat p0 34 (FV7z.mk .xor 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl
theorem p0_36 : ∀ feat, Dec feat p0 36 (FV7z.mk .mov 64 [gr 64 7, Src.opd 64 (.r 4)] 3) := by dec_rfl

/-- What the stretch does. -/
def o0 (fb : Addr) : List Op := [
  Op.nop,
  Op.push 13,
  Op.mov 64 13 (.r 1),
  Op.push 12,
  Op.push 5,
  Op.mov 64 5 (.r 7),
  Op.push 3,
  Op.sub 64 4 (.i 24),
  Op.ldf fb 64 0 none none 1 40,
  Op.st 64 (some 4) none 1 8 0,
  Op.xor 32 0 (.r 0),
  Op.mov 64 7 (.r 4)]

theorem b0 (prof : Profile) (fb : Addr) : BlkF prof p0 (0x42bf80 : Addr) fb 0 39 (o0 fb) :=
  .cons (p0_0 _) (((OpI.endbr).at _).fs _) (by decide) <|
  .cons (p0_4 _) (((OpI.push).at _).fs _) (by decide) <|
  .cons (p0_6 _) (((OpI.mov (.r 1) (.inr rfl)).at _).fs _) (by decide) <|
  .cons (p0_9 _) (((OpI.push).at _).fs _) (by decide) <|
  .cons (p0_11 _) (((OpI.push).at _).fs _) (by decide) <|
  .cons (p0_12 _) (((OpI.mov (.r 7) (.inr rfl)).at _).fs _) (by decide) <|
  .cons (p0_15 _) (((OpI.push).at _).fs _) (by decide) <|
  .cons (p0_16 _) (((OpI.sub (.i 24) (.inr rfl)).at _).fs _) (by decide) <|
  .cons (p0_20 _) (OpIF.ldf (.inr rfl)) (by decide) <|
  .cons (p0_29 _) (((OpI.st (.inr (.inr (.inr rfl)))).at _).fs _) (by decide) <|
  .cons (p0_34 _) (((OpI.xor (.r 0) (.inl rfl)).at _).fs _) (by decide) <|
  .cons (p0_36 _) (((OpI.mov (.r 4) (.inr rfl)).at _).fs _) (by decide) <|
  .nil 39

/-- The stretch at `44`. -/
def p1 : List Byte := [
  0x41, 0x89, 0xc4, 0x85, 0xc0]

theorem p1_0 : ∀ feat, Dec feat p1 0 (FV7z.mk .mov 32 [gr 32 12, Src.opd 32 (.r 0)] 3) := by dec_rfl
theorem p1_3 : ∀ feat, Dec feat p1 3 (FV7z.mk .test 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl

/-- What the stretch does. -/
def o1 : List Op := [
  Op.mov 32 12 (.r 0),
  Op.test 32 0 (.r 0)]

theorem b1 (prof : Profile) : Blk prof p1 0 5 o1 :=
  .cons (p1_0 _) (OpI.mov (.r 0) (.inl rfl)) (by decide) <|
  .cons (p1_3 _) (OpI.test (.r 0) (.inl rfl)) (by decide) <|
  .nil 5

def j0 : List Byte := [0x74, 0x25]
theorem j0_0 : ∀ feat, Dec feat j0 0 (FV7z.mk (.jcc 4) 64 [.rel 37] 2) := by dec_rfl

/-- The stretch at `51`. -/
def p2 : List Byte := [
  0x48, 0x8b, 0x44, 0x24, 0x08, 0x64, 0x48, 0x33, 0x04, 0x25, 0x28, 0x00, 0x00, 0x00]

theorem p2_0 : ∀ feat, Dec feat p2 0 (FV7z.mk .mov 64 [gr 64 0, .mem (mg (some 4) none 1 8 64)] 5) := by dec_rfl
theorem p2_5 : ∀ feat, Dec feat p2 5 (FV7z.mk .xor 64 [gr 64 0, .mem (mf none none 1 40 64)] 9) := by dec_rfl

/-- What the stretch does. -/
def o2 (fb : Addr) : List Op := [
  Op.ld 64 0 (some 4) none 1 8,
  Op.xormf fb 64 0 none none 1 40]

theorem b2 (prof : Profile) (fb : Addr) : BlkF prof p2 (0x42bfb3 : Addr) fb 0 14 (o2 fb) :=
  .cons (p2_0 _) (((OpI.ld (.inr rfl)).at _).fs _) (by decide) <|
  .cons (p2_5 _) (OpIF.xormf (.inr rfl)) (by decide) <|
  .nil 14

def j1 : List Byte := [0x0f, 0x85, 0xdf, 0x00, 0x00, 0x00]
theorem j1_0 : ∀ feat, Dec feat j1 0 (FV7z.mk (.jcc 5) 64 [.rel 223] 6) := by dec_rfl

/-- The stretch at `71`. -/
def p3 : List Byte := [
  0x48, 0x83, 0xc4, 0x18, 0x44, 0x89, 0xe0, 0x5b, 0x5d, 0x41, 0x5c, 0x41, 0x5d]

theorem p3_0 : ∀ feat, Dec feat p3 0 (FV7z.mk .add 64 [gr 64 4, Src.opd 64 (.i 24)] 4) := by dec_rfl
theorem p3_4 : ∀ feat, Dec feat p3 4 (FV7z.mk .mov 32 [gr 32 0, Src.opd 32 (.r 12)] 3) := by dec_rfl
theorem p3_7 : ∀ feat, Dec feat p3 7 (FV7z.mk .pop 64 [gr 64 3] 1) := by dec_rfl
theorem p3_8 : ∀ feat, Dec feat p3 8 (FV7z.mk .pop 64 [gr 64 5] 1) := by dec_rfl
theorem p3_9 : ∀ feat, Dec feat p3 9 (FV7z.mk .pop 64 [gr 64 12] 2) := by dec_rfl
theorem p3_11 : ∀ feat, Dec feat p3 11 (FV7z.mk .pop 64 [gr 64 13] 2) := by dec_rfl

/-- What the stretch does. -/
def o3 : List Op := [
  Op.add 64 4 (.i 24),
  Op.mov 32 0 (.r 12),
  Op.pop 3,
  Op.pop 5,
  Op.pop 12,
  Op.pop 13]

theorem b3 (prof : Profile) : Blk prof p3 0 13 o3 :=
  .cons (p3_0 _) (OpI.add (.i 24) (.inr rfl)) (by decide) <|
  .cons (p3_4 _) (OpI.mov (.r 12) (.inl rfl)) (by decide) <|
  .cons (p3_7 _) (OpI.pop) (by decide) <|
  .cons (p3_8 _) (OpI.pop) (by decide) <|
  .cons (p3_9 _) (OpI.pop) (by decide) <|
  .cons (p3_11 _) (OpI.pop) (by decide) <|
  .nil 13

/-- The stretch at `88`. -/
def p4 : List Byte := [
  0x0f, 0xb6, 0x54, 0x24, 0x01, 0x0f, 0xb6, 0x34, 0x24, 0x4c, 0x89, 0xe9, 0x48, 0x89, 0xef]

theorem p4_0 : ∀ feat, Dec feat p4 0 (FV7z.mk .movzx 32 [gr 32 2, .mem (mg (some 4) none 1 1 8)] 5) := by dec_rfl
theorem p4_5 : ∀ feat, Dec feat p4 5 (FV7z.mk .movzx 32 [gr 32 6, .mem (mg (some 4) none 1 0 8)] 4) := by dec_rfl
theorem p4_9 : ∀ feat, Dec feat p4 9 (FV7z.mk .mov 64 [gr 64 1, Src.opd 64 (.r 13)] 3) := by dec_rfl
theorem p4_12 : ∀ feat, Dec feat p4 12 (FV7z.mk .mov 64 [gr 64 7, Src.opd 64 (.r 5)] 3) := by dec_rfl

/-- What the stretch does. -/
def o4 : List Op := [
  Op.ldzx 8 2 (some 4) none 1 1,
  Op.ldzx 8 6 (some 4) none 1 0,
  Op.mov 64 1 (.r 13),
  Op.mov 64 7 (.r 5)]

theorem b4 (prof : Profile) : Blk prof p4 0 15 o4 :=
  .cons (p4_0 _) (OpI.ldzx (.inl rfl)) (by decide) <|
  .cons (p4_5 _) (OpI.ldzx (.inl rfl)) (by decide) <|
  .cons (p4_9 _) (OpI.mov (.r 13) (.inr rfl)) (by decide) <|
  .cons (p4_12 _) (OpI.mov (.r 5) (.inr rfl)) (by decide) <|
  .nil 15

def j2 : List Byte := [0x75, 0xc0]
theorem j2_0 : ∀ feat, Dec feat j2 0 (FV7z.mk (.jcc 5) 64 [.rel 18446744073709551552] 2) := by dec_rfl

/-- The stretch at `115`. -/
def p5 : List Byte := [
  0x8b, 0x44, 0x24, 0x04, 0x3d, 0xff, 0xff, 0xff, 0x3f]

theorem p5_0 : ∀ feat, Dec feat p5 0 (FV7z.mk .mov 32 [gr 32 0, .mem (mg (some 4) none 1 4 32)] 4) := by dec_rfl
theorem p5_4 : ∀ feat, Dec feat p5 4 (FV7z.mk .cmp 32 [gr 32 0, Src.opd 32 (.i 1073741823)] 5) := by dec_rfl

/-- What the stretch does. -/
def o5 : List Op := [
  Op.ld 32 0 (some 4) none 1 4,
  Op.cmp 32 0 (.i 1073741823)]

theorem b5 (prof : Profile) : Blk prof p5 0 9 o5 :=
  .cons (p5_0 _) (OpI.ld (.inl rfl)) (by decide) <|
  .cons (p5_4 _) (OpI.cmp (.i 1073741823) (.inl rfl)) (by decide) <|
  .nil 9

def j3 : List Byte := [0x0f, 0x87, 0x7e, 0x00, 0x00, 0x00]
theorem j3_0 : ∀ feat, Dec feat j3 0 (FV7z.mk (.jcc 7) 64 [.rel 126] 6) := by dec_rfl

/-- The stretch at `130`. -/
def p6 : List Byte := [
  0x3d, 0x00, 0x00, 0x40, 0x00, 0x48, 0x19, 0xdb, 0x81, 0xe3, 0x00, 0xf0, 0x0f, 0x00, 0x48, 0x81,
  0xeb, 0x00, 0x00, 0x10, 0x00, 0x3d, 0x00, 0x00, 0x40, 0x00, 0x48, 0x19, 0xd2, 0x48, 0x81, 0xe2,
  0x00, 0x10, 0xf0, 0xff, 0x48, 0x81, 0xc2, 0xff, 0xff, 0x0f, 0x00]

theorem p6_0 : ∀ feat, Dec feat p6 0 (FV7z.mk .cmp 32 [gr 32 0, Src.opd 32 (.i 4194304)] 5) := by dec_rfl
theorem p6_5 : ∀ feat, Dec feat p6 5 (FV7z.mk .sbb 64 [gr 64 3, Src.opd 64 (.r 3)] 3) := by dec_rfl
theorem p6_8 : ∀ feat, Dec feat p6 8 (FV7z.mk .and 32 [gr 32 3, Src.opd 32 (.i 1044480)] 6) := by dec_rfl
theorem p6_14 : ∀ feat, Dec feat p6 14 (FV7z.mk .sub 64 [gr 64 3, Src.opd 64 (.i 1048576)] 7) := by dec_rfl
theorem p6_21 : ∀ feat, Dec feat p6 21 (FV7z.mk .cmp 32 [gr 32 0, Src.opd 32 (.i 4194304)] 5) := by dec_rfl
theorem p6_26 : ∀ feat, Dec feat p6 26 (FV7z.mk .sbb 64 [gr 64 2, Src.opd 64 (.r 2)] 3) := by dec_rfl
theorem p6_29 : ∀ feat, Dec feat p6 29 (FV7z.mk .and 64 [gr 64 2, Src.opd 64 (.i 18446744073708507136)] 7) := by dec_rfl
theorem p6_36 : ∀ feat, Dec feat p6 36 (FV7z.mk .add 64 [gr 64 2, Src.opd 64 (.i 1048575)] 7) := by dec_rfl

/-- What the stretch does. -/
def o6 : List Op := [
  Op.cmp 32 0 (.i 4194304),
  Op.sbb 64 3 (.r 3),
  Op.and 32 3 (.i 1044480),
  Op.sub 64 3 (.i 1048576),
  Op.cmp 32 0 (.i 4194304),
  Op.sbb 64 2 (.r 2),
  Op.and 64 2 (.i 18446744073708507136),
  Op.add 64 2 (.i 1048575)]

theorem b6 (prof : Profile) : Blk prof p6 0 43 o6 :=
  .cons (p6_0 _) (OpI.cmp (.i 4194304) (.inl rfl)) (by decide) <|
  .cons (p6_5 _) (OpI.sbb (.r 3) (.inr rfl)) (by decide) <|
  .cons (p6_8 _) (OpI.and (.i 1044480) (.inl rfl)) (by decide) <|
  .cons (p6_14 _) (OpI.sub (.i 1048576) (.inr rfl)) (by decide) <|
  .cons (p6_21 _) (OpI.cmp (.i 4194304) (.inl rfl)) (by decide) <|
  .cons (p6_26 _) (OpI.sbb (.r 2) (.inr rfl)) (by decide) <|
  .cons (p6_29 _) (OpI.and (.i 18446744073708507136) (.inr rfl)) (by decide) <|
  .cons (p6_36 _) (OpI.add (.i 1048575) (.inr rfl)) (by decide) <|
  .nil 43

/-- The stretch at `173`. -/
def p7 : List Byte := [
  0x48, 0x01, 0xc2, 0x48, 0x8b, 0x75, 0x18, 0x48, 0x21, 0xda, 0x48, 0x39, 0xd0, 0x48, 0x89, 0xd3,
  0x48, 0x0f, 0x43, 0xd8, 0x48, 0x85, 0xf6]

theorem p7_0 : ∀ feat, Dec feat p7 0 (FV7z.mk .add 64 [gr 64 2, Src.opd 64 (.r 0)] 3) := by dec_rfl
theorem p7_3 : ∀ feat, Dec feat p7 3 (FV7z.mk .mov 64 [gr 64 6, .mem (mg (some 5) none 1 24 64)] 4) := by dec_rfl
theorem p7_7 : ∀ feat, Dec feat p7 7 (FV7z.mk .and 64 [gr 64 2, Src.opd 64 (.r 3)] 3) := by dec_rfl
theorem p7_10 : ∀ feat, Dec feat p7 10 (FV7z.mk .cmp 64 [gr 64 0, Src.opd 64 (.r 2)] 3) := by dec_rfl
theorem p7_13 : ∀ feat, Dec feat p7 13 (FV7z.mk .mov 64 [gr 64 3, Src.opd 64 (.r 2)] 3) := by dec_rfl
theorem p7_16 : ∀ feat, Dec feat p7 16 (FV7z.mk (.cmovcc 3) 64 [gr 64 3, gr 64 0] 4) := by dec_rfl
theorem p7_20 : ∀ feat, Dec feat p7 20 (FV7z.mk .test 64 [gr 64 6, Src.opd 64 (.r 6)] 3) := by dec_rfl

/-- What the stretch does. -/
def o7 : List Op := [
  Op.add 64 2 (.r 0),
  Op.ld 64 6 (some 5) none 1 24,
  Op.and 64 2 (.r 3),
  Op.cmp 64 0 (.r 2),
  Op.mov 64 3 (.r 2),
  Op.cmov64 3 3 0,
  Op.test 64 6 (.r 6)]

theorem b7 (prof : Profile) : Blk prof p7 0 23 o7 :=
  .cons (p7_0 _) (OpI.add (.r 0) (.inr rfl)) (by decide) <|
  .cons (p7_3 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p7_7 _) (OpI.and (.r 3) (.inr rfl)) (by decide) <|
  .cons (p7_10 _) (OpI.cmp (.r 2) (.inr rfl)) (by decide) <|
  .cons (p7_13 _) (OpI.mov (.r 2) (.inr rfl)) (by decide) <|
  .cons (p7_16 _) (OpI.cmov64) (by decide) <|
  .cons (p7_20 _) (OpI.test (.r 6) (.inr rfl)) (by decide) <|
  .nil 23

def j4 : List Byte := [0x74, 0x06]
theorem j4_0 : ∀ feat, Dec feat j4 0 (FV7z.mk (.jcc 4) 64 [.rel 6] 2) := by dec_rfl

/-- The stretch at `198`. -/
def p8 : List Byte := [
  0x48, 0x39, 0x5d, 0x20]

theorem p8_0 : ∀ feat, Dec feat p8 0 (FV7z.mk .cmp 64 [.mem (mg (some 5) none 1 32 64), gr 64 3] 4) := by dec_rfl

/-- What the stretch does. -/
def o8 : List Op := [
  Op.cmpmr 64 (some 5) none 1 32 3]

theorem b8 (prof : Profile) : Blk prof p8 0 4 o8 :=
  .cons (p8_0 _) (OpI.cmpmr (.inr rfl)) (by decide) <|
  .nil 4

def j5 : List Byte := [0x74, 0x22]
theorem j5_0 : ∀ feat, Dec feat j5 0 (FV7z.mk (.jcc 4) 64 [.rel 34] 2) := by dec_rfl

/-- The stretch at `204`. -/
def p9 : List Byte := [
  0x4c, 0x89, 0xef]

theorem p9_0 : ∀ feat, Dec feat p9 0 (FV7z.mk .mov 64 [gr 64 7, Src.opd 64 (.r 13)] 3) := by dec_rfl

/-- What the stretch does. -/
def o9 : List Op := [
  Op.mov 64 7 (.r 13)]

theorem b9 (prof : Profile) : Blk prof p9 0 3 o9 :=
  .cons (p9_0 _) (OpI.mov (.r 13) (.inr rfl)) (by decide) <|
  .nil 3

/-- The stretch at `211`. -/
def p10 : List Byte := [
  0x48, 0xc7, 0x45, 0x18, 0x00, 0x00, 0x00, 0x00, 0x48, 0x89, 0xde, 0x4c, 0x89, 0xef]

theorem p10_0 : ∀ feat, Dec feat p10 0 (FV7z.mk .mov 64 [.mem (mg (some 5) none 1 24 64), .imm 64 0] 8) := by dec_rfl
theorem p10_8 : ∀ feat, Dec feat p10 8 (FV7z.mk .mov 64 [gr 64 6, Src.opd 64 (.r 3)] 3) := by dec_rfl
theorem p10_11 : ∀ feat, Dec feat p10 11 (FV7z.mk .mov 64 [gr 64 7, Src.opd 64 (.r 13)] 3) := by dec_rfl

/-- What the stretch does. -/
def o10 : List Op := [
  Op.sti 64 (some 5) none 1 24 0,
  Op.mov 64 6 (.r 3),
  Op.mov 64 7 (.r 13)]

theorem b10 (prof : Profile) : Blk prof p10 0 14 o10 :=
  .cons (p10_0 _) (OpI.sti (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p10_8 _) (OpI.mov (.r 3) (.inr rfl)) (by decide) <|
  .cons (p10_11 _) (OpI.mov (.r 13) (.inr rfl)) (by decide) <|
  .nil 14

/-- The stretch at `229`. -/
def p11 : List Byte := [
  0x48, 0x89, 0x45, 0x18, 0x48, 0x85, 0xc0]

theorem p11_0 : ∀ feat, Dec feat p11 0 (FV7z.mk .mov 64 [.mem (mg (some 5) none 1 24 64), gr 64 0] 4) := by dec_rfl
theorem p11_4 : ∀ feat, Dec feat p11 4 (FV7z.mk .test 64 [gr 64 0, Src.opd 64 (.r 0)] 3) := by dec_rfl

/-- What the stretch does. -/
def o11 : List Op := [
  Op.st 64 (some 5) none 1 24 0,
  Op.test 64 0 (.r 0)]

theorem b11 (prof : Profile) : Blk prof p11 0 7 o11 :=
  .cons (p11_0 _) (OpI.st (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p11_4 _) (OpI.test (.r 0) (.inr rfl)) (by decide) <|
  .nil 7

/-- The stretch at `238`. -/
def p12 : List Byte := [
  0x48, 0x8b, 0x04, 0x24, 0x48, 0x89, 0x5d, 0x20, 0x48, 0x89, 0x45, 0x00]

theorem p12_0 : ∀ feat, Dec feat p12 0 (FV7z.mk .mov 64 [gr 64 0, .mem (mg (some 4) none 1 0 64)] 4) := by dec_rfl
theorem p12_4 : ∀ feat, Dec feat p12 4 (FV7z.mk .mov 64 [.mem (mg (some 5) none 1 32 64), gr 64 3] 4) := by dec_rfl
theorem p12_8 : ∀ feat, Dec feat p12 8 (FV7z.mk .mov 64 [.mem (mg (some 5) none 1 0 64), gr 64 0] 4) := by dec_rfl

/-- What the stretch does. -/
def o12 : List Op := [
  Op.ld 64 0 (some 4) none 1 0,
  Op.st 64 (some 5) none 1 32 3,
  Op.st 64 (some 5) none 1 0 0]

theorem b12 (prof : Profile) : Blk prof p12 0 12 o12 :=
  .cons (p12_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p12_4 _) (OpI.st (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p12_8 _) (OpI.st (.inr (.inr (.inr rfl)))) (by decide) <|
  .nil 12

def j6 : List Byte := [0xe9, 0x34, 0xff, 0xff, 0xff]
theorem j6_0 : ∀ feat, Dec feat j6 0 (FV7z.mk .jmp 64 [.rel 18446744073709551412] 5) := by dec_rfl

/-- The stretch at `256`. -/
def p13 : List Byte := [
  0x48, 0xc7, 0xc3, 0x00, 0x00, 0xc0, 0xff, 0xba, 0xff, 0xff, 0x3f, 0x00]

theorem p13_0 : ∀ feat, Dec feat p13 0 (FV7z.mk .mov 64 [gr 64 3, Src.opd 64 (.i 18446744073705357312)] 7) := by dec_rfl
theorem p13_7 : ∀ feat, Dec feat p13 7 (FV7z.mk .mov 32 [gr 32 2, Src.opd 32 (.i 4194303)] 5) := by dec_rfl

/-- What the stretch does. -/
def o13 : List Op := [
  Op.mov 64 3 (.i 18446744073705357312),
  Op.mov 32 2 (.i 4194303)]

theorem b13 (prof : Profile) : Blk prof p13 0 12 o13 :=
  .cons (p13_0 _) (OpI.mov (.i 18446744073705357312) (.inr rfl)) (by decide) <|
  .cons (p13_7 _) (OpI.mov (.i 4194303) (.inl rfl)) (by decide) <|
  .nil 12

def j7 : List Byte := [0xeb, 0x9f]
theorem j7_0 : ∀ feat, Dec feat j7 0 (FV7z.mk .jmp 64 [.rel 18446744073709551519] 2) := by dec_rfl

/-- The stretch at `272`. -/
def p14 : List Byte := [
  0x4c, 0x89, 0xee, 0x48, 0x89, 0xef, 0x41, 0xbc, 0x02, 0x00, 0x00, 0x00]

theorem p14_0 : ∀ feat, Dec feat p14 0 (FV7z.mk .mov 64 [gr 64 6, Src.opd 64 (.r 13)] 3) := by dec_rfl
theorem p14_3 : ∀ feat, Dec feat p14 3 (FV7z.mk .mov 64 [gr 64 7, Src.opd 64 (.r 5)] 3) := by dec_rfl
theorem p14_6 : ∀ feat, Dec feat p14 6 (FV7z.mk .mov 32 [gr 32 12, Src.opd 32 (.i 2)] 6) := by dec_rfl

/-- What the stretch does. -/
def o14 : List Op := [
  Op.mov 64 6 (.r 13),
  Op.mov 64 7 (.r 5),
  Op.mov 32 12 (.i 2)]

theorem b14 (prof : Profile) : Blk prof p14 0 12 o14 :=
  .cons (p14_0 _) (OpI.mov (.r 13) (.inr rfl)) (by decide) <|
  .cons (p14_3 _) (OpI.mov (.r 5) (.inr rfl)) (by decide) <|
  .cons (p14_6 _) (OpI.mov (.i 2) (.inl rfl)) (by decide) <|
  .nil 12

def j8 : List Byte := [0xe9, 0x0d, 0xff, 0xff, 0xff]
theorem j8_0 : ∀ feat, Dec feat j8 0 (FV7z.mk .jmp 64 [.rel 18446744073709551373] 5) := by dec_rfl

end FV7z.Lza
