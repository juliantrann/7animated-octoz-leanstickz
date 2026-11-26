import FV7z.Lemmas.SpFs
import FV7z.Lemmas.BlkOps6
import FV7z.Lemmas.BlkOps4
/-!
# The stretches of straight-line code of `ConvertUInt32ToString` (PLAN.md §M, M1)

Each distinct stretch between labels and jumps (`p*`, 10 of them) and each distinct jump (`j*`, 6) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.U2s
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The stretch at `0`. -/
def p0 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0x48, 0x83, 0xec, 0x28, 0x4c, 0x8d, 0x56, 0x01, 0x64, 0x48, 0x8b, 0x04,
  0x25, 0x28, 0x00, 0x00, 0x00, 0x48, 0x89, 0x44, 0x24, 0x18, 0x31, 0xc0, 0x83, 0xff, 0x09]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem p0_4 : ∀ feat, Dec feat p0 4 (FV7z.mk .sub 64 [gr 64 4, Src.opd 64 (.i 40)] 4) := by dec_rfl
theorem p0_8 : ∀ feat, Dec feat p0 8 (FV7z.mk .lea 64 [gr 64 10, .mem (mg (some 6) none 1 1 0)] 4) := by dec_rfl
theorem p0_12 : ∀ feat, Dec feat p0 12 (FV7z.mk .mov 64 [gr 64 0, .mem (mf none none 1 40 64)] 9) := by dec_rfl
theorem p0_21 : ∀ feat, Dec feat p0 21 (FV7z.mk .mov 64 [.mem (mg (some 4) none 1 24 64), gr 64 0] 5) := by dec_rfl
theorem p0_26 : ∀ feat, Dec feat p0 26 (FV7z.mk .xor 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl
theorem p0_28 : ∀ feat, Dec feat p0 28 (FV7z.mk .cmp 32 [gr 32 7, Src.opd 32 (.i 9)] 3) := by dec_rfl

/-- What the stretch does. -/
def o0 (fb : Addr) : List Op := [
  Op.nop,
  Op.sub 64 4 (.i 40),
  Op.lea 64 10 (some 6) none 1 1,
  Op.ldf fb 64 0 none none 1 40,
  Op.st 64 (some 4) none 1 24 0,
  Op.xor 32 0 (.r 0),
  Op.cmp 32 7 (.i 9)]

theorem b0 (prof : Profile) (fb : Addr) : BlkF prof p0 (0x44ab70 : Addr) fb 0 31 (o0 fb) :=
  .cons (p0_0 _) (((OpI.endbr).at _).fs _) (by decide) <|
  .cons (p0_4 _) (((OpI.sub (.i 40) (.inr rfl)).at _).fs _) (by decide) <|
  .cons (p0_8 _) (((OpI.lea (.inr rfl)).at _).fs _) (by decide) <|
  .cons (p0_12 _) (OpIF.ldf (.inr rfl)) (by decide) <|
  .cons (p0_21 _) (((OpI.st (.inr (.inr (.inr rfl)))).at _).fs _) (by decide) <|
  .cons (p0_26 _) (((OpI.xor (.r 0) (.inl rfl)).at _).fs _) (by decide) <|
  .cons (p0_28 _) (((OpI.cmp (.i 9) (.inl rfl)).at _).fs _) (by decide) <|
  .nil 31

def j0 : List Byte := [0x77, 0x27]
theorem j0_0 : ∀ feat, Dec feat j0 0 (FV7z.mk (.jcc 7) 64 [.rel 39] 2) := by dec_rfl

/-- The stretch at `33`. -/
def p1 : List Byte := [
  0x83, 0xc7, 0x30, 0x40, 0x88, 0x3e]

theorem p1_0 : ∀ feat, Dec feat p1 0 (FV7z.mk .add 32 [gr 32 7, Src.opd 32 (.i 48)] 3) := by dec_rfl
theorem p1_3 : ∀ feat, Dec feat p1 3 (FV7z.mk .mov 8 [.mem (mg (some 6) none 1 0 8), gr 8 7] 3) := by dec_rfl

/-- What the stretch does. -/
def o1 : List Op := [
  Op.add 32 7 (.i 48),
  Op.st 8 (some 6) none 1 0 7]

theorem b1 (prof : Profile) : Blk prof p1 0 6 o1 :=
  .cons (p1_0 _) (OpI.add (.i 48) (.inl rfl)) (by decide) <|
  .cons (p1_3 _) (OpI.st (.inl rfl)) (by decide) <|
  .nil 6

/-- The stretch at `39`. -/
def p2 : List Byte := [
  0x41, 0xc6, 0x02, 0x00, 0x48, 0x8b, 0x44, 0x24, 0x18, 0x64, 0x48, 0x33, 0x04, 0x25, 0x28, 0x00,
  0x00, 0x00]

theorem p2_0 : ∀ feat, Dec feat p2 0 (FV7z.mk .mov 8 [.mem (mg (some 10) none 1 0 8), .imm 8 0] 4) := by dec_rfl
theorem p2_4 : ∀ feat, Dec feat p2 4 (FV7z.mk .mov 64 [gr 64 0, .mem (mg (some 4) none 1 24 64)] 5) := by dec_rfl
theorem p2_9 : ∀ feat, Dec feat p2 9 (FV7z.mk .xor 64 [gr 64 0, .mem (mf none none 1 40 64)] 9) := by dec_rfl

/-- What the stretch does. -/
def o2 (fb : Addr) : List Op := [
  Op.sti 8 (some 10) none 1 0 0,
  Op.ld 64 0 (some 4) none 1 24,
  Op.xormf fb 64 0 none none 1 40]

theorem b2 (prof : Profile) (fb : Addr) : BlkF prof p2 (0x44ab97 : Addr) fb 0 18 (o2 fb) :=
  .cons (p2_0 _) (((OpI.sti (.inl rfl)).at _).fs _) (by decide) <|
  .cons (p2_4 _) (((OpI.ld (.inr rfl)).at _).fs _) (by decide) <|
  .cons (p2_9 _) (OpIF.xormf (.inr rfl)) (by decide) <|
  .nil 18

def j1 : List Byte := [0x75, 0x77]
theorem j1_0 : ∀ feat, Dec feat j1 0 (FV7z.mk (.jcc 5) 64 [.rel 119] 2) := by dec_rfl

/-- The stretch at `59`. -/
def p3 : List Byte := [
  0x4c, 0x89, 0xd0, 0x48, 0x83, 0xc4, 0x28]

theorem p3_0 : ∀ feat, Dec feat p3 0 (FV7z.mk .mov 64 [gr 64 0, Src.opd 64 (.r 10)] 3) := by dec_rfl
theorem p3_3 : ∀ feat, Dec feat p3 3 (FV7z.mk .add 64 [gr 64 4, Src.opd 64 (.i 40)] 4) := by dec_rfl

/-- What the stretch does. -/
def o3 : List Op := [
  Op.mov 64 0 (.r 10),
  Op.add 64 4 (.i 40)]

theorem b3 (prof : Profile) : Blk prof p3 0 7 o3 :=
  .cons (p3_0 _) (OpI.mov (.r 10) (.inr rfl)) (by decide) <|
  .cons (p3_3 _) (OpI.add (.i 40) (.inr rfl)) (by decide) <|
  .nil 7

/-- The stretch at `72`. -/
def p4 : List Byte := [
  0x31, 0xc9, 0x49, 0x89, 0xe0, 0x41, 0xbb, 0xcd, 0xcc, 0xcc, 0xcc, 0x0f, 0x1f, 0x44, 0x00, 0x00]

theorem p4_0 : ∀ feat, Dec feat p4 0 (FV7z.mk .xor 32 [gr 32 1, Src.opd 32 (.r 1)] 2) := by dec_rfl
theorem p4_2 : ∀ feat, Dec feat p4 2 (FV7z.mk .mov 64 [gr 64 8, Src.opd 64 (.r 4)] 3) := by dec_rfl
theorem p4_5 : ∀ feat, Dec feat p4 5 (FV7z.mk .mov 32 [gr 32 11, Src.opd 32 (.i 3435973837)] 6) := by dec_rfl
theorem p4_11 : ∀ feat, Dec feat p4 11 (FV7z.mk .nop 32 [.mem (mg (some 0) (some 0) 1 0 32)] 5) := by dec_rfl

/-- What the stretch does. -/
def o4 : List Op := [
  Op.xor 32 1 (.r 1),
  Op.mov 64 8 (.r 4),
  Op.mov 32 11 (.i 3435973837),
  Op.nop]

theorem b4 (prof : Profile) : Blk prof p4 0 16 o4 :=
  .cons (p4_0 _) (OpI.xor (.r 1) (.inl rfl)) (by decide) <|
  .cons (p4_2 _) (OpI.mov (.r 4) (.inr rfl)) (by decide) <|
  .cons (p4_5 _) (OpI.mov (.i 3435973837) (.inl rfl)) (by decide) <|
  .cons (p4_11 _) (OpI.nop) (by decide) <|
  .nil 16

/-- The stretch at `88`. -/
def p5 : List Byte := [
  0x89, 0xf8, 0x41, 0x89, 0xf9, 0x48, 0x83, 0xc1, 0x01, 0x49, 0x0f, 0xaf, 0xc3, 0x48, 0xc1, 0xe8,
  0x23, 0x8d, 0x14, 0x80, 0x01, 0xd2, 0x41, 0x29, 0xd1, 0x44, 0x89, 0xca, 0x41, 0x89, 0xf9, 0x89,
  0xc7, 0x83, 0xc2, 0x30, 0x41, 0x88, 0x14, 0x08, 0x41, 0x83, 0xf9, 0x63]

theorem p5_0 : ∀ feat, Dec feat p5 0 (FV7z.mk .mov 32 [gr 32 0, Src.opd 32 (.r 7)] 2) := by dec_rfl
theorem p5_2 : ∀ feat, Dec feat p5 2 (FV7z.mk .mov 32 [gr 32 9, Src.opd 32 (.r 7)] 3) := by dec_rfl
theorem p5_5 : ∀ feat, Dec feat p5 5 (FV7z.mk .add 64 [gr 64 1, Src.opd 64 (.i 1)] 4) := by dec_rfl
theorem p5_9 : ∀ feat, Dec feat p5 9 (FV7z.mk .imul 64 [gr 64 0, gr 64 11] 4) := by dec_rfl
theorem p5_13 : ∀ feat, Dec feat p5 13 (FV7z.mk .shr 64 [gr 64 0, Src.opd 8 (.i 35)] 4) := by dec_rfl
theorem p5_17 : ∀ feat, Dec feat p5 17 (FV7z.mk .lea 32 [gr 32 2, .mem (mg (some 0) (some 0) 4 0 0)] 3) := by dec_rfl
theorem p5_20 : ∀ feat, Dec feat p5 20 (FV7z.mk .add 32 [gr 32 2, Src.opd 32 (.r 2)] 2) := by dec_rfl
theorem p5_22 : ∀ feat, Dec feat p5 22 (FV7z.mk .sub 32 [gr 32 9, Src.opd 32 (.r 2)] 3) := by dec_rfl
theorem p5_25 : ∀ feat, Dec feat p5 25 (FV7z.mk .mov 32 [gr 32 2, Src.opd 32 (.r 9)] 3) := by dec_rfl
theorem p5_28 : ∀ feat, Dec feat p5 28 (FV7z.mk .mov 32 [gr 32 9, Src.opd 32 (.r 7)] 3) := by dec_rfl
theorem p5_31 : ∀ feat, Dec feat p5 31 (FV7z.mk .mov 32 [gr 32 7, Src.opd 32 (.r 0)] 2) := by dec_rfl
theorem p5_33 : ∀ feat, Dec feat p5 33 (FV7z.mk .add 32 [gr 32 2, Src.opd 32 (.i 48)] 3) := by dec_rfl
theorem p5_36 : ∀ feat, Dec feat p5 36 (FV7z.mk .mov 8 [.mem (mg (some 8) (some 1) 1 0 8), gr 8 2] 4) := by dec_rfl
theorem p5_40 : ∀ feat, Dec feat p5 40 (FV7z.mk .cmp 32 [gr 32 9, Src.opd 32 (.i 99)] 4) := by dec_rfl

/-- What the stretch does. -/
def o5 : List Op := [
  Op.mov 32 0 (.r 7),
  Op.mov 32 9 (.r 7),
  Op.add 64 1 (.i 1),
  Op.imul64 0 11,
  Op.shr64 0 (.i 35),
  Op.lea 32 2 (some 0) (some 0) 4 0,
  Op.add 32 2 (.r 2),
  Op.sub 32 9 (.r 2),
  Op.mov 32 2 (.r 9),
  Op.mov 32 9 (.r 7),
  Op.mov 32 7 (.r 0),
  Op.add 32 2 (.i 48),
  Op.st 8 (some 8) (some 1) 1 0 2,
  Op.cmp 32 9 (.i 99)]

theorem b5 (prof : Profile) : Blk prof p5 0 44 o5 :=
  .cons (p5_0 _) (OpI.mov (.r 7) (.inl rfl)) (by decide) <|
  .cons (p5_2 _) (OpI.mov (.r 7) (.inl rfl)) (by decide) <|
  .cons (p5_5 _) (OpI.add (.i 1) (.inr rfl)) (by decide) <|
  .cons (p5_9 _) (OpI.imul64) (by decide) <|
  .cons (p5_13 _) (OpI.shr64 (.i 35)) (by decide) <|
  .cons (p5_17 _) (OpI.lea (.inl rfl)) (by decide) <|
  .cons (p5_20 _) (OpI.add (.r 2) (.inl rfl)) (by decide) <|
  .cons (p5_22 _) (OpI.sub (.r 2) (.inl rfl)) (by decide) <|
  .cons (p5_25 _) (OpI.mov (.r 9) (.inl rfl)) (by decide) <|
  .cons (p5_28 _) (OpI.mov (.r 7) (.inl rfl)) (by decide) <|
  .cons (p5_31 _) (OpI.mov (.r 0) (.inl rfl)) (by decide) <|
  .cons (p5_33 _) (OpI.add (.i 48) (.inl rfl)) (by decide) <|
  .cons (p5_36 _) (OpI.st (.inl rfl)) (by decide) <|
  .cons (p5_40 _) (OpI.cmp (.i 99) (.inl rfl)) (by decide) <|
  .nil 44

def j2 : List Byte := [0x77, 0xd2]
theorem j2_0 : ∀ feat, Dec feat j2 0 (FV7z.mk (.jcc 7) 64 [.rel 18446744073709551570] 2) := by dec_rfl

/-- The stretch at `134`. -/
def p6 : List Byte := [
  0x83, 0xc7, 0x30, 0x49, 0x8d, 0x04, 0x08, 0x40, 0x88, 0x3e, 0x4c, 0x89, 0xd6]

theorem p6_0 : ∀ feat, Dec feat p6 0 (FV7z.mk .add 32 [gr 32 7, Src.opd 32 (.i 48)] 3) := by dec_rfl
theorem p6_3 : ∀ feat, Dec feat p6 3 (FV7z.mk .lea 64 [gr 64 0, .mem (mg (some 8) (some 1) 1 0 0)] 4) := by dec_rfl
theorem p6_7 : ∀ feat, Dec feat p6 7 (FV7z.mk .mov 8 [.mem (mg (some 6) none 1 0 8), gr 8 7] 3) := by dec_rfl
theorem p6_10 : ∀ feat, Dec feat p6 10 (FV7z.mk .mov 64 [gr 64 6, Src.opd 64 (.r 10)] 3) := by dec_rfl

/-- What the stretch does. -/
def o6 : List Op := [
  Op.add 32 7 (.i 48),
  Op.lea 64 0 (some 8) (some 1) 1 0,
  Op.st 8 (some 6) none 1 0 7,
  Op.mov 64 6 (.r 10)]

theorem b6 (prof : Profile) : Blk prof p6 0 13 o6 :=
  .cons (p6_0 _) (OpI.add (.i 48) (.inl rfl)) (by decide) <|
  .cons (p6_3 _) (OpI.lea (.inr rfl)) (by decide) <|
  .cons (p6_7 _) (OpI.st (.inl rfl)) (by decide) <|
  .cons (p6_10 _) (OpI.mov (.r 10) (.inr rfl)) (by decide) <|
  .nil 13

def j3 : List Byte := [0xeb, 0x06]
theorem j3_0 : ∀ feat, Dec feat j3 0 (FV7z.mk .jmp 64 [.rel 6] 2) := by dec_rfl

/-- The stretch at `152`. -/
def p7 : List Byte := [
  0x0f, 0xb6, 0x10]

theorem p7_0 : ∀ feat, Dec feat p7 0 (FV7z.mk .movzx 32 [gr 32 2, .mem (mg (some 0) none 1 0 8)] 3) := by dec_rfl

/-- What the stretch does. -/
def o7 : List Op := [
  Op.ldzx 8 2 (some 0) none 1 0]

theorem b7 (prof : Profile) : Blk prof p7 0 3 o7 :=
  .cons (p7_0 _) (OpI.ldzx (.inl rfl)) (by decide) <|
  .nil 3

/-- The stretch at `155`. -/
def p8 : List Byte := [
  0x48, 0x83, 0xe8, 0x01, 0x88, 0x16, 0x48, 0x83, 0xc6, 0x01, 0x4c, 0x39, 0xc0]

theorem p8_0 : ∀ feat, Dec feat p8 0 (FV7z.mk .sub 64 [gr 64 0, Src.opd 64 (.i 1)] 4) := by dec_rfl
theorem p8_4 : ∀ feat, Dec feat p8 4 (FV7z.mk .mov 8 [.mem (mg (some 6) none 1 0 8), gr 8 2] 2) := by dec_rfl
theorem p8_6 : ∀ feat, Dec feat p8 6 (FV7z.mk .add 64 [gr 64 6, Src.opd 64 (.i 1)] 4) := by dec_rfl
theorem p8_10 : ∀ feat, Dec feat p8 10 (FV7z.mk .cmp 64 [gr 64 0, Src.opd 64 (.r 8)] 3) := by dec_rfl

/-- What the stretch does. -/
def o8 : List Op := [
  Op.sub 64 0 (.i 1),
  Op.st 8 (some 6) none 1 0 2,
  Op.add 64 6 (.i 1),
  Op.cmp 64 0 (.r 8)]

theorem b8 (prof : Profile) : Blk prof p8 0 13 o8 :=
  .cons (p8_0 _) (OpI.sub (.i 1) (.inr rfl)) (by decide) <|
  .cons (p8_4 _) (OpI.st (.inl rfl)) (by decide) <|
  .cons (p8_6 _) (OpI.add (.i 1) (.inr rfl)) (by decide) <|
  .cons (p8_10 _) (OpI.cmp (.r 8) (.inr rfl)) (by decide) <|
  .nil 13

def j4 : List Byte := [0x75, 0xee]
theorem j4_0 : ∀ feat, Dec feat j4 0 (FV7z.mk (.jcc 5) 64 [.rel 18446744073709551598] 2) := by dec_rfl

/-- The stretch at `170`. -/
def p9 : List Byte := [
  0x49, 0x01, 0xca]

theorem p9_0 : ∀ feat, Dec feat p9 0 (FV7z.mk .add 64 [gr 64 10, Src.opd 64 (.r 1)] 3) := by dec_rfl

/-- What the stretch does. -/
def o9 : List Op := [
  Op.add 64 10 (.r 1)]

theorem b9 (prof : Profile) : Blk prof p9 0 3 o9 :=
  .cons (p9_0 _) (OpI.add (.r 1) (.inr rfl)) (by decide) <|
  .nil 3

def j5 : List Byte := [0xe9, 0x75, 0xff, 0xff, 0xff]
theorem j5_0 : ∀ feat, Dec feat j5 0 (FV7z.mk .jmp 64 [.rel 18446744073709551477] 5) := by dec_rfl

end FV7z.U2s
