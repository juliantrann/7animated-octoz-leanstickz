import FV7z.Lemmas.SpFs
import FV7z.Lemmas.BlkOps17
import FV7z.Lemmas.BlkOps6
import FV7z.Lemmas.BlkOps3
/-!
# The stretches of straight-line code of `ConvertUInt64ToString` (PLAN.md §M, M1)

Each distinct stretch between labels and jumps (`p*`, 9 of them) and each distinct jump (`j*`, 6) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.C64
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The stretch at `0`. -/
def p0 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0x48, 0x83, 0xec, 0x28, 0x45, 0x31, 0xc0, 0x49, 0xba, 0xcd, 0xcc, 0xcc,
  0xcc, 0xcc, 0xcc, 0xcc, 0xcc, 0x64, 0x48, 0x8b, 0x04, 0x25, 0x28, 0x00, 0x00, 0x00, 0x48, 0x89,
  0x44, 0x24, 0x18, 0x31, 0xc0, 0xb8, 0xff, 0xff, 0xff, 0xff, 0x49, 0x89, 0xe1, 0x48, 0x39, 0xc7]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem p0_4 : ∀ feat, Dec feat p0 4 (FV7z.mk .sub 64 [gr 64 4, Src.opd 64 (.i 40)] 4) := by dec_rfl
theorem p0_8 : ∀ feat, Dec feat p0 8 (FV7z.mk .xor 32 [gr 32 8, Src.opd 32 (.r 8)] 3) := by dec_rfl
theorem p0_11 : ∀ feat, Dec feat p0 11 (FV7z.mk .mov 64 [gr 64 10, Src.opd 64 (.i 14757395258967641293)] 10) := by dec_rfl
theorem p0_21 : ∀ feat, Dec feat p0 21 (FV7z.mk .mov 64 [gr 64 0, .mem (mf none none 1 40 64)] 9) := by dec_rfl
theorem p0_30 : ∀ feat, Dec feat p0 30 (FV7z.mk .mov 64 [.mem (mg (some 4) none 1 24 64), gr 64 0] 5) := by dec_rfl
theorem p0_35 : ∀ feat, Dec feat p0 35 (FV7z.mk .xor 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl
theorem p0_37 : ∀ feat, Dec feat p0 37 (FV7z.mk .mov 32 [gr 32 0, Src.opd 32 (.i 4294967295)] 5) := by dec_rfl
theorem p0_42 : ∀ feat, Dec feat p0 42 (FV7z.mk .mov 64 [gr 64 9, Src.opd 64 (.r 4)] 3) := by dec_rfl
theorem p0_45 : ∀ feat, Dec feat p0 45 (FV7z.mk .cmp 64 [gr 64 7, Src.opd 64 (.r 0)] 3) := by dec_rfl

/-- What the stretch does. -/
def o0 (fb : Addr) : List Op := [
  Op.nop,
  Op.sub 64 4 (.i 40),
  Op.xor 32 8 (.r 8),
  Op.mov 64 10 (.i 14757395258967641293),
  Op.ldf fb 64 0 none none 1 40,
  Op.st 64 (some 4) none 1 24 0,
  Op.xor 32 0 (.r 0),
  Op.mov 32 0 (.i 4294967295),
  Op.mov 64 9 (.r 4),
  Op.cmp 64 7 (.r 0)]

theorem b0 (prof : Profile) (fb : Addr) : BlkF prof p0 (0x44ac30 : Addr) fb 0 48 (o0 fb) :=
  .cons (p0_0 _) (((OpI.endbr).at _).fs _) (by decide) <|
  .cons (p0_4 _) (((OpI.sub (.i 40) (.inr rfl)).at _).fs _) (by decide) <|
  .cons (p0_8 _) (((OpI.xor (.r 8) (.inl rfl)).at _).fs _) (by decide) <|
  .cons (p0_11 _) (((OpI.mov (.i 14757395258967641293) (.inr rfl)).at _).fs _) (by decide) <|
  .cons (p0_21 _) (OpIF.ldf (.inr rfl)) (by decide) <|
  .cons (p0_30 _) (((OpI.st (.inr (.inr (.inr rfl)))).at _).fs _) (by decide) <|
  .cons (p0_35 _) (((OpI.xor (.r 0) (.inl rfl)).at _).fs _) (by decide) <|
  .cons (p0_37 _) (((OpI.mov (.i 4294967295) (.inl rfl)).at _).fs _) (by decide) <|
  .cons (p0_42 _) (((OpI.mov (.r 4) (.inr rfl)).at _).fs _) (by decide) <|
  .cons (p0_45 _) (((OpI.cmp (.r 0) (.inr rfl)).at _).fs _) (by decide) <|
  .nil 48

def j0 : List Byte := [0x76, 0x7e]
theorem j0_0 : ∀ feat, Dec feat j0 0 (FV7z.mk (.jcc 6) 64 [.rel 126] 2) := by dec_rfl

/-- The stretch at `50`. -/
def p1 : List Byte := [
  0x66, 0x0f, 0x1f, 0x44, 0x00, 0x00]

theorem p1_0 : ∀ feat, Dec feat p1 0 (FV7z.mk .nop 16 [.mem (mg (some 0) (some 0) 1 0 16)] 6) := by dec_rfl

/-- What the stretch does. -/
def o1 : List Op := [
  Op.nop]

theorem b1 (prof : Profile) : Blk prof p1 0 6 o1 :=
  .cons (p1_0 _) (OpI.nop) (by decide) <|
  .nil 6

/-- The stretch at `56`. -/
def p2 : List Byte := [
  0x48, 0x89, 0xf8, 0x48, 0x89, 0xf9, 0x49, 0x83, 0xc0, 0x01, 0x49, 0xf7, 0xe2, 0x48, 0xc1, 0xea,
  0x03, 0x48, 0x8d, 0x04, 0x92, 0x48, 0x01, 0xc0, 0x48, 0x29, 0xc1, 0x48, 0x89, 0xf8, 0x48, 0x89,
  0xd7, 0x83, 0xc1, 0x30, 0x43, 0x88, 0x0c, 0x01, 0x48, 0x83, 0xf8, 0x63]

theorem p2_0 : ∀ feat, Dec feat p2 0 (FV7z.mk .mov 64 [gr 64 0, Src.opd 64 (.r 7)] 3) := by dec_rfl
theorem p2_3 : ∀ feat, Dec feat p2 3 (FV7z.mk .mov 64 [gr 64 1, Src.opd 64 (.r 7)] 3) := by dec_rfl
theorem p2_6 : ∀ feat, Dec feat p2 6 (FV7z.mk .add 64 [gr 64 8, Src.opd 64 (.i 1)] 4) := by dec_rfl
theorem p2_10 : ∀ feat, Dec feat p2 10 (FV7z.mk .mul 64 [gr 64 10] 3) := by dec_rfl
theorem p2_13 : ∀ feat, Dec feat p2 13 (FV7z.mk .shr 64 [gr 64 2, Src.opd 8 (.i 3)] 4) := by dec_rfl
theorem p2_17 : ∀ feat, Dec feat p2 17 (FV7z.mk .lea 64 [gr 64 0, .mem (mg (some 2) (some 2) 4 0 0)] 4) := by dec_rfl
theorem p2_21 : ∀ feat, Dec feat p2 21 (FV7z.mk .add 64 [gr 64 0, Src.opd 64 (.r 0)] 3) := by dec_rfl
theorem p2_24 : ∀ feat, Dec feat p2 24 (FV7z.mk .sub 64 [gr 64 1, Src.opd 64 (.r 0)] 3) := by dec_rfl
theorem p2_27 : ∀ feat, Dec feat p2 27 (FV7z.mk .mov 64 [gr 64 0, Src.opd 64 (.r 7)] 3) := by dec_rfl
theorem p2_30 : ∀ feat, Dec feat p2 30 (FV7z.mk .mov 64 [gr 64 7, Src.opd 64 (.r 2)] 3) := by dec_rfl
theorem p2_33 : ∀ feat, Dec feat p2 33 (FV7z.mk .add 32 [gr 32 1, Src.opd 32 (.i 48)] 3) := by dec_rfl
theorem p2_36 : ∀ feat, Dec feat p2 36 (FV7z.mk .mov 8 [.mem (mg (some 9) (some 8) 1 0 8), gr 8 1] 4) := by dec_rfl
theorem p2_40 : ∀ feat, Dec feat p2 40 (FV7z.mk .cmp 64 [gr 64 0, Src.opd 64 (.i 99)] 4) := by dec_rfl

/-- What the stretch does. -/
def o2 : List Op := [
  Op.mov 64 0 (.r 7),
  Op.mov 64 1 (.r 7),
  Op.add 64 8 (.i 1),
  Op.mul64 10,
  Op.shr64 2 (.i 3),
  Op.lea 64 0 (some 2) (some 2) 4 0,
  Op.add 64 0 (.r 0),
  Op.sub 64 1 (.r 0),
  Op.mov 64 0 (.r 7),
  Op.mov 64 7 (.r 2),
  Op.add 32 1 (.i 48),
  Op.st 8 (some 9) (some 8) 1 0 1,
  Op.cmp 64 0 (.i 99)]

theorem b2 (prof : Profile) : Blk prof p2 0 44 o2 :=
  .cons (p2_0 _) (OpI.mov (.r 7) (.inr rfl)) (by decide) <|
  .cons (p2_3 _) (OpI.mov (.r 7) (.inr rfl)) (by decide) <|
  .cons (p2_6 _) (OpI.add (.i 1) (.inr rfl)) (by decide) <|
  .cons (p2_10 _) (OpI.mul64) (by decide) <|
  .cons (p2_13 _) (OpI.shr64 (.i 3)) (by decide) <|
  .cons (p2_17 _) (OpI.lea (.inr rfl)) (by decide) <|
  .cons (p2_21 _) (OpI.add (.r 0) (.inr rfl)) (by decide) <|
  .cons (p2_24 _) (OpI.sub (.r 0) (.inr rfl)) (by decide) <|
  .cons (p2_27 _) (OpI.mov (.r 7) (.inr rfl)) (by decide) <|
  .cons (p2_30 _) (OpI.mov (.r 2) (.inr rfl)) (by decide) <|
  .cons (p2_33 _) (OpI.add (.i 48) (.inl rfl)) (by decide) <|
  .cons (p2_36 _) (OpI.st (.inl rfl)) (by decide) <|
  .cons (p2_40 _) (OpI.cmp (.i 99) (.inr rfl)) (by decide) <|
  .nil 44

def j1 : List Byte := [0x77, 0xd2]
theorem j1_0 : ∀ feat, Dec feat j1 0 (FV7z.mk (.jcc 7) 64 [.rel 18446744073709551570] 2) := by dec_rfl

/-- The stretch at `102`. -/
def p3 : List Byte := [
  0x48, 0x8d, 0x46, 0x01, 0x83, 0xc7, 0x30, 0x4b, 0x8d, 0x14, 0x01, 0x40, 0x88, 0x3e, 0x48, 0x89,
  0xc6]

theorem p3_0 : ∀ feat, Dec feat p3 0 (FV7z.mk .lea 64 [gr 64 0, .mem (mg (some 6) none 1 1 0)] 4) := by dec_rfl
theorem p3_4 : ∀ feat, Dec feat p3 4 (FV7z.mk .add 32 [gr 32 7, Src.opd 32 (.i 48)] 3) := by dec_rfl
theorem p3_7 : ∀ feat, Dec feat p3 7 (FV7z.mk .lea 64 [gr 64 2, .mem (mg (some 9) (some 8) 1 0 0)] 4) := by dec_rfl
theorem p3_11 : ∀ feat, Dec feat p3 11 (FV7z.mk .mov 8 [.mem (mg (some 6) none 1 0 8), gr 8 7] 3) := by dec_rfl
theorem p3_14 : ∀ feat, Dec feat p3 14 (FV7z.mk .mov 64 [gr 64 6, Src.opd 64 (.r 0)] 3) := by dec_rfl

/-- What the stretch does. -/
def o3 : List Op := [
  Op.lea 64 0 (some 6) none 1 1,
  Op.add 32 7 (.i 48),
  Op.lea 64 2 (some 9) (some 8) 1 0,
  Op.st 8 (some 6) none 1 0 7,
  Op.mov 64 6 (.r 0)]

theorem b3 (prof : Profile) : Blk prof p3 0 17 o3 :=
  .cons (p3_0 _) (OpI.lea (.inr rfl)) (by decide) <|
  .cons (p3_4 _) (OpI.add (.i 48) (.inl rfl)) (by decide) <|
  .cons (p3_7 _) (OpI.lea (.inr rfl)) (by decide) <|
  .cons (p3_11 _) (OpI.st (.inl rfl)) (by decide) <|
  .cons (p3_14 _) (OpI.mov (.r 0) (.inr rfl)) (by decide) <|
  .nil 17

def j2 : List Byte := [0xeb, 0x0a]
theorem j2_0 : ∀ feat, Dec feat j2 0 (FV7z.mk .jmp 64 [.rel 10] 2) := by dec_rfl

/-- The stretch at `128`. -/
def p4 : List Byte := [
  0x0f, 0xb6, 0x0a]

theorem p4_0 : ∀ feat, Dec feat p4 0 (FV7z.mk .movzx 32 [gr 32 1, .mem (mg (some 2) none 1 0 8)] 3) := by dec_rfl

/-- What the stretch does. -/
def o4 : List Op := [
  Op.ldzx 8 1 (some 2) none 1 0]

theorem b4 (prof : Profile) : Blk prof p4 0 3 o4 :=
  .cons (p4_0 _) (OpI.ldzx (.inl rfl)) (by decide) <|
  .nil 3

/-- The stretch at `131`. -/
def p5 : List Byte := [
  0x48, 0x83, 0xea, 0x01, 0x88, 0x0e, 0x48, 0x83, 0xc6, 0x01, 0x4c, 0x39, 0xca]

theorem p5_0 : ∀ feat, Dec feat p5 0 (FV7z.mk .sub 64 [gr 64 2, Src.opd 64 (.i 1)] 4) := by dec_rfl
theorem p5_4 : ∀ feat, Dec feat p5 4 (FV7z.mk .mov 8 [.mem (mg (some 6) none 1 0 8), gr 8 1] 2) := by dec_rfl
theorem p5_6 : ∀ feat, Dec feat p5 6 (FV7z.mk .add 64 [gr 64 6, Src.opd 64 (.i 1)] 4) := by dec_rfl
theorem p5_10 : ∀ feat, Dec feat p5 10 (FV7z.mk .cmp 64 [gr 64 2, Src.opd 64 (.r 9)] 3) := by dec_rfl

/-- What the stretch does. -/
def o5 : List Op := [
  Op.sub 64 2 (.i 1),
  Op.st 8 (some 6) none 1 0 1,
  Op.add 64 6 (.i 1),
  Op.cmp 64 2 (.r 9)]

theorem b5 (prof : Profile) : Blk prof p5 0 13 o5 :=
  .cons (p5_0 _) (OpI.sub (.i 1) (.inr rfl)) (by decide) <|
  .cons (p5_4 _) (OpI.st (.inl rfl)) (by decide) <|
  .cons (p5_6 _) (OpI.add (.i 1) (.inr rfl)) (by decide) <|
  .cons (p5_10 _) (OpI.cmp (.r 9) (.inr rfl)) (by decide) <|
  .nil 13

def j3 : List Byte := [0x75, 0xee]
theorem j3_0 : ∀ feat, Dec feat j3 0 (FV7z.mk (.jcc 5) 64 [.rel 18446744073709551598] 2) := by dec_rfl

/-- The stretch at `146`. -/
def p6 : List Byte := [
  0x4c, 0x01, 0xc0, 0xc6, 0x00, 0x00, 0x48, 0x8b, 0x74, 0x24, 0x18, 0x64, 0x48, 0x33, 0x34, 0x25,
  0x28, 0x00, 0x00, 0x00]

theorem p6_0 : ∀ feat, Dec feat p6 0 (FV7z.mk .add 64 [gr 64 0, Src.opd 64 (.r 8)] 3) := by dec_rfl
theorem p6_3 : ∀ feat, Dec feat p6 3 (FV7z.mk .mov 8 [.mem (mg (some 0) none 1 0 8), .imm 8 0] 3) := by dec_rfl
theorem p6_6 : ∀ feat, Dec feat p6 6 (FV7z.mk .mov 64 [gr 64 6, .mem (mg (some 4) none 1 24 64)] 5) := by dec_rfl
theorem p6_11 : ∀ feat, Dec feat p6 11 (FV7z.mk .xor 64 [gr 64 6, .mem (mf none none 1 40 64)] 9) := by dec_rfl

/-- What the stretch does. -/
def o6 (fb : Addr) : List Op := [
  Op.add 64 0 (.r 8),
  Op.sti 8 (some 0) none 1 0 0,
  Op.ld 64 6 (some 4) none 1 24,
  Op.xormf fb 64 6 none none 1 40]

theorem b6 (prof : Profile) (fb : Addr) : BlkF prof p6 (0x44acc2 : Addr) fb 0 20 (o6 fb) :=
  .cons (p6_0 _) (((OpI.add (.r 8) (.inr rfl)).at _).fs _) (by decide) <|
  .cons (p6_3 _) (((OpI.sti (.inl rfl)).at _).fs _) (by decide) <|
  .cons (p6_6 _) (((OpI.ld (.inr rfl)).at _).fs _) (by decide) <|
  .cons (p6_11 _) (OpIF.xormf (.inr rfl)) (by decide) <|
  .nil 20

def j4 : List Byte := [0x75, 0x21]
theorem j4_0 : ∀ feat, Dec feat j4 0 (FV7z.mk (.jcc 5) 64 [.rel 33] 2) := by dec_rfl

/-- The stretch at `168`. -/
def p7 : List Byte := [
  0x48, 0x83, 0xc4, 0x28]

theorem p7_0 : ∀ feat, Dec feat p7 0 (FV7z.mk .add 64 [gr 64 4, Src.opd 64 (.i 40)] 4) := by dec_rfl

/-- What the stretch does. -/
def o7 : List Op := [
  Op.add 64 4 (.i 40)]

theorem b7 (prof : Profile) : Blk prof p7 0 4 o7 :=
  .cons (p7_0 _) (OpI.add (.i 40) (.inr rfl)) (by decide) <|
  .nil 4

/-- The stretch at `176`. -/
def p8 : List Byte := [
  0x48, 0x8b, 0x44, 0x24, 0x18, 0x64, 0x48, 0x33, 0x04, 0x25, 0x28, 0x00, 0x00, 0x00]

theorem p8_0 : ∀ feat, Dec feat p8 0 (FV7z.mk .mov 64 [gr 64 0, .mem (mg (some 4) none 1 24 64)] 5) := by dec_rfl
theorem p8_5 : ∀ feat, Dec feat p8 5 (FV7z.mk .xor 64 [gr 64 0, .mem (mf none none 1 40 64)] 9) := by dec_rfl

/-- What the stretch does. -/
def o8 (fb : Addr) : List Op := [
  Op.ld 64 0 (some 4) none 1 24,
  Op.xormf fb 64 0 none none 1 40]

theorem b8 (prof : Profile) (fb : Addr) : BlkF prof p8 (0x44ace0 : Addr) fb 0 14 (o8 fb) :=
  .cons (p8_0 _) (((OpI.ld (.inr rfl)).at _).fs _) (by decide) <|
  .cons (p8_5 _) (OpIF.xormf (.inr rfl)) (by decide) <|
  .nil 14

def j5 : List Byte := [0x75, 0x09]
theorem j5_0 : ∀ feat, Dec feat j5 0 (FV7z.mk (.jcc 5) 64 [.rel 9] 2) := by dec_rfl

end FV7z.C64
