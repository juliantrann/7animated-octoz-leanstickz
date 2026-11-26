import FV7z.Lemmas.SpFs
import FV7z.Lemmas.BlkOps12
import FV7z.Lemmas.BlkOps9
import FV7z.Lemmas.BlkOps6
import FV7z.Lemmas.BlkOps3
/-!
# The stretches of straight-line code of `_int_free` (PLAN.md G3, `free`)

Each distinct stretch between labels and jumps (`p*`, 11 of them) and each distinct jump (`j*`, 10) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.Ifr
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The stretch at `0`. -/
def p0 : List Byte := [
  0x41, 0x57, 0x41, 0x56, 0x41, 0x55, 0x41, 0x89, 0xd5, 0x41, 0x54, 0x55, 0x53, 0x48, 0x83, 0xec,
  0x48, 0x64, 0x48, 0x8b, 0x04, 0x25, 0x28, 0x00, 0x00, 0x00, 0x48, 0x89, 0x44, 0x24, 0x38, 0x31,
  0xc0, 0x48, 0x8b, 0x46, 0x08, 0x48, 0x89, 0xc3, 0x48, 0x83, 0xe3, 0xf8, 0x48, 0x89, 0xda, 0x48,
  0xf7, 0xda, 0x48, 0x39, 0xd6]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .push 64 [gr 64 15] 2) := by dec_rfl
theorem p0_2 : ∀ feat, Dec feat p0 2 (FV7z.mk .push 64 [gr 64 14] 2) := by dec_rfl
theorem p0_4 : ∀ feat, Dec feat p0 4 (FV7z.mk .push 64 [gr 64 13] 2) := by dec_rfl
theorem p0_6 : ∀ feat, Dec feat p0 6 (FV7z.mk .mov 32 [gr 32 13, Src.opd 32 (.r 2)] 3) := by dec_rfl
theorem p0_9 : ∀ feat, Dec feat p0 9 (FV7z.mk .push 64 [gr 64 12] 2) := by dec_rfl
theorem p0_11 : ∀ feat, Dec feat p0 11 (FV7z.mk .push 64 [gr 64 5] 1) := by dec_rfl
theorem p0_12 : ∀ feat, Dec feat p0 12 (FV7z.mk .push 64 [gr 64 3] 1) := by dec_rfl
theorem p0_13 : ∀ feat, Dec feat p0 13 (FV7z.mk .sub 64 [gr 64 4, Src.opd 64 (.i 72)] 4) := by dec_rfl
theorem p0_17 : ∀ feat, Dec feat p0 17 (FV7z.mk .mov 64 [gr 64 0, .mem (mf none none 1 40 64)] 9) := by dec_rfl
theorem p0_26 : ∀ feat, Dec feat p0 26 (FV7z.mk .mov 64 [.mem (mg (some 4) none 1 56 64), gr 64 0] 5) := by dec_rfl
theorem p0_31 : ∀ feat, Dec feat p0 31 (FV7z.mk .xor 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl
theorem p0_33 : ∀ feat, Dec feat p0 33 (FV7z.mk .mov 64 [gr 64 0, .mem (mg (some 6) none 1 8 64)] 4) := by dec_rfl
theorem p0_37 : ∀ feat, Dec feat p0 37 (FV7z.mk .mov 64 [gr 64 3, Src.opd 64 (.r 0)] 3) := by dec_rfl
theorem p0_40 : ∀ feat, Dec feat p0 40 (FV7z.mk .and 64 [gr 64 3, Src.opd 64 (.i 18446744073709551608)] 4) := by dec_rfl
theorem p0_44 : ∀ feat, Dec feat p0 44 (FV7z.mk .mov 64 [gr 64 2, Src.opd 64 (.r 3)] 3) := by dec_rfl
theorem p0_47 : ∀ feat, Dec feat p0 47 (FV7z.mk .neg 64 [gr 64 2] 3) := by dec_rfl
theorem p0_50 : ∀ feat, Dec feat p0 50 (FV7z.mk .cmp 64 [gr 64 6, Src.opd 64 (.r 2)] 3) := by dec_rfl

/-- What the stretch does. -/
def o0 (fb : Addr) : List Op := [
  Op.push 15,
  Op.push 14,
  Op.push 13,
  Op.mov 32 13 (.r 2),
  Op.push 12,
  Op.push 5,
  Op.push 3,
  Op.sub 64 4 (.i 72),
  Op.ldf fb 64 0 none none 1 40,
  Op.st 64 (some 4) none 1 56 0,
  Op.xor 32 0 (.r 0),
  Op.ld 64 0 (some 6) none 1 8,
  Op.mov 64 3 (.r 0),
  Op.and 64 3 (.i 18446744073709551608),
  Op.mov 64 2 (.r 3),
  Op.neg 64 2,
  Op.cmp 64 6 (.r 2)]

theorem b0 (prof : Profile) (fb : Addr) : BlkF prof p0 (0x62f990 : Addr) fb 0 53 (o0 fb) :=
  .cons (p0_0 _) (((OpI.push).at _).fs _) (by decide) <|
  .cons (p0_2 _) (((OpI.push).at _).fs _) (by decide) <|
  .cons (p0_4 _) (((OpI.push).at _).fs _) (by decide) <|
  .cons (p0_6 _) (((OpI.mov (.r 2) (.inl rfl)).at _).fs _) (by decide) <|
  .cons (p0_9 _) (((OpI.push).at _).fs _) (by decide) <|
  .cons (p0_11 _) (((OpI.push).at _).fs _) (by decide) <|
  .cons (p0_12 _) (((OpI.push).at _).fs _) (by decide) <|
  .cons (p0_13 _) (((OpI.sub (.i 72) (.inr rfl)).at _).fs _) (by decide) <|
  .cons (p0_17 _) (OpIF.ldf (.inr rfl)) (by decide) <|
  .cons (p0_26 _) (((OpI.st (.inr (.inr (.inr rfl)))).at _).fs _) (by decide) <|
  .cons (p0_31 _) (((OpI.xor (.r 0) (.inl rfl)).at _).fs _) (by decide) <|
  .cons (p0_33 _) (((OpI.ld (.inr rfl)).at _).fs _) (by decide) <|
  .cons (p0_37 _) (((OpI.mov (.r 0) (.inr rfl)).at _).fs _) (by decide) <|
  .cons (p0_40 _) (((OpI.and (.i 18446744073709551608) (.inr rfl)).at _).fs _) (by decide) <|
  .cons (p0_44 _) (((OpI.mov (.r 3) (.inr rfl)).at _).fs _) (by decide) <|
  .cons (p0_47 _) (((OpI.neg (.inr rfl)).at _).fs _) (by decide) <|
  .cons (p0_50 _) (((OpI.cmp (.r 2) (.inr rfl)).at _).fs _) (by decide) <|
  .nil 53

def j0 : List Byte := [0x0f, 0x87, 0xa5, 0x02, 0x00, 0x00]
theorem j0_0 : ∀ feat, Dec feat j0 0 (FV7z.mk (.jcc 7) 64 [.rel 677] 6) := by dec_rfl

/-- The stretch at `59`. -/
def p1 : List Byte := [
  0x49, 0x89, 0xf4, 0x40, 0xf6, 0xc6, 0x0f]

theorem p1_0 : ∀ feat, Dec feat p1 0 (FV7z.mk .mov 64 [gr 64 12, Src.opd 64 (.r 6)] 3) := by dec_rfl
theorem p1_3 : ∀ feat, Dec feat p1 3 (FV7z.mk .test 8 [gr 8 6, Src.opd 8 (.i 15)] 4) := by dec_rfl

/-- What the stretch does. -/
def o1 : List Op := [
  Op.mov 64 12 (.r 6),
  Op.test 8 6 (.i 15)]

theorem b1 (prof : Profile) : Blk prof p1 0 7 o1 :=
  .cons (p1_0 _) (OpI.mov (.r 6) (.inr rfl)) (by decide) <|
  .cons (p1_3 _) (OpI.test8 (.i 15)) (by decide) <|
  .nil 7

def j1 : List Byte := [0x0f, 0x85, 0x98, 0x02, 0x00, 0x00]
theorem j1_0 : ∀ feat, Dec feat j1 0 (FV7z.mk (.jcc 5) 64 [.rel 664] 6) := by dec_rfl

/-- The stretch at `72`. -/
def p2 : List Byte := [
  0x48, 0x83, 0xfb, 0x1f]

theorem p2_0 : ∀ feat, Dec feat p2 0 (FV7z.mk .cmp 64 [gr 64 3, Src.opd 64 (.i 31)] 4) := by dec_rfl

/-- What the stretch does. -/
def o2 : List Op := [
  Op.cmp 64 3 (.i 31)]

theorem b2 (prof : Profile) : Blk prof p2 0 4 o2 :=
  .cons (p2_0 _) (OpI.cmp (.i 31) (.inr rfl)) (by decide) <|
  .nil 4

def j2 : List Byte := [0x0f, 0x86, 0x9e, 0x02, 0x00, 0x00]
theorem j2_0 : ∀ feat, Dec feat j2 0 (FV7z.mk (.jcc 6) 64 [.rel 670] 6) := by dec_rfl

/-- The stretch at `82`. -/
def p3 : List Byte := [
  0xa8, 0x08]

theorem p3_0 : ∀ feat, Dec feat p3 0 (FV7z.mk .test 8 [gr 8 0, Src.opd 8 (.i 8)] 2) := by dec_rfl

/-- What the stretch does. -/
def o3 : List Op := [
  Op.test 8 0 (.i 8)]

theorem b3 (prof : Profile) : Blk prof p3 0 2 o3 :=
  .cons (p3_0 _) (OpI.test8 (.i 8)) (by decide) <|
  .nil 2

def j3 : List Byte := [0x0f, 0x85, 0x96, 0x02, 0x00, 0x00]
theorem j3_0 : ∀ feat, Dec feat j3 0 (FV7z.mk (.jcc 5) 64 [.rel 662] 6) := by dec_rfl

/-- The stretch at `90`. -/
def p4 : List Byte := [
  0x64, 0x48, 0x8b, 0x14, 0x25, 0xd8, 0xff, 0xff, 0xff, 0x48, 0x89, 0xfd, 0x48, 0x85, 0xd2]

theorem p4_0 : ∀ feat, Dec feat p4 0 (FV7z.mk .mov 64 [gr 64 2, .mem (mf none none 1 18446744073709551576 64)] 9) := by dec_rfl
theorem p4_9 : ∀ feat, Dec feat p4 9 (FV7z.mk .mov 64 [gr 64 5, Src.opd 64 (.r 7)] 3) := by dec_rfl
theorem p4_12 : ∀ feat, Dec feat p4 12 (FV7z.mk .test 64 [gr 64 2, Src.opd 64 (.r 2)] 3) := by dec_rfl

/-- What the stretch does. -/
def o4 (fb : Addr) : List Op := [
  Op.ldf fb 64 2 none none 1 18446744073709551576,
  Op.mov 64 5 (.r 7),
  Op.test 64 2 (.r 2)]

theorem b4 (prof : Profile) (fb : Addr) : BlkF prof p4 (0x62f9ea : Addr) fb 0 15 (o4 fb) :=
  .cons (p4_0 _) (OpIF.ldf (.inr rfl)) (by decide) <|
  .cons (p4_9 _) (((OpI.mov (.r 7) (.inr rfl)).at _).fs _) (by decide) <|
  .cons (p4_12 _) (((OpI.test (.r 2) (.inr rfl)).at _).fs _) (by decide) <|
  .nil 15

def j4 : List Byte := [0x74, 0x38]
theorem j4_0 : ∀ feat, Dec feat j4 0 (FV7z.mk (.jcc 4) 64 [.rel 56] 2) := by dec_rfl

/-- The stretch at `107`. -/
def p5 : List Byte := [
  0x48, 0x8d, 0x43, 0xef, 0x48, 0xc1, 0xe8, 0x04, 0x48, 0x39, 0x05, 0xe6, 0x2f, 0x16, 0x00]

theorem p5_0 : ∀ feat, Dec feat p5 0 (FV7z.mk .lea 64 [gr 64 0, .mem (mg (some 3) none 1 18446744073709551599 0)] 4) := by dec_rfl
theorem p5_4 : ∀ feat, Dec feat p5 4 (FV7z.mk .shr 64 [gr 64 0, Src.opd 8 (.i 4)] 4) := by dec_rfl
theorem p5_8 : ∀ feat, Dec feat p5 8 (FV7z.mk .cmp 64 [.mem (mrip 1454054 64), gr 64 0] 7) := by dec_rfl

/-- What the stretch does. -/
def o5 : List Op := [
  Op.lea 64 0 (some 3) none 1 18446744073709551599,
  Op.shr64 0 (.i 4),
  Op.cmpmra 64 7940592 0]

theorem b5 (prof : Profile) : BlkA prof p5 (0x62f9fb : Addr) 0 15 o5 :=
  .cons (p5_0 _) ((OpI.lea (.inr rfl)).at _) (by decide) <|
  .cons (p5_4 _) ((OpI.shr64 (.i 4)).at _) (by decide) <|
  .cons (p5_8 _) (OpIA.cmpmr_rip (.inr rfl) (by decide)) (by decide) <|
  .nil 15

def j5 : List Byte := [0x76, 0x27]
theorem j5_0 : ∀ feat, Dec feat j5 0 (FV7z.mk (.jcc 6) 64 [.rel 39] 2) := by dec_rfl

/-- The stretch at `124`. -/
def p6 : List Byte := [
  0x48, 0x8d, 0x76, 0x10, 0x49, 0x3b, 0x54, 0x24, 0x18]

theorem p6_0 : ∀ feat, Dec feat p6 0 (FV7z.mk .lea 64 [gr 64 6, .mem (mg (some 6) none 1 16 0)] 4) := by dec_rfl
theorem p6_4 : ∀ feat, Dec feat p6 4 (FV7z.mk .cmp 64 [gr 64 2, .mem (mg (some 12) none 1 24 64)] 5) := by dec_rfl

/-- What the stretch does. -/
def o6 : List Op := [
  Op.lea 64 6 (some 6) none 1 16,
  Op.cmpm 64 2 (some 12) none 1 24]

theorem b6 (prof : Profile) : Blk prof p6 0 9 o6 :=
  .cons (p6_0 _) (OpI.lea (.inr rfl)) (by decide) <|
  .cons (p6_4 _) (OpI.cmpm (.inr rfl)) (by decide) <|
  .nil 9

def j6 : List Byte := [0x0f, 0x84, 0x6d, 0x06, 0x00, 0x00]
theorem j6_0 : ∀ feat, Dec feat j6 0 (FV7z.mk (.jcc 4) 64 [.rel 1645] 6) := by dec_rfl

/-- The stretch at `139`. -/
def p7 : List Byte := [
  0x48, 0x8d, 0x3c, 0x42, 0x44, 0x0f, 0xb7, 0x07, 0x4c, 0x3b, 0x05, 0xd6, 0x2f, 0x16, 0x00, 0x4c,
  0x89, 0xc1]

theorem p7_0 : ∀ feat, Dec feat p7 0 (FV7z.mk .lea 64 [gr 64 7, .mem (mg (some 2) (some 0) 2 0 0)] 4) := by dec_rfl
theorem p7_4 : ∀ feat, Dec feat p7 4 (FV7z.mk .movzx 32 [gr 32 8, .mem (mg (some 7) none 1 0 16)] 4) := by dec_rfl
theorem p7_8 : ∀ feat, Dec feat p7 8 (FV7z.mk .cmp 64 [gr 64 8, .mem (mrip 1454038 64)] 7) := by dec_rfl
theorem p7_15 : ∀ feat, Dec feat p7 15 (FV7z.mk .mov 64 [gr 64 1, Src.opd 64 (.r 8)] 3) := by dec_rfl

/-- What the stretch does. -/
def o7 : List Op := [
  Op.lea 64 7 (some 2) (some 0) 2 0,
  Op.ldzx 16 8 (some 7) none 1 0,
  Op.cmpma 64 8 7940608,
  Op.mov 64 1 (.r 8)]

theorem b7 (prof : Profile) : BlkA prof p7 (0x62fa1b : Addr) 0 18 o7 :=
  .cons (p7_0 _) ((OpI.lea (.inr rfl)).at _) (by decide) <|
  .cons (p7_4 _) ((OpI.ldzx (.inr rfl)).at _) (by decide) <|
  .cons (p7_8 _) (OpIA.cmpm_rip (.inr (.inr rfl)) (by decide)) (by decide) <|
  .cons (p7_15 _) ((OpI.mov (.r 8) (.inr rfl)).at _) (by decide) <|
  .nil 18

def j7 : List Byte := [0x0f, 0x82, 0x15, 0x02, 0x00, 0x00]
theorem j7_0 : ∀ feat, Dec feat j7 0 (FV7z.mk (.jcc 2) 64 [.rel 533] 6) := by dec_rfl

/-- The stretch at `307`. -/
def p8 : List Byte := [
  0x48, 0x8b, 0x44, 0x24, 0x38, 0x64, 0x48, 0x33, 0x04, 0x25, 0x28, 0x00, 0x00, 0x00]

theorem p8_0 : ∀ feat, Dec feat p8 0 (FV7z.mk .mov 64 [gr 64 0, .mem (mg (some 4) none 1 56 64)] 5) := by dec_rfl
theorem p8_5 : ∀ feat, Dec feat p8 5 (FV7z.mk .xor 64 [gr 64 0, .mem (mf none none 1 40 64)] 9) := by dec_rfl

/-- What the stretch does. -/
def o8 (fb : Addr) : List Op := [
  Op.ld 64 0 (some 4) none 1 56,
  Op.xormf fb 64 0 none none 1 40]

theorem b8 (prof : Profile) (fb : Addr) : BlkF prof p8 (0x62fac3 : Addr) fb 0 14 (o8 fb) :=
  .cons (p8_0 _) (((OpI.ld (.inr rfl)).at _).fs _) (by decide) <|
  .cons (p8_5 _) (OpIF.xormf (.inr rfl)) (by decide) <|
  .nil 14

def j8 : List Byte := [0x0f, 0x85, 0x40, 0x08, 0x00, 0x00]
theorem j8_0 : ∀ feat, Dec feat j8 0 (FV7z.mk (.jcc 5) 64 [.rel 2112] 6) := by dec_rfl

/-- The stretch at `327`. -/
def p9 : List Byte := [
  0x48, 0x83, 0xc4, 0x48, 0x5b, 0x5d, 0x41, 0x5c, 0x41, 0x5d, 0x41, 0x5e, 0x41, 0x5f]

theorem p9_0 : ∀ feat, Dec feat p9 0 (FV7z.mk .add 64 [gr 64 4, Src.opd 64 (.i 72)] 4) := by dec_rfl
theorem p9_4 : ∀ feat, Dec feat p9 4 (FV7z.mk .pop 64 [gr 64 3] 1) := by dec_rfl
theorem p9_5 : ∀ feat, Dec feat p9 5 (FV7z.mk .pop 64 [gr 64 5] 1) := by dec_rfl
theorem p9_6 : ∀ feat, Dec feat p9 6 (FV7z.mk .pop 64 [gr 64 12] 2) := by dec_rfl
theorem p9_8 : ∀ feat, Dec feat p9 8 (FV7z.mk .pop 64 [gr 64 13] 2) := by dec_rfl
theorem p9_10 : ∀ feat, Dec feat p9 10 (FV7z.mk .pop 64 [gr 64 14] 2) := by dec_rfl
theorem p9_12 : ∀ feat, Dec feat p9 12 (FV7z.mk .pop 64 [gr 64 15] 2) := by dec_rfl

/-- What the stretch does. -/
def o9 : List Op := [
  Op.add 64 4 (.i 72),
  Op.pop 3,
  Op.pop 5,
  Op.pop 12,
  Op.pop 13,
  Op.pop 14,
  Op.pop 15]

theorem b9 (prof : Profile) : Blk prof p9 0 14 o9 :=
  .cons (p9_0 _) (OpI.add (.i 72) (.inr rfl)) (by decide) <|
  .cons (p9_4 _) (OpI.pop) (by decide) <|
  .cons (p9_5 _) (OpI.pop) (by decide) <|
  .cons (p9_6 _) (OpI.pop) (by decide) <|
  .cons (p9_8 _) (OpI.pop) (by decide) <|
  .cons (p9_10 _) (OpI.pop) (by decide) <|
  .cons (p9_12 _) (OpI.pop) (by decide) <|
  .nil 14

/-- The stretch at `696`. -/
def p10 : List Byte := [
  0x48, 0x8d, 0x04, 0xc2, 0x49, 0x89, 0x54, 0x24, 0x18, 0x83, 0xc1, 0x01, 0x48, 0x8b, 0x90, 0x80,
  0x00, 0x00, 0x00, 0x49, 0x89, 0x54, 0x24, 0x10, 0x48, 0x89, 0xb0, 0x80, 0x00, 0x00, 0x00, 0x66,
  0x89, 0x0f]

theorem p10_0 : ∀ feat, Dec feat p10 0 (FV7z.mk .lea 64 [gr 64 0, .mem (mg (some 2) (some 0) 8 0 0)] 4) := by dec_rfl
theorem p10_4 : ∀ feat, Dec feat p10 4 (FV7z.mk .mov 64 [.mem (mg (some 12) none 1 24 64), gr 64 2] 5) := by dec_rfl
theorem p10_9 : ∀ feat, Dec feat p10 9 (FV7z.mk .add 32 [gr 32 1, Src.opd 32 (.i 1)] 3) := by dec_rfl
theorem p10_12 : ∀ feat, Dec feat p10 12 (FV7z.mk .mov 64 [gr 64 2, .mem (mg (some 0) none 1 128 64)] 7) := by dec_rfl
theorem p10_19 : ∀ feat, Dec feat p10 19 (FV7z.mk .mov 64 [.mem (mg (some 12) none 1 16 64), gr 64 2] 5) := by dec_rfl
theorem p10_24 : ∀ feat, Dec feat p10 24 (FV7z.mk .mov 64 [.mem (mg (some 0) none 1 128 64), gr 64 6] 7) := by dec_rfl
theorem p10_31 : ∀ feat, Dec feat p10 31 (FV7z.mk .mov 16 [.mem (mg (some 7) none 1 0 16), gr 16 1] 3) := by dec_rfl

/-- What the stretch does. -/
def o10 : List Op := [
  Op.lea 64 0 (some 2) (some 0) 8 0,
  Op.st 64 (some 12) none 1 24 2,
  Op.add 32 1 (.i 1),
  Op.ld 64 2 (some 0) none 1 128,
  Op.st 64 (some 12) none 1 16 2,
  Op.st 64 (some 0) none 1 128 6,
  Op.st 16 (some 7) none 1 0 1]

theorem b10 (prof : Profile) : Blk prof p10 0 34 o10 :=
  .cons (p10_0 _) (OpI.lea (.inr rfl)) (by decide) <|
  .cons (p10_4 _) (OpI.st (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p10_9 _) (OpI.add (.i 1) (.inl rfl)) (by decide) <|
  .cons (p10_12 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p10_19 _) (OpI.st (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p10_24 _) (OpI.st (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p10_31 _) (OpI.st (.inr (.inl rfl))) (by decide) <|
  .nil 34

def j9 : List Byte := [0xe9, 0x54, 0xfe, 0xff, 0xff]
theorem j9_0 : ∀ feat, Dec feat j9 0 (FV7z.mk .jmp 64 [.rel 18446744073709551188] 5) := by dec_rfl

end FV7z.Ifr
