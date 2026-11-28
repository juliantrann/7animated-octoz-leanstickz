import FV7z.Lemmas.SpFs
import FV7z.Lemmas.BlkOps25
import FV7z.Lemmas.BlkOps14
import FV7z.Lemmas.BlkOps6
import FV7z.Lemmas.BlkOps2
/-!
# The stretches of straight-line code of `CArc::GetItem_DefaultPath` (PLAN.md §M, M1)

Each distinct stretch between labels and jumps (`p*`, 13 of them) and each distinct jump (`j*`, 9) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.Gdp
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The stretch at `0`. -/
def p0 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0x41, 0x56, 0x41, 0x55, 0x41, 0x89, 0xf5, 0x41, 0x54, 0x55, 0x48, 0x89,
  0xd5, 0x53, 0x48, 0x89, 0xfb, 0x48, 0x83, 0xec, 0x30, 0x48, 0x8b, 0x3f, 0x64, 0x48, 0x8b, 0x04,
  0x25, 0x28, 0x00, 0x00, 0x00, 0x48, 0x89, 0x44, 0x24, 0x28, 0x31, 0xc0, 0x48, 0x8b, 0x02, 0xc7,
  0x42, 0x08, 0x00, 0x00, 0x00, 0x00, 0x48, 0x8d, 0x54, 0x24, 0x0f, 0xc7, 0x00, 0x00, 0x00, 0x00,
  0x00]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem p0_4 : ∀ feat, Dec feat p0 4 (FV7z.mk .push 64 [gr 64 14] 2) := by dec_rfl
theorem p0_6 : ∀ feat, Dec feat p0 6 (FV7z.mk .push 64 [gr 64 13] 2) := by dec_rfl
theorem p0_8 : ∀ feat, Dec feat p0 8 (FV7z.mk .mov 32 [gr 32 13, Src.opd 32 (.r 6)] 3) := by dec_rfl
theorem p0_11 : ∀ feat, Dec feat p0 11 (FV7z.mk .push 64 [gr 64 12] 2) := by dec_rfl
theorem p0_13 : ∀ feat, Dec feat p0 13 (FV7z.mk .push 64 [gr 64 5] 1) := by dec_rfl
theorem p0_14 : ∀ feat, Dec feat p0 14 (FV7z.mk .mov 64 [gr 64 5, Src.opd 64 (.r 2)] 3) := by dec_rfl
theorem p0_17 : ∀ feat, Dec feat p0 17 (FV7z.mk .push 64 [gr 64 3] 1) := by dec_rfl
theorem p0_18 : ∀ feat, Dec feat p0 18 (FV7z.mk .mov 64 [gr 64 3, Src.opd 64 (.r 7)] 3) := by dec_rfl
theorem p0_21 : ∀ feat, Dec feat p0 21 (FV7z.mk .sub 64 [gr 64 4, Src.opd 64 (.i 48)] 4) := by dec_rfl
theorem p0_25 : ∀ feat, Dec feat p0 25 (FV7z.mk .mov 64 [gr 64 7, .mem (mg (some 7) none 1 0 64)] 3) := by dec_rfl
theorem p0_28 : ∀ feat, Dec feat p0 28 (FV7z.mk .mov 64 [gr 64 0, .mem (mf none none 1 40 64)] 9) := by dec_rfl
theorem p0_37 : ∀ feat, Dec feat p0 37 (FV7z.mk .mov 64 [.mem (mg (some 4) none 1 40 64), gr 64 0] 5) := by dec_rfl
theorem p0_42 : ∀ feat, Dec feat p0 42 (FV7z.mk .xor 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl
theorem p0_44 : ∀ feat, Dec feat p0 44 (FV7z.mk .mov 64 [gr 64 0, .mem (mg (some 2) none 1 0 64)] 3) := by dec_rfl
theorem p0_47 : ∀ feat, Dec feat p0 47 (FV7z.mk .mov 32 [.mem (mg (some 2) none 1 8 32), .imm 32 0] 7) := by dec_rfl
theorem p0_54 : ∀ feat, Dec feat p0 54 (FV7z.mk .lea 64 [gr 64 2, .mem (mg (some 4) none 1 15 0)] 5) := by dec_rfl
theorem p0_59 : ∀ feat, Dec feat p0 59 (FV7z.mk .mov 32 [.mem (mg (some 0) none 1 0 32), .imm 32 0] 6) := by dec_rfl

/-- What the stretch does. -/
def o0 (fb : Addr) : List Op := [
  Op.nop,
  Op.push 14,
  Op.push 13,
  Op.mov 32 13 (.r 6),
  Op.push 12,
  Op.push 5,
  Op.mov 64 5 (.r 2),
  Op.push 3,
  Op.mov 64 3 (.r 7),
  Op.sub 64 4 (.i 48),
  Op.ld 64 7 (some 7) none 1 0,
  Op.ldf fb 64 0 none none 1 40,
  Op.st 64 (some 4) none 1 40 0,
  Op.xor 32 0 (.r 0),
  Op.ld 64 0 (some 2) none 1 0,
  Op.sti 32 (some 2) none 1 8 0,
  Op.lea 64 2 (some 4) none 1 15,
  Op.sti 32 (some 0) none 1 0 0]

theorem b0 (prof : Profile) (fb : Addr) : BlkF prof p0 (0x5d2040 : Addr) fb 0 65 (o0 fb) :=
  .cons (p0_0 _) (((OpI.endbr).at _).fs _) (by decide) <|
  .cons (p0_4 _) (((OpI.push).at _).fs _) (by decide) <|
  .cons (p0_6 _) (((OpI.push).at _).fs _) (by decide) <|
  .cons (p0_8 _) (((OpI.mov (.r 6) (.inl rfl)).at _).fs _) (by decide) <|
  .cons (p0_11 _) (((OpI.push).at _).fs _) (by decide) <|
  .cons (p0_13 _) (((OpI.push).at _).fs _) (by decide) <|
  .cons (p0_14 _) (((OpI.mov (.r 2) (.inr rfl)).at _).fs _) (by decide) <|
  .cons (p0_17 _) (((OpI.push).at _).fs _) (by decide) <|
  .cons (p0_18 _) (((OpI.mov (.r 7) (.inr rfl)).at _).fs _) (by decide) <|
  .cons (p0_21 _) (((OpI.sub (.i 48) (.inr rfl)).at _).fs _) (by decide) <|
  .cons (p0_25 _) (((OpI.ld (.inr rfl)).at _).fs _) (by decide) <|
  .cons (p0_28 _) (OpIF.ldf (.inr rfl)) (by decide) <|
  .cons (p0_37 _) (((OpI.st (.inr (.inr (.inr rfl)))).at _).fs _) (by decide) <|
  .cons (p0_42 _) (((OpI.xor (.r 0) (.inl rfl)).at _).fs _) (by decide) <|
  .cons (p0_44 _) (((OpI.ld (.inr rfl)).at _).fs _) (by decide) <|
  .cons (p0_47 _) (((OpI.sti (.inr (.inr (.inl rfl)))).at _).fs _) (by decide) <|
  .cons (p0_54 _) (((OpI.lea (.inr rfl)).at _).fs _) (by decide) <|
  .cons (p0_59 _) (((OpI.sti (.inr (.inr (.inl rfl)))).at _).fs _) (by decide) <|
  .nil 65

/-- The stretch at `70`. -/
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

def j0 : List Byte := [0x75, 0x07]
theorem j0_0 : ∀ feat, Dec feat j0 0 (FV7z.mk (.jcc 5) 64 [.rel 7] 2) := by dec_rfl

/-- The stretch at `77`. -/
def p2 : List Byte := [
  0x80, 0x7c, 0x24, 0x0f, 0x00]

theorem p2_0 : ∀ feat, Dec feat p2 0 (FV7z.mk .cmp 8 [.mem (mg (some 4) none 1 15 8), .imm 8 0] 5) := by dec_rfl

/-- What the stretch does. -/
def o2 : List Op := [
  Op.cmpmi 8 (some 4) none 1 15 0]

theorem b2 (prof : Profile) : Blk prof p2 0 5 o2 :=
  .cons (p2_0 _) (OpI.cmpmi (.inl rfl)) (by decide) <|
  .nil 5

def j1 : List Byte := [0x74, 0x2c]
theorem j1_0 : ∀ feat, Dec feat j1 0 (FV7z.mk (.jcc 4) 64 [.rel 44] 2) := by dec_rfl

/-- The stretch at `84`. -/
def p3 : List Byte := [
  0x48, 0x8b, 0x44, 0x24, 0x28, 0x64, 0x48, 0x33, 0x04, 0x25, 0x28, 0x00, 0x00, 0x00]

theorem p3_0 : ∀ feat, Dec feat p3 0 (FV7z.mk .mov 64 [gr 64 0, .mem (mg (some 4) none 1 40 64)] 5) := by dec_rfl
theorem p3_5 : ∀ feat, Dec feat p3 5 (FV7z.mk .xor 64 [gr 64 0, .mem (mf none none 1 40 64)] 9) := by dec_rfl

/-- What the stretch does. -/
def o3 (fb : Addr) : List Op := [
  Op.ld 64 0 (some 4) none 1 40,
  Op.xormf fb 64 0 none none 1 40]

theorem b3 (prof : Profile) (fb : Addr) : BlkF prof p3 (0x5d2094 : Addr) fb 0 14 (o3 fb) :=
  .cons (p3_0 _) (((OpI.ld (.inr rfl)).at _).fs _) (by decide) <|
  .cons (p3_5 _) (OpIF.xormf (.inr rfl)) (by decide) <|
  .nil 14

def j2 : List Byte := [0x0f, 0x85, 0x9f, 0x00, 0x00, 0x00]
theorem j2_0 : ∀ feat, Dec feat j2 0 (FV7z.mk (.jcc 5) 64 [.rel 159] 6) := by dec_rfl

/-- The stretch at `104`. -/
def p4 : List Byte := [
  0x48, 0x83, 0xc4, 0x30, 0x44, 0x89, 0xe0, 0x5b, 0x5d, 0x41, 0x5c, 0x41, 0x5d, 0x41, 0x5e]

theorem p4_0 : ∀ feat, Dec feat p4 0 (FV7z.mk .add 64 [gr 64 4, Src.opd 64 (.i 48)] 4) := by dec_rfl
theorem p4_4 : ∀ feat, Dec feat p4 4 (FV7z.mk .mov 32 [gr 32 0, Src.opd 32 (.r 12)] 3) := by dec_rfl
theorem p4_7 : ∀ feat, Dec feat p4 7 (FV7z.mk .pop 64 [gr 64 3] 1) := by dec_rfl
theorem p4_8 : ∀ feat, Dec feat p4 8 (FV7z.mk .pop 64 [gr 64 5] 1) := by dec_rfl
theorem p4_9 : ∀ feat, Dec feat p4 9 (FV7z.mk .pop 64 [gr 64 12] 2) := by dec_rfl
theorem p4_11 : ∀ feat, Dec feat p4 11 (FV7z.mk .pop 64 [gr 64 13] 2) := by dec_rfl
theorem p4_13 : ∀ feat, Dec feat p4 13 (FV7z.mk .pop 64 [gr 64 14] 2) := by dec_rfl

/-- What the stretch does. -/
def o4 : List Op := [
  Op.add 64 4 (.i 48),
  Op.mov 32 0 (.r 12),
  Op.pop 3,
  Op.pop 5,
  Op.pop 12,
  Op.pop 13,
  Op.pop 14]

theorem b4 (prof : Profile) : Blk prof p4 0 15 o4 :=
  .cons (p4_0 _) (OpI.add (.i 48) (.inr rfl)) (by decide) <|
  .cons (p4_4 _) (OpI.mov (.r 12) (.inl rfl)) (by decide) <|
  .cons (p4_7 _) (OpI.pop) (by decide) <|
  .cons (p4_8 _) (OpI.pop) (by decide) <|
  .cons (p4_9 _) (OpI.pop) (by decide) <|
  .cons (p4_11 _) (OpI.pop) (by decide) <|
  .cons (p4_13 _) (OpI.pop) (by decide) <|
  .nil 15

/-- The stretch at `128`. -/
def p5 : List Byte := [
  0x48, 0x8d, 0x73, 0x48, 0x48, 0x89, 0xef, 0x4c, 0x8d, 0x74, 0x24, 0x10]

theorem p5_0 : ∀ feat, Dec feat p5 0 (FV7z.mk .lea 64 [gr 64 6, .mem (mg (some 3) none 1 72 0)] 4) := by dec_rfl
theorem p5_4 : ∀ feat, Dec feat p5 4 (FV7z.mk .mov 64 [gr 64 7, Src.opd 64 (.r 5)] 3) := by dec_rfl
theorem p5_7 : ∀ feat, Dec feat p5 7 (FV7z.mk .lea 64 [gr 64 14, .mem (mg (some 4) none 1 16 0)] 5) := by dec_rfl

/-- What the stretch does. -/
def o5 : List Op := [
  Op.lea 64 6 (some 3) none 1 72,
  Op.mov 64 7 (.r 5),
  Op.lea 64 14 (some 4) none 1 16]

theorem b5 (prof : Profile) : Blk prof p5 0 12 o5 :=
  .cons (p5_0 _) (OpI.lea (.inr rfl)) (by decide) <|
  .cons (p5_4 _) (OpI.mov (.r 5) (.inr rfl)) (by decide) <|
  .cons (p5_7 _) (OpI.lea (.inr rfl)) (by decide) <|
  .nil 12

/-- The stretch at `145`. -/
def p6 : List Byte := [
  0x48, 0x8b, 0x3b, 0x4c, 0x89, 0xf1, 0xba, 0x05, 0x00, 0x00, 0x00, 0xc7, 0x44, 0x24, 0x10, 0x00,
  0x00, 0x00, 0x00, 0x44, 0x89, 0xee, 0x48, 0xc7, 0x44, 0x24, 0x18, 0x00, 0x00, 0x00, 0x00, 0x48,
  0x8b, 0x07]

theorem p6_0 : ∀ feat, Dec feat p6 0 (FV7z.mk .mov 64 [gr 64 7, .mem (mg (some 3) none 1 0 64)] 3) := by dec_rfl
theorem p6_3 : ∀ feat, Dec feat p6 3 (FV7z.mk .mov 64 [gr 64 1, Src.opd 64 (.r 14)] 3) := by dec_rfl
theorem p6_6 : ∀ feat, Dec feat p6 6 (FV7z.mk .mov 32 [gr 32 2, Src.opd 32 (.i 5)] 5) := by dec_rfl
theorem p6_11 : ∀ feat, Dec feat p6 11 (FV7z.mk .mov 32 [.mem (mg (some 4) none 1 16 32), .imm 32 0] 8) := by dec_rfl
theorem p6_19 : ∀ feat, Dec feat p6 19 (FV7z.mk .mov 32 [gr 32 6, Src.opd 32 (.r 13)] 3) := by dec_rfl
theorem p6_22 : ∀ feat, Dec feat p6 22 (FV7z.mk .mov 64 [.mem (mg (some 4) none 1 24 64), .imm 64 0] 9) := by dec_rfl
theorem p6_31 : ∀ feat, Dec feat p6 31 (FV7z.mk .mov 64 [gr 64 0, .mem (mg (some 7) none 1 0 64)] 3) := by dec_rfl

/-- What the stretch does. -/
def o6 : List Op := [
  Op.ld 64 7 (some 3) none 1 0,
  Op.mov 64 1 (.r 14),
  Op.mov 32 2 (.i 5),
  Op.sti 32 (some 4) none 1 16 0,
  Op.mov 32 6 (.r 13),
  Op.sti 64 (some 4) none 1 24 0,
  Op.ld 64 0 (some 7) none 1 0]

theorem b6 (prof : Profile) : Blk prof p6 0 34 o6 :=
  .cons (p6_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p6_3 _) (OpI.mov (.r 14) (.inr rfl)) (by decide) <|
  .cons (p6_6 _) (OpI.mov (.i 5) (.inl rfl)) (by decide) <|
  .cons (p6_11 _) (OpI.sti (.inr (.inr (.inl rfl)))) (by decide) <|
  .cons (p6_19 _) (OpI.mov (.r 13) (.inl rfl)) (by decide) <|
  .cons (p6_22 _) (OpI.sti (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p6_31 _) (OpI.ld (.inr rfl)) (by decide) <|
  .nil 34

def j3 : List Byte := [0x75, 0x10]
theorem j3_0 : ∀ feat, Dec feat j3 0 (FV7z.mk (.jcc 5) 64 [.rel 16] 2) := by dec_rfl

/-- The stretch at `189`. -/
def p7 : List Byte := [
  0x0f, 0xb7, 0x44, 0x24, 0x10, 0x66, 0x83, 0xf8, 0x08]

theorem p7_0 : ∀ feat, Dec feat p7 0 (FV7z.mk .movzx 32 [gr 32 0, .mem (mg (some 4) none 1 16 16)] 5) := by dec_rfl
theorem p7_5 : ∀ feat, Dec feat p7 5 (FV7z.mk .cmp 16 [gr 16 0, Src.opd 16 (.i 8)] 4) := by dec_rfl

/-- What the stretch does. -/
def o7 : List Op := [
  Op.ldzx 16 0 (some 4) none 1 16,
  Op.cmp 16 0 (.i 8)]

theorem b7 (prof : Profile) : Blk prof p7 0 9 o7 :=
  .cons (p7_0 _) (OpI.ldzx (.inr rfl)) (by decide) <|
  .cons (p7_5 _) (OpI.cmp16 (.i 8)) (by decide) <|
  .nil 9

def j4 : List Byte := [0x74, 0x28]
theorem j4_0 : ∀ feat, Dec feat j4 0 (FV7z.mk (.jcc 4) 64 [.rel 40] 2) := by dec_rfl

/-- The stretch at `200`. -/
def p8 : List Byte := [
  0x66, 0x85, 0xc0]

theorem p8_0 : ∀ feat, Dec feat p8 0 (FV7z.mk .test 16 [gr 16 0, Src.opd 16 (.r 0)] 3) := by dec_rfl

/-- What the stretch does. -/
def o8 : List Op := [
  Op.test 16 0 (.r 0)]

theorem b8 (prof : Profile) : Blk prof p8 0 3 o8 :=
  .cons (p8_0 _) (OpI.test16 (.r 0)) (by decide) <|
  .nil 3

def j5 : List Byte := [0x75, 0x13]
theorem j5_0 : ∀ feat, Dec feat j5 0 (FV7z.mk (.jcc 5) 64 [.rel 19] 2) := by dec_rfl

/-- The stretch at `205`. -/
def p9 : List Byte := [
  0x4c, 0x89, 0xf7]

theorem p9_0 : ∀ feat, Dec feat p9 0 (FV7z.mk .mov 64 [gr 64 7, Src.opd 64 (.r 14)] 3) := by dec_rfl

/-- What the stretch does. -/
def o9 : List Op := [
  Op.mov 64 7 (.r 14)]

theorem b9 (prof : Profile) : Blk prof p9 0 3 o9 :=
  .cons (p9_0 _) (OpI.mov (.r 14) (.inr rfl)) (by decide) <|
  .nil 3

def j6 : List Byte := [0xe9, 0x7a, 0xff, 0xff, 0xff]
theorem j6_0 : ∀ feat, Dec feat j6 0 (FV7z.mk .jmp 64 [.rel 18446744073709551482] 5) := by dec_rfl

/-- The stretch at `224`. -/
def p10 : List Byte := [
  0x41, 0xbc, 0x05, 0x40, 0x00, 0x80]

theorem p10_0 : ∀ feat, Dec feat p10 0 (FV7z.mk .mov 32 [gr 32 12, Src.opd 32 (.i 2147500037)] 6) := by dec_rfl

/-- What the stretch does. -/
def o10 : List Op := [
  Op.mov 32 12 (.i 2147500037)]

theorem b10 (prof : Profile) : Blk prof p10 0 6 o10 :=
  .cons (p10_0 _) (OpI.mov (.i 2147500037) (.inl rfl)) (by decide) <|
  .nil 6

def j7 : List Byte := [0xeb, 0xe5]
theorem j7_0 : ∀ feat, Dec feat j7 0 (FV7z.mk .jmp 64 [.rel 18446744073709551589] 2) := by dec_rfl

/-- The stretch at `240`. -/
def p11 : List Byte := [
  0x48, 0x89, 0xef]

theorem p11_0 : ∀ feat, Dec feat p11 0 (FV7z.mk .mov 64 [gr 64 7, Src.opd 64 (.r 5)] 3) := by dec_rfl

/-- What the stretch does. -/
def o11 : List Op := [
  Op.mov 64 7 (.r 5)]

theorem b11 (prof : Profile) : Blk prof p11 0 3 o11 :=
  .cons (p11_0 _) (OpI.mov (.r 5) (.inr rfl)) (by decide) <|
  .nil 3

/-- The stretch at `248`. -/
def p12 : List Byte := [
  0x48, 0x8b, 0x74, 0x24, 0x18, 0x48, 0x89, 0xef]

theorem p12_0 : ∀ feat, Dec feat p12 0 (FV7z.mk .mov 64 [gr 64 6, .mem (mg (some 4) none 1 24 64)] 5) := by dec_rfl
theorem p12_5 : ∀ feat, Dec feat p12 5 (FV7z.mk .mov 64 [gr 64 7, Src.opd 64 (.r 5)] 3) := by dec_rfl

/-- What the stretch does. -/
def o12 : List Op := [
  Op.ld 64 6 (some 4) none 1 24,
  Op.mov 64 7 (.r 5)]

theorem b12 (prof : Profile) : Blk prof p12 0 8 o12 :=
  .cons (p12_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p12_5 _) (OpI.mov (.r 5) (.inr rfl)) (by decide) <|
  .nil 8

def j8 : List Byte := [0xeb, 0xc6]
theorem j8_0 : ∀ feat, Dec feat j8 0 (FV7z.mk .jmp 64 [.rel 18446744073709551558] 2) := by dec_rfl

end FV7z.Gdp
