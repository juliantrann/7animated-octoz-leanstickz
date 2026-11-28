import FV7z.Lemmas.SpFs
import FV7z.Lemmas.BlkOps6
import FV7z.Lemmas.BlkOps2
/-!
# The stretches of straight-line code of `GetDefaultName2` (PLAN.md §M, M1)

Each distinct stretch between labels and jumps (`p*`, 17 of them) and each distinct jump (`j*`, 10) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.Dfn
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The stretch at `0`. -/
def p0 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0x41, 0x57, 0x41, 0x56, 0x41, 0x55, 0x49, 0x89, 0xcd, 0x41, 0x54, 0x49,
  0x89, 0xfc, 0x55, 0x48, 0x89, 0xf5, 0x48, 0x83, 0xec, 0x20, 0x8b, 0x4a, 0x08, 0x64, 0x48, 0x8b,
  0x04, 0x25, 0x28, 0x00, 0x00, 0x00, 0x48, 0x89, 0x44, 0x24, 0x18, 0x31, 0xc0, 0x8b, 0x46, 0x08,
  0x8d, 0x71, 0x01, 0x39, 0xf0]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem p0_4 : ∀ feat, Dec feat p0 4 (FV7z.mk .push 64 [gr 64 15] 2) := by dec_rfl
theorem p0_6 : ∀ feat, Dec feat p0 6 (FV7z.mk .push 64 [gr 64 14] 2) := by dec_rfl
theorem p0_8 : ∀ feat, Dec feat p0 8 (FV7z.mk .push 64 [gr 64 13] 2) := by dec_rfl
theorem p0_10 : ∀ feat, Dec feat p0 10 (FV7z.mk .mov 64 [gr 64 13, Src.opd 64 (.r 1)] 3) := by dec_rfl
theorem p0_13 : ∀ feat, Dec feat p0 13 (FV7z.mk .push 64 [gr 64 12] 2) := by dec_rfl
theorem p0_15 : ∀ feat, Dec feat p0 15 (FV7z.mk .mov 64 [gr 64 12, Src.opd 64 (.r 7)] 3) := by dec_rfl
theorem p0_18 : ∀ feat, Dec feat p0 18 (FV7z.mk .push 64 [gr 64 5] 1) := by dec_rfl
theorem p0_19 : ∀ feat, Dec feat p0 19 (FV7z.mk .mov 64 [gr 64 5, Src.opd 64 (.r 6)] 3) := by dec_rfl
theorem p0_22 : ∀ feat, Dec feat p0 22 (FV7z.mk .sub 64 [gr 64 4, Src.opd 64 (.i 32)] 4) := by dec_rfl
theorem p0_26 : ∀ feat, Dec feat p0 26 (FV7z.mk .mov 32 [gr 32 1, .mem (mg (some 2) none 1 8 32)] 3) := by dec_rfl
theorem p0_29 : ∀ feat, Dec feat p0 29 (FV7z.mk .mov 64 [gr 64 0, .mem (mf none none 1 40 64)] 9) := by dec_rfl
theorem p0_38 : ∀ feat, Dec feat p0 38 (FV7z.mk .mov 64 [.mem (mg (some 4) none 1 24 64), gr 64 0] 5) := by dec_rfl
theorem p0_43 : ∀ feat, Dec feat p0 43 (FV7z.mk .xor 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl
theorem p0_45 : ∀ feat, Dec feat p0 45 (FV7z.mk .mov 32 [gr 32 0, .mem (mg (some 6) none 1 8 32)] 3) := by dec_rfl
theorem p0_48 : ∀ feat, Dec feat p0 48 (FV7z.mk .lea 32 [gr 32 6, .mem (mg (some 1) none 1 1 0)] 3) := by dec_rfl
theorem p0_51 : ∀ feat, Dec feat p0 51 (FV7z.mk .cmp 32 [gr 32 0, Src.opd 32 (.r 6)] 2) := by dec_rfl

/-- What the stretch does. -/
def o0 (fb : Addr) : List Op := [
  Op.nop,
  Op.push 15,
  Op.push 14,
  Op.push 13,
  Op.mov 64 13 (.r 1),
  Op.push 12,
  Op.mov 64 12 (.r 7),
  Op.push 5,
  Op.mov 64 5 (.r 6),
  Op.sub 64 4 (.i 32),
  Op.ld 32 1 (some 2) none 1 8,
  Op.ldf fb 64 0 none none 1 40,
  Op.st 64 (some 4) none 1 24 0,
  Op.xor 32 0 (.r 0),
  Op.ld 32 0 (some 6) none 1 8,
  Op.lea 32 6 (some 1) none 1 1,
  Op.cmp 32 0 (.r 6)]

theorem b0 (prof : Profile) (fb : Addr) : BlkF prof p0 (0x5bfdd0 : Addr) fb 0 53 (o0 fb) :=
  .cons (p0_0 _) (((OpI.endbr).at _).fs _) (by decide) <|
  .cons (p0_4 _) (((OpI.push).at _).fs _) (by decide) <|
  .cons (p0_6 _) (((OpI.push).at _).fs _) (by decide) <|
  .cons (p0_8 _) (((OpI.push).at _).fs _) (by decide) <|
  .cons (p0_10 _) (((OpI.mov (.r 1) (.inr rfl)).at _).fs _) (by decide) <|
  .cons (p0_13 _) (((OpI.push).at _).fs _) (by decide) <|
  .cons (p0_15 _) (((OpI.mov (.r 7) (.inr rfl)).at _).fs _) (by decide) <|
  .cons (p0_18 _) (((OpI.push).at _).fs _) (by decide) <|
  .cons (p0_19 _) (((OpI.mov (.r 6) (.inr rfl)).at _).fs _) (by decide) <|
  .cons (p0_22 _) (((OpI.sub (.i 32) (.inr rfl)).at _).fs _) (by decide) <|
  .cons (p0_26 _) (((OpI.ld (.inl rfl)).at _).fs _) (by decide) <|
  .cons (p0_29 _) (OpIF.ldf (.inr rfl)) (by decide) <|
  .cons (p0_38 _) (((OpI.st (.inr (.inr (.inr rfl)))).at _).fs _) (by decide) <|
  .cons (p0_43 _) (((OpI.xor (.r 0) (.inl rfl)).at _).fs _) (by decide) <|
  .cons (p0_45 _) (((OpI.ld (.inl rfl)).at _).fs _) (by decide) <|
  .cons (p0_48 _) (((OpI.lea (.inl rfl)).at _).fs _) (by decide) <|
  .cons (p0_51 _) (((OpI.cmp (.r 6) (.inl rfl)).at _).fs _) (by decide) <|
  .nil 53

def j0 : List Byte := [0x76, 0x16]
theorem j0_0 : ∀ feat, Dec feat j0 0 (FV7z.mk (.jcc 6) 64 [.rel 22] 2) := by dec_rfl

/-- The stretch at `55`. -/
def p1 : List Byte := [
  0x29, 0xc8, 0x48, 0x8b, 0x4d, 0x00, 0x8d, 0x70, 0xff, 0x83, 0x3c, 0xb1, 0x2e, 0x49, 0x89, 0xf6]

theorem p1_0 : ∀ feat, Dec feat p1 0 (FV7z.mk .sub 32 [gr 32 0, Src.opd 32 (.r 1)] 2) := by dec_rfl
theorem p1_2 : ∀ feat, Dec feat p1 2 (FV7z.mk .mov 64 [gr 64 1, .mem (mg (some 5) none 1 0 64)] 4) := by dec_rfl
theorem p1_6 : ∀ feat, Dec feat p1 6 (FV7z.mk .lea 32 [gr 32 6, .mem (mg (some 0) none 1 18446744073709551615 0)] 3) := by dec_rfl
theorem p1_9 : ∀ feat, Dec feat p1 9 (FV7z.mk .cmp 32 [.mem (mg (some 1) (some 6) 4 0 32), .imm 32 46] 4) := by dec_rfl
theorem p1_13 : ∀ feat, Dec feat p1 13 (FV7z.mk .mov 64 [gr 64 14, Src.opd 64 (.r 6)] 3) := by dec_rfl

/-- What the stretch does. -/
def o1 : List Op := [
  Op.sub 32 0 (.r 1),
  Op.ld 64 1 (some 5) none 1 0,
  Op.lea 32 6 (some 0) none 1 18446744073709551615,
  Op.cmpmi 32 (some 1) (some 6) 4 0 46,
  Op.mov 64 14 (.r 6)]

theorem b1 (prof : Profile) : Blk prof p1 0 16 o1 :=
  .cons (p1_0 _) (OpI.sub (.r 1) (.inl rfl)) (by decide) <|
  .cons (p1_2 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p1_6 _) (OpI.lea (.inl rfl)) (by decide) <|
  .cons (p1_9 _) (OpI.cmpmi (.inr rfl)) (by decide) <|
  .cons (p1_13 _) (OpI.mov (.r 6) (.inr rfl)) (by decide) <|
  .nil 16

def j1 : List Byte := [0x0f, 0x84, 0xa3, 0x00, 0x00, 0x00]
theorem j1_0 : ∀ feat, Dec feat j1 0 (FV7z.mk (.jcc 4) 64 [.rel 163] 6) := by dec_rfl

/-- The stretch at `77`. -/
def p2 : List Byte := [
  0xbe, 0x2e, 0x00, 0x00, 0x00, 0x48, 0x89, 0xef]

theorem p2_0 : ∀ feat, Dec feat p2 0 (FV7z.mk .mov 32 [gr 32 6, Src.opd 32 (.i 46)] 5) := by dec_rfl
theorem p2_5 : ∀ feat, Dec feat p2 5 (FV7z.mk .mov 64 [gr 64 7, Src.opd 64 (.r 5)] 3) := by dec_rfl

/-- What the stretch does. -/
def o2 : List Op := [
  Op.mov 32 6 (.i 46),
  Op.mov 64 7 (.r 5)]

theorem b2 (prof : Profile) : Blk prof p2 0 8 o2 :=
  .cons (p2_0 _) (OpI.mov (.i 46) (.inl rfl)) (by decide) <|
  .cons (p2_5 _) (OpI.mov (.r 5) (.inr rfl)) (by decide) <|
  .nil 8

/-- The stretch at `90`. -/
def p3 : List Byte := [
  0x89, 0xc6, 0x85, 0xc0]

theorem p3_0 : ∀ feat, Dec feat p3 0 (FV7z.mk .mov 32 [gr 32 6, Src.opd 32 (.r 0)] 2) := by dec_rfl
theorem p3_2 : ∀ feat, Dec feat p3 2 (FV7z.mk .test 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl

/-- What the stretch does. -/
def o3 : List Op := [
  Op.mov 32 6 (.r 0),
  Op.test 32 0 (.r 0)]

theorem b3 (prof : Profile) : Blk prof p3 0 4 o3 :=
  .cons (p3_0 _) (OpI.mov (.r 0) (.inl rfl)) (by decide) <|
  .cons (p3_2 _) (OpI.test (.r 0) (.inl rfl)) (by decide) <|
  .nil 4

def j2 : List Byte := [0x7f, 0x60]
theorem j2_0 : ∀ feat, Dec feat j2 0 (FV7z.mk (.jcc 15) 64 [.rel 96] 2) := by dec_rfl

/-- The stretch at `96`. -/
def p4 : List Byte := [
  0x41, 0x8b, 0x45, 0x08, 0x85, 0xc0]

theorem p4_0 : ∀ feat, Dec feat p4 0 (FV7z.mk .mov 32 [gr 32 0, .mem (mg (some 13) none 1 8 32)] 4) := by dec_rfl
theorem p4_4 : ∀ feat, Dec feat p4 4 (FV7z.mk .test 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl

/-- What the stretch does. -/
def o4 : List Op := [
  Op.ld 32 0 (some 13) none 1 8,
  Op.test 32 0 (.r 0)]

theorem b4 (prof : Profile) : Blk prof p4 0 6 o4 :=
  .cons (p4_0 _) (OpI.ld (.inl rfl)) (by decide) <|
  .cons (p4_4 _) (OpI.test (.r 0) (.inl rfl)) (by decide) <|
  .nil 6

def j3 : List Byte := [0x74, 0x40]
theorem j3_0 : ∀ feat, Dec feat j3 0 (FV7z.mk (.jcc 4) 64 [.rel 64] 2) := by dec_rfl

/-- The stretch at `104`. -/
def p5 : List Byte := [
  0x4c, 0x89, 0xea, 0x48, 0x89, 0xee, 0x4c, 0x89, 0xe7]

theorem p5_0 : ∀ feat, Dec feat p5 0 (FV7z.mk .mov 64 [gr 64 2, Src.opd 64 (.r 13)] 3) := by dec_rfl
theorem p5_3 : ∀ feat, Dec feat p5 3 (FV7z.mk .mov 64 [gr 64 6, Src.opd 64 (.r 5)] 3) := by dec_rfl
theorem p5_6 : ∀ feat, Dec feat p5 6 (FV7z.mk .mov 64 [gr 64 7, Src.opd 64 (.r 12)] 3) := by dec_rfl

/-- What the stretch does. -/
def o5 : List Op := [
  Op.mov 64 2 (.r 13),
  Op.mov 64 6 (.r 5),
  Op.mov 64 7 (.r 12)]

theorem b5 (prof : Profile) : Blk prof p5 0 9 o5 :=
  .cons (p5_0 _) (OpI.mov (.r 13) (.inr rfl)) (by decide) <|
  .cons (p5_3 _) (OpI.mov (.r 5) (.inr rfl)) (by decide) <|
  .cons (p5_6 _) (OpI.mov (.r 12) (.inr rfl)) (by decide) <|
  .nil 9

/-- The stretch at `118`. -/
def p6 : List Byte := [
  0x4c, 0x89, 0xe7]

theorem p6_0 : ∀ feat, Dec feat p6 0 (FV7z.mk .mov 64 [gr 64 7, Src.opd 64 (.r 12)] 3) := by dec_rfl

/-- What the stretch does. -/
def o6 : List Op := [
  Op.mov 64 7 (.r 12)]

theorem b6 (prof : Profile) : Blk prof p6 0 3 o6 :=
  .cons (p6_0 _) (OpI.mov (.r 12) (.inr rfl)) (by decide) <|
  .nil 3

/-- The stretch at `126`. -/
def p7 : List Byte := [
  0x48, 0x8b, 0x44, 0x24, 0x18, 0x64, 0x48, 0x33, 0x04, 0x25, 0x28, 0x00, 0x00, 0x00]

theorem p7_0 : ∀ feat, Dec feat p7 0 (FV7z.mk .mov 64 [gr 64 0, .mem (mg (some 4) none 1 24 64)] 5) := by dec_rfl
theorem p7_5 : ∀ feat, Dec feat p7 5 (FV7z.mk .xor 64 [gr 64 0, .mem (mf none none 1 40 64)] 9) := by dec_rfl

/-- What the stretch does. -/
def o7 (fb : Addr) : List Op := [
  Op.ld 64 0 (some 4) none 1 24,
  Op.xormf fb 64 0 none none 1 40]

theorem b7 (prof : Profile) (fb : Addr) : BlkF prof p7 (0x5bfe4e : Addr) fb 0 14 (o7 fb) :=
  .cons (p7_0 _) (((OpI.ld (.inr rfl)).at _).fs _) (by decide) <|
  .cons (p7_5 _) (OpIF.xormf (.inr rfl)) (by decide) <|
  .nil 14

def j4 : List Byte := [0x0f, 0x85, 0x93, 0x00, 0x00, 0x00]
theorem j4_0 : ∀ feat, Dec feat j4 0 (FV7z.mk (.jcc 5) 64 [.rel 147] 6) := by dec_rfl

/-- The stretch at `146`. -/
def p8 : List Byte := [
  0x48, 0x83, 0xc4, 0x20, 0x4c, 0x89, 0xe0, 0x5d, 0x41, 0x5c, 0x41, 0x5d, 0x41, 0x5e, 0x41, 0x5f]

theorem p8_0 : ∀ feat, Dec feat p8 0 (FV7z.mk .add 64 [gr 64 4, Src.opd 64 (.i 32)] 4) := by dec_rfl
theorem p8_4 : ∀ feat, Dec feat p8 4 (FV7z.mk .mov 64 [gr 64 0, Src.opd 64 (.r 12)] 3) := by dec_rfl
theorem p8_7 : ∀ feat, Dec feat p8 7 (FV7z.mk .pop 64 [gr 64 5] 1) := by dec_rfl
theorem p8_8 : ∀ feat, Dec feat p8 8 (FV7z.mk .pop 64 [gr 64 12] 2) := by dec_rfl
theorem p8_10 : ∀ feat, Dec feat p8 10 (FV7z.mk .pop 64 [gr 64 13] 2) := by dec_rfl
theorem p8_12 : ∀ feat, Dec feat p8 12 (FV7z.mk .pop 64 [gr 64 14] 2) := by dec_rfl
theorem p8_14 : ∀ feat, Dec feat p8 14 (FV7z.mk .pop 64 [gr 64 15] 2) := by dec_rfl

/-- What the stretch does. -/
def o8 : List Op := [
  Op.add 64 4 (.i 32),
  Op.mov 64 0 (.r 12),
  Op.pop 5,
  Op.pop 12,
  Op.pop 13,
  Op.pop 14,
  Op.pop 15]

theorem b8 (prof : Profile) : Blk prof p8 0 16 o8 :=
  .cons (p8_0 _) (OpI.add (.i 32) (.inr rfl)) (by decide) <|
  .cons (p8_4 _) (OpI.mov (.r 12) (.inr rfl)) (by decide) <|
  .cons (p8_7 _) (OpI.pop) (by decide) <|
  .cons (p8_8 _) (OpI.pop) (by decide) <|
  .cons (p8_10 _) (OpI.pop) (by decide) <|
  .cons (p8_12 _) (OpI.pop) (by decide) <|
  .cons (p8_14 _) (OpI.pop) (by decide) <|
  .nil 16

/-- The stretch at `168`. -/
def p9 : List Byte := [
  0xba, 0x7e, 0x00, 0x00, 0x00, 0x48, 0x89, 0xee, 0x4c, 0x89, 0xe7]

theorem p9_0 : ∀ feat, Dec feat p9 0 (FV7z.mk .mov 32 [gr 32 2, Src.opd 32 (.i 126)] 5) := by dec_rfl
theorem p9_5 : ∀ feat, Dec feat p9 5 (FV7z.mk .mov 64 [gr 64 6, Src.opd 64 (.r 5)] 3) := by dec_rfl
theorem p9_8 : ∀ feat, Dec feat p9 8 (FV7z.mk .mov 64 [gr 64 7, Src.opd 64 (.r 12)] 3) := by dec_rfl

/-- What the stretch does. -/
def o9 : List Op := [
  Op.mov 32 2 (.i 126),
  Op.mov 64 6 (.r 5),
  Op.mov 64 7 (.r 12)]

theorem b9 (prof : Profile) : Blk prof p9 0 11 o9 :=
  .cons (p9_0 _) (OpI.mov (.i 126) (.inl rfl)) (by decide) <|
  .cons (p9_5 _) (OpI.mov (.r 5) (.inr rfl)) (by decide) <|
  .cons (p9_8 _) (OpI.mov (.r 12) (.inr rfl)) (by decide) <|
  .nil 11

def j5 : List Byte := [0xeb, 0xbc]
theorem j5_0 : ∀ feat, Dec feat j5 0 (FV7z.mk .jmp 64 [.rel 18446744073709551548] 2) := by dec_rfl

/-- The stretch at `192`. -/
def p10 : List Byte := [
  0x49, 0x89, 0xe6, 0x48, 0x89, 0xea, 0x4c, 0x89, 0xf7]

theorem p10_0 : ∀ feat, Dec feat p10 0 (FV7z.mk .mov 64 [gr 64 14, Src.opd 64 (.r 4)] 3) := by dec_rfl
theorem p10_3 : ∀ feat, Dec feat p10 3 (FV7z.mk .mov 64 [gr 64 2, Src.opd 64 (.r 5)] 3) := by dec_rfl
theorem p10_6 : ∀ feat, Dec feat p10 6 (FV7z.mk .mov 64 [gr 64 7, Src.opd 64 (.r 14)] 3) := by dec_rfl

/-- What the stretch does. -/
def o10 : List Op := [
  Op.mov 64 14 (.r 4),
  Op.mov 64 2 (.r 5),
  Op.mov 64 7 (.r 14)]

theorem b10 (prof : Profile) : Blk prof p10 0 9 o10 :=
  .cons (p10_0 _) (OpI.mov (.r 4) (.inr rfl)) (by decide) <|
  .cons (p10_3 _) (OpI.mov (.r 5) (.inr rfl)) (by decide) <|
  .cons (p10_6 _) (OpI.mov (.r 14) (.inr rfl)) (by decide) <|
  .nil 9

/-- The stretch at `206`. -/
def p11 : List Byte := [
  0x4c, 0x89, 0xea, 0x4c, 0x89, 0xf6, 0x4c, 0x89, 0xe7]

theorem p11_0 : ∀ feat, Dec feat p11 0 (FV7z.mk .mov 64 [gr 64 2, Src.opd 64 (.r 13)] 3) := by dec_rfl
theorem p11_3 : ∀ feat, Dec feat p11 3 (FV7z.mk .mov 64 [gr 64 6, Src.opd 64 (.r 14)] 3) := by dec_rfl
theorem p11_6 : ∀ feat, Dec feat p11 6 (FV7z.mk .mov 64 [gr 64 7, Src.opd 64 (.r 12)] 3) := by dec_rfl

/-- What the stretch does. -/
def o11 : List Op := [
  Op.mov 64 2 (.r 13),
  Op.mov 64 6 (.r 14),
  Op.mov 64 7 (.r 12)]

theorem b11 (prof : Profile) : Blk prof p11 0 9 o11 :=
  .cons (p11_0 _) (OpI.mov (.r 13) (.inr rfl)) (by decide) <|
  .cons (p11_3 _) (OpI.mov (.r 14) (.inr rfl)) (by decide) <|
  .cons (p11_6 _) (OpI.mov (.r 12) (.inr rfl)) (by decide) <|
  .nil 9

/-- The stretch at `220`. -/
def p12 : List Byte := [
  0x48, 0x8b, 0x3c, 0x24, 0x48, 0x85, 0xff]

theorem p12_0 : ∀ feat, Dec feat p12 0 (FV7z.mk .mov 64 [gr 64 7, .mem (mg (some 4) none 1 0 64)] 4) := by dec_rfl
theorem p12_4 : ∀ feat, Dec feat p12 4 (FV7z.mk .test 64 [gr 64 7, Src.opd 64 (.r 7)] 3) := by dec_rfl

/-- What the stretch does. -/
def o12 : List Op := [
  Op.ld 64 7 (some 4) none 1 0,
  Op.test 64 7 (.r 7)]

theorem b12 (prof : Profile) : Blk prof p12 0 7 o12 :=
  .cons (p12_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p12_4 _) (OpI.test (.r 7) (.inr rfl)) (by decide) <|
  .nil 7

def j6 : List Byte := [0x74, 0x91]
theorem j6_0 : ∀ feat, Dec feat j6 0 (FV7z.mk (.jcc 4) 64 [.rel 18446744073709551505] 2) := by dec_rfl

def j7 : List Byte := [0xeb, 0x8a]
theorem j7_0 : ∀ feat, Dec feat j7 0 (FV7z.mk .jmp 64 [.rel 18446744073709551498] 2) := by dec_rfl

/-- The stretch at `240`. -/
def p13 : List Byte := [
  0x48, 0x8b, 0x3a, 0x48, 0x8d, 0x34, 0x81]

theorem p13_0 : ∀ feat, Dec feat p13 0 (FV7z.mk .mov 64 [gr 64 7, .mem (mg (some 2) none 1 0 64)] 3) := by dec_rfl
theorem p13_3 : ∀ feat, Dec feat p13 3 (FV7z.mk .lea 64 [gr 64 6, .mem (mg (some 1) (some 0) 4 0 0)] 4) := by dec_rfl

/-- What the stretch does. -/
def o13 : List Op := [
  Op.ld 64 7 (some 2) none 1 0,
  Op.lea 64 6 (some 1) (some 0) 4 0]

theorem b13 (prof : Profile) : Blk prof p13 0 7 o13 :=
  .cons (p13_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p13_3 _) (OpI.lea (.inr rfl)) (by decide) <|
  .nil 7

/-- The stretch at `252`. -/
def p14 : List Byte := [
  0x84, 0xc0]

theorem p14_0 : ∀ feat, Dec feat p14 0 (FV7z.mk .test 8 [gr 8 0, Src.opd 8 (.r 0)] 2) := by dec_rfl

/-- What the stretch does. -/
def o14 : List Op := [
  Op.test 8 0 (.r 0)]

theorem b14 (prof : Profile) : Blk prof p14 0 2 o14 :=
  .cons (p14_0 _) (OpI.test8 (.r 0)) (by decide) <|
  .nil 2

def j8 : List Byte := [0x0f, 0x84, 0x49, 0xff, 0xff, 0xff]
theorem j8_0 : ∀ feat, Dec feat j8 0 (FV7z.mk (.jcc 4) 64 [.rel 18446744073709551433] 6) := by dec_rfl

/-- The stretch at `260`. -/
def p15 : List Byte := [
  0x49, 0x89, 0xe7, 0x48, 0x89, 0xea, 0x44, 0x89, 0xf6, 0x4c, 0x89, 0xff]

theorem p15_0 : ∀ feat, Dec feat p15 0 (FV7z.mk .mov 64 [gr 64 15, Src.opd 64 (.r 4)] 3) := by dec_rfl
theorem p15_3 : ∀ feat, Dec feat p15 3 (FV7z.mk .mov 64 [gr 64 2, Src.opd 64 (.r 5)] 3) := by dec_rfl
theorem p15_6 : ∀ feat, Dec feat p15 6 (FV7z.mk .mov 32 [gr 32 6, Src.opd 32 (.r 14)] 3) := by dec_rfl
theorem p15_9 : ∀ feat, Dec feat p15 9 (FV7z.mk .mov 64 [gr 64 7, Src.opd 64 (.r 15)] 3) := by dec_rfl

/-- What the stretch does. -/
def o15 : List Op := [
  Op.mov 64 15 (.r 4),
  Op.mov 64 2 (.r 5),
  Op.mov 32 6 (.r 14),
  Op.mov 64 7 (.r 15)]

theorem b15 (prof : Profile) : Blk prof p15 0 12 o15 :=
  .cons (p15_0 _) (OpI.mov (.r 4) (.inr rfl)) (by decide) <|
  .cons (p15_3 _) (OpI.mov (.r 5) (.inr rfl)) (by decide) <|
  .cons (p15_6 _) (OpI.mov (.r 14) (.inl rfl)) (by decide) <|
  .cons (p15_9 _) (OpI.mov (.r 15) (.inr rfl)) (by decide) <|
  .nil 12

/-- The stretch at `277`. -/
def p16 : List Byte := [
  0x4c, 0x89, 0xea, 0x4c, 0x89, 0xfe, 0x4c, 0x89, 0xe7]

theorem p16_0 : ∀ feat, Dec feat p16 0 (FV7z.mk .mov 64 [gr 64 2, Src.opd 64 (.r 13)] 3) := by dec_rfl
theorem p16_3 : ∀ feat, Dec feat p16 3 (FV7z.mk .mov 64 [gr 64 6, Src.opd 64 (.r 15)] 3) := by dec_rfl
theorem p16_6 : ∀ feat, Dec feat p16 6 (FV7z.mk .mov 64 [gr 64 7, Src.opd 64 (.r 12)] 3) := by dec_rfl

/-- What the stretch does. -/
def o16 : List Op := [
  Op.mov 64 2 (.r 13),
  Op.mov 64 6 (.r 15),
  Op.mov 64 7 (.r 12)]

theorem b16 (prof : Profile) : Blk prof p16 0 9 o16 :=
  .cons (p16_0 _) (OpI.mov (.r 13) (.inr rfl)) (by decide) <|
  .cons (p16_3 _) (OpI.mov (.r 15) (.inr rfl)) (by decide) <|
  .cons (p16_6 _) (OpI.mov (.r 12) (.inr rfl)) (by decide) <|
  .nil 9

def j9 : List Byte := [0xeb, 0xb7]
theorem j9_0 : ∀ feat, Dec feat j9 0 (FV7z.mk .jmp 64 [.rel 18446744073709551543] 2) := by dec_rfl

end FV7z.Dfn
