import FV7z.Lemmas.Sp
import FV7z.Lemmas.BlkOps10
import FV7z.Lemmas.BlkOps2
/-!
# The stretches of straight-line code of `getenv` (PLAN.md G3, startup)

Each distinct stretch between labels and jumps (`p*`, 10 of them) and each distinct jump (`j*`, 9) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.Genv
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The stretch at `0`. -/
def p0 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0x41, 0x57, 0x41, 0x56, 0x41, 0x55, 0x41, 0x54, 0x55, 0x53, 0x48, 0x83,
  0xec, 0x08, 0x48, 0x8b, 0x1d, 0x0f, 0x17, 0x18, 0x00, 0x48, 0x85, 0xdb]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem p0_4 : ∀ feat, Dec feat p0 4 (FV7z.mk .push 64 [gr 64 15] 2) := by dec_rfl
theorem p0_6 : ∀ feat, Dec feat p0 6 (FV7z.mk .push 64 [gr 64 14] 2) := by dec_rfl
theorem p0_8 : ∀ feat, Dec feat p0 8 (FV7z.mk .push 64 [gr 64 13] 2) := by dec_rfl
theorem p0_10 : ∀ feat, Dec feat p0 10 (FV7z.mk .push 64 [gr 64 12] 2) := by dec_rfl
theorem p0_12 : ∀ feat, Dec feat p0 12 (FV7z.mk .push 64 [gr 64 5] 1) := by dec_rfl
theorem p0_13 : ∀ feat, Dec feat p0 13 (FV7z.mk .push 64 [gr 64 3] 1) := by dec_rfl
theorem p0_14 : ∀ feat, Dec feat p0 14 (FV7z.mk .sub 64 [gr 64 4, Src.opd 64 (.i 8)] 4) := by dec_rfl
theorem p0_18 : ∀ feat, Dec feat p0 18 (FV7z.mk .mov 64 [gr 64 3, .mem (mrip 1578767 64)] 7) := by dec_rfl
theorem p0_25 : ∀ feat, Dec feat p0 25 (FV7z.mk .test 64 [gr 64 3, Src.opd 64 (.r 3)] 3) := by dec_rfl

/-- What the stretch does. -/
def o0 : List Op := [
  Op.nop,
  Op.push 15,
  Op.push 14,
  Op.push 13,
  Op.push 12,
  Op.push 5,
  Op.push 3,
  Op.sub 64 4 (.i 8),
  Op.lda 64 3 8013720,
  Op.test 64 3 (.r 3)]

theorem b0 (prof : Profile) : BlkA prof p0 (0x623070 : Addr) 0 28 o0 :=
  .cons (p0_0 _) ((OpI.endbr).at _) (by decide) <|
  .cons (p0_4 _) ((OpI.push).at _) (by decide) <|
  .cons (p0_6 _) ((OpI.push).at _) (by decide) <|
  .cons (p0_8 _) ((OpI.push).at _) (by decide) <|
  .cons (p0_10 _) ((OpI.push).at _) (by decide) <|
  .cons (p0_12 _) ((OpI.push).at _) (by decide) <|
  .cons (p0_13 _) ((OpI.push).at _) (by decide) <|
  .cons (p0_14 _) ((OpI.sub (.i 8) (.inr rfl)).at _) (by decide) <|
  .cons (p0_18 _) (OpIA.ld_rip (.inr rfl) (by decide)) (by decide) <|
  .cons (p0_25 _) ((OpI.test (.r 3) (.inr rfl)).at _) (by decide) <|
  .nil 28

def j0 : List Byte := [0x0f, 0x84, 0xae, 0x00, 0x00, 0x00]
theorem j0_0 : ∀ feat, Dec feat j0 0 (FV7z.mk (.jcc 4) 64 [.rel 174] 6) := by dec_rfl

/-- The stretch at `34`. -/
def p1 : List Byte := [
  0x0f, 0xb6, 0x07, 0x49, 0x89, 0xfd, 0x84, 0xc0]

theorem p1_0 : ∀ feat, Dec feat p1 0 (FV7z.mk .movzx 32 [gr 32 0, .mem (mg (some 7) none 1 0 8)] 3) := by dec_rfl
theorem p1_3 : ∀ feat, Dec feat p1 3 (FV7z.mk .mov 64 [gr 64 13, Src.opd 64 (.r 7)] 3) := by dec_rfl
theorem p1_6 : ∀ feat, Dec feat p1 6 (FV7z.mk .test 8 [gr 8 0, Src.opd 8 (.r 0)] 2) := by dec_rfl

/-- What the stretch does. -/
def o1 : List Op := [
  Op.ldzx 8 0 (some 7) none 1 0,
  Op.mov 64 13 (.r 7),
  Op.test 8 0 (.r 0)]

theorem b1 (prof : Profile) : Blk prof p1 0 8 o1 :=
  .cons (p1_0 _) (OpI.ldzx (.inl rfl)) (by decide) <|
  .cons (p1_3 _) (OpI.mov (.r 7) (.inr rfl)) (by decide) <|
  .cons (p1_6 _) (OpI.test8 (.r 0)) (by decide) <|
  .nil 8

def j1 : List Byte := [0x0f, 0x84, 0xa0, 0x00, 0x00, 0x00]
theorem j1_0 : ∀ feat, Dec feat j1 0 (FV7z.mk (.jcc 4) 64 [.rel 160] 6) := by dec_rfl

/-- The stretch at `48`. -/
def p2 : List Byte := [
  0x80, 0x7f, 0x01, 0x00, 0x4c, 0x8b, 0x23]

theorem p2_0 : ∀ feat, Dec feat p2 0 (FV7z.mk .cmp 8 [.mem (mg (some 7) none 1 1 8), .imm 8 0] 4) := by dec_rfl
theorem p2_4 : ∀ feat, Dec feat p2 4 (FV7z.mk .mov 64 [gr 64 12, .mem (mg (some 3) none 1 0 64)] 3) := by dec_rfl

/-- What the stretch does. -/
def o2 : List Op := [
  Op.cmpmi 8 (some 7) none 1 1 0,
  Op.ld 64 12 (some 3) none 1 0]

theorem b2 (prof : Profile) : Blk prof p2 0 7 o2 :=
  .cons (p2_0 _) (OpI.cmpmi (.inl rfl)) (by decide) <|
  .cons (p2_4 _) (OpI.ld (.inr rfl)) (by decide) <|
  .nil 7

def j2 : List Byte := [0x75, 0x3f]
theorem j2_0 : ∀ feat, Dec feat j2 0 (FV7z.mk (.jcc 5) 64 [.rel 63] 2) := by dec_rfl

/-- The stretch at `96`. -/
def p3 : List Byte := [
  0x48, 0x83, 0xc4, 0x08, 0x4c, 0x89, 0xe0, 0x5b, 0x5d, 0x41, 0x5c, 0x41, 0x5d, 0x41, 0x5e, 0x41,
  0x5f]

theorem p3_0 : ∀ feat, Dec feat p3 0 (FV7z.mk .add 64 [gr 64 4, Src.opd 64 (.i 8)] 4) := by dec_rfl
theorem p3_4 : ∀ feat, Dec feat p3 4 (FV7z.mk .mov 64 [gr 64 0, Src.opd 64 (.r 12)] 3) := by dec_rfl
theorem p3_7 : ∀ feat, Dec feat p3 7 (FV7z.mk .pop 64 [gr 64 3] 1) := by dec_rfl
theorem p3_8 : ∀ feat, Dec feat p3 8 (FV7z.mk .pop 64 [gr 64 5] 1) := by dec_rfl
theorem p3_9 : ∀ feat, Dec feat p3 9 (FV7z.mk .pop 64 [gr 64 12] 2) := by dec_rfl
theorem p3_11 : ∀ feat, Dec feat p3 11 (FV7z.mk .pop 64 [gr 64 13] 2) := by dec_rfl
theorem p3_13 : ∀ feat, Dec feat p3 13 (FV7z.mk .pop 64 [gr 64 14] 2) := by dec_rfl
theorem p3_15 : ∀ feat, Dec feat p3 15 (FV7z.mk .pop 64 [gr 64 15] 2) := by dec_rfl

/-- What the stretch does. -/
def o3 : List Op := [
  Op.add 64 4 (.i 8),
  Op.mov 64 0 (.r 12),
  Op.pop 3,
  Op.pop 5,
  Op.pop 12,
  Op.pop 13,
  Op.pop 14,
  Op.pop 15]

theorem b3 (prof : Profile) : Blk prof p3 0 17 o3 :=
  .cons (p3_0 _) (OpI.add (.i 8) (.inr rfl)) (by decide) <|
  .cons (p3_4 _) (OpI.mov (.r 12) (.inr rfl)) (by decide) <|
  .cons (p3_7 _) (OpI.pop) (by decide) <|
  .cons (p3_8 _) (OpI.pop) (by decide) <|
  .cons (p3_9 _) (OpI.pop) (by decide) <|
  .cons (p3_11 _) (OpI.pop) (by decide) <|
  .cons (p3_13 _) (OpI.pop) (by decide) <|
  .cons (p3_15 _) (OpI.pop) (by decide) <|
  .nil 17

/-- The stretch at `125`. -/
def p4 : List Byte := [
  0x49, 0x83, 0xc5, 0x02, 0x41, 0x0f, 0xb7, 0x6d, 0xfe, 0x49, 0x89, 0xc6, 0x4c, 0x8d, 0x78, 0xfe,
  0x4d, 0x85, 0xe4]

theorem p4_0 : ∀ feat, Dec feat p4 0 (FV7z.mk .add 64 [gr 64 13, Src.opd 64 (.i 2)] 4) := by dec_rfl
theorem p4_4 : ∀ feat, Dec feat p4 4 (FV7z.mk .movzx 32 [gr 32 5, .mem (mg (some 13) none 1 18446744073709551614 16)] 5) := by dec_rfl
theorem p4_9 : ∀ feat, Dec feat p4 9 (FV7z.mk .mov 64 [gr 64 14, Src.opd 64 (.r 0)] 3) := by dec_rfl
theorem p4_12 : ∀ feat, Dec feat p4 12 (FV7z.mk .lea 64 [gr 64 15, .mem (mg (some 0) none 1 18446744073709551614 0)] 4) := by dec_rfl
theorem p4_16 : ∀ feat, Dec feat p4 16 (FV7z.mk .test 64 [gr 64 12, Src.opd 64 (.r 12)] 3) := by dec_rfl

/-- What the stretch does. -/
def o4 : List Op := [
  Op.add 64 13 (.i 2),
  Op.ldzx 16 5 (some 13) none 1 18446744073709551614,
  Op.mov 64 14 (.r 0),
  Op.lea 64 15 (some 0) none 1 18446744073709551614,
  Op.test 64 12 (.r 12)]

theorem b4 (prof : Profile) : Blk prof p4 0 19 o4 :=
  .cons (p4_0 _) (OpI.add (.i 2) (.inr rfl)) (by decide) <|
  .cons (p4_4 _) (OpI.ldzx (.inr rfl)) (by decide) <|
  .cons (p4_9 _) (OpI.mov (.r 0) (.inr rfl)) (by decide) <|
  .cons (p4_12 _) (OpI.lea (.inr rfl)) (by decide) <|
  .cons (p4_16 _) (OpI.test (.r 12) (.inr rfl)) (by decide) <|
  .nil 19

def j3 : List Byte := [0x75, 0x13]
theorem j3_0 : ∀ feat, Dec feat j3 0 (FV7z.mk (.jcc 5) 64 [.rel 19] 2) := by dec_rfl

def j4 : List Byte := [0xeb, 0xcc]
theorem j4_0 : ∀ feat, Dec feat j4 0 (FV7z.mk .jmp 64 [.rel 18446744073709551564] 2) := by dec_rfl

/-- The stretch at `152`. -/
def p5 : List Byte := [
  0x4c, 0x8b, 0x63, 0x08, 0x48, 0x83, 0xc3, 0x08, 0x4d, 0x85, 0xe4]

theorem p5_0 : ∀ feat, Dec feat p5 0 (FV7z.mk .mov 64 [gr 64 12, .mem (mg (some 3) none 1 8 64)] 4) := by dec_rfl
theorem p5_4 : ∀ feat, Dec feat p5 4 (FV7z.mk .add 64 [gr 64 3, Src.opd 64 (.i 8)] 4) := by dec_rfl
theorem p5_8 : ∀ feat, Dec feat p5 8 (FV7z.mk .test 64 [gr 64 12, Src.opd 64 (.r 12)] 3) := by dec_rfl

/-- What the stretch does. -/
def o5 : List Op := [
  Op.ld 64 12 (some 3) none 1 8,
  Op.add 64 3 (.i 8),
  Op.test 64 12 (.r 12)]

theorem b5 (prof : Profile) : Blk prof p5 0 11 o5 :=
  .cons (p5_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p5_4 _) (OpI.add (.i 8) (.inr rfl)) (by decide) <|
  .cons (p5_8 _) (OpI.test (.r 12) (.inr rfl)) (by decide) <|
  .nil 11

def j5 : List Byte := [0x74, 0xbb]
theorem j5_0 : ∀ feat, Dec feat j5 0 (FV7z.mk (.jcc 4) 64 [.rel 18446744073709551547] 2) := by dec_rfl

/-- The stretch at `165`. -/
def p6 : List Byte := [
  0x66, 0x41, 0x3b, 0x2c, 0x24]

theorem p6_0 : ∀ feat, Dec feat p6 0 (FV7z.mk .cmp 16 [gr 16 5, .mem (mg (some 12) none 1 0 16)] 5) := by dec_rfl

/-- What the stretch does. -/
def o6 : List Op := [
  Op.cmpm 16 5 (some 12) none 1 0]

theorem b6 (prof : Profile) : Blk prof p6 0 5 o6 :=
  .cons (p6_0 _) (OpI.cmpm16) (by decide) <|
  .nil 5

def j6 : List Byte := [0x75, 0xec]
theorem j6_0 : ∀ feat, Dec feat j6 0 (FV7z.mk (.jcc 5) 64 [.rel 18446744073709551596] 2) := by dec_rfl

/-- The stretch at `172`. -/
def p7 : List Byte := [
  0x49, 0x8d, 0x7c, 0x24, 0x02, 0x4c, 0x89, 0xfa, 0x4c, 0x89, 0xee]

theorem p7_0 : ∀ feat, Dec feat p7 0 (FV7z.mk .lea 64 [gr 64 7, .mem (mg (some 12) none 1 2 0)] 5) := by dec_rfl
theorem p7_5 : ∀ feat, Dec feat p7 5 (FV7z.mk .mov 64 [gr 64 2, Src.opd 64 (.r 15)] 3) := by dec_rfl
theorem p7_8 : ∀ feat, Dec feat p7 8 (FV7z.mk .mov 64 [gr 64 6, Src.opd 64 (.r 13)] 3) := by dec_rfl

/-- What the stretch does. -/
def o7 : List Op := [
  Op.lea 64 7 (some 12) none 1 2,
  Op.mov 64 2 (.r 15),
  Op.mov 64 6 (.r 13)]

theorem b7 (prof : Profile) : Blk prof p7 0 11 o7 :=
  .cons (p7_0 _) (OpI.lea (.inr rfl)) (by decide) <|
  .cons (p7_5 _) (OpI.mov (.r 15) (.inr rfl)) (by decide) <|
  .cons (p7_8 _) (OpI.mov (.r 13) (.inr rfl)) (by decide) <|
  .nil 11

/-- The stretch at `188`. -/
def p8 : List Byte := [
  0x85, 0xc0]

theorem p8_0 : ∀ feat, Dec feat p8 0 (FV7z.mk .test 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl

/-- What the stretch does. -/
def o8 : List Op := [
  Op.test 32 0 (.r 0)]

theorem b8 (prof : Profile) : Blk prof p8 0 2 o8 :=
  .cons (p8_0 _) (OpI.test (.r 0) (.inl rfl)) (by decide) <|
  .nil 2

def j7 : List Byte := [0x75, 0xd8]
theorem j7_0 : ∀ feat, Dec feat j7 0 (FV7z.mk (.jcc 5) 64 [.rel 18446744073709551576] 2) := by dec_rfl

/-- The stretch at `192`. -/
def p9 : List Byte := [
  0x43, 0x80, 0x3c, 0x34, 0x3d]

theorem p9_0 : ∀ feat, Dec feat p9 0 (FV7z.mk .cmp 8 [.mem (mg (some 12) (some 14) 1 0 8), .imm 8 61] 5) := by dec_rfl

/-- What the stretch does. -/
def o9 : List Op := [
  Op.cmpmi 8 (some 12) (some 14) 1 0 61]

theorem b9 (prof : Profile) : Blk prof p9 0 5 o9 :=
  .cons (p9_0 _) (OpI.cmpmi (.inl rfl)) (by decide) <|
  .nil 5

def j8 : List Byte := [0x75, 0xd1]
theorem j8_0 : ∀ feat, Dec feat j8 0 (FV7z.mk (.jcc 5) 64 [.rel 18446744073709551569] 2) := by dec_rfl

end FV7z.Genv
