import FV7z.Lemmas.Sp
import FV7z.Lemmas.BlkOps18
import FV7z.Lemmas.BlkOps14
import FV7z.Lemmas.BlkOps2
/-!
# The stretches of straight-line code of `find_module_idx` (PLAN.md §M, M1)

Each distinct stretch between labels and jumps (`p*`, 11 of them) and each distinct jump (`j*`, 4) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.Fmi
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The stretch at `0`. -/
def p0 : List Byte := [
  0x41, 0x57, 0x41, 0x56, 0x41, 0x55, 0x41, 0x54, 0x55, 0x53, 0x48, 0x83, 0xec, 0x28, 0x4c, 0x8b,
  0x35, 0x6b, 0x7d, 0x12, 0x00, 0x48, 0x89, 0x7c, 0x24, 0x10, 0x41, 0x0f, 0xb7, 0x46, 0x04, 0x45,
  0x0f, 0xb7, 0x66, 0x06, 0x48, 0x89, 0x74, 0x24, 0x18, 0x48, 0x89, 0x44, 0x24, 0x08]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .push 64 [gr 64 15] 2) := by dec_rfl
theorem p0_2 : ∀ feat, Dec feat p0 2 (FV7z.mk .push 64 [gr 64 14] 2) := by dec_rfl
theorem p0_4 : ∀ feat, Dec feat p0 4 (FV7z.mk .push 64 [gr 64 13] 2) := by dec_rfl
theorem p0_6 : ∀ feat, Dec feat p0 6 (FV7z.mk .push 64 [gr 64 12] 2) := by dec_rfl
theorem p0_8 : ∀ feat, Dec feat p0 8 (FV7z.mk .push 64 [gr 64 5] 1) := by dec_rfl
theorem p0_9 : ∀ feat, Dec feat p0 9 (FV7z.mk .push 64 [gr 64 3] 1) := by dec_rfl
theorem p0_10 : ∀ feat, Dec feat p0 10 (FV7z.mk .sub 64 [gr 64 4, Src.opd 64 (.i 40)] 4) := by dec_rfl
theorem p0_14 : ∀ feat, Dec feat p0 14 (FV7z.mk .mov 64 [gr 64 14, .mem (mrip 1211755 64)] 7) := by dec_rfl
theorem p0_21 : ∀ feat, Dec feat p0 21 (FV7z.mk .mov 64 [.mem (mg (some 4) none 1 16 64), gr 64 7] 5) := by dec_rfl
theorem p0_26 : ∀ feat, Dec feat p0 26 (FV7z.mk .movzx 32 [gr 32 0, .mem (mg (some 14) none 1 4 16)] 5) := by dec_rfl
theorem p0_31 : ∀ feat, Dec feat p0 31 (FV7z.mk .movzx 32 [gr 32 12, .mem (mg (some 14) none 1 6 16)] 5) := by dec_rfl
theorem p0_36 : ∀ feat, Dec feat p0 36 (FV7z.mk .mov 64 [.mem (mg (some 4) none 1 24 64), gr 64 6] 5) := by dec_rfl
theorem p0_41 : ∀ feat, Dec feat p0 41 (FV7z.mk .mov 64 [.mem (mg (some 4) none 1 8 64), gr 64 0] 5) := by dec_rfl

/-- What the stretch does. -/
def o0 : List Op := [
  Op.push 15,
  Op.push 14,
  Op.push 13,
  Op.push 12,
  Op.push 5,
  Op.push 3,
  Op.sub 64 4 (.i 40),
  Op.lda 64 14 8014768,
  Op.st 64 (some 4) none 1 16 7,
  Op.ldzx 16 0 (some 14) none 1 4,
  Op.ldzx 16 12 (some 14) none 1 6,
  Op.st 64 (some 4) none 1 24 6,
  Op.st 64 (some 4) none 1 8 0]

theorem b0 (prof : Profile) : BlkA prof p0 (0x67ce30 : Addr) 0 46 o0 :=
  .cons (p0_0 _) ((OpI.push).at _) (by decide) <|
  .cons (p0_2 _) ((OpI.push).at _) (by decide) <|
  .cons (p0_4 _) ((OpI.push).at _) (by decide) <|
  .cons (p0_6 _) ((OpI.push).at _) (by decide) <|
  .cons (p0_8 _) ((OpI.push).at _) (by decide) <|
  .cons (p0_9 _) ((OpI.push).at _) (by decide) <|
  .cons (p0_10 _) ((OpI.sub (.i 40) (.inr rfl)).at _) (by decide) <|
  .cons (p0_14 _) (OpIA.ld_rip (.inr rfl) (by decide)) (by decide) <|
  .cons (p0_21 _) ((OpI.st (.inr (.inr (.inr rfl)))).at _) (by decide) <|
  .cons (p0_26 _) ((OpI.ldzx (.inr rfl)).at _) (by decide) <|
  .cons (p0_31 _) ((OpI.ldzx (.inr rfl)).at _) (by decide) <|
  .cons (p0_36 _) ((OpI.st (.inr (.inr (.inr rfl)))).at _) (by decide) <|
  .cons (p0_41 _) ((OpI.st (.inr (.inr (.inr rfl)))).at _) (by decide) <|
  .nil 46

/-- The stretch at `51`. -/
def p1 : List Byte := [
  0x41, 0x0f, 0xb7, 0x5e, 0x08, 0x31, 0xd2, 0x8b, 0x3d, 0x38, 0x7d, 0x12, 0x00, 0x89, 0xc5]

theorem p1_0 : ∀ feat, Dec feat p1 0 (FV7z.mk .movzx 32 [gr 32 3, .mem (mg (some 14) none 1 8 16)] 5) := by dec_rfl
theorem p1_5 : ∀ feat, Dec feat p1 5 (FV7z.mk .xor 32 [gr 32 2, Src.opd 32 (.r 2)] 2) := by dec_rfl
theorem p1_7 : ∀ feat, Dec feat p1 7 (FV7z.mk .mov 32 [gr 32 7, .mem (mrip 1211704 32)] 6) := by dec_rfl
theorem p1_13 : ∀ feat, Dec feat p1 13 (FV7z.mk .mov 32 [gr 32 5, Src.opd 32 (.r 0)] 2) := by dec_rfl

/-- What the stretch does. -/
def o1 : List Op := [
  Op.ldzx 16 3 (some 14) none 1 8,
  Op.xor 32 2 (.r 2),
  Op.lda 32 7 8014760,
  Op.mov 32 5 (.r 0)]

theorem b1 (prof : Profile) : BlkA prof p1 (0x67ce63 : Addr) 0 15 o1 :=
  .cons (p1_0 _) ((OpI.ldzx (.inr rfl)).at _) (by decide) <|
  .cons (p1_5 _) ((OpI.xor (.r 2) (.inl rfl)).at _) (by decide) <|
  .cons (p1_7 _) (OpIA.ld_rip (.inl rfl) (by decide)) (by decide) <|
  .cons (p1_13 _) ((OpI.mov (.r 0) (.inl rfl)).at _) (by decide) <|
  .nil 15

/-- The stretch at `68`. -/
def p2 : List Byte := [
  0x8d, 0x73, 0xfe, 0x89, 0xe8, 0x41, 0x89, 0xd5, 0x31, 0xd2]

theorem p2_0 : ∀ feat, Dec feat p2 0 (FV7z.mk .lea 32 [gr 32 6, .mem (mg (some 3) none 1 18446744073709551614 0)] 3) := by dec_rfl
theorem p2_3 : ∀ feat, Dec feat p2 3 (FV7z.mk .mov 32 [gr 32 0, Src.opd 32 (.r 5)] 2) := by dec_rfl
theorem p2_5 : ∀ feat, Dec feat p2 5 (FV7z.mk .mov 32 [gr 32 13, Src.opd 32 (.r 2)] 3) := by dec_rfl
theorem p2_8 : ∀ feat, Dec feat p2 8 (FV7z.mk .xor 32 [gr 32 2, Src.opd 32 (.r 2)] 2) := by dec_rfl

/-- What the stretch does. -/
def o2 : List Op := [
  Op.lea 32 6 (some 3) none 1 18446744073709551614,
  Op.mov 32 0 (.r 5),
  Op.mov 32 13 (.r 2),
  Op.xor 32 2 (.r 2)]

theorem b2 (prof : Profile) : Blk prof p2 0 10 o2 :=
  .cons (p2_0 _) (OpI.lea (.inl rfl)) (by decide) <|
  .cons (p2_3 _) (OpI.mov (.r 5) (.inl rfl)) (by decide) <|
  .cons (p2_5 _) (OpI.mov (.r 2) (.inl rfl)) (by decide) <|
  .cons (p2_8 _) (OpI.xor (.r 2) (.inl rfl)) (by decide) <|
  .nil 10

/-- The stretch at `80`. -/
def p3 : List Byte := [
  0x41, 0x0f, 0xb7, 0x46, 0x04, 0x29, 0xc7, 0x89, 0x7c, 0x24, 0x04, 0x8d, 0x6a, 0x01]

theorem p3_0 : ∀ feat, Dec feat p3 0 (FV7z.mk .movzx 32 [gr 32 0, .mem (mg (some 14) none 1 4 16)] 5) := by dec_rfl
theorem p3_5 : ∀ feat, Dec feat p3 5 (FV7z.mk .sub 32 [gr 32 7, Src.opd 32 (.r 0)] 2) := by dec_rfl
theorem p3_7 : ∀ feat, Dec feat p3 7 (FV7z.mk .mov 32 [.mem (mg (some 4) none 1 4 32), gr 32 7] 4) := by dec_rfl
theorem p3_11 : ∀ feat, Dec feat p3 11 (FV7z.mk .lea 32 [gr 32 5, .mem (mg (some 2) none 1 1 0)] 3) := by dec_rfl

/-- What the stretch does. -/
def o3 : List Op := [
  Op.ldzx 16 0 (some 14) none 1 4,
  Op.sub 32 7 (.r 0),
  Op.st 32 (some 4) none 1 4 7,
  Op.lea 32 5 (some 2) none 1 1]

theorem b3 (prof : Profile) : Blk prof p3 0 14 o3 :=
  .cons (p3_0 _) (OpI.ldzx (.inr rfl)) (by decide) <|
  .cons (p3_5 _) (OpI.sub (.r 0) (.inl rfl)) (by decide) <|
  .cons (p3_7 _) (OpI.st (.inr (.inr (.inl rfl)))) (by decide) <|
  .cons (p3_11 _) (OpI.lea (.inl rfl)) (by decide) <|
  .nil 14

def j0 : List Byte := [0xeb, 0x33]
theorem j0_0 : ∀ feat, Dec feat j0 0 (FV7z.mk .jmp 64 [.rel 51] 2) := by dec_rfl

/-- The stretch at `96`. -/
def p4 : List Byte := [
  0x0f, 0xb7, 0xc6, 0x3b, 0x44, 0x24, 0x04]

theorem p4_0 : ∀ feat, Dec feat p4 0 (FV7z.mk .movzx 32 [gr 32 0, gr 16 6] 3) := by dec_rfl
theorem p4_3 : ∀ feat, Dec feat p4 3 (FV7z.mk .cmp 32 [gr 32 0, .mem (mg (some 4) none 1 4 32)] 4) := by dec_rfl

/-- What the stretch does. -/
def o4 : List Op := [
  Op.zxr16 0 6,
  Op.cmpm 32 0 (some 4) none 1 4]

theorem b4 (prof : Profile) : Blk prof p4 0 7 o4 :=
  .cons (p4_0 _) (OpI.zxr16) (by decide) <|
  .cons (p4_3 _) (OpI.cmpm (.inl rfl)) (by decide) <|
  .nil 7

def j1 : List Byte := [0x73, 0x16]
theorem j1_0 : ∀ feat, Dec feat j1 0 (FV7z.mk (.jcc 3) 64 [.rel 22] 2) := by dec_rfl

/-- The stretch at `105`. -/
def p5 : List Byte := [
  0x48, 0x03, 0x74, 0x24, 0x08, 0x48, 0x8b, 0x7c, 0x24, 0x10, 0x4c, 0x01, 0xf6]

theorem p5_0 : ∀ feat, Dec feat p5 0 (FV7z.mk .add 64 [gr 64 6, .mem (mg (some 4) none 1 8 64)] 5) := by dec_rfl
theorem p5_5 : ∀ feat, Dec feat p5 5 (FV7z.mk .mov 64 [gr 64 7, .mem (mg (some 4) none 1 16 64)] 5) := by dec_rfl
theorem p5_10 : ∀ feat, Dec feat p5 10 (FV7z.mk .add 64 [gr 64 6, Src.opd 64 (.r 14)] 3) := by dec_rfl

/-- What the stretch does. -/
def o5 : List Op := [
  Op.addm 64 6 (some 4) none 1 8,
  Op.ld 64 7 (some 4) none 1 16,
  Op.add 64 6 (.r 14)]

theorem b5 (prof : Profile) : Blk prof p5 0 13 o5 :=
  .cons (p5_0 _) (OpI.addm (.inr rfl)) (by decide) <|
  .cons (p5_5 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p5_10 _) (OpI.add (.r 14) (.inr rfl)) (by decide) <|
  .nil 13

/-- The stretch at `123`. -/
def p6 : List Byte := [
  0x85, 0xc0]

theorem p6_0 : ∀ feat, Dec feat p6 0 (FV7z.mk .test 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl

/-- What the stretch does. -/
def o6 : List Op := [
  Op.test 32 0 (.r 0)]

theorem b6 (prof : Profile) : Blk prof p6 0 2 o6 :=
  .cons (p6_0 _) (OpI.test (.r 0) (.inl rfl)) (by decide) <|
  .nil 2

def j2 : List Byte := [0x74, 0x41]
theorem j2_0 : ∀ feat, Dec feat j2 0 (FV7z.mk (.jcc 4) 64 [.rel 65] 2) := by dec_rfl

/-- The stretch at `127`. -/
def p7 : List Byte := [
  0x41, 0x01, 0xed, 0x44, 0x89, 0xea, 0x44, 0x89, 0xe8, 0x29, 0xda, 0x44, 0x39, 0xeb, 0x0f, 0x46,
  0xc2, 0x41, 0x89, 0xc5]

theorem p7_0 : ∀ feat, Dec feat p7 0 (FV7z.mk .add 32 [gr 32 13, Src.opd 32 (.r 5)] 3) := by dec_rfl
theorem p7_3 : ∀ feat, Dec feat p7 3 (FV7z.mk .mov 32 [gr 32 2, Src.opd 32 (.r 13)] 3) := by dec_rfl
theorem p7_6 : ∀ feat, Dec feat p7 6 (FV7z.mk .mov 32 [gr 32 0, Src.opd 32 (.r 13)] 3) := by dec_rfl
theorem p7_9 : ∀ feat, Dec feat p7 9 (FV7z.mk .sub 32 [gr 32 2, Src.opd 32 (.r 3)] 2) := by dec_rfl
theorem p7_11 : ∀ feat, Dec feat p7 11 (FV7z.mk .cmp 32 [gr 32 3, Src.opd 32 (.r 13)] 3) := by dec_rfl
theorem p7_14 : ∀ feat, Dec feat p7 14 (FV7z.mk (.cmovcc 6) 32 [gr 32 0, gr 32 2] 3) := by dec_rfl
theorem p7_17 : ∀ feat, Dec feat p7 17 (FV7z.mk .mov 32 [gr 32 13, Src.opd 32 (.r 0)] 3) := by dec_rfl

/-- What the stretch does. -/
def o7 : List Op := [
  Op.add 32 13 (.r 5),
  Op.mov 32 2 (.r 13),
  Op.mov 32 0 (.r 13),
  Op.sub 32 2 (.r 3),
  Op.cmp 32 3 (.r 13),
  Op.cmov32 6 0 2,
  Op.mov 32 13 (.r 0)]

theorem b7 (prof : Profile) : Blk prof p7 0 20 o7 :=
  .cons (p7_0 _) (OpI.add (.r 5) (.inl rfl)) (by decide) <|
  .cons (p7_3 _) (OpI.mov (.r 13) (.inl rfl)) (by decide) <|
  .cons (p7_6 _) (OpI.mov (.r 13) (.inl rfl)) (by decide) <|
  .cons (p7_9 _) (OpI.sub (.r 3) (.inl rfl)) (by decide) <|
  .cons (p7_11 _) (OpI.cmp (.r 13) (.inl rfl)) (by decide) <|
  .cons (p7_14 _) (OpI.cmov32) (by decide) <|
  .cons (p7_17 _) (OpI.mov (.r 0) (.inl rfl)) (by decide) <|
  .nil 20

/-- The stretch at `147`. -/
def p8 : List Byte := [
  0x44, 0x89, 0xe8, 0x49, 0x8d, 0x14, 0x84, 0x4d, 0x8d, 0x3c, 0x16, 0x41, 0x0f, 0xb7, 0x37, 0x66,
  0x85, 0xf6]

theorem p8_0 : ∀ feat, Dec feat p8 0 (FV7z.mk .mov 32 [gr 32 0, Src.opd 32 (.r 13)] 3) := by dec_rfl
theorem p8_3 : ∀ feat, Dec feat p8 3 (FV7z.mk .lea 64 [gr 64 2, .mem (mg (some 12) (some 0) 4 0 0)] 4) := by dec_rfl
theorem p8_7 : ∀ feat, Dec feat p8 7 (FV7z.mk .lea 64 [gr 64 15, .mem (mg (some 14) (some 2) 1 0 0)] 4) := by dec_rfl
theorem p8_11 : ∀ feat, Dec feat p8 11 (FV7z.mk .movzx 32 [gr 32 6, .mem (mg (some 15) none 1 0 16)] 4) := by dec_rfl
theorem p8_15 : ∀ feat, Dec feat p8 15 (FV7z.mk .test 16 [gr 16 6, Src.opd 16 (.r 6)] 3) := by dec_rfl

/-- What the stretch does. -/
def o8 : List Op := [
  Op.mov 32 0 (.r 13),
  Op.lea 64 2 (some 12) (some 0) 4 0,
  Op.lea 64 15 (some 14) (some 2) 1 0,
  Op.ldzx 16 6 (some 15) none 1 0,
  Op.test 16 6 (.r 6)]

theorem b8 (prof : Profile) : Blk prof p8 0 18 o8 :=
  .cons (p8_0 _) (OpI.mov (.r 13) (.inl rfl)) (by decide) <|
  .cons (p8_3 _) (OpI.lea (.inr rfl)) (by decide) <|
  .cons (p8_7 _) (OpI.lea (.inr rfl)) (by decide) <|
  .cons (p8_11 _) (OpI.ldzx (.inr rfl)) (by decide) <|
  .cons (p8_15 _) (OpI.test16 (.r 6)) (by decide) <|
  .nil 18

def j3 : List Byte := [0x75, 0xb9]
theorem j3_0 : ∀ feat, Dec feat j3 0 (FV7z.mk (.jcc 5) 64 [.rel 18446744073709551545] 2) := by dec_rfl

/-- The stretch at `167`. -/
def p9 : List Byte := [
  0x48, 0x83, 0xc4, 0x28, 0xb8, 0xff, 0xff, 0xff, 0xff, 0x5b, 0x5d, 0x41, 0x5c, 0x41, 0x5d, 0x41,
  0x5e, 0x41, 0x5f]

theorem p9_0 : ∀ feat, Dec feat p9 0 (FV7z.mk .add 64 [gr 64 4, Src.opd 64 (.i 40)] 4) := by dec_rfl
theorem p9_4 : ∀ feat, Dec feat p9 4 (FV7z.mk .mov 32 [gr 32 0, Src.opd 32 (.i 4294967295)] 5) := by dec_rfl
theorem p9_9 : ∀ feat, Dec feat p9 9 (FV7z.mk .pop 64 [gr 64 3] 1) := by dec_rfl
theorem p9_10 : ∀ feat, Dec feat p9 10 (FV7z.mk .pop 64 [gr 64 5] 1) := by dec_rfl
theorem p9_11 : ∀ feat, Dec feat p9 11 (FV7z.mk .pop 64 [gr 64 12] 2) := by dec_rfl
theorem p9_13 : ∀ feat, Dec feat p9 13 (FV7z.mk .pop 64 [gr 64 13] 2) := by dec_rfl
theorem p9_15 : ∀ feat, Dec feat p9 15 (FV7z.mk .pop 64 [gr 64 14] 2) := by dec_rfl
theorem p9_17 : ∀ feat, Dec feat p9 17 (FV7z.mk .pop 64 [gr 64 15] 2) := by dec_rfl

/-- What the stretch does. -/
def o9 : List Op := [
  Op.add 64 4 (.i 40),
  Op.mov 32 0 (.i 4294967295),
  Op.pop 3,
  Op.pop 5,
  Op.pop 12,
  Op.pop 13,
  Op.pop 14,
  Op.pop 15]

theorem b9 (prof : Profile) : Blk prof p9 0 19 o9 :=
  .cons (p9_0 _) (OpI.add (.i 40) (.inr rfl)) (by decide) <|
  .cons (p9_4 _) (OpI.mov (.i 4294967295) (.inl rfl)) (by decide) <|
  .cons (p9_9 _) (OpI.pop) (by decide) <|
  .cons (p9_10 _) (OpI.pop) (by decide) <|
  .cons (p9_11 _) (OpI.pop) (by decide) <|
  .cons (p9_13 _) (OpI.pop) (by decide) <|
  .cons (p9_15 _) (OpI.pop) (by decide) <|
  .cons (p9_17 _) (OpI.pop) (by decide) <|
  .nil 19

/-- The stretch at `192`. -/
def p10 : List Byte := [
  0x41, 0x0f, 0xb7, 0x57, 0x02, 0x48, 0x8b, 0x7c, 0x24, 0x18, 0x48, 0x89, 0x17, 0x48, 0x83, 0xc4,
  0x28, 0x5b, 0x5d, 0x41, 0x5c, 0x41, 0x5d, 0x41, 0x5e, 0x41, 0x5f]

theorem p10_0 : ∀ feat, Dec feat p10 0 (FV7z.mk .movzx 32 [gr 32 2, .mem (mg (some 15) none 1 2 16)] 5) := by dec_rfl
theorem p10_5 : ∀ feat, Dec feat p10 5 (FV7z.mk .mov 64 [gr 64 7, .mem (mg (some 4) none 1 24 64)] 5) := by dec_rfl
theorem p10_10 : ∀ feat, Dec feat p10 10 (FV7z.mk .mov 64 [.mem (mg (some 7) none 1 0 64), gr 64 2] 3) := by dec_rfl
theorem p10_13 : ∀ feat, Dec feat p10 13 (FV7z.mk .add 64 [gr 64 4, Src.opd 64 (.i 40)] 4) := by dec_rfl
theorem p10_17 : ∀ feat, Dec feat p10 17 (FV7z.mk .pop 64 [gr 64 3] 1) := by dec_rfl
theorem p10_18 : ∀ feat, Dec feat p10 18 (FV7z.mk .pop 64 [gr 64 5] 1) := by dec_rfl
theorem p10_19 : ∀ feat, Dec feat p10 19 (FV7z.mk .pop 64 [gr 64 12] 2) := by dec_rfl
theorem p10_21 : ∀ feat, Dec feat p10 21 (FV7z.mk .pop 64 [gr 64 13] 2) := by dec_rfl
theorem p10_23 : ∀ feat, Dec feat p10 23 (FV7z.mk .pop 64 [gr 64 14] 2) := by dec_rfl
theorem p10_25 : ∀ feat, Dec feat p10 25 (FV7z.mk .pop 64 [gr 64 15] 2) := by dec_rfl

/-- What the stretch does. -/
def o10 : List Op := [
  Op.ldzx 16 2 (some 15) none 1 2,
  Op.ld 64 7 (some 4) none 1 24,
  Op.st 64 (some 7) none 1 0 2,
  Op.add 64 4 (.i 40),
  Op.pop 3,
  Op.pop 5,
  Op.pop 12,
  Op.pop 13,
  Op.pop 14,
  Op.pop 15]

theorem b10 (prof : Profile) : Blk prof p10 0 27 o10 :=
  .cons (p10_0 _) (OpI.ldzx (.inr rfl)) (by decide) <|
  .cons (p10_5 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p10_10 _) (OpI.st (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p10_13 _) (OpI.add (.i 40) (.inr rfl)) (by decide) <|
  .cons (p10_17 _) (OpI.pop) (by decide) <|
  .cons (p10_18 _) (OpI.pop) (by decide) <|
  .cons (p10_19 _) (OpI.pop) (by decide) <|
  .cons (p10_21 _) (OpI.pop) (by decide) <|
  .cons (p10_23 _) (OpI.pop) (by decide) <|
  .cons (p10_25 _) (OpI.pop) (by decide) <|
  .nil 27

end FV7z.Fmi
