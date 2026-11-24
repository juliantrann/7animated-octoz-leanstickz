import FV7z.Lemmas.SpFs
import FV7z.Lemmas.BlkOps14
import FV7z.Lemmas.BlkOps12
import FV7z.Lemmas.BlkOps6
import FV7z.Lemmas.BlkOps2
/-!
# The stretches of straight-line code of `handle_intel` (PLAN.md M, ctor 103)

Each distinct stretch between labels and jumps (`p*`, 18 of them) and each distinct jump (`j*`, 12) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.Hin
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The stretch at `1280`. -/
def p0 : List Byte := [
  0x41, 0x57, 0x41, 0x56, 0x41, 0x55, 0x41, 0x54, 0x55, 0x53, 0x48, 0x83, 0xec, 0x28, 0x64, 0x48,
  0x8b, 0x04, 0x25, 0x28, 0x00, 0x00, 0x00, 0x48, 0x89, 0x44, 0x24, 0x18, 0x31, 0xc0, 0x83, 0x3d,
  0x17, 0x7b, 0x14, 0x00, 0x01]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .push 64 [gr 64 15] 2) := by dec_rfl
theorem p0_2 : ∀ feat, Dec feat p0 2 (FV7z.mk .push 64 [gr 64 14] 2) := by dec_rfl
theorem p0_4 : ∀ feat, Dec feat p0 4 (FV7z.mk .push 64 [gr 64 13] 2) := by dec_rfl
theorem p0_6 : ∀ feat, Dec feat p0 6 (FV7z.mk .push 64 [gr 64 12] 2) := by dec_rfl
theorem p0_8 : ∀ feat, Dec feat p0 8 (FV7z.mk .push 64 [gr 64 5] 1) := by dec_rfl
theorem p0_9 : ∀ feat, Dec feat p0 9 (FV7z.mk .push 64 [gr 64 3] 1) := by dec_rfl
theorem p0_10 : ∀ feat, Dec feat p0 10 (FV7z.mk .sub 64 [gr 64 4, Src.opd 64 (.i 40)] 4) := by dec_rfl
theorem p0_14 : ∀ feat, Dec feat p0 14 (FV7z.mk .mov 64 [gr 64 0, .mem (mf none none 1 40 64)] 9) := by dec_rfl
theorem p0_23 : ∀ feat, Dec feat p0 23 (FV7z.mk .mov 64 [.mem (mg (some 4) none 1 24 64), gr 64 0] 5) := by dec_rfl
theorem p0_28 : ∀ feat, Dec feat p0 28 (FV7z.mk .xor 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl
theorem p0_30 : ∀ feat, Dec feat p0 30 (FV7z.mk .cmp 32 [.mem (mrip 1342231 32), .imm 32 1] 7) := by dec_rfl

/-- What the stretch does. -/
def o0 (fb : Addr) : List Op := [
  Op.push 15,
  Op.push 14,
  Op.push 13,
  Op.push 12,
  Op.push 5,
  Op.push 3,
  Op.sub 64 4 (.i 40),
  Op.ldf fb 64 0 none none 1 40,
  Op.st 64 (some 4) none 1 24 0,
  Op.xor 32 0 (.r 0),
  Op.cmpmia 32 8014668 1]

theorem b0 (prof : Profile) (fb : Addr) : BlkF prof p0 (0x65d010 : Addr) fb 0 37 (o0 fb) :=
  .cons (p0_0 _) (((OpI.push).at _).fs _) (by decide) <|
  .cons (p0_2 _) (((OpI.push).at _).fs _) (by decide) <|
  .cons (p0_4 _) (((OpI.push).at _).fs _) (by decide) <|
  .cons (p0_6 _) (((OpI.push).at _).fs _) (by decide) <|
  .cons (p0_8 _) (((OpI.push).at _).fs _) (by decide) <|
  .cons (p0_9 _) (((OpI.push).at _).fs _) (by decide) <|
  .cons (p0_10 _) (((OpI.sub (.i 40) (.inr rfl)).at _).fs _) (by decide) <|
  .cons (p0_14 _) (OpIF.ldf (.inr rfl)) (by decide) <|
  .cons (p0_23 _) (((OpI.st (.inr (.inr (.inr rfl)))).at _).fs _) (by decide) <|
  .cons (p0_28 _) (((OpI.xor (.r 0) (.inl rfl)).at _).fs _) (by decide) <|
  .cons (p0_30 _) ((OpIA.cmpmi_rip (.inl rfl) (by decide)).fs _) (by decide) <|
  .nil 37

def j0 : List Byte := [0x0f, 0x86, 0x1f, 0x01, 0x00, 0x00]
theorem j0_0 : ∀ feat, Dec feat j0 0 (FV7z.mk (.jcc 6) 64 [.rel 287] 6) := by dec_rfl

/-- The stretch at `1323`. -/
def p1 : List Byte := [
  0xc6, 0x44, 0x24, 0x16, 0x00, 0x89, 0xfd, 0x41, 0xbe, 0x01, 0x00, 0x00, 0x00, 0x4c, 0x8d, 0x6c,
  0x24, 0x16, 0xc6, 0x44, 0x24, 0x17, 0x00, 0x4c, 0x8d, 0x64, 0x24, 0x17, 0xc7, 0x44, 0x24, 0x0c,
  0x01, 0x00, 0x00, 0x00]

theorem p1_0 : ∀ feat, Dec feat p1 0 (FV7z.mk .mov 8 [.mem (mg (some 4) none 1 22 8), .imm 8 0] 5) := by dec_rfl
theorem p1_5 : ∀ feat, Dec feat p1 5 (FV7z.mk .mov 32 [gr 32 5, Src.opd 32 (.r 7)] 2) := by dec_rfl
theorem p1_7 : ∀ feat, Dec feat p1 7 (FV7z.mk .mov 32 [gr 32 14, Src.opd 32 (.i 1)] 6) := by dec_rfl
theorem p1_13 : ∀ feat, Dec feat p1 13 (FV7z.mk .lea 64 [gr 64 13, .mem (mg (some 4) none 1 22 0)] 5) := by dec_rfl
theorem p1_18 : ∀ feat, Dec feat p1 18 (FV7z.mk .mov 8 [.mem (mg (some 4) none 1 23 8), .imm 8 0] 5) := by dec_rfl
theorem p1_23 : ∀ feat, Dec feat p1 23 (FV7z.mk .lea 64 [gr 64 12, .mem (mg (some 4) none 1 23 0)] 5) := by dec_rfl
theorem p1_28 : ∀ feat, Dec feat p1 28 (FV7z.mk .mov 32 [.mem (mg (some 4) none 1 12 32), .imm 32 1] 8) := by dec_rfl

/-- What the stretch does. -/
def o1 : List Op := [
  Op.sti 8 (some 4) none 1 22 0,
  Op.mov 32 5 (.r 7),
  Op.mov 32 14 (.i 1),
  Op.lea 64 13 (some 4) none 1 22,
  Op.sti 8 (some 4) none 1 23 0,
  Op.lea 64 12 (some 4) none 1 23,
  Op.sti 32 (some 4) none 1 12 1]

theorem b1 (prof : Profile) : Blk prof p1 0 36 o1 :=
  .cons (p1_0 _) (OpI.sti (.inl rfl)) (by decide) <|
  .cons (p1_5 _) (OpI.mov (.r 7) (.inl rfl)) (by decide) <|
  .cons (p1_7 _) (OpI.mov (.i 1) (.inl rfl)) (by decide) <|
  .cons (p1_13 _) (OpI.lea (.inr rfl)) (by decide) <|
  .cons (p1_18 _) (OpI.sti (.inl rfl)) (by decide) <|
  .cons (p1_23 _) (OpI.lea (.inr rfl)) (by decide) <|
  .cons (p1_28 _) (OpI.sti (.inr (.inr (.inl rfl)))) (by decide) <|
  .nil 36

def j1 : List Byte := [0xeb, 0x0a]
theorem j1_0 : ∀ feat, Dec feat j1 0 (FV7z.mk .jmp 64 [.rel 10] 2) := by dec_rfl

/-- The stretch at `1368`. -/
def p2 : List Byte := [
  0x41, 0x89, 0xd6]

theorem p2_0 : ∀ feat, Dec feat p2 0 (FV7z.mk .mov 32 [gr 32 14, Src.opd 32 (.r 2)] 3) := by dec_rfl

/-- What the stretch does. -/
def o2 : List Op := [
  Op.mov 32 14 (.r 2)]

theorem b2 (prof : Profile) : Blk prof p2 0 3 o2 :=
  .cons (p2_0 _) (OpI.mov (.r 2) (.inl rfl)) (by decide) <|
  .nil 3

/-- The stretch at `1371`. -/
def p3 : List Byte := [
  0xb8, 0x02, 0x00, 0x00, 0x00]

theorem p3_0 : ∀ feat, Dec feat p3 0 (FV7z.mk .mov 32 [gr 32 0, Src.opd 32 (.i 2)] 5) := by dec_rfl

/-- What the stretch does. -/
def o3 : List Op := [
  Op.mov 32 0 (.i 2)]

theorem b3 (prof : Profile) : Blk prof p3 0 5 o3 :=
  .cons (p3_0 _) (OpI.mov (.i 2) (.inl rfl)) (by decide) <|
  .nil 5

/-- The stretch at `1378`. -/
def p4 : List Byte := [
  0x89, 0x54, 0x24, 0x08, 0x41, 0x89, 0xcf, 0x89, 0xc6, 0x41, 0x83, 0xfe, 0x01]

theorem p4_0 : ∀ feat, Dec feat p4 0 (FV7z.mk .mov 32 [.mem (mg (some 4) none 1 8 32), gr 32 2] 4) := by dec_rfl
theorem p4_4 : ∀ feat, Dec feat p4 4 (FV7z.mk .mov 32 [gr 32 15, Src.opd 32 (.r 1)] 3) := by dec_rfl
theorem p4_7 : ∀ feat, Dec feat p4 7 (FV7z.mk .mov 32 [gr 32 6, Src.opd 32 (.r 0)] 2) := by dec_rfl
theorem p4_9 : ∀ feat, Dec feat p4 9 (FV7z.mk .cmp 32 [gr 32 14, Src.opd 32 (.i 1)] 4) := by dec_rfl

/-- What the stretch does. -/
def o4 : List Op := [
  Op.st 32 (some 4) none 1 8 2,
  Op.mov 32 15 (.r 1),
  Op.mov 32 6 (.r 0),
  Op.cmp 32 14 (.i 1)]

theorem b4 (prof : Profile) : Blk prof p4 0 13 o4 :=
  .cons (p4_0 _) (OpI.st (.inr (.inr (.inl rfl)))) (by decide) <|
  .cons (p4_4 _) (OpI.mov (.r 1) (.inl rfl)) (by decide) <|
  .cons (p4_7 _) (OpI.mov (.r 0) (.inl rfl)) (by decide) <|
  .cons (p4_9 _) (OpI.cmp (.i 1) (.inl rfl)) (by decide) <|
  .nil 13

def j2 : List Byte := [0x75, 0x0a]
theorem j2_0 : ∀ feat, Dec feat j2 0 (FV7z.mk (.jcc 5) 64 [.rel 10] 2) := by dec_rfl

/-- The stretch at `1393`. -/
def p5 : List Byte := [
  0x0f, 0xb6, 0xc0, 0x40, 0x30, 0xf6, 0x89, 0x44, 0x24, 0x0c]

theorem p5_0 : ∀ feat, Dec feat p5 0 (FV7z.mk .movzx 32 [gr 32 0, gr 8 0] 3) := by dec_rfl
theorem p5_3 : ∀ feat, Dec feat p5 3 (FV7z.mk .xor 8 [gr 8 6, Src.opd 8 (.r 6)] 3) := by dec_rfl
theorem p5_6 : ∀ feat, Dec feat p5 6 (FV7z.mk .mov 32 [.mem (mg (some 4) none 1 12 32), gr 32 0] 4) := by dec_rfl

/-- What the stretch does. -/
def o5 : List Op := [
  Op.zxr 0 0,
  Op.xor8 6 (.r 6),
  Op.st 32 (some 4) none 1 12 0]

theorem b5 (prof : Profile) : Blk prof p5 0 10 o5 :=
  .cons (p5_0 _) (OpI.zxr) (by decide) <|
  .cons (p5_3 _) (OpI.xor8 (.r 6)) (by decide) <|
  .cons (p5_6 _) (OpI.st (.inr (.inr (.inl rfl)))) (by decide) <|
  .nil 10

/-- The stretch at `1403`. -/
def p6 : List Byte := [
  0x4c, 0x8d, 0x0d, 0xc2, 0x7a, 0x14, 0x00, 0x4c, 0x89, 0xe9, 0x4c, 0x89, 0xe2, 0x89, 0xef, 0x4d,
  0x8d, 0x41, 0xfc]

theorem p6_0 : ∀ feat, Dec feat p6 0 (FV7z.mk .lea 64 [gr 64 9, .mem (mrip 1342146 0)] 7) := by dec_rfl
theorem p6_7 : ∀ feat, Dec feat p6 7 (FV7z.mk .mov 64 [gr 64 1, Src.opd 64 (.r 13)] 3) := by dec_rfl
theorem p6_10 : ∀ feat, Dec feat p6 10 (FV7z.mk .mov 64 [gr 64 2, Src.opd 64 (.r 12)] 3) := by dec_rfl
theorem p6_13 : ∀ feat, Dec feat p6 13 (FV7z.mk .mov 32 [gr 32 7, Src.opd 32 (.r 5)] 2) := by dec_rfl
theorem p6_15 : ∀ feat, Dec feat p6 15 (FV7z.mk .lea 64 [gr 64 8, .mem (mg (some 9) none 1 18446744073709551612 0)] 4) := by dec_rfl

/-- What the stretch does. -/
def o6 : List Op := [
  Op.mov 64 9 (.i 8014676),
  Op.mov 64 1 (.r 13),
  Op.mov 64 2 (.r 12),
  Op.mov 32 7 (.r 5),
  Op.lea 64 8 (some 9) none 1 18446744073709551612]

theorem b6 (prof : Profile) : BlkA prof p6 (0x65d08b : Addr) 0 19 o6 :=
  .cons (p6_0 _) (OpIA.lea_rip (by decide)) (by decide) <|
  .cons (p6_7 _) ((OpI.mov (.r 13) (.inr rfl)).at _) (by decide) <|
  .cons (p6_10 _) ((OpI.mov (.r 12) (.inr rfl)).at _) (by decide) <|
  .cons (p6_13 _) ((OpI.mov (.r 5) (.inl rfl)).at _) (by decide) <|
  .cons (p6_15 _) ((OpI.lea (.inr rfl)).at _) (by decide) <|
  .nil 19

/-- The stretch at `1427`. -/
def p7 : List Byte := [
  0x48, 0x85, 0xc0]

theorem p7_0 : ∀ feat, Dec feat p7 0 (FV7z.mk .test 64 [gr 64 0, Src.opd 64 (.r 0)] 3) := by dec_rfl

/-- What the stretch does. -/
def o7 : List Op := [
  Op.test 64 0 (.r 0)]

theorem b7 (prof : Profile) : Blk prof p7 0 3 o7 :=
  .cons (p7_0 _) (OpI.test (.r 0) (.inr rfl)) (by decide) <|
  .nil 3

def j3 : List Byte := [0x0f, 0x85, 0x84, 0x00, 0x00, 0x00]
theorem j3_0 : ∀ feat, Dec feat j3 0 (FV7z.mk (.jcc 5) 64 [.rel 132] 6) := by dec_rfl

/-- The stretch at `1436`. -/
def p8 : List Byte := [
  0x4c, 0x8d, 0x0d, 0xa1, 0x7a, 0x14, 0x00, 0x4c, 0x89, 0xe9, 0x4c, 0x89, 0xe2, 0x89, 0xde, 0x4d,
  0x8d, 0x41, 0xfc, 0x89, 0xef]

theorem p8_0 : ∀ feat, Dec feat p8 0 (FV7z.mk .lea 64 [gr 64 9, .mem (mrip 1342113 0)] 7) := by dec_rfl
theorem p8_7 : ∀ feat, Dec feat p8 7 (FV7z.mk .mov 64 [gr 64 1, Src.opd 64 (.r 13)] 3) := by dec_rfl
theorem p8_10 : ∀ feat, Dec feat p8 10 (FV7z.mk .mov 64 [gr 64 2, Src.opd 64 (.r 12)] 3) := by dec_rfl
theorem p8_13 : ∀ feat, Dec feat p8 13 (FV7z.mk .mov 32 [gr 32 6, Src.opd 32 (.r 3)] 2) := by dec_rfl
theorem p8_15 : ∀ feat, Dec feat p8 15 (FV7z.mk .lea 64 [gr 64 8, .mem (mg (some 9) none 1 18446744073709551612 0)] 4) := by dec_rfl
theorem p8_19 : ∀ feat, Dec feat p8 19 (FV7z.mk .mov 32 [gr 32 7, Src.opd 32 (.r 5)] 2) := by dec_rfl

/-- What the stretch does. -/
def o8 : List Op := [
  Op.mov 64 9 (.i 8014676),
  Op.mov 64 1 (.r 13),
  Op.mov 64 2 (.r 12),
  Op.mov 32 6 (.r 3),
  Op.lea 64 8 (some 9) none 1 18446744073709551612,
  Op.mov 32 7 (.r 5)]

theorem b8 (prof : Profile) : BlkA prof p8 (0x65d0ac : Addr) 0 21 o8 :=
  .cons (p8_0 _) (OpIA.lea_rip (by decide)) (by decide) <|
  .cons (p8_7 _) ((OpI.mov (.r 13) (.inr rfl)).at _) (by decide) <|
  .cons (p8_10 _) ((OpI.mov (.r 12) (.inr rfl)).at _) (by decide) <|
  .cons (p8_13 _) ((OpI.mov (.r 3) (.inl rfl)).at _) (by decide) <|
  .cons (p8_15 _) ((OpI.lea (.inr rfl)).at _) (by decide) <|
  .cons (p8_19 _) ((OpI.mov (.r 5) (.inl rfl)).at _) (by decide) <|
  .nil 21

def j4 : List Byte := [0x75, 0x65]
theorem j4_0 : ∀ feat, Dec feat j4 0 (FV7z.mk (.jcc 5) 64 [.rel 101] 2) := by dec_rfl

/-- The stretch at `1467`. -/
def p9 : List Byte := [
  0x4c, 0x8d, 0x0d, 0x82, 0x7a, 0x14, 0x00, 0x4c, 0x89, 0xe9, 0x4c, 0x89, 0xe2, 0x44, 0x89, 0xfe,
  0x4d, 0x8d, 0x41, 0xfc, 0x89, 0xef]

theorem p9_0 : ∀ feat, Dec feat p9 0 (FV7z.mk .lea 64 [gr 64 9, .mem (mrip 1342082 0)] 7) := by dec_rfl
theorem p9_7 : ∀ feat, Dec feat p9 7 (FV7z.mk .mov 64 [gr 64 1, Src.opd 64 (.r 13)] 3) := by dec_rfl
theorem p9_10 : ∀ feat, Dec feat p9 10 (FV7z.mk .mov 64 [gr 64 2, Src.opd 64 (.r 12)] 3) := by dec_rfl
theorem p9_13 : ∀ feat, Dec feat p9 13 (FV7z.mk .mov 32 [gr 32 6, Src.opd 32 (.r 15)] 3) := by dec_rfl
theorem p9_16 : ∀ feat, Dec feat p9 16 (FV7z.mk .lea 64 [gr 64 8, .mem (mg (some 9) none 1 18446744073709551612 0)] 4) := by dec_rfl
theorem p9_20 : ∀ feat, Dec feat p9 20 (FV7z.mk .mov 32 [gr 32 7, Src.opd 32 (.r 5)] 2) := by dec_rfl

/-- What the stretch does. -/
def o9 : List Op := [
  Op.mov 64 9 (.i 8014676),
  Op.mov 64 1 (.r 13),
  Op.mov 64 2 (.r 12),
  Op.mov 32 6 (.r 15),
  Op.lea 64 8 (some 9) none 1 18446744073709551612,
  Op.mov 32 7 (.r 5)]

theorem b9 (prof : Profile) : BlkA prof p9 (0x65d0cb : Addr) 0 22 o9 :=
  .cons (p9_0 _) (OpIA.lea_rip (by decide)) (by decide) <|
  .cons (p9_7 _) ((OpI.mov (.r 13) (.inr rfl)).at _) (by decide) <|
  .cons (p9_10 _) ((OpI.mov (.r 12) (.inr rfl)).at _) (by decide) <|
  .cons (p9_13 _) ((OpI.mov (.r 15) (.inl rfl)).at _) (by decide) <|
  .cons (p9_16 _) ((OpI.lea (.inr rfl)).at _) (by decide) <|
  .cons (p9_20 _) ((OpI.mov (.r 5) (.inl rfl)).at _) (by decide) <|
  .nil 22

def j5 : List Byte := [0x75, 0x45]
theorem j5_0 : ∀ feat, Dec feat j5 0 (FV7z.mk (.jcc 5) 64 [.rel 69] 2) := by dec_rfl

/-- The stretch at `1499`. -/
def p10 : List Byte := [
  0x4c, 0x8d, 0x0d, 0x62, 0x7a, 0x14, 0x00, 0x8b, 0x74, 0x24, 0x08, 0x4c, 0x89, 0xe9, 0x89, 0xef,
  0x4d, 0x8d, 0x41, 0xfc, 0x4c, 0x89, 0xe2]

theorem p10_0 : ∀ feat, Dec feat p10 0 (FV7z.mk .lea 64 [gr 64 9, .mem (mrip 1342050 0)] 7) := by dec_rfl
theorem p10_7 : ∀ feat, Dec feat p10 7 (FV7z.mk .mov 32 [gr 32 6, .mem (mg (some 4) none 1 8 32)] 4) := by dec_rfl
theorem p10_11 : ∀ feat, Dec feat p10 11 (FV7z.mk .mov 64 [gr 64 1, Src.opd 64 (.r 13)] 3) := by dec_rfl
theorem p10_14 : ∀ feat, Dec feat p10 14 (FV7z.mk .mov 32 [gr 32 7, Src.opd 32 (.r 5)] 2) := by dec_rfl
theorem p10_16 : ∀ feat, Dec feat p10 16 (FV7z.mk .lea 64 [gr 64 8, .mem (mg (some 9) none 1 18446744073709551612 0)] 4) := by dec_rfl
theorem p10_20 : ∀ feat, Dec feat p10 20 (FV7z.mk .mov 64 [gr 64 2, Src.opd 64 (.r 12)] 3) := by dec_rfl

/-- What the stretch does. -/
def o10 : List Op := [
  Op.mov 64 9 (.i 8014676),
  Op.ld 32 6 (some 4) none 1 8,
  Op.mov 64 1 (.r 13),
  Op.mov 32 7 (.r 5),
  Op.lea 64 8 (some 9) none 1 18446744073709551612,
  Op.mov 64 2 (.r 12)]

theorem b10 (prof : Profile) : BlkA prof p10 (0x65d0eb : Addr) 0 23 o10 :=
  .cons (p10_0 _) (OpIA.lea_rip (by decide)) (by decide) <|
  .cons (p10_7 _) ((OpI.ld (.inl rfl)).at _) (by decide) <|
  .cons (p10_11 _) ((OpI.mov (.r 13) (.inr rfl)).at _) (by decide) <|
  .cons (p10_14 _) ((OpI.mov (.r 5) (.inl rfl)).at _) (by decide) <|
  .cons (p10_16 _) ((OpI.lea (.inr rfl)).at _) (by decide) <|
  .cons (p10_20 _) ((OpI.mov (.r 12) (.inr rfl)).at _) (by decide) <|
  .nil 23

def j6 : List Byte := [0x75, 0x24]
theorem j6_0 : ∀ feat, Dec feat j6 0 (FV7z.mk (.jcc 5) 64 [.rel 36] 2) := by dec_rfl

/-- The stretch at `1532`. -/
def p11 : List Byte := [
  0x41, 0x8d, 0x56, 0x01, 0x44, 0x39, 0x74, 0x24, 0x0c]

theorem p11_0 : ∀ feat, Dec feat p11 0 (FV7z.mk .lea 32 [gr 32 2, .mem (mg (some 14) none 1 1 0)] 4) := by dec_rfl
theorem p11_4 : ∀ feat, Dec feat p11 4 (FV7z.mk .cmp 32 [.mem (mg (some 4) none 1 12 32), gr 32 14] 5) := by dec_rfl

/-- What the stretch does. -/
def o11 : List Op := [
  Op.lea 32 2 (some 14) none 1 1,
  Op.cmpmr 32 (some 4) none 1 12 14]

theorem b11 (prof : Profile) : Blk prof p11 0 9 o11 :=
  .cons (p11_0 _) (OpI.lea (.inl rfl)) (by decide) <|
  .cons (p11_4 _) (OpI.cmpmr (.inl rfl)) (by decide) <|
  .nil 9

def j7 : List Byte := [0x0f, 0x87, 0x4d, 0xff, 0xff, 0xff]
theorem j7_0 : ∀ feat, Dec feat j7 0 (FV7z.mk (.jcc 7) 64 [.rel 18446744073709551437] 6) := by dec_rfl

/-- The stretch at `1547`. -/
def p12 : List Byte := [
  0x81, 0xed, 0xbf, 0x00, 0x00, 0x00, 0x83, 0xfd, 0x05]

theorem p12_0 : ∀ feat, Dec feat p12 0 (FV7z.mk .sub 32 [gr 32 5, Src.opd 32 (.i 191)] 6) := by dec_rfl
theorem p12_6 : ∀ feat, Dec feat p12 6 (FV7z.mk .cmp 32 [gr 32 5, Src.opd 32 (.i 5)] 3) := by dec_rfl

/-- What the stretch does. -/
def o12 : List Op := [
  Op.sub 32 5 (.i 191),
  Op.cmp 32 5 (.i 5)]

theorem b12 (prof : Profile) : Blk prof p12 0 9 o12 :=
  .cons (p12_0 _) (OpI.sub (.i 191) (.inl rfl)) (by decide) <|
  .cons (p12_6 _) (OpI.cmp (.i 5) (.inl rfl)) (by decide) <|
  .nil 9

def j8 : List Byte := [0x76, 0x2a]
theorem j8_0 : ∀ feat, Dec feat j8 0 (FV7z.mk (.jcc 6) 64 [.rel 42] 2) := by dec_rfl

/-- The stretch at `1558`. -/
def p13 : List Byte := [
  0x66, 0x2e, 0x0f, 0x1f, 0x84, 0x00, 0x00, 0x00, 0x00, 0x00]

theorem p13_0 : ∀ feat, Dec feat p13 0 (FV7z.mk .nop 16 [.mem (mg (some 0) (some 0) 1 0 16)] 10) := by dec_rfl

/-- What the stretch does. -/
def o13 : List Op := [
  Op.nop]

theorem b13 (prof : Profile) : Blk prof p13 0 10 o13 :=
  .cons (p13_0 _) (OpI.nop) (by decide) <|
  .nil 10

/-- The stretch at `1568`. -/
def p14 : List Byte := [
  0x48, 0x8b, 0x5c, 0x24, 0x18, 0x64, 0x48, 0x33, 0x1c, 0x25, 0x28, 0x00, 0x00, 0x00]

theorem p14_0 : ∀ feat, Dec feat p14 0 (FV7z.mk .mov 64 [gr 64 3, .mem (mg (some 4) none 1 24 64)] 5) := by dec_rfl
theorem p14_5 : ∀ feat, Dec feat p14 5 (FV7z.mk .xor 64 [gr 64 3, .mem (mf none none 1 40 64)] 9) := by dec_rfl

/-- What the stretch does. -/
def o14 (fb : Addr) : List Op := [
  Op.ld 64 3 (some 4) none 1 24,
  Op.xormf fb 64 3 none none 1 40]

theorem b14 (prof : Profile) (fb : Addr) : BlkF prof p14 (0x65d130 : Addr) fb 0 14 (o14 fb) :=
  .cons (p14_0 _) (((OpI.ld (.inr rfl)).at _).fs _) (by decide) <|
  .cons (p14_5 _) (OpIF.xormf (.inr rfl)) (by decide) <|
  .nil 14

def j9 : List Byte := [0x75, 0x23]
theorem j9_0 : ∀ feat, Dec feat j9 0 (FV7z.mk (.jcc 5) 64 [.rel 35] 2) := by dec_rfl

/-- The stretch at `1584`. -/
def p15 : List Byte := [
  0x48, 0x83, 0xc4, 0x28, 0x5b, 0x5d, 0x41, 0x5c, 0x41, 0x5d, 0x41, 0x5e, 0x41, 0x5f]

theorem p15_0 : ∀ feat, Dec feat p15 0 (FV7z.mk .add 64 [gr 64 4, Src.opd 64 (.i 40)] 4) := by dec_rfl
theorem p15_4 : ∀ feat, Dec feat p15 4 (FV7z.mk .pop 64 [gr 64 3] 1) := by dec_rfl
theorem p15_5 : ∀ feat, Dec feat p15 5 (FV7z.mk .pop 64 [gr 64 5] 1) := by dec_rfl
theorem p15_6 : ∀ feat, Dec feat p15 6 (FV7z.mk .pop 64 [gr 64 12] 2) := by dec_rfl
theorem p15_8 : ∀ feat, Dec feat p15 8 (FV7z.mk .pop 64 [gr 64 13] 2) := by dec_rfl
theorem p15_10 : ∀ feat, Dec feat p15 10 (FV7z.mk .pop 64 [gr 64 14] 2) := by dec_rfl
theorem p15_12 : ∀ feat, Dec feat p15 12 (FV7z.mk .pop 64 [gr 64 15] 2) := by dec_rfl

/-- What the stretch does. -/
def o15 : List Op := [
  Op.add 64 4 (.i 40),
  Op.pop 3,
  Op.pop 5,
  Op.pop 12,
  Op.pop 13,
  Op.pop 14,
  Op.pop 15]

theorem b15 (prof : Profile) : Blk prof p15 0 14 o15 :=
  .cons (p15_0 _) (OpI.add (.i 40) (.inr rfl)) (by decide) <|
  .cons (p15_4 _) (OpI.pop) (by decide) <|
  .cons (p15_5 _) (OpI.pop) (by decide) <|
  .cons (p15_6 _) (OpI.pop) (by decide) <|
  .cons (p15_8 _) (OpI.pop) (by decide) <|
  .cons (p15_10 _) (OpI.pop) (by decide) <|
  .cons (p15_12 _) (OpI.pop) (by decide) <|
  .nil 14

/-- The stretch at `1600`. -/
def p16 : List Byte := [
  0x0f, 0xb6, 0x44, 0x24, 0x16, 0x48, 0xf7, 0xd8]

theorem p16_0 : ∀ feat, Dec feat p16 0 (FV7z.mk .movzx 32 [gr 32 0, .mem (mg (some 4) none 1 22 8)] 5) := by dec_rfl
theorem p16_5 : ∀ feat, Dec feat p16 5 (FV7z.mk .neg 64 [gr 64 0] 3) := by dec_rfl

/-- What the stretch does. -/
def o16 : List Op := [
  Op.ldzx 8 0 (some 4) none 1 22,
  Op.neg 64 0]

theorem b16 (prof : Profile) : Blk prof p16 0 8 o16 :=
  .cons (p16_0 _) (OpI.ldzx (.inl rfl)) (by decide) <|
  .cons (p16_5 _) (OpI.neg (.inr rfl)) (by decide) <|
  .nil 8

def j10 : List Byte := [0xeb, 0xd6]
theorem j10_0 : ∀ feat, Dec feat j10 0 (FV7z.mk .jmp 64 [.rel 18446744073709551574] 2) := by dec_rfl

/-- The stretch at `1610`. -/
def p17 : List Byte := [
  0x48, 0xc7, 0xc0, 0xff, 0xff, 0xff, 0xff]

theorem p17_0 : ∀ feat, Dec feat p17 0 (FV7z.mk .mov 64 [gr 64 0, Src.opd 64 (.i 18446744073709551615)] 7) := by dec_rfl

/-- What the stretch does. -/
def o17 : List Op := [
  Op.mov 64 0 (.i 18446744073709551615)]

theorem b17 (prof : Profile) : Blk prof p17 0 7 o17 :=
  .cons (p17_0 _) (OpI.mov (.i 18446744073709551615) (.inr rfl)) (by decide) <|
  .nil 7

def j11 : List Byte := [0xeb, 0xcd]
theorem j11_0 : ∀ feat, Dec feat j11 0 (FV7z.mk .jmp 64 [.rel 18446744073709551565] 2) := by dec_rfl

end FV7z.Hin
