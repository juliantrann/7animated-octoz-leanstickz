import FV7z.Lemmas.Sp
import FV7z.Lemmas.BlkOps8
import FV7z.Lemmas.BlkOps3
/-!
# The stretches of straight-line code of `__new_exitfn` (PLAN.md G3, startup)

Each distinct stretch between labels and jumps (`p*`, 15 of them) and each distinct jump (`j*`, 10) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.Nef
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The stretch at `0`. -/
def p0 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0x80, 0x3d, 0x59, 0x06, 0x18, 0x00, 0x00]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem p0_4 : ∀ feat, Dec feat p0 4 (FV7z.mk .cmp 8 [.mem (mrip 1574489 8), .imm 8 0] 7) := by dec_rfl

/-- What the stretch does. -/
def o0 : List Op := [
  Op.nop,
  Op.cmpmia 8 8010388 0]

theorem b0 (prof : Profile) : BlkA prof p0 (0x623430 : Addr) 0 11 o0 :=
  .cons (p0_0 _) ((OpI.endbr).at _) (by decide) <|
  .cons (p0_4 _) (OpIA.cmpmi8_rip (by decide)) (by decide) <|
  .nil 11

def j0 : List Byte := [0x0f, 0x85, 0xec, 0x00, 0x00, 0x00]
theorem j0_0 : ∀ feat, Dec feat j0 0 (FV7z.mk (.jcc 5) 64 [.rel 236] 6) := by dec_rfl

/-- The stretch at `17`. -/
def p1 : List Byte := [
  0x55, 0x53, 0x48, 0x89, 0xfb, 0x48, 0x83, 0xec, 0x08, 0x48, 0x8b, 0x2f, 0x48, 0x85, 0xed]

theorem p1_0 : ∀ feat, Dec feat p1 0 (FV7z.mk .push 64 [gr 64 5] 1) := by dec_rfl
theorem p1_1 : ∀ feat, Dec feat p1 1 (FV7z.mk .push 64 [gr 64 3] 1) := by dec_rfl
theorem p1_2 : ∀ feat, Dec feat p1 2 (FV7z.mk .mov 64 [gr 64 3, Src.opd 64 (.r 7)] 3) := by dec_rfl
theorem p1_5 : ∀ feat, Dec feat p1 5 (FV7z.mk .sub 64 [gr 64 4, Src.opd 64 (.i 8)] 4) := by dec_rfl
theorem p1_9 : ∀ feat, Dec feat p1 9 (FV7z.mk .mov 64 [gr 64 5, .mem (mg (some 7) none 1 0 64)] 3) := by dec_rfl
theorem p1_12 : ∀ feat, Dec feat p1 12 (FV7z.mk .test 64 [gr 64 5, Src.opd 64 (.r 5)] 3) := by dec_rfl

/-- What the stretch does. -/
def o1 : List Op := [
  Op.push 5,
  Op.push 3,
  Op.mov 64 3 (.r 7),
  Op.sub 64 4 (.i 8),
  Op.ld 64 5 (some 7) none 1 0,
  Op.test 64 5 (.r 5)]

theorem b1 (prof : Profile) : Blk prof p1 0 15 o1 :=
  .cons (p1_0 _) (OpI.push) (by decide) <|
  .cons (p1_1 _) (OpI.push) (by decide) <|
  .cons (p1_2 _) (OpI.mov (.r 7) (.inr rfl)) (by decide) <|
  .cons (p1_5 _) (OpI.sub (.i 8) (.inr rfl)) (by decide) <|
  .cons (p1_9 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p1_12 _) (OpI.test (.r 5) (.inr rfl)) (by decide) <|
  .nil 15

def j1 : List Byte := [0x0f, 0x84, 0xb8, 0x00, 0x00, 0x00]
theorem j1_0 : ∀ feat, Dec feat j1 0 (FV7z.mk (.jcc 4) 64 [.rel 184] 6) := by dec_rfl

/-- The stretch at `38`. -/
def p2 : List Byte := [
  0x48, 0x89, 0xee, 0x31, 0xff, 0x0f, 0x1f, 0x44, 0x00, 0x00]

theorem p2_0 : ∀ feat, Dec feat p2 0 (FV7z.mk .mov 64 [gr 64 6, Src.opd 64 (.r 5)] 3) := by dec_rfl
theorem p2_3 : ∀ feat, Dec feat p2 3 (FV7z.mk .xor 32 [gr 32 7, Src.opd 32 (.r 7)] 2) := by dec_rfl
theorem p2_5 : ∀ feat, Dec feat p2 5 (FV7z.mk .nop 32 [.mem (mg (some 0) (some 0) 1 0 32)] 5) := by dec_rfl

/-- What the stretch does. -/
def o2 : List Op := [
  Op.mov 64 6 (.r 5),
  Op.xor 32 7 (.r 7),
  Op.nop]

theorem b2 (prof : Profile) : Blk prof p2 0 10 o2 :=
  .cons (p2_0 _) (OpI.mov (.r 5) (.inr rfl)) (by decide) <|
  .cons (p2_3 _) (OpI.xor (.r 7) (.inl rfl)) (by decide) <|
  .cons (p2_5 _) (OpI.nop) (by decide) <|
  .nil 10

/-- The stretch at `48`. -/
def p3 : List Byte := [
  0x48, 0x8b, 0x46, 0x08]

theorem p3_0 : ∀ feat, Dec feat p3 0 (FV7z.mk .mov 64 [gr 64 0, .mem (mg (some 6) none 1 8 64)] 4) := by dec_rfl

/-- What the stretch does. -/
def o3 : List Op := [
  Op.ld 64 0 (some 6) none 1 8]

theorem b3 (prof : Profile) : Blk prof p3 0 4 o3 :=
  .cons (p3_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .nil 4

def j2 : List Byte := [0xeb, 0x20]
theorem j2_0 : ∀ feat, Dec feat j2 0 (FV7z.mk .jmp 64 [.rel 32] 2) := by dec_rfl

/-- The stretch at `64`. -/
def p4 : List Byte := [
  0x48, 0x8d, 0x50, 0xff, 0x48, 0x89, 0xd1, 0x48, 0xc1, 0xe1, 0x05, 0x48, 0x83, 0x7c, 0x0e, 0x10,
  0x00]

theorem p4_0 : ∀ feat, Dec feat p4 0 (FV7z.mk .lea 64 [gr 64 2, .mem (mg (some 0) none 1 18446744073709551615 0)] 4) := by dec_rfl
theorem p4_4 : ∀ feat, Dec feat p4 4 (FV7z.mk .mov 64 [gr 64 1, Src.opd 64 (.r 2)] 3) := by dec_rfl
theorem p4_7 : ∀ feat, Dec feat p4 7 (FV7z.mk .shl 64 [gr 64 1, Src.opd 8 (.i 5)] 4) := by dec_rfl
theorem p4_11 : ∀ feat, Dec feat p4 11 (FV7z.mk .cmp 64 [.mem (mg (some 6) (some 1) 1 16 64), .imm 64 0] 6) := by dec_rfl

/-- What the stretch does. -/
def o4 : List Op := [
  Op.lea 64 2 (some 0) none 1 18446744073709551615,
  Op.mov 64 1 (.r 2),
  Op.shl64 1 (.i 5),
  Op.cmpmi 64 (some 6) (some 1) 1 16 0]

theorem b4 (prof : Profile) : Blk prof p4 0 17 o4 :=
  .cons (p4_0 _) (OpI.lea (.inr rfl)) (by decide) <|
  .cons (p4_4 _) (OpI.mov (.r 2) (.inr rfl)) (by decide) <|
  .cons (p4_7 _) (OpI.shl64 (.i 5)) (by decide) <|
  .cons (p4_11 _) (OpI.cmpmi64) (by decide) <|
  .nil 17

def j3 : List Byte := [0x75, 0x25]
theorem j3_0 : ∀ feat, Dec feat j3 0 (FV7z.mk (.jcc 5) 64 [.rel 37] 2) := by dec_rfl

/-- The stretch at `83`. -/
def p5 : List Byte := [
  0x48, 0x89, 0xd0]

theorem p5_0 : ∀ feat, Dec feat p5 0 (FV7z.mk .mov 64 [gr 64 0, Src.opd 64 (.r 2)] 3) := by dec_rfl

/-- What the stretch does. -/
def o5 : List Op := [
  Op.mov 64 0 (.r 2)]

theorem b5 (prof : Profile) : Blk prof p5 0 3 o5 :=
  .cons (p5_0 _) (OpI.mov (.r 2) (.inr rfl)) (by decide) <|
  .nil 3

/-- The stretch at `86`. -/
def p6 : List Byte := [
  0x48, 0x85, 0xc0]

theorem p6_0 : ∀ feat, Dec feat p6 0 (FV7z.mk .test 64 [gr 64 0, Src.opd 64 (.r 0)] 3) := by dec_rfl

/-- What the stretch does. -/
def o6 : List Op := [
  Op.test 64 0 (.r 0)]

theorem b6 (prof : Profile) : Blk prof p6 0 3 o6 :=
  .cons (p6_0 _) (OpI.test (.r 0) (.inr rfl)) (by decide) <|
  .nil 3

def j4 : List Byte := [0x75, 0xe5]
theorem j4_0 : ∀ feat, Dec feat j4 0 (FV7z.mk (.jcc 5) 64 [.rel 18446744073709551589] 2) := by dec_rfl

/-- The stretch at `91`. -/
def p7 : List Byte := [
  0x48, 0x8b, 0x06, 0x48, 0xc7, 0x46, 0x08, 0x00, 0x00, 0x00, 0x00, 0x48, 0x89, 0xf7, 0x48, 0x85,
  0xc0]

theorem p7_0 : ∀ feat, Dec feat p7 0 (FV7z.mk .mov 64 [gr 64 0, .mem (mg (some 6) none 1 0 64)] 3) := by dec_rfl
theorem p7_3 : ∀ feat, Dec feat p7 3 (FV7z.mk .mov 64 [.mem (mg (some 6) none 1 8 64), .imm 64 0] 8) := by dec_rfl
theorem p7_11 : ∀ feat, Dec feat p7 11 (FV7z.mk .mov 64 [gr 64 7, Src.opd 64 (.r 6)] 3) := by dec_rfl
theorem p7_14 : ∀ feat, Dec feat p7 14 (FV7z.mk .test 64 [gr 64 0, Src.opd 64 (.r 0)] 3) := by dec_rfl

/-- What the stretch does. -/
def o7 : List Op := [
  Op.ld 64 0 (some 6) none 1 0,
  Op.sti 64 (some 6) none 1 8 0,
  Op.mov 64 7 (.r 6),
  Op.test 64 0 (.r 0)]

theorem b7 (prof : Profile) : Blk prof p7 0 17 o7 :=
  .cons (p7_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p7_3 _) (OpI.sti (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p7_11 _) (OpI.mov (.r 6) (.inr rfl)) (by decide) <|
  .cons (p7_14 _) (OpI.test (.r 0) (.inr rfl)) (by decide) <|
  .nil 17

def j5 : List Byte := [0x74, 0x62]
theorem j5_0 : ∀ feat, Dec feat j5 0 (FV7z.mk (.jcc 4) 64 [.rel 98] 2) := by dec_rfl

/-- The stretch at `110`. -/
def p8 : List Byte := [
  0x48, 0x89, 0xc6]

theorem p8_0 : ∀ feat, Dec feat p8 0 (FV7z.mk .mov 64 [gr 64 6, Src.opd 64 (.r 0)] 3) := by dec_rfl

/-- What the stretch does. -/
def o8 : List Op := [
  Op.mov 64 6 (.r 0)]

theorem b8 (prof : Profile) : Blk prof p8 0 3 o8 :=
  .cons (p8_0 _) (OpI.mov (.r 0) (.inr rfl)) (by decide) <|
  .nil 3

def j6 : List Byte := [0xeb, 0xbd]
theorem j6_0 : ∀ feat, Dec feat j6 0 (FV7z.mk .jmp 64 [.rel 18446744073709551549] 2) := by dec_rfl

/-- The stretch at `120`. -/
def p9 : List Byte := [
  0x48, 0x83, 0xf8, 0x20]

theorem p9_0 : ∀ feat, Dec feat p9 0 (FV7z.mk .cmp 64 [gr 64 0, Src.opd 64 (.i 32)] 4) := by dec_rfl

/-- What the stretch does. -/
def o9 : List Op := [
  Op.cmp 64 0 (.i 32)]

theorem b9 (prof : Profile) : Blk prof p9 0 4 o9 :=
  .cons (p9_0 _) (OpI.cmp (.i 32) (.inr rfl)) (by decide) <|
  .nil 4

def j7 : List Byte := [0x74, 0x2d]
theorem j7_0 : ∀ feat, Dec feat j7 0 (FV7z.mk (.jcc 4) 64 [.rel 45] 2) := by dec_rfl

/-- The stretch at `126`. -/
def p10 : List Byte := [
  0x48, 0x89, 0xc2, 0x48, 0x83, 0xc0, 0x01, 0x48, 0x89, 0x46, 0x08, 0x48, 0xc1, 0xe2, 0x05, 0x4c,
  0x8d, 0x44, 0x16, 0x10]

theorem p10_0 : ∀ feat, Dec feat p10 0 (FV7z.mk .mov 64 [gr 64 2, Src.opd 64 (.r 0)] 3) := by dec_rfl
theorem p10_3 : ∀ feat, Dec feat p10 3 (FV7z.mk .add 64 [gr 64 0, Src.opd 64 (.i 1)] 4) := by dec_rfl
theorem p10_7 : ∀ feat, Dec feat p10 7 (FV7z.mk .mov 64 [.mem (mg (some 6) none 1 8 64), gr 64 0] 4) := by dec_rfl
theorem p10_11 : ∀ feat, Dec feat p10 11 (FV7z.mk .shl 64 [gr 64 2, Src.opd 8 (.i 5)] 4) := by dec_rfl
theorem p10_15 : ∀ feat, Dec feat p10 15 (FV7z.mk .lea 64 [gr 64 8, .mem (mg (some 6) (some 2) 1 16 0)] 5) := by dec_rfl

/-- What the stretch does. -/
def o10 : List Op := [
  Op.mov 64 2 (.r 0),
  Op.add 64 0 (.i 1),
  Op.st 64 (some 6) none 1 8 0,
  Op.shl64 2 (.i 5),
  Op.lea 64 8 (some 6) (some 2) 1 16]

theorem b10 (prof : Profile) : Blk prof p10 0 20 o10 :=
  .cons (p10_0 _) (OpI.mov (.r 0) (.inr rfl)) (by decide) <|
  .cons (p10_3 _) (OpI.add (.i 1) (.inr rfl)) (by decide) <|
  .cons (p10_7 _) (OpI.st (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p10_11 _) (OpI.shl64 (.i 5)) (by decide) <|
  .cons (p10_15 _) (OpI.lea (.inr rfl)) (by decide) <|
  .nil 20

/-- The stretch at `146`. -/
def p11 : List Byte := [
  0x49, 0xc7, 0x00, 0x01, 0x00, 0x00, 0x00, 0x4c, 0x89, 0xc0]

theorem p11_0 : ∀ feat, Dec feat p11 0 (FV7z.mk .mov 64 [.mem (mg (some 8) none 1 0 64), .imm 64 1] 7) := by dec_rfl
theorem p11_7 : ∀ feat, Dec feat p11 7 (FV7z.mk .mov 64 [gr 64 0, Src.opd 64 (.r 8)] 3) := by dec_rfl

/-- What the stretch does. -/
def o11 : List Op := [
  Op.sti 64 (some 8) none 1 0 1,
  Op.mov 64 0 (.r 8)]

theorem b11 (prof : Profile) : Blk prof p11 0 10 o11 :=
  .cons (p11_0 _) (OpI.sti (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p11_7 _) (OpI.mov (.r 8) (.inr rfl)) (by decide) <|
  .nil 10

/-- The stretch at `164`. -/
def p12 : List Byte := [
  0x48, 0x83, 0xc4, 0x08, 0x5b, 0x5d]

theorem p12_0 : ∀ feat, Dec feat p12 0 (FV7z.mk .add 64 [gr 64 4, Src.opd 64 (.i 8)] 4) := by dec_rfl
theorem p12_4 : ∀ feat, Dec feat p12 4 (FV7z.mk .pop 64 [gr 64 3] 1) := by dec_rfl
theorem p12_5 : ∀ feat, Dec feat p12 5 (FV7z.mk .pop 64 [gr 64 5] 1) := by dec_rfl

/-- What the stretch does. -/
def o12 : List Op := [
  Op.add 64 4 (.i 8),
  Op.pop 3,
  Op.pop 5]

theorem b12 (prof : Profile) : Blk prof p12 0 6 o12 :=
  .cons (p12_0 _) (OpI.add (.i 8) (.inr rfl)) (by decide) <|
  .cons (p12_4 _) (OpI.pop) (by decide) <|
  .cons (p12_5 _) (OpI.pop) (by decide) <|
  .nil 6

/-- The stretch at `171`. -/
def p13 : List Byte := [
  0x48, 0x89, 0xfe, 0x48, 0x85, 0xff]

theorem p13_0 : ∀ feat, Dec feat p13 0 (FV7z.mk .mov 64 [gr 64 6, Src.opd 64 (.r 7)] 3) := by dec_rfl
theorem p13_3 : ∀ feat, Dec feat p13 3 (FV7z.mk .test 64 [gr 64 7, Src.opd 64 (.r 7)] 3) := by dec_rfl

/-- What the stretch does. -/
def o13 : List Op := [
  Op.mov 64 6 (.r 7),
  Op.test 64 7 (.r 7)]

theorem b13 (prof : Profile) : Blk prof p13 0 6 o13 :=
  .cons (p13_0 _) (OpI.mov (.r 7) (.inr rfl)) (by decide) <|
  .cons (p13_3 _) (OpI.test (.r 7) (.inr rfl)) (by decide) <|
  .nil 6

def j8 : List Byte := [0x75, 0x1d]
theorem j8_0 : ∀ feat, Dec feat j8 0 (FV7z.mk (.jcc 5) 64 [.rel 29] 2) := by dec_rfl

/-- The stretch at `208`. -/
def p14 : List Byte := [
  0x48, 0xc7, 0x46, 0x08, 0x01, 0x00, 0x00, 0x00, 0x4c, 0x8d, 0x46, 0x10]

theorem p14_0 : ∀ feat, Dec feat p14 0 (FV7z.mk .mov 64 [.mem (mg (some 6) none 1 8 64), .imm 64 1] 8) := by dec_rfl
theorem p14_8 : ∀ feat, Dec feat p14 8 (FV7z.mk .lea 64 [gr 64 8, .mem (mg (some 6) none 1 16 0)] 4) := by dec_rfl

/-- What the stretch does. -/
def o14 : List Op := [
  Op.sti 64 (some 6) none 1 8 1,
  Op.lea 64 8 (some 6) none 1 16]

theorem b14 (prof : Profile) : Blk prof p14 0 12 o14 :=
  .cons (p14_0 _) (OpI.sti (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p14_8 _) (OpI.lea (.inr rfl)) (by decide) <|
  .nil 12

def j9 : List Byte := [0xeb, 0xb4]
theorem j9_0 : ∀ feat, Dec feat j9 0 (FV7z.mk .jmp 64 [.rel 18446744073709551540] 2) := by dec_rfl

end FV7z.Nef
