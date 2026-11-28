import FV7z.Lemmas.Sp
import FV7z.Lemmas.BlkOps12
import FV7z.Lemmas.BlkOps2
/-!
# The stretches of straight-line code of `CFieldPrinter::PrintTitle` (PLAN.md §M, M1)

Each distinct stretch between labels and jumps (`p*`, 8 of them) and each distinct jump (`j*`, 6) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.Ptt
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The stretch at `0`. -/
def p0 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0x8b, 0x47, 0x08, 0x85, 0xc0]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem p0_4 : ∀ feat, Dec feat p0 4 (FV7z.mk .mov 32 [gr 32 0, .mem (mg (some 7) none 1 8 32)] 3) := by dec_rfl
theorem p0_7 : ∀ feat, Dec feat p0 7 (FV7z.mk .test 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl

/-- What the stretch does. -/
def o0 : List Op := [
  Op.nop,
  Op.ld 32 0 (some 7) none 1 8,
  Op.test 32 0 (.r 0)]

theorem b0 (prof : Profile) : Blk prof p0 0 9 o0 :=
  .cons (p0_0 _) (OpI.endbr) (by decide) <|
  .cons (p0_4 _) (OpI.ld (.inl rfl)) (by decide) <|
  .cons (p0_7 _) (OpI.test (.r 0) (.inl rfl)) (by decide) <|
  .nil 9

def j0 : List Byte := [0x74, 0x5d]
theorem j0_0 : ∀ feat, Dec feat j0 0 (FV7z.mk (.jcc 4) 64 [.rel 93] 2) := by dec_rfl

/-- The stretch at `11`. -/
def p1 : List Byte := [
  0x41, 0x54, 0x49, 0x89, 0xfc, 0x55, 0x31, 0xed, 0x53]

theorem p1_0 : ∀ feat, Dec feat p1 0 (FV7z.mk .push 64 [gr 64 12] 2) := by dec_rfl
theorem p1_2 : ∀ feat, Dec feat p1 2 (FV7z.mk .mov 64 [gr 64 12, Src.opd 64 (.r 7)] 3) := by dec_rfl
theorem p1_5 : ∀ feat, Dec feat p1 5 (FV7z.mk .push 64 [gr 64 5] 1) := by dec_rfl
theorem p1_6 : ∀ feat, Dec feat p1 6 (FV7z.mk .xor 32 [gr 32 5, Src.opd 32 (.r 5)] 2) := by dec_rfl
theorem p1_8 : ∀ feat, Dec feat p1 8 (FV7z.mk .push 64 [gr 64 3] 1) := by dec_rfl

/-- What the stretch does. -/
def o1 : List Op := [
  Op.push 12,
  Op.mov 64 12 (.r 7),
  Op.push 5,
  Op.xor 32 5 (.r 5),
  Op.push 3]

theorem b1 (prof : Profile) : Blk prof p1 0 9 o1 :=
  .cons (p1_0 _) (OpI.push) (by decide) <|
  .cons (p1_2 _) (OpI.mov (.r 7) (.inr rfl)) (by decide) <|
  .cons (p1_5 _) (OpI.push) (by decide) <|
  .cons (p1_6 _) (OpI.xor (.r 5) (.inl rfl)) (by decide) <|
  .cons (p1_8 _) (OpI.push) (by decide) <|
  .nil 9

def j1 : List Byte := [0xeb, 0x2a]
theorem j1_0 : ∀ feat, Dec feat j1 0 (FV7z.mk .jmp 64 [.rel 42] 2) := by dec_rfl

/-- The stretch at `32`. -/
def p2 : List Byte := [
  0x31, 0xf6, 0x83, 0x3b, 0x03, 0x48, 0x8b, 0x53, 0x18]

theorem p2_0 : ∀ feat, Dec feat p2 0 (FV7z.mk .xor 32 [gr 32 6, Src.opd 32 (.r 6)] 2) := by dec_rfl
theorem p2_2 : ∀ feat, Dec feat p2 2 (FV7z.mk .cmp 32 [.mem (mg (some 3) none 1 0 32), .imm 32 3] 3) := by dec_rfl
theorem p2_5 : ∀ feat, Dec feat p2 5 (FV7z.mk .mov 64 [gr 64 2, .mem (mg (some 3) none 1 24 64)] 4) := by dec_rfl

/-- What the stretch does. -/
def o2 : List Op := [
  Op.xor 32 6 (.r 6),
  Op.cmpmi 32 (some 3) none 1 0 3,
  Op.ld 64 2 (some 3) none 1 24]

theorem b2 (prof : Profile) : Blk prof p2 0 9 o2 :=
  .cons (p2_0 _) (OpI.xor (.r 6) (.inl rfl)) (by decide) <|
  .cons (p2_2 _) (OpI.cmpmi (.inr rfl)) (by decide) <|
  .cons (p2_5 _) (OpI.ld (.inr rfl)) (by decide) <|
  .nil 9

def j2 : List Byte := [0x74, 0x03]
theorem j2_0 : ∀ feat, Dec feat j2 0 (FV7z.mk (.jcc 4) 64 [.rel 3] 2) := by dec_rfl

/-- The stretch at `43`. -/
def p3 : List Byte := [
  0x8b, 0x73, 0x34]

theorem p3_0 : ∀ feat, Dec feat p3 0 (FV7z.mk .mov 32 [gr 32 6, .mem (mg (some 3) none 1 52 32)] 3) := by dec_rfl

/-- What the stretch does. -/
def o3 : List Op := [
  Op.ld 32 6 (some 3) none 1 52]

theorem b3 (prof : Profile) : Blk prof p3 0 3 o3 :=
  .cons (p3_0 _) (OpI.ld (.inl rfl)) (by decide) <|
  .nil 3

/-- The stretch at `46`. -/
def p4 : List Byte := [
  0x8b, 0x7b, 0x28, 0x83, 0xc5, 0x01]

theorem p4_0 : ∀ feat, Dec feat p4 0 (FV7z.mk .mov 32 [gr 32 7, .mem (mg (some 3) none 1 40 32)] 3) := by dec_rfl
theorem p4_3 : ∀ feat, Dec feat p4 3 (FV7z.mk .add 32 [gr 32 5, Src.opd 32 (.i 1)] 3) := by dec_rfl

/-- What the stretch does. -/
def o4 : List Op := [
  Op.ld 32 7 (some 3) none 1 40,
  Op.add 32 5 (.i 1)]

theorem b4 (prof : Profile) : Blk prof p4 0 6 o4 :=
  .cons (p4_0 _) (OpI.ld (.inl rfl)) (by decide) <|
  .cons (p4_3 _) (OpI.add (.i 1) (.inl rfl)) (by decide) <|
  .nil 6

/-- The stretch at `57`. -/
def p5 : List Byte := [
  0x41, 0x39, 0x6c, 0x24, 0x08]

theorem p5_0 : ∀ feat, Dec feat p5 0 (FV7z.mk .cmp 32 [.mem (mg (some 12) none 1 8 32), gr 32 5] 5) := by dec_rfl

/-- What the stretch does. -/
def o5 : List Op := [
  Op.cmpmr 32 (some 12) none 1 8 5]

theorem b5 (prof : Profile) : Blk prof p5 0 5 o5 :=
  .cons (p5_0 _) (OpI.cmpmr (.inl rfl)) (by decide) <|
  .nil 5

def j3 : List Byte := [0x76, 0x20]
theorem j3_0 : ∀ feat, Dec feat j3 0 (FV7z.mk (.jcc 6) 64 [.rel 32] 2) := by dec_rfl

/-- The stretch at `64`. -/
def p6 : List Byte := [
  0x49, 0x8b, 0x14, 0x24, 0x89, 0xe8, 0x48, 0x8b, 0x1c, 0xc2, 0x8b, 0x7b, 0x30, 0x8d, 0x47, 0xff,
  0x83, 0xf8, 0x1f]

theorem p6_0 : ∀ feat, Dec feat p6 0 (FV7z.mk .mov 64 [gr 64 2, .mem (mg (some 12) none 1 0 64)] 4) := by dec_rfl
theorem p6_4 : ∀ feat, Dec feat p6 4 (FV7z.mk .mov 32 [gr 32 0, Src.opd 32 (.r 5)] 2) := by dec_rfl
theorem p6_6 : ∀ feat, Dec feat p6 6 (FV7z.mk .mov 64 [gr 64 3, .mem (mg (some 2) (some 0) 8 0 64)] 4) := by dec_rfl
theorem p6_10 : ∀ feat, Dec feat p6 10 (FV7z.mk .mov 32 [gr 32 7, .mem (mg (some 3) none 1 48 32)] 3) := by dec_rfl
theorem p6_13 : ∀ feat, Dec feat p6 13 (FV7z.mk .lea 32 [gr 32 0, .mem (mg (some 7) none 1 18446744073709551615 0)] 3) := by dec_rfl
theorem p6_16 : ∀ feat, Dec feat p6 16 (FV7z.mk .cmp 32 [gr 32 0, Src.opd 32 (.i 31)] 3) := by dec_rfl

/-- What the stretch does. -/
def o6 : List Op := [
  Op.ld 64 2 (some 12) none 1 0,
  Op.mov 32 0 (.r 5),
  Op.ld 64 3 (some 2) (some 0) 8 0,
  Op.ld 32 7 (some 3) none 1 48,
  Op.lea 32 0 (some 7) none 1 18446744073709551615,
  Op.cmp 32 0 (.i 31)]

theorem b6 (prof : Profile) : Blk prof p6 0 19 o6 :=
  .cons (p6_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p6_4 _) (OpI.mov (.r 5) (.inl rfl)) (by decide) <|
  .cons (p6_6 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p6_10 _) (OpI.ld (.inl rfl)) (by decide) <|
  .cons (p6_13 _) (OpI.lea (.inl rfl)) (by decide) <|
  .cons (p6_16 _) (OpI.cmp (.i 31) (.inl rfl)) (by decide) <|
  .nil 19

def j4 : List Byte := [0x77, 0xcb]
theorem j4_0 : ∀ feat, Dec feat j4 0 (FV7z.mk (.jcc 7) 64 [.rel 18446744073709551563] 2) := by dec_rfl

def j5 : List Byte := [0xeb, 0xc4]
theorem j5_0 : ∀ feat, Dec feat j5 0 (FV7z.mk .jmp 64 [.rel 18446744073709551556] 2) := by dec_rfl

/-- The stretch at `96`. -/
def p7 : List Byte := [
  0x5b, 0x5d, 0x41, 0x5c]

theorem p7_0 : ∀ feat, Dec feat p7 0 (FV7z.mk .pop 64 [gr 64 3] 1) := by dec_rfl
theorem p7_1 : ∀ feat, Dec feat p7 1 (FV7z.mk .pop 64 [gr 64 5] 1) := by dec_rfl
theorem p7_2 : ∀ feat, Dec feat p7 2 (FV7z.mk .pop 64 [gr 64 12] 2) := by dec_rfl

/-- What the stretch does. -/
def o7 : List Op := [
  Op.pop 3,
  Op.pop 5,
  Op.pop 12]

theorem b7 (prof : Profile) : Blk prof p7 0 4 o7 :=
  .cons (p7_0 _) (OpI.pop) (by decide) <|
  .cons (p7_1 _) (OpI.pop) (by decide) <|
  .cons (p7_2 _) (OpI.pop) (by decide) <|
  .nil 4

end FV7z.Ptt
