import FV7z.Lemmas.Sp
import FV7z.Lemmas.BlkOps3
/-!
# The stretches of straight-line code of `UString::TrimRight` (PLAN.md §M, M1)

Each distinct stretch between labels and jumps (`p*`, 8 of them) and each distinct jump (`j*`, 6) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.Utr
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The stretch at `0`. -/
def p0 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0x44, 0x8b, 0x4f, 0x08, 0x4c, 0x8b, 0x07, 0x45, 0x85, 0xc9]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem p0_4 : ∀ feat, Dec feat p0 4 (FV7z.mk .mov 32 [gr 32 9, .mem (mg (some 7) none 1 8 32)] 4) := by dec_rfl
theorem p0_8 : ∀ feat, Dec feat p0 8 (FV7z.mk .mov 64 [gr 64 8, .mem (mg (some 7) none 1 0 64)] 3) := by dec_rfl
theorem p0_11 : ∀ feat, Dec feat p0 11 (FV7z.mk .test 32 [gr 32 9, Src.opd 32 (.r 9)] 3) := by dec_rfl

/-- What the stretch does. -/
def o0 : List Op := [
  Op.nop,
  Op.ld 32 9 (some 7) none 1 8,
  Op.ld 64 8 (some 7) none 1 0,
  Op.test 32 9 (.r 9)]

theorem b0 (prof : Profile) : Blk prof p0 0 14 o0 :=
  .cons (p0_0 _) (OpI.endbr) (by decide) <|
  .cons (p0_4 _) (OpI.ld (.inl rfl)) (by decide) <|
  .cons (p0_8 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p0_11 _) (OpI.test (.r 9) (.inl rfl)) (by decide) <|
  .nil 14

def j0 : List Byte := [0x74, 0x35]
theorem j0_0 : ∀ feat, Dec feat j0 0 (FV7z.mk (.jcc 4) 64 [.rel 53] 2) := by dec_rfl

/-- The stretch at `16`. -/
def p1 : List Byte := [
  0x44, 0x89, 0xc8, 0x44, 0x89, 0xca, 0x48, 0xc1, 0xe0, 0x02, 0x66, 0x0f, 0x1f, 0x44, 0x00, 0x00]

theorem p1_0 : ∀ feat, Dec feat p1 0 (FV7z.mk .mov 32 [gr 32 0, Src.opd 32 (.r 9)] 3) := by dec_rfl
theorem p1_3 : ∀ feat, Dec feat p1 3 (FV7z.mk .mov 32 [gr 32 2, Src.opd 32 (.r 9)] 3) := by dec_rfl
theorem p1_6 : ∀ feat, Dec feat p1 6 (FV7z.mk .shl 64 [gr 64 0, Src.opd 8 (.i 2)] 4) := by dec_rfl
theorem p1_10 : ∀ feat, Dec feat p1 10 (FV7z.mk .nop 16 [.mem (mg (some 0) (some 0) 1 0 16)] 6) := by dec_rfl

/-- What the stretch does. -/
def o1 : List Op := [
  Op.mov 32 0 (.r 9),
  Op.mov 32 2 (.r 9),
  Op.shl64 0 (.i 2),
  Op.nop]

theorem b1 (prof : Profile) : Blk prof p1 0 16 o1 :=
  .cons (p1_0 _) (OpI.mov (.r 9) (.inl rfl)) (by decide) <|
  .cons (p1_3 _) (OpI.mov (.r 9) (.inl rfl)) (by decide) <|
  .cons (p1_6 _) (OpI.shl64 (.i 2)) (by decide) <|
  .cons (p1_10 _) (OpI.nop) (by decide) <|
  .nil 16

/-- The stretch at `32`. -/
def p2 : List Byte := [
  0x41, 0x8b, 0x4c, 0x00, 0xfc, 0x8d, 0x71, 0xf7, 0x83, 0xfe, 0x01]

theorem p2_0 : ∀ feat, Dec feat p2 0 (FV7z.mk .mov 32 [gr 32 1, .mem (mg (some 8) (some 0) 1 18446744073709551612 32)] 5) := by dec_rfl
theorem p2_5 : ∀ feat, Dec feat p2 5 (FV7z.mk .lea 32 [gr 32 6, .mem (mg (some 1) none 1 18446744073709551607 0)] 3) := by dec_rfl
theorem p2_8 : ∀ feat, Dec feat p2 8 (FV7z.mk .cmp 32 [gr 32 6, Src.opd 32 (.i 1)] 3) := by dec_rfl

/-- What the stretch does. -/
def o2 : List Op := [
  Op.ld 32 1 (some 8) (some 0) 1 18446744073709551612,
  Op.lea 32 6 (some 1) none 1 18446744073709551607,
  Op.cmp 32 6 (.i 1)]

theorem b2 (prof : Profile) : Blk prof p2 0 11 o2 :=
  .cons (p2_0 _) (OpI.ld (.inl rfl)) (by decide) <|
  .cons (p2_5 _) (OpI.lea (.inl rfl)) (by decide) <|
  .cons (p2_8 _) (OpI.cmp (.i 1) (.inl rfl)) (by decide) <|
  .nil 11

def j1 : List Byte := [0x76, 0x05]
theorem j1_0 : ∀ feat, Dec feat j1 0 (FV7z.mk (.jcc 6) 64 [.rel 5] 2) := by dec_rfl

/-- The stretch at `45`. -/
def p3 : List Byte := [
  0x83, 0xf9, 0x20]

theorem p3_0 : ∀ feat, Dec feat p3 0 (FV7z.mk .cmp 32 [gr 32 1, Src.opd 32 (.i 32)] 3) := by dec_rfl

/-- What the stretch does. -/
def o3 : List Op := [
  Op.cmp 32 1 (.i 32)]

theorem b3 (prof : Profile) : Blk prof p3 0 3 o3 :=
  .cons (p3_0 _) (OpI.cmp (.i 32) (.inl rfl)) (by decide) <|
  .nil 3

def j2 : List Byte := [0x75, 0x1e]
theorem j2_0 : ∀ feat, Dec feat j2 0 (FV7z.mk (.jcc 5) 64 [.rel 30] 2) := by dec_rfl

/-- The stretch at `50`. -/
def p4 : List Byte := [
  0x48, 0x83, 0xe8, 0x04, 0x83, 0xea, 0x01]

theorem p4_0 : ∀ feat, Dec feat p4 0 (FV7z.mk .sub 64 [gr 64 0, Src.opd 64 (.i 4)] 4) := by dec_rfl
theorem p4_4 : ∀ feat, Dec feat p4 4 (FV7z.mk .sub 32 [gr 32 2, Src.opd 32 (.i 1)] 3) := by dec_rfl

/-- What the stretch does. -/
def o4 : List Op := [
  Op.sub 64 0 (.i 4),
  Op.sub 32 2 (.i 1)]

theorem b4 (prof : Profile) : Blk prof p4 0 7 o4 :=
  .cons (p4_0 _) (OpI.sub (.i 4) (.inr rfl)) (by decide) <|
  .cons (p4_4 _) (OpI.sub (.i 1) (.inl rfl)) (by decide) <|
  .nil 7

def j3 : List Byte := [0x75, 0xe5]
theorem j3_0 : ∀ feat, Dec feat j3 0 (FV7z.mk (.jcc 5) 64 [.rel 18446744073709551589] 2) := by dec_rfl

/-- The stretch at `59`. -/
def p5 : List Byte := [
  0x41, 0xc7, 0x00, 0x00, 0x00, 0x00, 0x00, 0x89, 0x57, 0x08]

theorem p5_0 : ∀ feat, Dec feat p5 0 (FV7z.mk .mov 32 [.mem (mg (some 8) none 1 0 32), .imm 32 0] 7) := by dec_rfl
theorem p5_7 : ∀ feat, Dec feat p5 7 (FV7z.mk .mov 32 [.mem (mg (some 7) none 1 8 32), gr 32 2] 3) := by dec_rfl

/-- What the stretch does. -/
def o5 : List Op := [
  Op.sti 32 (some 8) none 1 0 0,
  Op.st 32 (some 7) none 1 8 2]

theorem b5 (prof : Profile) : Blk prof p5 0 10 o5 :=
  .cons (p5_0 _) (OpI.sti (.inr (.inr (.inl rfl)))) (by decide) <|
  .cons (p5_7 _) (OpI.st (.inr (.inr (.inl rfl)))) (by decide) <|
  .nil 10

/-- The stretch at `80`. -/
def p6 : List Byte := [
  0x41, 0x39, 0xd1]

theorem p6_0 : ∀ feat, Dec feat p6 0 (FV7z.mk .cmp 32 [gr 32 9, Src.opd 32 (.r 2)] 3) := by dec_rfl

/-- What the stretch does. -/
def o6 : List Op := [
  Op.cmp 32 9 (.r 2)]

theorem b6 (prof : Profile) : Blk prof p6 0 3 o6 :=
  .cons (p6_0 _) (OpI.cmp (.r 2) (.inl rfl)) (by decide) <|
  .nil 3

def j4 : List Byte := [0x74, 0xf0]
theorem j4_0 : ∀ feat, Dec feat j4 0 (FV7z.mk (.jcc 4) 64 [.rel 18446744073709551600] 2) := by dec_rfl

/-- The stretch at `85`. -/
def p7 : List Byte := [
  0x49, 0x01, 0xc0]

theorem p7_0 : ∀ feat, Dec feat p7 0 (FV7z.mk .add 64 [gr 64 8, Src.opd 64 (.r 0)] 3) := by dec_rfl

/-- What the stretch does. -/
def o7 : List Op := [
  Op.add 64 8 (.r 0)]

theorem b7 (prof : Profile) : Blk prof p7 0 3 o7 :=
  .cons (p7_0 _) (OpI.add (.r 0) (.inr rfl)) (by decide) <|
  .nil 3

def j5 : List Byte := [0xeb, 0xe1]
theorem j5_0 : ∀ feat, Dec feat j5 0 (FV7z.mk .jmp 64 [.rel 18446744073709551585] 2) := by dec_rfl

end FV7z.Utr
