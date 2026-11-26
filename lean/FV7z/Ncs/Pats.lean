import FV7z.Lemmas.Sp
import FV7z.Lemmas.BlkOps2
/-!
# The stretches of straight-line code of `CCensorNode::NeedCheckSubDirs` (PLAN.md §M, M1)

Each distinct stretch between labels and jumps (`p*`, 8 of them) and each distinct jump (`j*`, 6) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.Ncs
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The stretch at `0`. -/
def p0 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0x8b, 0x57, 0x30, 0x85, 0xd2]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem p0_4 : ∀ feat, Dec feat p0 4 (FV7z.mk .mov 32 [gr 32 2, .mem (mg (some 7) none 1 48 32)] 3) := by dec_rfl
theorem p0_7 : ∀ feat, Dec feat p0 7 (FV7z.mk .test 32 [gr 32 2, Src.opd 32 (.r 2)] 2) := by dec_rfl

/-- What the stretch does. -/
def o0 : List Op := [
  Op.nop,
  Op.ld 32 2 (some 7) none 1 48,
  Op.test 32 2 (.r 2)]

theorem b0 (prof : Profile) : Blk prof p0 0 9 o0 :=
  .cons (p0_0 _) (OpI.endbr) (by decide) <|
  .cons (p0_4 _) (OpI.ld (.inl rfl)) (by decide) <|
  .cons (p0_7 _) (OpI.test (.r 2) (.inl rfl)) (by decide) <|
  .nil 9

def j0 : List Byte := [0x74, 0x3f]
theorem j0_0 : ∀ feat, Dec feat j0 0 (FV7z.mk (.jcc 4) 64 [.rel 63] 2) := by dec_rfl

/-- The stretch at `11`. -/
def p1 : List Byte := [
  0x48, 0x8b, 0x47, 0x28, 0x83, 0xea, 0x01, 0x48, 0x8d, 0x4c, 0xd0, 0x08]

theorem p1_0 : ∀ feat, Dec feat p1 0 (FV7z.mk .mov 64 [gr 64 0, .mem (mg (some 7) none 1 40 64)] 4) := by dec_rfl
theorem p1_4 : ∀ feat, Dec feat p1 4 (FV7z.mk .sub 32 [gr 32 2, Src.opd 32 (.i 1)] 3) := by dec_rfl
theorem p1_7 : ∀ feat, Dec feat p1 7 (FV7z.mk .lea 64 [gr 64 1, .mem (mg (some 0) (some 2) 8 8 0)] 5) := by dec_rfl

/-- What the stretch does. -/
def o1 : List Op := [
  Op.ld 64 0 (some 7) none 1 40,
  Op.sub 32 2 (.i 1),
  Op.lea 64 1 (some 0) (some 2) 8 8]

theorem b1 (prof : Profile) : Blk prof p1 0 12 o1 :=
  .cons (p1_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p1_4 _) (OpI.sub (.i 1) (.inl rfl)) (by decide) <|
  .cons (p1_7 _) (OpI.lea (.inr rfl)) (by decide) <|
  .nil 12

def j1 : List Byte := [0xeb, 0x16]
theorem j1_0 : ∀ feat, Dec feat j1 0 (FV7z.mk .jmp 64 [.rel 22] 2) := by dec_rfl

/-- The stretch at `32`. -/
def p2 : List Byte := [
  0x83, 0x7a, 0x08, 0x01]

theorem p2_0 : ∀ feat, Dec feat p2 0 (FV7z.mk .cmp 32 [.mem (mg (some 2) none 1 8 32), .imm 32 1] 4) := by dec_rfl

/-- What the stretch does. -/
def o2 : List Op := [
  Op.cmpmi 32 (some 2) none 1 8 1]

theorem b2 (prof : Profile) : Blk prof p2 0 4 o2 :=
  .cons (p2_0 _) (OpI.cmpmi (.inr rfl)) (by decide) <|
  .nil 4

def j2 : List Byte := [0x77, 0x1a]
theorem j2_0 : ∀ feat, Dec feat j2 0 (FV7z.mk (.jcc 7) 64 [.rel 26] 2) := by dec_rfl

/-- The stretch at `38`. -/
def p3 : List Byte := [
  0x48, 0x83, 0xc0, 0x08, 0x48, 0x39, 0xc8]

theorem p3_0 : ∀ feat, Dec feat p3 0 (FV7z.mk .add 64 [gr 64 0, Src.opd 64 (.i 8)] 4) := by dec_rfl
theorem p3_4 : ∀ feat, Dec feat p3 4 (FV7z.mk .cmp 64 [gr 64 0, Src.opd 64 (.r 1)] 3) := by dec_rfl

/-- What the stretch does. -/
def o3 : List Op := [
  Op.add 64 0 (.i 8),
  Op.cmp 64 0 (.r 1)]

theorem b3 (prof : Profile) : Blk prof p3 0 7 o3 :=
  .cons (p3_0 _) (OpI.add (.i 8) (.inr rfl)) (by decide) <|
  .cons (p3_4 _) (OpI.cmp (.r 1) (.inr rfl)) (by decide) <|
  .nil 7

def j3 : List Byte := [0x74, 0x0d]
theorem j3_0 : ∀ feat, Dec feat j3 0 (FV7z.mk (.jcc 4) 64 [.rel 13] 2) := by dec_rfl

/-- The stretch at `47`. -/
def p4 : List Byte := [
  0x48, 0x8b, 0x10, 0x44, 0x0f, 0xb6, 0x42, 0x10, 0x45, 0x84, 0xc0]

theorem p4_0 : ∀ feat, Dec feat p4 0 (FV7z.mk .mov 64 [gr 64 2, .mem (mg (some 0) none 1 0 64)] 3) := by dec_rfl
theorem p4_3 : ∀ feat, Dec feat p4 3 (FV7z.mk .movzx 32 [gr 32 8, .mem (mg (some 2) none 1 16 8)] 5) := by dec_rfl
theorem p4_8 : ∀ feat, Dec feat p4 8 (FV7z.mk .test 8 [gr 8 8, Src.opd 8 (.r 8)] 3) := by dec_rfl

/-- What the stretch does. -/
def o4 : List Op := [
  Op.ld 64 2 (some 0) none 1 0,
  Op.ldzx 8 8 (some 2) none 1 16,
  Op.test 8 8 (.r 8)]

theorem b4 (prof : Profile) : Blk prof p4 0 11 o4 :=
  .cons (p4_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p4_3 _) (OpI.ldzx (.inl rfl)) (by decide) <|
  .cons (p4_8 _) (OpI.test8 (.r 8)) (by decide) <|
  .nil 11

def j4 : List Byte := [0x74, 0xe4]
theorem j4_0 : ∀ feat, Dec feat j4 0 (FV7z.mk (.jcc 4) 64 [.rel 18446744073709551588] 2) := by dec_rfl

/-- The stretch at `60`. -/
def p5 : List Byte := [
  0x44, 0x89, 0xc0]

theorem p5_0 : ∀ feat, Dec feat p5 0 (FV7z.mk .mov 32 [gr 32 0, Src.opd 32 (.r 8)] 3) := by dec_rfl

/-- What the stretch does. -/
def o5 : List Op := [
  Op.mov 32 0 (.r 8)]

theorem b5 (prof : Profile) : Blk prof p5 0 3 o5 :=
  .cons (p5_0 _) (OpI.mov (.r 8) (.inl rfl)) (by decide) <|
  .nil 3

/-- The stretch at `64`. -/
def p6 : List Byte := [
  0x41, 0xb8, 0x01, 0x00, 0x00, 0x00, 0x44, 0x89, 0xc0]

theorem p6_0 : ∀ feat, Dec feat p6 0 (FV7z.mk .mov 32 [gr 32 8, Src.opd 32 (.i 1)] 6) := by dec_rfl
theorem p6_6 : ∀ feat, Dec feat p6 6 (FV7z.mk .mov 32 [gr 32 0, Src.opd 32 (.r 8)] 3) := by dec_rfl

/-- What the stretch does. -/
def o6 : List Op := [
  Op.mov 32 8 (.i 1),
  Op.mov 32 0 (.r 8)]

theorem b6 (prof : Profile) : Blk prof p6 0 9 o6 :=
  .cons (p6_0 _) (OpI.mov (.i 1) (.inl rfl)) (by decide) <|
  .cons (p6_6 _) (OpI.mov (.r 8) (.inl rfl)) (by decide) <|
  .nil 9

/-- The stretch at `74`. -/
def p7 : List Byte := [
  0x45, 0x31, 0xc0]

theorem p7_0 : ∀ feat, Dec feat p7 0 (FV7z.mk .xor 32 [gr 32 8, Src.opd 32 (.r 8)] 3) := by dec_rfl

/-- What the stretch does. -/
def o7 : List Op := [
  Op.xor 32 8 (.r 8)]

theorem b7 (prof : Profile) : Blk prof p7 0 3 o7 :=
  .cons (p7_0 _) (OpI.xor (.r 8) (.inl rfl)) (by decide) <|
  .nil 3

def j5 : List Byte := [0xeb, 0xed]
theorem j5_0 : ∀ feat, Dec feat j5 0 (FV7z.mk .jmp 64 [.rel 18446744073709551597] 2) := by dec_rfl

end FV7z.Ncs
