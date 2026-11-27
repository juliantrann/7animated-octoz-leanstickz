import FV7z.Lemmas.Sp
import FV7z.Lemmas.BlkOps2
/-!
# The stretches of straight-line code of `NWildcard::CCensorNode::AreAllAllowed` (PLAN.md §M, M1)

Each distinct stretch between labels and jumps (`p*`, 6 of them) and each distinct jump (`j*`, 4) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.Caa
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The stretch at `0`. -/
def p0 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0x8b, 0x4f, 0x10, 0x85, 0xc9]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem p0_4 : ∀ feat, Dec feat p0 4 (FV7z.mk .mov 32 [gr 32 1, .mem (mg (some 7) none 1 16 32)] 3) := by dec_rfl
theorem p0_7 : ∀ feat, Dec feat p0 7 (FV7z.mk .test 32 [gr 32 1, Src.opd 32 (.r 1)] 2) := by dec_rfl

/-- What the stretch does. -/
def o0 : List Op := [
  Op.nop,
  Op.ld 32 1 (some 7) none 1 16,
  Op.test 32 1 (.r 1)]

theorem b0 (prof : Profile) : Blk prof p0 0 9 o0 :=
  .cons (p0_0 _) (OpI.endbr) (by decide) <|
  .cons (p0_4 _) (OpI.ld (.inl rfl)) (by decide) <|
  .cons (p0_7 _) (OpI.test (.r 1) (.inl rfl)) (by decide) <|
  .nil 9

def j0 : List Byte := [0x75, 0x14]
theorem j0_0 : ∀ feat, Dec feat j0 0 (FV7z.mk (.jcc 5) 64 [.rel 20] 2) := by dec_rfl

/-- The stretch at `11`. -/
def p1 : List Byte := [
  0x8b, 0x57, 0x20, 0x85, 0xd2]

theorem p1_0 : ∀ feat, Dec feat p1 0 (FV7z.mk .mov 32 [gr 32 2, .mem (mg (some 7) none 1 32 32)] 3) := by dec_rfl
theorem p1_3 : ∀ feat, Dec feat p1 3 (FV7z.mk .test 32 [gr 32 2, Src.opd 32 (.r 2)] 2) := by dec_rfl

/-- What the stretch does. -/
def o1 : List Op := [
  Op.ld 32 2 (some 7) none 1 32,
  Op.test 32 2 (.r 2)]

theorem b1 (prof : Profile) : Blk prof p1 0 5 o1 :=
  .cons (p1_0 _) (OpI.ld (.inl rfl)) (by decide) <|
  .cons (p1_3 _) (OpI.test (.r 2) (.inl rfl)) (by decide) <|
  .nil 5

def j1 : List Byte := [0x75, 0x0d]
theorem j1_0 : ∀ feat, Dec feat j1 0 (FV7z.mk (.jcc 5) 64 [.rel 13] 2) := by dec_rfl

/-- The stretch at `18`. -/
def p2 : List Byte := [
  0x8b, 0x47, 0x40, 0x85, 0xc0]

theorem p2_0 : ∀ feat, Dec feat p2 0 (FV7z.mk .mov 32 [gr 32 0, .mem (mg (some 7) none 1 64 32)] 3) := by dec_rfl
theorem p2_3 : ∀ feat, Dec feat p2 3 (FV7z.mk .test 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl

/-- What the stretch does. -/
def o2 : List Op := [
  Op.ld 32 0 (some 7) none 1 64,
  Op.test 32 0 (.r 0)]

theorem b2 (prof : Profile) : Blk prof p2 0 5 o2 :=
  .cons (p2_0 _) (OpI.ld (.inl rfl)) (by decide) <|
  .cons (p2_3 _) (OpI.test (.r 0) (.inl rfl)) (by decide) <|
  .nil 5

def j2 : List Byte := [0x75, 0x06]
theorem j2_0 : ∀ feat, Dec feat j2 0 (FV7z.mk (.jcc 5) 64 [.rel 6] 2) := by dec_rfl

/-- The stretch at `25`. -/
def p3 : List Byte := [
  0x83, 0x7f, 0x30, 0x01]

theorem p3_0 : ∀ feat, Dec feat p3 0 (FV7z.mk .cmp 32 [.mem (mg (some 7) none 1 48 32), .imm 32 1] 4) := by dec_rfl

/-- What the stretch does. -/
def o3 : List Op := [
  Op.cmpmi 32 (some 7) none 1 48 1]

theorem b3 (prof : Profile) : Blk prof p3 0 4 o3 :=
  .cons (p3_0 _) (OpI.cmpmi (.inr rfl)) (by decide) <|
  .nil 4

def j3 : List Byte := [0x74, 0x09]
theorem j3_0 : ∀ feat, Dec feat j3 0 (FV7z.mk (.jcc 4) 64 [.rel 9] 2) := by dec_rfl

/-- The stretch at `31`. -/
def p4 : List Byte := [
  0x31, 0xc0]

theorem p4_0 : ∀ feat, Dec feat p4 0 (FV7z.mk .xor 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl

/-- What the stretch does. -/
def o4 : List Op := [
  Op.xor 32 0 (.r 0)]

theorem b4 (prof : Profile) : Blk prof p4 0 2 o4 :=
  .cons (p4_0 _) (OpI.xor (.r 0) (.inl rfl)) (by decide) <|
  .nil 2

/-- The stretch at `40`. -/
def p5 : List Byte := [
  0x48, 0x8b, 0x47, 0x28, 0x48, 0x8b, 0x38]

theorem p5_0 : ∀ feat, Dec feat p5 0 (FV7z.mk .mov 64 [gr 64 0, .mem (mg (some 7) none 1 40 64)] 4) := by dec_rfl
theorem p5_4 : ∀ feat, Dec feat p5 4 (FV7z.mk .mov 64 [gr 64 7, .mem (mg (some 0) none 1 0 64)] 3) := by dec_rfl

/-- What the stretch does. -/
def o5 : List Op := [
  Op.ld 64 0 (some 7) none 1 40,
  Op.ld 64 7 (some 0) none 1 0]

theorem b5 (prof : Profile) : Blk prof p5 0 7 o5 :=
  .cons (p5_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p5_4 _) (OpI.ld (.inr rfl)) (by decide) <|
  .nil 7

end FV7z.Caa
