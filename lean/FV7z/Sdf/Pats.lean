import FV7z.Lemmas.Sp
import FV7z.Lemmas.BlkOps2
/-!
# The stretches of straight-line code of `CFiTimesCAM::SetDirTime_to_FS` (PLAN.md §M, M1)

Each distinct stretch between labels and jumps (`p*`, 5 of them) and each distinct jump (`j*`, 1) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.Sdf
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The stretch at `0`. -/
def p0 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0x31, 0xc9, 0x80, 0x7f, 0x32, 0x00, 0x49, 0x89, 0xf0]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem p0_4 : ∀ feat, Dec feat p0 4 (FV7z.mk .xor 32 [gr 32 1, Src.opd 32 (.r 1)] 2) := by dec_rfl
theorem p0_6 : ∀ feat, Dec feat p0 6 (FV7z.mk .cmp 8 [.mem (mg (some 7) none 1 50 8), .imm 8 0] 4) := by dec_rfl
theorem p0_10 : ∀ feat, Dec feat p0 10 (FV7z.mk .mov 64 [gr 64 8, Src.opd 64 (.r 6)] 3) := by dec_rfl

/-- What the stretch does. -/
def o0 : List Op := [
  Op.nop,
  Op.xor 32 1 (.r 1),
  Op.cmpmi 8 (some 7) none 1 50 0,
  Op.mov 64 8 (.r 6)]

theorem b0 (prof : Profile) : Blk prof p0 0 13 o0 :=
  .cons (p0_0 _) (OpI.endbr) (by decide) <|
  .cons (p0_4 _) (OpI.xor (.r 1) (.inl rfl)) (by decide) <|
  .cons (p0_6 _) (OpI.cmpmi (.inl rfl)) (by decide) <|
  .cons (p0_10 _) (OpI.mov (.r 6) (.inr rfl)) (by decide) <|
  .nil 13

def j0 : List Byte := [0x74, 0x04]
theorem j0_0 : ∀ feat, Dec feat j0 0 (FV7z.mk (.jcc 4) 64 [.rel 4] 2) := by dec_rfl

/-- The stretch at `15`. -/
def p1 : List Byte := [
  0x48, 0x8d, 0x4f, 0x20]

theorem p1_0 : ∀ feat, Dec feat p1 0 (FV7z.mk .lea 64 [gr 64 1, .mem (mg (some 7) none 1 32 0)] 4) := by dec_rfl

/-- What the stretch does. -/
def o1 : List Op := [
  Op.lea 64 1 (some 7) none 1 32]

theorem b1 (prof : Profile) : Blk prof p1 0 4 o1 :=
  .cons (p1_0 _) (OpI.lea (.inr rfl)) (by decide) <|
  .nil 4

/-- The stretch at `19`. -/
def p2 : List Byte := [
  0x31, 0xd2, 0x80, 0x7f, 0x31, 0x00]

theorem p2_0 : ∀ feat, Dec feat p2 0 (FV7z.mk .xor 32 [gr 32 2, Src.opd 32 (.r 2)] 2) := by dec_rfl
theorem p2_2 : ∀ feat, Dec feat p2 2 (FV7z.mk .cmp 8 [.mem (mg (some 7) none 1 49 8), .imm 8 0] 4) := by dec_rfl

/-- What the stretch does. -/
def o2 : List Op := [
  Op.xor 32 2 (.r 2),
  Op.cmpmi 8 (some 7) none 1 49 0]

theorem b2 (prof : Profile) : Blk prof p2 0 6 o2 :=
  .cons (p2_0 _) (OpI.xor (.r 2) (.inl rfl)) (by decide) <|
  .cons (p2_2 _) (OpI.cmpmi (.inl rfl)) (by decide) <|
  .nil 6

/-- The stretch at `27`. -/
def p3 : List Byte := [
  0x48, 0x8d, 0x57, 0x10]

theorem p3_0 : ∀ feat, Dec feat p3 0 (FV7z.mk .lea 64 [gr 64 2, .mem (mg (some 7) none 1 16 0)] 4) := by dec_rfl

/-- What the stretch does. -/
def o3 : List Op := [
  Op.lea 64 2 (some 7) none 1 16]

theorem b3 (prof : Profile) : Blk prof p3 0 4 o3 :=
  .cons (p3_0 _) (OpI.lea (.inr rfl)) (by decide) <|
  .nil 4

/-- The stretch at `31`. -/
def p4 : List Byte := [
  0x80, 0x7f, 0x30, 0x00, 0xbe, 0x00, 0x00, 0x00, 0x00, 0x48, 0x0f, 0x45, 0xf7, 0x4c, 0x89, 0xc7]

theorem p4_0 : ∀ feat, Dec feat p4 0 (FV7z.mk .cmp 8 [.mem (mg (some 7) none 1 48 8), .imm 8 0] 4) := by dec_rfl
theorem p4_4 : ∀ feat, Dec feat p4 4 (FV7z.mk .mov 32 [gr 32 6, Src.opd 32 (.i 0)] 5) := by dec_rfl
theorem p4_9 : ∀ feat, Dec feat p4 9 (FV7z.mk (.cmovcc 5) 64 [gr 64 6, gr 64 7] 4) := by dec_rfl
theorem p4_13 : ∀ feat, Dec feat p4 13 (FV7z.mk .mov 64 [gr 64 7, Src.opd 64 (.r 8)] 3) := by dec_rfl

/-- What the stretch does. -/
def o4 : List Op := [
  Op.cmpmi 8 (some 7) none 1 48 0,
  Op.mov 32 6 (.i 0),
  Op.cmov64 5 6 7,
  Op.mov 64 7 (.r 8)]

theorem b4 (prof : Profile) : Blk prof p4 0 16 o4 :=
  .cons (p4_0 _) (OpI.cmpmi (.inl rfl)) (by decide) <|
  .cons (p4_4 _) (OpI.mov (.i 0) (.inl rfl)) (by decide) <|
  .cons (p4_9 _) (OpI.cmov64) (by decide) <|
  .cons (p4_13 _) (OpI.mov (.r 8) (.inr rfl)) (by decide) <|
  .nil 16

end FV7z.Sdf
