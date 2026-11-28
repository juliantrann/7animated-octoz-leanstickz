import FV7z.Lemmas.Sp
import FV7z.Lemmas.BlkOps2
/-!
# The stretches of straight-line code of `CStdOutStream::Convert_UString_to_AString` (PLAN.md §M, M1)

Each distinct stretch between labels and jumps (`p*`, 5 of them) and each distinct jump (`j*`, 2) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.Cua
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The stretch at `0`. -/
def p0 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0x49, 0x89, 0xf9, 0x48, 0x89, 0xd7, 0x49, 0x89, 0xf0, 0x41, 0x8b, 0x51,
  0x0c, 0x83, 0xfa, 0xff]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem p0_4 : ∀ feat, Dec feat p0 4 (FV7z.mk .mov 64 [gr 64 9, Src.opd 64 (.r 7)] 3) := by dec_rfl
theorem p0_7 : ∀ feat, Dec feat p0 7 (FV7z.mk .mov 64 [gr 64 7, Src.opd 64 (.r 2)] 3) := by dec_rfl
theorem p0_10 : ∀ feat, Dec feat p0 10 (FV7z.mk .mov 64 [gr 64 8, Src.opd 64 (.r 6)] 3) := by dec_rfl
theorem p0_13 : ∀ feat, Dec feat p0 13 (FV7z.mk .mov 32 [gr 32 2, .mem (mg (some 9) none 1 12 32)] 4) := by dec_rfl
theorem p0_17 : ∀ feat, Dec feat p0 17 (FV7z.mk .cmp 32 [gr 32 2, Src.opd 32 (.i 4294967295)] 3) := by dec_rfl

/-- What the stretch does. -/
def o0 : List Op := [
  Op.nop,
  Op.mov 64 9 (.r 7),
  Op.mov 64 7 (.r 2),
  Op.mov 64 8 (.r 6),
  Op.ld 32 2 (some 9) none 1 12,
  Op.cmp 32 2 (.i 4294967295)]

theorem b0 (prof : Profile) : Blk prof p0 0 20 o0 :=
  .cons (p0_0 _) (OpI.endbr) (by decide) <|
  .cons (p0_4 _) (OpI.mov (.r 7) (.inr rfl)) (by decide) <|
  .cons (p0_7 _) (OpI.mov (.r 2) (.inr rfl)) (by decide) <|
  .cons (p0_10 _) (OpI.mov (.r 6) (.inr rfl)) (by decide) <|
  .cons (p0_13 _) (OpI.ld (.inl rfl)) (by decide) <|
  .cons (p0_17 _) (OpI.cmp (.i 4294967295) (.inl rfl)) (by decide) <|
  .nil 20

def j0 : List Byte := [0x74, 0x1a]
theorem j0_0 : ∀ feat, Dec feat j0 0 (FV7z.mk (.jcc 4) 64 [.rel 26] 2) := by dec_rfl

/-- The stretch at `22`. -/
def p1 : List Byte := [
  0x81, 0xfa, 0xe9, 0xfd, 0x00, 0x00]

theorem p1_0 : ∀ feat, Dec feat p1 0 (FV7z.mk .cmp 32 [gr 32 2, Src.opd 32 (.i 65001)] 6) := by dec_rfl

/-- What the stretch does. -/
def o1 : List Op := [
  Op.cmp 32 2 (.i 65001)]

theorem b1 (prof : Profile) : Blk prof p1 0 6 o1 :=
  .cons (p1_0 _) (OpI.cmp (.i 65001) (.inl rfl)) (by decide) <|
  .nil 6

def j1 : List Byte := [0x74, 0x22]
theorem j1_0 : ∀ feat, Dec feat j1 0 (FV7z.mk (.jcc 4) 64 [.rel 34] 2) := by dec_rfl

/-- The stretch at `30`. -/
def p2 : List Byte := [
  0x4c, 0x89, 0xc6]

theorem p2_0 : ∀ feat, Dec feat p2 0 (FV7z.mk .mov 64 [gr 64 6, Src.opd 64 (.r 8)] 3) := by dec_rfl

/-- What the stretch does. -/
def o2 : List Op := [
  Op.mov 64 6 (.r 8)]

theorem b2 (prof : Profile) : Blk prof p2 0 3 o2 :=
  .cons (p2_0 _) (OpI.mov (.r 8) (.inr rfl)) (by decide) <|
  .nil 3

/-- The stretch at `48`. -/
def p3 : List Byte := [
  0xba, 0x01, 0x00, 0x00, 0x00, 0x4c, 0x89, 0xc6]

theorem p3_0 : ∀ feat, Dec feat p3 0 (FV7z.mk .mov 32 [gr 32 2, Src.opd 32 (.i 1)] 5) := by dec_rfl
theorem p3_5 : ∀ feat, Dec feat p3 5 (FV7z.mk .mov 64 [gr 64 6, Src.opd 64 (.r 8)] 3) := by dec_rfl

/-- What the stretch does. -/
def o3 : List Op := [
  Op.mov 32 2 (.i 1),
  Op.mov 64 6 (.r 8)]

theorem b3 (prof : Profile) : Blk prof p3 0 8 o3 :=
  .cons (p3_0 _) (OpI.mov (.i 1) (.inl rfl)) (by decide) <|
  .cons (p3_5 _) (OpI.mov (.r 8) (.inr rfl)) (by decide) <|
  .nil 8

/-- The stretch at `64`. -/
def p4 : List Byte := [
  0x48, 0x89, 0xfe, 0x4c, 0x89, 0xc7]

theorem p4_0 : ∀ feat, Dec feat p4 0 (FV7z.mk .mov 64 [gr 64 6, Src.opd 64 (.r 7)] 3) := by dec_rfl
theorem p4_3 : ∀ feat, Dec feat p4 3 (FV7z.mk .mov 64 [gr 64 7, Src.opd 64 (.r 8)] 3) := by dec_rfl

/-- What the stretch does. -/
def o4 : List Op := [
  Op.mov 64 6 (.r 7),
  Op.mov 64 7 (.r 8)]

theorem b4 (prof : Profile) : Blk prof p4 0 6 o4 :=
  .cons (p4_0 _) (OpI.mov (.r 7) (.inr rfl)) (by decide) <|
  .cons (p4_3 _) (OpI.mov (.r 8) (.inr rfl)) (by decide) <|
  .nil 6

end FV7z.Cua
