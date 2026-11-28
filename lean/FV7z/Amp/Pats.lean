import FV7z.Lemmas.Sp
import FV7z.Lemmas.BlkOps2
/-!
# The stretches of straight-line code of `Add_Messsage_Pre_ArcType(UString&, char const*, wchar_t const*)` (PLAN.md §M, M1)

Each distinct stretch between labels and jumps (`p*`, 5 of them) and each distinct jump (`j*`, 0) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.Amp
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The stretch at `0`. -/
def p0 : List Byte := [
  0x41, 0x55, 0x49, 0x89, 0xf5, 0x41, 0x54, 0x49, 0x89, 0xd4, 0x55, 0x48, 0x89, 0xfd]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .push 64 [gr 64 13] 2) := by dec_rfl
theorem p0_2 : ∀ feat, Dec feat p0 2 (FV7z.mk .mov 64 [gr 64 13, Src.opd 64 (.r 6)] 3) := by dec_rfl
theorem p0_5 : ∀ feat, Dec feat p0 5 (FV7z.mk .push 64 [gr 64 12] 2) := by dec_rfl
theorem p0_7 : ∀ feat, Dec feat p0 7 (FV7z.mk .mov 64 [gr 64 12, Src.opd 64 (.r 2)] 3) := by dec_rfl
theorem p0_10 : ∀ feat, Dec feat p0 10 (FV7z.mk .push 64 [gr 64 5] 1) := by dec_rfl
theorem p0_11 : ∀ feat, Dec feat p0 11 (FV7z.mk .mov 64 [gr 64 5, Src.opd 64 (.r 7)] 3) := by dec_rfl

/-- What the stretch does. -/
def o0 : List Op := [
  Op.push 13,
  Op.mov 64 13 (.r 6),
  Op.push 12,
  Op.mov 64 12 (.r 2),
  Op.push 5,
  Op.mov 64 5 (.r 7)]

theorem b0 (prof : Profile) : Blk prof p0 0 14 o0 :=
  .cons (p0_0 _) (OpI.push) (by decide) <|
  .cons (p0_2 _) (OpI.mov (.r 6) (.inr rfl)) (by decide) <|
  .cons (p0_5 _) (OpI.push) (by decide) <|
  .cons (p0_7 _) (OpI.mov (.r 2) (.inr rfl)) (by decide) <|
  .cons (p0_10 _) (OpI.push) (by decide) <|
  .cons (p0_11 _) (OpI.mov (.r 7) (.inr rfl)) (by decide) <|
  .nil 14

/-- The stretch at `19`. -/
def p1 : List Byte := [
  0x4c, 0x89, 0xee, 0x48, 0x89, 0xef]

theorem p1_0 : ∀ feat, Dec feat p1 0 (FV7z.mk .mov 64 [gr 64 6, Src.opd 64 (.r 13)] 3) := by dec_rfl
theorem p1_3 : ∀ feat, Dec feat p1 3 (FV7z.mk .mov 64 [gr 64 7, Src.opd 64 (.r 5)] 3) := by dec_rfl

/-- What the stretch does. -/
def o1 : List Op := [
  Op.mov 64 6 (.r 13),
  Op.mov 64 7 (.r 5)]

theorem b1 (prof : Profile) : Blk prof p1 0 6 o1 :=
  .cons (p1_0 _) (OpI.mov (.r 13) (.inr rfl)) (by decide) <|
  .cons (p1_3 _) (OpI.mov (.r 5) (.inr rfl)) (by decide) <|
  .nil 6

/-- The stretch at `30`. -/
def p2 : List Byte := [
  0x48, 0x89, 0xef, 0x48, 0x8d, 0x35, 0xcc, 0x28, 0x10, 0x00]

theorem p2_0 : ∀ feat, Dec feat p2 0 (FV7z.mk .mov 64 [gr 64 7, Src.opd 64 (.r 5)] 3) := by dec_rfl
theorem p2_3 : ∀ feat, Dec feat p2 3 (FV7z.mk .lea 64 [gr 64 6, .mem (mrip 1059020 0)] 7) := by dec_rfl

/-- What the stretch does. -/
def o2 : List Op := [
  Op.mov 64 7 (.r 5),
  Op.mov 64 6 (.i 7250756)]

theorem b2 (prof : Profile) : BlkA prof p2 (0x5e7a6e : Addr) 0 10 o2 :=
  .cons (p2_0 _) ((OpI.mov (.r 5) (.inr rfl)).at _) (by decide) <|
  .cons (p2_3 _) (OpIA.lea_rip (by decide)) (by decide) <|
  .nil 10

/-- The stretch at `45`. -/
def p3 : List Byte := [
  0x4c, 0x89, 0xe6, 0x48, 0x89, 0xef]

theorem p3_0 : ∀ feat, Dec feat p3 0 (FV7z.mk .mov 64 [gr 64 6, Src.opd 64 (.r 12)] 3) := by dec_rfl
theorem p3_3 : ∀ feat, Dec feat p3 3 (FV7z.mk .mov 64 [gr 64 7, Src.opd 64 (.r 5)] 3) := by dec_rfl

/-- What the stretch does. -/
def o3 : List Op := [
  Op.mov 64 6 (.r 12),
  Op.mov 64 7 (.r 5)]

theorem b3 (prof : Profile) : Blk prof p3 0 6 o3 :=
  .cons (p3_0 _) (OpI.mov (.r 12) (.inr rfl)) (by decide) <|
  .cons (p3_3 _) (OpI.mov (.r 5) (.inr rfl)) (by decide) <|
  .nil 6

/-- The stretch at `56`. -/
def p4 : List Byte := [
  0x48, 0x89, 0xef, 0x48, 0x8d, 0x35, 0x54, 0x20, 0x10, 0x00, 0x5d, 0x41, 0x5c, 0x41, 0x5d]

theorem p4_0 : ∀ feat, Dec feat p4 0 (FV7z.mk .mov 64 [gr 64 7, Src.opd 64 (.r 5)] 3) := by dec_rfl
theorem p4_3 : ∀ feat, Dec feat p4 3 (FV7z.mk .lea 64 [gr 64 6, .mem (mrip 1056852 0)] 7) := by dec_rfl
theorem p4_10 : ∀ feat, Dec feat p4 10 (FV7z.mk .pop 64 [gr 64 5] 1) := by dec_rfl
theorem p4_11 : ∀ feat, Dec feat p4 11 (FV7z.mk .pop 64 [gr 64 12] 2) := by dec_rfl
theorem p4_13 : ∀ feat, Dec feat p4 13 (FV7z.mk .pop 64 [gr 64 13] 2) := by dec_rfl

/-- What the stretch does. -/
def o4 : List Op := [
  Op.mov 64 7 (.r 5),
  Op.mov 64 6 (.i 7248614),
  Op.pop 5,
  Op.pop 12,
  Op.pop 13]

theorem b4 (prof : Profile) : BlkA prof p4 (0x5e7a88 : Addr) 0 15 o4 :=
  .cons (p4_0 _) ((OpI.mov (.r 5) (.inr rfl)).at _) (by decide) <|
  .cons (p4_3 _) (OpIA.lea_rip (by decide)) (by decide) <|
  .cons (p4_10 _) ((OpI.pop).at _) (by decide) <|
  .cons (p4_11 _) ((OpI.pop).at _) (by decide) <|
  .cons (p4_13 _) ((OpI.pop).at _) (by decide) <|
  .nil 15

end FV7z.Amp
