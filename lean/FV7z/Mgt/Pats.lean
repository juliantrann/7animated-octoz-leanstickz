import FV7z.Lemmas.Sp
import FV7z.Lemmas.BlkOps2
/-!
# The stretches of straight-line code of `NWindows::NFile::NDir::MyGetTempPath` (PLAN.md §M, M1)

Each distinct stretch between labels and jumps (`p*`, 4 of them) and each distinct jump (`j*`, 0) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.Mgt
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The stretch at `0`. -/
def p0 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0x55, 0x48, 0x8d, 0x35, 0x01, 0x49, 0x28, 0x00, 0x48, 0x89, 0xfd]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem p0_4 : ∀ feat, Dec feat p0 4 (FV7z.mk .push 64 [gr 64 5] 1) := by dec_rfl
theorem p0_5 : ∀ feat, Dec feat p0 5 (FV7z.mk .lea 64 [gr 64 6, .mem (mrip 2640129 0)] 7) := by dec_rfl
theorem p0_12 : ∀ feat, Dec feat p0 12 (FV7z.mk .mov 64 [gr 64 5, Src.opd 64 (.r 7)] 3) := by dec_rfl

/-- What the stretch does. -/
def o0 : List Op := [
  Op.nop,
  Op.push 5,
  Op.mov 64 6 (.i 7181389),
  Op.mov 64 5 (.r 7)]

theorem b0 (prof : Profile) : BlkA prof p0 (0x454b40 : Addr) 0 15 o0 :=
  .cons (p0_0 _) ((OpI.endbr).at _) (by decide) <|
  .cons (p0_4 _) ((OpI.push).at _) (by decide) <|
  .cons (p0_5 _) (OpIA.lea_rip (by decide)) (by decide) <|
  .cons (p0_12 _) ((OpI.mov (.r 7) (.inr rfl)).at _) (by decide) <|
  .nil 15

/-- The stretch at `20`. -/
def p1 : List Byte := [
  0x48, 0x8b, 0x7d, 0x00, 0xbe, 0x01, 0x00, 0x00, 0x00]

theorem p1_0 : ∀ feat, Dec feat p1 0 (FV7z.mk .mov 64 [gr 64 7, .mem (mg (some 5) none 1 0 64)] 4) := by dec_rfl
theorem p1_4 : ∀ feat, Dec feat p1 4 (FV7z.mk .mov 32 [gr 32 6, Src.opd 32 (.i 1)] 5) := by dec_rfl

/-- What the stretch does. -/
def o1 : List Op := [
  Op.ld 64 7 (some 5) none 1 0,
  Op.mov 32 6 (.i 1)]

theorem b1 (prof : Profile) : Blk prof p1 0 9 o1 :=
  .cons (p1_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p1_4 _) (OpI.mov (.i 1) (.inl rfl)) (by decide) <|
  .nil 9

/-- The stretch at `34`. -/
def p2 : List Byte := [
  0x48, 0x8d, 0x35, 0xde, 0x48, 0x28, 0x00, 0x48, 0x89, 0xef, 0x84, 0xc0, 0x48, 0x8d, 0x05, 0xe1,
  0x9d, 0x29, 0x00, 0x48, 0x0f, 0x44, 0xf0]

theorem p2_0 : ∀ feat, Dec feat p2 0 (FV7z.mk .lea 64 [gr 64 6, .mem (mrip 2640094 0)] 7) := by dec_rfl
theorem p2_7 : ∀ feat, Dec feat p2 7 (FV7z.mk .mov 64 [gr 64 7, Src.opd 64 (.r 5)] 3) := by dec_rfl
theorem p2_10 : ∀ feat, Dec feat p2 10 (FV7z.mk .test 8 [gr 8 0, Src.opd 8 (.r 0)] 2) := by dec_rfl
theorem p2_12 : ∀ feat, Dec feat p2 12 (FV7z.mk .lea 64 [gr 64 0, .mem (mrip 2727393 0)] 7) := by dec_rfl
theorem p2_19 : ∀ feat, Dec feat p2 19 (FV7z.mk (.cmovcc 4) 64 [gr 64 6, gr 64 0] 4) := by dec_rfl

/-- What the stretch does. -/
def o2 : List Op := [
  Op.mov 64 6 (.i 7181383),
  Op.mov 64 7 (.r 5),
  Op.test 8 0 (.r 0),
  Op.mov 64 0 (.i 7268694),
  Op.cmov64 4 6 0]

theorem b2 (prof : Profile) : BlkA prof p2 (0x454b62 : Addr) 0 23 o2 :=
  .cons (p2_0 _) (OpIA.lea_rip (by decide)) (by decide) <|
  .cons (p2_7 _) ((OpI.mov (.r 5) (.inr rfl)).at _) (by decide) <|
  .cons (p2_10 _) ((OpI.test8 (.r 0)).at _) (by decide) <|
  .cons (p2_12 _) (OpIA.lea_rip (by decide)) (by decide) <|
  .cons (p2_19 _) ((OpI.cmov64).at _) (by decide) <|
  .nil 23

/-- The stretch at `62`. -/
def p3 : List Byte := [
  0xb8, 0x01, 0x00, 0x00, 0x00, 0x5d]

theorem p3_0 : ∀ feat, Dec feat p3 0 (FV7z.mk .mov 32 [gr 32 0, Src.opd 32 (.i 1)] 5) := by dec_rfl
theorem p3_5 : ∀ feat, Dec feat p3 5 (FV7z.mk .pop 64 [gr 64 5] 1) := by dec_rfl

/-- What the stretch does. -/
def o3 : List Op := [
  Op.mov 32 0 (.i 1),
  Op.pop 5]

theorem b3 (prof : Profile) : Blk prof p3 0 6 o3 :=
  .cons (p3_0 _) (OpI.mov (.i 1) (.inl rfl)) (by decide) <|
  .cons (p3_5 _) (OpI.pop) (by decide) <|
  .nil 6

end FV7z.Mgt
