import FV7z.Lemmas.Sp
import FV7z.Lemmas.BlkOps2
/-!
# The stretches of straight-line code of `CPercentPrinter::~CPercentPrinter` (PLAN.md §M, M1)

Each distinct stretch between labels and jumps (`p*`, 11 of them) and each distinct jump (`j*`, 2) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.Ppd
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The stretch at `0`. -/
def p0 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0x53, 0x31, 0xf6, 0x48, 0x89, 0xfb]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem p0_4 : ∀ feat, Dec feat p0 4 (FV7z.mk .push 64 [gr 64 3] 1) := by dec_rfl
theorem p0_5 : ∀ feat, Dec feat p0 5 (FV7z.mk .xor 32 [gr 32 6, Src.opd 32 (.r 6)] 2) := by dec_rfl
theorem p0_7 : ∀ feat, Dec feat p0 7 (FV7z.mk .mov 64 [gr 64 3, Src.opd 64 (.r 7)] 3) := by dec_rfl

/-- What the stretch does. -/
def o0 : List Op := [
  Op.nop,
  Op.push 3,
  Op.xor 32 6 (.r 6),
  Op.mov 64 3 (.r 7)]

theorem b0 (prof : Profile) : Blk prof p0 0 10 o0 :=
  .cons (p0_0 _) (OpI.endbr) (by decide) <|
  .cons (p0_4 _) (OpI.push) (by decide) <|
  .cons (p0_5 _) (OpI.xor (.r 6) (.inl rfl)) (by decide) <|
  .cons (p0_7 _) (OpI.mov (.r 7) (.inr rfl)) (by decide) <|
  .nil 10

/-- The stretch at `15`. -/
def p1 : List Byte := [
  0x48, 0x8b, 0xbb, 0xc8, 0x00, 0x00, 0x00, 0x48, 0x85, 0xff]

theorem p1_0 : ∀ feat, Dec feat p1 0 (FV7z.mk .mov 64 [gr 64 7, .mem (mg (some 3) none 1 200 64)] 7) := by dec_rfl
theorem p1_7 : ∀ feat, Dec feat p1 7 (FV7z.mk .test 64 [gr 64 7, Src.opd 64 (.r 7)] 3) := by dec_rfl

/-- What the stretch does. -/
def o1 : List Op := [
  Op.ld 64 7 (some 3) none 1 200,
  Op.test 64 7 (.r 7)]

theorem b1 (prof : Profile) : Blk prof p1 0 10 o1 :=
  .cons (p1_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p1_7 _) (OpI.test (.r 7) (.inr rfl)) (by decide) <|
  .nil 10

def j0 : List Byte := [0x74, 0x05]
theorem j0_0 : ∀ feat, Dec feat j0 0 (FV7z.mk (.jcc 4) 64 [.rel 5] 2) := by dec_rfl

/-- The stretch at `32`. -/
def p2 : List Byte := [
  0x48, 0x8b, 0xbb, 0xb8, 0x00, 0x00, 0x00, 0x48, 0x85, 0xff]

theorem p2_0 : ∀ feat, Dec feat p2 0 (FV7z.mk .mov 64 [gr 64 7, .mem (mg (some 3) none 1 184 64)] 7) := by dec_rfl
theorem p2_7 : ∀ feat, Dec feat p2 7 (FV7z.mk .test 64 [gr 64 7, Src.opd 64 (.r 7)] 3) := by dec_rfl

/-- What the stretch does. -/
def o2 : List Op := [
  Op.ld 64 7 (some 3) none 1 184,
  Op.test 64 7 (.r 7)]

theorem b2 (prof : Profile) : Blk prof p2 0 10 o2 :=
  .cons (p2_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p2_7 _) (OpI.test (.r 7) (.inr rfl)) (by decide) <|
  .nil 10

/-- The stretch at `49`. -/
def p3 : List Byte := [
  0x48, 0x8b, 0xbb, 0xa8, 0x00, 0x00, 0x00, 0x48, 0x85, 0xff]

theorem p3_0 : ∀ feat, Dec feat p3 0 (FV7z.mk .mov 64 [gr 64 7, .mem (mg (some 3) none 1 168 64)] 7) := by dec_rfl
theorem p3_7 : ∀ feat, Dec feat p3 7 (FV7z.mk .test 64 [gr 64 7, Src.opd 64 (.r 7)] 3) := by dec_rfl

/-- What the stretch does. -/
def o3 : List Op := [
  Op.ld 64 7 (some 3) none 1 168,
  Op.test 64 7 (.r 7)]

theorem b3 (prof : Profile) : Blk prof p3 0 10 o3 :=
  .cons (p3_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p3_7 _) (OpI.test (.r 7) (.inr rfl)) (by decide) <|
  .nil 10

/-- The stretch at `66`. -/
def p4 : List Byte := [
  0x48, 0x8b, 0xbb, 0x80, 0x00, 0x00, 0x00, 0x48, 0x85, 0xff]

theorem p4_0 : ∀ feat, Dec feat p4 0 (FV7z.mk .mov 64 [gr 64 7, .mem (mg (some 3) none 1 128 64)] 7) := by dec_rfl
theorem p4_7 : ∀ feat, Dec feat p4 7 (FV7z.mk .test 64 [gr 64 7, Src.opd 64 (.r 7)] 3) := by dec_rfl

/-- What the stretch does. -/
def o4 : List Op := [
  Op.ld 64 7 (some 3) none 1 128,
  Op.test 64 7 (.r 7)]

theorem b4 (prof : Profile) : Blk prof p4 0 10 o4 :=
  .cons (p4_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p4_7 _) (OpI.test (.r 7) (.inr rfl)) (by decide) <|
  .nil 10

/-- The stretch at `83`. -/
def p5 : List Byte := [
  0x48, 0x8b, 0x7b, 0x70, 0x48, 0x85, 0xff]

theorem p5_0 : ∀ feat, Dec feat p5 0 (FV7z.mk .mov 64 [gr 64 7, .mem (mg (some 3) none 1 112 64)] 4) := by dec_rfl
theorem p5_4 : ∀ feat, Dec feat p5 4 (FV7z.mk .test 64 [gr 64 7, Src.opd 64 (.r 7)] 3) := by dec_rfl

/-- What the stretch does. -/
def o5 : List Op := [
  Op.ld 64 7 (some 3) none 1 112,
  Op.test 64 7 (.r 7)]

theorem b5 (prof : Profile) : Blk prof p5 0 7 o5 :=
  .cons (p5_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p5_4 _) (OpI.test (.r 7) (.inr rfl)) (by decide) <|
  .nil 7

/-- The stretch at `97`. -/
def p6 : List Byte := [
  0x48, 0x8b, 0x7b, 0x60, 0x48, 0x85, 0xff]

theorem p6_0 : ∀ feat, Dec feat p6 0 (FV7z.mk .mov 64 [gr 64 7, .mem (mg (some 3) none 1 96 64)] 4) := by dec_rfl
theorem p6_4 : ∀ feat, Dec feat p6 4 (FV7z.mk .test 64 [gr 64 7, Src.opd 64 (.r 7)] 3) := by dec_rfl

/-- What the stretch does. -/
def o6 : List Op := [
  Op.ld 64 7 (some 3) none 1 96,
  Op.test 64 7 (.r 7)]

theorem b6 (prof : Profile) : Blk prof p6 0 7 o6 :=
  .cons (p6_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p6_4 _) (OpI.test (.r 7) (.inr rfl)) (by decide) <|
  .nil 7

/-- The stretch at `111`. -/
def p7 : List Byte := [
  0x48, 0x8b, 0x7b, 0x50, 0x48, 0x85, 0xff]

theorem p7_0 : ∀ feat, Dec feat p7 0 (FV7z.mk .mov 64 [gr 64 7, .mem (mg (some 3) none 1 80 64)] 4) := by dec_rfl
theorem p7_4 : ∀ feat, Dec feat p7 4 (FV7z.mk .test 64 [gr 64 7, Src.opd 64 (.r 7)] 3) := by dec_rfl

/-- What the stretch does. -/
def o7 : List Op := [
  Op.ld 64 7 (some 3) none 1 80,
  Op.test 64 7 (.r 7)]

theorem b7 (prof : Profile) : Blk prof p7 0 7 o7 :=
  .cons (p7_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p7_4 _) (OpI.test (.r 7) (.inr rfl)) (by decide) <|
  .nil 7

/-- The stretch at `125`. -/
def p8 : List Byte := [
  0x48, 0x8b, 0x7b, 0x28, 0x48, 0x85, 0xff]

theorem p8_0 : ∀ feat, Dec feat p8 0 (FV7z.mk .mov 64 [gr 64 7, .mem (mg (some 3) none 1 40 64)] 4) := by dec_rfl
theorem p8_4 : ∀ feat, Dec feat p8 4 (FV7z.mk .test 64 [gr 64 7, Src.opd 64 (.r 7)] 3) := by dec_rfl

/-- What the stretch does. -/
def o8 : List Op := [
  Op.ld 64 7 (some 3) none 1 40,
  Op.test 64 7 (.r 7)]

theorem b8 (prof : Profile) : Blk prof p8 0 7 o8 :=
  .cons (p8_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p8_4 _) (OpI.test (.r 7) (.inr rfl)) (by decide) <|
  .nil 7

/-- The stretch at `139`. -/
def p9 : List Byte := [
  0x48, 0x8b, 0x7b, 0x18, 0x48, 0x85, 0xff]

theorem p9_0 : ∀ feat, Dec feat p9 0 (FV7z.mk .mov 64 [gr 64 7, .mem (mg (some 3) none 1 24 64)] 4) := by dec_rfl
theorem p9_4 : ∀ feat, Dec feat p9 4 (FV7z.mk .test 64 [gr 64 7, Src.opd 64 (.r 7)] 3) := by dec_rfl

/-- What the stretch does. -/
def o9 : List Op := [
  Op.ld 64 7 (some 3) none 1 24,
  Op.test 64 7 (.r 7)]

theorem b9 (prof : Profile) : Blk prof p9 0 7 o9 :=
  .cons (p9_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p9_4 _) (OpI.test (.r 7) (.inr rfl)) (by decide) <|
  .nil 7

def j1 : List Byte := [0x74, 0x0c]
theorem j1_0 : ∀ feat, Dec feat j1 0 (FV7z.mk (.jcc 4) 64 [.rel 12] 2) := by dec_rfl

/-- The stretch at `148`. -/
def p10 : List Byte := [
  0x5b]

theorem p10_0 : ∀ feat, Dec feat p10 0 (FV7z.mk .pop 64 [gr 64 3] 1) := by dec_rfl

/-- What the stretch does. -/
def o10 : List Op := [
  Op.pop 3]

theorem b10 (prof : Profile) : Blk prof p10 0 1 o10 :=
  .cons (p10_0 _) (OpI.pop) (by decide) <|
  .nil 1

end FV7z.Ppd
