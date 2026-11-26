import FV7z.Lemmas.Sp
import FV7z.Lemmas.BlkOps2
/-!
# The stretches of straight-line code of `NArchive::NLzma::CHandler::Close` (PLAN.md §M, M1)

Each distinct stretch between labels and jumps (`p*`, 6 of them) and each distinct jump (`j*`, 1) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.Hcl
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The stretch at `0`. -/
def p0 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0x53, 0x48, 0x89, 0xfb, 0x48, 0xc7, 0x47, 0x15, 0x00, 0x00, 0x00, 0x00,
  0xc6, 0x47, 0x1d, 0x00, 0x48, 0xc7, 0x47, 0x40, 0x00, 0x00, 0x00, 0x00, 0x48, 0x8b, 0x7f, 0x30,
  0x48, 0x85, 0xff]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem p0_4 : ∀ feat, Dec feat p0 4 (FV7z.mk .push 64 [gr 64 3] 1) := by dec_rfl
theorem p0_5 : ∀ feat, Dec feat p0 5 (FV7z.mk .mov 64 [gr 64 3, Src.opd 64 (.r 7)] 3) := by dec_rfl
theorem p0_8 : ∀ feat, Dec feat p0 8 (FV7z.mk .mov 64 [.mem (mg (some 7) none 1 21 64), .imm 64 0] 8) := by dec_rfl
theorem p0_16 : ∀ feat, Dec feat p0 16 (FV7z.mk .mov 8 [.mem (mg (some 7) none 1 29 8), .imm 8 0] 4) := by dec_rfl
theorem p0_20 : ∀ feat, Dec feat p0 20 (FV7z.mk .mov 64 [.mem (mg (some 7) none 1 64 64), .imm 64 0] 8) := by dec_rfl
theorem p0_28 : ∀ feat, Dec feat p0 28 (FV7z.mk .mov 64 [gr 64 7, .mem (mg (some 7) none 1 48 64)] 4) := by dec_rfl
theorem p0_32 : ∀ feat, Dec feat p0 32 (FV7z.mk .test 64 [gr 64 7, Src.opd 64 (.r 7)] 3) := by dec_rfl

/-- What the stretch does. -/
def o0 : List Op := [
  Op.nop,
  Op.push 3,
  Op.mov 64 3 (.r 7),
  Op.sti 64 (some 7) none 1 21 0,
  Op.sti 8 (some 7) none 1 29 0,
  Op.sti 64 (some 7) none 1 64 0,
  Op.ld 64 7 (some 7) none 1 48,
  Op.test 64 7 (.r 7)]

theorem b0 (prof : Profile) : Blk prof p0 0 35 o0 :=
  .cons (p0_0 _) (OpI.endbr) (by decide) <|
  .cons (p0_4 _) (OpI.push) (by decide) <|
  .cons (p0_5 _) (OpI.mov (.r 7) (.inr rfl)) (by decide) <|
  .cons (p0_8 _) (OpI.sti (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p0_16 _) (OpI.sti (.inl rfl)) (by decide) <|
  .cons (p0_20 _) (OpI.sti (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p0_28 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p0_32 _) (OpI.test (.r 7) (.inr rfl)) (by decide) <|
  .nil 35

def j0 : List Byte := [0x74, 0x0e]
theorem j0_0 : ∀ feat, Dec feat j0 0 (FV7z.mk (.jcc 4) 64 [.rel 14] 2) := by dec_rfl

/-- The stretch at `37`. -/
def p1 : List Byte := [
  0x48, 0x8b, 0x07]

theorem p1_0 : ∀ feat, Dec feat p1 0 (FV7z.mk .mov 64 [gr 64 0, .mem (mg (some 7) none 1 0 64)] 3) := by dec_rfl

/-- What the stretch does. -/
def o1 : List Op := [
  Op.ld 64 0 (some 7) none 1 0]

theorem b1 (prof : Profile) : Blk prof p1 0 3 o1 :=
  .cons (p1_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .nil 3

/-- The stretch at `43`. -/
def p2 : List Byte := [
  0x48, 0xc7, 0x43, 0x30, 0x00, 0x00, 0x00, 0x00]

theorem p2_0 : ∀ feat, Dec feat p2 0 (FV7z.mk .mov 64 [.mem (mg (some 3) none 1 48 64), .imm 64 0] 8) := by dec_rfl

/-- What the stretch does. -/
def o2 : List Op := [
  Op.sti 64 (some 3) none 1 48 0]

theorem b2 (prof : Profile) : Blk prof p2 0 8 o2 :=
  .cons (p2_0 _) (OpI.sti (.inr (.inr (.inr rfl)))) (by decide) <|
  .nil 8

/-- The stretch at `51`. -/
def p3 : List Byte := [
  0x48, 0x8b, 0x7b, 0x38, 0x48, 0x85, 0xff]

theorem p3_0 : ∀ feat, Dec feat p3 0 (FV7z.mk .mov 64 [gr 64 7, .mem (mg (some 3) none 1 56 64)] 4) := by dec_rfl
theorem p3_4 : ∀ feat, Dec feat p3 4 (FV7z.mk .test 64 [gr 64 7, Src.opd 64 (.r 7)] 3) := by dec_rfl

/-- What the stretch does. -/
def o3 : List Op := [
  Op.ld 64 7 (some 3) none 1 56,
  Op.test 64 7 (.r 7)]

theorem b3 (prof : Profile) : Blk prof p3 0 7 o3 :=
  .cons (p3_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p3_4 _) (OpI.test (.r 7) (.inr rfl)) (by decide) <|
  .nil 7

/-- The stretch at `66`. -/
def p4 : List Byte := [
  0x48, 0xc7, 0x43, 0x38, 0x00, 0x00, 0x00, 0x00]

theorem p4_0 : ∀ feat, Dec feat p4 0 (FV7z.mk .mov 64 [.mem (mg (some 3) none 1 56 64), .imm 64 0] 8) := by dec_rfl

/-- What the stretch does. -/
def o4 : List Op := [
  Op.sti 64 (some 3) none 1 56 0]

theorem b4 (prof : Profile) : Blk prof p4 0 8 o4 :=
  .cons (p4_0 _) (OpI.sti (.inr (.inr (.inr rfl)))) (by decide) <|
  .nil 8

/-- The stretch at `74`. -/
def p5 : List Byte := [
  0x31, 0xc0, 0x5b]

theorem p5_0 : ∀ feat, Dec feat p5 0 (FV7z.mk .xor 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl
theorem p5_2 : ∀ feat, Dec feat p5 2 (FV7z.mk .pop 64 [gr 64 3] 1) := by dec_rfl

/-- What the stretch does. -/
def o5 : List Op := [
  Op.xor 32 0 (.r 0),
  Op.pop 3]

theorem b5 (prof : Profile) : Blk prof p5 0 3 o5 :=
  .cons (p5_0 _) (OpI.xor (.r 0) (.inl rfl)) (by decide) <|
  .cons (p5_2 _) (OpI.pop) (by decide) <|
  .nil 3

end FV7z.Hcl
