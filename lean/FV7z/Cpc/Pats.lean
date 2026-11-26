import FV7z.Lemmas.Sp
import FV7z.Lemmas.BlkOps2
/-!
# The stretches of straight-line code of `NCommandLineParser::CParser::CParser` (PLAN.md §M, M1)

Each distinct stretch between labels and jumps (`p*`, 3 of them) and each distinct jump (`j*`, 0) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.Cpc
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The stretch at `0`. -/
def p0 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0x41, 0x55, 0x41, 0x54, 0x55, 0x53, 0x48, 0x89, 0xfb, 0x48, 0x8d, 0x7f,
  0x20, 0x48, 0x83, 0xec, 0x08, 0x48, 0xc7, 0x47, 0xe0, 0x00, 0x00, 0x00, 0x00, 0x48, 0xc7, 0x47,
  0xe8, 0x00, 0x00, 0x00, 0x00, 0x48, 0xc7, 0x47, 0xf0, 0x00, 0x00, 0x00, 0x00, 0xc7, 0x47, 0xf8,
  0xff, 0xff, 0xff, 0xff]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem p0_4 : ∀ feat, Dec feat p0 4 (FV7z.mk .push 64 [gr 64 13] 2) := by dec_rfl
theorem p0_6 : ∀ feat, Dec feat p0 6 (FV7z.mk .push 64 [gr 64 12] 2) := by dec_rfl
theorem p0_8 : ∀ feat, Dec feat p0 8 (FV7z.mk .push 64 [gr 64 5] 1) := by dec_rfl
theorem p0_9 : ∀ feat, Dec feat p0 9 (FV7z.mk .push 64 [gr 64 3] 1) := by dec_rfl
theorem p0_10 : ∀ feat, Dec feat p0 10 (FV7z.mk .mov 64 [gr 64 3, Src.opd 64 (.r 7)] 3) := by dec_rfl
theorem p0_13 : ∀ feat, Dec feat p0 13 (FV7z.mk .lea 64 [gr 64 7, .mem (mg (some 7) none 1 32 0)] 4) := by dec_rfl
theorem p0_17 : ∀ feat, Dec feat p0 17 (FV7z.mk .sub 64 [gr 64 4, Src.opd 64 (.i 8)] 4) := by dec_rfl
theorem p0_21 : ∀ feat, Dec feat p0 21 (FV7z.mk .mov 64 [.mem (mg (some 7) none 1 18446744073709551584 64), .imm 64 0] 8) := by dec_rfl
theorem p0_29 : ∀ feat, Dec feat p0 29 (FV7z.mk .mov 64 [.mem (mg (some 7) none 1 18446744073709551592 64), .imm 64 0] 8) := by dec_rfl
theorem p0_37 : ∀ feat, Dec feat p0 37 (FV7z.mk .mov 64 [.mem (mg (some 7) none 1 18446744073709551600 64), .imm 64 0] 8) := by dec_rfl
theorem p0_45 : ∀ feat, Dec feat p0 45 (FV7z.mk .mov 32 [.mem (mg (some 7) none 1 18446744073709551608 32), .imm 32 4294967295] 7) := by dec_rfl

/-- What the stretch does. -/
def o0 : List Op := [
  Op.nop,
  Op.push 13,
  Op.push 12,
  Op.push 5,
  Op.push 3,
  Op.mov 64 3 (.r 7),
  Op.lea 64 7 (some 7) none 1 32,
  Op.sub 64 4 (.i 8),
  Op.sti 64 (some 7) none 1 18446744073709551584 0,
  Op.sti 64 (some 7) none 1 18446744073709551592 0,
  Op.sti 64 (some 7) none 1 18446744073709551600 0,
  Op.sti 32 (some 7) none 1 18446744073709551608 4294967295]

theorem b0 (prof : Profile) : Blk prof p0 0 52 o0 :=
  .cons (p0_0 _) (OpI.endbr) (by decide) <|
  .cons (p0_4 _) (OpI.push) (by decide) <|
  .cons (p0_6 _) (OpI.push) (by decide) <|
  .cons (p0_8 _) (OpI.push) (by decide) <|
  .cons (p0_9 _) (OpI.push) (by decide) <|
  .cons (p0_10 _) (OpI.mov (.r 7) (.inr rfl)) (by decide) <|
  .cons (p0_13 _) (OpI.lea (.inr rfl)) (by decide) <|
  .cons (p0_17 _) (OpI.sub (.i 8) (.inr rfl)) (by decide) <|
  .cons (p0_21 _) (OpI.sti (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p0_29 _) (OpI.sti (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p0_37 _) (OpI.sti (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p0_45 _) (OpI.sti (.inr (.inr (.inl rfl)))) (by decide) <|
  .nil 52

/-- The stretch at `57`. -/
def p1 : List Byte := [
  0x48, 0x8d, 0x7b, 0x30]

theorem p1_0 : ∀ feat, Dec feat p1 0 (FV7z.mk .lea 64 [gr 64 7, .mem (mg (some 3) none 1 48 0)] 4) := by dec_rfl

/-- What the stretch does. -/
def o1 : List Op := [
  Op.lea 64 7 (some 3) none 1 48]

theorem b1 (prof : Profile) : Blk prof p1 0 4 o1 :=
  .cons (p1_0 _) (OpI.lea (.inr rfl)) (by decide) <|
  .nil 4

/-- The stretch at `66`. -/
def p2 : List Byte := [
  0x48, 0x83, 0xc4, 0x08, 0x5b, 0x5d, 0x41, 0x5c, 0x41, 0x5d]

theorem p2_0 : ∀ feat, Dec feat p2 0 (FV7z.mk .add 64 [gr 64 4, Src.opd 64 (.i 8)] 4) := by dec_rfl
theorem p2_4 : ∀ feat, Dec feat p2 4 (FV7z.mk .pop 64 [gr 64 3] 1) := by dec_rfl
theorem p2_5 : ∀ feat, Dec feat p2 5 (FV7z.mk .pop 64 [gr 64 5] 1) := by dec_rfl
theorem p2_6 : ∀ feat, Dec feat p2 6 (FV7z.mk .pop 64 [gr 64 12] 2) := by dec_rfl
theorem p2_8 : ∀ feat, Dec feat p2 8 (FV7z.mk .pop 64 [gr 64 13] 2) := by dec_rfl

/-- What the stretch does. -/
def o2 : List Op := [
  Op.add 64 4 (.i 8),
  Op.pop 3,
  Op.pop 5,
  Op.pop 12,
  Op.pop 13]

theorem b2 (prof : Profile) : Blk prof p2 0 10 o2 :=
  .cons (p2_0 _) (OpI.add (.i 8) (.inr rfl)) (by decide) <|
  .cons (p2_4 _) (OpI.pop) (by decide) <|
  .cons (p2_5 _) (OpI.pop) (by decide) <|
  .cons (p2_6 _) (OpI.pop) (by decide) <|
  .cons (p2_8 _) (OpI.pop) (by decide) <|
  .nil 10

end FV7z.Cpc
