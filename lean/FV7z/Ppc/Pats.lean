import FV7z.Lemmas.Sp
import FV7z.Lemmas.BlkOps2
/-!
# The stretches of straight-line code of `CPercentPrinter::CPercentPrinter` (PLAN.md §M, M1)

Each distinct stretch between labels and jumps (`p*`, 10 of them) and each distinct jump (`j*`, 0) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.Ppc
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The stretch at `0`. -/
def p0 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0x41, 0x54, 0x55, 0x48, 0x89, 0xfd, 0x48, 0x8d, 0x7f, 0x18, 0x53, 0x89,
  0xf3, 0x48, 0xc7, 0x47, 0xe8, 0x00, 0x00, 0x00, 0x00, 0x48, 0xc7, 0x47, 0xf0, 0xff, 0xff, 0xff,
  0xff, 0x48, 0xc7, 0x47, 0xf8, 0x00, 0x00, 0x00, 0x00]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem p0_4 : ∀ feat, Dec feat p0 4 (FV7z.mk .push 64 [gr 64 12] 2) := by dec_rfl
theorem p0_6 : ∀ feat, Dec feat p0 6 (FV7z.mk .push 64 [gr 64 5] 1) := by dec_rfl
theorem p0_7 : ∀ feat, Dec feat p0 7 (FV7z.mk .mov 64 [gr 64 5, Src.opd 64 (.r 7)] 3) := by dec_rfl
theorem p0_10 : ∀ feat, Dec feat p0 10 (FV7z.mk .lea 64 [gr 64 7, .mem (mg (some 7) none 1 24 0)] 4) := by dec_rfl
theorem p0_14 : ∀ feat, Dec feat p0 14 (FV7z.mk .push 64 [gr 64 3] 1) := by dec_rfl
theorem p0_15 : ∀ feat, Dec feat p0 15 (FV7z.mk .mov 32 [gr 32 3, Src.opd 32 (.r 6)] 2) := by dec_rfl
theorem p0_17 : ∀ feat, Dec feat p0 17 (FV7z.mk .mov 64 [.mem (mg (some 7) none 1 18446744073709551592 64), .imm 64 0] 8) := by dec_rfl
theorem p0_25 : ∀ feat, Dec feat p0 25 (FV7z.mk .mov 64 [.mem (mg (some 7) none 1 18446744073709551600 64), .imm 64 18446744073709551615] 8) := by dec_rfl
theorem p0_33 : ∀ feat, Dec feat p0 33 (FV7z.mk .mov 64 [.mem (mg (some 7) none 1 18446744073709551608 64), .imm 64 0] 8) := by dec_rfl

/-- What the stretch does. -/
def o0 : List Op := [
  Op.nop,
  Op.push 12,
  Op.push 5,
  Op.mov 64 5 (.r 7),
  Op.lea 64 7 (some 7) none 1 24,
  Op.push 3,
  Op.mov 32 3 (.r 6),
  Op.sti 64 (some 7) none 1 18446744073709551592 0,
  Op.sti 64 (some 7) none 1 18446744073709551600 18446744073709551615,
  Op.sti 64 (some 7) none 1 18446744073709551608 0]

theorem b0 (prof : Profile) : Blk prof p0 0 41 o0 :=
  .cons (p0_0 _) (OpI.endbr) (by decide) <|
  .cons (p0_4 _) (OpI.push) (by decide) <|
  .cons (p0_6 _) (OpI.push) (by decide) <|
  .cons (p0_7 _) (OpI.mov (.r 7) (.inr rfl)) (by decide) <|
  .cons (p0_10 _) (OpI.lea (.inr rfl)) (by decide) <|
  .cons (p0_14 _) (OpI.push) (by decide) <|
  .cons (p0_15 _) (OpI.mov (.r 6) (.inl rfl)) (by decide) <|
  .cons (p0_17 _) (OpI.sti (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p0_25 _) (OpI.sti (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p0_33 _) (OpI.sti (.inr (.inr (.inr rfl)))) (by decide) <|
  .nil 41

/-- The stretch at `46`. -/
def p1 : List Byte := [
  0x48, 0x8d, 0x7d, 0x28]

theorem p1_0 : ∀ feat, Dec feat p1 0 (FV7z.mk .lea 64 [gr 64 7, .mem (mg (some 5) none 1 40 0)] 4) := by dec_rfl

/-- What the stretch does. -/
def o1 : List Op := [
  Op.lea 64 7 (some 5) none 1 40]

theorem b1 (prof : Profile) : Blk prof p1 0 4 o1 :=
  .cons (p1_0 _) (OpI.lea (.inr rfl)) (by decide) <|
  .nil 4

/-- The stretch at `55`. -/
def p2 : List Byte := [
  0xb8, 0x00, 0x01, 0x00, 0x00, 0x89, 0x5d, 0x48, 0x48, 0x8d, 0x7d, 0x50, 0x66, 0x89, 0x45, 0x40,
  0xc7, 0x45, 0x44, 0x4f, 0x00, 0x00, 0x00, 0xc7, 0x45, 0x4c, 0x00, 0x00, 0x00, 0x00]

theorem p2_0 : ∀ feat, Dec feat p2 0 (FV7z.mk .mov 32 [gr 32 0, Src.opd 32 (.i 256)] 5) := by dec_rfl
theorem p2_5 : ∀ feat, Dec feat p2 5 (FV7z.mk .mov 32 [.mem (mg (some 5) none 1 72 32), gr 32 3] 3) := by dec_rfl
theorem p2_8 : ∀ feat, Dec feat p2 8 (FV7z.mk .lea 64 [gr 64 7, .mem (mg (some 5) none 1 80 0)] 4) := by dec_rfl
theorem p2_12 : ∀ feat, Dec feat p2 12 (FV7z.mk .mov 16 [.mem (mg (some 5) none 1 64 16), gr 16 0] 4) := by dec_rfl
theorem p2_16 : ∀ feat, Dec feat p2 16 (FV7z.mk .mov 32 [.mem (mg (some 5) none 1 68 32), .imm 32 79] 7) := by dec_rfl
theorem p2_23 : ∀ feat, Dec feat p2 23 (FV7z.mk .mov 32 [.mem (mg (some 5) none 1 76 32), .imm 32 0] 7) := by dec_rfl

/-- What the stretch does. -/
def o2 : List Op := [
  Op.mov 32 0 (.i 256),
  Op.st 32 (some 5) none 1 72 3,
  Op.lea 64 7 (some 5) none 1 80,
  Op.st 16 (some 5) none 1 64 0,
  Op.sti 32 (some 5) none 1 68 79,
  Op.sti 32 (some 5) none 1 76 0]

theorem b2 (prof : Profile) : Blk prof p2 0 30 o2 :=
  .cons (p2_0 _) (OpI.mov (.i 256) (.inl rfl)) (by decide) <|
  .cons (p2_5 _) (OpI.st (.inr (.inr (.inl rfl)))) (by decide) <|
  .cons (p2_8 _) (OpI.lea (.inr rfl)) (by decide) <|
  .cons (p2_12 _) (OpI.st (.inr (.inl rfl))) (by decide) <|
  .cons (p2_16 _) (OpI.sti (.inr (.inr (.inl rfl)))) (by decide) <|
  .cons (p2_23 _) (OpI.sti (.inr (.inr (.inl rfl)))) (by decide) <|
  .nil 30

/-- The stretch at `90`. -/
def p3 : List Byte := [
  0x48, 0x8d, 0x7d, 0x60]

theorem p3_0 : ∀ feat, Dec feat p3 0 (FV7z.mk .lea 64 [gr 64 7, .mem (mg (some 5) none 1 96 0)] 4) := by dec_rfl

/-- What the stretch does. -/
def o3 : List Op := [
  Op.lea 64 7 (some 5) none 1 96]

theorem b3 (prof : Profile) : Blk prof p3 0 4 o3 :=
  .cons (p3_0 _) (OpI.lea (.inr rfl)) (by decide) <|
  .nil 4

/-- The stretch at `99`. -/
def p4 : List Byte := [
  0x48, 0x8d, 0x7d, 0x70]

theorem p4_0 : ∀ feat, Dec feat p4 0 (FV7z.mk .lea 64 [gr 64 7, .mem (mg (some 5) none 1 112 0)] 4) := by dec_rfl

/-- What the stretch does. -/
def o4 : List Op := [
  Op.lea 64 7 (some 5) none 1 112]

theorem b4 (prof : Profile) : Blk prof p4 0 4 o4 :=
  .cons (p4_0 _) (OpI.lea (.inr rfl)) (by decide) <|
  .nil 4

/-- The stretch at `108`. -/
def p5 : List Byte := [
  0x48, 0x8d, 0xbd, 0x80, 0x00, 0x00, 0x00]

theorem p5_0 : ∀ feat, Dec feat p5 0 (FV7z.mk .lea 64 [gr 64 7, .mem (mg (some 5) none 1 128 0)] 7) := by dec_rfl

/-- What the stretch does. -/
def o5 : List Op := [
  Op.lea 64 7 (some 5) none 1 128]

theorem b5 (prof : Profile) : Blk prof p5 0 7 o5 :=
  .cons (p5_0 _) (OpI.lea (.inr rfl)) (by decide) <|
  .nil 7

/-- The stretch at `120`. -/
def p6 : List Byte := [
  0x48, 0xc7, 0x85, 0x90, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x48, 0x8d, 0xbd, 0xa8, 0x00,
  0x00, 0x00, 0x48, 0xc7, 0x85, 0x98, 0x00, 0x00, 0x00, 0xff, 0xff, 0xff, 0xff, 0x48, 0xc7, 0x85,
  0xa0, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00]

theorem p6_0 : ∀ feat, Dec feat p6 0 (FV7z.mk .mov 64 [.mem (mg (some 5) none 1 144 64), .imm 64 0] 11) := by dec_rfl
theorem p6_11 : ∀ feat, Dec feat p6 11 (FV7z.mk .lea 64 [gr 64 7, .mem (mg (some 5) none 1 168 0)] 7) := by dec_rfl
theorem p6_18 : ∀ feat, Dec feat p6 18 (FV7z.mk .mov 64 [.mem (mg (some 5) none 1 152 64), .imm 64 18446744073709551615] 11) := by dec_rfl
theorem p6_29 : ∀ feat, Dec feat p6 29 (FV7z.mk .mov 64 [.mem (mg (some 5) none 1 160 64), .imm 64 0] 11) := by dec_rfl

/-- What the stretch does. -/
def o6 : List Op := [
  Op.sti 64 (some 5) none 1 144 0,
  Op.lea 64 7 (some 5) none 1 168,
  Op.sti 64 (some 5) none 1 152 18446744073709551615,
  Op.sti 64 (some 5) none 1 160 0]

theorem b6 (prof : Profile) : Blk prof p6 0 40 o6 :=
  .cons (p6_0 _) (OpI.sti (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p6_11 _) (OpI.lea (.inr rfl)) (by decide) <|
  .cons (p6_18 _) (OpI.sti (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p6_29 _) (OpI.sti (.inr (.inr (.inr rfl)))) (by decide) <|
  .nil 40

/-- The stretch at `165`. -/
def p7 : List Byte := [
  0x48, 0x8d, 0xbd, 0xb8, 0x00, 0x00, 0x00]

theorem p7_0 : ∀ feat, Dec feat p7 0 (FV7z.mk .lea 64 [gr 64 7, .mem (mg (some 5) none 1 184 0)] 7) := by dec_rfl

/-- What the stretch does. -/
def o7 : List Op := [
  Op.lea 64 7 (some 5) none 1 184]

theorem b7 (prof : Profile) : Blk prof p7 0 7 o7 :=
  .cons (p7_0 _) (OpI.lea (.inr rfl)) (by decide) <|
  .nil 7

/-- The stretch at `177`. -/
def p8 : List Byte := [
  0x48, 0x8d, 0xbd, 0xc8, 0x00, 0x00, 0x00]

theorem p8_0 : ∀ feat, Dec feat p8 0 (FV7z.mk .lea 64 [gr 64 7, .mem (mg (some 5) none 1 200 0)] 7) := by dec_rfl

/-- What the stretch does. -/
def o8 : List Op := [
  Op.lea 64 7 (some 5) none 1 200]

theorem b8 (prof : Profile) : Blk prof p8 0 7 o8 :=
  .cons (p8_0 _) (OpI.lea (.inr rfl)) (by decide) <|
  .nil 7

/-- The stretch at `189`. -/
def p9 : List Byte := [
  0x5b, 0x5d, 0x41, 0x5c]

theorem p9_0 : ∀ feat, Dec feat p9 0 (FV7z.mk .pop 64 [gr 64 3] 1) := by dec_rfl
theorem p9_1 : ∀ feat, Dec feat p9 1 (FV7z.mk .pop 64 [gr 64 5] 1) := by dec_rfl
theorem p9_2 : ∀ feat, Dec feat p9 2 (FV7z.mk .pop 64 [gr 64 12] 2) := by dec_rfl

/-- What the stretch does. -/
def o9 : List Op := [
  Op.pop 3,
  Op.pop 5,
  Op.pop 12]

theorem b9 (prof : Profile) : Blk prof p9 0 4 o9 :=
  .cons (p9_0 _) (OpI.pop) (by decide) <|
  .cons (p9_1 _) (OpI.pop) (by decide) <|
  .cons (p9_2 _) (OpI.pop) (by decide) <|
  .nil 4

end FV7z.Ppc
