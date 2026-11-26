import FV7z.Lemmas.Sp
import FV7z.Lemmas.BlkOps2
/-!
# The stretches of straight-line code of `CreateArc` (PLAN.md §M, M1)

Each distinct stretch between labels and jumps (`p*`, 2 of them) and each distinct jump (`j*`, 0) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.Cra
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The stretch at `0`. -/
def p0 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0x48, 0x83, 0xec, 0x08, 0xbf, 0x58, 0x00, 0x00, 0x00]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem p0_4 : ∀ feat, Dec feat p0 4 (FV7z.mk .sub 64 [gr 64 4, Src.opd 64 (.i 8)] 4) := by dec_rfl
theorem p0_8 : ∀ feat, Dec feat p0 8 (FV7z.mk .mov 32 [gr 32 7, Src.opd 32 (.i 88)] 5) := by dec_rfl

/-- What the stretch does. -/
def o0 : List Op := [
  Op.nop,
  Op.sub 64 4 (.i 8),
  Op.mov 32 7 (.i 88)]

theorem b0 (prof : Profile) : Blk prof p0 0 13 o0 :=
  .cons (p0_0 _) (OpI.endbr) (by decide) <|
  .cons (p0_4 _) (OpI.sub (.i 8) (.inr rfl)) (by decide) <|
  .cons (p0_8 _) (OpI.mov (.i 88) (.inl rfl)) (by decide) <|
  .nil 13

/-- The stretch at `18`. -/
def p1 : List Byte := [
  0x48, 0xc7, 0xc2, 0xa0, 0x5f, 0x78, 0x00, 0xc7, 0x40, 0x10, 0x00, 0x00, 0x00, 0x00, 0x48, 0x8d,
  0x4a, 0x10, 0x48, 0x81, 0xc2, 0x90, 0x00, 0x00, 0x00, 0x48, 0xc7, 0x40, 0x30, 0x00, 0x00, 0x00,
  0x00, 0x48, 0x89, 0x08, 0x48, 0x89, 0x50, 0x08, 0x48, 0xc7, 0x40, 0x38, 0x00, 0x00, 0x00, 0x00,
  0xc6, 0x40, 0x14, 0x00, 0x48, 0x83, 0xc4, 0x08]

theorem p1_0 : ∀ feat, Dec feat p1 0 (FV7z.mk .mov 64 [gr 64 2, Src.opd 64 (.i 7888800)] 7) := by dec_rfl
theorem p1_7 : ∀ feat, Dec feat p1 7 (FV7z.mk .mov 32 [.mem (mg (some 0) none 1 16 32), .imm 32 0] 7) := by dec_rfl
theorem p1_14 : ∀ feat, Dec feat p1 14 (FV7z.mk .lea 64 [gr 64 1, .mem (mg (some 2) none 1 16 0)] 4) := by dec_rfl
theorem p1_18 : ∀ feat, Dec feat p1 18 (FV7z.mk .add 64 [gr 64 2, Src.opd 64 (.i 144)] 7) := by dec_rfl
theorem p1_25 : ∀ feat, Dec feat p1 25 (FV7z.mk .mov 64 [.mem (mg (some 0) none 1 48 64), .imm 64 0] 8) := by dec_rfl
theorem p1_33 : ∀ feat, Dec feat p1 33 (FV7z.mk .mov 64 [.mem (mg (some 0) none 1 0 64), gr 64 1] 3) := by dec_rfl
theorem p1_36 : ∀ feat, Dec feat p1 36 (FV7z.mk .mov 64 [.mem (mg (some 0) none 1 8 64), gr 64 2] 4) := by dec_rfl
theorem p1_40 : ∀ feat, Dec feat p1 40 (FV7z.mk .mov 64 [.mem (mg (some 0) none 1 56 64), .imm 64 0] 8) := by dec_rfl
theorem p1_48 : ∀ feat, Dec feat p1 48 (FV7z.mk .mov 8 [.mem (mg (some 0) none 1 20 8), .imm 8 0] 4) := by dec_rfl
theorem p1_52 : ∀ feat, Dec feat p1 52 (FV7z.mk .add 64 [gr 64 4, Src.opd 64 (.i 8)] 4) := by dec_rfl

/-- What the stretch does. -/
def o1 : List Op := [
  Op.mov 64 2 (.i 7888800),
  Op.sti 32 (some 0) none 1 16 0,
  Op.lea 64 1 (some 2) none 1 16,
  Op.add 64 2 (.i 144),
  Op.sti 64 (some 0) none 1 48 0,
  Op.st 64 (some 0) none 1 0 1,
  Op.st 64 (some 0) none 1 8 2,
  Op.sti 64 (some 0) none 1 56 0,
  Op.sti 8 (some 0) none 1 20 0,
  Op.add 64 4 (.i 8)]

theorem b1 (prof : Profile) : Blk prof p1 0 56 o1 :=
  .cons (p1_0 _) (OpI.mov (.i 7888800) (.inr rfl)) (by decide) <|
  .cons (p1_7 _) (OpI.sti (.inr (.inr (.inl rfl)))) (by decide) <|
  .cons (p1_14 _) (OpI.lea (.inr rfl)) (by decide) <|
  .cons (p1_18 _) (OpI.add (.i 144) (.inr rfl)) (by decide) <|
  .cons (p1_25 _) (OpI.sti (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p1_33 _) (OpI.st (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p1_36 _) (OpI.st (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p1_40 _) (OpI.sti (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p1_48 _) (OpI.sti (.inl rfl)) (by decide) <|
  .cons (p1_52 _) (OpI.add (.i 8) (.inr rfl)) (by decide) <|
  .nil 56

end FV7z.Cra
