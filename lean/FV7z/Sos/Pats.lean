import FV7z.Lemmas.Sp
import FV7z.Lemmas.BlkOps2
/-!
# The stretches of straight-line code of `NCompress::NLzma::CDecoder::SetOutStreamSizeResume` (PLAN.md §M, M1)

Each distinct stretch between labels and jumps (`p*`, 3 of them) and each distinct jump (`j*`, 1) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.Sos
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The stretch at `0`. -/
def p0 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0x48, 0x85, 0xf6, 0x48, 0xc7, 0x47, 0x68, 0x00, 0x00, 0x00, 0x00]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem p0_4 : ∀ feat, Dec feat p0 4 (FV7z.mk .test 64 [gr 64 6, Src.opd 64 (.r 6)] 3) := by dec_rfl
theorem p0_7 : ∀ feat, Dec feat p0 7 (FV7z.mk .mov 64 [.mem (mg (some 7) none 1 104 64), .imm 64 0] 8) := by dec_rfl

/-- What the stretch does. -/
def o0 : List Op := [
  Op.nop,
  Op.test 64 6 (.r 6),
  Op.sti 64 (some 7) none 1 104 0]

theorem b0 (prof : Profile) : Blk prof p0 0 15 o0 :=
  .cons (p0_0 _) (OpI.endbr) (by decide) <|
  .cons (p0_4 _) (OpI.test (.r 6) (.inr rfl)) (by decide) <|
  .cons (p0_7 _) (OpI.sti (.inr (.inr (.inr rfl)))) (by decide) <|
  .nil 15

def j0 : List Byte := [0x74, 0x07]
theorem j0_0 : ∀ feat, Dec feat j0 0 (FV7z.mk (.jcc 4) 64 [.rel 7] 2) := by dec_rfl

/-- The stretch at `21`. -/
def p1 : List Byte := [
  0x48, 0x8b, 0x06, 0x48, 0x89, 0x47, 0x68]

theorem p1_0 : ∀ feat, Dec feat p1 0 (FV7z.mk .mov 64 [gr 64 0, .mem (mg (some 6) none 1 0 64)] 3) := by dec_rfl
theorem p1_3 : ∀ feat, Dec feat p1 3 (FV7z.mk .mov 64 [.mem (mg (some 7) none 1 104 64), gr 64 0] 4) := by dec_rfl

/-- What the stretch does. -/
def o1 : List Op := [
  Op.ld 64 0 (some 6) none 1 0,
  Op.st 64 (some 7) none 1 104 0]

theorem b1 (prof : Profile) : Blk prof p1 0 7 o1 :=
  .cons (p1_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p1_3 _) (OpI.st (.inr (.inr (.inr rfl)))) (by decide) <|
  .nil 7

/-- The stretch at `28`. -/
def p2 : List Byte := [
  0x48, 0xc7, 0x47, 0x78, 0x00, 0x00, 0x00, 0x00, 0x48, 0x83, 0xef, 0x80, 0xc7, 0x47, 0xd4, 0x00,
  0x00, 0x00, 0x00]

theorem p2_0 : ∀ feat, Dec feat p2 0 (FV7z.mk .mov 64 [.mem (mg (some 7) none 1 120 64), .imm 64 0] 8) := by dec_rfl
theorem p2_8 : ∀ feat, Dec feat p2 8 (FV7z.mk .sub 64 [gr 64 7, Src.opd 64 (.i 18446744073709551488)] 4) := by dec_rfl
theorem p2_12 : ∀ feat, Dec feat p2 12 (FV7z.mk .mov 32 [.mem (mg (some 7) none 1 18446744073709551572 32), .imm 32 0] 7) := by dec_rfl

/-- What the stretch does. -/
def o2 : List Op := [
  Op.sti 64 (some 7) none 1 120 0,
  Op.sub 64 7 (.i 18446744073709551488),
  Op.sti 32 (some 7) none 1 18446744073709551572 0]

theorem b2 (prof : Profile) : Blk prof p2 0 19 o2 :=
  .cons (p2_0 _) (OpI.sti (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p2_8 _) (OpI.sub (.i 18446744073709551488) (.inr rfl)) (by decide) <|
  .cons (p2_12 _) (OpI.sti (.inr (.inr (.inl rfl)))) (by decide) <|
  .nil 19

end FV7z.Sos
