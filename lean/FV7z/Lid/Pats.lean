import FV7z.Lemmas.Sp
import FV7z.Lemmas.BlkOps2
/-!
# The stretches of straight-line code of `LzmaDec_InitDicAndState` (PLAN.md §M, M1)

Each distinct stretch between labels and jumps (`p*`, 4 of them) and each distinct jump (`j*`, 2) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.Lid
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The stretch at `0`. -/
def p0 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0xc7, 0x47, 0x5c, 0x13, 0x01, 0x00, 0x00, 0xc7, 0x47, 0x64, 0x00, 0x00,
  0x00, 0x00, 0x85, 0xf6]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem p0_4 : ∀ feat, Dec feat p0 4 (FV7z.mk .mov 32 [.mem (mg (some 7) none 1 92 32), .imm 32 275] 7) := by dec_rfl
theorem p0_11 : ∀ feat, Dec feat p0 11 (FV7z.mk .mov 32 [.mem (mg (some 7) none 1 100 32), .imm 32 0] 7) := by dec_rfl
theorem p0_18 : ∀ feat, Dec feat p0 18 (FV7z.mk .test 32 [gr 32 6, Src.opd 32 (.r 6)] 2) := by dec_rfl

/-- What the stretch does. -/
def o0 : List Op := [
  Op.nop,
  Op.sti 32 (some 7) none 1 92 275,
  Op.sti 32 (some 7) none 1 100 0,
  Op.test 32 6 (.r 6)]

theorem b0 (prof : Profile) : Blk prof p0 0 20 o0 :=
  .cons (p0_0 _) (OpI.endbr) (by decide) <|
  .cons (p0_4 _) (OpI.sti (.inr (.inr (.inl rfl)))) (by decide) <|
  .cons (p0_11 _) (OpI.sti (.inr (.inr (.inl rfl)))) (by decide) <|
  .cons (p0_18 _) (OpI.test (.r 6) (.inl rfl)) (by decide) <|
  .nil 20

def j0 : List Byte := [0x74, 0x0f]
theorem j0_0 : ∀ feat, Dec feat j0 0 (FV7z.mk (.jcc 4) 64 [.rel 15] 2) := by dec_rfl

/-- The stretch at `22`. -/
def p1 : List Byte := [
  0x48, 0xc7, 0x47, 0x40, 0x00, 0x00, 0x00, 0x00, 0xc7, 0x47, 0x5c, 0x14, 0x01, 0x00, 0x00]

theorem p1_0 : ∀ feat, Dec feat p1 0 (FV7z.mk .mov 64 [.mem (mg (some 7) none 1 64 64), .imm 64 0] 8) := by dec_rfl
theorem p1_8 : ∀ feat, Dec feat p1 8 (FV7z.mk .mov 32 [.mem (mg (some 7) none 1 92 32), .imm 32 276] 7) := by dec_rfl

/-- What the stretch does. -/
def o1 : List Op := [
  Op.sti 64 (some 7) none 1 64 0,
  Op.sti 32 (some 7) none 1 92 276]

theorem b1 (prof : Profile) : Blk prof p1 0 15 o1 :=
  .cons (p1_0 _) (OpI.sti (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p1_8 _) (OpI.sti (.inr (.inr (.inl rfl)))) (by decide) <|
  .nil 15

/-- The stretch at `37`. -/
def p2 : List Byte := [
  0x85, 0xd2]

theorem p2_0 : ∀ feat, Dec feat p2 0 (FV7z.mk .test 32 [gr 32 2, Src.opd 32 (.r 2)] 2) := by dec_rfl

/-- What the stretch does. -/
def o2 : List Op := [
  Op.test 32 2 (.r 2)]

theorem b2 (prof : Profile) : Blk prof p2 0 2 o2 :=
  .cons (p2_0 _) (OpI.test (.r 2) (.inl rfl)) (by decide) <|
  .nil 2

def j1 : List Byte := [0x74, 0x07]
theorem j1_0 : ∀ feat, Dec feat j1 0 (FV7z.mk (.jcc 4) 64 [.rel 7] 2) := by dec_rfl

/-- The stretch at `41`. -/
def p3 : List Byte := [
  0xc7, 0x47, 0x5c, 0x14, 0x01, 0x00, 0x00]

theorem p3_0 : ∀ feat, Dec feat p3 0 (FV7z.mk .mov 32 [.mem (mg (some 7) none 1 92 32), .imm 32 276] 7) := by dec_rfl

/-- What the stretch does. -/
def o3 : List Op := [
  Op.sti 32 (some 7) none 1 92 276]

theorem b3 (prof : Profile) : Blk prof p3 0 7 o3 :=
  .cons (p3_0 _) (OpI.sti (.inr (.inr (.inl rfl)))) (by decide) <|
  .nil 7

end FV7z.Lid
