import FV7z.Lemmas.Sp
import FV7z.Lemmas.CmpMi16
import FV7z.Lemmas.BlkOps2
/-!
# The stretches of straight-line code of `NWindows::NCOM::CPropVariant::Clear` (PLAN.md §M, M1)

Each distinct stretch between labels and jumps (`p*`, 2 of them) and each distinct jump (`j*`, 1) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.Pvc
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The stretch at `0`. -/
def p0 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0x66, 0x83, 0x3f, 0x00]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem p0_4 : ∀ feat, Dec feat p0 4 (FV7z.mk .cmp 16 [.mem (mg (some 7) none 1 0 16), .imm 16 0] 4) := by dec_rfl

/-- What the stretch does. -/
def o0 : List Op := [
  Op.nop,
  Op.cmpmi 16 (some 7) none 1 0 0]

theorem b0 (prof : Profile) : Blk prof p0 0 8 o0 :=
  .cons (p0_0 _) (OpI.endbr) (by decide) <|
  .cons (p0_4 _) (OpI.cmpmi16) (by decide) <|
  .nil 8

def j0 : List Byte := [0x75, 0x0e]
theorem j0_0 : ∀ feat, Dec feat j0 0 (FV7z.mk (.jcc 5) 64 [.rel 14] 2) := by dec_rfl

/-- The stretch at `10`. -/
def p1 : List Byte := [
  0x31, 0xc0, 0x66, 0x89, 0x47, 0x02, 0x31, 0xc0]

theorem p1_0 : ∀ feat, Dec feat p1 0 (FV7z.mk .xor 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl
theorem p1_2 : ∀ feat, Dec feat p1 2 (FV7z.mk .mov 16 [.mem (mg (some 7) none 1 2 16), gr 16 0] 4) := by dec_rfl
theorem p1_6 : ∀ feat, Dec feat p1 6 (FV7z.mk .xor 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl

/-- What the stretch does. -/
def o1 : List Op := [
  Op.xor 32 0 (.r 0),
  Op.st 16 (some 7) none 1 2 0,
  Op.xor 32 0 (.r 0)]

theorem b1 (prof : Profile) : Blk prof p1 0 8 o1 :=
  .cons (p1_0 _) (OpI.xor (.r 0) (.inl rfl)) (by decide) <|
  .cons (p1_2 _) (OpI.st (.inr (.inl rfl))) (by decide) <|
  .cons (p1_6 _) (OpI.xor (.r 0) (.inl rfl)) (by decide) <|
  .nil 8

end FV7z.Pvc
