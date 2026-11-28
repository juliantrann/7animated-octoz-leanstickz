import FV7z.Lemmas.Sp
import FV7z.Lemmas.BlkOps2
/-!
# The stretches of straight-line code of `__init_sched_fifo_prio` (PLAN.md §M, M1)

Each distinct stretch between labels and jumps (`p*`, 3 of them) and each distinct jump (`j*`, 0) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.Isf
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The stretch at `0`. -/
def p0 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0x48, 0x83, 0xec, 0x08, 0xbf, 0x01, 0x00, 0x00, 0x00]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem p0_4 : ∀ feat, Dec feat p0 4 (FV7z.mk .sub 64 [gr 64 4, Src.opd 64 (.i 8)] 4) := by dec_rfl
theorem p0_8 : ∀ feat, Dec feat p0 8 (FV7z.mk .mov 32 [gr 32 7, Src.opd 32 (.i 1)] 5) := by dec_rfl

/-- What the stretch does. -/
def o0 : List Op := [
  Op.nop,
  Op.sub 64 4 (.i 8),
  Op.mov 32 7 (.i 1)]

theorem b0 (prof : Profile) : Blk prof p0 0 13 o0 :=
  .cons (p0_0 _) (OpI.endbr) (by decide) <|
  .cons (p0_4 _) (OpI.sub (.i 8) (.inr rfl)) (by decide) <|
  .cons (p0_8 _) (OpI.mov (.i 1) (.inl rfl)) (by decide) <|
  .nil 13

/-- The stretch at `18`. -/
def p1 : List Byte := [
  0xbf, 0x01, 0x00, 0x00, 0x00, 0x89, 0x05, 0x33, 0x2c, 0x19, 0x00]

theorem p1_0 : ∀ feat, Dec feat p1 0 (FV7z.mk .mov 32 [gr 32 7, Src.opd 32 (.i 1)] 5) := by dec_rfl
theorem p1_5 : ∀ feat, Dec feat p1 5 (FV7z.mk .mov 32 [.mem (mrip 1649715 32), gr 32 0] 6) := by dec_rfl

/-- What the stretch does. -/
def o1 : List Op := [
  Op.mov 32 7 (.i 1),
  Op.sta 32 7938672 0]

theorem b1 (prof : Profile) : BlkA prof p1 (0x5ff632 : Addr) 0 11 o1 :=
  .cons (p1_0 _) ((OpI.mov (.i 1) (.inl rfl)).at _) (by decide) <|
  .cons (p1_5 _) (OpIA.st_rip (.inr (.inl rfl)) (by decide)) (by decide) <|
  .nil 11

/-- The stretch at `34`. -/
def p2 : List Byte := [
  0x89, 0x05, 0x2c, 0x2c, 0x19, 0x00, 0x48, 0x83, 0xc4, 0x08]

theorem p2_0 : ∀ feat, Dec feat p2 0 (FV7z.mk .mov 32 [.mem (mrip 1649708 32), gr 32 0] 6) := by dec_rfl
theorem p2_6 : ∀ feat, Dec feat p2 6 (FV7z.mk .add 64 [gr 64 4, Src.opd 64 (.i 8)] 4) := by dec_rfl

/-- What the stretch does. -/
def o2 : List Op := [
  Op.sta 32 7938676 0,
  Op.add 64 4 (.i 8)]

theorem b2 (prof : Profile) : BlkA prof p2 (0x5ff642 : Addr) 0 10 o2 :=
  .cons (p2_0 _) (OpIA.st_rip (.inr (.inl rfl)) (by decide)) (by decide) <|
  .cons (p2_6 _) ((OpI.add (.i 8) (.inr rfl)).at _) (by decide) <|
  .nil 10

end FV7z.Isf
