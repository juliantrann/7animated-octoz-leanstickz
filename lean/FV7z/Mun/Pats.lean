import FV7z.Lemmas.SpFs
import FV7z.Lemmas.BlkOps2
/-!
# The stretches of straight-line code of `__munmap` (PLAN.md §M, M1)

Each distinct stretch between labels and jumps (`p*`, 3 of them) and each distinct jump (`j*`, 1) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.Mun
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The stretch at `0`. -/
def p0 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0xb8, 0x0b, 0x00, 0x00, 0x00]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem p0_4 : ∀ feat, Dec feat p0 4 (FV7z.mk .mov 32 [gr 32 0, Src.opd 32 (.i 11)] 5) := by dec_rfl

/-- What the stretch does. -/
def o0 : List Op := [
  Op.nop,
  Op.mov 32 0 (.i 11)]

theorem b0 (prof : Profile) : Blk prof p0 0 9 o0 :=
  .cons (p0_0 _) (OpI.endbr) (by decide) <|
  .cons (p0_4 _) (OpI.mov (.i 11) (.inl rfl)) (by decide) <|
  .nil 9

/-- The stretch at `11`. -/
def p1 : List Byte := [
  0x48, 0x3d, 0x01, 0xf0, 0xff, 0xff]

theorem p1_0 : ∀ feat, Dec feat p1 0 (FV7z.mk .cmp 64 [gr 64 0, Src.opd 64 (.i 18446744073709547521)] 6) := by dec_rfl

/-- What the stretch does. -/
def o1 : List Op := [
  Op.cmp 64 0 (.i 18446744073709547521)]

theorem b1 (prof : Profile) : Blk prof p1 0 6 o1 :=
  .cons (p1_0 _) (OpI.cmp (.i 18446744073709547521) (.inr rfl)) (by decide) <|
  .nil 6

def j0 : List Byte := [0x73, 0x01]
theorem j0_0 : ∀ feat, Dec feat j0 0 (FV7z.mk (.jcc 3) 64 [.rel 1] 2) := by dec_rfl

/-- The stretch at `20`. -/
def p2 : List Byte := [
  0x48, 0xc7, 0xc1, 0xb8, 0xff, 0xff, 0xff, 0xf7, 0xd8, 0x64, 0x89, 0x01, 0x48, 0x83, 0xc8, 0xff]

theorem p2_0 : ∀ feat, Dec feat p2 0 (FV7z.mk .mov 64 [gr 64 1, Src.opd 64 (.i 18446744073709551544)] 7) := by dec_rfl
theorem p2_7 : ∀ feat, Dec feat p2 7 (FV7z.mk .neg 32 [gr 32 0] 2) := by dec_rfl
theorem p2_9 : ∀ feat, Dec feat p2 9 (FV7z.mk .mov 32 [.mem (mf (some 1) none 1 0 32), gr 32 0] 3) := by dec_rfl
theorem p2_12 : ∀ feat, Dec feat p2 12 (FV7z.mk .or 64 [gr 64 0, Src.opd 64 (.i 18446744073709551615)] 4) := by dec_rfl

/-- What the stretch does. -/
def o2 (fb : Addr) : List Op := [
  Op.mov 64 1 (.i 18446744073709551544),
  Op.neg 32 0,
  Op.stf fb 32 (some 1) none 1 0 0,
  Op.or 64 0 (.i 18446744073709551615)]

theorem b2 (prof : Profile) (fb : Addr) : BlkF prof p2 (0x6665e4 : Addr) fb 0 16 (o2 fb) :=
  .cons (p2_0 _) (((OpI.mov (.i 18446744073709551544) (.inr rfl)).at _).fs _) (by decide) <|
  .cons (p2_7 _) (((OpI.neg (.inl rfl)).at _).fs _) (by decide) <|
  .cons (p2_9 _) (OpIF.stf (.inl rfl)) (by decide) <|
  .cons (p2_12 _) (((OpI.or (.i 18446744073709551615) (.inr rfl)).at _).fs _) (by decide) <|
  .nil 16

end FV7z.Mun
