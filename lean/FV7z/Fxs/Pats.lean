import FV7z.Lemmas.SpFs
import FV7z.Lemmas.BlkOps6
import FV7z.Lemmas.BlkOps2
/-!
# The stretches of straight-line code of `__fxstat` (PLAN.md §M, M1)

Each distinct stretch between labels and jumps (`p*`, 5 of them) and each distinct jump (`j*`, 2) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.Fxs
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The stretch at `0`. -/
def p0 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0x41, 0x89, 0xf8, 0x89, 0xf7, 0x48, 0x89, 0xd6, 0x41, 0x83, 0xf8, 0x01]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem p0_4 : ∀ feat, Dec feat p0 4 (FV7z.mk .mov 32 [gr 32 8, Src.opd 32 (.r 7)] 3) := by dec_rfl
theorem p0_7 : ∀ feat, Dec feat p0 7 (FV7z.mk .mov 32 [gr 32 7, Src.opd 32 (.r 6)] 2) := by dec_rfl
theorem p0_9 : ∀ feat, Dec feat p0 9 (FV7z.mk .mov 64 [gr 64 6, Src.opd 64 (.r 2)] 3) := by dec_rfl
theorem p0_12 : ∀ feat, Dec feat p0 12 (FV7z.mk .cmp 32 [gr 32 8, Src.opd 32 (.i 1)] 4) := by dec_rfl

/-- What the stretch does. -/
def o0 : List Op := [
  Op.nop,
  Op.mov 32 8 (.r 7),
  Op.mov 32 7 (.r 6),
  Op.mov 64 6 (.r 2),
  Op.cmp 32 8 (.i 1)]

theorem b0 (prof : Profile) : Blk prof p0 0 16 o0 :=
  .cons (p0_0 _) (OpI.endbr) (by decide) <|
  .cons (p0_4 _) (OpI.mov (.r 7) (.inl rfl)) (by decide) <|
  .cons (p0_7 _) (OpI.mov (.r 6) (.inl rfl)) (by decide) <|
  .cons (p0_9 _) (OpI.mov (.r 2) (.inr rfl)) (by decide) <|
  .cons (p0_12 _) (OpI.cmp (.i 1) (.inl rfl)) (by decide) <|
  .nil 16

def j0 : List Byte := [0x77, 0x2e]
theorem j0_0 : ∀ feat, Dec feat j0 0 (FV7z.mk (.jcc 7) 64 [.rel 46] 2) := by dec_rfl

/-- The stretch at `18`. -/
def p1 : List Byte := [
  0xb8, 0x05, 0x00, 0x00, 0x00]

theorem p1_0 : ∀ feat, Dec feat p1 0 (FV7z.mk .mov 32 [gr 32 0, Src.opd 32 (.i 5)] 5) := by dec_rfl

/-- What the stretch does. -/
def o1 : List Op := [
  Op.mov 32 0 (.i 5)]

theorem b1 (prof : Profile) : Blk prof p1 0 5 o1 :=
  .cons (p1_0 _) (OpI.mov (.i 5) (.inl rfl)) (by decide) <|
  .nil 5

/-- The stretch at `25`. -/
def p2 : List Byte := [
  0x48, 0x3d, 0x00, 0xf0, 0xff, 0xff]

theorem p2_0 : ∀ feat, Dec feat p2 0 (FV7z.mk .cmp 64 [gr 64 0, Src.opd 64 (.i 18446744073709547520)] 6) := by dec_rfl

/-- What the stretch does. -/
def o2 : List Op := [
  Op.cmp 64 0 (.i 18446744073709547520)]

theorem b2 (prof : Profile) : Blk prof p2 0 6 o2 :=
  .cons (p2_0 _) (OpI.cmp (.i 18446744073709547520) (.inr rfl)) (by decide) <|
  .nil 6

def j1 : List Byte := [0x77, 0x07]
theorem j1_0 : ∀ feat, Dec feat j1 0 (FV7z.mk (.jcc 7) 64 [.rel 7] 2) := by dec_rfl

/-- The stretch at `40`. -/
def p3 : List Byte := [
  0x48, 0xc7, 0xc2, 0xb8, 0xff, 0xff, 0xff, 0xf7, 0xd8, 0x64, 0x89, 0x02, 0xb8, 0xff, 0xff, 0xff,
  0xff]

theorem p3_0 : ∀ feat, Dec feat p3 0 (FV7z.mk .mov 64 [gr 64 2, Src.opd 64 (.i 18446744073709551544)] 7) := by dec_rfl
theorem p3_7 : ∀ feat, Dec feat p3 7 (FV7z.mk .neg 32 [gr 32 0] 2) := by dec_rfl
theorem p3_9 : ∀ feat, Dec feat p3 9 (FV7z.mk .mov 32 [.mem (mf (some 2) none 1 0 32), gr 32 0] 3) := by dec_rfl
theorem p3_12 : ∀ feat, Dec feat p3 12 (FV7z.mk .mov 32 [gr 32 0, Src.opd 32 (.i 4294967295)] 5) := by dec_rfl

/-- What the stretch does. -/
def o3 (fb : Addr) : List Op := [
  Op.mov 64 2 (.i 18446744073709551544),
  Op.neg 32 0,
  Op.stf fb 32 (some 2) none 1 0 0,
  Op.mov 32 0 (.i 4294967295)]

theorem b3 (prof : Profile) (fb : Addr) : BlkF prof p3 (0x665388 : Addr) fb 0 17 (o3 fb) :=
  .cons (p3_0 _) (((OpI.mov (.i 18446744073709551544) (.inr rfl)).at _).fs _) (by decide) <|
  .cons (p3_7 _) (((OpI.neg (.inl rfl)).at _).fs _) (by decide) <|
  .cons (p3_9 _) (OpIF.stf (.inl rfl)) (by decide) <|
  .cons (p3_12 _) (((OpI.mov (.i 4294967295) (.inl rfl)).at _).fs _) (by decide) <|
  .nil 17

/-- The stretch at `64`. -/
def p4 : List Byte := [
  0x48, 0xc7, 0xc0, 0xb8, 0xff, 0xff, 0xff, 0x64, 0xc7, 0x00, 0x16, 0x00, 0x00, 0x00, 0xb8, 0xff,
  0xff, 0xff, 0xff]

theorem p4_0 : ∀ feat, Dec feat p4 0 (FV7z.mk .mov 64 [gr 64 0, Src.opd 64 (.i 18446744073709551544)] 7) := by dec_rfl
theorem p4_7 : ∀ feat, Dec feat p4 7 (FV7z.mk .mov 32 [.mem (mf (some 0) none 1 0 32), .imm 32 22] 7) := by dec_rfl
theorem p4_14 : ∀ feat, Dec feat p4 14 (FV7z.mk .mov 32 [gr 32 0, Src.opd 32 (.i 4294967295)] 5) := by dec_rfl

/-- What the stretch does. -/
def o4 (fb : Addr) : List Op := [
  Op.mov 64 0 (.i 18446744073709551544),
  Op.stfi fb 32 (some 0) none 1 0 22,
  Op.mov 32 0 (.i 4294967295)]

theorem b4 (prof : Profile) (fb : Addr) : BlkF prof p4 (0x6653a0 : Addr) fb 0 19 (o4 fb) :=
  .cons (p4_0 _) (((OpI.mov (.i 18446744073709551544) (.inr rfl)).at _).fs _) (by decide) <|
  .cons (p4_7 _) (OpIF.stfi (.inr (.inr (.inl rfl)))) (by decide) <|
  .cons (p4_14 _) (((OpI.mov (.i 4294967295) (.inl rfl)).at _).fs _) (by decide) <|
  .nil 19

end FV7z.Fxs
