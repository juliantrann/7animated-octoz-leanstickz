import FV7z.Lemmas.SpFs
import FV7z.Lemmas.BlkOps6
import FV7z.Lemmas.BlkOps2
/-!
# The stretches of straight-line code of `__sigaction` (PLAN.md §M, M1)

Each distinct stretch between labels and jumps (`p*`, 3 of them) and each distinct jump (`j*`, 2) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.Sgw
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The stretch at `0`. -/
def p0 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0x8d, 0x47, 0xff, 0x83, 0xf8, 0x3f]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem p0_4 : ∀ feat, Dec feat p0 4 (FV7z.mk .lea 32 [gr 32 0, .mem (mg (some 7) none 1 18446744073709551615 0)] 3) := by dec_rfl
theorem p0_7 : ∀ feat, Dec feat p0 7 (FV7z.mk .cmp 32 [gr 32 0, Src.opd 32 (.i 63)] 3) := by dec_rfl

/-- What the stretch does. -/
def o0 : List Op := [
  Op.nop,
  Op.lea 32 0 (some 7) none 1 18446744073709551615,
  Op.cmp 32 0 (.i 63)]

theorem b0 (prof : Profile) : Blk prof p0 0 10 o0 :=
  .cons (p0_0 _) (OpI.endbr) (by decide) <|
  .cons (p0_4 _) (OpI.lea (.inl rfl)) (by decide) <|
  .cons (p0_7 _) (OpI.cmp (.i 63) (.inl rfl)) (by decide) <|
  .nil 10

def j0 : List Byte := [0x77, 0x14]
theorem j0_0 : ∀ feat, Dec feat j0 0 (FV7z.mk (.jcc 7) 64 [.rel 20] 2) := by dec_rfl

/-- The stretch at `12`. -/
def p1 : List Byte := [
  0x8d, 0x47, 0xe0, 0x83, 0xf8, 0x01]

theorem p1_0 : ∀ feat, Dec feat p1 0 (FV7z.mk .lea 32 [gr 32 0, .mem (mg (some 7) none 1 18446744073709551584 0)] 3) := by dec_rfl
theorem p1_3 : ∀ feat, Dec feat p1 3 (FV7z.mk .cmp 32 [gr 32 0, Src.opd 32 (.i 1)] 3) := by dec_rfl

/-- What the stretch does. -/
def o1 : List Op := [
  Op.lea 32 0 (some 7) none 1 18446744073709551584,
  Op.cmp 32 0 (.i 1)]

theorem b1 (prof : Profile) : Blk prof p1 0 6 o1 :=
  .cons (p1_0 _) (OpI.lea (.inl rfl)) (by decide) <|
  .cons (p1_3 _) (OpI.cmp (.i 1) (.inl rfl)) (by decide) <|
  .nil 6

def j1 : List Byte := [0x76, 0x0c]
theorem j1_0 : ∀ feat, Dec feat j1 0 (FV7z.mk (.jcc 6) 64 [.rel 12] 2) := by dec_rfl

/-- The stretch at `32`. -/
def p2 : List Byte := [
  0x48, 0xc7, 0xc0, 0xb8, 0xff, 0xff, 0xff, 0x64, 0xc7, 0x00, 0x16, 0x00, 0x00, 0x00, 0xb8, 0xff,
  0xff, 0xff, 0xff]

theorem p2_0 : ∀ feat, Dec feat p2 0 (FV7z.mk .mov 64 [gr 64 0, Src.opd 64 (.i 18446744073709551544)] 7) := by dec_rfl
theorem p2_7 : ∀ feat, Dec feat p2 7 (FV7z.mk .mov 32 [.mem (mf (some 0) none 1 0 32), .imm 32 22] 7) := by dec_rfl
theorem p2_14 : ∀ feat, Dec feat p2 14 (FV7z.mk .mov 32 [gr 32 0, Src.opd 32 (.i 4294967295)] 5) := by dec_rfl

/-- What the stretch does. -/
def o2 (fb : Addr) : List Op := [
  Op.mov 64 0 (.i 18446744073709551544),
  Op.stfi fb 32 (some 0) none 1 0 22,
  Op.mov 32 0 (.i 4294967295)]

theorem b2 (prof : Profile) (fb : Addr) : BlkF prof p2 (0x6011f0 : Addr) fb 0 19 (o2 fb) :=
  .cons (p2_0 _) (((OpI.mov (.i 18446744073709551544) (.inr rfl)).at _).fs _) (by decide) <|
  .cons (p2_7 _) (OpIF.stfi (.inr (.inr (.inl rfl)))) (by decide) <|
  .cons (p2_14 _) (((OpI.mov (.i 4294967295) (.inl rfl)).at _).fs _) (by decide) <|
  .nil 19

end FV7z.Sgw
