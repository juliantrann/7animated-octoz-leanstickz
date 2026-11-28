import FV7z.Lemmas.SpFs
import FV7z.Lemmas.BlkOps6
import FV7z.Lemmas.BlkOps2
/-!
# The stretches of straight-line code of `UnicodeStringToMultiByte2` (PLAN.md §M, M1)

Each distinct stretch between labels and jumps (`p*`, 3 of them) and each distinct jump (`j*`, 1) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.Um2
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The stretch at `0`. -/
def p0 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0x48, 0x83, 0xec, 0x18, 0xb9, 0x5f, 0x00, 0x00, 0x00, 0x64, 0x48, 0x8b,
  0x04, 0x25, 0x28, 0x00, 0x00, 0x00, 0x48, 0x89, 0x44, 0x24, 0x08, 0x31, 0xc0, 0x4c, 0x8d, 0x44,
  0x24, 0x07]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem p0_4 : ∀ feat, Dec feat p0 4 (FV7z.mk .sub 64 [gr 64 4, Src.opd 64 (.i 24)] 4) := by dec_rfl
theorem p0_8 : ∀ feat, Dec feat p0 8 (FV7z.mk .mov 32 [gr 32 1, Src.opd 32 (.i 95)] 5) := by dec_rfl
theorem p0_13 : ∀ feat, Dec feat p0 13 (FV7z.mk .mov 64 [gr 64 0, .mem (mf none none 1 40 64)] 9) := by dec_rfl
theorem p0_22 : ∀ feat, Dec feat p0 22 (FV7z.mk .mov 64 [.mem (mg (some 4) none 1 8 64), gr 64 0] 5) := by dec_rfl
theorem p0_27 : ∀ feat, Dec feat p0 27 (FV7z.mk .xor 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl
theorem p0_29 : ∀ feat, Dec feat p0 29 (FV7z.mk .lea 64 [gr 64 8, .mem (mg (some 4) none 1 7 0)] 5) := by dec_rfl

/-- What the stretch does. -/
def o0 (fb : Addr) : List Op := [
  Op.nop,
  Op.sub 64 4 (.i 24),
  Op.mov 32 1 (.i 95),
  Op.ldf fb 64 0 none none 1 40,
  Op.st 64 (some 4) none 1 8 0,
  Op.xor 32 0 (.r 0),
  Op.lea 64 8 (some 4) none 1 7]

theorem b0 (prof : Profile) (fb : Addr) : BlkF prof p0 (0x450d20 : Addr) fb 0 34 (o0 fb) :=
  .cons (p0_0 _) (((OpI.endbr).at _).fs _) (by decide) <|
  .cons (p0_4 _) (((OpI.sub (.i 24) (.inr rfl)).at _).fs _) (by decide) <|
  .cons (p0_8 _) (((OpI.mov (.i 95) (.inl rfl)).at _).fs _) (by decide) <|
  .cons (p0_13 _) (OpIF.ldf (.inr rfl)) (by decide) <|
  .cons (p0_22 _) (((OpI.st (.inr (.inr (.inr rfl)))).at _).fs _) (by decide) <|
  .cons (p0_27 _) (((OpI.xor (.r 0) (.inl rfl)).at _).fs _) (by decide) <|
  .cons (p0_29 _) (((OpI.lea (.inr rfl)).at _).fs _) (by decide) <|
  .nil 34

/-- The stretch at `39`. -/
def p1 : List Byte := [
  0x48, 0x8b, 0x44, 0x24, 0x08, 0x64, 0x48, 0x33, 0x04, 0x25, 0x28, 0x00, 0x00, 0x00]

theorem p1_0 : ∀ feat, Dec feat p1 0 (FV7z.mk .mov 64 [gr 64 0, .mem (mg (some 4) none 1 8 64)] 5) := by dec_rfl
theorem p1_5 : ∀ feat, Dec feat p1 5 (FV7z.mk .xor 64 [gr 64 0, .mem (mf none none 1 40 64)] 9) := by dec_rfl

/-- What the stretch does. -/
def o1 (fb : Addr) : List Op := [
  Op.ld 64 0 (some 4) none 1 8,
  Op.xormf fb 64 0 none none 1 40]

theorem b1 (prof : Profile) (fb : Addr) : BlkF prof p1 (0x450d47 : Addr) fb 0 14 (o1 fb) :=
  .cons (p1_0 _) (((OpI.ld (.inr rfl)).at _).fs _) (by decide) <|
  .cons (p1_5 _) (OpIF.xormf (.inr rfl)) (by decide) <|
  .nil 14

def j0 : List Byte := [0x75, 0x05]
theorem j0_0 : ∀ feat, Dec feat j0 0 (FV7z.mk (.jcc 5) 64 [.rel 5] 2) := by dec_rfl

/-- The stretch at `55`. -/
def p2 : List Byte := [
  0x48, 0x83, 0xc4, 0x18]

theorem p2_0 : ∀ feat, Dec feat p2 0 (FV7z.mk .add 64 [gr 64 4, Src.opd 64 (.i 24)] 4) := by dec_rfl

/-- What the stretch does. -/
def o2 : List Op := [
  Op.add 64 4 (.i 24)]

theorem b2 (prof : Profile) : Blk prof p2 0 4 o2 :=
  .cons (p2_0 _) (OpI.add (.i 24) (.inr rfl)) (by decide) <|
  .nil 4

end FV7z.Um2
