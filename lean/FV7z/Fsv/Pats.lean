import FV7z.Lemmas.SpFs
import FV7z.Lemmas.BlkOps6
import FV7z.Lemmas.BlkOps2
/-!
# The stretches of straight-line code of `fs2us (const char *), the twin at 0x44e600` (PLAN.md §M, M1)

Each distinct stretch between labels and jumps (`p*`, 3 of them) and each distinct jump (`j*`, 1) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.Fsv
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The stretch at `0`. -/
def p0 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0x41, 0x54, 0x31, 0xd2, 0x49, 0x89, 0xfc, 0x48, 0x83, 0xec, 0x10, 0x64,
  0x48, 0x8b, 0x04, 0x25, 0x28, 0x00, 0x00, 0x00, 0x48, 0x89, 0x44, 0x24, 0x08, 0x31, 0xc0]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem p0_4 : ∀ feat, Dec feat p0 4 (FV7z.mk .push 64 [gr 64 12] 2) := by dec_rfl
theorem p0_6 : ∀ feat, Dec feat p0 6 (FV7z.mk .xor 32 [gr 32 2, Src.opd 32 (.r 2)] 2) := by dec_rfl
theorem p0_8 : ∀ feat, Dec feat p0 8 (FV7z.mk .mov 64 [gr 64 12, Src.opd 64 (.r 7)] 3) := by dec_rfl
theorem p0_11 : ∀ feat, Dec feat p0 11 (FV7z.mk .sub 64 [gr 64 4, Src.opd 64 (.i 16)] 4) := by dec_rfl
theorem p0_15 : ∀ feat, Dec feat p0 15 (FV7z.mk .mov 64 [gr 64 0, .mem (mf none none 1 40 64)] 9) := by dec_rfl
theorem p0_24 : ∀ feat, Dec feat p0 24 (FV7z.mk .mov 64 [.mem (mg (some 4) none 1 8 64), gr 64 0] 5) := by dec_rfl
theorem p0_29 : ∀ feat, Dec feat p0 29 (FV7z.mk .xor 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl

/-- What the stretch does. -/
def o0 (fb : Addr) : List Op := [
  Op.nop,
  Op.push 12,
  Op.xor 32 2 (.r 2),
  Op.mov 64 12 (.r 7),
  Op.sub 64 4 (.i 16),
  Op.ldf fb 64 0 none none 1 40,
  Op.st 64 (some 4) none 1 8 0,
  Op.xor 32 0 (.r 0)]

theorem b0 (prof : Profile) (fb : Addr) : BlkF prof p0 (0x44e600 : Addr) fb 0 31 (o0 fb) :=
  .cons (p0_0 _) (((OpI.endbr).at _).fs _) (by decide) <|
  .cons (p0_4 _) (((OpI.push).at _).fs _) (by decide) <|
  .cons (p0_6 _) (((OpI.xor (.r 2) (.inl rfl)).at _).fs _) (by decide) <|
  .cons (p0_8 _) (((OpI.mov (.r 7) (.inr rfl)).at _).fs _) (by decide) <|
  .cons (p0_11 _) (((OpI.sub (.i 16) (.inr rfl)).at _).fs _) (by decide) <|
  .cons (p0_15 _) (OpIF.ldf (.inr rfl)) (by decide) <|
  .cons (p0_24 _) (((OpI.st (.inr (.inr (.inr rfl)))).at _).fs _) (by decide) <|
  .cons (p0_29 _) (((OpI.xor (.r 0) (.inl rfl)).at _).fs _) (by decide) <|
  .nil 31

/-- The stretch at `36`. -/
def p1 : List Byte := [
  0x48, 0x8b, 0x44, 0x24, 0x08, 0x64, 0x48, 0x33, 0x04, 0x25, 0x28, 0x00, 0x00, 0x00]

theorem p1_0 : ∀ feat, Dec feat p1 0 (FV7z.mk .mov 64 [gr 64 0, .mem (mg (some 4) none 1 8 64)] 5) := by dec_rfl
theorem p1_5 : ∀ feat, Dec feat p1 5 (FV7z.mk .xor 64 [gr 64 0, .mem (mf none none 1 40 64)] 9) := by dec_rfl

/-- What the stretch does. -/
def o1 (fb : Addr) : List Op := [
  Op.ld 64 0 (some 4) none 1 8,
  Op.xormf fb 64 0 none none 1 40]

theorem b1 (prof : Profile) (fb : Addr) : BlkF prof p1 (0x44e624 : Addr) fb 0 14 (o1 fb) :=
  .cons (p1_0 _) (((OpI.ld (.inr rfl)).at _).fs _) (by decide) <|
  .cons (p1_5 _) (OpIF.xormf (.inr rfl)) (by decide) <|
  .nil 14

def j0 : List Byte := [0x75, 0x0a]
theorem j0_0 : ∀ feat, Dec feat j0 0 (FV7z.mk (.jcc 5) 64 [.rel 10] 2) := by dec_rfl

/-- The stretch at `52`. -/
def p2 : List Byte := [
  0x48, 0x83, 0xc4, 0x10, 0x4c, 0x89, 0xe0, 0x41, 0x5c]

theorem p2_0 : ∀ feat, Dec feat p2 0 (FV7z.mk .add 64 [gr 64 4, Src.opd 64 (.i 16)] 4) := by dec_rfl
theorem p2_4 : ∀ feat, Dec feat p2 4 (FV7z.mk .mov 64 [gr 64 0, Src.opd 64 (.r 12)] 3) := by dec_rfl
theorem p2_7 : ∀ feat, Dec feat p2 7 (FV7z.mk .pop 64 [gr 64 12] 2) := by dec_rfl

/-- What the stretch does. -/
def o2 : List Op := [
  Op.add 64 4 (.i 16),
  Op.mov 64 0 (.r 12),
  Op.pop 12]

theorem b2 (prof : Profile) : Blk prof p2 0 9 o2 :=
  .cons (p2_0 _) (OpI.add (.i 16) (.inr rfl)) (by decide) <|
  .cons (p2_4 _) (OpI.mov (.r 12) (.inr rfl)) (by decide) <|
  .cons (p2_7 _) (OpI.pop) (by decide) <|
  .nil 9

end FV7z.Fsv
