import FV7z.Lemmas.SpFs
import FV7z.Lemmas.BlkOps6
import FV7z.Lemmas.BlkOps2
/-!
# The stretches of straight-line code of `StringToUInt32 (const wchar_t *, UInt32 &)` (PLAN.md §M, M1)

Each distinct stretch between labels and jumps (`p*`, 3 of them) and each distinct jump (`j*`, 1) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.Sti
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The stretch at `0`. -/
def p0 : List Byte := [
  0x53, 0x48, 0x89, 0xf3, 0x48, 0x83, 0xec, 0x10, 0x64, 0x48, 0x8b, 0x04, 0x25, 0x28, 0x00, 0x00,
  0x00, 0x48, 0x89, 0x44, 0x24, 0x08, 0x31, 0xc0, 0x48, 0x89, 0xe6]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .push 64 [gr 64 3] 1) := by dec_rfl
theorem p0_1 : ∀ feat, Dec feat p0 1 (FV7z.mk .mov 64 [gr 64 3, Src.opd 64 (.r 6)] 3) := by dec_rfl
theorem p0_4 : ∀ feat, Dec feat p0 4 (FV7z.mk .sub 64 [gr 64 4, Src.opd 64 (.i 16)] 4) := by dec_rfl
theorem p0_8 : ∀ feat, Dec feat p0 8 (FV7z.mk .mov 64 [gr 64 0, .mem (mf none none 1 40 64)] 9) := by dec_rfl
theorem p0_17 : ∀ feat, Dec feat p0 17 (FV7z.mk .mov 64 [.mem (mg (some 4) none 1 8 64), gr 64 0] 5) := by dec_rfl
theorem p0_22 : ∀ feat, Dec feat p0 22 (FV7z.mk .xor 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl
theorem p0_24 : ∀ feat, Dec feat p0 24 (FV7z.mk .mov 64 [gr 64 6, Src.opd 64 (.r 4)] 3) := by dec_rfl

/-- What the stretch does. -/
def o0 (fb : Addr) : List Op := [
  Op.push 3,
  Op.mov 64 3 (.r 6),
  Op.sub 64 4 (.i 16),
  Op.ldf fb 64 0 none none 1 40,
  Op.st 64 (some 4) none 1 8 0,
  Op.xor 32 0 (.r 0),
  Op.mov 64 6 (.r 4)]

theorem b0 (prof : Profile) (fb : Addr) : BlkF prof p0 (0x5a6760 : Addr) fb 0 27 (o0 fb) :=
  .cons (p0_0 _) (((OpI.push).at _).fs _) (by decide) <|
  .cons (p0_1 _) (((OpI.mov (.r 6) (.inr rfl)).at _).fs _) (by decide) <|
  .cons (p0_4 _) (((OpI.sub (.i 16) (.inr rfl)).at _).fs _) (by decide) <|
  .cons (p0_8 _) (OpIF.ldf (.inr rfl)) (by decide) <|
  .cons (p0_17 _) (((OpI.st (.inr (.inr (.inr rfl)))).at _).fs _) (by decide) <|
  .cons (p0_22 _) (((OpI.xor (.r 0) (.inl rfl)).at _).fs _) (by decide) <|
  .cons (p0_24 _) (((OpI.mov (.r 4) (.inr rfl)).at _).fs _) (by decide) <|
  .nil 27

/-- The stretch at `32`. -/
def p1 : List Byte := [
  0x89, 0x03, 0x48, 0x8b, 0x04, 0x24, 0x8b, 0x00, 0x85, 0xc0, 0x0f, 0x94, 0xc0, 0x48, 0x8b, 0x54,
  0x24, 0x08, 0x64, 0x48, 0x33, 0x14, 0x25, 0x28, 0x00, 0x00, 0x00]

theorem p1_0 : ∀ feat, Dec feat p1 0 (FV7z.mk .mov 32 [.mem (mg (some 3) none 1 0 32), gr 32 0] 2) := by dec_rfl
theorem p1_2 : ∀ feat, Dec feat p1 2 (FV7z.mk .mov 64 [gr 64 0, .mem (mg (some 4) none 1 0 64)] 4) := by dec_rfl
theorem p1_6 : ∀ feat, Dec feat p1 6 (FV7z.mk .mov 32 [gr 32 0, .mem (mg (some 0) none 1 0 32)] 2) := by dec_rfl
theorem p1_8 : ∀ feat, Dec feat p1 8 (FV7z.mk .test 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl
theorem p1_10 : ∀ feat, Dec feat p1 10 (FV7z.mk (.setcc 4) 8 [gr 8 0] 3) := by dec_rfl
theorem p1_13 : ∀ feat, Dec feat p1 13 (FV7z.mk .mov 64 [gr 64 2, .mem (mg (some 4) none 1 8 64)] 5) := by dec_rfl
theorem p1_18 : ∀ feat, Dec feat p1 18 (FV7z.mk .xor 64 [gr 64 2, .mem (mf none none 1 40 64)] 9) := by dec_rfl

/-- What the stretch does. -/
def o1 (fb : Addr) : List Op := [
  Op.st 32 (some 3) none 1 0 0,
  Op.ld 64 0 (some 4) none 1 0,
  Op.ld 32 0 (some 0) none 1 0,
  Op.test 32 0 (.r 0),
  Op.setcc 4 0,
  Op.ld 64 2 (some 4) none 1 8,
  Op.xormf fb 64 2 none none 1 40]

theorem b1 (prof : Profile) (fb : Addr) : BlkF prof p1 (0x5a6780 : Addr) fb 0 27 (o1 fb) :=
  .cons (p1_0 _) (((OpI.st (.inr (.inr (.inl rfl)))).at _).fs _) (by decide) <|
  .cons (p1_2 _) (((OpI.ld (.inr rfl)).at _).fs _) (by decide) <|
  .cons (p1_6 _) (((OpI.ld (.inl rfl)).at _).fs _) (by decide) <|
  .cons (p1_8 _) (((OpI.test (.r 0) (.inl rfl)).at _).fs _) (by decide) <|
  .cons (p1_10 _) (((OpI.setcc).at _).fs _) (by decide) <|
  .cons (p1_13 _) (((OpI.ld (.inr rfl)).at _).fs _) (by decide) <|
  .cons (p1_18 _) (OpIF.xormf (.inr rfl)) (by decide) <|
  .nil 27

def j0 : List Byte := [0x75, 0x06]
theorem j0_0 : ∀ feat, Dec feat j0 0 (FV7z.mk (.jcc 5) 64 [.rel 6] 2) := by dec_rfl

/-- The stretch at `61`. -/
def p2 : List Byte := [
  0x48, 0x83, 0xc4, 0x10, 0x5b]

theorem p2_0 : ∀ feat, Dec feat p2 0 (FV7z.mk .add 64 [gr 64 4, Src.opd 64 (.i 16)] 4) := by dec_rfl
theorem p2_4 : ∀ feat, Dec feat p2 4 (FV7z.mk .pop 64 [gr 64 3] 1) := by dec_rfl

/-- What the stretch does. -/
def o2 : List Op := [
  Op.add 64 4 (.i 16),
  Op.pop 3]

theorem b2 (prof : Profile) : Blk prof p2 0 5 o2 :=
  .cons (p2_0 _) (OpI.add (.i 16) (.inr rfl)) (by decide) <|
  .cons (p2_4 _) (OpI.pop) (by decide) <|
  .nil 5

end FV7z.Sti
