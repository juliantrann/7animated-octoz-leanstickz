import FV7z.Lemmas.Sp
import FV7z.Lemmas.CmpMi16
import FV7z.Lemmas.BlkOps2
/-!
# The stretches of straight-line code of `CPropVariant::operator=(UInt32)` (PLAN.md §M, M1)

Each distinct stretch between labels and jumps (`p*`, 3 of them) and each distinct jump (`j*`, 1) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.Pvu
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The stretch at `0`. -/
def p0 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0x41, 0x54, 0x49, 0x89, 0xfc, 0x53, 0x89, 0xf3, 0x48, 0x83, 0xec, 0x08,
  0x66, 0x83, 0x3f, 0x13]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem p0_4 : ∀ feat, Dec feat p0 4 (FV7z.mk .push 64 [gr 64 12] 2) := by dec_rfl
theorem p0_6 : ∀ feat, Dec feat p0 6 (FV7z.mk .mov 64 [gr 64 12, Src.opd 64 (.r 7)] 3) := by dec_rfl
theorem p0_9 : ∀ feat, Dec feat p0 9 (FV7z.mk .push 64 [gr 64 3] 1) := by dec_rfl
theorem p0_10 : ∀ feat, Dec feat p0 10 (FV7z.mk .mov 32 [gr 32 3, Src.opd 32 (.r 6)] 2) := by dec_rfl
theorem p0_12 : ∀ feat, Dec feat p0 12 (FV7z.mk .sub 64 [gr 64 4, Src.opd 64 (.i 8)] 4) := by dec_rfl
theorem p0_16 : ∀ feat, Dec feat p0 16 (FV7z.mk .cmp 16 [.mem (mg (some 7) none 1 0 16), .imm 16 19] 4) := by dec_rfl

/-- What the stretch does. -/
def o0 : List Op := [
  Op.nop,
  Op.push 12,
  Op.mov 64 12 (.r 7),
  Op.push 3,
  Op.mov 32 3 (.r 6),
  Op.sub 64 4 (.i 8),
  Op.cmpmi 16 (some 7) none 1 0 19]

theorem b0 (prof : Profile) : Blk prof p0 0 20 o0 :=
  .cons (p0_0 _) (OpI.endbr) (by decide) <|
  .cons (p0_4 _) (OpI.push) (by decide) <|
  .cons (p0_6 _) (OpI.mov (.r 7) (.inr rfl)) (by decide) <|
  .cons (p0_9 _) (OpI.push) (by decide) <|
  .cons (p0_10 _) (OpI.mov (.r 6) (.inl rfl)) (by decide) <|
  .cons (p0_12 _) (OpI.sub (.i 8) (.inr rfl)) (by decide) <|
  .cons (p0_16 _) (OpI.cmpmi16) (by decide) <|
  .nil 20

def j0 : List Byte := [0x74, 0x0f]
theorem j0_0 : ∀ feat, Dec feat j0 0 (FV7z.mk (.jcc 4) 64 [.rel 15] 2) := by dec_rfl

/-- The stretch at `27`. -/
def p1 : List Byte := [
  0xba, 0x13, 0x00, 0x00, 0x00, 0x66, 0x41, 0x89, 0x14, 0x24]

theorem p1_0 : ∀ feat, Dec feat p1 0 (FV7z.mk .mov 32 [gr 32 2, Src.opd 32 (.i 19)] 5) := by dec_rfl
theorem p1_5 : ∀ feat, Dec feat p1 5 (FV7z.mk .mov 16 [.mem (mg (some 12) none 1 0 16), gr 16 2] 5) := by dec_rfl

/-- What the stretch does. -/
def o1 : List Op := [
  Op.mov 32 2 (.i 19),
  Op.st 16 (some 12) none 1 0 2]

theorem b1 (prof : Profile) : Blk prof p1 0 10 o1 :=
  .cons (p1_0 _) (OpI.mov (.i 19) (.inl rfl)) (by decide) <|
  .cons (p1_5 _) (OpI.st (.inr (.inl rfl))) (by decide) <|
  .nil 10

/-- The stretch at `37`. -/
def p2 : List Byte := [
  0x31, 0xc0, 0x41, 0x89, 0x5c, 0x24, 0x08, 0x66, 0x41, 0x89, 0x44, 0x24, 0x02, 0x48, 0x83, 0xc4,
  0x08, 0x4c, 0x89, 0xe0, 0x5b, 0x41, 0x5c]

theorem p2_0 : ∀ feat, Dec feat p2 0 (FV7z.mk .xor 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl
theorem p2_2 : ∀ feat, Dec feat p2 2 (FV7z.mk .mov 32 [.mem (mg (some 12) none 1 8 32), gr 32 3] 5) := by dec_rfl
theorem p2_7 : ∀ feat, Dec feat p2 7 (FV7z.mk .mov 16 [.mem (mg (some 12) none 1 2 16), gr 16 0] 6) := by dec_rfl
theorem p2_13 : ∀ feat, Dec feat p2 13 (FV7z.mk .add 64 [gr 64 4, Src.opd 64 (.i 8)] 4) := by dec_rfl
theorem p2_17 : ∀ feat, Dec feat p2 17 (FV7z.mk .mov 64 [gr 64 0, Src.opd 64 (.r 12)] 3) := by dec_rfl
theorem p2_20 : ∀ feat, Dec feat p2 20 (FV7z.mk .pop 64 [gr 64 3] 1) := by dec_rfl
theorem p2_21 : ∀ feat, Dec feat p2 21 (FV7z.mk .pop 64 [gr 64 12] 2) := by dec_rfl

/-- What the stretch does. -/
def o2 : List Op := [
  Op.xor 32 0 (.r 0),
  Op.st 32 (some 12) none 1 8 3,
  Op.st 16 (some 12) none 1 2 0,
  Op.add 64 4 (.i 8),
  Op.mov 64 0 (.r 12),
  Op.pop 3,
  Op.pop 12]

theorem b2 (prof : Profile) : Blk prof p2 0 23 o2 :=
  .cons (p2_0 _) (OpI.xor (.r 0) (.inl rfl)) (by decide) <|
  .cons (p2_2 _) (OpI.st (.inr (.inr (.inl rfl)))) (by decide) <|
  .cons (p2_7 _) (OpI.st (.inr (.inl rfl))) (by decide) <|
  .cons (p2_13 _) (OpI.add (.i 8) (.inr rfl)) (by decide) <|
  .cons (p2_17 _) (OpI.mov (.r 12) (.inr rfl)) (by decide) <|
  .cons (p2_20 _) (OpI.pop) (by decide) <|
  .cons (p2_21 _) (OpI.pop) (by decide) <|
  .nil 23

end FV7z.Pvu
