import FV7z.Lemmas.Sp
import FV7z.Lemmas.BlkOps17
import FV7z.Lemmas.BlkOps3
/-!
# The stretches of straight-line code of `FiTime_To_FILETIME_ns100` (PLAN.md §M, M1)

Each distinct stretch between labels and jumps (`p*`, 2 of them) and each distinct jump (`j*`, 0) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.Fft
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The stretch at `0`. -/
def p0 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0x41, 0x54, 0x49, 0x89, 0xd4, 0x55, 0x48, 0x89, 0xf5, 0x53, 0x48, 0x89,
  0xfb, 0x48, 0x8b, 0x3f]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem p0_4 : ∀ feat, Dec feat p0 4 (FV7z.mk .push 64 [gr 64 12] 2) := by dec_rfl
theorem p0_6 : ∀ feat, Dec feat p0 6 (FV7z.mk .mov 64 [gr 64 12, Src.opd 64 (.r 2)] 3) := by dec_rfl
theorem p0_9 : ∀ feat, Dec feat p0 9 (FV7z.mk .push 64 [gr 64 5] 1) := by dec_rfl
theorem p0_10 : ∀ feat, Dec feat p0 10 (FV7z.mk .mov 64 [gr 64 5, Src.opd 64 (.r 6)] 3) := by dec_rfl
theorem p0_13 : ∀ feat, Dec feat p0 13 (FV7z.mk .push 64 [gr 64 3] 1) := by dec_rfl
theorem p0_14 : ∀ feat, Dec feat p0 14 (FV7z.mk .mov 64 [gr 64 3, Src.opd 64 (.r 7)] 3) := by dec_rfl
theorem p0_17 : ∀ feat, Dec feat p0 17 (FV7z.mk .mov 64 [gr 64 7, .mem (mg (some 7) none 1 0 64)] 3) := by dec_rfl

/-- What the stretch does. -/
def o0 : List Op := [
  Op.nop,
  Op.push 12,
  Op.mov 64 12 (.r 2),
  Op.push 5,
  Op.mov 64 5 (.r 6),
  Op.push 3,
  Op.mov 64 3 (.r 7),
  Op.ld 64 7 (some 7) none 1 0]

theorem b0 (prof : Profile) : Blk prof p0 0 20 o0 :=
  .cons (p0_0 _) (OpI.endbr) (by decide) <|
  .cons (p0_4 _) (OpI.push) (by decide) <|
  .cons (p0_6 _) (OpI.mov (.r 2) (.inr rfl)) (by decide) <|
  .cons (p0_9 _) (OpI.push) (by decide) <|
  .cons (p0_10 _) (OpI.mov (.r 6) (.inr rfl)) (by decide) <|
  .cons (p0_13 _) (OpI.push) (by decide) <|
  .cons (p0_14 _) (OpI.mov (.r 7) (.inr rfl)) (by decide) <|
  .cons (p0_17 _) (OpI.ld (.inr rfl)) (by decide) <|
  .nil 20

/-- The stretch at `25`. -/
def p1 : List Byte := [
  0x48, 0x8b, 0x4b, 0x08, 0x5b, 0x48, 0xbe, 0xc3, 0xf5, 0x28, 0x5c, 0x8f, 0xc2, 0xf5, 0x28, 0x49,
  0x89, 0xc0, 0x48, 0x89, 0xca, 0x48, 0xc1, 0xea, 0x02, 0x48, 0x89, 0xd0, 0x48, 0xf7, 0xe6, 0x48,
  0x89, 0xd0, 0x48, 0x83, 0xe2, 0xfc, 0x48, 0xc1, 0xe8, 0x02, 0x48, 0x01, 0xc2, 0x4c, 0x01, 0xc0,
  0x48, 0x8d, 0x14, 0x92, 0x48, 0xc1, 0xe2, 0x02, 0x48, 0x29, 0xd1, 0x41, 0x89, 0x0c, 0x24, 0x48,
  0x89, 0x45, 0x00, 0x5d, 0x41, 0x5c]

theorem p1_0 : ∀ feat, Dec feat p1 0 (FV7z.mk .mov 64 [gr 64 1, .mem (mg (some 3) none 1 8 64)] 4) := by dec_rfl
theorem p1_4 : ∀ feat, Dec feat p1 4 (FV7z.mk .pop 64 [gr 64 3] 1) := by dec_rfl
theorem p1_5 : ∀ feat, Dec feat p1 5 (FV7z.mk .mov 64 [gr 64 6, Src.opd 64 (.i 2951479051793528259)] 10) := by dec_rfl
theorem p1_15 : ∀ feat, Dec feat p1 15 (FV7z.mk .mov 64 [gr 64 8, Src.opd 64 (.r 0)] 3) := by dec_rfl
theorem p1_18 : ∀ feat, Dec feat p1 18 (FV7z.mk .mov 64 [gr 64 2, Src.opd 64 (.r 1)] 3) := by dec_rfl
theorem p1_21 : ∀ feat, Dec feat p1 21 (FV7z.mk .shr 64 [gr 64 2, Src.opd 8 (.i 2)] 4) := by dec_rfl
theorem p1_25 : ∀ feat, Dec feat p1 25 (FV7z.mk .mov 64 [gr 64 0, Src.opd 64 (.r 2)] 3) := by dec_rfl
theorem p1_28 : ∀ feat, Dec feat p1 28 (FV7z.mk .mul 64 [gr 64 6] 3) := by dec_rfl
theorem p1_31 : ∀ feat, Dec feat p1 31 (FV7z.mk .mov 64 [gr 64 0, Src.opd 64 (.r 2)] 3) := by dec_rfl
theorem p1_34 : ∀ feat, Dec feat p1 34 (FV7z.mk .and 64 [gr 64 2, Src.opd 64 (.i 18446744073709551612)] 4) := by dec_rfl
theorem p1_38 : ∀ feat, Dec feat p1 38 (FV7z.mk .shr 64 [gr 64 0, Src.opd 8 (.i 2)] 4) := by dec_rfl
theorem p1_42 : ∀ feat, Dec feat p1 42 (FV7z.mk .add 64 [gr 64 2, Src.opd 64 (.r 0)] 3) := by dec_rfl
theorem p1_45 : ∀ feat, Dec feat p1 45 (FV7z.mk .add 64 [gr 64 0, Src.opd 64 (.r 8)] 3) := by dec_rfl
theorem p1_48 : ∀ feat, Dec feat p1 48 (FV7z.mk .lea 64 [gr 64 2, .mem (mg (some 2) (some 2) 4 0 0)] 4) := by dec_rfl
theorem p1_52 : ∀ feat, Dec feat p1 52 (FV7z.mk .shl 64 [gr 64 2, Src.opd 8 (.i 2)] 4) := by dec_rfl
theorem p1_56 : ∀ feat, Dec feat p1 56 (FV7z.mk .sub 64 [gr 64 1, Src.opd 64 (.r 2)] 3) := by dec_rfl
theorem p1_59 : ∀ feat, Dec feat p1 59 (FV7z.mk .mov 32 [.mem (mg (some 12) none 1 0 32), gr 32 1] 4) := by dec_rfl
theorem p1_63 : ∀ feat, Dec feat p1 63 (FV7z.mk .mov 64 [.mem (mg (some 5) none 1 0 64), gr 64 0] 4) := by dec_rfl
theorem p1_67 : ∀ feat, Dec feat p1 67 (FV7z.mk .pop 64 [gr 64 5] 1) := by dec_rfl
theorem p1_68 : ∀ feat, Dec feat p1 68 (FV7z.mk .pop 64 [gr 64 12] 2) := by dec_rfl

/-- What the stretch does. -/
def o1 : List Op := [
  Op.ld 64 1 (some 3) none 1 8,
  Op.pop 3,
  Op.mov 64 6 (.i 2951479051793528259),
  Op.mov 64 8 (.r 0),
  Op.mov 64 2 (.r 1),
  Op.shr64 2 (.i 2),
  Op.mov 64 0 (.r 2),
  Op.mul64 6,
  Op.mov 64 0 (.r 2),
  Op.and 64 2 (.i 18446744073709551612),
  Op.shr64 0 (.i 2),
  Op.add 64 2 (.r 0),
  Op.add 64 0 (.r 8),
  Op.lea 64 2 (some 2) (some 2) 4 0,
  Op.shl64 2 (.i 2),
  Op.sub 64 1 (.r 2),
  Op.st 32 (some 12) none 1 0 1,
  Op.st 64 (some 5) none 1 0 0,
  Op.pop 5,
  Op.pop 12]

theorem b1 (prof : Profile) : Blk prof p1 0 70 o1 :=
  .cons (p1_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p1_4 _) (OpI.pop) (by decide) <|
  .cons (p1_5 _) (OpI.mov (.i 2951479051793528259) (.inr rfl)) (by decide) <|
  .cons (p1_15 _) (OpI.mov (.r 0) (.inr rfl)) (by decide) <|
  .cons (p1_18 _) (OpI.mov (.r 1) (.inr rfl)) (by decide) <|
  .cons (p1_21 _) (OpI.shr64 (.i 2)) (by decide) <|
  .cons (p1_25 _) (OpI.mov (.r 2) (.inr rfl)) (by decide) <|
  .cons (p1_28 _) (OpI.mul64) (by decide) <|
  .cons (p1_31 _) (OpI.mov (.r 2) (.inr rfl)) (by decide) <|
  .cons (p1_34 _) (OpI.and (.i 18446744073709551612) (.inr rfl)) (by decide) <|
  .cons (p1_38 _) (OpI.shr64 (.i 2)) (by decide) <|
  .cons (p1_42 _) (OpI.add (.r 0) (.inr rfl)) (by decide) <|
  .cons (p1_45 _) (OpI.add (.r 8) (.inr rfl)) (by decide) <|
  .cons (p1_48 _) (OpI.lea (.inr rfl)) (by decide) <|
  .cons (p1_52 _) (OpI.shl64 (.i 2)) (by decide) <|
  .cons (p1_56 _) (OpI.sub (.r 2) (.inr rfl)) (by decide) <|
  .cons (p1_59 _) (OpI.st (.inr (.inr (.inl rfl)))) (by decide) <|
  .cons (p1_63 _) (OpI.st (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p1_67 _) (OpI.pop) (by decide) <|
  .cons (p1_68 _) (OpI.pop) (by decide) <|
  .nil 70

end FV7z.Fft
