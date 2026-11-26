import FV7z.Lemmas.SpFs
import FV7z.Lemmas.BlkOps2
/-!
# The stretches of straight-line code of `munmap_chunk` (PLAN.md §M, M1)

Each distinct stretch between labels and jumps (`p*`, 4 of them) and each distinct jump (`j*`, 2) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.Mck
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The stretch at `0`. -/
def p0 : List Byte := [
  0x48, 0x83, 0xec, 0x08, 0x48, 0x8b, 0x57, 0x08, 0x48, 0x8b, 0x05, 0x69, 0x4d, 0x16, 0x00, 0x48,
  0x89, 0xd1, 0x48, 0x83, 0xe1, 0xf8, 0x83, 0xe2, 0x02]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .sub 64 [gr 64 4, Src.opd 64 (.i 8)] 4) := by dec_rfl
theorem p0_4 : ∀ feat, Dec feat p0 4 (FV7z.mk .mov 64 [gr 64 2, .mem (mg (some 7) none 1 8 64)] 4) := by dec_rfl
theorem p0_8 : ∀ feat, Dec feat p0 8 (FV7z.mk .mov 64 [gr 64 0, .mem (mrip 1461609 64)] 7) := by dec_rfl
theorem p0_15 : ∀ feat, Dec feat p0 15 (FV7z.mk .mov 64 [gr 64 1, Src.opd 64 (.r 2)] 3) := by dec_rfl
theorem p0_18 : ∀ feat, Dec feat p0 18 (FV7z.mk .and 64 [gr 64 1, Src.opd 64 (.i 18446744073709551608)] 4) := by dec_rfl
theorem p0_22 : ∀ feat, Dec feat p0 22 (FV7z.mk .and 32 [gr 32 2, Src.opd 32 (.i 2)] 3) := by dec_rfl

/-- What the stretch does. -/
def o0 : List Op := [
  Op.sub 64 4 (.i 8),
  Op.ld 64 2 (some 7) none 1 8,
  Op.lda 64 0 7943128,
  Op.mov 64 1 (.r 2),
  Op.and 64 1 (.i 18446744073709551608),
  Op.and 32 2 (.i 2)]

theorem b0 (prof : Profile) : BlkA prof p0 (0x62e660 : Addr) 0 25 o0 :=
  .cons (p0_0 _) ((OpI.sub (.i 8) (.inr rfl)).at _) (by decide) <|
  .cons (p0_4 _) ((OpI.ld (.inr rfl)).at _) (by decide) <|
  .cons (p0_8 _) (OpIA.ld_rip (.inr rfl) (by decide)) (by decide) <|
  .cons (p0_15 _) ((OpI.mov (.r 2) (.inr rfl)).at _) (by decide) <|
  .cons (p0_18 _) ((OpI.and (.i 18446744073709551608) (.inr rfl)).at _) (by decide) <|
  .cons (p0_22 _) ((OpI.and (.i 2) (.inl rfl)).at _) (by decide) <|
  .nil 25

def j0 : List Byte := [0x74, 0x61]
theorem j0_0 : ∀ feat, Dec feat j0 0 (FV7z.mk (.jcc 4) 64 [.rel 97] 2) := by dec_rfl

/-- The stretch at `27`. -/
def p1 : List Byte := [
  0x48, 0x8b, 0x37, 0x49, 0x89, 0xf8, 0x48, 0x83, 0xe8, 0x01, 0x48, 0x83, 0xc7, 0x10, 0x48, 0x21,
  0xc7, 0x49, 0x29, 0xf0, 0x48, 0x01, 0xce, 0x4c, 0x89, 0xc2, 0x48, 0x09, 0xf2, 0x48, 0x21, 0xd0,
  0x48, 0x8d, 0x57, 0xff, 0x48, 0x21, 0xd7, 0x48, 0x09, 0xf8]

theorem p1_0 : ∀ feat, Dec feat p1 0 (FV7z.mk .mov 64 [gr 64 6, .mem (mg (some 7) none 1 0 64)] 3) := by dec_rfl
theorem p1_3 : ∀ feat, Dec feat p1 3 (FV7z.mk .mov 64 [gr 64 8, Src.opd 64 (.r 7)] 3) := by dec_rfl
theorem p1_6 : ∀ feat, Dec feat p1 6 (FV7z.mk .sub 64 [gr 64 0, Src.opd 64 (.i 1)] 4) := by dec_rfl
theorem p1_10 : ∀ feat, Dec feat p1 10 (FV7z.mk .add 64 [gr 64 7, Src.opd 64 (.i 16)] 4) := by dec_rfl
theorem p1_14 : ∀ feat, Dec feat p1 14 (FV7z.mk .and 64 [gr 64 7, Src.opd 64 (.r 0)] 3) := by dec_rfl
theorem p1_17 : ∀ feat, Dec feat p1 17 (FV7z.mk .sub 64 [gr 64 8, Src.opd 64 (.r 6)] 3) := by dec_rfl
theorem p1_20 : ∀ feat, Dec feat p1 20 (FV7z.mk .add 64 [gr 64 6, Src.opd 64 (.r 1)] 3) := by dec_rfl
theorem p1_23 : ∀ feat, Dec feat p1 23 (FV7z.mk .mov 64 [gr 64 2, Src.opd 64 (.r 8)] 3) := by dec_rfl
theorem p1_26 : ∀ feat, Dec feat p1 26 (FV7z.mk .or 64 [gr 64 2, Src.opd 64 (.r 6)] 3) := by dec_rfl
theorem p1_29 : ∀ feat, Dec feat p1 29 (FV7z.mk .and 64 [gr 64 0, Src.opd 64 (.r 2)] 3) := by dec_rfl
theorem p1_32 : ∀ feat, Dec feat p1 32 (FV7z.mk .lea 64 [gr 64 2, .mem (mg (some 7) none 1 18446744073709551615 0)] 4) := by dec_rfl
theorem p1_36 : ∀ feat, Dec feat p1 36 (FV7z.mk .and 64 [gr 64 7, Src.opd 64 (.r 2)] 3) := by dec_rfl
theorem p1_39 : ∀ feat, Dec feat p1 39 (FV7z.mk .or 64 [gr 64 0, Src.opd 64 (.r 7)] 3) := by dec_rfl

/-- What the stretch does. -/
def o1 : List Op := [
  Op.ld 64 6 (some 7) none 1 0,
  Op.mov 64 8 (.r 7),
  Op.sub 64 0 (.i 1),
  Op.add 64 7 (.i 16),
  Op.and 64 7 (.r 0),
  Op.sub 64 8 (.r 6),
  Op.add 64 6 (.r 1),
  Op.mov 64 2 (.r 8),
  Op.or 64 2 (.r 6),
  Op.and 64 0 (.r 2),
  Op.lea 64 2 (some 7) none 1 18446744073709551615,
  Op.and 64 7 (.r 2),
  Op.or 64 0 (.r 7)]

theorem b1 (prof : Profile) : Blk prof p1 0 42 o1 :=
  .cons (p1_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p1_3 _) (OpI.mov (.r 7) (.inr rfl)) (by decide) <|
  .cons (p1_6 _) (OpI.sub (.i 1) (.inr rfl)) (by decide) <|
  .cons (p1_10 _) (OpI.add (.i 16) (.inr rfl)) (by decide) <|
  .cons (p1_14 _) (OpI.and (.r 0) (.inr rfl)) (by decide) <|
  .cons (p1_17 _) (OpI.sub (.r 6) (.inr rfl)) (by decide) <|
  .cons (p1_20 _) (OpI.add (.r 1) (.inr rfl)) (by decide) <|
  .cons (p1_23 _) (OpI.mov (.r 8) (.inr rfl)) (by decide) <|
  .cons (p1_26 _) (OpI.or (.r 6) (.inr rfl)) (by decide) <|
  .cons (p1_29 _) (OpI.and (.r 2) (.inr rfl)) (by decide) <|
  .cons (p1_32 _) (OpI.lea (.inr rfl)) (by decide) <|
  .cons (p1_36 _) (OpI.and (.r 2) (.inr rfl)) (by decide) <|
  .cons (p1_39 _) (OpI.or (.r 7) (.inr rfl)) (by decide) <|
  .nil 42

def j1 : List Byte := [0x75, 0x29]
theorem j1_0 : ∀ feat, Dec feat j1 0 (FV7z.mk (.jcc 5) 64 [.rel 41] 2) := by dec_rfl

/-- The stretch at `78`. -/
def p2 : List Byte := [
  0x48, 0x89, 0xf0, 0x48, 0xf7, 0xd8]

theorem p2_0 : ∀ feat, Dec feat p2 0 (FV7z.mk .mov 64 [gr 64 0, Src.opd 64 (.r 6)] 3) := by dec_rfl
theorem p2_3 : ∀ feat, Dec feat p2 3 (FV7z.mk .neg 64 [gr 64 0] 3) := by dec_rfl

/-- What the stretch does. -/
def o2 : List Op := [
  Op.mov 64 0 (.r 6),
  Op.neg 64 0]

theorem b2 (prof : Profile) : Blk prof p2 0 6 o2 :=
  .cons (p2_0 _) (OpI.mov (.r 6) (.inr rfl)) (by decide) <|
  .cons (p2_3 _) (OpI.neg (.inr rfl)) (by decide) <|
  .nil 6

/-- The stretch at `92`. -/
def p3 : List Byte := [
  0x4c, 0x89, 0xc7, 0x48, 0x83, 0xc4, 0x08]

theorem p3_0 : ∀ feat, Dec feat p3 0 (FV7z.mk .mov 64 [gr 64 7, Src.opd 64 (.r 8)] 3) := by dec_rfl
theorem p3_3 : ∀ feat, Dec feat p3 3 (FV7z.mk .add 64 [gr 64 4, Src.opd 64 (.i 8)] 4) := by dec_rfl

/-- What the stretch does. -/
def o3 : List Op := [
  Op.mov 64 7 (.r 8),
  Op.add 64 4 (.i 8)]

theorem b3 (prof : Profile) : Blk prof p3 0 7 o3 :=
  .cons (p3_0 _) (OpI.mov (.r 8) (.inr rfl)) (by decide) <|
  .cons (p3_3 _) (OpI.add (.i 8) (.inr rfl)) (by decide) <|
  .nil 7

end FV7z.Mck
