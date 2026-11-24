import FV7z.Lemmas.Sp
import FV7z.Lemmas.BlkOps2
/-!
# The stretches of straight-line code of `csuTg 75` (PLAN.md G3, constructors)

Each distinct stretch between labels and jumps (`p*`, 2 of them) and each distinct jump (`j*`, 1) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.C75
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The stretch at `1584`. -/
def p0 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0x48, 0xc7, 0xc6, 0x40, 0xd3, 0x79, 0x00, 0x31, 0xc9, 0x0f, 0x1f, 0x00]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem p0_4 : ∀ feat, Dec feat p0 4 (FV7z.mk .mov 64 [gr 64 6, Src.opd 64 (.i 7983936)] 7) := by dec_rfl
theorem p0_11 : ∀ feat, Dec feat p0 11 (FV7z.mk .xor 32 [gr 32 1, Src.opd 32 (.r 1)] 2) := by dec_rfl
theorem p0_13 : ∀ feat, Dec feat p0 13 (FV7z.mk .nop 32 [.mem (mg (some 0) none 1 0 32)] 3) := by dec_rfl

/-- What the stretch does. -/
def o0 : List Op := [
  Op.nop,
  Op.mov 64 6 (.i 7983936),
  Op.xor 32 1 (.r 1),
  Op.nop]

theorem b0 (prof : Profile) : Blk prof p0 0 16 o0 :=
  .cons (p0_0 _) (OpI.endbr) (by decide) <|
  .cons (p0_4 _) (OpI.mov (.i 7983936) (.inr rfl)) (by decide) <|
  .cons (p0_11 _) (OpI.xor (.r 1) (.inl rfl)) (by decide) <|
  .cons (p0_13 _) (OpI.nop) (by decide) <|
  .nil 16

/-- The stretch at `1600`. -/
def p1 : List Byte := [
  0x89, 0xca, 0x8d, 0x04, 0x09, 0x48, 0x83, 0xc1, 0x01, 0xd1, 0xea, 0x25, 0xaa, 0x00, 0x00, 0x00,
  0x83, 0xe2, 0x55, 0x09, 0xd0, 0x8d, 0x14, 0x85, 0x00, 0x00, 0x00, 0x00, 0xc1, 0xe8, 0x02, 0x81,
  0xe2, 0xcc, 0x00, 0x00, 0x00, 0x83, 0xe0, 0x33, 0x09, 0xd0, 0x89, 0xc2, 0xc1, 0xe8, 0x04, 0xc1,
  0xe2, 0x04, 0x09, 0xd0, 0x88, 0x44, 0x31, 0xff, 0x48, 0x81, 0xf9, 0x00, 0x01, 0x00, 0x00]

theorem p1_0 : ∀ feat, Dec feat p1 0 (FV7z.mk .mov 32 [gr 32 2, Src.opd 32 (.r 1)] 2) := by dec_rfl
theorem p1_2 : ∀ feat, Dec feat p1 2 (FV7z.mk .lea 32 [gr 32 0, .mem (mg (some 1) (some 1) 1 0 0)] 3) := by dec_rfl
theorem p1_5 : ∀ feat, Dec feat p1 5 (FV7z.mk .add 64 [gr 64 1, Src.opd 64 (.i 1)] 4) := by dec_rfl
theorem p1_9 : ∀ feat, Dec feat p1 9 (FV7z.mk .shr 32 [gr 32 2, Src.opd 8 (.i 1)] 2) := by dec_rfl
theorem p1_11 : ∀ feat, Dec feat p1 11 (FV7z.mk .and 32 [gr 32 0, Src.opd 32 (.i 170)] 5) := by dec_rfl
theorem p1_16 : ∀ feat, Dec feat p1 16 (FV7z.mk .and 32 [gr 32 2, Src.opd 32 (.i 85)] 3) := by dec_rfl
theorem p1_19 : ∀ feat, Dec feat p1 19 (FV7z.mk .or 32 [gr 32 0, Src.opd 32 (.r 2)] 2) := by dec_rfl
theorem p1_21 : ∀ feat, Dec feat p1 21 (FV7z.mk .lea 32 [gr 32 2, .mem (mg none (some 0) 4 0 0)] 7) := by dec_rfl
theorem p1_28 : ∀ feat, Dec feat p1 28 (FV7z.mk .shr 32 [gr 32 0, Src.opd 8 (.i 2)] 3) := by dec_rfl
theorem p1_31 : ∀ feat, Dec feat p1 31 (FV7z.mk .and 32 [gr 32 2, Src.opd 32 (.i 204)] 6) := by dec_rfl
theorem p1_37 : ∀ feat, Dec feat p1 37 (FV7z.mk .and 32 [gr 32 0, Src.opd 32 (.i 51)] 3) := by dec_rfl
theorem p1_40 : ∀ feat, Dec feat p1 40 (FV7z.mk .or 32 [gr 32 0, Src.opd 32 (.r 2)] 2) := by dec_rfl
theorem p1_42 : ∀ feat, Dec feat p1 42 (FV7z.mk .mov 32 [gr 32 2, Src.opd 32 (.r 0)] 2) := by dec_rfl
theorem p1_44 : ∀ feat, Dec feat p1 44 (FV7z.mk .shr 32 [gr 32 0, Src.opd 8 (.i 4)] 3) := by dec_rfl
theorem p1_47 : ∀ feat, Dec feat p1 47 (FV7z.mk .shl 32 [gr 32 2, Src.opd 8 (.i 4)] 3) := by dec_rfl
theorem p1_50 : ∀ feat, Dec feat p1 50 (FV7z.mk .or 32 [gr 32 0, Src.opd 32 (.r 2)] 2) := by dec_rfl
theorem p1_52 : ∀ feat, Dec feat p1 52 (FV7z.mk .mov 8 [.mem (mg (some 1) (some 6) 1 18446744073709551615 8), gr 8 0] 4) := by dec_rfl
theorem p1_56 : ∀ feat, Dec feat p1 56 (FV7z.mk .cmp 64 [gr 64 1, Src.opd 64 (.i 256)] 7) := by dec_rfl

/-- What the stretch does. -/
def o1 : List Op := [
  Op.mov 32 2 (.r 1),
  Op.lea 32 0 (some 1) (some 1) 1 0,
  Op.add 64 1 (.i 1),
  Op.shr 2 (.i 1),
  Op.and 32 0 (.i 170),
  Op.and 32 2 (.i 85),
  Op.or 32 0 (.r 2),
  Op.lea 32 2 none (some 0) 4 0,
  Op.shr 0 (.i 2),
  Op.and 32 2 (.i 204),
  Op.and 32 0 (.i 51),
  Op.or 32 0 (.r 2),
  Op.mov 32 2 (.r 0),
  Op.shr 0 (.i 4),
  Op.shl 2 (.i 4),
  Op.or 32 0 (.r 2),
  Op.st 8 (some 1) (some 6) 1 18446744073709551615 0,
  Op.cmp 64 1 (.i 256)]

theorem b1 (prof : Profile) : Blk prof p1 0 63 o1 :=
  .cons (p1_0 _) (OpI.mov (.r 1) (.inl rfl)) (by decide) <|
  .cons (p1_2 _) (OpI.lea (.inl rfl)) (by decide) <|
  .cons (p1_5 _) (OpI.add (.i 1) (.inr rfl)) (by decide) <|
  .cons (p1_9 _) (OpI.shr (.i 1)) (by decide) <|
  .cons (p1_11 _) (OpI.and (.i 170) (.inl rfl)) (by decide) <|
  .cons (p1_16 _) (OpI.and (.i 85) (.inl rfl)) (by decide) <|
  .cons (p1_19 _) (OpI.or (.r 2) (.inl rfl)) (by decide) <|
  .cons (p1_21 _) (OpI.lea (.inl rfl)) (by decide) <|
  .cons (p1_28 _) (OpI.shr (.i 2)) (by decide) <|
  .cons (p1_31 _) (OpI.and (.i 204) (.inl rfl)) (by decide) <|
  .cons (p1_37 _) (OpI.and (.i 51) (.inl rfl)) (by decide) <|
  .cons (p1_40 _) (OpI.or (.r 2) (.inl rfl)) (by decide) <|
  .cons (p1_42 _) (OpI.mov (.r 0) (.inl rfl)) (by decide) <|
  .cons (p1_44 _) (OpI.shr (.i 4)) (by decide) <|
  .cons (p1_47 _) (OpI.shl (.i 4)) (by decide) <|
  .cons (p1_50 _) (OpI.or (.r 2) (.inl rfl)) (by decide) <|
  .cons (p1_52 _) (OpI.st (.inl rfl)) (by decide) <|
  .cons (p1_56 _) (OpI.cmp (.i 256) (.inr rfl)) (by decide) <|
  .nil 63

def j0 : List Byte := [0x75, 0xbf]
theorem j0_0 : ∀ feat, Dec feat j0 0 (FV7z.mk (.jcc 5) 64 [.rel 18446744073709551551] 2) := by dec_rfl

end FV7z.C75
