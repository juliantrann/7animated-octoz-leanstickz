import FV7z.Lemmas.Sp
import FV7z.Lemmas.BlkOps2
/-!
# The stretches of straight-line code of `CBZip2Crc::InitTable` (PLAN.md G3, constructors)

Each distinct stretch between labels and jumps (`p*`, 4 of them) and each distinct jump (`j*`, 2) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.C78
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The stretch at `0`. -/
def p0 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0x48, 0xc7, 0xc6, 0x40, 0xd4, 0x79, 0x00, 0x31, 0xff, 0x4c, 0x8d, 0x86,
  0x00, 0x04, 0x00, 0x00, 0x0f, 0x1f, 0x40, 0x00]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem p0_4 : ∀ feat, Dec feat p0 4 (FV7z.mk .mov 64 [gr 64 6, Src.opd 64 (.i 7984192)] 7) := by dec_rfl
theorem p0_11 : ∀ feat, Dec feat p0 11 (FV7z.mk .xor 32 [gr 32 7, Src.opd 32 (.r 7)] 2) := by dec_rfl
theorem p0_13 : ∀ feat, Dec feat p0 13 (FV7z.mk .lea 64 [gr 64 8, .mem (mg (some 6) none 1 1024 0)] 7) := by dec_rfl
theorem p0_20 : ∀ feat, Dec feat p0 20 (FV7z.mk .nop 32 [.mem (mg (some 0) none 1 0 32)] 4) := by dec_rfl

/-- What the stretch does. -/
def o0 : List Op := [
  Op.nop,
  Op.mov 64 6 (.i 7984192),
  Op.xor 32 7 (.r 7),
  Op.lea 64 8 (some 6) none 1 1024,
  Op.nop]

theorem b0 (prof : Profile) : Blk prof p0 0 24 o0 :=
  .cons (p0_0 _) (OpI.endbr) (by decide) <|
  .cons (p0_4 _) (OpI.mov (.i 7984192) (.inr rfl)) (by decide) <|
  .cons (p0_11 _) (OpI.xor (.r 7) (.inl rfl)) (by decide) <|
  .cons (p0_13 _) (OpI.lea (.inr rfl)) (by decide) <|
  .cons (p0_20 _) (OpI.nop) (by decide) <|
  .nil 24

/-- The stretch at `24`. -/
def p1 : List Byte := [
  0x89, 0xf8, 0xba, 0x08, 0x00, 0x00, 0x00, 0x90]

theorem p1_0 : ∀ feat, Dec feat p1 0 (FV7z.mk .mov 32 [gr 32 0, Src.opd 32 (.r 7)] 2) := by dec_rfl
theorem p1_2 : ∀ feat, Dec feat p1 2 (FV7z.mk .mov 32 [gr 32 2, Src.opd 32 (.i 8)] 5) := by dec_rfl
theorem p1_7 : ∀ feat, Dec feat p1 7 (FV7z.mk .nop 32 [] 1) := by dec_rfl

/-- What the stretch does. -/
def o1 : List Op := [
  Op.mov 32 0 (.r 7),
  Op.mov 32 2 (.i 8),
  Op.nop]

theorem b1 (prof : Profile) : Blk prof p1 0 8 o1 :=
  .cons (p1_0 _) (OpI.mov (.r 7) (.inl rfl)) (by decide) <|
  .cons (p1_2 _) (OpI.mov (.i 8) (.inl rfl)) (by decide) <|
  .cons (p1_7 _) (OpI.nop) (by decide) <|
  .nil 8

/-- The stretch at `32`. -/
def p2 : List Byte := [
  0x8d, 0x0c, 0x00, 0xc1, 0xf8, 0x1f, 0x25, 0xb7, 0x1d, 0xc1, 0x04, 0x31, 0xc8, 0x83, 0xea, 0x01]

theorem p2_0 : ∀ feat, Dec feat p2 0 (FV7z.mk .lea 32 [gr 32 1, .mem (mg (some 0) (some 0) 1 0 0)] 3) := by dec_rfl
theorem p2_3 : ∀ feat, Dec feat p2 3 (FV7z.mk .sar 32 [gr 32 0, Src.opd 8 (.i 31)] 3) := by dec_rfl
theorem p2_6 : ∀ feat, Dec feat p2 6 (FV7z.mk .and 32 [gr 32 0, Src.opd 32 (.i 79764919)] 5) := by dec_rfl
theorem p2_11 : ∀ feat, Dec feat p2 11 (FV7z.mk .xor 32 [gr 32 0, Src.opd 32 (.r 1)] 2) := by dec_rfl
theorem p2_13 : ∀ feat, Dec feat p2 13 (FV7z.mk .sub 32 [gr 32 2, Src.opd 32 (.i 1)] 3) := by dec_rfl

/-- What the stretch does. -/
def o2 : List Op := [
  Op.lea 32 1 (some 0) (some 0) 1 0,
  Op.sar 0 (.i 31),
  Op.and 32 0 (.i 79764919),
  Op.xor 32 0 (.r 1),
  Op.sub 32 2 (.i 1)]

theorem b2 (prof : Profile) : Blk prof p2 0 16 o2 :=
  .cons (p2_0 _) (OpI.lea (.inl rfl)) (by decide) <|
  .cons (p2_3 _) (OpI.sar (.i 31)) (by decide) <|
  .cons (p2_6 _) (OpI.and (.i 79764919) (.inl rfl)) (by decide) <|
  .cons (p2_11 _) (OpI.xor (.r 1) (.inl rfl)) (by decide) <|
  .cons (p2_13 _) (OpI.sub (.i 1) (.inl rfl)) (by decide) <|
  .nil 16

def j0 : List Byte := [0x75, 0xee]
theorem j0_0 : ∀ feat, Dec feat j0 0 (FV7z.mk (.jcc 5) 64 [.rel 18446744073709551598] 2) := by dec_rfl

/-- The stretch at `50`. -/
def p3 : List Byte := [
  0x89, 0x06, 0x48, 0x83, 0xc6, 0x04, 0x81, 0xc7, 0x00, 0x00, 0x00, 0x01, 0x49, 0x39, 0xf0]

theorem p3_0 : ∀ feat, Dec feat p3 0 (FV7z.mk .mov 32 [.mem (mg (some 6) none 1 0 32), gr 32 0] 2) := by dec_rfl
theorem p3_2 : ∀ feat, Dec feat p3 2 (FV7z.mk .add 64 [gr 64 6, Src.opd 64 (.i 4)] 4) := by dec_rfl
theorem p3_6 : ∀ feat, Dec feat p3 6 (FV7z.mk .add 32 [gr 32 7, Src.opd 32 (.i 16777216)] 6) := by dec_rfl
theorem p3_12 : ∀ feat, Dec feat p3 12 (FV7z.mk .cmp 64 [gr 64 8, Src.opd 64 (.r 6)] 3) := by dec_rfl

/-- What the stretch does. -/
def o3 : List Op := [
  Op.st 32 (some 6) none 1 0 0,
  Op.add 64 6 (.i 4),
  Op.add 32 7 (.i 16777216),
  Op.cmp 64 8 (.r 6)]

theorem b3 (prof : Profile) : Blk prof p3 0 15 o3 :=
  .cons (p3_0 _) (OpI.st (.inr (.inr (.inl rfl)))) (by decide) <|
  .cons (p3_2 _) (OpI.add (.i 4) (.inr rfl)) (by decide) <|
  .cons (p3_6 _) (OpI.add (.i 16777216) (.inl rfl)) (by decide) <|
  .cons (p3_12 _) (OpI.cmp (.r 6) (.inr rfl)) (by decide) <|
  .nil 15

def j1 : List Byte := [0x75, 0xd5]
theorem j1_0 : ∀ feat, Dec feat j1 0 (FV7z.mk (.jcc 5) 64 [.rel 18446744073709551573] 2) := by dec_rfl

end FV7z.C78
