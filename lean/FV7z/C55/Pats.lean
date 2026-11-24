import FV7z.Lemmas.Sp
import FV7z.Lemmas.BlkOps2
/-!
# The stretches of straight-line code of `csuTg 55` (PLAN.md G3, constructors)

Each distinct stretch between labels and jumps (`p*`, 5 of them) and each distinct jump (`j*`, 2) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.C55
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The stretch at `1056`. -/
def p0 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0x31, 0xd2, 0x48, 0x8d, 0x35, 0xd3, 0x07, 0x38, 0x00, 0x0f, 0x1f, 0x00]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem p0_4 : ∀ feat, Dec feat p0 4 (FV7z.mk .xor 32 [gr 32 2, Src.opd 32 (.r 2)] 2) := by dec_rfl
theorem p0_6 : ∀ feat, Dec feat p0 6 (FV7z.mk .lea 64 [gr 64 6, .mem (mrip 3672019 0)] 7) := by dec_rfl
theorem p0_13 : ∀ feat, Dec feat p0 13 (FV7z.mk .nop 32 [.mem (mg (some 0) none 1 0 32)] 3) := by dec_rfl

/-- What the stretch does. -/
def o0 : List Op := [
  Op.nop,
  Op.xor 32 2 (.r 2),
  Op.mov 64 6 (.i 7982400),
  Op.nop]

theorem b0 (prof : Profile) : BlkA prof p0 (0x41c560 : Addr) 0 16 o0 :=
  .cons (p0_0 _) ((OpI.endbr).at _) (by decide) <|
  .cons (p0_4 _) ((OpI.xor (.r 2) (.inl rfl)).at _) (by decide) <|
  .cons (p0_6 _) (OpIA.lea_rip (by decide)) (by decide) <|
  .cons (p0_13 _) ((OpI.nop).at _) (by decide) <|
  .nil 16

/-- The stretch at `1072`. -/
def p1 : List Byte := [
  0x89, 0xd0, 0xb9, 0x08, 0x00, 0x00, 0x00]

theorem p1_0 : ∀ feat, Dec feat p1 0 (FV7z.mk .mov 32 [gr 32 0, Src.opd 32 (.r 2)] 2) := by dec_rfl
theorem p1_2 : ∀ feat, Dec feat p1 2 (FV7z.mk .mov 32 [gr 32 1, Src.opd 32 (.i 8)] 5) := by dec_rfl

/-- What the stretch does. -/
def o1 : List Op := [
  Op.mov 32 0 (.r 2),
  Op.mov 32 1 (.i 8)]

theorem b1 (prof : Profile) : Blk prof p1 0 7 o1 :=
  .cons (p1_0 _) (OpI.mov (.r 2) (.inl rfl)) (by decide) <|
  .cons (p1_2 _) (OpI.mov (.i 8) (.inl rfl)) (by decide) <|
  .nil 7

/-- The stretch at `1079`. -/
def p2 : List Byte := [
  0x89, 0xc7, 0x83, 0xe0, 0x01, 0xf7, 0xd8, 0xd1, 0xef, 0x25, 0x78, 0x3b, 0xf6, 0x82, 0x31, 0xf8,
  0x83, 0xe9, 0x01]

theorem p2_0 : ∀ feat, Dec feat p2 0 (FV7z.mk .mov 32 [gr 32 7, Src.opd 32 (.r 0)] 2) := by dec_rfl
theorem p2_2 : ∀ feat, Dec feat p2 2 (FV7z.mk .and 32 [gr 32 0, Src.opd 32 (.i 1)] 3) := by dec_rfl
theorem p2_5 : ∀ feat, Dec feat p2 5 (FV7z.mk .neg 32 [gr 32 0] 2) := by dec_rfl
theorem p2_7 : ∀ feat, Dec feat p2 7 (FV7z.mk .shr 32 [gr 32 7, Src.opd 8 (.i 1)] 2) := by dec_rfl
theorem p2_9 : ∀ feat, Dec feat p2 9 (FV7z.mk .and 32 [gr 32 0, Src.opd 32 (.i 2197175160)] 5) := by dec_rfl
theorem p2_14 : ∀ feat, Dec feat p2 14 (FV7z.mk .xor 32 [gr 32 0, Src.opd 32 (.r 7)] 2) := by dec_rfl
theorem p2_16 : ∀ feat, Dec feat p2 16 (FV7z.mk .sub 32 [gr 32 1, Src.opd 32 (.i 1)] 3) := by dec_rfl

/-- What the stretch does. -/
def o2 : List Op := [
  Op.mov 32 7 (.r 0),
  Op.and 32 0 (.i 1),
  Op.neg 32 0,
  Op.shr 7 (.i 1),
  Op.and 32 0 (.i 2197175160),
  Op.xor 32 0 (.r 7),
  Op.sub 32 1 (.i 1)]

theorem b2 (prof : Profile) : Blk prof p2 0 19 o2 :=
  .cons (p2_0 _) (OpI.mov (.r 0) (.inl rfl)) (by decide) <|
  .cons (p2_2 _) (OpI.and (.i 1) (.inl rfl)) (by decide) <|
  .cons (p2_5 _) (OpI.neg (.inl rfl)) (by decide) <|
  .cons (p2_7 _) (OpI.shr (.i 1)) (by decide) <|
  .cons (p2_9 _) (OpI.and (.i 2197175160) (.inl rfl)) (by decide) <|
  .cons (p2_14 _) (OpI.xor (.r 7) (.inl rfl)) (by decide) <|
  .cons (p2_16 _) (OpI.sub (.i 1) (.inl rfl)) (by decide) <|
  .nil 19

def j0 : List Byte := [0x75, 0xeb]
theorem j0_0 : ∀ feat, Dec feat j0 0 (FV7z.mk (.jcc 5) 64 [.rel 18446744073709551595] 2) := by dec_rfl

/-- The stretch at `1100`. -/
def p3 : List Byte := [
  0x89, 0x04, 0x96, 0x48, 0x83, 0xc2, 0x01, 0x48, 0x81, 0xfa, 0x00, 0x01, 0x00, 0x00]

theorem p3_0 : ∀ feat, Dec feat p3 0 (FV7z.mk .mov 32 [.mem (mg (some 6) (some 2) 4 0 32), gr 32 0] 3) := by dec_rfl
theorem p3_3 : ∀ feat, Dec feat p3 3 (FV7z.mk .add 64 [gr 64 2, Src.opd 64 (.i 1)] 4) := by dec_rfl
theorem p3_7 : ∀ feat, Dec feat p3 7 (FV7z.mk .cmp 64 [gr 64 2, Src.opd 64 (.i 256)] 7) := by dec_rfl

/-- What the stretch does. -/
def o3 : List Op := [
  Op.st 32 (some 6) (some 2) 4 0 0,
  Op.add 64 2 (.i 1),
  Op.cmp 64 2 (.i 256)]

theorem b3 (prof : Profile) : Blk prof p3 0 14 o3 :=
  .cons (p3_0 _) (OpI.st (.inr (.inr (.inl rfl)))) (by decide) <|
  .cons (p3_3 _) (OpI.add (.i 1) (.inr rfl)) (by decide) <|
  .cons (p3_7 _) (OpI.cmp (.i 256) (.inr rfl)) (by decide) <|
  .nil 14

def j1 : List Byte := [0x75, 0xd4]
theorem j1_0 : ∀ feat, Dec feat j1 0 (FV7z.mk (.jcc 5) 64 [.rel 18446744073709551572] 2) := by dec_rfl

/-- The stretch at `1116`. -/
def p4 : List Byte := [
  0x48, 0x8d, 0x3d, 0xdd, 0x06, 0x36, 0x00]

theorem p4_0 : ∀ feat, Dec feat p4 0 (FV7z.mk .lea 64 [gr 64 7, .mem (mrip 3540701 0)] 7) := by dec_rfl

/-- What the stretch does. -/
def o4 : List Op := [
  Op.mov 64 7 (.i 7851136)]

theorem b4 (prof : Profile) : BlkA prof p4 (0x41c59c : Addr) 0 7 o4 :=
  .cons (p4_0 _) (OpIA.lea_rip (by decide)) (by decide) <|
  .nil 7

end FV7z.C55
