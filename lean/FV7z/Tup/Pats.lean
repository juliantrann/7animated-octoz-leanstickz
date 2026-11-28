import FV7z.Lemmas.SpFs
import FV7z.Lemmas.BlkOps2
/-!
# The stretches of straight-line code of `towupper` (PLAN.md §M, M1)

Each distinct stretch between labels and jumps (`p*`, 4 of them) and each distinct jump (`j*`, 3) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.Tup
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The stretch at `0`. -/
def p0 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0x48, 0xc7, 0xc2, 0x90, 0xff, 0xff, 0xff, 0x89, 0xfe, 0x89, 0xf8, 0x64,
  0x48, 0x8b, 0x12, 0x48, 0x8b, 0x12, 0x0f, 0xb7, 0x8a, 0xd0, 0x00, 0x00, 0x00, 0x48, 0x8b, 0x54,
  0xca, 0x40, 0x8b, 0x0a, 0xd3, 0xee, 0x89, 0xf1, 0x3b, 0x72, 0x04]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem p0_4 : ∀ feat, Dec feat p0 4 (FV7z.mk .mov 64 [gr 64 2, Src.opd 64 (.i 18446744073709551504)] 7) := by dec_rfl
theorem p0_11 : ∀ feat, Dec feat p0 11 (FV7z.mk .mov 32 [gr 32 6, Src.opd 32 (.r 7)] 2) := by dec_rfl
theorem p0_13 : ∀ feat, Dec feat p0 13 (FV7z.mk .mov 32 [gr 32 0, Src.opd 32 (.r 7)] 2) := by dec_rfl
theorem p0_15 : ∀ feat, Dec feat p0 15 (FV7z.mk .mov 64 [gr 64 2, .mem (mf (some 2) none 1 0 64)] 4) := by dec_rfl
theorem p0_19 : ∀ feat, Dec feat p0 19 (FV7z.mk .mov 64 [gr 64 2, .mem (mg (some 2) none 1 0 64)] 3) := by dec_rfl
theorem p0_22 : ∀ feat, Dec feat p0 22 (FV7z.mk .movzx 32 [gr 32 1, .mem (mg (some 2) none 1 208 16)] 7) := by dec_rfl
theorem p0_29 : ∀ feat, Dec feat p0 29 (FV7z.mk .mov 64 [gr 64 2, .mem (mg (some 2) (some 1) 8 64 64)] 5) := by dec_rfl
theorem p0_34 : ∀ feat, Dec feat p0 34 (FV7z.mk .mov 32 [gr 32 1, .mem (mg (some 2) none 1 0 32)] 2) := by dec_rfl
theorem p0_36 : ∀ feat, Dec feat p0 36 (FV7z.mk .shr 32 [gr 32 6, Src.opd 8 (.r 1)] 2) := by dec_rfl
theorem p0_38 : ∀ feat, Dec feat p0 38 (FV7z.mk .mov 32 [gr 32 1, Src.opd 32 (.r 6)] 2) := by dec_rfl
theorem p0_40 : ∀ feat, Dec feat p0 40 (FV7z.mk .cmp 32 [gr 32 6, .mem (mg (some 2) none 1 4 32)] 3) := by dec_rfl

/-- What the stretch does. -/
def o0 (fb : Addr) : List Op := [
  Op.nop,
  Op.mov 64 2 (.i 18446744073709551504),
  Op.mov 32 6 (.r 7),
  Op.mov 32 0 (.r 7),
  Op.ldf fb 64 2 (some 2) none 1 0,
  Op.ld 64 2 (some 2) none 1 0,
  Op.ldzx 16 1 (some 2) none 1 208,
  Op.ld 64 2 (some 2) (some 1) 8 64,
  Op.ld 32 1 (some 2) none 1 0,
  Op.shr 6 (.r 1),
  Op.mov 32 1 (.r 6),
  Op.cmpm 32 6 (some 2) none 1 4]

theorem b0 (prof : Profile) (fb : Addr) : BlkF prof p0 (0x669660 : Addr) fb 0 43 (o0 fb) :=
  .cons (p0_0 _) (((OpI.endbr).at _).fs _) (by decide) <|
  .cons (p0_4 _) (((OpI.mov (.i 18446744073709551504) (.inr rfl)).at _).fs _) (by decide) <|
  .cons (p0_11 _) (((OpI.mov (.r 7) (.inl rfl)).at _).fs _) (by decide) <|
  .cons (p0_13 _) (((OpI.mov (.r 7) (.inl rfl)).at _).fs _) (by decide) <|
  .cons (p0_15 _) (OpIF.ldf (.inr rfl)) (by decide) <|
  .cons (p0_19 _) (((OpI.ld (.inr rfl)).at _).fs _) (by decide) <|
  .cons (p0_22 _) (((OpI.ldzx (.inr rfl)).at _).fs _) (by decide) <|
  .cons (p0_29 _) (((OpI.ld (.inr rfl)).at _).fs _) (by decide) <|
  .cons (p0_34 _) (((OpI.ld (.inl rfl)).at _).fs _) (by decide) <|
  .cons (p0_36 _) (((OpI.shr (.r 1)).at _).fs _) (by decide) <|
  .cons (p0_38 _) (((OpI.mov (.r 6) (.inl rfl)).at _).fs _) (by decide) <|
  .cons (p0_40 _) (((OpI.cmpm (.inl rfl)).at _).fs _) (by decide) <|
  .nil 43

def j0 : List Byte := [0x73, 0x1f]
theorem j0_0 : ∀ feat, Dec feat j0 0 (FV7z.mk (.jcc 3) 64 [.rel 31] 2) := by dec_rfl

/-- The stretch at `45`. -/
def p1 : List Byte := [
  0x83, 0xc1, 0x05, 0x8b, 0x34, 0x8a, 0x85, 0xf6]

theorem p1_0 : ∀ feat, Dec feat p1 0 (FV7z.mk .add 32 [gr 32 1, Src.opd 32 (.i 5)] 3) := by dec_rfl
theorem p1_3 : ∀ feat, Dec feat p1 3 (FV7z.mk .mov 32 [gr 32 6, .mem (mg (some 2) (some 1) 4 0 32)] 3) := by dec_rfl
theorem p1_6 : ∀ feat, Dec feat p1 6 (FV7z.mk .test 32 [gr 32 6, Src.opd 32 (.r 6)] 2) := by dec_rfl

/-- What the stretch does. -/
def o1 : List Op := [
  Op.add 32 1 (.i 5),
  Op.ld 32 6 (some 2) (some 1) 4 0,
  Op.test 32 6 (.r 6)]

theorem b1 (prof : Profile) : Blk prof p1 0 8 o1 :=
  .cons (p1_0 _) (OpI.add (.i 5) (.inl rfl)) (by decide) <|
  .cons (p1_3 _) (OpI.ld (.inl rfl)) (by decide) <|
  .cons (p1_6 _) (OpI.test (.r 6) (.inl rfl)) (by decide) <|
  .nil 8

def j1 : List Byte := [0x74, 0x15]
theorem j1_0 : ∀ feat, Dec feat j1 0 (FV7z.mk (.jcc 4) 64 [.rel 21] 2) := by dec_rfl

/-- The stretch at `55`. -/
def p2 : List Byte := [
  0x8b, 0x4a, 0x08, 0xd3, 0xef, 0x89, 0xf9, 0x23, 0x4a, 0x0c, 0x48, 0x8d, 0x0c, 0x8a, 0x8b, 0x0c,
  0x31, 0x85, 0xc9]

theorem p2_0 : ∀ feat, Dec feat p2 0 (FV7z.mk .mov 32 [gr 32 1, .mem (mg (some 2) none 1 8 32)] 3) := by dec_rfl
theorem p2_3 : ∀ feat, Dec feat p2 3 (FV7z.mk .shr 32 [gr 32 7, Src.opd 8 (.r 1)] 2) := by dec_rfl
theorem p2_5 : ∀ feat, Dec feat p2 5 (FV7z.mk .mov 32 [gr 32 1, Src.opd 32 (.r 7)] 2) := by dec_rfl
theorem p2_7 : ∀ feat, Dec feat p2 7 (FV7z.mk .and 32 [gr 32 1, .mem (mg (some 2) none 1 12 32)] 3) := by dec_rfl
theorem p2_10 : ∀ feat, Dec feat p2 10 (FV7z.mk .lea 64 [gr 64 1, .mem (mg (some 2) (some 1) 4 0 0)] 4) := by dec_rfl
theorem p2_14 : ∀ feat, Dec feat p2 14 (FV7z.mk .mov 32 [gr 32 1, .mem (mg (some 1) (some 6) 1 0 32)] 3) := by dec_rfl
theorem p2_17 : ∀ feat, Dec feat p2 17 (FV7z.mk .test 32 [gr 32 1, Src.opd 32 (.r 1)] 2) := by dec_rfl

/-- What the stretch does. -/
def o2 : List Op := [
  Op.ld 32 1 (some 2) none 1 8,
  Op.shr 7 (.r 1),
  Op.mov 32 1 (.r 7),
  Op.andm 32 1 (some 2) none 1 12,
  Op.lea 64 1 (some 2) (some 1) 4 0,
  Op.ld 32 1 (some 1) (some 6) 1 0,
  Op.test 32 1 (.r 1)]

theorem b2 (prof : Profile) : Blk prof p2 0 19 o2 :=
  .cons (p2_0 _) (OpI.ld (.inl rfl)) (by decide) <|
  .cons (p2_3 _) (OpI.shr (.r 1)) (by decide) <|
  .cons (p2_5 _) (OpI.mov (.r 7) (.inl rfl)) (by decide) <|
  .cons (p2_7 _) (OpI.andm (.inl rfl)) (by decide) <|
  .cons (p2_10 _) (OpI.lea (.inr rfl)) (by decide) <|
  .cons (p2_14 _) (OpI.ld (.inl rfl)) (by decide) <|
  .cons (p2_17 _) (OpI.test (.r 1) (.inl rfl)) (by decide) <|
  .nil 19

def j2 : List Byte := [0x75, 0x04]
theorem j2_0 : ∀ feat, Dec feat j2 0 (FV7z.mk (.jcc 5) 64 [.rel 4] 2) := by dec_rfl

/-- The stretch at `80`. -/
def p3 : List Byte := [
  0x89, 0xc6, 0x23, 0x72, 0x10, 0x48, 0x8d, 0x14, 0xb2, 0x03, 0x04, 0x0a]

theorem p3_0 : ∀ feat, Dec feat p3 0 (FV7z.mk .mov 32 [gr 32 6, Src.opd 32 (.r 0)] 2) := by dec_rfl
theorem p3_2 : ∀ feat, Dec feat p3 2 (FV7z.mk .and 32 [gr 32 6, .mem (mg (some 2) none 1 16 32)] 3) := by dec_rfl
theorem p3_5 : ∀ feat, Dec feat p3 5 (FV7z.mk .lea 64 [gr 64 2, .mem (mg (some 2) (some 6) 4 0 0)] 4) := by dec_rfl
theorem p3_9 : ∀ feat, Dec feat p3 9 (FV7z.mk .add 32 [gr 32 0, .mem (mg (some 2) (some 1) 1 0 32)] 3) := by dec_rfl

/-- What the stretch does. -/
def o3 : List Op := [
  Op.mov 32 6 (.r 0),
  Op.andm 32 6 (some 2) none 1 16,
  Op.lea 64 2 (some 2) (some 6) 4 0,
  Op.addm 32 0 (some 2) (some 1) 1 0]

theorem b3 (prof : Profile) : Blk prof p3 0 12 o3 :=
  .cons (p3_0 _) (OpI.mov (.r 0) (.inl rfl)) (by decide) <|
  .cons (p3_2 _) (OpI.andm (.inl rfl)) (by decide) <|
  .cons (p3_5 _) (OpI.lea (.inr rfl)) (by decide) <|
  .cons (p3_9 _) (OpI.addm (.inl rfl)) (by decide) <|
  .nil 12

end FV7z.Tup
