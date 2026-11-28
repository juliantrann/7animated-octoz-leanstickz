import FV7z.Lemmas.Sp
import FV7z.Lemmas.BlkOps2
/-!
# The stretches of straight-line code of `_dl_setup_hash` (PLAN.md G3, startup)

Each distinct stretch between labels and jumps (`p*`, 5 of them) and each distinct jump (`j*`, 3) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.Dsh
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The stretch at `0`. -/
def p0 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0x48, 0x8b, 0x87, 0xa0, 0x02, 0x00, 0x00, 0x48, 0x85, 0xc0]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem p0_4 : ∀ feat, Dec feat p0 4 (FV7z.mk .mov 64 [gr 64 0, .mem (mg (some 7) none 1 672 64)] 7) := by dec_rfl
theorem p0_11 : ∀ feat, Dec feat p0 11 (FV7z.mk .test 64 [gr 64 0, Src.opd 64 (.r 0)] 3) := by dec_rfl

/-- What the stretch does. -/
def o0 : List Op := [
  Op.nop,
  Op.ld 64 0 (some 7) none 1 672,
  Op.test 64 0 (.r 0)]

theorem b0 (prof : Profile) : Blk prof p0 0 14 o0 :=
  .cons (p0_0 _) (OpI.endbr) (by decide) <|
  .cons (p0_4 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p0_11 _) (OpI.test (.r 0) (.inr rfl)) (by decide) <|
  .nil 14

def j0 : List Byte := [0x74, 0x58]
theorem j0_0 : ∀ feat, Dec feat j0 0 (FV7z.mk (.jcc 4) 64 [.rel 88] 2) := by dec_rfl

/-- The stretch at `16`. -/
def p1 : List Byte := [
  0x48, 0x8b, 0x48, 0x08, 0x8b, 0x11, 0x89, 0x97, 0xf4, 0x02, 0x00, 0x00, 0x8b, 0x41, 0x08, 0x8b,
  0x71, 0x04, 0x44, 0x8d, 0x40, 0xff, 0x41, 0x85, 0xc0]

theorem p1_0 : ∀ feat, Dec feat p1 0 (FV7z.mk .mov 64 [gr 64 1, .mem (mg (some 0) none 1 8 64)] 4) := by dec_rfl
theorem p1_4 : ∀ feat, Dec feat p1 4 (FV7z.mk .mov 32 [gr 32 2, .mem (mg (some 1) none 1 0 32)] 2) := by dec_rfl
theorem p1_6 : ∀ feat, Dec feat p1 6 (FV7z.mk .mov 32 [.mem (mg (some 7) none 1 756 32), gr 32 2] 6) := by dec_rfl
theorem p1_12 : ∀ feat, Dec feat p1 12 (FV7z.mk .mov 32 [gr 32 0, .mem (mg (some 1) none 1 8 32)] 3) := by dec_rfl
theorem p1_15 : ∀ feat, Dec feat p1 15 (FV7z.mk .mov 32 [gr 32 6, .mem (mg (some 1) none 1 4 32)] 3) := by dec_rfl
theorem p1_18 : ∀ feat,
    Dec feat p1 18 (FV7z.mk .lea 32 [gr 32 8, .mem (mg (some 0) none 1 18446744073709551615 0)] 4) := by dec_rfl
theorem p1_22 : ∀ feat, Dec feat p1 22 (FV7z.mk .test 32 [gr 32 8, Src.opd 32 (.r 0)] 3) := by dec_rfl

/-- What the stretch does. -/
def o1 : List Op := [
  Op.ld 64 1 (some 0) none 1 8,
  Op.ld 32 2 (some 1) none 1 0,
  Op.st 32 (some 7) none 1 756 2,
  Op.ld 32 0 (some 1) none 1 8,
  Op.ld 32 6 (some 1) none 1 4,
  Op.lea 32 8 (some 0) none 1 18446744073709551615,
  Op.test 32 8 (.r 0)]

theorem b1 (prof : Profile) : Blk prof p1 0 25 o1 :=
  .cons (p1_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p1_4 _) (OpI.ld (.inl rfl)) (by decide) <|
  .cons (p1_6 _) (OpI.st (.inr (.inr (.inl rfl)))) (by decide) <|
  .cons (p1_12 _) (OpI.ld (.inl rfl)) (by decide) <|
  .cons (p1_15 _) (OpI.ld (.inl rfl)) (by decide) <|
  .cons (p1_18 _) (OpI.lea (.inl rfl)) (by decide) <|
  .cons (p1_22 _) (OpI.test (.r 0) (.inl rfl)) (by decide) <|
  .nil 25

def j1 : List Byte := [0x75, 0x69]
theorem j1_0 : ∀ feat, Dec feat j1 0 (FV7z.mk (.jcc 5) 64 [.rel 105] 2) := by dec_rfl

/-- The stretch at `43`. -/
def p2 : List Byte := [
  0x44, 0x89, 0x87, 0xf8, 0x02, 0x00, 0x00, 0x01, 0xc0, 0x4c, 0x8d, 0x41, 0x10, 0x48, 0x29, 0xf2,
  0x8b, 0x49, 0x0c, 0x49, 0x8d, 0x04, 0x80, 0x4c, 0x89, 0x87, 0x00, 0x03, 0x00, 0x00, 0x48, 0x89,
  0x87, 0x08, 0x03, 0x00, 0x00, 0x48, 0x8d, 0x04, 0x90, 0x89, 0x8f, 0xfc, 0x02, 0x00, 0x00, 0x48,
  0x89, 0x87, 0x10, 0x03, 0x00, 0x00]

theorem p2_0 : ∀ feat, Dec feat p2 0 (FV7z.mk .mov 32 [.mem (mg (some 7) none 1 760 32), gr 32 8] 7) := by dec_rfl
theorem p2_7 : ∀ feat, Dec feat p2 7 (FV7z.mk .add 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl
theorem p2_9 : ∀ feat, Dec feat p2 9 (FV7z.mk .lea 64 [gr 64 8, .mem (mg (some 1) none 1 16 0)] 4) := by dec_rfl
theorem p2_13 : ∀ feat, Dec feat p2 13 (FV7z.mk .sub 64 [gr 64 2, Src.opd 64 (.r 6)] 3) := by dec_rfl
theorem p2_16 : ∀ feat, Dec feat p2 16 (FV7z.mk .mov 32 [gr 32 1, .mem (mg (some 1) none 1 12 32)] 3) := by dec_rfl
theorem p2_19 : ∀ feat, Dec feat p2 19 (FV7z.mk .lea 64 [gr 64 0, .mem (mg (some 8) (some 0) 4 0 0)] 4) := by dec_rfl
theorem p2_23 : ∀ feat, Dec feat p2 23 (FV7z.mk .mov 64 [.mem (mg (some 7) none 1 768 64), gr 64 8] 7) := by dec_rfl
theorem p2_30 : ∀ feat, Dec feat p2 30 (FV7z.mk .mov 64 [.mem (mg (some 7) none 1 776 64), gr 64 0] 7) := by dec_rfl
theorem p2_37 : ∀ feat, Dec feat p2 37 (FV7z.mk .lea 64 [gr 64 0, .mem (mg (some 0) (some 2) 4 0 0)] 4) := by dec_rfl
theorem p2_41 : ∀ feat, Dec feat p2 41 (FV7z.mk .mov 32 [.mem (mg (some 7) none 1 764 32), gr 32 1] 6) := by dec_rfl
theorem p2_47 : ∀ feat, Dec feat p2 47 (FV7z.mk .mov 64 [.mem (mg (some 7) none 1 784 64), gr 64 0] 7) := by dec_rfl

/-- What the stretch does. -/
def o2 : List Op := [
  Op.st 32 (some 7) none 1 760 8,
  Op.add 32 0 (.r 0),
  Op.lea 64 8 (some 1) none 1 16,
  Op.sub 64 2 (.r 6),
  Op.ld 32 1 (some 1) none 1 12,
  Op.lea 64 0 (some 8) (some 0) 4 0,
  Op.st 64 (some 7) none 1 768 8,
  Op.st 64 (some 7) none 1 776 0,
  Op.lea 64 0 (some 0) (some 2) 4 0,
  Op.st 32 (some 7) none 1 764 1,
  Op.st 64 (some 7) none 1 784 0]

theorem b2 (prof : Profile) : Blk prof p2 0 54 o2 :=
  .cons (p2_0 _) (OpI.st (.inr (.inr (.inl rfl)))) (by decide) <|
  .cons (p2_7 _) (OpI.add (.r 0) (.inl rfl)) (by decide) <|
  .cons (p2_9 _) (OpI.lea (.inr rfl)) (by decide) <|
  .cons (p2_13 _) (OpI.sub (.r 6) (.inr rfl)) (by decide) <|
  .cons (p2_16 _) (OpI.ld (.inl rfl)) (by decide) <|
  .cons (p2_19 _) (OpI.lea (.inr rfl)) (by decide) <|
  .cons (p2_23 _) (OpI.st (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p2_30 _) (OpI.st (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p2_37 _) (OpI.lea (.inr rfl)) (by decide) <|
  .cons (p2_41 _) (OpI.st (.inr (.inr (.inl rfl)))) (by decide) <|
  .cons (p2_47 _) (OpI.st (.inr (.inr (.inr rfl)))) (by decide) <|
  .nil 54

/-- The stretch at `104`. -/
def p3 : List Byte := [
  0x48, 0x8b, 0x47, 0x60, 0x48, 0x85, 0xc0]

theorem p3_0 : ∀ feat, Dec feat p3 0 (FV7z.mk .mov 64 [gr 64 0, .mem (mg (some 7) none 1 96 64)] 4) := by dec_rfl
theorem p3_4 : ∀ feat, Dec feat p3 4 (FV7z.mk .test 64 [gr 64 0, Src.opd 64 (.r 0)] 3) := by dec_rfl

/-- What the stretch does. -/
def o3 : List Op := [
  Op.ld 64 0 (some 7) none 1 96,
  Op.test 64 0 (.r 0)]

theorem b3 (prof : Profile) : Blk prof p3 0 7 o3 :=
  .cons (p3_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p3_4 _) (OpI.test (.r 0) (.inr rfl)) (by decide) <|
  .nil 7

def j2 : List Byte := [0x74, 0x22]
theorem j2_0 : ∀ feat, Dec feat j2 0 (FV7z.mk (.jcc 4) 64 [.rel 34] 2) := by dec_rfl

/-- The stretch at `113`. -/
def p4 : List Byte := [
  0x48, 0x8b, 0x40, 0x08, 0x8b, 0x10, 0x48, 0x83, 0xc0, 0x08, 0x48, 0x89, 0x87, 0x10, 0x03, 0x00,
  0x00, 0x48, 0x8d, 0x04, 0x90, 0x89, 0x97, 0xf4, 0x02, 0x00, 0x00, 0x48, 0x89, 0x87, 0x08, 0x03,
  0x00, 0x00]

theorem p4_0 : ∀ feat, Dec feat p4 0 (FV7z.mk .mov 64 [gr 64 0, .mem (mg (some 0) none 1 8 64)] 4) := by dec_rfl
theorem p4_4 : ∀ feat, Dec feat p4 4 (FV7z.mk .mov 32 [gr 32 2, .mem (mg (some 0) none 1 0 32)] 2) := by dec_rfl
theorem p4_6 : ∀ feat, Dec feat p4 6 (FV7z.mk .add 64 [gr 64 0, Src.opd 64 (.i 8)] 4) := by dec_rfl
theorem p4_10 : ∀ feat, Dec feat p4 10 (FV7z.mk .mov 64 [.mem (mg (some 7) none 1 784 64), gr 64 0] 7) := by dec_rfl
theorem p4_17 : ∀ feat, Dec feat p4 17 (FV7z.mk .lea 64 [gr 64 0, .mem (mg (some 0) (some 2) 4 0 0)] 4) := by dec_rfl
theorem p4_21 : ∀ feat, Dec feat p4 21 (FV7z.mk .mov 32 [.mem (mg (some 7) none 1 756 32), gr 32 2] 6) := by dec_rfl
theorem p4_27 : ∀ feat, Dec feat p4 27 (FV7z.mk .mov 64 [.mem (mg (some 7) none 1 776 64), gr 64 0] 7) := by dec_rfl

/-- What the stretch does. -/
def o4 : List Op := [
  Op.ld 64 0 (some 0) none 1 8,
  Op.ld 32 2 (some 0) none 1 0,
  Op.add 64 0 (.i 8),
  Op.st 64 (some 7) none 1 784 0,
  Op.lea 64 0 (some 0) (some 2) 4 0,
  Op.st 32 (some 7) none 1 756 2,
  Op.st 64 (some 7) none 1 776 0]

theorem b4 (prof : Profile) : Blk prof p4 0 34 o4 :=
  .cons (p4_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p4_4 _) (OpI.ld (.inl rfl)) (by decide) <|
  .cons (p4_6 _) (OpI.add (.i 8) (.inr rfl)) (by decide) <|
  .cons (p4_10 _) (OpI.st (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p4_17 _) (OpI.lea (.inr rfl)) (by decide) <|
  .cons (p4_21 _) (OpI.st (.inr (.inr (.inl rfl)))) (by decide) <|
  .cons (p4_27 _) (OpI.st (.inr (.inr (.inr rfl)))) (by decide) <|
  .nil 34

end FV7z.Dsh
