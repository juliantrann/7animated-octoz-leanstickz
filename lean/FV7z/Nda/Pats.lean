import FV7z.Lemmas.Sp
import FV7z.Lemmas.BlkOps2
/-!
# The stretches of straight-line code of `NWindows::NFile::NName::NormalizeDirPathPrefix(AString&)` (PLAN.md §M, M1)

Each distinct stretch between labels and jumps (`p*`, 7 of them) and each distinct jump (`j*`, 3) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.Nda
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The stretch at `0`. -/
def p0 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0x8b, 0x47, 0x08, 0x85, 0xc0]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem p0_4 : ∀ feat, Dec feat p0 4 (FV7z.mk .mov 32 [gr 32 0, .mem (mg (some 7) none 1 8 32)] 3) := by dec_rfl
theorem p0_7 : ∀ feat, Dec feat p0 7 (FV7z.mk .test 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl

/-- What the stretch does. -/
def o0 : List Op := [
  Op.nop,
  Op.ld 32 0 (some 7) none 1 8,
  Op.test 32 0 (.r 0)]

theorem b0 (prof : Profile) : Blk prof p0 0 9 o0 :=
  .cons (p0_0 _) (OpI.endbr) (by decide) <|
  .cons (p0_4 _) (OpI.ld (.inl rfl)) (by decide) <|
  .cons (p0_7 _) (OpI.test (.r 0) (.inl rfl)) (by decide) <|
  .nil 9

def j0 : List Byte := [0x74, 0x0c]
theorem j0_0 : ∀ feat, Dec feat j0 0 (FV7z.mk (.jcc 4) 64 [.rel 12] 2) := by dec_rfl

/-- The stretch at `11`. -/
def p1 : List Byte := [
  0x48, 0x8b, 0x17, 0x89, 0xc1, 0x80, 0x7c, 0x0a, 0xff, 0x2f]

theorem p1_0 : ∀ feat, Dec feat p1 0 (FV7z.mk .mov 64 [gr 64 2, .mem (mg (some 7) none 1 0 64)] 3) := by dec_rfl
theorem p1_3 : ∀ feat, Dec feat p1 3 (FV7z.mk .mov 32 [gr 32 1, Src.opd 32 (.r 0)] 2) := by dec_rfl
theorem p1_5 : ∀ feat, Dec feat p1 5 (FV7z.mk .cmp 8 [.mem (mg (some 2) (some 1) 1 18446744073709551615 8), .imm 8 47] 5) := by dec_rfl

/-- What the stretch does. -/
def o1 : List Op := [
  Op.ld 64 2 (some 7) none 1 0,
  Op.mov 32 1 (.r 0),
  Op.cmpmi 8 (some 2) (some 1) 1 18446744073709551615 47]

theorem b1 (prof : Profile) : Blk prof p1 0 10 o1 :=
  .cons (p1_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p1_3 _) (OpI.mov (.r 0) (.inl rfl)) (by decide) <|
  .cons (p1_5 _) (OpI.cmpmi (.inl rfl)) (by decide) <|
  .nil 10

def j1 : List Byte := [0x75, 0x09]
theorem j1_0 : ∀ feat, Dec feat j1 0 (FV7z.mk (.jcc 5) 64 [.rel 9] 2) := by dec_rfl

/-- The stretch at `32`. -/
def p2 : List Byte := [
  0x3b, 0x47, 0x0c]

theorem p2_0 : ∀ feat, Dec feat p2 0 (FV7z.mk .cmp 32 [gr 32 0, .mem (mg (some 7) none 1 12 32)] 3) := by dec_rfl

/-- What the stretch does. -/
def o2 : List Op := [
  Op.cmpm 32 0 (some 7) none 1 12]

theorem b2 (prof : Profile) : Blk prof p2 0 3 o2 :=
  .cons (p2_0 _) (OpI.cmpm (.inl rfl)) (by decide) <|
  .nil 3

def j2 : List Byte := [0x74, 0x1b]
theorem j2_0 : ∀ feat, Dec feat j2 0 (FV7z.mk (.jcc 4) 64 [.rel 27] 2) := by dec_rfl

/-- The stretch at `37`. -/
def p3 : List Byte := [
  0x83, 0xc0, 0x01, 0xc6, 0x04, 0x0a, 0x2f, 0x89, 0xc1, 0xc6, 0x04, 0x0a, 0x00, 0x89, 0x47, 0x08]

theorem p3_0 : ∀ feat, Dec feat p3 0 (FV7z.mk .add 32 [gr 32 0, Src.opd 32 (.i 1)] 3) := by dec_rfl
theorem p3_3 : ∀ feat, Dec feat p3 3 (FV7z.mk .mov 8 [.mem (mg (some 2) (some 1) 1 0 8), .imm 8 47] 4) := by dec_rfl
theorem p3_7 : ∀ feat, Dec feat p3 7 (FV7z.mk .mov 32 [gr 32 1, Src.opd 32 (.r 0)] 2) := by dec_rfl
theorem p3_9 : ∀ feat, Dec feat p3 9 (FV7z.mk .mov 8 [.mem (mg (some 2) (some 1) 1 0 8), .imm 8 0] 4) := by dec_rfl
theorem p3_13 : ∀ feat, Dec feat p3 13 (FV7z.mk .mov 32 [.mem (mg (some 7) none 1 8 32), gr 32 0] 3) := by dec_rfl

/-- What the stretch does. -/
def o3 : List Op := [
  Op.add 32 0 (.i 1),
  Op.sti 8 (some 2) (some 1) 1 0 47,
  Op.mov 32 1 (.r 0),
  Op.sti 8 (some 2) (some 1) 1 0 0,
  Op.st 32 (some 7) none 1 8 0]

theorem b3 (prof : Profile) : Blk prof p3 0 16 o3 :=
  .cons (p3_0 _) (OpI.add (.i 1) (.inl rfl)) (by decide) <|
  .cons (p3_3 _) (OpI.sti (.inl rfl)) (by decide) <|
  .cons (p3_7 _) (OpI.mov (.r 0) (.inl rfl)) (by decide) <|
  .cons (p3_9 _) (OpI.sti (.inl rfl)) (by decide) <|
  .cons (p3_13 _) (OpI.st (.inr (.inr (.inl rfl)))) (by decide) <|
  .nil 16

/-- The stretch at `64`. -/
def p4 : List Byte := [
  0x48, 0x83, 0xec, 0x18, 0x48, 0x89, 0x7c, 0x24, 0x08]

theorem p4_0 : ∀ feat, Dec feat p4 0 (FV7z.mk .sub 64 [gr 64 4, Src.opd 64 (.i 24)] 4) := by dec_rfl
theorem p4_4 : ∀ feat, Dec feat p4 4 (FV7z.mk .mov 64 [.mem (mg (some 4) none 1 8 64), gr 64 7] 5) := by dec_rfl

/-- What the stretch does. -/
def o4 : List Op := [
  Op.sub 64 4 (.i 24),
  Op.st 64 (some 4) none 1 8 7]

theorem b4 (prof : Profile) : Blk prof p4 0 9 o4 :=
  .cons (p4_0 _) (OpI.sub (.i 24) (.inr rfl)) (by decide) <|
  .cons (p4_4 _) (OpI.st (.inr (.inr (.inr rfl)))) (by decide) <|
  .nil 9

/-- The stretch at `78`. -/
def p5 : List Byte := [
  0x48, 0x8b, 0x7c, 0x24, 0x08, 0x8b, 0x4f, 0x08, 0x48, 0x8b, 0x17, 0x48, 0x89, 0xc8]

theorem p5_0 : ∀ feat, Dec feat p5 0 (FV7z.mk .mov 64 [gr 64 7, .mem (mg (some 4) none 1 8 64)] 5) := by dec_rfl
theorem p5_5 : ∀ feat, Dec feat p5 5 (FV7z.mk .mov 32 [gr 32 1, .mem (mg (some 7) none 1 8 32)] 3) := by dec_rfl
theorem p5_8 : ∀ feat, Dec feat p5 8 (FV7z.mk .mov 64 [gr 64 2, .mem (mg (some 7) none 1 0 64)] 3) := by dec_rfl
theorem p5_11 : ∀ feat, Dec feat p5 11 (FV7z.mk .mov 64 [gr 64 0, Src.opd 64 (.r 1)] 3) := by dec_rfl

/-- What the stretch does. -/
def o5 : List Op := [
  Op.ld 64 7 (some 4) none 1 8,
  Op.ld 32 1 (some 7) none 1 8,
  Op.ld 64 2 (some 7) none 1 0,
  Op.mov 64 0 (.r 1)]

theorem b5 (prof : Profile) : Blk prof p5 0 14 o5 :=
  .cons (p5_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p5_5 _) (OpI.ld (.inl rfl)) (by decide) <|
  .cons (p5_8 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p5_11 _) (OpI.mov (.r 1) (.inr rfl)) (by decide) <|
  .nil 14

/-- The stretch at `92`. -/
def p6 : List Byte := [
  0xc6, 0x04, 0x0a, 0x2f, 0x83, 0xc0, 0x01, 0x89, 0xc1, 0xc6, 0x04, 0x0a, 0x00, 0x89, 0x47, 0x08,
  0x48, 0x83, 0xc4, 0x18]

theorem p6_0 : ∀ feat, Dec feat p6 0 (FV7z.mk .mov 8 [.mem (mg (some 2) (some 1) 1 0 8), .imm 8 47] 4) := by dec_rfl
theorem p6_4 : ∀ feat, Dec feat p6 4 (FV7z.mk .add 32 [gr 32 0, Src.opd 32 (.i 1)] 3) := by dec_rfl
theorem p6_7 : ∀ feat, Dec feat p6 7 (FV7z.mk .mov 32 [gr 32 1, Src.opd 32 (.r 0)] 2) := by dec_rfl
theorem p6_9 : ∀ feat, Dec feat p6 9 (FV7z.mk .mov 8 [.mem (mg (some 2) (some 1) 1 0 8), .imm 8 0] 4) := by dec_rfl
theorem p6_13 : ∀ feat, Dec feat p6 13 (FV7z.mk .mov 32 [.mem (mg (some 7) none 1 8 32), gr 32 0] 3) := by dec_rfl
theorem p6_16 : ∀ feat, Dec feat p6 16 (FV7z.mk .add 64 [gr 64 4, Src.opd 64 (.i 24)] 4) := by dec_rfl

/-- What the stretch does. -/
def o6 : List Op := [
  Op.sti 8 (some 2) (some 1) 1 0 47,
  Op.add 32 0 (.i 1),
  Op.mov 32 1 (.r 0),
  Op.sti 8 (some 2) (some 1) 1 0 0,
  Op.st 32 (some 7) none 1 8 0,
  Op.add 64 4 (.i 24)]

theorem b6 (prof : Profile) : Blk prof p6 0 20 o6 :=
  .cons (p6_0 _) (OpI.sti (.inl rfl)) (by decide) <|
  .cons (p6_4 _) (OpI.add (.i 1) (.inl rfl)) (by decide) <|
  .cons (p6_7 _) (OpI.mov (.r 0) (.inl rfl)) (by decide) <|
  .cons (p6_9 _) (OpI.sti (.inl rfl)) (by decide) <|
  .cons (p6_13 _) (OpI.st (.inr (.inr (.inl rfl)))) (by decide) <|
  .cons (p6_16 _) (OpI.add (.i 24) (.inr rfl)) (by decide) <|
  .nil 20

end FV7z.Nda
