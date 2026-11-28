import FV7z.Lemmas.Sp
import FV7z.Lemmas.BlkOps3
/-!
# The stretches of straight-line code of `NWindows::NFile::NName::NormalizeDirPathPrefix` (PLAN.md §M, M1)

Each distinct stretch between labels and jumps (`p*`, 6 of them) and each distinct jump (`j*`, 4) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.Ndp
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

def j0 : List Byte := [0x74, 0x14]
theorem j0_0 : ∀ feat, Dec feat j0 0 (FV7z.mk (.jcc 4) 64 [.rel 20] 2) := by dec_rfl

/-- The stretch at `11`. -/
def p1 : List Byte := [
  0x48, 0x8b, 0x17, 0x89, 0xc1, 0x48, 0x8d, 0x34, 0x8d, 0x00, 0x00, 0x00, 0x00, 0x83, 0x7c, 0x8a,
  0xfc, 0x2f]

theorem p1_0 : ∀ feat, Dec feat p1 0 (FV7z.mk .mov 64 [gr 64 2, .mem (mg (some 7) none 1 0 64)] 3) := by dec_rfl
theorem p1_3 : ∀ feat, Dec feat p1 3 (FV7z.mk .mov 32 [gr 32 1, Src.opd 32 (.r 0)] 2) := by dec_rfl
theorem p1_5 : ∀ feat, Dec feat p1 5 (FV7z.mk .lea 64 [gr 64 6, .mem (mg none (some 1) 4 0 0)] 8) := by dec_rfl
theorem p1_13 : ∀ feat, Dec feat p1 13 (FV7z.mk .cmp 32 [.mem (mg (some 2) (some 1) 4 18446744073709551612 32), .imm 32 47] 5) := by dec_rfl

/-- What the stretch does. -/
def o1 : List Op := [
  Op.ld 64 2 (some 7) none 1 0,
  Op.mov 32 1 (.r 0),
  Op.lea 64 6 none (some 1) 4 0,
  Op.cmpmi 32 (some 2) (some 1) 4 18446744073709551612 47]

theorem b1 (prof : Profile) : Blk prof p1 0 18 o1 :=
  .cons (p1_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p1_3 _) (OpI.mov (.r 0) (.inl rfl)) (by decide) <|
  .cons (p1_5 _) (OpI.lea (.inr rfl)) (by decide) <|
  .cons (p1_13 _) (OpI.cmpmi (.inr rfl)) (by decide) <|
  .nil 18

def j1 : List Byte := [0x75, 0x01]
theorem j1_0 : ∀ feat, Dec feat j1 0 (FV7z.mk (.jcc 5) 64 [.rel 1] 2) := by dec_rfl

/-- The stretch at `32`. -/
def p2 : List Byte := [
  0x48, 0x83, 0xec, 0x18, 0x3b, 0x47, 0x0c]

theorem p2_0 : ∀ feat, Dec feat p2 0 (FV7z.mk .sub 64 [gr 64 4, Src.opd 64 (.i 24)] 4) := by dec_rfl
theorem p2_4 : ∀ feat, Dec feat p2 4 (FV7z.mk .cmp 32 [gr 32 0, .mem (mg (some 7) none 1 12 32)] 3) := by dec_rfl

/-- What the stretch does. -/
def o2 : List Op := [
  Op.sub 64 4 (.i 24),
  Op.cmpm 32 0 (some 7) none 1 12]

theorem b2 (prof : Profile) : Blk prof p2 0 7 o2 :=
  .cons (p2_0 _) (OpI.sub (.i 24) (.inr rfl)) (by decide) <|
  .cons (p2_4 _) (OpI.cmpm (.inl rfl)) (by decide) <|
  .nil 7

def j2 : List Byte := [0x74, 0x1f]
theorem j2_0 : ∀ feat, Dec feat j2 0 (FV7z.mk (.jcc 4) 64 [.rel 31] 2) := by dec_rfl

/-- The stretch at `41`. -/
def p3 : List Byte := [
  0x8d, 0x48, 0x01, 0xc7, 0x04, 0x32, 0x2f, 0x00, 0x00, 0x00, 0xc7, 0x04, 0x8a, 0x00, 0x00, 0x00,
  0x00, 0x89, 0x4f, 0x08, 0x48, 0x83, 0xc4, 0x18]

theorem p3_0 : ∀ feat, Dec feat p3 0 (FV7z.mk .lea 32 [gr 32 1, .mem (mg (some 0) none 1 1 0)] 3) := by dec_rfl
theorem p3_3 : ∀ feat, Dec feat p3 3 (FV7z.mk .mov 32 [.mem (mg (some 2) (some 6) 1 0 32), .imm 32 47] 7) := by dec_rfl
theorem p3_10 : ∀ feat, Dec feat p3 10 (FV7z.mk .mov 32 [.mem (mg (some 2) (some 1) 4 0 32), .imm 32 0] 7) := by dec_rfl
theorem p3_17 : ∀ feat, Dec feat p3 17 (FV7z.mk .mov 32 [.mem (mg (some 7) none 1 8 32), gr 32 1] 3) := by dec_rfl
theorem p3_20 : ∀ feat, Dec feat p3 20 (FV7z.mk .add 64 [gr 64 4, Src.opd 64 (.i 24)] 4) := by dec_rfl

/-- What the stretch does. -/
def o3 : List Op := [
  Op.lea 32 1 (some 0) none 1 1,
  Op.sti 32 (some 2) (some 6) 1 0 47,
  Op.sti 32 (some 2) (some 1) 4 0 0,
  Op.st 32 (some 7) none 1 8 1,
  Op.add 64 4 (.i 24)]

theorem b3 (prof : Profile) : Blk prof p3 0 24 o3 :=
  .cons (p3_0 _) (OpI.lea (.inl rfl)) (by decide) <|
  .cons (p3_3 _) (OpI.sti (.inr (.inr (.inl rfl)))) (by decide) <|
  .cons (p3_10 _) (OpI.sti (.inr (.inr (.inl rfl)))) (by decide) <|
  .cons (p3_17 _) (OpI.st (.inr (.inr (.inl rfl)))) (by decide) <|
  .cons (p3_20 _) (OpI.add (.i 24) (.inr rfl)) (by decide) <|
  .nil 24

/-- The stretch at `72`. -/
def p4 : List Byte := [
  0x48, 0x89, 0x7c, 0x24, 0x08]

theorem p4_0 : ∀ feat, Dec feat p4 0 (FV7z.mk .mov 64 [.mem (mg (some 4) none 1 8 64), gr 64 7] 5) := by dec_rfl

/-- What the stretch does. -/
def o4 : List Op := [
  Op.st 64 (some 4) none 1 8 7]

theorem b4 (prof : Profile) : Blk prof p4 0 5 o4 :=
  .cons (p4_0 _) (OpI.st (.inr (.inr (.inr rfl)))) (by decide) <|
  .nil 5

/-- The stretch at `82`. -/
def p5 : List Byte := [
  0x48, 0x8b, 0x7c, 0x24, 0x08, 0x8b, 0x77, 0x08, 0x48, 0x8b, 0x17, 0x48, 0x89, 0xf0, 0x48, 0xc1,
  0xe6, 0x02]

theorem p5_0 : ∀ feat, Dec feat p5 0 (FV7z.mk .mov 64 [gr 64 7, .mem (mg (some 4) none 1 8 64)] 5) := by dec_rfl
theorem p5_5 : ∀ feat, Dec feat p5 5 (FV7z.mk .mov 32 [gr 32 6, .mem (mg (some 7) none 1 8 32)] 3) := by dec_rfl
theorem p5_8 : ∀ feat, Dec feat p5 8 (FV7z.mk .mov 64 [gr 64 2, .mem (mg (some 7) none 1 0 64)] 3) := by dec_rfl
theorem p5_11 : ∀ feat, Dec feat p5 11 (FV7z.mk .mov 64 [gr 64 0, Src.opd 64 (.r 6)] 3) := by dec_rfl
theorem p5_14 : ∀ feat, Dec feat p5 14 (FV7z.mk .shl 64 [gr 64 6, Src.opd 8 (.i 2)] 4) := by dec_rfl

/-- What the stretch does. -/
def o5 : List Op := [
  Op.ld 64 7 (some 4) none 1 8,
  Op.ld 32 6 (some 7) none 1 8,
  Op.ld 64 2 (some 7) none 1 0,
  Op.mov 64 0 (.r 6),
  Op.shl64 6 (.i 2)]

theorem b5 (prof : Profile) : Blk prof p5 0 18 o5 :=
  .cons (p5_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p5_5 _) (OpI.ld (.inl rfl)) (by decide) <|
  .cons (p5_8 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p5_11 _) (OpI.mov (.r 6) (.inr rfl)) (by decide) <|
  .cons (p5_14 _) (OpI.shl64 (.i 2)) (by decide) <|
  .nil 18

def j3 : List Byte := [0xeb, 0xc3]
theorem j3_0 : ∀ feat, Dec feat j3 0 (FV7z.mk .jmp 64 [.rel 18446744073709551555] 2) := by dec_rfl

end FV7z.Ndp
