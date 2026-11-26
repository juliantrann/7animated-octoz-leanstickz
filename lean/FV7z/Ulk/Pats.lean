import FV7z.Lemmas.SpFs
import FV7z.Lemmas.BlkOps2
/-!
# The stretches of straight-line code of `unlink_chunk.isra.0` (PLAN.md §M, M1)

Each distinct stretch between labels and jumps (`p*`, 12 of them) and each distinct jump (`j*`, 11) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.Ulk
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The stretch at `0`. -/
def p0 : List Byte := [
  0x48, 0x83, 0xec, 0x08, 0x48, 0x8b, 0x4f, 0x08, 0x48, 0x89, 0xc8, 0x48, 0x83, 0xe0, 0xf8, 0x48,
  0x3b, 0x04, 0x07]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .sub 64 [gr 64 4, Src.opd 64 (.i 8)] 4) := by dec_rfl
theorem p0_4 : ∀ feat, Dec feat p0 4 (FV7z.mk .mov 64 [gr 64 1, .mem (mg (some 7) none 1 8 64)] 4) := by dec_rfl
theorem p0_8 : ∀ feat, Dec feat p0 8 (FV7z.mk .mov 64 [gr 64 0, Src.opd 64 (.r 1)] 3) := by dec_rfl
theorem p0_11 : ∀ feat, Dec feat p0 11 (FV7z.mk .and 64 [gr 64 0, Src.opd 64 (.i 18446744073709551608)] 4) := by dec_rfl
theorem p0_15 : ∀ feat, Dec feat p0 15 (FV7z.mk .cmp 64 [gr 64 0, .mem (mg (some 7) (some 0) 1 0 64)] 4) := by dec_rfl

/-- What the stretch does. -/
def o0 : List Op := [
  Op.sub 64 4 (.i 8),
  Op.ld 64 1 (some 7) none 1 8,
  Op.mov 64 0 (.r 1),
  Op.and 64 0 (.i 18446744073709551608),
  Op.cmpm 64 0 (some 7) (some 0) 1 0]

theorem b0 (prof : Profile) : Blk prof p0 0 19 o0 :=
  .cons (p0_0 _) (OpI.sub (.i 8) (.inr rfl)) (by decide) <|
  .cons (p0_4 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p0_8 _) (OpI.mov (.r 1) (.inr rfl)) (by decide) <|
  .cons (p0_11 _) (OpI.and (.i 18446744073709551608) (.inr rfl)) (by decide) <|
  .cons (p0_15 _) (OpI.cmpm (.inr rfl)) (by decide) <|
  .nil 19

def j0 : List Byte := [0x0f, 0x85, 0xa6, 0x00, 0x00, 0x00]
theorem j0_0 : ∀ feat, Dec feat j0 0 (FV7z.mk (.jcc 5) 64 [.rel 166] 6) := by dec_rfl

/-- The stretch at `25`. -/
def p1 : List Byte := [
  0x48, 0x8b, 0x47, 0x10, 0x48, 0x8b, 0x57, 0x18, 0x48, 0x3b, 0x78, 0x18]

theorem p1_0 : ∀ feat, Dec feat p1 0 (FV7z.mk .mov 64 [gr 64 0, .mem (mg (some 7) none 1 16 64)] 4) := by dec_rfl
theorem p1_4 : ∀ feat, Dec feat p1 4 (FV7z.mk .mov 64 [gr 64 2, .mem (mg (some 7) none 1 24 64)] 4) := by dec_rfl
theorem p1_8 : ∀ feat, Dec feat p1 8 (FV7z.mk .cmp 64 [gr 64 7, .mem (mg (some 0) none 1 24 64)] 4) := by dec_rfl

/-- What the stretch does. -/
def o1 : List Op := [
  Op.ld 64 0 (some 7) none 1 16,
  Op.ld 64 2 (some 7) none 1 24,
  Op.cmpm 64 7 (some 0) none 1 24]

theorem b1 (prof : Profile) : Blk prof p1 0 12 o1 :=
  .cons (p1_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p1_4 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p1_8 _) (OpI.cmpm (.inr rfl)) (by decide) <|
  .nil 12

def j1 : List Byte := [0x75, 0x79]
theorem j1_0 : ∀ feat, Dec feat j1 0 (FV7z.mk (.jcc 5) 64 [.rel 121] 2) := by dec_rfl

/-- The stretch at `39`. -/
def p2 : List Byte := [
  0x48, 0x3b, 0x7a, 0x10]

theorem p2_0 : ∀ feat, Dec feat p2 0 (FV7z.mk .cmp 64 [gr 64 7, .mem (mg (some 2) none 1 16 64)] 4) := by dec_rfl

/-- What the stretch does. -/
def o2 : List Op := [
  Op.cmpm 64 7 (some 2) none 1 16]

theorem b2 (prof : Profile) : Blk prof p2 0 4 o2 :=
  .cons (p2_0 _) (OpI.cmpm (.inr rfl)) (by decide) <|
  .nil 4

def j2 : List Byte := [0x75, 0x73]
theorem j2_0 : ∀ feat, Dec feat j2 0 (FV7z.mk (.jcc 5) 64 [.rel 115] 2) := by dec_rfl

/-- The stretch at `45`. -/
def p3 : List Byte := [
  0x48, 0x89, 0x50, 0x18, 0x48, 0x89, 0x42, 0x10, 0x48, 0x81, 0xf9, 0xff, 0x03, 0x00, 0x00]

theorem p3_0 : ∀ feat, Dec feat p3 0 (FV7z.mk .mov 64 [.mem (mg (some 0) none 1 24 64), gr 64 2] 4) := by dec_rfl
theorem p3_4 : ∀ feat, Dec feat p3 4 (FV7z.mk .mov 64 [.mem (mg (some 2) none 1 16 64), gr 64 0] 4) := by dec_rfl
theorem p3_8 : ∀ feat, Dec feat p3 8 (FV7z.mk .cmp 64 [gr 64 1, Src.opd 64 (.i 1023)] 7) := by dec_rfl

/-- What the stretch does. -/
def o3 : List Op := [
  Op.st 64 (some 0) none 1 24 2,
  Op.st 64 (some 2) none 1 16 0,
  Op.cmp 64 1 (.i 1023)]

theorem b3 (prof : Profile) : Blk prof p3 0 15 o3 :=
  .cons (p3_0 _) (OpI.st (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p3_4 _) (OpI.st (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p3_8 _) (OpI.cmp (.i 1023) (.inr rfl)) (by decide) <|
  .nil 15

def j3 : List Byte := [0x76, 0x2c]
theorem j3_0 : ∀ feat, Dec feat j3 0 (FV7z.mk (.jcc 6) 64 [.rel 44] 2) := by dec_rfl

/-- The stretch at `62`. -/
def p4 : List Byte := [
  0x48, 0x8b, 0x57, 0x20, 0x48, 0x85, 0xd2]

theorem p4_0 : ∀ feat, Dec feat p4 0 (FV7z.mk .mov 64 [gr 64 2, .mem (mg (some 7) none 1 32 64)] 4) := by dec_rfl
theorem p4_4 : ∀ feat, Dec feat p4 4 (FV7z.mk .test 64 [gr 64 2, Src.opd 64 (.r 2)] 3) := by dec_rfl

/-- What the stretch does. -/
def o4 : List Op := [
  Op.ld 64 2 (some 7) none 1 32,
  Op.test 64 2 (.r 2)]

theorem b4 (prof : Profile) : Blk prof p4 0 7 o4 :=
  .cons (p4_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p4_4 _) (OpI.test (.r 2) (.inr rfl)) (by decide) <|
  .nil 7

def j4 : List Byte := [0x74, 0x23]
theorem j4_0 : ∀ feat, Dec feat j4 0 (FV7z.mk (.jcc 4) 64 [.rel 35] 2) := by dec_rfl

/-- The stretch at `71`. -/
def p5 : List Byte := [
  0x48, 0x3b, 0x7a, 0x28]

theorem p5_0 : ∀ feat, Dec feat p5 0 (FV7z.mk .cmp 64 [gr 64 7, .mem (mg (some 2) none 1 40 64)] 4) := by dec_rfl

/-- What the stretch does. -/
def o5 : List Op := [
  Op.cmpm 64 7 (some 2) none 1 40]

theorem b5 (prof : Profile) : Blk prof p5 0 4 o5 :=
  .cons (p5_0 _) (OpI.cmpm (.inr rfl)) (by decide) <|
  .nil 4

def j5 : List Byte := [0x75, 0x7e]
theorem j5_0 : ∀ feat, Dec feat j5 0 (FV7z.mk (.jcc 5) 64 [.rel 126] 2) := by dec_rfl

/-- The stretch at `77`. -/
def p6 : List Byte := [
  0x48, 0x8b, 0x4f, 0x28, 0x48, 0x3b, 0x79, 0x20]

theorem p6_0 : ∀ feat, Dec feat p6 0 (FV7z.mk .mov 64 [gr 64 1, .mem (mg (some 7) none 1 40 64)] 4) := by dec_rfl
theorem p6_4 : ∀ feat, Dec feat p6 4 (FV7z.mk .cmp 64 [gr 64 7, .mem (mg (some 1) none 1 32 64)] 4) := by dec_rfl

/-- What the stretch does. -/
def o6 : List Op := [
  Op.ld 64 1 (some 7) none 1 40,
  Op.cmpm 64 7 (some 1) none 1 32]

theorem b6 (prof : Profile) : Blk prof p6 0 8 o6 :=
  .cons (p6_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p6_4 _) (OpI.cmpm (.inr rfl)) (by decide) <|
  .nil 8

def j6 : List Byte := [0x75, 0x74]
theorem j6_0 : ∀ feat, Dec feat j6 0 (FV7z.mk (.jcc 5) 64 [.rel 116] 2) := by dec_rfl

/-- The stretch at `87`. -/
def p7 : List Byte := [
  0x48, 0x83, 0x78, 0x20, 0x00]

theorem p7_0 : ∀ feat, Dec feat p7 0 (FV7z.mk .cmp 64 [.mem (mg (some 0) none 1 32 64), .imm 64 0] 5) := by dec_rfl

/-- What the stretch does. -/
def o7 : List Op := [
  Op.cmpmi 64 (some 0) none 1 32 0]

theorem b7 (prof : Profile) : Blk prof p7 0 5 o7 :=
  .cons (p7_0 _) (OpI.cmpmi64) (by decide) <|
  .nil 5

def j7 : List Byte := [0x74, 0x12]
theorem j7_0 : ∀ feat, Dec feat j7 0 (FV7z.mk (.jcc 4) 64 [.rel 18] 2) := by dec_rfl

/-- The stretch at `94`. -/
def p8 : List Byte := [
  0x48, 0x89, 0x4a, 0x28, 0x48, 0x8b, 0x47, 0x28, 0x48, 0x89, 0x50, 0x20]

theorem p8_0 : ∀ feat, Dec feat p8 0 (FV7z.mk .mov 64 [.mem (mg (some 2) none 1 40 64), gr 64 1] 4) := by dec_rfl
theorem p8_4 : ∀ feat, Dec feat p8 4 (FV7z.mk .mov 64 [gr 64 0, .mem (mg (some 7) none 1 40 64)] 4) := by dec_rfl
theorem p8_8 : ∀ feat, Dec feat p8 8 (FV7z.mk .mov 64 [.mem (mg (some 0) none 1 32 64), gr 64 2] 4) := by dec_rfl

/-- What the stretch does. -/
def o8 : List Op := [
  Op.st 64 (some 2) none 1 40 1,
  Op.ld 64 0 (some 7) none 1 40,
  Op.st 64 (some 0) none 1 32 2]

theorem b8 (prof : Profile) : Blk prof p8 0 12 o8 :=
  .cons (p8_0 _) (OpI.st (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p8_4 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p8_8 _) (OpI.st (.inr (.inr (.inr rfl)))) (by decide) <|
  .nil 12

/-- The stretch at `106`. -/
def p9 : List Byte := [
  0x48, 0x83, 0xc4, 0x08]

theorem p9_0 : ∀ feat, Dec feat p9 0 (FV7z.mk .add 64 [gr 64 4, Src.opd 64 (.i 8)] 4) := by dec_rfl

/-- What the stretch does. -/
def o9 : List Op := [
  Op.add 64 4 (.i 8)]

theorem b9 (prof : Profile) : Blk prof p9 0 4 o9 :=
  .cons (p9_0 _) (OpI.add (.i 8) (.inr rfl)) (by decide) <|
  .nil 4

/-- The stretch at `112`. -/
def p10 : List Byte := [
  0x48, 0x39, 0xd7]

theorem p10_0 : ∀ feat, Dec feat p10 0 (FV7z.mk .cmp 64 [gr 64 7, Src.opd 64 (.r 2)] 3) := by dec_rfl

/-- What the stretch does. -/
def o10 : List Op := [
  Op.cmp 64 7 (.r 2)]

theorem b10 (prof : Profile) : Blk prof p10 0 3 o10 :=
  .cons (p10_0 _) (OpI.cmp (.r 2) (.inr rfl)) (by decide) <|
  .nil 3

def j8 : List Byte := [0x74, 0x3b]
theorem j8_0 : ∀ feat, Dec feat j8 0 (FV7z.mk (.jcc 4) 64 [.rel 59] 2) := by dec_rfl

/-- The stretch at `135`. -/
def p11 : List Byte := [
  0x48, 0x8b, 0x57, 0x20, 0x48, 0x89, 0x42, 0x28, 0x48, 0x8b, 0x57, 0x28, 0x48, 0x89, 0x42, 0x20]

theorem p11_0 : ∀ feat, Dec feat p11 0 (FV7z.mk .mov 64 [gr 64 2, .mem (mg (some 7) none 1 32 64)] 4) := by dec_rfl
theorem p11_4 : ∀ feat, Dec feat p11 4 (FV7z.mk .mov 64 [.mem (mg (some 2) none 1 40 64), gr 64 0] 4) := by dec_rfl
theorem p11_8 : ∀ feat, Dec feat p11 8 (FV7z.mk .mov 64 [gr 64 2, .mem (mg (some 7) none 1 40 64)] 4) := by dec_rfl
theorem p11_12 : ∀ feat, Dec feat p11 12 (FV7z.mk .mov 64 [.mem (mg (some 2) none 1 32 64), gr 64 0] 4) := by dec_rfl

/-- What the stretch does. -/
def o11 : List Op := [
  Op.ld 64 2 (some 7) none 1 32,
  Op.st 64 (some 2) none 1 40 0,
  Op.ld 64 2 (some 7) none 1 40,
  Op.st 64 (some 2) none 1 32 0]

theorem b11 (prof : Profile) : Blk prof p11 0 16 o11 :=
  .cons (p11_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p11_4 _) (OpI.st (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p11_8 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p11_12 _) (OpI.st (.inr (.inr (.inr rfl)))) (by decide) <|
  .nil 16

def j9 : List Byte := [0xeb, 0xd1]
theorem j9_0 : ∀ feat, Dec feat j9 0 (FV7z.mk .jmp 64 [.rel 18446744073709551569] 2) := by dec_rfl

def j10 : List Byte := [0xeb, 0xab]
theorem j10_0 : ∀ feat, Dec feat j10 0 (FV7z.mk .jmp 64 [.rel 18446744073709551531] 2) := by dec_rfl

end FV7z.Ulk
