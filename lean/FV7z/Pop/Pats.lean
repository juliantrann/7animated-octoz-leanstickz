import FV7z.Lemmas.Sp
import FV7z.Lemmas.BlkOps2
/-!
# The stretches of straight-line code of `CArchiveExtractCallback::PrepareOperation` (PLAN.md §M, M1)

Each distinct stretch between labels and jumps (`p*`, 9 of them) and each distinct jump (`j*`, 5) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.Pop
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The stretch at `0`. -/
def p0 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0x48, 0x89, 0xf8, 0x48, 0x8b, 0xbf, 0xc0, 0x00, 0x00, 0x00, 0x48, 0x85,
  0xff]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem p0_4 : ∀ feat, Dec feat p0 4 (FV7z.mk .mov 64 [gr 64 0, Src.opd 64 (.r 7)] 3) := by dec_rfl
theorem p0_7 : ∀ feat, Dec feat p0 7 (FV7z.mk .mov 64 [gr 64 7, .mem (mg (some 7) none 1 192 64)] 7) := by dec_rfl
theorem p0_14 : ∀ feat, Dec feat p0 14 (FV7z.mk .test 64 [gr 64 7, Src.opd 64 (.r 7)] 3) := by dec_rfl

/-- What the stretch does. -/
def o0 : List Op := [
  Op.nop,
  Op.mov 64 0 (.r 7),
  Op.ld 64 7 (some 7) none 1 192,
  Op.test 64 7 (.r 7)]

theorem b0 (prof : Profile) : Blk prof p0 0 17 o0 :=
  .cons (p0_0 _) (OpI.endbr) (by decide) <|
  .cons (p0_4 _) (OpI.mov (.r 7) (.inr rfl)) (by decide) <|
  .cons (p0_7 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p0_14 _) (OpI.test (.r 7) (.inr rfl)) (by decide) <|
  .nil 17

def j0 : List Byte := [0x74, 0x0d]
theorem j0_0 : ∀ feat, Dec feat j0 0 (FV7z.mk (.jcc 4) 64 [.rel 13] 2) := by dec_rfl

/-- The stretch at `19`. -/
def p1 : List Byte := [
  0x48, 0x8b, 0x07]

theorem p1_0 : ∀ feat, Dec feat p1 0 (FV7z.mk .mov 64 [gr 64 0, .mem (mg (some 7) none 1 0 64)] 3) := by dec_rfl

/-- What the stretch does. -/
def o1 : List Op := [
  Op.ld 64 0 (some 7) none 1 0]

theorem b1 (prof : Profile) : Blk prof p1 0 3 o1 :=
  .cons (p1_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .nil 3

/-- The stretch at `32`. -/
def p2 : List Byte := [
  0xc6, 0x40, 0x6d, 0x00, 0x85, 0xf6]

theorem p2_0 : ∀ feat, Dec feat p2 0 (FV7z.mk .mov 8 [.mem (mg (some 0) none 1 109 8), .imm 8 0] 4) := by dec_rfl
theorem p2_4 : ∀ feat, Dec feat p2 4 (FV7z.mk .test 32 [gr 32 6, Src.opd 32 (.r 6)] 2) := by dec_rfl

/-- What the stretch does. -/
def o2 : List Op := [
  Op.sti 8 (some 0) none 1 109 0,
  Op.test 32 6 (.r 6)]

theorem b2 (prof : Profile) : Blk prof p2 0 6 o2 :=
  .cons (p2_0 _) (OpI.sti (.inl rfl)) (by decide) <|
  .cons (p2_4 _) (OpI.test (.r 6) (.inl rfl)) (by decide) <|
  .nil 6

def j1 : List Byte := [0x75, 0x0a]
theorem j1_0 : ∀ feat, Dec feat j1 0 (FV7z.mk (.jcc 5) 64 [.rel 10] 2) := by dec_rfl

/-- The stretch at `40`. -/
def p3 : List Byte := [
  0x80, 0x78, 0x3d, 0x00]

theorem p3_0 : ∀ feat, Dec feat p3 0 (FV7z.mk .cmp 8 [.mem (mg (some 0) none 1 61 8), .imm 8 0] 4) := by dec_rfl

/-- What the stretch does. -/
def o3 : List Op := [
  Op.cmpmi 8 (some 0) none 1 61 0]

theorem b3 (prof : Profile) : Blk prof p3 0 4 o3 :=
  .cons (p3_0 _) (OpI.cmpmi (.inl rfl)) (by decide) <|
  .nil 4

def j2 : List Byte := [0x75, 0x42]
theorem j2_0 : ∀ feat, Dec feat j2 0 (FV7z.mk (.jcc 5) 64 [.rel 66] 2) := by dec_rfl

/-- The stretch at `46`. -/
def p4 : List Byte := [
  0xc6, 0x40, 0x6d, 0x01]

theorem p4_0 : ∀ feat, Dec feat p4 0 (FV7z.mk .mov 8 [.mem (mg (some 0) none 1 109 8), .imm 8 1] 4) := by dec_rfl

/-- What the stretch does. -/
def o4 : List Op := [
  Op.sti 8 (some 0) none 1 109 1]

theorem b4 (prof : Profile) : Blk prof p4 0 4 o4 :=
  .cons (p4_0 _) (OpI.sti (.inl rfl)) (by decide) <|
  .nil 4

/-- The stretch at `50`. -/
def p5 : List Byte := [
  0x4c, 0x8b, 0x88, 0x80, 0x00, 0x00, 0x00, 0x80, 0x78, 0x69, 0x00, 0x49, 0x8b, 0x11, 0x4c, 0x8b,
  0x52, 0x30]

theorem p5_0 : ∀ feat, Dec feat p5 0 (FV7z.mk .mov 64 [gr 64 9, .mem (mg (some 0) none 1 128 64)] 7) := by dec_rfl
theorem p5_7 : ∀ feat, Dec feat p5 7 (FV7z.mk .cmp 8 [.mem (mg (some 0) none 1 105 8), .imm 8 0] 4) := by dec_rfl
theorem p5_11 : ∀ feat, Dec feat p5 11 (FV7z.mk .mov 64 [gr 64 2, .mem (mg (some 9) none 1 0 64)] 3) := by dec_rfl
theorem p5_14 : ∀ feat, Dec feat p5 14 (FV7z.mk .mov 64 [gr 64 10, .mem (mg (some 2) none 1 48 64)] 4) := by dec_rfl

/-- What the stretch does. -/
def o5 : List Op := [
  Op.ld 64 9 (some 0) none 1 128,
  Op.cmpmi 8 (some 0) none 1 105 0,
  Op.ld 64 2 (some 9) none 1 0,
  Op.ld 64 10 (some 2) none 1 48]

theorem b5 (prof : Profile) : Blk prof p5 0 18 o5 :=
  .cons (p5_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p5_7 _) (OpI.cmpmi (.inl rfl)) (by decide) <|
  .cons (p5_11 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p5_14 _) (OpI.ld (.inr rfl)) (by decide) <|
  .nil 18

def j3 : List Byte := [0x74, 0x07]
theorem j3_0 : ∀ feat, Dec feat j3 0 (FV7z.mk (.jcc 4) 64 [.rel 7] 2) := by dec_rfl

/-- The stretch at `70`. -/
def p6 : List Byte := [
  0x48, 0x8d, 0xb8, 0x90, 0x01, 0x00, 0x00]

theorem p6_0 : ∀ feat, Dec feat p6 0 (FV7z.mk .lea 64 [gr 64 7, .mem (mg (some 0) none 1 400 0)] 7) := by dec_rfl

/-- What the stretch does. -/
def o6 : List Op := [
  Op.lea 64 7 (some 0) none 1 400]

theorem b6 (prof : Profile) : Blk prof p6 0 7 o6 :=
  .cons (p6_0 _) (OpI.lea (.inr rfl)) (by decide) <|
  .nil 7

/-- The stretch at `77`. -/
def p7 : List Byte := [
  0x4c, 0x8b, 0x98, 0xd0, 0x00, 0x00, 0x00, 0x49, 0x89, 0xf8, 0x89, 0xf1, 0x0f, 0xb6, 0x90, 0x12,
  0x01, 0x00, 0x00, 0x4c, 0x89, 0xcf, 0x4c, 0x89, 0xde]

theorem p7_0 : ∀ feat, Dec feat p7 0 (FV7z.mk .mov 64 [gr 64 11, .mem (mg (some 0) none 1 208 64)] 7) := by dec_rfl
theorem p7_7 : ∀ feat, Dec feat p7 7 (FV7z.mk .mov 64 [gr 64 8, Src.opd 64 (.r 7)] 3) := by dec_rfl
theorem p7_10 : ∀ feat, Dec feat p7 10 (FV7z.mk .mov 32 [gr 32 1, Src.opd 32 (.r 6)] 2) := by dec_rfl
theorem p7_12 : ∀ feat, Dec feat p7 12 (FV7z.mk .movzx 32 [gr 32 2, .mem (mg (some 0) none 1 274 8)] 7) := by dec_rfl
theorem p7_19 : ∀ feat, Dec feat p7 19 (FV7z.mk .mov 64 [gr 64 7, Src.opd 64 (.r 9)] 3) := by dec_rfl
theorem p7_22 : ∀ feat, Dec feat p7 22 (FV7z.mk .mov 64 [gr 64 6, Src.opd 64 (.r 11)] 3) := by dec_rfl

/-- What the stretch does. -/
def o7 : List Op := [
  Op.ld 64 11 (some 0) none 1 208,
  Op.mov 64 8 (.r 7),
  Op.mov 32 1 (.r 6),
  Op.ldzx 8 2 (some 0) none 1 274,
  Op.mov 64 7 (.r 9),
  Op.mov 64 6 (.r 11)]

theorem b7 (prof : Profile) : Blk prof p7 0 25 o7 :=
  .cons (p7_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p7_7 _) (OpI.mov (.r 7) (.inr rfl)) (by decide) <|
  .cons (p7_10 _) (OpI.mov (.r 6) (.inl rfl)) (by decide) <|
  .cons (p7_12 _) (OpI.ldzx (.inl rfl)) (by decide) <|
  .cons (p7_19 _) (OpI.mov (.r 9) (.inr rfl)) (by decide) <|
  .cons (p7_22 _) (OpI.mov (.r 11) (.inr rfl)) (by decide) <|
  .nil 25

/-- The stretch at `112`. -/
def p8 : List Byte := [
  0xbe, 0x01, 0x00, 0x00, 0x00]

theorem p8_0 : ∀ feat, Dec feat p8 0 (FV7z.mk .mov 32 [gr 32 6, Src.opd 32 (.i 1)] 5) := by dec_rfl

/-- What the stretch does. -/
def o8 : List Op := [
  Op.mov 32 6 (.i 1)]

theorem b8 (prof : Profile) : Blk prof p8 0 5 o8 :=
  .cons (p8_0 _) (OpI.mov (.i 1) (.inl rfl)) (by decide) <|
  .nil 5

def j4 : List Byte := [0xeb, 0xbb]
theorem j4_0 : ∀ feat, Dec feat j4 0 (FV7z.mk .jmp 64 [.rel 18446744073709551547] 2) := by dec_rfl

end FV7z.Pop
