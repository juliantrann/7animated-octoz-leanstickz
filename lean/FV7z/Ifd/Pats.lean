import FV7z.Lemmas.Sp
import FV7z.Lemmas.BlkOps2
/-!
# The stretches of straight-line code of `CInFileStream::~CInFileStream` (PLAN.md §M, M1)

Each distinct stretch between labels and jumps (`p*`, 6 of them) and each distinct jump (`j*`, 2) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.Ifd
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The stretch at `0`. -/
def p0 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0x48, 0xc7, 0xc0, 0x48, 0xe7, 0x78, 0x00, 0x53, 0x48, 0x89, 0xfb, 0x48,
  0x8d, 0x50, 0x10, 0x48, 0x89, 0x17, 0x48, 0x8d, 0x50, 0x70, 0x48, 0x89, 0x57, 0x08, 0x48, 0x8d,
  0x90, 0xa0, 0x00, 0x00, 0x00, 0x48, 0x89, 0x57, 0x10, 0x48, 0x8d, 0x90, 0xd0, 0x00, 0x00, 0x00,
  0x48, 0x05, 0x00, 0x01, 0x00, 0x00, 0x48, 0x89, 0x57, 0x18, 0x48, 0x89, 0x47, 0x20, 0x48, 0x8b,
  0xbf, 0xf8, 0x00, 0x00, 0x00, 0x48, 0x85, 0xff]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem p0_4 : ∀ feat, Dec feat p0 4 (FV7z.mk .mov 64 [gr 64 0, Src.opd 64 (.i 7923528)] 7) := by dec_rfl
theorem p0_11 : ∀ feat, Dec feat p0 11 (FV7z.mk .push 64 [gr 64 3] 1) := by dec_rfl
theorem p0_12 : ∀ feat, Dec feat p0 12 (FV7z.mk .mov 64 [gr 64 3, Src.opd 64 (.r 7)] 3) := by dec_rfl
theorem p0_15 : ∀ feat, Dec feat p0 15 (FV7z.mk .lea 64 [gr 64 2, .mem (mg (some 0) none 1 16 0)] 4) := by dec_rfl
theorem p0_19 : ∀ feat, Dec feat p0 19 (FV7z.mk .mov 64 [.mem (mg (some 7) none 1 0 64), gr 64 2] 3) := by dec_rfl
theorem p0_22 : ∀ feat, Dec feat p0 22 (FV7z.mk .lea 64 [gr 64 2, .mem (mg (some 0) none 1 112 0)] 4) := by dec_rfl
theorem p0_26 : ∀ feat, Dec feat p0 26 (FV7z.mk .mov 64 [.mem (mg (some 7) none 1 8 64), gr 64 2] 4) := by dec_rfl
theorem p0_30 : ∀ feat, Dec feat p0 30 (FV7z.mk .lea 64 [gr 64 2, .mem (mg (some 0) none 1 160 0)] 7) := by dec_rfl
theorem p0_37 : ∀ feat, Dec feat p0 37 (FV7z.mk .mov 64 [.mem (mg (some 7) none 1 16 64), gr 64 2] 4) := by dec_rfl
theorem p0_41 : ∀ feat, Dec feat p0 41 (FV7z.mk .lea 64 [gr 64 2, .mem (mg (some 0) none 1 208 0)] 7) := by dec_rfl
theorem p0_48 : ∀ feat, Dec feat p0 48 (FV7z.mk .add 64 [gr 64 0, Src.opd 64 (.i 256)] 6) := by dec_rfl
theorem p0_54 : ∀ feat, Dec feat p0 54 (FV7z.mk .mov 64 [.mem (mg (some 7) none 1 24 64), gr 64 2] 4) := by dec_rfl
theorem p0_58 : ∀ feat, Dec feat p0 58 (FV7z.mk .mov 64 [.mem (mg (some 7) none 1 32 64), gr 64 0] 4) := by dec_rfl
theorem p0_62 : ∀ feat, Dec feat p0 62 (FV7z.mk .mov 64 [gr 64 7, .mem (mg (some 7) none 1 248 64)] 7) := by dec_rfl
theorem p0_69 : ∀ feat, Dec feat p0 69 (FV7z.mk .test 64 [gr 64 7, Src.opd 64 (.r 7)] 3) := by dec_rfl

/-- What the stretch does. -/
def o0 : List Op := [
  Op.nop,
  Op.mov 64 0 (.i 7923528),
  Op.push 3,
  Op.mov 64 3 (.r 7),
  Op.lea 64 2 (some 0) none 1 16,
  Op.st 64 (some 7) none 1 0 2,
  Op.lea 64 2 (some 0) none 1 112,
  Op.st 64 (some 7) none 1 8 2,
  Op.lea 64 2 (some 0) none 1 160,
  Op.st 64 (some 7) none 1 16 2,
  Op.lea 64 2 (some 0) none 1 208,
  Op.add 64 0 (.i 256),
  Op.st 64 (some 7) none 1 24 2,
  Op.st 64 (some 7) none 1 32 0,
  Op.ld 64 7 (some 7) none 1 248,
  Op.test 64 7 (.r 7)]

theorem b0 (prof : Profile) : Blk prof p0 0 72 o0 :=
  .cons (p0_0 _) (OpI.endbr) (by decide) <|
  .cons (p0_4 _) (OpI.mov (.i 7923528) (.inr rfl)) (by decide) <|
  .cons (p0_11 _) (OpI.push) (by decide) <|
  .cons (p0_12 _) (OpI.mov (.r 7) (.inr rfl)) (by decide) <|
  .cons (p0_15 _) (OpI.lea (.inr rfl)) (by decide) <|
  .cons (p0_19 _) (OpI.st (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p0_22 _) (OpI.lea (.inr rfl)) (by decide) <|
  .cons (p0_26 _) (OpI.st (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p0_30 _) (OpI.lea (.inr rfl)) (by decide) <|
  .cons (p0_37 _) (OpI.st (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p0_41 _) (OpI.lea (.inr rfl)) (by decide) <|
  .cons (p0_48 _) (OpI.add (.i 256) (.inr rfl)) (by decide) <|
  .cons (p0_54 _) (OpI.st (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p0_58 _) (OpI.st (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p0_62 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p0_69 _) (OpI.test (.r 7) (.inr rfl)) (by decide) <|
  .nil 72

def j0 : List Byte := [0x74, 0x10]
theorem j0_0 : ∀ feat, Dec feat j0 0 (FV7z.mk (.jcc 4) 64 [.rel 16] 2) := by dec_rfl

/-- The stretch at `74`. -/
def p1 : List Byte := [
  0x48, 0x8b, 0x07, 0x48, 0x8b, 0x93, 0x00, 0x01, 0x00, 0x00, 0x48, 0x89, 0xde]

theorem p1_0 : ∀ feat, Dec feat p1 0 (FV7z.mk .mov 64 [gr 64 0, .mem (mg (some 7) none 1 0 64)] 3) := by dec_rfl
theorem p1_3 : ∀ feat, Dec feat p1 3 (FV7z.mk .mov 64 [gr 64 2, .mem (mg (some 3) none 1 256 64)] 7) := by dec_rfl
theorem p1_10 : ∀ feat, Dec feat p1 10 (FV7z.mk .mov 64 [gr 64 6, Src.opd 64 (.r 3)] 3) := by dec_rfl

/-- What the stretch does. -/
def o1 : List Op := [
  Op.ld 64 0 (some 7) none 1 0,
  Op.ld 64 2 (some 3) none 1 256,
  Op.mov 64 6 (.r 3)]

theorem b1 (prof : Profile) : Blk prof p1 0 13 o1 :=
  .cons (p1_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p1_3 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p1_10 _) (OpI.mov (.r 3) (.inr rfl)) (by decide) <|
  .nil 13

/-- The stretch at `90`. -/
def p2 : List Byte := [
  0x48, 0x8b, 0xbb, 0xe0, 0x00, 0x00, 0x00, 0x48, 0x85, 0xff]

theorem p2_0 : ∀ feat, Dec feat p2 0 (FV7z.mk .mov 64 [gr 64 7, .mem (mg (some 3) none 1 224 64)] 7) := by dec_rfl
theorem p2_7 : ∀ feat, Dec feat p2 7 (FV7z.mk .test 64 [gr 64 7, Src.opd 64 (.r 7)] 3) := by dec_rfl

/-- What the stretch does. -/
def o2 : List Op := [
  Op.ld 64 7 (some 3) none 1 224,
  Op.test 64 7 (.r 7)]

theorem b2 (prof : Profile) : Blk prof p2 0 10 o2 :=
  .cons (p2_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p2_7 _) (OpI.test (.r 7) (.inr rfl)) (by decide) <|
  .nil 10

def j1 : List Byte := [0x74, 0x05]
theorem j1_0 : ∀ feat, Dec feat j1 0 (FV7z.mk (.jcc 4) 64 [.rel 5] 2) := by dec_rfl

/-- The stretch at `107`. -/
def p3 : List Byte := [
  0x48, 0x8b, 0xbb, 0xd0, 0x00, 0x00, 0x00, 0x48, 0x85, 0xff]

theorem p3_0 : ∀ feat, Dec feat p3 0 (FV7z.mk .mov 64 [gr 64 7, .mem (mg (some 3) none 1 208 64)] 7) := by dec_rfl
theorem p3_7 : ∀ feat, Dec feat p3 7 (FV7z.mk .test 64 [gr 64 7, Src.opd 64 (.r 7)] 3) := by dec_rfl

/-- What the stretch does. -/
def o3 : List Op := [
  Op.ld 64 7 (some 3) none 1 208,
  Op.test 64 7 (.r 7)]

theorem b3 (prof : Profile) : Blk prof p3 0 10 o3 :=
  .cons (p3_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p3_7 _) (OpI.test (.r 7) (.inr rfl)) (by decide) <|
  .nil 10

/-- The stretch at `124`. -/
def p4 : List Byte := [
  0x48, 0x8d, 0x7b, 0x2c]

theorem p4_0 : ∀ feat, Dec feat p4 0 (FV7z.mk .lea 64 [gr 64 7, .mem (mg (some 3) none 1 44 0)] 4) := by dec_rfl

/-- What the stretch does. -/
def o4 : List Op := [
  Op.lea 64 7 (some 3) none 1 44]

theorem b4 (prof : Profile) : Blk prof p4 0 4 o4 :=
  .cons (p4_0 _) (OpI.lea (.inr rfl)) (by decide) <|
  .nil 4

/-- The stretch at `133`. -/
def p5 : List Byte := [
  0x5b]

theorem p5_0 : ∀ feat, Dec feat p5 0 (FV7z.mk .pop 64 [gr 64 3] 1) := by dec_rfl

/-- What the stretch does. -/
def o5 : List Op := [
  Op.pop 3]

theorem b5 (prof : Profile) : Blk prof p5 0 1 o5 :=
  .cons (p5_0 _) (OpI.pop) (by decide) <|
  .nil 1

end FV7z.Ifd
