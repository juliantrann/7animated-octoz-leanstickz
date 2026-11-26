import FV7z.Lemmas.Sp
import FV7z.Lemmas.BlkOps12
import FV7z.Lemmas.BlkOps2
/-!
# The stretches of straight-line code of `NCompress::NLzma::CDecoder::CreateInputBuffer` (PLAN.md §M, M1)

Each distinct stretch between labels and jumps (`p*`, 7 of them) and each distinct jump (`j*`, 2) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.Cib
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The stretch at `0`. -/
def p0 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0x53, 0x48, 0x89, 0xfb, 0x48, 0x8b, 0x7f, 0x60, 0x48, 0x85, 0xff]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem p0_4 : ∀ feat, Dec feat p0 4 (FV7z.mk .push 64 [gr 64 3] 1) := by dec_rfl
theorem p0_5 : ∀ feat, Dec feat p0 5 (FV7z.mk .mov 64 [gr 64 3, Src.opd 64 (.r 7)] 3) := by dec_rfl
theorem p0_8 : ∀ feat, Dec feat p0 8 (FV7z.mk .mov 64 [gr 64 7, .mem (mg (some 7) none 1 96 64)] 4) := by dec_rfl
theorem p0_12 : ∀ feat, Dec feat p0 12 (FV7z.mk .test 64 [gr 64 7, Src.opd 64 (.r 7)] 3) := by dec_rfl

/-- What the stretch does. -/
def o0 : List Op := [
  Op.nop,
  Op.push 3,
  Op.mov 64 3 (.r 7),
  Op.ld 64 7 (some 7) none 1 96,
  Op.test 64 7 (.r 7)]

theorem b0 (prof : Profile) : Blk prof p0 0 15 o0 :=
  .cons (p0_0 _) (OpI.endbr) (by decide) <|
  .cons (p0_4 _) (OpI.push) (by decide) <|
  .cons (p0_5 _) (OpI.mov (.r 7) (.inr rfl)) (by decide) <|
  .cons (p0_8 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p0_12 _) (OpI.test (.r 7) (.inr rfl)) (by decide) <|
  .nil 15

def j0 : List Byte := [0x74, 0x0a]
theorem j0_0 : ∀ feat, Dec feat j0 0 (FV7z.mk (.jcc 4) 64 [.rel 10] 2) := by dec_rfl

/-- The stretch at `17`. -/
def p1 : List Byte := [
  0x8b, 0x53, 0x4c, 0x31, 0xc0, 0x39, 0x53, 0x50]

theorem p1_0 : ∀ feat, Dec feat p1 0 (FV7z.mk .mov 32 [gr 32 2, .mem (mg (some 3) none 1 76 32)] 3) := by dec_rfl
theorem p1_3 : ∀ feat, Dec feat p1 3 (FV7z.mk .xor 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl
theorem p1_5 : ∀ feat, Dec feat p1 5 (FV7z.mk .cmp 32 [.mem (mg (some 3) none 1 80 32), gr 32 2] 3) := by dec_rfl

/-- What the stretch does. -/
def o1 : List Op := [
  Op.ld 32 2 (some 3) none 1 76,
  Op.xor 32 0 (.r 0),
  Op.cmpmr 32 (some 3) none 1 80 2]

theorem b1 (prof : Profile) : Blk prof p1 0 8 o1 :=
  .cons (p1_0 _) (OpI.ld (.inl rfl)) (by decide) <|
  .cons (p1_3 _) (OpI.xor (.r 0) (.inl rfl)) (by decide) <|
  .cons (p1_5 _) (OpI.cmpmr (.inl rfl)) (by decide) <|
  .nil 8

def j1 : List Byte := [0x74, 0x25]
theorem j1_0 : ∀ feat, Dec feat j1 0 (FV7z.mk (.jcc 4) 64 [.rel 37] 2) := by dec_rfl

/-- The stretch at `32`. -/
def p2 : List Byte := [
  0xc7, 0x43, 0x4c, 0x00, 0x00, 0x00, 0x00, 0x8b, 0x7b, 0x50]

theorem p2_0 : ∀ feat, Dec feat p2 0 (FV7z.mk .mov 32 [.mem (mg (some 3) none 1 76 32), .imm 32 0] 7) := by dec_rfl
theorem p2_7 : ∀ feat, Dec feat p2 7 (FV7z.mk .mov 32 [gr 32 7, .mem (mg (some 3) none 1 80 32)] 3) := by dec_rfl

/-- What the stretch does. -/
def o2 : List Op := [
  Op.sti 32 (some 3) none 1 76 0,
  Op.ld 32 7 (some 3) none 1 80]

theorem b2 (prof : Profile) : Blk prof p2 0 10 o2 :=
  .cons (p2_0 _) (OpI.sti (.inr (.inr (.inl rfl)))) (by decide) <|
  .cons (p2_7 _) (OpI.ld (.inl rfl)) (by decide) <|
  .nil 10

/-- The stretch at `47`. -/
def p3 : List Byte := [
  0x48, 0x89, 0x43, 0x60, 0x48, 0x85, 0xc0]

theorem p3_0 : ∀ feat, Dec feat p3 0 (FV7z.mk .mov 64 [.mem (mg (some 3) none 1 96 64), gr 64 0] 4) := by dec_rfl
theorem p3_4 : ∀ feat, Dec feat p3 4 (FV7z.mk .test 64 [gr 64 0, Src.opd 64 (.r 0)] 3) := by dec_rfl

/-- What the stretch does. -/
def o3 : List Op := [
  Op.st 64 (some 3) none 1 96 0,
  Op.test 64 0 (.r 0)]

theorem b3 (prof : Profile) : Blk prof p3 0 7 o3 :=
  .cons (p3_0 _) (OpI.st (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p3_4 _) (OpI.test (.r 0) (.inr rfl)) (by decide) <|
  .nil 7

/-- The stretch at `56`. -/
def p4 : List Byte := [
  0x8b, 0x43, 0x50, 0x89, 0x43, 0x4c, 0x31, 0xc0]

theorem p4_0 : ∀ feat, Dec feat p4 0 (FV7z.mk .mov 32 [gr 32 0, .mem (mg (some 3) none 1 80 32)] 3) := by dec_rfl
theorem p4_3 : ∀ feat, Dec feat p4 3 (FV7z.mk .mov 32 [.mem (mg (some 3) none 1 76 32), gr 32 0] 3) := by dec_rfl
theorem p4_6 : ∀ feat, Dec feat p4 6 (FV7z.mk .xor 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl

/-- What the stretch does. -/
def o4 : List Op := [
  Op.ld 32 0 (some 3) none 1 80,
  Op.st 32 (some 3) none 1 76 0,
  Op.xor 32 0 (.r 0)]

theorem b4 (prof : Profile) : Blk prof p4 0 8 o4 :=
  .cons (p4_0 _) (OpI.ld (.inl rfl)) (by decide) <|
  .cons (p4_3 _) (OpI.st (.inr (.inr (.inl rfl)))) (by decide) <|
  .cons (p4_6 _) (OpI.xor (.r 0) (.inl rfl)) (by decide) <|
  .nil 8

/-- The stretch at `64`. -/
def p5 : List Byte := [
  0x5b]

theorem p5_0 : ∀ feat, Dec feat p5 0 (FV7z.mk .pop 64 [gr 64 3] 1) := by dec_rfl

/-- What the stretch does. -/
def o5 : List Op := [
  Op.pop 3]

theorem b5 (prof : Profile) : Blk prof p5 0 1 o5 :=
  .cons (p5_0 _) (OpI.pop) (by decide) <|
  .nil 1

/-- The stretch at `66`. -/
def p6 : List Byte := [
  0xb8, 0x0e, 0x00, 0x07, 0x80, 0x5b]

theorem p6_0 : ∀ feat, Dec feat p6 0 (FV7z.mk .mov 32 [gr 32 0, Src.opd 32 (.i 2147942414)] 5) := by dec_rfl
theorem p6_5 : ∀ feat, Dec feat p6 5 (FV7z.mk .pop 64 [gr 64 3] 1) := by dec_rfl

/-- What the stretch does. -/
def o6 : List Op := [
  Op.mov 32 0 (.i 2147942414),
  Op.pop 3]

theorem b6 (prof : Profile) : Blk prof p6 0 6 o6 :=
  .cons (p6_0 _) (OpI.mov (.i 2147942414) (.inl rfl)) (by decide) <|
  .cons (p6_5 _) (OpI.pop) (by decide) <|
  .nil 6

end FV7z.Cib
