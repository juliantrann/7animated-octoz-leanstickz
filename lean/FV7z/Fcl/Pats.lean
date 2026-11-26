import FV7z.Lemmas.Sp
import FV7z.Lemmas.BlkOps2
/-!
# The stretches of straight-line code of `NWindows::NFile::NIO::CFileBase::Close` (PLAN.md §M, M1)

Each distinct stretch between labels and jumps (`p*`, 4 of them) and each distinct jump (`j*`, 2) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.Fcl
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The stretch at `0`. -/
def p0 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0x53, 0x48, 0x89, 0xfb, 0x8b, 0x3f, 0xb8, 0x01, 0x00, 0x00, 0x00, 0x83,
  0xff, 0xff]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem p0_4 : ∀ feat, Dec feat p0 4 (FV7z.mk .push 64 [gr 64 3] 1) := by dec_rfl
theorem p0_5 : ∀ feat, Dec feat p0 5 (FV7z.mk .mov 64 [gr 64 3, Src.opd 64 (.r 7)] 3) := by dec_rfl
theorem p0_8 : ∀ feat, Dec feat p0 8 (FV7z.mk .mov 32 [gr 32 7, .mem (mg (some 7) none 1 0 32)] 2) := by dec_rfl
theorem p0_10 : ∀ feat, Dec feat p0 10 (FV7z.mk .mov 32 [gr 32 0, Src.opd 32 (.i 1)] 5) := by dec_rfl
theorem p0_15 : ∀ feat, Dec feat p0 15 (FV7z.mk .cmp 32 [gr 32 7, Src.opd 32 (.i 4294967295)] 3) := by dec_rfl

/-- What the stretch does. -/
def o0 : List Op := [
  Op.nop,
  Op.push 3,
  Op.mov 64 3 (.r 7),
  Op.ld 32 7 (some 7) none 1 0,
  Op.mov 32 0 (.i 1),
  Op.cmp 32 7 (.i 4294967295)]

theorem b0 (prof : Profile) : Blk prof p0 0 18 o0 :=
  .cons (p0_0 _) (OpI.endbr) (by decide) <|
  .cons (p0_4 _) (OpI.push) (by decide) <|
  .cons (p0_5 _) (OpI.mov (.r 7) (.inr rfl)) (by decide) <|
  .cons (p0_8 _) (OpI.ld (.inl rfl)) (by decide) <|
  .cons (p0_10 _) (OpI.mov (.i 1) (.inl rfl)) (by decide) <|
  .cons (p0_15 _) (OpI.cmp (.i 4294967295) (.inl rfl)) (by decide) <|
  .nil 18

def j0 : List Byte := [0x74, 0x1a]
theorem j0_0 : ∀ feat, Dec feat j0 0 (FV7z.mk (.jcc 4) 64 [.rel 26] 2) := by dec_rfl

/-- The stretch at `25`. -/
def p1 : List Byte := [
  0x41, 0x89, 0xc0, 0x31, 0xc0, 0x45, 0x85, 0xc0]

theorem p1_0 : ∀ feat, Dec feat p1 0 (FV7z.mk .mov 32 [gr 32 8, Src.opd 32 (.r 0)] 3) := by dec_rfl
theorem p1_3 : ∀ feat, Dec feat p1 3 (FV7z.mk .xor 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl
theorem p1_5 : ∀ feat, Dec feat p1 5 (FV7z.mk .test 32 [gr 32 8, Src.opd 32 (.r 8)] 3) := by dec_rfl

/-- What the stretch does. -/
def o1 : List Op := [
  Op.mov 32 8 (.r 0),
  Op.xor 32 0 (.r 0),
  Op.test 32 8 (.r 8)]

theorem b1 (prof : Profile) : Blk prof p1 0 8 o1 :=
  .cons (p1_0 _) (OpI.mov (.r 0) (.inl rfl)) (by decide) <|
  .cons (p1_3 _) (OpI.xor (.r 0) (.inl rfl)) (by decide) <|
  .cons (p1_5 _) (OpI.test (.r 8) (.inl rfl)) (by decide) <|
  .nil 8

def j1 : List Byte := [0x75, 0x0b]
theorem j1_0 : ∀ feat, Dec feat j1 0 (FV7z.mk (.jcc 5) 64 [.rel 11] 2) := by dec_rfl

/-- The stretch at `35`. -/
def p2 : List Byte := [
  0xc7, 0x03, 0xff, 0xff, 0xff, 0xff, 0xb8, 0x01, 0x00, 0x00, 0x00]

theorem p2_0 : ∀ feat, Dec feat p2 0 (FV7z.mk .mov 32 [.mem (mg (some 3) none 1 0 32), .imm 32 4294967295] 6) := by dec_rfl
theorem p2_6 : ∀ feat, Dec feat p2 6 (FV7z.mk .mov 32 [gr 32 0, Src.opd 32 (.i 1)] 5) := by dec_rfl

/-- What the stretch does. -/
def o2 : List Op := [
  Op.sti 32 (some 3) none 1 0 4294967295,
  Op.mov 32 0 (.i 1)]

theorem b2 (prof : Profile) : Blk prof p2 0 11 o2 :=
  .cons (p2_0 _) (OpI.sti (.inr (.inr (.inl rfl)))) (by decide) <|
  .cons (p2_6 _) (OpI.mov (.i 1) (.inl rfl)) (by decide) <|
  .nil 11

/-- The stretch at `46`. -/
def p3 : List Byte := [
  0x5b]

theorem p3_0 : ∀ feat, Dec feat p3 0 (FV7z.mk .pop 64 [gr 64 3] 1) := by dec_rfl

/-- What the stretch does. -/
def o3 : List Op := [
  Op.pop 3]

theorem b3 (prof : Profile) : Blk prof p3 0 1 o3 :=
  .cons (p3_0 _) (OpI.pop) (by decide) <|
  .nil 1

end FV7z.Fcl
