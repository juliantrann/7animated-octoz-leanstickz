import FV7z.Lemmas.Sp
import FV7z.Lemmas.BlkOps2
/-!
# The stretches of straight-line code of `CStdOutStream::NormalizePrint_UString` (PLAN.md §M, M1)

Each distinct stretch between labels and jumps (`p*`, 4 of them) and each distinct jump (`j*`, 3) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.Npl
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The stretch at `0`. -/
def p0 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0x41, 0x54, 0x49, 0x89, 0xf4, 0x55, 0x48, 0x89, 0xfd, 0x48, 0x83, 0xec,
  0x08, 0x80, 0x7f, 0x0a, 0x00]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem p0_4 : ∀ feat, Dec feat p0 4 (FV7z.mk .push 64 [gr 64 12] 2) := by dec_rfl
theorem p0_6 : ∀ feat, Dec feat p0 6 (FV7z.mk .mov 64 [gr 64 12, Src.opd 64 (.r 6)] 3) := by dec_rfl
theorem p0_9 : ∀ feat, Dec feat p0 9 (FV7z.mk .push 64 [gr 64 5] 1) := by dec_rfl
theorem p0_10 : ∀ feat, Dec feat p0 10 (FV7z.mk .mov 64 [gr 64 5, Src.opd 64 (.r 7)] 3) := by dec_rfl
theorem p0_13 : ∀ feat, Dec feat p0 13 (FV7z.mk .sub 64 [gr 64 4, Src.opd 64 (.i 8)] 4) := by dec_rfl
theorem p0_17 : ∀ feat, Dec feat p0 17 (FV7z.mk .cmp 8 [.mem (mg (some 7) none 1 10 8), .imm 8 0] 4) := by dec_rfl

/-- What the stretch does. -/
def o0 : List Op := [
  Op.nop,
  Op.push 12,
  Op.mov 64 12 (.r 6),
  Op.push 5,
  Op.mov 64 5 (.r 7),
  Op.sub 64 4 (.i 8),
  Op.cmpmi 8 (some 7) none 1 10 0]

theorem b0 (prof : Profile) : Blk prof p0 0 21 o0 :=
  .cons (p0_0 _) (OpI.endbr) (by decide) <|
  .cons (p0_4 _) (OpI.push) (by decide) <|
  .cons (p0_6 _) (OpI.mov (.r 6) (.inr rfl)) (by decide) <|
  .cons (p0_9 _) (OpI.push) (by decide) <|
  .cons (p0_10 _) (OpI.mov (.r 7) (.inr rfl)) (by decide) <|
  .cons (p0_13 _) (OpI.sub (.i 8) (.inr rfl)) (by decide) <|
  .cons (p0_17 _) (OpI.cmpmi (.inl rfl)) (by decide) <|
  .nil 21

def j0 : List Byte := [0x74, 0x06]
theorem j0_0 : ∀ feat, Dec feat j0 0 (FV7z.mk (.jcc 4) 64 [.rel 6] 2) := by dec_rfl

/-- The stretch at `23`. -/
def p1 : List Byte := [
  0x80, 0x7f, 0x09, 0x00]

theorem p1_0 : ∀ feat, Dec feat p1 0 (FV7z.mk .cmp 8 [.mem (mg (some 7) none 1 9 8), .imm 8 0] 4) := by dec_rfl

/-- What the stretch does. -/
def o1 : List Op := [
  Op.cmpmi 8 (some 7) none 1 9 0]

theorem b1 (prof : Profile) : Blk prof p1 0 4 o1 :=
  .cons (p1_0 _) (OpI.cmpmi (.inl rfl)) (by decide) <|
  .nil 4

def j1 : List Byte := [0x74, 0x13]
theorem j1_0 : ∀ feat, Dec feat j1 0 (FV7z.mk (.jcc 4) 64 [.rel 19] 2) := by dec_rfl

/-- The stretch at `29`. -/
def p2 : List Byte := [
  0x48, 0x83, 0xc4, 0x08, 0x4c, 0x89, 0xe6, 0x48, 0x89, 0xef, 0x5d, 0x41, 0x5c]

theorem p2_0 : ∀ feat, Dec feat p2 0 (FV7z.mk .add 64 [gr 64 4, Src.opd 64 (.i 8)] 4) := by dec_rfl
theorem p2_4 : ∀ feat, Dec feat p2 4 (FV7z.mk .mov 64 [gr 64 6, Src.opd 64 (.r 12)] 3) := by dec_rfl
theorem p2_7 : ∀ feat, Dec feat p2 7 (FV7z.mk .mov 64 [gr 64 7, Src.opd 64 (.r 5)] 3) := by dec_rfl
theorem p2_10 : ∀ feat, Dec feat p2 10 (FV7z.mk .pop 64 [gr 64 5] 1) := by dec_rfl
theorem p2_11 : ∀ feat, Dec feat p2 11 (FV7z.mk .pop 64 [gr 64 12] 2) := by dec_rfl

/-- What the stretch does. -/
def o2 : List Op := [
  Op.add 64 4 (.i 8),
  Op.mov 64 6 (.r 12),
  Op.mov 64 7 (.r 5),
  Op.pop 5,
  Op.pop 12]

theorem b2 (prof : Profile) : Blk prof p2 0 13 o2 :=
  .cons (p2_0 _) (OpI.add (.i 8) (.inr rfl)) (by decide) <|
  .cons (p2_4 _) (OpI.mov (.r 12) (.inr rfl)) (by decide) <|
  .cons (p2_7 _) (OpI.mov (.r 5) (.inr rfl)) (by decide) <|
  .cons (p2_10 _) (OpI.pop) (by decide) <|
  .cons (p2_11 _) (OpI.pop) (by decide) <|
  .nil 13

/-- The stretch at `48`. -/
def p3 : List Byte := [
  0xba, 0x5c, 0x00, 0x00, 0x00, 0xbe, 0x2f, 0x00, 0x00, 0x00, 0x4c, 0x89, 0xe7]

theorem p3_0 : ∀ feat, Dec feat p3 0 (FV7z.mk .mov 32 [gr 32 2, Src.opd 32 (.i 92)] 5) := by dec_rfl
theorem p3_5 : ∀ feat, Dec feat p3 5 (FV7z.mk .mov 32 [gr 32 6, Src.opd 32 (.i 47)] 5) := by dec_rfl
theorem p3_10 : ∀ feat, Dec feat p3 10 (FV7z.mk .mov 64 [gr 64 7, Src.opd 64 (.r 12)] 3) := by dec_rfl

/-- What the stretch does. -/
def o3 : List Op := [
  Op.mov 32 2 (.i 92),
  Op.mov 32 6 (.i 47),
  Op.mov 64 7 (.r 12)]

theorem b3 (prof : Profile) : Blk prof p3 0 13 o3 :=
  .cons (p3_0 _) (OpI.mov (.i 92) (.inl rfl)) (by decide) <|
  .cons (p3_5 _) (OpI.mov (.i 47) (.inl rfl)) (by decide) <|
  .cons (p3_10 _) (OpI.mov (.r 12) (.inr rfl)) (by decide) <|
  .nil 13

def j2 : List Byte := [0xeb, 0xd9]
theorem j2_0 : ∀ feat, Dec feat j2 0 (FV7z.mk .jmp 64 [.rel 18446744073709551577] 2) := by dec_rfl

end FV7z.Npl
