import FV7z.Lemmas.Sp
import FV7z.Lemmas.CmpMi16
import FV7z.Lemmas.BlkOps2
/-!
# The stretches of straight-line code of `CPropVariant::InternalClear` (PLAN.md §M, M1)

Each distinct stretch between labels and jumps (`p*`, 5 of them) and each distinct jump (`j*`, 2) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.Pic
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The stretch at `0`. -/
def p0 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0x66, 0x83, 0x3f, 0x00, 0x53, 0x48, 0x89, 0xfb]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem p0_4 : ∀ feat, Dec feat p0 4 (FV7z.mk .cmp 16 [.mem (mg (some 7) none 1 0 16), .imm 16 0] 4) := by dec_rfl
theorem p0_8 : ∀ feat, Dec feat p0 8 (FV7z.mk .push 64 [gr 64 3] 1) := by dec_rfl
theorem p0_9 : ∀ feat, Dec feat p0 9 (FV7z.mk .mov 64 [gr 64 3, Src.opd 64 (.r 7)] 3) := by dec_rfl

/-- What the stretch does. -/
def o0 : List Op := [
  Op.nop,
  Op.cmpmi 16 (some 7) none 1 0 0,
  Op.push 3,
  Op.mov 64 3 (.r 7)]

theorem b0 (prof : Profile) : Blk prof p0 0 12 o0 :=
  .cons (p0_0 _) (OpI.endbr) (by decide) <|
  .cons (p0_4 _) (OpI.cmpmi16) (by decide) <|
  .cons (p0_8 _) (OpI.push) (by decide) <|
  .cons (p0_9 _) (OpI.mov (.r 7) (.inr rfl)) (by decide) <|
  .nil 12

def j0 : List Byte := [0x75, 0x12]
theorem j0_0 : ∀ feat, Dec feat j0 0 (FV7z.mk (.jcc 5) 64 [.rel 18] 2) := by dec_rfl

/-- The stretch at `14`. -/
def p1 : List Byte := [
  0x31, 0xc9, 0x31, 0xc0, 0x66, 0x89, 0x4f, 0x02]

theorem p1_0 : ∀ feat, Dec feat p1 0 (FV7z.mk .xor 32 [gr 32 1, Src.opd 32 (.r 1)] 2) := by dec_rfl
theorem p1_2 : ∀ feat, Dec feat p1 2 (FV7z.mk .xor 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl
theorem p1_4 : ∀ feat, Dec feat p1 4 (FV7z.mk .mov 16 [.mem (mg (some 7) none 1 2 16), gr 16 1] 4) := by dec_rfl

/-- What the stretch does. -/
def o1 : List Op := [
  Op.xor 32 1 (.r 1),
  Op.xor 32 0 (.r 0),
  Op.st 16 (some 7) none 1 2 1]

theorem b1 (prof : Profile) : Blk prof p1 0 8 o1 :=
  .cons (p1_0 _) (OpI.xor (.r 1) (.inl rfl)) (by decide) <|
  .cons (p1_2 _) (OpI.xor (.r 0) (.inl rfl)) (by decide) <|
  .cons (p1_4 _) (OpI.st (.inr (.inl rfl))) (by decide) <|
  .nil 8

/-- The stretch at `22`. -/
def p2 : List Byte := [
  0x5b]

theorem p2_0 : ∀ feat, Dec feat p2 0 (FV7z.mk .pop 64 [gr 64 3] 1) := by dec_rfl

/-- What the stretch does. -/
def o2 : List Op := [
  Op.pop 3]

theorem b2 (prof : Profile) : Blk prof p2 0 1 o2 :=
  .cons (p2_0 _) (OpI.pop) (by decide) <|
  .nil 1

/-- The stretch at `37`. -/
def p3 : List Byte := [
  0x85, 0xc0]

theorem p3_0 : ∀ feat, Dec feat p3 0 (FV7z.mk .test 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl

/-- What the stretch does. -/
def o3 : List Op := [
  Op.test 32 0 (.r 0)]

theorem b3 (prof : Profile) : Blk prof p3 0 2 o3 :=
  .cons (p3_0 _) (OpI.test (.r 0) (.inl rfl)) (by decide) <|
  .nil 2

def j1 : List Byte := [0x79, 0xed]
theorem j1_0 : ∀ feat, Dec feat j1 0 (FV7z.mk (.jcc 9) 64 [.rel 18446744073709551597] 2) := by dec_rfl

/-- The stretch at `41`. -/
def p4 : List Byte := [
  0xba, 0x0a, 0x00, 0x00, 0x00, 0x89, 0x43, 0x08, 0x66, 0x89, 0x13, 0x5b]

theorem p4_0 : ∀ feat, Dec feat p4 0 (FV7z.mk .mov 32 [gr 32 2, Src.opd 32 (.i 10)] 5) := by dec_rfl
theorem p4_5 : ∀ feat, Dec feat p4 5 (FV7z.mk .mov 32 [.mem (mg (some 3) none 1 8 32), gr 32 0] 3) := by dec_rfl
theorem p4_8 : ∀ feat, Dec feat p4 8 (FV7z.mk .mov 16 [.mem (mg (some 3) none 1 0 16), gr 16 2] 3) := by dec_rfl
theorem p4_11 : ∀ feat, Dec feat p4 11 (FV7z.mk .pop 64 [gr 64 3] 1) := by dec_rfl

/-- What the stretch does. -/
def o4 : List Op := [
  Op.mov 32 2 (.i 10),
  Op.st 32 (some 3) none 1 8 0,
  Op.st 16 (some 3) none 1 0 2,
  Op.pop 3]

theorem b4 (prof : Profile) : Blk prof p4 0 12 o4 :=
  .cons (p4_0 _) (OpI.mov (.i 10) (.inl rfl)) (by decide) <|
  .cons (p4_5 _) (OpI.st (.inr (.inr (.inl rfl)))) (by decide) <|
  .cons (p4_8 _) (OpI.st (.inr (.inl rfl))) (by decide) <|
  .cons (p4_11 _) (OpI.pop) (by decide) <|
  .nil 12

end FV7z.Pic
