import FV7z.Lemmas.Sp
import FV7z.Lemmas.BlkOps2
/-!
# The stretches of straight-line code of `pthread_mutex_unlock` (PLAN.md G3, pthread)

Each distinct stretch between labels and jumps (`p*`, 5 of them) and each distinct jump (`j*`, 3) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.Pmu
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The stretch at `0`. -/
def p0 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0x8b, 0x47, 0x10, 0x89, 0xc2, 0x81, 0xe2, 0x7f, 0x01, 0x00, 0x00, 0x83,
  0xe0, 0x7c]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem p0_4 : ∀ feat, Dec feat p0 4 (FV7z.mk .mov 32 [gr 32 0, .mem (mg (some 7) none 1 16 32)] 3) := by dec_rfl
theorem p0_7 : ∀ feat, Dec feat p0 7 (FV7z.mk .mov 32 [gr 32 2, Src.opd 32 (.r 0)] 2) := by dec_rfl
theorem p0_9 : ∀ feat, Dec feat p0 9 (FV7z.mk .and 32 [gr 32 2, Src.opd 32 (.i 383)] 6) := by dec_rfl
theorem p0_15 : ∀ feat, Dec feat p0 15 (FV7z.mk .and 32 [gr 32 0, Src.opd 32 (.i 124)] 3) := by dec_rfl

/-- What the stretch does. -/
def o0 : List Op := [
  Op.nop,
  Op.ld 32 0 (some 7) none 1 16,
  Op.mov 32 2 (.r 0),
  Op.and 32 2 (.i 383),
  Op.and 32 0 (.i 124)]

theorem b0 (prof : Profile) : Blk prof p0 0 18 o0 :=
  .cons (p0_0 _) (OpI.endbr) (by decide) <|
  .cons (p0_4 _) (OpI.ld (.inl rfl)) (by decide) <|
  .cons (p0_7 _) (OpI.mov (.r 0) (.inl rfl)) (by decide) <|
  .cons (p0_9 _) (OpI.and (.i 383) (.inl rfl)) (by decide) <|
  .cons (p0_15 _) (OpI.and (.i 124) (.inl rfl)) (by decide) <|
  .nil 18

def j0 : List Byte := [0x75, 0x2c]
theorem j0_0 : ∀ feat, Dec feat j0 0 (FV7z.mk (.jcc 5) 64 [.rel 44] 2) := by dec_rfl

/-- The stretch at `20`. -/
def p1 : List Byte := [
  0x41, 0x89, 0xc0, 0x85, 0xd2]

theorem p1_0 : ∀ feat, Dec feat p1 0 (FV7z.mk .mov 32 [gr 32 8, Src.opd 32 (.r 0)] 3) := by dec_rfl
theorem p1_3 : ∀ feat, Dec feat p1 3 (FV7z.mk .test 32 [gr 32 2, Src.opd 32 (.r 2)] 2) := by dec_rfl

/-- What the stretch does. -/
def o1 : List Op := [
  Op.mov 32 8 (.r 0),
  Op.test 32 2 (.r 2)]

theorem b1 (prof : Profile) : Blk prof p1 0 5 o1 :=
  .cons (p1_0 _) (OpI.mov (.r 0) (.inl rfl)) (by decide) <|
  .cons (p1_3 _) (OpI.test (.r 2) (.inl rfl)) (by decide) <|
  .nil 5

def j1 : List Byte := [0x75, 0x35]
theorem j1_0 : ∀ feat, Dec feat j1 0 (FV7z.mk (.jcc 5) 64 [.rel 53] 2) := by dec_rfl

/-- The stretch at `31`. -/
def p2 : List Byte := [
  0x31, 0xc0, 0xc7, 0x47, 0x08, 0x00, 0x00, 0x00, 0x00, 0x8b, 0x77, 0x10]

theorem p2_0 : ∀ feat, Dec feat p2 0 (FV7z.mk .xor 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl
theorem p2_2 : ∀ feat, Dec feat p2 2 (FV7z.mk .mov 32 [.mem (mg (some 7) none 1 8 32), .imm 32 0] 7) := by dec_rfl
theorem p2_9 : ∀ feat, Dec feat p2 9 (FV7z.mk .mov 32 [gr 32 6, .mem (mg (some 7) none 1 16 32)] 3) := by dec_rfl

/-- What the stretch does. -/
def o2 : List Op := [
  Op.xor 32 0 (.r 0),
  Op.sti 32 (some 7) none 1 8 0,
  Op.ld 32 6 (some 7) none 1 16]

theorem b2 (prof : Profile) : Blk prof p2 0 12 o2 :=
  .cons (p2_0 _) (OpI.xor (.r 0) (.inl rfl)) (by decide) <|
  .cons (p2_2 _) (OpI.sti (.inr (.inr (.inl rfl)))) (by decide) <|
  .cons (p2_9 _) (OpI.ld (.inl rfl)) (by decide) <|
  .nil 12

/-- The stretch at `45`. -/
def p3 : List Byte := [
  0x83, 0xf8, 0x01]

theorem p3_0 : ∀ feat, Dec feat p3 0 (FV7z.mk .cmp 32 [gr 32 0, Src.opd 32 (.i 1)] 3) := by dec_rfl

/-- What the stretch does. -/
def o3 : List Op := [
  Op.cmp 32 0 (.i 1)]

theorem b3 (prof : Profile) : Blk prof p3 0 3 o3 :=
  .cons (p3_0 _) (OpI.cmp (.i 1) (.inl rfl)) (by decide) <|
  .nil 3

def j2 : List Byte := [0x7f, 0x3e]
theorem j2_0 : ∀ feat, Dec feat j2 0 (FV7z.mk (.jcc 15) 64 [.rel 62] 2) := by dec_rfl

/-- The stretch at `50`. -/
def p4 : List Byte := [
  0x90, 0x44, 0x89, 0xc0]

theorem p4_0 : ∀ feat, Dec feat p4 0 (FV7z.mk .nop 32 [] 1) := by dec_rfl
theorem p4_1 : ∀ feat, Dec feat p4 1 (FV7z.mk .mov 32 [gr 32 0, Src.opd 32 (.r 8)] 3) := by dec_rfl

/-- What the stretch does. -/
def o4 : List Op := [
  Op.nop,
  Op.mov 32 0 (.r 8)]

theorem b4 (prof : Profile) : Blk prof p4 0 4 o4 :=
  .cons (p4_0 _) (OpI.nop) (by decide) <|
  .cons (p4_1 _) (OpI.mov (.r 8) (.inl rfl)) (by decide) <|
  .nil 4

end FV7z.Pmu
