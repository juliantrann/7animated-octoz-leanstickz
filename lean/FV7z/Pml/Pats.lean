import FV7z.Lemmas.SpFs
import FV7z.Lemmas.BlkOps2
/-!
# The stretches of straight-line code of `pthread_mutex_lock` (PLAN.md G3, pthread)

Each distinct stretch between labels and jumps (`p*`, 8 of them) and each distinct jump (`j*`, 5) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.Pml
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The stretch at `0`. -/
def p0 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0x8b, 0x47, 0x10, 0x89, 0xc2, 0x81, 0xe2, 0x7f, 0x01, 0x00, 0x00, 0x90,
  0x83, 0xe0, 0x7c]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem p0_4 : ∀ feat, Dec feat p0 4 (FV7z.mk .mov 32 [gr 32 0, .mem (mg (some 7) none 1 16 32)] 3) := by dec_rfl
theorem p0_7 : ∀ feat, Dec feat p0 7 (FV7z.mk .mov 32 [gr 32 2, Src.opd 32 (.r 0)] 2) := by dec_rfl
theorem p0_9 : ∀ feat, Dec feat p0 9 (FV7z.mk .and 32 [gr 32 2, Src.opd 32 (.i 383)] 6) := by dec_rfl
theorem p0_15 : ∀ feat, Dec feat p0 15 (FV7z.mk .nop 32 [] 1) := by dec_rfl
theorem p0_16 : ∀ feat, Dec feat p0 16 (FV7z.mk .and 32 [gr 32 0, Src.opd 32 (.i 124)] 3) := by dec_rfl

/-- What the stretch does. -/
def o0 : List Op := [
  Op.nop,
  Op.ld 32 0 (some 7) none 1 16,
  Op.mov 32 2 (.r 0),
  Op.and 32 2 (.i 383),
  Op.nop,
  Op.and 32 0 (.i 124)]

theorem b0 (prof : Profile) : Blk prof p0 0 19 o0 :=
  .cons (p0_0 _) (OpI.endbr) (by decide) <|
  .cons (p0_4 _) (OpI.ld (.inl rfl)) (by decide) <|
  .cons (p0_7 _) (OpI.mov (.r 0) (.inl rfl)) (by decide) <|
  .cons (p0_9 _) (OpI.and (.i 383) (.inl rfl)) (by decide) <|
  .cons (p0_15 _) (OpI.nop) (by decide) <|
  .cons (p0_16 _) (OpI.and (.i 124) (.inl rfl)) (by decide) <|
  .nil 19

def j0 : List Byte := [0x75, 0x7b]
theorem j0_0 : ∀ feat, Dec feat j0 0 (FV7z.mk (.jcc 5) 64 [.rel 123] 2) := by dec_rfl

/-- The stretch at `21`. -/
def p1 : List Byte := [
  0x53, 0x48, 0x83, 0xec, 0x10, 0x85, 0xd2]

theorem p1_0 : ∀ feat, Dec feat p1 0 (FV7z.mk .push 64 [gr 64 3] 1) := by dec_rfl
theorem p1_1 : ∀ feat, Dec feat p1 1 (FV7z.mk .sub 64 [gr 64 4, Src.opd 64 (.i 16)] 4) := by dec_rfl
theorem p1_5 : ∀ feat, Dec feat p1 5 (FV7z.mk .test 32 [gr 32 2, Src.opd 32 (.r 2)] 2) := by dec_rfl

/-- What the stretch does. -/
def o1 : List Op := [
  Op.push 3,
  Op.sub 64 4 (.i 16),
  Op.test 32 2 (.r 2)]

theorem b1 (prof : Profile) : Blk prof p1 0 7 o1 :=
  .cons (p1_0 _) (OpI.push) (by decide) <|
  .cons (p1_1 _) (OpI.sub (.i 16) (.inr rfl)) (by decide) <|
  .cons (p1_5 _) (OpI.test (.r 2) (.inl rfl)) (by decide) <|
  .nil 7

def j1 : List Byte := [0x75, 0x7a]
theorem j1_0 : ∀ feat, Dec feat j1 0 (FV7z.mk (.jcc 5) 64 [.rel 122] 2) := by dec_rfl

/-- The stretch at `30`. -/
def p2 : List Byte := [
  0x8b, 0x0d, 0xd8, 0x2c, 0x1a, 0x00, 0x85, 0xc9]

theorem p2_0 : ∀ feat, Dec feat p2 0 (FV7z.mk .mov 32 [gr 32 1, .mem (mrip 1715416 32)] 6) := by dec_rfl
theorem p2_6 : ∀ feat, Dec feat p2 6 (FV7z.mk .test 32 [gr 32 1, Src.opd 32 (.r 1)] 2) := by dec_rfl

/-- What the stretch does. -/
def o2 : List Op := [
  Op.lda 32 1 7991628,
  Op.test 32 1 (.r 1)]

theorem b2 (prof : Profile) : BlkA prof p2 (0x5fc46e : Addr) 0 8 o2 :=
  .cons (p2_0 _) (OpIA.ld_rip (.inl rfl) (by decide)) (by decide) <|
  .cons (p2_6 _) ((OpI.test (.r 1) (.inl rfl)).at _) (by decide) <|
  .nil 8

def j2 : List Byte := [0x75, 0x38]
theorem j2_0 : ∀ feat, Dec feat j2 0 (FV7z.mk (.jcc 5) 64 [.rel 56] 2) := by dec_rfl

/-- The stretch at `40`. -/
def p3 : List Byte := [
  0x31, 0xc0, 0xba, 0x01, 0x00, 0x00, 0x00]

theorem p3_0 : ∀ feat, Dec feat p3 0 (FV7z.mk .xor 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl
theorem p3_2 : ∀ feat, Dec feat p3 2 (FV7z.mk .mov 32 [gr 32 2, Src.opd 32 (.i 1)] 5) := by dec_rfl

/-- What the stretch does. -/
def o3 : List Op := [
  Op.xor 32 0 (.r 0),
  Op.mov 32 2 (.i 1)]

theorem b3 (prof : Profile) : Blk prof p3 0 7 o3 :=
  .cons (p3_0 _) (OpI.xor (.r 0) (.inl rfl)) (by decide) <|
  .cons (p3_2 _) (OpI.mov (.i 1) (.inl rfl)) (by decide) <|
  .nil 7

def j3 : List Byte := [0x0f, 0x85, 0x97, 0x00, 0x00, 0x00]
theorem j3_0 : ∀ feat, Dec feat j3 0 (FV7z.mk (.jcc 5) 64 [.rel 151] 6) := by dec_rfl

/-- The stretch at `57`. -/
def p4 : List Byte := [
  0x8b, 0x57, 0x08, 0x85, 0xd2]

theorem p4_0 : ∀ feat, Dec feat p4 0 (FV7z.mk .mov 32 [gr 32 2, .mem (mg (some 7) none 1 8 32)] 3) := by dec_rfl
theorem p4_3 : ∀ feat, Dec feat p4 3 (FV7z.mk .test 32 [gr 32 2, Src.opd 32 (.r 2)] 2) := by dec_rfl

/-- What the stretch does. -/
def o4 : List Op := [
  Op.ld 32 2 (some 7) none 1 8,
  Op.test 32 2 (.r 2)]

theorem b4 (prof : Profile) : Blk prof p4 0 5 o4 :=
  .cons (p4_0 _) (OpI.ld (.inl rfl)) (by decide) <|
  .cons (p4_3 _) (OpI.test (.r 2) (.inl rfl)) (by decide) <|
  .nil 5

def j4 : List Byte := [0x0f, 0x85, 0x41, 0x01, 0x00, 0x00]
theorem j4_0 : ∀ feat, Dec feat j4 0 (FV7z.mk (.jcc 5) 64 [.rel 321] 6) := by dec_rfl

/-- The stretch at `68`. -/
def p5 : List Byte := [
  0x64, 0x8b, 0x04, 0x25, 0xd0, 0x02, 0x00, 0x00, 0x89, 0x47, 0x08]

theorem p5_0 : ∀ feat, Dec feat p5 0 (FV7z.mk .mov 32 [gr 32 0, .mem (mf none none 1 720 32)] 8) := by dec_rfl
theorem p5_8 : ∀ feat, Dec feat p5 8 (FV7z.mk .mov 32 [.mem (mg (some 7) none 1 8 32), gr 32 0] 3) := by dec_rfl

/-- What the stretch does. -/
def o5 (fb : Addr) : List Op := [
  Op.ldf fb 32 0 none none 1 720,
  Op.st 32 (some 7) none 1 8 0]

theorem b5 (prof : Profile) (fb : Addr) : BlkF prof p5 (0x5fc494 : Addr) fb 0 11 (o5 fb) :=
  .cons (p5_0 _) (OpIF.ldf (.inl rfl)) (by decide) <|
  .cons (p5_8 _) (((OpI.st (.inr (.inr (.inl rfl)))).at _).fs _) (by decide) <|
  .nil 11

/-- The stretch at `83`. -/
def p6 : List Byte := [
  0x90, 0x31, 0xc0]

theorem p6_0 : ∀ feat, Dec feat p6 0 (FV7z.mk .nop 32 [] 1) := by dec_rfl
theorem p6_1 : ∀ feat, Dec feat p6 1 (FV7z.mk .xor 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl

/-- What the stretch does. -/
def o6 : List Op := [
  Op.nop,
  Op.xor 32 0 (.r 0)]

theorem b6 (prof : Profile) : Blk prof p6 0 3 o6 :=
  .cons (p6_0 _) (OpI.nop) (by decide) <|
  .cons (p6_1 _) (OpI.xor (.r 0) (.inl rfl)) (by decide) <|
  .nil 3

/-- The stretch at `86`. -/
def p7 : List Byte := [
  0x48, 0x83, 0xc4, 0x10, 0x5b]

theorem p7_0 : ∀ feat, Dec feat p7 0 (FV7z.mk .add 64 [gr 64 4, Src.opd 64 (.i 16)] 4) := by dec_rfl
theorem p7_4 : ∀ feat, Dec feat p7 4 (FV7z.mk .pop 64 [gr 64 3] 1) := by dec_rfl

/-- What the stretch does. -/
def o7 : List Op := [
  Op.add 64 4 (.i 16),
  Op.pop 3]

theorem b7 (prof : Profile) : Blk prof p7 0 5 o7 :=
  .cons (p7_0 _) (OpI.add (.i 16) (.inr rfl)) (by decide) <|
  .cons (p7_4 _) (OpI.pop) (by decide) <|
  .nil 5

end FV7z.Pml
