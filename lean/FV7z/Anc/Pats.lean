import FV7z.Lemmas.SpFs
import FV7z.Lemmas.BlkOps6
import FV7z.Lemmas.BlkOps2
/-!
# The stretches of straight-line code of `AddNameToCensor` (PLAN.md §M, M1)

Each distinct stretch between labels and jumps (`p*`, 6 of them) and each distinct jump (`j*`, 3) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.Anc
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The stretch at `0`. -/
def p0 : List Byte := [
  0x41, 0x54, 0x49, 0x89, 0xd4, 0x55, 0x48, 0x89, 0xfd, 0x53, 0x48, 0x89, 0xf3, 0x48, 0x83, 0xec,
  0x10, 0x8b, 0x56, 0x04, 0x64, 0x48, 0x8b, 0x04, 0x25, 0x28, 0x00, 0x00, 0x00, 0x48, 0x89, 0x44,
  0x24, 0x08, 0x31, 0xc0, 0xb8, 0x01, 0x00, 0x00, 0x00, 0x85, 0xd2]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .push 64 [gr 64 12] 2) := by dec_rfl
theorem p0_2 : ∀ feat, Dec feat p0 2 (FV7z.mk .mov 64 [gr 64 12, Src.opd 64 (.r 2)] 3) := by dec_rfl
theorem p0_5 : ∀ feat, Dec feat p0 5 (FV7z.mk .push 64 [gr 64 5] 1) := by dec_rfl
theorem p0_6 : ∀ feat, Dec feat p0 6 (FV7z.mk .mov 64 [gr 64 5, Src.opd 64 (.r 7)] 3) := by dec_rfl
theorem p0_9 : ∀ feat, Dec feat p0 9 (FV7z.mk .push 64 [gr 64 3] 1) := by dec_rfl
theorem p0_10 : ∀ feat, Dec feat p0 10 (FV7z.mk .mov 64 [gr 64 3, Src.opd 64 (.r 6)] 3) := by dec_rfl
theorem p0_13 : ∀ feat, Dec feat p0 13 (FV7z.mk .sub 64 [gr 64 4, Src.opd 64 (.i 16)] 4) := by dec_rfl
theorem p0_17 : ∀ feat, Dec feat p0 17 (FV7z.mk .mov 32 [gr 32 2, .mem (mg (some 6) none 1 4 32)] 3) := by dec_rfl
theorem p0_20 : ∀ feat, Dec feat p0 20 (FV7z.mk .mov 64 [gr 64 0, .mem (mf none none 1 40 64)] 9) := by dec_rfl
theorem p0_29 : ∀ feat, Dec feat p0 29 (FV7z.mk .mov 64 [.mem (mg (some 4) none 1 8 64), gr 64 0] 5) := by dec_rfl
theorem p0_34 : ∀ feat, Dec feat p0 34 (FV7z.mk .xor 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl
theorem p0_36 : ∀ feat, Dec feat p0 36 (FV7z.mk .mov 32 [gr 32 0, Src.opd 32 (.i 1)] 5) := by dec_rfl
theorem p0_41 : ∀ feat, Dec feat p0 41 (FV7z.mk .test 32 [gr 32 2, Src.opd 32 (.r 2)] 2) := by dec_rfl

/-- What the stretch does. -/
def o0 (fb : Addr) : List Op := [
  Op.push 12,
  Op.mov 64 12 (.r 2),
  Op.push 5,
  Op.mov 64 5 (.r 7),
  Op.push 3,
  Op.mov 64 3 (.r 6),
  Op.sub 64 4 (.i 16),
  Op.ld 32 2 (some 6) none 1 4,
  Op.ldf fb 64 0 none none 1 40,
  Op.st 64 (some 4) none 1 8 0,
  Op.xor 32 0 (.r 0),
  Op.mov 32 0 (.i 1),
  Op.test 32 2 (.r 2)]

theorem b0 (prof : Profile) (fb : Addr) : BlkF prof p0 (0x5a66e0 : Addr) fb 0 43 (o0 fb) :=
  .cons (p0_0 _) (((OpI.push).at _).fs _) (by decide) <|
  .cons (p0_2 _) (((OpI.mov (.r 2) (.inr rfl)).at _).fs _) (by decide) <|
  .cons (p0_5 _) (((OpI.push).at _).fs _) (by decide) <|
  .cons (p0_6 _) (((OpI.mov (.r 7) (.inr rfl)).at _).fs _) (by decide) <|
  .cons (p0_9 _) (((OpI.push).at _).fs _) (by decide) <|
  .cons (p0_10 _) (((OpI.mov (.r 6) (.inr rfl)).at _).fs _) (by decide) <|
  .cons (p0_13 _) (((OpI.sub (.i 16) (.inr rfl)).at _).fs _) (by decide) <|
  .cons (p0_17 _) (((OpI.ld (.inl rfl)).at _).fs _) (by decide) <|
  .cons (p0_20 _) (OpIF.ldf (.inr rfl)) (by decide) <|
  .cons (p0_29 _) (((OpI.st (.inr (.inr (.inr rfl)))).at _).fs _) (by decide) <|
  .cons (p0_34 _) (((OpI.xor (.r 0) (.inl rfl)).at _).fs _) (by decide) <|
  .cons (p0_36 _) (((OpI.mov (.i 1) (.inl rfl)).at _).fs _) (by decide) <|
  .cons (p0_41 _) (((OpI.test (.r 2) (.inl rfl)).at _).fs _) (by decide) <|
  .nil 43

def j0 : List Byte := [0x74, 0x0f]
theorem j0_0 : ∀ feat, Dec feat j0 0 (FV7z.mk (.jcc 4) 64 [.rel 15] 2) := by dec_rfl

/-- The stretch at `45`. -/
def p1 : List Byte := [
  0x31, 0xc0, 0x83, 0xfa, 0x01]

theorem p1_0 : ∀ feat, Dec feat p1 0 (FV7z.mk .xor 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl
theorem p1_2 : ∀ feat, Dec feat p1 2 (FV7z.mk .cmp 32 [gr 32 2, Src.opd 32 (.i 1)] 3) := by dec_rfl

/-- What the stretch does. -/
def o1 : List Op := [
  Op.xor 32 0 (.r 0),
  Op.cmp 32 2 (.i 1)]

theorem b1 (prof : Profile) : Blk prof p1 0 5 o1 :=
  .cons (p1_0 _) (OpI.xor (.r 0) (.inl rfl)) (by decide) <|
  .cons (p1_2 _) (OpI.cmp (.i 1) (.inl rfl)) (by decide) <|
  .nil 5

def j1 : List Byte := [0x75, 0x08]
theorem j1_0 : ∀ feat, Dec feat j1 0 (FV7z.mk (.jcc 5) 64 [.rel 8] 2) := by dec_rfl

/-- The stretch at `52`. -/
def p2 : List Byte := [
  0x4c, 0x89, 0xe7]

theorem p2_0 : ∀ feat, Dec feat p2 0 (FV7z.mk .mov 64 [gr 64 7, Src.opd 64 (.r 12)] 3) := by dec_rfl

/-- What the stretch does. -/
def o2 : List Op := [
  Op.mov 64 7 (.r 12)]

theorem b2 (prof : Profile) : Blk prof p2 0 3 o2 :=
  .cons (p2_0 _) (OpI.mov (.r 12) (.inr rfl)) (by decide) <|
  .nil 3

/-- The stretch at `60`. -/
def p3 : List Byte := [
  0x88, 0x44, 0x24, 0x05, 0x0f, 0xb6, 0x33, 0x48, 0x8d, 0x4c, 0x24, 0x05, 0x4c, 0x89, 0xe2, 0x0f,
  0xb7, 0x43, 0x01, 0x48, 0x89, 0xef, 0x66, 0x89, 0x44, 0x24, 0x06]

theorem p3_0 : ∀ feat, Dec feat p3 0 (FV7z.mk .mov 8 [.mem (mg (some 4) none 1 5 8), gr 8 0] 4) := by dec_rfl
theorem p3_4 : ∀ feat, Dec feat p3 4 (FV7z.mk .movzx 32 [gr 32 6, .mem (mg (some 3) none 1 0 8)] 3) := by dec_rfl
theorem p3_7 : ∀ feat, Dec feat p3 7 (FV7z.mk .lea 64 [gr 64 1, .mem (mg (some 4) none 1 5 0)] 5) := by dec_rfl
theorem p3_12 : ∀ feat, Dec feat p3 12 (FV7z.mk .mov 64 [gr 64 2, Src.opd 64 (.r 12)] 3) := by dec_rfl
theorem p3_15 : ∀ feat, Dec feat p3 15 (FV7z.mk .movzx 32 [gr 32 0, .mem (mg (some 3) none 1 1 16)] 4) := by dec_rfl
theorem p3_19 : ∀ feat, Dec feat p3 19 (FV7z.mk .mov 64 [gr 64 7, Src.opd 64 (.r 5)] 3) := by dec_rfl
theorem p3_22 : ∀ feat, Dec feat p3 22 (FV7z.mk .mov 16 [.mem (mg (some 4) none 1 6 16), gr 16 0] 5) := by dec_rfl

/-- What the stretch does. -/
def o3 : List Op := [
  Op.st 8 (some 4) none 1 5 0,
  Op.ldzx 8 6 (some 3) none 1 0,
  Op.lea 64 1 (some 4) none 1 5,
  Op.mov 64 2 (.r 12),
  Op.ldzx 16 0 (some 3) none 1 1,
  Op.mov 64 7 (.r 5),
  Op.st 16 (some 4) none 1 6 0]

theorem b3 (prof : Profile) : Blk prof p3 0 27 o3 :=
  .cons (p3_0 _) (OpI.st (.inl rfl)) (by decide) <|
  .cons (p3_4 _) (OpI.ldzx (.inl rfl)) (by decide) <|
  .cons (p3_7 _) (OpI.lea (.inr rfl)) (by decide) <|
  .cons (p3_12 _) (OpI.mov (.r 12) (.inr rfl)) (by decide) <|
  .cons (p3_15 _) (OpI.ldzx (.inr rfl)) (by decide) <|
  .cons (p3_19 _) (OpI.mov (.r 5) (.inr rfl)) (by decide) <|
  .cons (p3_22 _) (OpI.st (.inr (.inl rfl))) (by decide) <|
  .nil 27

/-- The stretch at `92`. -/
def p4 : List Byte := [
  0x48, 0x8b, 0x44, 0x24, 0x08, 0x64, 0x48, 0x33, 0x04, 0x25, 0x28, 0x00, 0x00, 0x00]

theorem p4_0 : ∀ feat, Dec feat p4 0 (FV7z.mk .mov 64 [gr 64 0, .mem (mg (some 4) none 1 8 64)] 5) := by dec_rfl
theorem p4_5 : ∀ feat, Dec feat p4 5 (FV7z.mk .xor 64 [gr 64 0, .mem (mf none none 1 40 64)] 9) := by dec_rfl

/-- What the stretch does. -/
def o4 (fb : Addr) : List Op := [
  Op.ld 64 0 (some 4) none 1 8,
  Op.xormf fb 64 0 none none 1 40]

theorem b4 (prof : Profile) (fb : Addr) : BlkF prof p4 (0x5a673c : Addr) fb 0 14 (o4 fb) :=
  .cons (p4_0 _) (((OpI.ld (.inr rfl)).at _).fs _) (by decide) <|
  .cons (p4_5 _) (OpIF.xormf (.inr rfl)) (by decide) <|
  .nil 14

def j2 : List Byte := [0x75, 0x09]
theorem j2_0 : ∀ feat, Dec feat j2 0 (FV7z.mk (.jcc 5) 64 [.rel 9] 2) := by dec_rfl

/-- The stretch at `108`. -/
def p5 : List Byte := [
  0x48, 0x83, 0xc4, 0x10, 0x5b, 0x5d, 0x41, 0x5c]

theorem p5_0 : ∀ feat, Dec feat p5 0 (FV7z.mk .add 64 [gr 64 4, Src.opd 64 (.i 16)] 4) := by dec_rfl
theorem p5_4 : ∀ feat, Dec feat p5 4 (FV7z.mk .pop 64 [gr 64 3] 1) := by dec_rfl
theorem p5_5 : ∀ feat, Dec feat p5 5 (FV7z.mk .pop 64 [gr 64 5] 1) := by dec_rfl
theorem p5_6 : ∀ feat, Dec feat p5 6 (FV7z.mk .pop 64 [gr 64 12] 2) := by dec_rfl

/-- What the stretch does. -/
def o5 : List Op := [
  Op.add 64 4 (.i 16),
  Op.pop 3,
  Op.pop 5,
  Op.pop 12]

theorem b5 (prof : Profile) : Blk prof p5 0 8 o5 :=
  .cons (p5_0 _) (OpI.add (.i 16) (.inr rfl)) (by decide) <|
  .cons (p5_4 _) (OpI.pop) (by decide) <|
  .cons (p5_5 _) (OpI.pop) (by decide) <|
  .cons (p5_6 _) (OpI.pop) (by decide) <|
  .nil 8

end FV7z.Anc
