import FV7z.Lemmas.SpFs
import FV7z.Lemmas.BlkOps6
import FV7z.Lemmas.BlkOps2
/-!
# The stretches of straight-line code of `CDummyOutStream::Write` (PLAN.md §M, M1)

Each distinct stretch between labels and jumps (`p*`, 8 of them) and each distinct jump (`j*`, 3) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.Dow
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The stretch at `0`. -/
def p0 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0x55, 0x48, 0x89, 0xcd, 0x53, 0x48, 0x89, 0xfb, 0x48, 0x83, 0xec, 0x18,
  0x48, 0x8b, 0x7f, 0x10, 0x64, 0x48, 0x8b, 0x04, 0x25, 0x28, 0x00, 0x00, 0x00, 0x48, 0x89, 0x44,
  0x24, 0x08, 0x31, 0xc0, 0x89, 0x54, 0x24, 0x04, 0x48, 0x85, 0xff]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem p0_4 : ∀ feat, Dec feat p0 4 (FV7z.mk .push 64 [gr 64 5] 1) := by dec_rfl
theorem p0_5 : ∀ feat, Dec feat p0 5 (FV7z.mk .mov 64 [gr 64 5, Src.opd 64 (.r 1)] 3) := by dec_rfl
theorem p0_8 : ∀ feat, Dec feat p0 8 (FV7z.mk .push 64 [gr 64 3] 1) := by dec_rfl
theorem p0_9 : ∀ feat, Dec feat p0 9 (FV7z.mk .mov 64 [gr 64 3, Src.opd 64 (.r 7)] 3) := by dec_rfl
theorem p0_12 : ∀ feat, Dec feat p0 12 (FV7z.mk .sub 64 [gr 64 4, Src.opd 64 (.i 24)] 4) := by dec_rfl
theorem p0_16 : ∀ feat, Dec feat p0 16 (FV7z.mk .mov 64 [gr 64 7, .mem (mg (some 7) none 1 16 64)] 4) := by dec_rfl
theorem p0_20 : ∀ feat, Dec feat p0 20 (FV7z.mk .mov 64 [gr 64 0, .mem (mf none none 1 40 64)] 9) := by dec_rfl
theorem p0_29 : ∀ feat, Dec feat p0 29 (FV7z.mk .mov 64 [.mem (mg (some 4) none 1 8 64), gr 64 0] 5) := by dec_rfl
theorem p0_34 : ∀ feat, Dec feat p0 34 (FV7z.mk .xor 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl
theorem p0_36 : ∀ feat, Dec feat p0 36 (FV7z.mk .mov 32 [.mem (mg (some 4) none 1 4 32), gr 32 2] 4) := by dec_rfl
theorem p0_40 : ∀ feat, Dec feat p0 40 (FV7z.mk .test 64 [gr 64 7, Src.opd 64 (.r 7)] 3) := by dec_rfl

/-- What the stretch does. -/
def o0 (fb : Addr) : List Op := [
  Op.nop,
  Op.push 5,
  Op.mov 64 5 (.r 1),
  Op.push 3,
  Op.mov 64 3 (.r 7),
  Op.sub 64 4 (.i 24),
  Op.ld 64 7 (some 7) none 1 16,
  Op.ldf fb 64 0 none none 1 40,
  Op.st 64 (some 4) none 1 8 0,
  Op.xor 32 0 (.r 0),
  Op.st 32 (some 4) none 1 4 2,
  Op.test 64 7 (.r 7)]

theorem b0 (prof : Profile) (fb : Addr) : BlkF prof p0 (0x4e2470 : Addr) fb 0 43 (o0 fb) :=
  .cons (p0_0 _) (((OpI.endbr).at _).fs _) (by decide) <|
  .cons (p0_4 _) (((OpI.push).at _).fs _) (by decide) <|
  .cons (p0_5 _) (((OpI.mov (.r 1) (.inr rfl)).at _).fs _) (by decide) <|
  .cons (p0_8 _) (((OpI.push).at _).fs _) (by decide) <|
  .cons (p0_9 _) (((OpI.mov (.r 7) (.inr rfl)).at _).fs _) (by decide) <|
  .cons (p0_12 _) (((OpI.sub (.i 24) (.inr rfl)).at _).fs _) (by decide) <|
  .cons (p0_16 _) (((OpI.ld (.inr rfl)).at _).fs _) (by decide) <|
  .cons (p0_20 _) (OpIF.ldf (.inr rfl)) (by decide) <|
  .cons (p0_29 _) (((OpI.st (.inr (.inr (.inr rfl)))).at _).fs _) (by decide) <|
  .cons (p0_34 _) (((OpI.xor (.r 0) (.inl rfl)).at _).fs _) (by decide) <|
  .cons (p0_36 _) (((OpI.st (.inr (.inr (.inl rfl)))).at _).fs _) (by decide) <|
  .cons (p0_40 _) (((OpI.test (.r 7) (.inr rfl)).at _).fs _) (by decide) <|
  .nil 43

def j0 : List Byte := [0x74, 0x0f]
theorem j0_0 : ∀ feat, Dec feat j0 0 (FV7z.mk (.jcc 4) 64 [.rel 15] 2) := by dec_rfl

/-- The stretch at `45`. -/
def p1 : List Byte := [
  0x48, 0x8b, 0x07, 0x48, 0x8d, 0x4c, 0x24, 0x04]

theorem p1_0 : ∀ feat, Dec feat p1 0 (FV7z.mk .mov 64 [gr 64 0, .mem (mg (some 7) none 1 0 64)] 3) := by dec_rfl
theorem p1_3 : ∀ feat, Dec feat p1 3 (FV7z.mk .lea 64 [gr 64 1, .mem (mg (some 4) none 1 4 0)] 5) := by dec_rfl

/-- What the stretch does. -/
def o1 : List Op := [
  Op.ld 64 0 (some 7) none 1 0,
  Op.lea 64 1 (some 4) none 1 4]

theorem b1 (prof : Profile) : Blk prof p1 0 8 o1 :=
  .cons (p1_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p1_3 _) (OpI.lea (.inr rfl)) (by decide) <|
  .nil 8

/-- The stretch at `56`. -/
def p2 : List Byte := [
  0x8b, 0x54, 0x24, 0x04]

theorem p2_0 : ∀ feat, Dec feat p2 0 (FV7z.mk .mov 32 [gr 32 2, .mem (mg (some 4) none 1 4 32)] 4) := by dec_rfl

/-- What the stretch does. -/
def o2 : List Op := [
  Op.ld 32 2 (some 4) none 1 4]

theorem b2 (prof : Profile) : Blk prof p2 0 4 o2 :=
  .cons (p2_0 _) (OpI.ld (.inl rfl)) (by decide) <|
  .nil 4

/-- The stretch at `60`. -/
def p3 : List Byte := [
  0x89, 0xd1]

theorem p3_0 : ∀ feat, Dec feat p3 0 (FV7z.mk .mov 32 [gr 32 1, Src.opd 32 (.r 2)] 2) := by dec_rfl

/-- What the stretch does. -/
def o3 : List Op := [
  Op.mov 32 1 (.r 2)]

theorem b3 (prof : Profile) : Blk prof p3 0 2 o3 :=
  .cons (p3_0 _) (OpI.mov (.r 2) (.inl rfl)) (by decide) <|
  .nil 2

/-- The stretch at `66`. -/
def p4 : List Byte := [
  0x48, 0x85, 0xed]

theorem p4_0 : ∀ feat, Dec feat p4 0 (FV7z.mk .test 64 [gr 64 5, Src.opd 64 (.r 5)] 3) := by dec_rfl

/-- What the stretch does. -/
def o4 : List Op := [
  Op.test 64 5 (.r 5)]

theorem b4 (prof : Profile) : Blk prof p4 0 3 o4 :=
  .cons (p4_0 _) (OpI.test (.r 5) (.inr rfl)) (by decide) <|
  .nil 3

def j1 : List Byte := [0x74, 0x03]
theorem j1_0 : ∀ feat, Dec feat j1 0 (FV7z.mk (.jcc 4) 64 [.rel 3] 2) := by dec_rfl

/-- The stretch at `71`. -/
def p5 : List Byte := [
  0x89, 0x55, 0x00]

theorem p5_0 : ∀ feat, Dec feat p5 0 (FV7z.mk .mov 32 [.mem (mg (some 5) none 1 0 32), gr 32 2] 3) := by dec_rfl

/-- What the stretch does. -/
def o5 : List Op := [
  Op.st 32 (some 5) none 1 0 2]

theorem b5 (prof : Profile) : Blk prof p5 0 3 o5 :=
  .cons (p5_0 _) (OpI.st (.inr (.inr (.inl rfl)))) (by decide) <|
  .nil 3

/-- The stretch at `74`. -/
def p6 : List Byte := [
  0x48, 0x8b, 0x5c, 0x24, 0x08, 0x64, 0x48, 0x33, 0x1c, 0x25, 0x28, 0x00, 0x00, 0x00]

theorem p6_0 : ∀ feat, Dec feat p6 0 (FV7z.mk .mov 64 [gr 64 3, .mem (mg (some 4) none 1 8 64)] 5) := by dec_rfl
theorem p6_5 : ∀ feat, Dec feat p6 5 (FV7z.mk .xor 64 [gr 64 3, .mem (mf none none 1 40 64)] 9) := by dec_rfl

/-- What the stretch does. -/
def o6 (fb : Addr) : List Op := [
  Op.ld 64 3 (some 4) none 1 8,
  Op.xormf fb 64 3 none none 1 40]

theorem b6 (prof : Profile) (fb : Addr) : BlkF prof p6 (0x4e24ba : Addr) fb 0 14 (o6 fb) :=
  .cons (p6_0 _) (((OpI.ld (.inr rfl)).at _).fs _) (by decide) <|
  .cons (p6_5 _) (OpIF.xormf (.inr rfl)) (by decide) <|
  .nil 14

def j2 : List Byte := [0x75, 0x07]
theorem j2_0 : ∀ feat, Dec feat j2 0 (FV7z.mk (.jcc 5) 64 [.rel 7] 2) := by dec_rfl

/-- The stretch at `90`. -/
def p7 : List Byte := [
  0x48, 0x83, 0xc4, 0x18, 0x5b, 0x5d]

theorem p7_0 : ∀ feat, Dec feat p7 0 (FV7z.mk .add 64 [gr 64 4, Src.opd 64 (.i 24)] 4) := by dec_rfl
theorem p7_4 : ∀ feat, Dec feat p7 4 (FV7z.mk .pop 64 [gr 64 3] 1) := by dec_rfl
theorem p7_5 : ∀ feat, Dec feat p7 5 (FV7z.mk .pop 64 [gr 64 5] 1) := by dec_rfl

/-- What the stretch does. -/
def o7 : List Op := [
  Op.add 64 4 (.i 24),
  Op.pop 3,
  Op.pop 5]

theorem b7 (prof : Profile) : Blk prof p7 0 6 o7 :=
  .cons (p7_0 _) (OpI.add (.i 24) (.inr rfl)) (by decide) <|
  .cons (p7_4 _) (OpI.pop) (by decide) <|
  .cons (p7_5 _) (OpI.pop) (by decide) <|
  .nil 6

end FV7z.Dow
