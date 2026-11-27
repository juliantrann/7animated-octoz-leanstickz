import FV7z.Lemmas.SpFs
import FV7z.Lemmas.BlkOps6
import FV7z.Lemmas.BlkOps2
/-!
# The stretches of straight-line code of `LzmaDec_AllocateProbs` (PLAN.md §M, M1)

Each distinct stretch between labels and jumps (`p*`, 6 of them) and each distinct jump (`j*`, 4) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.Lpb
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The stretch at `0`. -/
def p0 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0x41, 0x54, 0x49, 0x89, 0xcc, 0x53, 0x48, 0x89, 0xfb, 0x48, 0x83, 0xec,
  0x18, 0x64, 0x48, 0x8b, 0x04, 0x25, 0x28, 0x00, 0x00, 0x00, 0x48, 0x89, 0x44, 0x24, 0x08, 0x31,
  0xc0, 0x48, 0x89, 0xe7]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem p0_4 : ∀ feat, Dec feat p0 4 (FV7z.mk .push 64 [gr 64 12] 2) := by dec_rfl
theorem p0_6 : ∀ feat, Dec feat p0 6 (FV7z.mk .mov 64 [gr 64 12, Src.opd 64 (.r 1)] 3) := by dec_rfl
theorem p0_9 : ∀ feat, Dec feat p0 9 (FV7z.mk .push 64 [gr 64 3] 1) := by dec_rfl
theorem p0_10 : ∀ feat, Dec feat p0 10 (FV7z.mk .mov 64 [gr 64 3, Src.opd 64 (.r 7)] 3) := by dec_rfl
theorem p0_13 : ∀ feat, Dec feat p0 13 (FV7z.mk .sub 64 [gr 64 4, Src.opd 64 (.i 24)] 4) := by dec_rfl
theorem p0_17 : ∀ feat, Dec feat p0 17 (FV7z.mk .mov 64 [gr 64 0, .mem (mf none none 1 40 64)] 9) := by dec_rfl
theorem p0_26 : ∀ feat, Dec feat p0 26 (FV7z.mk .mov 64 [.mem (mg (some 4) none 1 8 64), gr 64 0] 5) := by dec_rfl
theorem p0_31 : ∀ feat, Dec feat p0 31 (FV7z.mk .xor 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl
theorem p0_33 : ∀ feat, Dec feat p0 33 (FV7z.mk .mov 64 [gr 64 7, Src.opd 64 (.r 4)] 3) := by dec_rfl

/-- What the stretch does. -/
def o0 (fb : Addr) : List Op := [
  Op.nop,
  Op.push 12,
  Op.mov 64 12 (.r 1),
  Op.push 3,
  Op.mov 64 3 (.r 7),
  Op.sub 64 4 (.i 24),
  Op.ldf fb 64 0 none none 1 40,
  Op.st 64 (some 4) none 1 8 0,
  Op.xor 32 0 (.r 0),
  Op.mov 64 7 (.r 4)]

theorem b0 (prof : Profile) (fb : Addr) : BlkF prof p0 (0x42bf10 : Addr) fb 0 36 (o0 fb) :=
  .cons (p0_0 _) (((OpI.endbr).at _).fs _) (by decide) <|
  .cons (p0_4 _) (((OpI.push).at _).fs _) (by decide) <|
  .cons (p0_6 _) (((OpI.mov (.r 1) (.inr rfl)).at _).fs _) (by decide) <|
  .cons (p0_9 _) (((OpI.push).at _).fs _) (by decide) <|
  .cons (p0_10 _) (((OpI.mov (.r 7) (.inr rfl)).at _).fs _) (by decide) <|
  .cons (p0_13 _) (((OpI.sub (.i 24) (.inr rfl)).at _).fs _) (by decide) <|
  .cons (p0_17 _) (OpIF.ldf (.inr rfl)) (by decide) <|
  .cons (p0_26 _) (((OpI.st (.inr (.inr (.inr rfl)))).at _).fs _) (by decide) <|
  .cons (p0_31 _) (((OpI.xor (.r 0) (.inl rfl)).at _).fs _) (by decide) <|
  .cons (p0_33 _) (((OpI.mov (.r 4) (.inr rfl)).at _).fs _) (by decide) <|
  .nil 36

/-- The stretch at `41`. -/
def p1 : List Byte := [
  0x85, 0xc0]

theorem p1_0 : ∀ feat, Dec feat p1 0 (FV7z.mk .test 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl

/-- What the stretch does. -/
def o1 : List Op := [
  Op.test 32 0 (.r 0)]

theorem b1 (prof : Profile) : Blk prof p1 0 2 o1 :=
  .cons (p1_0 _) (OpI.test (.r 0) (.inl rfl)) (by decide) <|
  .nil 2

def j0 : List Byte := [0x74, 0x1b]
theorem j0_0 : ∀ feat, Dec feat j0 0 (FV7z.mk (.jcc 4) 64 [.rel 27] 2) := by dec_rfl

/-- The stretch at `45`. -/
def p2 : List Byte := [
  0x48, 0x8b, 0x5c, 0x24, 0x08, 0x64, 0x48, 0x33, 0x1c, 0x25, 0x28, 0x00, 0x00, 0x00]

theorem p2_0 : ∀ feat, Dec feat p2 0 (FV7z.mk .mov 64 [gr 64 3, .mem (mg (some 4) none 1 8 64)] 5) := by dec_rfl
theorem p2_5 : ∀ feat, Dec feat p2 5 (FV7z.mk .xor 64 [gr 64 3, .mem (mf none none 1 40 64)] 9) := by dec_rfl

/-- What the stretch does. -/
def o2 (fb : Addr) : List Op := [
  Op.ld 64 3 (some 4) none 1 8,
  Op.xormf fb 64 3 none none 1 40]

theorem b2 (prof : Profile) (fb : Addr) : BlkF prof p2 (0x42bf3d : Addr) fb 0 14 (o2 fb) :=
  .cons (p2_0 _) (((OpI.ld (.inr rfl)).at _).fs _) (by decide) <|
  .cons (p2_5 _) (OpIF.xormf (.inr rfl)) (by decide) <|
  .nil 14

def j1 : List Byte := [0x75, 0x2c]
theorem j1_0 : ∀ feat, Dec feat j1 0 (FV7z.mk (.jcc 5) 64 [.rel 44] 2) := by dec_rfl

/-- The stretch at `61`. -/
def p3 : List Byte := [
  0x48, 0x83, 0xc4, 0x18, 0x5b, 0x41, 0x5c]

theorem p3_0 : ∀ feat, Dec feat p3 0 (FV7z.mk .add 64 [gr 64 4, Src.opd 64 (.i 24)] 4) := by dec_rfl
theorem p3_4 : ∀ feat, Dec feat p3 4 (FV7z.mk .pop 64 [gr 64 3] 1) := by dec_rfl
theorem p3_5 : ∀ feat, Dec feat p3 5 (FV7z.mk .pop 64 [gr 64 12] 2) := by dec_rfl

/-- What the stretch does. -/
def o3 : List Op := [
  Op.add 64 4 (.i 24),
  Op.pop 3,
  Op.pop 12]

theorem b3 (prof : Profile) : Blk prof p3 0 7 o3 :=
  .cons (p3_0 _) (OpI.add (.i 24) (.inr rfl)) (by decide) <|
  .cons (p3_4 _) (OpI.pop) (by decide) <|
  .cons (p3_5 _) (OpI.pop) (by decide) <|
  .nil 7

/-- The stretch at `72`. -/
def p4 : List Byte := [
  0x0f, 0xb6, 0x54, 0x24, 0x01, 0x0f, 0xb6, 0x34, 0x24, 0x4c, 0x89, 0xe1, 0x48, 0x89, 0xdf]

theorem p4_0 : ∀ feat, Dec feat p4 0 (FV7z.mk .movzx 32 [gr 32 2, .mem (mg (some 4) none 1 1 8)] 5) := by dec_rfl
theorem p4_5 : ∀ feat, Dec feat p4 5 (FV7z.mk .movzx 32 [gr 32 6, .mem (mg (some 4) none 1 0 8)] 4) := by dec_rfl
theorem p4_9 : ∀ feat, Dec feat p4 9 (FV7z.mk .mov 64 [gr 64 1, Src.opd 64 (.r 12)] 3) := by dec_rfl
theorem p4_12 : ∀ feat, Dec feat p4 12 (FV7z.mk .mov 64 [gr 64 7, Src.opd 64 (.r 3)] 3) := by dec_rfl

/-- What the stretch does. -/
def o4 : List Op := [
  Op.ldzx 8 2 (some 4) none 1 1,
  Op.ldzx 8 6 (some 4) none 1 0,
  Op.mov 64 1 (.r 12),
  Op.mov 64 7 (.r 3)]

theorem b4 (prof : Profile) : Blk prof p4 0 15 o4 :=
  .cons (p4_0 _) (OpI.ldzx (.inl rfl)) (by decide) <|
  .cons (p4_5 _) (OpI.ldzx (.inl rfl)) (by decide) <|
  .cons (p4_9 _) (OpI.mov (.r 12) (.inr rfl)) (by decide) <|
  .cons (p4_12 _) (OpI.mov (.r 3) (.inr rfl)) (by decide) <|
  .nil 15

def j2 : List Byte := [0x75, 0xcd]
theorem j2_0 : ∀ feat, Dec feat j2 0 (FV7z.mk (.jcc 5) 64 [.rel 18446744073709551565] 2) := by dec_rfl

/-- The stretch at `96`. -/
def p5 : List Byte := [
  0x48, 0x8b, 0x14, 0x24, 0x48, 0x89, 0x13]

theorem p5_0 : ∀ feat, Dec feat p5 0 (FV7z.mk .mov 64 [gr 64 2, .mem (mg (some 4) none 1 0 64)] 4) := by dec_rfl
theorem p5_4 : ∀ feat, Dec feat p5 4 (FV7z.mk .mov 64 [.mem (mg (some 3) none 1 0 64), gr 64 2] 3) := by dec_rfl

/-- What the stretch does. -/
def o5 : List Op := [
  Op.ld 64 2 (some 4) none 1 0,
  Op.st 64 (some 3) none 1 0 2]

theorem b5 (prof : Profile) : Blk prof p5 0 7 o5 :=
  .cons (p5_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p5_4 _) (OpI.st (.inr (.inr (.inr rfl)))) (by decide) <|
  .nil 7

def j3 : List Byte := [0xeb, 0xc4]
theorem j3_0 : ∀ feat, Dec feat j3 0 (FV7z.mk .jmp 64 [.rel 18446744073709551556] 2) := by dec_rfl

end FV7z.Lpb
