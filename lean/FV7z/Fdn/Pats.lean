import FV7z.Lemmas.SpFs
import FV7z.Lemmas.BlkOps14
import FV7z.Lemmas.BlkOps6
import FV7z.Lemmas.BlkOps2
/-!
# The stretches of straight-line code of `NWindows::NFile::NFind::CFileInfo::Find_DontFill_Name` (PLAN.md §M, M1)

Each distinct stretch between labels and jumps (`p*`, 6 of them) and each distinct jump (`j*`, 2) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.Fdn
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The stretch at `0`. -/
def p0 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0x41, 0x54, 0x0f, 0xb6, 0xd2, 0x55, 0x48, 0x89, 0xfd, 0x48, 0x89, 0xf7,
  0x48, 0x81, 0xec, 0xa8, 0x00, 0x00, 0x00, 0x64, 0x48, 0x8b, 0x04, 0x25, 0x28, 0x00, 0x00, 0x00,
  0x48, 0x89, 0x84, 0x24, 0x98, 0x00, 0x00, 0x00, 0x31, 0xc0, 0x49, 0x89, 0xe4, 0x4c, 0x89, 0xe6]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem p0_4 : ∀ feat, Dec feat p0 4 (FV7z.mk .push 64 [gr 64 12] 2) := by dec_rfl
theorem p0_6 : ∀ feat, Dec feat p0 6 (FV7z.mk .movzx 32 [gr 32 2, gr 8 2] 3) := by dec_rfl
theorem p0_9 : ∀ feat, Dec feat p0 9 (FV7z.mk .push 64 [gr 64 5] 1) := by dec_rfl
theorem p0_10 : ∀ feat, Dec feat p0 10 (FV7z.mk .mov 64 [gr 64 5, Src.opd 64 (.r 7)] 3) := by dec_rfl
theorem p0_13 : ∀ feat, Dec feat p0 13 (FV7z.mk .mov 64 [gr 64 7, Src.opd 64 (.r 6)] 3) := by dec_rfl
theorem p0_16 : ∀ feat, Dec feat p0 16 (FV7z.mk .sub 64 [gr 64 4, Src.opd 64 (.i 168)] 7) := by dec_rfl
theorem p0_23 : ∀ feat, Dec feat p0 23 (FV7z.mk .mov 64 [gr 64 0, .mem (mf none none 1 40 64)] 9) := by dec_rfl
theorem p0_32 : ∀ feat, Dec feat p0 32 (FV7z.mk .mov 64 [.mem (mg (some 4) none 1 152 64), gr 64 0] 8) := by dec_rfl
theorem p0_40 : ∀ feat, Dec feat p0 40 (FV7z.mk .xor 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl
theorem p0_42 : ∀ feat, Dec feat p0 42 (FV7z.mk .mov 64 [gr 64 12, Src.opd 64 (.r 4)] 3) := by dec_rfl
theorem p0_45 : ∀ feat, Dec feat p0 45 (FV7z.mk .mov 64 [gr 64 6, Src.opd 64 (.r 12)] 3) := by dec_rfl

/-- What the stretch does. -/
def o0 (fb : Addr) : List Op := [
  Op.nop,
  Op.push 12,
  Op.zxr 2 2,
  Op.push 5,
  Op.mov 64 5 (.r 7),
  Op.mov 64 7 (.r 6),
  Op.sub 64 4 (.i 168),
  Op.ldf fb 64 0 none none 1 40,
  Op.st 64 (some 4) none 1 152 0,
  Op.xor 32 0 (.r 0),
  Op.mov 64 12 (.r 4),
  Op.mov 64 6 (.r 12)]

theorem b0 (prof : Profile) (fb : Addr) : BlkF prof p0 (0x455b00 : Addr) fb 0 48 (o0 fb) :=
  .cons (p0_0 _) (((OpI.endbr).at _).fs _) (by decide) <|
  .cons (p0_4 _) (((OpI.push).at _).fs _) (by decide) <|
  .cons (p0_6 _) (((OpI.zxr).at _).fs _) (by decide) <|
  .cons (p0_9 _) (((OpI.push).at _).fs _) (by decide) <|
  .cons (p0_10 _) (((OpI.mov (.r 7) (.inr rfl)).at _).fs _) (by decide) <|
  .cons (p0_13 _) (((OpI.mov (.r 6) (.inr rfl)).at _).fs _) (by decide) <|
  .cons (p0_16 _) (((OpI.sub (.i 168) (.inr rfl)).at _).fs _) (by decide) <|
  .cons (p0_23 _) (OpIF.ldf (.inr rfl)) (by decide) <|
  .cons (p0_32 _) (((OpI.st (.inr (.inr (.inr rfl)))).at _).fs _) (by decide) <|
  .cons (p0_40 _) (((OpI.xor (.r 0) (.inl rfl)).at _).fs _) (by decide) <|
  .cons (p0_42 _) (((OpI.mov (.r 4) (.inr rfl)).at _).fs _) (by decide) <|
  .cons (p0_45 _) (((OpI.mov (.r 12) (.inr rfl)).at _).fs _) (by decide) <|
  .nil 48

/-- The stretch at `53`. -/
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

def j0 : List Byte := [0x75, 0x10]
theorem j0_0 : ∀ feat, Dec feat j0 0 (FV7z.mk (.jcc 5) 64 [.rel 16] 2) := by dec_rfl

/-- The stretch at `63`. -/
def p2 : List Byte := [
  0x4c, 0x89, 0xe6, 0x48, 0x89, 0xef]

theorem p2_0 : ∀ feat, Dec feat p2 0 (FV7z.mk .mov 64 [gr 64 6, Src.opd 64 (.r 12)] 3) := by dec_rfl
theorem p2_3 : ∀ feat, Dec feat p2 3 (FV7z.mk .mov 64 [gr 64 7, Src.opd 64 (.r 5)] 3) := by dec_rfl

/-- What the stretch does. -/
def o2 : List Op := [
  Op.mov 64 6 (.r 12),
  Op.mov 64 7 (.r 5)]

theorem b2 (prof : Profile) : Blk prof p2 0 6 o2 :=
  .cons (p2_0 _) (OpI.mov (.r 12) (.inr rfl)) (by decide) <|
  .cons (p2_3 _) (OpI.mov (.r 5) (.inr rfl)) (by decide) <|
  .nil 6

/-- The stretch at `74`. -/
def p3 : List Byte := [
  0xb8, 0x01, 0x00, 0x00, 0x00]

theorem p3_0 : ∀ feat, Dec feat p3 0 (FV7z.mk .mov 32 [gr 32 0, Src.opd 32 (.i 1)] 5) := by dec_rfl

/-- What the stretch does. -/
def o3 : List Op := [
  Op.mov 32 0 (.i 1)]

theorem b3 (prof : Profile) : Blk prof p3 0 5 o3 :=
  .cons (p3_0 _) (OpI.mov (.i 1) (.inl rfl)) (by decide) <|
  .nil 5

/-- The stretch at `79`. -/
def p4 : List Byte := [
  0x48, 0x8b, 0x8c, 0x24, 0x98, 0x00, 0x00, 0x00, 0x64, 0x48, 0x33, 0x0c, 0x25, 0x28, 0x00, 0x00,
  0x00]

theorem p4_0 : ∀ feat, Dec feat p4 0 (FV7z.mk .mov 64 [gr 64 1, .mem (mg (some 4) none 1 152 64)] 8) := by dec_rfl
theorem p4_8 : ∀ feat, Dec feat p4 8 (FV7z.mk .xor 64 [gr 64 1, .mem (mf none none 1 40 64)] 9) := by dec_rfl

/-- What the stretch does. -/
def o4 (fb : Addr) : List Op := [
  Op.ld 64 1 (some 4) none 1 152,
  Op.xormf fb 64 1 none none 1 40]

theorem b4 (prof : Profile) (fb : Addr) : BlkF prof p4 (0x455b4f : Addr) fb 0 17 (o4 fb) :=
  .cons (p4_0 _) (((OpI.ld (.inr rfl)).at _).fs _) (by decide) <|
  .cons (p4_8 _) (OpIF.xormf (.inr rfl)) (by decide) <|
  .nil 17

def j1 : List Byte := [0x75, 0x0b]
theorem j1_0 : ∀ feat, Dec feat j1 0 (FV7z.mk (.jcc 5) 64 [.rel 11] 2) := by dec_rfl

/-- The stretch at `98`. -/
def p5 : List Byte := [
  0x48, 0x81, 0xc4, 0xa8, 0x00, 0x00, 0x00, 0x5d, 0x41, 0x5c]

theorem p5_0 : ∀ feat, Dec feat p5 0 (FV7z.mk .add 64 [gr 64 4, Src.opd 64 (.i 168)] 7) := by dec_rfl
theorem p5_7 : ∀ feat, Dec feat p5 7 (FV7z.mk .pop 64 [gr 64 5] 1) := by dec_rfl
theorem p5_8 : ∀ feat, Dec feat p5 8 (FV7z.mk .pop 64 [gr 64 12] 2) := by dec_rfl

/-- What the stretch does. -/
def o5 : List Op := [
  Op.add 64 4 (.i 168),
  Op.pop 5,
  Op.pop 12]

theorem b5 (prof : Profile) : Blk prof p5 0 10 o5 :=
  .cons (p5_0 _) (OpI.add (.i 168) (.inr rfl)) (by decide) <|
  .cons (p5_7 _) (OpI.pop) (by decide) <|
  .cons (p5_8 _) (OpI.pop) (by decide) <|
  .nil 10

end FV7z.Fdn
