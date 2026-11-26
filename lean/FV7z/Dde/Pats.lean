import FV7z.Lemmas.SpFs
import FV7z.Lemmas.BlkOps14
import FV7z.Lemmas.BlkOps6
import FV7z.Lemmas.BlkOps2
/-!
# The stretches of straight-line code of `NWindows::NFile::NFind::DoesDirExist` (PLAN.md §M, M1)

Each distinct stretch between labels and jumps (`p*`, 5 of them) and each distinct jump (`j*`, 2) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.Dde
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The stretch at `0`. -/
def p0 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0x48, 0x81, 0xec, 0xa8, 0x00, 0x00, 0x00, 0x40, 0x0f, 0xb6, 0xd6, 0x64,
  0x48, 0x8b, 0x04, 0x25, 0x28, 0x00, 0x00, 0x00, 0x48, 0x89, 0x84, 0x24, 0x98, 0x00, 0x00, 0x00,
  0x31, 0xc0, 0x48, 0x89, 0xe6]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem p0_4 : ∀ feat, Dec feat p0 4 (FV7z.mk .sub 64 [gr 64 4, Src.opd 64 (.i 168)] 7) := by dec_rfl
theorem p0_11 : ∀ feat, Dec feat p0 11 (FV7z.mk .movzx 32 [gr 32 2, gr 8 6] 4) := by dec_rfl
theorem p0_15 : ∀ feat, Dec feat p0 15 (FV7z.mk .mov 64 [gr 64 0, .mem (mf none none 1 40 64)] 9) := by dec_rfl
theorem p0_24 : ∀ feat, Dec feat p0 24 (FV7z.mk .mov 64 [.mem (mg (some 4) none 1 152 64), gr 64 0] 8) := by dec_rfl
theorem p0_32 : ∀ feat, Dec feat p0 32 (FV7z.mk .xor 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl
theorem p0_34 : ∀ feat, Dec feat p0 34 (FV7z.mk .mov 64 [gr 64 6, Src.opd 64 (.r 4)] 3) := by dec_rfl

/-- What the stretch does. -/
def o0 (fb : Addr) : List Op := [
  Op.nop,
  Op.sub 64 4 (.i 168),
  Op.zxr 2 6,
  Op.ldf fb 64 0 none none 1 40,
  Op.st 64 (some 4) none 1 152 0,
  Op.xor 32 0 (.r 0),
  Op.mov 64 6 (.r 4)]

theorem b0 (prof : Profile) (fb : Addr) : BlkF prof p0 (0x455cf0 : Addr) fb 0 37 (o0 fb) :=
  .cons (p0_0 _) (((OpI.endbr).at _).fs _) (by decide) <|
  .cons (p0_4 _) (((OpI.sub (.i 168) (.inr rfl)).at _).fs _) (by decide) <|
  .cons (p0_11 _) (((OpI.zxr).at _).fs _) (by decide) <|
  .cons (p0_15 _) (OpIF.ldf (.inr rfl)) (by decide) <|
  .cons (p0_24 _) (((OpI.st (.inr (.inr (.inr rfl)))).at _).fs _) (by decide) <|
  .cons (p0_32 _) (((OpI.xor (.r 0) (.inl rfl)).at _).fs _) (by decide) <|
  .cons (p0_34 _) (((OpI.mov (.r 4) (.inr rfl)).at _).fs _) (by decide) <|
  .nil 37

/-- The stretch at `42`. -/
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

def j0 : List Byte := [0x75, 0x11]
theorem j0_0 : ∀ feat, Dec feat j0 0 (FV7z.mk (.jcc 5) 64 [.rel 17] 2) := by dec_rfl

/-- The stretch at `52`. -/
def p2 : List Byte := [
  0x8b, 0x44, 0x24, 0x18, 0x25, 0x00, 0xf0, 0x00, 0x00, 0x3d, 0x00, 0x40, 0x00, 0x00, 0x0f, 0x94,
  0xc0]

theorem p2_0 : ∀ feat, Dec feat p2 0 (FV7z.mk .mov 32 [gr 32 0, .mem (mg (some 4) none 1 24 32)] 4) := by dec_rfl
theorem p2_4 : ∀ feat, Dec feat p2 4 (FV7z.mk .and 32 [gr 32 0, Src.opd 32 (.i 61440)] 5) := by dec_rfl
theorem p2_9 : ∀ feat, Dec feat p2 9 (FV7z.mk .cmp 32 [gr 32 0, Src.opd 32 (.i 16384)] 5) := by dec_rfl
theorem p2_14 : ∀ feat, Dec feat p2 14 (FV7z.mk (.setcc 4) 8 [gr 8 0] 3) := by dec_rfl

/-- What the stretch does. -/
def o2 : List Op := [
  Op.ld 32 0 (some 4) none 1 24,
  Op.and 32 0 (.i 61440),
  Op.cmp 32 0 (.i 16384),
  Op.setcc 4 0]

theorem b2 (prof : Profile) : Blk prof p2 0 17 o2 :=
  .cons (p2_0 _) (OpI.ld (.inl rfl)) (by decide) <|
  .cons (p2_4 _) (OpI.and (.i 61440) (.inl rfl)) (by decide) <|
  .cons (p2_9 _) (OpI.cmp (.i 16384) (.inl rfl)) (by decide) <|
  .cons (p2_14 _) (OpI.setcc) (by decide) <|
  .nil 17

/-- The stretch at `69`. -/
def p3 : List Byte := [
  0x48, 0x8b, 0x8c, 0x24, 0x98, 0x00, 0x00, 0x00, 0x64, 0x48, 0x33, 0x0c, 0x25, 0x28, 0x00, 0x00,
  0x00]

theorem p3_0 : ∀ feat, Dec feat p3 0 (FV7z.mk .mov 64 [gr 64 1, .mem (mg (some 4) none 1 152 64)] 8) := by dec_rfl
theorem p3_8 : ∀ feat, Dec feat p3 8 (FV7z.mk .xor 64 [gr 64 1, .mem (mf none none 1 40 64)] 9) := by dec_rfl

/-- What the stretch does. -/
def o3 (fb : Addr) : List Op := [
  Op.ld 64 1 (some 4) none 1 152,
  Op.xormf fb 64 1 none none 1 40]

theorem b3 (prof : Profile) (fb : Addr) : BlkF prof p3 (0x455d35 : Addr) fb 0 17 (o3 fb) :=
  .cons (p3_0 _) (((OpI.ld (.inr rfl)).at _).fs _) (by decide) <|
  .cons (p3_8 _) (OpIF.xormf (.inr rfl)) (by decide) <|
  .nil 17

def j1 : List Byte := [0x75, 0x08]
theorem j1_0 : ∀ feat, Dec feat j1 0 (FV7z.mk (.jcc 5) 64 [.rel 8] 2) := by dec_rfl

/-- The stretch at `88`. -/
def p4 : List Byte := [
  0x48, 0x81, 0xc4, 0xa8, 0x00, 0x00, 0x00]

theorem p4_0 : ∀ feat, Dec feat p4 0 (FV7z.mk .add 64 [gr 64 4, Src.opd 64 (.i 168)] 7) := by dec_rfl

/-- What the stretch does. -/
def o4 : List Op := [
  Op.add 64 4 (.i 168)]

theorem b4 (prof : Profile) : Blk prof p4 0 7 o4 :=
  .cons (p4_0 _) (OpI.add (.i 168) (.inr rfl)) (by decide) <|
  .nil 7

end FV7z.Dde
