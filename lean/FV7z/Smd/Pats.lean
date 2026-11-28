import FV7z.Lemmas.SpFs
import FV7z.Lemmas.BlkOps6
import FV7z.Lemmas.BlkOps2
/-!
# The stretches of straight-line code of `Set_ModuleDirPrefix_From_ProgArg0` (PLAN.md §M, M1)

Each distinct stretch between labels and jumps (`p*`, 8 of them) and each distinct jump (`j*`, 3) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.Smd
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The stretch at `0`. -/
def p0 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0x55, 0x48, 0x89, 0xfe, 0x48, 0x83, 0xec, 0x20, 0x64, 0x48, 0x8b, 0x04,
  0x25, 0x28, 0x00, 0x00, 0x00, 0x48, 0x89, 0x44, 0x24, 0x18, 0x31, 0xc0, 0x48, 0x89, 0xe5, 0x48,
  0x89, 0xef]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem p0_4 : ∀ feat, Dec feat p0 4 (FV7z.mk .push 64 [gr 64 5] 1) := by dec_rfl
theorem p0_5 : ∀ feat, Dec feat p0 5 (FV7z.mk .mov 64 [gr 64 6, Src.opd 64 (.r 7)] 3) := by dec_rfl
theorem p0_8 : ∀ feat, Dec feat p0 8 (FV7z.mk .sub 64 [gr 64 4, Src.opd 64 (.i 32)] 4) := by dec_rfl
theorem p0_12 : ∀ feat, Dec feat p0 12 (FV7z.mk .mov 64 [gr 64 0, .mem (mf none none 1 40 64)] 9) := by dec_rfl
theorem p0_21 : ∀ feat, Dec feat p0 21 (FV7z.mk .mov 64 [.mem (mg (some 4) none 1 24 64), gr 64 0] 5) := by dec_rfl
theorem p0_26 : ∀ feat, Dec feat p0 26 (FV7z.mk .xor 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl
theorem p0_28 : ∀ feat, Dec feat p0 28 (FV7z.mk .mov 64 [gr 64 5, Src.opd 64 (.r 4)] 3) := by dec_rfl
theorem p0_31 : ∀ feat, Dec feat p0 31 (FV7z.mk .mov 64 [gr 64 7, Src.opd 64 (.r 5)] 3) := by dec_rfl

/-- What the stretch does. -/
def o0 (fb : Addr) : List Op := [
  Op.nop,
  Op.push 5,
  Op.mov 64 6 (.r 7),
  Op.sub 64 4 (.i 32),
  Op.ldf fb 64 0 none none 1 40,
  Op.st 64 (some 4) none 1 24 0,
  Op.xor 32 0 (.r 0),
  Op.mov 64 5 (.r 4),
  Op.mov 64 7 (.r 5)]

theorem b0 (prof : Profile) (fb : Addr) : BlkF prof p0 (0x5a9ed0 : Addr) fb 0 34 (o0 fb) :=
  .cons (p0_0 _) (((OpI.endbr).at _).fs _) (by decide) <|
  .cons (p0_4 _) (((OpI.push).at _).fs _) (by decide) <|
  .cons (p0_5 _) (((OpI.mov (.r 7) (.inr rfl)).at _).fs _) (by decide) <|
  .cons (p0_8 _) (((OpI.sub (.i 32) (.inr rfl)).at _).fs _) (by decide) <|
  .cons (p0_12 _) (OpIF.ldf (.inr rfl)) (by decide) <|
  .cons (p0_21 _) (((OpI.st (.inr (.inr (.inr rfl)))).at _).fs _) (by decide) <|
  .cons (p0_26 _) (((OpI.xor (.r 0) (.inl rfl)).at _).fs _) (by decide) <|
  .cons (p0_28 _) (((OpI.mov (.r 4) (.inr rfl)).at _).fs _) (by decide) <|
  .cons (p0_31 _) (((OpI.mov (.r 5) (.inr rfl)).at _).fs _) (by decide) <|
  .nil 34

/-- The stretch at `39`. -/
def p1 : List Byte := [
  0x48, 0x89, 0xef]

theorem p1_0 : ∀ feat, Dec feat p1 0 (FV7z.mk .mov 64 [gr 64 7, Src.opd 64 (.r 5)] 3) := by dec_rfl

/-- What the stretch does. -/
def o1 : List Op := [
  Op.mov 64 7 (.r 5)]

theorem b1 (prof : Profile) : Blk prof p1 0 3 o1 :=
  .cons (p1_0 _) (OpI.mov (.r 5) (.inr rfl)) (by decide) <|
  .nil 3

/-- The stretch at `47`. -/
def p2 : List Byte := [
  0x83, 0xc0, 0x01, 0x3b, 0x44, 0x24, 0x08]

theorem p2_0 : ∀ feat, Dec feat p2 0 (FV7z.mk .add 32 [gr 32 0, Src.opd 32 (.i 1)] 3) := by dec_rfl
theorem p2_3 : ∀ feat, Dec feat p2 3 (FV7z.mk .cmp 32 [gr 32 0, .mem (mg (some 4) none 1 8 32)] 4) := by dec_rfl

/-- What the stretch does. -/
def o2 : List Op := [
  Op.add 32 0 (.i 1),
  Op.cmpm 32 0 (some 4) none 1 8]

theorem b2 (prof : Profile) : Blk prof p2 0 7 o2 :=
  .cons (p2_0 _) (OpI.add (.i 1) (.inl rfl)) (by decide) <|
  .cons (p2_3 _) (OpI.cmpm (.inl rfl)) (by decide) <|
  .nil 7

def j0 : List Byte := [0x73, 0x0c]
theorem j0_0 : ∀ feat, Dec feat j0 0 (FV7z.mk (.jcc 3) 64 [.rel 12] 2) := by dec_rfl

/-- The stretch at `56`. -/
def p3 : List Byte := [
  0x48, 0x8b, 0x14, 0x24, 0x89, 0x44, 0x24, 0x08, 0xc6, 0x04, 0x02, 0x00]

theorem p3_0 : ∀ feat, Dec feat p3 0 (FV7z.mk .mov 64 [gr 64 2, .mem (mg (some 4) none 1 0 64)] 4) := by dec_rfl
theorem p3_4 : ∀ feat, Dec feat p3 4 (FV7z.mk .mov 32 [.mem (mg (some 4) none 1 8 32), gr 32 0] 4) := by dec_rfl
theorem p3_8 : ∀ feat, Dec feat p3 8 (FV7z.mk .mov 8 [.mem (mg (some 2) (some 0) 1 0 8), .imm 8 0] 4) := by dec_rfl

/-- What the stretch does. -/
def o3 : List Op := [
  Op.ld 64 2 (some 4) none 1 0,
  Op.st 32 (some 4) none 1 8 0,
  Op.sti 8 (some 2) (some 0) 1 0 0]

theorem b3 (prof : Profile) : Blk prof p3 0 12 o3 :=
  .cons (p3_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p3_4 _) (OpI.st (.inr (.inr (.inl rfl)))) (by decide) <|
  .cons (p3_8 _) (OpI.sti (.inl rfl)) (by decide) <|
  .nil 12

/-- The stretch at `68`. -/
def p4 : List Byte := [
  0x48, 0x89, 0xee, 0x48, 0x8d, 0x3d, 0x72, 0x4e, 0x1f, 0x00]

theorem p4_0 : ∀ feat, Dec feat p4 0 (FV7z.mk .mov 64 [gr 64 6, Src.opd 64 (.r 5)] 3) := by dec_rfl
theorem p4_3 : ∀ feat, Dec feat p4 3 (FV7z.mk .lea 64 [gr 64 7, .mem (mrip 2051698 0)] 7) := by dec_rfl

/-- What the stretch does. -/
def o4 : List Op := [
  Op.mov 64 6 (.r 5),
  Op.mov 64 7 (.i 7990672)]

theorem b4 (prof : Profile) : BlkA prof p4 (0x5a9f14 : Addr) 0 10 o4 :=
  .cons (p4_0 _) ((OpI.mov (.r 5) (.inr rfl)).at _) (by decide) <|
  .cons (p4_3 _) (OpIA.lea_rip (by decide)) (by decide) <|
  .nil 10

/-- The stretch at `83`. -/
def p5 : List Byte := [
  0x48, 0x8b, 0x3c, 0x24, 0x48, 0x85, 0xff]

theorem p5_0 : ∀ feat, Dec feat p5 0 (FV7z.mk .mov 64 [gr 64 7, .mem (mg (some 4) none 1 0 64)] 4) := by dec_rfl
theorem p5_4 : ∀ feat, Dec feat p5 4 (FV7z.mk .test 64 [gr 64 7, Src.opd 64 (.r 7)] 3) := by dec_rfl

/-- What the stretch does. -/
def o5 : List Op := [
  Op.ld 64 7 (some 4) none 1 0,
  Op.test 64 7 (.r 7)]

theorem b5 (prof : Profile) : Blk prof p5 0 7 o5 :=
  .cons (p5_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p5_4 _) (OpI.test (.r 7) (.inr rfl)) (by decide) <|
  .nil 7

def j1 : List Byte := [0x74, 0x05]
theorem j1_0 : ∀ feat, Dec feat j1 0 (FV7z.mk (.jcc 4) 64 [.rel 5] 2) := by dec_rfl

/-- The stretch at `97`. -/
def p6 : List Byte := [
  0x48, 0x8b, 0x44, 0x24, 0x18, 0x64, 0x48, 0x33, 0x04, 0x25, 0x28, 0x00, 0x00, 0x00]

theorem p6_0 : ∀ feat, Dec feat p6 0 (FV7z.mk .mov 64 [gr 64 0, .mem (mg (some 4) none 1 24 64)] 5) := by dec_rfl
theorem p6_5 : ∀ feat, Dec feat p6 5 (FV7z.mk .xor 64 [gr 64 0, .mem (mf none none 1 40 64)] 9) := by dec_rfl

/-- What the stretch does. -/
def o6 (fb : Addr) : List Op := [
  Op.ld 64 0 (some 4) none 1 24,
  Op.xormf fb 64 0 none none 1 40]

theorem b6 (prof : Profile) (fb : Addr) : BlkF prof p6 (0x5a9f31 : Addr) fb 0 14 (o6 fb) :=
  .cons (p6_0 _) (((OpI.ld (.inr rfl)).at _).fs _) (by decide) <|
  .cons (p6_5 _) (OpIF.xormf (.inr rfl)) (by decide) <|
  .nil 14

def j2 : List Byte := [0x75, 0x06]
theorem j2_0 : ∀ feat, Dec feat j2 0 (FV7z.mk (.jcc 5) 64 [.rel 6] 2) := by dec_rfl

/-- The stretch at `113`. -/
def p7 : List Byte := [
  0x48, 0x83, 0xc4, 0x20, 0x5d]

theorem p7_0 : ∀ feat, Dec feat p7 0 (FV7z.mk .add 64 [gr 64 4, Src.opd 64 (.i 32)] 4) := by dec_rfl
theorem p7_4 : ∀ feat, Dec feat p7 4 (FV7z.mk .pop 64 [gr 64 5] 1) := by dec_rfl

/-- What the stretch does. -/
def o7 : List Op := [
  Op.add 64 4 (.i 32),
  Op.pop 5]

theorem b7 (prof : Profile) : Blk prof p7 0 5 o7 :=
  .cons (p7_0 _) (OpI.add (.i 32) (.inr rfl)) (by decide) <|
  .cons (p7_4 _) (OpI.pop) (by decide) <|
  .nil 5

end FV7z.Smd
