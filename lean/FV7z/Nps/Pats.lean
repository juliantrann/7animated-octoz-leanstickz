import FV7z.Lemmas.SpFs
import FV7z.Lemmas.BlkOps6
import FV7z.Lemmas.BlkOps2
/-!
# The stretches of straight-line code of `CStdOutStream::NormalizePrint_UString (const UString &)` (PLAN.md §M, M1)

Each distinct stretch between labels and jumps (`p*`, 8 of them) and each distinct jump (`j*`, 2) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.Nps
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The stretch at `0`. -/
def p0 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0x41, 0x55, 0x41, 0x54, 0x55, 0x48, 0x89, 0xfd, 0x48, 0x83, 0xec, 0x30,
  0x64, 0x48, 0x8b, 0x04, 0x25, 0x28, 0x00, 0x00, 0x00, 0x48, 0x89, 0x44, 0x24, 0x28, 0x31, 0xc0,
  0x49, 0x89, 0xe4, 0x4c, 0x89, 0xe7]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem p0_4 : ∀ feat, Dec feat p0 4 (FV7z.mk .push 64 [gr 64 13] 2) := by dec_rfl
theorem p0_6 : ∀ feat, Dec feat p0 6 (FV7z.mk .push 64 [gr 64 12] 2) := by dec_rfl
theorem p0_8 : ∀ feat, Dec feat p0 8 (FV7z.mk .push 64 [gr 64 5] 1) := by dec_rfl
theorem p0_9 : ∀ feat, Dec feat p0 9 (FV7z.mk .mov 64 [gr 64 5, Src.opd 64 (.r 7)] 3) := by dec_rfl
theorem p0_12 : ∀ feat, Dec feat p0 12 (FV7z.mk .sub 64 [gr 64 4, Src.opd 64 (.i 48)] 4) := by dec_rfl
theorem p0_16 : ∀ feat, Dec feat p0 16 (FV7z.mk .mov 64 [gr 64 0, .mem (mf none none 1 40 64)] 9) := by dec_rfl
theorem p0_25 : ∀ feat, Dec feat p0 25 (FV7z.mk .mov 64 [.mem (mg (some 4) none 1 40 64), gr 64 0] 5) := by dec_rfl
theorem p0_30 : ∀ feat, Dec feat p0 30 (FV7z.mk .xor 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl
theorem p0_32 : ∀ feat, Dec feat p0 32 (FV7z.mk .mov 64 [gr 64 12, Src.opd 64 (.r 4)] 3) := by dec_rfl
theorem p0_35 : ∀ feat, Dec feat p0 35 (FV7z.mk .mov 64 [gr 64 7, Src.opd 64 (.r 12)] 3) := by dec_rfl

/-- What the stretch does. -/
def o0 (fb : Addr) : List Op := [
  Op.nop,
  Op.push 13,
  Op.push 12,
  Op.push 5,
  Op.mov 64 5 (.r 7),
  Op.sub 64 4 (.i 48),
  Op.ldf fb 64 0 none none 1 40,
  Op.st 64 (some 4) none 1 40 0,
  Op.xor 32 0 (.r 0),
  Op.mov 64 12 (.r 4),
  Op.mov 64 7 (.r 12)]

theorem b0 (prof : Profile) (fb : Addr) : BlkF prof p0 (0x5a1870 : Addr) fb 0 38 (o0 fb) :=
  .cons (p0_0 _) (((OpI.endbr).at _).fs _) (by decide) <|
  .cons (p0_4 _) (((OpI.push).at _).fs _) (by decide) <|
  .cons (p0_6 _) (((OpI.push).at _).fs _) (by decide) <|
  .cons (p0_8 _) (((OpI.push).at _).fs _) (by decide) <|
  .cons (p0_9 _) (((OpI.mov (.r 7) (.inr rfl)).at _).fs _) (by decide) <|
  .cons (p0_12 _) (((OpI.sub (.i 48) (.inr rfl)).at _).fs _) (by decide) <|
  .cons (p0_16 _) (OpIF.ldf (.inr rfl)) (by decide) <|
  .cons (p0_25 _) (((OpI.st (.inr (.inr (.inr rfl)))).at _).fs _) (by decide) <|
  .cons (p0_30 _) (((OpI.xor (.r 0) (.inl rfl)).at _).fs _) (by decide) <|
  .cons (p0_32 _) (((OpI.mov (.r 4) (.inr rfl)).at _).fs _) (by decide) <|
  .cons (p0_35 _) (((OpI.mov (.r 12) (.inr rfl)).at _).fs _) (by decide) <|
  .nil 38

/-- The stretch at `43`. -/
def p1 : List Byte := [
  0x4c, 0x89, 0xe6, 0x48, 0x89, 0xef]

theorem p1_0 : ∀ feat, Dec feat p1 0 (FV7z.mk .mov 64 [gr 64 6, Src.opd 64 (.r 12)] 3) := by dec_rfl
theorem p1_3 : ∀ feat, Dec feat p1 3 (FV7z.mk .mov 64 [gr 64 7, Src.opd 64 (.r 5)] 3) := by dec_rfl

/-- What the stretch does. -/
def o1 : List Op := [
  Op.mov 64 6 (.r 12),
  Op.mov 64 7 (.r 5)]

theorem b1 (prof : Profile) : Blk prof p1 0 6 o1 :=
  .cons (p1_0 _) (OpI.mov (.r 12) (.inr rfl)) (by decide) <|
  .cons (p1_3 _) (OpI.mov (.r 5) (.inr rfl)) (by decide) <|
  .nil 6

/-- The stretch at `54`. -/
def p2 : List Byte := [
  0x4c, 0x8d, 0x6c, 0x24, 0x10, 0x4c, 0x89, 0xef]

theorem p2_0 : ∀ feat, Dec feat p2 0 (FV7z.mk .lea 64 [gr 64 13, .mem (mg (some 4) none 1 16 0)] 5) := by dec_rfl
theorem p2_5 : ∀ feat, Dec feat p2 5 (FV7z.mk .mov 64 [gr 64 7, Src.opd 64 (.r 13)] 3) := by dec_rfl

/-- What the stretch does. -/
def o2 : List Op := [
  Op.lea 64 13 (some 4) none 1 16,
  Op.mov 64 7 (.r 13)]

theorem b2 (prof : Profile) : Blk prof p2 0 8 o2 :=
  .cons (p2_0 _) (OpI.lea (.inr rfl)) (by decide) <|
  .cons (p2_5 _) (OpI.mov (.r 13) (.inr rfl)) (by decide) <|
  .nil 8

/-- The stretch at `67`. -/
def p3 : List Byte := [
  0x4c, 0x89, 0xea, 0x4c, 0x89, 0xe6, 0x48, 0x89, 0xef]

theorem p3_0 : ∀ feat, Dec feat p3 0 (FV7z.mk .mov 64 [gr 64 2, Src.opd 64 (.r 13)] 3) := by dec_rfl
theorem p3_3 : ∀ feat, Dec feat p3 3 (FV7z.mk .mov 64 [gr 64 6, Src.opd 64 (.r 12)] 3) := by dec_rfl
theorem p3_6 : ∀ feat, Dec feat p3 6 (FV7z.mk .mov 64 [gr 64 7, Src.opd 64 (.r 5)] 3) := by dec_rfl

/-- What the stretch does. -/
def o3 : List Op := [
  Op.mov 64 2 (.r 13),
  Op.mov 64 6 (.r 12),
  Op.mov 64 7 (.r 5)]

theorem b3 (prof : Profile) : Blk prof p3 0 9 o3 :=
  .cons (p3_0 _) (OpI.mov (.r 13) (.inr rfl)) (by decide) <|
  .cons (p3_3 _) (OpI.mov (.r 12) (.inr rfl)) (by decide) <|
  .cons (p3_6 _) (OpI.mov (.r 5) (.inr rfl)) (by decide) <|
  .nil 9

/-- The stretch at `81`. -/
def p4 : List Byte := [
  0x48, 0x8b, 0x7c, 0x24, 0x10, 0x48, 0x85, 0xff]

theorem p4_0 : ∀ feat, Dec feat p4 0 (FV7z.mk .mov 64 [gr 64 7, .mem (mg (some 4) none 1 16 64)] 5) := by dec_rfl
theorem p4_5 : ∀ feat, Dec feat p4 5 (FV7z.mk .test 64 [gr 64 7, Src.opd 64 (.r 7)] 3) := by dec_rfl

/-- What the stretch does. -/
def o4 : List Op := [
  Op.ld 64 7 (some 4) none 1 16,
  Op.test 64 7 (.r 7)]

theorem b4 (prof : Profile) : Blk prof p4 0 8 o4 :=
  .cons (p4_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p4_5 _) (OpI.test (.r 7) (.inr rfl)) (by decide) <|
  .nil 8

def j0 : List Byte := [0x74, 0x05]
theorem j0_0 : ∀ feat, Dec feat j0 0 (FV7z.mk (.jcc 4) 64 [.rel 5] 2) := by dec_rfl

/-- The stretch at `96`. -/
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

/-- The stretch at `110`. -/
def p6 : List Byte := [
  0x48, 0x8b, 0x44, 0x24, 0x28, 0x64, 0x48, 0x33, 0x04, 0x25, 0x28, 0x00, 0x00, 0x00]

theorem p6_0 : ∀ feat, Dec feat p6 0 (FV7z.mk .mov 64 [gr 64 0, .mem (mg (some 4) none 1 40 64)] 5) := by dec_rfl
theorem p6_5 : ∀ feat, Dec feat p6 5 (FV7z.mk .xor 64 [gr 64 0, .mem (mf none none 1 40 64)] 9) := by dec_rfl

/-- What the stretch does. -/
def o6 (fb : Addr) : List Op := [
  Op.ld 64 0 (some 4) none 1 40,
  Op.xormf fb 64 0 none none 1 40]

theorem b6 (prof : Profile) (fb : Addr) : BlkF prof p6 (0x5a18de : Addr) fb 0 14 (o6 fb) :=
  .cons (p6_0 _) (((OpI.ld (.inr rfl)).at _).fs _) (by decide) <|
  .cons (p6_5 _) (OpIF.xormf (.inr rfl)) (by decide) <|
  .nil 14

def j1 : List Byte := [0x75, 0x0a]
theorem j1_0 : ∀ feat, Dec feat j1 0 (FV7z.mk (.jcc 5) 64 [.rel 10] 2) := by dec_rfl

/-- The stretch at `126`. -/
def p7 : List Byte := [
  0x48, 0x83, 0xc4, 0x30, 0x5d, 0x41, 0x5c, 0x41, 0x5d]

theorem p7_0 : ∀ feat, Dec feat p7 0 (FV7z.mk .add 64 [gr 64 4, Src.opd 64 (.i 48)] 4) := by dec_rfl
theorem p7_4 : ∀ feat, Dec feat p7 4 (FV7z.mk .pop 64 [gr 64 5] 1) := by dec_rfl
theorem p7_5 : ∀ feat, Dec feat p7 5 (FV7z.mk .pop 64 [gr 64 12] 2) := by dec_rfl
theorem p7_7 : ∀ feat, Dec feat p7 7 (FV7z.mk .pop 64 [gr 64 13] 2) := by dec_rfl

/-- What the stretch does. -/
def o7 : List Op := [
  Op.add 64 4 (.i 48),
  Op.pop 5,
  Op.pop 12,
  Op.pop 13]

theorem b7 (prof : Profile) : Blk prof p7 0 9 o7 :=
  .cons (p7_0 _) (OpI.add (.i 48) (.inr rfl)) (by decide) <|
  .cons (p7_4 _) (OpI.pop) (by decide) <|
  .cons (p7_5 _) (OpI.pop) (by decide) <|
  .cons (p7_7 _) (OpI.pop) (by decide) <|
  .nil 9

end FV7z.Nps
