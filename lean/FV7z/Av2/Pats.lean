import FV7z.Lemmas.SpFs
import FV7z.Lemmas.BlkOps6
import FV7z.Lemmas.BlkOps2
/-!
# The stretches of straight-line code of `CPU_IsSupported_AVX2` (PLAN.md §M, M1)

Each distinct stretch between labels and jumps (`p*`, 8 of them) and each distinct jump (`j*`, 4) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.Av2
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The stretch at `0`. -/
def p0 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0x48, 0x83, 0xec, 0x28, 0x64, 0x48, 0x8b, 0x04, 0x25, 0x28, 0x00, 0x00,
  0x00, 0x48, 0x89, 0x44, 0x24, 0x18, 0x31, 0xc0]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem p0_4 : ∀ feat, Dec feat p0 4 (FV7z.mk .sub 64 [gr 64 4, Src.opd 64 (.i 40)] 4) := by dec_rfl
theorem p0_8 : ∀ feat, Dec feat p0 8 (FV7z.mk .mov 64 [gr 64 0, .mem (mf none none 1 40 64)] 9) := by dec_rfl
theorem p0_17 : ∀ feat, Dec feat p0 17 (FV7z.mk .mov 64 [.mem (mg (some 4) none 1 24 64), gr 64 0] 5) := by dec_rfl
theorem p0_22 : ∀ feat, Dec feat p0 22 (FV7z.mk .xor 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl

/-- What the stretch does. -/
def o0 (fb : Addr) : List Op := [
  Op.nop,
  Op.sub 64 4 (.i 40),
  Op.ldf fb 64 0 none none 1 40,
  Op.st 64 (some 4) none 1 24 0,
  Op.xor 32 0 (.r 0)]

theorem b0 (prof : Profile) (fb : Addr) : BlkF prof p0 (0x4244b0 : Addr) fb 0 24 (o0 fb) :=
  .cons (p0_0 _) (((OpI.endbr).at _).fs _) (by decide) <|
  .cons (p0_4 _) (((OpI.sub (.i 40) (.inr rfl)).at _).fs _) (by decide) <|
  .cons (p0_8 _) (OpIF.ldf (.inr rfl)) (by decide) <|
  .cons (p0_17 _) (((OpI.st (.inr (.inr (.inr rfl)))).at _).fs _) (by decide) <|
  .cons (p0_22 _) (((OpI.xor (.r 0) (.inl rfl)).at _).fs _) (by decide) <|
  .nil 24

/-- The stretch at `29`. -/
def p1 : List Byte := [
  0x85, 0xc0]

theorem p1_0 : ∀ feat, Dec feat p1 0 (FV7z.mk .test 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl

/-- What the stretch does. -/
def o1 : List Op := [
  Op.test 32 0 (.r 0)]

theorem b1 (prof : Profile) : Blk prof p1 0 2 o1 :=
  .cons (p1_0 _) (OpI.test (.r 0) (.inl rfl)) (by decide) <|
  .nil 2

def j0 : List Byte := [0x75, 0x1f]
theorem j0_0 : ∀ feat, Dec feat j0 0 (FV7z.mk (.jcc 5) 64 [.rel 31] 2) := by dec_rfl

/-- The stretch at `33`. -/
def p2 : List Byte := [
  0x31, 0xc0]

theorem p2_0 : ∀ feat, Dec feat p2 0 (FV7z.mk .xor 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl

/-- What the stretch does. -/
def o2 : List Op := [
  Op.xor 32 0 (.r 0)]

theorem b2 (prof : Profile) : Blk prof p2 0 2 o2 :=
  .cons (p2_0 _) (OpI.xor (.r 0) (.inl rfl)) (by decide) <|
  .nil 2

/-- The stretch at `35`. -/
def p3 : List Byte := [
  0x48, 0x8b, 0x54, 0x24, 0x18, 0x64, 0x48, 0x33, 0x14, 0x25, 0x28, 0x00, 0x00, 0x00]

theorem p3_0 : ∀ feat, Dec feat p3 0 (FV7z.mk .mov 64 [gr 64 2, .mem (mg (some 4) none 1 24 64)] 5) := by dec_rfl
theorem p3_5 : ∀ feat, Dec feat p3 5 (FV7z.mk .xor 64 [gr 64 2, .mem (mf none none 1 40 64)] 9) := by dec_rfl

/-- What the stretch does. -/
def o3 (fb : Addr) : List Op := [
  Op.ld 64 2 (some 4) none 1 24,
  Op.xormf fb 64 2 none none 1 40]

theorem b3 (prof : Profile) (fb : Addr) : BlkF prof p3 (0x4244d3 : Addr) fb 0 14 (o3 fb) :=
  .cons (p3_0 _) (((OpI.ld (.inr rfl)).at _).fs _) (by decide) <|
  .cons (p3_5 _) (OpIF.xormf (.inr rfl)) (by decide) <|
  .nil 14

def j1 : List Byte := [0x75, 0x30]
theorem j1_0 : ∀ feat, Dec feat j1 0 (FV7z.mk (.jcc 5) 64 [.rel 48] 2) := by dec_rfl

/-- The stretch at `51`. -/
def p4 : List Byte := [
  0x48, 0x83, 0xc4, 0x28]

theorem p4_0 : ∀ feat, Dec feat p4 0 (FV7z.mk .add 64 [gr 64 4, Src.opd 64 (.i 40)] 4) := by dec_rfl

/-- What the stretch does. -/
def o4 : List Op := [
  Op.add 64 4 (.i 40)]

theorem b4 (prof : Profile) : Blk prof p4 0 4 o4 :=
  .cons (p4_0 _) (OpI.add (.i 40) (.inr rfl)) (by decide) <|
  .nil 4

/-- The stretch at `69`. -/
def p5 : List Byte := [
  0x83, 0xf8, 0x06]

theorem p5_0 : ∀ feat, Dec feat p5 0 (FV7z.mk .cmp 32 [gr 32 0, Src.opd 32 (.i 6)] 3) := by dec_rfl

/-- What the stretch does. -/
def o5 : List Op := [
  Op.cmp 32 0 (.i 6)]

theorem b5 (prof : Profile) : Blk prof p5 0 3 o5 :=
  .cons (p5_0 _) (OpI.cmp (.i 6) (.inl rfl)) (by decide) <|
  .nil 3

def j2 : List Byte := [0x76, 0xd7]
theorem j2_0 : ∀ feat, Dec feat j2 0 (FV7z.mk (.jcc 6) 64 [.rel 18446744073709551575] 2) := by dec_rfl

/-- The stretch at `74`. -/
def p6 : List Byte := [
  0x48, 0x89, 0xe7, 0xbe, 0x07, 0x00, 0x00, 0x00]

theorem p6_0 : ∀ feat, Dec feat p6 0 (FV7z.mk .mov 64 [gr 64 7, Src.opd 64 (.r 4)] 3) := by dec_rfl
theorem p6_3 : ∀ feat, Dec feat p6 3 (FV7z.mk .mov 32 [gr 32 6, Src.opd 32 (.i 7)] 5) := by dec_rfl

/-- What the stretch does. -/
def o6 : List Op := [
  Op.mov 64 7 (.r 4),
  Op.mov 32 6 (.i 7)]

theorem b6 (prof : Profile) : Blk prof p6 0 8 o6 :=
  .cons (p6_0 _) (OpI.mov (.r 4) (.inr rfl)) (by decide) <|
  .cons (p6_3 _) (OpI.mov (.i 7) (.inl rfl)) (by decide) <|
  .nil 8

/-- The stretch at `87`. -/
def p7 : List Byte := [
  0x8b, 0x44, 0x24, 0x04, 0xc1, 0xe8, 0x05, 0x83, 0xe0, 0x01]

theorem p7_0 : ∀ feat, Dec feat p7 0 (FV7z.mk .mov 32 [gr 32 0, .mem (mg (some 4) none 1 4 32)] 4) := by dec_rfl
theorem p7_4 : ∀ feat, Dec feat p7 4 (FV7z.mk .shr 32 [gr 32 0, Src.opd 8 (.i 5)] 3) := by dec_rfl
theorem p7_7 : ∀ feat, Dec feat p7 7 (FV7z.mk .and 32 [gr 32 0, Src.opd 32 (.i 1)] 3) := by dec_rfl

/-- What the stretch does. -/
def o7 : List Op := [
  Op.ld 32 0 (some 4) none 1 4,
  Op.shr 0 (.i 5),
  Op.and 32 0 (.i 1)]

theorem b7 (prof : Profile) : Blk prof p7 0 10 o7 :=
  .cons (p7_0 _) (OpI.ld (.inl rfl)) (by decide) <|
  .cons (p7_4 _) (OpI.shr (.i 5)) (by decide) <|
  .cons (p7_7 _) (OpI.and (.i 1) (.inl rfl)) (by decide) <|
  .nil 10

def j3 : List Byte := [0xeb, 0xc0]
theorem j3_0 : ∀ feat, Dec feat j3 0 (FV7z.mk .jmp 64 [.rel 18446744073709551552] 2) := by dec_rfl

end FV7z.Av2
