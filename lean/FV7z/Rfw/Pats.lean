import FV7z.Lemmas.Sp
import FV7z.Lemmas.BlkOps12
import FV7z.Lemmas.BlkOps3
/-!
# The stretches of straight-line code of `UString::ReverseFind` (PLAN.md §M, M1)

Each distinct stretch between labels and jumps (`p*`, 6 of them) and each distinct jump (`j*`, 4) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.Rfw
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The stretch at `0`. -/
def p0 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0x8b, 0x47, 0x08, 0x85, 0xc0]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem p0_4 : ∀ feat, Dec feat p0 4 (FV7z.mk .mov 32 [gr 32 0, .mem (mg (some 7) none 1 8 32)] 3) := by dec_rfl
theorem p0_7 : ∀ feat, Dec feat p0 7 (FV7z.mk .test 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl

/-- What the stretch does. -/
def o0 : List Op := [
  Op.nop,
  Op.ld 32 0 (some 7) none 1 8,
  Op.test 32 0 (.r 0)]

theorem b0 (prof : Profile) : Blk prof p0 0 9 o0 :=
  .cons (p0_0 _) (OpI.endbr) (by decide) <|
  .cons (p0_4 _) (OpI.ld (.inl rfl)) (by decide) <|
  .cons (p0_7 _) (OpI.test (.r 0) (.inl rfl)) (by decide) <|
  .nil 9

def j0 : List Byte := [0x74, 0x25]
theorem j0_0 : ∀ feat, Dec feat j0 0 (FV7z.mk (.jcc 4) 64 [.rel 37] 2) := by dec_rfl

/-- The stretch at `11`. -/
def p1 : List Byte := [
  0x48, 0x8b, 0x17, 0x48, 0x8d, 0x04, 0x82]

theorem p1_0 : ∀ feat, Dec feat p1 0 (FV7z.mk .mov 64 [gr 64 2, .mem (mg (some 7) none 1 0 64)] 3) := by dec_rfl
theorem p1_3 : ∀ feat, Dec feat p1 3 (FV7z.mk .lea 64 [gr 64 0, .mem (mg (some 2) (some 0) 4 0 0)] 4) := by dec_rfl

/-- What the stretch does. -/
def o1 : List Op := [
  Op.ld 64 2 (some 7) none 1 0,
  Op.lea 64 0 (some 2) (some 0) 4 0]

theorem b1 (prof : Profile) : Blk prof p1 0 7 o1 :=
  .cons (p1_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p1_3 _) (OpI.lea (.inr rfl)) (by decide) <|
  .nil 7

def j1 : List Byte := [0xeb, 0x09]
theorem j1_0 : ∀ feat, Dec feat j1 0 (FV7z.mk .jmp 64 [.rel 9] 2) := by dec_rfl

/-- The stretch at `24`. -/
def p2 : List Byte := [
  0x48, 0x39, 0xc2]

theorem p2_0 : ∀ feat, Dec feat p2 0 (FV7z.mk .cmp 64 [gr 64 2, Src.opd 64 (.r 0)] 3) := by dec_rfl

/-- What the stretch does. -/
def o2 : List Op := [
  Op.cmp 64 2 (.r 0)]

theorem b2 (prof : Profile) : Blk prof p2 0 3 o2 :=
  .cons (p2_0 _) (OpI.cmp (.r 0) (.inr rfl)) (by decide) <|
  .nil 3

def j2 : List Byte := [0x74, 0x13]
theorem j2_0 : ∀ feat, Dec feat j2 0 (FV7z.mk (.jcc 4) 64 [.rel 19] 2) := by dec_rfl

/-- The stretch at `29`. -/
def p3 : List Byte := [
  0x48, 0x83, 0xe8, 0x04, 0x39, 0x30]

theorem p3_0 : ∀ feat, Dec feat p3 0 (FV7z.mk .sub 64 [gr 64 0, Src.opd 64 (.i 4)] 4) := by dec_rfl
theorem p3_4 : ∀ feat, Dec feat p3 4 (FV7z.mk .cmp 32 [.mem (mg (some 0) none 1 0 32), gr 32 6] 2) := by dec_rfl

/-- What the stretch does. -/
def o3 : List Op := [
  Op.sub 64 0 (.i 4),
  Op.cmpmr 32 (some 0) none 1 0 6]

theorem b3 (prof : Profile) : Blk prof p3 0 6 o3 :=
  .cons (p3_0 _) (OpI.sub (.i 4) (.inr rfl)) (by decide) <|
  .cons (p3_4 _) (OpI.cmpmr (.inl rfl)) (by decide) <|
  .nil 6

def j3 : List Byte := [0x75, 0xf3]
theorem j3_0 : ∀ feat, Dec feat j3 0 (FV7z.mk (.jcc 5) 64 [.rel 18446744073709551603] 2) := by dec_rfl

/-- The stretch at `37`. -/
def p4 : List Byte := [
  0x48, 0x29, 0xd0, 0x48, 0xc1, 0xf8, 0x02]

theorem p4_0 : ∀ feat, Dec feat p4 0 (FV7z.mk .sub 64 [gr 64 0, Src.opd 64 (.r 2)] 3) := by dec_rfl
theorem p4_3 : ∀ feat, Dec feat p4 3 (FV7z.mk .sar 64 [gr 64 0, Src.opd 8 (.i 2)] 4) := by dec_rfl

/-- What the stretch does. -/
def o4 : List Op := [
  Op.sub 64 0 (.r 2),
  Op.sar64 0 (.i 2)]

theorem b4 (prof : Profile) : Blk prof p4 0 7 o4 :=
  .cons (p4_0 _) (OpI.sub (.r 2) (.inr rfl)) (by decide) <|
  .cons (p4_3 _) (OpI.sar64 (.i 2)) (by decide) <|
  .nil 7

/-- The stretch at `48`. -/
def p5 : List Byte := [
  0xb8, 0xff, 0xff, 0xff, 0xff]

theorem p5_0 : ∀ feat, Dec feat p5 0 (FV7z.mk .mov 32 [gr 32 0, Src.opd 32 (.i 4294967295)] 5) := by dec_rfl

/-- What the stretch does. -/
def o5 : List Op := [
  Op.mov 32 0 (.i 4294967295)]

theorem b5 (prof : Profile) : Blk prof p5 0 5 o5 :=
  .cons (p5_0 _) (OpI.mov (.i 4294967295) (.inl rfl)) (by decide) <|
  .nil 5

end FV7z.Rfw
