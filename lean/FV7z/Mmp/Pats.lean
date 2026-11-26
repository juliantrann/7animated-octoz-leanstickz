import FV7z.Lemmas.SpFs
import FV7z.Lemmas.BlkOps2
/-!
# The stretches of straight-line code of `__mmap` (PLAN.md §M, M1)

Each distinct stretch between labels and jumps (`p*`, 7 of them) and each distinct jump (`j*`, 5) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.Mmp
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The stretch at `0`. -/
def p0 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0x41, 0xf7, 0xc1, 0xff, 0x0f, 0x00, 0x00]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem p0_4 : ∀ feat, Dec feat p0 4 (FV7z.mk .test 32 [gr 32 9, Src.opd 32 (.i 4095)] 7) := by dec_rfl

/-- What the stretch does. -/
def o0 : List Op := [
  Op.nop,
  Op.test 32 9 (.i 4095)]

theorem b0 (prof : Profile) : Blk prof p0 0 11 o0 :=
  .cons (p0_0 _) (OpI.endbr) (by decide) <|
  .cons (p0_4 _) (OpI.test (.i 4095) (.inl rfl)) (by decide) <|
  .nil 11

def j0 : List Byte := [0x75, 0x2b]
theorem j0_0 : ∀ feat, Dec feat j0 0 (FV7z.mk (.jcc 5) 64 [.rel 43] 2) := by dec_rfl

/-- The stretch at `13`. -/
def p1 : List Byte := [
  0x55, 0x48, 0x89, 0xfd, 0x53, 0x89, 0xcb, 0x48, 0x85, 0xff]

theorem p1_0 : ∀ feat, Dec feat p1 0 (FV7z.mk .push 64 [gr 64 5] 1) := by dec_rfl
theorem p1_1 : ∀ feat, Dec feat p1 1 (FV7z.mk .mov 64 [gr 64 5, Src.opd 64 (.r 7)] 3) := by dec_rfl
theorem p1_4 : ∀ feat, Dec feat p1 4 (FV7z.mk .push 64 [gr 64 3] 1) := by dec_rfl
theorem p1_5 : ∀ feat, Dec feat p1 5 (FV7z.mk .mov 32 [gr 32 3, Src.opd 32 (.r 1)] 2) := by dec_rfl
theorem p1_7 : ∀ feat, Dec feat p1 7 (FV7z.mk .test 64 [gr 64 7, Src.opd 64 (.r 7)] 3) := by dec_rfl

/-- What the stretch does. -/
def o1 : List Op := [
  Op.push 5,
  Op.mov 64 5 (.r 7),
  Op.push 3,
  Op.mov 32 3 (.r 1),
  Op.test 64 7 (.r 7)]

theorem b1 (prof : Profile) : Blk prof p1 0 10 o1 :=
  .cons (p1_0 _) (OpI.push) (by decide) <|
  .cons (p1_1 _) (OpI.mov (.r 7) (.inr rfl)) (by decide) <|
  .cons (p1_4 _) (OpI.push) (by decide) <|
  .cons (p1_5 _) (OpI.mov (.r 1) (.inl rfl)) (by decide) <|
  .cons (p1_7 _) (OpI.test (.r 7) (.inr rfl)) (by decide) <|
  .nil 10

def j1 : List Byte := [0x74, 0x37]
theorem j1_0 : ∀ feat, Dec feat j1 0 (FV7z.mk (.jcc 4) 64 [.rel 55] 2) := by dec_rfl

/-- The stretch at `25`. -/
def p2 : List Byte := [
  0x41, 0x89, 0xda, 0x48, 0x89, 0xef, 0xb8, 0x09, 0x00, 0x00, 0x00]

theorem p2_0 : ∀ feat, Dec feat p2 0 (FV7z.mk .mov 32 [gr 32 10, Src.opd 32 (.r 3)] 3) := by dec_rfl
theorem p2_3 : ∀ feat, Dec feat p2 3 (FV7z.mk .mov 64 [gr 64 7, Src.opd 64 (.r 5)] 3) := by dec_rfl
theorem p2_6 : ∀ feat, Dec feat p2 6 (FV7z.mk .mov 32 [gr 32 0, Src.opd 32 (.i 9)] 5) := by dec_rfl

/-- What the stretch does. -/
def o2 : List Op := [
  Op.mov 32 10 (.r 3),
  Op.mov 64 7 (.r 5),
  Op.mov 32 0 (.i 9)]

theorem b2 (prof : Profile) : Blk prof p2 0 11 o2 :=
  .cons (p2_0 _) (OpI.mov (.r 3) (.inl rfl)) (by decide) <|
  .cons (p2_3 _) (OpI.mov (.r 5) (.inr rfl)) (by decide) <|
  .cons (p2_6 _) (OpI.mov (.i 9) (.inl rfl)) (by decide) <|
  .nil 11

/-- The stretch at `38`. -/
def p3 : List Byte := [
  0x48, 0x3d, 0x00, 0xf0, 0xff, 0xff]

theorem p3_0 : ∀ feat, Dec feat p3 0 (FV7z.mk .cmp 64 [gr 64 0, Src.opd 64 (.i 18446744073709547520)] 6) := by dec_rfl

/-- What the stretch does. -/
def o3 : List Op := [
  Op.cmp 64 0 (.i 18446744073709547520)]

theorem b3 (prof : Profile) : Blk prof p3 0 6 o3 :=
  .cons (p3_0 _) (OpI.cmp (.i 18446744073709547520) (.inr rfl)) (by decide) <|
  .nil 6

def j2 : List Byte := [0x77, 0x62]
theorem j2_0 : ∀ feat, Dec feat j2 0 (FV7z.mk (.jcc 7) 64 [.rel 98] 2) := by dec_rfl

/-- The stretch at `46`. -/
def p4 : List Byte := [
  0x5b, 0x5d]

theorem p4_0 : ∀ feat, Dec feat p4 0 (FV7z.mk .pop 64 [gr 64 3] 1) := by dec_rfl
theorem p4_1 : ∀ feat, Dec feat p4 1 (FV7z.mk .pop 64 [gr 64 5] 1) := by dec_rfl

/-- What the stretch does. -/
def o4 : List Op := [
  Op.pop 3,
  Op.pop 5]

theorem b4 (prof : Profile) : Blk prof p4 0 2 o4 :=
  .cons (p4_0 _) (OpI.pop) (by decide) <|
  .cons (p4_1 _) (OpI.pop) (by decide) <|
  .nil 2

/-- The stretch at `80`. -/
def p5 : List Byte := [
  0xf6, 0xc2, 0x04]

theorem p5_0 : ∀ feat, Dec feat p5 0 (FV7z.mk .test 8 [gr 8 2, Src.opd 8 (.i 4)] 3) := by dec_rfl

/-- What the stretch does. -/
def o5 : List Op := [
  Op.test 8 2 (.i 4)]

theorem b5 (prof : Profile) : Blk prof p5 0 3 o5 :=
  .cons (p5_0 _) (OpI.test8 (.i 4)) (by decide) <|
  .nil 3

def j3 : List Byte := [0x74, 0xc4]
theorem j3_0 : ∀ feat, Dec feat j3 0 (FV7z.mk (.jcc 4) 64 [.rel 18446744073709551556] 2) := by dec_rfl

/-- The stretch at `144`. -/
def p6 : List Byte := [
  0x48, 0xc7, 0xc2, 0xb8, 0xff, 0xff, 0xff, 0xf7, 0xd8, 0x64, 0x89, 0x02, 0x48, 0xc7, 0xc0, 0xff,
  0xff, 0xff, 0xff]

theorem p6_0 : ∀ feat, Dec feat p6 0 (FV7z.mk .mov 64 [gr 64 2, Src.opd 64 (.i 18446744073709551544)] 7) := by dec_rfl
theorem p6_7 : ∀ feat, Dec feat p6 7 (FV7z.mk .neg 32 [gr 32 0] 2) := by dec_rfl
theorem p6_9 : ∀ feat, Dec feat p6 9 (FV7z.mk .mov 32 [.mem (mf (some 2) none 1 0 32), gr 32 0] 3) := by dec_rfl
theorem p6_12 : ∀ feat, Dec feat p6 12 (FV7z.mk .mov 64 [gr 64 0, Src.opd 64 (.i 18446744073709551615)] 7) := by dec_rfl

/-- What the stretch does. -/
def o6 (fb : Addr) : List Op := [
  Op.mov 64 2 (.i 18446744073709551544),
  Op.neg 32 0,
  Op.stf fb 32 (some 2) none 1 0 0,
  Op.mov 64 0 (.i 18446744073709551615)]

theorem b6 (prof : Profile) (fb : Addr) : BlkF prof p6 (0x6665b0 : Addr) fb 0 19 (o6 fb) :=
  .cons (p6_0 _) (((OpI.mov (.i 18446744073709551544) (.inr rfl)).at _).fs _) (by decide) <|
  .cons (p6_7 _) (((OpI.neg (.inl rfl)).at _).fs _) (by decide) <|
  .cons (p6_9 _) (OpIF.stf (.inl rfl)) (by decide) <|
  .cons (p6_12 _) (((OpI.mov (.i 18446744073709551615) (.inr rfl)).at _).fs _) (by decide) <|
  .nil 19

def j4 : List Byte := [0xeb, 0x89]
theorem j4_0 : ∀ feat, Dec feat j4 0 (FV7z.mk .jmp 64 [.rel 18446744073709551497] 2) := by dec_rfl

end FV7z.Mmp
