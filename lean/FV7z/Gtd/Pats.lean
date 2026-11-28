import FV7z.Lemmas.SpFs
import FV7z.Lemmas.BlkOps15
import FV7z.Lemmas.BlkOps2
/-!
# The stretches of straight-line code of `__gettimeofday` (PLAN.md §M, M1)

Each distinct stretch between labels and jumps (`p*`, 10 of them) and each distinct jump (`j*`, 6) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.Gtd
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The stretch at `0`. -/
def p0 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0x41, 0x54, 0x49, 0x89, 0xfc, 0x55, 0x48, 0x89, 0xf5, 0x48, 0x83, 0xec,
  0x08, 0x48, 0x85, 0xf6]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem p0_4 : ∀ feat, Dec feat p0 4 (FV7z.mk .push 64 [gr 64 12] 2) := by dec_rfl
theorem p0_6 : ∀ feat, Dec feat p0 6 (FV7z.mk .mov 64 [gr 64 12, Src.opd 64 (.r 7)] 3) := by dec_rfl
theorem p0_9 : ∀ feat, Dec feat p0 9 (FV7z.mk .push 64 [gr 64 5] 1) := by dec_rfl
theorem p0_10 : ∀ feat, Dec feat p0 10 (FV7z.mk .mov 64 [gr 64 5, Src.opd 64 (.r 6)] 3) := by dec_rfl
theorem p0_13 : ∀ feat, Dec feat p0 13 (FV7z.mk .sub 64 [gr 64 4, Src.opd 64 (.i 8)] 4) := by dec_rfl
theorem p0_17 : ∀ feat, Dec feat p0 17 (FV7z.mk .test 64 [gr 64 6, Src.opd 64 (.r 6)] 3) := by dec_rfl

/-- What the stretch does. -/
def o0 : List Op := [
  Op.nop,
  Op.push 12,
  Op.mov 64 12 (.r 7),
  Op.push 5,
  Op.mov 64 5 (.r 6),
  Op.sub 64 4 (.i 8),
  Op.test 64 6 (.r 6)]

theorem b0 (prof : Profile) : Blk prof p0 0 20 o0 :=
  .cons (p0_0 _) (OpI.endbr) (by decide) <|
  .cons (p0_4 _) (OpI.push) (by decide) <|
  .cons (p0_6 _) (OpI.mov (.r 7) (.inr rfl)) (by decide) <|
  .cons (p0_9 _) (OpI.push) (by decide) <|
  .cons (p0_10 _) (OpI.mov (.r 6) (.inr rfl)) (by decide) <|
  .cons (p0_13 _) (OpI.sub (.i 8) (.inr rfl)) (by decide) <|
  .cons (p0_17 _) (OpI.test (.r 6) (.inr rfl)) (by decide) <|
  .nil 20

def j0 : List Byte := [0x75, 0x6a]
theorem j0_0 : ∀ feat, Dec feat j0 0 (FV7z.mk (.jcc 5) 64 [.rel 106] 2) := by dec_rfl

/-- The stretch at `22`. -/
def p1 : List Byte := [
  0x48, 0x8b, 0x05, 0x53, 0x19, 0x13, 0x00, 0x48, 0x85, 0xc0]

theorem p1_0 : ∀ feat, Dec feat p1 0 (FV7z.mk .mov 64 [gr 64 0, .mem (mrip 1251667 64)] 7) := by dec_rfl
theorem p1_7 : ∀ feat, Dec feat p1 7 (FV7z.mk .test 64 [gr 64 0, Src.opd 64 (.r 0)] 3) := by dec_rfl

/-- What the stretch does. -/
def o1 : List Op := [
  Op.lda 64 0 7937232,
  Op.test 64 0 (.r 0)]

theorem b1 (prof : Profile) : BlkA prof p1 (0x660376 : Addr) 0 10 o1 :=
  .cons (p1_0 _) (OpIA.ld_rip (.inr rfl) (by decide)) (by decide) <|
  .cons (p1_7 _) ((OpI.test (.r 0) (.inr rfl)).at _) (by decide) <|
  .nil 10

def j1 : List Byte := [0x74, 0x3e]
theorem j1_0 : ∀ feat, Dec feat j1 0 (FV7z.mk (.jcc 4) 64 [.rel 62] 2) := by dec_rfl

/-- The stretch at `34`. -/
def p2 : List Byte := [
  0x48, 0x89, 0xee, 0x4c, 0x89, 0xe7]

theorem p2_0 : ∀ feat, Dec feat p2 0 (FV7z.mk .mov 64 [gr 64 6, Src.opd 64 (.r 5)] 3) := by dec_rfl
theorem p2_3 : ∀ feat, Dec feat p2 3 (FV7z.mk .mov 64 [gr 64 7, Src.opd 64 (.r 12)] 3) := by dec_rfl

/-- What the stretch does. -/
def o2 : List Op := [
  Op.mov 64 6 (.r 5),
  Op.mov 64 7 (.r 12)]

theorem b2 (prof : Profile) : Blk prof p2 0 6 o2 :=
  .cons (p2_0 _) (OpI.mov (.r 5) (.inr rfl)) (by decide) <|
  .cons (p2_3 _) (OpI.mov (.r 12) (.inr rfl)) (by decide) <|
  .nil 6

/-- The stretch at `42`. -/
def p3 : List Byte := [
  0x48, 0x63, 0xd0, 0x48, 0x81, 0xfa, 0x00, 0xf0, 0xff, 0xff]

theorem p3_0 : ∀ feat, Dec feat p3 0 (FV7z.mk .movsxd 64 [gr 64 2, gr 32 0] 3) := by dec_rfl
theorem p3_3 : ∀ feat, Dec feat p3 3 (FV7z.mk .cmp 64 [gr 64 2, Src.opd 64 (.i 18446744073709547520)] 7) := by dec_rfl

/-- What the stretch does. -/
def o3 : List Op := [
  Op.sxr 2 0,
  Op.cmp 64 2 (.i 18446744073709547520)]

theorem b3 (prof : Profile) : Blk prof p3 0 10 o3 :=
  .cons (p3_0 _) (OpI.sxr) (by decide) <|
  .cons (p3_3 _) (OpI.cmp (.i 18446744073709547520) (.inr rfl)) (by decide) <|
  .nil 10

def j2 : List Byte := [0x76, 0x1b]
theorem j2_0 : ∀ feat, Dec feat j2 0 (FV7z.mk (.jcc 6) 64 [.rel 27] 2) := by dec_rfl

/-- The stretch at `54`. -/
def p4 : List Byte := [
  0x48, 0x83, 0xfa, 0xda]

theorem p4_0 : ∀ feat, Dec feat p4 0 (FV7z.mk .cmp 64 [gr 64 2, Src.opd 64 (.i 18446744073709551578)] 4) := by dec_rfl

/-- What the stretch does. -/
def o4 : List Op := [
  Op.cmp 64 2 (.i 18446744073709551578)]

theorem b4 (prof : Profile) : Blk prof p4 0 4 o4 :=
  .cons (p4_0 _) (OpI.cmp (.i 18446744073709551578) (.inr rfl)) (by decide) <|
  .nil 4

def j3 : List Byte := [0x74, 0x24]
theorem j3_0 : ∀ feat, Dec feat j3 0 (FV7z.mk (.jcc 4) 64 [.rel 36] 2) := by dec_rfl

/-- The stretch at `60`. -/
def p5 : List Byte := [
  0x48, 0xc7, 0xc0, 0xb8, 0xff, 0xff, 0xff, 0xf7, 0xda, 0x64, 0x89, 0x10, 0xb8, 0xff, 0xff, 0xff,
  0xff, 0xf3, 0x0f, 0x1e, 0xfa]

theorem p5_0 : ∀ feat, Dec feat p5 0 (FV7z.mk .mov 64 [gr 64 0, Src.opd 64 (.i 18446744073709551544)] 7) := by dec_rfl
theorem p5_7 : ∀ feat, Dec feat p5 7 (FV7z.mk .neg 32 [gr 32 2] 2) := by dec_rfl
theorem p5_9 : ∀ feat, Dec feat p5 9 (FV7z.mk .mov 32 [.mem (mf (some 0) none 1 0 32), gr 32 2] 3) := by dec_rfl
theorem p5_12 : ∀ feat, Dec feat p5 12 (FV7z.mk .mov 32 [gr 32 0, Src.opd 32 (.i 4294967295)] 5) := by dec_rfl
theorem p5_17 : ∀ feat, Dec feat p5 17 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl

/-- What the stretch does. -/
def o5 (fb : Addr) : List Op := [
  Op.mov 64 0 (.i 18446744073709551544),
  Op.neg 32 2,
  Op.stf fb 32 (some 0) none 1 0 2,
  Op.mov 32 0 (.i 4294967295),
  Op.nop]

theorem b5 (prof : Profile) (fb : Addr) : BlkF prof p5 (0x66039c : Addr) fb 0 21 (o5 fb) :=
  .cons (p5_0 _) (((OpI.mov (.i 18446744073709551544) (.inr rfl)).at _).fs _) (by decide) <|
  .cons (p5_7 _) (((OpI.neg (.inl rfl)).at _).fs _) (by decide) <|
  .cons (p5_9 _) (OpIF.stf (.inl rfl)) (by decide) <|
  .cons (p5_12 _) (((OpI.mov (.i 4294967295) (.inl rfl)).at _).fs _) (by decide) <|
  .cons (p5_17 _) (((OpI.endbr).at _).fs _) (by decide) <|
  .nil 21

/-- The stretch at `81`. -/
def p6 : List Byte := [
  0x48, 0x83, 0xc4, 0x08, 0x5d, 0x41, 0x5c]

theorem p6_0 : ∀ feat, Dec feat p6 0 (FV7z.mk .add 64 [gr 64 4, Src.opd 64 (.i 8)] 4) := by dec_rfl
theorem p6_4 : ∀ feat, Dec feat p6 4 (FV7z.mk .pop 64 [gr 64 5] 1) := by dec_rfl
theorem p6_5 : ∀ feat, Dec feat p6 5 (FV7z.mk .pop 64 [gr 64 12] 2) := by dec_rfl

/-- What the stretch does. -/
def o6 : List Op := [
  Op.add 64 4 (.i 8),
  Op.pop 5,
  Op.pop 12]

theorem b6 (prof : Profile) : Blk prof p6 0 7 o6 :=
  .cons (p6_0 _) (OpI.add (.i 8) (.inr rfl)) (by decide) <|
  .cons (p6_4 _) (OpI.pop) (by decide) <|
  .cons (p6_5 _) (OpI.pop) (by decide) <|
  .nil 7

/-- The stretch at `96`. -/
def p7 : List Byte := [
  0x48, 0x89, 0xee, 0x4c, 0x89, 0xe7, 0xb8, 0x60, 0x00, 0x00, 0x00]

theorem p7_0 : ∀ feat, Dec feat p7 0 (FV7z.mk .mov 64 [gr 64 6, Src.opd 64 (.r 5)] 3) := by dec_rfl
theorem p7_3 : ∀ feat, Dec feat p7 3 (FV7z.mk .mov 64 [gr 64 7, Src.opd 64 (.r 12)] 3) := by dec_rfl
theorem p7_6 : ∀ feat, Dec feat p7 6 (FV7z.mk .mov 32 [gr 32 0, Src.opd 32 (.i 96)] 5) := by dec_rfl

/-- What the stretch does. -/
def o7 : List Op := [
  Op.mov 64 6 (.r 5),
  Op.mov 64 7 (.r 12),
  Op.mov 32 0 (.i 96)]

theorem b7 (prof : Profile) : Blk prof p7 0 11 o7 :=
  .cons (p7_0 _) (OpI.mov (.r 5) (.inr rfl)) (by decide) <|
  .cons (p7_3 _) (OpI.mov (.r 12) (.inr rfl)) (by decide) <|
  .cons (p7_6 _) (OpI.mov (.i 96) (.inl rfl)) (by decide) <|
  .nil 11

/-- The stretch at `109`. -/
def p8 : List Byte := [
  0x48, 0x89, 0xc2, 0x48, 0x3d, 0x00, 0xf0, 0xff, 0xff]

theorem p8_0 : ∀ feat, Dec feat p8 0 (FV7z.mk .mov 64 [gr 64 2, Src.opd 64 (.r 0)] 3) := by dec_rfl
theorem p8_3 : ∀ feat, Dec feat p8 3 (FV7z.mk .cmp 64 [gr 64 0, Src.opd 64 (.i 18446744073709547520)] 6) := by dec_rfl

/-- What the stretch does. -/
def o8 : List Op := [
  Op.mov 64 2 (.r 0),
  Op.cmp 64 0 (.i 18446744073709547520)]

theorem b8 (prof : Profile) : Blk prof p8 0 9 o8 :=
  .cons (p8_0 _) (OpI.mov (.r 0) (.inr rfl)) (by decide) <|
  .cons (p8_3 _) (OpI.cmp (.i 18446744073709547520) (.inr rfl)) (by decide) <|
  .nil 9

def j4 : List Byte := [0x77, 0xc4]
theorem j4_0 : ∀ feat, Dec feat j4 0 (FV7z.mk (.jcc 7) 64 [.rel 18446744073709551556] 2) := by dec_rfl

/-- The stretch at `128`. -/
def p9 : List Byte := [
  0xc6, 0x06, 0x00]

theorem p9_0 : ∀ feat, Dec feat p9 0 (FV7z.mk .mov 8 [.mem (mg (some 6) none 1 0 8), .imm 8 0] 3) := by dec_rfl

/-- What the stretch does. -/
def o9 : List Op := [
  Op.sti 8 (some 6) none 1 0 0]

theorem b9 (prof : Profile) : Blk prof p9 0 3 o9 :=
  .cons (p9_0 _) (OpI.sti (.inl rfl)) (by decide) <|
  .nil 3

def j5 : List Byte := [0xeb, 0x91]
theorem j5_0 : ∀ feat, Dec feat j5 0 (FV7z.mk .jmp 64 [.rel 18446744073709551505] 2) := by dec_rfl

end FV7z.Gtd
