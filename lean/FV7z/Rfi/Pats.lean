import FV7z.Lemmas.Sp
import FV7z.Lemmas.BlkOps2
/-!
# The stretches of straight-line code of `__register_frame_info` (PLAN.md G3, startup)

Each distinct stretch between labels and jumps (`p*`, 10 of them) and each distinct jump (`j*`, 7) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.Rfi
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The stretch at `0`. -/
def p0 : List Byte := [
  0x55, 0x53, 0x48, 0x89, 0xf3, 0x48, 0x83, 0xec, 0x08, 0x48, 0xc7, 0xc5, 0x60, 0xeb, 0x5f, 0x00,
  0x48, 0xc7, 0x06, 0xff, 0xff, 0xff, 0xff, 0x48, 0x89, 0x56, 0x08, 0x48, 0x89, 0x4e, 0x10, 0x48,
  0x89, 0x7e, 0x18, 0x48, 0xc7, 0x46, 0x20, 0xf8, 0x07, 0x00, 0x00, 0x48, 0x85, 0xed]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .push 64 [gr 64 5] 1) := by dec_rfl
theorem p0_1 : ∀ feat, Dec feat p0 1 (FV7z.mk .push 64 [gr 64 3] 1) := by dec_rfl
theorem p0_2 : ∀ feat, Dec feat p0 2 (FV7z.mk .mov 64 [gr 64 3, Src.opd 64 (.r 6)] 3) := by dec_rfl
theorem p0_5 : ∀ feat, Dec feat p0 5 (FV7z.mk .sub 64 [gr 64 4, Src.opd 64 (.i 8)] 4) := by dec_rfl
theorem p0_9 : ∀ feat, Dec feat p0 9 (FV7z.mk .mov 64 [gr 64 5, Src.opd 64 (.i 6286176)] 7) := by dec_rfl
theorem p0_16 : ∀ feat, Dec feat p0 16 (FV7z.mk .mov 64 [.mem (mg (some 6) none 1 0 64), .imm 64 18446744073709551615] 7) := by dec_rfl
theorem p0_23 : ∀ feat, Dec feat p0 23 (FV7z.mk .mov 64 [.mem (mg (some 6) none 1 8 64), gr 64 2] 4) := by dec_rfl
theorem p0_27 : ∀ feat, Dec feat p0 27 (FV7z.mk .mov 64 [.mem (mg (some 6) none 1 16 64), gr 64 1] 4) := by dec_rfl
theorem p0_31 : ∀ feat, Dec feat p0 31 (FV7z.mk .mov 64 [.mem (mg (some 6) none 1 24 64), gr 64 7] 4) := by dec_rfl
theorem p0_35 : ∀ feat, Dec feat p0 35 (FV7z.mk .mov 64 [.mem (mg (some 6) none 1 32 64), .imm 64 2040] 8) := by dec_rfl
theorem p0_43 : ∀ feat, Dec feat p0 43 (FV7z.mk .test 64 [gr 64 5, Src.opd 64 (.r 5)] 3) := by dec_rfl

/-- What the stretch does. -/
def o0 : List Op := [
  Op.push 5,
  Op.push 3,
  Op.mov 64 3 (.r 6),
  Op.sub 64 4 (.i 8),
  Op.mov 64 5 (.i 6286176),
  Op.sti 64 (some 6) none 1 0 18446744073709551615,
  Op.st 64 (some 6) none 1 8 2,
  Op.st 64 (some 6) none 1 16 1,
  Op.st 64 (some 6) none 1 24 7,
  Op.sti 64 (some 6) none 1 32 2040,
  Op.test 64 5 (.r 5)]

theorem b0 (prof : Profile) : Blk prof p0 0 46 o0 :=
  .cons (p0_0 _) (OpI.push) (by decide) <|
  .cons (p0_1 _) (OpI.push) (by decide) <|
  .cons (p0_2 _) (OpI.mov (.r 6) (.inr rfl)) (by decide) <|
  .cons (p0_5 _) (OpI.sub (.i 8) (.inr rfl)) (by decide) <|
  .cons (p0_9 _) (OpI.mov (.i 6286176) (.inr rfl)) (by decide) <|
  .cons (p0_16 _) (OpI.sti (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p0_23 _) (OpI.st (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p0_27 _) (OpI.st (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p0_31 _) (OpI.st (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p0_35 _) (OpI.sti (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p0_43 _) (OpI.test (.r 5) (.inr rfl)) (by decide) <|
  .nil 46

def j0 : List Byte := [0x74, 0x0c]
theorem j0_0 : ∀ feat, Dec feat j0 0 (FV7z.mk (.jcc 4) 64 [.rel 12] 2) := by dec_rfl

/-- The stretch at `48`. -/
def p1 : List Byte := [
  0x48, 0x8d, 0x3d, 0x39, 0x0c, 0x19, 0x00]

theorem p1_0 : ∀ feat, Dec feat p1 0 (FV7z.mk .lea 64 [gr 64 7, .mem (mrip 1641529 0)] 7) := by dec_rfl

/-- What the stretch does. -/
def o1 : List Op := [
  Op.mov 64 7 (.i 8008608)]

theorem b1 (prof : Profile) : BlkA prof p1 (0x612760 : Addr) 0 7 o1 :=
  .cons (p1_0 _) (OpIA.lea_rip (by decide)) (by decide) <|
  .nil 7

/-- The stretch at `60`. -/
def p2 : List Byte := [
  0x48, 0x8b, 0x05, 0x65, 0x0c, 0x19, 0x00, 0x48, 0x89, 0x1d, 0x5e, 0x0c, 0x19, 0x00, 0x48, 0x89,
  0x43, 0x28, 0x8b, 0x05, 0x44, 0x0c, 0x19, 0x00, 0x85, 0xc0]

theorem p2_0 : ∀ feat, Dec feat p2 0 (FV7z.mk .mov 64 [gr 64 0, .mem (mrip 1641573 64)] 7) := by dec_rfl
theorem p2_7 : ∀ feat, Dec feat p2 7 (FV7z.mk .mov 64 [.mem (mrip 1641566 64), gr 64 3] 7) := by dec_rfl
theorem p2_14 : ∀ feat, Dec feat p2 14 (FV7z.mk .mov 64 [.mem (mg (some 3) none 1 40 64), gr 64 0] 4) := by dec_rfl
theorem p2_18 : ∀ feat, Dec feat p2 18 (FV7z.mk .mov 32 [gr 32 0, .mem (mrip 1641540 32)] 6) := by dec_rfl
theorem p2_24 : ∀ feat, Dec feat p2 24 (FV7z.mk .test 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl

/-- What the stretch does. -/
def o2 : List Op := [
  Op.lda 64 0 8008664,
  Op.sta 64 8008664 3,
  Op.st 64 (some 3) none 1 40 0,
  Op.lda 32 0 8008648,
  Op.test 32 0 (.r 0)]

theorem b2 (prof : Profile) : BlkA prof p2 (0x61276c : Addr) 0 26 o2 :=
  .cons (p2_0 _) (OpIA.ld_rip (.inr rfl) (by decide)) (by decide) <|
  .cons (p2_7 _) (OpIA.st_rip (.inr (.inr rfl)) (by decide)) (by decide) <|
  .cons (p2_14 _) ((OpI.st (.inr (.inr (.inr rfl)))).at _) (by decide) <|
  .cons (p2_18 _) (OpIA.ld_rip (.inl rfl) (by decide)) (by decide) <|
  .cons (p2_24 _) ((OpI.test (.r 0) (.inl rfl)).at _) (by decide) <|
  .nil 26

def j1 : List Byte := [0x74, 0x28]
theorem j1_0 : ∀ feat, Dec feat j1 0 (FV7z.mk (.jcc 4) 64 [.rel 40] 2) := by dec_rfl

/-- The stretch at `88`. -/
def p3 : List Byte := [
  0x48, 0x85, 0xed]

theorem p3_0 : ∀ feat, Dec feat p3 0 (FV7z.mk .test 64 [gr 64 5, Src.opd 64 (.r 5)] 3) := by dec_rfl

/-- What the stretch does. -/
def o3 : List Op := [
  Op.test 64 5 (.r 5)]

theorem b3 (prof : Profile) : Blk prof p3 0 3 o3 :=
  .cons (p3_0 _) (OpI.test (.r 5) (.inr rfl)) (by decide) <|
  .nil 3

def j2 : List Byte := [0x74, 0x13]
theorem j2_0 : ∀ feat, Dec feat j2 0 (FV7z.mk (.jcc 4) 64 [.rel 19] 2) := by dec_rfl

/-- The stretch at `93`. -/
def p4 : List Byte := [
  0x48, 0x83, 0xc4, 0x08, 0x48, 0x8d, 0x3d, 0x08, 0x0c, 0x19, 0x00, 0x5b, 0x5d]

theorem p4_0 : ∀ feat, Dec feat p4 0 (FV7z.mk .add 64 [gr 64 4, Src.opd 64 (.i 8)] 4) := by dec_rfl
theorem p4_4 : ∀ feat, Dec feat p4 4 (FV7z.mk .lea 64 [gr 64 7, .mem (mrip 1641480 0)] 7) := by dec_rfl
theorem p4_11 : ∀ feat, Dec feat p4 11 (FV7z.mk .pop 64 [gr 64 3] 1) := by dec_rfl
theorem p4_12 : ∀ feat, Dec feat p4 12 (FV7z.mk .pop 64 [gr 64 5] 1) := by dec_rfl

/-- What the stretch does. -/
def o4 : List Op := [
  Op.add 64 4 (.i 8),
  Op.mov 64 7 (.i 8008608),
  Op.pop 3,
  Op.pop 5]

theorem b4 (prof : Profile) : BlkA prof p4 (0x61278d : Addr) 0 13 o4 :=
  .cons (p4_0 _) ((OpI.add (.i 8) (.inr rfl)).at _) (by decide) <|
  .cons (p4_4 _) (OpIA.lea_rip (by decide)) (by decide) <|
  .cons (p4_11 _) ((OpI.pop).at _) (by decide) <|
  .cons (p4_12 _) ((OpI.pop).at _) (by decide) <|
  .nil 13

/-- The stretch at `112`. -/
def p5 : List Byte := [
  0x48, 0x83, 0xc4, 0x08, 0x5b, 0x5d]

theorem p5_0 : ∀ feat, Dec feat p5 0 (FV7z.mk .add 64 [gr 64 4, Src.opd 64 (.i 8)] 4) := by dec_rfl
theorem p5_4 : ∀ feat, Dec feat p5 4 (FV7z.mk .pop 64 [gr 64 3] 1) := by dec_rfl
theorem p5_5 : ∀ feat, Dec feat p5 5 (FV7z.mk .pop 64 [gr 64 5] 1) := by dec_rfl

/-- What the stretch does. -/
def o5 : List Op := [
  Op.add 64 4 (.i 8),
  Op.pop 3,
  Op.pop 5]

theorem b5 (prof : Profile) : Blk prof p5 0 6 o5 :=
  .cons (p5_0 _) (OpI.add (.i 8) (.inr rfl)) (by decide) <|
  .cons (p5_4 _) (OpI.pop) (by decide) <|
  .cons (p5_5 _) (OpI.pop) (by decide) <|
  .nil 6

/-- The stretch at `128`. -/
def p6 : List Byte := [
  0xc7, 0x05, 0x0e, 0x0c, 0x19, 0x00, 0x01, 0x00, 0x00, 0x00]

theorem p6_0 : ∀ feat, Dec feat p6 0 (FV7z.mk .mov 32 [.mem (mrip 1641486 32), .imm 32 1] 10) := by dec_rfl

/-- What the stretch does. -/
def o6 : List Op := [
  Op.stia 32 8008648 1]

theorem b6 (prof : Profile) : BlkA prof p6 (0x6127b0 : Addr) 0 10 o6 :=
  .cons (p6_0 _) (OpIA.sti_rip (.inr (.inl rfl)) (by decide)) (by decide) <|
  .nil 10

def j3 : List Byte := [0xeb, 0xcc]
theorem j3_0 : ∀ feat, Dec feat j3 0 (FV7z.mk .jmp 64 [.rel 18446744073709551564] 2) := by dec_rfl

/-- The stretch at `176`. -/
def p7 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0x48, 0x85, 0xff]

theorem p7_0 : ∀ feat, Dec feat p7 0 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem p7_4 : ∀ feat, Dec feat p7 4 (FV7z.mk .test 64 [gr 64 7, Src.opd 64 (.r 7)] 3) := by dec_rfl

/-- What the stretch does. -/
def o7 : List Op := [
  Op.nop,
  Op.test 64 7 (.r 7)]

theorem b7 (prof : Profile) : Blk prof p7 0 7 o7 :=
  .cons (p7_0 _) (OpI.endbr) (by decide) <|
  .cons (p7_4 _) (OpI.test (.r 7) (.inr rfl)) (by decide) <|
  .nil 7

def j4 : List Byte := [0x74, 0x17]
theorem j4_0 : ∀ feat, Dec feat j4 0 (FV7z.mk (.jcc 4) 64 [.rel 23] 2) := by dec_rfl

/-- The stretch at `185`. -/
def p8 : List Byte := [
  0x8b, 0x07, 0x85, 0xc0]

theorem p8_0 : ∀ feat, Dec feat p8 0 (FV7z.mk .mov 32 [gr 32 0, .mem (mg (some 7) none 1 0 32)] 2) := by dec_rfl
theorem p8_2 : ∀ feat, Dec feat p8 2 (FV7z.mk .test 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl

/-- What the stretch does. -/
def o8 : List Op := [
  Op.ld 32 0 (some 7) none 1 0,
  Op.test 32 0 (.r 0)]

theorem b8 (prof : Profile) : Blk prof p8 0 4 o8 :=
  .cons (p8_0 _) (OpI.ld (.inl rfl)) (by decide) <|
  .cons (p8_2 _) (OpI.test (.r 0) (.inl rfl)) (by decide) <|
  .nil 4

def j5 : List Byte := [0x74, 0x11]
theorem j5_0 : ∀ feat, Dec feat j5 0 (FV7z.mk (.jcc 4) 64 [.rel 17] 2) := by dec_rfl

/-- The stretch at `191`. -/
def p9 : List Byte := [
  0x31, 0xc9, 0x31, 0xd2]

theorem p9_0 : ∀ feat, Dec feat p9 0 (FV7z.mk .xor 32 [gr 32 1, Src.opd 32 (.r 1)] 2) := by dec_rfl
theorem p9_2 : ∀ feat, Dec feat p9 2 (FV7z.mk .xor 32 [gr 32 2, Src.opd 32 (.r 2)] 2) := by dec_rfl

/-- What the stretch does. -/
def o9 : List Op := [
  Op.xor 32 1 (.r 1),
  Op.xor 32 2 (.r 2)]

theorem b9 (prof : Profile) : Blk prof p9 0 4 o9 :=
  .cons (p9_0 _) (OpI.xor (.r 1) (.inl rfl)) (by decide) <|
  .cons (p9_2 _) (OpI.xor (.r 2) (.inl rfl)) (by decide) <|
  .nil 4

def j6 : List Byte := [0xe9, 0x38, 0xff, 0xff, 0xff]
theorem j6_0 : ∀ feat, Dec feat j6 0 (FV7z.mk .jmp 64 [.rel 18446744073709551416] 5) := by dec_rfl

end FV7z.Rfi
