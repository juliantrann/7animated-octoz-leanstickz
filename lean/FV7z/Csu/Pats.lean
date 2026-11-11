import FV7z.Lemmas.Sp
import FV7z.Lemmas.BlkOps3
/-!
# The stretches of straight-line code of `__libc_csu_init` (PLAN.md G3, startup)

Each distinct stretch between labels and jumps (`p*`, 7 of them) and each distinct jump (`j*`, 2) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.Csu
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The stretch at `0`. -/
def p0 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0x41, 0x57, 0x4c, 0x8d, 0x3d, 0xeb, 0x3a, 0x16, 0x00, 0x41, 0x56, 0x4c,
  0x8d, 0x35, 0xea, 0x3a, 0x16, 0x00, 0x41, 0x55, 0x4d, 0x29, 0xfe, 0x49, 0x89, 0xd5, 0x41, 0x54,
  0x49, 0x89, 0xf4, 0x55, 0x89, 0xfd, 0x53, 0x48, 0x83, 0xec, 0x08, 0x49, 0xc1, 0xfe, 0x03]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem p0_4 : ∀ feat, Dec feat p0 4 (FV7z.mk .push 64 [gr 64 15] 2) := by dec_rfl
theorem p0_6 : ∀ feat, Dec feat p0 6 (FV7z.mk .lea 64 [gr 64 15, .mem (mrip 1456875 0)] 7) := by dec_rfl
theorem p0_13 : ∀ feat, Dec feat p0 13 (FV7z.mk .push 64 [gr 64 14] 2) := by dec_rfl
theorem p0_15 : ∀ feat, Dec feat p0 15 (FV7z.mk .lea 64 [gr 64 14, .mem (mrip 1456874 0)] 7) := by dec_rfl
theorem p0_22 : ∀ feat, Dec feat p0 22 (FV7z.mk .push 64 [gr 64 13] 2) := by dec_rfl
theorem p0_24 : ∀ feat, Dec feat p0 24 (FV7z.mk .sub 64 [gr 64 14, Src.opd 64 (.r 15)] 3) := by dec_rfl
theorem p0_27 : ∀ feat, Dec feat p0 27 (FV7z.mk .mov 64 [gr 64 13, Src.opd 64 (.r 2)] 3) := by dec_rfl
theorem p0_30 : ∀ feat, Dec feat p0 30 (FV7z.mk .push 64 [gr 64 12] 2) := by dec_rfl
theorem p0_32 : ∀ feat, Dec feat p0 32 (FV7z.mk .mov 64 [gr 64 12, Src.opd 64 (.r 6)] 3) := by dec_rfl
theorem p0_35 : ∀ feat, Dec feat p0 35 (FV7z.mk .push 64 [gr 64 5] 1) := by dec_rfl
theorem p0_36 : ∀ feat, Dec feat p0 36 (FV7z.mk .mov 32 [gr 32 5, Src.opd 32 (.r 7)] 2) := by dec_rfl
theorem p0_38 : ∀ feat, Dec feat p0 38 (FV7z.mk .push 64 [gr 64 3] 1) := by dec_rfl
theorem p0_39 : ∀ feat, Dec feat p0 39 (FV7z.mk .sub 64 [gr 64 4, Src.opd 64 (.i 8)] 4) := by dec_rfl
theorem p0_43 : ∀ feat, Dec feat p0 43 (FV7z.mk .sar 64 [gr 64 14, Src.opd 8 (.i 3)] 4) := by dec_rfl

/-- What the stretch does. -/
def o0 : List Op := [
  Op.nop,
  Op.push 15,
  Op.mov 64 15 (.i 7829400),
  Op.push 14,
  Op.mov 64 14 (.i 7829408),
  Op.push 13,
  Op.sub 64 14 (.r 15),
  Op.mov 64 13 (.r 2),
  Op.push 12,
  Op.mov 64 12 (.r 6),
  Op.push 5,
  Op.mov 32 5 (.r 7),
  Op.push 3,
  Op.sub 64 4 (.i 8),
  Op.sar64 14 (.i 3)]

theorem b0 (prof : Profile) : BlkA prof p0 (0x613ca0 : Addr) 0 47 o0 :=
  .cons (p0_0 _) ((OpI.endbr).at _) (by decide) <|
  .cons (p0_4 _) ((OpI.push).at _) (by decide) <|
  .cons (p0_6 _) (OpIA.lea_rip (by decide)) (by decide) <|
  .cons (p0_13 _) ((OpI.push).at _) (by decide) <|
  .cons (p0_15 _) (OpIA.lea_rip (by decide)) (by decide) <|
  .cons (p0_22 _) ((OpI.push).at _) (by decide) <|
  .cons (p0_24 _) ((OpI.sub (.r 15) (.inr rfl)).at _) (by decide) <|
  .cons (p0_27 _) ((OpI.mov (.r 2) (.inr rfl)).at _) (by decide) <|
  .cons (p0_30 _) ((OpI.push).at _) (by decide) <|
  .cons (p0_32 _) ((OpI.mov (.r 6) (.inr rfl)).at _) (by decide) <|
  .cons (p0_35 _) ((OpI.push).at _) (by decide) <|
  .cons (p0_36 _) ((OpI.mov (.r 7) (.inl rfl)).at _) (by decide) <|
  .cons (p0_38 _) ((OpI.push).at _) (by decide) <|
  .cons (p0_39 _) ((OpI.sub (.i 8) (.inr rfl)).at _) (by decide) <|
  .cons (p0_43 _) ((OpI.sar64 (.i 3)).at _) (by decide) <|
  .nil 47

def j0 : List Byte := [0x74, 0x1c]
theorem j0_0 : ∀ feat, Dec feat j0 0 (FV7z.mk (.jcc 4) 64 [.rel 28] 2) := by dec_rfl

/-- The stretch at `49`. -/
def p1 : List Byte := [
  0x31, 0xdb, 0x0f, 0x1f, 0x44, 0x00, 0x00]

theorem p1_0 : ∀ feat, Dec feat p1 0 (FV7z.mk .xor 32 [gr 32 3, Src.opd 32 (.r 3)] 2) := by dec_rfl
theorem p1_2 : ∀ feat, Dec feat p1 2 (FV7z.mk .nop 32 [.mem (mg (some 0) (some 0) 1 0 32)] 5) := by dec_rfl

/-- What the stretch does. -/
def o1 : List Op := [
  Op.xor 32 3 (.r 3),
  Op.nop]

theorem b1 (prof : Profile) : Blk prof p1 0 7 o1 :=
  .cons (p1_0 _) (OpI.xor (.r 3) (.inl rfl)) (by decide) <|
  .cons (p1_2 _) (OpI.nop) (by decide) <|
  .nil 7

/-- The stretch at `56`. -/
def p2 : List Byte := [
  0x4c, 0x89, 0xea, 0x4c, 0x89, 0xe6, 0x89, 0xef]

theorem p2_0 : ∀ feat, Dec feat p2 0 (FV7z.mk .mov 64 [gr 64 2, Src.opd 64 (.r 13)] 3) := by dec_rfl
theorem p2_3 : ∀ feat, Dec feat p2 3 (FV7z.mk .mov 64 [gr 64 6, Src.opd 64 (.r 12)] 3) := by dec_rfl
theorem p2_6 : ∀ feat, Dec feat p2 6 (FV7z.mk .mov 32 [gr 32 7, Src.opd 32 (.r 5)] 2) := by dec_rfl

/-- What the stretch does. -/
def o2 : List Op := [
  Op.mov 64 2 (.r 13),
  Op.mov 64 6 (.r 12),
  Op.mov 32 7 (.r 5)]

theorem b2 (prof : Profile) : Blk prof p2 0 8 o2 :=
  .cons (p2_0 _) (OpI.mov (.r 13) (.inr rfl)) (by decide) <|
  .cons (p2_3 _) (OpI.mov (.r 12) (.inr rfl)) (by decide) <|
  .cons (p2_6 _) (OpI.mov (.r 5) (.inl rfl)) (by decide) <|
  .nil 8

/-- The stretch at `68`. -/
def p3 : List Byte := [
  0x48, 0x83, 0xc3, 0x01, 0x49, 0x39, 0xde]

theorem p3_0 : ∀ feat, Dec feat p3 0 (FV7z.mk .add 64 [gr 64 3, Src.opd 64 (.i 1)] 4) := by dec_rfl
theorem p3_4 : ∀ feat, Dec feat p3 4 (FV7z.mk .cmp 64 [gr 64 14, Src.opd 64 (.r 3)] 3) := by dec_rfl

/-- What the stretch does. -/
def o3 : List Op := [
  Op.add 64 3 (.i 1),
  Op.cmp 64 14 (.r 3)]

theorem b3 (prof : Profile) : Blk prof p3 0 7 o3 :=
  .cons (p3_0 _) (OpI.add (.i 1) (.inr rfl)) (by decide) <|
  .cons (p3_4 _) (OpI.cmp (.r 3) (.inr rfl)) (by decide) <|
  .nil 7

def j1 : List Byte := [0x75, 0xeb]
theorem j1_0 : ∀ feat, Dec feat j1 0 (FV7z.mk (.jcc 5) 64 [.rel 18446744073709551595] 2) := by dec_rfl

/-- The stretch at `77`. -/
def p4 : List Byte := [
  0x4c, 0x8d, 0x3d, 0xac, 0x3a, 0x16, 0x00, 0x4c, 0x8d, 0x35, 0xd5, 0x3d, 0x16, 0x00]

theorem p4_0 : ∀ feat, Dec feat p4 0 (FV7z.mk .lea 64 [gr 64 15, .mem (mrip 1456812 0)] 7) := by dec_rfl
theorem p4_7 : ∀ feat, Dec feat p4 7 (FV7z.mk .lea 64 [gr 64 14, .mem (mrip 1457621 0)] 7) := by dec_rfl

/-- What the stretch does. -/
def o4 : List Op := [
  Op.mov 64 15 (.i 7829408),
  Op.mov 64 14 (.i 7830224)]

theorem b4 (prof : Profile) : BlkA prof p4 (0x613ced : Addr) 0 14 o4 :=
  .cons (p4_0 _) (OpIA.lea_rip (by decide)) (by decide) <|
  .cons (p4_7 _) (OpIA.lea_rip (by decide)) (by decide) <|
  .nil 14

/-- The stretch at `96`. -/
def p5 : List Byte := [
  0x4d, 0x29, 0xfe, 0x49, 0xc1, 0xfe, 0x03]

theorem p5_0 : ∀ feat, Dec feat p5 0 (FV7z.mk .sub 64 [gr 64 14, Src.opd 64 (.r 15)] 3) := by dec_rfl
theorem p5_3 : ∀ feat, Dec feat p5 3 (FV7z.mk .sar 64 [gr 64 14, Src.opd 8 (.i 3)] 4) := by dec_rfl

/-- What the stretch does. -/
def o5 : List Op := [
  Op.sub 64 14 (.r 15),
  Op.sar64 14 (.i 3)]

theorem b5 (prof : Profile) : Blk prof p5 0 7 o5 :=
  .cons (p5_0 _) (OpI.sub (.r 15) (.inr rfl)) (by decide) <|
  .cons (p5_3 _) (OpI.sar64 (.i 3)) (by decide) <|
  .nil 7

/-- The stretch at `133`. -/
def p6 : List Byte := [
  0x48, 0x83, 0xc4, 0x08, 0x5b, 0x5d, 0x41, 0x5c, 0x41, 0x5d, 0x41, 0x5e, 0x41, 0x5f]

theorem p6_0 : ∀ feat, Dec feat p6 0 (FV7z.mk .add 64 [gr 64 4, Src.opd 64 (.i 8)] 4) := by dec_rfl
theorem p6_4 : ∀ feat, Dec feat p6 4 (FV7z.mk .pop 64 [gr 64 3] 1) := by dec_rfl
theorem p6_5 : ∀ feat, Dec feat p6 5 (FV7z.mk .pop 64 [gr 64 5] 1) := by dec_rfl
theorem p6_6 : ∀ feat, Dec feat p6 6 (FV7z.mk .pop 64 [gr 64 12] 2) := by dec_rfl
theorem p6_8 : ∀ feat, Dec feat p6 8 (FV7z.mk .pop 64 [gr 64 13] 2) := by dec_rfl
theorem p6_10 : ∀ feat, Dec feat p6 10 (FV7z.mk .pop 64 [gr 64 14] 2) := by dec_rfl
theorem p6_12 : ∀ feat, Dec feat p6 12 (FV7z.mk .pop 64 [gr 64 15] 2) := by dec_rfl

/-- What the stretch does. -/
def o6 : List Op := [
  Op.add 64 4 (.i 8),
  Op.pop 3,
  Op.pop 5,
  Op.pop 12,
  Op.pop 13,
  Op.pop 14,
  Op.pop 15]

theorem b6 (prof : Profile) : Blk prof p6 0 14 o6 :=
  .cons (p6_0 _) (OpI.add (.i 8) (.inr rfl)) (by decide) <|
  .cons (p6_4 _) (OpI.pop) (by decide) <|
  .cons (p6_5 _) (OpI.pop) (by decide) <|
  .cons (p6_6 _) (OpI.pop) (by decide) <|
  .cons (p6_8 _) (OpI.pop) (by decide) <|
  .cons (p6_10 _) (OpI.pop) (by decide) <|
  .cons (p6_12 _) (OpI.pop) (by decide) <|
  .nil 14

end FV7z.Csu
