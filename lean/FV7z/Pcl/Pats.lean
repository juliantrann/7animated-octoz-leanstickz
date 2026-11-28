import FV7z.Lemmas.Sp
import FV7z.Lemmas.CmpMi16
import FV7z.Lemmas.BlkOps25
import FV7z.Lemmas.BlkOps16
import FV7z.Lemmas.BlkOps2
/-!
# The stretches of straight-line code of `NWindows::NCOM::PropVariant_Clear` (PLAN.md §M, M1)

Each distinct stretch between labels and jumps (`p*`, 9 of them) and each distinct jump (`j*`, 5) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.Pcl
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The stretch at `0`. -/
def p0 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0x53, 0x0f, 0xb7, 0x07, 0x48, 0x89, 0xfb, 0x66, 0x83, 0xf8, 0x07]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem p0_4 : ∀ feat, Dec feat p0 4 (FV7z.mk .push 64 [gr 64 3] 1) := by dec_rfl
theorem p0_5 : ∀ feat, Dec feat p0 5 (FV7z.mk .movzx 32 [gr 32 0, .mem (mg (some 7) none 1 0 16)] 3) := by dec_rfl
theorem p0_8 : ∀ feat, Dec feat p0 8 (FV7z.mk .mov 64 [gr 64 3, Src.opd 64 (.r 7)] 3) := by dec_rfl
theorem p0_11 : ∀ feat, Dec feat p0 11 (FV7z.mk .cmp 16 [gr 16 0, Src.opd 16 (.i 7)] 4) := by dec_rfl

/-- What the stretch does. -/
def o0 : List Op := [
  Op.nop,
  Op.push 3,
  Op.ldzx 16 0 (some 7) none 1 0,
  Op.mov 64 3 (.r 7),
  Op.cmp 16 0 (.i 7)]

theorem b0 (prof : Profile) : Blk prof p0 0 15 o0 :=
  .cons (p0_0 _) (OpI.endbr) (by decide) <|
  .cons (p0_4 _) (OpI.push) (by decide) <|
  .cons (p0_5 _) (OpI.ldzx (.inr rfl)) (by decide) <|
  .cons (p0_8 _) (OpI.mov (.r 7) (.inr rfl)) (by decide) <|
  .cons (p0_11 _) (OpI.cmp16 (.i 7)) (by decide) <|
  .nil 15

def j0 : List Byte := [0x76, 0x2d]
theorem j0_0 : ∀ feat, Dec feat j0 0 (FV7z.mk (.jcc 6) 64 [.rel 45] 2) := by dec_rfl

/-- The stretch at `17`. -/
def p1 : List Byte := [
  0x83, 0xe8, 0x0a, 0x66, 0x83, 0xf8, 0x36]

theorem p1_0 : ∀ feat, Dec feat p1 0 (FV7z.mk .sub 32 [gr 32 0, Src.opd 32 (.i 10)] 3) := by dec_rfl
theorem p1_3 : ∀ feat, Dec feat p1 3 (FV7z.mk .cmp 16 [gr 16 0, Src.opd 16 (.i 54)] 4) := by dec_rfl

/-- What the stretch does. -/
def o1 : List Op := [
  Op.sub 32 0 (.i 10),
  Op.cmp 16 0 (.i 54)]

theorem b1 (prof : Profile) : Blk prof p1 0 7 o1 :=
  .cons (p1_0 _) (OpI.sub (.i 10) (.inl rfl)) (by decide) <|
  .cons (p1_3 _) (OpI.cmp16 (.i 54)) (by decide) <|
  .nil 7

def j1 : List Byte := [0x77, 0x10]
theorem j1_0 : ∀ feat, Dec feat j1 0 (FV7z.mk (.jcc 7) 64 [.rel 16] 2) := by dec_rfl

/-- The stretch at `26`. -/
def p2 : List Byte := [
  0x48, 0xba, 0xc3, 0x3f, 0x00, 0x00, 0x00, 0x00, 0x40, 0x00, 0x48, 0x0f, 0xa3, 0xc2]

theorem p2_0 : ∀ feat, Dec feat p2 0 (FV7z.mk .mov 64 [gr 64 2, Src.opd 64 (.i 18014398509498307)] 10) := by dec_rfl
theorem p2_10 : ∀ feat, Dec feat p2 10 (FV7z.mk (.bit (BitMn.bt)) 64 [gr 64 2, gr 64 0] 4) := by dec_rfl

/-- What the stretch does. -/
def o2 : List Op := [
  Op.mov 64 2 (.i 18014398509498307),
  Op.bt64 2 0]

theorem b2 (prof : Profile) : Blk prof p2 0 14 o2 :=
  .cons (p2_0 _) (OpI.mov (.i 18014398509498307) (.inr rfl)) (by decide) <|
  .cons (p2_10 _) (OpI.bt64) (by decide) <|
  .nil 14

def j2 : List Byte := [0x72, 0x14]
theorem j2_0 : ∀ feat, Dec feat j2 0 (FV7z.mk (.jcc 2) 64 [.rel 20] 2) := by dec_rfl

/-- The stretch at `42`. -/
def p3 : List Byte := [
  0x48, 0x89, 0xdf]

theorem p3_0 : ∀ feat, Dec feat p3 0 (FV7z.mk .mov 64 [gr 64 7, Src.opd 64 (.r 3)] 3) := by dec_rfl

/-- What the stretch does. -/
def o3 : List Op := [
  Op.mov 64 7 (.r 3)]

theorem b3 (prof : Profile) : Blk prof p3 0 3 o3 :=
  .cons (p3_0 _) (OpI.mov (.r 3) (.inr rfl)) (by decide) <|
  .nil 3

/-- The stretch at `50`. -/
def p4 : List Byte := [
  0x85, 0xc0]

theorem p4_0 : ∀ feat, Dec feat p4 0 (FV7z.mk .test 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl

/-- What the stretch does. -/
def o4 : List Op := [
  Op.test 32 0 (.r 0)]

theorem b4 (prof : Profile) : Blk prof p4 0 2 o4 :=
  .cons (p4_0 _) (OpI.test (.r 0) (.inl rfl)) (by decide) <|
  .nil 2

def j3 : List Byte := [0x75, 0x06]
theorem j3_0 : ∀ feat, Dec feat j3 0 (FV7z.mk (.jcc 5) 64 [.rel 6] 2) := by dec_rfl

/-- The stretch at `54`. -/
def p5 : List Byte := [
  0x66, 0x83, 0x3b, 0x00]

theorem p5_0 : ∀ feat, Dec feat p5 0 (FV7z.mk .cmp 16 [.mem (mg (some 3) none 1 0 16), .imm 16 0] 4) := by dec_rfl

/-- What the stretch does. -/
def o5 : List Op := [
  Op.cmpmi 16 (some 3) none 1 0 0]

theorem b5 (prof : Profile) : Blk prof p5 0 4 o5 :=
  .cons (p5_0 _) (OpI.cmpmi16) (by decide) <|
  .nil 4

def j4 : List Byte := [0x74, 0x07]
theorem j4_0 : ∀ feat, Dec feat j4 0 (FV7z.mk (.jcc 4) 64 [.rel 7] 2) := by dec_rfl

/-- The stretch at `60`. -/
def p6 : List Byte := [
  0x5b]

theorem p6_0 : ∀ feat, Dec feat p6 0 (FV7z.mk .pop 64 [gr 64 3] 1) := by dec_rfl

/-- What the stretch does. -/
def o6 : List Op := [
  Op.pop 3]

theorem b6 (prof : Profile) : Blk prof p6 0 1 o6 :=
  .cons (p6_0 _) (OpI.pop) (by decide) <|
  .nil 1

/-- The stretch at `62`. -/
def p7 : List Byte := [
  0x31, 0xd2, 0x66, 0x89, 0x13]

theorem p7_0 : ∀ feat, Dec feat p7 0 (FV7z.mk .xor 32 [gr 32 2, Src.opd 32 (.r 2)] 2) := by dec_rfl
theorem p7_2 : ∀ feat, Dec feat p7 2 (FV7z.mk .mov 16 [.mem (mg (some 3) none 1 0 16), gr 16 2] 3) := by dec_rfl

/-- What the stretch does. -/
def o7 : List Op := [
  Op.xor 32 2 (.r 2),
  Op.st 16 (some 3) none 1 0 2]

theorem b7 (prof : Profile) : Blk prof p7 0 5 o7 :=
  .cons (p7_0 _) (OpI.xor (.r 2) (.inl rfl)) (by decide) <|
  .cons (p7_2 _) (OpI.st (.inr (.inl rfl))) (by decide) <|
  .nil 5

/-- The stretch at `67`. -/
def p8 : List Byte := [
  0x31, 0xc0, 0xc7, 0x43, 0x04, 0x00, 0x00, 0x00, 0x00, 0x66, 0x89, 0x43, 0x02, 0x31, 0xc0, 0x48,
  0xc7, 0x43, 0x08, 0x00, 0x00, 0x00, 0x00, 0x5b]

theorem p8_0 : ∀ feat, Dec feat p8 0 (FV7z.mk .xor 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl
theorem p8_2 : ∀ feat, Dec feat p8 2 (FV7z.mk .mov 32 [.mem (mg (some 3) none 1 4 32), .imm 32 0] 7) := by dec_rfl
theorem p8_9 : ∀ feat, Dec feat p8 9 (FV7z.mk .mov 16 [.mem (mg (some 3) none 1 2 16), gr 16 0] 4) := by dec_rfl
theorem p8_13 : ∀ feat, Dec feat p8 13 (FV7z.mk .xor 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl
theorem p8_15 : ∀ feat, Dec feat p8 15 (FV7z.mk .mov 64 [.mem (mg (some 3) none 1 8 64), .imm 64 0] 8) := by dec_rfl
theorem p8_23 : ∀ feat, Dec feat p8 23 (FV7z.mk .pop 64 [gr 64 3] 1) := by dec_rfl

/-- What the stretch does. -/
def o8 : List Op := [
  Op.xor 32 0 (.r 0),
  Op.sti 32 (some 3) none 1 4 0,
  Op.st 16 (some 3) none 1 2 0,
  Op.xor 32 0 (.r 0),
  Op.sti 64 (some 3) none 1 8 0,
  Op.pop 3]

theorem b8 (prof : Profile) : Blk prof p8 0 24 o8 :=
  .cons (p8_0 _) (OpI.xor (.r 0) (.inl rfl)) (by decide) <|
  .cons (p8_2 _) (OpI.sti (.inr (.inr (.inl rfl)))) (by decide) <|
  .cons (p8_9 _) (OpI.st (.inr (.inl rfl))) (by decide) <|
  .cons (p8_13 _) (OpI.xor (.r 0) (.inl rfl)) (by decide) <|
  .cons (p8_15 _) (OpI.sti (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p8_23 _) (OpI.pop) (by decide) <|
  .nil 24

end FV7z.Pcl
