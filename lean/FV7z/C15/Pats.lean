import FV7z.Lemmas.Sp
import FV7z.Lemmas.BlkOps14
import FV7z.Lemmas.BlkOps3
/-!
# The stretches of straight-line code of `Crc64GenerateTable` (PLAN.md G3, constructors)

Each distinct stretch between labels and jumps (`p*`, 6 of them) and each distinct jump (`j*`, 3) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.C15
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The stretch at `0`. -/
def p0 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0x31, 0xff, 0x4c, 0x8d, 0x05, 0x43, 0x29, 0x35, 0x00, 0x48, 0xbe, 0x42,
  0x0f, 0x87, 0xd7, 0x95, 0x57, 0x6c, 0xc9, 0x66, 0x0f, 0x1f, 0x84, 0x00, 0x00, 0x00, 0x00, 0x00]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem p0_4 : ∀ feat, Dec feat p0 4 (FV7z.mk .xor 32 [gr 32 7, Src.opd 32 (.r 7)] 2) := by dec_rfl
theorem p0_6 : ∀ feat, Dec feat p0 6 (FV7z.mk .lea 64 [gr 64 8, .mem (mrip 3483971 0)] 7) := by dec_rfl
theorem p0_13 : ∀ feat, Dec feat p0 13 (FV7z.mk .mov 64 [gr 64 6, Src.opd 64 (.i 14514072000185962306)] 10) := by dec_rfl
theorem p0_23 : ∀ feat, Dec feat p0 23 (FV7z.mk .nop 16 [.mem (mg (some 0) (some 0) 1 0 16)] 9) := by dec_rfl

/-- What the stretch does. -/
def o0 : List Op := [
  Op.nop,
  Op.xor 32 7 (.r 7),
  Op.mov 64 8 (.i 7956416),
  Op.mov 64 6 (.i 14514072000185962306),
  Op.nop]

theorem b0 (prof : Profile) : BlkA prof p0 (0x443e70 : Addr) 0 32 o0 :=
  .cons (p0_0 _) ((OpI.endbr).at _) (by decide) <|
  .cons (p0_4 _) ((OpI.xor (.r 7) (.inl rfl)).at _) (by decide) <|
  .cons (p0_6 _) (OpIA.lea_rip (by decide)) (by decide) <|
  .cons (p0_13 _) ((OpI.mov (.i 14514072000185962306) (.inr rfl)).at _) (by decide) <|
  .cons (p0_23 _) ((OpI.nop).at _) (by decide) <|
  .nil 32

/-- The stretch at `32`. -/
def p1 : List Byte := [
  0x48, 0x89, 0xf8, 0xba, 0x08, 0x00, 0x00, 0x00, 0x0f, 0x1f, 0x84, 0x00, 0x00, 0x00, 0x00, 0x00]

theorem p1_0 : ∀ feat, Dec feat p1 0 (FV7z.mk .mov 64 [gr 64 0, Src.opd 64 (.r 7)] 3) := by dec_rfl
theorem p1_3 : ∀ feat, Dec feat p1 3 (FV7z.mk .mov 32 [gr 32 2, Src.opd 32 (.i 8)] 5) := by dec_rfl
theorem p1_8 : ∀ feat, Dec feat p1 8 (FV7z.mk .nop 32 [.mem (mg (some 0) (some 0) 1 0 32)] 8) := by dec_rfl

/-- What the stretch does. -/
def o1 : List Op := [
  Op.mov 64 0 (.r 7),
  Op.mov 32 2 (.i 8),
  Op.nop]

theorem b1 (prof : Profile) : Blk prof p1 0 16 o1 :=
  .cons (p1_0 _) (OpI.mov (.r 7) (.inr rfl)) (by decide) <|
  .cons (p1_3 _) (OpI.mov (.i 8) (.inl rfl)) (by decide) <|
  .cons (p1_8 _) (OpI.nop) (by decide) <|
  .nil 16

/-- The stretch at `48`. -/
def p2 : List Byte := [
  0x48, 0x89, 0xc1, 0x83, 0xe0, 0x01, 0x48, 0xf7, 0xd8, 0x48, 0xd1, 0xe9, 0x48, 0x21, 0xf0, 0x48,
  0x31, 0xc8, 0x83, 0xea, 0x01]

theorem p2_0 : ∀ feat, Dec feat p2 0 (FV7z.mk .mov 64 [gr 64 1, Src.opd 64 (.r 0)] 3) := by dec_rfl
theorem p2_3 : ∀ feat, Dec feat p2 3 (FV7z.mk .and 32 [gr 32 0, Src.opd 32 (.i 1)] 3) := by dec_rfl
theorem p2_6 : ∀ feat, Dec feat p2 6 (FV7z.mk .neg 64 [gr 64 0] 3) := by dec_rfl
theorem p2_9 : ∀ feat, Dec feat p2 9 (FV7z.mk .shr 64 [gr 64 1, Src.opd 8 (.i 1)] 3) := by dec_rfl
theorem p2_12 : ∀ feat, Dec feat p2 12 (FV7z.mk .and 64 [gr 64 0, Src.opd 64 (.r 6)] 3) := by dec_rfl
theorem p2_15 : ∀ feat, Dec feat p2 15 (FV7z.mk .xor 64 [gr 64 0, Src.opd 64 (.r 1)] 3) := by dec_rfl
theorem p2_18 : ∀ feat, Dec feat p2 18 (FV7z.mk .sub 32 [gr 32 2, Src.opd 32 (.i 1)] 3) := by dec_rfl

/-- What the stretch does. -/
def o2 : List Op := [
  Op.mov 64 1 (.r 0),
  Op.and 32 0 (.i 1),
  Op.neg 64 0,
  Op.shr64 1 (.i 1),
  Op.and 64 0 (.r 6),
  Op.xor 64 0 (.r 1),
  Op.sub 32 2 (.i 1)]

theorem b2 (prof : Profile) : Blk prof p2 0 21 o2 :=
  .cons (p2_0 _) (OpI.mov (.r 0) (.inr rfl)) (by decide) <|
  .cons (p2_3 _) (OpI.and (.i 1) (.inl rfl)) (by decide) <|
  .cons (p2_6 _) (OpI.neg (.inr rfl)) (by decide) <|
  .cons (p2_9 _) (OpI.shr64 (.i 1)) (by decide) <|
  .cons (p2_12 _) (OpI.and (.r 6) (.inr rfl)) (by decide) <|
  .cons (p2_15 _) (OpI.xor (.r 1) (.inr rfl)) (by decide) <|
  .cons (p2_18 _) (OpI.sub (.i 1) (.inl rfl)) (by decide) <|
  .nil 21

def j0 : List Byte := [0x75, 0xe9]
theorem j0_0 : ∀ feat, Dec feat j0 0 (FV7z.mk (.jcc 5) 64 [.rel 18446744073709551593] 2) := by dec_rfl

/-- The stretch at `71`. -/
def p3 : List Byte := [
  0x49, 0x89, 0x04, 0xf8, 0x48, 0x83, 0xc7, 0x01, 0x48, 0x81, 0xff, 0x00, 0x01, 0x00, 0x00]

theorem p3_0 : ∀ feat, Dec feat p3 0 (FV7z.mk .mov 64 [.mem (mg (some 8) (some 7) 8 0 64), gr 64 0] 4) := by dec_rfl
theorem p3_4 : ∀ feat, Dec feat p3 4 (FV7z.mk .add 64 [gr 64 7, Src.opd 64 (.i 1)] 4) := by dec_rfl
theorem p3_8 : ∀ feat, Dec feat p3 8 (FV7z.mk .cmp 64 [gr 64 7, Src.opd 64 (.i 256)] 7) := by dec_rfl

/-- What the stretch does. -/
def o3 : List Op := [
  Op.st 64 (some 8) (some 7) 8 0 0,
  Op.add 64 7 (.i 1),
  Op.cmp 64 7 (.i 256)]

theorem b3 (prof : Profile) : Blk prof p3 0 15 o3 :=
  .cons (p3_0 _) (OpI.st (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p3_4 _) (OpI.add (.i 1) (.inr rfl)) (by decide) <|
  .cons (p3_8 _) (OpI.cmp (.i 256) (.inr rfl)) (by decide) <|
  .nil 15

def j1 : List Byte := [0x75, 0xc8]
theorem j1_0 : ∀ feat, Dec feat j1 0 (FV7z.mk (.jcc 5) 64 [.rel 18446744073709551560] 2) := by dec_rfl

/-- The stretch at `88`. -/
def p4 : List Byte := [
  0x48, 0x8d, 0x15, 0xf1, 0x28, 0x35, 0x00, 0x48, 0x8d, 0xb2, 0x00, 0x58, 0x00, 0x00, 0x66, 0x2e,
  0x0f, 0x1f, 0x84, 0x00, 0x00, 0x00, 0x00, 0x00]

theorem p4_0 : ∀ feat, Dec feat p4 0 (FV7z.mk .lea 64 [gr 64 2, .mem (mrip 3483889 0)] 7) := by dec_rfl
theorem p4_7 : ∀ feat, Dec feat p4 7 (FV7z.mk .lea 64 [gr 64 6, .mem (mg (some 2) none 1 22528 0)] 7) := by dec_rfl
theorem p4_14 : ∀ feat, Dec feat p4 14 (FV7z.mk .nop 16 [.mem (mg (some 0) (some 0) 1 0 16)] 10) := by dec_rfl

/-- What the stretch does. -/
def o4 : List Op := [
  Op.mov 64 2 (.i 7956416),
  Op.lea 64 6 (some 2) none 1 22528,
  Op.nop]

theorem b4 (prof : Profile) : BlkA prof p4 (0x443ec8 : Addr) 0 24 o4 :=
  .cons (p4_0 _) (OpIA.lea_rip (by decide)) (by decide) <|
  .cons (p4_7 _) ((OpI.lea (.inr rfl)).at _) (by decide) <|
  .cons (p4_14 _) ((OpI.nop).at _) (by decide) <|
  .nil 24

/-- The stretch at `112`. -/
def p5 : List Byte := [
  0x48, 0x8b, 0x02, 0x48, 0x83, 0xc2, 0x08, 0x0f, 0xb6, 0xc8, 0x48, 0xc1, 0xe8, 0x08, 0x49, 0x33,
  0x04, 0xc8, 0x48, 0x89, 0x82, 0xf8, 0x07, 0x00, 0x00, 0x48, 0x39, 0xd6]

theorem p5_0 : ∀ feat, Dec feat p5 0 (FV7z.mk .mov 64 [gr 64 0, .mem (mg (some 2) none 1 0 64)] 3) := by dec_rfl
theorem p5_3 : ∀ feat, Dec feat p5 3 (FV7z.mk .add 64 [gr 64 2, Src.opd 64 (.i 8)] 4) := by dec_rfl
theorem p5_7 : ∀ feat, Dec feat p5 7 (FV7z.mk .movzx 32 [gr 32 1, gr 8 0] 3) := by dec_rfl
theorem p5_10 : ∀ feat, Dec feat p5 10 (FV7z.mk .shr 64 [gr 64 0, Src.opd 8 (.i 8)] 4) := by dec_rfl
theorem p5_14 : ∀ feat, Dec feat p5 14 (FV7z.mk .xor 64 [gr 64 0, .mem (mg (some 8) (some 1) 8 0 64)] 4) := by dec_rfl
theorem p5_18 : ∀ feat, Dec feat p5 18 (FV7z.mk .mov 64 [.mem (mg (some 2) none 1 2040 64), gr 64 0] 7) := by dec_rfl
theorem p5_25 : ∀ feat, Dec feat p5 25 (FV7z.mk .cmp 64 [gr 64 6, Src.opd 64 (.r 2)] 3) := by dec_rfl

/-- What the stretch does. -/
def o5 : List Op := [
  Op.ld 64 0 (some 2) none 1 0,
  Op.add 64 2 (.i 8),
  Op.zxr 1 0,
  Op.shr64 0 (.i 8),
  Op.xorm 64 0 (some 8) (some 1) 8 0,
  Op.st 64 (some 2) none 1 2040 0,
  Op.cmp 64 6 (.r 2)]

theorem b5 (prof : Profile) : Blk prof p5 0 28 o5 :=
  .cons (p5_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p5_3 _) (OpI.add (.i 8) (.inr rfl)) (by decide) <|
  .cons (p5_7 _) (OpI.zxr) (by decide) <|
  .cons (p5_10 _) (OpI.shr64 (.i 8)) (by decide) <|
  .cons (p5_14 _) (OpI.xorm (.inr rfl)) (by decide) <|
  .cons (p5_18 _) (OpI.st (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p5_25 _) (OpI.cmp (.r 2) (.inr rfl)) (by decide) <|
  .nil 28

def j2 : List Byte := [0x75, 0xe2]
theorem j2_0 : ∀ feat, Dec feat j2 0 (FV7z.mk (.jcc 5) 64 [.rel 18446744073709551586] 2) := by dec_rfl

end FV7z.C15
