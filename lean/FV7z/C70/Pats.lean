import FV7z.Lemmas.Sp
import FV7z.Lemmas.BlkOps18
import FV7z.Lemmas.BlkOps14
import FV7z.Lemmas.BlkOps2
/-!
# The stretches of straight-line code of `csuTg 70` (PLAN.md G3, constructors)

Each distinct stretch between labels and jumps (`p*`, 4 of them) and each distinct jump (`j*`, 2) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.C70
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The stretch at `1440`. -/
def p0 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0x48, 0x8d, 0x35, 0x55, 0x0a, 0x38, 0x00, 0x31, 0xff, 0x4c, 0x8d, 0x86,
  0x00, 0x02, 0x00, 0x00, 0x0f, 0x1f, 0x40, 0x00]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem p0_4 : ∀ feat, Dec feat p0 4 (FV7z.mk .lea 64 [gr 64 6, .mem (mrip 3672661 0)] 7) := by dec_rfl
theorem p0_11 : ∀ feat, Dec feat p0 11 (FV7z.mk .xor 32 [gr 32 7, Src.opd 32 (.r 7)] 2) := by dec_rfl
theorem p0_13 : ∀ feat, Dec feat p0 13 (FV7z.mk .lea 64 [gr 64 8, .mem (mg (some 6) none 1 512 0)] 7) := by dec_rfl
theorem p0_20 : ∀ feat, Dec feat p0 20 (FV7z.mk .nop 32 [.mem (mg (some 0) none 1 0 32)] 4) := by dec_rfl

/-- What the stretch does. -/
def o0 : List Op := [
  Op.nop,
  Op.mov 64 6 (.i 7983424),
  Op.xor 32 7 (.r 7),
  Op.lea 64 8 (some 6) none 1 512,
  Op.nop]

theorem b0 (prof : Profile) : BlkA prof p0 (0x41c6e0 : Addr) 0 24 o0 :=
  .cons (p0_0 _) ((OpI.endbr).at _) (by decide) <|
  .cons (p0_4 _) (OpIA.lea_rip (by decide)) (by decide) <|
  .cons (p0_11 _) ((OpI.xor (.r 7) (.inl rfl)).at _) (by decide) <|
  .cons (p0_13 _) ((OpI.lea (.inr rfl)).at _) (by decide) <|
  .cons (p0_20 _) ((OpI.nop).at _) (by decide) <|
  .nil 24

/-- The stretch at `1464`. -/
def p1 : List Byte := [
  0x89, 0xfa, 0xb9, 0x08, 0x00, 0x00, 0x00, 0x90]

theorem p1_0 : ∀ feat, Dec feat p1 0 (FV7z.mk .mov 32 [gr 32 2, Src.opd 32 (.r 7)] 2) := by dec_rfl
theorem p1_2 : ∀ feat, Dec feat p1 2 (FV7z.mk .mov 32 [gr 32 1, Src.opd 32 (.i 8)] 5) := by dec_rfl
theorem p1_7 : ∀ feat, Dec feat p1 7 (FV7z.mk .nop 32 [] 1) := by dec_rfl

/-- What the stretch does. -/
def o1 : List Op := [
  Op.mov 32 2 (.r 7),
  Op.mov 32 1 (.i 8),
  Op.nop]

theorem b1 (prof : Profile) : Blk prof p1 0 8 o1 :=
  .cons (p1_0 _) (OpI.mov (.r 7) (.inl rfl)) (by decide) <|
  .cons (p1_2 _) (OpI.mov (.i 8) (.inl rfl)) (by decide) <|
  .cons (p1_7 _) (OpI.nop) (by decide) <|
  .nil 8

/-- The stretch at `1472`. -/
def p2 : List Byte := [
  0x89, 0xd0, 0x01, 0xd2, 0xc1, 0xe8, 0x0f, 0xf7, 0xd8, 0x25, 0x21, 0x10, 0x00, 0x00, 0x31, 0xd0,
  0x0f, 0xb7, 0xd0, 0x83, 0xe9, 0x01]

theorem p2_0 : ∀ feat, Dec feat p2 0 (FV7z.mk .mov 32 [gr 32 0, Src.opd 32 (.r 2)] 2) := by dec_rfl
theorem p2_2 : ∀ feat, Dec feat p2 2 (FV7z.mk .add 32 [gr 32 2, Src.opd 32 (.r 2)] 2) := by dec_rfl
theorem p2_4 : ∀ feat, Dec feat p2 4 (FV7z.mk .shr 32 [gr 32 0, Src.opd 8 (.i 15)] 3) := by dec_rfl
theorem p2_7 : ∀ feat, Dec feat p2 7 (FV7z.mk .neg 32 [gr 32 0] 2) := by dec_rfl
theorem p2_9 : ∀ feat, Dec feat p2 9 (FV7z.mk .and 32 [gr 32 0, Src.opd 32 (.i 4129)] 5) := by dec_rfl
theorem p2_14 : ∀ feat, Dec feat p2 14 (FV7z.mk .xor 32 [gr 32 0, Src.opd 32 (.r 2)] 2) := by dec_rfl
theorem p2_16 : ∀ feat, Dec feat p2 16 (FV7z.mk .movzx 32 [gr 32 2, gr 16 0] 3) := by dec_rfl
theorem p2_19 : ∀ feat, Dec feat p2 19 (FV7z.mk .sub 32 [gr 32 1, Src.opd 32 (.i 1)] 3) := by dec_rfl

/-- What the stretch does. -/
def o2 : List Op := [
  Op.mov 32 0 (.r 2),
  Op.add 32 2 (.r 2),
  Op.shr 0 (.i 15),
  Op.neg 32 0,
  Op.and 32 0 (.i 4129),
  Op.xor 32 0 (.r 2),
  Op.zxr16 2 0,
  Op.sub 32 1 (.i 1)]

theorem b2 (prof : Profile) : Blk prof p2 0 22 o2 :=
  .cons (p2_0 _) (OpI.mov (.r 2) (.inl rfl)) (by decide) <|
  .cons (p2_2 _) (OpI.add (.r 2) (.inl rfl)) (by decide) <|
  .cons (p2_4 _) (OpI.shr (.i 15)) (by decide) <|
  .cons (p2_7 _) (OpI.neg (.inl rfl)) (by decide) <|
  .cons (p2_9 _) (OpI.and (.i 4129) (.inl rfl)) (by decide) <|
  .cons (p2_14 _) (OpI.xor (.r 2) (.inl rfl)) (by decide) <|
  .cons (p2_16 _) (OpI.zxr16) (by decide) <|
  .cons (p2_19 _) (OpI.sub (.i 1) (.inl rfl)) (by decide) <|
  .nil 22

def j0 : List Byte := [0x75, 0xe8]
theorem j0_0 : ∀ feat, Dec feat j0 0 (FV7z.mk (.jcc 5) 64 [.rel 18446744073709551592] 2) := by dec_rfl

/-- The stretch at `1496`. -/
def p3 : List Byte := [
  0x66, 0x89, 0x06, 0x48, 0x83, 0xc6, 0x02, 0x81, 0xc7, 0x00, 0x01, 0x00, 0x00, 0x49, 0x39, 0xf0]

theorem p3_0 : ∀ feat, Dec feat p3 0 (FV7z.mk .mov 16 [.mem (mg (some 6) none 1 0 16), gr 16 0] 3) := by dec_rfl
theorem p3_3 : ∀ feat, Dec feat p3 3 (FV7z.mk .add 64 [gr 64 6, Src.opd 64 (.i 2)] 4) := by dec_rfl
theorem p3_7 : ∀ feat, Dec feat p3 7 (FV7z.mk .add 32 [gr 32 7, Src.opd 32 (.i 256)] 6) := by dec_rfl
theorem p3_13 : ∀ feat, Dec feat p3 13 (FV7z.mk .cmp 64 [gr 64 8, Src.opd 64 (.r 6)] 3) := by dec_rfl

/-- What the stretch does. -/
def o3 : List Op := [
  Op.st 16 (some 6) none 1 0 0,
  Op.add 64 6 (.i 2),
  Op.add 32 7 (.i 256),
  Op.cmp 64 8 (.r 6)]

theorem b3 (prof : Profile) : Blk prof p3 0 16 o3 :=
  .cons (p3_0 _) (OpI.st (.inr (.inl rfl))) (by decide) <|
  .cons (p3_3 _) (OpI.add (.i 2) (.inr rfl)) (by decide) <|
  .cons (p3_7 _) (OpI.add (.i 256) (.inl rfl)) (by decide) <|
  .cons (p3_13 _) (OpI.cmp (.r 6) (.inr rfl)) (by decide) <|
  .nil 16

def j1 : List Byte := [0x75, 0xce]
theorem j1_0 : ∀ feat, Dec feat j1 0 (FV7z.mk (.jcc 5) 64 [.rel 18446744073709551566] 2) := by dec_rfl

end FV7z.C70
