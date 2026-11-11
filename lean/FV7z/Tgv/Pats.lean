import FV7z.Lemmas.Sp
import FV7z.Lemmas.BlkOps2
/-!
# The stretches of straight-line code of `__tunable_get_val` (PLAN.md G3, startup)

Each distinct stretch between labels and jumps (`p*`, 7 of them) and each distinct jump (`j*`, 5) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.Tgv
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The stretch at `0`. -/
def p0 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0x89, 0xff, 0x48, 0x8d, 0x0d, 0xb3, 0x22, 0x12, 0x00, 0x48, 0x8d, 0x04,
  0xfd, 0x00, 0x00, 0x00, 0x00, 0x48, 0x29, 0xf8, 0x48, 0x8d, 0x04, 0xc1, 0x44, 0x8b, 0x40, 0x08,
  0x48, 0x8b, 0x40, 0x20, 0x41, 0x83, 0xf8, 0x02]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem p0_4 : ∀ feat, Dec feat p0 4 (FV7z.mk .mov 32 [gr 32 7, Src.opd 32 (.r 7)] 2) := by dec_rfl
theorem p0_6 : ∀ feat, Dec feat p0 6 (FV7z.mk .lea 64 [gr 64 1, .mem (mrip 1188531 0)] 7) := by dec_rfl
theorem p0_13 : ∀ feat, Dec feat p0 13 (FV7z.mk .lea 64 [gr 64 0, .mem (mg none (some 7) 8 0 0)] 8) := by dec_rfl
theorem p0_21 : ∀ feat, Dec feat p0 21 (FV7z.mk .sub 64 [gr 64 0, Src.opd 64 (.r 7)] 3) := by dec_rfl
theorem p0_24 : ∀ feat, Dec feat p0 24 (FV7z.mk .lea 64 [gr 64 0, .mem (mg (some 1) (some 0) 8 0 0)] 4) := by dec_rfl
theorem p0_28 : ∀ feat, Dec feat p0 28 (FV7z.mk .mov 32 [gr 32 8, .mem (mg (some 0) none 1 8 32)] 4) := by dec_rfl
theorem p0_32 : ∀ feat, Dec feat p0 32 (FV7z.mk .mov 64 [gr 64 0, .mem (mg (some 0) none 1 32 64)] 4) := by dec_rfl
theorem p0_36 : ∀ feat, Dec feat p0 36 (FV7z.mk .cmp 32 [gr 32 8, Src.opd 32 (.i 2)] 4) := by dec_rfl

/-- What the stretch does. -/
def o0 : List Op := [
  Op.nop,
  Op.mov 32 7 (.r 7),
  Op.mov 64 1 (.i 7935584),
  Op.lea 64 0 none (some 7) 8 0,
  Op.sub 64 0 (.r 7),
  Op.lea 64 0 (some 1) (some 0) 8 0,
  Op.ld 32 8 (some 0) none 1 8,
  Op.ld 64 0 (some 0) none 1 32,
  Op.cmp 32 8 (.i 2)]

theorem b0 (prof : Profile) : BlkA prof p0 (0x66f3a0 : Addr) 0 40 o0 :=
  .cons (p0_0 _) ((OpI.endbr).at _) (by decide) <|
  .cons (p0_4 _) ((OpI.mov (.r 7) (.inl rfl)).at _) (by decide) <|
  .cons (p0_6 _) (OpIA.lea_rip (by decide)) (by decide) <|
  .cons (p0_13 _) ((OpI.lea (.inr rfl)).at _) (by decide) <|
  .cons (p0_21 _) ((OpI.sub (.r 7) (.inr rfl)).at _) (by decide) <|
  .cons (p0_24 _) ((OpI.lea (.inr rfl)).at _) (by decide) <|
  .cons (p0_28 _) ((OpI.ld (.inl rfl)).at _) (by decide) <|
  .cons (p0_32 _) ((OpI.ld (.inr rfl)).at _) (by decide) <|
  .cons (p0_36 _) ((OpI.cmp (.i 2) (.inl rfl)).at _) (by decide) <|
  .nil 40

def j0 : List Byte := [0x77, 0x3e]
theorem j0_0 : ∀ feat, Dec feat j0 0 (FV7z.mk (.jcc 7) 64 [.rel 62] 2) := by dec_rfl

/-- The stretch at `42`. -/
def p1 : List Byte := [
  0x45, 0x85, 0xc0]

theorem p1_0 : ∀ feat, Dec feat p1 0 (FV7z.mk .test 32 [gr 32 8, Src.opd 32 (.r 8)] 3) := by dec_rfl

/-- What the stretch does. -/
def o1 : List Op := [
  Op.test 32 8 (.r 8)]

theorem b1 (prof : Profile) : Blk prof p1 0 3 o1 :=
  .cons (p1_0 _) (OpI.test (.r 8) (.inl rfl)) (by decide) <|
  .nil 3

def j1 : List Byte := [0x75, 0x39]
theorem j1_0 : ∀ feat, Dec feat j1 0 (FV7z.mk (.jcc 5) 64 [.rel 57] 2) := by dec_rfl

/-- The stretch at `47`. -/
def p2 : List Byte := [
  0x89, 0x06]

theorem p2_0 : ∀ feat, Dec feat p2 0 (FV7z.mk .mov 32 [.mem (mg (some 6) none 1 0 32), gr 32 0] 2) := by dec_rfl

/-- What the stretch does. -/
def o2 : List Op := [
  Op.st 32 (some 6) none 1 0 0]

theorem b2 (prof : Profile) : Blk prof p2 0 2 o2 :=
  .cons (p2_0 _) (OpI.st (.inr (.inr (.inl rfl)))) (by decide) <|
  .nil 2

/-- The stretch at `49`. -/
def p3 : List Byte := [
  0x48, 0x8d, 0x04, 0xfd, 0x00, 0x00, 0x00, 0x00, 0x48, 0x29, 0xf8, 0x80, 0x7c, 0xc1, 0x28, 0x00,
  0x48, 0x8d, 0x34, 0xc5, 0x00, 0x00, 0x00, 0x00]

theorem p3_0 : ∀ feat, Dec feat p3 0 (FV7z.mk .lea 64 [gr 64 0, .mem (mg none (some 7) 8 0 0)] 8) := by dec_rfl
theorem p3_8 : ∀ feat, Dec feat p3 8 (FV7z.mk .sub 64 [gr 64 0, Src.opd 64 (.r 7)] 3) := by dec_rfl
theorem p3_11 : ∀ feat, Dec feat p3 11 (FV7z.mk .cmp 8 [.mem (mg (some 1) (some 0) 8 40 8), .imm 8 0] 5) := by dec_rfl
theorem p3_16 : ∀ feat, Dec feat p3 16 (FV7z.mk .lea 64 [gr 64 6, .mem (mg none (some 0) 8 0 0)] 8) := by dec_rfl

/-- What the stretch does. -/
def o3 : List Op := [
  Op.lea 64 0 none (some 7) 8 0,
  Op.sub 64 0 (.r 7),
  Op.cmpmi 8 (some 1) (some 0) 8 40 0,
  Op.lea 64 6 none (some 0) 8 0]

theorem b3 (prof : Profile) : Blk prof p3 0 24 o3 :=
  .cons (p3_0 _) (OpI.lea (.inr rfl)) (by decide) <|
  .cons (p3_8 _) (OpI.sub (.r 7) (.inr rfl)) (by decide) <|
  .cons (p3_11 _) (OpI.cmpmi (.inl rfl)) (by decide) <|
  .cons (p3_16 _) (OpI.lea (.inr rfl)) (by decide) <|
  .nil 24

def j2 : List Byte := [0x74, 0x15]
theorem j2_0 : ∀ feat, Dec feat j2 0 (FV7z.mk (.jcc 4) 64 [.rel 21] 2) := by dec_rfl

/-- The stretch at `75`. -/
def p4 : List Byte := [
  0x48, 0x85, 0xd2]

theorem p4_0 : ∀ feat, Dec feat p4 0 (FV7z.mk .test 64 [gr 64 2, Src.opd 64 (.r 2)] 3) := by dec_rfl

/-- What the stretch does. -/
def o4 : List Op := [
  Op.test 64 2 (.r 2)]

theorem b4 (prof : Profile) : Blk prof p4 0 3 o4 :=
  .cons (p4_0 _) (OpI.test (.r 2) (.inr rfl)) (by decide) <|
  .nil 3

def j3 : List Byte := [0x74, 0x10]
theorem j3_0 : ∀ feat, Dec feat j3 0 (FV7z.mk (.jcc 4) 64 [.rel 16] 2) := by dec_rfl

/-- The stretch at `80`. -/
def p5 : List Byte := [
  0x48, 0x8d, 0x7c, 0x31, 0x20]

theorem p5_0 : ∀ feat, Dec feat p5 0 (FV7z.mk .lea 64 [gr 64 7, .mem (mg (some 1) (some 6) 1 32 0)] 5) := by dec_rfl

/-- What the stretch does. -/
def o5 : List Op := [
  Op.lea 64 7 (some 1) (some 6) 1 32]

theorem b5 (prof : Profile) : Blk prof p5 0 5 o5 :=
  .cons (p5_0 _) (OpI.lea (.inr rfl)) (by decide) <|
  .nil 5

/-- The stretch at `104`. -/
def p6 : List Byte := [
  0x48, 0x89, 0x06]

theorem p6_0 : ∀ feat, Dec feat p6 0 (FV7z.mk .mov 64 [.mem (mg (some 6) none 1 0 64), gr 64 0] 3) := by dec_rfl

/-- What the stretch does. -/
def o6 : List Op := [
  Op.st 64 (some 6) none 1 0 0]

theorem b6 (prof : Profile) : Blk prof p6 0 3 o6 :=
  .cons (p6_0 _) (OpI.st (.inr (.inr (.inr rfl)))) (by decide) <|
  .nil 3

def j4 : List Byte := [0xeb, 0xc4]
theorem j4_0 : ∀ feat, Dec feat j4 0 (FV7z.mk .jmp 64 [.rel 18446744073709551556] 2) := by dec_rfl

end FV7z.Tgv
