import FV7z.Lemmas.SpFs
import FV7z.Lemmas.BlkOps11
import FV7z.Lemmas.BlkOps6
import FV7z.Lemmas.BlkOps2
/-!
# The stretches of straight-line code of `__cxa_atexit` (PLAN.md G3, startup)

Each distinct stretch between labels and jumps (`p*`, 9 of them) and each distinct jump (`j*`, 4) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.Cxa
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The stretch at `0`. -/
def p0 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0x53, 0x48, 0x83, 0xec, 0x10, 0x48, 0x89, 0x34, 0x24, 0x48, 0x89, 0x54,
  0x24, 0x08, 0x48, 0x85, 0xff]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem p0_4 : ∀ feat, Dec feat p0 4 (FV7z.mk .push 64 [gr 64 3] 1) := by dec_rfl
theorem p0_5 : ∀ feat, Dec feat p0 5 (FV7z.mk .sub 64 [gr 64 4, Src.opd 64 (.i 16)] 4) := by dec_rfl
theorem p0_9 : ∀ feat, Dec feat p0 9 (FV7z.mk .mov 64 [.mem (mg (some 4) none 1 0 64), gr 64 6] 4) := by dec_rfl
theorem p0_13 : ∀ feat, Dec feat p0 13 (FV7z.mk .mov 64 [.mem (mg (some 4) none 1 8 64), gr 64 2] 5) := by dec_rfl
theorem p0_18 : ∀ feat, Dec feat p0 18 (FV7z.mk .test 64 [gr 64 7, Src.opd 64 (.r 7)] 3) := by dec_rfl

/-- What the stretch does. -/
def o0 : List Op := [
  Op.nop,
  Op.push 3,
  Op.sub 64 4 (.i 16),
  Op.st 64 (some 4) none 1 0 6,
  Op.st 64 (some 4) none 1 8 2,
  Op.test 64 7 (.r 7)]

theorem b0 (prof : Profile) : Blk prof p0 0 21 o0 :=
  .cons (p0_0 _) (OpI.endbr) (by decide) <|
  .cons (p0_4 _) (OpI.push) (by decide) <|
  .cons (p0_5 _) (OpI.sub (.i 16) (.inr rfl)) (by decide) <|
  .cons (p0_9 _) (OpI.st (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p0_13 _) (OpI.st (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p0_18 _) (OpI.test (.r 7) (.inr rfl)) (by decide) <|
  .nil 21

def j0 : List Byte := [0x0f, 0x84, 0xed, 0x00, 0x00, 0x00]
theorem j0_0 : ∀ feat, Dec feat j0 0 (FV7z.mk (.jcc 4) 64 [.rel 237] 6) := by dec_rfl

/-- The stretch at `27`. -/
def p1 : List Byte := [
  0x48, 0x89, 0xfb, 0x64, 0x8b, 0x04, 0x25, 0x18, 0x00, 0x00, 0x00, 0x85, 0xc0]

theorem p1_0 : ∀ feat, Dec feat p1 0 (FV7z.mk .mov 64 [gr 64 3, Src.opd 64 (.r 7)] 3) := by dec_rfl
theorem p1_3 : ∀ feat, Dec feat p1 3 (FV7z.mk .mov 32 [gr 32 0, .mem (mf none none 1 24 32)] 8) := by dec_rfl
theorem p1_11 : ∀ feat, Dec feat p1 11 (FV7z.mk .test 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl

/-- What the stretch does. -/
def o1 (fb : Addr) : List Op := [
  Op.mov 64 3 (.r 7),
  Op.ldf fb 32 0 none none 1 24,
  Op.test 32 0 (.r 0)]

theorem b1 (prof : Profile) (fb : Addr) : BlkF prof p1 (0x6236ab : Addr) fb 0 13 (o1 fb) :=
  .cons (p1_0 _) (((OpI.mov (.r 7) (.inr rfl)).at _).fs _) (by decide) <|
  .cons (p1_3 _) (OpIF.ldf (.inl rfl)) (by decide) <|
  .cons (p1_11 _) (((OpI.test (.r 0) (.inl rfl)).at _).fs _) (by decide) <|
  .nil 13

def j1 : List Byte := [0x75, 0x6e]
theorem j1_0 : ∀ feat, Dec feat j1 0 (FV7z.mk (.jcc 5) 64 [.rel 110] 2) := by dec_rfl

/-- The stretch at `42`. -/
def p2 : List Byte := [
  0xba, 0x01, 0x00, 0x00, 0x00]

theorem p2_0 : ∀ feat, Dec feat p2 0 (FV7z.mk .mov 32 [gr 32 2, Src.opd 32 (.i 1)] 5) := by dec_rfl

/-- What the stretch does. -/
def o2 : List Op := [
  Op.mov 32 2 (.i 1)]

theorem b2 (prof : Profile) : Blk prof p2 0 5 o2 :=
  .cons (p2_0 _) (OpI.mov (.i 1) (.inl rfl)) (by decide) <|
  .nil 5

/-- The stretch at `54`. -/
def p3 : List Byte := [
  0x48, 0x8d, 0x3d, 0xe3, 0xec, 0x16, 0x00]

theorem p3_0 : ∀ feat, Dec feat p3 0 (FV7z.mk .lea 64 [gr 64 7, .mem (mrip 1502435 0)] 7) := by dec_rfl

/-- What the stretch does. -/
def o3 : List Op := [
  Op.mov 64 7 (.i 7938992)]

theorem b3 (prof : Profile) : BlkA prof p3 (0x6236c6 : Addr) 0 7 o3 :=
  .cons (p3_0 _) (OpIA.lea_rip (by decide)) (by decide) <|
  .nil 7

/-- The stretch at `66`. -/
def p4 : List Byte := [
  0x48, 0x85, 0xc0]

theorem p4_0 : ∀ feat, Dec feat p4 0 (FV7z.mk .test 64 [gr 64 0, Src.opd 64 (.r 0)] 3) := by dec_rfl

/-- What the stretch does. -/
def o4 : List Op := [
  Op.test 64 0 (.r 0)]

theorem b4 (prof : Profile) : Blk prof p4 0 3 o4 :=
  .cons (p4_0 _) (OpI.test (.r 0) (.inr rfl)) (by decide) <|
  .nil 3

def j2 : List Byte := [0x0f, 0x84, 0xa2, 0x00, 0x00, 0x00]
theorem j2_0 : ∀ feat, Dec feat j2 0 (FV7z.mk (.jcc 4) 64 [.rel 162] 6) := by dec_rfl

/-- The stretch at `80`. -/
def p5 : List Byte := [
  0x48, 0x89, 0xdf, 0x48, 0xc7, 0x00, 0x04, 0x00, 0x00, 0x00, 0x64, 0x48, 0x33, 0x3c, 0x25, 0x30,
  0x00, 0x00, 0x00, 0x48, 0xc1, 0xc7, 0x11]

theorem p5_0 : ∀ feat, Dec feat p5 0 (FV7z.mk .mov 64 [gr 64 7, Src.opd 64 (.r 3)] 3) := by dec_rfl
theorem p5_3 : ∀ feat, Dec feat p5 3 (FV7z.mk .mov 64 [.mem (mg (some 0) none 1 0 64), .imm 64 4] 7) := by dec_rfl
theorem p5_10 : ∀ feat, Dec feat p5 10 (FV7z.mk .xor 64 [gr 64 7, .mem (mf none none 1 48 64)] 9) := by dec_rfl
theorem p5_19 : ∀ feat, Dec feat p5 19 (FV7z.mk .rol 64 [gr 64 7, Src.opd 8 (.i 17)] 4) := by dec_rfl

/-- What the stretch does. -/
def o5 (fb : Addr) : List Op := [
  Op.mov 64 7 (.r 3),
  Op.sti 64 (some 0) none 1 0 4,
  Op.xormf fb 64 7 none none 1 48,
  Op.rol64 7 (.i 17)]

theorem b5 (prof : Profile) (fb : Addr) : BlkF prof p5 (0x6236e0 : Addr) fb 0 23 (o5 fb) :=
  .cons (p5_0 _) (((OpI.mov (.r 3) (.inr rfl)).at _).fs _) (by decide) <|
  .cons (p5_3 _) (((OpI.sti (.inr (.inr (.inr rfl)))).at _).fs _) (by decide) <|
  .cons (p5_10 _) (OpIF.xormf (.inr rfl)) (by decide) <|
  .cons (p5_19 _) (((OpI.rol64 (.i 17)).at _).fs _) (by decide) <|
  .nil 23

/-- The stretch at `108`. -/
def p6 : List Byte := [
  0x48, 0x89, 0x78, 0x08]

theorem p6_0 : ∀ feat, Dec feat p6 0 (FV7z.mk .mov 64 [.mem (mg (some 0) none 1 8 64), gr 64 7] 4) := by dec_rfl

/-- What the stretch does. -/
def o6 : List Op := [
  Op.st 64 (some 0) none 1 8 7]

theorem b6 (prof : Profile) : Blk prof p6 0 4 o6 :=
  .cons (p6_0 _) (OpI.st (.inr (.inr (.inr rfl)))) (by decide) <|
  .nil 4

/-- The stretch at `116`. -/
def p7 : List Byte := [
  0x64, 0x44, 0x8b, 0x04, 0x25, 0x18, 0x00, 0x00, 0x00, 0x45, 0x85, 0xc0]

theorem p7_0 : ∀ feat, Dec feat p7 0 (FV7z.mk .mov 32 [gr 32 8, .mem (mf none none 1 24 32)] 9) := by dec_rfl
theorem p7_9 : ∀ feat, Dec feat p7 9 (FV7z.mk .test 32 [gr 32 8, Src.opd 32 (.r 8)] 3) := by dec_rfl

/-- What the stretch does. -/
def o7 (fb : Addr) : List Op := [
  Op.ldf fb 32 8 none none 1 24,
  Op.test 32 8 (.r 8)]

theorem b7 (prof : Profile) (fb : Addr) : BlkF prof p7 (0x623704 : Addr) fb 0 12 (o7 fb) :=
  .cons (p7_0 _) (OpIF.ldf (.inl rfl)) (by decide) <|
  .cons (p7_9 _) (((OpI.test (.r 8) (.inl rfl)).at _).fs _) (by decide) <|
  .nil 12

def j3 : List Byte := [0x75, 0x3e]
theorem j3_0 : ∀ feat, Dec feat j3 0 (FV7z.mk (.jcc 5) 64 [.rel 62] 2) := by dec_rfl

/-- The stretch at `137`. -/
def p8 : List Byte := [
  0x48, 0x83, 0xc4, 0x10, 0x44, 0x89, 0xc0, 0x5b]

theorem p8_0 : ∀ feat, Dec feat p8 0 (FV7z.mk .add 64 [gr 64 4, Src.opd 64 (.i 16)] 4) := by dec_rfl
theorem p8_4 : ∀ feat, Dec feat p8 4 (FV7z.mk .mov 32 [gr 32 0, Src.opd 32 (.r 8)] 3) := by dec_rfl
theorem p8_7 : ∀ feat, Dec feat p8 7 (FV7z.mk .pop 64 [gr 64 3] 1) := by dec_rfl

/-- What the stretch does. -/
def o8 : List Op := [
  Op.add 64 4 (.i 16),
  Op.mov 32 0 (.r 8),
  Op.pop 3]

theorem b8 (prof : Profile) : Blk prof p8 0 8 o8 :=
  .cons (p8_0 _) (OpI.add (.i 16) (.inr rfl)) (by decide) <|
  .cons (p8_4 _) (OpI.mov (.r 8) (.inl rfl)) (by decide) <|
  .cons (p8_7 _) (OpI.pop) (by decide) <|
  .nil 8

end FV7z.Cxa
