import FV7z.Lemmas.SpFs
import FV7z.Lemmas.BlkOps2
/-!
# The stretches of straight-line code of `tcache_init` (PLAN.md G3, `malloc`)

Each distinct stretch between labels and jumps (`p*`, 9 of them) and each distinct jump (`j*`, 5) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.Tci
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The stretch at `0`. -/
def p0 : List Byte := [
  0x48, 0xc7, 0xc0, 0xe8, 0xff, 0xff, 0xff, 0x55, 0x64, 0x48, 0x8b, 0x28, 0x48, 0x85, 0xed]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .mov 64 [gr 64 0, Src.opd 64 (.i 18446744073709551592)] 7) := by dec_rfl
theorem p0_7 : ∀ feat, Dec feat p0 7 (FV7z.mk .push 64 [gr 64 5] 1) := by dec_rfl
theorem p0_8 : ∀ feat, Dec feat p0 8 (FV7z.mk .mov 64 [gr 64 5, .mem (mf (some 0) none 1 0 64)] 4) := by dec_rfl
theorem p0_12 : ∀ feat, Dec feat p0 12 (FV7z.mk .test 64 [gr 64 5, Src.opd 64 (.r 5)] 3) := by dec_rfl

/-- What the stretch does. -/
def o0 (fb : Addr) : List Op := [
  Op.mov 64 0 (.i 18446744073709551592),
  Op.push 5,
  Op.ldf fb 64 5 (some 0) none 1 0,
  Op.test 64 5 (.r 5)]

theorem b0 (prof : Profile) (fb : Addr) : BlkF prof p0 (0x631a60 : Addr) fb 0 15 (o0 fb) :=
  .cons (p0_0 _) (((OpI.mov (.i 18446744073709551592) (.inr rfl)).at _).fs _) (by decide) <|
  .cons (p0_7 _) (((OpI.push).at _).fs _) (by decide) <|
  .cons (p0_8 _) (OpIF.ldf (.inr rfl)) (by decide) <|
  .cons (p0_12 _) (((OpI.test (.r 5) (.inr rfl)).at _).fs _) (by decide) <|
  .nil 15

def j0 : List Byte := [0x0f, 0x84, 0x8b, 0x00, 0x00, 0x00]
theorem j0_0 : ∀ feat, Dec feat j0 0 (FV7z.mk (.jcc 4) 64 [.rel 139] 6) := by dec_rfl

/-- The stretch at `21`. -/
def p1 : List Byte := [
  0x64, 0x8b, 0x04, 0x25, 0x18, 0x00, 0x00, 0x00, 0x85, 0xc0]

theorem p1_0 : ∀ feat, Dec feat p1 0 (FV7z.mk .mov 32 [gr 32 0, .mem (mf none none 1 24 32)] 8) := by dec_rfl
theorem p1_8 : ∀ feat, Dec feat p1 8 (FV7z.mk .test 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl

/-- What the stretch does. -/
def o1 (fb : Addr) : List Op := [
  Op.ldf fb 32 0 none none 1 24,
  Op.test 32 0 (.r 0)]

theorem b1 (prof : Profile) (fb : Addr) : BlkF prof p1 (0x631a75 : Addr) fb 0 10 (o1 fb) :=
  .cons (p1_0 _) (OpIF.ldf (.inl rfl)) (by decide) <|
  .cons (p1_8 _) (((OpI.test (.r 0) (.inl rfl)).at _).fs _) (by decide) <|
  .nil 10

def j1 : List Byte := [0x0f, 0x85, 0xeb, 0x00, 0x00, 0x00]
theorem j1_0 : ∀ feat, Dec feat j1 0 (FV7z.mk (.jcc 5) 64 [.rel 235] 6) := by dec_rfl

/-- The stretch at `37`. -/
def p2 : List Byte := [
  0xba, 0x01, 0x00, 0x00, 0x00]

theorem p2_0 : ∀ feat, Dec feat p2 0 (FV7z.mk .mov 32 [gr 32 2, Src.opd 32 (.i 1)] 5) := by dec_rfl

/-- What the stretch does. -/
def o2 : List Op := [
  Op.mov 32 2 (.i 1)]

theorem b2 (prof : Profile) : Blk prof p2 0 5 o2 :=
  .cons (p2_0 _) (OpI.mov (.i 1) (.inl rfl)) (by decide) <|
  .nil 5

/-- The stretch at `46`. -/
def p3 : List Byte := [
  0xbe, 0x80, 0x02, 0x00, 0x00, 0x48, 0x89, 0xef]

theorem p3_0 : ∀ feat, Dec feat p3 0 (FV7z.mk .mov 32 [gr 32 6, Src.opd 32 (.i 640)] 5) := by dec_rfl
theorem p3_5 : ∀ feat, Dec feat p3 5 (FV7z.mk .mov 64 [gr 64 7, Src.opd 64 (.r 5)] 3) := by dec_rfl

/-- What the stretch does. -/
def o3 : List Op := [
  Op.mov 32 6 (.i 640),
  Op.mov 64 7 (.r 5)]

theorem b3 (prof : Profile) : Blk prof p3 0 8 o3 :=
  .cons (p3_0 _) (OpI.mov (.i 640) (.inl rfl)) (by decide) <|
  .cons (p3_5 _) (OpI.mov (.r 5) (.inr rfl)) (by decide) <|
  .nil 8

/-- The stretch at `59`. -/
def p4 : List Byte := [
  0x49, 0x89, 0xc0, 0x48, 0x85, 0xc0]

theorem p4_0 : ∀ feat, Dec feat p4 0 (FV7z.mk .mov 64 [gr 64 8, Src.opd 64 (.r 0)] 3) := by dec_rfl
theorem p4_3 : ∀ feat, Dec feat p4 3 (FV7z.mk .test 64 [gr 64 0, Src.opd 64 (.r 0)] 3) := by dec_rfl

/-- What the stretch does. -/
def o4 : List Op := [
  Op.mov 64 8 (.r 0),
  Op.test 64 0 (.r 0)]

theorem b4 (prof : Profile) : Blk prof p4 0 6 o4 :=
  .cons (p4_0 _) (OpI.mov (.r 0) (.inr rfl)) (by decide) <|
  .cons (p4_3 _) (OpI.test (.r 0) (.inr rfl)) (by decide) <|
  .nil 6

def j2 : List Byte := [0x0f, 0x84, 0x99, 0x00, 0x00, 0x00]
theorem j2_0 : ∀ feat, Dec feat j2 0 (FV7z.mk (.jcc 4) 64 [.rel 153] 6) := by dec_rfl

/-- The stretch at `71`. -/
def p5 : List Byte := [
  0x64, 0x8b, 0x04, 0x25, 0x18, 0x00, 0x00, 0x00, 0x85, 0xc0]

theorem p5_0 : ∀ feat, Dec feat p5 0 (FV7z.mk .mov 32 [gr 32 0, .mem (mf none none 1 24 32)] 8) := by dec_rfl
theorem p5_8 : ∀ feat, Dec feat p5 8 (FV7z.mk .test 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl

/-- What the stretch does. -/
def o5 (fb : Addr) : List Op := [
  Op.ldf fb 32 0 none none 1 24,
  Op.test 32 0 (.r 0)]

theorem b5 (prof : Profile) (fb : Addr) : BlkF prof p5 (0x631aa7 : Addr) fb 0 10 (o5 fb) :=
  .cons (p5_0 _) (OpIF.ldf (.inl rfl)) (by decide) <|
  .cons (p5_8 _) (((OpI.test (.r 0) (.inl rfl)).at _).fs _) (by decide) <|
  .nil 10

def j3 : List Byte := [0x0f, 0x85, 0xd9, 0x00, 0x00, 0x00]
theorem j3_0 : ∀ feat, Dec feat j3 0 (FV7z.mk (.jcc 5) 64 [.rel 217] 6) := by dec_rfl

/-- The stretch at `91`. -/
def p6 : List Byte := [
  0x4d, 0x85, 0xc0]

theorem p6_0 : ∀ feat, Dec feat p6 0 (FV7z.mk .test 64 [gr 64 8, Src.opd 64 (.r 8)] 3) := by dec_rfl

/-- What the stretch does. -/
def o6 : List Op := [
  Op.test 64 8 (.r 8)]

theorem b6 (prof : Profile) : Blk prof p6 0 3 o6 :=
  .cons (p6_0 _) (OpI.test (.r 8) (.inr rfl)) (by decide) <|
  .nil 3

def j4 : List Byte := [0x74, 0x35]
theorem j4_0 : ∀ feat, Dec feat j4 0 (FV7z.mk (.jcc 4) 64 [.rel 53] 2) := by dec_rfl

/-- The stretch at `96`. -/
def p7 : List Byte := [
  0x64, 0x4c, 0x89, 0x04, 0x25, 0xd8, 0xff, 0xff, 0xff, 0x49, 0x8d, 0x78, 0x08, 0x31, 0xc0, 0x48,
  0x83, 0xe7, 0xf8, 0x49, 0xc7, 0x00, 0x00, 0x00, 0x00, 0x00, 0x49, 0xc7, 0x80, 0x78, 0x02, 0x00,
  0x00, 0x00, 0x00, 0x00, 0x00, 0x49, 0x29, 0xf8, 0x41, 0x8d, 0x88, 0x80, 0x02, 0x00, 0x00, 0xc1,
  0xe9, 0x03]

theorem p7_0 : ∀ feat, Dec feat p7 0 (FV7z.mk .mov 64 [.mem (mf none none 1 18446744073709551576 64), gr 64 8] 9) := by dec_rfl
theorem p7_9 : ∀ feat, Dec feat p7 9 (FV7z.mk .lea 64 [gr 64 7, .mem (mg (some 8) none 1 8 0)] 4) := by dec_rfl
theorem p7_13 : ∀ feat, Dec feat p7 13 (FV7z.mk .xor 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl
theorem p7_15 : ∀ feat, Dec feat p7 15 (FV7z.mk .and 64 [gr 64 7, Src.opd 64 (.i 18446744073709551608)] 4) := by dec_rfl
theorem p7_19 : ∀ feat, Dec feat p7 19 (FV7z.mk .mov 64 [.mem (mg (some 8) none 1 0 64), .imm 64 0] 7) := by dec_rfl
theorem p7_26 : ∀ feat, Dec feat p7 26 (FV7z.mk .mov 64 [.mem (mg (some 8) none 1 632 64), .imm 64 0] 11) := by dec_rfl
theorem p7_37 : ∀ feat, Dec feat p7 37 (FV7z.mk .sub 64 [gr 64 8, Src.opd 64 (.r 7)] 3) := by dec_rfl
theorem p7_40 : ∀ feat, Dec feat p7 40 (FV7z.mk .lea 32 [gr 32 1, .mem (mg (some 8) none 1 640 0)] 7) := by dec_rfl
theorem p7_47 : ∀ feat, Dec feat p7 47 (FV7z.mk .shr 32 [gr 32 1, Src.opd 8 (.i 3)] 3) := by dec_rfl

/-- What the stretch does. -/
def o7 (fb : Addr) : List Op := [
  Op.stf fb 64 none none 1 18446744073709551576 8,
  Op.lea 64 7 (some 8) none 1 8,
  Op.xor 32 0 (.r 0),
  Op.and 64 7 (.i 18446744073709551608),
  Op.sti 64 (some 8) none 1 0 0,
  Op.sti 64 (some 8) none 1 632 0,
  Op.sub 64 8 (.r 7),
  Op.lea 32 1 (some 8) none 1 640,
  Op.shr 1 (.i 3)]

theorem b7 (prof : Profile) (fb : Addr) : BlkF prof p7 (0x631ac0 : Addr) fb 0 50 (o7 fb) :=
  .cons (p7_0 _) (OpIF.stf (.inr rfl)) (by decide) <|
  .cons (p7_9 _) (((OpI.lea (.inr rfl)).at _).fs _) (by decide) <|
  .cons (p7_13 _) (((OpI.xor (.r 0) (.inl rfl)).at _).fs _) (by decide) <|
  .cons (p7_15 _) (((OpI.and (.i 18446744073709551608) (.inr rfl)).at _).fs _) (by decide) <|
  .cons (p7_19 _) (((OpI.sti (.inr (.inr (.inr rfl)))).at _).fs _) (by decide) <|
  .cons (p7_26 _) (((OpI.sti (.inr (.inr (.inr rfl)))).at _).fs _) (by decide) <|
  .cons (p7_37 _) (((OpI.sub (.r 7) (.inr rfl)).at _).fs _) (by decide) <|
  .cons (p7_40 _) (((OpI.lea (.inl rfl)).at _).fs _) (by decide) <|
  .cons (p7_47 _) (((OpI.shr (.i 3)).at _).fs _) (by decide) <|
  .nil 50

/-- The stretch at `149`. -/
def p8 : List Byte := [
  0x5d]

theorem p8_0 : ∀ feat, Dec feat p8 0 (FV7z.mk .pop 64 [gr 64 5] 1) := by dec_rfl

/-- What the stretch does. -/
def o8 : List Op := [
  Op.pop 5]

theorem b8 (prof : Profile) : Blk prof p8 0 1 o8 :=
  .cons (p8_0 _) (OpI.pop) (by decide) <|
  .nil 1

end FV7z.Tci
