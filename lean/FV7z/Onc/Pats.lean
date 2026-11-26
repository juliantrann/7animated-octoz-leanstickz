import FV7z.Lemmas.SpFs
import FV7z.Lemmas.BlkOps6
import FV7z.Lemmas.BlkOps2
/-!
# The stretches of straight-line code of `__open64_nocancel` (PLAN.md §M, M1)

Each distinct stretch between labels and jumps (`p*`, 7 of them) and each distinct jump (`j*`, 5) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.Onc
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The stretch at `0`. -/
def p0 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0x48, 0x83, 0xec, 0x58, 0x41, 0x89, 0xf2, 0x49, 0x89, 0xf9, 0x41, 0x89,
  0xf0, 0x48, 0x89, 0x54, 0x24, 0x30, 0x64, 0x48, 0x8b, 0x04, 0x25, 0x28, 0x00, 0x00, 0x00, 0x48,
  0x89, 0x44, 0x24, 0x18, 0x31, 0xc0, 0x41, 0x83, 0xe2, 0x40]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem p0_4 : ∀ feat, Dec feat p0 4 (FV7z.mk .sub 64 [gr 64 4, Src.opd 64 (.i 88)] 4) := by dec_rfl
theorem p0_8 : ∀ feat, Dec feat p0 8 (FV7z.mk .mov 32 [gr 32 10, Src.opd 32 (.r 6)] 3) := by dec_rfl
theorem p0_11 : ∀ feat, Dec feat p0 11 (FV7z.mk .mov 64 [gr 64 9, Src.opd 64 (.r 7)] 3) := by dec_rfl
theorem p0_14 : ∀ feat, Dec feat p0 14 (FV7z.mk .mov 32 [gr 32 8, Src.opd 32 (.r 6)] 3) := by dec_rfl
theorem p0_17 : ∀ feat, Dec feat p0 17 (FV7z.mk .mov 64 [.mem (mg (some 4) none 1 48 64), gr 64 2] 5) := by dec_rfl
theorem p0_22 : ∀ feat, Dec feat p0 22 (FV7z.mk .mov 64 [gr 64 0, .mem (mf none none 1 40 64)] 9) := by dec_rfl
theorem p0_31 : ∀ feat, Dec feat p0 31 (FV7z.mk .mov 64 [.mem (mg (some 4) none 1 24 64), gr 64 0] 5) := by dec_rfl
theorem p0_36 : ∀ feat, Dec feat p0 36 (FV7z.mk .xor 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl
theorem p0_38 : ∀ feat, Dec feat p0 38 (FV7z.mk .and 32 [gr 32 10, Src.opd 32 (.i 64)] 4) := by dec_rfl

/-- What the stretch does. -/
def o0 (fb : Addr) : List Op := [
  Op.nop,
  Op.sub 64 4 (.i 88),
  Op.mov 32 10 (.r 6),
  Op.mov 64 9 (.r 7),
  Op.mov 32 8 (.r 6),
  Op.st 64 (some 4) none 1 48 2,
  Op.ldf fb 64 0 none none 1 40,
  Op.st 64 (some 4) none 1 24 0,
  Op.xor 32 0 (.r 0),
  Op.and 32 10 (.i 64)]

theorem b0 (prof : Profile) (fb : Addr) : BlkF prof p0 (0x666090 : Addr) fb 0 42 (o0 fb) :=
  .cons (p0_0 _) (((OpI.endbr).at _).fs _) (by decide) <|
  .cons (p0_4 _) (((OpI.sub (.i 88) (.inr rfl)).at _).fs _) (by decide) <|
  .cons (p0_8 _) (((OpI.mov (.r 6) (.inl rfl)).at _).fs _) (by decide) <|
  .cons (p0_11 _) (((OpI.mov (.r 7) (.inr rfl)).at _).fs _) (by decide) <|
  .cons (p0_14 _) (((OpI.mov (.r 6) (.inl rfl)).at _).fs _) (by decide) <|
  .cons (p0_17 _) (((OpI.st (.inr (.inr (.inr rfl)))).at _).fs _) (by decide) <|
  .cons (p0_22 _) (OpIF.ldf (.inr rfl)) (by decide) <|
  .cons (p0_31 _) (((OpI.st (.inr (.inr (.inr rfl)))).at _).fs _) (by decide) <|
  .cons (p0_36 _) (((OpI.xor (.r 0) (.inl rfl)).at _).fs _) (by decide) <|
  .cons (p0_38 _) (((OpI.and (.i 64) (.inl rfl)).at _).fs _) (by decide) <|
  .nil 42

def j0 : List Byte := [0x75, 0x44]
theorem j0_0 : ∀ feat, Dec feat j0 0 (FV7z.mk (.jcc 5) 64 [.rel 68] 2) := by dec_rfl

/-- The stretch at `44`. -/
def p1 : List Byte := [
  0x89, 0xf0, 0x25, 0x00, 0x00, 0x41, 0x00, 0x3d, 0x00, 0x00, 0x41, 0x00]

theorem p1_0 : ∀ feat, Dec feat p1 0 (FV7z.mk .mov 32 [gr 32 0, Src.opd 32 (.r 6)] 2) := by dec_rfl
theorem p1_2 : ∀ feat, Dec feat p1 2 (FV7z.mk .and 32 [gr 32 0, Src.opd 32 (.i 4259840)] 5) := by dec_rfl
theorem p1_7 : ∀ feat, Dec feat p1 7 (FV7z.mk .cmp 32 [gr 32 0, Src.opd 32 (.i 4259840)] 5) := by dec_rfl

/-- What the stretch does. -/
def o1 : List Op := [
  Op.mov 32 0 (.r 6),
  Op.and 32 0 (.i 4259840),
  Op.cmp 32 0 (.i 4259840)]

theorem b1 (prof : Profile) : Blk prof p1 0 12 o1 :=
  .cons (p1_0 _) (OpI.mov (.r 6) (.inl rfl)) (by decide) <|
  .cons (p1_2 _) (OpI.and (.i 4259840) (.inl rfl)) (by decide) <|
  .cons (p1_7 _) (OpI.cmp (.i 4259840) (.inl rfl)) (by decide) <|
  .nil 12

def j1 : List Byte := [0x74, 0x36]
theorem j1_0 : ∀ feat, Dec feat j1 0 (FV7z.mk (.jcc 4) 64 [.rel 54] 2) := by dec_rfl

/-- The stretch at `58`. -/
def p2 : List Byte := [
  0x44, 0x89, 0xc2, 0x4c, 0x89, 0xce, 0xbf, 0x9c, 0xff, 0xff, 0xff, 0xb8, 0x01, 0x01, 0x00, 0x00]

theorem p2_0 : ∀ feat, Dec feat p2 0 (FV7z.mk .mov 32 [gr 32 2, Src.opd 32 (.r 8)] 3) := by dec_rfl
theorem p2_3 : ∀ feat, Dec feat p2 3 (FV7z.mk .mov 64 [gr 64 6, Src.opd 64 (.r 9)] 3) := by dec_rfl
theorem p2_6 : ∀ feat, Dec feat p2 6 (FV7z.mk .mov 32 [gr 32 7, Src.opd 32 (.i 4294967196)] 5) := by dec_rfl
theorem p2_11 : ∀ feat, Dec feat p2 11 (FV7z.mk .mov 32 [gr 32 0, Src.opd 32 (.i 257)] 5) := by dec_rfl

/-- What the stretch does. -/
def o2 : List Op := [
  Op.mov 32 2 (.r 8),
  Op.mov 64 6 (.r 9),
  Op.mov 32 7 (.i 4294967196),
  Op.mov 32 0 (.i 257)]

theorem b2 (prof : Profile) : Blk prof p2 0 16 o2 :=
  .cons (p2_0 _) (OpI.mov (.r 8) (.inl rfl)) (by decide) <|
  .cons (p2_3 _) (OpI.mov (.r 9) (.inr rfl)) (by decide) <|
  .cons (p2_6 _) (OpI.mov (.i 4294967196) (.inl rfl)) (by decide) <|
  .cons (p2_11 _) (OpI.mov (.i 257) (.inl rfl)) (by decide) <|
  .nil 16

/-- The stretch at `76`. -/
def p3 : List Byte := [
  0x48, 0x3d, 0x00, 0xf0, 0xff, 0xff]

theorem p3_0 : ∀ feat, Dec feat p3 0 (FV7z.mk .cmp 64 [gr 64 0, Src.opd 64 (.i 18446744073709547520)] 6) := by dec_rfl

/-- What the stretch does. -/
def o3 : List Op := [
  Op.cmp 64 0 (.i 18446744073709547520)]

theorem b3 (prof : Profile) : Blk prof p3 0 6 o3 :=
  .cons (p3_0 _) (OpI.cmp (.i 18446744073709547520) (.inr rfl)) (by decide) <|
  .nil 6

def j2 : List Byte := [0x77, 0x44]
theorem j2_0 : ∀ feat, Dec feat j2 0 (FV7z.mk (.jcc 7) 64 [.rel 68] 2) := by dec_rfl

/-- The stretch at `84`. -/
def p4 : List Byte := [
  0x48, 0x8b, 0x4c, 0x24, 0x18, 0x64, 0x48, 0x33, 0x0c, 0x25, 0x28, 0x00, 0x00, 0x00]

theorem p4_0 : ∀ feat, Dec feat p4 0 (FV7z.mk .mov 64 [gr 64 1, .mem (mg (some 4) none 1 24 64)] 5) := by dec_rfl
theorem p4_5 : ∀ feat, Dec feat p4 5 (FV7z.mk .xor 64 [gr 64 1, .mem (mf none none 1 40 64)] 9) := by dec_rfl

/-- What the stretch does. -/
def o4 (fb : Addr) : List Op := [
  Op.ld 64 1 (some 4) none 1 24,
  Op.xormf fb 64 1 none none 1 40]

theorem b4 (prof : Profile) (fb : Addr) : BlkF prof p4 (0x6660e4 : Addr) fb 0 14 (o4 fb) :=
  .cons (p4_0 _) (((OpI.ld (.inr rfl)).at _).fs _) (by decide) <|
  .cons (p4_5 _) (OpIF.xormf (.inr rfl)) (by decide) <|
  .nil 14

def j3 : List Byte := [0x75, 0x47]
theorem j3_0 : ∀ feat, Dec feat j3 0 (FV7z.mk (.jcc 5) 64 [.rel 71] 2) := by dec_rfl

/-- The stretch at `100`. -/
def p5 : List Byte := [
  0x48, 0x83, 0xc4, 0x58]

theorem p5_0 : ∀ feat, Dec feat p5 0 (FV7z.mk .add 64 [gr 64 4, Src.opd 64 (.i 88)] 4) := by dec_rfl

/-- What the stretch does. -/
def o5 : List Op := [
  Op.add 64 4 (.i 88)]

theorem b5 (prof : Profile) : Blk prof p5 0 4 o5 :=
  .cons (p5_0 _) (OpI.add (.i 88) (.inr rfl)) (by decide) <|
  .nil 4

/-- The stretch at `152`. -/
def p6 : List Byte := [
  0x48, 0xc7, 0xc2, 0xb8, 0xff, 0xff, 0xff, 0xf7, 0xd8, 0x64, 0x89, 0x02, 0xb8, 0xff, 0xff, 0xff,
  0xff]

theorem p6_0 : ∀ feat, Dec feat p6 0 (FV7z.mk .mov 64 [gr 64 2, Src.opd 64 (.i 18446744073709551544)] 7) := by dec_rfl
theorem p6_7 : ∀ feat, Dec feat p6 7 (FV7z.mk .neg 32 [gr 32 0] 2) := by dec_rfl
theorem p6_9 : ∀ feat, Dec feat p6 9 (FV7z.mk .mov 32 [.mem (mf (some 2) none 1 0 32), gr 32 0] 3) := by dec_rfl
theorem p6_12 : ∀ feat, Dec feat p6 12 (FV7z.mk .mov 32 [gr 32 0, Src.opd 32 (.i 4294967295)] 5) := by dec_rfl

/-- What the stretch does. -/
def o6 (fb : Addr) : List Op := [
  Op.mov 64 2 (.i 18446744073709551544),
  Op.neg 32 0,
  Op.stf fb 32 (some 2) none 1 0 0,
  Op.mov 32 0 (.i 4294967295)]

theorem b6 (prof : Profile) (fb : Addr) : BlkF prof p6 (0x666128 : Addr) fb 0 17 (o6 fb) :=
  .cons (p6_0 _) (((OpI.mov (.i 18446744073709551544) (.inr rfl)).at _).fs _) (by decide) <|
  .cons (p6_7 _) (((OpI.neg (.inl rfl)).at _).fs _) (by decide) <|
  .cons (p6_9 _) (OpIF.stf (.inl rfl)) (by decide) <|
  .cons (p6_12 _) (((OpI.mov (.i 4294967295) (.inl rfl)).at _).fs _) (by decide) <|
  .nil 17

def j4 : List Byte := [0xeb, 0xa9]
theorem j4_0 : ∀ feat, Dec feat j4 0 (FV7z.mk .jmp 64 [.rel 18446744073709551529] 2) := by dec_rfl

end FV7z.Onc
