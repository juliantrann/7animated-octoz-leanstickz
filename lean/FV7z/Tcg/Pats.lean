import FV7z.Lemmas.SpFs
import FV7z.Lemmas.BlkOps6
import FV7z.Lemmas.BlkOps2
/-!
# The stretches of straight-line code of `__tcgetattr` (PLAN.md §M, M1)

Each distinct stretch between labels and jumps (`p*`, 7 of them) and each distinct jump (`j*`, 4) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.Tcg
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The stretch at `0`. -/
def p0 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0x48, 0x83, 0xec, 0x38, 0x49, 0x89, 0xf0, 0xbe, 0x01, 0x54, 0x00, 0x00,
  0x64, 0x48, 0x8b, 0x04, 0x25, 0x28, 0x00, 0x00, 0x00, 0x48, 0x89, 0x44, 0x24, 0x28, 0x31, 0xc0,
  0x48, 0x89, 0xe2, 0xb8, 0x10, 0x00, 0x00, 0x00]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem p0_4 : ∀ feat, Dec feat p0 4 (FV7z.mk .sub 64 [gr 64 4, Src.opd 64 (.i 56)] 4) := by dec_rfl
theorem p0_8 : ∀ feat, Dec feat p0 8 (FV7z.mk .mov 64 [gr 64 8, Src.opd 64 (.r 6)] 3) := by dec_rfl
theorem p0_11 : ∀ feat, Dec feat p0 11 (FV7z.mk .mov 32 [gr 32 6, Src.opd 32 (.i 21505)] 5) := by dec_rfl
theorem p0_16 : ∀ feat, Dec feat p0 16 (FV7z.mk .mov 64 [gr 64 0, .mem (mf none none 1 40 64)] 9) := by dec_rfl
theorem p0_25 : ∀ feat, Dec feat p0 25 (FV7z.mk .mov 64 [.mem (mg (some 4) none 1 40 64), gr 64 0] 5) := by dec_rfl
theorem p0_30 : ∀ feat, Dec feat p0 30 (FV7z.mk .xor 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl
theorem p0_32 : ∀ feat, Dec feat p0 32 (FV7z.mk .mov 64 [gr 64 2, Src.opd 64 (.r 4)] 3) := by dec_rfl
theorem p0_35 : ∀ feat, Dec feat p0 35 (FV7z.mk .mov 32 [gr 32 0, Src.opd 32 (.i 16)] 5) := by dec_rfl

/-- What the stretch does. -/
def o0 (fb : Addr) : List Op := [
  Op.nop,
  Op.sub 64 4 (.i 56),
  Op.mov 64 8 (.r 6),
  Op.mov 32 6 (.i 21505),
  Op.ldf fb 64 0 none none 1 40,
  Op.st 64 (some 4) none 1 40 0,
  Op.xor 32 0 (.r 0),
  Op.mov 64 2 (.r 4),
  Op.mov 32 0 (.i 16)]

theorem b0 (prof : Profile) (fb : Addr) : BlkF prof p0 (0x666240 : Addr) fb 0 40 (o0 fb) :=
  .cons (p0_0 _) (((OpI.endbr).at _).fs _) (by decide) <|
  .cons (p0_4 _) (((OpI.sub (.i 56) (.inr rfl)).at _).fs _) (by decide) <|
  .cons (p0_8 _) (((OpI.mov (.r 6) (.inr rfl)).at _).fs _) (by decide) <|
  .cons (p0_11 _) (((OpI.mov (.i 21505) (.inl rfl)).at _).fs _) (by decide) <|
  .cons (p0_16 _) (OpIF.ldf (.inr rfl)) (by decide) <|
  .cons (p0_25 _) (((OpI.st (.inr (.inr (.inr rfl)))).at _).fs _) (by decide) <|
  .cons (p0_30 _) (((OpI.xor (.r 0) (.inl rfl)).at _).fs _) (by decide) <|
  .cons (p0_32 _) (((OpI.mov (.r 4) (.inr rfl)).at _).fs _) (by decide) <|
  .cons (p0_35 _) (((OpI.mov (.i 16) (.inl rfl)).at _).fs _) (by decide) <|
  .nil 40

/-- The stretch at `42`. -/
def p1 : List Byte := [
  0x48, 0x3d, 0x00, 0xf0, 0xff, 0xff]

theorem p1_0 : ∀ feat, Dec feat p1 0 (FV7z.mk .cmp 64 [gr 64 0, Src.opd 64 (.i 18446744073709547520)] 6) := by dec_rfl

/-- What the stretch does. -/
def o1 : List Op := [
  Op.cmp 64 0 (.i 18446744073709547520)]

theorem b1 (prof : Profile) : Blk prof p1 0 6 o1 :=
  .cons (p1_0 _) (OpI.cmp (.i 18446744073709547520) (.inr rfl)) (by decide) <|
  .nil 6

def j0 : List Byte := [0x77, 0x7e]
theorem j0_0 : ∀ feat, Dec feat j0 0 (FV7z.mk (.jcc 7) 64 [.rel 126] 2) := by dec_rfl

/-- The stretch at `50`. -/
def p2 : List Byte := [
  0x41, 0x89, 0xc1, 0x85, 0xc0]

theorem p2_0 : ∀ feat, Dec feat p2 0 (FV7z.mk .mov 32 [gr 32 9, Src.opd 32 (.r 0)] 3) := by dec_rfl
theorem p2_3 : ∀ feat, Dec feat p2 3 (FV7z.mk .test 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl

/-- What the stretch does. -/
def o2 : List Op := [
  Op.mov 32 9 (.r 0),
  Op.test 32 0 (.r 0)]

theorem b2 (prof : Profile) : Blk prof p2 0 5 o2 :=
  .cons (p2_0 _) (OpI.mov (.r 0) (.inl rfl)) (by decide) <|
  .cons (p2_3 _) (OpI.test (.r 0) (.inl rfl)) (by decide) <|
  .nil 5

def j1 : List Byte := [0x75, 0x56]
theorem j1_0 : ∀ feat, Dec feat j1 0 (FV7z.mk (.jcc 5) 64 [.rel 86] 2) := by dec_rfl

/-- The stretch at `57`. -/
def p3 : List Byte := [
  0x0f, 0xb6, 0x44, 0x24, 0x10, 0x0f, 0xb7, 0x54, 0x24, 0x21, 0x49, 0xc7, 0x40, 0x24, 0x00, 0x00,
  0x00, 0x00]

theorem p3_0 : ∀ feat, Dec feat p3 0 (FV7z.mk .movzx 32 [gr 32 0, .mem (mg (some 4) none 1 16 8)] 5) := by dec_rfl
theorem p3_5 : ∀ feat, Dec feat p3 5 (FV7z.mk .movzx 32 [gr 32 2, .mem (mg (some 4) none 1 33 16)] 5) := by dec_rfl
theorem p3_10 : ∀ feat, Dec feat p3 10 (FV7z.mk .mov 64 [.mem (mg (some 8) none 1 36 64), .imm 64 0] 8) := by dec_rfl

/-- What the stretch does. -/
def o3 : List Op := [
  Op.ldzx 8 0 (some 4) none 1 16,
  Op.ldzx 16 2 (some 4) none 1 33,
  Op.sti 64 (some 8) none 1 36 0]

theorem b3 (prof : Profile) : Blk prof p3 0 18 o3 :=
  .cons (p3_0 _) (OpI.ldzx (.inl rfl)) (by decide) <|
  .cons (p3_5 _) (OpI.ldzx (.inr rfl)) (by decide) <|
  .cons (p3_10 _) (OpI.sti (.inr (.inr (.inr rfl)))) (by decide) <|
  .nil 18

/-- The stretch at `143`. -/
def p4 : List Byte := [
  0x48, 0x8b, 0x44, 0x24, 0x28, 0x64, 0x48, 0x33, 0x04, 0x25, 0x28, 0x00, 0x00, 0x00]

theorem p4_0 : ∀ feat, Dec feat p4 0 (FV7z.mk .mov 64 [gr 64 0, .mem (mg (some 4) none 1 40 64)] 5) := by dec_rfl
theorem p4_5 : ∀ feat, Dec feat p4 5 (FV7z.mk .xor 64 [gr 64 0, .mem (mf none none 1 40 64)] 9) := by dec_rfl

/-- What the stretch does. -/
def o4 (fb : Addr) : List Op := [
  Op.ld 64 0 (some 4) none 1 40,
  Op.xormf fb 64 0 none none 1 40]

theorem b4 (prof : Profile) (fb : Addr) : BlkF prof p4 (0x6662cf : Addr) fb 0 14 (o4 fb) :=
  .cons (p4_0 _) (((OpI.ld (.inr rfl)).at _).fs _) (by decide) <|
  .cons (p4_5 _) (OpIF.xormf (.inr rfl)) (by decide) <|
  .nil 14

def j2 : List Byte := [0x75, 0x25]
theorem j2_0 : ∀ feat, Dec feat j2 0 (FV7z.mk (.jcc 5) 64 [.rel 37] 2) := by dec_rfl

/-- The stretch at `159`. -/
def p5 : List Byte := [
  0x44, 0x89, 0xc8, 0x48, 0x83, 0xc4, 0x38]

theorem p5_0 : ∀ feat, Dec feat p5 0 (FV7z.mk .mov 32 [gr 32 0, Src.opd 32 (.r 9)] 3) := by dec_rfl
theorem p5_3 : ∀ feat, Dec feat p5 3 (FV7z.mk .add 64 [gr 64 4, Src.opd 64 (.i 56)] 4) := by dec_rfl

/-- What the stretch does. -/
def o5 : List Op := [
  Op.mov 32 0 (.r 9),
  Op.add 64 4 (.i 56)]

theorem b5 (prof : Profile) : Blk prof p5 0 7 o5 :=
  .cons (p5_0 _) (OpI.mov (.r 9) (.inl rfl)) (by decide) <|
  .cons (p5_3 _) (OpI.add (.i 56) (.inr rfl)) (by decide) <|
  .nil 7

/-- The stretch at `176`. -/
def p6 : List Byte := [
  0x48, 0xc7, 0xc2, 0xb8, 0xff, 0xff, 0xff, 0xf7, 0xd8, 0x41, 0xb9, 0xff, 0xff, 0xff, 0xff, 0x64,
  0x89, 0x02]

theorem p6_0 : ∀ feat, Dec feat p6 0 (FV7z.mk .mov 64 [gr 64 2, Src.opd 64 (.i 18446744073709551544)] 7) := by dec_rfl
theorem p6_7 : ∀ feat, Dec feat p6 7 (FV7z.mk .neg 32 [gr 32 0] 2) := by dec_rfl
theorem p6_9 : ∀ feat, Dec feat p6 9 (FV7z.mk .mov 32 [gr 32 9, Src.opd 32 (.i 4294967295)] 6) := by dec_rfl
theorem p6_15 : ∀ feat, Dec feat p6 15 (FV7z.mk .mov 32 [.mem (mf (some 2) none 1 0 32), gr 32 0] 3) := by dec_rfl

/-- What the stretch does. -/
def o6 (fb : Addr) : List Op := [
  Op.mov 64 2 (.i 18446744073709551544),
  Op.neg 32 0,
  Op.mov 32 9 (.i 4294967295),
  Op.stf fb 32 (some 2) none 1 0 0]

theorem b6 (prof : Profile) (fb : Addr) : BlkF prof p6 (0x6662f0 : Addr) fb 0 18 (o6 fb) :=
  .cons (p6_0 _) (((OpI.mov (.i 18446744073709551544) (.inr rfl)).at _).fs _) (by decide) <|
  .cons (p6_7 _) (((OpI.neg (.inl rfl)).at _).fs _) (by decide) <|
  .cons (p6_9 _) (((OpI.mov (.i 4294967295) (.inl rfl)).at _).fs _) (by decide) <|
  .cons (p6_15 _) (OpIF.stf (.inl rfl)) (by decide) <|
  .nil 18

def j3 : List Byte := [0xeb, 0xcb]
theorem j3_0 : ∀ feat, Dec feat j3 0 (FV7z.mk .jmp 64 [.rel 18446744073709551563] 2) := by dec_rfl

end FV7z.Tcg
