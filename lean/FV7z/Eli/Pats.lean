import FV7z.Lemmas.SpFs
import FV7z.Lemmas.BlkOps6
import FV7z.Lemmas.BlkOps2
/-!
# The stretches of straight-line code of `elision_init` (PLAN.md G3, startup)

Each distinct stretch between labels and jumps (`p*`, 9 of them) and each distinct jump (`j*`, 2) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.Eli
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The stretch at `0`. -/
def p0 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0x55, 0x48, 0x8d, 0x15, 0xb4, 0x00, 0x00, 0x00, 0xbf, 0x05, 0x00, 0x00,
  0x00, 0x48, 0x83, 0xec, 0x10, 0x64, 0x48, 0x8b, 0x04, 0x25, 0x28, 0x00, 0x00, 0x00, 0x48, 0x89,
  0x44, 0x24, 0x08, 0x31, 0xc0, 0x48, 0x8d, 0x6c, 0x24, 0x04, 0x48, 0x89, 0xee]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem p0_4 : ∀ feat, Dec feat p0 4 (FV7z.mk .push 64 [gr 64 5] 1) := by dec_rfl
theorem p0_5 : ∀ feat, Dec feat p0 5 (FV7z.mk .lea 64 [gr 64 2, .mem (mrip 180 0)] 7) := by dec_rfl
theorem p0_12 : ∀ feat, Dec feat p0 12 (FV7z.mk .mov 32 [gr 32 7, Src.opd 32 (.i 5)] 5) := by dec_rfl
theorem p0_17 : ∀ feat, Dec feat p0 17 (FV7z.mk .sub 64 [gr 64 4, Src.opd 64 (.i 16)] 4) := by dec_rfl
theorem p0_21 : ∀ feat, Dec feat p0 21 (FV7z.mk .mov 64 [gr 64 0, .mem (mf none none 1 40 64)] 9) := by dec_rfl
theorem p0_30 : ∀ feat, Dec feat p0 30 (FV7z.mk .mov 64 [.mem (mg (some 4) none 1 8 64), gr 64 0] 5) := by dec_rfl
theorem p0_35 : ∀ feat, Dec feat p0 35 (FV7z.mk .xor 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl
theorem p0_37 : ∀ feat, Dec feat p0 37 (FV7z.mk .lea 64 [gr 64 5, .mem (mg (some 4) none 1 4 0)] 5) := by dec_rfl
theorem p0_42 : ∀ feat, Dec feat p0 42 (FV7z.mk .mov 64 [gr 64 6, Src.opd 64 (.r 5)] 3) := by dec_rfl

/-- What the stretch does. -/
def o0 (fb : Addr) : List Op := [
  Op.nop,
  Op.push 5,
  Op.mov 64 2 (.i 6290704),
  Op.mov 32 7 (.i 5),
  Op.sub 64 4 (.i 16),
  Op.ldf fb 64 0 none none 1 40,
  Op.st 64 (some 4) none 1 8 0,
  Op.xor 32 0 (.r 0),
  Op.lea 64 5 (some 4) none 1 4,
  Op.mov 64 6 (.r 5)]

theorem b0 (prof : Profile) (fb : Addr) : BlkF prof p0 (0x5ffc50 : Addr) fb 0 45 (o0 fb) :=
  .cons (p0_0 _) (((OpI.endbr).at _).fs _) (by decide) <|
  .cons (p0_4 _) (((OpI.push).at _).fs _) (by decide) <|
  .cons (p0_5 _) ((OpIA.lea_rip (by decide)).fs _) (by decide) <|
  .cons (p0_12 _) (((OpI.mov (.i 5) (.inl rfl)).at _).fs _) (by decide) <|
  .cons (p0_17 _) (((OpI.sub (.i 16) (.inr rfl)).at _).fs _) (by decide) <|
  .cons (p0_21 _) (OpIF.ldf (.inr rfl)) (by decide) <|
  .cons (p0_30 _) (((OpI.st (.inr (.inr (.inr rfl)))).at _).fs _) (by decide) <|
  .cons (p0_35 _) (((OpI.xor (.r 0) (.inl rfl)).at _).fs _) (by decide) <|
  .cons (p0_37 _) (((OpI.lea (.inr rfl)).at _).fs _) (by decide) <|
  .cons (p0_42 _) (((OpI.mov (.r 5) (.inr rfl)).at _).fs _) (by decide) <|
  .nil 45

/-- The stretch at `50`. -/
def p1 : List Byte := [
  0x48, 0x8d, 0x15, 0x87, 0xff, 0xff, 0xff, 0x48, 0x89, 0xee, 0xbf, 0x07, 0x00, 0x00, 0x00]

theorem p1_0 : ∀ feat, Dec feat p1 0 (FV7z.mk .lea 64 [gr 64 2, .mem (mrip 18446744073709551495 0)] 7) := by dec_rfl
theorem p1_7 : ∀ feat, Dec feat p1 7 (FV7z.mk .mov 64 [gr 64 6, Src.opd 64 (.r 5)] 3) := by dec_rfl
theorem p1_10 : ∀ feat, Dec feat p1 10 (FV7z.mk .mov 32 [gr 32 7, Src.opd 32 (.i 7)] 5) := by dec_rfl

/-- What the stretch does. -/
def o1 : List Op := [
  Op.mov 64 2 (.i 6290448),
  Op.mov 64 6 (.r 5),
  Op.mov 32 7 (.i 7)]

theorem b1 (prof : Profile) : BlkA prof p1 (0x5ffc82 : Addr) 0 15 o1 :=
  .cons (p1_0 _) (OpIA.lea_rip (by decide)) (by decide) <|
  .cons (p1_7 _) ((OpI.mov (.r 5) (.inr rfl)).at _) (by decide) <|
  .cons (p1_10 _) ((OpI.mov (.i 7) (.inl rfl)).at _) (by decide) <|
  .nil 15

/-- The stretch at `70`. -/
def p2 : List Byte := [
  0x48, 0x8d, 0x15, 0x83, 0xff, 0xff, 0xff, 0x48, 0x89, 0xee, 0xbf, 0x11, 0x00, 0x00, 0x00]

theorem p2_0 : ∀ feat, Dec feat p2 0 (FV7z.mk .lea 64 [gr 64 2, .mem (mrip 18446744073709551491 0)] 7) := by dec_rfl
theorem p2_7 : ∀ feat, Dec feat p2 7 (FV7z.mk .mov 64 [gr 64 6, Src.opd 64 (.r 5)] 3) := by dec_rfl
theorem p2_10 : ∀ feat, Dec feat p2 10 (FV7z.mk .mov 32 [gr 32 7, Src.opd 32 (.i 17)] 5) := by dec_rfl

/-- What the stretch does. -/
def o2 : List Op := [
  Op.mov 64 2 (.i 6290464),
  Op.mov 64 6 (.r 5),
  Op.mov 32 7 (.i 17)]

theorem b2 (prof : Profile) : BlkA prof p2 (0x5ffc96 : Addr) 0 15 o2 :=
  .cons (p2_0 _) (OpIA.lea_rip (by decide)) (by decide) <|
  .cons (p2_7 _) ((OpI.mov (.r 5) (.inr rfl)).at _) (by decide) <|
  .cons (p2_10 _) ((OpI.mov (.i 17) (.inl rfl)).at _) (by decide) <|
  .nil 15

/-- The stretch at `90`. -/
def p3 : List Byte := [
  0x48, 0x8d, 0x15, 0x7f, 0xff, 0xff, 0xff, 0x48, 0x89, 0xee, 0xbf, 0x04, 0x00, 0x00, 0x00]

theorem p3_0 : ∀ feat, Dec feat p3 0 (FV7z.mk .lea 64 [gr 64 2, .mem (mrip 18446744073709551487 0)] 7) := by dec_rfl
theorem p3_7 : ∀ feat, Dec feat p3 7 (FV7z.mk .mov 64 [gr 64 6, Src.opd 64 (.r 5)] 3) := by dec_rfl
theorem p3_10 : ∀ feat, Dec feat p3 10 (FV7z.mk .mov 32 [gr 32 7, Src.opd 32 (.i 4)] 5) := by dec_rfl

/-- What the stretch does. -/
def o3 : List Op := [
  Op.mov 64 2 (.i 6290480),
  Op.mov 64 6 (.r 5),
  Op.mov 32 7 (.i 4)]

theorem b3 (prof : Profile) : BlkA prof p3 (0x5ffcaa : Addr) 0 15 o3 :=
  .cons (p3_0 _) (OpIA.lea_rip (by decide)) (by decide) <|
  .cons (p3_7 _) ((OpI.mov (.r 5) (.inr rfl)).at _) (by decide) <|
  .cons (p3_10 _) ((OpI.mov (.i 4) (.inl rfl)).at _) (by decide) <|
  .nil 15

/-- The stretch at `110`. -/
def p4 : List Byte := [
  0x48, 0x8d, 0x15, 0x7b, 0xff, 0xff, 0xff, 0x48, 0x89, 0xee, 0xbf, 0x0d, 0x00, 0x00, 0x00]

theorem p4_0 : ∀ feat, Dec feat p4 0 (FV7z.mk .lea 64 [gr 64 2, .mem (mrip 18446744073709551483 0)] 7) := by dec_rfl
theorem p4_7 : ∀ feat, Dec feat p4 7 (FV7z.mk .mov 64 [gr 64 6, Src.opd 64 (.r 5)] 3) := by dec_rfl
theorem p4_10 : ∀ feat, Dec feat p4 10 (FV7z.mk .mov 32 [gr 32 7, Src.opd 32 (.i 13)] 5) := by dec_rfl

/-- What the stretch does. -/
def o4 : List Op := [
  Op.mov 64 2 (.i 6290496),
  Op.mov 64 6 (.r 5),
  Op.mov 32 7 (.i 13)]

theorem b4 (prof : Profile) : BlkA prof p4 (0x5ffcbe : Addr) 0 15 o4 :=
  .cons (p4_0 _) (OpIA.lea_rip (by decide)) (by decide) <|
  .cons (p4_7 _) ((OpI.mov (.r 5) (.inr rfl)).at _) (by decide) <|
  .cons (p4_10 _) ((OpI.mov (.i 13) (.inl rfl)).at _) (by decide) <|
  .nil 15

/-- The stretch at `130`. -/
def p5 : List Byte := [
  0x8b, 0x05, 0x74, 0xf4, 0x19, 0x00, 0x85, 0xc0]

theorem p5_0 : ∀ feat, Dec feat p5 0 (FV7z.mk .mov 32 [gr 32 0, .mem (mrip 1700980 32)] 6) := by dec_rfl
theorem p5_6 : ∀ feat, Dec feat p5 6 (FV7z.mk .test 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl

/-- What the stretch does. -/
def o5 : List Op := [
  Op.lda 32 0 7991628,
  Op.test 32 0 (.r 0)]

theorem b5 (prof : Profile) : BlkA prof p5 (0x5ffcd2 : Addr) 0 8 o5 :=
  .cons (p5_0 _) (OpIA.ld_rip (.inl rfl) (by decide)) (by decide) <|
  .cons (p5_6 _) ((OpI.test (.r 0) (.inl rfl)).at _) (by decide) <|
  .nil 8

def j0 : List Byte := [0x75, 0x0a]
theorem j0_0 : ∀ feat, Dec feat j0 0 (FV7z.mk (.jcc 5) 64 [.rel 10] 2) := by dec_rfl

/-- The stretch at `140`. -/
def p6 : List Byte := [
  0xc7, 0x05, 0xa2, 0x25, 0x19, 0x00, 0x00, 0x00, 0x00, 0x00]

theorem p6_0 : ∀ feat, Dec feat p6 0 (FV7z.mk .mov 32 [.mem (mrip 1648034 32), .imm 32 0] 10) := by dec_rfl

/-- What the stretch does. -/
def o6 : List Op := [
  Op.stia 32 7938696 0]

theorem b6 (prof : Profile) : BlkA prof p6 (0x5ffcdc : Addr) 0 10 o6 :=
  .cons (p6_0 _) (OpIA.sti_rip (.inr (.inl rfl)) (by decide)) (by decide) <|
  .nil 10

/-- The stretch at `150`. -/
def p7 : List Byte := [
  0x48, 0x8b, 0x44, 0x24, 0x08, 0x64, 0x48, 0x33, 0x04, 0x25, 0x28, 0x00, 0x00, 0x00]

theorem p7_0 : ∀ feat, Dec feat p7 0 (FV7z.mk .mov 64 [gr 64 0, .mem (mg (some 4) none 1 8 64)] 5) := by dec_rfl
theorem p7_5 : ∀ feat, Dec feat p7 5 (FV7z.mk .xor 64 [gr 64 0, .mem (mf none none 1 40 64)] 9) := by dec_rfl

/-- What the stretch does. -/
def o7 (fb : Addr) : List Op := [
  Op.ld 64 0 (some 4) none 1 8,
  Op.xormf fb 64 0 none none 1 40]

theorem b7 (prof : Profile) (fb : Addr) : BlkF prof p7 (0x5ffce6 : Addr) fb 0 14 (o7 fb) :=
  .cons (p7_0 _) (((OpI.ld (.inr rfl)).at _).fs _) (by decide) <|
  .cons (p7_5 _) (OpIF.xormf (.inr rfl)) (by decide) <|
  .nil 14

def j1 : List Byte := [0x75, 0x06]
theorem j1_0 : ∀ feat, Dec feat j1 0 (FV7z.mk (.jcc 5) 64 [.rel 6] 2) := by dec_rfl

/-- The stretch at `166`. -/
def p8 : List Byte := [
  0x48, 0x83, 0xc4, 0x10, 0x5d]

theorem p8_0 : ∀ feat, Dec feat p8 0 (FV7z.mk .add 64 [gr 64 4, Src.opd 64 (.i 16)] 4) := by dec_rfl
theorem p8_4 : ∀ feat, Dec feat p8 4 (FV7z.mk .pop 64 [gr 64 5] 1) := by dec_rfl

/-- What the stretch does. -/
def o8 : List Op := [
  Op.add 64 4 (.i 16),
  Op.pop 5]

theorem b8 (prof : Profile) : Blk prof p8 0 5 o8 :=
  .cons (p8_0 _) (OpI.add (.i 16) (.inr rfl)) (by decide) <|
  .cons (p8_4 _) (OpI.pop) (by decide) <|
  .nil 5

end FV7z.Eli
