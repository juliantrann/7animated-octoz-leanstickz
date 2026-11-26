import FV7z.Lemmas.SpFs
import FV7z.Lemmas.CmpMi16
import FV7z.Lemmas.BlkOps25
import FV7z.Lemmas.BlkOps14
import FV7z.Lemmas.BlkOps6
import FV7z.Lemmas.BlkOps2
/-!
# The stretches of straight-line code of `Archive_GetItemBoolProp` (PLAN.md §M, M1)

Each distinct stretch between labels and jumps (`p*`, 8 of them) and each distinct jump (`j*`, 4) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.Gbp
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The stretch at `0`. -/
def p0 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0x41, 0x54, 0x55, 0x53, 0x48, 0x89, 0xcb, 0x48, 0x83, 0xec, 0x20, 0x64,
  0x48, 0x8b, 0x04, 0x25, 0x28, 0x00, 0x00, 0x00, 0x48, 0x89, 0x44, 0x24, 0x18, 0x31, 0xc0, 0x48,
  0x8b, 0x07, 0x48, 0x89, 0xe5, 0xc6, 0x01, 0x00, 0xc7, 0x04, 0x24, 0x00, 0x00, 0x00, 0x00, 0x48,
  0x89, 0xe9, 0x48, 0xc7, 0x44, 0x24, 0x08, 0x00, 0x00, 0x00, 0x00]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem p0_4 : ∀ feat, Dec feat p0 4 (FV7z.mk .push 64 [gr 64 12] 2) := by dec_rfl
theorem p0_6 : ∀ feat, Dec feat p0 6 (FV7z.mk .push 64 [gr 64 5] 1) := by dec_rfl
theorem p0_7 : ∀ feat, Dec feat p0 7 (FV7z.mk .push 64 [gr 64 3] 1) := by dec_rfl
theorem p0_8 : ∀ feat, Dec feat p0 8 (FV7z.mk .mov 64 [gr 64 3, Src.opd 64 (.r 1)] 3) := by dec_rfl
theorem p0_11 : ∀ feat, Dec feat p0 11 (FV7z.mk .sub 64 [gr 64 4, Src.opd 64 (.i 32)] 4) := by dec_rfl
theorem p0_15 : ∀ feat, Dec feat p0 15 (FV7z.mk .mov 64 [gr 64 0, .mem (mf none none 1 40 64)] 9) := by dec_rfl
theorem p0_24 : ∀ feat, Dec feat p0 24 (FV7z.mk .mov 64 [.mem (mg (some 4) none 1 24 64), gr 64 0] 5) := by dec_rfl
theorem p0_29 : ∀ feat, Dec feat p0 29 (FV7z.mk .xor 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl
theorem p0_31 : ∀ feat, Dec feat p0 31 (FV7z.mk .mov 64 [gr 64 0, .mem (mg (some 7) none 1 0 64)] 3) := by dec_rfl
theorem p0_34 : ∀ feat, Dec feat p0 34 (FV7z.mk .mov 64 [gr 64 5, Src.opd 64 (.r 4)] 3) := by dec_rfl
theorem p0_37 : ∀ feat, Dec feat p0 37 (FV7z.mk .mov 8 [.mem (mg (some 1) none 1 0 8), .imm 8 0] 3) := by dec_rfl
theorem p0_40 : ∀ feat, Dec feat p0 40 (FV7z.mk .mov 32 [.mem (mg (some 4) none 1 0 32), .imm 32 0] 7) := by dec_rfl
theorem p0_47 : ∀ feat, Dec feat p0 47 (FV7z.mk .mov 64 [gr 64 1, Src.opd 64 (.r 5)] 3) := by dec_rfl
theorem p0_50 : ∀ feat, Dec feat p0 50 (FV7z.mk .mov 64 [.mem (mg (some 4) none 1 8 64), .imm 64 0] 9) := by dec_rfl

/-- What the stretch does. -/
def o0 (fb : Addr) : List Op := [
  Op.nop,
  Op.push 12,
  Op.push 5,
  Op.push 3,
  Op.mov 64 3 (.r 1),
  Op.sub 64 4 (.i 32),
  Op.ldf fb 64 0 none none 1 40,
  Op.st 64 (some 4) none 1 24 0,
  Op.xor 32 0 (.r 0),
  Op.ld 64 0 (some 7) none 1 0,
  Op.mov 64 5 (.r 4),
  Op.sti 8 (some 1) none 1 0 0,
  Op.sti 32 (some 4) none 1 0 0,
  Op.mov 64 1 (.r 5),
  Op.sti 64 (some 4) none 1 8 0]

theorem b0 (prof : Profile) (fb : Addr) : BlkF prof p0 (0x5d15e0 : Addr) fb 0 59 (o0 fb) :=
  .cons (p0_0 _) (((OpI.endbr).at _).fs _) (by decide) <|
  .cons (p0_4 _) (((OpI.push).at _).fs _) (by decide) <|
  .cons (p0_6 _) (((OpI.push).at _).fs _) (by decide) <|
  .cons (p0_7 _) (((OpI.push).at _).fs _) (by decide) <|
  .cons (p0_8 _) (((OpI.mov (.r 1) (.inr rfl)).at _).fs _) (by decide) <|
  .cons (p0_11 _) (((OpI.sub (.i 32) (.inr rfl)).at _).fs _) (by decide) <|
  .cons (p0_15 _) (OpIF.ldf (.inr rfl)) (by decide) <|
  .cons (p0_24 _) (((OpI.st (.inr (.inr (.inr rfl)))).at _).fs _) (by decide) <|
  .cons (p0_29 _) (((OpI.xor (.r 0) (.inl rfl)).at _).fs _) (by decide) <|
  .cons (p0_31 _) (((OpI.ld (.inr rfl)).at _).fs _) (by decide) <|
  .cons (p0_34 _) (((OpI.mov (.r 4) (.inr rfl)).at _).fs _) (by decide) <|
  .cons (p0_37 _) (((OpI.sti (.inl rfl)).at _).fs _) (by decide) <|
  .cons (p0_40 _) (((OpI.sti (.inr (.inr (.inl rfl)))).at _).fs _) (by decide) <|
  .cons (p0_47 _) (((OpI.mov (.r 5) (.inr rfl)).at _).fs _) (by decide) <|
  .cons (p0_50 _) (((OpI.sti (.inr (.inr (.inr rfl)))).at _).fs _) (by decide) <|
  .nil 59

/-- The stretch at `62`. -/
def p1 : List Byte := [
  0x41, 0x89, 0xc4, 0x85, 0xc0]

theorem p1_0 : ∀ feat, Dec feat p1 0 (FV7z.mk .mov 32 [gr 32 12, Src.opd 32 (.r 0)] 3) := by dec_rfl
theorem p1_3 : ∀ feat, Dec feat p1 3 (FV7z.mk .test 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl

/-- What the stretch does. -/
def o1 : List Op := [
  Op.mov 32 12 (.r 0),
  Op.test 32 0 (.r 0)]

theorem b1 (prof : Profile) : Blk prof p1 0 5 o1 :=
  .cons (p1_0 _) (OpI.mov (.r 0) (.inl rfl)) (by decide) <|
  .cons (p1_3 _) (OpI.test (.r 0) (.inl rfl)) (by decide) <|
  .nil 5

def j0 : List Byte := [0x75, 0x16]
theorem j0_0 : ∀ feat, Dec feat j0 0 (FV7z.mk (.jcc 5) 64 [.rel 22] 2) := by dec_rfl

/-- The stretch at `69`. -/
def p2 : List Byte := [
  0x0f, 0xb7, 0x04, 0x24, 0x66, 0x83, 0xf8, 0x0b]

theorem p2_0 : ∀ feat, Dec feat p2 0 (FV7z.mk .movzx 32 [gr 32 0, .mem (mg (some 4) none 1 0 16)] 4) := by dec_rfl
theorem p2_4 : ∀ feat, Dec feat p2 4 (FV7z.mk .cmp 16 [gr 16 0, Src.opd 16 (.i 11)] 4) := by dec_rfl

/-- What the stretch does. -/
def o2 : List Op := [
  Op.ldzx 16 0 (some 4) none 1 0,
  Op.cmp 16 0 (.i 11)]

theorem b2 (prof : Profile) : Blk prof p2 0 8 o2 :=
  .cons (p2_0 _) (OpI.ldzx (.inr rfl)) (by decide) <|
  .cons (p2_4 _) (OpI.cmp16 (.i 11)) (by decide) <|
  .nil 8

def j1 : List Byte := [0x74, 0x31]
theorem j1_0 : ∀ feat, Dec feat j1 0 (FV7z.mk (.jcc 4) 64 [.rel 49] 2) := by dec_rfl

/-- The stretch at `79`. -/
def p3 : List Byte := [
  0x66, 0x85, 0xc0, 0xb8, 0x05, 0x40, 0x00, 0x80, 0x44, 0x0f, 0x45, 0xe0]

theorem p3_0 : ∀ feat, Dec feat p3 0 (FV7z.mk .test 16 [gr 16 0, Src.opd 16 (.r 0)] 3) := by dec_rfl
theorem p3_3 : ∀ feat, Dec feat p3 3 (FV7z.mk .mov 32 [gr 32 0, Src.opd 32 (.i 2147500037)] 5) := by dec_rfl
theorem p3_8 : ∀ feat, Dec feat p3 8 (FV7z.mk (.cmovcc 5) 32 [gr 32 12, gr 32 0] 4) := by dec_rfl

/-- What the stretch does. -/
def o3 : List Op := [
  Op.test 16 0 (.r 0),
  Op.mov 32 0 (.i 2147500037),
  Op.cmov32 5 12 0]

theorem b3 (prof : Profile) : Blk prof p3 0 12 o3 :=
  .cons (p3_0 _) (OpI.test16 (.r 0)) (by decide) <|
  .cons (p3_3 _) (OpI.mov (.i 2147500037) (.inl rfl)) (by decide) <|
  .cons (p3_8 _) (OpI.cmov32) (by decide) <|
  .nil 12

/-- The stretch at `91`. -/
def p4 : List Byte := [
  0x48, 0x89, 0xef]

theorem p4_0 : ∀ feat, Dec feat p4 0 (FV7z.mk .mov 64 [gr 64 7, Src.opd 64 (.r 5)] 3) := by dec_rfl

/-- What the stretch does. -/
def o4 : List Op := [
  Op.mov 64 7 (.r 5)]

theorem b4 (prof : Profile) : Blk prof p4 0 3 o4 :=
  .cons (p4_0 _) (OpI.mov (.r 5) (.inr rfl)) (by decide) <|
  .nil 3

/-- The stretch at `99`. -/
def p5 : List Byte := [
  0x48, 0x8b, 0x44, 0x24, 0x18, 0x64, 0x48, 0x33, 0x04, 0x25, 0x28, 0x00, 0x00, 0x00]

theorem p5_0 : ∀ feat, Dec feat p5 0 (FV7z.mk .mov 64 [gr 64 0, .mem (mg (some 4) none 1 24 64)] 5) := by dec_rfl
theorem p5_5 : ∀ feat, Dec feat p5 5 (FV7z.mk .xor 64 [gr 64 0, .mem (mf none none 1 40 64)] 9) := by dec_rfl

/-- What the stretch does. -/
def o5 (fb : Addr) : List Op := [
  Op.ld 64 0 (some 4) none 1 24,
  Op.xormf fb 64 0 none none 1 40]

theorem b5 (prof : Profile) (fb : Addr) : BlkF prof p5 (0x5d1643 : Addr) fb 0 14 (o5 fb) :=
  .cons (p5_0 _) (((OpI.ld (.inr rfl)).at _).fs _) (by decide) <|
  .cons (p5_5 _) (OpIF.xormf (.inr rfl)) (by decide) <|
  .nil 14

def j2 : List Byte := [0x75, 0x18]
theorem j2_0 : ∀ feat, Dec feat j2 0 (FV7z.mk (.jcc 5) 64 [.rel 24] 2) := by dec_rfl

/-- The stretch at `115`. -/
def p6 : List Byte := [
  0x48, 0x83, 0xc4, 0x20, 0x44, 0x89, 0xe0, 0x5b, 0x5d, 0x41, 0x5c]

theorem p6_0 : ∀ feat, Dec feat p6 0 (FV7z.mk .add 64 [gr 64 4, Src.opd 64 (.i 32)] 4) := by dec_rfl
theorem p6_4 : ∀ feat, Dec feat p6 4 (FV7z.mk .mov 32 [gr 32 0, Src.opd 32 (.r 12)] 3) := by dec_rfl
theorem p6_7 : ∀ feat, Dec feat p6 7 (FV7z.mk .pop 64 [gr 64 3] 1) := by dec_rfl
theorem p6_8 : ∀ feat, Dec feat p6 8 (FV7z.mk .pop 64 [gr 64 5] 1) := by dec_rfl
theorem p6_9 : ∀ feat, Dec feat p6 9 (FV7z.mk .pop 64 [gr 64 12] 2) := by dec_rfl

/-- What the stretch does. -/
def o6 : List Op := [
  Op.add 64 4 (.i 32),
  Op.mov 32 0 (.r 12),
  Op.pop 3,
  Op.pop 5,
  Op.pop 12]

theorem b6 (prof : Profile) : Blk prof p6 0 11 o6 :=
  .cons (p6_0 _) (OpI.add (.i 32) (.inr rfl)) (by decide) <|
  .cons (p6_4 _) (OpI.mov (.r 12) (.inl rfl)) (by decide) <|
  .cons (p6_7 _) (OpI.pop) (by decide) <|
  .cons (p6_8 _) (OpI.pop) (by decide) <|
  .cons (p6_9 _) (OpI.pop) (by decide) <|
  .nil 11

/-- The stretch at `128`. -/
def p7 : List Byte := [
  0x66, 0x83, 0x7c, 0x24, 0x08, 0x00]

theorem p7_0 : ∀ feat, Dec feat p7 0 (FV7z.mk .cmp 16 [.mem (mg (some 4) none 1 8 16), .imm 16 0] 6) := by dec_rfl

/-- What the stretch does. -/
def o7 : List Op := [
  Op.cmpmi 16 (some 4) none 1 8 0]

theorem b7 (prof : Profile) : Blk prof p7 0 6 o7 :=
  .cons (p7_0 _) (OpI.cmpmi16) (by decide) <|
  .nil 6

def j3 : List Byte := [0xeb, 0xd0]
theorem j3_0 : ∀ feat, Dec feat j3 0 (FV7z.mk .jmp 64 [.rel 18446744073709551568] 2) := by dec_rfl

end FV7z.Gbp
