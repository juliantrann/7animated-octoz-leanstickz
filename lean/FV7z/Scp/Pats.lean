import FV7z.Lemmas.SpFs
import FV7z.Lemmas.BlkOps20
import FV7z.Lemmas.BlkOps6
import FV7z.Lemmas.BlkOps2
/-!
# The stretches of straight-line code of `CExtractScanConsole::ScanProgress` (PLAN.md §M, M1)

Each distinct stretch between labels and jumps (`p*`, 8 of them) and each distinct jump (`j*`, 4) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.Scp
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The stretch at `0`. -/
def p0 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0x55, 0x53, 0x48, 0x83, 0xec, 0x28, 0x64, 0x48, 0x8b, 0x04, 0x25, 0x28,
  0x00, 0x00, 0x00, 0x48, 0x89, 0x44, 0x24, 0x18, 0x31, 0xc0, 0x48, 0x83, 0x7f, 0x50, 0x00]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem p0_4 : ∀ feat, Dec feat p0 4 (FV7z.mk .push 64 [gr 64 5] 1) := by dec_rfl
theorem p0_5 : ∀ feat, Dec feat p0 5 (FV7z.mk .push 64 [gr 64 3] 1) := by dec_rfl
theorem p0_6 : ∀ feat, Dec feat p0 6 (FV7z.mk .sub 64 [gr 64 4, Src.opd 64 (.i 40)] 4) := by dec_rfl
theorem p0_10 : ∀ feat, Dec feat p0 10 (FV7z.mk .mov 64 [gr 64 0, .mem (mf none none 1 40 64)] 9) := by dec_rfl
theorem p0_19 : ∀ feat, Dec feat p0 19 (FV7z.mk .mov 64 [.mem (mg (some 4) none 1 24 64), gr 64 0] 5) := by dec_rfl
theorem p0_24 : ∀ feat, Dec feat p0 24 (FV7z.mk .xor 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl
theorem p0_26 : ∀ feat, Dec feat p0 26 (FV7z.mk .cmp 64 [.mem (mg (some 7) none 1 80 64), .imm 64 0] 5) := by dec_rfl

/-- What the stretch does. -/
def o0 (fb : Addr) : List Op := [
  Op.nop,
  Op.push 5,
  Op.push 3,
  Op.sub 64 4 (.i 40),
  Op.ldf fb 64 0 none none 1 40,
  Op.st 64 (some 4) none 1 24 0,
  Op.xor 32 0 (.r 0),
  Op.cmpmi 64 (some 7) none 1 80 0]

theorem b0 (prof : Profile) (fb : Addr) : BlkF prof p0 (0x5e7810 : Addr) fb 0 31 (o0 fb) :=
  .cons (p0_0 _) (((OpI.endbr).at _).fs _) (by decide) <|
  .cons (p0_4 _) (((OpI.push).at _).fs _) (by decide) <|
  .cons (p0_5 _) (((OpI.push).at _).fs _) (by decide) <|
  .cons (p0_6 _) (((OpI.sub (.i 40) (.inr rfl)).at _).fs _) (by decide) <|
  .cons (p0_10 _) (OpIF.ldf (.inr rfl)) (by decide) <|
  .cons (p0_19 _) (((OpI.st (.inr (.inr (.inr rfl)))).at _).fs _) (by decide) <|
  .cons (p0_24 _) (((OpI.xor (.r 0) (.inl rfl)).at _).fs _) (by decide) <|
  .cons (p0_26 _) (((OpI.cmpmi64).at _).fs _) (by decide) <|
  .nil 31

def j0 : List Byte := [0x74, 0x51]
theorem j0_0 : ∀ feat, Dec feat j0 0 (FV7z.mk (.jcc 4) 64 [.rel 81] 2) := by dec_rfl

/-- The stretch at `33`. -/
def p1 : List Byte := [
  0x80, 0x7f, 0x58, 0x00, 0x48, 0x89, 0xfb]

theorem p1_0 : ∀ feat, Dec feat p1 0 (FV7z.mk .cmp 8 [.mem (mg (some 7) none 1 88 8), .imm 8 0] 4) := by dec_rfl
theorem p1_4 : ∀ feat, Dec feat p1 4 (FV7z.mk .mov 64 [gr 64 3, Src.opd 64 (.r 7)] 3) := by dec_rfl

/-- What the stretch does. -/
def o1 : List Op := [
  Op.cmpmi 8 (some 7) none 1 88 0,
  Op.mov 64 3 (.r 7)]

theorem b1 (prof : Profile) : Blk prof p1 0 7 o1 :=
  .cons (p1_0 _) (OpI.cmpmi (.inl rfl)) (by decide) <|
  .cons (p1_4 _) (OpI.mov (.r 7) (.inr rfl)) (by decide) <|
  .nil 7

def j1 : List Byte := [0x75, 0x48]
theorem j1_0 : ∀ feat, Dec feat j1 0 (FV7z.mk (.jcc 5) 64 [.rel 72] 2) := by dec_rfl

/-- The stretch at `42`. -/
def p2 : List Byte := [
  0x48, 0x8b, 0x46, 0x08, 0x48, 0x03, 0x06, 0x48, 0x89, 0xe5, 0x48, 0x89, 0x47, 0x28, 0x48, 0x8b,
  0x46, 0x20, 0x48, 0x03, 0x46, 0x18, 0x48, 0x89, 0xd6, 0x48, 0x89, 0x47, 0x18, 0x48, 0x89, 0xef]

theorem p2_0 : ∀ feat, Dec feat p2 0 (FV7z.mk .mov 64 [gr 64 0, .mem (mg (some 6) none 1 8 64)] 4) := by dec_rfl
theorem p2_4 : ∀ feat, Dec feat p2 4 (FV7z.mk .add 64 [gr 64 0, .mem (mg (some 6) none 1 0 64)] 3) := by dec_rfl
theorem p2_7 : ∀ feat, Dec feat p2 7 (FV7z.mk .mov 64 [gr 64 5, Src.opd 64 (.r 4)] 3) := by dec_rfl
theorem p2_10 : ∀ feat, Dec feat p2 10 (FV7z.mk .mov 64 [.mem (mg (some 7) none 1 40 64), gr 64 0] 4) := by dec_rfl
theorem p2_14 : ∀ feat, Dec feat p2 14 (FV7z.mk .mov 64 [gr 64 0, .mem (mg (some 6) none 1 32 64)] 4) := by dec_rfl
theorem p2_18 : ∀ feat, Dec feat p2 18 (FV7z.mk .add 64 [gr 64 0, .mem (mg (some 6) none 1 24 64)] 4) := by dec_rfl
theorem p2_22 : ∀ feat, Dec feat p2 22 (FV7z.mk .mov 64 [gr 64 6, Src.opd 64 (.r 2)] 3) := by dec_rfl
theorem p2_25 : ∀ feat, Dec feat p2 25 (FV7z.mk .mov 64 [.mem (mg (some 7) none 1 24 64), gr 64 0] 4) := by dec_rfl
theorem p2_29 : ∀ feat, Dec feat p2 29 (FV7z.mk .mov 64 [gr 64 7, Src.opd 64 (.r 5)] 3) := by dec_rfl

/-- What the stretch does. -/
def o2 : List Op := [
  Op.ld 64 0 (some 6) none 1 8,
  Op.addm 64 0 (some 6) none 1 0,
  Op.mov 64 5 (.r 4),
  Op.st 64 (some 7) none 1 40 0,
  Op.ld 64 0 (some 6) none 1 32,
  Op.addm 64 0 (some 6) none 1 24,
  Op.mov 64 6 (.r 2),
  Op.st 64 (some 7) none 1 24 0,
  Op.mov 64 7 (.r 5)]

theorem b2 (prof : Profile) : Blk prof p2 0 32 o2 :=
  .cons (p2_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p2_4 _) (OpI.addm (.inr rfl)) (by decide) <|
  .cons (p2_7 _) (OpI.mov (.r 4) (.inr rfl)) (by decide) <|
  .cons (p2_10 _) (OpI.st (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p2_14 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p2_18 _) (OpI.addm (.inr rfl)) (by decide) <|
  .cons (p2_22 _) (OpI.mov (.r 2) (.inr rfl)) (by decide) <|
  .cons (p2_25 _) (OpI.st (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p2_29 _) (OpI.mov (.r 5) (.inr rfl)) (by decide) <|
  .nil 32

/-- The stretch at `79`. -/
def p3 : List Byte := [
  0x48, 0x8d, 0x7b, 0x40, 0x48, 0x89, 0xee]

theorem p3_0 : ∀ feat, Dec feat p3 0 (FV7z.mk .lea 64 [gr 64 7, .mem (mg (some 3) none 1 64 0)] 4) := by dec_rfl
theorem p3_4 : ∀ feat, Dec feat p3 4 (FV7z.mk .mov 64 [gr 64 6, Src.opd 64 (.r 5)] 3) := by dec_rfl

/-- What the stretch does. -/
def o3 : List Op := [
  Op.lea 64 7 (some 3) none 1 64,
  Op.mov 64 6 (.r 5)]

theorem b3 (prof : Profile) : Blk prof p3 0 7 o3 :=
  .cons (p3_0 _) (OpI.lea (.inr rfl)) (by decide) <|
  .cons (p3_4 _) (OpI.mov (.r 5) (.inr rfl)) (by decide) <|
  .nil 7

/-- The stretch at `91`. -/
def p4 : List Byte := [
  0x48, 0x8b, 0x3c, 0x24, 0x48, 0x85, 0xff]

theorem p4_0 : ∀ feat, Dec feat p4 0 (FV7z.mk .mov 64 [gr 64 7, .mem (mg (some 4) none 1 0 64)] 4) := by dec_rfl
theorem p4_4 : ∀ feat, Dec feat p4 4 (FV7z.mk .test 64 [gr 64 7, Src.opd 64 (.r 7)] 3) := by dec_rfl

/-- What the stretch does. -/
def o4 : List Op := [
  Op.ld 64 7 (some 4) none 1 0,
  Op.test 64 7 (.r 7)]

theorem b4 (prof : Profile) : Blk prof p4 0 7 o4 :=
  .cons (p4_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p4_4 _) (OpI.test (.r 7) (.inr rfl)) (by decide) <|
  .nil 7

def j2 : List Byte := [0x74, 0x05]
theorem j2_0 : ∀ feat, Dec feat j2 0 (FV7z.mk (.jcc 4) 64 [.rel 5] 2) := by dec_rfl

/-- The stretch at `105`. -/
def p5 : List Byte := [
  0x48, 0x8d, 0x7b, 0x18]

theorem p5_0 : ∀ feat, Dec feat p5 0 (FV7z.mk .lea 64 [gr 64 7, .mem (mg (some 3) none 1 24 0)] 4) := by dec_rfl

/-- What the stretch does. -/
def o5 : List Op := [
  Op.lea 64 7 (some 3) none 1 24]

theorem b5 (prof : Profile) : Blk prof p5 0 4 o5 :=
  .cons (p5_0 _) (OpI.lea (.inr rfl)) (by decide) <|
  .nil 4

/-- The stretch at `114`. -/
def p6 : List Byte := [
  0x48, 0xc7, 0xc0, 0x88, 0xf0, 0x79, 0x00, 0x83, 0x38, 0x01, 0x19, 0xc0, 0xf7, 0xd0, 0x25, 0x04,
  0x40, 0x00, 0x80, 0x48, 0x8b, 0x4c, 0x24, 0x18, 0x64, 0x48, 0x33, 0x0c, 0x25, 0x28, 0x00, 0x00,
  0x00]

theorem p6_0 : ∀ feat, Dec feat p6 0 (FV7z.mk .mov 64 [gr 64 0, Src.opd 64 (.i 7991432)] 7) := by dec_rfl
theorem p6_7 : ∀ feat, Dec feat p6 7 (FV7z.mk .cmp 32 [.mem (mg (some 0) none 1 0 32), .imm 32 1] 3) := by dec_rfl
theorem p6_10 : ∀ feat, Dec feat p6 10 (FV7z.mk .sbb 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl
theorem p6_12 : ∀ feat, Dec feat p6 12 (FV7z.mk .not 32 [gr 32 0] 2) := by dec_rfl
theorem p6_14 : ∀ feat, Dec feat p6 14 (FV7z.mk .and 32 [gr 32 0, Src.opd 32 (.i 2147500036)] 5) := by dec_rfl
theorem p6_19 : ∀ feat, Dec feat p6 19 (FV7z.mk .mov 64 [gr 64 1, .mem (mg (some 4) none 1 24 64)] 5) := by dec_rfl
theorem p6_24 : ∀ feat, Dec feat p6 24 (FV7z.mk .xor 64 [gr 64 1, .mem (mf none none 1 40 64)] 9) := by dec_rfl

/-- What the stretch does. -/
def o6 (fb : Addr) : List Op := [
  Op.mov 64 0 (.i 7991432),
  Op.cmpmi 32 (some 0) none 1 0 1,
  Op.sbb 32 0 (.r 0),
  Op.not32 0,
  Op.and 32 0 (.i 2147500036),
  Op.ld 64 1 (some 4) none 1 24,
  Op.xormf fb 64 1 none none 1 40]

theorem b6 (prof : Profile) (fb : Addr) : BlkF prof p6 (0x5e7882 : Addr) fb 0 33 (o6 fb) :=
  .cons (p6_0 _) (((OpI.mov (.i 7991432) (.inr rfl)).at _).fs _) (by decide) <|
  .cons (p6_7 _) (((OpI.cmpmi (.inr rfl)).at _).fs _) (by decide) <|
  .cons (p6_10 _) (((OpI.sbb (.r 0) (.inl rfl)).at _).fs _) (by decide) <|
  .cons (p6_12 _) (((OpI.not32).at _).fs _) (by decide) <|
  .cons (p6_14 _) (((OpI.and (.i 2147500036) (.inl rfl)).at _).fs _) (by decide) <|
  .cons (p6_19 _) (((OpI.ld (.inr rfl)).at _).fs _) (by decide) <|
  .cons (p6_24 _) (OpIF.xormf (.inr rfl)) (by decide) <|
  .nil 33

def j3 : List Byte := [0x75, 0x07]
theorem j3_0 : ∀ feat, Dec feat j3 0 (FV7z.mk (.jcc 5) 64 [.rel 7] 2) := by dec_rfl

/-- The stretch at `149`. -/
def p7 : List Byte := [
  0x48, 0x83, 0xc4, 0x28, 0x5b, 0x5d]

theorem p7_0 : ∀ feat, Dec feat p7 0 (FV7z.mk .add 64 [gr 64 4, Src.opd 64 (.i 40)] 4) := by dec_rfl
theorem p7_4 : ∀ feat, Dec feat p7 4 (FV7z.mk .pop 64 [gr 64 3] 1) := by dec_rfl
theorem p7_5 : ∀ feat, Dec feat p7 5 (FV7z.mk .pop 64 [gr 64 5] 1) := by dec_rfl

/-- What the stretch does. -/
def o7 : List Op := [
  Op.add 64 4 (.i 40),
  Op.pop 3,
  Op.pop 5]

theorem b7 (prof : Profile) : Blk prof p7 0 6 o7 :=
  .cons (p7_0 _) (OpI.add (.i 40) (.inr rfl)) (by decide) <|
  .cons (p7_4 _) (OpI.pop) (by decide) <|
  .cons (p7_5 _) (OpI.pop) (by decide) <|
  .nil 6

end FV7z.Scp
