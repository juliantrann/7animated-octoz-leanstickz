import FV7z.Lemmas.Sp
import FV7z.Lemmas.BlkOps2
/-!
# The stretches of straight-line code of `LzFindPrepare` (PLAN.md §M, M1)

Each distinct stretch between labels and jumps (`p*`, 4 of them) and each distinct jump (`j*`, 1) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.Lzp
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The stretch at `0`. -/
def p0 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0x48, 0x83, 0xec, 0x08]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem p0_4 : ∀ feat, Dec feat p0 4 (FV7z.mk .sub 64 [gr 64 4, Src.opd 64 (.i 8)] 4) := by dec_rfl

/-- What the stretch does. -/
def o0 : List Op := [
  Op.nop,
  Op.sub 64 4 (.i 8)]

theorem b0 (prof : Profile) : Blk prof p0 0 8 o0 :=
  .cons (p0_0 _) (OpI.endbr) (by decide) <|
  .cons (p0_4 _) (OpI.sub (.i 8) (.inr rfl)) (by decide) <|
  .nil 8

/-- The stretch at `13`. -/
def p1 : List Byte := [
  0x41, 0x89, 0xc0, 0x31, 0xc0, 0x45, 0x85, 0xc0]

theorem p1_0 : ∀ feat, Dec feat p1 0 (FV7z.mk .mov 32 [gr 32 8, Src.opd 32 (.r 0)] 3) := by dec_rfl
theorem p1_3 : ∀ feat, Dec feat p1 3 (FV7z.mk .xor 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl
theorem p1_5 : ∀ feat, Dec feat p1 5 (FV7z.mk .test 32 [gr 32 8, Src.opd 32 (.r 8)] 3) := by dec_rfl

/-- What the stretch does. -/
def o1 : List Op := [
  Op.mov 32 8 (.r 0),
  Op.xor 32 0 (.r 0),
  Op.test 32 8 (.r 8)]

theorem b1 (prof : Profile) : Blk prof p1 0 8 o1 :=
  .cons (p1_0 _) (OpI.mov (.r 0) (.inl rfl)) (by decide) <|
  .cons (p1_3 _) (OpI.xor (.r 0) (.inl rfl)) (by decide) <|
  .cons (p1_5 _) (OpI.test (.r 8) (.inl rfl)) (by decide) <|
  .nil 8

def j0 : List Byte := [0x75, 0x11]
theorem j0_0 : ∀ feat, Dec feat j0 0 (FV7z.mk (.jcc 5) 64 [.rel 17] 2) := by dec_rfl

/-- The stretch at `23`. -/
def p2 : List Byte := [
  0x48, 0x89, 0x05, 0xa2, 0xe9, 0x36, 0x00, 0x48, 0x83, 0xc4, 0x08]

theorem p2_0 : ∀ feat, Dec feat p2 0 (FV7z.mk .mov 64 [.mem (mrip 3598754 64), gr 64 0] 7) := by dec_rfl
theorem p2_7 : ∀ feat, Dec feat p2 7 (FV7z.mk .add 64 [gr 64 4, Src.opd 64 (.i 8)] 4) := by dec_rfl

/-- What the stretch does. -/
def o2 : List Op := [
  Op.sta 64 7956384 0,
  Op.add 64 4 (.i 8)]

theorem b2 (prof : Profile) : BlkA prof p2 (0x427df7 : Addr) 0 11 o2 :=
  .cons (p2_0 _) (OpIA.st_rip (.inr (.inr rfl)) (by decide)) (by decide) <|
  .cons (p2_7 _) ((OpI.add (.i 8) (.inr rfl)).at _) (by decide) <|
  .nil 11

/-- The stretch at `45`. -/
def p3 : List Byte := [
  0x48, 0x8d, 0x15, 0x3c, 0xd3, 0xff, 0xff, 0x85, 0xc0, 0x48, 0x8d, 0x05, 0x93, 0xd3, 0xff, 0xff,
  0x48, 0x0f, 0x45, 0xc2, 0x48, 0x89, 0x05, 0x78, 0xe9, 0x36, 0x00, 0x48, 0x83, 0xc4, 0x08]

theorem p3_0 : ∀ feat, Dec feat p3 0 (FV7z.mk .lea 64 [gr 64 2, .mem (mrip 18446744073709540156 0)] 7) := by dec_rfl
theorem p3_7 : ∀ feat, Dec feat p3 7 (FV7z.mk .test 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl
theorem p3_9 : ∀ feat, Dec feat p3 9 (FV7z.mk .lea 64 [gr 64 0, .mem (mrip 18446744073709540243 0)] 7) := by dec_rfl
theorem p3_16 : ∀ feat, Dec feat p3 16 (FV7z.mk (.cmovcc 5) 64 [gr 64 0, gr 64 2] 4) := by dec_rfl
theorem p3_20 : ∀ feat, Dec feat p3 20 (FV7z.mk .mov 64 [.mem (mrip 3598712 64), gr 64 0] 7) := by dec_rfl
theorem p3_27 : ∀ feat, Dec feat p3 27 (FV7z.mk .add 64 [gr 64 4, Src.opd 64 (.i 8)] 4) := by dec_rfl

/-- What the stretch does. -/
def o3 : List Op := [
  Op.mov 64 2 (.i 4346192),
  Op.test 32 0 (.r 0),
  Op.mov 64 0 (.i 4346288),
  Op.cmov64 5 0 2,
  Op.sta 64 7956384 0,
  Op.add 64 4 (.i 8)]

theorem b3 (prof : Profile) : BlkA prof p3 (0x427e0d : Addr) 0 31 o3 :=
  .cons (p3_0 _) (OpIA.lea_rip (by decide)) (by decide) <|
  .cons (p3_7 _) ((OpI.test (.r 0) (.inl rfl)).at _) (by decide) <|
  .cons (p3_9 _) (OpIA.lea_rip (by decide)) (by decide) <|
  .cons (p3_16 _) ((OpI.cmov64).at _) (by decide) <|
  .cons (p3_20 _) (OpIA.st_rip (.inr (.inr rfl)) (by decide)) (by decide) <|
  .cons (p3_27 _) ((OpI.add (.i 8) (.inr rfl)).at _) (by decide) <|
  .nil 31

end FV7z.Lzp
