import FV7z.Lemmas.Sp
import FV7z.Lemmas.BlkOps2
/-!
# The stretches of straight-line code of `__brk` (PLAN.md G3, startup)

Each distinct stretch between labels and jumps (`p*`, 4 of them) and each distinct jump (`j*`, 2) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.Brk
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The stretch at `0`. -/
def p0 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0xb8, 0x0c, 0x00, 0x00, 0x00]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem p0_4 : ∀ feat, Dec feat p0 4 (FV7z.mk .mov 32 [gr 32 0, Src.opd 32 (.i 12)] 5) := by dec_rfl

/-- What the stretch does. -/
def o0 : List Op := [
  Op.nop,
  Op.mov 32 0 (.i 12)]

theorem b0 (prof : Profile) : Blk prof p0 0 9 o0 :=
  .cons (p0_0 _) (OpI.endbr) (by decide) <|
  .cons (p0_4 _) (OpI.mov (.i 12) (.inl rfl)) (by decide) <|
  .nil 9

/-- The stretch at `11`. -/
def p1 : List Byte := [
  0x48, 0x3d, 0x00, 0xf0, 0xff, 0xff]

theorem p1_0 : ∀ feat, Dec feat p1 0 (FV7z.mk .cmp 64 [gr 64 0, Src.opd 64 (.i 18446744073709547520)] 6) := by dec_rfl

/-- What the stretch does. -/
def o1 : List Op := [
  Op.cmp 64 0 (.i 18446744073709547520)]

theorem b1 (prof : Profile) : Blk prof p1 0 6 o1 :=
  .cons (p1_0 _) (OpI.cmp (.i 18446744073709547520) (.inr rfl)) (by decide) <|
  .nil 6

def j0 : List Byte := [0x77, 0x15]
theorem j0_0 : ∀ feat, Dec feat j0 0 (FV7z.mk (.jcc 7) 64 [.rel 21] 2) := by dec_rfl

/-- The stretch at `19`. -/
def p2 : List Byte := [
  0x48, 0x89, 0x05, 0x1e, 0x22, 0x10, 0x00, 0x48, 0x39, 0xc7]

theorem p2_0 : ∀ feat, Dec feat p2 0 (FV7z.mk .mov 64 [.mem (mrip 1057310 64), gr 64 0] 7) := by dec_rfl
theorem p2_7 : ∀ feat, Dec feat p2 7 (FV7z.mk .cmp 64 [gr 64 7, Src.opd 64 (.r 0)] 3) := by dec_rfl

/-- What the stretch does. -/
def o2 : List Op := [
  Op.sta 64 8014904 0,
  Op.cmp 64 7 (.r 0)]

theorem b2 (prof : Profile) : BlkA prof p2 (0x6a2a13 : Addr) 0 10 o2 :=
  .cons (p2_0 _) (OpIA.st_rip (.inr (.inr rfl)) (by decide)) (by decide) <|
  .cons (p2_7 _) ((OpI.cmp (.r 0) (.inr rfl)).at _) (by decide) <|
  .nil 10

def j1 : List Byte := [0x77, 0x29]
theorem j1_0 : ∀ feat, Dec feat j1 0 (FV7z.mk (.jcc 7) 64 [.rel 41] 2) := by dec_rfl

/-- The stretch at `31`. -/
def p3 : List Byte := [
  0x31, 0xc0]

theorem p3_0 : ∀ feat, Dec feat p3 0 (FV7z.mk .xor 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl

/-- What the stretch does. -/
def o3 : List Op := [
  Op.xor 32 0 (.r 0)]

theorem b3 (prof : Profile) : Blk prof p3 0 2 o3 :=
  .cons (p3_0 _) (OpI.xor (.r 0) (.inl rfl)) (by decide) <|
  .nil 2

end FV7z.Brk
