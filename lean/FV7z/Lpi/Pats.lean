import FV7z.Lemmas.Sp
import FV7z.Lemmas.BlkOps2
/-!
# The stretches of straight-line code of `__libc_pthread_init` (PLAN.md G3, startup)

Each distinct stretch between labels and jumps (`p*`, 2 of them) and each distinct jump (`j*`, 0) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.Lpi
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The stretch at `0`. -/
def p0 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0x48, 0x83, 0xec, 0x08, 0x48, 0x89, 0xf2, 0x48, 0x89, 0x3d, 0xce, 0xa9,
  0x17, 0x00, 0x31, 0xc9, 0x31, 0xf6, 0x31, 0xff]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem p0_4 : ∀ feat, Dec feat p0 4 (FV7z.mk .sub 64 [gr 64 4, Src.opd 64 (.i 8)] 4) := by dec_rfl
theorem p0_8 : ∀ feat, Dec feat p0 8 (FV7z.mk .mov 64 [gr 64 2, Src.opd 64 (.r 6)] 3) := by dec_rfl
theorem p0_11 : ∀ feat, Dec feat p0 11 (FV7z.mk .mov 64 [.mem (mrip 1550798 64), gr 64 7] 7) := by dec_rfl
theorem p0_18 : ∀ feat, Dec feat p0 18 (FV7z.mk .xor 32 [gr 32 1, Src.opd 32 (.r 1)] 2) := by dec_rfl
theorem p0_20 : ∀ feat, Dec feat p0 20 (FV7z.mk .xor 32 [gr 32 6, Src.opd 32 (.r 6)] 2) := by dec_rfl
theorem p0_22 : ∀ feat, Dec feat p0 22 (FV7z.mk .xor 32 [gr 32 7, Src.opd 32 (.r 7)] 2) := by dec_rfl

/-- What the stretch does. -/
def o0 : List Op := [
  Op.nop,
  Op.sub 64 4 (.i 8),
  Op.mov 64 2 (.r 6),
  Op.sta 64 8029200 7,
  Op.xor 32 1 (.r 1),
  Op.xor 32 6 (.r 6),
  Op.xor 32 7 (.r 7)]

theorem b0 (prof : Profile) : BlkA prof p0 (0x62da30 : Addr) 0 24 o0 :=
  .cons (p0_0 _) ((OpI.endbr).at _) (by decide) <|
  .cons (p0_4 _) ((OpI.sub (.i 8) (.inr rfl)).at _) (by decide) <|
  .cons (p0_8 _) ((OpI.mov (.r 6) (.inr rfl)).at _) (by decide) <|
  .cons (p0_11 _) (OpIA.st_rip (.inr (.inr rfl)) (by decide)) (by decide) <|
  .cons (p0_18 _) ((OpI.xor (.r 1) (.inl rfl)).at _) (by decide) <|
  .cons (p0_20 _) ((OpI.xor (.r 6) (.inl rfl)).at _) (by decide) <|
  .cons (p0_22 _) ((OpI.xor (.r 7) (.inl rfl)).at _) (by decide) <|
  .nil 24

/-- The stretch at `29`. -/
def p1 : List Byte := [
  0x48, 0x8d, 0x05, 0xc4, 0xa9, 0x17, 0x00, 0x48, 0x83, 0xc4, 0x08]

theorem p1_0 : ∀ feat, Dec feat p1 0 (FV7z.mk .lea 64 [gr 64 0, .mem (mrip 1550788 0)] 7) := by dec_rfl
theorem p1_7 : ∀ feat, Dec feat p1 7 (FV7z.mk .add 64 [gr 64 4, Src.opd 64 (.i 8)] 4) := by dec_rfl

/-- What the stretch does. -/
def o1 : List Op := [
  Op.mov 64 0 (.i 8029208),
  Op.add 64 4 (.i 8)]

theorem b1 (prof : Profile) : BlkA prof p1 (0x62da4d : Addr) 0 11 o1 :=
  .cons (p1_0 _) (OpIA.lea_rip (by decide)) (by decide) <|
  .cons (p1_7 _) ((OpI.add (.i 8) (.inr rfl)).at _) (by decide) <|
  .nil 11

end FV7z.Lpi
