import FV7z.Lemmas.SpFs
import FV7z.Lemmas.BlkOps2
/-!
# The stretches of straight-line code of `__ctype_init` (PLAN.md G3, startup)

Each distinct stretch between labels and jumps (`p*`, 1 of them) and each distinct jump (`j*`, 0) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.Cti
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The stretch at `0`. -/
def p0 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0x48, 0xc7, 0xc0, 0x90, 0xff, 0xff, 0xff, 0x48, 0xc7, 0xc1, 0xd0, 0xff,
  0xff, 0xff, 0x64, 0x48, 0x8b, 0x00, 0x48, 0x8b, 0x00, 0x48, 0x8b, 0x70, 0x40, 0x48, 0x8d, 0x96,
  0x00, 0x01, 0x00, 0x00, 0x64, 0x48, 0x89, 0x11, 0x48, 0x8b, 0x78, 0x48, 0x48, 0xc7, 0xc1, 0xc8,
  0xff, 0xff, 0xff, 0x48, 0x8d, 0x97, 0x00, 0x02, 0x00, 0x00, 0x64, 0x48, 0x89, 0x11, 0x48, 0x8b,
  0x40, 0x58, 0x48, 0xc7, 0xc2, 0xc0, 0xff, 0xff, 0xff, 0x48, 0x05, 0x00, 0x02, 0x00, 0x00, 0x64,
  0x48, 0x89, 0x02]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem p0_4 : ∀ feat, Dec feat p0 4 (FV7z.mk .mov 64 [gr 64 0, Src.opd 64 (.i 18446744073709551504)] 7) := by dec_rfl
theorem p0_11 : ∀ feat, Dec feat p0 11 (FV7z.mk .mov 64 [gr 64 1, Src.opd 64 (.i 18446744073709551568)] 7) := by dec_rfl
theorem p0_18 : ∀ feat, Dec feat p0 18 (FV7z.mk .mov 64 [gr 64 0, .mem (mf (some 0) none 1 0 64)] 4) := by dec_rfl
theorem p0_22 : ∀ feat, Dec feat p0 22 (FV7z.mk .mov 64 [gr 64 0, .mem (mg (some 0) none 1 0 64)] 3) := by dec_rfl
theorem p0_25 : ∀ feat, Dec feat p0 25 (FV7z.mk .mov 64 [gr 64 6, .mem (mg (some 0) none 1 64 64)] 4) := by dec_rfl
theorem p0_29 : ∀ feat, Dec feat p0 29 (FV7z.mk .lea 64 [gr 64 2, .mem (mg (some 6) none 1 256 0)] 7) := by dec_rfl
theorem p0_36 : ∀ feat, Dec feat p0 36 (FV7z.mk .mov 64 [.mem (mf (some 1) none 1 0 64), gr 64 2] 4) := by dec_rfl
theorem p0_40 : ∀ feat, Dec feat p0 40 (FV7z.mk .mov 64 [gr 64 7, .mem (mg (some 0) none 1 72 64)] 4) := by dec_rfl
theorem p0_44 : ∀ feat, Dec feat p0 44 (FV7z.mk .mov 64 [gr 64 1, Src.opd 64 (.i 18446744073709551560)] 7) := by dec_rfl
theorem p0_51 : ∀ feat, Dec feat p0 51 (FV7z.mk .lea 64 [gr 64 2, .mem (mg (some 7) none 1 512 0)] 7) := by dec_rfl
theorem p0_58 : ∀ feat, Dec feat p0 58 (FV7z.mk .mov 64 [.mem (mf (some 1) none 1 0 64), gr 64 2] 4) := by dec_rfl
theorem p0_62 : ∀ feat, Dec feat p0 62 (FV7z.mk .mov 64 [gr 64 0, .mem (mg (some 0) none 1 88 64)] 4) := by dec_rfl
theorem p0_66 : ∀ feat, Dec feat p0 66 (FV7z.mk .mov 64 [gr 64 2, Src.opd 64 (.i 18446744073709551552)] 7) := by dec_rfl
theorem p0_73 : ∀ feat, Dec feat p0 73 (FV7z.mk .add 64 [gr 64 0, Src.opd 64 (.i 512)] 6) := by dec_rfl
theorem p0_79 : ∀ feat, Dec feat p0 79 (FV7z.mk .mov 64 [.mem (mf (some 2) none 1 0 64), gr 64 0] 4) := by dec_rfl

/-- What the stretch does. -/
def o0 (fb : Addr) : List Op := [
  Op.nop,
  Op.mov 64 0 (.i 18446744073709551504),
  Op.mov 64 1 (.i 18446744073709551568),
  Op.ldf fb 64 0 (some 0) none 1 0,
  Op.ld 64 0 (some 0) none 1 0,
  Op.ld 64 6 (some 0) none 1 64,
  Op.lea 64 2 (some 6) none 1 256,
  Op.stf fb 64 (some 1) none 1 0 2,
  Op.ld 64 7 (some 0) none 1 72,
  Op.mov 64 1 (.i 18446744073709551560),
  Op.lea 64 2 (some 7) none 1 512,
  Op.stf fb 64 (some 1) none 1 0 2,
  Op.ld 64 0 (some 0) none 1 88,
  Op.mov 64 2 (.i 18446744073709551552),
  Op.add 64 0 (.i 512),
  Op.stf fb 64 (some 2) none 1 0 0]

theorem b0 (prof : Profile) (fb : Addr) : BlkF prof p0 (0x6160e0 : Addr) fb 0 83 (o0 fb) :=
  .cons (p0_0 _) (((OpI.endbr).at _).fs _) (by decide) <|
  .cons (p0_4 _) (((OpI.mov (.i 18446744073709551504) (.inr rfl)).at _).fs _) (by decide) <|
  .cons (p0_11 _) (((OpI.mov (.i 18446744073709551568) (.inr rfl)).at _).fs _) (by decide) <|
  .cons (p0_18 _) (OpIF.ldf (.inr rfl)) (by decide) <|
  .cons (p0_22 _) (((OpI.ld (.inr rfl)).at _).fs _) (by decide) <|
  .cons (p0_25 _) (((OpI.ld (.inr rfl)).at _).fs _) (by decide) <|
  .cons (p0_29 _) (((OpI.lea (.inr rfl)).at _).fs _) (by decide) <|
  .cons (p0_36 _) (OpIF.stf (.inr rfl)) (by decide) <|
  .cons (p0_40 _) (((OpI.ld (.inr rfl)).at _).fs _) (by decide) <|
  .cons (p0_44 _) (((OpI.mov (.i 18446744073709551560) (.inr rfl)).at _).fs _) (by decide) <|
  .cons (p0_51 _) (((OpI.lea (.inr rfl)).at _).fs _) (by decide) <|
  .cons (p0_58 _) (OpIF.stf (.inr rfl)) (by decide) <|
  .cons (p0_62 _) (((OpI.ld (.inr rfl)).at _).fs _) (by decide) <|
  .cons (p0_66 _) (((OpI.mov (.i 18446744073709551552) (.inr rfl)).at _).fs _) (by decide) <|
  .cons (p0_73 _) (((OpI.add (.i 512) (.inr rfl)).at _).fs _) (by decide) <|
  .cons (p0_79 _) (OpIF.stf (.inr rfl)) (by decide) <|
  .nil 83

end FV7z.Cti
