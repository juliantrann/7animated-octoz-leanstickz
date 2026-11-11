import FV7z.Lemmas.SpFs
import FV7z.Lemmas.BlkOps11
import FV7z.Lemmas.BlkOps6
import FV7z.Lemmas.BlkOps2
/-!
# The stretches of straight-line code of `__sigsetjmp` (PLAN.md G3, startup)

Each distinct stretch between labels and jumps (`p*`, 4 of them) and each distinct jump (`j*`, 2) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.Ssj
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The stretch at `0`. -/
def p0 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0x48, 0x89, 0x1f, 0x48, 0x89, 0xe8, 0x64, 0x48, 0x33, 0x04, 0x25, 0x30,
  0x00, 0x00, 0x00, 0x48, 0xc1, 0xc0, 0x11, 0x48, 0x89, 0x47, 0x08, 0x4c, 0x89, 0x67, 0x10, 0x4c,
  0x89, 0x6f, 0x18, 0x4c, 0x89, 0x77, 0x20, 0x4c, 0x89, 0x7f, 0x28, 0x48, 0x8d, 0x54, 0x24, 0x08,
  0x64, 0x48, 0x33, 0x14, 0x25, 0x30, 0x00, 0x00, 0x00, 0x48, 0xc1, 0xc2, 0x11, 0x48, 0x89, 0x57,
  0x30, 0x48, 0x8b, 0x04, 0x24, 0x90, 0x64, 0x48, 0x33, 0x04, 0x25, 0x30, 0x00, 0x00, 0x00, 0x48,
  0xc1, 0xc0, 0x11, 0x48, 0x89, 0x47, 0x38, 0x31, 0xc0]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem p0_4 : ∀ feat, Dec feat p0 4 (FV7z.mk .mov 64 [.mem (mg (some 7) none 1 0 64), gr 64 3] 3) := by dec_rfl
theorem p0_7 : ∀ feat, Dec feat p0 7 (FV7z.mk .mov 64 [gr 64 0, Src.opd 64 (.r 5)] 3) := by dec_rfl
theorem p0_10 : ∀ feat, Dec feat p0 10 (FV7z.mk .xor 64 [gr 64 0, .mem (mf none none 1 48 64)] 9) := by dec_rfl
theorem p0_19 : ∀ feat, Dec feat p0 19 (FV7z.mk .rol 64 [gr 64 0, Src.opd 8 (.i 17)] 4) := by dec_rfl
theorem p0_23 : ∀ feat, Dec feat p0 23 (FV7z.mk .mov 64 [.mem (mg (some 7) none 1 8 64), gr 64 0] 4) := by dec_rfl
theorem p0_27 : ∀ feat, Dec feat p0 27 (FV7z.mk .mov 64 [.mem (mg (some 7) none 1 16 64), gr 64 12] 4) := by dec_rfl
theorem p0_31 : ∀ feat, Dec feat p0 31 (FV7z.mk .mov 64 [.mem (mg (some 7) none 1 24 64), gr 64 13] 4) := by dec_rfl
theorem p0_35 : ∀ feat, Dec feat p0 35 (FV7z.mk .mov 64 [.mem (mg (some 7) none 1 32 64), gr 64 14] 4) := by dec_rfl
theorem p0_39 : ∀ feat, Dec feat p0 39 (FV7z.mk .mov 64 [.mem (mg (some 7) none 1 40 64), gr 64 15] 4) := by dec_rfl
theorem p0_43 : ∀ feat, Dec feat p0 43 (FV7z.mk .lea 64 [gr 64 2, .mem (mg (some 4) none 1 8 0)] 5) := by dec_rfl
theorem p0_48 : ∀ feat, Dec feat p0 48 (FV7z.mk .xor 64 [gr 64 2, .mem (mf none none 1 48 64)] 9) := by dec_rfl
theorem p0_57 : ∀ feat, Dec feat p0 57 (FV7z.mk .rol 64 [gr 64 2, Src.opd 8 (.i 17)] 4) := by dec_rfl
theorem p0_61 : ∀ feat, Dec feat p0 61 (FV7z.mk .mov 64 [.mem (mg (some 7) none 1 48 64), gr 64 2] 4) := by dec_rfl
theorem p0_65 : ∀ feat, Dec feat p0 65 (FV7z.mk .mov 64 [gr 64 0, .mem (mg (some 4) none 1 0 64)] 4) := by dec_rfl
theorem p0_69 : ∀ feat, Dec feat p0 69 (FV7z.mk .nop 32 [] 1) := by dec_rfl
theorem p0_70 : ∀ feat, Dec feat p0 70 (FV7z.mk .xor 64 [gr 64 0, .mem (mf none none 1 48 64)] 9) := by dec_rfl
theorem p0_79 : ∀ feat, Dec feat p0 79 (FV7z.mk .rol 64 [gr 64 0, Src.opd 8 (.i 17)] 4) := by dec_rfl
theorem p0_83 : ∀ feat, Dec feat p0 83 (FV7z.mk .mov 64 [.mem (mg (some 7) none 1 56 64), gr 64 0] 4) := by dec_rfl
theorem p0_87 : ∀ feat, Dec feat p0 87 (FV7z.mk .xor 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl

/-- What the stretch does. -/
def o0 (fb : Addr) : List Op := [
  Op.nop,
  Op.st 64 (some 7) none 1 0 3,
  Op.mov 64 0 (.r 5),
  Op.xormf fb 64 0 none none 1 48,
  Op.rol64 0 (.i 17),
  Op.st 64 (some 7) none 1 8 0,
  Op.st 64 (some 7) none 1 16 12,
  Op.st 64 (some 7) none 1 24 13,
  Op.st 64 (some 7) none 1 32 14,
  Op.st 64 (some 7) none 1 40 15,
  Op.lea 64 2 (some 4) none 1 8,
  Op.xormf fb 64 2 none none 1 48,
  Op.rol64 2 (.i 17),
  Op.st 64 (some 7) none 1 48 2,
  Op.ld 64 0 (some 4) none 1 0,
  Op.nop,
  Op.xormf fb 64 0 none none 1 48,
  Op.rol64 0 (.i 17),
  Op.st 64 (some 7) none 1 56 0,
  Op.xor 32 0 (.r 0)]

theorem b0 (prof : Profile) (fb : Addr) : BlkF prof p0 (0x67e040 : Addr) fb 0 89 (o0 fb) :=
  .cons (p0_0 _) (((OpI.endbr).at _).fs _) (by decide) <|
  .cons (p0_4 _) (((OpI.st (.inr (.inr (.inr rfl)))).at _).fs _) (by decide) <|
  .cons (p0_7 _) (((OpI.mov (.r 5) (.inr rfl)).at _).fs _) (by decide) <|
  .cons (p0_10 _) (OpIF.xormf (.inr rfl)) (by decide) <|
  .cons (p0_19 _) (((OpI.rol64 (.i 17)).at _).fs _) (by decide) <|
  .cons (p0_23 _) (((OpI.st (.inr (.inr (.inr rfl)))).at _).fs _) (by decide) <|
  .cons (p0_27 _) (((OpI.st (.inr (.inr (.inr rfl)))).at _).fs _) (by decide) <|
  .cons (p0_31 _) (((OpI.st (.inr (.inr (.inr rfl)))).at _).fs _) (by decide) <|
  .cons (p0_35 _) (((OpI.st (.inr (.inr (.inr rfl)))).at _).fs _) (by decide) <|
  .cons (p0_39 _) (((OpI.st (.inr (.inr (.inr rfl)))).at _).fs _) (by decide) <|
  .cons (p0_43 _) (((OpI.lea (.inr rfl)).at _).fs _) (by decide) <|
  .cons (p0_48 _) (OpIF.xormf (.inr rfl)) (by decide) <|
  .cons (p0_57 _) (((OpI.rol64 (.i 17)).at _).fs _) (by decide) <|
  .cons (p0_61 _) (((OpI.st (.inr (.inr (.inr rfl)))).at _).fs _) (by decide) <|
  .cons (p0_65 _) (((OpI.ld (.inr rfl)).at _).fs _) (by decide) <|
  .cons (p0_69 _) (((OpI.nop).at _).fs _) (by decide) <|
  .cons (p0_70 _) (OpIF.xormf (.inr rfl)) (by decide) <|
  .cons (p0_79 _) (((OpI.rol64 (.i 17)).at _).fs _) (by decide) <|
  .cons (p0_83 _) (((OpI.st (.inr (.inr (.inr rfl)))).at _).fs _) (by decide) <|
  .cons (p0_87 _) (((OpI.xor (.r 0) (.inl rfl)).at _).fs _) (by decide) <|
  .nil 89

/-- The stretch at `94`. -/
def p1 : List Byte := [
  0x48, 0x89, 0x47, 0x58]

theorem p1_0 : ∀ feat, Dec feat p1 0 (FV7z.mk .mov 64 [.mem (mg (some 7) none 1 88 64), gr 64 0] 4) := by dec_rfl

/-- What the stretch does. -/
def o1 : List Op := [
  Op.st 64 (some 7) none 1 88 0]

theorem b1 (prof : Profile) : Blk prof p1 0 4 o1 :=
  .cons (p1_0 _) (OpI.st (.inr (.inr (.inr rfl)))) (by decide) <|
  .nil 4

def j0 : List Byte := [0xe9, 0x09, 0x00, 0x00, 0x00]
theorem j0_0 : ∀ feat, Dec feat j0 0 (FV7z.mk .jmp 64 [.rel 9] 5) := by dec_rfl

/-- The stretch at `112`. -/
def p2 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0x53, 0x48, 0x89, 0xfb, 0x85, 0xf6]

theorem p2_0 : ∀ feat, Dec feat p2 0 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem p2_4 : ∀ feat, Dec feat p2 4 (FV7z.mk .push 64 [gr 64 3] 1) := by dec_rfl
theorem p2_5 : ∀ feat, Dec feat p2 5 (FV7z.mk .mov 64 [gr 64 3, Src.opd 64 (.r 7)] 3) := by dec_rfl
theorem p2_8 : ∀ feat, Dec feat p2 8 (FV7z.mk .test 32 [gr 32 6, Src.opd 32 (.r 6)] 2) := by dec_rfl

/-- What the stretch does. -/
def o2 : List Op := [
  Op.nop,
  Op.push 3,
  Op.mov 64 3 (.r 7),
  Op.test 32 6 (.r 6)]

theorem b2 (prof : Profile) : Blk prof p2 0 10 o2 :=
  .cons (p2_0 _) (OpI.endbr) (by decide) <|
  .cons (p2_4 _) (OpI.push) (by decide) <|
  .cons (p2_5 _) (OpI.mov (.r 7) (.inr rfl)) (by decide) <|
  .cons (p2_8 _) (OpI.test (.r 6) (.inl rfl)) (by decide) <|
  .nil 10

def j1 : List Byte := [0x75, 0x0c]
theorem j1_0 : ∀ feat, Dec feat j1 0 (FV7z.mk (.jcc 5) 64 [.rel 12] 2) := by dec_rfl

/-- The stretch at `124`. -/
def p3 : List Byte := [
  0x89, 0x73, 0x40, 0x31, 0xc0, 0x5b]

theorem p3_0 : ∀ feat, Dec feat p3 0 (FV7z.mk .mov 32 [.mem (mg (some 3) none 1 64 32), gr 32 6] 3) := by dec_rfl
theorem p3_3 : ∀ feat, Dec feat p3 3 (FV7z.mk .xor 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl
theorem p3_5 : ∀ feat, Dec feat p3 5 (FV7z.mk .pop 64 [gr 64 3] 1) := by dec_rfl

/-- What the stretch does. -/
def o3 : List Op := [
  Op.st 32 (some 3) none 1 64 6,
  Op.xor 32 0 (.r 0),
  Op.pop 3]

theorem b3 (prof : Profile) : Blk prof p3 0 6 o3 :=
  .cons (p3_0 _) (OpI.st (.inr (.inr (.inl rfl)))) (by decide) <|
  .cons (p3_3 _) (OpI.xor (.r 0) (.inl rfl)) (by decide) <|
  .cons (p3_5 _) (OpI.pop) (by decide) <|
  .nil 6

end FV7z.Ssj
