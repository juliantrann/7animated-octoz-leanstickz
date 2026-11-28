import FV7z.Lemmas.Sp
import FV7z.Lemmas.BlkOps2
/-!
# The stretches of straight-line code of `GetPropName` (PLAN.md §M, M1)

Each distinct stretch between labels and jumps (`p*`, 5 of them) and each distinct jump (`j*`, 2) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.Gpn
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The stretch at `0`. -/
def p0 : List Byte := [
  0x41, 0x89, 0xf8, 0x48, 0x89, 0xd7, 0x41, 0x83, 0xf8, 0x68]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .mov 32 [gr 32 8, Src.opd 32 (.r 7)] 3) := by dec_rfl
theorem p0_3 : ∀ feat, Dec feat p0 3 (FV7z.mk .mov 64 [gr 64 7, Src.opd 64 (.r 2)] 3) := by dec_rfl
theorem p0_6 : ∀ feat, Dec feat p0 6 (FV7z.mk .cmp 32 [gr 32 8, Src.opd 32 (.i 104)] 4) := by dec_rfl

/-- What the stretch does. -/
def o0 : List Op := [
  Op.mov 32 8 (.r 7),
  Op.mov 64 7 (.r 2),
  Op.cmp 32 8 (.i 104)]

theorem b0 (prof : Profile) : Blk prof p0 0 10 o0 :=
  .cons (p0_0 _) (OpI.mov (.r 7) (.inl rfl)) (by decide) <|
  .cons (p0_3 _) (OpI.mov (.r 2) (.inr rfl)) (by decide) <|
  .cons (p0_6 _) (OpI.cmp (.i 104) (.inl rfl)) (by decide) <|
  .nil 10

def j0 : List Byte := [0x76, 0x2c]
theorem j0_0 : ∀ feat, Dec feat j0 0 (FV7z.mk (.jcc 6) 64 [.rel 44] 2) := by dec_rfl

/-- The stretch at `12`. -/
def p1 : List Byte := [
  0x48, 0x85, 0xf6]

theorem p1_0 : ∀ feat, Dec feat p1 0 (FV7z.mk .test 64 [gr 64 6, Src.opd 64 (.r 6)] 3) := by dec_rfl

/-- What the stretch does. -/
def o1 : List Op := [
  Op.test 64 6 (.r 6)]

theorem b1 (prof : Profile) : Blk prof p1 0 3 o1 :=
  .cons (p1_0 _) (OpI.test (.r 6) (.inr rfl)) (by decide) <|
  .nil 3

def j1 : List Byte := [0x74, 0x0f]
theorem j1_0 : ∀ feat, Dec feat j1 0 (FV7z.mk (.jcc 4) 64 [.rel 15] 2) := by dec_rfl

/-- The stretch at `17`. -/
def p2 : List Byte := [
  0x48, 0x89, 0xcf]

theorem p2_0 : ∀ feat, Dec feat p2 0 (FV7z.mk .mov 64 [gr 64 7, Src.opd 64 (.r 1)] 3) := by dec_rfl

/-- What the stretch does. -/
def o2 : List Op := [
  Op.mov 64 7 (.r 1)]

theorem b2 (prof : Profile) : Blk prof p2 0 3 o2 :=
  .cons (p2_0 _) (OpI.mov (.r 1) (.inr rfl)) (by decide) <|
  .nil 3

/-- The stretch at `32`. -/
def p3 : List Byte := [
  0x48, 0x8b, 0x02, 0xc7, 0x42, 0x08, 0x00, 0x00, 0x00, 0x00, 0x44, 0x89, 0xc6, 0xc6, 0x00, 0x00]

theorem p3_0 : ∀ feat, Dec feat p3 0 (FV7z.mk .mov 64 [gr 64 0, .mem (mg (some 2) none 1 0 64)] 3) := by dec_rfl
theorem p3_3 : ∀ feat, Dec feat p3 3 (FV7z.mk .mov 32 [.mem (mg (some 2) none 1 8 32), .imm 32 0] 7) := by dec_rfl
theorem p3_10 : ∀ feat, Dec feat p3 10 (FV7z.mk .mov 32 [gr 32 6, Src.opd 32 (.r 8)] 3) := by dec_rfl
theorem p3_13 : ∀ feat, Dec feat p3 13 (FV7z.mk .mov 8 [.mem (mg (some 0) none 1 0 8), .imm 8 0] 3) := by dec_rfl

/-- What the stretch does. -/
def o3 : List Op := [
  Op.ld 64 0 (some 2) none 1 0,
  Op.sti 32 (some 2) none 1 8 0,
  Op.mov 32 6 (.r 8),
  Op.sti 8 (some 0) none 1 0 0]

theorem b3 (prof : Profile) : Blk prof p3 0 16 o3 :=
  .cons (p3_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p3_3 _) (OpI.sti (.inr (.inr (.inl rfl)))) (by decide) <|
  .cons (p3_10 _) (OpI.mov (.r 8) (.inl rfl)) (by decide) <|
  .cons (p3_13 _) (OpI.sti (.inl rfl)) (by decide) <|
  .nil 16

/-- The stretch at `56`. -/
def p4 : List Byte := [
  0x48, 0x8d, 0x05, 0x61, 0x38, 0x19, 0x00, 0x4a, 0x8b, 0x34, 0xc0]

theorem p4_0 : ∀ feat, Dec feat p4 0 (FV7z.mk .lea 64 [gr 64 0, .mem (mrip 1652833 0)] 7) := by dec_rfl
theorem p4_7 : ∀ feat, Dec feat p4 7 (FV7z.mk .mov 64 [gr 64 6, .mem (mg (some 0) (some 8) 8 0 64)] 4) := by dec_rfl

/-- What the stretch does. -/
def o4 : List Op := [
  Op.mov 64 0 (.i 7861536),
  Op.ld 64 6 (some 0) (some 8) 8 0]

theorem b4 (prof : Profile) : BlkA prof p4 (0x5ebcb8 : Addr) 0 11 o4 :=
  .cons (p4_0 _) (OpIA.lea_rip (by decide)) (by decide) <|
  .cons (p4_7 _) ((OpI.ld (.inr rfl)).at _) (by decide) <|
  .nil 11

end FV7z.Gpn
