import FV7z.Lemmas.Sp
import FV7z.Lemmas.BlkOps2
/-!
# The stretches of straight-line code of `_dl_protect_relro` (PLAN.md G3, startup)

Each distinct stretch between labels and jumps (`p*`, 4 of them) and each distinct jump (`j*`, 2) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.Dpr
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The stretch at `0`. -/
def p0 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0x48, 0x8b, 0x35, 0x2d, 0x7d, 0x0e, 0x00, 0x53, 0x48, 0x89, 0xfb, 0x48,
  0x8b, 0x87, 0x68, 0x04, 0x00, 0x00, 0x48, 0x03, 0x07, 0x48, 0xf7, 0xde, 0x48, 0x89, 0xc7, 0x48,
  0x03, 0x83, 0x70, 0x04, 0x00, 0x00, 0x48, 0x21, 0xf7, 0x48, 0x21, 0xf0, 0x48, 0x39, 0xc7]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem p0_4 : ∀ feat, Dec feat p0 4 (FV7z.mk .mov 64 [gr 64 6, .mem (mrip 949549 64)] 7) := by dec_rfl
theorem p0_11 : ∀ feat, Dec feat p0 11 (FV7z.mk .push 64 [gr 64 3] 1) := by dec_rfl
theorem p0_12 : ∀ feat, Dec feat p0 12 (FV7z.mk .mov 64 [gr 64 3, Src.opd 64 (.r 7)] 3) := by dec_rfl
theorem p0_15 : ∀ feat, Dec feat p0 15 (FV7z.mk .mov 64 [gr 64 0, .mem (mg (some 7) none 1 1128 64)] 7) := by dec_rfl
theorem p0_22 : ∀ feat, Dec feat p0 22 (FV7z.mk .add 64 [gr 64 0, .mem (mg (some 7) none 1 0 64)] 3) := by dec_rfl
theorem p0_25 : ∀ feat, Dec feat p0 25 (FV7z.mk .neg 64 [gr 64 6] 3) := by dec_rfl
theorem p0_28 : ∀ feat, Dec feat p0 28 (FV7z.mk .mov 64 [gr 64 7, Src.opd 64 (.r 0)] 3) := by dec_rfl
theorem p0_31 : ∀ feat, Dec feat p0 31 (FV7z.mk .add 64 [gr 64 0, .mem (mg (some 3) none 1 1136 64)] 7) := by dec_rfl
theorem p0_38 : ∀ feat, Dec feat p0 38 (FV7z.mk .and 64 [gr 64 7, Src.opd 64 (.r 6)] 3) := by dec_rfl
theorem p0_41 : ∀ feat, Dec feat p0 41 (FV7z.mk .and 64 [gr 64 0, Src.opd 64 (.r 6)] 3) := by dec_rfl
theorem p0_44 : ∀ feat, Dec feat p0 44 (FV7z.mk .cmp 64 [gr 64 7, Src.opd 64 (.r 0)] 3) := by dec_rfl

/-- What the stretch does. -/
def o0 : List Op := [
  Op.nop,
  Op.lda 64 6 7943128,
  Op.push 3,
  Op.mov 64 3 (.r 7),
  Op.ld 64 0 (some 7) none 1 1128,
  Op.addm 64 0 (some 7) none 1 0,
  Op.neg 64 6,
  Op.mov 64 7 (.r 0),
  Op.addm 64 0 (some 3) none 1 1136,
  Op.and 64 7 (.r 6),
  Op.and 64 0 (.r 6),
  Op.cmp 64 7 (.r 0)]

theorem b0 (prof : Profile) : BlkA prof p0 (0x6ab6a0 : Addr) 0 47 o0 :=
  .cons (p0_0 _) ((OpI.endbr).at _) (by decide) <|
  .cons (p0_4 _) (OpIA.ld_rip (.inr rfl) (by decide)) (by decide) <|
  .cons (p0_11 _) ((OpI.push).at _) (by decide) <|
  .cons (p0_12 _) ((OpI.mov (.r 7) (.inr rfl)).at _) (by decide) <|
  .cons (p0_15 _) ((OpI.ld (.inr rfl)).at _) (by decide) <|
  .cons (p0_22 _) ((OpI.addm (.inr rfl)).at _) (by decide) <|
  .cons (p0_25 _) ((OpI.neg (.inr rfl)).at _) (by decide) <|
  .cons (p0_28 _) ((OpI.mov (.r 0) (.inr rfl)).at _) (by decide) <|
  .cons (p0_31 _) ((OpI.addm (.inr rfl)).at _) (by decide) <|
  .cons (p0_38 _) ((OpI.and (.r 6) (.inr rfl)).at _) (by decide) <|
  .cons (p0_41 _) ((OpI.and (.r 6) (.inr rfl)).at _) (by decide) <|
  .cons (p0_44 _) ((OpI.cmp (.r 0) (.inr rfl)).at _) (by decide) <|
  .nil 47

def j0 : List Byte := [0x75, 0x07]
theorem j0_0 : ∀ feat, Dec feat j0 0 (FV7z.mk (.jcc 5) 64 [.rel 7] 2) := by dec_rfl

/-- The stretch at `49`. -/
def p1 : List Byte := [
  0x5b]

theorem p1_0 : ∀ feat, Dec feat p1 0 (FV7z.mk .pop 64 [gr 64 3] 1) := by dec_rfl

/-- What the stretch does. -/
def o1 : List Op := [
  Op.pop 3]

theorem b1 (prof : Profile) : Blk prof p1 0 1 o1 :=
  .cons (p1_0 _) (OpI.pop) (by decide) <|
  .nil 1

/-- The stretch at `56`. -/
def p2 : List Byte := [
  0x48, 0x29, 0xf8, 0xba, 0x01, 0x00, 0x00, 0x00, 0x48, 0x89, 0xc6]

theorem p2_0 : ∀ feat, Dec feat p2 0 (FV7z.mk .sub 64 [gr 64 0, Src.opd 64 (.r 7)] 3) := by dec_rfl
theorem p2_3 : ∀ feat, Dec feat p2 3 (FV7z.mk .mov 32 [gr 32 2, Src.opd 32 (.i 1)] 5) := by dec_rfl
theorem p2_8 : ∀ feat, Dec feat p2 8 (FV7z.mk .mov 64 [gr 64 6, Src.opd 64 (.r 0)] 3) := by dec_rfl

/-- What the stretch does. -/
def o2 : List Op := [
  Op.sub 64 0 (.r 7),
  Op.mov 32 2 (.i 1),
  Op.mov 64 6 (.r 0)]

theorem b2 (prof : Profile) : Blk prof p2 0 11 o2 :=
  .cons (p2_0 _) (OpI.sub (.r 7) (.inr rfl)) (by decide) <|
  .cons (p2_3 _) (OpI.mov (.i 1) (.inl rfl)) (by decide) <|
  .cons (p2_8 _) (OpI.mov (.r 0) (.inr rfl)) (by decide) <|
  .nil 11

/-- The stretch at `72`. -/
def p3 : List Byte := [
  0x85, 0xc0]

theorem p3_0 : ∀ feat, Dec feat p3 0 (FV7z.mk .test 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl

/-- What the stretch does. -/
def o3 : List Op := [
  Op.test 32 0 (.r 0)]

theorem b3 (prof : Profile) : Blk prof p3 0 2 o3 :=
  .cons (p3_0 _) (OpI.test (.r 0) (.inl rfl)) (by decide) <|
  .nil 2

def j1 : List Byte := [0x79, 0xe5]
theorem j1_0 : ∀ feat, Dec feat j1 0 (FV7z.mk (.jcc 9) 64 [.rel 18446744073709551589] 2) := by dec_rfl

end FV7z.Dpr
