import FV7z.Lemmas.Sp
import FV7z.Lemmas.BlkOps2
/-!
# The stretches of straight-line code of `__init_misc` (PLAN.md G3, startup)

Each distinct stretch between labels and jumps (`p*`, 5 of them) and each distinct jump (`j*`, 2) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.Ims
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The stretch at `0`. -/
def p0 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0x48, 0x85, 0xf6]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem p0_4 : ∀ feat, Dec feat p0 4 (FV7z.mk .test 64 [gr 64 6, Src.opd 64 (.r 6)] 3) := by dec_rfl

/-- What the stretch does. -/
def o0 : List Op := [
  Op.nop,
  Op.test 64 6 (.r 6)]

theorem b0 (prof : Profile) : Blk prof p0 0 7 o0 :=
  .cons (p0_0 _) (OpI.endbr) (by decide) <|
  .cons (p0_4 _) (OpI.test (.r 6) (.inr rfl)) (by decide) <|
  .nil 7

def j0 : List Byte := [0x74, 0x47]
theorem j0_0 : ∀ feat, Dec feat j0 0 (FV7z.mk (.jcc 4) 64 [.rel 71] 2) := by dec_rfl

/-- The stretch at `9`. -/
def p1 : List Byte := [
  0x55, 0x53, 0x48, 0x89, 0xf3, 0x48, 0x83, 0xec, 0x08, 0x48, 0x8b, 0x2e, 0x48, 0x85, 0xed]

theorem p1_0 : ∀ feat, Dec feat p1 0 (FV7z.mk .push 64 [gr 64 5] 1) := by dec_rfl
theorem p1_1 : ∀ feat, Dec feat p1 1 (FV7z.mk .push 64 [gr 64 3] 1) := by dec_rfl
theorem p1_2 : ∀ feat, Dec feat p1 2 (FV7z.mk .mov 64 [gr 64 3, Src.opd 64 (.r 6)] 3) := by dec_rfl
theorem p1_5 : ∀ feat, Dec feat p1 5 (FV7z.mk .sub 64 [gr 64 4, Src.opd 64 (.i 8)] 4) := by dec_rfl
theorem p1_9 : ∀ feat, Dec feat p1 9 (FV7z.mk .mov 64 [gr 64 5, .mem (mg (some 6) none 1 0 64)] 3) := by dec_rfl
theorem p1_12 : ∀ feat, Dec feat p1 12 (FV7z.mk .test 64 [gr 64 5, Src.opd 64 (.r 5)] 3) := by dec_rfl

/-- What the stretch does. -/
def o1 : List Op := [
  Op.push 5,
  Op.push 3,
  Op.mov 64 3 (.r 6),
  Op.sub 64 4 (.i 8),
  Op.ld 64 5 (some 6) none 1 0,
  Op.test 64 5 (.r 5)]

theorem b1 (prof : Profile) : Blk prof p1 0 15 o1 :=
  .cons (p1_0 _) (OpI.push) (by decide) <|
  .cons (p1_1 _) (OpI.push) (by decide) <|
  .cons (p1_2 _) (OpI.mov (.r 6) (.inr rfl)) (by decide) <|
  .cons (p1_5 _) (OpI.sub (.i 8) (.inr rfl)) (by decide) <|
  .cons (p1_9 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p1_12 _) (OpI.test (.r 5) (.inr rfl)) (by decide) <|
  .nil 15

def j1 : List Byte := [0x74, 0x29]
theorem j1_0 : ∀ feat, Dec feat j1 0 (FV7z.mk (.jcc 4) 64 [.rel 41] 2) := by dec_rfl

/-- The stretch at `26`. -/
def p2 : List Byte := [
  0x48, 0x89, 0xef, 0xbe, 0x2f, 0x00, 0x00, 0x00]

theorem p2_0 : ∀ feat, Dec feat p2 0 (FV7z.mk .mov 64 [gr 64 7, Src.opd 64 (.r 5)] 3) := by dec_rfl
theorem p2_3 : ∀ feat, Dec feat p2 3 (FV7z.mk .mov 32 [gr 32 6, Src.opd 32 (.i 47)] 5) := by dec_rfl

/-- What the stretch does. -/
def o2 : List Op := [
  Op.mov 64 7 (.r 5),
  Op.mov 32 6 (.i 47)]

theorem b2 (prof : Profile) : Blk prof p2 0 8 o2 :=
  .cons (p2_0 _) (OpI.mov (.r 5) (.inr rfl)) (by decide) <|
  .cons (p2_3 _) (OpI.mov (.i 47) (.inl rfl)) (by decide) <|
  .nil 8

/-- The stretch at `39`. -/
def p3 : List Byte := [
  0x48, 0x8d, 0x50, 0x01, 0x48, 0x85, 0xc0, 0x48, 0x0f, 0x45, 0xea, 0x48, 0x89, 0x2d, 0x5f, 0xa5,
  0x12, 0x00, 0x48, 0x8b, 0x03, 0x48, 0x89, 0x05, 0x5d, 0xa5, 0x12, 0x00]

theorem p3_0 : ∀ feat, Dec feat p3 0 (FV7z.mk .lea 64 [gr 64 2, .mem (mg (some 0) none 1 1 0)] 4) := by dec_rfl
theorem p3_4 : ∀ feat, Dec feat p3 4 (FV7z.mk .test 64 [gr 64 0, Src.opd 64 (.r 0)] 3) := by dec_rfl
theorem p3_7 : ∀ feat, Dec feat p3 7 (FV7z.mk (.cmovcc 5) 64 [gr 64 5, gr 64 2] 4) := by dec_rfl
theorem p3_11 : ∀ feat, Dec feat p3 11 (FV7z.mk .mov 64 [.mem (mrip 1221983 64), gr 64 5] 7) := by dec_rfl
theorem p3_18 : ∀ feat, Dec feat p3 18 (FV7z.mk .mov 64 [gr 64 0, .mem (mg (some 3) none 1 0 64)] 3) := by dec_rfl
theorem p3_21 : ∀ feat, Dec feat p3 21 (FV7z.mk .mov 64 [.mem (mrip 1221981 64), gr 64 0] 7) := by dec_rfl

/-- What the stretch does. -/
def o3 : List Op := [
  Op.lea 64 2 (some 0) none 1 1,
  Op.test 64 0 (.r 0),
  Op.cmov64 5 5 2,
  Op.sta 64 7942968 5,
  Op.ld 64 0 (some 3) none 1 0,
  Op.sta 64 7942976 0]

theorem b3 (prof : Profile) : BlkA prof p3 (0x668dc7 : Addr) 0 28 o3 :=
  .cons (p3_0 _) ((OpI.lea (.inr rfl)).at _) (by decide) <|
  .cons (p3_4 _) ((OpI.test (.r 0) (.inr rfl)).at _) (by decide) <|
  .cons (p3_7 _) ((OpI.cmov64).at _) (by decide) <|
  .cons (p3_11 _) (OpIA.st_rip (.inr (.inr rfl)) (by decide)) (by decide) <|
  .cons (p3_18 _) ((OpI.ld (.inr rfl)).at _) (by decide) <|
  .cons (p3_21 _) (OpIA.st_rip (.inr (.inr rfl)) (by decide)) (by decide) <|
  .nil 28

/-- The stretch at `67`. -/
def p4 : List Byte := [
  0x48, 0x83, 0xc4, 0x08, 0x5b, 0x5d]

theorem p4_0 : ∀ feat, Dec feat p4 0 (FV7z.mk .add 64 [gr 64 4, Src.opd 64 (.i 8)] 4) := by dec_rfl
theorem p4_4 : ∀ feat, Dec feat p4 4 (FV7z.mk .pop 64 [gr 64 3] 1) := by dec_rfl
theorem p4_5 : ∀ feat, Dec feat p4 5 (FV7z.mk .pop 64 [gr 64 5] 1) := by dec_rfl

/-- What the stretch does. -/
def o4 : List Op := [
  Op.add 64 4 (.i 8),
  Op.pop 3,
  Op.pop 5]

theorem b4 (prof : Profile) : Blk prof p4 0 6 o4 :=
  .cons (p4_0 _) (OpI.add (.i 8) (.inr rfl)) (by decide) <|
  .cons (p4_4 _) (OpI.pop) (by decide) <|
  .cons (p4_5 _) (OpI.pop) (by decide) <|
  .nil 6

end FV7z.Ims
