import FV7z.Lemmas.Sp
import FV7z.Lemmas.RepCmpsb
import FV7z.Lemmas.BlkOps2
/-!
# The stretches of straight-line code of `fini` (PLAN.md §M, M1)

Each distinct stretch between labels and jumps (`p*`, 5 of them) and each distinct jump (`j*`, 2) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.Fni
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The stretch at `0`. -/
def p0 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0x4c, 0x8b, 0x05, 0x1d, 0x8b, 0x38, 0x00, 0x4d, 0x85, 0xc0]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem p0_4 : ∀ feat, Dec feat p0 4 (FV7z.mk .mov 64 [gr 64 8, .mem (mrip 3705629 64)] 7) := by dec_rfl
theorem p0_11 : ∀ feat, Dec feat p0 11 (FV7z.mk .test 64 [gr 64 8, Src.opd 64 (.r 8)] 3) := by dec_rfl

/-- What the stretch does. -/
def o0 : List Op := [
  Op.nop,
  Op.lda 64 8 8014872,
  Op.test 64 8 (.r 8)]

theorem b0 (prof : Profile) : BlkA prof p0 (0x41c0f0 : Addr) 0 14 o0 :=
  .cons (p0_0 _) ((OpI.endbr).at _) (by decide) <|
  .cons (p0_4 _) (OpIA.ld_rip (.inr rfl) (by decide)) (by decide) <|
  .cons (p0_11 _) ((OpI.test (.r 8) (.inr rfl)).at _) (by decide) <|
  .nil 14

def j0 : List Byte := [0x74, 0x1a]
theorem j0_0 : ∀ feat, Dec feat j0 0 (FV7z.mk (.jcc 4) 64 [.rel 26] 2) := by dec_rfl

/-- The stretch at `16`. -/
def p1 : List Byte := [
  0xb9, 0x0e, 0x00, 0x00, 0x00, 0x48, 0x8d, 0x3d, 0x50, 0xd3, 0x2b, 0x00, 0x4c, 0x89, 0xc6]

theorem p1_0 : ∀ feat, Dec feat p1 0 (FV7z.mk .mov 32 [gr 32 1, Src.opd 32 (.i 14)] 5) := by dec_rfl
theorem p1_5 : ∀ feat, Dec feat p1 5 (FV7z.mk .lea 64 [gr 64 7, .mem (mrip 2872144 0)] 7) := by dec_rfl
theorem p1_12 : ∀ feat, Dec feat p1 12 (FV7z.mk .mov 64 [gr 64 6, Src.opd 64 (.r 8)] 3) := by dec_rfl

/-- What the stretch does. -/
def o1 : List Op := [
  Op.mov 32 1 (.i 14),
  Op.mov 64 7 (.i 7181404),
  Op.mov 64 6 (.r 8)]

theorem b1 (prof : Profile) : BlkA prof p1 (0x41c100 : Addr) 0 15 o1 :=
  .cons (p1_0 _) ((OpI.mov (.i 14) (.inl rfl)).at _) (by decide) <|
  .cons (p1_5 _) (OpIA.lea_rip (by decide)) (by decide) <|
  .cons (p1_12 _) ((OpI.mov (.r 8) (.inr rfl)).at _) (by decide) <|
  .nil 15

/-- The stretch at `33`. -/
def p2 : List Byte := [
  0x0f, 0x97, 0xc0, 0x1c, 0x00, 0x84, 0xc0]

theorem p2_0 : ∀ feat, Dec feat p2 0 (FV7z.mk (.setcc 7) 8 [gr 8 0] 3) := by dec_rfl
theorem p2_3 : ∀ feat, Dec feat p2 3 (FV7z.mk .sbb 8 [gr 8 0, Src.opd 8 (.i 0)] 2) := by dec_rfl
theorem p2_5 : ∀ feat, Dec feat p2 5 (FV7z.mk .test 8 [gr 8 0, Src.opd 8 (.r 0)] 2) := by dec_rfl

/-- What the stretch does. -/
def o2 : List Op := [
  Op.setcc 7 0,
  Op.sbb8 0 (.i 0),
  Op.test 8 0 (.r 0)]

theorem b2 (prof : Profile) : Blk prof p2 0 7 o2 :=
  .cons (p2_0 _) (OpI.setcc) (by decide) <|
  .cons (p2_3 _) (OpI.sbb8 (.i 0)) (by decide) <|
  .cons (p2_5 _) (OpI.test8 (.r 0)) (by decide) <|
  .nil 7

def j1 : List Byte := [0x75, 0x01]
theorem j1_0 : ∀ feat, Dec feat j1 0 (FV7z.mk (.jcc 5) 64 [.rel 1] 2) := by dec_rfl

/-- The stretch at `43`. -/
def p3 : List Byte := [
  0x50, 0x4c, 0x89, 0xc7]

theorem p3_0 : ∀ feat, Dec feat p3 0 (FV7z.mk .push 64 [gr 64 0] 1) := by dec_rfl
theorem p3_1 : ∀ feat, Dec feat p3 1 (FV7z.mk .mov 64 [gr 64 7, Src.opd 64 (.r 8)] 3) := by dec_rfl

/-- What the stretch does. -/
def o3 : List Op := [
  Op.push 0,
  Op.mov 64 7 (.r 8)]

theorem b3 (prof : Profile) : Blk prof p3 0 4 o3 :=
  .cons (p3_0 _) (OpI.push) (by decide) <|
  .cons (p3_1 _) (OpI.mov (.r 8) (.inr rfl)) (by decide) <|
  .nil 4

/-- The stretch at `52`. -/
def p4 : List Byte := [
  0x48, 0xc7, 0x05, 0xe9, 0x8a, 0x38, 0x00, 0x00, 0x00, 0x00, 0x00, 0x5a]

theorem p4_0 : ∀ feat, Dec feat p4 0 (FV7z.mk .mov 64 [.mem (mrip 3705577 64), .imm 64 0] 11) := by dec_rfl
theorem p4_11 : ∀ feat, Dec feat p4 11 (FV7z.mk .pop 64 [gr 64 2] 1) := by dec_rfl

/-- What the stretch does. -/
def o4 : List Op := [
  Op.stia 64 8014872 0,
  Op.pop 2]

theorem b4 (prof : Profile) : BlkA prof p4 (0x41c124 : Addr) 0 12 o4 :=
  .cons (p4_0 _) (OpIA.sti_rip (.inr (.inr rfl)) (by decide)) (by decide) <|
  .cons (p4_11 _) ((OpI.pop).at _) (by decide) <|
  .nil 12

end FV7z.Fni
