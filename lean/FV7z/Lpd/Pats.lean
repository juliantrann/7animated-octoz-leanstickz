import FV7z.Lemmas.Sp
import FV7z.Lemmas.BlkOps24
import FV7z.Lemmas.BlkOps20
import FV7z.Lemmas.BlkOps14
import FV7z.Lemmas.BlkOps2
/-!
# The stretches of straight-line code of `LzmaProps_Decode` (PLAN.md §M, M1)

Each distinct stretch between labels and jumps (`p*`, 4 of them) and each distinct jump (`j*`, 2) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.Lpd
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The stretch at `0`. -/
def p0 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0x83, 0xfa, 0x04]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem p0_4 : ∀ feat, Dec feat p0 4 (FV7z.mk .cmp 32 [gr 32 2, Src.opd 32 (.i 4)] 3) := by dec_rfl

/-- What the stretch does. -/
def o0 : List Op := [
  Op.nop,
  Op.cmp 32 2 (.i 4)]

theorem b0 (prof : Profile) : Blk prof p0 0 7 o0 :=
  .cons (p0_0 _) (OpI.endbr) (by decide) <|
  .cons (p0_4 _) (OpI.cmp (.i 4) (.inl rfl)) (by decide) <|
  .nil 7

def j0 : List Byte := [0x76, 0x57]
theorem j0_0 : ∀ feat, Dec feat j0 0 (FV7z.mk (.jcc 6) 64 [.rel 87] 2) := by dec_rfl

/-- The stretch at `9`. -/
def p1 : List Byte := [
  0x8b, 0x46, 0x01, 0xba, 0x00, 0x10, 0x00, 0x00, 0x3d, 0x00, 0x10, 0x00, 0x00, 0x0f, 0x42, 0xc2,
  0x89, 0x47, 0x04, 0x0f, 0xb6, 0x16, 0x80, 0xfa, 0xe0]

theorem p1_0 : ∀ feat, Dec feat p1 0 (FV7z.mk .mov 32 [gr 32 0, .mem (mg (some 6) none 1 1 32)] 3) := by dec_rfl
theorem p1_3 : ∀ feat, Dec feat p1 3 (FV7z.mk .mov 32 [gr 32 2, Src.opd 32 (.i 4096)] 5) := by dec_rfl
theorem p1_8 : ∀ feat, Dec feat p1 8 (FV7z.mk .cmp 32 [gr 32 0, Src.opd 32 (.i 4096)] 5) := by dec_rfl
theorem p1_13 : ∀ feat, Dec feat p1 13 (FV7z.mk (.cmovcc 2) 32 [gr 32 0, gr 32 2] 3) := by dec_rfl
theorem p1_16 : ∀ feat, Dec feat p1 16 (FV7z.mk .mov 32 [.mem (mg (some 7) none 1 4 32), gr 32 0] 3) := by dec_rfl
theorem p1_19 : ∀ feat, Dec feat p1 19 (FV7z.mk .movzx 32 [gr 32 2, .mem (mg (some 6) none 1 0 8)] 3) := by dec_rfl
theorem p1_22 : ∀ feat, Dec feat p1 22 (FV7z.mk .cmp 8 [gr 8 2, Src.opd 8 (.i 224)] 3) := by dec_rfl

/-- What the stretch does. -/
def o1 : List Op := [
  Op.ld 32 0 (some 6) none 1 1,
  Op.mov 32 2 (.i 4096),
  Op.cmp 32 0 (.i 4096),
  Op.cmov32 2 0 2,
  Op.st 32 (some 7) none 1 4 0,
  Op.ldzx 8 2 (some 6) none 1 0,
  Op.cmp 8 2 (.i 224)]

theorem b1 (prof : Profile) : Blk prof p1 0 25 o1 :=
  .cons (p1_0 _) (OpI.ld (.inl rfl)) (by decide) <|
  .cons (p1_3 _) (OpI.mov (.i 4096) (.inl rfl)) (by decide) <|
  .cons (p1_8 _) (OpI.cmp (.i 4096) (.inl rfl)) (by decide) <|
  .cons (p1_13 _) (OpI.cmov32) (by decide) <|
  .cons (p1_16 _) (OpI.st (.inr (.inr (.inl rfl)))) (by decide) <|
  .cons (p1_19 _) (OpI.ldzx (.inl rfl)) (by decide) <|
  .cons (p1_22 _) (OpI.cmp8 (.i 224)) (by decide) <|
  .nil 25

def j1 : List Byte := [0x77, 0x3c]
theorem j1_0 : ∀ feat, Dec feat j1 0 (FV7z.mk (.jcc 7) 64 [.rel 60] 2) := by dec_rfl

/-- The stretch at `36`. -/
def p2 : List Byte := [
  0x0f, 0xb6, 0xca, 0x8d, 0x04, 0xcd, 0x00, 0x00, 0x00, 0x00, 0x29, 0xc8, 0x8d, 0x04, 0xc1, 0x66,
  0xc1, 0xe8, 0x09, 0x8d, 0x0c, 0xc0, 0x29, 0xca, 0x88, 0x17, 0x66, 0x0f, 0xbe, 0xd0, 0x6b, 0xd2,
  0x67, 0x66, 0xc1, 0xea, 0x09, 0x88, 0x57, 0x02, 0x8d, 0x14, 0x92, 0x29, 0xd0, 0x88, 0x47, 0x01,
  0x31, 0xc0]

theorem p2_0 : ∀ feat, Dec feat p2 0 (FV7z.mk .movzx 32 [gr 32 1, gr 8 2] 3) := by dec_rfl
theorem p2_3 : ∀ feat, Dec feat p2 3 (FV7z.mk .lea 32 [gr 32 0, .mem (mg none (some 1) 8 0 0)] 7) := by dec_rfl
theorem p2_10 : ∀ feat, Dec feat p2 10 (FV7z.mk .sub 32 [gr 32 0, Src.opd 32 (.r 1)] 2) := by dec_rfl
theorem p2_12 : ∀ feat, Dec feat p2 12 (FV7z.mk .lea 32 [gr 32 0, .mem (mg (some 1) (some 0) 8 0 0)] 3) := by dec_rfl
theorem p2_15 : ∀ feat, Dec feat p2 15 (FV7z.mk .shr 16 [gr 16 0, .imm 8 9] 4) := by dec_rfl
theorem p2_19 : ∀ feat, Dec feat p2 19 (FV7z.mk .lea 32 [gr 32 1, .mem (mg (some 0) (some 0) 8 0 0)] 3) := by dec_rfl
theorem p2_22 : ∀ feat, Dec feat p2 22 (FV7z.mk .sub 32 [gr 32 2, Src.opd 32 (.r 1)] 2) := by dec_rfl
theorem p2_24 : ∀ feat, Dec feat p2 24 (FV7z.mk .mov 8 [.mem (mg (some 7) none 1 0 8), gr 8 2] 2) := by dec_rfl
theorem p2_26 : ∀ feat, Dec feat p2 26 (FV7z.mk .movsx 16 [gr 16 2, gr 8 0] 4) := by dec_rfl
theorem p2_30 : ∀ feat, Dec feat p2 30 (FV7z.mk .imul 32 [gr 32 2, gr 32 2, .imm 32 103] 3) := by dec_rfl
theorem p2_33 : ∀ feat, Dec feat p2 33 (FV7z.mk .shr 16 [gr 16 2, .imm 8 9] 4) := by dec_rfl
theorem p2_37 : ∀ feat, Dec feat p2 37 (FV7z.mk .mov 8 [.mem (mg (some 7) none 1 2 8), gr 8 2] 3) := by dec_rfl
theorem p2_40 : ∀ feat, Dec feat p2 40 (FV7z.mk .lea 32 [gr 32 2, .mem (mg (some 2) (some 2) 4 0 0)] 3) := by dec_rfl
theorem p2_43 : ∀ feat, Dec feat p2 43 (FV7z.mk .sub 32 [gr 32 0, Src.opd 32 (.r 2)] 2) := by dec_rfl
theorem p2_45 : ∀ feat, Dec feat p2 45 (FV7z.mk .mov 8 [.mem (mg (some 7) none 1 1 8), gr 8 0] 3) := by dec_rfl
theorem p2_48 : ∀ feat, Dec feat p2 48 (FV7z.mk .xor 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl

/-- What the stretch does. -/
def o2 : List Op := [
  Op.zxr 1 2,
  Op.lea 32 0 none (some 1) 8 0,
  Op.sub 32 0 (.r 1),
  Op.lea 32 0 (some 1) (some 0) 8 0,
  Op.shr16 0 9,
  Op.lea 32 1 (some 0) (some 0) 8 0,
  Op.sub 32 2 (.r 1),
  Op.st 8 (some 7) none 1 0 2,
  Op.sxb16 2 0,
  Op.imul3d 2 2 103,
  Op.shr16 2 9,
  Op.st 8 (some 7) none 1 2 2,
  Op.lea 32 2 (some 2) (some 2) 4 0,
  Op.sub 32 0 (.r 2),
  Op.st 8 (some 7) none 1 1 0,
  Op.xor 32 0 (.r 0)]

theorem b2 (prof : Profile) : Blk prof p2 0 50 o2 :=
  .cons (p2_0 _) (OpI.zxr) (by decide) <|
  .cons (p2_3 _) (OpI.lea (.inl rfl)) (by decide) <|
  .cons (p2_10 _) (OpI.sub (.r 1) (.inl rfl)) (by decide) <|
  .cons (p2_12 _) (OpI.lea (.inl rfl)) (by decide) <|
  .cons (p2_15 _) (OpI.shr16) (by decide) <|
  .cons (p2_19 _) (OpI.lea (.inl rfl)) (by decide) <|
  .cons (p2_22 _) (OpI.sub (.r 1) (.inl rfl)) (by decide) <|
  .cons (p2_24 _) (OpI.st (.inl rfl)) (by decide) <|
  .cons (p2_26 _) (OpI.sxb16) (by decide) <|
  .cons (p2_30 _) (OpI.imul3d) (by decide) <|
  .cons (p2_33 _) (OpI.shr16) (by decide) <|
  .cons (p2_37 _) (OpI.st (.inl rfl)) (by decide) <|
  .cons (p2_40 _) (OpI.lea (.inl rfl)) (by decide) <|
  .cons (p2_43 _) (OpI.sub (.r 2) (.inl rfl)) (by decide) <|
  .cons (p2_45 _) (OpI.st (.inl rfl)) (by decide) <|
  .cons (p2_48 _) (OpI.xor (.r 0) (.inl rfl)) (by decide) <|
  .nil 50

/-- The stretch at `96`. -/
def p3 : List Byte := [
  0xb8, 0x04, 0x00, 0x00, 0x00]

theorem p3_0 : ∀ feat, Dec feat p3 0 (FV7z.mk .mov 32 [gr 32 0, Src.opd 32 (.i 4)] 5) := by dec_rfl

/-- What the stretch does. -/
def o3 : List Op := [
  Op.mov 32 0 (.i 4)]

theorem b3 (prof : Profile) : Blk prof p3 0 5 o3 :=
  .cons (p3_0 _) (OpI.mov (.i 4) (.inl rfl)) (by decide) <|
  .nil 5

end FV7z.Lpd
