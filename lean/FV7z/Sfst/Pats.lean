import FV7z.Lemmas.Sp
import FV7z.Lemmas.BlkOps7
import FV7z.Lemmas.BlkOps2
/-!
# The stretches of straight-line code of `SetFrom_stat` (PLAN.md §M, M1)

Each distinct stretch between labels and jumps (`p*`, 3 of them) and each distinct jump (`j*`, 1) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.Sfst
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The stretch at `0`. -/
def p0 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0x8b, 0x46, 0x18, 0x31, 0xd2, 0x89, 0xc1, 0x81, 0xe1, 0x00, 0xf0, 0x00,
  0x00, 0x81, 0xf9, 0x00, 0x40, 0x00, 0x00]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem p0_4 : ∀ feat, Dec feat p0 4 (FV7z.mk .mov 32 [gr 32 0, .mem (mg (some 6) none 1 24 32)] 3) := by dec_rfl
theorem p0_7 : ∀ feat, Dec feat p0 7 (FV7z.mk .xor 32 [gr 32 2, Src.opd 32 (.r 2)] 2) := by dec_rfl
theorem p0_9 : ∀ feat, Dec feat p0 9 (FV7z.mk .mov 32 [gr 32 1, Src.opd 32 (.r 0)] 2) := by dec_rfl
theorem p0_11 : ∀ feat, Dec feat p0 11 (FV7z.mk .and 32 [gr 32 1, Src.opd 32 (.i 61440)] 6) := by dec_rfl
theorem p0_17 : ∀ feat, Dec feat p0 17 (FV7z.mk .cmp 32 [gr 32 1, Src.opd 32 (.i 16384)] 6) := by dec_rfl

/-- What the stretch does. -/
def o0 : List Op := [
  Op.nop,
  Op.ld 32 0 (some 6) none 1 24,
  Op.xor 32 2 (.r 2),
  Op.mov 32 1 (.r 0),
  Op.and 32 1 (.i 61440),
  Op.cmp 32 1 (.i 16384)]

theorem b0 (prof : Profile) : Blk prof p0 0 23 o0 :=
  .cons (p0_0 _) (OpI.endbr) (by decide) <|
  .cons (p0_4 _) (OpI.ld (.inl rfl)) (by decide) <|
  .cons (p0_7 _) (OpI.xor (.r 2) (.inl rfl)) (by decide) <|
  .cons (p0_9 _) (OpI.mov (.r 0) (.inl rfl)) (by decide) <|
  .cons (p0_11 _) (OpI.and (.i 61440) (.inl rfl)) (by decide) <|
  .cons (p0_17 _) (OpI.cmp (.i 16384) (.inl rfl)) (by decide) <|
  .nil 23

def j0 : List Byte := [0x74, 0x04]
theorem j0_0 : ∀ feat, Dec feat j0 0 (FV7z.mk (.jcc 4) 64 [.rel 4] 2) := by dec_rfl

/-- The stretch at `25`. -/
def p1 : List Byte := [
  0x48, 0x8b, 0x56, 0x30]

theorem p1_0 : ∀ feat, Dec feat p1 0 (FV7z.mk .mov 64 [gr 64 2, .mem (mg (some 6) none 1 48 64)] 4) := by dec_rfl

/-- What the stretch does. -/
def o1 : List Op := [
  Op.ld 64 2 (some 6) none 1 48]

theorem b1 (prof : Profile) : Blk prof p1 0 4 o1 :=
  .cons (p1_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .nil 4

/-- The stretch at `29`. -/
def p2 : List Byte := [
  0xf3, 0x0f, 0x6f, 0x46, 0x68, 0xf3, 0x0f, 0x6f, 0x4e, 0x58, 0x48, 0x89, 0x17, 0x48, 0x8b, 0x16,
  0xf3, 0x0f, 0x6f, 0x56, 0x48, 0x0f, 0x11, 0x47, 0x08, 0x48, 0x89, 0x57, 0x38, 0x48, 0x8b, 0x56,
  0x08, 0x89, 0x47, 0x48, 0x48, 0x8b, 0x46, 0x10, 0x48, 0x89, 0x57, 0x40, 0x48, 0x89, 0x47, 0x50,
  0x8b, 0x46, 0x1c, 0x0f, 0x11, 0x4f, 0x28, 0x89, 0x47, 0x58, 0x8b, 0x46, 0x20, 0x0f, 0x11, 0x57,
  0x18, 0x89, 0x47, 0x5c, 0x48, 0x8b, 0x46, 0x28, 0x48, 0x89, 0x47, 0x60]

theorem p2_0 : ∀ feat, Dec feat p2 0 (FV7z.mk (.sse (SseMn.movdqu)) 32 [.xmm 0, .mem (mg (some 6) none 1 104 128)] 5) := by dec_rfl
theorem p2_5 : ∀ feat, Dec feat p2 5 (FV7z.mk (.sse (SseMn.movdqu)) 32 [.xmm 1, .mem (mg (some 6) none 1 88 128)] 5) := by dec_rfl
theorem p2_10 : ∀ feat, Dec feat p2 10 (FV7z.mk .mov 64 [.mem (mg (some 7) none 1 0 64), gr 64 2] 3) := by dec_rfl
theorem p2_13 : ∀ feat, Dec feat p2 13 (FV7z.mk .mov 64 [gr 64 2, .mem (mg (some 6) none 1 0 64)] 3) := by dec_rfl
theorem p2_16 : ∀ feat, Dec feat p2 16 (FV7z.mk (.sse (SseMn.movdqu)) 32 [.xmm 2, .mem (mg (some 6) none 1 72 128)] 5) := by dec_rfl
theorem p2_21 : ∀ feat, Dec feat p2 21 (FV7z.mk (.sse (SseMn.movups)) 32 [.mem (mg (some 7) none 1 8 128), .xmm 0] 4) := by dec_rfl
theorem p2_25 : ∀ feat, Dec feat p2 25 (FV7z.mk .mov 64 [.mem (mg (some 7) none 1 56 64), gr 64 2] 4) := by dec_rfl
theorem p2_29 : ∀ feat, Dec feat p2 29 (FV7z.mk .mov 64 [gr 64 2, .mem (mg (some 6) none 1 8 64)] 4) := by dec_rfl
theorem p2_33 : ∀ feat, Dec feat p2 33 (FV7z.mk .mov 32 [.mem (mg (some 7) none 1 72 32), gr 32 0] 3) := by dec_rfl
theorem p2_36 : ∀ feat, Dec feat p2 36 (FV7z.mk .mov 64 [gr 64 0, .mem (mg (some 6) none 1 16 64)] 4) := by dec_rfl
theorem p2_40 : ∀ feat, Dec feat p2 40 (FV7z.mk .mov 64 [.mem (mg (some 7) none 1 64 64), gr 64 2] 4) := by dec_rfl
theorem p2_44 : ∀ feat, Dec feat p2 44 (FV7z.mk .mov 64 [.mem (mg (some 7) none 1 80 64), gr 64 0] 4) := by dec_rfl
theorem p2_48 : ∀ feat, Dec feat p2 48 (FV7z.mk .mov 32 [gr 32 0, .mem (mg (some 6) none 1 28 32)] 3) := by dec_rfl
theorem p2_51 : ∀ feat, Dec feat p2 51 (FV7z.mk (.sse (SseMn.movups)) 32 [.mem (mg (some 7) none 1 40 128), .xmm 1] 4) := by dec_rfl
theorem p2_55 : ∀ feat, Dec feat p2 55 (FV7z.mk .mov 32 [.mem (mg (some 7) none 1 88 32), gr 32 0] 3) := by dec_rfl
theorem p2_58 : ∀ feat, Dec feat p2 58 (FV7z.mk .mov 32 [gr 32 0, .mem (mg (some 6) none 1 32 32)] 3) := by dec_rfl
theorem p2_61 : ∀ feat, Dec feat p2 61 (FV7z.mk (.sse (SseMn.movups)) 32 [.mem (mg (some 7) none 1 24 128), .xmm 2] 4) := by dec_rfl
theorem p2_65 : ∀ feat, Dec feat p2 65 (FV7z.mk .mov 32 [.mem (mg (some 7) none 1 92 32), gr 32 0] 3) := by dec_rfl
theorem p2_68 : ∀ feat, Dec feat p2 68 (FV7z.mk .mov 64 [gr 64 0, .mem (mg (some 6) none 1 40 64)] 4) := by dec_rfl
theorem p2_72 : ∀ feat, Dec feat p2 72 (FV7z.mk .mov 64 [.mem (mg (some 7) none 1 96 64), gr 64 0] 4) := by dec_rfl

/-- What the stretch does. -/
def o2 : List Op := [
  Op.vl 16 (some 6) none 1 104,
  Op.vl 16 (some 6) none 1 88,
  Op.st 64 (some 7) none 1 0 2,
  Op.ld 64 2 (some 6) none 1 0,
  Op.vl 16 (some 6) none 1 72,
  Op.vs 16 (some 7) none 1 8,
  Op.st 64 (some 7) none 1 56 2,
  Op.ld 64 2 (some 6) none 1 8,
  Op.st 32 (some 7) none 1 72 0,
  Op.ld 64 0 (some 6) none 1 16,
  Op.st 64 (some 7) none 1 64 2,
  Op.st 64 (some 7) none 1 80 0,
  Op.ld 32 0 (some 6) none 1 28,
  Op.vs 16 (some 7) none 1 40,
  Op.st 32 (some 7) none 1 88 0,
  Op.ld 32 0 (some 6) none 1 32,
  Op.vs 16 (some 7) none 1 24,
  Op.st 32 (some 7) none 1 92 0,
  Op.ld 64 0 (some 6) none 1 40,
  Op.st 64 (some 7) none 1 96 0]

theorem b2 (prof : Profile) : Blk prof p2 0 76 o2 :=
  .cons (p2_0 _) (OpI.vl_movdqu) (by decide) <|
  .cons (p2_5 _) (OpI.vl_movdqu) (by decide) <|
  .cons (p2_10 _) (OpI.st (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p2_13 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p2_16 _) (OpI.vl_movdqu) (by decide) <|
  .cons (p2_21 _) (OpI.vs_movups) (by decide) <|
  .cons (p2_25 _) (OpI.st (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p2_29 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p2_33 _) (OpI.st (.inr (.inr (.inl rfl)))) (by decide) <|
  .cons (p2_36 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p2_40 _) (OpI.st (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p2_44 _) (OpI.st (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p2_48 _) (OpI.ld (.inl rfl)) (by decide) <|
  .cons (p2_51 _) (OpI.vs_movups) (by decide) <|
  .cons (p2_55 _) (OpI.st (.inr (.inr (.inl rfl)))) (by decide) <|
  .cons (p2_58 _) (OpI.ld (.inl rfl)) (by decide) <|
  .cons (p2_61 _) (OpI.vs_movups) (by decide) <|
  .cons (p2_65 _) (OpI.st (.inr (.inr (.inl rfl)))) (by decide) <|
  .cons (p2_68 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p2_72 _) (OpI.st (.inr (.inr (.inr rfl)))) (by decide) <|
  .nil 76

end FV7z.Sfst
