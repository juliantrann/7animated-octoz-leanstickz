import FV7z.Lemmas.Sp
import FV7z.Lemmas.BlkOps19
import FV7z.Lemmas.BlkOps7
import FV7z.Lemmas.BlkOps2
/-!
# The stretches of straight-line code of `NCrypto::N7z::CKey::Wipe` (PLAN.md §M, M1)

Each distinct stretch between labels and jumps (`p*`, 3 of them) and each distinct jump (`j*`, 2) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.Ckw
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The stretch at `0`. -/
def p0 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0x53, 0x48, 0x8b, 0x57, 0x50, 0x48, 0x89, 0xfb, 0x48, 0x85, 0xd2]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem p0_4 : ∀ feat, Dec feat p0 4 (FV7z.mk .push 64 [gr 64 3] 1) := by dec_rfl
theorem p0_5 : ∀ feat, Dec feat p0 5 (FV7z.mk .mov 64 [gr 64 2, .mem (mg (some 7) none 1 80 64)] 4) := by dec_rfl
theorem p0_9 : ∀ feat, Dec feat p0 9 (FV7z.mk .mov 64 [gr 64 3, Src.opd 64 (.r 7)] 3) := by dec_rfl
theorem p0_12 : ∀ feat, Dec feat p0 12 (FV7z.mk .test 64 [gr 64 2, Src.opd 64 (.r 2)] 3) := by dec_rfl

/-- What the stretch does. -/
def o0 : List Op := [
  Op.nop,
  Op.push 3,
  Op.ld 64 2 (some 7) none 1 80,
  Op.mov 64 3 (.r 7),
  Op.test 64 2 (.r 2)]

theorem b0 (prof : Profile) : Blk prof p0 0 15 o0 :=
  .cons (p0_0 _) (OpI.endbr) (by decide) <|
  .cons (p0_4 _) (OpI.push) (by decide) <|
  .cons (p0_5 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p0_9 _) (OpI.mov (.r 7) (.inr rfl)) (by decide) <|
  .cons (p0_12 _) (OpI.test (.r 2) (.inr rfl)) (by decide) <|
  .nil 15

def j0 : List Byte := [0x75, 0x27]
theorem j0_0 : ∀ feat, Dec feat j0 0 (FV7z.mk (.jcc 5) 64 [.rel 39] 2) := by dec_rfl

/-- The stretch at `17`. -/
def p1 : List Byte := [
  0x66, 0x0f, 0xef, 0xc0, 0x48, 0xc7, 0x43, 0x40, 0x00, 0x00, 0x00, 0x00, 0x0f, 0x11, 0x43, 0x60,
  0x0f, 0x11, 0x03, 0x0f, 0x11, 0x43, 0x10, 0x0f, 0x11, 0x43, 0x20, 0x0f, 0x11, 0x43, 0x30, 0x5b]

theorem p1_0 : ∀ feat, Dec feat p1 0 (FV7z.mk (.sse (SseMn.pxor)) 16 [.xmm 0, .xmm 0] 4) := by dec_rfl
theorem p1_4 : ∀ feat, Dec feat p1 4 (FV7z.mk .mov 64 [.mem (mg (some 3) none 1 64 64), .imm 64 0] 8) := by dec_rfl
theorem p1_12 : ∀ feat, Dec feat p1 12 (FV7z.mk (.sse (SseMn.movups)) 32 [.mem (mg (some 3) none 1 96 128), .xmm 0] 4) := by dec_rfl
theorem p1_16 : ∀ feat, Dec feat p1 16 (FV7z.mk (.sse (SseMn.movups)) 32 [.mem (mg (some 3) none 1 0 128), .xmm 0] 3) := by dec_rfl
theorem p1_19 : ∀ feat, Dec feat p1 19 (FV7z.mk (.sse (SseMn.movups)) 32 [.mem (mg (some 3) none 1 16 128), .xmm 0] 4) := by dec_rfl
theorem p1_23 : ∀ feat, Dec feat p1 23 (FV7z.mk (.sse (SseMn.movups)) 32 [.mem (mg (some 3) none 1 32 128), .xmm 0] 4) := by dec_rfl
theorem p1_27 : ∀ feat, Dec feat p1 27 (FV7z.mk (.sse (SseMn.movups)) 32 [.mem (mg (some 3) none 1 48 128), .xmm 0] 4) := by dec_rfl
theorem p1_31 : ∀ feat, Dec feat p1 31 (FV7z.mk .pop 64 [gr 64 3] 1) := by dec_rfl

/-- What the stretch does. -/
def o1 : List Op := [
  Op.vld 0 fun _ => 0,
  Op.sti 64 (some 3) none 1 64 0,
  Op.vs 16 (some 3) none 1 96,
  Op.vs 16 (some 3) none 1 0,
  Op.vs 16 (some 3) none 1 16,
  Op.vs 16 (some 3) none 1 32,
  Op.vs 16 (some 3) none 1 48,
  Op.pop 3]

theorem b1 (prof : Profile) : Blk prof p1 0 32 o1 :=
  .cons (p1_0 _) (OpI.vz_pxor) (by decide) <|
  .cons (p1_4 _) (OpI.sti (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p1_12 _) (OpI.vs_movups) (by decide) <|
  .cons (p1_16 _) (OpI.vs_movups) (by decide) <|
  .cons (p1_19 _) (OpI.vs_movups) (by decide) <|
  .cons (p1_23 _) (OpI.vs_movups) (by decide) <|
  .cons (p1_27 _) (OpI.vs_movups) (by decide) <|
  .cons (p1_31 _) (OpI.pop) (by decide) <|
  .nil 32

/-- The stretch at `56`. -/
def p2 : List Byte := [
  0x48, 0x8b, 0x7f, 0x48, 0x31, 0xf6]

theorem p2_0 : ∀ feat, Dec feat p2 0 (FV7z.mk .mov 64 [gr 64 7, .mem (mg (some 7) none 1 72 64)] 4) := by dec_rfl
theorem p2_4 : ∀ feat, Dec feat p2 4 (FV7z.mk .xor 32 [gr 32 6, Src.opd 32 (.r 6)] 2) := by dec_rfl

/-- What the stretch does. -/
def o2 : List Op := [
  Op.ld 64 7 (some 7) none 1 72,
  Op.xor 32 6 (.r 6)]

theorem b2 (prof : Profile) : Blk prof p2 0 6 o2 :=
  .cons (p2_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p2_4 _) (OpI.xor (.r 6) (.inl rfl)) (by decide) <|
  .nil 6

def j1 : List Byte := [0xeb, 0xcc]
theorem j1_0 : ∀ feat, Dec feat j1 0 (FV7z.mk .jmp 64 [.rel 18446744073709551564] 2) := by dec_rfl

end FV7z.Ckw
