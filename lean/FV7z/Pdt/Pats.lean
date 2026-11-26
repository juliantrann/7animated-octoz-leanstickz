import FV7z.Lemmas.Sp
import FV7z.Lemmas.CmpMi16
import FV7z.Lemmas.BlkOps7
import FV7z.Lemmas.BlkOps2
/-!
# The stretches of straight-line code of `CPropVariant::Detach` (PLAN.md §M, M1)

Each distinct stretch between labels and jumps (`p*`, 5 of them) and each distinct jump (`j*`, 3) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.Pdt
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The stretch at `0`. -/
def p0 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0x55, 0x48, 0x89, 0xfd, 0x53, 0x48, 0x89, 0xf3, 0x48, 0x83, 0xec, 0x08,
  0x66, 0x83, 0x3e, 0x00]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem p0_4 : ∀ feat, Dec feat p0 4 (FV7z.mk .push 64 [gr 64 5] 1) := by dec_rfl
theorem p0_5 : ∀ feat, Dec feat p0 5 (FV7z.mk .mov 64 [gr 64 5, Src.opd 64 (.r 7)] 3) := by dec_rfl
theorem p0_8 : ∀ feat, Dec feat p0 8 (FV7z.mk .push 64 [gr 64 3] 1) := by dec_rfl
theorem p0_9 : ∀ feat, Dec feat p0 9 (FV7z.mk .mov 64 [gr 64 3, Src.opd 64 (.r 6)] 3) := by dec_rfl
theorem p0_12 : ∀ feat, Dec feat p0 12 (FV7z.mk .sub 64 [gr 64 4, Src.opd 64 (.i 8)] 4) := by dec_rfl
theorem p0_16 : ∀ feat, Dec feat p0 16 (FV7z.mk .cmp 16 [.mem (mg (some 6) none 1 0 16), .imm 16 0] 4) := by dec_rfl

/-- What the stretch does. -/
def o0 : List Op := [
  Op.nop,
  Op.push 5,
  Op.mov 64 5 (.r 7),
  Op.push 3,
  Op.mov 64 3 (.r 6),
  Op.sub 64 4 (.i 8),
  Op.cmpmi 16 (some 6) none 1 0 0]

theorem b0 (prof : Profile) : Blk prof p0 0 20 o0 :=
  .cons (p0_0 _) (OpI.endbr) (by decide) <|
  .cons (p0_4 _) (OpI.push) (by decide) <|
  .cons (p0_5 _) (OpI.mov (.r 7) (.inr rfl)) (by decide) <|
  .cons (p0_8 _) (OpI.push) (by decide) <|
  .cons (p0_9 _) (OpI.mov (.r 6) (.inr rfl)) (by decide) <|
  .cons (p0_12 _) (OpI.sub (.i 8) (.inr rfl)) (by decide) <|
  .cons (p0_16 _) (OpI.cmpmi16) (by decide) <|
  .nil 20

def j0 : List Byte := [0x75, 0x1a]
theorem j0_0 : ∀ feat, Dec feat j0 0 (FV7z.mk (.jcc 5) 64 [.rel 26] 2) := by dec_rfl

/-- The stretch at `22`. -/
def p1 : List Byte := [
  0xf3, 0x0f, 0x6f, 0x45, 0x00, 0x31, 0xc0, 0x0f, 0x11, 0x03, 0xc7, 0x45, 0x00, 0x00, 0x00, 0x00,
  0x00]

theorem p1_0 : ∀ feat, Dec feat p1 0 (FV7z.mk (.sse (SseMn.movdqu)) 32 [.xmm 0, .mem (mg (some 5) none 1 0 128)] 5) := by dec_rfl
theorem p1_5 : ∀ feat, Dec feat p1 5 (FV7z.mk .xor 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl
theorem p1_7 : ∀ feat, Dec feat p1 7 (FV7z.mk (.sse (SseMn.movups)) 32 [.mem (mg (some 3) none 1 0 128), .xmm 0] 3) := by dec_rfl
theorem p1_10 : ∀ feat, Dec feat p1 10 (FV7z.mk .mov 32 [.mem (mg (some 5) none 1 0 32), .imm 32 0] 7) := by dec_rfl

/-- What the stretch does. -/
def o1 : List Op := [
  Op.vl 16 (some 5) none 1 0,
  Op.xor 32 0 (.r 0),
  Op.vs 16 (some 3) none 1 0,
  Op.sti 32 (some 5) none 1 0 0]

theorem b1 (prof : Profile) : Blk prof p1 0 17 o1 :=
  .cons (p1_0 _) (OpI.vl_movdqu) (by decide) <|
  .cons (p1_5 _) (OpI.xor (.r 0) (.inl rfl)) (by decide) <|
  .cons (p1_7 _) (OpI.vs_movups) (by decide) <|
  .cons (p1_10 _) (OpI.sti (.inr (.inr (.inl rfl)))) (by decide) <|
  .nil 17

/-- The stretch at `39`. -/
def p2 : List Byte := [
  0x48, 0x83, 0xc4, 0x08, 0x5b, 0x5d]

theorem p2_0 : ∀ feat, Dec feat p2 0 (FV7z.mk .add 64 [gr 64 4, Src.opd 64 (.i 8)] 4) := by dec_rfl
theorem p2_4 : ∀ feat, Dec feat p2 4 (FV7z.mk .pop 64 [gr 64 3] 1) := by dec_rfl
theorem p2_5 : ∀ feat, Dec feat p2 5 (FV7z.mk .pop 64 [gr 64 5] 1) := by dec_rfl

/-- What the stretch does. -/
def o2 : List Op := [
  Op.add 64 4 (.i 8),
  Op.pop 3,
  Op.pop 5]

theorem b2 (prof : Profile) : Blk prof p2 0 6 o2 :=
  .cons (p2_0 _) (OpI.add (.i 8) (.inr rfl)) (by decide) <|
  .cons (p2_4 _) (OpI.pop) (by decide) <|
  .cons (p2_5 _) (OpI.pop) (by decide) <|
  .nil 6

/-- The stretch at `48`. -/
def p3 : List Byte := [
  0x48, 0x89, 0xf7]

theorem p3_0 : ∀ feat, Dec feat p3 0 (FV7z.mk .mov 64 [gr 64 7, Src.opd 64 (.r 6)] 3) := by dec_rfl

/-- What the stretch does. -/
def o3 : List Op := [
  Op.mov 64 7 (.r 6)]

theorem b3 (prof : Profile) : Blk prof p3 0 3 o3 :=
  .cons (p3_0 _) (OpI.mov (.r 6) (.inr rfl)) (by decide) <|
  .nil 3

/-- The stretch at `56`. -/
def p4 : List Byte := [
  0x85, 0xc0]

theorem p4_0 : ∀ feat, Dec feat p4 0 (FV7z.mk .test 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl

/-- What the stretch does. -/
def o4 : List Op := [
  Op.test 32 0 (.r 0)]

theorem b4 (prof : Profile) : Blk prof p4 0 2 o4 :=
  .cons (p4_0 _) (OpI.test (.r 0) (.inl rfl)) (by decide) <|
  .nil 2

def j1 : List Byte := [0x79, 0xda]
theorem j1_0 : ∀ feat, Dec feat j1 0 (FV7z.mk (.jcc 9) 64 [.rel 18446744073709551578] 2) := by dec_rfl

def j2 : List Byte := [0xeb, 0xe9]
theorem j2_0 : ∀ feat, Dec feat j2 0 (FV7z.mk .jmp 64 [.rel 18446744073709551593] 2) := by dec_rfl

end FV7z.Pdt
