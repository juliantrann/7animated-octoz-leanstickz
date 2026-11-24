import FV7z.Lemmas.SpFs
import FV7z.Lemmas.BlkOps19
import FV7z.Lemmas.BlkOps7
import FV7z.Lemmas.BlkOps6
import FV7z.Lemmas.BlkOps2
/-!
# The stretches of straight-line code of `__pthread_mutex_init` (PLAN.md G3, constructors)

Each distinct stretch between labels and jumps (`p*`, 5 of them) and each distinct jump (`j*`, 3) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.Mxi
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The stretch at `0`. -/
def p0 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0x41, 0x55, 0x41, 0x54, 0x55, 0x53, 0x48, 0x89, 0xfb, 0x48, 0x83, 0xec,
  0x18, 0x64, 0x48, 0x8b, 0x04, 0x25, 0x28, 0x00, 0x00, 0x00, 0x48, 0x89, 0x44, 0x24, 0x08, 0x31,
  0xc0, 0x48, 0x85, 0xf6]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem p0_4 : ∀ feat, Dec feat p0 4 (FV7z.mk .push 64 [gr 64 13] 2) := by dec_rfl
theorem p0_6 : ∀ feat, Dec feat p0 6 (FV7z.mk .push 64 [gr 64 12] 2) := by dec_rfl
theorem p0_8 : ∀ feat, Dec feat p0 8 (FV7z.mk .push 64 [gr 64 5] 1) := by dec_rfl
theorem p0_9 : ∀ feat, Dec feat p0 9 (FV7z.mk .push 64 [gr 64 3] 1) := by dec_rfl
theorem p0_10 : ∀ feat, Dec feat p0 10 (FV7z.mk .mov 64 [gr 64 3, Src.opd 64 (.r 7)] 3) := by dec_rfl
theorem p0_13 : ∀ feat, Dec feat p0 13 (FV7z.mk .sub 64 [gr 64 4, Src.opd 64 (.i 24)] 4) := by dec_rfl
theorem p0_17 : ∀ feat, Dec feat p0 17 (FV7z.mk .mov 64 [gr 64 0, .mem (mf none none 1 40 64)] 9) := by dec_rfl
theorem p0_26 : ∀ feat, Dec feat p0 26 (FV7z.mk .mov 64 [.mem (mg (some 4) none 1 8 64), gr 64 0] 5) := by dec_rfl
theorem p0_31 : ∀ feat, Dec feat p0 31 (FV7z.mk .xor 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl
theorem p0_33 : ∀ feat, Dec feat p0 33 (FV7z.mk .test 64 [gr 64 6, Src.opd 64 (.r 6)] 3) := by dec_rfl

/-- What the stretch does. -/
def o0 (fb : Addr) : List Op := [
  Op.nop,
  Op.push 13,
  Op.push 12,
  Op.push 5,
  Op.push 3,
  Op.mov 64 3 (.r 7),
  Op.sub 64 4 (.i 24),
  Op.ldf fb 64 0 none none 1 40,
  Op.st 64 (some 4) none 1 8 0,
  Op.xor 32 0 (.r 0),
  Op.test 64 6 (.r 6)]

theorem b0 (prof : Profile) (fb : Addr) : BlkF prof p0 (0x5fbb20 : Addr) fb 0 36 (o0 fb) :=
  .cons (p0_0 _) (((OpI.endbr).at _).fs _) (by decide) <|
  .cons (p0_4 _) (((OpI.push).at _).fs _) (by decide) <|
  .cons (p0_6 _) (((OpI.push).at _).fs _) (by decide) <|
  .cons (p0_8 _) (((OpI.push).at _).fs _) (by decide) <|
  .cons (p0_9 _) (((OpI.push).at _).fs _) (by decide) <|
  .cons (p0_10 _) (((OpI.mov (.r 7) (.inr rfl)).at _).fs _) (by decide) <|
  .cons (p0_13 _) (((OpI.sub (.i 24) (.inr rfl)).at _).fs _) (by decide) <|
  .cons (p0_17 _) (OpIF.ldf (.inr rfl)) (by decide) <|
  .cons (p0_26 _) (((OpI.st (.inr (.inr (.inr rfl)))).at _).fs _) (by decide) <|
  .cons (p0_31 _) (((OpI.xor (.r 0) (.inl rfl)).at _).fs _) (by decide) <|
  .cons (p0_33 _) (((OpI.test (.r 6) (.inr rfl)).at _).fs _) (by decide) <|
  .nil 36

def j0 : List Byte := [0x0f, 0x84, 0xc6, 0x00, 0x00, 0x00]
theorem j0_0 : ∀ feat, Dec feat j0 0 (FV7z.mk (.jcc 4) 64 [.rel 198] 6) := by dec_rfl

/-- The stretch at `134`. -/
def p1 : List Byte := [
  0x89, 0x6b, 0x10, 0x90, 0x31, 0xc0]

theorem p1_0 : ∀ feat, Dec feat p1 0 (FV7z.mk .mov 32 [.mem (mg (some 3) none 1 16 32), gr 32 5] 3) := by dec_rfl
theorem p1_3 : ∀ feat, Dec feat p1 3 (FV7z.mk .nop 32 [] 1) := by dec_rfl
theorem p1_4 : ∀ feat, Dec feat p1 4 (FV7z.mk .xor 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl

/-- What the stretch does. -/
def o1 : List Op := [
  Op.st 32 (some 3) none 1 16 5,
  Op.nop,
  Op.xor 32 0 (.r 0)]

theorem b1 (prof : Profile) : Blk prof p1 0 6 o1 :=
  .cons (p1_0 _) (OpI.st (.inr (.inr (.inl rfl)))) (by decide) <|
  .cons (p1_3 _) (OpI.nop) (by decide) <|
  .cons (p1_4 _) (OpI.xor (.r 0) (.inl rfl)) (by decide) <|
  .nil 6

/-- The stretch at `140`. -/
def p2 : List Byte := [
  0x48, 0x8b, 0x4c, 0x24, 0x08, 0x64, 0x48, 0x33, 0x0c, 0x25, 0x28, 0x00, 0x00, 0x00]

theorem p2_0 : ∀ feat, Dec feat p2 0 (FV7z.mk .mov 64 [gr 64 1, .mem (mg (some 4) none 1 8 64)] 5) := by dec_rfl
theorem p2_5 : ∀ feat, Dec feat p2 5 (FV7z.mk .xor 64 [gr 64 1, .mem (mf none none 1 40 64)] 9) := by dec_rfl

/-- What the stretch does. -/
def o2 (fb : Addr) : List Op := [
  Op.ld 64 1 (some 4) none 1 8,
  Op.xormf fb 64 1 none none 1 40]

theorem b2 (prof : Profile) (fb : Addr) : BlkF prof p2 (0x5fbbac : Addr) fb 0 14 (o2 fb) :=
  .cons (p2_0 _) (((OpI.ld (.inr rfl)).at _).fs _) (by decide) <|
  .cons (p2_5 _) (OpIF.xormf (.inr rfl)) (by decide) <|
  .nil 14

def j1 : List Byte := [0x0f, 0x85, 0x38, 0x01, 0x00, 0x00]
theorem j1_0 : ∀ feat, Dec feat j1 0 (FV7z.mk (.jcc 5) 64 [.rel 312] 6) := by dec_rfl

/-- The stretch at `160`. -/
def p3 : List Byte := [
  0x48, 0x83, 0xc4, 0x18, 0x5b, 0x5d, 0x41, 0x5c, 0x41, 0x5d]

theorem p3_0 : ∀ feat, Dec feat p3 0 (FV7z.mk .add 64 [gr 64 4, Src.opd 64 (.i 24)] 4) := by dec_rfl
theorem p3_4 : ∀ feat, Dec feat p3 4 (FV7z.mk .pop 64 [gr 64 3] 1) := by dec_rfl
theorem p3_5 : ∀ feat, Dec feat p3 5 (FV7z.mk .pop 64 [gr 64 5] 1) := by dec_rfl
theorem p3_6 : ∀ feat, Dec feat p3 6 (FV7z.mk .pop 64 [gr 64 12] 2) := by dec_rfl
theorem p3_8 : ∀ feat, Dec feat p3 8 (FV7z.mk .pop 64 [gr 64 13] 2) := by dec_rfl

/-- What the stretch does. -/
def o3 : List Op := [
  Op.add 64 4 (.i 24),
  Op.pop 3,
  Op.pop 5,
  Op.pop 12,
  Op.pop 13]

theorem b3 (prof : Profile) : Blk prof p3 0 10 o3 :=
  .cons (p3_0 _) (OpI.add (.i 24) (.inr rfl)) (by decide) <|
  .cons (p3_4 _) (OpI.pop) (by decide) <|
  .cons (p3_5 _) (OpI.pop) (by decide) <|
  .cons (p3_6 _) (OpI.pop) (by decide) <|
  .cons (p3_8 _) (OpI.pop) (by decide) <|
  .nil 10

/-- The stretch at `240`. -/
def p4 : List Byte := [
  0x66, 0x0f, 0xef, 0xc0, 0x48, 0xc7, 0x47, 0x20, 0x00, 0x00, 0x00, 0x00, 0x31, 0xed, 0x0f, 0x11,
  0x07, 0x0f, 0x11, 0x47, 0x10]

theorem p4_0 : ∀ feat, Dec feat p4 0 (FV7z.mk (.sse (SseMn.pxor)) 16 [.xmm 0, .xmm 0] 4) := by dec_rfl
theorem p4_4 : ∀ feat, Dec feat p4 4 (FV7z.mk .mov 64 [.mem (mg (some 7) none 1 32 64), .imm 64 0] 8) := by dec_rfl
theorem p4_12 : ∀ feat, Dec feat p4 12 (FV7z.mk .xor 32 [gr 32 5, Src.opd 32 (.r 5)] 2) := by dec_rfl
theorem p4_14 : ∀ feat, Dec feat p4 14 (FV7z.mk (.sse (SseMn.movups)) 32 [.mem (mg (some 7) none 1 0 128), .xmm 0] 3) := by dec_rfl
theorem p4_17 : ∀ feat, Dec feat p4 17 (FV7z.mk (.sse (SseMn.movups)) 32 [.mem (mg (some 7) none 1 16 128), .xmm 0] 4) := by dec_rfl

/-- What the stretch does. -/
def o4 : List Op := [
  Op.vld 0 fun _ => 0,
  Op.sti 64 (some 7) none 1 32 0,
  Op.xor 32 5 (.r 5),
  Op.vs 16 (some 7) none 1 0,
  Op.vs 16 (some 7) none 1 16]

theorem b4 (prof : Profile) : Blk prof p4 0 21 o4 :=
  .cons (p4_0 _) (OpI.vz_pxor) (by decide) <|
  .cons (p4_4 _) (OpI.sti (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p4_12 _) (OpI.xor (.r 5) (.inl rfl)) (by decide) <|
  .cons (p4_14 _) (OpI.vs_movups) (by decide) <|
  .cons (p4_17 _) (OpI.vs_movups) (by decide) <|
  .nil 21

def j2 : List Byte := [0xe9, 0x7c, 0xff, 0xff, 0xff]
theorem j2_0 : ∀ feat, Dec feat j2 0 (FV7z.mk .jmp 64 [.rel 18446744073709551484] 5) := by dec_rfl

end FV7z.Mxi
