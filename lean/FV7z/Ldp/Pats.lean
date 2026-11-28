import FV7z.Lemmas.Sp
import FV7z.Lemmas.BlkOps2
/-!
# The stretches of straight-line code of `NCompress::NLzma::CDecoder::SetDecoderProperties2` (PLAN.md §M, M1)

Each distinct stretch between labels and jumps (`p*`, 6 of them) and each distinct jump (`j*`, 2) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.Ldp
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The stretch at `0`. -/
def p0 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0x55, 0x48, 0xc7, 0xc1, 0xe0, 0x7a, 0x77, 0x00, 0x48, 0x89, 0xfd, 0x48,
  0x8d, 0xbf, 0x80, 0x00, 0x00, 0x00]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem p0_4 : ∀ feat, Dec feat p0 4 (FV7z.mk .push 64 [gr 64 5] 1) := by dec_rfl
theorem p0_5 : ∀ feat, Dec feat p0 5 (FV7z.mk .mov 64 [gr 64 1, Src.opd 64 (.i 7830240)] 7) := by dec_rfl
theorem p0_12 : ∀ feat, Dec feat p0 12 (FV7z.mk .mov 64 [gr 64 5, Src.opd 64 (.r 7)] 3) := by dec_rfl
theorem p0_15 : ∀ feat, Dec feat p0 15 (FV7z.mk .lea 64 [gr 64 7, .mem (mg (some 7) none 1 128 0)] 7) := by dec_rfl

/-- What the stretch does. -/
def o0 : List Op := [
  Op.nop,
  Op.push 5,
  Op.mov 64 1 (.i 7830240),
  Op.mov 64 5 (.r 7),
  Op.lea 64 7 (some 7) none 1 128]

theorem b0 (prof : Profile) : Blk prof p0 0 22 o0 :=
  .cons (p0_0 _) (OpI.endbr) (by decide) <|
  .cons (p0_4 _) (OpI.push) (by decide) <|
  .cons (p0_5 _) (OpI.mov (.i 7830240) (.inr rfl)) (by decide) <|
  .cons (p0_12 _) (OpI.mov (.r 7) (.inr rfl)) (by decide) <|
  .cons (p0_15 _) (OpI.lea (.inr rfl)) (by decide) <|
  .nil 22

/-- The stretch at `27`. -/
def p1 : List Byte := [
  0x83, 0xf8, 0x05]

theorem p1_0 : ∀ feat, Dec feat p1 0 (FV7z.mk .cmp 32 [gr 32 0, Src.opd 32 (.i 5)] 3) := by dec_rfl

/-- What the stretch does. -/
def o1 : List Op := [
  Op.cmp 32 0 (.i 5)]

theorem b1 (prof : Profile) : Blk prof p1 0 3 o1 :=
  .cons (p1_0 _) (OpI.cmp (.i 5) (.inl rfl)) (by decide) <|
  .nil 3

def j0 : List Byte := [0x77, 0x18]
theorem j0_0 : ∀ feat, Dec feat j0 0 (FV7z.mk (.jcc 7) 64 [.rel 24] 2) := by dec_rfl

/-- The stretch at `32`. -/
def p2 : List Byte := [
  0x89, 0xc0, 0x48, 0x8d, 0x15, 0x87, 0x6b, 0x16, 0x00, 0x8b, 0x04, 0x82, 0x85, 0xc0]

theorem p2_0 : ∀ feat, Dec feat p2 0 (FV7z.mk .mov 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl
theorem p2_2 : ∀ feat, Dec feat p2 2 (FV7z.mk .lea 64 [gr 64 2, .mem (mrip 1469319 0)] 7) := by dec_rfl
theorem p2_9 : ∀ feat, Dec feat p2 9 (FV7z.mk .mov 32 [gr 32 0, .mem (mg (some 2) (some 0) 4 0 32)] 3) := by dec_rfl
theorem p2_12 : ∀ feat, Dec feat p2 12 (FV7z.mk .test 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl

/-- What the stretch does. -/
def o2 : List Op := [
  Op.mov 32 0 (.r 0),
  Op.mov 64 2 (.i 7235776),
  Op.ld 32 0 (some 2) (some 0) 4 0,
  Op.test 32 0 (.r 0)]

theorem b2 (prof : Profile) : BlkA prof p2 (0x57fd30 : Addr) 0 14 o2 :=
  .cons (p2_0 _) ((OpI.mov (.r 0) (.inl rfl)).at _) (by decide) <|
  .cons (p2_2 _) (OpIA.lea_rip (by decide)) (by decide) <|
  .cons (p2_9 _) ((OpI.ld (.inl rfl)).at _) (by decide) <|
  .cons (p2_12 _) ((OpI.test (.r 0) (.inl rfl)).at _) (by decide) <|
  .nil 14

def j1 : List Byte := [0x74, 0x10]
theorem j1_0 : ∀ feat, Dec feat j1 0 (FV7z.mk (.jcc 4) 64 [.rel 16] 2) := by dec_rfl

/-- The stretch at `48`. -/
def p3 : List Byte := [
  0x5d]

theorem p3_0 : ∀ feat, Dec feat p3 0 (FV7z.mk .pop 64 [gr 64 5] 1) := by dec_rfl

/-- What the stretch does. -/
def o3 : List Op := [
  Op.pop 5]

theorem b3 (prof : Profile) : Blk prof p3 0 1 o3 :=
  .cons (p3_0 _) (OpI.pop) (by decide) <|
  .nil 1

/-- The stretch at `56`. -/
def p4 : List Byte := [
  0xb8, 0x05, 0x40, 0x00, 0x80, 0x5d]

theorem p4_0 : ∀ feat, Dec feat p4 0 (FV7z.mk .mov 32 [gr 32 0, Src.opd 32 (.i 2147500037)] 5) := by dec_rfl
theorem p4_5 : ∀ feat, Dec feat p4 5 (FV7z.mk .pop 64 [gr 64 5] 1) := by dec_rfl

/-- What the stretch does. -/
def o4 : List Op := [
  Op.mov 32 0 (.i 2147500037),
  Op.pop 5]

theorem b4 (prof : Profile) : Blk prof p4 0 6 o4 :=
  .cons (p4_0 _) (OpI.mov (.i 2147500037) (.inl rfl)) (by decide) <|
  .cons (p4_5 _) (OpI.pop) (by decide) <|
  .nil 6

/-- The stretch at `64`. -/
def p5 : List Byte := [
  0xc6, 0x45, 0x45, 0x01, 0x48, 0x89, 0xef]

theorem p5_0 : ∀ feat, Dec feat p5 0 (FV7z.mk .mov 8 [.mem (mg (some 5) none 1 69 8), .imm 8 1] 4) := by dec_rfl
theorem p5_4 : ∀ feat, Dec feat p5 4 (FV7z.mk .mov 64 [gr 64 7, Src.opd 64 (.r 5)] 3) := by dec_rfl

/-- What the stretch does. -/
def o5 : List Op := [
  Op.sti 8 (some 5) none 1 69 1,
  Op.mov 64 7 (.r 5)]

theorem b5 (prof : Profile) : Blk prof p5 0 7 o5 :=
  .cons (p5_0 _) (OpI.sti (.inl rfl)) (by decide) <|
  .cons (p5_4 _) (OpI.mov (.r 5) (.inr rfl)) (by decide) <|
  .nil 7

end FV7z.Ldp
