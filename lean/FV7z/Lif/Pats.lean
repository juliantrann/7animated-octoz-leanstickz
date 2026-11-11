import FV7z.Lemmas.Sp
import FV7z.Lemmas.BlkOps9
import FV7z.Lemmas.BlkOps2
/-!
# The stretches of straight-line code of `__libc_init_first` (PLAN.md G3, startup)

Each distinct stretch between labels and jumps (`p*`, 5 of them) and each distinct jump (`j*`, 3) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.Lif
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The stretch at `0`. -/
def p0 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0x48, 0xc7, 0xc0, 0x00, 0x00, 0x00, 0x00, 0x41, 0x55, 0x49, 0x89, 0xd5,
  0x41, 0x54, 0x49, 0x89, 0xf4, 0x55, 0x89, 0xfd, 0x48, 0x85, 0xc0]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem p0_4 : ∀ feat, Dec feat p0 4 (FV7z.mk .mov 64 [gr 64 0, Src.opd 64 (.i 0)] 7) := by dec_rfl
theorem p0_11 : ∀ feat, Dec feat p0 11 (FV7z.mk .push 64 [gr 64 13] 2) := by dec_rfl
theorem p0_13 : ∀ feat, Dec feat p0 13 (FV7z.mk .mov 64 [gr 64 13, Src.opd 64 (.r 2)] 3) := by dec_rfl
theorem p0_16 : ∀ feat, Dec feat p0 16 (FV7z.mk .push 64 [gr 64 12] 2) := by dec_rfl
theorem p0_18 : ∀ feat, Dec feat p0 18 (FV7z.mk .mov 64 [gr 64 12, Src.opd 64 (.r 6)] 3) := by dec_rfl
theorem p0_21 : ∀ feat, Dec feat p0 21 (FV7z.mk .push 64 [gr 64 5] 1) := by dec_rfl
theorem p0_22 : ∀ feat, Dec feat p0 22 (FV7z.mk .mov 32 [gr 32 5, Src.opd 32 (.r 7)] 2) := by dec_rfl
theorem p0_24 : ∀ feat, Dec feat p0 24 (FV7z.mk .test 64 [gr 64 0, Src.opd 64 (.r 0)] 3) := by dec_rfl

/-- What the stretch does. -/
def o0 : List Op := [
  Op.nop,
  Op.mov 64 0 (.i 0),
  Op.push 13,
  Op.mov 64 13 (.r 2),
  Op.push 12,
  Op.mov 64 12 (.r 6),
  Op.push 5,
  Op.mov 32 5 (.r 7),
  Op.test 64 0 (.r 0)]

theorem b0 (prof : Profile) : Blk prof p0 0 27 o0 :=
  .cons (p0_0 _) (OpI.endbr) (by decide) <|
  .cons (p0_4 _) (OpI.mov (.i 0) (.inr rfl)) (by decide) <|
  .cons (p0_11 _) (OpI.push) (by decide) <|
  .cons (p0_13 _) (OpI.mov (.r 2) (.inr rfl)) (by decide) <|
  .cons (p0_16 _) (OpI.push) (by decide) <|
  .cons (p0_18 _) (OpI.mov (.r 6) (.inr rfl)) (by decide) <|
  .cons (p0_21 _) (OpI.push) (by decide) <|
  .cons (p0_22 _) (OpI.mov (.r 7) (.inl rfl)) (by decide) <|
  .cons (p0_24 _) (OpI.test (.r 0) (.inr rfl)) (by decide) <|
  .nil 27

def j0 : List Byte := [0x74, 0x43]
theorem j0_0 : ∀ feat, Dec feat j0 0 (FV7z.mk (.jcc 4) 64 [.rel 67] 2) := by dec_rfl

/-- The stretch at `45`. -/
def p1 : List Byte := [
  0x89, 0x2d, 0x35, 0x64, 0x13, 0x00, 0x4c, 0x89, 0x25, 0x36, 0x64, 0x13, 0x00, 0x4c, 0x89, 0x2d,
  0xf7, 0x25, 0x13, 0x00]

theorem p1_0 : ∀ feat, Dec feat p1 0 (FV7z.mk .mov 32 [.mem (mrip 1270837 32), gr 32 5] 6) := by dec_rfl
theorem p1_6 : ∀ feat, Dec feat p1 6 (FV7z.mk .mov 64 [.mem (mrip 1270838 64), gr 64 12] 7) := by dec_rfl
theorem p1_13 : ∀ feat, Dec feat p1 13 (FV7z.mk .mov 64 [.mem (mrip 1254903 64), gr 64 13] 7) := by dec_rfl

/-- What the stretch does. -/
def o1 : List Op := [
  Op.sta 32 8029640 5,
  Op.sta 64 8029648 12,
  Op.sta 64 8013720 13]

theorem b1 (prof : Profile) : BlkA prof p1 (0x67218d : Addr) 0 20 o1 :=
  .cons (p1_0 _) (OpIA.st_rip (.inr (.inl rfl)) (by decide)) (by decide) <|
  .cons (p1_6 _) (OpIA.st_rip (.inr (.inr rfl)) (by decide)) (by decide) <|
  .cons (p1_13 _) (OpIA.st_rip (.inr (.inr rfl)) (by decide)) (by decide) <|
  .nil 20

/-- The stretch at `70`. -/
def p2 : List Byte := [
  0x4c, 0x89, 0xea, 0x4c, 0x89, 0xe6, 0x89, 0xef]

theorem p2_0 : ∀ feat, Dec feat p2 0 (FV7z.mk .mov 64 [gr 64 2, Src.opd 64 (.r 13)] 3) := by dec_rfl
theorem p2_3 : ∀ feat, Dec feat p2 3 (FV7z.mk .mov 64 [gr 64 6, Src.opd 64 (.r 12)] 3) := by dec_rfl
theorem p2_6 : ∀ feat, Dec feat p2 6 (FV7z.mk .mov 32 [gr 32 7, Src.opd 32 (.r 5)] 2) := by dec_rfl

/-- What the stretch does. -/
def o2 : List Op := [
  Op.mov 64 2 (.r 13),
  Op.mov 64 6 (.r 12),
  Op.mov 32 7 (.r 5)]

theorem b2 (prof : Profile) : Blk prof p2 0 8 o2 :=
  .cons (p2_0 _) (OpI.mov (.r 13) (.inr rfl)) (by decide) <|
  .cons (p2_3 _) (OpI.mov (.r 12) (.inr rfl)) (by decide) <|
  .cons (p2_6 _) (OpI.mov (.r 5) (.inl rfl)) (by decide) <|
  .nil 8

/-- The stretch at `83`. -/
def p3 : List Byte := [
  0x5d, 0x41, 0x5c, 0x41, 0x5d]

theorem p3_0 : ∀ feat, Dec feat p3 0 (FV7z.mk .pop 64 [gr 64 5] 1) := by dec_rfl
theorem p3_1 : ∀ feat, Dec feat p3 1 (FV7z.mk .pop 64 [gr 64 12] 2) := by dec_rfl
theorem p3_3 : ∀ feat, Dec feat p3 3 (FV7z.mk .pop 64 [gr 64 13] 2) := by dec_rfl

/-- What the stretch does. -/
def o3 : List Op := [
  Op.pop 5,
  Op.pop 12,
  Op.pop 13]

theorem b3 (prof : Profile) : Blk prof p3 0 5 o3 :=
  .cons (p3_0 _) (OpI.pop) (by decide) <|
  .cons (p3_1 _) (OpI.pop) (by decide) <|
  .cons (p3_3 _) (OpI.pop) (by decide) <|
  .nil 5

/-- The stretch at `96`. -/
def p4 : List Byte := [
  0x0f, 0xb7, 0x3d, 0xb9, 0x1a, 0x12, 0x00, 0x66, 0x3b, 0x3d, 0xfe, 0x11, 0x12, 0x00, 0xc7, 0x05,
  0xe8, 0x17, 0x12, 0x00, 0x00, 0x00, 0x00, 0x00]

theorem p4_0 : ∀ feat, Dec feat p4 0 (FV7z.mk .movzx 32 [gr 32 7, .mem (mrip 1186489 16)] 7) := by dec_rfl
theorem p4_7 : ∀ feat, Dec feat p4 7 (FV7z.mk .cmp 16 [gr 16 7, .mem (mrip 1184254 16)] 7) := by dec_rfl
theorem p4_14 : ∀ feat, Dec feat p4 14 (FV7z.mk .mov 32 [.mem (mrip 1185768 32), .imm 32 0] 10) := by dec_rfl

/-- What the stretch does. -/
def o4 : List Op := [
  Op.ldzxa 16 7 7945344,
  Op.cmpma 16 7 7943116,
  Op.stia 32 7944640 0]

theorem b4 (prof : Profile) : BlkA prof p4 (0x6721c0 : Addr) 0 24 o4 :=
  .cons (p4_0 _) (OpIA.ldzx_rip (.inr rfl) (by decide)) (by decide) <|
  .cons (p4_7 _) (OpIA.cmpm_rip (.inl rfl) (by decide)) (by decide) <|
  .cons (p4_14 _) (OpIA.sti_rip (.inr (.inl rfl)) (by decide)) (by decide) <|
  .nil 24

def j1 : List Byte := [0x74, 0xb3]
theorem j1_0 : ∀ feat, Dec feat j1 0 (FV7z.mk (.jcc 4) 64 [.rel 18446744073709551539] 2) := by dec_rfl

def j2 : List Byte := [0xeb, 0xac]
theorem j2_0 : ∀ feat, Dec feat j2 0 (FV7z.mk .jmp 64 [.rel 18446744073709551532] 2) := by dec_rfl

end FV7z.Lif
