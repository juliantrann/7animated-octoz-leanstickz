import FV7z.Lemmas.Sp
import FV7z.Lemmas.BlkOps3
/-!
# The stretches of straight-line code of `_dl_debug_initialize` (PLAN.md G3, startup)

Each distinct stretch between labels and jumps (`p*`, 8 of them) and each distinct jump (`j*`, 5) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.Dbg
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The stretch at `0`. -/
def p0 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0x48, 0x8d, 0x05, 0x15, 0xa0, 0x13, 0x00, 0x48, 0x85, 0xf6]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem p0_4 : ∀ feat, Dec feat p0 4 (FV7z.mk .lea 64 [gr 64 0, .mem (mrip 1286165 0)] 7) := by dec_rfl
theorem p0_11 : ∀ feat, Dec feat p0 11 (FV7z.mk .test 64 [gr 64 6, Src.opd 64 (.r 6)] 3) := by dec_rfl

/-- What the stretch does. -/
def o0 : List Op := [
  Op.nop,
  Op.mov 64 0 (.i 8029376),
  Op.test 64 6 (.r 6)]

theorem b0 (prof : Profile) : BlkA prof p0 (0x66e4a0 : Addr) 0 14 o0 :=
  .cons (p0_0 _) ((OpI.endbr).at _) (by decide) <|
  .cons (p0_4 _) (OpIA.lea_rip (by decide)) (by decide) <|
  .cons (p0_11 _) ((OpI.test (.r 6) (.inr rfl)).at _) (by decide) <|
  .nil 14

def j0 : List Byte := [0x74, 0x14]
theorem j0_0 : ∀ feat, Dec feat j0 0 (FV7z.mk (.jcc 4) 64 [.rel 20] 2) := by dec_rfl

/-- The stretch at `16`. -/
def p1 : List Byte := [
  0x48, 0x8d, 0x04, 0xf6, 0x48, 0x8d, 0x15, 0x85, 0x4f, 0x12, 0x00, 0x48, 0xc1, 0xe0, 0x04, 0x48,
  0x8d, 0x44, 0x02, 0x68]

theorem p1_0 : ∀ feat, Dec feat p1 0 (FV7z.mk .lea 64 [gr 64 0, .mem (mg (some 6) (some 6) 8 0 0)] 4) := by dec_rfl
theorem p1_4 : ∀ feat, Dec feat p1 4 (FV7z.mk .lea 64 [gr 64 2, .mem (mrip 1200005 0)] 7) := by dec_rfl
theorem p1_11 : ∀ feat, Dec feat p1 11 (FV7z.mk .shl 64 [gr 64 0, Src.opd 8 (.i 4)] 4) := by dec_rfl
theorem p1_15 : ∀ feat, Dec feat p1 15 (FV7z.mk .lea 64 [gr 64 0, .mem (mg (some 2) (some 0) 1 104 0)] 5) := by dec_rfl

/-- What the stretch does. -/
def o1 : List Op := [
  Op.lea 64 0 (some 6) (some 6) 8 0,
  Op.mov 64 2 (.i 7943232),
  Op.shl64 0 (.i 4),
  Op.lea 64 0 (some 2) (some 0) 1 104]

theorem b1 (prof : Profile) : BlkA prof p1 (0x66e4b0 : Addr) 0 20 o1 :=
  .cons (p1_0 _) ((OpI.lea (.inr rfl)).at _) (by decide) <|
  .cons (p1_4 _) (OpIA.lea_rip (by decide)) (by decide) <|
  .cons (p1_11 _) ((OpI.shl64 (.i 4)).at _) (by decide) <|
  .cons (p1_15 _) ((OpI.lea (.inr rfl)).at _) (by decide) <|
  .nil 20

/-- The stretch at `36`. -/
def p2 : List Byte := [
  0x48, 0x83, 0x78, 0x08, 0x00]

theorem p2_0 : ∀ feat, Dec feat p2 0 (FV7z.mk .cmp 64 [.mem (mg (some 0) none 1 8 64), .imm 64 0] 5) := by dec_rfl

/-- What the stretch does. -/
def o2 : List Op := [
  Op.cmpmi 64 (some 0) none 1 8 0]

theorem b2 (prof : Profile) : Blk prof p2 0 5 o2 :=
  .cons (p2_0 _) (OpI.cmpmi64) (by decide) <|
  .nil 5

def j1 : List Byte := [0x74, 0x3d]
theorem j1_0 : ∀ feat, Dec feat j1 0 (FV7z.mk (.jcc 4) 64 [.rel 61] 2) := by dec_rfl

/-- The stretch at `43`. -/
def p3 : List Byte := [
  0x48, 0x85, 0xff]

theorem p3_0 : ∀ feat, Dec feat p3 0 (FV7z.mk .test 64 [gr 64 7, Src.opd 64 (.r 7)] 3) := by dec_rfl

/-- What the stretch does. -/
def o3 : List Op := [
  Op.test 64 7 (.r 7)]

theorem b3 (prof : Profile) : Blk prof p3 0 3 o3 :=
  .cons (p3_0 _) (OpI.test (.r 7) (.inr rfl)) (by decide) <|
  .nil 3

def j2 : List Byte := [0x74, 0x30]
theorem j2_0 : ∀ feat, Dec feat j2 0 (FV7z.mk (.jcc 4) 64 [.rel 48] 2) := by dec_rfl

/-- The stretch at `48`. -/
def p4 : List Byte := [
  0xc7, 0x00, 0x01, 0x00, 0x00, 0x00]

theorem p4_0 : ∀ feat, Dec feat p4 0 (FV7z.mk .mov 32 [.mem (mg (some 0) none 1 0 32), .imm 32 1] 6) := by dec_rfl

/-- What the stretch does. -/
def o4 : List Op := [
  Op.sti 32 (some 0) none 1 0 1]

theorem b4 (prof : Profile) : Blk prof p4 0 6 o4 :=
  .cons (p4_0 _) (OpI.sti (.inr (.inr (.inl rfl)))) (by decide) <|
  .nil 6

/-- The stretch at `54`. -/
def p5 : List Byte := [
  0x48, 0x8d, 0x14, 0xf6, 0x48, 0x8d, 0x0d, 0x5f, 0x4f, 0x12, 0x00, 0x48, 0x89, 0x78, 0x20, 0x48,
  0xc1, 0xe2, 0x04, 0x48, 0x8b, 0x14, 0x11, 0x48, 0x8d, 0x0d, 0x9c, 0xff, 0xff, 0xff, 0x48, 0x89,
  0x48, 0x10, 0x48, 0x89, 0x50, 0x08]

theorem p5_0 : ∀ feat, Dec feat p5 0 (FV7z.mk .lea 64 [gr 64 2, .mem (mg (some 6) (some 6) 8 0 0)] 4) := by dec_rfl
theorem p5_4 : ∀ feat, Dec feat p5 4 (FV7z.mk .lea 64 [gr 64 1, .mem (mrip 1199967 0)] 7) := by dec_rfl
theorem p5_11 : ∀ feat, Dec feat p5 11 (FV7z.mk .mov 64 [.mem (mg (some 0) none 1 32 64), gr 64 7] 4) := by dec_rfl
theorem p5_15 : ∀ feat, Dec feat p5 15 (FV7z.mk .shl 64 [gr 64 2, Src.opd 8 (.i 4)] 4) := by dec_rfl
theorem p5_19 : ∀ feat, Dec feat p5 19 (FV7z.mk .mov 64 [gr 64 2, .mem (mg (some 1) (some 2) 1 0 64)] 4) := by dec_rfl
theorem p5_23 : ∀ feat, Dec feat p5 23 (FV7z.mk .lea 64 [gr 64 1, .mem (mrip 18446744073709551516 0)] 7) := by dec_rfl
theorem p5_30 : ∀ feat, Dec feat p5 30 (FV7z.mk .mov 64 [.mem (mg (some 0) none 1 16 64), gr 64 1] 4) := by dec_rfl
theorem p5_34 : ∀ feat, Dec feat p5 34 (FV7z.mk .mov 64 [.mem (mg (some 0) none 1 8 64), gr 64 2] 4) := by dec_rfl

/-- What the stretch does. -/
def o5 : List Op := [
  Op.lea 64 2 (some 6) (some 6) 8 0,
  Op.mov 64 1 (.i 7943232),
  Op.st 64 (some 0) none 1 32 7,
  Op.shl64 2 (.i 4),
  Op.ld 64 2 (some 1) (some 2) 1 0,
  Op.mov 64 1 (.i 6743184),
  Op.st 64 (some 0) none 1 16 1,
  Op.st 64 (some 0) none 1 8 2]

theorem b5 (prof : Profile) : BlkA prof p5 (0x66e4d6 : Addr) 0 38 o5 :=
  .cons (p5_0 _) ((OpI.lea (.inr rfl)).at _) (by decide) <|
  .cons (p5_4 _) (OpIA.lea_rip (by decide)) (by decide) <|
  .cons (p5_11 _) ((OpI.st (.inr (.inr (.inr rfl)))).at _) (by decide) <|
  .cons (p5_15 _) ((OpI.shl64 (.i 4)).at _) (by decide) <|
  .cons (p5_19 _) ((OpI.ld (.inr rfl)).at _) (by decide) <|
  .cons (p5_23 _) (OpIA.lea_rip (by decide)) (by decide) <|
  .cons (p5_30 _) ((OpI.st (.inr (.inr (.inr rfl)))).at _) (by decide) <|
  .cons (p5_34 _) ((OpI.st (.inr (.inr (.inr rfl)))).at _) (by decide) <|
  .nil 38

/-- The stretch at `104`. -/
def p6 : List Byte := [
  0xc7, 0x00, 0x01, 0x00, 0x00, 0x00, 0x48, 0x85, 0xff]

theorem p6_0 : ∀ feat, Dec feat p6 0 (FV7z.mk .mov 32 [.mem (mg (some 0) none 1 0 32), .imm 32 1] 6) := by dec_rfl
theorem p6_6 : ∀ feat, Dec feat p6 6 (FV7z.mk .test 64 [gr 64 7, Src.opd 64 (.r 7)] 3) := by dec_rfl

/-- What the stretch does. -/
def o6 : List Op := [
  Op.sti 32 (some 0) none 1 0 1,
  Op.test 64 7 (.r 7)]

theorem b6 (prof : Profile) : Blk prof p6 0 9 o6 :=
  .cons (p6_0 _) (OpI.sti (.inr (.inr (.inl rfl)))) (by decide) <|
  .cons (p6_6 _) (OpI.test (.r 7) (.inr rfl)) (by decide) <|
  .nil 9

def j3 : List Byte := [0x75, 0xc3]
theorem j3_0 : ∀ feat, Dec feat j3 0 (FV7z.mk (.jcc 5) 64 [.rel 18446744073709551555] 2) := by dec_rfl

/-- The stretch at `115`. -/
def p7 : List Byte := [
  0x48, 0x8b, 0x3d, 0xc6, 0x9f, 0x13, 0x00]

theorem p7_0 : ∀ feat, Dec feat p7 0 (FV7z.mk .mov 64 [gr 64 7, .mem (mrip 1286086 64)] 7) := by dec_rfl

/-- What the stretch does. -/
def o7 : List Op := [
  Op.lda 64 7 8029408]

theorem b7 (prof : Profile) : BlkA prof p7 (0x66e513 : Addr) 0 7 o7 :=
  .cons (p7_0 _) (OpIA.ld_rip (.inr rfl) (by decide)) (by decide) <|
  .nil 7

def j4 : List Byte := [0xeb, 0xba]
theorem j4_0 : ∀ feat, Dec feat j4 0 (FV7z.mk .jmp 64 [.rel 18446744073709551546] 2) := by dec_rfl

end FV7z.Dbg
