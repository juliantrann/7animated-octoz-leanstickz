import FV7z.Lemmas.SpFs
import FV7z.Lemmas.BlkOps7
import FV7z.Lemmas.BlkOps6
import FV7z.Lemmas.BlkOps2
/-!
# The stretches of straight-line code of `__libc_sigaction` (PLAN.md G3, startup)

Each distinct stretch between labels and jumps (`p*`, 9 of them) and each distinct jump (`j*`, 6) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.Sga
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The stretch at `0`. -/
def p0 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0x48, 0x81, 0xec, 0x48, 0x01, 0x00, 0x00, 0x49, 0x89, 0xd0, 0x64, 0x48,
  0x8b, 0x04, 0x25, 0x28, 0x00, 0x00, 0x00, 0x48, 0x89, 0x84, 0x24, 0x38, 0x01, 0x00, 0x00, 0x31,
  0xc0, 0x48, 0x85, 0xf6]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem p0_4 : ∀ feat, Dec feat p0 4 (FV7z.mk .sub 64 [gr 64 4, Src.opd 64 (.i 328)] 7) := by dec_rfl
theorem p0_11 : ∀ feat, Dec feat p0 11 (FV7z.mk .mov 64 [gr 64 8, Src.opd 64 (.r 2)] 3) := by dec_rfl
theorem p0_14 : ∀ feat, Dec feat p0 14 (FV7z.mk .mov 64 [gr 64 0, .mem (mf none none 1 40 64)] 9) := by dec_rfl
theorem p0_23 : ∀ feat, Dec feat p0 23 (FV7z.mk .mov 64 [.mem (mg (some 4) none 1 312 64), gr 64 0] 8) := by dec_rfl
theorem p0_31 : ∀ feat, Dec feat p0 31 (FV7z.mk .xor 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl
theorem p0_33 : ∀ feat, Dec feat p0 33 (FV7z.mk .test 64 [gr 64 6, Src.opd 64 (.r 6)] 3) := by dec_rfl

/-- What the stretch does. -/
def o0 (fb : Addr) : List Op := [
  Op.nop,
  Op.sub 64 4 (.i 328),
  Op.mov 64 8 (.r 2),
  Op.ldf fb 64 0 none none 1 40,
  Op.st 64 (some 4) none 1 312 0,
  Op.xor 32 0 (.r 0),
  Op.test 64 6 (.r 6)]

theorem b0 (prof : Profile) (fb : Addr) : BlkF prof p0 (0x600ff0 : Addr) fb 0 36 (o0 fb) :=
  .cons (p0_0 _) (((OpI.endbr).at _).fs _) (by decide) <|
  .cons (p0_4 _) (((OpI.sub (.i 328) (.inr rfl)).at _).fs _) (by decide) <|
  .cons (p0_11 _) (((OpI.mov (.r 2) (.inr rfl)).at _).fs _) (by decide) <|
  .cons (p0_14 _) (OpIF.ldf (.inr rfl)) (by decide) <|
  .cons (p0_23 _) (((OpI.st (.inr (.inr (.inr rfl)))).at _).fs _) (by decide) <|
  .cons (p0_31 _) (((OpI.xor (.r 0) (.inl rfl)).at _).fs _) (by decide) <|
  .cons (p0_33 _) (((OpI.test (.r 6) (.inr rfl)).at _).fs _) (by decide) <|
  .nil 36

def j0 : List Byte := [0x0f, 0x84, 0x76, 0x01, 0x00, 0x00]
theorem j0_0 : ∀ feat, Dec feat j0 0 (FV7z.mk (.jcc 4) 64 [.rel 374] 6) := by dec_rfl

/-- The stretch at `42`. -/
def p1 : List Byte := [
  0x48, 0x8b, 0x06, 0xf3, 0x0f, 0x6f, 0x46, 0x08, 0x48, 0x8d, 0x94, 0x24, 0xa0, 0x00, 0x00, 0x00,
  0xf3, 0x0f, 0x6f, 0x4e, 0x18, 0xf3, 0x0f, 0x6f, 0x56, 0x28, 0xf3, 0x0f, 0x6f, 0x5e, 0x38, 0xf3,
  0x0f, 0x6f, 0x66, 0x48, 0x48, 0x89, 0x04, 0x24, 0x8b, 0x86, 0x88, 0x00, 0x00, 0x00, 0xf3, 0x0f,
  0x6f, 0x6e, 0x58, 0x0f, 0x11, 0x44, 0x24, 0x18, 0xf3, 0x0f, 0x6f, 0x76, 0x68, 0xf3, 0x0f, 0x6f,
  0x7e, 0x78, 0x0f, 0x11, 0x4c, 0x24, 0x28, 0x48, 0x89, 0xe6, 0x0d, 0x00, 0x00, 0x00, 0x04, 0x4d,
  0x85, 0xc0, 0x0f, 0x11, 0x54, 0x24, 0x38, 0x48, 0x98, 0x0f, 0x11, 0x5c, 0x24, 0x48, 0x48, 0x89,
  0x44, 0x24, 0x08, 0x48, 0xc7, 0xc0, 0xe0, 0x0f, 0x60, 0x00, 0x0f, 0x11, 0x64, 0x24, 0x58, 0x48,
  0x89, 0x44, 0x24, 0x10, 0xb8, 0x00, 0x00, 0x00, 0x00, 0x48, 0x0f, 0x44, 0xd0, 0x0f, 0x11, 0x6c,
  0x24, 0x68, 0x0f, 0x11, 0x74, 0x24, 0x78, 0x0f, 0x11, 0xbc, 0x24, 0x88, 0x00, 0x00, 0x00]

theorem p1_0 : ∀ feat, Dec feat p1 0 (FV7z.mk .mov 64 [gr 64 0, .mem (mg (some 6) none 1 0 64)] 3) := by dec_rfl
theorem p1_3 : ∀ feat, Dec feat p1 3 (FV7z.mk (.sse (SseMn.movdqu)) 32 [.xmm 0, .mem (mg (some 6) none 1 8 128)] 5) := by dec_rfl
theorem p1_8 : ∀ feat, Dec feat p1 8 (FV7z.mk .lea 64 [gr 64 2, .mem (mg (some 4) none 1 160 0)] 8) := by dec_rfl
theorem p1_16 : ∀ feat, Dec feat p1 16 (FV7z.mk (.sse (SseMn.movdqu)) 32 [.xmm 1, .mem (mg (some 6) none 1 24 128)] 5) := by dec_rfl
theorem p1_21 : ∀ feat, Dec feat p1 21 (FV7z.mk (.sse (SseMn.movdqu)) 32 [.xmm 2, .mem (mg (some 6) none 1 40 128)] 5) := by dec_rfl
theorem p1_26 : ∀ feat, Dec feat p1 26 (FV7z.mk (.sse (SseMn.movdqu)) 32 [.xmm 3, .mem (mg (some 6) none 1 56 128)] 5) := by dec_rfl
theorem p1_31 : ∀ feat, Dec feat p1 31 (FV7z.mk (.sse (SseMn.movdqu)) 32 [.xmm 4, .mem (mg (some 6) none 1 72 128)] 5) := by dec_rfl
theorem p1_36 : ∀ feat, Dec feat p1 36 (FV7z.mk .mov 64 [.mem (mg (some 4) none 1 0 64), gr 64 0] 4) := by dec_rfl
theorem p1_40 : ∀ feat, Dec feat p1 40 (FV7z.mk .mov 32 [gr 32 0, .mem (mg (some 6) none 1 136 32)] 6) := by dec_rfl
theorem p1_46 : ∀ feat, Dec feat p1 46 (FV7z.mk (.sse (SseMn.movdqu)) 32 [.xmm 5, .mem (mg (some 6) none 1 88 128)] 5) := by dec_rfl
theorem p1_51 : ∀ feat, Dec feat p1 51 (FV7z.mk (.sse (SseMn.movups)) 32 [.mem (mg (some 4) none 1 24 128), .xmm 0] 5) := by dec_rfl
theorem p1_56 : ∀ feat, Dec feat p1 56 (FV7z.mk (.sse (SseMn.movdqu)) 32 [.xmm 6, .mem (mg (some 6) none 1 104 128)] 5) := by dec_rfl
theorem p1_61 : ∀ feat, Dec feat p1 61 (FV7z.mk (.sse (SseMn.movdqu)) 32 [.xmm 7, .mem (mg (some 6) none 1 120 128)] 5) := by dec_rfl
theorem p1_66 : ∀ feat, Dec feat p1 66 (FV7z.mk (.sse (SseMn.movups)) 32 [.mem (mg (some 4) none 1 40 128), .xmm 1] 5) := by dec_rfl
theorem p1_71 : ∀ feat, Dec feat p1 71 (FV7z.mk .mov 64 [gr 64 6, Src.opd 64 (.r 4)] 3) := by dec_rfl
theorem p1_74 : ∀ feat, Dec feat p1 74 (FV7z.mk .or 32 [gr 32 0, Src.opd 32 (.i 67108864)] 5) := by dec_rfl
theorem p1_79 : ∀ feat, Dec feat p1 79 (FV7z.mk .test 64 [gr 64 8, Src.opd 64 (.r 8)] 3) := by dec_rfl
theorem p1_82 : ∀ feat, Dec feat p1 82 (FV7z.mk (.sse (SseMn.movups)) 32 [.mem (mg (some 4) none 1 56 128), .xmm 2] 5) := by dec_rfl
theorem p1_87 : ∀ feat, Dec feat p1 87 (FV7z.mk .cbw 64 [] 2) := by dec_rfl
theorem p1_89 : ∀ feat, Dec feat p1 89 (FV7z.mk (.sse (SseMn.movups)) 32 [.mem (mg (some 4) none 1 72 128), .xmm 3] 5) := by dec_rfl
theorem p1_94 : ∀ feat, Dec feat p1 94 (FV7z.mk .mov 64 [.mem (mg (some 4) none 1 8 64), gr 64 0] 5) := by dec_rfl
theorem p1_99 : ∀ feat, Dec feat p1 99 (FV7z.mk .mov 64 [gr 64 0, Src.opd 64 (.i 6295520)] 7) := by dec_rfl
theorem p1_106 : ∀ feat, Dec feat p1 106 (FV7z.mk (.sse (SseMn.movups)) 32 [.mem (mg (some 4) none 1 88 128), .xmm 4] 5) := by dec_rfl
theorem p1_111 : ∀ feat, Dec feat p1 111 (FV7z.mk .mov 64 [.mem (mg (some 4) none 1 16 64), gr 64 0] 5) := by dec_rfl
theorem p1_116 : ∀ feat, Dec feat p1 116 (FV7z.mk .mov 32 [gr 32 0, Src.opd 32 (.i 0)] 5) := by dec_rfl
theorem p1_121 : ∀ feat, Dec feat p1 121 (FV7z.mk (.cmovcc 4) 64 [gr 64 2, gr 64 0] 4) := by dec_rfl
theorem p1_125 : ∀ feat, Dec feat p1 125 (FV7z.mk (.sse (SseMn.movups)) 32 [.mem (mg (some 4) none 1 104 128), .xmm 5] 5) := by dec_rfl
theorem p1_130 : ∀ feat, Dec feat p1 130 (FV7z.mk (.sse (SseMn.movups)) 32 [.mem (mg (some 4) none 1 120 128), .xmm 6] 5) := by dec_rfl
theorem p1_135 : ∀ feat, Dec feat p1 135 (FV7z.mk (.sse (SseMn.movups)) 32 [.mem (mg (some 4) none 1 136 128), .xmm 7] 8) := by dec_rfl

/-- What the stretch does. -/
def o1 : List Op := [
  Op.ld 64 0 (some 6) none 1 0,
  Op.vl 16 (some 6) none 1 8,
  Op.lea 64 2 (some 4) none 1 160,
  Op.vl 16 (some 6) none 1 24,
  Op.vl 16 (some 6) none 1 40,
  Op.vl 16 (some 6) none 1 56,
  Op.vl 16 (some 6) none 1 72,
  Op.st 64 (some 4) none 1 0 0,
  Op.ld 32 0 (some 6) none 1 136,
  Op.vl 16 (some 6) none 1 88,
  Op.vs 16 (some 4) none 1 24,
  Op.vl 16 (some 6) none 1 104,
  Op.vl 16 (some 6) none 1 120,
  Op.vs 16 (some 4) none 1 40,
  Op.mov 64 6 (.r 4),
  Op.or 32 0 (.i 67108864),
  Op.test 64 8 (.r 8),
  Op.vs 16 (some 4) none 1 56,
  Op.cdqe,
  Op.vs 16 (some 4) none 1 72,
  Op.st 64 (some 4) none 1 8 0,
  Op.mov 64 0 (.i 6295520),
  Op.vs 16 (some 4) none 1 88,
  Op.st 64 (some 4) none 1 16 0,
  Op.mov 32 0 (.i 0),
  Op.cmov64 4 2 0,
  Op.vs 16 (some 4) none 1 104,
  Op.vs 16 (some 4) none 1 120,
  Op.vs 16 (some 4) none 1 136]

theorem b1 (prof : Profile) : Blk prof p1 0 143 o1 :=
  .cons (p1_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p1_3 _) (OpI.vl_movdqu) (by decide) <|
  .cons (p1_8 _) (OpI.lea (.inr rfl)) (by decide) <|
  .cons (p1_16 _) (OpI.vl_movdqu) (by decide) <|
  .cons (p1_21 _) (OpI.vl_movdqu) (by decide) <|
  .cons (p1_26 _) (OpI.vl_movdqu) (by decide) <|
  .cons (p1_31 _) (OpI.vl_movdqu) (by decide) <|
  .cons (p1_36 _) (OpI.st (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p1_40 _) (OpI.ld (.inl rfl)) (by decide) <|
  .cons (p1_46 _) (OpI.vl_movdqu) (by decide) <|
  .cons (p1_51 _) (OpI.vs_movups) (by decide) <|
  .cons (p1_56 _) (OpI.vl_movdqu) (by decide) <|
  .cons (p1_61 _) (OpI.vl_movdqu) (by decide) <|
  .cons (p1_66 _) (OpI.vs_movups) (by decide) <|
  .cons (p1_71 _) (OpI.mov (.r 4) (.inr rfl)) (by decide) <|
  .cons (p1_74 _) (OpI.or (.i 67108864) (.inl rfl)) (by decide) <|
  .cons (p1_79 _) (OpI.test (.r 8) (.inr rfl)) (by decide) <|
  .cons (p1_82 _) (OpI.vs_movups) (by decide) <|
  .cons (p1_87 _) (OpI.cdqe) (by decide) <|
  .cons (p1_89 _) (OpI.vs_movups) (by decide) <|
  .cons (p1_94 _) (OpI.st (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p1_99 _) (OpI.mov (.i 6295520) (.inr rfl)) (by decide) <|
  .cons (p1_106 _) (OpI.vs_movups) (by decide) <|
  .cons (p1_111 _) (OpI.st (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p1_116 _) (OpI.mov (.i 0) (.inl rfl)) (by decide) <|
  .cons (p1_121 _) (OpI.cmov64) (by decide) <|
  .cons (p1_125 _) (OpI.vs_movups) (by decide) <|
  .cons (p1_130 _) (OpI.vs_movups) (by decide) <|
  .cons (p1_135 _) (OpI.vs_movups) (by decide) <|
  .nil 143

/-- The stretch at `185`. -/
def p2 : List Byte := [
  0x41, 0xba, 0x08, 0x00, 0x00, 0x00, 0xb8, 0x0d, 0x00, 0x00, 0x00]

theorem p2_0 : ∀ feat, Dec feat p2 0 (FV7z.mk .mov 32 [gr 32 10, Src.opd 32 (.i 8)] 6) := by dec_rfl
theorem p2_6 : ∀ feat, Dec feat p2 6 (FV7z.mk .mov 32 [gr 32 0, Src.opd 32 (.i 13)] 5) := by dec_rfl

/-- What the stretch does. -/
def o2 : List Op := [
  Op.mov 32 10 (.i 8),
  Op.mov 32 0 (.i 13)]

theorem b2 (prof : Profile) : Blk prof p2 0 11 o2 :=
  .cons (p2_0 _) (OpI.mov (.i 8) (.inl rfl)) (by decide) <|
  .cons (p2_6 _) (OpI.mov (.i 13) (.inl rfl)) (by decide) <|
  .nil 11

/-- The stretch at `198`. -/
def p3 : List Byte := [
  0x48, 0x3d, 0x00, 0xf0, 0xff, 0xff]

theorem p3_0 : ∀ feat, Dec feat p3 0 (FV7z.mk .cmp 64 [gr 64 0, Src.opd 64 (.i 18446744073709547520)] 6) := by dec_rfl

/-- What the stretch does. -/
def o3 : List Op := [
  Op.cmp 64 0 (.i 18446744073709547520)]

theorem b3 (prof : Profile) : Blk prof p3 0 6 o3 :=
  .cons (p3_0 _) (OpI.cmp (.i 18446744073709547520) (.inr rfl)) (by decide) <|
  .nil 6

def j1 : List Byte := [0x0f, 0x87, 0xee, 0x00, 0x00, 0x00]
theorem j1_0 : ∀ feat, Dec feat j1 0 (FV7z.mk (.jcc 7) 64 [.rel 238] 6) := by dec_rfl

/-- The stretch at `210`. -/
def p4 : List Byte := [
  0x41, 0x89, 0xc1, 0x4d, 0x85, 0xc0]

theorem p4_0 : ∀ feat, Dec feat p4 0 (FV7z.mk .mov 32 [gr 32 9, Src.opd 32 (.r 0)] 3) := by dec_rfl
theorem p4_3 : ∀ feat, Dec feat p4 3 (FV7z.mk .test 64 [gr 64 8, Src.opd 64 (.r 8)] 3) := by dec_rfl

/-- What the stretch does. -/
def o4 : List Op := [
  Op.mov 32 9 (.r 0),
  Op.test 64 8 (.r 8)]

theorem b4 (prof : Profile) : Blk prof p4 0 6 o4 :=
  .cons (p4_0 _) (OpI.mov (.r 0) (.inl rfl)) (by decide) <|
  .cons (p4_3 _) (OpI.test (.r 8) (.inr rfl)) (by decide) <|
  .nil 6

def j2 : List Byte := [0x0f, 0x84, 0xa1, 0x00, 0x00, 0x00]
theorem j2_0 : ∀ feat, Dec feat j2 0 (FV7z.mk (.jcc 4) 64 [.rel 161] 6) := by dec_rfl

/-- The stretch at `222`. -/
def p5 : List Byte := [
  0x85, 0xc0]

theorem p5_0 : ∀ feat, Dec feat p5 0 (FV7z.mk .test 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl

/-- What the stretch does. -/
def o5 : List Op := [
  Op.test 32 0 (.r 0)]

theorem b5 (prof : Profile) : Blk prof p5 0 2 o5 :=
  .cons (p5_0 _) (OpI.test (.r 0) (.inl rfl)) (by decide) <|
  .nil 2

def j3 : List Byte := [0x0f, 0x88, 0x99, 0x00, 0x00, 0x00]
theorem j3_0 : ∀ feat, Dec feat j3 0 (FV7z.mk (.jcc 8) 64 [.rel 153] 6) := by dec_rfl

/-- The stretch at `383`. -/
def p6 : List Byte := [
  0x48, 0x8b, 0x84, 0x24, 0x38, 0x01, 0x00, 0x00, 0x64, 0x48, 0x33, 0x04, 0x25, 0x28, 0x00, 0x00,
  0x00]

theorem p6_0 : ∀ feat, Dec feat p6 0 (FV7z.mk .mov 64 [gr 64 0, .mem (mg (some 4) none 1 312 64)] 8) := by dec_rfl
theorem p6_8 : ∀ feat, Dec feat p6 8 (FV7z.mk .xor 64 [gr 64 0, .mem (mf none none 1 40 64)] 9) := by dec_rfl

/-- What the stretch does. -/
def o6 (fb : Addr) : List Op := [
  Op.ld 64 0 (some 4) none 1 312,
  Op.xormf fb 64 0 none none 1 40]

theorem b6 (prof : Profile) (fb : Addr) : BlkF prof p6 (0x60116f : Addr) fb 0 17 (o6 fb) :=
  .cons (p6_0 _) (((OpI.ld (.inr rfl)).at _).fs _) (by decide) <|
  .cons (p6_8 _) (OpIF.xormf (.inr rfl)) (by decide) <|
  .nil 17

def j4 : List Byte := [0x75, 0x42]
theorem j4_0 : ∀ feat, Dec feat j4 0 (FV7z.mk (.jcc 5) 64 [.rel 66] 2) := by dec_rfl

/-- The stretch at `402`. -/
def p7 : List Byte := [
  0x44, 0x89, 0xc8, 0x48, 0x81, 0xc4, 0x48, 0x01, 0x00, 0x00]

theorem p7_0 : ∀ feat, Dec feat p7 0 (FV7z.mk .mov 32 [gr 32 0, Src.opd 32 (.r 9)] 3) := by dec_rfl
theorem p7_3 : ∀ feat, Dec feat p7 3 (FV7z.mk .add 64 [gr 64 4, Src.opd 64 (.i 328)] 7) := by dec_rfl

/-- What the stretch does. -/
def o7 : List Op := [
  Op.mov 32 0 (.r 9),
  Op.add 64 4 (.i 328)]

theorem b7 (prof : Profile) : Blk prof p7 0 10 o7 :=
  .cons (p7_0 _) (OpI.mov (.r 9) (.inl rfl)) (by decide) <|
  .cons (p7_3 _) (OpI.add (.i 328) (.inr rfl)) (by decide) <|
  .nil 10

/-- The stretch at `416`. -/
def p8 : List Byte := [
  0x31, 0xf6, 0x48, 0x8d, 0x94, 0x24, 0xa0, 0x00, 0x00, 0x00, 0x4d, 0x85, 0xc0, 0x48, 0x0f, 0x44,
  0xd6]

theorem p8_0 : ∀ feat, Dec feat p8 0 (FV7z.mk .xor 32 [gr 32 6, Src.opd 32 (.r 6)] 2) := by dec_rfl
theorem p8_2 : ∀ feat, Dec feat p8 2 (FV7z.mk .lea 64 [gr 64 2, .mem (mg (some 4) none 1 160 0)] 8) := by dec_rfl
theorem p8_10 : ∀ feat, Dec feat p8 10 (FV7z.mk .test 64 [gr 64 8, Src.opd 64 (.r 8)] 3) := by dec_rfl
theorem p8_13 : ∀ feat, Dec feat p8 13 (FV7z.mk (.cmovcc 4) 64 [gr 64 2, gr 64 6] 4) := by dec_rfl

/-- What the stretch does. -/
def o8 : List Op := [
  Op.xor 32 6 (.r 6),
  Op.lea 64 2 (some 4) none 1 160,
  Op.test 64 8 (.r 8),
  Op.cmov64 4 2 6]

theorem b8 (prof : Profile) : Blk prof p8 0 17 o8 :=
  .cons (p8_0 _) (OpI.xor (.r 6) (.inl rfl)) (by decide) <|
  .cons (p8_2 _) (OpI.lea (.inr rfl)) (by decide) <|
  .cons (p8_10 _) (OpI.test (.r 8) (.inr rfl)) (by decide) <|
  .cons (p8_13 _) (OpI.cmov64) (by decide) <|
  .nil 17

def j5 : List Byte := [0xe9, 0x03, 0xff, 0xff, 0xff]
theorem j5_0 : ∀ feat, Dec feat j5 0 (FV7z.mk .jmp 64 [.rel 18446744073709551363] 5) := by dec_rfl

end FV7z.Sga
