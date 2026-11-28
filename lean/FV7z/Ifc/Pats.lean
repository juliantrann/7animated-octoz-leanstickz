import FV7z.Lemmas.Sp
import FV7z.Lemmas.BlkOps2
/-!
# The stretches of straight-line code of `CInFileStream::CInFileStream` (PLAN.md §M, M1)

Each distinct stretch between labels and jumps (`p*`, 3 of them) and each distinct jump (`j*`, 0) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.Ifc
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The stretch at `0`. -/
def p0 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0x55, 0x53, 0x48, 0x89, 0xfb, 0x48, 0x8d, 0xbf, 0xd0, 0x00, 0x00, 0x00,
  0x48, 0x83, 0xec, 0x08, 0x48, 0xc7, 0xc0, 0x48, 0xe7, 0x78, 0x00, 0xc6, 0x87, 0x60, 0xff, 0xff,
  0xff, 0x00, 0x48, 0xc7, 0x47, 0xf8, 0x00, 0x00, 0x00, 0x00, 0x48, 0x8d, 0x50, 0x10, 0x48, 0x89,
  0x97, 0x30, 0xff, 0xff, 0xff, 0x48, 0x8d, 0x50, 0x70, 0x48, 0x89, 0x97, 0x38, 0xff, 0xff, 0xff,
  0x48, 0x8d, 0x90, 0xa0, 0x00, 0x00, 0x00, 0x48, 0x89, 0x97, 0x40, 0xff, 0xff, 0xff, 0x48, 0x8d,
  0x90, 0xd0, 0x00, 0x00, 0x00, 0x48, 0x05, 0x00, 0x01, 0x00, 0x00, 0x48, 0x89, 0x87, 0x50, 0xff,
  0xff, 0xff, 0x48, 0xb8, 0x00, 0x00, 0x00, 0x00, 0xff, 0xff, 0xff, 0xff, 0x48, 0x89, 0x97, 0x48,
  0xff, 0xff, 0xff, 0x48, 0x89, 0x87, 0x58, 0xff, 0xff, 0xff]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem p0_4 : ∀ feat, Dec feat p0 4 (FV7z.mk .push 64 [gr 64 5] 1) := by dec_rfl
theorem p0_5 : ∀ feat, Dec feat p0 5 (FV7z.mk .push 64 [gr 64 3] 1) := by dec_rfl
theorem p0_6 : ∀ feat, Dec feat p0 6 (FV7z.mk .mov 64 [gr 64 3, Src.opd 64 (.r 7)] 3) := by dec_rfl
theorem p0_9 : ∀ feat, Dec feat p0 9 (FV7z.mk .lea 64 [gr 64 7, .mem (mg (some 7) none 1 208 0)] 7) := by dec_rfl
theorem p0_16 : ∀ feat, Dec feat p0 16 (FV7z.mk .sub 64 [gr 64 4, Src.opd 64 (.i 8)] 4) := by dec_rfl
theorem p0_20 : ∀ feat, Dec feat p0 20 (FV7z.mk .mov 64 [gr 64 0, Src.opd 64 (.i 7923528)] 7) := by dec_rfl
theorem p0_27 : ∀ feat, Dec feat p0 27 (FV7z.mk .mov 8 [.mem (mg (some 7) none 1 18446744073709551456 8), .imm 8 0] 7) := by dec_rfl
theorem p0_34 : ∀ feat, Dec feat p0 34 (FV7z.mk .mov 64 [.mem (mg (some 7) none 1 18446744073709551608 64), .imm 64 0] 8) := by dec_rfl
theorem p0_42 : ∀ feat, Dec feat p0 42 (FV7z.mk .lea 64 [gr 64 2, .mem (mg (some 0) none 1 16 0)] 4) := by dec_rfl
theorem p0_46 : ∀ feat, Dec feat p0 46 (FV7z.mk .mov 64 [.mem (mg (some 7) none 1 18446744073709551408 64), gr 64 2] 7) := by dec_rfl
theorem p0_53 : ∀ feat, Dec feat p0 53 (FV7z.mk .lea 64 [gr 64 2, .mem (mg (some 0) none 1 112 0)] 4) := by dec_rfl
theorem p0_57 : ∀ feat, Dec feat p0 57 (FV7z.mk .mov 64 [.mem (mg (some 7) none 1 18446744073709551416 64), gr 64 2] 7) := by dec_rfl
theorem p0_64 : ∀ feat, Dec feat p0 64 (FV7z.mk .lea 64 [gr 64 2, .mem (mg (some 0) none 1 160 0)] 7) := by dec_rfl
theorem p0_71 : ∀ feat, Dec feat p0 71 (FV7z.mk .mov 64 [.mem (mg (some 7) none 1 18446744073709551424 64), gr 64 2] 7) := by dec_rfl
theorem p0_78 : ∀ feat, Dec feat p0 78 (FV7z.mk .lea 64 [gr 64 2, .mem (mg (some 0) none 1 208 0)] 7) := by dec_rfl
theorem p0_85 : ∀ feat, Dec feat p0 85 (FV7z.mk .add 64 [gr 64 0, Src.opd 64 (.i 256)] 6) := by dec_rfl
theorem p0_91 : ∀ feat, Dec feat p0 91 (FV7z.mk .mov 64 [.mem (mg (some 7) none 1 18446744073709551440 64), gr 64 0] 7) := by dec_rfl
theorem p0_98 : ∀ feat, Dec feat p0 98 (FV7z.mk .mov 64 [gr 64 0, Src.opd 64 (.i 18446744069414584320)] 10) := by dec_rfl
theorem p0_108 : ∀ feat, Dec feat p0 108 (FV7z.mk .mov 64 [.mem (mg (some 7) none 1 18446744073709551432 64), gr 64 2] 7) := by dec_rfl
theorem p0_115 : ∀ feat, Dec feat p0 115 (FV7z.mk .mov 64 [.mem (mg (some 7) none 1 18446744073709551448 64), gr 64 0] 7) := by dec_rfl

/-- What the stretch does. -/
def o0 : List Op := [
  Op.nop,
  Op.push 5,
  Op.push 3,
  Op.mov 64 3 (.r 7),
  Op.lea 64 7 (some 7) none 1 208,
  Op.sub 64 4 (.i 8),
  Op.mov 64 0 (.i 7923528),
  Op.sti 8 (some 7) none 1 18446744073709551456 0,
  Op.sti 64 (some 7) none 1 18446744073709551608 0,
  Op.lea 64 2 (some 0) none 1 16,
  Op.st 64 (some 7) none 1 18446744073709551408 2,
  Op.lea 64 2 (some 0) none 1 112,
  Op.st 64 (some 7) none 1 18446744073709551416 2,
  Op.lea 64 2 (some 0) none 1 160,
  Op.st 64 (some 7) none 1 18446744073709551424 2,
  Op.lea 64 2 (some 0) none 1 208,
  Op.add 64 0 (.i 256),
  Op.st 64 (some 7) none 1 18446744073709551440 0,
  Op.mov 64 0 (.i 18446744069414584320),
  Op.st 64 (some 7) none 1 18446744073709551432 2,
  Op.st 64 (some 7) none 1 18446744073709551448 0]

theorem b0 (prof : Profile) : Blk prof p0 0 122 o0 :=
  .cons (p0_0 _) (OpI.endbr) (by decide) <|
  .cons (p0_4 _) (OpI.push) (by decide) <|
  .cons (p0_5 _) (OpI.push) (by decide) <|
  .cons (p0_6 _) (OpI.mov (.r 7) (.inr rfl)) (by decide) <|
  .cons (p0_9 _) (OpI.lea (.inr rfl)) (by decide) <|
  .cons (p0_16 _) (OpI.sub (.i 8) (.inr rfl)) (by decide) <|
  .cons (p0_20 _) (OpI.mov (.i 7923528) (.inr rfl)) (by decide) <|
  .cons (p0_27 _) (OpI.sti (.inl rfl)) (by decide) <|
  .cons (p0_34 _) (OpI.sti (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p0_42 _) (OpI.lea (.inr rfl)) (by decide) <|
  .cons (p0_46 _) (OpI.st (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p0_53 _) (OpI.lea (.inr rfl)) (by decide) <|
  .cons (p0_57 _) (OpI.st (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p0_64 _) (OpI.lea (.inr rfl)) (by decide) <|
  .cons (p0_71 _) (OpI.st (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p0_78 _) (OpI.lea (.inr rfl)) (by decide) <|
  .cons (p0_85 _) (OpI.add (.i 256) (.inr rfl)) (by decide) <|
  .cons (p0_91 _) (OpI.st (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p0_98 _) (OpI.mov (.i 18446744069414584320) (.inr rfl)) (by decide) <|
  .cons (p0_108 _) (OpI.st (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p0_115 _) (OpI.st (.inr (.inr (.inr rfl)))) (by decide) <|
  .nil 122

/-- The stretch at `127`. -/
def p1 : List Byte := [
  0x48, 0x8d, 0xbb, 0xe0, 0x00, 0x00, 0x00]

theorem p1_0 : ∀ feat, Dec feat p1 0 (FV7z.mk .lea 64 [gr 64 7, .mem (mg (some 3) none 1 224 0)] 7) := by dec_rfl

/-- What the stretch does. -/
def o1 : List Op := [
  Op.lea 64 7 (some 3) none 1 224]

theorem b1 (prof : Profile) : Blk prof p1 0 7 o1 :=
  .cons (p1_0 _) (OpI.lea (.inr rfl)) (by decide) <|
  .nil 7

/-- The stretch at `139`. -/
def p2 : List Byte := [
  0xc7, 0x83, 0xf0, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x48, 0xc7, 0x83, 0xf8, 0x00, 0x00,
  0x00, 0x00, 0x00, 0x00, 0x00, 0x48, 0xc7, 0x83, 0x00, 0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
  0x48, 0x83, 0xc4, 0x08, 0x5b, 0x5d]

theorem p2_0 : ∀ feat, Dec feat p2 0 (FV7z.mk .mov 32 [.mem (mg (some 3) none 1 240 32), .imm 32 0] 10) := by dec_rfl
theorem p2_10 : ∀ feat, Dec feat p2 10 (FV7z.mk .mov 64 [.mem (mg (some 3) none 1 248 64), .imm 64 0] 11) := by dec_rfl
theorem p2_21 : ∀ feat, Dec feat p2 21 (FV7z.mk .mov 64 [.mem (mg (some 3) none 1 256 64), .imm 64 0] 11) := by dec_rfl
theorem p2_32 : ∀ feat, Dec feat p2 32 (FV7z.mk .add 64 [gr 64 4, Src.opd 64 (.i 8)] 4) := by dec_rfl
theorem p2_36 : ∀ feat, Dec feat p2 36 (FV7z.mk .pop 64 [gr 64 3] 1) := by dec_rfl
theorem p2_37 : ∀ feat, Dec feat p2 37 (FV7z.mk .pop 64 [gr 64 5] 1) := by dec_rfl

/-- What the stretch does. -/
def o2 : List Op := [
  Op.sti 32 (some 3) none 1 240 0,
  Op.sti 64 (some 3) none 1 248 0,
  Op.sti 64 (some 3) none 1 256 0,
  Op.add 64 4 (.i 8),
  Op.pop 3,
  Op.pop 5]

theorem b2 (prof : Profile) : Blk prof p2 0 38 o2 :=
  .cons (p2_0 _) (OpI.sti (.inr (.inr (.inl rfl)))) (by decide) <|
  .cons (p2_10 _) (OpI.sti (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p2_21 _) (OpI.sti (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p2_32 _) (OpI.add (.i 8) (.inr rfl)) (by decide) <|
  .cons (p2_36 _) (OpI.pop) (by decide) <|
  .cons (p2_37 _) (OpI.pop) (by decide) <|
  .nil 38

end FV7z.Ifc
