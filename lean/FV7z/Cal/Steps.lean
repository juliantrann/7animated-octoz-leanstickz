import FV7z.Cal.Cuts
import FV7z.Strlen.Steps
import FV7z.Lemmas.StoreX
import FV7z.Lemmas.Xmm2
/-!
# `__libc_calloc`: the steps outside the generated pieces (PLAN.md §M, M1)

- `Op.mul64o`: `mul r64` with what the model says of `OF` (set iff the high half of the product is not 0;
  `Op.mul64` says nothing of the flags); `o0'`, `blk_0'`, `W_0'`, `c_0'`: the entry's piece with it, for the
  overflow check (`seto`) after the multiply.
- `mul_lo`, `mul_hi`: the halves of a product that fits 64 bits.
- `call_123` (`_int_malloc`), `call_717` (`memset` through the PLT), `ret_209`: the instructions the pieces stop at.
- `bpx`: `pxor xmm0, xmm0` at 252 as a `BlkV`; `mv_264` … `mv_296`: the `movups` of `xmm0` that clear the block
  (`Seg.s_movups_stv`); `jb_272` … `jb_294`: the `jbe`s between them.
-/
namespace FV7z
open ZellicX86 Decode

namespace Op

/-- `mul r64`, `OF` as the model sets it: whether the high half is not 0. -/
def mul64o (q : Nat) : Op :=
  .reg (fun g _ => wr (wr g 0 ((mulp g q).setWidth 64)) 2 ((mulp g q).extractLsb' 64 64))
    fun g _ fl => fl.of = ((mulp g q).extractLsb' 64 64 != 0)

end Op

theorem OpI.mul64o {prof : Profile} {q len : Nat} : OpI prof (mk .mul 64 [gr 64 q] len) (Op.mul64o q) :=
  fun _ _ _ htf hdec => ⟨_, _, instruction_next htf hdec rfl, rfl, rfl, rfl, rfl⟩

theorem cond_0 (f : Rflags) : f.cond 0 = f.of := rfl

/-- The low half of a 128-bit product of two 64-bit values. -/
theorem mul_lo (x y : BitVec 64) : ((x.setWidth 128) * (y.setWidth 128)).setWidth 64 = x * y := by
  rw [BitVec.setWidth_mul _ _ (by decide), BitVec.setWidth_setWidth_of_le _ (by decide),
    BitVec.setWidth_setWidth_of_le _ (by decide), BitVec.setWidth_eq, BitVec.setWidth_eq]

/-- The high half of a 128-bit product that fits 64 bits. -/
theorem mul_hi {x y : BitVec 64} (h : x.toNat * y.toNat < 2 ^ 64) :
    ((x.setWidth 128) * (y.setWidth 128)).extractLsb' 64 64 = 0#64 := by
  apply BitVec.eq_of_toNat_eq
  have hx := x.isLt
  have hy := y.isLt
  rw [BitVec.extractLsb'_toNat, BitVec.toNat_mul, BitVec.toNat_setWidth, BitVec.toNat_setWidth,
    Nat.mod_eq_of_lt (a := x.toNat) (by omega), Nat.mod_eq_of_lt (a := y.toNat) (by omega),
    Nat.mod_eq_of_lt (a := x.toNat * y.toNat) (b := 2 ^ 128) (by omega), Nat.shiftRight_eq_div_pow,
    Nat.div_eq_of_lt h]
  rfl

end FV7z

namespace FV7z.Cal
set_option maxRecDepth 100000
open ZellicX86 Decode FV7z.Leaf

/-! ## The entry, `OF` kept -/

/-- What the entry's stretch does, `OF` of the `mul` kept. -/
def o0' : List Op := [
  Op.nop,
  Op.push 13,
  Op.mov 64 0 (.r 7),
  Op.push 12,
  Op.push 5,
  Op.push 3,
  Op.sub 64 4 (.i 8),
  Op.mul64o 6,
  Op.mov 64 12 (.r 0),
  Op.setcc 0 0,
  Op.test 64 12 (.r 12)]

theorem b0' (prof : Profile) : Blk prof p0 0 29 o0' :=
  .cons (p0_0 _) (OpI.endbr) (by decide) <|
  .cons (p0_4 _) (OpI.push) (by decide) <|
  .cons (p0_6 _) (OpI.mov (.r 7) (.inr rfl)) (by decide) <|
  .cons (p0_9 _) (OpI.push) (by decide) <|
  .cons (p0_11 _) (OpI.push) (by decide) <|
  .cons (p0_12 _) (OpI.push) (by decide) <|
  .cons (p0_13 _) (OpI.sub (.i 8) (.inr rfl)) (by decide) <|
  .cons (p0_17 _) (OpI.mul64o) (by decide) <|
  .cons (p0_20 _) (OpI.mov (.r 0) (.inr rfl)) (by decide) <|
  .cons (p0_23 _) (OpI.setcc) (by decide) <|
  .cons (p0_26 _) (OpI.test (.r 12) (.inr rfl)) (by decide) <|
  .nil 29

theorem blk_0' (prof : Profile) : Blk prof cal 0 29 o0' := (b0' prof).shift w_0

def W_0' (fb : Addr) : Wpt := fun F Wl Q => wp F Wl o0' fun g f V =>
    (f.cond 8 = true → Q 400 g (rfz f) V) ∧
    (f.cond 8 = false → W_35 fb F Wl Q g (rfz f) V)
theorem c_0' (prof : Profile) (fb : Addr) : SpF prof cal cal_at fb 0 (W_0' fb) :=
  SpF.blk_then (blk_0' prof) (SpF.jcc_then (spj_29 prof fb) (SpF.skip 400) (c_35 prof fb))

/-! ## The calls, the `ret` -/

def pc123 : List Byte := [0xe8, 0x00, 0xc1, 0xff, 0xff]
theorem pc123_0 : ∀ feat, Dec feat pc123 0 (FV7z.mk .call 64 [.rel 18446744073709535488] 5) := by dec_rfl
theorem w_123 : pc123 <+: cal.drop 123 := by decide +kernel
theorem call_123 (feat : Features) : Dec feat cal 123 (FV7z.mk .call 64 [.rel 18446744073709535488] 5) :=
  Dec.shift (j := 123) (k := 0) (pc123_0 feat) w_123 (Nat.zero_le _)
theorem tgt_123 : cal_at.add (123 + 5) + BitVec.ofNat 64 18446744073709535488 = 6491104#64 := by decide

def pc717 : List Byte := [0xe8, 0x4e, 0xc3, 0xdc, 0xff]
theorem pc717_0 : ∀ feat, Dec feat pc717 0 (FV7z.mk .call 64 [.rel 18446744073707242318] 5) := by dec_rfl
theorem w_717 : pc717 <+: cal.drop 717 := by decide +kernel
theorem call_717 (feat : Features) : Dec feat cal 717 (FV7z.mk .call 64 [.rel 18446744073707242318] 5) :=
  Dec.shift (j := 717) (k := 0) (pc717_0 feat) w_717 (Nat.zero_le _)
theorem tgt_717 : cal_at.add (717 + 5) + BitVec.ofNat 64 18446744073707242318 = 4198528#64 := by decide

def pr209 : List Byte := [0xc3]
theorem pr209_0 : ∀ feat, Dec feat pr209 0 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem w_209 : pr209 <+: cal.drop 209 := by decide +kernel
theorem ret_209 (feat : Features) : Dec feat cal 209 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 209) (k := 0) (pr209_0 feat) w_209 (Nat.zero_le _)

/-! ## The inline clearing -/

def px252 : List Byte := [0x66, 0x0f, 0xef, 0xc0]
theorem px252_0 : ∀ feat, Dec feat px252 0 (FV7z.mk (.sse .pxor) 16 [.xmm 0, .xmm 0] 4) := by dec_rfl
theorem w_252 : px252 <+: cal.drop 252 := by decide +kernel
/-- `pxor xmm0, xmm0` at 252. -/
theorem bpx (prof : Profile) : BlkV prof cal 252 256 [VOp.pxor 0 0] :=
  .cons (Dec.shift (j := 252) (k := 0) (px252_0 _) w_252 (Nat.zero_le _)) VOpI.pxor (lt_len (by decide)) (.nil 256)

def mv264 : List Byte := [0x41, 0x0f, 0x11, 0x00]
theorem mv264_0 : ∀ feat, Dec feat mv264 0 (FV7z.mk (.sse .movups) 32 [.mem (mbd 8 0 128), .xmm 0] 4) := by
  dec_rfl
theorem w_264 : mv264 <+: cal.drop 264 := by decide +kernel
theorem mv_264 (feat : Features) : Dec feat cal 264 (FV7z.mk (.sse .movups) 32 [.mem (mbd 8 0 128), .xmm 0] 4) :=
  Dec.shift (j := 264) (k := 0) (mv264_0 feat) w_264 (Nat.zero_le _)

def mv274 : List Byte := [0x41, 0x0f, 0x11, 0x40, 0x18]
theorem mv274_0 : ∀ feat, Dec feat mv274 0 (FV7z.mk (.sse .movups) 32 [.mem (mbd 8 24 128), .xmm 0] 5) := by
  dec_rfl
theorem w_274 : mv274 <+: cal.drop 274 := by decide +kernel
theorem mv_274 (feat : Features) : Dec feat cal 274 (FV7z.mk (.sse .movups) 32 [.mem (mbd 8 24 128), .xmm 0] 5) :=
  Dec.shift (j := 274) (k := 0) (mv274_0 feat) w_274 (Nat.zero_le _)

def mv285 : List Byte := [0x41, 0x0f, 0x11, 0x40, 0x28]
theorem mv285_0 : ∀ feat, Dec feat mv285 0 (FV7z.mk (.sse .movups) 32 [.mem (mbd 8 40 128), .xmm 0] 5) := by
  dec_rfl
theorem w_285 : mv285 <+: cal.drop 285 := by decide +kernel
theorem mv_285 (feat : Features) : Dec feat cal 285 (FV7z.mk (.sse .movups) 32 [.mem (mbd 8 40 128), .xmm 0] 5) :=
  Dec.shift (j := 285) (k := 0) (mv285_0 feat) w_285 (Nat.zero_le _)

def mv296 : List Byte := [0x41, 0x0f, 0x11, 0x40, 0x38]
theorem mv296_0 : ∀ feat, Dec feat mv296 0 (FV7z.mk (.sse .movups) 32 [.mem (mbd 8 56 128), .xmm 0] 5) := by
  dec_rfl
theorem w_296 : mv296 <+: cal.drop 296 := by decide +kernel
theorem mv_296 (feat : Features) : Dec feat cal 296 (FV7z.mk (.sse .movups) 32 [.mem (mbd 8 56 128), .xmm 0] 5) :=
  Dec.shift (j := 296) (k := 0) (mv296_0 feat) w_296 (Nat.zero_le _)

/-- The `jbe 196`s after the stores (at 272, 283, 294) and the `jmp 196` (301). -/
theorem jb_272 (feat : Features) : Dec feat cal 272 (FV7z.mk (.jcc 6) 64 [.rel 18446744073709551538] 2) :=
  Dec.shift (j14_0 _) wj_272 (by decide)
theorem jb_283 (feat : Features) : Dec feat cal 283 (FV7z.mk (.jcc 6) 64 [.rel 18446744073709551527] 2) :=
  Dec.shift (j15_0 _) wj_283 (by decide)
theorem jb_294 (feat : Features) : Dec feat cal 294 (FV7z.mk (.jcc 6) 64 [.rel 18446744073709551516] 2) :=
  Dec.shift (j16_0 _) wj_294 (by decide)

end FV7z.Cal
