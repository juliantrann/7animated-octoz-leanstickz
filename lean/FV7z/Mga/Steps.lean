import FV7z.Mga.Cuts
import FV7z.Lemmas.Rmw5
import FV7z.Lemmas.BlkOps4
import FV7z.Ulk.Holds
/-!
# `_int_memalign`: the steps outside the generated pieces (PLAN.md §M, M1)

- `call_58`: `_int_malloc (av, nb + alignment + MINSIZE)`; `call_216`, `call_336`: `_int_free (av, p, 1)` of the
  leading and of the trailing remainder; `im_58`, `if_216`, `if_336`: their targets.
- `div_81`, `div_239`: `div rbx` (`(unsigned long) m % alignment`, and the assert's).
- `or_186`: `or qword [r13 + r14 + 8], 1` (`set_inuse_bit_at_offset (newp, newsize)`).
- `ret_358`: the `ret`.
-/
namespace FV7z.Mga
open ZellicX86 Decode FV7z.Leaf

def pc58 : List Byte := [0xe8, 0xe1, 0xef, 0xff, 0xff]
theorem pc58_0 : ∀ feat, Dec feat pc58 0 (FV7z.mk .call 64 [.rel 18446744073709547489] 5) := by dec_rfl
theorem w_58 : pc58 <+: mga.drop 58 := by decide +kernel
theorem call_58 (feat : Features) : Dec feat mga 58 (FV7z.mk .call 64 [.rel 18446744073709547489] 5) :=
  Dec.shift (j := 58) (k := 0) (pc58_0 feat) w_58 (Nat.zero_le _)

def pd3 : List Byte := [0x48, 0xf7, 0xf3]
theorem pd3_0 : ∀ feat, Dec feat pd3 0 (FV7z.mk .div 64 [gr 64 3] 3) := by dec_rfl
theorem w_81 : pd3 <+: mga.drop 81 := by decide +kernel
theorem div_81 (feat : Features) : Dec feat mga 81 (FV7z.mk .div 64 [gr 64 3] 3) :=
  Dec.shift (j := 81) (k := 0) (pd3_0 feat) w_81 (Nat.zero_le _)
theorem w_239 : pd3 <+: mga.drop 239 := by decide +kernel
theorem div_239 (feat : Features) : Dec feat mga 239 (FV7z.mk .div 64 [gr 64 3] 3) :=
  Dec.shift (j := 239) (k := 0) (pd3_0 feat) w_239 (Nat.zero_le _)

/-- `or qword [r13 + r14 + 8], 1`. -/
abbrev orM : Inst := FV7z.mk .or 64 [.mem (mbi 13 14 8 64), .imm 64 1] 6
def po186 : List Byte := [0x4b, 0x83, 0x4c, 0x35, 0x08, 0x01]
theorem po186_0 : ∀ feat, Dec feat po186 0 orM := by dec_rfl
theorem w_186 : po186 <+: mga.drop 186 := by decide +kernel
theorem or_186 (feat : Features) : Dec feat mga 186 orM :=
  Dec.shift (j := 186) (k := 0) (po186_0 feat) w_186 (Nat.zero_le _)

def pc216 : List Byte := [0xe8, 0xf3, 0xdc, 0xff, 0xff]
theorem pc216_0 : ∀ feat, Dec feat pc216 0 (FV7z.mk .call 64 [.rel 18446744073709542643] 5) := by dec_rfl
theorem w_216 : pc216 <+: mga.drop 216 := by decide +kernel
theorem call_216 (feat : Features) : Dec feat mga 216 (FV7z.mk .call 64 [.rel 18446744073709542643] 5) :=
  Dec.shift (j := 216) (k := 0) (pc216_0 feat) w_216 (Nat.zero_le _)

def pc336 : List Byte := [0xe8, 0x7b, 0xdc, 0xff, 0xff]
theorem pc336_0 : ∀ feat, Dec feat pc336 0 (FV7z.mk .call 64 [.rel 18446744073709542523] 5) := by dec_rfl
theorem w_336 : pc336 <+: mga.drop 336 := by decide +kernel
theorem call_336 (feat : Features) : Dec feat mga 336 (FV7z.mk .call 64 [.rel 18446744073709542523] 5) :=
  Dec.shift (j := 336) (k := 0) (pc336_0 feat) w_336 (Nat.zero_le _)

theorem w_358 : Sbrk.pret <+: mga.drop 358 := by decide +kernel
theorem ret_358 (feat : Features) : Dec feat mga 358 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 358) (k := 0) (Sbrk.pret_0 feat) w_358 (Nat.zero_le _)

/-- The call at 58 is of `_int_malloc` (`0x630be0`), those at 216 and 336 of `_int_free` (`0x62f990`). -/
theorem im_58 : mga_at.add (58 + 5) + BitVec.ofNat 64 18446744073709547489 = 0x630be0 := by decide
theorem if_216 : mga_at.add (216 + 5) + BitVec.ofNat 64 18446744073709542643 = 0x62f990 := by decide
theorem if_336 : mga_at.add (336 + 5) + BitVec.ofNat 64 18446744073709542523 = 0x62f990 := by decide

end FV7z.Mga
