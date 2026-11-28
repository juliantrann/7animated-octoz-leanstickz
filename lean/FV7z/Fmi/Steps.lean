import FV7z.Fmi.Cuts
import FV7z.Lemmas.Div32
import FV7z.Sbrk.Holds
/-!
# `find_module_idx`: the steps outside the generated pieces (PLAN.md §M, M1)

- `call_46`: `__hash_string (str)`; `call_118`: `strcmp (str, strtab + name)` through the PLT; `hs_46`, `sc_118`:
  their targets.
- `div_66`: `div ebx` (`hval % hash_size`); `div_78`: `div esi` (`hval % (hash_size - 2)`).
- `ret_186`, `ret_219`: the `ret`s (an empty slot; found).
-/
namespace FV7z.Fmi
open ZellicX86 Decode FV7z.Leaf

def pc46 : List Byte := [0xe8, 0x7d, 0x54, 0xfa, 0xff]
theorem pc46_0 : ∀ feat, Dec feat pc46 0 (FV7z.mk .call 64 [.rel 18446744073709180029] 5) := by dec_rfl
theorem w_46 : pc46 <+: fmi.drop 46 := by decide +kernel
theorem call_46 (feat : Features) : Dec feat fmi 46 (FV7z.mk .call 64 [.rel 18446744073709180029] 5) :=
  Dec.shift (j := 46) (k := 0) (pc46_0 feat) w_46 (Nat.zero_le _)

def pc118 : List Byte := [0xe8, 0x65, 0x42, 0xd8, 0xff]
theorem pc118_0 : ∀ feat, Dec feat pc118 0 (FV7z.mk .call 64 [.rel 18446744073706947173] 5) := by dec_rfl
theorem w_118 : pc118 <+: fmi.drop 118 := by decide +kernel
theorem call_118 (feat : Features) : Dec feat fmi 118 (FV7z.mk .call 64 [.rel 18446744073706947173] 5) :=
  Dec.shift (j := 118) (k := 0) (pc118_0 feat) w_118 (Nat.zero_le _)

def pd3 : List Byte := [0xf7, 0xf3]
theorem pd3_0 : ∀ feat, Dec feat pd3 0 (FV7z.mk .div 32 [gr 32 3] 2) := by dec_rfl
theorem w_66 : pd3 <+: fmi.drop 66 := by decide +kernel
theorem div_66 (feat : Features) : Dec feat fmi 66 (FV7z.mk .div 32 [gr 32 3] 2) :=
  Dec.shift (j := 66) (k := 0) (pd3_0 feat) w_66 (Nat.zero_le _)

def pd6 : List Byte := [0xf7, 0xf6]
theorem pd6_0 : ∀ feat, Dec feat pd6 0 (FV7z.mk .div 32 [gr 32 6] 2) := by dec_rfl
theorem w_78 : pd6 <+: fmi.drop 78 := by decide +kernel
theorem div_78 (feat : Features) : Dec feat fmi 78 (FV7z.mk .div 32 [gr 32 6] 2) :=
  Dec.shift (j := 78) (k := 0) (pd6_0 feat) w_78 (Nat.zero_le _)

theorem w_186 : Sbrk.pret <+: fmi.drop 186 := by decide +kernel
theorem ret_186 (feat : Features) : Dec feat fmi 186 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 186) (k := 0) (Sbrk.pret_0 feat) w_186 (Nat.zero_le _)
theorem w_219 : Sbrk.pret <+: fmi.drop 219 := by decide +kernel
theorem ret_219 (feat : Features) : Dec feat fmi 219 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 219) (k := 0) (Sbrk.pret_0 feat) w_219 (Nat.zero_le _)

/-- The call at 46 is of `__hash_string` (`0x6222e0`), the one at 118 of `strcmp`'s PLT entry (`0x401110`). -/
theorem hs_46 : fmi_at.add (46 + 5) + BitVec.ofNat 64 18446744073709180029 = 0x6222e0 := by decide
theorem sc_118 : fmi_at.add (118 + 5) + BitVec.ofNat 64 18446744073706947173 = 0x401110 := by decide

end FV7z.Fmi
