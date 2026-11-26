import FV7z.Stm.Cuts
import FV7z.Lemmas.Lock4
import FV7z.Lemmas.CallR
import FV7z.Dmc.Holds
/-!
# `systrim`: the steps outside the generated pieces (PLAN.md §M, M1)

- `call_51`, `call_94`, `call_114`: `call *__morecore` (`0x7932d8`): `MORECORE (0)`, `MORECORE (-extra)`,
  `MORECORE (0)`.
- `ret_81`: the `ret`.
- `sub_141`: `sub qword [rip + 0x163954], rbp` (`main_arena.system_mem` at `0x7932c8`).
-/
namespace FV7z.Stm
open ZellicX86 Decode FV7z.Leaf

def pc51 : List Byte := [0xff, 0x15, 0xbf, 0x39, 0x16, 0x00]
theorem pc51_0 : ∀ feat, Dec feat pc51 0 (FV7z.mk .call 64 [.mem (mrip 1456575 64)] 6) := by dec_rfl
theorem w_51 : pc51 <+: stm.drop 51 := by decide +kernel
theorem call_51 (feat : Features) : Dec feat stm 51 (FV7z.mk .call 64 [.mem (mrip 1456575 64)] 6) :=
  Dec.shift (j := 51) (k := 0) (pc51_0 feat) w_51 (Nat.zero_le _)

def pc94 : List Byte := [0xff, 0x15, 0x94, 0x39, 0x16, 0x00]
theorem pc94_0 : ∀ feat, Dec feat pc94 0 (FV7z.mk .call 64 [.mem (mrip 1456532 64)] 6) := by dec_rfl
theorem w_94 : pc94 <+: stm.drop 94 := by decide +kernel
theorem call_94 (feat : Features) : Dec feat stm 94 (FV7z.mk .call 64 [.mem (mrip 1456532 64)] 6) :=
  Dec.shift (j := 94) (k := 0) (pc94_0 feat) w_94 (Nat.zero_le _)

def pc114 : List Byte := [0xff, 0x15, 0x80, 0x39, 0x16, 0x00]
theorem pc114_0 : ∀ feat, Dec feat pc114 0 (FV7z.mk .call 64 [.mem (mrip 1456512 64)] 6) := by dec_rfl
theorem w_114 : pc114 <+: stm.drop 114 := by decide +kernel
theorem call_114 (feat : Features) : Dec feat stm 114 (FV7z.mk .call 64 [.mem (mrip 1456512 64)] 6) :=
  Dec.shift (j := 114) (k := 0) (pc114_0 feat) w_114 (Nat.zero_le _)

theorem w_81 : Sbrk.pret <+: stm.drop 81 := by decide +kernel
theorem ret_81 (feat : Features) : Dec feat stm 81 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 81) (k := 0) (Sbrk.pret_0 feat) w_81 (Nat.zero_le _)

def ps141 : List Byte := [0x48, 0x29, 0x2d, 0x54, 0x39, 0x16, 0x00]
theorem ps141_0 : ∀ feat, Dec feat ps141 0 (FV7z.mk .sub 64 [.mem (mrip 1456468 64), gr 64 5] 7) := by dec_rfl
theorem w_141 : ps141 <+: stm.drop 141 := by decide +kernel
theorem sub_141 (feat : Features) : Dec feat stm 141 (FV7z.mk .sub 64 [.mem (mrip 1456468 64), gr 64 5] 7) :=
  Dec.shift (j := 141) (k := 0) (ps141_0 feat) w_141 (Nat.zero_le _)

/-- The three calls read `__morecore`. -/
theorem mc_51 : stm_at.add (51 + 6) + BitVec.ofNat 64 1456575 = 7942872#64 := by decide
theorem mc_94 : stm_at.add (94 + 6) + BitVec.ofNat 64 1456532 = 7942872#64 := by decide
theorem mc_114 : stm_at.add (114 + 6) + BitVec.ofNat 64 1456512 = 7942872#64 := by decide
/-- The `sub` is of `main_arena.system_mem`. -/
theorem sm_141 : stm_at.add (141 + 7) + BitVec.ofNat 64 1456468 = 7942856#64 := by decide

end FV7z.Stm
