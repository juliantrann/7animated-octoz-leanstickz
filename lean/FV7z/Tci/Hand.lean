import FV7z.Tci.Cuts
import FV7z.Imm.Hand
import FV7z.Pim.Dec
/-!
# `tcache_init`: the instructions outside the blocks (PLAN.md G3, `malloc`)

Decoded at their offsets:

- `cx_42`: `cmpxchg [rbp], edx`, not locked (the arena's lock, one thread);
- `call_54`: the `call` of `_int_malloc`, with its target `tgt_54`;
- `sb_87`: `sub dword [rbp], 1` (the lock given back);
- `stos_146`: `rep stos qword [rdi], rax` (the cache's 640 bytes);
- `ret_150`: the `ret`.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Tci

/-- `cmpxchg [rbp], edx`, not locked. -/
def pcx : List Byte := [0x0f, 0xb1, 0x55, 0x00]
theorem pcx_0 : ∀ feat, Dec feat pcx 0 (FV7z.mk .cmpxchg 32 [.mem (mbd 5 0 32), gr 32 2] 4) := by dec_rfl
theorem w_42 : pcx <+: tci.drop 42 := by decide +kernel
theorem cx_42 (feat : Features) : Dec feat tci 42 (FV7z.mk .cmpxchg 32 [.mem (mbd 5 0 32), gr 32 2] 4) :=
  Dec.shift (j := 42) (k := 0) (pcx_0 feat) w_42 (Nat.zero_le _)

/-- `call _int_malloc`. -/
def pcl : List Byte := [0xe8, 0x45, 0xf1, 0xff, 0xff]
theorem pcl_0 : ∀ feat, Dec feat pcl 0 (FV7z.mk .call 64 [.rel 18446744073709547845] 5) := by dec_rfl
theorem w_54 : pcl <+: tci.drop 54 := by decide +kernel
theorem call_54 (feat : Features) : Dec feat tci 54 (FV7z.mk .call 64 [.rel 18446744073709547845] 5) :=
  Dec.shift (j := 54) (k := 0) (pcl_0 feat) w_54 (Nat.zero_le _)

/-- The `call` at 54 goes to `_int_malloc`. -/
theorem tgt_54 : tci_at.add (54 + 5) + BitVec.ofNat 64 18446744073709547845 = Imm.imm_at := by decide

/-- `sub dword [rbp], 1`. -/
def psb : List Byte := [0x83, 0x6d, 0x00, 0x01]
theorem psb_0 : ∀ feat, Dec feat psb 0 (FV7z.mk .sub 32 [.mem (mbd 5 0 32), .imm 32 1] 4) := by dec_rfl
theorem w_87 : psb <+: tci.drop 87 := by decide +kernel
theorem sb_87 (feat : Features) : Dec feat tci 87 (FV7z.mk .sub 32 [.mem (mbd 5 0 32), .imm 32 1] 4) :=
  Dec.shift (j := 87) (k := 0) (psb_0 feat) w_87 (Nat.zero_le _)

theorem w_146 : Pim.pstos <+: tci.drop 146 := by decide +kernel
theorem stos_146 (feat : Features) : Dec feat tci 146 (repStosq 3) :=
  Dec.shift (j := 146) (k := 0) (Pim.pstos_0 feat) w_146 (Nat.zero_le _)

theorem w_150 : Sbrk.pret <+: tci.drop 150 := by decide +kernel
theorem ret_150 (feat : Features) : Dec feat tci 150 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 150) (k := 0) (Sbrk.pret_0 feat) w_150 (Nat.zero_le _)

end FV7z.Tci
