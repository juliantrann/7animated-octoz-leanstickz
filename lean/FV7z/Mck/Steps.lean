import FV7z.Mck.Cuts
import FV7z.Lemmas.Lock4
/-!
# `munmap_chunk`: the steps outside the generated pieces (PLAN.md §M, M1)

- `dec_71`: `lock dec dword [rip + 0x16431a]` (`mp_.n_mmaps` at `0x7929c8`).
- `add_84`: `lock add qword [rip + 0x16431c], rax` (`mp_.mmapped_mem` at `0x7929d8`).
- `jmp_99`: the tail call `jmp __munmap` (`0x6665d0`).
-/
namespace FV7z.Mck
open ZellicX86 Decode FV7z.Leaf

def pd71 : List Byte := [0xf0, 0xff, 0x0d, 0x1a, 0x43, 0x16, 0x00]
theorem pd71_0 : ∀ feat, Dec feat pd71 0 (lockDec32 1458970 7) := by dec_rfl
theorem w_71 : pd71 <+: mck.drop 71 := by decide +kernel
theorem dec_71 (feat : Features) : Dec feat mck 71 (lockDec32 1458970 7) :=
  Dec.shift (j := 71) (k := 0) (pd71_0 feat) w_71 (Nat.zero_le _)

def pa84 : List Byte := [0xf0, 0x48, 0x01, 0x05, 0x1c, 0x43, 0x16, 0x00]
theorem pa84_0 : ∀ feat, Dec feat pa84 0 (lockAdd64r 1458972 0 8) := by dec_rfl
theorem w_84 : pa84 <+: mck.drop 84 := by decide +kernel
theorem add_84 (feat : Features) : Dec feat mck 84 (lockAdd64r 1458972 0 8) :=
  Dec.shift (j := 84) (k := 0) (pa84_0 feat) w_84 (Nat.zero_le _)

def pj99 : List Byte := [0xe9, 0x08, 0x7f, 0x03, 0x00]
theorem pj99_0 : ∀ feat, Dec feat pj99 0 (FV7z.mk .jmp 64 [.rel 229128] 5) := by dec_rfl
theorem w_99 : pj99 <+: mck.drop 99 := by decide +kernel
theorem jmp_99 (feat : Features) : Dec feat mck 99 (FV7z.mk .jmp 64 [.rel 229128] 5) :=
  Dec.shift (j := 99) (k := 0) (pj99_0 feat) w_99 (Nat.zero_le _)

end FV7z.Mck
