import FV7z.Ild.Cuts
import FV7z.Sbrk.Holds
/-!
# `_nl_intern_locale_data`: the steps outside the generated pieces (PLAN.md §M, M1)

- `call_122`, `ml_122`: the `call` of `malloc` (`0x633160`) with `rdi = 8N + 64`.
- `call_243`, `fr_243`: the `call` of `free` (`0x633750`) with `rdi` the new block, on the way to `EINVAL`.
- `ret_278`: the `ret`.
- `jt_case`, `cs_ok`: the jump table's 13 entries lead to the cases `ild_cases`, inside the code.
-/
namespace FV7z.Ild
open ZellicX86 Decode FV7z.Leaf

def pc122 : List Byte := [0xe8, 0xd1, 0xde, 0x01, 0x00]
theorem pc122_0 : ∀ feat, Dec feat pc122 0 (FV7z.mk .call 64 [.rel 122577] 5) := by dec_rfl
theorem w_122 : pc122 <+: ild.drop 122 := by decide +kernel
theorem call_122 (feat : Features) : Dec feat ild 122 (FV7z.mk .call 64 [.rel 122577] 5) :=
  Dec.shift (j := 122) (k := 0) (pc122_0 feat) w_122 (Nat.zero_le _)

def pc243 : List Byte := [0xe8, 0x48, 0xe4, 0x01, 0x00]
theorem pc243_0 : ∀ feat, Dec feat pc243 0 (FV7z.mk .call 64 [.rel 123976] 5) := by dec_rfl
theorem w_243 : pc243 <+: ild.drop 243 := by decide +kernel
theorem call_243 (feat : Features) : Dec feat ild 243 (FV7z.mk .call 64 [.rel 123976] 5) :=
  Dec.shift (j := 243) (k := 0) (pc243_0 feat) w_243 (Nat.zero_le _)

theorem w_278 : Sbrk.pret <+: ild.drop 278 := by decide +kernel
theorem ret_278 (feat : Features) : Dec feat ild 278 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 278) (k := 0) (Sbrk.pret_0 feat) w_278 (Nat.zero_le _)

/-- The `call` at 122 is of `malloc` (`0x633160`), the one at 243 of `free` (`0x633750`). -/
theorem ml_122 : ild_at.add (122 + 5) + BitVec.ofNat 64 122577 = 0x633160 := by decide
theorem fr_243 : ild_at.add (243 + 5) + BitVec.ofNat 64 123976 = 0x633750 := by decide

/-- The jump table's entries, from `0x6ee9e0` (`7268832`): the cases. -/
theorem jt_case : ∀ k < 13, (ofBytesLE 32 ((ild_jt.drop (4 * k)).take 4)).signExtend 64 + 7268832#64 =
    Addr.add ild_at (ild_cases.getD k 0) := by decide +kernel

theorem cs_ok : ∀ k < 13, ild_cases.getD k 0 < 485 := by decide +kernel

end FV7z.Ild
