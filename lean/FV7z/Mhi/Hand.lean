import FV7z.Mhi.Cuts
import FV7z.Tci.Hand
import FV7z.Pmi.Code
/-!
# `malloc_hook_ini`: the instructions outside the blocks (PLAN.md G3, `malloc`)

Decoded at their offsets:

- `call_336`: the `call` of `ptmalloc_init`, with its target `tgt_336`;
- `call_231`: the `call` of `tcache_init`, with its target `tgt_231`;
- `call_125`: the `call` of `_int_malloc`, with its target `tgt_125`;
- `ret_187`: the `ret`.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Mhi

/-- `call ptmalloc_init`. -/
def pc336 : List Byte := [0xe8, 0x7b, 0xf4, 0xff, 0xff]
theorem pc336_0 : ∀ feat, Dec feat pc336 0 (FV7z.mk .call 64 [.rel 18446744073709548667] 5) := by dec_rfl
theorem w_336 : pc336 <+: mhi.drop 336 := by decide +kernel
theorem call_336 (feat : Features) : Dec feat mhi 336 (FV7z.mk .call 64 [.rel 18446744073709548667] 5) :=
  Dec.shift (j := 336) (k := 0) (pc336_0 feat) w_336 (Nat.zero_le _)

/-- The `call` at 336 goes to `ptmalloc_init`. -/
theorem tgt_336 : mhi_at.add (336 + 5) + BitVec.ofNat 64 18446744073709548667 = Pmi.pmi_at := by decide

/-- `call tcache_init`. -/
def pc231 : List Byte := [0xe8, 0xd4, 0xed, 0xff, 0xff]
theorem pc231_0 : ∀ feat, Dec feat pc231 0 (FV7z.mk .call 64 [.rel 18446744073709546964] 5) := by dec_rfl
theorem w_231 : pc231 <+: mhi.drop 231 := by decide +kernel
theorem call_231 (feat : Features) : Dec feat mhi 231 (FV7z.mk .call 64 [.rel 18446744073709546964] 5) :=
  Dec.shift (j := 231) (k := 0) (pc231_0 feat) w_231 (Nat.zero_le _)

/-- The `call` at 231 goes to `tcache_init`. -/
theorem tgt_231 : mhi_at.add (231 + 5) + BitVec.ofNat 64 18446744073709546964 = Tci.tci_at := by decide

/-- `call _int_malloc`. -/
def pc125 : List Byte := [0xe8, 0xbe, 0xdf, 0xff, 0xff]
theorem pc125_0 : ∀ feat, Dec feat pc125 0 (FV7z.mk .call 64 [.rel 18446744073709543358] 5) := by dec_rfl
theorem w_125 : pc125 <+: mhi.drop 125 := by decide +kernel
theorem call_125 (feat : Features) : Dec feat mhi 125 (FV7z.mk .call 64 [.rel 18446744073709543358] 5) :=
  Dec.shift (j := 125) (k := 0) (pc125_0 feat) w_125 (Nat.zero_le _)

/-- The `call` at 125 goes to `_int_malloc`. -/
theorem tgt_125 : mhi_at.add (125 + 5) + BitVec.ofNat 64 18446744073709543358 = Imm.imm_at := by decide

theorem w_187 : Sbrk.pret <+: mhi.drop 187 := by decide +kernel
theorem ret_187 (feat : Features) : Dec feat mhi 187 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 187) (k := 0) (Sbrk.pret_0 feat) w_187 (Nat.zero_le _)

end FV7z.Mhi
