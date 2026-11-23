import FV7z.Start.Keep
/-!
# `PtrW` everywhere (PLAN.md G3, startup)

`launch_to_ptr` hands on bytes `W` that agree with the memory at `0x613434` on the data footprint and are
`PtrMem …` where `D` (its data footprint) or the TLS block hold. The steps after it only see `W` through `Agree`,
so `W` may be replaced by bytes that are `W`'s there and `PtrMem …`'s elsewhere: those agree with the memory as
well, and are `PtrMem …`'s at every address apart from the start code's stores. The lemmas about `lif_ok`'s bytes
then get their `D` for free, also for the code pages and the page between `.rodata` and `.data`, which are not
data.

- `ptrW_all`: such bytes.
-/
namespace FV7z.Start
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
open FV7z.StartB (GuardMem PtrMem)
open FV7z.Tls (TlsMem)

open Classical in
/-- Bytes that agree with the memory on `F` and are `PtrMem …`'s at every address apart from the start code's
stores, from bytes that are so where `D` or the TLS block hold, `F`'s data lying there. -/
theorem ptrW_all {K : Ctx} {F : Footprint} {m : Memory} {W V : Addr → Byte} {b : Addr} {ver : BitVec 32}
    {D : Addr → Prop} (hA : Agree F m W) (hW : PtrW K W V b ver D)
    (hF : ∀ a, Foot F.data a → D a ∨ (b.toNat ≤ a.toNat ∧ a.toNat < b.toNat + 8192)) :
    ∃ W' : Addr → Byte, Agree F m W' ∧ PtrW K W' V b ver (fun _ => True) := by
  refine ⟨fun a => if D a ∨ (b.toNat ≤ a.toNat ∧ a.toNat < b.toNat + 8192) then W a else
    PtrMem (VerMem (GuardMem (TlsMem V b) (b + 2176#64)) ver) (b + 2176#64) a, fun a ha => ?_,
    fun a _ hj hp => ?_⟩
  · try dsimp only
    rw [if_pos (hF a ha)]
    exact hA a ha
  · try dsimp only
    by_cases h : D a ∨ (b.toNat ≤ a.toNat ∧ a.toNat < b.toNat + 8192)
    · rw [if_pos h]
      exact hW a h hj hp
    · rw [if_neg h]

end FV7z.Start
