import FV7z.Lemmas.FnSteps
/-!
# The bytes of `7zzs`'s data the PLT contracts read (PLAN.md M, the PLT contracts)

A PLT stub `jmp qword [rip + d]` reads its slot of the GOT, `[0x792018, 0x792110)` in `7zzs`, and `memmove`'s copies
of more than 128 bytes read `__x86_shared_non_temporal_threshold`, `[0x7a8428, 0x7a8430)`; so a contract reached
through the PLT asks that these bytes be data of the caller's footprint (`GotF`; `Strlen.GotFoot` is its `got`).
-/
namespace FV7z
open ZellicX86 Decode FV7z.Leaf FV7z.Fn

/-- The GOT's slots, `[0x792018, 0x792110)`, and the threshold of `memmove`'s non-temporal copies,
`[0x7a8428, 0x7a8430)`: bytes of the footprint's data. -/
structure GotF (F : Footprint) : Prop where
  got : ∀ a : Addr, 0x792018 ≤ a.toNat → a.toNat < 0x792110 → Foot F.data a
  thr : ∀ a : Addr, 0x7a8428 ≤ a.toNat → a.toNat < 0x7a8430 → Foot F.data a

end FV7z
