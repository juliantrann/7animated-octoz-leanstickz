import FV7z.Lemmas.FnSteps
/-!
# The bytes of `7zzs`'s data the PLT contracts read (PLAN.md M, the PLT contracts)

A PLT stub `jmp qword [rip + d]` reads its slot of the GOT, `[0x792018, 0x792110)` in `7zzs`, and `memmove`'s copies
of more than 128 bytes read `__x86_shared_non_temporal_threshold`, `[0x7a8428, 0x7a8430)`, and `__strncmp_sse2`
reads its jump table in `.rodata`, `[0x6f0df0, 0x6f0e30)`; so a contract reached through the PLT asks that these
bytes be data of the caller's footprint (`GotF`; `Strlen.GotFoot` is its `got`). The table's values, as in the
binary, are `ncmpTab` (`NcmpTabV`, for the caller's `Pm`).
-/
namespace FV7z
open ZellicX86 Decode FV7z.Leaf FV7z.Fn

/-- The GOT's slots, `[0x792018, 0x792110)`, the threshold of `memmove`'s non-temporal copies,
`[0x7a8428, 0x7a8430)`, and `strncmp`'s jump table, `[0x6f0df0, 0x6f0e30)`: bytes of the footprint's data. -/
structure GotF (F : Footprint) : Prop where
  got : ∀ a : Addr, 0x792018 ≤ a.toNat → a.toNat < 0x792110 → Foot F.data a
  thr : ∀ a : Addr, 0x7a8428 ≤ a.toNat → a.toNat < 0x7a8430 → Foot F.data a
  ntab : ∀ a : Addr, 0x6f0df0 ≤ a.toNat → a.toNat < 0x6f0e30 → Foot F.data a

/-- `GotF` of a footprint with more data. -/
theorem GotF.mono {F F' : Footprint} (h : GotF F) (hF : ∀ a, Foot F.data a → Foot F'.data a) : GotF F' :=
  ⟨fun a h1 h2 => hF _ (h.got a h1 h2), fun a h1 h2 => hF _ (h.thr a h1 h2), fun a h1 h2 => hF _ (h.ntab a h1 h2)⟩

/-- `__strncmp_sse2`'s jump table at `0x6f0df0`: 16 offsets from it, of the code for each difference of the strings'
offsets in their 16 bytes. -/
def ncmpTab : List Byte := [0xc0, 0x97, 0xf4, 0xff, 0x40, 0x99, 0xf4, 0xff, 0xc0, 0x9a, 0xf4, 0xff, 0x40, 0x9c,
  0xf4, 0xff, 0xc0, 0x9d, 0xf4, 0xff, 0x40, 0x9f, 0xf4, 0xff, 0xc0, 0xa0, 0xf4, 0xff, 0x40, 0xa2, 0xf4, 0xff, 0xc0,
  0xa3, 0xf4, 0xff, 0x40, 0xa5, 0xf4, 0xff, 0xc0, 0xa6, 0xf4, 0xff, 0x40, 0xa8, 0xf4, 0xff, 0xc0, 0xa9, 0xf4, 0xff,
  0x40, 0xab, 0xf4, 0xff, 0xc0, 0xac, 0xf4, 0xff, 0xf0, 0x96, 0xf4, 0xff]

/-- The bytes `V` have `strncmp`'s jump table. -/
def NcmpTabV (V : Addr → Byte) : Prop := ∀ i < 64, V ((0x6f0df0 : Addr).add i) = ncmpTab.getD i 0

end FV7z
