import FV7z.Lemmas.FnSteps
/-!
# The GOT's slots as data of a footprint (PLAN.md M, the PLT contracts)

A PLT stub `jmp qword [rip + d]` reads its slot of the GOT, `[0x792018, 0x792110)` in `7zzs`, so a contract reached
through the PLT asks that these bytes be data of the caller's footprint (`GotF`; `Strlen.GotFoot` is the same).
-/
namespace FV7z

/-- The GOT's slots, `[0x792018, 0x792110)`, bytes of the footprint's data. -/
abbrev GotF (F : Footprint) : Prop := ∀ a : Addr, 0x792018 ≤ a.toNat → a.toNat < 0x792110 → Foot F.data a

end FV7z
