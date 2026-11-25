import FV7z.Strlen.Entry
import FV7z.Startup.StrAt
/-!
# `__strlen_sse2` meets `Str.LenAt` (PLAN.md M, the PLT contracts)

Wherever the code of `__strlen_sse2` (`Strlen/Code.lean`, at `0x6546d0` in `7zzs`) is in the list, a call there does
what `Str.LenAt` says, for any `Pm`: `Strlen.run` with the call's registers, its return address and the string.
The PLT stub at `0x401108` jumping through the GOT to it is a separate step.
-/
namespace FV7z.Strlen
open ZellicX86 Decode FV7z.Leaf FV7z.Fn

theorem addr_add_zero (e : Addr) : Addr.add e 0 = e := by
  apply BitVec.eq_of_toNat_eq
  have := e.isLt
  simp only [Addr.add, BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

theorem lenAt_sse2 {prof : Profile} {L : List (Addr × List Byte)} {o : Oracle} {e : Addr}
    {Pm : (Addr → Byte) → Prop} (hin : CodeIn L e sl2) : Str.LenAt prof L o e Pm := by
  intro F Wl s₀ gev gP gE X t V e' code j n c hK hA hrip _ hin₂ hj hra hl hov hnz hz hft K
  exact run c hin hK hA (by rw [hrip, addr_add_zero]) (by unfold Kp; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩)
    hov hnz hz hft (by unfold Ret; exact ⟨hl, e', code, j, hin₂, hj, hra, K⟩)

end FV7z.Strlen
