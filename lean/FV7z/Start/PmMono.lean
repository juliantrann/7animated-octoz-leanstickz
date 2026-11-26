import FV7z.Startup.StrAt
import FV7z.Gor.Mem
import FV7z.Start.ToTls
/-!
# The bytes a library contract asks for, weakened (PLAN.md G3, startup)

A contract `Str.LenAt … Pm` asks the bytes at the call to have `Pm`; it holds for any `Q` stronger than `Pm`
(`LenAt.mono`, `NcmpAt.mono`, `RchrAt.mono`, `PcpyAt.mono`). `GotTab`: the GOT as `apply_irel` left it and
`strncmp`'s jump table, what `strncmp` through the PLT asks (`Strncmp.ncmpAt_plt`).
-/
namespace FV7z.Start
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn FV7z.Glibc

/-- The GOT as `apply_irel` left it, and `strncmp`'s jump table. -/
def GotTab (prof : Profile) (W : Addr → Byte) : Prop := GotOkB prof W ∧ NcmpTabV W

variable {prof : Profile} {L : List (Addr × List Byte)} {o : Oracle} {e : Addr} {P Q : (Addr → Byte) → Prop}

theorem LenAt.mono (h : Str.LenAt prof L o e P) (hq : ∀ V, Q V → P V) : Str.LenAt prof L o e Q :=
  fun n c hg hk ha hr hQ => h n c hg hk ha hr (hq _ hQ)

theorem NcmpAt.mono (h : Str.NcmpAt prof L o e P) (hq : ∀ V, Q V → P V) : Str.NcmpAt prof L o e Q :=
  fun m c hg hk ha hr hQ => h m c hg hk ha hr (hq _ hQ)

theorem RchrAt.mono (h : Str.RchrAt prof L o e P) (hq : ∀ V, Q V → P V) : Str.RchrAt prof L o e Q :=
  fun n c hg hk ha hr hQ => h n c hg hk ha hr (hq _ hQ)

theorem PcpyAt.mono (h : Gor.PcpyAt prof L o e P) (hq : ∀ V, Q V → P V) : Gor.PcpyAt prof L o e Q :=
  fun c hg hk ha hr hQ => h c hg hk ha hr (hq _ hQ)

end FV7z.Start
