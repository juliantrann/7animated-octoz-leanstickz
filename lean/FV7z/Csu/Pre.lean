import FV7z.Csu.Holds
import FV7z.Eli.Holds
/-!
# `elision_init` as `__libc_csu_init` calls it (PLAN.md G3, startup)

The one entry of `.preinit_array` of `7zzs` (`elision_init` at `0x5ffc50`, the function 0 of `Csu.csu_ok`), by
`Eli.eli_ok`: it stores below the frame of `__libc_csu_init` and into `__elision_aconf.retry_try_xbegin` only.

- `eli_runs`: `Runs` for the function 0, for any invariant whose `I 0` has the five `glibc.elision.*` tunables not
  set and gives `I 1` whatever these bytes become.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn FV7z.Start
namespace FV7z.Csu

variable {F : Footprint} {Wl : List Rgn}
variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {I : Nat → (Addr → Byte) → Prop} {sp : Addr} {tg : Nat → Addr} {a₀ a₁ a₂ : BitVec 64}

theorem sp_n {sp : Addr} (h : 64 ≤ sp.toNat) : (sp - 64#64).toNat = sp.toNat - 64 := by bv_omega

/-- `elision_init` is a function as `csu_ok` asks: it keeps the frame of `__libc_csu_init` and the arrays. -/
theorem eli_runs {fb : Addr} (c : Seg prof F Wl L s₀ o) (hfs : s₀.cpu.seg.fsBase = fb) (hC : Env F Wl L sp tg)
    (hE : Eli.Env F Wl L fb (sp - 64#64)) (h0 : tg 0 = Eli.eli_at)
    (hU : ∀ V, I 0 V → Tgv.Unset F V 5 ∧ Tgv.Unset F V 7 ∧ Tgv.Unset F V 17 ∧ Tgv.Unset F V 4 ∧ Tgv.Unset F V 13)
    (h01 : ∀ V V', I 0 V → (∀ a : Addr, ¬ (sp.toNat - 96 ≤ a.toNat ∧ a.toNat < sp.toNat - 64) →
      ¬ (7938696 ≤ a.toNat ∧ a.toNat < 7938700) → V' a = V a) → I 1 V') :
    Runs prof F Wl L s₀ o gev gP gE I sp a₀ a₁ a₂ 0 (tg 0) := by
  intro X t V j₂ hK hA hI0 hr hsp _ hj hra k
  obtain ⟨h5, h7, h17, h4, h13⟩ := hU V hI0
  have hs0 := hC.s0
  have hhi := hE.hi
  have n := sp_n hs0
  rw [n] at hhi
  refine Eli.eli_ok c hfs (hsp ▸ hE) hK hA (hr.trans h0) h5 h7 h17 h4 h13 hC.code hj (by rw [hsp]; exact hra) ?_
  intro V' Z t' hKZ hAZ ho hz hrZ hbk
  rw [hsp, n] at ho
  exact k Z t' V' hKZ hAZ (h01 V V' hI0 fun a h1 h2 => ho a (by omega) h2) (fun a ha => ho a (by omega) (by omega))
    (fun a ha => ho a (by omega) (by omega)) hrZ hbk

end FV7z.Csu
