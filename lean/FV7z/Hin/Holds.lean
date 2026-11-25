import FV7z.Hin.VcA
import FV7z.Hin.VcB
/-!
# `handle_intel` keeps its contract (PLAN.md M, ctor 103)

The cut points' conditions from `VcA.lean` and `VcB.lean` put together by `cfgAt`, with `intel_check_word`'s contract
(`Icw.icw_fnK`) at its four calls, and the `ret` at 1598. Needs H-CPU-cache (`Glibc.CacheEnds`) for
`intel_check_word`.
-/
namespace FV7z.Hin
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
open FV7z.Hca (hca hca_at hca_length)

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle} {F : Footprint} {Wl : List Rgn}
  {fb : Addr} {g₀ g : Gprs} {V₀ V : Addr → Byte}

theorem vcAll (hT : Te F Wl L fb g₀ V₀) (hin : CodeIn L hca_at hca) (ℓ : Nat) :
    ∀ n g f V, Ih fb g₀ V₀ ℓ n g V → WtC prof F Wl L fb ℓ (Nx fb g₀ V₀ n) g f V := by
  intro n g f V h
  by_cases h1280 : ℓ = 1280
  · subst h1280; exact vc_1280 (f := f) hT h
  by_cases h1371 : ℓ = 1371
  · subst h1371; exact vc_1371 (f := f) h
  by_cases h1376 : ℓ = 1376
  · subst h1376; exact vc_1376 h
  by_cases h1378 : ℓ = 1378
  · subst h1378; exact vc_1378 (f := f) hT h
  by_cases h1403 : ℓ = 1403
  · subst h1403; exact vc_1403 (f := f) h
  by_cases h1422 : ℓ = 1422
  · subst h1422; exact vc_1422 (f := f) hT hin h
  by_cases h1427 : ℓ = 1427
  · subst h1427; exact vc_1427 (f := f) h
  by_cases h1457 : ℓ = 1457
  · subst h1457; exact vc_1457 (f := f) hT hin h
  by_cases h1462 : ℓ = 1462
  · subst h1462; exact vc_1462 (f := f) h
  by_cases h1489 : ℓ = 1489
  · subst h1489; exact vc_1489 (f := f) hT hin h
  by_cases h1494 : ℓ = 1494
  · subst h1494; exact vc_1494 (f := f) hT h
  by_cases h1522 : ℓ = 1522
  · subst h1522; exact vc_1522 (f := f) hT hin h
  by_cases h1527 : ℓ = 1527
  · subst h1527; exact vc_1527 (f := f) hT h
  by_cases h1568 : ℓ = 1568
  · subst h1568; exact vc_1568 (f := f) hT h
  · simp only [Ih, h1280, h1371, h1376, h1378, h1403, h1422, h1427, h1457, h1462, h1489, h1494, h1522, h1527,
      h1568, ↓reduceIte] at h

/-- From the `ret`'s `Fh` to `Rh` after it. -/
theorem rh_of {j : Nat} (hF : Fh g₀ V₀ j g V) : Rh g₀ V₀ (g.set 4 (g.rsp + 8)) V := by
  obtain ⟨-, hs, hb, hp, h12, h13, h14, h15, hK⟩ := hF
  cases g
  exact ⟨congrArg (· + 8) hs, hb, hp, h12, h13, h14, h15, hK⟩

/-- `handle_intel` in a run with its code and the `fs` base `fb`, on processors whose leaf 4 ends (H-CPU-cache). -/
theorem hin_fnK (hC : Glibc.CacheEnds prof) (c : Seg prof F Wl L s₀ o) (hfs : s₀.cpu.seg.fsBase = fb)
    (hin : CodeIn L hca_at hca) : FnK prof F Wl L s₀ o hin_at (Te F Wl L fb) Rh := by
  have hi := Icw.icw_fnK hC c hin
  refine ⟨?_⟩
  intro gev gP gE X t V hK hA hrip hT k
  refine cfgAt (spC c hfs hin hi) (fun ℓ n g _ V' => Ih fb X.cpu.gpr V ℓ n g V')
    (fun j g _ V' => Fh X.cpu.gpr V j g V') (fun ℓ n g f V' h => vcAll hT hin ℓ n g f V' h) ?_ 25700 1280 hK hA
    (hrip.trans hin_at_eq.symm) ⟨rfl, rfl, rfl⟩
  intro j g fl V' hF Y t' hKY hAY hrY hg _
  have hF' := hF
  obtain ⟨rfl, hs, -, -, -, -, -, -, hV⟩ := hF
  obtain ⟨e₂, code₂, j₂, hin₂, hj₂, hra⟩ := hT.ret
  have hl : ∀ i < 8, Foot F.data (Addr.add Y.cpu.gpr.rsp i) := by
    rw [hg, hs]; exact fD hT (by omega) (by omega)
  have hra' : ofBytesLE 64 ((byteAddrs Y.cpu.gpr.rsp 8).map V') = e₂.add j₂ := by
    rw [hg, hs, rd_keepH hT hV]; exact hra
  refine c.s_ret hKY hAY hin (lt_len (by decide)) hrY (ret_1598 prof.feat) hl hin₂ hj₂ hra' ?_
  rintro Z t₂ hKZ hAZ ⟨hrZ, hgZ⟩
  exact k Z t₂ V' hKZ hAZ (hrZ.trans hra.symm) (by rw [hgZ, hg]; exact rh_of hF')

end FV7z.Hin
