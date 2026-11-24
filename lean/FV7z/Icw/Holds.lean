import FV7z.Icw.VcA
import FV7z.Icw.VcB
/-!
# `intel_check_word` keeps its contract (PLAN.md M, ctor 103)

The cut points' conditions from `VcA.lean` and `VcB.lean` put together by `cfgAt`, and the `ret` at 729 or 765.
Needs H-CPU-cache (`Glibc.CacheEnds`) for the subleaf loops of leaf 4.
-/
namespace FV7z.Icw
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
open FV7z.Hca (hca hca_at hca_length lt_len)

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle} {F : Footprint} {Wl : List Rgn}
  {g₀ g : Gprs} {V₀ V : Addr → Byte}

theorem vcAll (hC : Glibc.CacheEnds prof) (hT : Te F Wl L g₀ V₀) (ℓ : Nat) :
    ∀ n g f V, Ih g₀ V₀ ℓ n g V → WtC prof F Wl ℓ (Nx g₀ V₀ n) g f V := by
  intro n g f V h
  by_cases h464 : ℓ = 464
  · subst h464; exact vc_464 (f := f) hT h
  by_cases h558 : ℓ = 558
  · subst h558; exact vc_558 (f := f) h
  by_cases h567 : ℓ = 567
  · subst h567; exact vc_567 (f := f) hT h
  by_cases h630 : ℓ = 630
  · subst h630; exact vc_630 (f := f) h
  by_cases h640 : ℓ = 640
  · subst h640; exact vc_640 (f := f) hT h
  by_cases h656 : ℓ = 656
  · subst h656; exact vc_656 (f := f) hT h
  by_cases h682 : ℓ = 682
  · subst h682; exact vc_682 (f := f) hT h
  by_cases h717 : ℓ = 717
  · subst h717; exact vc_717 (f := f) h
  by_cases h719 : ℓ = 719
  · subst h719; exact vc_719 (f := f) hT h
  by_cases h752 : ℓ = 752
  · subst h752; exact vc_752 (f := f) h
  by_cases h773 : ℓ = 773
  · subst h773; exact vc_773 h
  by_cases h775 : ℓ = 775
  · subst h775; exact vc_775 (f := f) h
  by_cases h821 : ℓ = 821
  · subst h821; exact vc_821 (f := f) h
  by_cases h829 : ℓ = 829
  · subst h829; exact vc_829 hC h
  by_cases h831 : ℓ = 831
  · subst h831; exact vc_831 (f := f) h
  by_cases h838 : ℓ = 838
  · subst h838; exact vc_838 (f := f) h
  by_cases h856 : ℓ = 856
  · subst h856; exact vc_856 (f := f) h
  by_cases h866 : ℓ = 866
  · subst h866; exact vc_866 (f := f) h
  by_cases h885 : ℓ = 885
  · subst h885; exact vc_885 (f := f) h
  by_cases h1033 : ℓ = 1033
  · subst h1033; exact vc_1033 (f := f) h
  by_cases h1048 : ℓ = 1048
  · subst h1048; exact vc_1048 (f := f) h
  by_cases h1230 : ℓ = 1230
  · subst h1230; exact vc_1230 (f := f) h
  by_cases h1250 : ℓ = 1250
  · subst h1250; exact vc_1250 (f := f) h
  by_cases h1258 : ℓ = 1258
  · subst h1258; exact vc_1258 hC h
  by_cases h1260 : ℓ = 1260
  · subst h1260; exact vc_1260 (f := f) h
  · simp only [Ih, h464, h558, h567, h630, h640, h656, h682, h717, h719, h752, h773, h775, h821, h829, h831,
      h838, h856, h866, h885, h1033, h1048, h1230, h1250, h1258, h1260, ↓reduceIte] at h

/-- From a `ret`'s `Fh` to `Rh` after it. -/
theorem rh_of {j : Nat} (hF : Fh g₀ V₀ j g V) : Rh g₀ V₀ (g.set 4 (g.rsp + 8)) V := by
  obtain ⟨-, hs, hb, hp, h12, h13, h14, h15, hK⟩ := hF
  cases g
  exact ⟨congrArg (· + 8) hs, hb, hp, h12, h13, h14, h15, hK⟩

/-- `intel_check_word` in a run with its code, on processors whose leaf 4 ends (H-CPU-cache). -/
theorem icw_fnK (hC : Glibc.CacheEnds prof) (c : Seg prof F Wl L s₀ o) (hin : CodeIn L hca_at hca) :
    FnK prof F Wl L s₀ o icw_at (Te F Wl L) Rh := by
  refine ⟨?_⟩
  intro gev gP gE X t V hK hA hrip hT k
  refine cfgAt (spC c hin) (fun ℓ n g _ V' => Ih X.cpu.gpr V ℓ n g V') (fun j g _ V' => Fh X.cpu.gpr V j g V')
    (fun ℓ n g f V' h => vcAll hC hT ℓ n g f V' h) ?_ (1000 * 4294967296 + 2000) 464 hK hA
    (hrip.trans icw_at_eq.symm) ⟨rfl, rfl, rfl⟩
  intro j g fl V' hF Y t' hKY hAY hrY hg _
  have hF' := hF
  obtain ⟨hj, hs, -, -, -, -, -, -, hV⟩ := hF
  obtain ⟨e₂, code₂, j₂, hin₂, hj₂, hra⟩ := hT.ret
  have hl : ∀ i < 8, Foot F.data (Addr.add Y.cpu.gpr.rsp i) := by
    rw [hg, hs]; exact (ld5 hT.ld).2.2.2.2
  have hra' : ofBytesLE 64 ((byteAddrs Y.cpu.gpr.rsp 8).map V') = e₂.add j₂ := by
    rw [hg, hs, rd_keep hT hV]; exact hra
  refine c.s_ret hKY hAY hin (ret_at prof.feat hj).1 hrY (ret_at prof.feat hj).2 hl hin₂ hj₂ hra' ?_
  rintro Z t₂ hKZ hAZ ⟨hrZ, hgZ⟩
  exact k Z t₂ V' hKZ hAZ (hrZ.trans hra.symm) (by rw [hgZ, hg]; exact rh_of hF')

end FV7z.Icw
