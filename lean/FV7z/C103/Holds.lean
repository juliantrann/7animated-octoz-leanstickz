import FV7z.C103.VcC
/-!
# `init_cacheinfo` keeps its contract (PLAN.md M, ctor 103)

The cut points' conditions from `VcA.lean`, `VcB.lean` and `VcC.lean` put together by `cfgAt`, and the `ret` at 3731.
Needs H-CPU-cache (`Glibc.CacheEnds`) for the subleaf loops of leaves 4 and `0xB`, and `handle_intel`'s and
`handle_amd`'s contracts at their calls (from `spC`).
-/
namespace FV7z.C103
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
open FV7z.Ctor (sti sti_at sti_length)
open FV7z.Hca (hca hca_at)

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle} {F : Footprint} {Wl : List Rgn}
  {fb : Addr} {g₀ g : Gprs} {V₀ V : Addr → Byte}

theorem vcAll (hC : Glibc.CacheEnds prof) (hT : Te F Wl L fb g₀ V₀) (hin : CodeIn L sti_at sti) (ℓ : Nat) :
    ∀ n g f V, Ih g₀ V₀ ℓ n g V → WtC prof F Wl L fb ℓ (Nx g₀ V₀ n) g f V := by
  intro n g f V h
  by_cases h3504 : ℓ = 3504
  · subst h3504; exact vc_3504 (f := f) hT h
  by_cases h3566 : ℓ = 3566
  · subst h3566; exact vc_3566 (f := f) h
  by_cases h3569 : ℓ = 3569
  · subst h3569; exact vc_3569 (f := f) hT h
  by_cases h3617 : ℓ = 3617
  · subst h3617; exact vc_3617 (f := f) hT h
  by_cases h3629 : ℓ = 3629
  · subst h3629; exact vc_3629 (f := f) h
  by_cases h3632 : ℓ = 3632
  · subst h3632; exact vc_3632 (f := f) hT h
  by_cases h3680 : ℓ = 3680
  · subst h3680; exact vc_3680 (f := f) hT h
  by_cases h3707 : ℓ = 3707
  · subst h3707; exact vc_3707 (f := f) h
  by_cases h3710 : ℓ = 3710
  · subst h3710; exact vc_3710 (f := f) hT h
  by_cases h3758 : ℓ = 3758
  · subst h3758; exact vc_3758 (f := f) hT hin h
  by_cases h3763 : ℓ = 3763
  · subst h3763; exact vc_3763 (f := f) h
  by_cases h3771 : ℓ = 3771
  · subst h3771; exact vc_3771 (f := f) hT hin h
  by_cases h3776 : ℓ = 3776
  · subst h3776; exact vc_3776 (f := f) h
  by_cases h3784 : ℓ = 3784
  · subst h3784; exact vc_3784 (f := f) hT hin h
  by_cases h3789 : ℓ = 3789
  · subst h3789; exact vc_3789 (f := f) h
  by_cases h3809 : ℓ = 3809
  · subst h3809; exact vc_3809 (f := f) hT h
  by_cases h3841 : ℓ = 3841
  · subst h3841; exact vc_3841 (f := f) h
  by_cases h3858 : ℓ = 3858
  · subst h3858; exact vc_3858 (f := f) h
  by_cases h3865 : ℓ = 3865
  · subst h3865; exact vc_3865 (f := f) hC h
  by_cases h3867 : ℓ = 3867
  · subst h3867; exact vc_3867 (f := f) h
  by_cases h3921 : ℓ = 3921
  · subst h3921; exact vc_3921 (f := f) h
  by_cases h3929 : ℓ = 3929
  · subst h3929; exact vc_3929 (f := f) h
  by_cases h4306 : ℓ = 4306
  · subst h4306; exact vc_4306 (f := f) h
  by_cases h4332 : ℓ = 4332
  · subst h4332; exact vc_4332 (f := f) h
  by_cases h4346 : ℓ = 4346
  · subst h4346; exact vc_4346 (f := f) hC h
  by_cases h4348 : ℓ = 4348
  · subst h4348; exact vc_4348 (f := f) h
  by_cases h4380 : ℓ = 4380
  · subst h4380; exact vc_4380 (f := f) h
  by_cases h4384 : ℓ = 4384
  · subst h4384; exact vc_4384 (f := f) h
  by_cases h4329 : ℓ = 4329
  · subst h4329; exact vc_4329 (f := f) h
  by_cases h4454 : ℓ = 4454
  · subst h4454; exact vc_4454 (f := f) h
  by_cases h4457 : ℓ = 4457
  · subst h4457; exact vc_4457 (f := f) h
  by_cases h4594 : ℓ = 4594
  · subst h4594; exact vc_4594 (f := f) h
  by_cases h4598 : ℓ = 4598
  · subst h4598; exact vc_4598 (f := f) h
  by_cases h4469 : ℓ = 4469
  · subst h4469; exact vc_4469 (f := f) h
  by_cases h4409 : ℓ = 4409
  · subst h4409; exact vc_4409 (f := f) h
  by_cases h4502 : ℓ = 4502
  · subst h4502; exact vc_4502 (f := f) hT h
  by_cases h4570 : ℓ = 4570
  · subst h4570; exact vc_4570 (f := f) h
  by_cases h3960 : ℓ = 3960
  · subst h3960; exact vc_3960 (f := f) hT h
  by_cases h3967 : ℓ = 3967
  · subst h3967; exact vc_3967 (f := f) h
  by_cases h3981 : ℓ = 3981
  · subst h3981; exact vc_3981 (f := f) h
  by_cases h3984 : ℓ = 3984
  · subst h3984; exact vc_3984 (f := f) h
  by_cases h3987 : ℓ = 3987
  · subst h3987; exact vc_3987 (f := f) h
  by_cases h4005 : ℓ = 4005
  · subst h4005; exact vc_4005 (f := f) h
  by_cases h4008 : ℓ = 4008
  · subst h4008; exact vc_4008 (f := f) h
  by_cases h4011 : ℓ = 4011
  · subst h4011; exact vc_4011 (f := f) h
  by_cases h4014 : ℓ = 4014
  · subst h4014; exact vc_4014 (f := f) hT h
  by_cases h4040 : ℓ = 4040
  · subst h4040; exact vc_4040 (f := f) hT hin h
  by_cases h4045 : ℓ = 4045
  · subst h4045; exact vc_4045 (f := f) h
  by_cases h4053 : ℓ = 4053
  · subst h4053; exact vc_4053 (f := f) hT hin h
  by_cases h4058 : ℓ = 4058
  · subst h4058; exact vc_4058 (f := f) h
  by_cases h4066 : ℓ = 4066
  · subst h4066; exact vc_4066 (f := f) hT hin h
  by_cases h4071 : ℓ = 4071
  · subst h4071; exact vc_4071 (f := f) h
  by_cases h4079 : ℓ = 4079
  · subst h4079; exact vc_4079 (f := f) h
  by_cases h4081 : ℓ = 4081
  · subst h4081; exact vc_4081 (f := f) h
  by_cases h4100 : ℓ = 4100
  · subst h4100; exact vc_4100 (f := f) h
  by_cases h4102 : ℓ = 4102
  · subst h4102; exact vc_4102 (f := f) h
  by_cases h4197 : ℓ = 4197
  · subst h4197; exact vc_4197 (f := f) h
  by_cases h4199 : ℓ = 4199
  · subst h4199; exact vc_4199 (f := f) h
  by_cases h4216 : ℓ = 4216
  · subst h4216; exact vc_4216 (f := f) h
  by_cases h4223 : ℓ = 4223
  · subst h4223; exact vc_4223 (f := f) h
  by_cases h4226 : ℓ = 4226
  · subst h4226; exact vc_4226 (f := f) h
  by_cases h4125 : ℓ = 4125
  · subst h4125; exact vc_4125 (f := f) h
  by_cases h4128 : ℓ = 4128
  · subst h4128; exact vc_4128 (f := f) h
  by_cases h4141 : ℓ = 4141
  · subst h4141; exact vc_4141 (f := f) h
  by_cases h4143 : ℓ = 4143
  · subst h4143; exact vc_4143 (f := f) h
  by_cases h4148 : ℓ = 4148
  · subst h4148; exact vc_4148 (f := f) hT h
· simp only [Ih, h3504, h3566, h3569, h3617, h3629, h3632, h3680, h3707, h3710, h3758, h3763, h3771, h3776, h3784,
      h3789, h3809, h3841, h3858, h3865, h3867, h3921, h3929, h4306, h4332, h4346, h4348, h4380, h4384, h4329, h4454,
      h4457, h4594, h4598, h4469, h4409, h4502, h4570, h3960, h3967, h3981, h3984, h3987, h4005, h4008, h4011, h4014,
      h4040, h4045, h4053, h4058, h4066, h4071, h4079, h4081, h4100, h4102, h4197, h4199, h4216, h4223, h4226, h4125,
      h4128, h4141, h4143, h4148, ↓reduceIte] at h

/-- From the `ret`'s `Fh` to `Rc` after it. -/
theorem rc_of {j : Nat} (hF : Fh g₀ V₀ j g V) : Rc g₀ V₀ (g.set 4 (g.rsp + 8)) V := by
  obtain ⟨-, hs, hb, hp, h12, h13, h14, h15, hK⟩ := hF
  cases g
  exact ⟨congrArg (· + 8) hs, hb, hp, h12, h13, h14, h15, hK⟩

/-- `init_cacheinfo` in a run with its code (and `handle_intel`'s and `handle_amd`'s), the `fs` base `fb`, on
processors whose leaves 4 and `0xB` end (H-CPU-cache). -/
theorem c103_fnK (hC : Glibc.CacheEnds prof) (c : Seg prof F Wl L s₀ o) (hfs : s₀.cpu.seg.fsBase = fb)
    (hin : CodeIn L sti_at sti) (hinH : CodeIn L hca_at hca) :
    FnK prof F Wl L s₀ o c103_at (Te F Wl L fb) Rc := by
  refine ⟨?_⟩
  intro gev gP gE X t V hK hA hrip hT k
  refine cfgAt (spC hC c hfs hin hinH) (fun ℓ n g _ V' => Ih X.cpu.gpr V ℓ n g V')
    (fun j g _ V' => Fh X.cpu.gpr V j g V') (fun ℓ n g f V' h => vcAll hC hT hin ℓ n g f V' h) ?_ 100000 3504 hK
    hA (hrip.trans c103_at_eq.symm) ⟨rfl, rfl, rfl⟩
  intro j g fl V' hF Y t' hKY hAY hrY hg _
  have hF' := hF
  obtain ⟨rfl, hs, -, -, -, -, -, -, hV⟩ := hF
  obtain ⟨e₂, code₂, j₂, hin₂, hj₂, hra⟩ := hT.ret
  have hl : ∀ i < 8, Foot F.data (Addr.add Y.cpu.gpr.rsp i) := by
    rw [hg, hs]; exact fD hT (by omega) (by omega)
  have hra' : ofBytesLE 64 ((byteAddrs Y.cpu.gpr.rsp 8).map V') = e₂.add j₂ := by
    rw [hg, hs, rd_kd hT hV]; exact hra
  refine c.s_ret hKY hAY hin (lt_len (by decide)) hrY (rt3731 prof.feat) hl hin₂ hj₂ hra' ?_
  rintro Z t₂ hKZ hAZ ⟨hrZ, hgZ⟩
  exact k Z t₂ V' hKZ hAZ (hrZ.trans hra.symm) (by rw [hgZ, hg]; exact rc_of hF')

end FV7z.C103
