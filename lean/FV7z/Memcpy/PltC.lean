import FV7z.Memcpy.Plt
import FV7z.Memcpy.EntryE
/-!
# The contracts of `memcpy` and `mempcpy` through the PLT (PLAN.md M, the PLT contracts)

A call at `0x401070` (`memcpy`) or `0x4010c0` (`mempcpy`) jumps through the GOT's slot (`got_memcpy`,
`got_mempcpy`) to one of the three variants in `mc2` at `0x65b8d0`, each of which does what `Tls.CpyAt` or
`Gor.PcpyAt` says (`erms`/`perms`, `sse2At`/`psse2At`, `sse2eAt`/`psse2eAt`). The SSE2 variants read
`__x86_shared_non_temporal_threshold` (`thrA`, `0x7a8428`), which `GotF` puts in the footprint's data (`thr_foot`).

- `cpyAt_plt`: `Tls.CpyAt` at `0x401070`; `pcpyAt_plt`: `Gor.PcpyAt` at `0x4010c0`.
-/

namespace FV7z.Memcpy
open ZellicX86 Decode FV7z.Leaf FV7z.Fn FV7z.Glibc FV7z.Start FV7z.Strlen

/-- The 8 bytes of the non-temporal threshold `mc2` at `0x65b8d0` reads are data of the footprint. -/
theorem thr_foot {F : Footprint} (hgf : GotF F) :
    ∀ i < 8, Foot F.data (Addr.add (BitVec.ofNat 64 (thrA 0x65b8d0#64)) i) := by
  intro i hi
  rw [show thrA 0x65b8d0#64 = 0x7a8428 from rfl]
  apply hgf.thr
  · simp only [Addr.add, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]; omega
  · simp only [Addr.add, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]; omega

/-- The 8 bytes of a GOT slot at `a`, `0x792018 ≤ a`, `a + 8 ≤ 0x792110`, are data of the footprint. -/
theorem got_foot {F : Footprint} (hgf : GotF F) {a : Nat} (h1 : 0x792018 ≤ a) (h2 : a + 8 ≤ 0x792110) :
    ∀ i < 8, Foot F.data (Addr.add (BitVec.ofNat 64 a) i) := by
  intro i hi
  apply hgf.got
  · simp only [Addr.add, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.reducePow]; omega
  · simp only [Addr.add, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.reducePow]; omega

/-- `memcpy` through the PLT, on a processor without SSSE3 and SSE3 together and without AVX and AVX2 together: the
jump through the GOT's slot to one of the three variants, then `erms`, `sse2At` or `sse2eAt`. -/
theorem cpyAt_plt {prof : Profile} {L : List (Addr × List Byte)} {o : Oracle}
    (hs : ¬ (prof.feat.ssse3 = true ∧ prof.feat.sse3 = true)) (hb : ¬ (prof.feat.avx = true ∧ prof.feat.avx2 = true))
    (hinP : CodeIn L 4198512#64 pltLen) (hin : CodeIn L 0x65b8d0#64 mc2) :
    Tls.CpyAt prof L o 4198512#64 (GotOkB prof) := by
  intro F Wl s₀ gev gP gE X t V e' code j c hgf hK hA hrip hG hin₂ hj hra hl hsrc hst hs64 hd64 hap hsp hdf hsp8 K
  have he : eaR X 6 3739634 = 0x792068#64 := by simp only [eaR, hrip]; rfl
  have hfoot : ∀ i < 8, Foot F.data ((eaR X 6 3739634).add i) := by
    rw [he]; exact got_foot (a := 0x792068) hgf (by decide) (by decide)
  have hdf₀ : s₀.cpu.rflags.df = false := hK.df.symm.trans hdf
  have hR : RetC prof F Wl L s₀ o gev gP gE V X.cpu.gpr X.cpu.gpr.rdi := ⟨hl, e', code, j, hin₂, hj, hra, K⟩
  rcases got_memcpy hG hs hb with h | h | h
  · refine c.s_jmp_mripJ hK hA hinP (j := 0) (by decide) (by rw [hrip, addr_add_zero]) (pd0 prof.feat) hfoot hin
      (j₂ := 128) (by rw [mc2_length]; decide) (by rw [he, h]; rfl) ?_
    rintro Y t' hKY hAY ⟨hrY, hgY⟩
    exact erms c hin hKY hAY hrY hgY hsrc hst hs64 hd64 hap hsp (hKY.df.trans hdf₀) hsp8 hR
  · refine c.s_jmp_mripJ hK hA hinP (j := 0) (by decide) (by rw [hrip, addr_add_zero]) (pd0 prof.feat) hfoot hin
      (j₂ := 16) (by rw [mc2_length]; decide) (by rw [he, h]; rfl) ?_
    rintro Y t' hKY hAY ⟨hrY, hgY⟩
    exact sse2At c hin hKY hAY hrY hgY hsrc hst hd64 hs64 hsp hsp8 (thr_foot hgf) hR
  · refine c.s_jmp_mripJ hK hA hinP (j := 0) (by decide) (by rw [hrip, addr_add_zero]) (pd0 prof.feat) hfoot hin
      (j₂ := 208) (by rw [mc2_length]; decide) (by rw [he, h]; rfl) ?_
    rintro Y t' hKY hAY ⟨hrY, hgY⟩
    exact sse2eAt c hin hKY hAY hrY hgY hsrc hst hd64 hs64 hap hsp (hKY.df.trans hdf₀) hsp8 (thr_foot hgf) hR

/-- `mempcpy` through the PLT, on a processor without SSSE3 and SSE3 together and without AVX and AVX2 together:
the jump through the GOT's slot to one of the three variants, then `perms`, `psse2At` or `psse2eAt`. -/
theorem pcpyAt_plt {prof : Profile} {L : List (Addr × List Byte)} {o : Oracle}
    (hs : ¬ (prof.feat.ssse3 = true ∧ prof.feat.sse3 = true)) (hb : ¬ (prof.feat.avx = true ∧ prof.feat.avx2 = true))
    (hinP : CodeIn L 4198592#64 pltLen) (hin : CodeIn L 0x65b8d0#64 mc2) :
    Gor.PcpyAt prof L o 4198592#64 (GotOkB prof) := by
  intro F Wl s₀ gev gP gE X t V e' code j c hgf hK hA hrip hG hin₂ hj hra hl hsrc hst hs64 hd64 hap hsp hdf hsp8 K
  have he : eaR X 6 3739634 = 0x7920b8#64 := by simp only [eaR, hrip]; rfl
  have hfoot : ∀ i < 8, Foot F.data ((eaR X 6 3739634).add i) := by
    rw [he]; exact got_foot (a := 0x7920b8) hgf (by decide) (by decide)
  have hdf₀ : s₀.cpu.rflags.df = false := hK.df.symm.trans hdf
  have hR : RetC prof F Wl L s₀ o gev gP gE V X.cpu.gpr (X.cpu.gpr.rdi + X.cpu.gpr.rdx) :=
    ⟨hl, e', code, j, hin₂, hj, hra, K⟩
  rcases got_mempcpy hG hs hb with h | h | h
  · refine c.s_jmp_mripJ hK hA hinP (j := 0) (by decide) (by rw [hrip, addr_add_zero]) (pd0 prof.feat) hfoot hin
      (j₂ := 80) (by rw [mc2_length]; decide) (by rw [he, h]; rfl) ?_
    rintro Y t' hKY hAY ⟨hrY, hgY⟩
    exact perms c hin hKY hAY hrY hgY hsrc hst hs64 hd64 hap hsp (hKY.df.trans hdf₀) hsp8 hR
  · refine c.s_jmp_mripJ hK hA hinP (j := 0) (by decide) (by rw [hrip, addr_add_zero]) (pd0 prof.feat) hfoot hin
      (j₂ := 0) (by rw [mc2_length]; decide) (by rw [he, h]; rfl) ?_
    rintro Y t' hKY hAY ⟨hrY, hgY⟩
    exact psse2At c hin hKY hAY hrY hgY hsrc hst hd64 hs64 hsp hsp8 (thr_foot hgf) hR
  · refine c.s_jmp_mripJ hK hA hinP (j := 0) (by decide) (by rw [hrip, addr_add_zero]) (pd0 prof.feat) hfoot hin
      (j₂ := 192) (by rw [mc2_length]; decide) (by rw [he, h]; rfl) ?_
    rintro Y t' hKY hAY ⟨hrY, hgY⟩
    exact psse2eAt c hin hKY hAY hrY hgY hsrc hst hd64 hs64 hap hsp (hKY.df.trans hdf₀) hsp8 (thr_foot hgf) hR

end FV7z.Memcpy
