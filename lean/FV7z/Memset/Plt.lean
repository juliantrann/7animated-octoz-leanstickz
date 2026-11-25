import FV7z.Memset.Sse2
import FV7z.Strlen.Plt
/-!
# `memset` through the PLT (PLAN.md M, the PLT contracts)

`7zzs` calls `memset` at `0x401080`: `jmp qword [rip + 0x390ff2]` (the same 8 bytes as `strlen`'s entry,
`Strlen.pltLen`), through the GOT's slot `0x792078`, which `apply_irel` filled with what the resolver at `0x636b20`
returned (`GotOkB`). Without both AVX and AVX2 that is one of the three variants in `ms2` (`got_memset`):
`__memset_erms` (`+80`), `__memset_sse2_unaligned_erms` (`+112`) or `__memset_sse2_unaligned` (`+0`); each does what
`SetAtD` says (`Memset/Erms.lean`, `Memset/Sse2.lean`). So does a call at `0x401080`, with the GOT's slots bytes of
the footprint's data (`setAtDG_plt`), which is `Ipa.SetAt` (`setAt_plt`).
-/

namespace FV7z.Fn.Seg
open ZellicX86 Decode FV7z.Leaf

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle} {F : Footprint} {Wl : List Rgn}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop} {X : State} {t j : Nat}
  {e' : Addr} {code : List Byte} {V : Addr → Byte}

/-- `jmp qword [rip + d]`, through bytes of the footprint's data, to the `j₂`-th byte of a segment. -/
theorem s_jmp_mripJ (c : Seg prof F Wl L s₀ o) (hK : KeptW Wl s₀ X)
    (hA : Agree F X.proc.mm.mem V) (hin : CodeIn L e' code) (hj : j < code.length)
    (hrip : X.cpu.rip = e'.add j) {d len : Nat}
    (hd : Dec prof.feat code j (FV7z.mk .jmp 64 [.mem (mrip d 64)] len))
    (hl : ∀ i < 8, Foot F.data ((eaR X len d).add i))
    {e₂ : Addr} {code₂ : List Byte} {j₂ : Nat} (hin₂ : CodeIn L e₂ code₂) (h₂ : j₂ < code₂.length)
    (htgt : ofBytesLE 64 ((byteAddrs (eaR X len d) 8).map V) = e₂.add j₂)
    (k' : ContG prof F Wl L s₀ o gev gP gE V fun Y => Y.cpu.rip = e₂.add j₂ ∧ Y.cpu.gpr = X.cpu.gpr) :
    GoG prof L o gev gP gE X t :=
  c.next hK hA hin hj hrip (fun M hK' hA' htf hac => by
    have hca := ((c.codeAt hK' hin₂) j₂ h₂).1
    obtain ⟨hrd, hv⟩ := c.load_ok (X := X.withMem M) hK' hA' hl
    have hT : ofBytesLE 64 (readBytes (X.withMem M).proc.mm.mem (eaR (X.withMem M) len d) 8) = e₂.add j₂ :=
      (congrArg (ofBytesLE 64) hv).trans htgt
    have hr := jmp_mrip (s := X.withMem M) (o := o) (t := t + 1) htf hac (c.dec hK' hin hrip hd) hrd
      (by rw [hT]; exact hca)
    rw [hT] at hr
    exact ⟨_, _, hr, hK'.upd rfl rfl rfl, hA', rfl, rfl⟩) k'

end FV7z.Fn.Seg

namespace FV7z.Memset
open ZellicX86 Decode FV7z.Leaf FV7z.Fn FV7z.Glibc FV7z.Start FV7z.Strlen

theorem plt_pin : Exe.bytesAt V2606.zzs.blob 0x401080 8 = some pltLen := by decide +kernel

/-- Without both AVX and AVX2, the GOT's slot of `memset` holds one of the three variants in `ms2`. -/
theorem got_memset {prof : Profile} {W : Addr → Byte} (hG : GotOkB prof W)
    (hb : ¬ (prof.feat.avx = true ∧ prof.feat.avx2 = true)) :
    ofBytesLE 64 ((byteAddrs 0x792078#64 8).map W) = 0x65c6a0#64 ∨
      ofBytesLE 64 ((byteAddrs 0x792078#64 8).map W) = 0x65c6c0#64 ∨
      ofBytesLE 64 ((byteAddrs 0x792078#64 8).map W) = 0x65c650#64 := by
  have hR : Returns prof [(0x65c6a0, []), (0x65c6c0, []), (0x65c650, []), (0x65c7d0, [Features.avx, Features.avx2]),
      (0x65c820, [Features.avx, Features.avx2]), (0x65b650, [Features.avx, Features.avx2, Features.avx512f]),
      (0x65c950, [Features.avx, Features.avx2, Features.avx512f]),
      (0x65c9b0, [Features.avx, Features.avx2, Features.avx512f])] (ofBytesLE 64 ((byteAddrs 0x792078#64 8).map W)) :=
    hG (0x792078, 0x636b20) (by
      unfold V2606.irel
      exact
        List.Mem.tail _ <| List.Mem.tail _ <| List.Mem.tail _ <| List.Mem.tail _ <| List.Mem.tail _ <|
        List.Mem.tail _ <| List.Mem.tail _ <| List.Mem.tail _ <| List.Mem.tail _ <| List.Mem.tail _ <|
        List.Mem.tail _ <| List.Mem.tail _ <| List.Mem.tail _ <| List.Mem.tail _ <| List.Mem.tail _ <|
        List.Mem.tail _ <| List.Mem.tail _ <| List.Mem.tail _ <| List.Mem.head _)
      (0x636b20, 158, [(0x65c6a0, []), (0x65c6c0, []), (0x65c650, []), (0x65c7d0, [Features.avx, Features.avx2]),
      (0x65c820, [Features.avx, Features.avx2]), (0x65b650, [Features.avx, Features.avx2, Features.avx512f]),
      (0x65c950, [Features.avx, Features.avx2, Features.avx512f]),
      (0x65c9b0, [Features.avx, Features.avx2, Features.avx512f])]) (by
      unfold V2606.resolvers
      exact
        List.Mem.tail _ <| List.Mem.tail _ <| List.Mem.tail _ <| List.Mem.tail _ <| List.Mem.tail _ <|
        List.Mem.tail _ <| List.Mem.tail _ <| List.Mem.tail _ <| List.Mem.tail _ <| List.Mem.tail _ <|
        List.Mem.tail _ <| List.Mem.tail _ <| List.Mem.tail _ <| List.Mem.tail _ <| List.Mem.tail _ <|
        List.Mem.tail _ <| List.Mem.tail _ <| List.Mem.tail _ <| List.Mem.tail _ <| List.Mem.tail _ <|
        List.Mem.tail _ <| List.Mem.tail _ <| List.Mem.tail _ <| List.Mem.tail _ <| List.Mem.tail _ <|
        List.Mem.tail _ <| List.Mem.tail _ <| List.Mem.tail _ <| List.Mem.tail _ <| List.Mem.head _) rfl
  obtain ⟨v, hv, hw, hf⟩ := hR
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact .inl hw
  · exact .inr (.inl hw)
  · exact .inr (.inr hw)
  all_goals exact (hb ⟨hf _ (List.Mem.head _), hf _ (List.Mem.tail _ (List.Mem.head _))⟩).elim

/-- `SetAtD` with the GOT's slots bytes of the footprint's data (`GotFoot`). -/
def SetAtDG (prof : Profile) (L : List (Addr × List Byte)) (o : Oracle) (e : Addr) (Pm : (Addr → Byte) → Prop) :
    Prop :=
  ∀ {F : Footprint} {Wl : List Rgn} {s₀ : State} {gev : List Event} {gP : State → Nat → List Event → Prop}
    {gE : Outcome → List Event → Prop} {X : State} {t : Nat} {V : Addr → Byte} {e' : Addr} {code : List Byte}
    {j : Nat}, Seg prof F Wl L s₀ o → GotFoot F → KeptW Wl s₀ X → Agree F X.proc.mm.mem V → X.cpu.rip = e → Pm V →
    CodeIn L e' code → j < code.length → rdq(V, X.cpu.gpr.rsp) = e'.add j →
    (∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsp i)) →
    (∀ i < X.cpu.gpr.rdx.toNat, Foot Wl (Addr.add X.cpu.gpr.rdi i)) →
    X.cpu.gpr.rdi.toNat + X.cpu.gpr.rdx.toNat < 2 ^ 64 →
    (X.cpu.gpr.rdi.toNat + X.cpu.gpr.rdx.toNat ≤ X.cpu.gpr.rsp.toNat ∨
      X.cpu.gpr.rsp.toNat + 8 ≤ X.cpu.gpr.rdi.toNat) →
    X.cpu.rflags.df = false → X.cpu.gpr.rsp.toNat + 8 ≤ 2 ^ 64 →
    (∀ Z t' V₂, KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V₂ → Z.cpu.rip = e'.add j →
      Z.cpu.gpr.rsp = X.cpu.gpr.rsp + 8 → Z.cpu.gpr.rax = X.cpu.gpr.rdi →
      Z.cpu.gpr.rbx = X.cpu.gpr.rbx → Z.cpu.gpr.rbp = X.cpu.gpr.rbp → Z.cpu.gpr.r12 = X.cpu.gpr.r12 →
      Z.cpu.gpr.r13 = X.cpu.gpr.r13 → Z.cpu.gpr.r14 = X.cpu.gpr.r14 → Z.cpu.gpr.r15 = X.cpu.gpr.r15 →
      (∀ i < X.cpu.gpr.rdx.toNat, V₂ (Addr.add X.cpu.gpr.rdi i) = X.cpu.gpr.rsi.setWidth 8) →
      (∀ a : Addr, ¬ (X.cpu.gpr.rdi.toNat ≤ a.toNat ∧ a.toNat < X.cpu.gpr.rdi.toNat + X.cpu.gpr.rdx.toNat) →
        V₂ a = V a) →
      GoG prof L o gev gP gE Z t') →
    GoG prof L o gev gP gE X t

/-- `memset` through the PLT, on a processor without both AVX and AVX2: the jump through the GOT's slot to one of
the three variants, then `setAtD_erms`, `setAtD_sse2ue` or `setAtD_sse2u`. -/
theorem setAtDG_plt {prof : Profile} {L : List (Addr × List Byte)} {o : Oracle}
    (hb : ¬ (prof.feat.avx = true ∧ prof.feat.avx2 = true))
    (hinP : CodeIn L 4198528#64 pltLen) (hin : CodeIn L 0x65c650#64 ms2) :
    SetAtDG prof L o 4198528#64 (GotOkB prof) := by
  intro F Wl s₀ gev gP gE X t V e' code j c hgf hK hA hrip hG hin₂ hj hra hl hst hov hsp hdf hsp8 K
  have he : eaR X 6 3739634 = 0x792078#64 := by simp only [eaR, hrip]; rfl
  have hfoot : ∀ i < 8, Foot F.data ((eaR X 6 3739634).add i) := by
    intro i hi
    rw [he]
    apply hgf
    · simp only [Addr.add, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]; omega
    · simp only [Addr.add, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]; omega
  have hdf₀ : s₀.cpu.rflags.df = false := hK.df.symm.trans hdf
  rcases got_memset hG hb with h | h | h
  · refine c.s_jmp_mripJ hK hA hinP (j := 0) (by decide) (by rw [hrip, addr_add_zero]) (pd0 prof.feat) hfoot hin
      (j₂ := 80) (by rw [ms2_length]; decide) (by rw [he, h]; rfl) ?_
    rintro Y t' hKY hAY ⟨hrY, hgY⟩
    rw [← hgY] at hra hl hst hov hsp hsp8 K
    exact setAtD_erms (Pm := fun _ => True) hin c hKY hAY hrY trivial hin₂ hj hra hl hst hov hsp
      (hKY.df.trans hdf₀) hsp8 K
  · refine c.s_jmp_mripJ hK hA hinP (j := 0) (by decide) (by rw [hrip, addr_add_zero]) (pd0 prof.feat) hfoot hin
      (j₂ := 112) (by rw [ms2_length]; decide) (by rw [he, h]; rfl) ?_
    rintro Y t' hKY hAY ⟨hrY, hgY⟩
    rw [← hgY] at hra hl hst hov hsp hsp8 K
    exact setAtD_sse2ue (Pm := fun _ => True) hin c hKY hAY hrY trivial hin₂ hj hra hl hst hov hsp
      (hKY.df.trans hdf₀) hsp8 K
  · refine c.s_jmp_mripJ hK hA hinP (j := 0) (by decide) (by rw [hrip, addr_add_zero]) (pd0 prof.feat) hfoot hin
      (j₂ := 0) (by rw [ms2_length]; decide) (by rw [he, h]; rfl) ?_
    rintro Y t' hKY hAY ⟨hrY, hgY⟩
    rw [← hgY] at hra hl hst hov hsp hsp8 K
    exact setAtD_sse2u (Pm := fun _ => True) hin c hKY hAY hrY trivial hin₂ hj hra hl hst hov hsp
      (hKY.df.trans hdf₀) hsp8 K

/-- `Ipa.SetAt`, what `launch_to_main` assumes of `memset` through the PLT, on a processor without both AVX and
AVX2. -/
theorem setAt_plt {prof : Profile} {L : List (Addr × List Byte)} {o : Oracle}
    (hb : ¬ (prof.feat.avx = true ∧ prof.feat.avx2 = true))
    (hinP : CodeIn L 4198528#64 pltLen) (hin : CodeIn L 0x65c650#64 ms2) :
    Ipa.SetAt prof L o 4198528#64 (GotOkB prof) :=
  setAtDG_plt hb hinP hin

end FV7z.Memset
