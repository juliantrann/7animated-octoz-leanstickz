import FV7z.Strrchr.Run
import FV7z.Strlen.Plt
/-!
# `strrchr` through the PLT (PLAN.md M, the PLT contracts)

`7zzs` calls `strrchr` at `0x401050`: `jmp qword [rip + 0x390ff2]` (the same 8 bytes as `strlen`'s entry,
`Strlen.pltLen`), through the GOT's slot `0x792048`, which `apply_irel` filled with what the resolver at `0x636170`
returned (`GotOkB`): `__strrchr_sse2` (`0x654200`) unless the processor has AVX and AVX2. Without both, a call at
`0x401050` does what `Str.RchrAt` says (`rchrAt_plt`; the contract asks the GOT's slots to be data, `GotF`).
-/
namespace FV7z.Strrchr
open ZellicX86 Decode FV7z.Leaf FV7z.Fn FV7z.Glibc FV7z.Start FV7z.Strlen

theorem plt_pin : Exe.bytesAt V2606.zzs.blob 0x401050 8 = some pltLen := by decide +kernel

/-- Without both AVX and AVX2, the GOT's slot of `strrchr` holds `__strrchr_sse2`. -/
theorem got_strrchr {prof : Profile} {W : Addr → Byte} (hG : GotOkB prof W)
    (hb : ¬ (prof.feat.avx = true ∧ prof.feat.avx2 = true)) :
    ofBytesLE 64 ((byteAddrs 0x792048#64 8).map W) = 0x654200#64 := by
  have hR : Returns prof [(0x654200, []), (0x654500, [Features.avx, Features.avx2])]
      (ofBytesLE 64 ((byteAddrs 0x792048#64 8).map W)) :=
    hG (0x792048, 0x636170) (by
      unfold V2606.irel
      exact
        List.Mem.tail _ <| List.Mem.tail _ <| List.Mem.tail _ <| List.Mem.tail _ <| List.Mem.tail _ <|
        List.Mem.tail _ <| List.Mem.tail _ <| List.Mem.tail _ <| List.Mem.tail _ <| List.Mem.tail _ <|
        List.Mem.tail _ <| List.Mem.tail _ <| List.Mem.tail _ <| List.Mem.tail _ <| List.Mem.tail _ <|
        List.Mem.tail _ <| List.Mem.tail _ <| List.Mem.tail _ <| List.Mem.tail _ <| List.Mem.tail _ <|
        List.Mem.tail _ <| List.Mem.tail _ <| List.Mem.tail _ <| List.Mem.tail _ <| List.Mem.head _)
      (0x636170, 53, [(0x654200, []), (0x654500, [Features.avx, Features.avx2])]) (by
      unfold V2606.resolvers
      exact
        List.Mem.tail _ <| List.Mem.tail _ <| List.Mem.tail _ <| List.Mem.tail _ <| List.Mem.tail _ <|
        List.Mem.tail _ <| List.Mem.tail _ <| List.Mem.tail _ <| List.Mem.head _) rfl
  obtain ⟨v, hv, hw, hf⟩ := hR
  rcases List.mem_cons.1 hv with rfl | hv
  · exact hw
  · rcases List.mem_cons.1 hv with rfl | hv
    · exact (hb ⟨hf _ (List.Mem.head _), hf _ (List.Mem.tail _ (List.Mem.head _))⟩).elim
    · nomatch hv

/-- `strrchr` through the PLT, on a processor without both AVX and AVX2: the jump through the GOT's slot to
`__strrchr_sse2`, then `rchrAt_sse2`. -/
theorem rchrAt_plt {prof : Profile} {L : List (Addr × List Byte)} {o : Oracle}
    (hb : ¬ (prof.feat.avx = true ∧ prof.feat.avx2 = true))
    (hinP : CodeIn L 4198480#64 pltLen) (hin : CodeIn L 0x654200#64 sr2) :
    Str.RchrAt prof L o 4198480#64 (GotOkB prof) := by
  intro F Wl s₀ gev gP gE X t V e' code j n c hgf hK hA hrip hG hin₂ hj hra hl hov hnz hz hch hft K
  have he : eaR X 6 3739634 = 0x792048#64 := by simp only [eaR, hrip]; rfl
  refine c.s_jmp_mrip hK hA hinP (j := 0) (by decide) (by rw [hrip, addr_add_zero]) (pd0 prof.feat)
    (fun i hi => ?_) hin (by rw [sr2_length]; decide) (by rw [he]; exact got_strrchr hG hb) ?_
  · rw [he]
    apply hgf.got
    · simp only [Addr.add, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]; omega
    · simp only [Addr.add, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]; omega
  · rintro Y t' hKY hAY ⟨hrY, hgY⟩
    rw [← hgY] at hra hl hov hnz hz hch hft K
    exact rchrAt_sse2 (Pm := fun _ => True) hin n c hgf hKY hAY hrY trivial hin₂ hj hra hl hov hnz hz hch hft K

end FV7z.Strrchr
