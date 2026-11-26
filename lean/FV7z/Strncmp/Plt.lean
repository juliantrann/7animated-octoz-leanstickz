import FV7z.Strncmp.Sse2
import FV7z.Strlen.Plt
/-!
# `strncmp` through the PLT (PLAN.md G3, `strncmp`)

`7zzs` calls `strncmp` at `0x401048`: `jmp qword [rip + 0x390ff2]` (the bytes of `strlen`'s entry, `pltLen`),
through the GOT's slot `0x792040`, which `apply_irel` filled with what the resolver at `0x636110` returned
(`GotOkB`): `__strncmp_sse2` (`0x63a420`) unless the processor has SSSE3, or AVX and AVX2 (`got_strncmp`; SSSE3
alone is ruled out with SSE3 by `Chain`). Then a call at `0x401048` does what `Str.NcmpAt` says with the GOT's
bytes and the jump table's (`ncmpAt_plt`).
-/
namespace FV7z.Strncmp
open ZellicX86 Decode FV7z.Leaf FV7z.Fn FV7z.Glibc FV7z.Start FV7z.Strlen

theorem plt_pin_ncmp : Exe.bytesAt V2606.zzs.blob 0x401048 8 = some pltLen := by decide +kernel

/-- Without SSSE3 and SSE3 together, and without AVX and AVX2 together, the GOT's slot of `strncmp` holds
`__strncmp_sse2`. -/
theorem got_strncmp {prof : Profile} {W : Addr → Byte} (hG : GotOkB prof W)
    (hs : ¬ (prof.feat.ssse3 = true ∧ prof.feat.sse3 = true)) (hch : Chain prof)
    (hb : ¬ (prof.feat.avx = true ∧ prof.feat.avx2 = true)) :
    ofBytesLE 64 ((byteAddrs 0x792040#64 8).map W) = (0x63a420 : Addr) := by
  have hR : Returns prof [(0x63a420, []), (0x63bc80, [Features.ssse3]), (0x63d3f0, [Features.sse42, Features.ssse3]),
      (0x63e3d0, [Features.avx, Features.avx2])] (ofBytesLE 64 ((byteAddrs 0x792040#64 8).map W)) :=
    hG (0x792040, 0x636110) (by
      unfold V2606.irel
      exact
        List.Mem.tail _ <| List.Mem.tail _ <| List.Mem.tail _ <| List.Mem.tail _ <| List.Mem.tail _ <|
        List.Mem.tail _ <| List.Mem.tail _ <| List.Mem.tail _ <| List.Mem.tail _ <| List.Mem.tail _ <|
        List.Mem.tail _ <| List.Mem.tail _ <| List.Mem.tail _ <| List.Mem.tail _ <| List.Mem.tail _ <|
        List.Mem.tail _ <| List.Mem.tail _ <| List.Mem.tail _ <| List.Mem.tail _ <| List.Mem.tail _ <|
        List.Mem.tail _ <| List.Mem.tail _ <| List.Mem.tail _ <| List.Mem.tail _ <| List.Mem.tail _ <|
        List.Mem.head _)
      (0x636110, 95, [(0x63a420, []), (0x63bc80, [Features.ssse3]), (0x63d3f0, [Features.sse42, Features.ssse3]),
      (0x63e3d0, [Features.avx, Features.avx2])]) (by
      unfold V2606.resolvers
      exact
        List.Mem.tail _ <| List.Mem.tail _ <| List.Mem.tail _ <| List.Mem.tail _ <| List.Mem.tail _ <|
        List.Mem.tail _ <| List.Mem.tail _ <| List.Mem.tail _ <| List.Mem.tail _ <| List.Mem.tail _ <|
        List.Mem.tail _ <| List.Mem.tail _ <| List.Mem.tail _ <| List.Mem.tail _ <| List.Mem.tail _ <|
        List.Mem.tail _ <| List.Mem.tail _ <| List.Mem.tail _ <| List.Mem.tail _ <| List.Mem.tail _ <|
        List.Mem.tail _ <| List.Mem.tail _ <| List.Mem.tail _ <| List.Mem.tail _ <| List.Mem.head _) rfl
  have hs3 : ¬ prof.feat.ssse3 = true := fun h => hs ⟨h, hch.sse3 h⟩
  obtain ⟨v, hv, hw, hf⟩ := hR
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl | rfl | rfl
  · exact hw
  · exact (hs3 (hf _ (List.Mem.head _))).elim
  · exact (hs3 (hf _ (List.Mem.tail _ (List.Mem.head _)))).elim
  · exact (hb ⟨hf _ (List.Mem.head _), hf _ (List.Mem.tail _ (List.Mem.head _))⟩).elim

/-- `strncmp` through the PLT, on a processor without SSSE3 and SSE3 together and without AVX and AVX2 together:
the jump through the GOT's slot to `__strncmp_sse2`, then `ncmpAt_sse2`. -/
theorem ncmpAt_plt {prof : Profile} {L : List (Addr × List Byte)} {o : Oracle}
    (hs : ¬ (prof.feat.ssse3 = true ∧ prof.feat.sse3 = true)) (hch : Chain prof)
    (hb : ¬ (prof.feat.avx = true ∧ prof.feat.avx2 = true))
    (hinP : CodeIn L 4198472#64 pltLen) (hin : CodeIn L (0x63a420 : Addr) scm) :
    Str.NcmpAt prof L o 4198472#64 (fun W => GotOkB prof W ∧ NcmpTabV W) := by
  intro F Wl s₀ gev gP gE X t V e' code j m c hG hK hA hrip hPV hin₂ hj hra hl hm hova hovb hs' hpa hpb K
  have he : eaR X 6 3739634 = 0x792040#64 := by simp only [eaR, hrip]; rfl
  refine c.s_jmp_mrip hK hA hinP (j := 0) (by decide) (by rw [hrip, addr_add_zero]) (pd0 prof.feat)
    (fun i hi => ?_) hin (lt_scm (by decide)) (by rw [he]; exact got_strncmp hPV.1 hs hch hb) ?_
  · rw [he]
    apply hG.got
    · simp only [Addr.add, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]; omega
    · simp only [Addr.add, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]; omega
  · rintro Y t' hKY hAY ⟨hrY, hgY⟩
    rw [← hgY] at hra hl hm hova hovb hs' hpa hpb K
    exact ncmpAt_sse2 (Pm := NcmpTabV) hin (fun _ h => h) m c hG hKY hAY hrY hPV.2 hin₂ hj hra hl hm hova hovb hs'
      hpa hpb K

end FV7z.Strncmp
