import FV7z.Memcpy.Erms
import FV7z.Memset.Plt
/-!
# `memcpy` and `mempcpy` through the PLT (PLAN.md M, the PLT contracts)

`7zzs` calls `memcpy` at `0x401070` and `mempcpy` at `0x4010c0`, each `jmp qword [rip + 0x390ff2]` (the 8 bytes of
`Strlen.pltLen`), through the GOT's slots `0x792068` and `0x7920b8`, which `apply_irel` filled with what the resolvers
at `0x636d30` and `0x636bc0` returned (`GotOkB`). Without SSSE3 and SSE3 together and without AVX and AVX2 together,
that is one of the three variants in `mc2` (`got_memcpy`, `got_mempcpy`): for `memcpy` `__memmove_erms` (`+128`,
`Memcpy.cpyAt_erms`), `__memmove_sse2_unaligned` (`+16`) or `__memmove_sse2_unaligned_erms` (`+208`); for `mempcpy`
`__mempcpy_erms` (`+80`, `Memcpy.pcpyAt_erms`), `__mempcpy_sse2_unaligned` (`+0`) or `__mempcpy_sse2_unaligned_erms`
(`+192`).
-/

namespace FV7z.Memcpy
open ZellicX86 Decode FV7z.Leaf FV7z.Fn FV7z.Glibc FV7z.Start FV7z.Strlen

theorem plt_pin_cpy : Exe.bytesAt V2606.zzs.blob 0x401070 8 = some pltLen := by decide +kernel

theorem plt_pin_pcpy : Exe.bytesAt V2606.zzs.blob 0x4010c0 8 = some pltLen := by decide +kernel

/-- Without SSSE3 and SSE3 together, and without AVX and AVX2 together, the GOT's slot of `memcpy` holds one of the
three variants in `mc2`. -/
theorem got_memcpy {prof : Profile} {W : Addr → Byte} (hG : GotOkB prof W)
    (hs : ¬ (prof.feat.ssse3 = true ∧ prof.feat.sse3 = true)) (hb : ¬ (prof.feat.avx = true ∧ prof.feat.avx2 = true)) :
    ofBytesLE 64 ((byteAddrs 0x792068#64 8).map W) = 0x65b950#64 ∨
      ofBytesLE 64 ((byteAddrs 0x792068#64 8).map W) = 0x65b8e0#64 ∨
      ofBytesLE 64 ((byteAddrs 0x792068#64 8).map W) = 0x65b9a0#64 := by
  have hR : Returns prof [(0x65b950, []), (0x65b8e0, []), (0x65b9a0, []), (0x6410b0, [Features.ssse3, Features.sse3]),
      (0x646640, [Features.ssse3, Features.sse3]), (0x65bcb0, [Features.avx, Features.avx2]),
      (0x65bd00, [Features.avx, Features.avx2]), (0x64bc80, [Features.avx, Features.avx2, Features.avx512f]),
      (0x65c0f0, [Features.avx, Features.avx2, Features.avx512f]),
      (0x65c140, [Features.avx, Features.avx2, Features.avx512f])]
      (ofBytesLE 64 ((byteAddrs 0x792068#64 8).map W)) :=
    hG (0x792068, 0x636d30) (by
      unfold V2606.irel
      exact
        List.Mem.tail _ <| List.Mem.tail _ <| List.Mem.tail _ <| List.Mem.tail _ <| List.Mem.tail _ <|
        List.Mem.tail _ <| List.Mem.tail _ <| List.Mem.tail _ <| List.Mem.tail _ <| List.Mem.tail _ <|
        List.Mem.tail _ <| List.Mem.tail _ <| List.Mem.tail _ <| List.Mem.tail _ <| List.Mem.tail _ <|
        List.Mem.tail _ <| List.Mem.tail _ <| List.Mem.tail _ <| List.Mem.tail _ <| List.Mem.tail _ <|
        List.Mem.head _)
      (0x636d30, 186, [(0x65b950, []), (0x65b8e0, []), (0x65b9a0, []), (0x6410b0, [Features.ssse3, Features.sse3]),
      (0x646640, [Features.ssse3, Features.sse3]), (0x65bcb0, [Features.avx, Features.avx2]),
      (0x65bd00, [Features.avx, Features.avx2]), (0x64bc80, [Features.avx, Features.avx2, Features.avx512f]),
      (0x65c0f0, [Features.avx, Features.avx2, Features.avx512f]),
      (0x65c140, [Features.avx, Features.avx2, Features.avx512f])]) (by
      unfold V2606.resolvers
      exact
        List.Mem.tail _ <| List.Mem.tail _ <| List.Mem.tail _ <| List.Mem.tail _ <| List.Mem.tail _ <|
        List.Mem.tail _ <| List.Mem.tail _ <| List.Mem.tail _ <| List.Mem.tail _ <| List.Mem.tail _ <|
        List.Mem.tail _ <| List.Mem.tail _ <| List.Mem.tail _ <| List.Mem.tail _ <| List.Mem.tail _ <|
        List.Mem.tail _ <| List.Mem.tail _ <| List.Mem.tail _ <| List.Mem.tail _ <| List.Mem.tail _ <|
        List.Mem.tail _ <| List.Mem.tail _ <| List.Mem.tail _ <| List.Mem.tail _ <| List.Mem.tail _ <|
        List.Mem.tail _ <| List.Mem.tail _ <| List.Mem.head _) rfl
  obtain ⟨v, hv, hw, hf⟩ := hR
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact .inl hw
  · exact .inr (.inl hw)
  · exact .inr (.inr hw)
  · exact (hs ⟨hf _ (List.Mem.head _), hf _ (List.Mem.tail _ (List.Mem.head _))⟩).elim
  · exact (hs ⟨hf _ (List.Mem.head _), hf _ (List.Mem.tail _ (List.Mem.head _))⟩).elim
  all_goals exact (hb ⟨hf _ (List.Mem.head _), hf _ (List.Mem.tail _ (List.Mem.head _))⟩).elim

/-- Without SSSE3 and SSE3 together, and without AVX and AVX2 together, the GOT's slot of `mempcpy` holds one of the
three variants in `mc2`. -/
theorem got_mempcpy {prof : Profile} {W : Addr → Byte} (hG : GotOkB prof W)
    (hs : ¬ (prof.feat.ssse3 = true ∧ prof.feat.sse3 = true)) (hb : ¬ (prof.feat.avx = true ∧ prof.feat.avx2 = true)) :
    ofBytesLE 64 ((byteAddrs 0x7920b8#64 8).map W) = 0x65b920#64 ∨
      ofBytesLE 64 ((byteAddrs 0x7920b8#64 8).map W) = 0x65b8d0#64 ∨
      ofBytesLE 64 ((byteAddrs 0x7920b8#64 8).map W) = 0x65b990#64 := by
  have hR : Returns prof [(0x65b920, []), (0x65b8d0, []), (0x65b990, []), (0x641090, [Features.ssse3, Features.sse3]),
      (0x646620, [Features.ssse3, Features.sse3]), (0x65bca0, [Features.avx, Features.avx2]),
      (0x65bcf0, [Features.avx, Features.avx2]), (0x64bc60, [Features.avx, Features.avx2, Features.avx512f]),
      (0x65c0e0, [Features.avx, Features.avx2, Features.avx512f]),
      (0x65c130, [Features.avx, Features.avx2, Features.avx512f])]
      (ofBytesLE 64 ((byteAddrs 0x7920b8#64 8).map W)) :=
    hG (0x7920b8, 0x636bc0) (by
      unfold V2606.irel
      exact
        List.Mem.tail _ <| List.Mem.tail _ <| List.Mem.tail _ <| List.Mem.tail _ <| List.Mem.tail _ <|
        List.Mem.tail _ <| List.Mem.tail _ <| List.Mem.tail _ <| List.Mem.tail _ <| List.Mem.tail _ <|
        List.Mem.head _)
      (0x636bc0, 186, [(0x65b920, []), (0x65b8d0, []), (0x65b990, []), (0x641090, [Features.ssse3, Features.sse3]),
      (0x646620, [Features.ssse3, Features.sse3]), (0x65bca0, [Features.avx, Features.avx2]),
      (0x65bcf0, [Features.avx, Features.avx2]), (0x64bc60, [Features.avx, Features.avx2, Features.avx512f]),
      (0x65c0e0, [Features.avx, Features.avx2, Features.avx512f]),
      (0x65c130, [Features.avx, Features.avx2, Features.avx512f])]) (by
      unfold V2606.resolvers
      exact
        List.Mem.tail _ <| List.Mem.tail _ <| List.Mem.tail _ <| List.Mem.tail _ <| List.Mem.tail _ <|
        List.Mem.tail _ <| List.Mem.tail _ <| List.Mem.tail _ <| List.Mem.tail _ <| List.Mem.tail _ <|
        List.Mem.tail _ <| List.Mem.tail _ <| List.Mem.tail _ <| List.Mem.tail _ <| List.Mem.tail _ <|
        List.Mem.tail _ <| List.Mem.tail _ <| List.Mem.tail _ <| List.Mem.tail _ <| List.Mem.tail _ <|
        List.Mem.tail _ <| List.Mem.tail _ <| List.Mem.tail _ <| List.Mem.tail _ <| List.Mem.tail _ <|
        List.Mem.tail _ <| List.Mem.head _) rfl
  obtain ⟨v, hv, hw, hf⟩ := hR
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact .inl hw
  · exact .inr (.inl hw)
  · exact .inr (.inr hw)
  · exact (hs ⟨hf _ (List.Mem.head _), hf _ (List.Mem.tail _ (List.Mem.head _))⟩).elim
  · exact (hs ⟨hf _ (List.Mem.head _), hf _ (List.Mem.tail _ (List.Mem.head _))⟩).elim
  all_goals exact (hb ⟨hf _ (List.Mem.head _), hf _ (List.Mem.tail _ (List.Mem.head _))⟩).elim

end FV7z.Memcpy
