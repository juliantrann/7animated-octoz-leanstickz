import FV7z.Strrchr.Run
import FV7z.Strlen.Plt
/-!
# `strrchr` through the PLT (PLAN.md M, the PLT contracts)

`7zzs` calls `strrchr` at `0x401050`: `jmp qword [rip + 0x390ff2]` (the same 8 bytes as `strlen`'s entry,
`Strlen.pltLen`), through the GOT's slot `0x792048`, which `apply_irel` filled with what the resolver at `0x636170`
returned (`GotOkB`): `__strrchr_sse2` (`0x654200`) unless the processor has AVX and AVX2. Without both, a call at
`0x401050` does what `Str.RchrAt` says, with the GOT's slots bytes of the footprint's data (`rchrAtG_plt`).
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

/-- `Str.RchrAt` with the GOT's slots bytes of the footprint's data (`GotFoot`). -/
def RchrAtG (prof : Profile) (L : List (Addr × List Byte)) (o : Oracle) (e : Addr) (Pm : (Addr → Byte) → Prop) :
    Prop :=
  ∀ {F : Footprint} {Wl : List Rgn} {s₀ : State} {gev : List Event} {gP : State → Nat → List Event → Prop}
    {gE : Outcome → List Event → Prop} {X : State} {t : Nat} {V : Addr → Byte} {e' : Addr} {code : List Byte}
    {j : Nat} (n : Nat), Seg prof F Wl L s₀ o → GotFoot F → KeptW Wl s₀ X → Agree F X.proc.mm.mem V →
    X.cpu.rip = e → Pm V →
    CodeIn L e' code → j < code.length → rdq(V, X.cpu.gpr.rsp) = e'.add j →
    (∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsp i)) → X.cpu.gpr.rdi.toNat + n < 2 ^ 64 →
    (∀ k < n, V (Addr.add X.cpu.gpr.rdi k) ≠ 0) → V (Addr.add X.cpu.gpr.rdi n) = 0 →
    X.cpu.gpr.rsi.setWidth 8 ≠ 0#8 →
    (∀ x : Addr, X.cpu.gpr.rdi.toNat / 4096 ≤ x.toNat / 4096 →
      x.toNat / 4096 ≤ (X.cpu.gpr.rdi.toNat + n) / 4096 → Foot F.data x) →
    (∀ Z t', KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V → Z.cpu.rip = e'.add j →
      Z.cpu.gpr.rsp = X.cpu.gpr.rsp + 8 →
      ((∀ k < n, V (Addr.add X.cpu.gpr.rdi k) ≠ X.cpu.gpr.rsi.setWidth 8) → Z.cpu.gpr.rax = 0) →
      (∀ m < n, V (Addr.add X.cpu.gpr.rdi m) = X.cpu.gpr.rsi.setWidth 8 →
        (∀ k, m < k → k < n → V (Addr.add X.cpu.gpr.rdi k) ≠ X.cpu.gpr.rsi.setWidth 8) →
        Z.cpu.gpr.rax = Addr.add X.cpu.gpr.rdi m) →
      Z.cpu.gpr.rbx = X.cpu.gpr.rbx → Z.cpu.gpr.rbp = X.cpu.gpr.rbp → Z.cpu.gpr.r12 = X.cpu.gpr.r12 →
      Z.cpu.gpr.r13 = X.cpu.gpr.r13 → Z.cpu.gpr.r14 = X.cpu.gpr.r14 → Z.cpu.gpr.r15 = X.cpu.gpr.r15 →
      GoG prof L o gev gP gE Z t') →
    GoG prof L o gev gP gE X t

/-- `strrchr` through the PLT, on a processor without both AVX and AVX2: the jump through the GOT's slot to
`__strrchr_sse2`, then `rchrAt_sse2`. -/
theorem rchrAtG_plt {prof : Profile} {L : List (Addr × List Byte)} {o : Oracle}
    (hb : ¬ (prof.feat.avx = true ∧ prof.feat.avx2 = true))
    (hinP : CodeIn L 4198480#64 pltLen) (hin : CodeIn L 0x654200#64 sr2) :
    RchrAtG prof L o 4198480#64 (GotOkB prof) := by
  intro F Wl s₀ gev gP gE X t V e' code j n c hgf hK hA hrip hG hin₂ hj hra hl hov hnz hz hch hft K
  have he : eaR X 6 3739634 = 0x792048#64 := by simp only [eaR, hrip]; rfl
  refine c.s_jmp_mrip hK hA hinP (j := 0) (by decide) (by rw [hrip, addr_add_zero]) (pd0 prof.feat)
    (fun i hi => ?_) hin (by rw [sr2_length]; decide) (by rw [he]; exact got_strrchr hG hb) ?_
  · rw [he]
    apply hgf
    · simp only [Addr.add, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]; omega
    · simp only [Addr.add, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]; omega
  · rintro Y t' hKY hAY ⟨hrY, hgY⟩
    rw [← hgY] at hra hl hov hnz hz hch hft K
    exact rchrAt_sse2 (Pm := fun _ => True) hin n c hKY hAY hrY trivial hin₂ hj hra hl hov hnz hz hch hft K

end FV7z.Strrchr
