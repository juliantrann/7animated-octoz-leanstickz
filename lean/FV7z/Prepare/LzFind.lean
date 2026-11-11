import FV7z.Prepare.Sub
/-!
# `LzFindPrepare` installs only a variant the processor runs (PLAN.md G2, "Dispatch theo CPUID", 7-Zip)

`LzFindPrepare` (`C/LzFind.c`, at `0x427de0` in `7zzs` 26.06) sets the function pointer `g_LzFind_SaturSub`
(`0x7967a0`): to `LzFind_SaturSub_128` (`0x4251b0`, SSE4.1) if `CPU_IsSupported_SSE41()`, and then to
`LzFind_SaturSub_256` (`0x425150`, AVX2) if also `CPU_IsSupported_AVX2()`; otherwise to `NULL` (the portable loop).
On a consistent profile (`Profile.Consistent`: what `CPUID` and `XGETBV` report, the processor has), every call
returns, with the pointer one of the three, and a variant only on a processor with the features it uses. Its code
and its callees' (`z7_x86_cpuid`, `z7_x86_cpuid_GetMaxFunc`, `CPU_IsSupported_SSE41`, `CPU_IsSupported_AVX`,
`CPU_IsSupported_AVX2`) run step by step (`Sub.lean`), the stack canaries checked.
-/
namespace FV7z.Prepare
open ZellicX86 Decode FV7z.Leaf FV7z.Fn

/-- The pointer `LzFindPrepare` sets: `g_LzFind_SaturSub`. -/
def lzW (_ : State) : List Rgn := [⟨0x7967a0, 8⟩]

/-- What it reads besides its stack: the stack canary, at `fs:[40]`. -/
def lzR (s : State) : List Rgn := [⟨Addr.add s.cpu.seg.fsBase 40, 8⟩]

/-- The canary apart from the stack it uses, and the pointer apart from the return address's slot. -/
def lzPre (s : State) : Prop :=
  ((Addr.add s.cpu.seg.fsBase 40).toNat + 8 ≤ s.cpu.gpr.rsp.toNat - 120 ∨
    s.cpu.gpr.rsp.toNat ≤ (Addr.add s.cpu.seg.fsBase 40).toNat) ∧
  (0x7967a0 + 8 ≤ s.cpu.gpr.rsp.toNat ∨ s.cpu.gpr.rsp.toNat + 8 ≤ 0x7967a0)

/-- `g_LzFind_SaturSub` in `Y`. -/
def satVal (Y : State) : BitVec 64 := ofBytesLE 64 (readBytes Y.proc.mm.mem 0x7967a0 8)

/-- At the return: `NULL`, or `LzFind_SaturSub_128` on a processor with SSE4.1, or `LzFind_SaturSub_256` on one with
SSE4.1, AVX2 and AVX. -/
def lzPost (prof : Profile) (_ Y : State) : Prop :=
  satVal Y = 0 ∨ (satVal Y = 0x4251b0 ∧ prof.feat.sse41 = true) ∨
    (satVal Y = 0x425150 ∧ prof.feat.sse41 = true ∧ prof.feat.avx2 = true ∧ prof.feat.avx = true)

/-- The contract: a stack of 120 bytes (its own 8, `CPU_IsSupported_AVX2`'s 104 with what it calls, a return
address), the pointer written, the canary read. -/
abbrev lzC (prof : Profile) : Contract := fn 120 lzW lzR lzPre (lzPost prof)

theorem lzPost_of {prof : Profile} {s₀ Y : State} {v : BitVec 64}
    (hv : ofBytesLE 64 (readBytes Y.proc.mm.mem 0x7967a0 8) = v)
    (h : v = 0 ∨ (v = 0x4251b0 ∧ prof.feat.sse41 = true) ∨
      (v = 0x425150 ∧ prof.feat.sse41 = true ∧ prof.feat.avx2 = true ∧ prof.feat.avx = true)) :
    lzPost prof s₀ Y := by
  unfold lzPost satVal; rw [hv]; exact h

theorem callee_of {s₀ X : State} (h : Saved s₀ X) (hsp : X.cpu.gpr.rsp = s₀.cpu.gpr.rsp) : Callee s₀ X :=
  ⟨h.1, hsp, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {ra : Addr} {o : Oracle}

theorem run (hpc : prof.Consistent) (c : Call prof 120 lzW lzR lzPre (lzPost prof) 0x427de0 L s₀ ra o)
    (hin : CodeIn L 0x427de0 lz) (hinS : CodeIn L 0x424390 sse41) (hinA2 : CodeIn L 0x4244b0 avx2)
    (hinA : CodeIn L 0x424440 avx) (hinM : CodeIn L 0x4242b0 maxf) (hinC : CodeIn L 0x424290 cpuid) (t : Nat) :
    Go prof 120 lzW lzR lzPre (lzPost prof) L s₀ ra o s₀ t := by
  have hl : lz.length = 77 := lz_length
  have hK0 : KeptW (ws 120 lzW s₀) s₀ s₀ := KeptW.refl _ _
  have hA0 : Agree (fp 120 lzW lzR lzPre (lzPost prof) L s₀) s₀.proc.mm.mem
      (fun a => s₀.proc.mm.mem.readByte a) := fun _ _ => rfl
  obtain ⟨hpt0, hsf0⟩ := Call.frame_arith c.frame_fits
  obtain ⟨hca0, -⟩ := c.call.pre
  generalize hpd : s₀.cpu.gpr.rsp - BitVec.ofNat 64 120 = p at hpt0
  have hsp : s₀.cpu.gpr.rsp = Addr.add p 120 := by rw [← hpd]; exact sub_add_self _ _
  have hfit : p.toNat + 128 ≤ 2 ^ 64 := by omega
  have hpn : ∀ d, d < 128 → (Addr.add p d).toNat = p.toNat + d := fun d hd => toNat_addn hd hfit
  have hws : ∀ i < 120, Foot (ws 120 lzW s₀) (Addr.add p i) := fun i hi =>
    ⟨below s₀ 120, by simp, by simp only [below, hpd]; exact mem_add_of_fits hi (by omega)⟩
  -- the canary
  have hcr : (⟨Addr.add s₀.cpu.seg.fsBase 40, 8⟩ : Rgn) ∈ (fp 120 lzW lzR lzPre (lzPost prof) L s₀).data := by
    simp [Footprint.data, Contract.footprint, fn, lzR]
  have hcf : (Addr.add s₀.cpu.seg.fsBase 40).toNat + 8 ≤ 2 ^ 64 :=
    c.call.foot.fits _ (List.mem_append_left _ hcr)
  have hcn : ∀ i < 8, Foot (fp 120 lzW lzR lzPre (lzPost prof) L s₀).data
      (Addr.add (Addr.add s₀.cpu.seg.fsBase 40) i) := fun i hi => ⟨_, hcr, mem_add_of_fits hi hcf⟩
  -- the pointer
  have hgf : ∀ i < 8, Foot (ws 120 lzW s₀) (Addr.add 0x7967a0 i) := fun i hi =>
    ⟨⟨0x7967a0, 8⟩, by simp [lzW], mem_add_of_fits hi (by decide)⟩
  -- `endbr64`, `sub rsp, 8`
  refine c.s_endbr hK0 hA0 hin (by omega) (by rw [addr_add_zero]; exact c.call.shape.1) (lz_0 _) ?_
  rintro Y1 t1 hK1 hA1 ⟨hr1, hg1⟩
  refine c.s_sub_ri64 hK1 hA1 hin (by omega) hr1 (lz_4 _) ?_
  rintro Y2 t2 hK2 hA2 ⟨hr2, hg2⟩
  have hsp2 : Y2.cpu.gpr.rsp = Addr.add p 112 := by
    rw [hg2, hg1, set_r4, get_r4, hsp]; exact add_sub_lit p (by omega)
  -- `call CPU_IsSupported_SSE41`
  refine c.s_call hK2 hA2 hin (by omega) hr2 (lz_8 _) hinS (by rw [sse41_length]; omega) (by decide)
    (fun i hi => by rw [hsp2, add_sub8 p (m := 104) rfl, addr_add_add]; exact hws _ (by omega)) ?_
  rw [hsp2, add_sub8 p (m := 104) rfl]
  rintro Y3 t3 hK3 hA3 ⟨hr3, hg3⟩
  have hsp3 : Y3.cpu.gpr.rsp = Addr.add p 104 := by rw [hg3, set_4]
  have hsv3 : Saved s₀ Y3 := by simp [Saved, hg3, hg2, hg1]
  refine sub_bit c sse41_shape hK3 hA3 hinS hinC hr3 (fun i hi => by
      rw [hsp3, add_sub_lit p (n := 104) (d := 56) (by omega), addr_add_add]; exact hws _ (by omega))
    (fun i hi => by rw [hsp3, addr_add_add]; exact c.hws _ (hws _ (by omega)))
    hcn (by rw [hsp3, hpn 104 (by omega)]; omega) (by rw [hsp3, hpn 104 (by omega)]; omega) hcf
    (by rw [hsp3, hpn 104 (by omega)]; omega) hin (j₂ := 13) (by omega)
    (by rw [hsp3]; exact read_Vst_self (by rfl) _ (by rw [hpn 104 (by omega)]; omega)) ?_
  intro V4 _ Y4 t4 hK4 hA4 ⟨hr4, hsp4, hsv4, hax4⟩
  rw [hsp3, add_add8] at hsp4
  -- `mov r8d, eax`, `xor eax, eax`, `test r8d, r8d`, `jne`
  refine c.s_mov_rr32 hK4 hA4 hin (by omega) hr4 (lz_13 _) ?_
  rintro Y5 t5 hK5 hA5 ⟨hr5, hg5⟩
  refine c.s_xor_rr32 hK5 hA5 hin (by omega) hr5 (lz_16 _) ?_
  rintro Y6 t6 hK6 hA6 ⟨hr6, hg6⟩
  refine c.s_test_rr32 hK6 hA6 hin (by omega) hr6 (lz_18 _) ?_
  rintro Y7 t7 hK7 hA7 ⟨hr7, hg7, hz7⟩
  have hsv7 : Saved s₀ Y7 :=
    (hsv3.trans hsv4).trans (by simp [Saved, hg7, hg6, hg5])
  have hsp7 : Y7.cpu.gpr.rsp = Addr.add p 112 := by simp [hg7, hg6, hg5, hsp4]
  refine c.s_jcc hK7 hA7 hin (by omega) hr7 (lz_21 _) (tgt := 40) rfl (by omega) (fun hc => ?_) fun hc => ?_
  · -- SSE4.1: `call CPU_IsSupported_AVX2`
    have hsse : prof.reports 1 0 (·.ecx) 19 := hax4 fun h0 => by
      have hzf : Y7.cpu.rflags.zf = false := by simpa [Rflags.cond] using hc
      rw [hz7] at hzf
      simp only [rv, hg6, hg5, set_r0, set_r8, get_r8, get_r0, sw_sw, h0] at hzf
      simp at hzf
    rintro Y8 t8 hK8 hA8 ⟨hr8, hg8⟩
    have hsp8 : Y8.cpu.gpr.rsp = Addr.add p 112 := by rw [hg8, hsp7]
    refine c.s_call hK8 hA8 hin (by omega) hr8 (lz_40 _) hinA2 (by rw [avx2_length]; omega) (by decide)
      (fun i hi => by rw [hsp8, add_sub8 p (m := 104) rfl, addr_add_add]; exact hws _ (by omega)) ?_
    rw [hsp8, add_sub8 p (m := 104) rfl]
    rintro Y9 t9 hK9 hA9 ⟨hr9, hg9⟩
    have hsp9 : Y9.cpu.gpr.rsp = Addr.add p 104 := by rw [hg9, set_4]
    have hsv9 : Saved s₀ Y9 := hsv7.trans (by simp [Saved, hg9, hg8])
    refine sub_avx2 c hpc hK9 hA9 hinA2 hinA hinM hinC hr9 (fun i hi => by
        rw [hsp9, add_sub_lit p (n := 104) (d := 104) (by omega), addr_add_add]; exact hws _ (by omega))
      (fun i hi => by rw [hsp9, addr_add_add]; exact c.hws _ (hws _ (by omega)))
      hcn (by rw [hsp9, hpn 104 (by omega)]; omega) (by rw [hsp9, hpn 104 (by omega)]; omega) hcf
      (by rw [hsp9, hpn 104 (by omega)]; omega) hin (j₂ := 45) (by omega)
      (by rw [hsp9]; exact read_Vst_self (by rfl) _ (by rw [hpn 104 (by omega)]; omega)) ?_
    intro V10 _ Y10 t10 hK10 hA10 ⟨hr10, hsp10, hsv10, hax10⟩
    rw [hsp9, add_add8] at hsp10
    -- `lea rdx, LzFind_SaturSub_256`, `test eax, eax`, `lea rax, LzFind_SaturSub_128`, `cmovne rax, rdx`
    refine c.s_lea_rip hK10 hA10 hin (by omega) hr10 (lz_45 _) (v := 0x425150) (by decide) ?_
    rintro Y11 t11 hK11 hA11 ⟨hr11, hg11, -⟩
    refine c.s_test_rr32 hK11 hA11 hin (by omega) hr11 (lz_52 _) ?_
    rintro Y12 t12 hK12 hA12 ⟨hr12, hg12, hz12⟩
    refine c.s_lea_rip hK12 hA12 hin (by omega) hr12 (lz_54 _) (v := 0x4251b0) (by decide) ?_
    rintro Y13 t13 hK13 hA13 ⟨hr13, hg13, hf13⟩
    refine c.s_cmov hK13 hA13 hin (by omega) hr13 (lz_61 _) ?_
    rintro Y14 t14 hK14 hA14 ⟨hr14, hg14, -⟩
    have hg14' : Y14.cpu.gpr = { Y13.cpu.gpr with
        rax := if Y13.cpu.rflags.cond 5 then Y13.cpu.gpr.rdx else Y13.cpu.gpr.rax } := by
      rw [hg14]; split <;> rfl
    have hz : Y12.cpu.rflags.zf = (Y10.cpu.gpr.rax.setWidth 32 == 0) := by
      rw [hz12]; simp only [rv, hg11, set_r2, get_r0, BitVec.and_self]
    have hrax : Y14.cpu.gpr.rax = if Y12.cpu.rflags.zf then 0x4251b0 else 0x425150 := by
      cases hzz : Y12.cpu.rflags.zf <;> simp [hg14', Rflags.cond, hf13, rf0, hzz, hg13, hg12, hg11]
    -- `mov [g_LzFind_SaturSub], rax`, `add rsp, 8`, `ret`
    refine c.s_mov_rip_r64 hK14 hA14 hin (by omega) hr14 (lz_65 _) (g := 0x7967a0) (by decide) hgf ?_
    rintro Y15 t15 hK15 hA15 ⟨hr15, hg15⟩
    refine c.s_add_ri64 hK15 hA15 hin (by omega) hr15 (lz_72 _) ?_
    rintro Y16 t16 hK16 hA16 ⟨hr16, hg16⟩
    refine c.ret hK16 (callee_of (hsv9.trans (hsv10.trans ?_)) ?_) hin (by omega) hr16 (lz_76 _) fun M hM => ?_
    · simp [Saved, hg16, hg15, hg14', hg13, hg12, hg11]
    · simp only [hg16, hg15, hg14', hg13, hg12, hg11, set_r4, get_r4, set_r0, set_r2]
      rw [hsp10]; exact (add_add8 p _).trans (by rw [hsp])
    · refine lzPost_of (v := Y14.cpu.gpr.rax) ?_ ?_
      · show ofBytesLE 64 (readBytes M 0x7967a0 8) = _
        rw [(c.agreeK hK16 hA16 hM).read (fun i hi => c.hws _ (hgf i hi))]
        exact read_Vst_self (by rfl) _ (by decide)
      · rw [hrax]
        cases hzz : Y12.cpu.rflags.zf
        · rw [hz] at hzz
          have h0 : Y10.cpu.gpr.rax.setWidth 32 ≠ 0 := by simpa using hzz
          obtain ⟨h7, h28, hen⟩ := hax10 h0
          exact Or.inr (Or.inr ⟨rfl, hpc.sse41 hsse, hpc.avx2 h7 hen, hpc.avx h28 hen⟩)
        · exact Or.inr (Or.inl ⟨rfl, hpc.sse41 hsse⟩)
  · -- no SSE4.1: `mov [g_LzFind_SaturSub], rax` (0), `add rsp, 8`, `ret`
    rintro Y8 t8 hK8 hA8 ⟨hr8, hg8⟩
    refine c.s_mov_rip_r64 hK8 hA8 hin (by omega) hr8 (lz_23 _) (g := 0x7967a0) (by decide) hgf ?_
    rintro Y9 t9 hK9 hA9 ⟨hr9, hg9⟩
    refine c.s_add_ri64 hK9 hA9 hin (by omega) hr9 (lz_30 _) ?_
    rintro Y10 t10 hK10 hA10 ⟨hr10, hg10⟩
    refine c.ret hK10 (callee_of (hsv7.trans ?_) ?_) hin (by omega) hr10 (lz_34 _) fun M hM => ?_
    · simp [Saved, hg10, hg9, hg8]
    · simp only [hg10, hg9, hg8, set_r4, get_r4]
      rw [hsp7]; exact (add_add8 p _).trans (by rw [hsp])
    · refine lzPost_of (v := 0) ?_ (Or.inl rfl)
      show ofBytesLE 64 (readBytes M 0x7967a0 8) = _
      rw [(c.agreeK hK10 hA10 hM).read (fun i hi => c.hws _ (hgf i hi))]
      refine (read_Vst_self (by rfl) _ (by decide)).trans ?_
      simp [hg8, hg7, hg6]

/-- `LzFindPrepare`, at `0x427de0`, with its callees' code: on a consistent profile, every call returns, with
`g_LzFind_SaturSub` `NULL`, or a variant whose instructions the processor has. -/
theorem lzFindPrepare (prof : Profile) (hpc : prof.Consistent) {L : List (Addr × List Byte)}
    (hin : CodeIn L 0x427de0 lz) (hinS : CodeIn L 0x424390 sse41) (hinA2 : CodeIn L 0x4244b0 avx2)
    (hinA : CodeIn L 0x424440 avx) (hinM : CodeIn L 0x4242b0 maxf) (hinC : CodeIn L 0x424290 cpuid) :
    ImplementsCall prof 0x427de0 L (lzC prof) := by
  intro s₀ ra hcall
  have hfr := Call.frame_arith (k := 120) (s := s₀)
    (hcall.foot.fits (frame s₀ 120) (by simp [Footprint.data, Contract.footprint, fn]))
  have hslot : ∀ i < 8, ¬ Foot (lzW s₀) (Addr.add s₀.cpu.gpr.rsp i) := by
    rintro i hi ⟨r, hr, hm⟩
    simp only [lzW, List.mem_singleton] at hr
    subst hr
    have hg := hcall.pre.2
    simp only [Rgn.Mem, toNat_add_of_fits hi hfr.2] at hm
    have : (0x7967a0 : Addr).toNat = 0x7967a0 := rfl
    omega
  exact reachOrEndsIn_of_runsFrom fun o ho t =>
    run hpc (Call.of hcall ho hslot) hin hinS hinA2 hinA hinM hinC t

end FV7z.Prepare
