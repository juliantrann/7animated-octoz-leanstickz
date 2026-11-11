import FV7z.Prepare.LzFind
/-!
# `z7_SwapBytesPrepare` sets a mode only the processor runs (PLAN.md G2, "Dispatch theo CPUID", 7-Zip)

`z7_SwapBytesPrepare` (`C/SwapBytes.c`, at `0x43d3d0` in `7zzs` 26.06) sets `g_SwapBytes_Mode` (`0x7967b8`, 4 bytes),
which `z7_SwapBytes2`/`z7_SwapBytes4` branch on: 3 (AVX2) if `CPU_IsSupported_AVX2()`, else 2 (SSSE3) if
`CPU_IsSupported_SSSE3()`, else 1 (SSE2). On a consistent profile every call returns, with the mode one of the three,
and 2 or 3 only on a processor with the features that mode's code uses.
-/
namespace FV7z.Prepare
open ZellicX86 Decode FV7z.Leaf FV7z.Fn

/-- The mode `z7_SwapBytesPrepare` sets: `g_SwapBytes_Mode`. -/
def swW (_ : State) : List Rgn := [⟨0x7967b8, 4⟩]

/-- The canary apart from the stack it uses, and the mode apart from the return address's slot. -/
def swPre (s : State) : Prop :=
  ((Addr.add s.cpu.seg.fsBase 40).toNat + 8 ≤ s.cpu.gpr.rsp.toNat - 120 ∨
    s.cpu.gpr.rsp.toNat ≤ (Addr.add s.cpu.seg.fsBase 40).toNat) ∧
  (0x7967b8 + 4 ≤ s.cpu.gpr.rsp.toNat ∨ s.cpu.gpr.rsp.toNat + 8 ≤ 0x7967b8)

/-- `g_SwapBytes_Mode` in `Y`. -/
def swVal (Y : State) : BitVec 32 := ofBytesLE 32 (readBytes Y.proc.mm.mem 0x7967b8 4)

/-- At the return: 1 (SSE2), or 2 on a processor with SSSE3, or 3 on one with AVX2 and AVX. -/
def swPost (prof : Profile) (_ Y : State) : Prop :=
  swVal Y = 1 ∨ (swVal Y = 2 ∧ prof.feat.ssse3 = true) ∨
    (swVal Y = 3 ∧ prof.feat.avx2 = true ∧ prof.feat.avx = true)

/-- The contract: a stack of 120 bytes, the mode written, the canary read. -/
abbrev swC (prof : Profile) : Contract := fn 120 swW lzR swPre (swPost prof)

theorem swPost_of {prof : Profile} {s₀ Y : State} {v : BitVec 32}
    (hv : ofBytesLE 32 (readBytes Y.proc.mm.mem 0x7967b8 4) = v)
    (h : v = 1 ∨ (v = 2 ∧ prof.feat.ssse3 = true) ∨ (v = 3 ∧ prof.feat.avx2 = true ∧ prof.feat.avx = true)) :
    swPost prof s₀ Y := by
  unfold swPost swVal; rw [hv]; exact h

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {ra : Addr} {o : Oracle}

theorem swRun (hpc : prof.Consistent) (c : Call prof 120 swW lzR swPre (swPost prof) 0x43d3d0 L s₀ ra o)
    (hin : CodeIn L 0x43d3d0 swap) (hinS : CodeIn L 0x424340 ssse3) (hinA2 : CodeIn L 0x4244b0 avx2)
    (hinA : CodeIn L 0x424440 avx) (hinM : CodeIn L 0x4242b0 maxf) (hinC : CodeIn L 0x424290 cpuid) (t : Nat) :
    Go prof 120 swW lzR swPre (swPost prof) L s₀ ra o s₀ t := by
  have hl : swap.length = 67 := swap_length
  have hK0 : KeptW (ws 120 swW s₀) s₀ s₀ := KeptW.refl _ _
  have hA0 : Agree (fp 120 swW lzR swPre (swPost prof) L s₀) s₀.proc.mm.mem
      (fun a => s₀.proc.mm.mem.readByte a) := fun _ _ => rfl
  obtain ⟨hpt0, hsf0⟩ := Call.frame_arith c.frame_fits
  obtain ⟨hca0, -⟩ := c.call.pre
  generalize hpd : s₀.cpu.gpr.rsp - BitVec.ofNat 64 120 = p at hpt0
  have hsp : s₀.cpu.gpr.rsp = Addr.add p 120 := by rw [← hpd]; exact sub_add_self _ _
  have hfit : p.toNat + 128 ≤ 2 ^ 64 := by omega
  have hpn : ∀ d, d < 128 → (Addr.add p d).toNat = p.toNat + d := fun d hd => toNat_addn hd hfit
  have hws : ∀ i < 120, Foot (ws 120 swW s₀) (Addr.add p i) := fun i hi =>
    ⟨below s₀ 120, by simp, by simp only [below, hpd]; exact mem_add_of_fits hi (by omega)⟩
  -- the canary
  have hcr : (⟨Addr.add s₀.cpu.seg.fsBase 40, 8⟩ : Rgn) ∈ (fp 120 swW lzR swPre (swPost prof) L s₀).data := by
    simp [Footprint.data, Contract.footprint, fn, lzR]
  have hcf : (Addr.add s₀.cpu.seg.fsBase 40).toNat + 8 ≤ 2 ^ 64 :=
    c.call.foot.fits _ (List.mem_append_left _ hcr)
  have hcn : ∀ i < 8, Foot (fp 120 swW lzR swPre (swPost prof) L s₀).data
      (Addr.add (Addr.add s₀.cpu.seg.fsBase 40) i) := fun i hi => ⟨_, hcr, mem_add_of_fits hi hcf⟩
  -- the mode
  have hgf : ∀ i < 4, Foot (ws 120 swW s₀) (Addr.add 0x7967b8 i) := fun i hi =>
    ⟨⟨0x7967b8, 4⟩, by simp [swW], mem_add_of_fits hi (by decide)⟩
  -- `endbr64`, `sub rsp, 8`
  refine c.s_endbr hK0 hA0 hin (by omega) (by rw [addr_add_zero]; exact c.call.shape.1) (swap_0 _) ?_
  rintro Y1 t1 hK1 hA1 ⟨hr1, hg1⟩
  refine c.s_sub_ri64 hK1 hA1 hin (by omega) hr1 (swap_4 _) ?_
  rintro Y2 t2 hK2 hA2 ⟨hr2, hg2⟩
  have hsp2 : Y2.cpu.gpr.rsp = Addr.add p 112 := by
    rw [hg2, hg1, set_r4, get_r4, hsp]; exact add_sub_lit p (by omega)
  -- `call CPU_IsSupported_AVX2`
  refine c.s_call hK2 hA2 hin (by omega) hr2 (swap_8 _) hinA2 (by rw [avx2_length]; omega) (by decide)
    (fun i hi => by rw [hsp2, add_sub8 p (m := 104) rfl, addr_add_add]; exact hws _ (by omega)) ?_
  rw [hsp2, add_sub8 p (m := 104) rfl]
  rintro Y3 t3 hK3 hA3 ⟨hr3, hg3⟩
  have hsp3 : Y3.cpu.gpr.rsp = Addr.add p 104 := by rw [hg3, set_4]
  have hsv3 : Saved s₀ Y3 := by simp [Saved, hg3, hg2, hg1]
  refine sub_avx2 c hpc hK3 hA3 hinA2 hinA hinM hinC hr3 (fun i hi => by
      rw [hsp3, add_sub_lit p (n := 104) (d := 104) (by omega), addr_add_add]; exact hws _ (by omega))
    (fun i hi => by rw [hsp3, addr_add_add]; exact c.hws _ (hws _ (by omega)))
    hcn (by rw [hsp3, hpn 104 (by omega)]; omega) (by rw [hsp3, hpn 104 (by omega)]; omega) hcf
    (by rw [hsp3, hpn 104 (by omega)]; omega) hin (j₂ := 13) (by omega)
    (by rw [hsp3]; exact read_Vst_self (by rfl) _ (by rw [hpn 104 (by omega)]; omega)) ?_
  intro V4 _ Y4 t4 hK4 hA4 ⟨hr4, hsp4, hsv4, hax4⟩
  rw [hsp3, add_add8] at hsp4
  -- `mov r8d, eax`, `mov eax, 3`, `test r8d, r8d`, `je`
  refine c.s_mov_rr32 hK4 hA4 hin (by omega) hr4 (swap_13 _) ?_
  rintro Y5 t5 hK5 hA5 ⟨hr5, hg5⟩
  refine c.s_mov_ri32 hK5 hA5 hin (by omega) hr5 (swap_16 _) ?_
  rintro Y6 t6 hK6 hA6 ⟨hr6, hg6⟩
  refine c.s_test_rr32 hK6 hA6 hin (by omega) hr6 (swap_21 _) ?_
  rintro Y7 t7 hK7 hA7 ⟨hr7, hg7, hz7⟩
  have hsv7 : Saved s₀ Y7 :=
    (hsv3.trans hsv4).trans (by simp [Saved, hg7, hg6, hg5])
  have hsp7 : Y7.cpu.gpr.rsp = Addr.add p 112 := by simp [hg7, hg6, hg5, hsp4]
  refine c.s_jcc hK7 hA7 hin (by omega) hr7 (swap_24 _) (tgt := 40) rfl (by omega) (fun _ => ?_) fun hc => ?_
  · -- not AVX2: `call CPU_IsSupported_SSSE3`
    rintro Y8 t8 hK8 hA8 ⟨hr8, hg8⟩
    have hsp8 : Y8.cpu.gpr.rsp = Addr.add p 112 := by rw [hg8, hsp7]
    refine c.s_call hK8 hA8 hin (by omega) hr8 (swap_40 _) hinS (by rw [ssse3_length]; omega) (by decide)
      (fun i hi => by rw [hsp8, add_sub8 p (m := 104) rfl, addr_add_add]; exact hws _ (by omega)) ?_
    rw [hsp8, add_sub8 p (m := 104) rfl]
    rintro Y9 t9 hK9 hA9 ⟨hr9, hg9⟩
    have hsp9 : Y9.cpu.gpr.rsp = Addr.add p 104 := by rw [hg9, set_4]
    have hsv9 : Saved s₀ Y9 := hsv7.trans (by simp [Saved, hg9, hg8])
    refine sub_bit c ssse3_shape hK9 hA9 hinS hinC hr9 (fun i hi => by
        rw [hsp9, add_sub_lit p (n := 104) (d := 56) (by omega), addr_add_add]; exact hws _ (by omega))
      (fun i hi => by rw [hsp9, addr_add_add]; exact c.hws _ (hws _ (by omega)))
      hcn (by rw [hsp9, hpn 104 (by omega)]; omega) (by rw [hsp9, hpn 104 (by omega)]; omega) hcf
      (by rw [hsp9, hpn 104 (by omega)]; omega) hin (j₂ := 45) (by omega)
      (by rw [hsp9]; exact read_Vst_self (by rfl) _ (by rw [hpn 104 (by omega)]; omega)) ?_
    intro V10 _ Y10 t10 hK10 hA10 ⟨hr10, hsp10, hsv10, hax10⟩
    rw [hsp9, add_add8] at hsp10
    -- `test eax, eax`, `setne al`, `movzx eax, al`, `add eax, 1`
    refine c.s_test_rr32 hK10 hA10 hin (by omega) hr10 (swap_45 _) ?_
    rintro Y11 t11 hK11 hA11 ⟨hr11, hg11, hz11⟩
    refine c.s_setcc hK11 hA11 hin (by omega) hr11 (swap_47 _) ?_
    rintro Y12 t12 hK12 hA12 ⟨hr12, v, hg12, hv12⟩
    refine c.s_movzx_rr8 hK12 hA12 hin (by omega) hr12 (swap_50 _) ?_
    rintro Y13 t13 hK13 hA13 ⟨hr13, hg13⟩
    refine c.s_add_ri32 hK13 hA13 hin (by omega) hr13 (swap_53 _) ?_
    rintro Y14 t14 hK14 hA14 ⟨hr14, hg14⟩
    have hval : rv Y14 32 0 = ((BitVec.ofBool (Y11.cpu.rflags.cond 5)).setWidth 8).setWidth 32 + 1 := by
      simp only [rv, hg14, hg13, hg12, set_r0, get_r0, sw_sw]
      rw [hv12]; rfl
    -- `mov [g_SwapBytes_Mode], eax`, `add rsp, 8`, `ret`
    refine c.s_mov_rip_r32 hK14 hA14 hin (by omega) hr14 (swap_56 _) (g := 0x7967b8) (by decide) hgf ?_
    rintro Y15 t15 hK15 hA15 ⟨hr15, hg15⟩
    refine c.s_add_ri64 hK15 hA15 hin (by omega) hr15 (swap_62 _) ?_
    rintro Y16 t16 hK16 hA16 ⟨hr16, hg16⟩
    refine c.ret hK16 (callee_of (hsv9.trans (hsv10.trans ?_)) ?_) hin (by omega) hr16 (swap_66 _) fun M hM => ?_
    · simp [Saved, hg16, hg15, hg14, hg13, hg12, hg11]
    · simp only [hg16, hg15, hg14, hg13, hg12, hg11, set_r4, get_r4, set_r0]
      rw [hsp10]; exact (add_add8 p _).trans (by rw [hsp])
    · refine swPost_of (v := rv Y14 32 0) ?_ ?_
      · show ofBytesLE 32 (readBytes M 0x7967b8 4) = _
        rw [(c.agreeK hK16 hA16 hM).read (fun i hi => c.hws _ (hgf i hi))]
        exact read_Vst_self (by rfl) _ (by decide)
      · rw [hval]
        cases hzz : Y11.cpu.rflags.zf
        · have h0 : Y10.cpu.gpr.rax.setWidth 32 ≠ 0 := by
            intro h0
            rw [hz11] at hzz
            simp only [rv, get_r0, h0] at hzz
            simp at hzz
          exact Or.inr (Or.inl ⟨by simp [Rflags.cond, hzz], hpc.ssse3 (hax10 h0)⟩)
        · exact Or.inl (by simp [Rflags.cond, hzz])
  · -- AVX2: `mov [g_SwapBytes_Mode], eax` (3), `add rsp, 8`, `ret`
    have hav : prof.feat.avx2 = true ∧ prof.feat.avx = true := by
      have h0 : Y4.cpu.gpr.rax.setWidth 32 ≠ 0 := by
        intro h0
        have hzf : Y7.cpu.rflags.zf = false := by simpa [Rflags.cond] using hc
        rw [hz7] at hzf
        simp only [rv, hg6, hg5, set_r0, set_r8, get_r8, get_r0, sw_sw, h0] at hzf
        simp at hzf
      obtain ⟨h7, h28, hen⟩ := hax4 h0
      exact ⟨hpc.avx2 h7 hen, hpc.avx h28 hen⟩
    rintro Y8 t8 hK8 hA8 ⟨hr8, hg8⟩
    refine c.s_mov_rip_r32 hK8 hA8 hin (by omega) hr8 (swap_26 _) (g := 0x7967b8) (by decide) hgf ?_
    rintro Y9 t9 hK9 hA9 ⟨hr9, hg9⟩
    refine c.s_add_ri64 hK9 hA9 hin (by omega) hr9 (swap_32 _) ?_
    rintro Y10 t10 hK10 hA10 ⟨hr10, hg10⟩
    refine c.ret hK10 (callee_of (hsv7.trans ?_) ?_) hin (by omega) hr10 (swap_36 _) fun M hM => ?_
    · simp [Saved, hg10, hg9, hg8]
    · simp only [hg10, hg9, hg8, set_r4, get_r4]
      rw [hsp7]; exact (add_add8 p _).trans (by rw [hsp])
    · refine swPost_of (v := 3) ?_ (Or.inr (Or.inr ⟨rfl, hav⟩))
      show ofBytesLE 32 (readBytes M 0x7967b8 4) = _
      rw [(c.agreeK hK10 hA10 hM).read (fun i hi => c.hws _ (hgf i hi))]
      refine (read_Vst_self (by rfl) _ (by decide)).trans ?_
      simp [rv, hg8, hg7, hg6]

/-- `z7_SwapBytesPrepare`, at `0x43d3d0`, with its callees' code: on a consistent profile, every call returns, with
`g_SwapBytes_Mode` 1, or a mode whose instructions the processor has. -/
theorem swapBytesPrepare (prof : Profile) (hpc : prof.Consistent) {L : List (Addr × List Byte)}
    (hin : CodeIn L 0x43d3d0 swap) (hinS : CodeIn L 0x424340 ssse3) (hinA2 : CodeIn L 0x4244b0 avx2)
    (hinA : CodeIn L 0x424440 avx) (hinM : CodeIn L 0x4242b0 maxf) (hinC : CodeIn L 0x424290 cpuid) :
    ImplementsCall prof 0x43d3d0 L (swC prof) := by
  intro s₀ ra hcall
  have hfr := Call.frame_arith (k := 120) (s := s₀)
    (hcall.foot.fits (frame s₀ 120) (by simp [Footprint.data, Contract.footprint, fn]))
  have hslot : ∀ i < 8, ¬ Foot (swW s₀) (Addr.add s₀.cpu.gpr.rsp i) := by
    rintro i hi ⟨r, hr, hm⟩
    simp only [swW, List.mem_singleton] at hr
    subst hr
    have hg := hcall.pre.2
    simp only [Rgn.Mem, toNat_add_of_fits hi hfr.2] at hm
    have : (0x7967b8 : Addr).toNat = 0x7967b8 := rfl
    omega
  exact reachOrEndsIn_of_runsFrom fun o ho t =>
    swRun hpc (Call.of hcall ho hslot) hin hinS hinA2 hinA hinM hinC t

end FV7z.Prepare
