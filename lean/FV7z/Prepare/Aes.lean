import FV7z.Prepare.Sha
/-!
# `AesGenTables` installs the AES-NI and VAES code only on a processor with it (PLAN.md G2, 7-Zip)

`AesGenTables` (`C/Aes.c`, `0x41e540`) fills the tables `InvS` (`0x794680`, 256 bytes, indexed by `Sbox`), and the
encryption and decryption tables (`0x794780` to `0x796780`) in two loops of 256 rounds, then sets
`g_AesCbc_Decode` (`0x7a7e10`), `g_AesCbc_Encode` (`0x7a7e00`), `g_AesCtr_Code` (`0x7a7e08`) and
`g_Aes_SupportedFunctions_Flags` (`0x7a7e18`, 4 bytes): the portable code without `CPU_IsSupported_AES()`
(`0x4242f0`), the AES-NI code with it, and the VAES code where `CPU_IsSupported_VAES_AVX2()` (`0x4245a0`) also holds.
-/
namespace FV7z.Prepare
open ZellicX86 Decode FV7z.Leaf FV7z.Fn

variable {prof : Profile} {k : Nat} {W R : State → List Rgn} {pre : State → Prop} {post : State → State → Prop}
  {e : Addr} {L : List (Addr × List Byte)} {s₀ : State} {ra : Addr} {o : Oracle}

/-- `CPU_IsSupported_VAES_AVX2()`: not 0 only if some CPU reports `CPUID.07H.0H:EBX.AVX2[5]` and
`CPUID.07H.0H:ECX.VAES[9]`, some CPU reports
`CPUID.01H:ECX.AVX[28]` and the kernel enabled the SSE and AVX state in `XCR0`. Its frame and its callees' are the
104 bytes below `rsp`; the canary `fs:[40]` lies apart from them. -/
theorem sub_vaes (c : Call prof k W R pre post e L s₀ ra o) {X : State} {t : Nat} {V : Addr → Byte}
    (hpc : prof.Consistent) (hK : KeptW (ws k W s₀) s₀ X) (hA : Agree (fp k W R pre post L s₀) X.proc.mm.mem V)
    (hin : CodeIn L 0x4245a0 vaes) (hinA : CodeIn L 0x424440 avx) (hinM : CodeIn L 0x4242b0 maxf)
    (hinC : CodeIn L 0x424290 cpuid) (hrip : X.cpu.rip = 0x4245a0)
    (hws : ∀ i < 104, Foot (ws k W s₀) (Addr.add (X.cpu.gpr.rsp - BitVec.ofNat 64 104) i))
    (hrd : ∀ i < 8, Foot (fp k W R pre post L s₀).data (Addr.add X.cpu.gpr.rsp i))
    (hcn : ∀ i < 8, Foot (fp k W R pre post L s₀).data (Addr.add (Addr.add s₀.cpu.seg.fsBase 40) i))
    (h104 : 104 ≤ X.cpu.gpr.rsp.toNat) (hsf : X.cpu.gpr.rsp.toNat + 8 ≤ 2 ^ 64)
    (hcf : (Addr.add s₀.cpu.seg.fsBase 40).toNat + 8 ≤ 2 ^ 64)
    (hca : (Addr.add s₀.cpu.seg.fsBase 40).toNat + 8 ≤ X.cpu.gpr.rsp.toNat - 104 ∨
      X.cpu.gpr.rsp.toNat ≤ (Addr.add s₀.cpu.seg.fsBase 40).toNat)
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (hret : ofBytesLE 64 ((byteAddrs X.cpu.gpr.rsp 8).map V) = e₂.add j₂)
    (k' : ∀ V' : Addr → Byte, (∀ x, (∀ i < 104, x ≠ Addr.add (X.cpu.gpr.rsp - BitVec.ofNat 64 104) i) → V' x = V x) →
      Cont prof k W R pre post L s₀ ra o V' fun Y => Y.cpu.rip = e₂.add j₂ ∧
        Y.cpu.gpr.rsp = X.cpu.gpr.rsp + 8 ∧ Saved X Y ∧
        (Y.cpu.gpr.rax.setWidth 32 ≠ 0 →
          prof.reports 7 0 (·.ebx) 5 ∧ prof.reports 7 0 (·.ecx) 9 ∧ prof.reports 1 0 (·.ecx) 28 ∧ prof.enabled xcr0Avx)) :
    Go prof k W R pre post L s₀ ra o X t := by
  have hl : vaes.length = 113 := vaes_length
  generalize hpd : X.cpu.gpr.rsp - BitVec.ofNat 64 104 = p at hws k'
  have hsp : X.cpu.gpr.rsp = Addr.add p 104 := by rw [← hpd]; exact sub_add_self _ _
  have hpt : p.toNat = X.cpu.gpr.rsp.toNat - 104 := by rw [← hpd, BitVec.toNat_sub]; simp; omega
  have hfit : p.toNat + 112 ≤ 2 ^ 64 := by omega
  have hpn : ∀ d, d < 112 → (Addr.add p d).toNat = p.toNat + d := fun d hd => toNat_addn hd hfit
  generalize hcd : Addr.add s₀.cpu.seg.fsBase 40 = cn at hcn hcf hca
  have hcp : cn.toNat + 8 ≤ p.toNat ∨ p.toNat + 104 ≤ cn.toNat := by omega
  -- `endbr64`, `sub rsp, 40`, `mov rax, fs:[40]`, `mov [rsp + 24], rax`, `xor eax, eax`
  refine c.s_endbr hK hA hin (by omega) (by rw [addr_add_zero]; exact hrip) (vaes_0 _) ?_
  rintro Y1 t1 hK1 hA1 ⟨hr1, hg1⟩
  refine c.s_sub_ri64 hK1 hA1 hin (by omega) hr1 (vaes_4 _) ?_
  rintro Y2 t2 hK2 hA2 ⟨hr2, hg2⟩
  have hsp2 : Y2.cpu.gpr.rsp = Addr.add p 64 := by
    rw [hg2, hg1, set_r4, get_r4, hsp]; exact add_sub_lit p (by omega)
  have hc2 : eaF Y2 40 = cn := by rw [← hcd]; simp only [eaF, hK2.seg]; rfl
  refine c.s_mov_fs hK2 hA2 hin (by omega) hr2 (vaes_8 _) (fun i hi => by rw [hc2]; exact hcn i hi) ?_
  rw [hc2]
  rintro Y3 t3 hK3 hA3 ⟨hr3, hg3⟩
  generalize hcv : ofBytesLE 64 ((byteAddrs cn 8).map V) = cv at hg3
  have hsp3 : Y3.cpu.gpr.rsp = Addr.add p 64 := by simp [hg3, hsp2]
  have e3 : eaD Y3 4 24 = Addr.add p 88 := by simp only [eaD, get_r4, hsp3]; exact addr_add_add p 64 24
  refine c.s_mov_mr hK3 hA3 hin (by omega) hr3 (Or.inr rfl) (vaes_17 _) (fun i hi => by
    rw [e3, addr_add_add]; exact hws _ (by simp at hi; omega)) ?_
  rw [e3, show rv Y3 64 0 = cv by simp [rv, hg3]]
  rintro Y4 t4 hK4 hA4 ⟨hr4, hg4⟩
  generalize hV1 : Vst V (Addr.add p 88) (toBytesLE cv (64 / 8)) = V1 at hA4
  refine c.s_xor_rr32 hK4 hA4 hin (by omega) hr4 (vaes_22 _) ?_
  rintro Y5 t5 hK5 hA5 ⟨hr5, hg5⟩
  have hsp5 : Y5.cpu.gpr.rsp = Addr.add p 64 := by simp [hg5, hg4, hsp3]
  have hsv5 : Saved X Y5 := by simp [Saved, hg5, hg4, hg3, hg2, hg1]
  -- the canary check and the return, from the three paths
  have tail : ∀ (V' : Addr → Byte) Y t', (∀ x, (∀ i < 88, x ≠ Addr.add p i) → V' x = V1 x) →
      KeptW (ws k W s₀) s₀ Y → Agree (fp k W R pre post L s₀) Y.proc.mm.mem V' →
      Y.cpu.rip = (0x4245a0 : Addr).add 35 → Y.cpu.gpr.rsp = Addr.add p 64 → Saved X Y →
      (Y.cpu.gpr.rax.setWidth 32 ≠ 0 →
        prof.reports 7 0 (·.ebx) 5 ∧ prof.reports 7 0 (·.ecx) 9 ∧ prof.reports 1 0 (·.ecx) 28 ∧ prof.enabled xcr0Avx) →
      Go prof k W R pre post L s₀ ra o Y t' := by
    intro V' Y12 t12 hV' hK12 hA12 hr12 hsp12 hsv12 hax12
    have hfrV : ∀ x, (∀ i < 104, x ≠ Addr.add p i) → V' x = V x := by
      intro x hx
      rw [hV' x fun i hi => hx i (by omega), ← hV1]
      exact Vst_apart _ _ _ x fun i hi => by rw [addr_add_add]; exact hx _ (by simp at hi; omega)
    -- `mov rcx, [rsp + 24]`: the canary as stored
    have e12 : eaD Y12 4 24 = Addr.add p 88 := by simp only [eaD, get_r4, hsp12]; exact addr_add_add p 64 24
    refine c.s_mov_rm hK12 hA12 hin (by omega) hr12 (Or.inr rfl) (vaes_35 _) (fun i hi => by
      rw [e12, addr_add_add]; exact c.hws _ (hws _ (by simp at hi; omega))) ?_
    have hcs : ofBytesLE 64 ((byteAddrs (Addr.add p 88) 8).map V') = cv := by
      rw [show (byteAddrs (Addr.add p 88) 8).map V' = (byteAddrs (Addr.add p 88) 8).map V1 from
        List.map_congr_left fun x hx => by
          obtain ⟨i, hi, rfl⟩ := mem_byteAddrs.1 hx
          rw [addr_add_add]
          exact hV' _ fun i' hi' => add_ne_same hfit (by omega) (by omega) (by omega), ← hV1]
      exact read_Vst_self (by rfl) _ (by rw [hpn 88 (by omega)]; omega)
    rw [e12, hcs]
    rintro Y13 t13 hK13 hA13 ⟨hr13, hg13⟩
    -- `xor rcx, fs:[40]`: 0
    have hc13 : eaF Y13 40 = cn := by rw [← hcd]; simp only [eaF, hK13.seg]; rfl
    refine c.s_xor_fs hK13 hA13 hin (by omega) hr13 (vaes_40 _) (fun i hi => by rw [hc13]; exact hcn i hi) ?_
    have hcr : ofBytesLE 64 ((byteAddrs cn 8).map V') = cv := by
      refine Eq.trans ?_ hcv
      congr 1
      apply List.map_congr_left
      intro x hx
      obtain ⟨i, hi, rfl⟩ := mem_byteAddrs.1 hx
      exact hfrV _ fun i' hi' => add_ne_add hi hi' hcf (by omega) (by omega)
    rw [hc13, hcr]
    rintro Y14 t14 hK14 hA14 ⟨hr14, hg14, hz14⟩
    have hzf : Y14.cpu.rflags.zf = true := by rw [hz14, hg13]; simp [BitVec.setWidth_eq]
    refine c.s_jcc hK14 hA14 hin (by omega) hr14 (vaes_49 _) (tgt := 108) rfl (by omega)
      (fun h => by simp [Rflags.cond, hzf] at h) fun _ => ?_
    rintro Y15 t15 hK15 hA15 ⟨hr15, hg15⟩
    -- `add rsp, 40`, `ret`
    refine c.s_add_ri64 hK15 hA15 hin (by omega) hr15 (vaes_51 _) ?_
    rintro Y16 t16 hK16 hA16 ⟨hr16, hg16⟩
    have hsp16 : Y16.cpu.gpr.rsp = X.cpu.gpr.rsp := by
      simp only [hg16, hg15, hg14, hg13, set_r4, get_r4, set_r1]
      rw [hsp12, hsp]; exact addr_add_add p 64 40
    refine c.s_ret hK16 hA16 hin (by omega) hr16 (vaes_55 _) (fun i hi => by rw [hsp16]; exact hrd i hi) hin₂ h₂
      (by
        rw [hsp16, ← hret]; congr 1
        apply List.map_congr_left
        intro x hx
        obtain ⟨i, hi, rfl⟩ := mem_byteAddrs.1 hx
        rw [hsp, addr_add_add]
        exact hfrV _ fun i' hi' => add_ne_same hfit (by omega) (by omega) (by omega)) ?_
    rintro Y t' hKY hAY ⟨hrY, hgY⟩
    refine k' V' (fun x hx => hfrV x hx) Y t' hKY hAY ⟨hrY, by rw [hgY, set_4, hsp16], ?_, fun h => ?_⟩
    · refine Saved.trans hsv12 ?_
      simp [Saved, hgY, hg16, hg15, hg14, hg13]
    · have hax : Y.cpu.gpr.rax.setWidth 32 = Y12.cpu.gpr.rax.setWidth 32 := by
        simp [hgY, hg16, hg15, hg14, hg13]
      rw [hax] at h
      exact hax12 h
  -- `xor eax, eax` (offset 33), then the tail with 0
  have tail0 : ∀ (V' : Addr → Byte) Y t', (∀ x, (∀ i < 88, x ≠ Addr.add p i) → V' x = V1 x) →
      KeptW (ws k W s₀) s₀ Y → Agree (fp k W R pre post L s₀) Y.proc.mm.mem V' →
      Y.cpu.rip = (0x4245a0 : Addr).add 33 → Y.cpu.gpr.rsp = Addr.add p 64 → Saved X Y →
      Go prof k W R pre post L s₀ ra o Y t' := by
    intro V' Y t' hV' hKY hAY hrY hspY hsvY
    refine c.s_xor_rr32 hKY hAY hin (by omega) hrY (vaes_33 _) ?_
    rintro Z tz hKZ hAZ ⟨hrZ, hgZ⟩
    refine tail V' Z tz hV' hKZ hAZ hrZ (by rw [hgZ, set_r0, hspY]) (by rw [Saved, hgZ]; exact hsvY)
      fun h => absurd (by simp [hgZ]) h
  -- `call CPU_IsSupported_AVX`
  refine c.s_call hK5 hA5 hin (by omega) hr5 (vaes_24 _) hinA (by rw [avx_length]; omega) (by decide)
    (fun i hi => by rw [hsp5, add_sub8 p (m := 56) rfl, addr_add_add]; exact hws _ (by omega)) ?_
  rw [hsp5, add_sub8 p (m := 56) rfl]
  rintro Y6 t6 hK6 hA6 ⟨hr6, hg6⟩
  have hsp6 : Y6.cpu.gpr.rsp = Addr.add p 56 := by rw [hg6, set_4]
  have hs56 : Y6.cpu.gpr.rsp - BitVec.ofNat 64 56 = p := by
    rw [hsp6, add_sub_lit p (Nat.le_refl 56), Nat.sub_self, addr_add_zero]
  refine sub_avx c hpc hK6 hA6 hinA hinC (by rw [hr6]) (fun i hi => by rw [hs56]; exact hws i (by omega))
    (fun i hi => by rw [hsp6, addr_add_add]; exact c.hws _ (hws _ (by omega)))
    (by rw [← hcd] at hcn; exact hcn) (by rw [hsp6, hpn 56 (by omega)]; omega)
    (by rw [hsp6, hpn 56 (by omega)]; omega) (by rw [← hcd] at hcf; exact hcf)
    (by rw [hsp6, hpn 56 (by omega), ← hcd] at *; omega) hin (j₂ := 29) (by omega)
    (by rw [hsp6]; exact read_Vst_self (by rfl) _ (by rw [hpn 56 (by omega)]; omega)) ?_
  intro V3 hfr3 Y7 t7 hK7 hA7 ⟨hr7, hsp7, hsv7, hax7⟩
  rw [hs56] at hfr3
  rw [hsp6, add_add8] at hsp7
  have hV3 : ∀ x, (∀ i < 88, x ≠ Addr.add p i) → V3 x = V1 x := by
    intro x hx
    rw [hfr3 x fun i hi => hx i (by omega)]
    exact Vst_apart _ _ _ x fun i hi => by rw [addr_add_add]; exact hx _ (by simp at hi; omega)
  have hsv7' : Saved X Y7 := Saved.trans hsv5 (Saved.trans (by simp [Saved, hg6]) hsv7)
  -- `test eax, eax`, `jne`
  refine c.s_test_rr32 hK7 hA7 hin (by omega) hr7 (vaes_29 _) ?_
  rintro Y8 t8 hK8 hA8 ⟨hr8, hg8, hz8⟩
  have hsp8 : Y8.cpu.gpr.rsp = Addr.add p 64 := by rw [hg8, hsp7]
  have hsv8 : Saved X Y8 := by rw [Saved, hg8]; exact hsv7'
  refine c.s_jcc hK8 hA8 hin (by omega) hr8 (vaes_31 _) (tgt := 64) rfl (by omega) (fun h => ?_) fun h => ?_
  · -- AVX: `call z7_x86_cpuid_GetMaxFunc`
    have hav := hax7 fun h0 => by
      simp only [Rflags.cond, hz8, Bool.not_eq_true'] at h
      simp [rv, h0] at h
    rintro Y9 t9 hK9 hA9 ⟨hr9, hg9⟩
    refine c.s_call hK9 hA9 hin (by omega) hr9 (vaes_64 _) hinM (by rw [maxf_length]; omega) (by decide)
      (fun i hi => by rw [hg9, hsp8, add_sub8 p (m := 56) rfl, addr_add_add]; exact hws _ (by omega)) ?_
    rw [hg9, hsp8, add_sub8 p (m := 56) rfl]
    rintro Y10 t10 hK10 hA10 ⟨hr10, hg10⟩
    have hsp10 : Y10.cpu.gpr.rsp = Addr.add p 56 := by rw [hg10, set_4]
    have hs24 : Y10.cpu.gpr.rsp - BitVec.ofNat 64 24 = Addr.add p 32 := by
      rw [hsp10, add_sub_lit p (by omega : 24 ≤ 56)]
    refine sub_maxf c hK10 hA10 hinM (by rw [hr10])
      (fun i hi => by rw [hs24, addr_add_add]; exact hws _ (by omega))
      (fun i hi => by rw [hsp10, addr_add_add]; exact c.hws _ (hws _ (by omega)))
      (by rw [← hcd] at hcn; exact hcn) (by rw [hsp10, hpn 56 (by omega)]; omega)
      (by rw [hsp10, hpn 56 (by omega)]; omega) (by rw [← hcd] at hcf; exact hcf)
      (by rw [hsp10, hpn 56 (by omega), ← hcd] at *; omega) hin (j₂ := 69) (by omega)
      (by rw [hsp10]; exact read_Vst_self (by rfl) _ (by rw [hpn 56 (by omega)]; omega)) ?_
    intro V5 hfr5 Y11 t11 hK11 hA11 ⟨hr11, hsp11, hsv11⟩
    rw [hs24] at hfr5
    rw [hsp10, add_add8] at hsp11
    have hV5 : ∀ x, (∀ i < 88, x ≠ Addr.add p i) → V5 x = V1 x := by
      intro x hx
      rw [hfr5 x fun i hi => by rw [addr_add_add]; exact hx _ (by omega)]
      rw [Vst_apart _ _ _ x fun i hi => by rw [addr_add_add]; exact hx _ (by simp at hi; omega)]
      exact hV3 x hx
    have hsv11' : Saved X Y11 := Saved.trans hsv8 (Saved.trans (by simp [Saved, hg10]) hsv11)
    -- `cmp eax, 6`, `jbe`
    refine c.s_cmp_ri32 hK11 hA11 hin (by omega) hr11 (vaes_69 _) ?_
    rintro Y12 t12 hK12 hA12 ⟨hr12, hg12, -⟩
    have hsp12 : Y12.cpu.gpr.rsp = Addr.add p 64 := by rw [hg12, hsp11]
    have hsv12 : Saved X Y12 := by rw [Saved, hg12]; exact hsv11'
    refine c.s_jcc hK12 hA12 hin (by omega) hr12 (vaes_72 _) (tgt := 33) rfl (by omega) (fun _ => ?_) fun _ => ?_
    · rintro Y13 t13 hK13 hA13 ⟨hr13, hg13⟩
      exact tail0 V5 Y13 t13 hV5 hK13 hA13 hr13 (by rw [hg13, hsp12]) (by rw [Saved, hg13]; exact hsv12)
    -- `mov rdi, rsp`, `mov esi, 7`, `call z7_x86_cpuid`
    rintro Y13 t13 hK13 hA13 ⟨hr13, hg13⟩
    refine c.s_mov_rr64 hK13 hA13 hin (by omega) hr13 (vaes_74 _) ?_
    rintro Y14 t14 hK14 hA14 ⟨hr14, hg14⟩
    refine c.s_mov_ri32 hK14 hA14 hin (by omega) hr14 (vaes_77 _) ?_
    rintro Y15 t15 hK15 hA15 ⟨hr15, hg15⟩
    have hsp15 : Y15.cpu.gpr.rsp = Addr.add p 64 := by simp [hg15, hg14, hg13, hsp12]
    refine c.s_call hK15 hA15 hin (by omega) hr15 (vaes_82 _) hinC (by rw [cpuid_length]; omega) (by decide)
      (fun i hi => by rw [hsp15, add_sub8 p (m := 56) rfl, addr_add_add]; exact hws _ (by omega)) ?_
    rw [hsp15, add_sub8 p (m := 56) rfl]
    rintro Y16 t16 hK16 hA16 ⟨hr16, hg16⟩
    have hsp16 : Y16.cpu.gpr.rsp = Addr.add p 56 := by rw [hg16, set_4]
    have hdi16 : Y16.cpu.gpr.rdi = Addr.add p 64 := by simp [hg16, hg15, hg14, hg13, hsp12]
    have hsi16 : Y16.cpu.gpr.rsi.setWidth 32 = 7 := by simp [hg16, hg15]
    refine sub_cpuid c hK16 hA16 hinC (by rw [hr16]) (fun i hi => by
        rw [hsp16, add_sub8 p (m := 48) rfl, addr_add_add]; exact hws _ (by omega))
      (fun i hi => by rw [hdi16, addr_add_add]; exact hws _ (by omega))
      (fun i hi => by rw [hsp16, addr_add_add]; exact c.hws _ (hws _ (by omega)))
      (by rw [hsp16, hpn 56 (by omega)]; omega) (by rw [hsp16, hdi16, hpn 56 (by omega), hpn 64 (by omega)]; omega)
      (by rw [hdi16, hpn 64 (by omega)]; omega) hin (j₂ := 87) (by omega)
      (by rw [hsp16]; exact read_Vst_self (by rfl) _ (by rw [hpn 56 (by omega)]; omega)) ?_
    intro V7 hfr7 ⟨cpu, hcpu, hrep⟩ Y17 t17 hK17 hA17 ⟨hr17, hsp17, hsv17⟩
    rw [hsi16, hdi16] at hrep
    rw [hsp16, add_add8] at hsp17
    rw [hsp16, add_sub8 p (m := 48) rfl, hdi16] at hfr7
    have hV7 : ∀ x, (∀ i < 88, x ≠ Addr.add p i) → V7 x = V1 x := by
      intro x hx
      rw [hfr7 x (fun i hi => by rw [addr_add_add]; exact hx _ (by omega)) (fun i hi => by
        rw [addr_add_add]; exact hx _ (by omega))]
      rw [Vst_apart _ _ _ x fun i hi => by rw [addr_add_add]; exact hx _ (by simp at hi; omega)]
      exact hV5 x hx
    have hsv17' : Saved X Y17 := Saved.trans hsv12 (Saved.trans (by simp [Saved, hg16, hg15, hg14, hg13]) hsv17)
    -- `mov eax, [rsp + 4]`, `mov edx, [rsp + 8]`, `shr eax, 5`, `shr edx, 9`, `and eax, edx`, `and eax, 1`, `jmp`
    have e17 : eaD Y17 4 4 = Addr.add (Addr.add p 64) 4 := by simp only [eaD, get_r4, hsp17]; rfl
    refine c.s_mov_rm hK17 hA17 hin (by omega) hr17 (Or.inl rfl) (vaes_87 _) (fun i hi => by
      rw [e17, addr_add_add, addr_add_add]; exact c.hws _ (hws _ (by simp at hi; omega))) ?_
    rw [e17, hrep.2.1]
    rintro Y18 t18 hK18 hA18 ⟨hr18, hg18⟩
    have e18 : eaD Y18 4 8 = Addr.add (Addr.add p 64) 8 := by
      simp only [eaD, get_r4, hg18, set_r0, hsp17]; rfl
    refine c.s_mov_rm hK18 hA18 hin (by omega) hr18 (Or.inl rfl) (vaes_91 _) (fun i hi => by
      rw [e18, addr_add_add, addr_add_add]; exact c.hws _ (hws _ (by simp at hi; omega))) ?_
    rw [e18, hrep.2.2.1]
    rintro Y19 t19 hK19 hA19 ⟨hr19, hg19⟩
    refine c.s_shr_ri32 hK19 hA19 hin (by omega) hr19 (by decide) (vaes_95 _) ?_
    rintro Y20 t20 hK20 hA20 ⟨hr20, hg20⟩
    refine c.s_shr_ri32 hK20 hA20 hin (by omega) hr20 (by decide) (vaes_98 _) ?_
    rintro Y21 t21 hK21 hA21 ⟨hr21, hg21⟩
    refine c.s_and_rr32 hK21 hA21 hin (by omega) hr21 (vaes_101 _) ?_
    rintro Y22 t22 hK22 hA22 ⟨hr22, hg22⟩
    refine c.s_and_ri32 hK22 hA22 hin (by omega) hr22 (vaes_103 _) ?_
    rintro Y23 t23 hK23 hA23 ⟨hr23, hg23, -⟩
    refine c.s_jmp hK23 hA23 hin (by omega) hr23 (vaes_106 _) (tgt := 35) rfl (by omega) ?_
    rintro Y24 t24 hK24 hA24 ⟨hr24, hg24⟩
    refine tail V7 Y24 t24 hV7 hK24 hA24 hr24 (by simp [hg24, hg23, hg22, hg21, hg20, hg19, hg18, hsp17])
      (by refine Saved.trans hsv17' ?_; simp [Saved, hg24, hg23, hg22, hg21, hg20, hg19, hg18]) fun h0 => ?_
    have hax : Y24.cpu.gpr.rax.setWidth 32 =
        ((prof.cpuid cpu 7 0).ebx >>> 5 &&& (prof.cpuid cpu 7 0).ecx >>> 9) &&& 1#32 := by
      simp only [hg24, hg23, hg22, hg21, hg20, hg19, hg18, rv, set_r0, set_r2, get_r0, get_r2, sw_sw]
    rw [hax] at h0
    obtain ⟨hb5, hb9⟩ := bits_and _ _ h0
    simp only [BitVec.getLsbD_ushiftRight, Nat.add_zero] at hb5 hb9
    exact ⟨⟨cpu, hcpu, hb5⟩, ⟨cpu, hcpu, hb9⟩, hav.1, hav.2.2⟩
  · -- not AVX: 0
    rintro Y9 t9 hK9 hA9 ⟨hr9, hg9⟩
    exact tail0 V3 Y9 t9 hV3 hK9 hA9 hr9 (by rw [hg9, hsp8]) (by rw [Saved, hg9]; exact hsv8)

end FV7z.Prepare
