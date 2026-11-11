import FV7z.Prepare.Swap
/-!
# `Sha1Prepare` and `Sha256Prepare` install the SHA-NI code only on a processor with it (PLAN.md G2, 7-Zip)

`CPU_IsSupported_SHA` (`C/CpuArch.c`, `0x4243e0`): `CPUID` leaf 7 only if `z7_x86_cpuid_GetMaxFunc()` is at least 7,
then bit 29 of `EBX`. `Sha1Prepare` (`C/Sha1.c`, `0x43a740`) and `Sha256Prepare` (`C/Sha256.c`, `0x43b3e0`) have the
same code (`ShaPrep`): if `CPU_IsSupported_SHA()` and `CPU_IsSupported_SSSE3()`, both function pointers
(`g_SHA*_FUNC_UPDATE_BLOCKS`, `g_SHA*_FUNC_UPDATE_BLOCKS_HW`) are the SHA-NI `*_UpdateBlocks_HW`; otherwise the first
is the portable `*_UpdateBlocks` and the second `NULL`.
-/
namespace FV7z.Prepare
open ZellicX86 Decode FV7z.Leaf FV7z.Fn

variable {prof : Profile} {k : Nat} {W R : State → List Rgn} {pre : State → Prop} {post : State → State → Prop}
  {e : Addr} {L : List (Addr × List Byte)} {s₀ : State} {ra : Addr} {o : Oracle}

/-- `CPU_IsSupported_SHA()`: not 0 only if some CPU reports `CPUID.(EAX=07H,ECX=0):EBX.SHA[29]`. Its frame and its
callees' are the 72 bytes below `rsp`; the canary `fs:[40]` lies apart from them. -/
theorem sub_sha (c : Call prof k W R pre post e L s₀ ra o) {X : State} {t : Nat} {V : Addr → Byte}
    (hK : KeptW (ws k W s₀) s₀ X) (hA : Agree (fp k W R pre post L s₀) X.proc.mm.mem V)
    (hin : CodeIn L 0x4243e0 sha) (hinM : CodeIn L 0x4242b0 maxf) (hinC : CodeIn L 0x424290 cpuid)
    (hrip : X.cpu.rip = 0x4243e0)
    (hws : ∀ i < 72, Foot (ws k W s₀) (Addr.add (X.cpu.gpr.rsp - BitVec.ofNat 64 72) i))
    (hrd : ∀ i < 8, Foot (fp k W R pre post L s₀).data (Addr.add X.cpu.gpr.rsp i))
    (hcn : ∀ i < 8, Foot (fp k W R pre post L s₀).data (Addr.add (Addr.add s₀.cpu.seg.fsBase 40) i))
    (h72 : 72 ≤ X.cpu.gpr.rsp.toNat) (hsf : X.cpu.gpr.rsp.toNat + 8 ≤ 2 ^ 64)
    (hcf : (Addr.add s₀.cpu.seg.fsBase 40).toNat + 8 ≤ 2 ^ 64)
    (hca : (Addr.add s₀.cpu.seg.fsBase 40).toNat + 8 ≤ X.cpu.gpr.rsp.toNat - 72 ∨
      X.cpu.gpr.rsp.toNat ≤ (Addr.add s₀.cpu.seg.fsBase 40).toNat)
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (hret : ofBytesLE 64 ((byteAddrs X.cpu.gpr.rsp 8).map V) = e₂.add j₂)
    (k' : ∀ V' : Addr → Byte, (∀ x, (∀ i < 72, x ≠ Addr.add (X.cpu.gpr.rsp - BitVec.ofNat 64 72) i) → V' x = V x) →
      Cont prof k W R pre post L s₀ ra o V' fun Y => Y.cpu.rip = e₂.add j₂ ∧
        Y.cpu.gpr.rsp = X.cpu.gpr.rsp + 8 ∧ Saved X Y ∧
        (Y.cpu.gpr.rax.setWidth 32 ≠ 0 → prof.reports 7 0 (·.ebx) 29)) :
    Go prof k W R pre post L s₀ ra o X t := by
  have hl : sha.length = 89 := sha_length
  generalize hpd : X.cpu.gpr.rsp - BitVec.ofNat 64 72 = p at hws k'
  have hsp : X.cpu.gpr.rsp = Addr.add p 72 := by rw [← hpd]; exact sub_add_self _ _
  have hpt : p.toNat = X.cpu.gpr.rsp.toNat - 72 := by rw [← hpd, BitVec.toNat_sub]; simp; omega
  have hfit : p.toNat + 80 ≤ 2 ^ 64 := by omega
  have hpn : ∀ d, d < 80 → (Addr.add p d).toNat = p.toNat + d := fun d hd => toNat_addn hd hfit
  generalize hcd : Addr.add s₀.cpu.seg.fsBase 40 = cn at hcn hcf hca
  have hcp : cn.toNat + 8 ≤ p.toNat ∨ p.toNat + 72 ≤ cn.toNat := by omega
  -- `endbr64`, `sub rsp, 40`, `mov rax, fs:[40]`, `mov [rsp + 24], rax`, `xor eax, eax`
  refine c.s_endbr hK hA hin (by omega) (by rw [addr_add_zero]; exact hrip) (sha_0 _) ?_
  rintro Y1 t1 hK1 hA1 ⟨hr1, hg1⟩
  refine c.s_sub_ri64 hK1 hA1 hin (by omega) hr1 (sha_4 _) ?_
  rintro Y2 t2 hK2 hA2 ⟨hr2, hg2⟩
  have hsp2 : Y2.cpu.gpr.rsp = Addr.add p 32 := by
    rw [hg2, hg1, set_r4, get_r4, hsp]; exact add_sub_lit p (by omega)
  have hc2 : eaF Y2 40 = cn := by rw [← hcd]; simp only [eaF, hK2.seg]; rfl
  refine c.s_mov_fs hK2 hA2 hin (by omega) hr2 (sha_8 _) (fun i hi => by rw [hc2]; exact hcn i hi) ?_
  rw [hc2]
  rintro Y3 t3 hK3 hA3 ⟨hr3, hg3⟩
  generalize hcv : ofBytesLE 64 ((byteAddrs cn 8).map V) = cv at hg3
  have hsp3 : Y3.cpu.gpr.rsp = Addr.add p 32 := by simp [hg3, hsp2]
  have e3 : eaD Y3 4 24 = Addr.add p 56 := by simp only [eaD, get_r4, hsp3]; exact addr_add_add p 32 24
  refine c.s_mov_mr hK3 hA3 hin (by omega) hr3 (Or.inr rfl) (sha_17 _) (fun i hi => by
    rw [e3, addr_add_add]; exact hws _ (by simp at hi; omega)) ?_
  rw [e3, show rv Y3 64 0 = cv by simp [rv, hg3]]
  rintro Y4 t4 hK4 hA4 ⟨hr4, hg4⟩
  generalize hV1 : Vst V (Addr.add p 56) (toBytesLE cv (64 / 8)) = V1 at hA4
  refine c.s_xor_rr32 hK4 hA4 hin (by omega) hr4 (sha_22 _) ?_
  rintro Y5 t5 hK5 hA5 ⟨hr5, hg5⟩
  have hsp5 : Y5.cpu.gpr.rsp = Addr.add p 32 := by simp [hg5, hg4, hsp3]
  have hsv5 : Saved X Y5 := by simp [Saved, hg5, hg4, hg3, hg2, hg1]
  -- the canary check and the return, from both paths
  have tail : ∀ (V' : Addr → Byte) Y t', (∀ x, (∀ i < 56, x ≠ Addr.add p i) → V' x = V1 x) →
      KeptW (ws k W s₀) s₀ Y → Agree (fp k W R pre post L s₀) Y.proc.mm.mem V' →
      Y.cpu.rip = (0x4243e0 : Addr).add 63 → Y.cpu.gpr.rsp = Addr.add p 32 → Saved X Y →
      (Y.cpu.gpr.rax.setWidth 32 ≠ 0 → prof.reports 7 0 (·.ebx) 29) →
      Go prof k W R pre post L s₀ ra o Y t' := by
    intro V' Y12 t12 hV' hK12 hA12 hr12 hsp12 hsv12 hax12
    have hfrV : ∀ x, (∀ i < 72, x ≠ Addr.add p i) → V' x = V x := by
      intro x hx
      rw [hV' x fun i hi => hx i (by omega), ← hV1]
      exact Vst_apart _ _ _ x fun i hi => by rw [addr_add_add]; exact hx _ (by simp at hi; omega)
    -- `mov rdx, [rsp + 24]`: the canary as stored
    have e12 : eaD Y12 4 24 = Addr.add p 56 := by simp only [eaD, get_r4, hsp12]; exact addr_add_add p 32 24
    refine c.s_mov_rm hK12 hA12 hin (by omega) hr12 (Or.inr rfl) (sha_63 _) (fun i hi => by
      rw [e12, addr_add_add]; exact c.hws _ (hws _ (by simp at hi; omega))) ?_
    have hcs : ofBytesLE 64 ((byteAddrs (Addr.add p 56) 8).map V') = cv := by
      rw [show (byteAddrs (Addr.add p 56) 8).map V' = (byteAddrs (Addr.add p 56) 8).map V1 from
        List.map_congr_left fun x hx => by
          obtain ⟨i, hi, rfl⟩ := mem_byteAddrs.1 hx
          rw [addr_add_add]
          exact hV' _ fun i' hi' => add_ne_same hfit (by omega) (by omega) (by omega), ← hV1]
      exact read_Vst_self (by rfl) _ (by rw [hpn 56 (by omega)]; omega)
    rw [e12, hcs]
    rintro Y13 t13 hK13 hA13 ⟨hr13, hg13⟩
    -- `xor rdx, fs:[40]`: 0
    have hc13 : eaF Y13 40 = cn := by rw [← hcd]; simp only [eaF, hK13.seg]; rfl
    refine c.s_xor_fs hK13 hA13 hin (by omega) hr13 (sha_68 _) (fun i hi => by rw [hc13]; exact hcn i hi) ?_
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
    refine c.s_jcc hK14 hA14 hin (by omega) hr14 (sha_77 _) (tgt := 84) rfl (by omega)
      (fun h => by simp [Rflags.cond, hzf] at h) fun _ => ?_
    rintro Y15 t15 hK15 hA15 ⟨hr15, hg15⟩
    -- `add rsp, 40`, `ret`
    refine c.s_add_ri64 hK15 hA15 hin (by omega) hr15 (sha_79 _) ?_
    rintro Y16 t16 hK16 hA16 ⟨hr16, hg16⟩
    have hsp16 : Y16.cpu.gpr.rsp = X.cpu.gpr.rsp := by
      simp only [hg16, hg15, hg14, hg13, set_r4, get_r4, set_r2]
      rw [hsp12, hsp]; exact addr_add_add p 32 40
    refine c.s_ret hK16 hA16 hin (by omega) hr16 (sha_83 _) (fun i hi => by rw [hsp16]; exact hrd i hi) hin₂ h₂
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
  -- `call z7_x86_cpuid_GetMaxFunc`
  refine c.s_call hK5 hA5 hin (by omega) hr5 (sha_24 _) hinM (by rw [maxf_length]; omega) (by decide)
    (fun i hi => by rw [hsp5, add_sub8 p (m := 24) rfl, addr_add_add]; exact hws _ (by omega)) ?_
  rw [hsp5, add_sub8 p (m := 24) rfl]
  rintro Y6 t6 hK6 hA6 ⟨hr6, hg6⟩
  have hsp6 : Y6.cpu.gpr.rsp = Addr.add p 24 := by rw [hg6, set_4]
  have hs24 : Y6.cpu.gpr.rsp - BitVec.ofNat 64 24 = p := by
    rw [hsp6, add_sub_lit p (Nat.le_refl 24), Nat.sub_self, addr_add_zero]
  refine sub_maxf c hK6 hA6 hinM hr6 (fun i hi => by rw [hs24]; exact hws i (by omega))
    (fun i hi => by rw [hsp6, addr_add_add]; exact c.hws _ (hws _ (by omega)))
    (by rw [← hcd] at hcn; exact hcn) (by rw [hsp6, hpn 24 (by omega)]; omega)
    (by rw [hsp6, hpn 24 (by omega)]; omega) (by rw [← hcd] at hcf; exact hcf)
    (by rw [hsp6, hpn 24 (by omega), ← hcd] at *; omega) hin (j₂ := 29) (by omega)
    (by rw [hsp6]; exact read_Vst_self (by rfl) _ (by rw [hpn 24 (by omega)]; omega)) ?_
  intro V3 hfr3 Y7 t7 hK7 hA7 ⟨hr7, hsp7, hsv7⟩
  rw [hs24] at hfr3
  rw [hsp6, add_add8] at hsp7
  have hV3 : ∀ x, (∀ i < 56, x ≠ Addr.add p i) → V3 x = V1 x := by
    intro x hx
    rw [hfr3 x fun i hi => hx i (by omega)]
    exact Vst_apart _ _ _ x fun i hi => by rw [addr_add_add]; exact hx _ (by simp at hi; omega)
  have hsv7' : Saved X Y7 := Saved.trans hsv5 (Saved.trans (by simp [Saved, hg6]) hsv7)
  -- `mov r8d, eax`, `xor eax, eax`, `cmp r8d, 6`, `jbe`
  refine c.s_mov_rr32 hK7 hA7 hin (by omega) hr7 (sha_29 _) ?_
  rintro Y8 t8 hK8 hA8 ⟨hr8, hg8⟩
  refine c.s_xor_rr32 hK8 hA8 hin (by omega) hr8 (sha_32 _) ?_
  rintro Y9 t9 hK9 hA9 ⟨hr9, hg9⟩
  refine c.s_cmp_ri32 hK9 hA9 hin (by omega) hr9 (sha_34 _) ?_
  rintro Y10 t10 hK10 hA10 ⟨hr10, hg10, -⟩
  have hsp10 : Y10.cpu.gpr.rsp = Addr.add p 32 := by simp [hg10, hg9, hg8, hsp7]
  have hsv10 : Saved X Y10 := hsv7'.trans (by simp [Saved, hg10, hg9, hg8])
  refine c.s_jcc hK10 hA10 hin (by omega) hr10 (sha_38 _) (tgt := 63) rfl (by omega) (fun _ => ?_) fun _ => ?_
  · -- leaf 7 not there: 0
    rintro Y11 t11 hK11 hA11 ⟨hr11, hg11⟩
    exact tail V3 Y11 t11 hV3 hK11 hA11 hr11 (by rw [hg11, hsp10]) (by rw [Saved, hg11]; exact hsv10)
      fun h => absurd (by simp [hg11, hg10, hg9]) h
  -- `mov rdi, rsp`, `mov esi, 7`, `call z7_x86_cpuid`
  rintro Y11 t11 hK11 hA11 ⟨hr11, hg11⟩
  refine c.s_mov_rr64 hK11 hA11 hin (by omega) hr11 (sha_40 _) ?_
  rintro Y12 t12 hK12 hA12 ⟨hr12, hg12⟩
  refine c.s_mov_ri32 hK12 hA12 hin (by omega) hr12 (sha_43 _) ?_
  rintro Y13 t13 hK13 hA13 ⟨hr13, hg13⟩
  have hsp13 : Y13.cpu.gpr.rsp = Addr.add p 32 := by simp [hg13, hg12, hg11, hsp10]
  refine c.s_call hK13 hA13 hin (by omega) hr13 (sha_48 _) hinC (by rw [cpuid_length]; omega) (by decide)
    (fun i hi => by rw [hsp13, add_sub8 p (m := 24) rfl, addr_add_add]; exact hws _ (by omega)) ?_
  rw [hsp13, add_sub8 p (m := 24) rfl]
  rintro Y14 t14 hK14 hA14 ⟨hr14, hg14⟩
  have hsp14 : Y14.cpu.gpr.rsp = Addr.add p 24 := by rw [hg14, set_4]
  have hdi14 : Y14.cpu.gpr.rdi = Addr.add p 32 := by simp [hg14, hg13, hg12, hg11, hsp10]
  have hsi14 : Y14.cpu.gpr.rsi.setWidth 32 = 7 := by simp [hg14, hg13]
  refine sub_cpuid c hK14 hA14 hinC hr14 (fun i hi => by
      rw [hsp14, add_sub8 p (m := 16) rfl, addr_add_add]; exact hws _ (by omega))
    (fun i hi => by rw [hdi14, addr_add_add]; exact hws _ (by omega))
    (fun i hi => by rw [hsp14, addr_add_add]; exact c.hws _ (hws _ (by omega)))
    (by rw [hsp14, hpn 24 (by omega)]; omega) (by rw [hsp14, hdi14, hpn 24 (by omega), hpn 32 (by omega)]; omega)
    (by rw [hdi14, hpn 32 (by omega)]; omega) hin (j₂ := 53) (by omega)
    (by rw [hsp14]; exact read_Vst_self (by rfl) _ (by rw [hpn 24 (by omega)]; omega)) ?_
  intro V5 hfr5 ⟨cpu, hcpu, hrep⟩ Y15 t15 hK15 hA15 ⟨hr15, hsp15, hsv15⟩
  rw [hsi14, hdi14] at hrep
  rw [hsp14, add_add8] at hsp15
  rw [hsp14, add_sub8 p (m := 16) rfl, hdi14] at hfr5
  have hV5 : ∀ x, (∀ i < 56, x ≠ Addr.add p i) → V5 x = V1 x := by
    intro x hx
    rw [hfr5 x (fun i hi => by rw [addr_add_add]; exact hx _ (by omega)) (fun i hi => by
      rw [addr_add_add]; exact hx _ (by omega))]
    rw [Vst_apart _ _ _ x fun i hi => by rw [addr_add_add]; exact hx _ (by simp at hi; omega)]
    exact hV3 x hx
  have hsv15' : Saved X Y15 := hsv10.trans (Saved.trans (by simp [Saved, hg14, hg13, hg12, hg11]) hsv15)
  -- `mov eax, [rsp + 4]`, `shr eax, 29`, `and eax, 1`
  have e15 : eaD Y15 4 4 = Addr.add (Addr.add p 32) 4 := by simp only [eaD, get_r4, hsp15]; rfl
  refine c.s_mov_rm hK15 hA15 hin (by omega) hr15 (Or.inl rfl) (sha_53 _) (fun i hi => by
    rw [e15, addr_add_add, addr_add_add]; exact c.hws _ (hws _ (by simp at hi; omega))) ?_
  rw [e15, hrep.2.1]
  rintro Y16 t16 hK16 hA16 ⟨hr16, hg16⟩
  refine c.s_shr_ri32 hK16 hA16 hin (by omega) hr16 (by decide) (sha_57 _) ?_
  rintro Y17 t17 hK17 hA17 ⟨hr17, hg17⟩
  refine c.s_and_ri32 hK17 hA17 hin (by omega) hr17 (sha_60 _) ?_
  rintro Y18 t18 hK18 hA18 ⟨hr18, hg18, -⟩
  refine tail V5 Y18 t18 hV5 hK18 hA18 hr18 (by simp [hg18, hg17, hg16, hsp15])
    (by refine hsv15'.trans ?_; simp [Saved, hg18, hg17, hg16]) fun h0 => ?_
  have hax : Y18.cpu.gpr.rax.setWidth 32 = (prof.cpuid cpu 7 0).ebx >>> 29 &&& 1#32 := by
    simp only [hg18, hg17, hg16, rv, set_r0, get_r0, sw_sw]
  rw [hax] at h0
  exact ⟨cpu, hcpu, bit_of _ h0⟩

/-! ## `Sha1Prepare`, `Sha256Prepare` -/

/-- The code of `Sha1Prepare` and `Sha256Prepare`, at `e`: the portable `sw` and the SHA-NI `hw` variant, stored into
`g1` (`g_SHA*_FUNC_UPDATE_BLOCKS`) and `g2` (`..._HW`). -/
structure ShaPrep (code : List Byte) (e sw hw g1 g2 : Addr) : Prop where
  len : code.length = 69
  g1f : g1.toNat + 8 ≤ 2 ^ 64
  g2f : g2.toNat + 8 ≤ 2 ^ 64
  gap : g1.toNat + 8 ≤ g2.toNat ∨ g2.toNat + 8 ≤ g1.toNat
  d0 : ∀ feat, Dec feat code 0 (FV7z.mk .endbr64 32 [] 4)
  d4 : ∀ feat, Dec feat code 4 (FV7z.mk .sub 64 [gr 64 4, .imm 64 8] 4)
  d8 : ∃ rel, (∀ feat, Dec feat code 8 (FV7z.mk .call 64 [.rel rel] 5)) ∧
    e.add (8 + 5) + BitVec.ofNat 64 rel = 0x4243e0
  d13 : ∀ feat, Dec feat code 13 (FV7z.mk .test 32 [gr 32 0, gr 32 0] 2)
  d15 : ∀ feat, Dec feat code 15 (FV7z.mk (.jcc 5) 64 [.rel 31] 2)
  d17 : ∃ imm, (∀ feat, Dec feat code 17 (FV7z.mk .mov 64 [gr 64 2, .imm 64 imm] 7)) ∧ BitVec.ofNat 64 imm = sw
  d24 : ∀ feat, Dec feat code 24 (FV7z.mk .xor 32 [gr 32 0, gr 32 0] 2)
  d26 : ∃ d, (∀ feat, Dec feat code 26 (FV7z.mk .mov 64 [.mem (mrip d 64), gr 64 2] 7)) ∧
    e.add (26 + 7) + BitVec.ofNat 64 d = g1
  d33 : ∃ d, (∀ feat, Dec feat code 33 (FV7z.mk .mov 64 [.mem (mrip d 64), gr 64 0] 7)) ∧
    e.add (33 + 7) + BitVec.ofNat 64 d = g2
  d40 : ∀ feat, Dec feat code 40 (FV7z.mk .add 64 [gr 64 4, .imm 64 8] 4)
  d44 : ∀ feat, Dec feat code 44 (FV7z.mk .ret 64 [] 1)
  d48 : ∃ rel, (∀ feat, Dec feat code 48 (FV7z.mk .call 64 [.rel rel] 5)) ∧
    e.add (48 + 5) + BitVec.ofNat 64 rel = 0x424340
  d53 : ∀ feat, Dec feat code 53 (FV7z.mk .test 32 [gr 32 0, gr 32 0] 2)
  d55 : ∀ feat, Dec feat code 55 (FV7z.mk (.jcc 4) 64 [.rel 18446744073709551576] 2)
  d57 : ∃ imm, (∀ feat, Dec feat code 57 (FV7z.mk .mov 64 [gr 64 0, .imm 64 imm] 7)) ∧ BitVec.ofNat 64 imm = hw
  d64 : ∀ feat, Dec feat code 64 (FV7z.mk .mov 64 [gr 64 2, gr 64 0] 3)
  d67 : ∀ feat, Dec feat code 67 (FV7z.mk .jmp 64 [.rel 18446744073709551573] 2)

theorem sha1p_shape : ShaPrep sha1p 0x43a740 0x439b70 0x43a790 0x792150 0x7967a8 where
  len := sha1p_length
  g1f := by decide
  g2f := by decide
  gap := by decide
  d0 := sha1p_0
  d4 := sha1p_4
  d8 := ⟨_, sha1p_8, by decide⟩
  d13 := sha1p_13
  d15 := sha1p_15
  d17 := ⟨_, sha1p_17, by decide⟩
  d24 := sha1p_24
  d26 := ⟨_, sha1p_26, by decide⟩
  d33 := ⟨_, sha1p_33, by decide⟩
  d40 := sha1p_40
  d44 := sha1p_44
  d48 := ⟨_, sha1p_48, by decide⟩
  d53 := sha1p_53
  d55 := sha1p_55
  d57 := ⟨_, sha1p_57, by decide⟩
  d64 := sha1p_64
  d67 := sha1p_67

theorem sha256p_shape : ShaPrep sha256p 0x43b3e0 0x43a9f0 0x43b430 0x792160 0x7967b0 where
  len := sha256p_length
  g1f := by decide
  g2f := by decide
  gap := by decide
  d0 := sha256p_0
  d4 := sha256p_4
  d8 := ⟨_, sha256p_8, by decide⟩
  d13 := sha256p_13
  d15 := sha256p_15
  d17 := ⟨_, sha256p_17, by decide⟩
  d24 := sha256p_24
  d26 := ⟨_, sha256p_26, by decide⟩
  d33 := ⟨_, sha256p_33, by decide⟩
  d40 := sha256p_40
  d44 := sha256p_44
  d48 := ⟨_, sha256p_48, by decide⟩
  d53 := sha256p_53
  d55 := sha256p_55
  d57 := ⟨_, sha256p_57, by decide⟩
  d64 := sha256p_64
  d67 := sha256p_67

/-- The two pointers. -/
def shW (g1 g2 : Addr) (_ : State) : List Rgn := [⟨g1, 8⟩, ⟨g2, 8⟩]

/-- The canary apart from the stack it uses, the pointers apart from the return address's slot. -/
def shPre (g1 g2 : Addr) (s : State) : Prop :=
  ((Addr.add s.cpu.seg.fsBase 40).toNat + 8 ≤ s.cpu.gpr.rsp.toNat - 88 ∨
    s.cpu.gpr.rsp.toNat ≤ (Addr.add s.cpu.seg.fsBase 40).toNat) ∧
  (g1.toNat + 8 ≤ s.cpu.gpr.rsp.toNat ∨ s.cpu.gpr.rsp.toNat + 8 ≤ g1.toNat) ∧
  (g2.toNat + 8 ≤ s.cpu.gpr.rsp.toNat ∨ s.cpu.gpr.rsp.toNat + 8 ≤ g2.toNat)

/-- A pointer in `Y`. -/
def ptrAt (g : Addr) (Y : State) : BitVec 64 := ofBytesLE 64 (readBytes Y.proc.mm.mem g 8)

/-- At the return: the portable variant and `NULL`, or the SHA-NI variant twice on a processor with SHA and SSSE3. -/
def shPost (prof : Profile) (sw hw g1 g2 : Addr) (_ Y : State) : Prop :=
  (ptrAt g1 Y = sw ∧ ptrAt g2 Y = 0) ∨
    (ptrAt g1 Y = hw ∧ ptrAt g2 Y = hw ∧ prof.feat.sha = true ∧ prof.feat.ssse3 = true)

/-- The contract: a stack of 88 bytes (its own 8, `CPU_IsSupported_SHA`'s 72 with what it calls, a return address),
the pointers written, the canary read. -/
abbrev shC (prof : Profile) (sw hw g1 g2 : Addr) : Contract :=
  fn 88 (shW g1 g2) lzR (shPre g1 g2) (shPost prof sw hw g1 g2)

theorem shPost_of {sw hw g1 g2 : Addr} {Y : State} {v1 v2 : BitVec 64}
    (h1 : ofBytesLE 64 (readBytes Y.proc.mm.mem g1 8) = v1) (h2 : ofBytesLE 64 (readBytes Y.proc.mm.mem g2 8) = v2)
    (h : (v1 = sw ∧ v2 = 0) ∨ (v1 = hw ∧ v2 = hw ∧ prof.feat.sha = true ∧ prof.feat.ssse3 = true)) :
    shPost prof sw hw g1 g2 s₀ Y := by
  unfold shPost ptrAt; rw [h1, h2]; exact h

theorem shRun (hpc : prof.Consistent) {code : List Byte} {e sw hw g1 g2 : Addr} (sh : ShaPrep code e sw hw g1 g2)
    (c : Call prof 88 (shW g1 g2) lzR (shPre g1 g2) (shPost prof sw hw g1 g2) e L s₀ ra o)
    (hin : CodeIn L e code) (hinH : CodeIn L 0x4243e0 sha) (hinS : CodeIn L 0x424340 ssse3)
    (hinM : CodeIn L 0x4242b0 maxf) (hinC : CodeIn L 0x424290 cpuid) (t : Nat) :
    Go prof 88 (shW g1 g2) lzR (shPre g1 g2) (shPost prof sw hw g1 g2) L s₀ ra o s₀ t := by
  have hl : code.length = 69 := sh.len
  have hK0 : KeptW (ws 88 (shW g1 g2) s₀) s₀ s₀ := KeptW.refl _ _
  have hA0 : Agree (fp 88 (shW g1 g2) lzR (shPre g1 g2) (shPost prof sw hw g1 g2) L s₀) s₀.proc.mm.mem
      (fun a => s₀.proc.mm.mem.readByte a) := fun _ _ => rfl
  obtain ⟨hpt0, hsf0⟩ := Call.frame_arith c.frame_fits
  obtain ⟨hca0, -⟩ := c.call.pre
  generalize hpd : s₀.cpu.gpr.rsp - BitVec.ofNat 64 88 = p at hpt0
  have hsp : s₀.cpu.gpr.rsp = Addr.add p 88 := by rw [← hpd]; exact sub_add_self _ _
  have hfit : p.toNat + 96 ≤ 2 ^ 64 := by omega
  have hpn : ∀ d, d < 96 → (Addr.add p d).toNat = p.toNat + d := fun d hd => toNat_addn hd hfit
  have hws : ∀ i < 88, Foot (ws 88 (shW g1 g2) s₀) (Addr.add p i) := fun i hi =>
    ⟨below s₀ 88, by simp, by simp only [below, hpd]; exact mem_add_of_fits hi (by omega)⟩
  -- the canary
  have hcr : (⟨Addr.add s₀.cpu.seg.fsBase 40, 8⟩ : Rgn) ∈
      (fp 88 (shW g1 g2) lzR (shPre g1 g2) (shPost prof sw hw g1 g2) L s₀).data := by
    simp [Footprint.data, Contract.footprint, fn, lzR]
  have hcf : (Addr.add s₀.cpu.seg.fsBase 40).toNat + 8 ≤ 2 ^ 64 :=
    c.call.foot.fits _ (List.mem_append_left _ hcr)
  have hcn : ∀ i < 8, Foot (fp 88 (shW g1 g2) lzR (shPre g1 g2) (shPost prof sw hw g1 g2) L s₀).data
      (Addr.add (Addr.add s₀.cpu.seg.fsBase 40) i) := fun i hi => ⟨_, hcr, mem_add_of_fits hi hcf⟩
  -- the pointers
  have hg1 : ∀ i < 8, Foot (ws 88 (shW g1 g2) s₀) (g1.add i) := fun i hi =>
    ⟨⟨g1, 8⟩, by simp [shW], mem_add_of_fits hi sh.g1f⟩
  have hg2 : ∀ i < 8, Foot (ws 88 (shW g1 g2) s₀) (g2.add i) := fun i hi =>
    ⟨⟨g2, 8⟩, by simp [shW], mem_add_of_fits hi sh.g2f⟩
  -- the stores and the return, from both paths
  have fin : ∀ (V' : Addr → Byte) Y t', KeptW (ws 88 (shW g1 g2) s₀) s₀ Y →
      Agree (fp 88 (shW g1 g2) lzR (shPre g1 g2) (shPost prof sw hw g1 g2) L s₀) Y.proc.mm.mem V' →
      Y.cpu.rip = e.add 26 → Y.cpu.gpr.rsp = Addr.add p 80 → Saved s₀ Y →
      ((Y.cpu.gpr.rdx = sw ∧ Y.cpu.gpr.rax = 0) ∨
        (Y.cpu.gpr.rdx = hw ∧ Y.cpu.gpr.rax = hw ∧ prof.feat.sha = true ∧ prof.feat.ssse3 = true)) →
      Go prof 88 (shW g1 g2) lzR (shPre g1 g2) (shPost prof sw hw g1 g2) L s₀ ra o Y t' := by
    intro V' Y1 t1 hK1 hA1 hr1 hsp1 hsv1 hv
    obtain ⟨d1, hd1, hgd1⟩ := sh.d26
    refine c.s_mov_rip_r64 hK1 hA1 hin (by omega) hr1 (hd1 _) hgd1 hg1 ?_
    rintro Y2 t2 hK2 hA2 ⟨hr2, hgr2⟩
    obtain ⟨d2, hd2, hgd2⟩ := sh.d33
    refine c.s_mov_rip_r64 hK2 hA2 hin (by omega) hr2 (hd2 _) hgd2 hg2 ?_
    rintro Y3 t3 hK3 hA3 ⟨hr3, hgr3⟩
    refine c.s_add_ri64 hK3 hA3 hin (by omega) hr3 (sh.d40 _) ?_
    rintro Y4 t4 hK4 hA4 ⟨hr4, hgr4⟩
    refine c.ret hK4 (callee_of (hsv1.trans ?_) ?_) hin (by omega) hr4 (sh.d44 _) fun M hM => ?_
    · simp [Saved, hgr4, hgr3, hgr2]
    · simp only [hgr4, hgr3, hgr2, set_r4, get_r4]
      rw [hsp1]; exact (add_add8 p _).trans (by rw [hsp])
    · have hAM := c.agreeK hK4 hA4 hM
      have r1 : ofBytesLE 64 (readBytes M g1 8) = Y1.cpu.gpr.rdx := by
        rw [hAM.read (fun i hi => c.hws _ (hg1 i hi)),
          map_Vst_apart (by rw [toBytesLE_length]; exact sh.g2f) sh.g1f (by rw [toBytesLE_length]; exact sh.gap.symm)]
        exact read_Vst_self (by rfl) _ sh.g1f
      have r2 : ofBytesLE 64 (readBytes M g2 8) = Y1.cpu.gpr.rax := by
        rw [hAM.read (fun i hi => c.hws _ (hg2 i hi))]
        refine (read_Vst_self (by rfl) _ sh.g2f).trans ?_
        rw [hgr2]; rfl
      exact shPost_of r1 r2 hv
  -- the portable variant, from offset 17
  have swp : ∀ (V' : Addr → Byte) Y t', KeptW (ws 88 (shW g1 g2) s₀) s₀ Y →
      Agree (fp 88 (shW g1 g2) lzR (shPre g1 g2) (shPost prof sw hw g1 g2) L s₀) Y.proc.mm.mem V' →
      Y.cpu.rip = e.add 17 → Y.cpu.gpr.rsp = Addr.add p 80 → Saved s₀ Y →
      Go prof 88 (shW g1 g2) lzR (shPre g1 g2) (shPost prof sw hw g1 g2) L s₀ ra o Y t' := by
    intro V' Y1 t1 hK1 hA1 hr1 hsp1 hsv1
    obtain ⟨imm, hd, hv⟩ := sh.d17
    refine c.s_mov_ri64 hK1 hA1 hin (by omega) hr1 (hd _) ?_
    rintro Y2 t2 hK2 hA2 ⟨hr2, hgr2⟩
    refine c.s_xor_rr32 hK2 hA2 hin (by omega) hr2 (sh.d24 _) ?_
    rintro Y3 t3 hK3 hA3 ⟨hr3, hgr3⟩
    exact fin V' Y3 t3 hK3 hA3 hr3 (by simp [hgr3, hgr2, hsp1]) (hsv1.trans (by simp [Saved, hgr3, hgr2]))
      (Or.inl ⟨by simp [hgr3, hgr2, hv], by simp [hgr3, hgr2]⟩)
  -- `endbr64`, `sub rsp, 8`, `call CPU_IsSupported_SHA`
  refine c.s_endbr hK0 hA0 hin (by omega) (by rw [addr_add_zero]; exact c.call.shape.1) (sh.d0 _) ?_
  rintro Y1 t1 hK1 hA1 ⟨hr1, hg1'⟩
  refine c.s_sub_ri64 hK1 hA1 hin (by omega) hr1 (sh.d4 _) ?_
  rintro Y2 t2 hK2 hA2 ⟨hr2, hg2'⟩
  have hsp2 : Y2.cpu.gpr.rsp = Addr.add p 80 := by
    rw [hg2', hg1', set_r4, get_r4, hsp]; exact add_sub_lit p (by omega)
  obtain ⟨rel, hd8, hc8⟩ := sh.d8
  refine c.s_call hK2 hA2 hin (by omega) hr2 (hd8 _) hinH (by rw [sha_length]; omega) hc8
    (fun i hi => by rw [hsp2, add_sub8 p (m := 72) rfl, addr_add_add]; exact hws _ (by omega)) ?_
  rw [hsp2, add_sub8 p (m := 72) rfl]
  rintro Y3 t3 hK3 hA3 ⟨hr3, hg3⟩
  have hsp3 : Y3.cpu.gpr.rsp = Addr.add p 72 := by rw [hg3, set_4]
  have hsv3 : Saved s₀ Y3 := by simp [Saved, hg3, hg2', hg1']
  refine sub_sha c hK3 hA3 hinH hinM hinC hr3 (fun i hi => by
      rw [hsp3, add_sub_lit p (n := 72) (d := 72) (by omega), addr_add_add]; exact hws _ (by omega))
    (fun i hi => by rw [hsp3, addr_add_add]; exact c.hws _ (hws _ (by omega)))
    hcn (by rw [hsp3, hpn 72 (by omega)]; omega) (by rw [hsp3, hpn 72 (by omega)]; omega) hcf
    (by rw [hsp3, hpn 72 (by omega)]; omega) hin (j₂ := 13) (by omega)
    (by rw [hsp3]; exact read_Vst_self (by rfl) _ (by rw [hpn 72 (by omega)]; omega)) ?_
  intro V4 _ Y4 t4 hK4 hA4 ⟨hr4, hsp4, hsv4, hax4⟩
  rw [hsp3, add_add8] at hsp4
  -- `test eax, eax`, `jne`
  refine c.s_test_rr32 hK4 hA4 hin (by omega) hr4 (sh.d13 _) ?_
  rintro Y5 t5 hK5 hA5 ⟨hr5, hg5, hz5⟩
  have hsv5 : Saved s₀ Y5 := (hsv3.trans hsv4).trans (by simp [Saved, hg5])
  have hsp5 : Y5.cpu.gpr.rsp = Addr.add p 80 := by rw [hg5, hsp4]
  refine c.s_jcc hK5 hA5 hin (by omega) hr5 (sh.d15 _) (tgt := 48) rfl (by omega) (fun hc => ?_) fun _ => ?_
  · -- SHA: `call CPU_IsSupported_SSSE3`
    have hsha : prof.reports 7 0 (·.ebx) 29 := hax4 fun h0 => by
      simp only [Rflags.cond, hz5, Bool.not_eq_true'] at hc
      simp [rv, h0] at hc
    rintro Y6 t6 hK6 hA6 ⟨hr6, hg6⟩
    have hsp6 : Y6.cpu.gpr.rsp = Addr.add p 80 := by rw [hg6, hsp5]
    obtain ⟨rel2, hd48, hc48⟩ := sh.d48
    refine c.s_call hK6 hA6 hin (by omega) hr6 (hd48 _) hinS (by rw [ssse3_length]; omega) hc48
      (fun i hi => by rw [hsp6, add_sub8 p (m := 72) rfl, addr_add_add]; exact hws _ (by omega)) ?_
    rw [hsp6, add_sub8 p (m := 72) rfl]
    rintro Y7 t7 hK7 hA7 ⟨hr7, hg7⟩
    have hsp7 : Y7.cpu.gpr.rsp = Addr.add p 72 := by rw [hg7, set_4]
    have hsv7 : Saved s₀ Y7 := hsv5.trans (by simp [Saved, hg7, hg6])
    refine sub_bit c ssse3_shape hK7 hA7 hinS hinC hr7 (fun i hi => by
        rw [hsp7, add_sub_lit p (n := 72) (d := 56) (by omega), addr_add_add]; exact hws _ (by omega))
      (fun i hi => by rw [hsp7, addr_add_add]; exact c.hws _ (hws _ (by omega)))
      hcn (by rw [hsp7, hpn 72 (by omega)]; omega) (by rw [hsp7, hpn 72 (by omega)]; omega) hcf
      (by rw [hsp7, hpn 72 (by omega)]; omega) hin (j₂ := 53) (by omega)
      (by rw [hsp7]; exact read_Vst_self (by rfl) _ (by rw [hpn 72 (by omega)]; omega)) ?_
    intro V8 _ Y8 t8 hK8 hA8 ⟨hr8, hsp8, hsv8, hax8⟩
    rw [hsp7, add_add8] at hsp8
    -- `test eax, eax`, `je`
    refine c.s_test_rr32 hK8 hA8 hin (by omega) hr8 (sh.d53 _) ?_
    rintro Y9 t9 hK9 hA9 ⟨hr9, hg9, hz9⟩
    have hsv9 : Saved s₀ Y9 := (hsv7.trans hsv8).trans (by simp [Saved, hg9])
    have hsp9 : Y9.cpu.gpr.rsp = Addr.add p 80 := by rw [hg9, hsp8]
    refine c.s_jcc hK9 hA9 hin (by omega) hr9 (sh.d55 _) (tgt := 17) rfl (by omega) (fun _ => ?_) fun hc9 => ?_
    · rintro Y10 t10 hK10 hA10 ⟨hr10, hg10⟩
      exact swp _ Y10 t10 hK10 hA10 hr10 (by rw [hg10, hsp9]) (by rw [Saved, hg10]; exact hsv9)
    · -- SSSE3: `mov rax, hw`, `mov rdx, rax`, `jmp`
      have hss : prof.reports 1 0 (·.ecx) 9 := hax8 fun h0 => by
        simp only [Rflags.cond, hz9] at hc9
        simp [rv, h0] at hc9
      rintro Y10 t10 hK10 hA10 ⟨hr10, hg10⟩
      obtain ⟨imm, hd57, hv57⟩ := sh.d57
      refine c.s_mov_ri64 hK10 hA10 hin (by omega) hr10 (hd57 _) ?_
      rintro Y11 t11 hK11 hA11 ⟨hr11, hg11⟩
      refine c.s_mov_rr64 hK11 hA11 hin (by omega) hr11 (sh.d64 _) ?_
      rintro Y12 t12 hK12 hA12 ⟨hr12, hg12⟩
      refine c.s_jmp hK12 hA12 hin (by omega) hr12 (sh.d67 _) (tgt := 26) rfl (by omega) ?_
      rintro Y13 t13 hK13 hA13 ⟨hr13, hg13⟩
      exact fin _ Y13 t13 hK13 hA13 hr13 (by simp [hg13, hg12, hg11, hg10, hsp9])
        (hsv9.trans (by simp [Saved, hg13, hg12, hg11, hg10]))
        (Or.inr ⟨by simp [hg13, hg12, hg11, hv57], by simp [hg13, hg12, hg11, hv57], hpc.sha hsha, hpc.ssse3 hss⟩)
  · -- no SHA
    rintro Y6 t6 hK6 hA6 ⟨hr6, hg6⟩
    exact swp _ Y6 t6 hK6 hA6 hr6 (by rw [hg6, hsp5]) (by rw [Saved, hg6]; exact hsv5)

/-- Such a function, at `e`, with its callees' code: on a consistent profile, every call returns, with the pointers
the portable variant and `NULL`, or the SHA-NI variant on a processor with SHA and SSSE3. -/
theorem shaPrep_holds (prof : Profile) (hpc : prof.Consistent) {code : List Byte} {e sw hw g1 g2 : Addr}
    (sh : ShaPrep code e sw hw g1 g2) {L : List (Addr × List Byte)}
    (hin : CodeIn L e code) (hinH : CodeIn L 0x4243e0 sha) (hinS : CodeIn L 0x424340 ssse3)
    (hinM : CodeIn L 0x4242b0 maxf) (hinC : CodeIn L 0x424290 cpuid) :
    ImplementsCall prof e L (shC prof sw hw g1 g2) := by
  intro s₀ ra hcall
  have hfr := Call.frame_arith (k := 88) (s := s₀)
    (hcall.foot.fits (frame s₀ 88) (by simp [Footprint.data, Contract.footprint, fn]))
  have hslot : ∀ i < 8, ¬ Foot (shW g1 g2 s₀) (Addr.add s₀.cpu.gpr.rsp i) := by
    rintro i hi ⟨r, hr, hm⟩
    have h1 := hcall.pre.2.1
    have h2 := hcall.pre.2.2
    simp only [shW, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> simp only [Rgn.Mem, toNat_add_of_fits hi hfr.2] at hm <;> omega
  exact reachOrEndsIn_of_runsFrom fun o ho t =>
    shRun hpc sh (Call.of hcall ho hslot) hin hinH hinS hinM hinC t

/-- `Sha1Prepare`, at `0x43a740`: `g_SHA1_FUNC_UPDATE_BLOCKS` (`0x792150`) is `Sha1_UpdateBlocks` (`0x439b70`) and
`g_SHA1_FUNC_UPDATE_BLOCKS_HW` (`0x7967a8`) `NULL`, or both `Sha1_UpdateBlocks_HW` (`0x43a790`) on a processor with
SHA and SSSE3. -/
theorem sha1Prepare (prof : Profile) (hpc : prof.Consistent) {L : List (Addr × List Byte)}
    (hin : CodeIn L 0x43a740 sha1p) (hinH : CodeIn L 0x4243e0 sha) (hinS : CodeIn L 0x424340 ssse3)
    (hinM : CodeIn L 0x4242b0 maxf) (hinC : CodeIn L 0x424290 cpuid) :
    ImplementsCall prof 0x43a740 L (shC prof 0x439b70 0x43a790 0x792150 0x7967a8) :=
  shaPrep_holds prof hpc sha1p_shape hin hinH hinS hinM hinC

/-- `Sha256Prepare`, at `0x43b3e0`: `g_SHA256_FUNC_UPDATE_BLOCKS` (`0x792160`) is `Sha256_UpdateBlocks`
(`0x43a9f0`) and `g_SHA256_FUNC_UPDATE_BLOCKS_HW` (`0x7967b0`) `NULL`, or both `Sha256_UpdateBlocks_HW` (`0x43b430`)
on a processor with SHA and SSSE3. -/
theorem sha256Prepare (prof : Profile) (hpc : prof.Consistent) {L : List (Addr × List Byte)}
    (hin : CodeIn L 0x43b3e0 sha256p) (hinH : CodeIn L 0x4243e0 sha) (hinS : CodeIn L 0x424340 ssse3)
    (hinM : CodeIn L 0x4242b0 maxf) (hinC : CodeIn L 0x424290 cpuid) :
    ImplementsCall prof 0x43b3e0 L (shC prof 0x43a9f0 0x43b430 0x792160 0x7967b0) :=
  shaPrep_holds prof hpc sha256p_shape hin hinH hinS hinM hinC

end FV7z.Prepare
