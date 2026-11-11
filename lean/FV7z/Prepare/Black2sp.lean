import FV7z.Prepare.Sha
/-!
# `z7_Black2sp_Prepare` installs the vector BLAKE2sp code only on a processor with it (PLAN.md G2, 7-Zip)

`z7_Black2sp_Prepare` (`C/Blake2s.c`, `0x422a20`) sets four function pointers and a flag word:
`g_Z7_BLAKE2SP_FUNC_COMPRESS_Fast` (`0x792148`), `..._Single` (`0x792140`), `g_Z7_BLAKE2SP_FUNC_INIT_Init`
(`0x796798`), `..._Final` (`0x796790`), `g_z7_Blake2sp_SupportedFlags` (`0x796788`, 4 bytes). Without SSE4.1:
the portable `Blake2sp_Compress2` (`0x420280`) twice, `NULL`, `NULL`, 0. With SSE4.1 (`CPU_IsSupported_SSE41`):
the 128-bit `Fast` (`0x420dc0`), `Compress2_V128` (`0x420a80`), `Init` (`0x420820`), `Final` (`0x420970`), flags
`0x14`; and if also `CPU_IsSupported_AVX2()`, the 256-bit `Fast` (`0x421820`), `Init` (`0x4208e0`), `Final`
(`0x421700`), flags `0x1c`. The compiler chooses between the last two with `cmovne` and `cmp eax, 1; sbb; and; add`.
-/
namespace FV7z.Prepare
open ZellicX86 Decode FV7z.Leaf FV7z.Fn

/-- What it writes. -/
def b2W (_ : State) : List Rgn := [⟨0x792148, 8⟩, ⟨0x792140, 8⟩, ⟨0x796798, 8⟩, ⟨0x796790, 8⟩, ⟨0x796788, 4⟩]

/-- The canary apart from the stack it uses; the globals (all in `[0x792140, 0x7967a0)`) apart from the return
address's slot. -/
def b2Pre (s : State) : Prop :=
  ((Addr.add s.cpu.seg.fsBase 40).toNat + 8 ≤ s.cpu.gpr.rsp.toNat - 120 ∨
    s.cpu.gpr.rsp.toNat ≤ (Addr.add s.cpu.seg.fsBase 40).toNat) ∧
  (0x7967a0 ≤ s.cpu.gpr.rsp.toNat ∨ s.cpu.gpr.rsp.toNat + 8 ≤ 0x792140)

/-- The three outcomes: `Fast`, `Single`, `Init`, `Final`, flags. -/
def b2Vals (prof : Profile) (a b c d : BitVec 64) (f : BitVec 32) : Prop :=
  (a = 0x420280 ∧ b = 0x420280 ∧ c = 0 ∧ d = 0 ∧ f = 0) ∨
  (a = 0x420dc0 ∧ b = 0x420a80 ∧ c = 0x420820 ∧ d = 0x420970 ∧ f = 0x14 ∧ prof.feat.sse41 = true) ∨
  (a = 0x421820 ∧ b = 0x420a80 ∧ c = 0x4208e0 ∧ d = 0x421700 ∧ f = 0x1c ∧ prof.feat.sse41 = true ∧
    prof.feat.avx2 = true ∧ prof.feat.avx = true)

/-- At the return: the portable code, or the 128-bit code on a processor with SSE4.1, or the 256-bit code on one
with SSE4.1, AVX2 and AVX. -/
def b2Post (prof : Profile) (_ Y : State) : Prop :=
  b2Vals prof (ptrAt 0x792148 Y) (ptrAt 0x792140 Y) (ptrAt 0x796798 Y) (ptrAt 0x796790 Y)
    (ofBytesLE 32 (readBytes Y.proc.mm.mem 0x796788 4))

/-- The contract: a stack of 120 bytes (its own 8, `CPU_IsSupported_AVX2`'s 104 with what it calls, a return
address), the globals written, the canary read. -/
abbrev b2C (prof : Profile) : Contract := fn 120 b2W lzR b2Pre (b2Post prof)

theorem b2Post_of {prof : Profile} {s₀ Y : State} {a b c d : BitVec 64} {f : BitVec 32}
    (ha : ofBytesLE 64 (readBytes Y.proc.mm.mem 0x792148 8) = a)
    (hb : ofBytesLE 64 (readBytes Y.proc.mm.mem 0x792140 8) = b)
    (hc : ofBytesLE 64 (readBytes Y.proc.mm.mem 0x796798 8) = c)
    (hd : ofBytesLE 64 (readBytes Y.proc.mm.mem 0x796790 8) = d)
    (hf : ofBytesLE 32 (readBytes Y.proc.mm.mem 0x796788 4) = f) (h : b2Vals prof a b c d f) :
    b2Post prof s₀ Y := by
  unfold b2Post ptrAt; rw [ha, hb, hc, hd, hf]; exact h

/-- A store of `m` bytes at `a` leaves the `n` bytes at `b` apart from it. -/
theorem rd_apart {V : Addr → Byte} {a b : Addr} {m n w : Nat} (v : BitVec w) (ha : a.toNat + m ≤ 2 ^ 64)
    (hb : b.toNat + n ≤ 2 ^ 64) (h : a.toNat + m ≤ b.toNat ∨ b.toNat + n ≤ a.toNat) :
    (byteAddrs b n).map (Vst V a (toBytesLE v m)) = (byteAddrs b n).map V :=
  map_Vst_apart (by rw [toBytesLE_length]; exact ha) hb (by rw [toBytesLE_length]; exact h)

/-- `cmp eax, 1; sbb eax, eax; and eax, -8; add eax, 28`. -/
theorem b2_flags (r : BitVec 32) :
    ((r - r - (BitVec.ofBool (borrowSub r (BitVec.ofNat 32 1) false)).setWidth 32) &&& BitVec.ofNat 32 4294967288) +
      BitVec.ofNat 32 28 = if r = 0 then 0x14 else 0x1c := by
  by_cases h : r = 0
  · subst h; decide
  · have h' : r.toNat ≠ 0 := fun e => h (BitVec.eq_of_toNat_eq (by simp [e]))
    have hb : borrowSub r (BitVec.ofNat 32 1) false = false := by simp [borrowSub]; omega
    simp [hb]; exact h

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {ra : Addr} {o : Oracle}

theorem b2Run (hpc : prof.Consistent) (c : Call prof 120 b2W lzR b2Pre (b2Post prof) 0x422a20 L s₀ ra o)
    (hin : CodeIn L 0x422a20 b2s) (hinS : CodeIn L 0x424390 sse41) (hinA2 : CodeIn L 0x4244b0 avx2)
    (hinA : CodeIn L 0x424440 avx) (hinM : CodeIn L 0x4242b0 maxf) (hinC : CodeIn L 0x424290 cpuid) (t : Nat) :
    Go prof 120 b2W lzR b2Pre (b2Post prof) L s₀ ra o s₀ t := by
  have hl : b2s.length = 161 := b2s_length
  have hK0 : KeptW (ws 120 b2W s₀) s₀ s₀ := KeptW.refl _ _
  have hA0 : Agree (fp 120 b2W lzR b2Pre (b2Post prof) L s₀) s₀.proc.mm.mem
      (fun a => s₀.proc.mm.mem.readByte a) := fun _ _ => rfl
  obtain ⟨hpt0, hsf0⟩ := Call.frame_arith c.frame_fits
  obtain ⟨hca0, -⟩ := c.call.pre
  generalize hpd : s₀.cpu.gpr.rsp - BitVec.ofNat 64 120 = p at hpt0
  have hsp : s₀.cpu.gpr.rsp = Addr.add p 120 := by rw [← hpd]; exact sub_add_self _ _
  have hfit : p.toNat + 128 ≤ 2 ^ 64 := by omega
  have hpn : ∀ d, d < 128 → (Addr.add p d).toNat = p.toNat + d := fun d hd => toNat_addn hd hfit
  have hws : ∀ i < 120, Foot (ws 120 b2W s₀) (Addr.add p i) := fun i hi =>
    ⟨below s₀ 120, by simp, by simp only [below, hpd]; exact mem_add_of_fits hi (by omega)⟩
  -- the canary
  have hcr : (⟨Addr.add s₀.cpu.seg.fsBase 40, 8⟩ : Rgn) ∈ (fp 120 b2W lzR b2Pre (b2Post prof) L s₀).data := by
    simp [Footprint.data, Contract.footprint, fn, lzR]
  have hcf : (Addr.add s₀.cpu.seg.fsBase 40).toNat + 8 ≤ 2 ^ 64 :=
    c.call.foot.fits _ (List.mem_append_left _ hcr)
  have hcn : ∀ i < 8, Foot (fp 120 b2W lzR b2Pre (b2Post prof) L s₀).data
      (Addr.add (Addr.add s₀.cpu.seg.fsBase 40) i) := fun i hi => ⟨_, hcr, mem_add_of_fits hi hcf⟩
  -- the globals
  have hgA : ∀ i < 8, Foot (ws 120 b2W s₀) (Addr.add 0x792148 i) := fun i hi =>
    ⟨⟨0x792148, 8⟩, by simp [b2W], mem_add_of_fits hi (by decide)⟩
  have hgB : ∀ i < 8, Foot (ws 120 b2W s₀) (Addr.add 0x792140 i) := fun i hi =>
    ⟨⟨0x792140, 8⟩, by simp [b2W], mem_add_of_fits hi (by decide)⟩
  have hgC : ∀ i < 8, Foot (ws 120 b2W s₀) (Addr.add 0x796798 i) := fun i hi =>
    ⟨⟨0x796798, 8⟩, by simp [b2W], mem_add_of_fits hi (by decide)⟩
  have hgD : ∀ i < 8, Foot (ws 120 b2W s₀) (Addr.add 0x796790 i) := fun i hi =>
    ⟨⟨0x796790, 8⟩, by simp [b2W], mem_add_of_fits hi (by decide)⟩
  have hgF : ∀ i < 4, Foot (ws 120 b2W s₀) (Addr.add 0x796788 i) := fun i hi =>
    ⟨⟨0x796788, 4⟩, by simp [b2W], mem_add_of_fits hi (by decide)⟩
  -- the stores and the return, from both paths
  have fin : ∀ (V' : Addr → Byte) Y t', KeptW (ws 120 b2W s₀) s₀ Y →
      Agree (fp 120 b2W lzR b2Pre (b2Post prof) L s₀) Y.proc.mm.mem V' →
      Y.cpu.rip = (0x422a20 : Addr).add 33 → Y.cpu.gpr.rsp = Addr.add p 112 → Saved s₀ Y →
      b2Vals prof Y.cpu.gpr.rdi Y.cpu.gpr.rdx Y.cpu.gpr.rsi Y.cpu.gpr.rcx (Y.cpu.gpr.rax.setWidth 32) →
      Go prof 120 b2W lzR b2Pre (b2Post prof) L s₀ ra o Y t' := by
    intro V' Y1 t1 hK1 hA1 hr1 hsp1 hsv1 hv
    refine c.s_mov_rip_r64 hK1 hA1 hin (by omega) hr1 (b2s_33 _) (g := 0x792148) (by decide) hgA ?_
    rintro Y2 t2 hK2 hA2 ⟨hr2, hgr2⟩
    refine c.s_mov_rip_r64 hK2 hA2 hin (by omega) hr2 (b2s_40 _) (g := 0x792140) (by decide) hgB ?_
    rintro Y3 t3 hK3 hA3 ⟨hr3, hgr3⟩
    refine c.s_mov_rip_r64 hK3 hA3 hin (by omega) hr3 (b2s_47 _) (g := 0x796798) (by decide) hgC ?_
    rintro Y4 t4 hK4 hA4 ⟨hr4, hgr4⟩
    refine c.s_mov_rip_r64 hK4 hA4 hin (by omega) hr4 (b2s_54 _) (g := 0x796790) (by decide) hgD ?_
    rintro Y5 t5 hK5 hA5 ⟨hr5, hgr5⟩
    refine c.s_mov_rip_r32 hK5 hA5 hin (by omega) hr5 (b2s_61 _) (g := 0x796788) (by decide) hgF ?_
    rintro Y6 t6 hK6 hA6 ⟨hr6, hgr6⟩
    refine c.s_add_ri64 hK6 hA6 hin (by omega) hr6 (b2s_67 _) ?_
    rintro Y7 t7 hK7 hA7 ⟨hr7, hgr7⟩
    refine c.ret hK7 (callee_of (hsv1.trans ?_) ?_) hin (by omega) hr7 (b2s_71 _) fun M hM => ?_
    · simp [Saved, hgr7, hgr6, hgr5, hgr4, hgr3, hgr2]
    · simp only [hgr7, hgr6, hgr5, hgr4, hgr3, hgr2, set_r4, get_r4]
      rw [hsp1]; exact (add_add8 p _).trans (by rw [hsp])
    · have hAM := c.agreeK hK7 hA7 hM
      refine b2Post_of ?_ ?_ ?_ ?_ ?_ hv
      · show ofBytesLE 64 (readBytes M 0x792148 8) = _
        rw [hAM.read (fun i hi => c.hws _ (hgA i hi)),
          rd_apart (a := 0x796788) (m := 4) (b := 0x792148) (n := 8) _ (by decide) (by decide) (by decide),
          rd_apart (a := 0x796790) (m := 8) (b := 0x792148) (n := 8) _ (by decide) (by decide) (by decide),
          rd_apart (a := 0x796798) (m := 8) (b := 0x792148) (n := 8) _ (by decide) (by decide) (by decide),
          rd_apart (a := 0x792140) (m := 8) (b := 0x792148) (n := 8) _ (by decide) (by decide) (by decide)]
        exact read_Vst_self (by rfl) _ (by decide)
      · show ofBytesLE 64 (readBytes M 0x792140 8) = _
        rw [hAM.read (fun i hi => c.hws _ (hgB i hi)),
          rd_apart (a := 0x796788) (m := 4) (b := 0x792140) (n := 8) _ (by decide) (by decide) (by decide),
          rd_apart (a := 0x796790) (m := 8) (b := 0x792140) (n := 8) _ (by decide) (by decide) (by decide),
          rd_apart (a := 0x796798) (m := 8) (b := 0x792140) (n := 8) _ (by decide) (by decide) (by decide)]
        refine (read_Vst_self (by rfl) _ (by decide)).trans ?_
        simp [hgr2]
      · show ofBytesLE 64 (readBytes M 0x796798 8) = _
        rw [hAM.read (fun i hi => c.hws _ (hgC i hi)),
          rd_apart (a := 0x796788) (m := 4) (b := 0x796798) (n := 8) _ (by decide) (by decide) (by decide),
          rd_apart (a := 0x796790) (m := 8) (b := 0x796798) (n := 8) _ (by decide) (by decide) (by decide)]
        refine (read_Vst_self (by rfl) _ (by decide)).trans ?_
        simp [hgr3, hgr2]
      · show ofBytesLE 64 (readBytes M 0x796790 8) = _
        rw [hAM.read (fun i hi => c.hws _ (hgD i hi)),
          rd_apart (a := 0x796788) (m := 4) (b := 0x796790) (n := 8) _ (by decide) (by decide) (by decide)]
        refine (read_Vst_self (by rfl) _ (by decide)).trans ?_
        simp [hgr4, hgr3, hgr2]
      · show ofBytesLE 32 (readBytes M 0x796788 4) = _
        rw [hAM.read (fun i hi => c.hws _ (hgF i hi))]
        refine (read_Vst_self (by rfl) _ (by decide)).trans ?_
        simp [rv, hgr5, hgr4, hgr3, hgr2]
  -- `endbr64`, `sub rsp, 8`, `call CPU_IsSupported_SSE41`
  refine c.s_endbr hK0 hA0 hin (by omega) (by rw [addr_add_zero]; exact c.call.shape.1) (b2s_0 _) ?_
  rintro Y1 t1 hK1 hA1 ⟨hr1, hg1⟩
  refine c.s_sub_ri64 hK1 hA1 hin (by omega) hr1 (b2s_4 _) ?_
  rintro Y2 t2 hK2 hA2 ⟨hr2, hg2⟩
  have hsp2 : Y2.cpu.gpr.rsp = Addr.add p 112 := by
    rw [hg2, hg1, set_r4, get_r4, hsp]; exact add_sub_lit p (by omega)
  refine c.s_call hK2 hA2 hin (by omega) hr2 (b2s_8 _) hinS (by rw [sse41_length]; omega) (by decide)
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
  -- `test eax, eax`, `jne`
  refine c.s_test_rr32 hK4 hA4 hin (by omega) hr4 (b2s_13 _) ?_
  rintro Y5 t5 hK5 hA5 ⟨hr5, hg5, hz5⟩
  have hsv5 : Saved s₀ Y5 := (hsv3.trans hsv4).trans (by simp [Saved, hg5])
  have hsp5 : Y5.cpu.gpr.rsp = Addr.add p 112 := by rw [hg5, hsp4]
  refine c.s_jcc hK5 hA5 hin (by omega) hr5 (b2s_15 _) (tgt := 80) rfl (by omega) (fun hc => ?_) fun _ => ?_
  · -- SSE4.1: `call CPU_IsSupported_AVX2`
    have hsse : prof.reports 1 0 (·.ecx) 19 := hax4 fun h0 => by
      simp only [Rflags.cond, hz5, Bool.not_eq_true'] at hc
      simp [rv, h0] at hc
    rintro Y6 t6 hK6 hA6 ⟨hr6, hg6⟩
    have hsp6 : Y6.cpu.gpr.rsp = Addr.add p 112 := by rw [hg6, hsp5]
    refine c.s_call hK6 hA6 hin (by omega) hr6 (b2s_80 _) hinA2 (by rw [avx2_length]; omega) (by decide)
      (fun i hi => by rw [hsp6, add_sub8 p (m := 104) rfl, addr_add_add]; exact hws _ (by omega)) ?_
    rw [hsp6, add_sub8 p (m := 104) rfl]
    rintro Y7 t7 hK7 hA7 ⟨hr7, hg7⟩
    have hsp7 : Y7.cpu.gpr.rsp = Addr.add p 104 := by rw [hg7, set_4]
    have hsv7 : Saved s₀ Y7 := hsv5.trans (by simp [Saved, hg7, hg6])
    refine sub_avx2 c hpc hK7 hA7 hinA2 hinA hinM hinC hr7 (fun i hi => by
        rw [hsp7, add_sub_lit p (n := 104) (d := 104) (by omega), addr_add_add]; exact hws _ (by omega))
      (fun i hi => by rw [hsp7, addr_add_add]; exact c.hws _ (hws _ (by omega)))
      hcn (by rw [hsp7, hpn 104 (by omega)]; omega) (by rw [hsp7, hpn 104 (by omega)]; omega) hcf
      (by rw [hsp7, hpn 104 (by omega)]; omega) hin (j₂ := 85) (by omega)
      (by rw [hsp7]; exact read_Vst_self (by rfl) _ (by rw [hpn 104 (by omega)]; omega)) ?_
    intro V8 _ Y8 t8 hK8 hA8 ⟨hr8, hsp8, hsv8, hax8⟩
    rw [hsp7, add_add8] at hsp8
    -- the choices
    refine c.s_lea_rip hK8 hA8 hin (by omega) hr8 (b2s_85 _) (v := 0x421700) (by decide) ?_
    rintro Y9 t9 hK9 hA9 ⟨hr9, hg9, -⟩
    refine c.s_lea_rip hK9 hA9 hin (by omega) hr9 (b2s_92 _) (v := 0x420970) (by decide) ?_
    rintro Y10 t10 hK10 hA10 ⟨hr10, hg10, -⟩
    refine c.s_test_rr32 hK10 hA10 hin (by omega) hr10 (b2s_99 _) ?_
    rintro Y11 t11 hK11 hA11 ⟨hr11, hg11, hz11⟩
    refine c.s_lea_rip hK11 hA11 hin (by omega) hr11 (b2s_101 _) (v := 0x420820) (by decide) ?_
    rintro Y12 t12 hK12 hA12 ⟨hr12, hg12, hf12⟩
    refine c.s_lea_rip hK12 hA12 hin (by omega) hr12 (b2s_108 _) (v := 0x420dc0) (by decide) ?_
    rintro Y13 t13 hK13 hA13 ⟨hr13, hg13, hf13⟩
    refine c.s_cmov hK13 hA13 hin (by omega) hr13 (b2s_115 _) ?_
    rintro Y14 t14 hK14 hA14 ⟨hr14, hg14, hf14⟩
    have hg14' : Y14.cpu.gpr = { Y13.cpu.gpr with
        rcx := if Y13.cpu.rflags.cond 5 then Y13.cpu.gpr.rdx else Y13.cpu.gpr.rcx } := by
      rw [hg14]; split <;> rfl
    refine c.s_lea_rip hK14 hA14 hin (by omega) hr14 (b2s_119 _) (v := 0x421820) (by decide) ?_
    rintro Y15 t15 hK15 hA15 ⟨hr15, hg15, hf15⟩
    refine c.s_lea_rip hK15 hA15 hin (by omega) hr15 (b2s_126 _) (v := 0x4208e0) (by decide) ?_
    rintro Y16 t16 hK16 hA16 ⟨hr16, hg16, hf16⟩
    refine c.s_cmov hK16 hA16 hin (by omega) hr16 (b2s_133 _) ?_
    rintro Y17 t17 hK17 hA17 ⟨hr17, hg17, hf17⟩
    have hg17' : Y17.cpu.gpr = { Y16.cpu.gpr with
        rsi := if Y16.cpu.rflags.cond 5 then Y16.cpu.gpr.rdx else Y16.cpu.gpr.rsi } := by
      rw [hg17]; split <;> rfl
    refine c.s_lea_rip hK17 hA17 hin (by omega) hr17 (b2s_137 _) (v := 0x420a80) (by decide) ?_
    rintro Y18 t18 hK18 hA18 ⟨hr18, hg18, hf18⟩
    refine c.s_cmov hK18 hA18 hin (by omega) hr18 (b2s_144 _) ?_
    rintro Y19 t19 hK19 hA19 ⟨hr19, hg19, hf19⟩
    have hg19' : Y19.cpu.gpr = { Y18.cpu.gpr with
        rdi := if Y18.cpu.rflags.cond 5 then Y18.cpu.gpr.r8 else Y18.cpu.gpr.rdi } := by
      rw [hg19]; split <;> rfl
    -- the flags
    refine c.s_cmp_ri32 hK19 hA19 hin (by omega) hr19 (b2s_148 _) ?_
    rintro Y20 t20 hK20 hA20 ⟨hr20, hg20, hf20⟩
    refine c.s_sbb_rr32 hK20 hA20 hin (by omega) hr20 (b2s_151 _) ?_
    rintro Y21 t21 hK21 hA21 ⟨hr21, hg21⟩
    refine c.s_and_ri32 hK21 hA21 hin (by omega) hr21 (b2s_153 _) ?_
    rintro Y22 t22 hK22 hA22 ⟨hr22, hg22, -⟩
    refine c.s_add_ri32 hK22 hA22 hin (by omega) hr22 (b2s_156 _) ?_
    rintro Y23 t23 hK23 hA23 ⟨hr23, hg23⟩
    refine c.s_jmp hK23 hA23 hin (by omega) hr23 (b2s_159 _) (tgt := 33) rfl (by omega) ?_
    rintro Y24 t24 hK24 hA24 ⟨hr24, hg24⟩
    have hc : ∀ Y : State, Y.cpu.rflags.zf = Y11.cpu.rflags.zf → Y.cpu.rflags.cond 5 = !Y11.cpu.rflags.zf := by
      intro Y hY; simp [Rflags.cond, hY]
    have c13 := hc Y13 (by simp [hf13, hf12, rf0])
    have c16 := hc Y16 (by simp [hf16, hf15, hf14, hf13, hf12, rf0])
    have c18 := hc Y18 (by simp [hf18, hf17, hf16, hf15, hf14, hf13, hf12, rf0])
    have hz : Y11.cpu.rflags.zf = (Y8.cpu.gpr.rax.setWidth 32 == 0) := by
      rw [hz11]; simp [rv, hg10, hg9]
    have hr0 : rv Y19 32 0 = Y8.cpu.gpr.rax.setWidth 32 := by
      simp [rv, hg19', hg18, hg17', hg16, hg15, hg14', hg13, hg12, hg11, hg10, hg9]
    have hcf : Y20.cpu.rflags.cf = borrowSub (Y8.cpu.gpr.rax.setWidth 32) (BitVec.ofNat 32 1) false := by
      rw [hf20, ← hr0]; rfl
    have hax : Y24.cpu.gpr.rax.setWidth 32 = if Y8.cpu.gpr.rax.setWidth 32 = 0 then 0x14 else 0x1c := by
      rw [← b2_flags, ← hcf]
      simp [rv, hg24, hg23, hg22, hg21, hg20]
    refine fin _ Y24 t24 hK24 hA24 hr24
      (by simp [hg24, hg23, hg22, hg21, hg20, hg19', hg18, hg17', hg16, hg15, hg14', hg13, hg12, hg11, hg10, hg9,
        hsp8])
      (hsv7.trans (hsv8.trans (by
        simp [Saved, hg24, hg23, hg22, hg21, hg20, hg19', hg18, hg17', hg16, hg15, hg14', hg13, hg12, hg11, hg10,
          hg9]))) ?_
    rw [hax]
    have hgpr : Y24.cpu.gpr.rdi = (if Y18.cpu.rflags.cond 5 then 0x421820 else 0x420dc0) ∧
        Y24.cpu.gpr.rdx = 0x420a80 ∧
        Y24.cpu.gpr.rsi = (if Y16.cpu.rflags.cond 5 then 0x4208e0 else 0x420820) ∧
        Y24.cpu.gpr.rcx = (if Y13.cpu.rflags.cond 5 then 0x421700 else 0x420970) := by
      simp [hg24, hg23, hg22, hg21, hg20, hg19', hg18, hg17', hg16, hg15, hg14', hg13, hg12, hg11, hg10, hg9]
    obtain ⟨e1, e2, e3, e4⟩ := hgpr
    rw [e1, e2, e3, e4, c13, c16, c18, hz]
    by_cases h0 : Y8.cpu.gpr.rax.setWidth 32 = 0
    · simp only [h0, beq_self_eq_true, Bool.not_true, ite_true, Bool.false_eq_true, ite_false]
      exact Or.inr (Or.inl ⟨rfl, rfl, rfl, rfl, rfl, hpc.sse41 hsse⟩)
    · obtain ⟨h7, h28, hen⟩ := hax8 h0
      have hb : (Y8.cpu.gpr.rax.setWidth 32 == 0) = false := by simpa using h0
      simp only [hb, h0, Bool.not_false, ite_true, ite_false]
      exact Or.inr (Or.inr ⟨rfl, rfl, rfl, rfl, rfl, hpc.sse41 hsse, hpc.avx2 h7 hen, hpc.avx h28 hen⟩)
  · -- no SSE4.1: `lea rdx, Blake2sp_Compress2`, `xor ecx, ecx`, `xor esi, esi`, `xor eax, eax`, `mov rdi, rdx`
    rintro Y6 t6 hK6 hA6 ⟨hr6, hg6⟩
    refine c.s_lea_rip hK6 hA6 hin (by omega) hr6 (b2s_17 _) (v := 0x420280) (by decide) ?_
    rintro Y7 t7 hK7 hA7 ⟨hr7, hg7, -⟩
    refine c.s_xor_rr32 hK7 hA7 hin (by omega) hr7 (b2s_24 _) ?_
    rintro Y8 t8 hK8 hA8 ⟨hr8, hg8⟩
    refine c.s_xor_rr32 hK8 hA8 hin (by omega) hr8 (b2s_26 _) ?_
    rintro Y9 t9 hK9 hA9 ⟨hr9, hg9⟩
    refine c.s_xor_rr32 hK9 hA9 hin (by omega) hr9 (b2s_28 _) ?_
    rintro Y10 t10 hK10 hA10 ⟨hr10, hg10⟩
    refine c.s_mov_rr64 hK10 hA10 hin (by omega) hr10 (b2s_30 _) ?_
    rintro Y11 t11 hK11 hA11 ⟨hr11, hg11⟩
    exact fin _ Y11 t11 hK11 hA11 hr11 (by simp [hg11, hg10, hg9, hg8, hg7, hg6, hsp5])
      (hsv5.trans (by simp [Saved, hg11, hg10, hg9, hg8, hg7, hg6]))
      (Or.inl ⟨by simp [hg11, hg10, hg9, hg8, hg7], by simp [hg11, hg10, hg9, hg8, hg7],
        by simp [hg11, hg10, hg9, hg8], by simp [hg11, hg10, hg9, hg8], by simp [rv, hg11, hg10]⟩)

/-- `z7_Black2sp_Prepare`, at `0x422a20`, with its callees' code: on a consistent profile, every call returns, with
the BLAKE2sp pointers and flags the portable ones, or the 128-bit ones on a processor with SSE4.1, or the 256-bit
ones on one with SSE4.1, AVX2 and AVX. -/
theorem black2spPrepare (prof : Profile) (hpc : prof.Consistent) {L : List (Addr × List Byte)}
    (hin : CodeIn L 0x422a20 b2s) (hinS : CodeIn L 0x424390 sse41) (hinA2 : CodeIn L 0x4244b0 avx2)
    (hinA : CodeIn L 0x424440 avx) (hinM : CodeIn L 0x4242b0 maxf) (hinC : CodeIn L 0x424290 cpuid) :
    ImplementsCall prof 0x422a20 L (b2C prof) := by
  intro s₀ ra hcall
  have hfr := Call.frame_arith (k := 120) (s := s₀)
    (hcall.foot.fits (frame s₀ 120) (by simp [Footprint.data, Contract.footprint, fn]))
  have hslot : ∀ i < 8, ¬ Foot (b2W s₀) (Addr.add s₀.cpu.gpr.rsp i) := by
    rintro i hi ⟨r, hr, hm⟩
    have hg := hcall.pre.2
    have e1 : (0x792148 : Addr).toNat = 0x792148 := rfl
    have e2 : (0x792140 : Addr).toNat = 0x792140 := rfl
    have e3 : (0x796798 : Addr).toNat = 0x796798 := rfl
    have e4 : (0x796790 : Addr).toNat = 0x796790 := rfl
    have e5 : (0x796788 : Addr).toNat = 0x796788 := rfl
    simp only [b2W, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;>
      simp only [Rgn.Mem, toNat_add_of_fits hi hfr.2, e1, e2, e3, e4, e5] at hm <;> omega
  exact reachOrEndsIn_of_runsFrom fun o ho t =>
    b2Run hpc (Call.of hcall ho hslot) hin hinS hinA2 hinA hinM hinC t

end FV7z.Prepare
