import FV7z.CpuFeat.IcfA
import FV7z.Lemmas.FnJt
/-!
# `init_cpu_features`: Intel's part (PLAN.md G2, glibc `init_cpu_features`)

From `0x613676`, for `GenuineIntel`: `get_common_indices` with the four pointers into the frame, the extended
leaves, and for family 6 the model's case by a jump table at `0x6ee6d0` (70 entries, 4 targets): bits of
`feature[1]` (never bit 8, `AVX_Fast_Unaligned_Load`, but kept as it was), `RTM` cleared in `cpuid[7].ebx`
for some models; then `feature[1]` with `Prefer_No_VZEROUPPER` or `Prefer_ERMS`-like bits (14, 11), `eax = 1` and
the common part at `88` (`iT1`).
-/
namespace FV7z.CpuFeat
open ZellicX86 Decode FV7z.Leaf FV7z.Fn FV7z.Prepare Glibc

set_option linter.deprecated false

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle} {F : Footprint} {Wl : List Rgn}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}

/-- The jump table at `0x6ee6d0`: 70 offsets from it. -/
def jtab : List Byte := [0x0e, 0x51, 0xf2, 0xff, 0x05, 0x51, 0xf2, 0xff, 0xdd, 0x50, 0xf2, 0xff, 0x05, 0x51, 0xf2, 0xff, 0x0e, 0x51, 0xf2, 0xff, 0x0e, 0x51, 0xf2, 0xff, 0x05, 0x51, 0xf2, 0xff, 0x05, 0x51, 0xf2, 0xff, 0x05, 0x51, 0xf2, 0xff, 0x05, 0x51, 0xf2, 0xff, 0x05, 0x51, 0xf2, 0xff, 0x0e, 0x51, 0xf2, 0xff, 0xdd, 0x50, 0xf2, 0xff, 0x05, 0x51, 0xf2, 0xff, 0x05, 0x51, 0xf2, 0xff, 0x05, 0x51, 0xf2, 0xff, 0x05, 0x51, 0xf2, 0xff, 0x05, 0x51, 0xf2, 0xff, 0x0e, 0x51, 0xf2, 0xff, 0x05, 0x51, 0xf2, 0xff, 0x0e, 0x51, 0xf2, 0xff, 0x0e, 0x51, 0xf2, 0xff, 0x05, 0x51, 0xf2, 0xff, 0x05, 0x51, 0xf2, 0xff, 0x05, 0x51, 0xf2, 0xff, 0x05, 0x51, 0xf2, 0xff, 0x05, 0x51, 0xf2, 0xff, 0x05, 0x51, 0xf2, 0xff, 0x05, 0x51, 0xf2, 0xff, 0xb2, 0x50, 0xf2, 0xff, 0x05, 0x51, 0xf2, 0xff, 0x05, 0x51, 0xf2, 0xff, 0x05, 0x51, 0xf2, 0xff, 0x05, 0x51, 0xf2, 0xff, 0x05, 0x51, 0xf2, 0xff, 0x05, 0x51, 0xf2, 0xff, 0x05, 0x51, 0xf2, 0xff, 0x05, 0x51, 0xf2, 0xff, 0x05, 0x51, 0xf2, 0xff, 0x05, 0x51, 0xf2, 0xff, 0x05, 0x51, 0xf2, 0xff, 0x05, 0x51, 0xf2, 0xff, 0x05, 0x51, 0xf2, 0xff, 0x05, 0x51, 0xf2, 0xff, 0x05, 0x51, 0xf2, 0xff, 0x05, 0x51, 0xf2, 0xff, 0x05, 0x51, 0xf2, 0xff, 0x05, 0x51, 0xf2, 0xff, 0xb2, 0x50, 0xf2, 0xff, 0x05, 0x51, 0xf2, 0xff, 0xb2, 0x50, 0xf2, 0xff, 0xb2, 0x50, 0xf2, 0xff, 0x05, 0x51, 0xf2, 0xff, 0x05, 0x51, 0xf2, 0xff, 0x05, 0x51, 0xf2, 0xff, 0x05, 0x51, 0xf2, 0xff, 0x05, 0x51, 0xf2, 0xff, 0x05, 0x51, 0xf2, 0xff, 0x05, 0x51, 0xf2, 0xff, 0x05, 0x51, 0xf2, 0xff, 0x05, 0x51, 0xf2, 0xff, 0xb2, 0x50, 0xf2, 0xff, 0x05, 0x51, 0xf2, 0xff, 0x05, 0x51, 0xf2, 0xff, 0xb2, 0x50, 0xf2, 0xff, 0x05, 0x51, 0xf2, 0xff, 0xb2, 0x50, 0xf2, 0xff, 0xb2, 0x50, 0xf2, 0xff, 0x05, 0x51, 0xf2, 0xff, 0xb2, 0x50, 0xf2, 0xff]

theorem jtab_pin : Exe.bytesAt V2606.zzs.blob 0x6ee6d0 280 = some jtab := by decide +kernel

/-- The target of entry `n`: `movsxd rcx, [rsi + rcx·4]`, `add rcx, rsi`. -/
def jtgt (n : Nat) : Addr :=
  (ofBytesLE 32 ((List.range 4).map fun k => jtab.getD (4 * n + k) 0)).signExtend 64 + 0x6ee6d0

theorem jtgt_cases : ∀ n < 70, jtgt n = (0x613676 : Addr).add 268 ∨ jtgt n = (0x613676 : Addr).add 311 ∨
    jtgt n = (0x613676 : Addr).add 351 ∨ jtgt n = (0x613676 : Addr).add 360 := by decide +kernel

/-- The table's bytes: the footprint's, not the run's to store into, as in the binary. -/
structure JT (F : Footprint) (Wl : List Rgn) (V₀ : Addr → Byte) : Prop where
  data : ∀ i < 280, Foot F.data ((0x6ee6d0 : Addr).add i)
  nw : ∀ i < 280, ¬ Foot Wl ((0x6ee6d0 : Addr).add i)
  val : ∀ i < 280, V₀ ((0x6ee6d0 : Addr).add i) = jtab.getD i 0

theorem jt_addr (n : BitVec 64) (k : Nat) :
    ((0x6ee6d0 : Addr) + n * BitVec.ofNat 64 4 + BitVec.ofNat 64 0).add k = (0x6ee6d0 : Addr).add (4 * n.toNat + k) := by
  apply BitVec.eq_of_toNat_eq
  have e : (0x6ee6d0 : Addr).toNat = 0x6ee6d0 := rfl
  simp only [Addr.add, BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat, e]
  omega

section

/-- Clearing bits of `cpuid[7].ebx` keeps `CInv`. -/
theorem CInv.and20 {V : Addr → Byte} (h : CInv prof V) (m : BitVec 32) :
    CInv prof (Vst V (cpuRgn.base.add 20) (toBytesLE (rdw V 20 &&& m) 4)) :=
  h.st_cpuid _ (Or.inr (Or.inr (Or.inl rfl))) fun i hi hb => by
    rw [BitVec.getLsbD_and, getLsbD_rd hi, Bool.and_eq_true] at hb
    exact ⟨fun h => absurd h (by omega), fun h => absurd h (by omega), fun _ => h.ebx7 i hi hb.1,
      fun h => absurd h (by omega)⟩

/-- `feature[1]` with bit 8 as it was. -/
theorem CInv.f1_eq8 {V : Addr → Byte} (h : CInv prof V) (w : BitVec 32) (h8 : w.getLsbD 8 = bitV V 100 8) :
    CInv prof (Vst V (cpuRgn.base.add 100) (toBytesLE w 4)) :=
  h.st_f1 w ⟨h.f.avx, h.f.avx2, h.f.avx512f, h.f.avx512vl, h.f.avx512dq, h.f.avx512bw, h.f.fma, h.f.vaes,
    fun hb => h.f.fastAvx (h8 ▸ hb)⟩

end

/-- `or ah, imm` with bit 0 of `imm` clear keeps bit 8. -/
theorem ob8 (x : BitVec 64) (imm : Nat) (h : imm % 2 = 0) :
    ((((x &&& ~~~(BitVec.ofNat 64 ((2 ^ 8 - 1) * 2 ^ 8))) |||
      (((x >>> 8).setWidth 8 ||| BitVec.ofNat 8 imm).setWidth 64 <<< 8))).setWidth 32).getLsbD 8 = x.getLsbD 8 := by
  simp only [BitVec.getLsbD_or, BitVec.getLsbD_setWidth, BitVec.getLsbD_and, BitVec.getLsbD_not,
    BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ofNat, BitVec.getLsbD_ushiftRight]
  simp only [Nat.reduceLT, decide_true, Bool.true_and]
  simp
  rw [decide_eq_false (by omega : ¬ imm % 2 = 1)]
  cases x[8] <;> decide

/-- Bit 8 of `eax` after `or ah, imm` (`Seg.s_or_h8i`), `imm` even. -/
theorem or_h8_b8 {X Y : State} {imm : Nat} (h0 : imm % 2 = 0)
    (h : Y.cpu.gpr = X.cpu.gpr.set (regOf 0) ((X.cpu.gpr.get (regOf 0) &&& ~~~(BitVec.ofNat 64 ((2 ^ 8 - 1) * 2 ^ 8))) |||
      (((X.cpu.gpr.get (regOf 0) >>> 8).setWidth 8 ||| BitVec.ofNat 8 imm).setWidth 64 <<< 8))) :
    (rv Y 32 0).getLsbD 8 = X.cpu.gpr.rax.getLsbD 8 := by
  rw [rv, h]
  exact ob8 _ _ h0

section K
variable (c : Seg prof F Wl L s₀ o) {V₀ : Addr → Byte} {q : Addr} (hE : IE F Wl L V₀ q) {g₀ : Gprs}
  (hsp0 : g₀.rsp = q.add 8) (k : IK prof F Wl L s₀ o gev gP gE V₀ g₀)
include c hE hsp0 k

/-- `0x613715`: `feature[1]` with bit 14, or bit 11 if bit 3 of the byte at offset 23 is set; `eax = 1`, to `88`. -/
theorem iI159 : AtK prof F Wl L s₀ o gev gP gE V₀ g₀ 0x613676 159 := by
  intro X t V hK hA hV hr hT
  have hl : icfi.length = 374 := icfi_length
  have a184 : ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y → Agree F Y.proc.mm.mem V →
      Y.cpu.rip = (0x613676 : Addr).add 184 → TK g₀ Y.cpu.gpr → (rv Y 32 0).getLsbD 8 = bitV V 100 8 →
      GoG prof L o gev gP gE Y t' := by
    intro Y0 t0 hK0 hA0 hr0 hT0 hb
    refine c.s_mov_rip_r32 hK0 hA0 hE.codei (by omega) hr0 (icfi_184 _) (g := (0x7a4ae0 : Addr).add 100) (by decide)
      (fun i hi => hE.cf (by omega)) ?_
    rintro Y1 t1 hK1 hA1 ⟨hr1, hg1⟩
    refine c.s_mov_ri32 hK1 hA1 hE.codei (by omega) hr1 (icfi_190 _) ?_
    rintro Y2 t2 hK2 hA2 ⟨hr2, hg2⟩
    refine c.s_jmp_x hK2 hA2 hE.codei (by omega) hr2 (icfi_195 _) hE.code (tgt := 88) (by rw [icf_length]; omega)
      (by decide) ?_
    rintro Y3 t3 hK3 hA3 ⟨hr3, hg3⟩
    exact iT1 c hE hsp0 k Y3 t3 _ hK3 hA3 (hV.st (fun i hi => hE.cf (by simp at hi; omega)) (hV.inv.f1_eq8 _ hb))
      hr3 (by rw [hg3, hg2, hg1]; exact hT0.set (by omega) _)
  refine c.s_mov_r32_rip hK hA hE.codei (by omega) hr (icfi_159 _) (g := (0x7a4ae0 : Addr).add 100) (by decide)
    (hE.cfd c (by omega)) ?_
  rintro Y1 t1 hK1 hA1 ⟨hr1, hg1⟩
  have hv1 : rv Y1 32 2 = rdw V 100 := by rw [rv, hg1]; simp; rfl
  refine c.s_mov_rr32 hK1 hA1 hE.codei (by omega) hr1 (icfi_165 _) ?_
  rintro Y2 t2 hK2 hA2 ⟨hr2, hg2⟩
  refine c.s_or_h8i hK2 hA2 hE.codei (by omega) hr2 (icfi_167 _) ?_
  rintro Y3 t3 hK3 hA3 ⟨hr3, hg3⟩
  have hT3 : TK g₀ Y3.cpu.gpr := by rw [hg3, hg2, hg1]; exact ((hT.set (by omega) _).set (by omega) _).set (by omega) _
  have hb3 : (rv Y3 32 0).getLsbD 8 = bitV V 100 8 := by
    rw [or_h8_b8 (by decide) hg3, show Y2.cpu.gpr.rax = (rv Y1 32 2).setWidth 64 by rw [hg2]; rfl, hv1,
      BitVec.getLsbD_setWidth, getLsbD_rd (by decide)]
    rfl
  refine c.s_test_m8i_rip hK3 hA3 hE.codei (by omega) hr3 (icfi_170 _) (g := (0x7a4ae0 : Addr).add 23) (by decide)
    (by have := hE.cfd c (a := 23) (n := 1) (by omega) 0 (by omega); rwa [addr_add_zero] at this) ?_
  rintro Y4 t4 hK4 hA4 ⟨hr4, hg4, -⟩
  refine c.s_jcc hK4 hA4 hE.codei (by omega) hr4 (icfi_177 _) (tgt := 184) (by decide) (by omega)
    (fun _ Y t' hKY hAY ⟨hrY, hgY⟩ => a184 Y t' hKY hAY hrY (by rw [hgY, hg4]; exact hT3)
      (by rw [rv, hgY, hg4]; exact hb3)) fun _ => ?_
  rintro Y5 t5 hK5 hA5 ⟨hr5, hg5⟩
  refine c.s_mov_rr32 hK5 hA5 hE.codei (by omega) hr5 (icfi_179 _) ?_
  rintro Y6 t6 hK6 hA6 ⟨hr6, hg6⟩
  refine c.s_or_h8i hK6 hA6 hE.codei (by omega) hr6 (icfi_181 _) ?_
  rintro Y7 t7 hK7 hA7 ⟨hr7, hg7⟩
  refine a184 Y7 t7 hK7 hA7 hr7 (by rw [hg7, hg6, hg5, hg4]; exact (hT3.set (by omega) _).set (by omega) _) ?_
  rw [or_h8_b8 (by decide) hg7, show Y6.cpu.gpr.rax = (rv Y5 32 2).setWidth 64 by rw [hg6]; rfl,
    show rv Y5 32 2 = rv Y1 32 2 by rw [rv, rv, hg5, hg4, hg3, hg2]; rfl, hv1,
    BitVec.getLsbD_setWidth, getLsbD_rd (by decide)]
  rfl

/-- `0x61379e`: `cpuid[7].ebx` without bit 11 (`RTM`), to `159`. -/
theorem iI296 : AtK prof F Wl L s₀ o gev gP gE V₀ g₀ 0x613676 296 := by
  intro X t V hK hA hV hr hT
  have hl : icfi.length = 374 := icfi_length
  refine c.s_and_rip_i32 hK hA hE.codei (by omega) hr (icfi_296 _) (g := (0x7a4ae0 : Addr).add 20) (by decide)
    (fun i hi => hE.cf (by omega)) ?_
  rintro Y1 t1 hK1 hA1 ⟨hr1, hg1⟩
  refine c.s_jmp_x hK1 hA1 hE.codei (by omega) hr1 (icfi_306 _) hE.codei (tgt := 159) (by omega) (by decide) ?_
  rintro Y2 t2 hK2 hA2 ⟨hr2, hg2⟩
  exact iI159 c hE hsp0 k Y2 t2 _ hK2 hA2 (hV.st (fun i hi => hE.cf (by simp at hi; omega)) (hV.inv.and20 _)) hr2
    (by rw [hg2, hg1]; exact hT)

/-- `0x61378e`: by the model in `eax`, `0x3c`, `0x45`, `0x46`, or `0x3f` with stepping at most 3, to `296`; else to
`159`. -/
theorem iI280 : AtK prof F Wl L s₀ o gev gP gE V₀ g₀ 0x613676 280 := by
  intro X t V hK hA hV hr hT
  have hl : icfi.length = 374 := icfi_length
  have a159 := iI159 c hE hsp0 k
  have a296 := iI296 c hE hsp0 k
  refine c.s_cmp_ri32 hK hA hE.codei (by omega) hr (icfi_280 _) ?_
  rintro Y1 t1 hK1 hA1 ⟨hr1, hg1, -⟩
  rw [← hg1] at hT
  refine c.s_jcc hK1 hA1 hE.codei (by omega) hr1 (icfi_283 _) (tgt := 338) (by decide) (by omega)
    (fun _ Y t' hKY hAY ⟨hrY, hgY⟩ => ?_) fun _ => ?_
  · have hs : Y.cpu.gpr.rsp = q.add 8 := by rw [hgY, hT.sp, hsp0]
    refine c.s_cmp_m32i hKY hAY hE.codei (by omega) hrY (icfi_338 _)
      (fun i hi => by rw [eaD_sp hs, addr_add_add]; exact c.hws _ (hE.fr (by omega))) ?_
    rintro Y2 t2 hK2 hA2 ⟨hr2, hg2⟩
    refine c.s_jcc hK2 hA2 hE.codei (by omega) hr2 (icfi_343 _) (tgt := 159) (by decide) (by omega)
      (fun _ Z t' hKZ hAZ ⟨hrZ, hgZ⟩ => a159 Z t' _ hKZ hAZ hV hrZ (by rw [hgZ, hg2, hgY]; exact hT)) fun _ => ?_
    rintro Y3 t3 hK3 hA3 ⟨hr3, hg3⟩
    refine c.s_jmp_x hK3 hA3 hE.codei (by omega) hr3 (icfi_349 _) hE.codei (tgt := 296) (by omega) (by decide) ?_
    rintro Y4 t4 hK4 hA4 ⟨hr4, hg4⟩
    exact a296 Y4 t4 _ hK4 hA4 hV hr4 (by rw [hg4, hg3, hg2, hgY]; exact hT)
  rintro Y2 t2 hK2 hA2 ⟨hr2, hg2⟩
  rw [← hg2] at hT
  refine c.s_jcc hK2 hA2 hE.codei (by omega) hr2 (icfi_285 _) (tgt := 325) (by decide) (by omega)
    (fun _ Y t' hKY hAY ⟨hrY, hgY⟩ => ?_) fun _ => ?_
  · refine c.s_wr hKY hAY hE.codei (by omega) hrY wr_sub_ri32 (icfi_325 _) ?_
    rintro Y3 t3 hK3 hA3 ⟨hr3, v, hg3⟩
    replace hr3 : Y3.cpu.rip = (0x613676 : Addr).add 328 := hr3
    have hT3 : TK g₀ Y3.cpu.gpr := by rw [hg3, hgY]; exact hT.set (by omega) _
    refine c.s_fl hK3 hA3 hE.codei (by omega) hr3 fl_cmp_ri32 (icfi_328 _) ?_
    rintro Y4 t4 hK4 hA4 ⟨hr4, hg4⟩
    replace hr4 : Y4.cpu.rip = (0x613676 : Addr).add 331 := hr4
    rw [← hg4] at hT3
    refine c.s_jcc hK4 hA4 hE.codei (by omega) hr4 (icfi_331 _) (tgt := 296) (by decide) (by omega)
      (fun _ Z t' hKZ hAZ ⟨hrZ, hgZ⟩ => a296 Z t' _ hKZ hAZ hV hrZ (by rw [hgZ]; exact hT3)) fun _ => ?_
    rintro Y5 t5 hK5 hA5 ⟨hr5, hg5⟩
    refine c.s_jmp_x hK5 hA5 hE.codei (by omega) hr5 (icfi_333 _) hE.codei (tgt := 159) (by omega) (by decide) ?_
    rintro Y6 t6 hK6 hA6 ⟨hr6, hg6⟩
    exact a159 Y6 t6 _ hK6 hA6 hV hr6 (by rw [hg6, hg5]; exact hT3)
  rintro Y3 t3 hK3 hA3 ⟨hr3, hg3⟩
  rw [← hg3] at hT
  refine c.s_cmp_ri32 hK3 hA3 hE.codei (by omega) hr3 (icfi_287 _) ?_
  rintro Y4 t4 hK4 hA4 ⟨hr4, hg4, -⟩
  rw [← hg4] at hT
  refine c.s_jcc hK4 hA4 hE.codei (by omega) hr4 (icfi_290 _) (tgt := 159) (by decide) (by omega)
    (fun _ Z t' hKZ hAZ ⟨hrZ, hgZ⟩ => a159 Z t' _ hKZ hAZ hV hrZ (by rw [hgZ]; exact hT)) fun _ => ?_
  rintro Y5 t5 hK5 hA5 ⟨hr5, hg5⟩
  exact a296 Y5 t5 _ hK5 hA5 hV hr5 (by rw [hg5]; exact hT)

/-- At `j`, with `edx` the word `feature[1]`. -/
def AtD (prof : Profile) (F : Footprint) (Wl : List Rgn) (L : List (Addr × List Byte)) (s₀ : State) (o : Oracle)
    (gev : List Event) (gP : State → Nat → List Event → Prop) (gE : Outcome → List Event → Prop)
    (V₀ : Addr → Byte) (g₀ : Gprs) (j : Nat) : Prop :=
  ∀ (X : State) (t : Nat) (V : Addr → Byte), KeptW Wl s₀ X → Agree F X.proc.mm.mem V → IV prof Wl V₀ V →
    X.cpu.rip = (0x613676 : Addr).add j → TK g₀ X.cpu.gpr → rv X 32 2 = rdw V 100 → GoG prof L o gev gP gE X t

omit c hE hsp0 k in
theorem or_edx {X Y : State} {V : Addr → Byte} {imm : Nat} (hd : rv X 32 2 = rdw V 100)
    (hg : Y.cpu.gpr = X.cpu.gpr.set (regOf 2) ((rv X 32 2 ||| BitVec.ofNat 32 imm).setWidth 64)) :
    rv Y 32 2 = rdw V 100 ||| BitVec.ofNat 32 imm := by
  rw [show rv Y 32 2 = ((rv X 32 2 ||| BitVec.ofNat 32 imm).setWidth 64).setWidth 32 by rw [rv, hg]; rfl, hd]
  simp

/-- `0x613782`: `feature[1] |= 0x4b0`, to `280`. -/
theorem iI268 : AtD prof F Wl L s₀ o gev gP gE V₀ g₀ 268 := by
  intro X t V hK hA hV hr hT hd
  have hl : icfi.length = 374 := icfi_length
  refine c.s_or_ri32 hK hA hE.codei (by omega) hr (icfi_268 _) ?_
  rintro Y1 t1 hK1 hA1 ⟨hr1, hg1⟩
  refine c.s_mov_rip_r32 hK1 hA1 hE.codei (by omega) hr1 (icfi_274 _) (g := (0x7a4ae0 : Addr).add 100) (by decide)
    (fun i hi => hE.cf (by omega)) ?_
  rintro Y2 t2 hK2 hA2 ⟨hr2, hg2⟩
  rw [or_edx hd hg1] at hA2
  exact iI280 c hE hsp0 k Y2 t2 _ hK2 hA2 (hV.or_f1 hE 1200 (by decide)) hr2
    (by rw [hg2, hg1]; exact hT.set (by omega) _)

/-- `0x6137ad`: `feature[1] |= 0x40`, to `159`. -/
theorem iI311 : AtD prof F Wl L s₀ o gev gP gE V₀ g₀ 311 := by
  intro X t V hK hA hV hr hT hd
  have hl : icfi.length = 374 := icfi_length
  refine c.s_or_ri32 hK hA hE.codei (by omega) hr (icfi_311 _) ?_
  rintro Y1 t1 hK1 hA1 ⟨hr1, hg1⟩
  refine c.s_mov_rip_r32 hK1 hA1 hE.codei (by omega) hr1 (icfi_314 _) (g := (0x7a4ae0 : Addr).add 100) (by decide)
    (fun i hi => hE.cf (by omega)) ?_
  rintro Y2 t2 hK2 hA2 ⟨hr2, hg2⟩
  rw [or_edx hd hg1] at hA2
  refine c.s_jmp_x hK2 hA2 hE.codei (by omega) hr2 (icfi_320 _) hE.codei (tgt := 159) (by omega) (by decide) ?_
  rintro Y3 t3 hK3 hA3 ⟨hr3, hg3⟩
  exact iI159 c hE hsp0 k Y3 t3 _ hK3 hA3 (hV.or_f1 hE 64 (by decide)) hr3
    (by rw [hg3, hg2, hg1]; exact hT.set (by omega) _)

/-- `0x6137de`: `feature[1] |= 0x434`, to `280`. -/
theorem iI360 : AtD prof F Wl L s₀ o gev gP gE V₀ g₀ 360 := by
  intro X t V hK hA hV hr hT hd
  have hl : icfi.length = 374 := icfi_length
  refine c.s_or_ri32 hK hA hE.codei (by omega) hr (icfi_360 _) ?_
  rintro Y1 t1 hK1 hA1 ⟨hr1, hg1⟩
  refine c.s_mov_rip_r32 hK1 hA1 hE.codei (by omega) hr1 (icfi_366 _) (g := (0x7a4ae0 : Addr).add 100) (by decide)
    (fun i hi => hE.cf (by omega)) ?_
  rintro Y2 t2 hK2 hA2 ⟨hr2, hg2⟩
  rw [or_edx hd hg1] at hA2
  refine c.s_jmp_x hK2 hA2 hE.codei (by omega) hr2 (icfi_372 _) hE.codei (tgt := 280) (by omega) (by decide) ?_
  rintro Y3 t3 hK3 hA3 ⟨hr3, hg3⟩
  exact iI280 c hE hsp0 k Y3 t3 _ hK3 hA3 (hV.or_f1 hE 1076 (by decide)) hr3
    (by rw [hg3, hg2, hg1]; exact hT.set (by omega) _)

/-- `0x6137d5`: if bit 4 of the byte at offset 11 is set, `360`; else `280`. -/
theorem iI351 : AtD prof F Wl L s₀ o gev gP gE V₀ g₀ 351 := by
  intro X t V hK hA hV hr hT hd
  have hl : icfi.length = 374 := icfi_length
  refine c.s_test_m8i_rip hK hA hE.codei (by omega) hr (icfi_351 _) (g := (0x7a4ae0 : Addr).add 11) (by decide)
    (by have := hE.cfd c (a := 11) (n := 1) (by omega) 0 (by omega); rwa [addr_add_zero] at this) ?_
  rintro Y1 t1 hK1 hA1 ⟨hr1, hg1, -⟩
  refine c.s_jcc hK1 hA1 hE.codei (by omega) hr1 (icfi_358 _) (tgt := 280) (by decide) (by omega)
    (fun _ Y t' hKY hAY ⟨hrY, hgY⟩ => iI280 c hE hsp0 k Y t' _ hKY hAY hV hrY (by rw [hgY, hg1]; exact hT))
    fun _ => ?_
  rintro Y2 t2 hK2 hA2 ⟨hr2, hg2⟩
  exact iI360 c hE hsp0 k Y2 t2 _ hK2 hA2 hV hr2 (by rw [hg2, hg1]; exact hT) (by rw [rv, hg2, hg1]; exact hd)

omit c hE hsp0 k in
theorem cond7_f {m : BitVec 32} {f : Rflags} (h : (subF f m (BitVec.ofNat 32 69)).cond 7 = false) : m.toNat ≤ 69 := by
  have e : ∀ g : Rflags, g.cond 7 = !(g.cf || g.zf) := fun _ => rfl
  rw [e] at h
  simp at h
  by_cases h' : 69 ≤ m.toNat
  · rw [h h']; decide
  · omega

/-- `0x61373e`: family 6: `model += extended model`, and by `model - 0x1a` the jump table at `0x6ee6d0` (to `268`,
`311`, `351`, `360`), or `351` past its end; `edx` the word `feature[1]`. -/
theorem iI200 (hJ : JT F Wl V₀) : AtK prof F Wl L s₀ o gev gP gE V₀ g₀ 0x613676 200 := by
  intro X t V hK hA hV hr hT
  have hl : icfi.length = 374 := icfi_length
  have hsp : X.cpu.gpr.rsp = q.add 8 := by rw [hT.sp, hsp0]
  refine c.s_mov_rm hK hA hE.codei (by omega) hr (Or.inl rfl) (icfi_200 _)
    (fun i hi => by rw [eaD_sp hsp, addr_add_add]; exact c.hws _ (hE.fr (by omega))) ?_
  rintro Y1 t1 hK1 hA1 ⟨hr1, hg1⟩
  have hs1 : Y1.cpu.gpr.rsp = q.add 8 := by rw [hg1]; exact hsp
  refine c.s_add_rm32 hK1 hA1 hE.codei (by omega) hr1 (icfi_204 _)
    (fun i hi => by rw [eaD_sp hs1, addr_add_add]; exact c.hws _ (hE.fr (by omega))) ?_
  rintro Y2 t2 hK2 hA2 ⟨hr2, hg2⟩
  refine c.s_lea32_bd hK2 hA2 hE.codei (by omega) hr2 (icfi_208 _) ?_
  rintro Y3 t3 hK3 hA3 ⟨hr3, hg3⟩
  generalize (eaD Y2 0 18446744073709551590).setWidth 32 = m at hg3
  have hs3 : Y3.cpu.gpr.rsp = q.add 8 := by rw [hg3, hg2]; exact hs1
  have hT3 : TK g₀ Y3.cpu.gpr := by rw [hg3, hg2, hg1]; exact ((hT.set (by omega) _).set (by omega) _).set (by omega) _
  refine c.s_mov_mr hK3 hA3 hE.codei (by omega) hr3 (Or.inl rfl) (icfi_211 _)
    (fun i hi => by rw [eaD_sp hs3, addr_add_add]; exact hE.fr (by omega)) ?_
  rintro Y4 t4 hK4 hA4 ⟨hr4, hg4⟩
  have hV4 : IV prof Wl V₀ (Vst V (eaD Y3 4 48) (toBytesLE (rv Y3 32 0) (32 / 8))) := by
    rw [eaD_sp hs3]; exact hV.fr hE (by simp) (by omega)
  generalize Vst V (eaD Y3 4 48) (toBytesLE (rv Y3 32 0) (32 / 8)) = V4 at hA4 hV4
  refine c.s_mov_r32_rip hK4 hA4 hE.codei (by omega) hr4 (icfi_215 _) (g := (0x7a4ae0 : Addr).add 100) (by decide)
    (hE.cfd c (by omega)) ?_
  rintro Y5 t5 hK5 hA5 ⟨hr5, hg5⟩
  have hd5 : rv Y5 32 2 = rdw V4 100 := by rw [rv, hg5]; simp; rfl
  have hT5 : TK g₀ Y5.cpu.gpr := by rw [hg5, hg4]; exact hT3.set (by omega) _
  refine c.s_cmp_ri32 hK5 hA5 hE.codei (by omega) hr5 (icfi_221 _) ?_
  have hm5 : rv Y5 32 1 = m := by
    rw [rv, hg5, hg4, hg3]
    show (m.setWidth 64).setWidth 32 = m
    rw [BitVec.setWidth_setWidth_of_le _ (by omega), BitVec.setWidth_eq]
  rintro Y6 t6 hK6 hA6 ⟨hr6, hg6, hf6⟩
  refine c.s_jcc hK6 hA6 hE.codei (by omega) hr6 (icfi_224 _) (tgt := 351) (by decide) (by omega)
    (fun _ Y t' hKY hAY ⟨hrY, hgY⟩ => iI351 c hE hsp0 k Y t' _ hKY hAY hV4 hrY (by rw [hgY, hg6]; exact hT5)
      (by rw [rv, hgY, hg6]; exact hd5)) fun hcc => ?_
  rw [hf6, hm5] at hcc
  have hn := cond7_f hcc
  rintro Y7 t7 hK7 hA7 ⟨hr7, hg7⟩
  refine c.s_lea_rip hK7 hA7 hE.codei (by omega) hr7 (icfi_226 _) (v := 0x6ee6d0) (by decide) ?_
  rintro Y8 t8 hK8 hA8 ⟨hr8, hg8, -⟩
  have hc8 : Y8.cpu.gpr.get (regOf 1) = m.setWidth 64 := by
    rw [hg8, hg7, hg6, hg5, hg4, hg3]; rfl
  have he : ∀ i, (eaS Y8 (some 6) 1 4 0).add i = (0x6ee6d0 : Addr).add (4 * m.toNat + i) := by
    intro i
    have h := jt_addr (m.setWidth 64) i
    rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by have := m.isLt; omega)] at h
    rw [← h, eaS, baseV, hc8, show Y8.cpu.gpr.get (regOf 6) = 0x6ee6d0 by rw [hg8]; rfl]
  refine c.s_movsxd_si hK8 hA8 hE.codei (by omega) hr8 (icfi_233 _)
    (fun i hi => by rw [he]; exact hJ.data _ (by omega)) ?_
  rintro Y9 t9 hK9 hA9 ⟨hr9, hg9⟩
  have hm : (byteAddrs (eaS Y8 (some 6) 1 4 0) 4).map V4 =
      (List.range 4).map fun i => jtab.getD (4 * m.toNat + i) 0 := by
    simp only [byteAddrs, List.map_map]
    refine List.map_congr_left fun i hi => ?_
    simp only [List.mem_range] at hi
    show V4 ((eaS Y8 (some 6) 1 4 0).add i) = _
    rw [he, hV4.off _ (hJ.nw _ (by omega)), hJ.val _ (by omega)]
  refine c.s_add_rr64 hK9 hA9 hE.codei (by omega) hr9 (icfi_237 _) ?_
  rintro Y10 t10 hK10 hA10 ⟨hr10, hg10⟩
  have hj10 : Y10.cpu.gpr.get (regOf 1) = jtgt m.toNat := by
    rw [hg10, show rv Y9 64 1 = (ofBytesLE 32 ((byteAddrs (eaS Y8 (some 6) 1 4 0) 4).map V4)).signExtend 64 by
        rw [rv, hg9]; simp,
      show rv Y9 64 6 = 0x6ee6d0 by rw [rv, hg9, hg8]; rfl, hm]
    simp [jtgt, addR]
  have hT10 : TK g₀ Y10.cpu.gpr := by
    rw [hg10, hg9, hg8, hg7, hg6]; exact ((hT5.set (by omega) _).set (by omega) _).set (by omega) _
  have hd10 : rv Y10 32 2 = rdw V4 100 := by rw [rv, hg10, hg9, hg8, hg7, hg6]; exact hd5
  have go : ∀ tgt, tgt < 374 → jtgt m.toNat = (0x613676 : Addr).add tgt →
      AtD prof F Wl L s₀ o gev gP gE V₀ g₀ tgt → GoG prof L o gev gP gE Y10 t10 := fun tgt ht hj hD =>
    c.s_jmp_rx hK10 hA10 hE.codei (by omega) hr10 (icfi_240 _) hE.codei (by rw [hl]; exact ht) (hj10.trans hj)
      fun Z tZ hKZ hAZ ⟨hrZ, hgZ⟩ => hD Z tZ _ hKZ hAZ hV4 hrZ (by rw [hgZ]; exact hT10)
        (by rw [rv, hgZ]; exact hd10)
  rcases jtgt_cases m.toNat (by omega) with h | h | h | h
  · exact go 268 (by omega) h (iI268 c hE hsp0 k)
  · exact go 311 (by omega) h (iI311 c hE hsp0 k)
  · exact go 351 (by omega) h (iI351 c hE hsp0 k)
  · exact go 360 (by omega) h (iI360 c hE hsp0 k)

/-- `0x61370e`: family 6 to `200`, else `159`. -/
theorem iI152 (hJ : JT F Wl V₀) : AtK prof F Wl L s₀ o gev gP gE V₀ g₀ 0x613676 152 := by
  intro X t V hK hA hV hr hT
  have hl : icfi.length = 374 := icfi_length
  have hsp : X.cpu.gpr.rsp = q.add 8 := by rw [hT.sp, hsp0]
  refine c.s_cmp_m32i hK hA hE.codei (by omega) hr (icfi_152 _)
    (fun i hi => by rw [eaD_sp hsp, addr_add_add]; exact c.hws _ (hE.fr (by omega))) ?_
  rintro Y1 t1 hK1 hA1 ⟨hr1, hg1⟩
  rw [← hg1] at hT
  refine c.s_jcc hK1 hA1 hE.codei (by omega) hr1 (icfi_157 _) (tgt := 200) (by decide) (by omega)
    (fun _ Y t' hKY hAY ⟨hrY, hgY⟩ => iI200 c hE hsp0 k hJ Y t' _ hKY hAY hV hrY (by rw [hgY]; exact hT)) fun _ => ?_
  rintro Y2 t2 hK2 hA2 ⟨hr2, hg2⟩
  exact iI159 c hE hsp0 k Y2 t2 _ hK2 hA2 hV hr2 (by rw [hg2]; exact hT)

end K

section R
variable (c : Seg prof F Wl L s₀ o) {V₀ : Addr → Byte} {q : Addr} (hE : IE F Wl L V₀ q) {g₀ : Gprs}
  (hsp0 : g₀.rsp = q.add 8) (kr : KR prof F Wl L s₀ o gev gP gE V₀ g₀)
  (hpc : prof.Consistent) (hdf : s₀.cpu.rflags.df = false) (hx87 : s₀.cpu.x87.full = 0)
include c hE hsp0 kr hpc hdf hx87

/-- `0x613676`: `get_common_indices` with the family, model, extended model and stepping in the frame, the extended
leaves, to `0x61370e`. -/
theorem iI0 (hJ : JT F Wl V₀) : AtR prof F Wl L s₀ o gev gP gE V₀ g₀ 0x613676 0 := by
  intro X t V hK hA hV hr hT
  have hl : icfi.length = 374 := icfi_length
  have a152 : AtR prof F Wl L s₀ o gev gP gE V₀ g₀ 0x613676 152 := AtR.go hsp0 kr fun g hs kg => iI152 c hE hs kg hJ
  have hsp : X.cpu.gpr.rsp = q.add 8 := by rw [hT.sp, hsp0]
  refine c.s_lea_bd hK hA hE.codei (by omega) hr (icfi_0 _) ?_
  rintro Y1 t1 hK1 hA1 ⟨hr1, hg1⟩
  refine c.s_lea_bd hK1 hA1 hE.codei (by omega) hr1 (icfi_5 _) ?_
  rintro Y2 t2 hK2 hA2 ⟨hr2, hg2⟩
  refine c.s_lea_bd hK2 hA2 hE.codei (by omega) hr2 (icfi_10 _) ?_
  rintro Y3 t3 hK3 hA3 ⟨hr3, hg3⟩
  refine c.s_lea_bd hK3 hA3 hE.codei (by omega) hr3 (icfi_15 _) ?_
  rintro Y4 t4 hK4 hA4 ⟨hr4, hg4⟩
  have hT4 : TKr g₀ Y4.cpu.gpr := by
    rw [hg4, hg3, hg2, hg1]
    exact (((hT.set (by omega) _).set (by omega) _).set (by omega) _).set (by omega) _
  have hs1 : Y1.cpu.gpr.rsp = q.add 8 := by rw [hg1]; exact hsp
  have hs2 : Y2.cpu.gpr.rsp = q.add 8 := by rw [hg2]; exact hs1
  have hs3 : Y3.cpu.gpr.rsp = q.add 8 := by rw [hg3]; exact hs2
  have hs4 : Y4.cpu.gpr.rsp = q.add 8 := by rw [hg4]; exact hs3
  have pi : ∀ m, 52 ≤ m → m + 4 ≤ 0x80 → PI q (q.add m) := fun m h1 h2 => ⟨m, h1, h2, rfl⟩
  refine callG c hE hpc hdf hx87 hK4 hA4 hV hE.codei (by omega) hr4 (icfi_20 _) (by omega) (by decide)
    (by cases prof.feat.la57 <;> decide) hs4 (fun _ => ?_) fun V' hV' Z t' hKZ hAZ hrZ hTZ => ?_
  · rw [hg4]
    simp only [set_rdi, set_rsi, set_rdx, set_rcx]
    rw [hg3, hg2, hg1]
    simp only [set_rdi, set_rsi, set_rdx, set_rcx, set_rax]
    rw [eaD_sp hs3, eaD_sp hs2, eaD_sp hs1, eaD_sp hsp]
    exact ⟨pi _ (by omega) (by omega), pi _ (by omega) (by omega), pi _ (by omega) (by omega),
      pi _ (by omega) (by omega)⟩
  have hTZ' : TKr g₀ Z.cpu.gpr := hT4.tk hTZ
  have st : ∀ {V : Addr → Byte} {a : Nat}, IV prof Wl V₀ V → a + 4 ≤ 0xa8 → 28 ≤ a → a + 4 ≤ 96 → ∀ v : BitVec 32,
      IV prof Wl V₀ (Vst V ((0x7a4ae0 : Addr).add a) (toBytesLE v 4)) := fun hV h1 h2 h3 v =>
    hV.stw hE h1 (fun b hb => by rcases hb with rfl | rfl | rfl | rfl | rfl | rfl <;> omega) v
  have j152 : ∀ (Y : State) (t' : Nat) (V : Addr → Byte), KeptW Wl s₀ Y → Agree F Y.proc.mm.mem V →
      IV prof Wl V₀ V → TKr g₀ Y.cpu.gpr → ∀ (Y' : State), Y'.cpu.gpr = Y.cpu.gpr → ∀ t'' , KeptW Wl s₀ Y' →
      Agree F Y'.proc.mm.mem V → Y'.cpu.rip = (0x613676 : Addr).add 152 → GoG prof L o gev gP gE Y' t'' :=
    fun _ _ _ _ _ hV hT Y' hg t'' hK hA hr => a152 Y' t'' _ hK hA hV hr (by rw [hg]; exact hT)
  refine c.s_mov_ri32 hKZ hAZ hE.codei (by omega) hrZ (icfi_25 _) ?_
  rintro Y11 t11 hK11 hA11 ⟨hr11, hg11⟩
  have hT11 : TKr g₀ Y11.cpu.gpr := by rw [hg11]; exact hTZ'.set (by omega) _
  refine c.s_mov_rr32 hK11 hA11 hE.codei (by omega) hr11 (icfi_30 _) ?_
  rintro Y12 t12 hK12 hA12 ⟨hr12, hg12⟩
  have hT12 : TKr g₀ Y12.cpu.gpr := by rw [hg12]; exact hT11.set (by omega) _
  refine c.s_cpuid hK12 hA12 hE.codei (by omega) hr12 (icfi_32 _) ?_
  rintro Y13 t13 hK13 hA13 ⟨hr13, _, -, hg13⟩
  have hT13 : TKr g₀ Y13.cpu.gpr := by rw [hg13]; exact hT12.cpuid _ _ _ _
  refine c.s_mov_rr32 hK13 hA13 hE.codei (by omega) hr13 (icfi_34 _) ?_
  rintro Y14 t14 hK14 hA14 ⟨hr14, hg14⟩
  have hT14 : TKr g₀ Y14.cpu.gpr := by rw [hg14]; exact hT13.set (by omega) _
  refine c.s_fl hK14 hA14 hE.codei (by omega) hr14 fl_cmp_ri32 (icfi_36 _) ?_
  rintro Y15 t15 hK15 hA15 ⟨hr15, hg15⟩
  replace hr15 : Y15.cpu.rip = (0x613676 : Addr).add 41 := hr15
  have hT15 : TKr g₀ Y15.cpu.gpr := by rw [hg15]; exact hT14
  refine c.s_jcc hK15 hA15 hE.codei (by omega) hr15 (icfi_41 _) (tgt := 152) (by decide) (by omega)
    (fun _ Y t' hKY hAY ⟨hrY, hgY⟩ => j152 Y15 0 _ hK15 hA15 hV' hT15 Y hgY t' hKY hAY hrY) fun _ => ?_
  rintro Y16 t16 hK16 hA16 ⟨hr16, hg16⟩
  have hT16 : TKr g₀ Y16.cpu.gpr := by rw [hg16]; exact hT15
  refine c.s_mov_ri32 hK16 hA16 hE.codei (by omega) hr16 (icfi_43 _) ?_
  rintro Y17 t17 hK17 hA17 ⟨hr17, hg17⟩
  have hT17 : TKr g₀ Y17.cpu.gpr := by rw [hg17]; exact hT16.set (by omega) _
  refine c.s_cpuid hK17 hA17 hE.codei (by omega) hr17 (icfi_48 _) ?_
  rintro Y18 t18 hK18 hA18 ⟨hr18, _, -, hg18⟩
  have hT18 : TKr g₀ Y18.cpu.gpr := by rw [hg18]; exact hT17.cpuid _ _ _ _
  refine c.s_mov_rip_r32 hK18 hA18 hE.codei (by omega) hr18 (icfi_50 _) (g := (0x7a4ae0 : Addr).add 32) (by decide)
    (fun i hi => hE.cf (by omega)) ?_
  rintro Y19 t19 hK19 hA19 ⟨hr19, hg19⟩
  have hT19 : TKr g₀ Y19.cpu.gpr := by rw [hg19]; exact hT18
  have hV19 := st hV' (a := 32) (by omega) (by omega) (by omega) (rv Y18 32 0)
  refine c.s_mov_rip_r32 hK19 hA19 hE.codei (by omega) hr19 (icfi_56 _) (g := (0x7a4ae0 : Addr).add 36) (by decide)
    (fun i hi => hE.cf (by omega)) ?_
  rintro Y20 t20 hK20 hA20 ⟨hr20, hg20⟩
  have hT20 : TKr g₀ Y20.cpu.gpr := by rw [hg20]; exact hT19
  have hV20 := st hV19 (a := 36) (by omega) (by omega) (by omega) (rv Y19 32 3)
  refine c.s_mov_rip_r32 hK20 hA20 hE.codei (by omega) hr20 (icfi_62 _) (g := (0x7a4ae0 : Addr).add 40) (by decide)
    (fun i hi => hE.cf (by omega)) ?_
  rintro Y21 t21 hK21 hA21 ⟨hr21, hg21⟩
  have hT21 : TKr g₀ Y21.cpu.gpr := by rw [hg21]; exact hT20
  have hV21 := st hV20 (a := 40) (by omega) (by omega) (by omega) (rv Y20 32 1)
  refine c.s_mov_rip_r32 hK21 hA21 hE.codei (by omega) hr21 (icfi_68 _) (g := (0x7a4ae0 : Addr).add 44) (by decide)
    (fun i hi => hE.cf (by omega)) ?_
  rintro Y22 t22 hK22 hA22 ⟨hr22, hg22⟩
  have hT22 : TKr g₀ Y22.cpu.gpr := by rw [hg22]; exact hT21
  have hV22 := st hV21 (a := 44) (by omega) (by omega) (by omega) (rv Y21 32 2)
  refine c.s_fl hK22 hA22 hE.codei (by omega) hr22 fl_cmp_ri32 (icfi_74 _) ?_
  rintro Y23 t23 hK23 hA23 ⟨hr23, hg23⟩
  replace hr23 : Y23.cpu.rip = (0x613676 : Addr).add 80 := hr23
  have hT23 : TKr g₀ Y23.cpu.gpr := by rw [hg23]; exact hT22
  refine c.s_jcc hK23 hA23 hE.codei (by omega) hr23 (icfi_80 _) (tgt := 152) (by decide) (by omega)
    (fun _ Y t' hKY hAY ⟨hrY, hgY⟩ => j152 Y23 0 _ hK23 hA23 hV22 hT23 Y hgY t' hKY hAY hrY) fun _ => ?_
  rintro Y24 t24 hK24 hA24 ⟨hr24, hg24⟩
  have hT24 : TKr g₀ Y24.cpu.gpr := by rw [hg24]; exact hT23
  refine c.s_mov_ri32 hK24 hA24 hE.codei (by omega) hr24 (icfi_82 _) ?_
  rintro Y25 t25 hK25 hA25 ⟨hr25, hg25⟩
  have hT25 : TKr g₀ Y25.cpu.gpr := by rw [hg25]; exact hT24.set (by omega) _
  refine c.s_cpuid hK25 hA25 hE.codei (by omega) hr25 (icfi_87 _) ?_
  rintro Y26 t26 hK26 hA26 ⟨hr26, _, -, hg26⟩
  have hT26 : TKr g₀ Y26.cpu.gpr := by rw [hg26]; exact hT25.cpuid _ _ _ _
  refine c.s_mov_rip_r32 hK26 hA26 hE.codei (by omega) hr26 (icfi_89 _) (g := (0x7a4ae0 : Addr).add 64) (by decide)
    (fun i hi => hE.cf (by omega)) ?_
  rintro Y27 t27 hK27 hA27 ⟨hr27, hg27⟩
  have hT27 : TKr g₀ Y27.cpu.gpr := by rw [hg27]; exact hT26
  have hV27 := st hV22 (a := 64) (by omega) (by omega) (by omega) (rv Y26 32 0)
  refine c.s_mov_rip_r32 hK27 hA27 hE.codei (by omega) hr27 (icfi_95 _) (g := (0x7a4ae0 : Addr).add 68) (by decide)
    (fun i hi => hE.cf (by omega)) ?_
  rintro Y28 t28 hK28 hA28 ⟨hr28, hg28⟩
  have hT28 : TKr g₀ Y28.cpu.gpr := by rw [hg28]; exact hT27
  have hV28 := st hV27 (a := 68) (by omega) (by omega) (by omega) (rv Y27 32 3)
  refine c.s_mov_rip_r32 hK28 hA28 hE.codei (by omega) hr28 (icfi_101 _) (g := (0x7a4ae0 : Addr).add 72) (by decide)
    (fun i hi => hE.cf (by omega)) ?_
  rintro Y29 t29 hK29 hA29 ⟨hr29, hg29⟩
  have hT29 : TKr g₀ Y29.cpu.gpr := by rw [hg29]; exact hT28
  have hV29 := st hV28 (a := 72) (by omega) (by omega) (by omega) (rv Y28 32 1)
  refine c.s_mov_rip_r32 hK29 hA29 hE.codei (by omega) hr29 (icfi_107 _) (g := (0x7a4ae0 : Addr).add 76) (by decide)
    (fun i hi => hE.cf (by omega)) ?_
  rintro Y30 t30 hK30 hA30 ⟨hr30, hg30⟩
  have hT30 : TKr g₀ Y30.cpu.gpr := by rw [hg30]; exact hT29
  have hV30 := st hV29 (a := 76) (by omega) (by omega) (by omega) (rv Y29 32 2)
  refine c.s_fl hK30 hA30 hE.codei (by omega) hr30 fl_cmp_ri32 (icfi_113 _) ?_
  rintro Y31 t31 hK31 hA31 ⟨hr31, hg31⟩
  replace hr31 : Y31.cpu.rip = (0x613676 : Addr).add 119 := hr31
  have hT31 : TKr g₀ Y31.cpu.gpr := by rw [hg31]; exact hT30
  refine c.s_jcc hK31 hA31 hE.codei (by omega) hr31 (icfi_119 _) (tgt := 152) (by decide) (by omega)
    (fun _ Y t' hKY hAY ⟨hrY, hgY⟩ => j152 Y31 0 _ hK31 hA31 hV30 hT31 Y hgY t' hKY hAY hrY) fun _ => ?_
  rintro Y32 t32 hK32 hA32 ⟨hr32, hg32⟩
  have hT32 : TKr g₀ Y32.cpu.gpr := by rw [hg32]; exact hT31
  refine c.s_mov_ri32 hK32 hA32 hE.codei (by omega) hr32 (icfi_121 _) ?_
  rintro Y33 t33 hK33 hA33 ⟨hr33, hg33⟩
  have hT33 : TKr g₀ Y33.cpu.gpr := by rw [hg33]; exact hT32.set (by omega) _
  refine c.s_cpuid hK33 hA33 hE.codei (by omega) hr33 (icfi_126 _) ?_
  rintro Y34 t34 hK34 hA34 ⟨hr34, _, -, hg34⟩
  have hT34 : TKr g₀ Y34.cpu.gpr := by rw [hg34]; exact hT33.cpuid _ _ _ _
  refine c.s_mov_rip_r32 hK34 hA34 hE.codei (by omega) hr34 (icfi_128 _) (g := (0x7a4ae0 : Addr).add 80) (by decide)
    (fun i hi => hE.cf (by omega)) ?_
  rintro Y35 t35 hK35 hA35 ⟨hr35, hg35⟩
  have hT35 : TKr g₀ Y35.cpu.gpr := by rw [hg35]; exact hT34
  have hV35 := st hV30 (a := 80) (by omega) (by omega) (by omega) (rv Y34 32 0)
  refine c.s_mov_rip_r32 hK35 hA35 hE.codei (by omega) hr35 (icfi_134 _) (g := (0x7a4ae0 : Addr).add 84) (by decide)
    (fun i hi => hE.cf (by omega)) ?_
  rintro Y36 t36 hK36 hA36 ⟨hr36, hg36⟩
  have hT36 : TKr g₀ Y36.cpu.gpr := by rw [hg36]; exact hT35
  have hV36 := st hV35 (a := 84) (by omega) (by omega) (by omega) (rv Y35 32 3)
  refine c.s_mov_rip_r32 hK36 hA36 hE.codei (by omega) hr36 (icfi_140 _) (g := (0x7a4ae0 : Addr).add 88) (by decide)
    (fun i hi => hE.cf (by omega)) ?_
  rintro Y37 t37 hK37 hA37 ⟨hr37, hg37⟩
  have hT37 : TKr g₀ Y37.cpu.gpr := by rw [hg37]; exact hT36
  have hV37 := st hV36 (a := 88) (by omega) (by omega) (by omega) (rv Y36 32 1)
  refine c.s_mov_rip_r32 hK37 hA37 hE.codei (by omega) hr37 (icfi_146 _) (g := (0x7a4ae0 : Addr).add 92) (by decide)
    (fun i hi => hE.cf (by omega)) ?_
  rintro Y38 t38 hK38 hA38 ⟨hr38, hg38⟩
  have hT38 : TKr g₀ Y38.cpu.gpr := by rw [hg38]; exact hT37
  have hV38 := st hV37 (a := 92) (by omega) (by omega) (by omega) (rv Y37 32 2)
  exact a152 Y38 _ _ hK38 hA38 hV38 hr38 hT38

/-- `0x613113`: family, model and extended model zero in the frame, leaf 0 (`max_cpuid` at offset 108), and by the
vendor's name to Intel's part (`0x613676`), AMD's or Hygon's (`0x6132ad`), or any other vendor's (`0x613159`). -/
theorem iC0 (hJ : JT F Wl V₀) : AtR prof F Wl L s₀ o gev gP gE V₀ g₀ 0x613113 0 := by
  intro X t V hK hA hV hr hT
  have hl : icf.length = 357 := icf_length
  have hsp : X.cpu.gpr.rsp = q.add 8 := by rw [hT.sp, hsp0]
  have a0 := iA0 c hE hsp0 kr hpc hdf hx87
  refine c.s_mov_mi32 hK hA hE.code (by omega) hr (icf_0 _)
    (fun i hi => by rw [eaD_sp hsp, addr_add_add]; exact hE.fr (by omega)) ?_
  rintro Y1 t1 hK1 hA1 ⟨hr1, hg1⟩
  have hV1 : IV prof Wl V₀ (Vst V (eaD X 4 44) (toBytesLE (BitVec.ofNat 32 0) 4)) := by
    rw [eaD_sp hsp]; exact hV.fr hE (by simp) (by omega)
  generalize Vst V (eaD X 4 44) (toBytesLE (BitVec.ofNat 32 0) 4) = V1 at hA1 hV1
  refine c.s_xor_rr32 hK1 hA1 hE.code (by omega) hr1 (icf_8 _) ?_
  rintro Y2 t2 hK2 hA2 ⟨hr2, hg2⟩
  have hs2 : Y2.cpu.gpr.rsp = q.add 8 := by rw [hg2, hg1]; exact hsp
  refine c.s_mov_mi32 hK2 hA2 hE.code (by omega) hr2 (icf_10 _)
    (fun i hi => by rw [eaD_sp hs2, addr_add_add]; exact hE.fr (by omega)) ?_
  rintro Y3 t3 hK3 hA3 ⟨hr3, hg3⟩
  have hV3 : IV prof Wl V₀ (Vst V1 (eaD Y2 4 48) (toBytesLE (BitVec.ofNat 32 0) 4)) := by
    rw [eaD_sp hs2]; exact hV1.fr hE (by simp) (by omega)
  generalize Vst V1 (eaD Y2 4 48) (toBytesLE (BitVec.ofNat 32 0) 4) = V3 at hA3 hV3
  have hs3 : Y3.cpu.gpr.rsp = q.add 8 := by rw [hg3]; exact hs2
  refine c.s_mov_mi32 hK3 hA3 hE.code (by omega) hr3 (icf_18 _)
    (fun i hi => by rw [eaD_sp hs3, addr_add_add]; exact hE.fr (by omega)) ?_
  rintro Y4 t4 hK4 hA4 ⟨hr4, hg4⟩
  have hV4 : IV prof Wl V₀ (Vst V3 (eaD Y3 4 52) (toBytesLE (BitVec.ofNat 32 0) 4)) := by
    rw [eaD_sp hs3]; exact hV3.fr hE (by simp) (by omega)
  generalize Vst V3 (eaD Y3 4 52) (toBytesLE (BitVec.ofNat 32 0) 4) = V4 at hA4 hV4
  have hT4 : TKr g₀ Y4.cpu.gpr := by rw [hg4, hg3, hg2, hg1]; exact hT.set (by omega) _
  refine c.s_cpuid hK4 hA4 hE.code (by omega) hr4 (icf_26 _) ?_
  rintro Y5 t5 hK5 hA5 ⟨hr5, _, -, hg5⟩
  have hT5 : TKr g₀ Y5.cpu.gpr := by rw [hg5]; exact hT4.cpuid _ _ _ _
  refine c.s_mov_rip_r32 hK5 hA5 hE.code (by omega) hr5 (icf_28 _) (g := (0x7a4ae0 : Addr).add 108) (by decide)
    (fun i hi => hE.cf (by omega)) ?_
  rintro Y6 t6 hK6 hA6 ⟨hr6, hg6⟩
  have hV6 := IV.stcf hE hV4 (a := 108) (bs := toBytesLE (rv Y5 32 0) 4) (by omega) (by simp) (by omega)
  have hT6 : TKr g₀ Y6.cpu.gpr := by rw [hg6]; exact hT5
  refine c.s_fl hK6 hA6 hE.code (by omega) hr6 fl_cmp_ri32 (icf_34 _) ?_
  rintro Y7 t7 hK7 hA7 ⟨hr7, hg7⟩
  replace hr7 : Y7.cpu.rip = (0x613113 : Addr).add 40 := hr7
  rw [← hg7] at hT6
  refine c.s_jcc_x hK7 hA7 hE.code (by omega) hr7 (icf_40 _) hE.codea (tgt := 0) (by rw [icfa_length]; omega)
    (by decide) (fun _ Y t' hKY hAY ⟨hrY, hgY⟩ => a0 Y t' _ hKY hAY hV6 hrY (by rw [hgY]; exact hT6)) fun _ => ?_
  rintro Y8 t8 hK8 hA8 ⟨hr8, hg8⟩
  rw [← hg8] at hT6
  refine c.s_fl hK8 hA8 hE.code (by omega) hr8 fl_cmp_ri32 (icf_46 _) ?_
  rintro Y9 t9 hK9 hA9 ⟨hr9, hg9⟩
  replace hr9 : Y9.cpu.rip = (0x613113 : Addr).add 52 := hr9
  rw [← hg9] at hT6
  refine c.s_jcc_x hK9 hA9 hE.code (by omega) hr9 (icf_52 _) hE.codea (tgt := 0) (by rw [icfa_length]; omega)
    (by decide) (fun _ Y t' hKY hAY ⟨hrY, hgY⟩ => a0 Y t' _ hKY hAY hV6 hrY (by rw [hgY]; exact hT6)) fun _ => ?_
  rintro Y10 t10 hK10 hA10 ⟨hr10, hg10⟩
  rw [← hg10] at hT6
  refine c.s_fl hK10 hA10 hE.code (by omega) hr10 fl_cmp_ri32 (icf_58 _) ?_
  rintro Y11 t11 hK11 hA11 ⟨hr11, hg11⟩
  replace hr11 : Y11.cpu.rip = (0x613113 : Addr).add 64 := hr11
  rw [← hg11] at hT6
  refine c.s_jcc_x hK11 hA11 hE.code (by omega) hr11 (icf_64 _) hE.codei (tgt := 0) (by rw [icfi_length]; omega)
    (by decide) (fun _ Y t' hKY hAY ⟨hrY, hgY⟩ => iI0 c hE hsp0 kr hpc hdf hx87 hJ Y t' _ hKY hAY hV6 hrY
      (by rw [hgY]; exact hT6)) fun _ => ?_
  rintro Y12 t12 hK12 hA12 ⟨hr12, hg12⟩
  exact AtR.go hsp0 kr (fun g hs kg => iO c hE hs kg hpc hdf hx87) Y12 t12 _ hK12 hA12 hV6 hr12
    (by rw [hg12]; exact hT6)

end R

/-- glibc's `init_cpu_features`, inlined in `__libc_start_main`, from `0x613113` to `0x613278`, for every vendor and every
answer of `cpuid` the profile allows: the one syscall is `arch_prctl (ARCH_CET_STATUS, …)`; at `0x613278`, `CpuOk`,
`rsp` and the callee-saved registers but `rbx` as they were, and off what the run may store into the footprint's bytes
as at the start. -/
theorem initCpuFeatures (c : Seg prof F Wl L s₀ o) {V₀ : Addr → Byte} {q : Addr} (hE : IE F Wl L V₀ q)
    (hJ : JT F Wl V₀) (hpc : prof.Consistent) (hdf : s₀.cpu.rflags.df = false) (hx87 : s₀.cpu.x87.full = 0)
    {X : State} {t : Nat} (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V₀) (hok : CInv prof V₀)
    (hr : X.cpu.rip = 0x613113) (hsp : X.cpu.gpr.rsp = q.add 8)
    (post : ∀ (g : Gprs) (Y : State) (t' : Nat), g.rax = BitVec.ofNat 64 158 → g.rdi = BitVec.ofNat 64 0x3001 →
      KeptW Wl s₀ Y → CpuOk prof Y.proc.mm.mem →
      (∀ y, Foot F.data y → ¬ Foot Wl y → Y.proc.mm.mem.readByte y = V₀ y) →
      Y.cpu.rip = 0x613278 → TKr X.cpu.gpr Y.cpu.gpr → GoG prof L o (gev ++ [Seg.cetEv g]) gP gE Y t') :
    GoG prof L o gev gP gE X t := by
  have kr : KR prof F Wl L s₀ o gev gP gE V₀ X.cpu.gpr := fun g hg g' V Y t' hax hdi hKY hAY hVY hrY hTY =>
    post g' Y t' hax hdi hKY
      (hVY.inv.mem fun j hj => hAY _ (by
        have h := hE.cf (a := 0) (i := j) (by omega); rw [addr_add_zero] at h; exact c.hws _ h))
      (fun y hy hw => (hAY y hy).trans (hVY.off y hw)) (by rw [hrY]; decide) (hg.tk hTY)
  exact iC0 c hE hsp kr hpc hdf hx87 hJ X t V₀ hK hA ⟨hok, fun _ _ => rfl⟩ (by rw [hr]; decide) (TK.refl _).r

end FV7z.CpuFeat
