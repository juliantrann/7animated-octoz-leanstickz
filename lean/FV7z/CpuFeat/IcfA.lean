import FV7z.CpuFeat.Icf
/-!
# `init_cpu_features`: AMD's and Hygon's part (PLAN.md G2, glibc `init_cpu_features`)

From `0x6132ad`, where the vendor string is not Intel's: `AuthenticAMD` or `HygonGenuine` (`0x613803`) run
`get_common_indices` with the four pointers into the frame, the extended leaves `0x80000000`–`0x80000008` stored apart
from the words `CInv` watches, `feature[0] |= 1 << 18` (`Prefer_FSRM`? a bit `CpuOk` does not watch) if `XOP`-ish bits
are set, and for family `0x15` with model `0x60`–`0x7f` `feature[1]` with bit 8 (`AVX_Fast_Unaligned_Load`) cleared
(`0x613830`), then `eax = 2` and the common part at `88` (`iT1`). Any other vendor goes to `0x613159` (`iO`).
-/
namespace FV7z.CpuFeat
open ZellicX86 Decode FV7z.Leaf FV7z.Fn FV7z.Prepare Glibc

set_option linter.deprecated false

/-! ## Stores -/

section
variable {prof : Profile}

/-- `feature[0] |= 1 << 18`: a bit `CpuOk` does not watch. -/
theorem CInv.or_f0_18 {V : Addr → Byte} (h : CInv prof V) :
    CInv prof (Vst V (cpuRgn.base.add 96) (toBytesLE (rdw V 96 ||| BitVec.ofNat 32 0x40000) 4)) :=
  h.st_f0_or _ (fun i => (BitVec.ofNat 32 0x40000).getLsbD i) (fun i hi => getLsbD_rd_or _ hi)
    (fun h => absurd h (by decide)) (fun h => absurd h (by decide)) (fun h => absurd h (by decide))
    (fun h => absurd h (by decide)) (fun h => absurd h (by decide)) (fun h => absurd h (by decide))
    (fun h => absurd h (by decide)) (fun h => absurd h (by decide))

/-- `feature[1]` without bit 8 (`AVX_Fast_Unaligned_Load`). -/
theorem CInv.f1_nb8 {V : Addr → Byte} (h : CInv prof V) (w : BitVec 32) (h8 : w.getLsbD 8 = false) :
    CInv prof (Vst V (cpuRgn.base.add 100) (toBytesLE w 4)) :=
  h.st_f1 w ⟨h.f.avx, h.f.avx2, h.f.avx512f, h.f.avx512vl, h.f.avx512dq, h.f.avx512bw, h.f.fma, h.f.vaes,
    fun hb => absurd hb (by rw [h8]; simp)⟩

end

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle} {F : Footprint} {Wl : List Rgn}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}

/-- A word of `_dl_x86_cpu_features` apart from the watched ones. -/
theorem IV.stw {V₀ V : Addr → Byte} {q : Addr} (hE : IE F Wl L V₀ q) (hV : IV prof Wl V₀ V) {a : Nat}
    (ha : a + 4 ≤ 0xa8) (hw : ∀ b, Watched b → b + 4 ≤ a ∨ a + 4 ≤ b) (v : BitVec 32) :
    IV prof Wl V₀ (Vst V ((0x7a4ae0 : Addr).add a) (toBytesLE v 4)) := by
  have e : ((0x7a4ae0 : Addr).add a).toNat = 0x7a4ae0 + a := CpuFeat.tn (by rw [base_toNat]; omega)
  refine hV.st (fun i hi => hE.cf (by simp at hi; omega))
    (hV.inv.st_apart _ _ (by rw [toBytesLE_length, e]; omega) fun b hb => ?_)
  rw [toBytesLE_length, e]
  rcases hw b hb with h | h <;> omega

theorem wr_sub_ri32 {r imm len : Nat} : WR prof (mk .sub 32 [gr 32 r, .imm 32 imm] len) r :=
  fun _ _ _ htf hdec => ⟨_, _, _, instruction_next htf hdec rfl, rfl, rfl, rfl⟩

/-- `and r8h, imm8` (`ah`, …), with its value. -/
theorem _root_.FV7z.Fn.Seg.s_and_h8i {X : State} {t j : Nat} {e' : Addr} {code : List Byte} {V : Addr → Byte}
    (c : Seg prof F Wl L s₀ o) (hK : KeptW Wl s₀ X)
    (hA : Agree F X.proc.mm.mem V) (hin : CodeIn L e' code) (hj : j < code.length)
    (hrip : X.cpu.rip = e'.add j) {r imm len : Nat}
    (hd : Dec prof.feat code j (FV7z.mk .and 8 [gh r, .imm 8 imm] len))
    (k' : ContG prof F Wl L s₀ o gev gP gE V fun Y => Y.cpu.rip = e'.add (j + len) ∧
      Y.cpu.gpr = X.cpu.gpr.set (regOf r) ((X.cpu.gpr.get (regOf r) &&& ~~~(BitVec.ofNat 64 ((2 ^ 8 - 1) * 2 ^ 8))) |||
        (((X.cpu.gpr.get (regOf r) >>> 8).setWidth 8 &&& BitVec.ofNat 8 imm).setWidth 64 <<< 8))) :
    GoG prof L o gev gP gE X t :=
  c.next hK hA hin hj hrip (fun M hK' hA' htf _ => by
    obtain ⟨af, t', hr⟩ := and_h8i (s := X.withMem M) (o := o) (t := t + 1) (r := r) (imm := imm) htf
      (c.dec hK' hin hrip hd)
    exact ⟨_, _, hr, hK'.nx rfl rfl rfl, hA', rip_add hrip M len, rfl⟩) k'

/-- After `and ah, 0xfe` and `or eax, 24`: bit 8 is clear. -/
theorem nb8 (x : BitVec 64) :
    (((((x &&& ~~~(BitVec.ofNat 64 ((2 ^ 8 - 1) * 2 ^ 8))) |||
      (((x >>> 8).setWidth 8 &&& BitVec.ofNat 8 0xfe).setWidth 64 <<< 8)).setWidth 32 |||
      BitVec.ofNat 32 24).setWidth 64).setWidth 32).getLsbD 8 = false := by
  simp only [BitVec.getLsbD_or, BitVec.getLsbD_setWidth, BitVec.getLsbD_and, BitVec.getLsbD_not,
    BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ofNat, BitVec.getLsbD_ushiftRight]
  simp only [Nat.reduceLT, decide_true, Bool.true_and, Bool.and_true, Bool.or_eq_false_iff, Bool.and_eq_false_imp]
  simp
  exact ⟨fun _ => by decide, by decide⟩

section K
variable (c : Seg prof F Wl L s₀ o) {V₀ : Addr → Byte} {q : Addr} (hE : IE F Wl L V₀ q) {g₀ : Gprs}
  (hsp0 : g₀.rsp = q.add 8) (k : IK prof F Wl L s₀ o gev gP gE V₀ g₀)
include c hE hsp0 k

/-- `0x613392`: `eax = 2`, to `88`. -/
theorem iA229 : AtK prof F Wl L s₀ o gev gP gE V₀ g₀ 0x6132ad 229 := by
  intro X t V hK hA hV hr hT
  have hl : icfa.length = 239 := icfa_length
  refine c.s_mov_ri32 hK hA hE.codea (by omega) hr (icfa_229 _) ?_
  rintro Y1 t1 hK1 hA1 ⟨hr1, hg1⟩
  refine c.s_jmp_x hK1 hA1 hE.codea (by omega) hr1 (icfa_234 _) hE.code (tgt := 88) (by rw [icf_length]; omega)
    (by decide) ?_
  rintro Y2 t2 hK2 hA2 ⟨hr2, hg2⟩
  exact iT1 c hE hsp0 k Y2 t2 _ hK2 hA2 hV hr2 (by rw [hg2, hg1]; exact hT.set (by omega) _)

/-- `0x613830`: family `0x15`, model `0x60`–`0x7f`: `feature[1]` without `AVX_Fast_Unaligned_Load`, with bits 3, 4. -/
theorem iH45 : AtK prof F Wl L s₀ o gev gP gE V₀ g₀ 0x613803 45 := by
  intro X t V hK hA hV hr hT
  have hl : icfh.length = 84 := icfh_length
  have hsp : X.cpu.gpr.rsp = q.add 8 := by rw [hT.sp, hsp0]
  have a229 := iA229 c hE hsp0 k
  refine c.s_mov_rm hK hA hE.codeh (by omega) hr (Or.inl rfl) (icfh_45 _)
    (fun i hi => by rw [eaD_sp hsp, addr_add_add]; exact c.hws _ (hE.fr (by omega))) ?_
  rintro Y1 t1 hK1 hA1 ⟨hr1, hg1⟩
  have hT1 : TK g₀ Y1.cpu.gpr := by rw [hg1]; exact hT.set (by omega) _
  refine c.s_wr hK1 hA1 hE.codeh (by omega) hr1 wr_sub_ri32 (icfh_49 _) ?_
  rintro Y2 t2 hK2 hA2 ⟨hr2, v, hg2⟩
  replace hr2 : Y2.cpu.rip = (0x613803 : Addr).add 52 := hr2
  have hT2 : TK g₀ Y2.cpu.gpr := by rw [hg2]; exact hT1.set (by omega) _
  refine c.s_fl hK2 hA2 hE.codeh (by omega) hr2 fl_cmp_ri32 (icfh_52 _) ?_
  rintro Y3 t3 hK3 hA3 ⟨hr3, hg3⟩
  replace hr3 : Y3.cpu.rip = (0x613803 : Addr).add 55 := hr3
  rw [← hg3] at hT2
  refine c.s_jcc_x hK3 hA3 hE.codeh (by omega) hr3 (icfh_55 _) hE.codea (tgt := 229) (by rw [icfa_length]; omega) (by decide)
    (fun _ Y t' hKY hAY ⟨hrY, hgY⟩ => a229 Y t' _ hKY hAY hV hrY (by rw [hgY]; exact hT2)) fun _ => ?_
  rintro Y4 t4 hK4 hA4 ⟨hr4, hg4⟩
  rw [← hg4] at hT2
  refine c.s_mov_r32_rip hK4 hA4 hE.codeh (by omega) hr4 (icfh_61 _) (g := (0x7a4ae0 : Addr).add 100) (by decide)
    (hE.cfd c (by omega)) ?_
  rintro Y5 t5 hK5 hA5 ⟨hr5, hg5⟩
  refine c.s_and_h8i hK5 hA5 hE.codeh (by omega) hr5 (icfh_67 _) ?_
  rintro Y6 t6 hK6 hA6 ⟨hr6, hg6⟩
  refine c.s_or_ri32 hK6 hA6 hE.codeh (by omega) hr6 (icfh_70 _) ?_
  rintro Y7 t7 hK7 hA7 ⟨hr7, hg7⟩
  have hT7 : TK g₀ Y7.cpu.gpr := by
    rw [hg7, hg6, hg5]; exact ((hT2.set (by omega) _).set (by omega) _).set (by omega) _
  refine c.s_mov_rip_r32 hK7 hA7 hE.codeh (by omega) hr7 (icfh_73 _) (g := (0x7a4ae0 : Addr).add 100) (by decide)
    (fun i hi => hE.cf (by omega)) ?_
  rintro Y8 t8 hK8 hA8 ⟨hr8, hg8⟩
  have hb : (rv Y7 32 0).getLsbD 8 = false := by
    have e7 : rv Y7 32 0 = ((rv Y6 32 0 ||| BitVec.ofNat 32 24).setWidth 64).setWidth 32 := by rw [rv, hg7]; rfl
    have e6 : rv Y6 32 0 = ((Y5.cpu.gpr.rax &&& ~~~(BitVec.ofNat 64 ((2 ^ 8 - 1) * 2 ^ 8))) |||
        (((Y5.cpu.gpr.rax >>> 8).setWidth 8 &&& BitVec.ofNat 8 0xfe).setWidth 64 <<< 8)).setWidth 32 := by
      rw [rv, hg6]; rfl
    rw [e7, e6]
    exact nb8 _
  refine c.s_jmp_x hK8 hA8 hE.codeh (by omega) hr8 (icfh_79 _) hE.codea (tgt := 229) (by rw [icfa_length]; omega) (by decide) ?_
  rintro Y9 t9 hK9 hA9 ⟨hr9, hg9⟩
  exact a229 Y9 t9 _ hK9 hA9 (hV.st (fun i hi => hE.cf (by simp at hi; omega)) (hV.inv.f1_nb8 _ hb)) hr9
    (by rw [hg9, hg8]; exact hT7)

/-- `0x613369`: `feature[0] |= 1 << 18` if bit 0 of it and bit 16 of `0x80000001`'s `ecx` are set; family `0x15`
to `0x613830`. -/
theorem iA188 : AtK prof F Wl L s₀ o gev gP gE V₀ g₀ 0x6132ad 188 := by
  intro X t V hK hA hV hr hT
  have hl : icfa.length = 239 := icfa_length
  have hsp : X.cpu.gpr.rsp = q.add 8 := by rw [hT.sp, hsp0]
  have a229 := iA229 c hE hsp0 k
  have h45 := iH45 c hE hsp0 k
  have a218 : ∀ (Y : State) (t' : Nat) (V : Addr → Byte), KeptW Wl s₀ Y → Agree F Y.proc.mm.mem V →
      IV prof Wl V₀ V → Y.cpu.rip = (0x6132ad : Addr).add 218 → TK g₀ Y.cpu.gpr →
      GoG prof L o gev gP gE Y t' := by
    intro Y0 t0 V hK0 hA0 hV hr0 hT0
    have hs0 : Y0.cpu.gpr.rsp = q.add 8 := by rw [hT0.sp, hsp0]
    refine c.s_cmp_m32i hK0 hA0 hE.codea (by omega) hr0 (icfa_218 _)
      (fun i hi => by rw [eaD_sp hs0, addr_add_add]; exact c.hws _ (hE.fr (by omega))) ?_
    rintro Y1 t1 hK1 hA1 ⟨hr1, hg1⟩
    rw [← hg1] at hT0
    refine c.s_jcc_x hK1 hA1 hE.codea (by omega) hr1 (icfa_223 _) hE.codeh (tgt := 45) (by rw [icfh_length]; omega)
      (by decide) (fun _ Y t' hKY hAY ⟨hrY, hgY⟩ => h45 Y t' _ hKY hAY hV hrY (by rw [hgY]; exact hT0)) fun _ => ?_
    rintro Y2 t2 hK2 hA2 ⟨hr2, hg2⟩
    exact a229 Y2 t2 _ hK2 hA2 hV hr2 (by rw [hg2]; exact hT0)
  refine c.s_mov_r32_rip hK hA hE.codea (by omega) hr (icfa_188 _) (g := (0x7a4ae0 : Addr).add 96) (by decide)
    (hE.cfd c (by omega)) ?_
  rintro Y1 t1 hK1 hA1 ⟨hr1, hg1⟩
  have hT1 : TK g₀ Y1.cpu.gpr := by rw [hg1]; exact hT.set (by omega) _
  have hv1 : rv Y1 32 0 = rdw V 96 := by rw [rv, hg1]; simp; rfl
  refine c.s_fl hK1 hA1 hE.codea (by omega) hr1 fl_test_r8i (icfa_194 _) ?_
  rintro Y2 t2 hK2 hA2 ⟨hr2, hg2⟩
  replace hr2 : Y2.cpu.rip = (0x6132ad : Addr).add 196 := hr2
  rw [← hg2] at hT1
  refine c.s_jcc hK2 hA2 hE.codea (by omega) hr2 (icfa_196 _) (tgt := 218) (by decide) (by omega)
    (fun _ Y t' hKY hAY ⟨hrY, hgY⟩ => a218 Y t' _ hKY hAY hV hrY (by rw [hgY]; exact hT1)) fun _ => ?_
  rintro Y3 t3 hK3 hA3 ⟨hr3, hg3⟩
  rw [← hg3] at hT1
  refine c.s_test_m8i_rip hK3 hA3 hE.codea (by omega) hr3 (icfa_198 _) (g := (0x7a4ae0 : Addr).add 42) (by decide)
    (by have := hE.cfd c (a := 42) (n := 1) (by omega) 0 (by omega); rwa [addr_add_zero] at this) ?_
  rintro Y4 t4 hK4 hA4 ⟨hr4, hg4, -⟩
  rw [← hg4] at hT1
  refine c.s_jcc hK4 hA4 hE.codea (by omega) hr4 (icfa_205 _) (tgt := 218) (by decide) (by omega)
    (fun _ Y t' hKY hAY ⟨hrY, hgY⟩ => a218 Y t' _ hKY hAY hV hrY (by rw [hgY]; exact hT1)) fun _ => ?_
  rintro Y5 t5 hK5 hA5 ⟨hr5, hg5⟩
  rw [← hg5] at hT1
  refine c.s_or_ri32 hK5 hA5 hE.codea (by omega) hr5 (icfa_207 _) ?_
  rintro Y6 t6 hK6 hA6 ⟨hr6, hg6⟩
  have hT6 : TK g₀ Y6.cpu.gpr := by rw [hg6]; exact hT1.set (by omega) _
  have hv6 : rv Y6 32 0 = rdw V 96 ||| BitVec.ofNat 32 0x40000 := by
    rw [show rv Y6 32 0 = ((rv Y5 32 0 ||| BitVec.ofNat 32 262144).setWidth 64).setWidth 32 by rw [rv, hg6]; rfl,
      show rv Y5 32 0 = rv Y1 32 0 by rw [rv, rv, hg5, hg4, hg3, hg2], hv1]
    simp
  refine c.s_mov_rip_r32 hK6 hA6 hE.codea (by omega) hr6 (icfa_212 _) (g := (0x7a4ae0 : Addr).add 96) (by decide)
    (fun i hi => hE.cf (by omega)) ?_
  rintro Y7 t7 hK7 hA7 ⟨hr7, hg7⟩
  rw [hv6] at hA7
  exact a218 Y7 t7 _ hK7 hA7 (hV.st (fun i hi => hE.cf (by simp at hi; omega)) hV.inv.or_f0_18) hr7
    (by rw [hg7]; exact hT6)

end K

/-! ## Past `cpuid`, which writes `rbx` -/

/-- `rsp` and the callee-saved registers but `rbx`, as in `g`. -/
structure TKr (g g' : Gprs) : Prop where
  sp : g'.rsp = g.rsp
  rbp : g'.rbp = g.rbp
  r12 : g'.r12 = g.r12
  r13 : g'.r13 = g.r13
  r14 : g'.r14 = g.r14
  r15 : g'.r15 = g.r15

theorem TK.refl (g : Gprs) : TK g g := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem TK.r {a b : Gprs} (h : TK a b) : TKr a b := ⟨h.sp, h.rbp, h.r12, h.r13, h.r14, h.r15⟩

theorem TKr.trans {a b c : Gprs} (h : TKr a b) (k : TKr b c) : TKr a c :=
  ⟨k.sp.trans h.sp, k.rbp.trans h.rbp, k.r12.trans h.r12, k.r13.trans h.r13, k.r14.trans h.r14, k.r15.trans h.r15⟩

theorem TKr.tk {a b c : Gprs} (h : TKr a b) (k : TK b c) : TKr a c := h.trans k.r

theorem TKr.set {g₀ g : Gprs} (h : TKr g₀ g) {r : Nat}
    (hr : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 6 ∨ r = 7) (v : BitVec 64) : TKr g₀ (g.set (regOf r) v) := by
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨h.sp, h.rbp, h.r12, h.r13, h.r14, h.r15⟩

theorem TKr.cpuid {g₀ g : Gprs} (h : TKr g₀ g) (a b c d : BitVec 64) :
    TKr g₀ ((((g.set 0 a).set 3 b).set 1 c).set 2 d) := ⟨h.sp, h.rbp, h.r12, h.r13, h.r14, h.r15⟩

/-- From the `j`-th byte of the code at `e`, with `TKr g₀`. -/
def AtR (prof : Profile) (F : Footprint) (Wl : List Rgn) (L : List (Addr × List Byte)) (s₀ : State) (o : Oracle)
    (gev : List Event) (gP : State → Nat → List Event → Prop) (gE : Outcome → List Event → Prop)
    (V₀ : Addr → Byte) (g₀ : Gprs) (e : Addr) (j : Nat) : Prop :=
  ∀ (X : State) (t : Nat) (V : Addr → Byte), KeptW Wl s₀ X → Agree F X.proc.mm.mem V → IV prof Wl V₀ V →
    X.cpu.rip = e.add j → TKr g₀ X.cpu.gpr → GoG prof L o gev gP gE X t

/-- The rest, for every value of the registers `cpuid` may write. -/
abbrev KR (prof : Profile) (F : Footprint) (Wl : List Rgn) (L : List (Addr × List Byte)) (s₀ : State) (o : Oracle)
    (gev : List Event) (gP : State → Nat → List Event → Prop) (gE : Outcome → List Event → Prop)
    (V₀ : Addr → Byte) (g₀ : Gprs) : Prop :=
  ∀ g, TKr g₀ g → IK prof F Wl L s₀ o gev gP gE V₀ g

/-- A part proved with `TK` of any registers (`section K`) holds with `TKr`. -/
theorem AtR.go {V₀ : Addr → Byte} {q : Addr} {g₀ : Gprs} (hsp0 : g₀.rsp = q.add 8)
    (kr : KR prof F Wl L s₀ o gev gP gE V₀ g₀) {e : Addr} {j : Nat}
    (h : ∀ g : Gprs, g.rsp = q.add 8 → IK prof F Wl L s₀ o gev gP gE V₀ g → AtK prof F Wl L s₀ o gev gP gE V₀ g e j) :
    AtR prof F Wl L s₀ o gev gP gE V₀ g₀ e j :=
  fun X t V hK hA hV hr hT => h X.cpu.gpr (by rw [hT.sp, hsp0]) (kr _ hT) X t V hK hA hV hr (TK.refl _)

section R
variable (c : Seg prof F Wl L s₀ o) {V₀ : Addr → Byte} {q : Addr} (hE : IE F Wl L V₀ q) {g₀ : Gprs}
  (hsp0 : g₀.rsp = q.add 8) (kr : KR prof F Wl L s₀ o gev gP gE V₀ g₀)
  (hpc : prof.Consistent) (hdf : s₀.cpu.rflags.df = false) (hx87 : s₀.cpu.x87.full = 0)
include c hE hsp0 kr hpc hdf hx87

/-- `0x6132d1`: `get_common_indices` with the family, model, extended model and stepping in the frame, the extended
leaves, to `0x613369`. -/
theorem iA36 : AtR prof F Wl L s₀ o gev gP gE V₀ g₀ 0x6132ad 36 := by
  intro X t V hK hA hV hr hT
  have hl : icfa.length = 239 := icfa_length
  have a188 : AtR prof F Wl L s₀ o gev gP gE V₀ g₀ 0x6132ad 188 := AtR.go hsp0 kr fun g hs kg => iA188 c hE hs kg
  have hsp : X.cpu.gpr.rsp = q.add 8 := by rw [hT.sp, hsp0]
  refine c.s_lea_bd hK hA hE.codea (by omega) hr (icfa_36 _) ?_
  rintro Y1 t1 hK1 hA1 ⟨hr1, hg1⟩
  refine c.s_lea_bd hK1 hA1 hE.codea (by omega) hr1 (icfa_41 _) ?_
  rintro Y2 t2 hK2 hA2 ⟨hr2, hg2⟩
  refine c.s_lea_bd hK2 hA2 hE.codea (by omega) hr2 (icfa_46 _) ?_
  rintro Y3 t3 hK3 hA3 ⟨hr3, hg3⟩
  refine c.s_lea_bd hK3 hA3 hE.codea (by omega) hr3 (icfa_51 _) ?_
  rintro Y4 t4 hK4 hA4 ⟨hr4, hg4⟩
  have hT4 : TKr g₀ Y4.cpu.gpr := by
    rw [hg4, hg3, hg2, hg1]
    exact (((hT.set (by omega) _).set (by omega) _).set (by omega) _).set (by omega) _
  have hs1 : Y1.cpu.gpr.rsp = q.add 8 := by rw [hg1]; exact hsp
  have hs2 : Y2.cpu.gpr.rsp = q.add 8 := by rw [hg2]; exact hs1
  have hs3 : Y3.cpu.gpr.rsp = q.add 8 := by rw [hg3]; exact hs2
  have hs4 : Y4.cpu.gpr.rsp = q.add 8 := by rw [hg4]; exact hs3
  have pi : ∀ m, 52 ≤ m → m + 4 ≤ 0x80 → PI q (q.add m) := fun m h1 h2 => ⟨m, h1, h2, rfl⟩
  refine callG c hE hpc hdf hx87 hK4 hA4 hV hE.codea (by omega) hr4 (icfa_56 _) (by omega) (by decide)
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
  have j188 : ∀ (Y : State) (t' : Nat) (V : Addr → Byte), KeptW Wl s₀ Y → Agree F Y.proc.mm.mem V →
      IV prof Wl V₀ V → TKr g₀ Y.cpu.gpr → ∀ (Y' : State), Y'.cpu.gpr = Y.cpu.gpr → ∀ t'' , KeptW Wl s₀ Y' →
      Agree F Y'.proc.mm.mem V → Y'.cpu.rip = (0x6132ad : Addr).add 188 → GoG prof L o gev gP gE Y' t'' :=
    fun _ _ _ _ _ hV hT Y' hg t'' hK hA hr => a188 Y' t'' _ hK hA hV hr (by rw [hg]; exact hT)
  refine c.s_mov_ri32 hKZ hAZ hE.codea (by omega) hrZ (icfa_61 _) ?_
  rintro Y11 t11 hK11 hA11 ⟨hr11, hg11⟩
  have hT11 : TKr g₀ Y11.cpu.gpr := by rw [hg11]; exact hTZ'.set (by omega) _
  refine c.s_mov_rr32 hK11 hA11 hE.codea (by omega) hr11 (icfa_66 _) ?_
  rintro Y12 t12 hK12 hA12 ⟨hr12, hg12⟩
  have hT12 : TKr g₀ Y12.cpu.gpr := by rw [hg12]; exact hT11.set (by omega) _
  refine c.s_cpuid hK12 hA12 hE.codea (by omega) hr12 (icfa_68 _) ?_
  rintro Y13 t13 hK13 hA13 ⟨hr13, _, -, hg13⟩
  have hT13 : TKr g₀ Y13.cpu.gpr := by rw [hg13]; exact hT12.cpuid _ _ _ _
  refine c.s_mov_rr32 hK13 hA13 hE.codea (by omega) hr13 (icfa_70 _) ?_
  rintro Y14 t14 hK14 hA14 ⟨hr14, hg14⟩
  have hT14 : TKr g₀ Y14.cpu.gpr := by rw [hg14]; exact hT13.set (by omega) _
  refine c.s_fl hK14 hA14 hE.codea (by omega) hr14 fl_cmp_ri32 (icfa_72 _) ?_
  rintro Y15 t15 hK15 hA15 ⟨hr15, hg15⟩
  replace hr15 : Y15.cpu.rip = (0x6132ad : Addr).add 77 := hr15
  have hT15 : TKr g₀ Y15.cpu.gpr := by rw [hg15]; exact hT14
  refine c.s_jcc hK15 hA15 hE.codea (by omega) hr15 (icfa_77 _) (tgt := 188) (by decide) (by omega)
    (fun _ Y t' hKY hAY ⟨hrY, hgY⟩ => j188 Y15 0 _ hK15 hA15 hV' hT15 Y hgY t' hKY hAY hrY) fun _ => ?_
  rintro Y16 t16 hK16 hA16 ⟨hr16, hg16⟩
  have hT16 : TKr g₀ Y16.cpu.gpr := by rw [hg16]; exact hT15
  refine c.s_mov_ri32 hK16 hA16 hE.codea (by omega) hr16 (icfa_79 _) ?_
  rintro Y17 t17 hK17 hA17 ⟨hr17, hg17⟩
  have hT17 : TKr g₀ Y17.cpu.gpr := by rw [hg17]; exact hT16.set (by omega) _
  refine c.s_cpuid hK17 hA17 hE.codea (by omega) hr17 (icfa_84 _) ?_
  rintro Y18 t18 hK18 hA18 ⟨hr18, _, -, hg18⟩
  have hT18 : TKr g₀ Y18.cpu.gpr := by rw [hg18]; exact hT17.cpuid _ _ _ _
  refine c.s_mov_rip_r32 hK18 hA18 hE.codea (by omega) hr18 (icfa_86 _) (g := (0x7a4ae0 : Addr).add 32) (by decide)
    (fun i hi => hE.cf (by omega)) ?_
  rintro Y19 t19 hK19 hA19 ⟨hr19, hg19⟩
  have hT19 : TKr g₀ Y19.cpu.gpr := by rw [hg19]; exact hT18
  have hV19 := st hV' (a := 32) (by omega) (by omega) (by omega) (rv Y18 32 0)
  refine c.s_mov_rip_r32 hK19 hA19 hE.codea (by omega) hr19 (icfa_92 _) (g := (0x7a4ae0 : Addr).add 36) (by decide)
    (fun i hi => hE.cf (by omega)) ?_
  rintro Y20 t20 hK20 hA20 ⟨hr20, hg20⟩
  have hT20 : TKr g₀ Y20.cpu.gpr := by rw [hg20]; exact hT19
  have hV20 := st hV19 (a := 36) (by omega) (by omega) (by omega) (rv Y19 32 3)
  refine c.s_mov_rip_r32 hK20 hA20 hE.codea (by omega) hr20 (icfa_98 _) (g := (0x7a4ae0 : Addr).add 40) (by decide)
    (fun i hi => hE.cf (by omega)) ?_
  rintro Y21 t21 hK21 hA21 ⟨hr21, hg21⟩
  have hT21 : TKr g₀ Y21.cpu.gpr := by rw [hg21]; exact hT20
  have hV21 := st hV20 (a := 40) (by omega) (by omega) (by omega) (rv Y20 32 1)
  refine c.s_mov_rip_r32 hK21 hA21 hE.codea (by omega) hr21 (icfa_104 _) (g := (0x7a4ae0 : Addr).add 44) (by decide)
    (fun i hi => hE.cf (by omega)) ?_
  rintro Y22 t22 hK22 hA22 ⟨hr22, hg22⟩
  have hT22 : TKr g₀ Y22.cpu.gpr := by rw [hg22]; exact hT21
  have hV22 := st hV21 (a := 44) (by omega) (by omega) (by omega) (rv Y21 32 2)
  refine c.s_fl hK22 hA22 hE.codea (by omega) hr22 fl_cmp_ri32 (icfa_110 _) ?_
  rintro Y23 t23 hK23 hA23 ⟨hr23, hg23⟩
  replace hr23 : Y23.cpu.rip = (0x6132ad : Addr).add 116 := hr23
  have hT23 : TKr g₀ Y23.cpu.gpr := by rw [hg23]; exact hT22
  refine c.s_jcc hK23 hA23 hE.codea (by omega) hr23 (icfa_116 _) (tgt := 188) (by decide) (by omega)
    (fun _ Y t' hKY hAY ⟨hrY, hgY⟩ => j188 Y23 0 _ hK23 hA23 hV22 hT23 Y hgY t' hKY hAY hrY) fun _ => ?_
  rintro Y24 t24 hK24 hA24 ⟨hr24, hg24⟩
  have hT24 : TKr g₀ Y24.cpu.gpr := by rw [hg24]; exact hT23
  refine c.s_mov_ri32 hK24 hA24 hE.codea (by omega) hr24 (icfa_118 _) ?_
  rintro Y25 t25 hK25 hA25 ⟨hr25, hg25⟩
  have hT25 : TKr g₀ Y25.cpu.gpr := by rw [hg25]; exact hT24.set (by omega) _
  refine c.s_cpuid hK25 hA25 hE.codea (by omega) hr25 (icfa_123 _) ?_
  rintro Y26 t26 hK26 hA26 ⟨hr26, _, -, hg26⟩
  have hT26 : TKr g₀ Y26.cpu.gpr := by rw [hg26]; exact hT25.cpuid _ _ _ _
  refine c.s_mov_rip_r32 hK26 hA26 hE.codea (by omega) hr26 (icfa_125 _) (g := (0x7a4ae0 : Addr).add 64) (by decide)
    (fun i hi => hE.cf (by omega)) ?_
  rintro Y27 t27 hK27 hA27 ⟨hr27, hg27⟩
  have hT27 : TKr g₀ Y27.cpu.gpr := by rw [hg27]; exact hT26
  have hV27 := st hV22 (a := 64) (by omega) (by omega) (by omega) (rv Y26 32 0)
  refine c.s_mov_rip_r32 hK27 hA27 hE.codea (by omega) hr27 (icfa_131 _) (g := (0x7a4ae0 : Addr).add 68) (by decide)
    (fun i hi => hE.cf (by omega)) ?_
  rintro Y28 t28 hK28 hA28 ⟨hr28, hg28⟩
  have hT28 : TKr g₀ Y28.cpu.gpr := by rw [hg28]; exact hT27
  have hV28 := st hV27 (a := 68) (by omega) (by omega) (by omega) (rv Y27 32 3)
  refine c.s_mov_rip_r32 hK28 hA28 hE.codea (by omega) hr28 (icfa_137 _) (g := (0x7a4ae0 : Addr).add 72) (by decide)
    (fun i hi => hE.cf (by omega)) ?_
  rintro Y29 t29 hK29 hA29 ⟨hr29, hg29⟩
  have hT29 : TKr g₀ Y29.cpu.gpr := by rw [hg29]; exact hT28
  have hV29 := st hV28 (a := 72) (by omega) (by omega) (by omega) (rv Y28 32 1)
  refine c.s_mov_rip_r32 hK29 hA29 hE.codea (by omega) hr29 (icfa_143 _) (g := (0x7a4ae0 : Addr).add 76) (by decide)
    (fun i hi => hE.cf (by omega)) ?_
  rintro Y30 t30 hK30 hA30 ⟨hr30, hg30⟩
  have hT30 : TKr g₀ Y30.cpu.gpr := by rw [hg30]; exact hT29
  have hV30 := st hV29 (a := 76) (by omega) (by omega) (by omega) (rv Y29 32 2)
  refine c.s_fl hK30 hA30 hE.codea (by omega) hr30 fl_cmp_ri32 (icfa_149 _) ?_
  rintro Y31 t31 hK31 hA31 ⟨hr31, hg31⟩
  replace hr31 : Y31.cpu.rip = (0x6132ad : Addr).add 155 := hr31
  have hT31 : TKr g₀ Y31.cpu.gpr := by rw [hg31]; exact hT30
  refine c.s_jcc hK31 hA31 hE.codea (by omega) hr31 (icfa_155 _) (tgt := 188) (by decide) (by omega)
    (fun _ Y t' hKY hAY ⟨hrY, hgY⟩ => j188 Y31 0 _ hK31 hA31 hV30 hT31 Y hgY t' hKY hAY hrY) fun _ => ?_
  rintro Y32 t32 hK32 hA32 ⟨hr32, hg32⟩
  have hT32 : TKr g₀ Y32.cpu.gpr := by rw [hg32]; exact hT31
  refine c.s_mov_ri32 hK32 hA32 hE.codea (by omega) hr32 (icfa_157 _) ?_
  rintro Y33 t33 hK33 hA33 ⟨hr33, hg33⟩
  have hT33 : TKr g₀ Y33.cpu.gpr := by rw [hg33]; exact hT32.set (by omega) _
  refine c.s_cpuid hK33 hA33 hE.codea (by omega) hr33 (icfa_162 _) ?_
  rintro Y34 t34 hK34 hA34 ⟨hr34, _, -, hg34⟩
  have hT34 : TKr g₀ Y34.cpu.gpr := by rw [hg34]; exact hT33.cpuid _ _ _ _
  refine c.s_mov_rip_r32 hK34 hA34 hE.codea (by omega) hr34 (icfa_164 _) (g := (0x7a4ae0 : Addr).add 80) (by decide)
    (fun i hi => hE.cf (by omega)) ?_
  rintro Y35 t35 hK35 hA35 ⟨hr35, hg35⟩
  have hT35 : TKr g₀ Y35.cpu.gpr := by rw [hg35]; exact hT34
  have hV35 := st hV30 (a := 80) (by omega) (by omega) (by omega) (rv Y34 32 0)
  refine c.s_mov_rip_r32 hK35 hA35 hE.codea (by omega) hr35 (icfa_170 _) (g := (0x7a4ae0 : Addr).add 84) (by decide)
    (fun i hi => hE.cf (by omega)) ?_
  rintro Y36 t36 hK36 hA36 ⟨hr36, hg36⟩
  have hT36 : TKr g₀ Y36.cpu.gpr := by rw [hg36]; exact hT35
  have hV36 := st hV35 (a := 84) (by omega) (by omega) (by omega) (rv Y35 32 3)
  refine c.s_mov_rip_r32 hK36 hA36 hE.codea (by omega) hr36 (icfa_176 _) (g := (0x7a4ae0 : Addr).add 88) (by decide)
    (fun i hi => hE.cf (by omega)) ?_
  rintro Y37 t37 hK37 hA37 ⟨hr37, hg37⟩
  have hT37 : TKr g₀ Y37.cpu.gpr := by rw [hg37]; exact hT36
  have hV37 := st hV36 (a := 88) (by omega) (by omega) (by omega) (rv Y36 32 1)
  refine c.s_mov_rip_r32 hK37 hA37 hE.codea (by omega) hr37 (icfa_182 _) (g := (0x7a4ae0 : Addr).add 92) (by decide)
    (fun i hi => hE.cf (by omega)) ?_
  rintro Y38 t38 hK38 hA38 ⟨hr38, hg38⟩
  have hT38 : TKr g₀ Y38.cpu.gpr := by rw [hg38]; exact hT37
  have hV38 := st hV37 (a := 92) (by omega) (by omega) (by omega) (rv Y37 32 2)
  exact a188 Y38 _ _ hK38 hA38 hV38 hr38 hT38

/-- `0x613803`: `HygonGenuine` to `0x6132d1` (`iA36`), any other vendor to `0x613159` (`iO`). -/
theorem iH0 : AtR prof F Wl L s₀ o gev gP gE V₀ g₀ 0x613803 0 := by
  intro X t V hK hA hV hr hT
  have hl : icfh.length = 84 := icfh_length
  have a36 := iA36 c hE hsp0 kr hpc hdf hx87
  have o70 : AtR prof F Wl L s₀ o gev gP gE V₀ g₀ 0x613113 70 :=
    AtR.go hsp0 kr fun g hs kg => iO c hE hs kg hpc hdf hx87
  refine c.s_fl hK hA hE.codeh (by omega) hr fl_cmp_ri32 (icfh_0 _) ?_
  rintro Y1 t1 hK1 hA1 ⟨hr1, hg1⟩
  replace hr1 : Y1.cpu.rip = (0x613803 : Addr).add 6 := hr1
  refine c.s_setcc hK1 hA1 hE.codeh (by omega) hr1 (icfh_6 _) ?_
  rintro Y2 t2 hK2 hA2 ⟨hr2, v2, hg2, -⟩
  refine c.s_fl hK2 hA2 hE.codeh (by omega) hr2 fl_cmp_ri32 (icfh_10 _) ?_
  rintro Y3 t3 hK3 hA3 ⟨hr3, hg3⟩
  replace hr3 : Y3.cpu.rip = (0x613803 : Addr).add 16 := hr3
  refine c.s_setcc hK3 hA3 hE.codeh (by omega) hr3 (icfh_16 _) ?_
  rintro Y4 t4 hK4 hA4 ⟨hr4, v4, hg4, -⟩
  refine c.s_wr hK4 hA4 hE.codeh (by omega) hr4 wr_test_rr8 (icfh_19 _) ?_
  rintro Y5 t5 hK5 hA5 ⟨hr5, v5, hg5⟩
  replace hr5 : Y5.cpu.rip = (0x613803 : Addr).add 22 := hr5
  have hT5 : TKr g₀ Y5.cpu.gpr := by
    rw [hg5, hg4, hg3, hg2, hg1]; exact ((hT.set (by omega) _).set (by omega) _).set (by omega) _
  refine c.s_jcc_x hK5 hA5 hE.codeh (by omega) hr5 (icfh_22 _) hE.code (tgt := 70) (by rw [icf_length]; omega)
    (by decide) (fun _ Y t' hKY hAY ⟨hrY, hgY⟩ => o70 Y t' _ hKY hAY hV hrY (by rw [hgY]; exact hT5)) fun _ => ?_
  rintro Y6 t6 hK6 hA6 ⟨hr6, hg6⟩
  rw [← hg6] at hT5
  refine c.s_fl hK6 hA6 hE.codeh (by omega) hr6 fl_cmp_ri32 (icfh_28 _) ?_
  rintro Y7 t7 hK7 hA7 ⟨hr7, hg7⟩
  replace hr7 : Y7.cpu.rip = (0x613803 : Addr).add 34 := hr7
  rw [← hg7] at hT5
  refine c.s_jcc_x hK7 hA7 hE.codeh (by omega) hr7 (icfh_34 _) hE.codea (tgt := 36) (by rw [icfa_length]; omega)
    (by decide) (fun _ Y t' hKY hAY ⟨hrY, hgY⟩ => a36 Y t' _ hKY hAY hV hrY (by rw [hgY]; exact hT5)) fun _ => ?_
  rintro Y8 t8 hK8 hA8 ⟨hr8, hg8⟩
  rw [← hg8] at hT5
  refine c.s_jmp_x hK8 hA8 hE.codeh (by omega) hr8 (icfh_40 _) hE.code (tgt := 70) (by rw [icf_length]; omega)
    (by decide) ?_
  rintro Y9 t9 hK9 hA9 ⟨hr9, hg9⟩
  exact o70 Y9 t9 _ hK9 hA9 hV hr9 (by rw [hg9]; exact hT5)

/-- `0x6132ad`: `AuthenticAMD` to `0x6132d1` (`iA36`), else Hygon's check (`iH0`) or another vendor (`iO`). -/
theorem iA0 : AtR prof F Wl L s₀ o gev gP gE V₀ g₀ 0x6132ad 0 := by
  intro X t V hK hA hV hr hT
  have hl : icfa.length = 239 := icfa_length
  have a36 := iA36 c hE hsp0 kr hpc hdf hx87
  have h0 := iH0 c hE hsp0 kr hpc hdf hx87
  have o70 : AtR prof F Wl L s₀ o gev gP gE V₀ g₀ 0x613113 70 :=
    AtR.go hsp0 kr fun g hs kg => iO c hE hs kg hpc hdf hx87
  refine c.s_fl hK hA hE.codea (by omega) hr fl_cmp_ri32 (icfa_0 _) ?_
  rintro Y1 t1 hK1 hA1 ⟨hr1, hg1⟩
  replace hr1 : Y1.cpu.rip = (0x6132ad : Addr).add 6 := hr1
  rw [← hg1] at hT
  refine c.s_jcc_x hK1 hA1 hE.codea (by omega) hr1 (icfa_6 _) hE.codeh (tgt := 0) (by rw [icfh_length]; omega)
    (by decide) (fun _ Y t' hKY hAY ⟨hrY, hgY⟩ => h0 Y t' _ hKY hAY hV hrY (by rw [hgY]; exact hT)) fun _ => ?_
  rintro Y2 t2 hK2 hA2 ⟨hr2, hg2⟩
  rw [← hg2] at hT
  refine c.s_fl hK2 hA2 hE.codea (by omega) hr2 fl_cmp_ri32 (icfa_12 _) ?_
  rintro Y3 t3 hK3 hA3 ⟨hr3, hg3⟩
  replace hr3 : Y3.cpu.rip = (0x6132ad : Addr).add 18 := hr3
  rw [← hg3] at hT
  refine c.s_jcc_x hK3 hA3 hE.codea (by omega) hr3 (icfa_18 _) hE.codeh (tgt := 0) (by rw [icfh_length]; omega)
    (by decide) (fun _ Y t' hKY hAY ⟨hrY, hgY⟩ => h0 Y t' _ hKY hAY hV hrY (by rw [hgY]; exact hT)) fun _ => ?_
  rintro Y4 t4 hK4 hA4 ⟨hr4, hg4⟩
  rw [← hg4] at hT
  refine c.s_fl hK4 hA4 hE.codea (by omega) hr4 fl_cmp_ri32 (icfa_24 _) ?_
  rintro Y5 t5 hK5 hA5 ⟨hr5, hg5⟩
  replace hr5 : Y5.cpu.rip = (0x6132ad : Addr).add 30 := hr5
  rw [← hg5] at hT
  refine c.s_jcc_x hK5 hA5 hE.codea (by omega) hr5 (icfa_30 _) hE.code (tgt := 70) (by rw [icf_length]; omega)
    (by decide) (fun _ Y t' hKY hAY ⟨hrY, hgY⟩ => o70 Y t' _ hKY hAY hV hrY (by rw [hgY]; exact hT)) fun _ => ?_
  rintro Y6 t6 hK6 hA6 ⟨hr6, hg6⟩
  exact a36 Y6 t6 _ hK6 hA6 hV hr6 (by rw [hg6]; exact hT)

end R

end FV7z.CpuFeat
