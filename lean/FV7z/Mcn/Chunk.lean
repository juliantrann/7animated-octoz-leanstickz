import FV7z.Mcn.Spec
/-!
# `malloc_consolidate`: one chunk (PLAN.md §M, M1)

From 164 with `rbx = p` (the chunk), `r13` its fastbin, `r15 = av`, `rsp = mB S`: the run reaches 156 with the
bytes `cstep`, `rdx = nextp`, `rsp`, `r13` and `r15` as they were (`chunk_ok`). The parts: `from127` (the head, the
`fd`/`bk` words and the foot, to 156), `from98` (first in the unsorted bin, a large chunk's `nextsize` words),
`from256` (the top chunk, or the forward merge), `chunk_ok` (the checks, the backward merge).
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
open FV7z.Tun (rd_Vst rd_Vst_self Vst_out)
open FV7z.Ulk (ulkV UlkPre)
open FV7z.Cxa (lane_lo st16)
namespace FV7z.Mcn

/-! ## The frame's words -/

theorem mB8_toNat {S : Addr} (hS : 80 ≤ S.toNat) : (mB S - 8).toNat = S.toNat - 80 := by
  have e := mB_toNat hS
  rw [Prepare.toNat_sub8 (by rw [e]; omega), e]
  omega

theorem mB8p_toNat {S : Addr} (hS : 80 ≤ S.toNat) : (mB S + 8#64).toNat = S.toNat - 64 := by
  have e := mB_toNat hS
  have hl := S.isLt
  rw [BitVec.toNat_add, e, show (8#64).toNat = 8 from rfl]
  omega

theorem psh_rd0 {S : Addr} (hS : 80 ≤ S.toNat) (V : Addr → Byte) (x ra : Addr) : rdq(psh S V x ra, mB S) = x := by
  have e := mB_toNat hS
  have e8 := mB8_toNat hS
  have hl := S.isLt
  unfold psh
  rw [rd_Vst _ _ _ _ _ (by rw [toBytesLE_length, e8]; omega) (by rw [e]; omega)
      (.inl (by rw [toBytesLE_length, e8, e]; omega)),
    rd_Vst_self _ _ _ (toBytesLE_length _ _) (by rw [e]; omega)]
  exact ofBytesLE_toBytesLE (n := 8) rfl _

theorem psh_rd8 {S : Addr} (hS : 80 ≤ S.toNat) (V : Addr → Byte) (x ra : Addr) :
    rdq(psh S V x ra, mB S - 8) = ra := by
  have e8 := mB8_toNat hS
  have hl := S.isLt
  unfold psh
  rw [rd_Vst_self _ _ _ (toBytesLE_length _ _) (by rw [e8]; omega)]
  exact ofBytesLE_toBytesLE (n := 8) rfl _

/-- A word in kept bytes. -/
theorem kf_rd {lo up : Nat} {V V' : Addr → Byte} (h : Kf lo up V V') {a : Addr} (h1 : lo ≤ a.toNat)
    (h2 : a.toNat + 8 ≤ up) (h3 : up ≤ 2 ^ 64) : rdq(V', a) = rdq(V, a) :=
  congrArg (ofBytesLE 64) (Stm.rd_in h (by omega) h1 h2)

/-- `nextp` and the return address read back after `unlink_chunk`. -/
theorem ulk_rd {S : Addr} (hS : 80 ≤ S.toNat) {V : Addr → Byte} {x ra q : Addr} (h : UlkOut S (psh S V x ra) q) :
    rdq(ulkV (psh S V x ra) q, mB S) = x ∧ rdq(ulkV (psh S V x ra) q, mB S - 8) = ra := by
  have e := mB_toNat hS
  have e8 := mB8_toNat hS
  have hl := S.isLt
  exact ⟨(kf_rd (kf_ulk h) (by rw [e]; omega) (by rw [e]; omega) (by omega)).trans (psh_rd0 hS V x ra),
    (kf_rd (kf_ulk h) (by rw [e8]) (by rw [e8]; omega) (by omega)).trans (psh_rd8 hS V x ra)⟩

/-! ## The parts -/

section
variable {prof : Profile} {F : Footprint} {Wl : List Rgn} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}

set_option maxHeartbeats 4000000 in
/-- From 127: `set_head (p, size | PREV_INUSE)`, `p->fd`, `p->bk`, `set_foot (p, size)`; to 156. -/
theorem from127 {fb S av fq : Addr} {V : Addr → Byte} {p : Addr} {X : State} {t : Nat}
    (c : Seg prof F Wl L s₀ o) (hfs : s₀.cpu.seg.fsBase = fb) (hin : CodeIn L mcn_at mcn)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem (cV4 S av V p)) (hrip : X.cpu.rip = mcn_at.add 127)
    (hS : 80 ≤ S.toNat) (hstk : ∀ a : Addr, S.toNat - 80 ≤ a.toNat → a.toNat < S.toNat → Foot Wl a)
    (hsp : X.cpu.gpr.rsp = mB S) (hbx : X.cpu.gpr.rbx = cp1 V p) (hbp : X.cpu.gpr.rbp = cz2 S V p)
    (h12 : X.cpu.gpr.r12 = cft S V p) (hax : X.cpu.gpr.rax = cfu S av V p) (hdx : X.cpu.gpr.rdx = cnx V p)
    (h13 : X.cpu.gpr.r13 = fq) (h15 : X.cpu.gpr.r15 = av) (h8 : rdq(cV4 S av V p, mB S + 8#64) = av + 96#64)
    (r : CRest F Wl S av V p)
    (k : ∀ Y t', KeptW Wl s₀ Y → Agree F Y.proc.mm.mem (cV7 S av V p) → Y.cpu.rip = mcn_at.add 156 →
      Y.cpu.gpr.rdx = cnx V p → Y.cpu.gpr.rsp = mB S → Y.cpu.gpr.r13 = fq → Y.cpu.gpr.r15 = av →
      GoG prof L o gev gP gE Y t') :
    GoG prof L o gev gP gE X t := by
  have hl := S.isLt
  have e8 := mB8p_toNat hS
  refine (c_127 prof fb).run c hfs hin _ hK hA hrip vc_127 ?_
  rintro j' g₁ fl V' ⟨rfl, rfl, rfl⟩ Y₁ t₁ hK₁ hA₁ hr₁ hg₁ -
  refine c.s_movq_rx hK₁ hA₁ hin (lt_len (by decide)) hr₁ (movq_130 _) ?_
  rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂, hx₂, -⟩
  refine (c_135 prof fb).run c hfs hin _ hK₂ hA₂ hr₂ vc_135 ?_
  rintro j' g₃ fl V' ⟨rfl, rfl, rfl⟩ Y₃ t₃ hK₃ hA₃ hr₃ hg₃ hv₃
  have hY₃ : Y₃.cpu.gpr = { X.cpu.gpr with rsi := X.cpu.gpr.rbp ||| 1#64 } := by rw [hg₃, hg₂, hg₁]
  have ea : eaD Y₃ 4 8 = mB S + 8#64 := by
    show Y₃.cpu.gpr.rsp + 8#64 = _
    rw [hY₃]
    exact congrArg (· + 8#64) hsp
  refine c.s_movhps_ld hK₃ hA₃ hin (lt_len (by decide)) hr₃ (movhps_139 _) (fun i hi => ?_) ?_
  · rw [ea]; exact c.hws _ (Stm.stk hstk (by rw [e8]; omega) (by rw [e8]; omega) (by omega) i hi)
  rintro Y₄ t₄ hK₄ hA₄ ⟨hr₄, hg₄, hx₄⟩
  have hx₃ : xlo Y₃ 0 = (cfu S av V p).setWidth 128 := by
    show (Y₃.cpu.vec.zmm (xmmOf 0)).setWidth 128 = _
    rw [hv₃]
    refine hx₂.trans ?_
    show ((Y₁.cpu.gpr.get (regOf 0)).setWidth 64).setWidth 128 = _
    rw [hg₁, BitVec.setWidth_eq]
    exact congrArg (BitVec.setWidth 128) hax
  rw [ea, h8, hx₃, lane_lo] at hx₄
  have hY₄ : Y₄.cpu.gpr = { X.cpu.gpr with rsi := X.cpu.gpr.rbp ||| 1#64 } := by rw [hg₄, hY₃]
  refine (c_144 prof fb).run c hfs hin _ hK₄ hA₄ hr₄ (vc_144 (by rw [hY₄]; exact (by rw [hbx]; exact r.w4.1))) ?_
  rintro j' g₅ fl V' ⟨rfl, rfl, rfl⟩ Y₅ t₅ hK₅ hA₅ hr₅ hg₅ hv₅
  have hY₅ : Y₅.cpu.gpr = { X.cpu.gpr with rsi := X.cpu.gpr.rbp ||| 1#64 } := by rw [hg₅, hY₄]
  have e16 : eaD Y₅ 3 16 = cp1 V p + 16#64 := by
    show Y₅.cpu.gpr.rbx + 16#64 = _
    rw [hY₅]
    exact congrArg (· + 16#64) hbx
  refine c.s_movups_st hK₅ hA₅ hin (lt_len (by decide)) hr₅ (movups_148 _) (by rw [e16]; exact r.w5.1) ?_
  rintro Y₆ t₆ hK₆ hA₆ ⟨hr₆, hg₆⟩
  have hx₅ : xlo Y₅ 0 = ((av + 96#64) ++ cfu S av V p).setWidth 128 := by
    show (Y₅.cpu.vec.zmm (xmmOf 0)).setWidth 128 = _
    rw [hv₅]
    exact hx₄
  rw [e16, hx₅, st16] at hA₆
  have hY₆ : Y₆.cpu.gpr = { X.cpu.gpr with rsi := X.cpu.gpr.rbp ||| 1#64 } := by rw [hg₆, hY₅]
  refine (c_152 prof fb).run c hfs hin _ hK₆ hA₆ hr₆ (vc_152 (by rw [hY₆]; exact (by rw [h12]; exact r.w6.1))) ?_
  rintro j' g₇ fl V' ⟨rfl, rfl, rfl⟩ Y₇ t₇ hK₇ hA₇ hr₇ hg₇ -
  have hY₇ : Y₇.cpu.gpr = { X.cpu.gpr with rsi := X.cpu.gpr.rbp ||| 1#64 } := by rw [hg₇, hY₆]
  have hrb : Y₄.cpu.gpr.rbx + 8#64 = cp1 V p + 8#64 := by rw [hY₄]; exact congrArg (· + 8#64) hbx
  have hrs : Y₄.cpu.gpr.rsi = cz2 S V p ||| 1#64 := by rw [hY₄]; exact congrArg (· ||| 1#64) hbp
  have hr12 : Y₆.cpu.gpr.r12 = cft S V p := by rw [hY₆]; exact h12
  have hrp : Y₆.cpu.gpr.rbp = cz2 S V p := by rw [hY₆]; exact hbp
  rw [hrb, hrs, hr12, hrp] at hA₇
  exact k Y₇ t₇ hK₇ hA₇ hr₇ (by rw [hY₇]; exact hdx) (by rw [hY₇]; exact hsp) (by rw [hY₇]; exact h13)
    (by rw [hY₇]; exact h15)

/-- The frame's words at `rsp`, at the return address under it. -/
theorem stB {S : Addr} (hS : 80 ≤ S.toNat) (hstk : ∀ a : Addr, S.toNat - 80 ≤ a.toNat → a.toNat < S.toNat → Foot Wl a) :
    (∀ i < 8, Foot Wl (Addr.add (mB S) i)) ∧ ∀ i < 8, Foot Wl (Addr.add (mB S - 8) i) := by
  have e := mB_toNat hS
  have e8 := mB8_toNat hS
  have hl := S.isLt
  exact ⟨Stm.stk hstk (by rw [e]; omega) (by rw [e]; omega) (by omega),
    Stm.stk hstk (by rw [e8]) (by rw [e8]; omega) (by omega)⟩

set_option maxHeartbeats 4000000 in
/-- From 98: `p` first in the unsorted bin, a large chunk's `nextsize` words cleared; then `from127`. -/
theorem from98 {fb S av fq : Addr} {V : Addr → Byte} {p : Addr} {X : State} {t : Nat}
    (c : Seg prof F Wl L s₀ o) (hfs : s₀.cpu.seg.fsBase = fb) (hin : CodeIn L mcn_at mcn)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem (cV2 S V p)) (hrip : X.cpu.rip = mcn_at.add 98)
    (hS : 80 ≤ S.toNat) (hstk : ∀ a : Addr, S.toNat - 80 ≤ a.toNat → a.toNat < S.toNat → Foot Wl a)
    (hsp : X.cpu.gpr.rsp = mB S) (hbx : X.cpu.gpr.rbx = cp1 V p) (hbp : X.cpu.gpr.rbp = cz2 S V p)
    (h12 : X.cpu.gpr.r12 = cft S V p) (hdx : X.cpu.gpr.rdx = cnx V p)
    (h13 : X.cpu.gpr.r13 = fq) (h15 : X.cpu.gpr.r15 = av) (h8 : rdq(cV4 S av V p, mB S + 8#64) = av + 96#64)
    (r : CRest F Wl S av V p)
    (k : ∀ Y t', KeptW Wl s₀ Y → Agree F Y.proc.mm.mem (cV7 S av V p) → Y.cpu.rip = mcn_at.add 156 →
      Y.cpu.gpr.rdx = cnx V p → Y.cpu.gpr.rsp = mB S → Y.cpu.gpr.r13 = fq → Y.cpu.gpr.r15 = av →
      GoG prof L o gev gP gE Y t') :
    GoG prof L o gev gP gE X t := by
  have hfu : rdq(cV2 S V p, X.cpu.gpr.r15 + 112#64) = cfu S av V p := by rw [h15]; rfl
  have f1 : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.r15 + 112#64) i) := by rw [h15]; exact r.f4
  have w1 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.r15 + 112#64) i) := by rw [h15]; exact r.w1.1
  by_cases hz : (cz2 S V p).toNat ≤ 1023
  · refine (c_98 prof fb).run c hfs hin _ hK hA hrip (vc_98s hfu (by rw [hbp]; exact hz) f1 w1 r.w2.1) ?_
    rintro j' g₁ fl V' ⟨rfl, rfl, rfl⟩ Y₁ t₁ hK₁ hA₁ hr₁ hg₁ -
    rw [h15, hbx] at hA₁
    have hA' : Agree F Y₁.proc.mm.mem (cV4 S av V p) := by unfold cV4; rw [ite_eq_left hz]; exact hA₁
    exact from127 c hfs hin hK₁ hA' hr₁ hS hstk (by rw [hg₁]; exact hsp) (by rw [hg₁]; exact hbx)
      (by rw [hg₁]; exact hbp) (by rw [hg₁]; exact h12) (by rw [hg₁]) (by rw [hg₁]; exact hdx)
      (by rw [hg₁]; exact h13) (by rw [hg₁]; exact h15) h8 r k
  · refine (c_98 prof fb).run c hfs hin _ hK hA hrip (vc_98l hfu (by rw [hbp]; exact hz) f1 w1 r.w2.1) ?_
    rintro j' g₁ fl V' ⟨rfl, rfl, rfl⟩ Y₁ t₁ hK₁ hA₁ hr₁ hg₁ -
    refine c.s_pxor hK₁ hA₁ hin (lt_len (by decide)) hr₁ (pxor_119 _) ?_
    rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂, hx₂, -⟩
    have e32 : eaD Y₂ 3 32 = cp1 V p + 32#64 := by
      show Y₂.cpu.gpr.rbx + 32#64 = _
      rw [hg₂, hg₁]
      exact congrArg (· + 32#64) hbx
    refine c.s_movups_st hK₂ hA₂ hin (lt_len (by decide)) hr₂ (movups_123 _) (by rw [e32]; exact (r.w3 hz).1) ?_
    rintro Y₃ t₃ hK₃ hA₃ ⟨hr₃, hg₃⟩
    rw [e32, hx₂, BitVec.xor_self, h15, hbx] at hA₃
    have hA' : Agree F Y₃.proc.mm.mem (cV4 S av V p) := by unfold cV4; rw [ite_eq_right hz]; exact hA₃
    have hY : Y₃.cpu.gpr = { X.cpu.gpr with rax := cfu S av V p } := by rw [hg₃, hg₂, hg₁]
    exact from127 c hfs hin hK₃ hA' hr₃ hS hstk (by rw [hY]; exact hsp) (by rw [hY]; exact hbx)
      (by rw [hY]; exact hbp) (by rw [hY]; exact h12) (by rw [hY]) (by rw [hY]; exact hdx)
      (by rw [hY]; exact h13) (by rw [hY]; exact h15) h8 r k

set_option maxHeartbeats 4000000 in
/-- From 256: `nextchunk` the top (`p` the new top), or the forward merge and `from98`. -/
theorem from256 {fb S av fq : Addr} {V : Addr → Byte} {p : Addr} {X : State} {t : Nat}
    (c : Seg prof F Wl L s₀ o) (hfs : s₀.cpu.seg.fsBase = fb) (hin : CodeIn L mcn_at mcn)
    (hinu : CodeIn L Ulk.ulk_at Ulk.ulk)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem (cV1 S V p)) (hrip : X.cpu.rip = mcn_at.add 256)
    (hS : 80 ≤ S.toNat) (hstk : ∀ a : Addr, S.toNat - 80 ≤ a.toNat → a.toNat < S.toNat → Foot Wl a)
    (hsp : X.cpu.gpr.rsp = mB S) (hbx : X.cpu.gpr.rbx = cp1 V p) (hbp : X.cpu.gpr.rbp = cz1 V p)
    (h12 : X.cpu.gpr.r12 = cnc V p) (h14 : X.cpu.gpr.r14 = cns V p) (hdx : X.cpu.gpr.rdx = cnx V p)
    (h13 : X.cpu.gpr.r13 = fq) (h15 : X.cpu.gpr.r15 = av) (h8 : rdq(V, mB S + 8#64) = av + 96#64)
    (hP : CPre F Wl S av fq V p)
    (k : ∀ Y t', KeptW Wl s₀ Y → Agree F Y.proc.mm.mem (cstep S av V p) → Y.cpu.rip = mcn_at.add 156 →
      Y.cpu.gpr.rdx = cnx V p → Y.cpu.gpr.rsp = mB S → Y.cpu.gpr.r13 = fq → Y.cpu.gpr.r15 = av →
      GoG prof L o gev gP gE Y t') :
    GoG prof L o gev gP gE X t := by
  have hl := S.isLt
  have e8 := mB8p_toNat hS
  obtain ⟨sB, sB8⟩ := stB hS hstk
  have f1 : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.r15 + 96#64) i) := by rw [h15]; exact hP.ft
  by_cases ht : ctop S av V p
  · obtain ⟨w1, w2⟩ := hP.tp ht
    refine (c_256 prof fb).run c hfs hin _ hK hA hrip (vc_256t (by rw [h15, h12]; exact ht) f1
      (by rw [hbx]; exact w1.1) (by rw [h15]; exact w2.1)) ?_
    rintro j' g₁ fl V' ⟨rfl, rfl, rfl⟩ Y₁ t₁ hK₁ hA₁ hr₁ hg₁ -
    rw [hbx, hbp, h14, h15] at hA₁
    have hA' : Agree F Y₁.proc.mm.mem (cstep S av V p) := by unfold cstep; rw [ite_eq_left ht]; exact hA₁
    exact k Y₁ t₁ hK₁ hA' hr₁ (by rw [hg₁]; exact hdx) (by rw [hg₁]; exact hsp) (by rw [hg₁]; exact h13)
      (by rw [hg₁]; exact h15)
  obtain ⟨f2, r⟩ := hP.nt ht
  have h8' : rdq(cV4 S av V p, mB S + 8#64) = av + 96#64 :=
    (kf_rd (kf_cV4 hS hP r) (by rw [e8]) (by rw [e8]; omega) (by omega)).trans h8
  have hnt : ¬ rdq(cV1 S V p, X.cpu.gpr.r15 + 96#64) = X.cpu.gpr.r12 := by rw [h15, h12]; exact ht
  have f2' : ∀ i < 1, Foot F.data (Addr.add (X.cpu.gpr.r12 + X.cpu.gpr.r14 + 8#64) i) := by
    rw [h12, h14]; exact f2
  by_cases hn : cnf S V p = true
  · obtain ⟨up, uo⟩ := r.nf hn
    refine (c_256 prof fb).run c hfs hin _ hK hA hrip (vc_256f hnt f1 (by rw [h12, h14]; exact hn) f2'
      (by rw [hsp]; exact sB)) ?_
    rintro j' g₁ fl V' ⟨rfl, rfl, rfl⟩ Y₁ t₁ hK₁ hA₁ hr₁ hg₁ -
    have hsp₁ : Y₁.cpu.gpr.rsp = mB S := by rw [hg₁]; exact hsp
    refine c.s_call hK₁ hA₁ hin (lt_len (by decide)) hr₁ (call_298 _) hinu (Ulk.lt_len (j := 0) (by decide))
      ul_298 (by rw [hsp₁]; exact sB8) ?_
    rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
    rw [hsp₁, hsp, hdx] at hA₂
    have hdi₂ : Y₂.cpu.gpr.rdi = cnc V p := by rw [hg₂]; show Y₁.cpu.gpr.rdi = _; rw [hg₁]; exact h12
    have hsp₂ : Y₂.cpu.gpr.rsp = mB S - 8 := by rw [hg₂]; show Y₁.cpu.gpr.rsp - 8 = _; rw [hsp₁]
    refine Ulk.ulk_ok c hfs hinu hK₂ hA₂ hr₂ (by rw [hdi₂]; exact up)
      (by rw [hsp₂]; exact fun i hi => c.hws _ (sB8 i hi)) hin (lt_len (j := 303) (by decide))
      (by rw [hdi₂, hsp₂]; exact (ulk_rd hS uo).2) ?_
    intro Z t' hKZ hAZ hrZ hspZ hkZ
    rw [hdi₂] at hAZ
    have hspZ' : Z.cpu.gpr.rsp = mB S := by rw [hspZ, hsp₂]; exact BitVec.sub_add_cancel _ _
    obtain ⟨-, kbx, kbp, -, k13, -, k15⟩ := hkZ
    refine (c_303 prof fb).run c hfs hin _ hKZ hAZ hrZ
      (vc_303 (by rw [hspZ']; exact fun i hi => c.hws _ (sB i hi))) ?_
    rintro j' g₃ fl V' ⟨rfl, rfl, rfl⟩ Y₃ t₃ hK₃ hA₃ hr₃ hg₃ -
    have hA' : Agree F Y₃.proc.mm.mem (cV2 S V p) := by unfold cV2; rw [ite_eq_left hn]; exact hA₃
    have zbx : Z.cpu.gpr.rbx = cp1 V p := by rw [kbx, hg₂]; show Y₁.cpu.gpr.rbx = _; rw [hg₁]; exact hbx
    have zbp : Z.cpu.gpr.rbp = cz2 S V p := by
      rw [kbp, hg₂]; show Y₁.cpu.gpr.rbp = _; rw [hg₁]; show X.cpu.gpr.rbp + X.cpu.gpr.r14 = _
      rw [hbp, h14]; unfold cz2; rw [ite_eq_left hn]
    refine from98 c hfs hin hK₃ hA' hr₃ hS hstk (by rw [hg₃]; exact hspZ') (by rw [hg₃]; exact zbx)
      (by rw [hg₃]; exact zbp) ?_ ?_ ?_ ?_ h8' r k
    · rw [hg₃]; show Z.cpu.gpr.rbx + Z.cpu.gpr.rbp = _
      rw [zbx, zbp]; unfold cft; rw [ite_eq_left hn]
    · rw [hg₃]; show rdq(ulkV _ (cnc V p), Z.cpu.gpr.rsp) = _
      rw [hspZ']; exact (ulk_rd hS uo).1
    · rw [hg₃]; show Z.cpu.gpr.r13 = _
      rw [k13, hg₂]; show Y₁.cpu.gpr.r13 = _; rw [hg₁]; exact h13
    · rw [hg₃]; show Z.cpu.gpr.r15 = _
      rw [k15, hg₂]; show Y₁.cpu.gpr.r15 = _; rw [hg₁]; exact h15
  · have hn' : cnf S V p = false := by simpa using hn
    refine (c_256 prof fb).run c hfs hin _ hK hA hrip (vc_256i hnt f1 (by rw [h12, h14]; exact hn') f2') ?_
    rintro j' g₁ fl V' ⟨rfl, rfl, rfl⟩ Y₁ t₁ hK₁ hA₁ hr₁ hg₁ -
    have e : eaD Y₁ 12 8 = cnc V p + 8#64 := by
      show Y₁.cpu.gpr.r12 + 8#64 = _
      rw [hg₁]
      exact congrArg (· + 8#64) h12
    refine c.s_and_mi64 hK₁ hA₁ hin (lt_len (by decide)) hr₁ (and_92 _) (by rw [e]; exact (r.ni hn').1) ?_
    rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
    rw [e] at hA₂
    have hA' : Agree F Y₂.proc.mm.mem (cV2 S V p) := by unfold cV2; rw [ite_eq_right hn]; exact hA₂
    have hY : Y₂.cpu.gpr = X.cpu.gpr := by rw [hg₂, hg₁]
    refine from98 c hfs hin hK₂ hA' hr₂ hS hstk (by rw [hY]; exact hsp) (by rw [hY]; exact hbx) ?_ ?_
      (by rw [hY]; exact hdx) (by rw [hY]; exact h13) (by rw [hY]; exact h15) h8' r k
    · rw [hY, hbp]; unfold cz2; rw [ite_eq_right hn]
    · rw [hY, h12]; unfold cft; rw [ite_eq_right hn]

set_option maxHeartbeats 4000000 in
/-- One chunk: from 164 (`rbx = p`, `r13` its fastbin, `r15 = av`, `rsp = mB S`) to 156 with the bytes `cstep`,
`rdx = nextp`. -/
theorem chunk_ok {fb S av fq : Addr} {V : Addr → Byte} {p : Addr} {X : State} {t : Nat}
    (c : Seg prof F Wl L s₀ o) (hfs : s₀.cpu.seg.fsBase = fb) (hin : CodeIn L mcn_at mcn)
    (hinu : CodeIn L Ulk.ulk_at Ulk.ulk)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = mcn_at.add 164)
    (hS : 80 ≤ S.toNat) (hstk : ∀ a : Addr, S.toNat - 80 ≤ a.toNat → a.toNat < S.toNat → Foot Wl a)
    (hsp : X.cpu.gpr.rsp = mB S) (hbx : X.cpu.gpr.rbx = p) (h13 : X.cpu.gpr.r13 = fq) (h15 : X.cpu.gpr.r15 = av)
    (h8 : rdq(V, mB S + 8#64) = av + 96#64) (hP : CPre F Wl S av fq V p)
    (k : ∀ Y t', KeptW Wl s₀ Y → Agree F Y.proc.mm.mem (cstep S av V p) → Y.cpu.rip = mcn_at.add 156 →
      Y.cpu.gpr.rdx = cnx V p → Y.cpu.gpr.rsp = mB S → Y.cpu.gpr.r13 = fq → Y.cpu.gpr.r15 = av →
      GoG prof L o gev gP gE Y t') :
    GoG prof L o gev gP gE X t := by
  subst hbx h13 h15
  obtain ⟨sB, sB8⟩ := stB hS hstk
  by_cases pf : cpf V X.cpu.gpr.rbx = true
  · obtain ⟨f4, f5, hck, up, uo⟩ := hP.pf pf
    refine (c_164 prof fb).run c hfs hin _ hK hA hrip (vc_164f (sz := csz V X.cpu.gpr.rbx)
      (nx := cnx V X.cpu.gpr.rbx) (ns := rdq(V, cnc V X.cpu.gpr.rbx + 8#64)) (pv := cpv V X.cpu.gpr.rbx) rfl hP.fb
      rfl rfl pf rfl hck hP.f1 hP.f2 hP.f3 f4 f5 (by rw [hsp]; exact sB)) ?_
    rintro j' g₁ fl V' ⟨rfl, rfl, hdi₁, hbx₁, hbp₁, hdx₁, h12₁, h14₁, h13₁, h15₁, hsp₁⟩ Y₁ t₁ hK₁ hA₁ hr₁ hg₁ -
    subst hg₁
    rw [hsp] at hA₁ hsp₁
    refine c.s_call hK₁ hA₁ hin (lt_len (by decide)) hr₁ (call_247 _) hinu (Ulk.lt_len (j := 0) (by decide))
      ul_247 (by rw [hsp₁]; exact sB8) ?_
    rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
    rw [hsp₁] at hA₂
    have hdi₂ : Y₂.cpu.gpr.rdi = X.cpu.gpr.rbx - cpv V X.cpu.gpr.rbx := by rw [hg₂]; exact hdi₁
    have hsp₂ : Y₂.cpu.gpr.rsp = mB S - 8 := by rw [hg₂]; show Y₁.cpu.gpr.rsp - 8 = _; rw [hsp₁]
    refine Ulk.ulk_ok c hfs hinu hK₂ hA₂ hr₂ (by rw [hdi₂]; exact up)
      (by rw [hsp₂]; exact fun i hi => c.hws _ (sB8 i hi)) hin (lt_len (j := 252) (by decide))
      (by rw [hdi₂, hsp₂]; exact (ulk_rd hS uo).2) ?_
    intro Z t' hKZ hAZ hrZ hspZ hkZ
    rw [hdi₂] at hAZ
    have hspZ' : Z.cpu.gpr.rsp = mB S := by rw [hspZ, hsp₂]; exact BitVec.sub_add_cancel _ _
    obtain ⟨-, kbx, kbp, k12, k13, k14, k15⟩ := hkZ
    refine (c_252 prof fb).run c hfs hin _ hKZ hAZ hrZ
      (vc_252 (by rw [hspZ']; exact fun i hi => c.hws _ (sB i hi))) ?_
    rintro j' g₃ fl V' ⟨rfl, rfl, rfl⟩ Y₃ t₃ hK₃ hA₃ hr₃ hg₃ -
    have hA' : Agree F Y₃.proc.mm.mem (cV1 S V X.cpu.gpr.rbx) := by unfold cV1; rw [ite_eq_left pf]; exact hA₃
    refine from256 c hfs hin hinu hK₃ hA' hr₃ hS hstk (by rw [hg₃]; exact hspZ') ?_ ?_ ?_ ?_ ?_ ?_ ?_ h8 hP k
    · rw [hg₃]; show Z.cpu.gpr.rbx = _
      rw [kbx, hg₂]; show Y₁.cpu.gpr.rbx = _; rw [hbx₁]; unfold cp1; rw [ite_eq_left pf]; rfl
    · rw [hg₃]; show Z.cpu.gpr.rbp = _
      rw [kbp, hg₂]; show Y₁.cpu.gpr.rbp = _; rw [hbp₁]; unfold cz1; rw [ite_eq_left pf]; rfl
    · rw [hg₃]; show Z.cpu.gpr.r12 = _
      rw [k12, hg₂]; show Y₁.cpu.gpr.r12 = _; rw [h12₁]; rfl
    · rw [hg₃]; show Z.cpu.gpr.r14 = _
      rw [k14, hg₂]; show Y₁.cpu.gpr.r14 = _; rw [h14₁]; rfl
    · rw [hg₃]; show rdq(ulkV _ _, Z.cpu.gpr.rsp) = _
      rw [hspZ']; exact (ulk_rd hS uo).1
    · rw [hg₃]; show Z.cpu.gpr.r13 = _
      rw [k13, hg₂]; show Y₁.cpu.gpr.r13 = _; exact h13₁
    · rw [hg₃]; show Z.cpu.gpr.r15 = _
      rw [k15, hg₂]; show Y₁.cpu.gpr.r15 = _; exact h15₁
  · have pf' : cpf V X.cpu.gpr.rbx = false := by simpa using pf
    refine (c_164 prof fb).run c hfs hin _ hK hA hrip (vc_164u (sz := csz V X.cpu.gpr.rbx)
      (nx := cnx V X.cpu.gpr.rbx) (ns := rdq(V, cnc V X.cpu.gpr.rbx + 8#64)) rfl hP.fb rfl rfl pf' hP.f1 hP.f2
      hP.f3) ?_
    rintro j' g₁ fl V' ⟨rfl, rfl, hbx₁, hbp₁, hdx₁, h12₁, h14₁, h13₁, h15₁, hsp₁⟩ Y₁ t₁ hK₁ hA₁ hr₁ hg₁ -
    subst hg₁
    have hA' : Agree F Y₁.proc.mm.mem (cV1 S V X.cpu.gpr.rbx) := by unfold cV1; rw [ite_eq_right pf]; exact hA₁
    refine from256 c hfs hin hinu hK₁ hA' hr₁ hS hstk (hsp₁.trans hsp) ?_ ?_ h12₁ h14₁ hdx₁ h13₁ h15₁ h8 hP k
    · rw [hbx₁]; unfold cp1; rw [ite_eq_right pf]
    · rw [hbp₁]; unfold cz1; rw [ite_eq_right pf]; rfl

end

end FV7z.Mcn
