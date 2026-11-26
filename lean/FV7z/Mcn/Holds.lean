import FV7z.Mcn.Chunk
/-!
# `malloc_consolidate` (PLAN.md §M, M1)

glibc 2.31's `malloc_consolidate (av)` at `0x62eb00` in `7zzs`, one thread. The entry pushes six registers and makes
room for two words (`nextp` at `[rsp]`, `&av->top` at `[rsp + 8]`), clears `av->have_fastchunks`, then for each of
the ten fastbins takes its list (an `xchg` with 0), and runs each chunk through `chunk_ok`. After the last bin the
pops and the `ret`.

`bin_ok`: one fastbin's list from 164 to 48. `bins_ok`: the bins from the `n`-th, from 37 to 48 after the last
one. `mcn_ok`: from the entry to the return address, the bytes `mbins S av 0 chs (mV0 V S av g)`, the registers a
call keeps as they were, `rsp = S + 8`.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
open FV7z.Tun (rd_Vst rd_Vst_self Vst_out)
open FV7z.Stm (Km)
namespace FV7z.Mcn

/-- The bytes after the entry: the six pushes (`S` the entry `rsp`, `g` the registers), `have_fastchunks = 0` and
`&av->top` at `[mB S + 8]`. -/
abbrev mV0 (V : Addr → Byte) (S av : Addr) (g : Gprs) : Addr → Byte :=
  Vst (Vst (fr6 V S g.r15 g.r14 g.r13 g.r12 g.rbp g.rbx) (av + 8#64) (toBytesLE 0#32 4)) (mB S + 8#64)
    (toBytesLE (av + 96#64) 8)

/-! ## Addresses and bytes -/

/-- A quadword read apart from a store. -/
theorem rdo {V : Addr → Byte} {a x : Addr} {w n : Nat} {v : BitVec w} (ha : a.toNat + n ≤ 2 ^ 64)
    (hx : x.toNat + 8 ≤ 2 ^ 64) (h : a.toNat + n ≤ x.toNat ∨ x.toNat + 8 ≤ a.toNat) :
    rdq(Vst V a (toBytesLE v n), x) = rdq(V, x) :=
  congrArg (ofBytesLE 64) (rd_Vst _ _ _ _ _ (by rw [toBytesLE_length]; exact ha) hx (by rw [toBytesLE_length]; exact h))

/-- A quadword read where it was stored. -/
theorem rds {V : Addr → Byte} {a : Addr} {v : BitVec 64} (ha : a.toNat + 8 ≤ 2 ^ 64) :
    rdq(Vst V a (toBytesLE v 8), a) = v := by
  rw [rd_Vst_self _ _ _ (toBytesLE_length _ _) ha]
  exact ofBytesLE_toBytesLE (n := 8) rfl _

theorem fr_e6 {S : Addr} (hS : 80 ≤ S.toNat) : (S - 8).toNat = S.toNat - 8 ∧ (S - 8 - 8).toNat = S.toNat - 16 ∧
    (S - 8 - 8 - 8).toNat = S.toNat - 24 ∧ (S - 8 - 8 - 8 - 8).toNat = S.toNat - 32 ∧
    (S - 8 - 8 - 8 - 8 - 8).toNat = S.toNat - 40 ∧ (S - 8 - 8 - 8 - 8 - 8 - 8).toNat = S.toNat - 48 := by
  obtain ⟨e1, e2, e3, e4⟩ := Cal.fr_e (S := S) (by omega)
  have e5 := Prepare.toNat_sub8 (a := S - 8 - 8 - 8 - 8) (by rw [e4]; omega)
  have e6 := Prepare.toNat_sub8 (a := S - 8 - 8 - 8 - 8 - 8) (by rw [e5, e4]; omega)
  exact ⟨e1, e2, e3, e4, by rw [e5, e4]; omega, by rw [e6, e5, e4]; omega⟩

/-- The pops' addresses as numbers. -/
theorem up_e {S : Addr} (hS : 80 ≤ S.toNat) :
    (mB S + 24#64).toNat = S.toNat - 48 ∧ (mB S + 24#64 + 8).toNat = S.toNat - 40 ∧
    (mB S + 24#64 + 8 + 8).toNat = S.toNat - 32 ∧ (mB S + 24#64 + 8 + 8 + 8).toNat = S.toNat - 24 ∧
    (mB S + 24#64 + 8 + 8 + 8 + 8).toNat = S.toNat - 16 ∧ (mB S + 24#64 + 8 + 8 + 8 + 8 + 8).toNat = S.toNat - 8 ∧
    (mB S + 24#64 + 8 + 8 + 8 + 8 + 8 + 8).toNat = S.toNat := by
  have e := mB_toNat hS
  have hl := S.isLt
  have e0 : (mB S + 24#64).toNat = S.toNat - 48 := by
    rw [BitVec.toNat_add, e, show (24#64).toNat = 24 from rfl]
    omega
  have e1 := Stm.ta8 (a := mB S + 24#64) (by omega)
  have e2 := Stm.ta8 (a := mB S + 24#64 + 8) (by omega)
  have e3 := Stm.ta8 (a := mB S + 24#64 + 8 + 8) (by omega)
  have e4 := Stm.ta8 (a := mB S + 24#64 + 8 + 8 + 8) (by omega)
  have e5 := Stm.ta8 (a := mB S + 24#64 + 8 + 8 + 8 + 8) (by omega)
  have e6 := Stm.ta8 (a := mB S + 24#64 + 8 + 8 + 8 + 8 + 8) (by omega)
  omega

/-- The six saved registers read back. -/
theorem fr6_rd (V : Addr → Byte) (S : Addr) (a b c d e f : BitVec 64) (hS : 80 ≤ S.toNat) :
    rdq(fr6 V S a b c d e f, S - 8 - 8 - 8 - 8 - 8 - 8) = f ∧ rdq(fr6 V S a b c d e f, S - 8 - 8 - 8 - 8 - 8) = e ∧
    rdq(fr6 V S a b c d e f, S - 8 - 8 - 8 - 8) = d ∧ rdq(fr6 V S a b c d e f, S - 8 - 8 - 8) = c ∧
    rdq(fr6 V S a b c d e f, S - 8 - 8) = b ∧ rdq(fr6 V S a b c d e f, S - 8) = a := by
  have hl := S.isLt
  obtain ⟨s1, s2, s3, s4, s5, s6⟩ := fr_e6 hS
  unfold fr6
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [rds]; omega
  · rw [rdo, rds] <;> omega
  · rw [rdo, rdo, rds] <;> omega
  · rw [rdo, rdo, rdo, rds] <;> omega
  · rw [rdo, rdo, rdo, rdo, rds] <;> omega
  · rw [rdo, rdo, rdo, rdo, rdo, rds] <;> omega

/-- In the pushes' slots the entry's bytes are the pushes'. -/
theorem mV0_rd {V : Addr → Byte} {S av : Addr} {g : Gprs} (hS : 80 ≤ S.toNat) (hw : Ow S (av + 8#64) 4) {x : Addr}
    (h1 : S.toNat - 48 ≤ x.toNat) (h2 : x.toNat + 8 ≤ S.toNat) :
    rdq(mV0 V S av g, x) = rdq(fr6 V S g.r15 g.r14 g.r13 g.r12 g.rbp g.rbx, x) := by
  have e := mB8p_toNat hS
  have hl := S.isLt
  obtain ⟨o1, o2⟩ := hw
  unfold mV0
  rw [rdo, rdo] <;> omega

/-- `&av->top` read back where the frame's upper part is kept. -/
theorem rd8 {S : Addr} (hS : 80 ≤ S.toNat) {V V' : Addr → Byte} (h : Kf (S.toNat - 64) S.toNat V V') :
    rdq(V', mB S + 8#64) = rdq(V, mB S + 8#64) := by
  have e := mB8p_toNat hS
  have hl := S.isLt
  exact kf_rd h (by omega) (by omega) (by omega)

theorem fbk_s (av : Addr) (n : Nat) : fbk av n + 8#64 = fbk av (n + 1) := by
  apply BitVec.eq_of_toNat_eq
  simp only [fbk, BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

/-- Not past the last bin: `fb + 8` is not `&av->top`. -/
theorem fbk_ne {av : Addr} {n : Nat} (hn : n ≤ 8) : ¬ av + 96#64 = fbk av n + 8#64 := by
  intro h
  have h' := congrArg BitVec.toNat h
  have hl := av.isLt
  simp only [fbk, BitVec.toNat_add, BitVec.toNat_ofNat] at h'
  omega

theorem fbk_al {av : Addr} (hal : av.toNat % 8 = 0) (n : Nat) : (fbk av n).toNat % 64 + 8 ≤ 64 := by
  have h : (fbk av n).toNat % 8 = 0 := by
    simp only [fbk, BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  omega

/-! ## The loops -/

section
variable {prof : Profile} {F : Footprint} {Wl : List Rgn} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}

/-- One fastbin's list `ps` (the first chunk in `rbx`, `r13` the bin): from 164 to 48 with the bytes `bfold`. -/
theorem bin_ok {fb S av fq : Addr} (c : Seg prof F Wl L s₀ o) (hfs : s₀.cpu.seg.fsBase = fb)
    (hin : CodeIn L mcn_at mcn) (hinu : CodeIn L Ulk.ulk_at Ulk.ulk) (hS : 80 ≤ S.toNat)
    (hstk : ∀ a : Addr, S.toNat - 80 ≤ a.toNat → a.toNat < S.toNat → Foot Wl a) :
    ∀ (ps : List Addr) (V : Addr → Byte) (X : State) (t : Nat), ps ≠ [] →
    KeptW Wl s₀ X → Agree F X.proc.mm.mem V → X.cpu.rip = mcn_at.add 164 → X.cpu.gpr.rsp = mB S →
    X.cpu.gpr.rbx = ps.headD 0#64 → X.cpu.gpr.r13 = fq → X.cpu.gpr.r15 = av → rdq(V, mB S + 8#64) = av + 96#64 →
    BCh F Wl S av fq V ps →
    (∀ Y t', KeptW Wl s₀ Y → Agree F Y.proc.mm.mem (bfold S av V ps) → Y.cpu.rip = mcn_at.add 48 →
      Y.cpu.gpr.rsp = mB S → Y.cpu.gpr.r13 = fq → Y.cpu.gpr.r15 = av → GoG prof L o gev gP gE Y t') →
    GoG prof L o gev gP gE X t
  | [], _, _, _, hne, _, _, _, _, _, _, _, _, _, _ => absurd rfl hne
  | p :: ps, V, X, t, _, hK, hA, hrip, hsp, hbx, h13, h15, h8, ⟨hP, hnx, hs⟩, k => by
    refine chunk_ok (p := p) c hfs hin hinu hK hA hrip hS hstk hsp hbx h13 h15 h8 hP ?_
    intro Y t' hKY hAY hrY hdxY hspY h13Y h15Y
    have h8' : rdq(cstep S av V p, mB S + 8#64) = av + 96#64 := (rd8 hS (kf_cstep hS hP)).trans h8
    by_cases hc : ps = []
    · subst hc
      refine (c_156 prof fb).run c hfs hin _ hKY hAY hrY (vc_156z (by rw [hdxY, hnx]; decide)) ?_
      rintro j' g₁ fl V' ⟨rfl, hV, rfl⟩ Y₁ t₁ hK₁ hA₁ hr₁ hg₁ -
      subst V'
      exact k Y₁ t₁ hK₁ hA₁ hr₁ (by rw [hg₁]; exact hspY) (by rw [hg₁]; exact h13Y) (by rw [hg₁]; exact h15Y)
    · have hq : ps.headD 0#64 ≠ 0#64 := by
        cases ps with
        | nil => exact absurd rfl hc
        | cons q qs => exact hs.1.nz
      refine (c_156 prof fb).run c hfs hin _ hKY hAY hrY
        (vc_156n (by rw [hdxY, hnx]; exact beq_eq_false_iff_ne.mpr hq)) ?_
      rintro j' g₁ fl V' ⟨rfl, hV, rfl⟩ Y₁ t₁ hK₁ hA₁ hr₁ hg₁ -
      subst V'
      exact bin_ok c hfs hin hinu hS hstk ps _ Y₁ t₁ hc hK₁ hA₁ hr₁ (by rw [hg₁]; exact hspY)
        (by rw [hg₁]; exact hdxY.trans hnx) (by rw [hg₁]; exact h13Y) (by rw [hg₁]; exact h15Y) h8' hs k

set_option maxHeartbeats 4000000 in
/-- The bins from the `n`-th (`r13` it, `chs` their lists, the last one the 9th): from 37 to 48 after the last one
with the bytes `mbins`. -/
theorem bins_ok {fb S av : Addr} (c : Seg prof F Wl L s₀ o) (hfs : s₀.cpu.seg.fsBase = fb)
    (hin : CodeIn L mcn_at mcn) (hinu : CodeIn L Ulk.ulk_at Ulk.ulk) (hS : 80 ≤ S.toNat)
    (hstk : ∀ a : Addr, S.toNat - 80 ≤ a.toNat → a.toNat < S.toNat → Foot Wl a) (hal : av.toNat % 8 = 0) :
    ∀ (chs : List (List Addr)) (n : Nat) (V : Addr → Byte) (X : State) (t : Nat), chs ≠ [] →
    n + chs.length = 10 →
    KeptW Wl s₀ X → Agree F X.proc.mm.mem V → X.cpu.rip = mcn_at.add 37 → X.cpu.gpr.rsp = mB S →
    X.cpu.gpr.r13 = fbk av n → X.cpu.gpr.r15 = av → rdq(V, mB S + 8#64) = av + 96#64 → MCh F Wl S av n chs V →
    (∀ Y t', KeptW Wl s₀ Y → Agree F Y.proc.mm.mem (mbins S av n chs V) → Y.cpu.rip = mcn_at.add 48 →
      Y.cpu.gpr.rsp = mB S → Y.cpu.gpr.r13 = fbk av 9 → Y.cpu.gpr.r15 = av → GoG prof L o gev gP gE Y t') →
    GoG prof L o gev gP gE X t
  | [], _, _, _, _, hne, _, _, _, _, _, _, _, _, _, _ => absurd rfl hne
  | ch :: chs, n, V, X, t, _, hn, hK, hA, hrip, hsp, h13, h15, h8, ⟨hw, hhd, hb, hm⟩, k => by
    have hl := S.isLt
    have e8 := mB8p_toNat hS
    have f8 : ∀ i < 8, Foot F.data (Addr.add (mB S + 8#64) i) := fun i hi =>
      c.hws _ (Stm.stk hstk (by rw [e8]; omega) (by rw [e8]; omega) (by omega) i hi)
    have h8₁ : rdq(Vst V (fbk av n) (toBytesLE 0#64 8), mB S + 8#64) = av + 96#64 :=
      (rd8 hS (kf_hi (kf_ow hw.2))).trans h8
    -- from 48: the next bin, or the last one done
    have k48 : ∀ Y t', KeptW Wl s₀ Y → Agree F Y.proc.mm.mem (bfold S av (Vst V (fbk av n) (toBytesLE 0#64 8)) ch) →
        Y.cpu.rip = mcn_at.add 48 → Y.cpu.gpr.rsp = mB S → Y.cpu.gpr.r13 = fbk av n → Y.cpu.gpr.r15 = av →
        GoG prof L o gev gP gE Y t' := by
      intro Y t' hKY hAY hrY hspY h13Y h15Y
      by_cases hc : chs = []
      · subst hc
        have h9 : n = 9 := by simp only [List.length_cons, List.length_nil] at hn; omega
        subst h9
        exact k Y t' hKY hAY hrY hspY h13Y h15Y
      · have hb8 : rdq(bfold S av (Vst V (fbk av n) (toBytesLE 0#64 8)) ch, mB S + 8#64) = av + 96#64 :=
          (rd8 hS (kf_bfold hS ch _ hb)).trans h8₁
        have hn8 : n ≤ 8 := by
          cases chs with
          | nil => exact absurd rfl hc
          | cons _ _ => simp only [List.length_cons] at hn; omega
        refine (c_48 prof fb).run c hfs hin _ hKY hAY hrY
          (vc_48c (by rw [hspY, h13Y, hb8]; exact fbk_ne hn8) (by rw [hspY]; exact f8)) ?_
        rintro j' g₄ fl V' ⟨rfl, hV, rfl⟩ Y₄ t₄ hK₄ hA₄ hr₄ hg₄ -
        subst V'
        exact bins_ok c hfs hin hinu hS hstk hal chs (n + 1) _ Y₄ t₄ hc
          (by simp only [List.length_cons] at hn; omega) hK₄ hA₄ hr₄ (by rw [hg₄]; exact hspY)
          (by rw [hg₄]; show Y.cpu.gpr.r13 + 8#64 = _; rw [h13Y]; exact fbk_s av n) (by rw [hg₄]; exact h15Y) hb8 hm k
    -- 37: `ebx = 0`
    refine (c_37 prof fb).run c hfs hin _ hK hA hrip vc_37 ?_
    rintro j' g₁ fl V' ⟨rfl, hV, rfl⟩ Y₁ t₁ hK₁ hA₁ hr₁ hg₁ -
    subst V'
    -- 39: `xchg [r13], rbx`
    have ea : eaD Y₁ 13 0 = fbk av n := by
      show Y₁.cpu.gpr.r13 + 0#64 = _
      rw [hg₁]
      show X.cpu.gpr.r13 + 0#64 = _
      rw [h13, BitVec.add_zero]
    have hrv : rv Y₁ 64 3 = 0#64 := by
      show (Y₁.cpu.gpr.get (regOf 3)).setWidth 64 = _
      rw [hg₁, BitVec.setWidth_eq]
      rfl
    refine c.s_xchg_bd64 hK₁ hA₁ hin (lt_len (by decide)) hr₁ (xchg_39 _) (by rw [ea]; exact fbk_al hal n)
      (by rw [ea]; exact hw.1) ?_
    rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
    rw [ea, hrv] at hA₂
    have hbx₂ : Y₂.cpu.gpr.rbx = ch.headD 0#64 := by
      rw [hg₂]
      show (ofBytesLE 64 (List.map V (byteAddrs (eaD Y₁ 13 0) 8))).setWidth 64 = _
      rw [ea, BitVec.setWidth_eq]
      exact hhd
    have sp₂ : Y₂.cpu.gpr.rsp = mB S := by rw [hg₂]; show Y₁.cpu.gpr.rsp = _; rw [hg₁]; exact hsp
    have r13₂ : Y₂.cpu.gpr.r13 = fbk av n := by rw [hg₂]; show Y₁.cpu.gpr.r13 = _; rw [hg₁]; exact h13
    have r15₂ : Y₂.cpu.gpr.r15 = av := by rw [hg₂]; show Y₁.cpu.gpr.r15 = _; rw [hg₁]; exact h15
    -- 43: the bin empty, or its chunks
    cases ch with
    | nil =>
      refine (c_43 prof fb).run c hfs hin _ hK₂ hA₂ hr₂ (vc_43z (by rw [hbx₂]; decide)) ?_
      rintro j' g₃ fl V' ⟨rfl, hV, rfl⟩ Y₃ t₃ hK₃ hA₃ hr₃ hg₃ -
      subst V'
      exact k48 Y₃ t₃ hK₃ hA₃ hr₃ (by rw [hg₃]; exact sp₂) (by rw [hg₃]; exact r13₂) (by rw [hg₃]; exact r15₂)
    | cons p ps =>
      refine (c_43 prof fb).run c hfs hin _ hK₂ hA₂ hr₂
        (vc_43n (by rw [hbx₂]; exact beq_eq_false_iff_ne.mpr hb.1.nz)) ?_
      rintro j' g₃ fl V' ⟨rfl, hV, rfl⟩ Y₃ t₃ hK₃ hA₃ hr₃ hg₃ -
      subst V'
      exact bin_ok c hfs hin hinu hS hstk (p :: ps) _ Y₃ t₃ (List.cons_ne_nil _ _) hK₃ hA₃ hr₃
        (by rw [hg₃]; exact sp₂) (by rw [hg₃]; exact hbx₂) (by rw [hg₃]; exact r13₂) (by rw [hg₃]; exact r15₂) h8₁
        hb k48

set_option maxHeartbeats 4000000 in
/-- `malloc_consolidate (av)` from the entry (`rsp = S`) to the return address: the bytes `mbins` of the ten bins'
lists `chs` after the entry's `mV0`, `rsp = S + 8`, the registers a call keeps as they were. -/
theorem mcn_ok {fb S av : Addr} {chs : List (List Addr)} {X : State} {t : Nat} {V : Addr → Byte}
    (c : Seg prof F Wl L s₀ o) (hfs : s₀.cpu.seg.fsBase = fb) (hin : CodeIn L mcn_at mcn)
    (hinu : CodeIn L Ulk.ulk_at Ulk.ulk)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = mcn_at)
    (hdi : X.cpu.gpr.rdi = av) (hsp : X.cpu.gpr.rsp = S) (hS : 80 ≤ S.toNat)
    (hstk : ∀ a : Addr, S.toNat - 80 ≤ a.toNat → a.toNat < S.toNat → Foot Wl a)
    (hlr : ∀ i < 8, Foot F.data (Addr.add S i)) (hal : av.toNat % 8 = 0) (hw4 : Wr Wl S (av + 8#64) 4)
    (hlen : chs.length = 10) (hM : MCh F Wl S av 0 chs (mV0 V S av X.cpu.gpr))
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (hra : rdq(mbins S av 0 chs (mV0 V S av X.cpu.gpr), S) = e₂.add j₂)
    (k : ∀ Y t', KeptW Wl s₀ Y → Agree F Y.proc.mm.mem (mbins S av 0 chs (mV0 V S av X.cpu.gpr)) →
      Y.cpu.rip = e₂.add j₂ → Y.cpu.gpr.rsp = S + 8 → Km X.cpu.gpr Y.cpu.gpr → GoG prof L o gev gP gE Y t') :
    GoG prof L o gev gP gE X t := by
  have hl := S.isLt
  obtain ⟨s1, s2, s3, s4, s5, s6⟩ := fr_e6 hS
  have e8 := mB8p_toNat hS
  obtain ⟨u0, u1, u2, u3, u4, u5, u6⟩ := up_e hS
  -- the entry: the pushes, `have_fastchunks = 0`, `&av->top`
  refine (c_0 prof fb).run c hfs hin _ hK hA (by rw [addr_add_zero]; exact hrip)
    (vc_0 (by rw [hsp]; exact Stm.stk hstk (by rw [s1]; omega) (by rw [s1]; omega) (by omega))
      (by rw [hsp]; exact Stm.stk hstk (by rw [s2]; omega) (by rw [s2]; omega) (by omega))
      (by rw [hsp]; exact Stm.stk hstk (by rw [s3]; omega) (by rw [s3]; omega) (by omega))
      (by rw [hsp]; exact Stm.stk hstk (by rw [s4]; omega) (by rw [s4]; omega) (by omega))
      (by rw [hsp]; exact Stm.stk hstk (by rw [s5]; omega) (by rw [s5]; omega) (by omega))
      (by rw [hsp]; exact Stm.stk hstk (by rw [s6]; omega) (by rw [s6]; omega) (by omega))
      (by rw [hdi]; exact hw4.1)
      (by rw [hsp]; exact Stm.stk hstk (by rw [e8]; omega) (by rw [e8]; omega) (by omega))) ?_
  rintro j' g₁ fl V' ⟨rfl, hV, hsp₁, h15₁, h13₁, -, -, -, -⟩ Y₁ t₁ hK₁ hA₁ hr₁ hg₁ -
  subst V'
  subst hg₁
  rw [hsp, hdi] at hA₁
  have h8₀ : rdq(mV0 V S av X.cpu.gpr, mB S + 8#64) = av + 96#64 := rds (by omega)
  have hne : chs ≠ [] := by
    intro h
    rw [h] at hlen
    exact absurd hlen (by decide)
  refine bins_ok c hfs hin hinu hS hstk hal chs 0 _ Y₁ t₁ hne (by omega) hK₁ hA₁ hr₁ (by rw [hsp₁, hsp])
    (h13₁.trans (congrArg (· + 16#64) hdi)) (h15₁.trans hdi) h8₀ hM ?_
  -- after the last bin: the pops, the `ret`
  intro Y t' hKY hAY hrY hspY h13Y h15Y
  have hm8 : rdq(mbins S av 0 chs (mV0 V S av X.cpu.gpr), mB S + 8#64) = av + 96#64 :=
    (rd8 hS (kf_mbins hS 0 chs _ hM)).trans h8₀
  have fp : ∀ x : Addr, S.toNat - 80 ≤ x.toNat → x.toNat + 8 ≤ S.toNat → ∀ i < 8, Foot F.data (Addr.add x i) :=
    fun x h1 h2 i hi => c.hws _ (Stm.stk hstk h1 h2 (by omega) i hi)
  have sl : ∀ x : Addr, S.toNat - 48 ≤ x.toNat → x.toNat + 8 ≤ S.toNat →
      rdq(mbins S av 0 chs (mV0 V S av X.cpu.gpr), x) =
        rdq(fr6 V S X.cpu.gpr.r15 X.cpu.gpr.r14 X.cpu.gpr.r13 X.cpu.gpr.r12 X.cpu.gpr.rbp X.cpu.gpr.rbx, x) :=
    fun x h1 h2 => (kf_rd (kf_mbins hS 0 chs _ hM) (by omega) h2 (by omega)).trans (mV0_rd hS hw4.2 h1 h2)
  obtain ⟨r6, r5, r4, r3, r2, r1⟩ :=
    fr6_rd V S X.cpu.gpr.r15 X.cpu.gpr.r14 X.cpu.gpr.r13 X.cpu.gpr.r12 X.cpu.gpr.rbp X.cpu.gpr.rbx hS
  have q0 : mB S + 24#64 = S - 8 - 8 - 8 - 8 - 8 - 8 := BitVec.eq_of_toNat_eq (by rw [u0, s6])
  have q1 : mB S + 24#64 + 8 = S - 8 - 8 - 8 - 8 - 8 := BitVec.eq_of_toNat_eq (by rw [u1, s5])
  have q2 : mB S + 24#64 + 8 + 8 = S - 8 - 8 - 8 - 8 := BitVec.eq_of_toNat_eq (by rw [u2, s4])
  have q3 : mB S + 24#64 + 8 + 8 + 8 = S - 8 - 8 - 8 := BitVec.eq_of_toNat_eq (by rw [u3, s3])
  have q4 : mB S + 24#64 + 8 + 8 + 8 + 8 = S - 8 - 8 := BitVec.eq_of_toNat_eq (by rw [u4, s2])
  have q5 : mB S + 24#64 + 8 + 8 + 8 + 8 + 8 = S - 8 := BitVec.eq_of_toNat_eq (by rw [u5, s1])
  have q6 : mB S + 24#64 + 8 + 8 + 8 + 8 + 8 + 8 = S := BitVec.eq_of_toNat_eq u6
  have fbk9 : fbk av 9 + 8#64 = av + 96#64 := (fbk_s av 9).trans rfl
  refine (c_48 prof fb).run c hfs hin _ hKY hAY hrY
    (vc_48e (by rw [hspY, h13Y, hm8]; exact fbk9.symm) (by rw [hspY]; exact fp _ (by omega) (by omega))
      (by rw [hspY]; exact fp _ (by omega) (by omega)) (by rw [hspY]; exact fp _ (by omega) (by omega))
      (by rw [hspY]; exact fp _ (by omega) (by omega)) (by rw [hspY]; exact fp _ (by omega) (by omega))
      (by rw [hspY]; exact fp _ (by omega) (by omega)) (by rw [hspY]; exact fp _ (by omega) (by omega))) ?_
  rintro j' g₂ fl V' ⟨rfl, hV, hsp₂, hbx₂, hbp₂, h12₂, h13₂, h14₂, h15₂⟩ Y₂ t₂ hK₂ hA₂ hr₂ hg₂ -
  subst V'
  subst hg₂
  rw [hspY] at hsp₂ hbx₂ hbp₂ h12₂ h13₂ h14₂ h15₂
  rw [q6] at hsp₂
  refine c.s_ret hK₂ hA₂ hin (lt_len (by decide)) hr₂ (ret_73 _) (by rw [hsp₂]; exact hlr) hin₂ h₂
    (by rw [hsp₂]; exact hra) ?_
  rintro Z t'' hKZ hAZ ⟨hrZ, hgZ⟩
  refine k Z t'' hKZ hAZ hrZ (by rw [hgZ]; show Y₂.cpu.gpr.rsp + 8 = _; rw [hsp₂]) ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hgZ]; show Y₂.cpu.gpr.rbx = _
    rw [hbx₂, sl (mB S + 24#64) (by rw [u0]; omega) (by rw [u0]; omega),
      q0]; exact r6
  · rw [hgZ]; show Y₂.cpu.gpr.rbp = _
    rw [hbp₂, sl (mB S + 24#64 + 8) (by rw [u1]; omega) (by rw [u1]; omega),
      q1]; exact r5
  · rw [hgZ]; show Y₂.cpu.gpr.r12 = _
    rw [h12₂, sl (mB S + 24#64 + 8 + 8) (by rw [u2]; omega) (by rw [u2]; omega),
      q2]; exact r4
  · rw [hgZ]; show Y₂.cpu.gpr.r13 = _
    rw [h13₂, sl (mB S + 24#64 + 8 + 8 + 8) (by rw [u3]; omega) (by rw [u3]; omega),
      q3]; exact r3
  · rw [hgZ]; show Y₂.cpu.gpr.r14 = _
    rw [h14₂, sl (mB S + 24#64 + 8 + 8 + 8 + 8) (by rw [u4]; omega) (by rw [u4]; omega),
      q4]; exact r2
  · rw [hgZ]; show Y₂.cpu.gpr.r15 = _
    rw [h15₂, sl (mB S + 24#64 + 8 + 8 + 8 + 8 + 8) (by rw [u5]; omega) (by rw [u5]; omega),
      q5]; exact r1

end

end FV7z.Mcn
