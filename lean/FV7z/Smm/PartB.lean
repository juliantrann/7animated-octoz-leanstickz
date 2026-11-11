import FV7z.Smm.PartA
/-!
# `sysmalloc`: from the first `MORECORE` to the second (PLAN.md G3, `malloc`)

- `call_1684`: the second `call qword [rip + d]` to `__morecore`.
- `rd_Vb`: a read outside what was stored from 900 to 1644.
- `sm_to2`: the run from offset 900, the first `MORECORE`'s answer in `rax`, to the entry of `__default_morecore`
  called a second time, its argument the correction that ends the heap at a page (`corr2`).
- `lo4_toNat`, `corr_toNat`, `corr2_zero`, `corr2_pos`: the corrections as numbers: the second is 0 when the
  break was a page's start, and otherwise what is left of the break's page.
- `sm_b_s`, `sm_b_z`: from offset 900 to offset 1690, the return of the second `MORECORE`, with
  `Dmc.dmc_same` (the break moves within its page; a new start) and `Dmc.dmc_zero` (no system call).
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn FV7z.Start
open FV7z.Tun (rd_Vst rd_Vst_self Vst_out)
open FV7z.Brk (curbrk)
open FV7z.Sbrk (sbrkEv)
namespace FV7z.Smm

/-! ## The instruction outside the blocks -/

def pc1684 : List Byte := [0xff, 0x15, 0xde, 0x28, 0x16, 0x00]
theorem pc1684_0 : ∀ feat, Dec feat pc1684 0 (FV7z.mk .call 64 [.mem (mrip 1452254 64)] 6) := by dec_rfl
theorem w_1684 : pc1684 <+: smm.drop 1684 := by decide +kernel
/-- `call *__morecore`, the second. -/
theorem call_1684 (feat : Features) : Dec feat smm 1684 (FV7z.mk .call 64 [.mem (mrip 1452254 64)] 6) :=
  Dec.shift (j := 1684) (k := 0) (pc1684_0 feat) w_1684 (Nat.zero_le _)

theorem mc_at2 : smm_at.add (1684 + 6) + BitVec.ofNat 64 1452254 = 7942872#64 := by decide

/-! ## The bytes -/

/-- A read that is not of `mp_.sbrk_base`, `av->system_mem` or the frame's second word, in the bytes at 1644. -/
theorem rd_Vb {g : Gprs} {V : Addr → Byte} {sm : BitVec 64} {x : Addr} {n : Nat} (hx : x.toNat + n ≤ 2 ^ 64)
    (hsp : g.rsp.toNat + 16 ≤ 2 ^ 64)
    (h1 : x.toNat + n ≤ 7940584 ∨ 7940592 ≤ x.toNat) (h2 : x.toNat + n ≤ 7942856 ∨ 7942864 ≤ x.toNat)
    (h3 : x.toNat + n ≤ g.rsp.toNat + 8 ∨ g.rsp.toNat + 16 ≤ x.toNat) :
    List.map (Vb g V sm) (byteAddrs x n) = List.map V (byteAddrs x n) := by
  show List.map (Vst (Vst (Vst V _ _) _ _) _ _) _ = _
  rw [rd_Vst _ _ _ _ _ (by simp only [toBytesLE_length]; bv_omega) hx
      (h3.elim (fun h => .inr (by sd)) fun h => .inl (by sd)),
    rd_Vst _ _ _ _ _ (by simp only [toBytesLE_length]; decide) hx
      (h2.elim (fun h => .inr (by sd)) fun h => .inl (by sd)),
    rd_Vst _ _ _ _ _ (by simp only [toBytesLE_length]; decide) hx
      (h1.elim (fun h => .inr (by sd)) fun h => .inl (by sd))]

/-! ## The run -/

variable {F : Footprint} {Wl : List Rgn} {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop} {X : State} {t : Nat}
  {V : Addr → Byte}

/-- From offset 900 with the first `MORECORE`'s answer `b` in `rax` (not 0, not the old top's end), no
`__after_morecore_hook`, `mp_.sbrk_base` 0 and the old size 0, to the entry of `__default_morecore` called from
1684: `rdi` is `corr2 b (corr b) size`, the bytes are `Vb` and the return address below the frame. -/
theorem sm_to2 {sm : BitVec 64} (c : Seg prof F Wl L s₀ o) (hin : CodeIn L smm_at smm)
    (hinD : CodeIn L Dmc.dmc_at Dmc.dmc)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = smm_at.add 900)
    (hsp : 8029888 + 8 ≤ X.cpu.gpr.rsp.toNat) (hsp2 : X.cpu.gpr.rsp.toNat + 104 ≤ 2 ^ 64)
    (hst : ∀ i < 104, Foot Wl (Addr.add X.cpu.gpr.rsp i))
    (hlr : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8) i))
    (hW : ∀ a : Addr, 7940480 ≤ a.toNat → a.toNat < 7943136 → Foot Wl a)
    (hhk : ∀ i < 8, Foot F.data (Addr.add (8013152#64) i))
    (hb0 : X.cpu.gpr.rax ≠ 0#64) (hbe : X.cpu.gpr.rax ≠ 7940768#64) (h12 : X.cpu.gpr.r12 = 0#64)
    (r0 : rdq(V, X.cpu.gpr.rsp) = 4096#64 + 18446744073709551615#64)
    (r1 : rdq(V, X.cpu.gpr.rsp + 8#64) = 7940768#64) (r2 : rdq(V, X.cpu.gpr.rsp + 16#64) = 0 - 4096#64)
    (hk : rdq(V, 8013152#64) = 0#64) (hsm : rdq(V, 7942856#64) = sm) (hsb : rdq(V, 7940584#64) = 0#64)
    (hfl : ofBytesLE 8 ((byteAddrs (7940676#64) 1).map V) &&& 2#8 = 0#8)
    (hmc : rdq(V, 7942872#64) = Dmc.dmc_at)
    (hm : (corr2 X.cpu.gpr.rax (corr X.cpu.gpr.rax) X.cpu.gpr.r14).toNat < 2 ^ 63)
    (k : ∀ Y t', KeptW Wl s₀ Y →
      Agree F Y.proc.mm.mem (Vst (Vb X.cpu.gpr V sm) (X.cpu.gpr.rsp - 8) (toBytesLE (smm_at.add (1684 + 6)) 8)) →
      Y.cpu.rip = Dmc.dmc_at → Y.cpu.gpr.rsp = X.cpu.gpr.rsp - 8 →
      Y.cpu.gpr.rdi = corr2 X.cpu.gpr.rax (corr X.cpu.gpr.rax) X.cpu.gpr.r14 →
      (Y.cpu.gpr.rbx = X.cpu.gpr.rbx ∧ Y.cpu.gpr.rbp = X.cpu.gpr.rbp ∧ Y.cpu.gpr.r12 = 0#64 ∧
        Y.cpu.gpr.r13 = X.cpu.gpr.r13 ∧
        Y.cpu.gpr.r14 = corr2 X.cpu.gpr.rax (corr X.cpu.gpr.rax) X.cpu.gpr.r14 ∧
        Y.cpu.gpr.r15 = X.cpu.gpr.r15) →
      (Y.cpu.gpr.rsi = corr X.cpu.gpr.rax + X.cpu.gpr.r14 ∧
        Y.cpu.gpr.rdx = X.cpu.gpr.rax + (corr X.cpu.gpr.rax + X.cpu.gpr.r14) ∧
        Y.cpu.gpr.r10 = 0 - 4096#64 ∧ Y.cpu.gpr.r8 = X.cpu.gpr.rax ∧ Y.cpu.gpr.r9 = X.cpu.gpr.r9) →
      GoG prof L o gev gP gE Y t') :
    GoG prof L o gev gP gE X t := by
  -- to 1644
  refine (c_900 prof).run c hin _ hK hA hrip
    (vc_900 (sm := sm) (by omega) hsp2 hst c.hws hW hhk hb0 hbe h12 r1 r2 hk hsm hsb hfl) ?_
  rintro j' g fl V₁ ⟨rfl, rfl, rfl⟩ Y₁ t₁ hK₁ hA₁ hr₁ hg₁ -
  have e₁ : Y₁.cpu.gpr.rsp = X.cpu.gpr.rsp := by rw [hg₁]
  have r0' : rdq(Vb X.cpu.gpr V sm, X.cpu.gpr.rsp) = 4096#64 + 18446744073709551615#64 := by
    rw [rd_Vb (by omega) (by omega) (.inr (by omega)) (.inr (by omega)) (.inl (by omega))]
    exact r0
  -- to the call
  refine (c_1644 prof).run c hin _ hK₁ hA₁ hr₁
    (vc_1644 (by rw [e₁]; exact fun i hi => c.hws _ (hst i (by omega))) (by rw [e₁]; exact r0') (by rw [hg₁])
      (by rw [hg₁]; exact hm)) ?_
  rintro j' g fl V₂ ⟨rfl, rfl, rfl⟩ Y₂ t₂ hK₂ hA₂ hr₂ hg₂ -
  have e₂ : Y₂.cpu.gpr.rsp = X.cpu.gpr.rsp := by rw [hg₂, hg₁]
  -- `call *__morecore`
  refine c.s_callR hK₂ hA₂ hin (lt_len (by decide)) hr₂ (call_1684 _) (fun i hi => ?_) hinD
    (Dmc.lt_len (j := 0) (by decide)) ?_ (fun i hi => ?_) ?_
  · rw [mc_at2]
    exact c.hws _ (hW _ (by simp only [Addr.add]; bv_omega) (by simp only [Addr.add]; bv_omega))
  · rw [mc_at2, rd_Vb (by decide) (by omega) (.inr (by decide)) (.inr (by decide)) (.inl (by bv_omega))]
    exact hmc
  · rw [e₂]
    exact hlr i hi
  rintro Y₃ t₃ hK₃ hA₃ ⟨hr₃, hg₃⟩
  rw [e₂] at hA₃ hg₃
  refine k Y₃ t₃ hK₃ hA₃ hr₃ (by rw [hg₃]; rfl) (by rw [hg₃, hg₂, hg₁]; rfl) ?_ ?_
  · rw [hg₃, hg₂, hg₁]
    exact ⟨rfl, rfl, h12, rfl, rfl, rfl⟩
  · rw [hg₃, hg₂, hg₁]
    exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-! ## The corrections, as numbers -/

/-- The low four bits, as a number. -/
theorem lo4_toNat (b : BitVec 64) : (lo4 b).toNat = b.toNat % 16 := by
  have h := Nat.and_two_pow_sub_one_eq_mod (b.toNat % 2 ^ 32) 4
  simp only [lo4, BitVec.toNat_setWidth, BitVec.toNat_and, BitVec.toNat_ofNat]
  have e : (15 % 2 ^ 32 : Nat) = 2 ^ 4 - 1 := by decide
  rw [e, h]
  omega

/-- The correction, as a number. -/
theorem corr_toNat (b : BitVec 64) : (corr b).toNat = (16 - b.toNat % 16) % 16 := by
  have hl := lo4_toNat b
  by_cases hz : (BitVec.setWidth 32 b &&& 15#32 == 0) = true
  · have hc : corr b = 0#64 := by simp only [corr, hz, ↓reduceIte]
    have h0 : lo4 b = 0#64 := by
      rw [beq_iff_eq] at hz
      show BitVec.setWidth 64 (BitVec.setWidth 32 b &&& 15#32) = 0#64
      rw [hz]
      rfl
    rw [h0] at hl
    rw [hc]
    have : b.toNat % 16 = 0 := by simpa using hl.symm
    omega
  · have hc : corr b = 16#64 - lo4 b := by simp only [corr, hz, Bool.false_eq_true, ↓reduceIte]
    have hn : (lo4 b).toNat ≠ 0 := by
      intro h
      apply hz
      rw [beq_iff_eq]
      apply BitVec.eq_of_toNat_eq
      have h2 : (lo4 b).toNat = (BitVec.setWidth 32 b &&& 15#32).toNat % 2 ^ 64 := BitVec.toNat_setWidth ..
      have h3 := (BitVec.setWidth 32 b &&& 15#32).isLt
      rw [h2] at h
      show (BitVec.setWidth 32 b &&& 15#32).toNat = 0
      omega
    rw [hc]
    bv_omega

/-- The break after the first `MORECORE` a page's start: no correction, and the second `MORECORE` is of 0 bytes. -/
theorem corr2_zero {b R : BitVec 64} (hb : b.toNat % 4096 = 0) (hR : R.toNat % 4096 = 0)
    (h : b.toNat + R.toNat < 2 ^ 48) : corr2 b (corr b) R = 0#64 := by
  have hc := corr_toNat b
  have h2 := corr2_toNat b (corr b) R (by omega)
  apply BitVec.eq_of_toNat_eq
  rw [h2]
  show _ = 0
  omega

/-- The break after the first `MORECORE` not a page's start: the second `MORECORE` is of what is left of its page. -/
theorem corr2_pos {b R : BitVec 64} (hb : b.toNat % 4096 ≠ 0) (hR : R.toNat % 4096 = 0)
    (h : b.toNat + R.toNat < 2 ^ 48) :
    (corr2 b (corr b) R).toNat = pageUp (b.toNat + R.toNat) - (b.toNat + R.toNat) ∧
      0 < (corr2 b (corr b) R).toNat ∧ (corr2 b (corr b) R).toNat < 4096 := by
  have hc := corr_toNat b
  have h2 := corr2_toNat b (corr b) R (by omega)
  rw [h2]
  unfold pageUp
  omega

/-! ## The second `MORECORE` -/

/-- A byte of the 56 below the frame: the return address of the call and the 48 bytes of `__default_morecore`. -/
theorem below56 {sp a : Addr} (hlo : ∀ i < 56, Foot Wl (Addr.add (sp - 56) i)) (hs : 56 ≤ sp.toNat)
    (h1 : sp.toNat - 56 ≤ a.toNat) (h2 : a.toNat < sp.toNat) : Foot Wl a := by
  have e : Addr.add (sp - 56) (a.toNat - (sp.toNat - 56)) = a := by
    simp only [Addr.add]
    bv_omega
  exact e ▸ hlo (a.toNat - (sp.toNat - 56)) (by omega)

/-- The event of the `brk` of the second `MORECORE`, from the registers at 900. -/
abbrev smEv2 (g : Gprs) : Event :=
  ⟨12, [g.rax + g.r14 + corr2 g.rax (corr g.rax) g.r14, corr g.rax + g.r14, g.rax + (corr g.rax + g.r14),
    0 - 4096#64, g.rax, g.r9], g.rax + g.r14 + corr2 g.rax (corr g.rax) g.r14, [], []⟩

/-- From offset 900 to offset 1690, the break before the first `MORECORE` (`b`, in `rax`) not a page's start: the
second `MORECORE` moves the break `b'` to the end of its page, with no new page. The run goes on from a new start
with `Base` of the break `b' + corr2`; `rax` is `b'`, `r14` the second correction, the frame's registers are as at
900, and the bytes are `Vb` but for the 56 below the frame and `__curbrk`. -/
theorem sm_b_s {lim : Nat} {b' fsb : Addr} {ks : Kst} {sm : BitVec 64} (c : Seg prof F Wl L s₀ o)
    (hB : Base s₀ lim b' fsb ks) (hin : CodeIn L smm_at smm) (hinD : CodeIn L Dmc.dmc_at Dmc.dmc)
    (hinS : CodeIn L Sbrk.sbk_at Sbrk.sbk) (hinb : CodeIn L Brk.brk_at Brk.brk)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = smm_at.add 900)
    (hb' : b' = X.cpu.gpr.rax + X.cpu.gpr.r14) (hbl : 8029888 ≤ X.cpu.gpr.rax.toNat)
    (hbu : X.cpu.gpr.rax.toNat < 2 ^ 47) (hR : X.cpu.gpr.r14.toNat % 4096 = 0)
    (hR1 : X.cpu.gpr.r14.toNat < 2 ^ 47) (hbn : X.cpu.gpr.rax.toNat % 4096 ≠ 0)
    (hsp : 8029888 + 56 ≤ X.cpu.gpr.rsp.toNat) (hsp2 : X.cpu.gpr.rsp.toNat + 104 ≤ 2 ^ 64)
    (hst : ∀ i < 104, Foot Wl (Addr.add X.cpu.gpr.rsp i))
    (hlo : ∀ i < 56, Foot Wl (Addr.add (X.cpu.gpr.rsp - 56) i))
    (hW : ∀ a : Addr, 7940480 ≤ a.toNat → a.toNat < 7943136 → Foot Wl a)
    (hhk : ∀ i < 8, Foot F.data (Addr.add (8013152#64) i))
    (hcur : ∀ i < 8, Foot Wl (curbrk.add i)) (hml : ∀ i < 4, Foot F.data (Addr.add (7944640#64) i))
    (h12 : X.cpu.gpr.r12 = 0#64)
    (r0 : rdq(V, X.cpu.gpr.rsp) = 4096#64 + 18446744073709551615#64)
    (r1 : rdq(V, X.cpu.gpr.rsp + 8#64) = 7940768#64) (r2 : rdq(V, X.cpu.gpr.rsp + 16#64) = 0 - 4096#64)
    (hk : rdq(V, 8013152#64) = 0#64) (hsm : rdq(V, 7942856#64) = sm) (hsb : rdq(V, 7940584#64) = 0#64)
    (hfl : ofBytesLE 8 ((byteAddrs (7940676#64) 1).map V) &&& 2#8 = 0#8)
    (hmc : rdq(V, 7942872#64) = Dmc.dmc_at)
    (hcb : rdq(V, curbrk) = b') (hm0 : rdd(V, 7944640#64) = 0) (hmg : ∀ t p, o t (.memFail p) = none)
    (k : ∀ V₃ s₁ Z t', Seg prof F Wl L s₁ o →
      Base s₁ lim (b' + corr2 X.cpu.gpr.rax (corr X.cpu.gpr.rax) X.cpu.gpr.r14) fsb ks → KeptW Wl s₁ Z →
      Agree F Z.proc.mm.mem V₃ → Z.cpu.rip = smm_at.add 1690 → Z.cpu.gpr.rax = b' → Z.cpu.gpr.rdx = 0 →
      (Z.cpu.gpr.rsp = X.cpu.gpr.rsp ∧ Z.cpu.gpr.rbx = X.cpu.gpr.rbx ∧ Z.cpu.gpr.rbp = X.cpu.gpr.rbp ∧
        Z.cpu.gpr.r12 = 0#64 ∧ Z.cpu.gpr.r13 = X.cpu.gpr.r13 ∧
        Z.cpu.gpr.r14 = corr2 X.cpu.gpr.rax (corr X.cpu.gpr.rax) X.cpu.gpr.r14 ∧
        Z.cpu.gpr.r15 = X.cpu.gpr.r15) →
      (∀ a : Addr, ¬ (X.cpu.gpr.rsp.toNat - 56 ≤ a.toNat ∧ a.toNat < X.cpu.gpr.rsp.toNat) →
        ¬ (0x7a4c38 ≤ a.toNat ∧ a.toNat < 0x7a4c40) → V₃ a = Vb X.cpu.gpr V sm a) →
      rdq(V₃, curbrk) = b' + corr2 X.cpu.gpr.rax (corr X.cpu.gpr.rax) X.cpu.gpr.r14 →
      GoG prof L o (gev ++ [smEv2 X.cpu.gpr]) gP gE Z t') :
    GoG prof L o gev gP gE X t := by
  have hbt := hB.brk_lt
  obtain ⟨hD, hD0, hD4⟩ := corr2_pos hbn hR (by omega)
  have hbn' : b'.toNat = X.cpu.gpr.rax.toNat + X.cpu.gpr.r14.toNat := by
    rw [hb', BitVec.toNat_add]
    omega
  have hcu : curbrk.toNat = 8014904 := by decide
  refine sm_to2 (sm := sm) c hin hinD hK hA hrip (by omega) hsp2 hst
    (fun i hi => below56 hlo (by omega) (by simp only [Addr.add]; bv_omega) (by simp only [Addr.add]; bv_omega))
    hW hhk (by intro h; rw [h] at hbl; exact absurd hbl (by decide))
    (by intro h; rw [h] at hbl; exact absurd hbl (by decide)) h12 r0 r1 r2 hk hsm hsb hfl hmc (by omega) ?_
  intro Y t₁ hK₁ hA₁ hr₁ hsp₁ hdi₁ ⟨y1, y2, y3, y4, y5, y6⟩ ⟨u1, u2, u3, u4, u5⟩
  have ev : sbrkEv Y (b' + corr2 X.cpu.gpr.rax (corr X.cpu.gpr.rax) X.cpu.gpr.r14)
      (b' + corr2 X.cpu.gpr.rax (corr X.cpu.gpr.rax) X.cpu.gpr.r14) = smEv2 X.cpu.gpr := by
    simp only [sbrkEv, smEv2, u1, u2, u3, u4, u5, hb']
  refine Dmc.dmc_same c hB hinD hinS hinb hK₁ hA₁ hr₁ hcur hml (fun i hi => ?_) (fun i hi => ?_)
    (by rw [hsp₁]; bv_omega) (by rw [hsp₁]; bv_omega) ?_ ?_ (by rw [hdi₁]; omega) (by rw [hdi₁]; omega) hmg ?_
    hin (j₂ := 1690) (lt_len (by decide)) ?_ ?_
  · rw [hsp₁]
    exact below56 hlo (by omega) (by simp only [Addr.add]; bv_omega) (by simp only [Addr.add]; bv_omega)
  · rw [hsp₁]
    exact below56 hlo (by omega) (by simp only [Addr.add]; bv_omega) (by simp only [Addr.add]; bv_omega)
  · rw [rd_Vst _ _ _ _ _ (by sd) (by sd) (by sd),
      rd_Vb (by omega) (by omega) (.inr (by omega)) (.inr (by omega)) (.inl (by omega))]
    exact hcb
  · rw [rd_Vst _ _ _ _ _ (by sd) (by sd) (by sd),
      rd_Vb (by decide) (by omega) (.inr (by decide)) (.inr (by decide)) (.inl (by bv_omega))]
    exact hm0
  · rw [hdi₁]
    have e : (b' + corr2 X.cpu.gpr.rax (corr X.cpu.gpr.rax) X.cpu.gpr.r14).toNat =
        b'.toNat + (corr2 X.cpu.gpr.rax (corr X.cpu.gpr.rax) X.cpu.gpr.r14).toNat := by
      rw [BitVec.toNat_add]
      omega
    rw [e, hbn', hD]
    unfold pageUp
    omega
  · rw [hsp₁, rd_Vst_self _ _ _ (by sd) (by sd), ofBytesLE_toBytesLE (n := 8) rfl]
  rw [hdi₁, ev]
  intro V₂ s₁ Z t' c' hB' hKz hAz hrz hax hdx ⟨s1, s2, s3, s4, s5, s6, s7⟩ hfr hq
  refine k V₂ s₁ Z t' c' hB' hKz hAz hrz hax hdx ⟨s1.trans (by rw [hsp₁]; bv_omega), s2.trans y1, s3.trans y2,
    s4.trans y3, s5.trans y4, s6.trans y5, s7.trans y6⟩ ?_ hq
  intro a h1 h3
  rw [hfr a (by rw [hsp₁]; bv_omega) h3, Vst_out _ _ _ _ (by sd) (by simp only [toBytesLE_length]; bv_omega)]

/-- From offset 900 to offset 1690, the break before the first `MORECORE` (`b`, in `rax`) a page's start: the second
`MORECORE` is of 0 bytes, with no system call. `rax` is the break `b'`, `r14` is 0, the frame's registers are as
at 900, and the bytes are `Vb` but for the 56 below the frame. -/
theorem sm_b_z {lim : Nat} {b' fsb : Addr} {ks : Kst} {sm : BitVec 64} (c : Seg prof F Wl L s₀ o)
    (hB : Base s₀ lim b' fsb ks) (hin : CodeIn L smm_at smm) (hinD : CodeIn L Dmc.dmc_at Dmc.dmc)
    (hinS : CodeIn L Sbrk.sbk_at Sbrk.sbk)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = smm_at.add 900)
    (hbl : 8029888 ≤ X.cpu.gpr.rax.toNat)
    (hbu : X.cpu.gpr.rax.toNat < 2 ^ 47) (hR : X.cpu.gpr.r14.toNat % 4096 = 0)
    (hR1 : X.cpu.gpr.r14.toNat < 2 ^ 47) (hbz : X.cpu.gpr.rax.toNat % 4096 = 0)
    (hsp : 8029888 + 56 ≤ X.cpu.gpr.rsp.toNat) (hsp2 : X.cpu.gpr.rsp.toNat + 104 ≤ 2 ^ 64)
    (hst : ∀ i < 104, Foot Wl (Addr.add X.cpu.gpr.rsp i))
    (hlo : ∀ i < 56, Foot Wl (Addr.add (X.cpu.gpr.rsp - 56) i))
    (hW : ∀ a : Addr, 7940480 ≤ a.toNat → a.toNat < 7943136 → Foot Wl a)
    (hhk : ∀ i < 8, Foot F.data (Addr.add (8013152#64) i))
    (hcur : ∀ i < 8, Foot Wl (curbrk.add i)) (hml : ∀ i < 4, Foot F.data (Addr.add (7944640#64) i))
    (h12 : X.cpu.gpr.r12 = 0#64)
    (r0 : rdq(V, X.cpu.gpr.rsp) = 4096#64 + 18446744073709551615#64)
    (r1 : rdq(V, X.cpu.gpr.rsp + 8#64) = 7940768#64) (r2 : rdq(V, X.cpu.gpr.rsp + 16#64) = 0 - 4096#64)
    (hk : rdq(V, 8013152#64) = 0#64) (hsm : rdq(V, 7942856#64) = sm) (hsb : rdq(V, 7940584#64) = 0#64)
    (hfl : ofBytesLE 8 ((byteAddrs (7940676#64) 1).map V) &&& 2#8 = 0#8)
    (hmc : rdq(V, 7942872#64) = Dmc.dmc_at)
    (hcb : rdq(V, curbrk) = b') (hm0 : rdd(V, 7944640#64) = 0)
    (k : ∀ V₃ Z t', KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V₃ → Z.cpu.rip = smm_at.add 1690 →
      Z.cpu.gpr.rax = b' → Z.cpu.gpr.rdx = 0 →
      (Z.cpu.gpr.rsp = X.cpu.gpr.rsp ∧ Z.cpu.gpr.rbx = X.cpu.gpr.rbx ∧ Z.cpu.gpr.rbp = X.cpu.gpr.rbp ∧
        Z.cpu.gpr.r12 = 0#64 ∧ Z.cpu.gpr.r13 = X.cpu.gpr.r13 ∧ Z.cpu.gpr.r14 = 0#64 ∧
        Z.cpu.gpr.r15 = X.cpu.gpr.r15) →
      (∀ a : Addr, ¬ (X.cpu.gpr.rsp.toNat - 56 ≤ a.toNat ∧ a.toNat < X.cpu.gpr.rsp.toNat) →
        V₃ a = Vb X.cpu.gpr V sm a) →
      GoG prof L o gev gP gE Z t') :
    GoG prof L o gev gP gE X t := by
  have hbt := hB.brk_lt
  have hz := corr2_zero hbz hR (by omega)
  have hcu : curbrk.toNat = 8014904 := by decide
  refine sm_to2 (sm := sm) c hin hinD hK hA hrip (by omega) hsp2 hst
    (fun i hi => below56 hlo (by omega) (by simp only [Addr.add]; bv_omega) (by simp only [Addr.add]; bv_omega))
    hW hhk (by intro h; rw [h] at hbl; exact absurd hbl (by decide))
    (by intro h; rw [h] at hbl; exact absurd hbl (by decide)) h12 r0 r1 r2 hk hsm hsb hfl hmc
    (by rw [hz]; decide) ?_
  intro Y t₁ hK₁ hA₁ hr₁ hsp₁ hdi₁ ⟨y1, y2, y3, y4, y5, y6⟩ _
  refine Dmc.dmc_zero c hB hinD hinS hK₁ hA₁ hr₁ (fun i hi => c.hws _ (hcur i hi)) hml (fun i hi => ?_)
    (fun i hi => ?_) (by rw [hsp₁]; bv_omega) (by rw [hsp₁]; bv_omega) ?_ ?_ (hdi₁.trans hz) hin (j₂ := 1690)
    (lt_len (by decide)) ?_ ?_
  · rw [hsp₁]
    exact below56 hlo (by omega) (by simp only [Addr.add]; bv_omega) (by simp only [Addr.add]; bv_omega)
  · rw [hsp₁]
    exact below56 hlo (by omega) (by simp only [Addr.add]; bv_omega) (by simp only [Addr.add]; bv_omega)
  · rw [rd_Vst _ _ _ _ _ (by sd) (by sd) (by sd),
      rd_Vb (by omega) (by omega) (.inr (by omega)) (.inr (by omega)) (.inl (by omega))]
    exact hcb
  · rw [rd_Vst _ _ _ _ _ (by sd) (by sd) (by sd),
      rd_Vb (by decide) (by omega) (.inr (by decide)) (.inr (by decide)) (.inl (by bv_omega))]
    exact hm0
  · rw [hsp₁, rd_Vst_self _ _ _ (by sd) (by sd), ofBytesLE_toBytesLE (n := 8) rfl]
  intro V₂ Z t' hKz hAz hrz hax hdx ⟨s1, s2, s3, s4, s5, s6, s7⟩ hfr
  refine k V₂ Z t' hKz hAz hrz hax hdx ⟨s1.trans (by rw [hsp₁]; bv_omega), s2.trans y1, s3.trans y2,
    s4.trans y3, s5.trans y4, s6.trans (y5.trans hz), s7.trans y6⟩ ?_
  intro a h1
  rw [hfr a (by rw [hsp₁]; bv_omega), Vst_out _ _ _ _ (by sd) (by simp only [toBytesLE_length]; bv_omega)]

end FV7z.Smm
