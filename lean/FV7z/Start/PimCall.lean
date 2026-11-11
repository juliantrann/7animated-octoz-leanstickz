import FV7z.Start.OsvCall
import FV7z.Pim.Holds
/-!
# `__libc_start_main` calls `__pthread_initialize_minimal` (PLAN.md G3, startup)

glibc 2.31's `__libc_start_main` from `0x6133f0` to `0x6133ff`: the weak reference to
`__pthread_initialize_minimal` (the slot `0x791fb0`) is not 0 in `7zzs`, so the function at `0x6000b0` is called.

- `PimCode L`: the code of the function and of its callees is in `L`.
- `vc_944`: the verification condition of the test; `call_954`: the `call`, decoded.
- `lsb_pim`: the run from `0x6133f0` to `0x6133ff`: six system calls; the bytes outside the 560 bytes below the
  stack pointer and outside `Pim.PimVar` are as before, the registers a call keeps too.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn FV7z.Start
open FV7z.Sga (vo vr vs)
namespace FV7z.StartB

/-- The code of `__pthread_initialize_minimal_internal` and of its callees is in the run's code. -/
structure PimCode (L : List (Addr × List Byte)) : Prop where
  pim : CodeIn L Pim.pim_at Pim.pim
  sga : CodeIn L Sga.sga_at Sga.sga
  gts : CodeIn L Gts.gts_at Gts.gts
  grl : CodeIn L Grl.grl_at Grl.grl
  lpi : CodeIn L Lpi.lpi_at Lpi.lpi
  raf : CodeIn L Raf.raf_at Raf.raf
  pti : CodeIn L Pti.pti_at Pti.pti
  tgv : CodeIn L Tgv.tgv_at Tgv.tgv

/-! ## The `call` -/

def pc954 : List Byte := [0xe8, 0xb1, 0xcc, 0xfe, 0xff]
theorem pc954_0 : ∀ feat, Dec feat pc954 0 (FV7z.mk .call 64 [.rel 18446744073709472945] 5) := by dec_rfl
set_option maxRecDepth 100000 in
theorem wc954 : pc954 <+: lsm.drop 954 := by decide +kernel
theorem call_954 (feat : Features) : Dec feat lsm 954 (FV7z.mk .call 64 [.rel 18446744073709472945] 5) :=
  Dec.shift (j := 954) (k := 0) (pc954_0 feat) wc954 (Nat.zero_le _)

variable {F : Footprint} {Wl : List Rgn}

/-- The reference to `__pthread_initialize_minimal` is not 0. -/
theorem vc_944 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (h1 : ∀ i < 8, Foot F.data (Addr.add 7937968#64 i)) (hn : rdq(V, 7937968#64) ≠ 0) :
    W_944 fb F Wl (fun j' g' _ V' => j' = 954 ∧ g' = g ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_944, o1, Op.cmpmia]
  exact ⟨h1, fun h => absurd (of_decide_eq_true h) hn, fun _ => trivial⟩

/-! ## The run -/

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop} {X : State} {t : Nat}
  {V : Addr → Byte}

/-- From `0x6133f0` to `0x6133ff`, the return of `__pthread_initialize_minimal`, in a run with one thread, the
locks free and the tunable of the stack's size not set (`Pim.pim_ok`): the bytes outside the 560 bytes below the
stack pointer and outside `Pim.PimVar` are as they were, and so are the registers a call keeps. -/
theorem lsb_pim {lim : Nat} {b fb : Addr} {kst : Kst} (c : Seg prof F Wl L s₀ o) (hB : Base s₀ lim b fb kst)
    (hl : CodeIn L lsm_at lsm) (hP : PimCode L) (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V)
    (hrip : X.cpu.rip = lsm_at.add 944) (hsl : ∀ i < 8, Foot F.data (Addr.add 7937968#64 i))
    (hslot : rdq(V, 7937968#64) ≠ 0) (hL : Pim.Lay F Wl (X.cpu.gpr.rsp - 8) fb)
    (hrw : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8) i)) (h8 : 8 ≤ X.cpu.gpr.rsp.toNat)
    (htop : X.cpu.gpr.rsp.toNat ≤ userPtrMax prof.feat) (hro : ∀ i < 16, Foot F.data (Addr.add 7273168#64 i))
    (hself : rdq(V, fb + 16#64) = fb) (hlk : rdd(V, 8008032#64) = 0) (hmt : rdd(V, fb + 24#64) = 0)
    (hfl : rdd(V, 8011552#64) = 0) (hfg : rdb(V, 8011556#64) = 0) (ht0 : rdd(V, 7936880#64) = 0)
    (htz : rdb(V, 7936912#64) = 0)
    (k : ∀ s₁ Y t' V', Seg prof F Wl L s₁ o → Base s₁ lim b fb kst → KeptW Wl s₁ Y → Agree F Y.proc.mm.mem V' →
      (∀ a : Addr, ¬ (X.cpu.gpr.rsp.toNat - 560 ≤ a.toNat ∧ a.toNat < X.cpu.gpr.rsp.toNat) → ¬ Pim.PimVar fb a →
        V' a = V a) →
      Y.cpu.rip = lsm_at.add 959 → Saved X.cpu.gpr Y.cpu.gpr →
      GoG prof L o (gev ++ [Pim.tidEv (callG X.cpu.gpr) fb kst.tid] ++ [Pim.robEv (callG X.cpu.gpr) fb] ++
        [Pim.sgEv (BitVec.setWidth 64 32#32) X.cpu.gpr.r9 (X.cpu.gpr.rsp - 8)] ++
        [Pim.sgEv (BitVec.setWidth 64 33#32) 0 (X.cpu.gpr.rsp - 8)] ++ [Pim.mskEv (X.cpu.gpr.rsp - 8)] ++
        [Pim.rlEv (X.cpu.gpr.rsp - 8) 0 0 (s₁.proc.signal.rlimits ⟨3, by decide⟩).bytes]) gP gE Y t') :
    GoG prof L o gev gP gE X t := by
  have hsp := hL.hsp
  have hfb := hL.hfb
  have hlo := hL.hlo
  have hlt := X.cpu.gpr.rsp.isLt
  have e8 : (X.cpu.gpr.rsp - 8).toNat = X.cpu.gpr.rsp.toNat - 8 := by bv_omega
  have hf : fb.toNat + 1704 ≤ 2 ^ 64 := by omega
  -- the test
  refine (c_944 prof fb).run c hB.fsb hl _ hK hA hrip (vc_944 hsl hslot) ?_
  rintro j' g fl V₁ ⟨rfl, rfl, rfl⟩ Y₁ t₁ hK₁ hA₁ hr₁ hg₁ -
  -- the call
  refine c.s_call hK₁ hA₁ hl (lt_len (by decide)) hr₁ (call_954 _) hP.pim (Pim.lt_len (by decide)) (by decide)
    (fun i hi => ?_) ?_
  · rw [hg₁]
    exact hrw i hi
  rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
  rw [hg₁] at hA₂ hg₂
  have hsp₂ : Y₂.cpu.gpr.rsp = X.cpu.gpr.rsp - 8 := by rw [hg₂]; rfl
  refine Pim.pim_ok c hB hP.pim hP.sga hP.gts hP.grl hP.lpi hP.raf hP.pti hP.tgv hK₂ hA₂ hr₂ (by rw [hsp₂]; exact hL)
    (by rw [hsp₂]; omega) hro (by rw [hsp₂]; omega) (by rw [hsp₂]; exact fun i hi => c.hws _ (hrw i hi))
    ((congrArg (ofBytesLE 64) (vr (by ln) (by omega) (by bv_omega) (by bv_omega))).trans hself)
    ((congrArg (ofBytesLE 32) (vr (by ln) (by omega) (by decide) (by bv_omega))).trans hlk)
    ((congrArg (ofBytesLE 32) (vr (by ln) (by omega) (by bv_omega) (by bv_omega))).trans hmt)
    ((congrArg (ofBytesLE 32) (vr (by ln) (by omega) (by decide) (by bv_omega))).trans hfl)
    ((congrArg (ofBytesLE 8) (vr (by ln) (by omega) (by decide) (by bv_omega))).trans hfg)
    ((congrArg (ofBytesLE 32) (vr (by ln) (by omega) (by decide) (by bv_omega))).trans ht0)
    ((congrArg (ofBytesLE 8) (vr (by ln) (by omega) (by decide) (by bv_omega))).trans htz)
    hl (j₂ := 959) (lt_len (by decide)) ?_ ?_
  · rw [hsp₂, vs (by ln) (by omega)]
    exact ofBytesLE_toBytesLE (n := 8) rfl _
  intro s₁ V' g' Z t' W am tv sz c₁ hB₁ hKZ hAZ hW hpW ho hrZ hgZ hb
  subst hgZ
  rw [hsp₂, e8] at ho
  rw [hg₂] at hb ⊢
  obtain ⟨b1, b2, b3, b4, b5, b6, b7⟩ := hb
  refine k s₁ Z t' V' c₁ hB₁ hKZ hAZ (fun a ha hv => ?_) hrZ ⟨b1.trans (by show X.cpu.gpr.rsp - 8 + 8#64 = _; bv_omega),
    b2, b3, b4, b5, b6, b7⟩
  have h1 : ¬ (X.cpu.gpr.rsp.toNat - 8 - 552 ≤ a.toNat ∧ a.toNat < X.cpu.gpr.rsp.toNat - 8) := fun ⟨p, q⟩ =>
    ha ⟨by rw [Nat.sub_sub] at p; exact p, Nat.lt_of_lt_of_le q (Nat.sub_le _ _)⟩
  have h2 : a.toNat < (X.cpu.gpr.rsp - 8).toNat ∨ (X.cpu.gpr.rsp - 8).toNat + 8 ≤ a.toNat := by
    rw [e8]
    by_cases q : a.toNat < X.cpu.gpr.rsp.toNat - 8
    · exact .inl q
    · exact .inr (Nat.le_of_not_lt fun q' => ha ⟨Nat.le_trans (Nat.sub_le_sub_left (by decide) _)
        (Nat.le_of_not_lt q), by omega⟩)
  exact (ho a h1).trans ((Pim.MemE_keep hf hW a hv).trans (vo (by ln) (by omega) h2))

end FV7z.StartB
