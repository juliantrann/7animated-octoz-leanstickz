import FV7z.Pim.DVc
/-!
# `__pthread_initialize_minimal_internal`: the default attributes, the hooks and the return (PLAN.md G3, startup)

The last stretch of the function at `0x6000b0`, from offset 545, over the verification conditions of `Pim/DVc.lean`:

- `pim_d1`: the lock of `__default_pthread_attr` taken and released, the two sizes, the two hooks,
  `__libc_pthread_init`, to offset 647.
- `pim_d2`: `__is_smp`, the pointer, `__pthread_tunables_init`, the stack guard, the two registers back, the `ret`.
- `pim_d`: the two.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn FV7z.Start
open FV7z.Sga (vo vr vs)
open FV7z.Raf (off_ft)
namespace FV7z.Pim

variable {F : Footprint} {Wl : List Rgn}

/-- The registers the stretch keeps apart from the stack's, `rbp` and `r12`. -/
structure Kq (g g' : Gprs) : Prop where
  rbx : g'.rbx = g.rbx
  r13 : g'.r13 = g.r13
  r14 : g'.r14 = g.r14
  r15 : g'.r15 = g.r15

theorem Kq.trans {a b d : Gprs} (h : Kq a b) (h' : Kq b d) : Kq a d :=
  ⟨h'.rbx.trans h.rbx, h'.r13.trans h.r13, h'.r14.trans h.r14, h'.r15.trans h.r15⟩

theorem Kq.of_back {g g' : Gprs} (h : Osv.Back g g') : Kq g g' :=
  ⟨h.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩

/-- Outside the 552 bytes: outside a callee's 56 bytes below the return address's slot. -/
theorem fr_sub {sp a : Nat} (h : ¬ (sp - 552 ≤ a ∧ a < sp)) : ¬ (sp - 224 - 56 ≤ a ∧ a < sp - 224) := by
  intro ⟨h1, h2⟩
  rw [Nat.sub_sub] at h1
  exact h ⟨Nat.le_trans (Nat.sub_le_sub_left (show 224 + 56 ≤ 552 by decide) sp) h1,
    Nat.lt_of_lt_of_le h2 (Nat.sub_le _ _)⟩

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ X : State} {o : Oracle} {t : Nat}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop} {V : Addr → Byte}

set_option maxHeartbeats 1600000 in
/-- From offset 545 to the return of `__libc_pthread_init`, with the lock of `__default_pthread_attr` free, one
thread, the fork handlers' lock free and their list not set up: outside the frame the bytes are `W`, which is
`MemD G sz` apart from what `__libc_pthread_init` set up. -/
theorem pim_d1 {fb : Addr} {g₀ : Gprs} {G : Addr → Byte} {cn sz : BitVec 64}
    (c : Seg prof F Wl L s₀ o) (hfs : s₀.cpu.seg.fsBase = fb) (hin : CodeIn L pim_at pim)
    (hinL : CodeIn L Lpi.lpi_at Lpi.lpi) (hinRf : CodeIn L Raf.raf_at Raf.raf) (hK : KeptW Wl s₀ X)
    (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = pim_at.add 545) (hL : Lay F Wl g₀.rsp fb)
    (hro : ∀ i < 16, Foot F.data (Addr.add 7273168#64 i)) (hF : Fr G V g₀.rsp g₀.r12 g₀.rbp cn)
    (hsz : rdq(V, g₀.rsp - 200#64) = sz) (hR : Rg g₀ X.cpu.gpr) (hax : X.cpu.gpr.rax = 0)
    (hdx : X.cpu.gpr.rdx = 1) (hlk : rdd(G, 8008032#64) = 0)
    (hmt : rdd(G, fb + 24#64) = 0) (hfl : rdd(G, 8011552#64) = 0) (hfg : rdb(G, 8011556#64) = 0)
    (k : ∀ V' Z t' (W : Addr → Byte), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V' →
      (∀ a : Addr, ¬ (8011552 ≤ a.toNat ∧ a.toNat < 8011640) → ¬ (8029200 ≤ a.toNat ∧ a.toNat < 8029208) →
        W a = MemD G sz a) → rdq(W, 8029200#64) = 8027680#64 →
      Fr W V' g₀.rsp g₀.r12 g₀.rbp cn → Z.cpu.rip = pim_at.add 647 → Z.cpu.gpr.rsp = g₀.rsp - 216#64 →
      Z.cpu.gpr.rax = 8029208#64 → Kq g₀ Z.cpu.gpr → GoG prof L o gev gP gE Z t') :
    GoG prof L o gev gP gE X t := by
  obtain ⟨hsp, hbp, h12, hbx, h13, h14, h15⟩ := hR
  have hsp' := hL.hsp
  have hfb := hL.hfb
  have hlo := hL.hlo
  have hlt := g₀.rsp.isLt
  have gl : ∀ (x : Addr) (n : Nat), 0x777000 ≤ x.toNat → x.toNat + n ≤ 0x7a9000 → ∀ i < n, Foot Wl (Addr.add x i) :=
    fun x n h1 h2 => hL.gl h1 h2
  have gd : ∀ (x : Addr) (n : Nat), 0x777000 ≤ x.toNat → x.toNat + n ≤ 0x7a9000 →
      ∀ i < n, Foot F.data (Addr.add x i) := fun x n h1 h2 i hi => hL.hws _ (hL.gl h1 h2 i hi)
  have st : ∀ (d n : Nat) (x : Addr), x = g₀.rsp - 552#64 + BitVec.ofNat 64 d → d + n ≤ 552 →
      ∀ i < n, Foot Wl (Addr.add x i) := fun d n x hx hd => off_ft hL.hst d hx hd
  have tc : ∀ (d n : Nat) (x : Addr), x = fb + BitVec.ofNat 64 d → d + n ≤ 1704 →
      ∀ i < n, Foot F.data (Addr.add x i) := fun d n x hx hd i hi => hL.hws _ (off_ft hL.htcb d hx hd i hi)
  -- the lock taken
  refine c.s_lock_cmpxchg_rip32 hK hA hin (lt_len (by decide)) hrip (cmpxchg_545 _) (g := 8008032#64) (by decide)
    (by decide) (gl _ 4 (by decide) (by decide)) ?_ ?_
  · rw [hF.rd (by decide) (by bv_omega)]
    show _ = X.cpu.gpr.rax.setWidth 32
    rw [hax]
    exact hlk
  rintro Y₁ t₁ hK₁ hA₁ ⟨hr₁, hg₁, hz₁⟩
  rw [show rv X 32 2 = 1#32 from by show X.cpu.gpr.rdx.setWidth 32 = _; rw [hdx]; rfl] at hA₁
  have hsp₁ : Y₁.cpu.gpr.rsp = g₀.rsp - 216#64 := by rw [hg₁]; exact hsp
  -- the sizes
  refine (c_553 prof fb).run c hfs hin _ hK₁ hA₁ hr₁
    (vc_553 hz₁ (by rw [hsp₁]; exact fun i hi => hL.hws _ (st 352 8 _ (by bv_omega) (by decide) i hi))
      (gl _ 8 (by decide) (by decide)) (gd _ 8 (by decide) (by decide)) (gl _ 8 (by decide) (by decide))) ?_
  rintro j' g fl V₂ ⟨rfl, rfl, rfl⟩ Y₂ t₂ hK₂ hA₂ hr₂ hg₂ -
  have e2 : rdq(Vst V (8008032#64) (toBytesLE (1#32) 4), Y₁.cpu.gpr.rsp + 16#64) = sz := by
    rw [hsp₁, show g₀.rsp - 216#64 + 16#64 = g₀.rsp - 200#64 from by bv_omega]
    exact (congrArg (ofBytesLE 64) (vr (by ln) (by decide) (by bv_omega) (by bv_omega))).trans hsz
  have e3 : rdq(Vst V (8008032#64) (toBytesLE (1#32) 4), 7943128#64) = rdq(G, 7943128#64) :=
    (congrArg (ofBytesLE 64) (vr (by ln) (by decide) (by decide) (by decide))).trans
      (congrArg (ofBytesLE 64) (hF.rd (by decide) (by bv_omega)))
  rw [e2, e3] at hA₂
  have hF₂ : Fr (MemD1 G sz) (Vst (Vst (Vst V (8008032#64) (toBytesLE (1#32) 4)) (8027808#64) (toBytesLE sz 8))
      (8027792#64) (toBytesLE rdq(G, 7943128#64) 8)) g₀.rsp g₀.r12 g₀.rbp cn :=
    ((hF.gl hL.hsp (by ln) (by decide) (by bv_omega)).gl hL.hsp (by ln) (by decide) (by bv_omega)).gl hL.hsp
      (by ln) (by decide) (by bv_omega)
  -- the lock released
  refine c.s_xchg_rip32 hK₂ hA₂ hin (lt_len (by decide)) hr₂ (xchg_587 _) (g := 8008032#64) (by decide)
    (by decide) (gl _ 4 (by decide) (by decide)) ?_
  rintro Y₃ t₃ hK₃ hA₃ ⟨hr₃, hg₃⟩
  rw [show rv Y₂ 32 0 = 0#32 from by show Y₂.cpu.gpr.rax.setWidth 32 = _; rw [hg₂]; rfl] at hA₃
  rw [vr (by ln) (by decide) (by decide) (by decide), vr (by ln) (by decide) (by decide) (by decide),
    vs (by ln) (by decide), ofBytesLE_toBytesLE (n := 4) rfl _] at hg₃
  -- the hooks
  refine (c_593 prof fb).run c hfs hin _ hK₃ hA₃ hr₃
    (vc_593 (by rw [hg₃]; rfl) (gl _ 8 (by decide) (by decide)) (gl _ 8 (by decide) (by decide))) ?_
  rintro j' g fl V₄ ⟨rfl, rfl, rfl⟩ Y₄ t₄ hK₄ hA₄ hr₄ hg₄ -
  have hsp₄ : Y₄.cpu.gpr.rsp = g₀.rsp - 216#64 := by rw [hg₄, hg₃, hg₂]; exact hsp₁
  have q4 : Kq g₀ Y₄.cpu.gpr := by
    rw [hg₄, hg₃, hg₂, hg₁]
    exact ⟨hbx, h13, h14, h15⟩
  refine c.s_call hK₄ hA₄ hin (lt_len (by decide)) hr₄ (call_642 _) hinL (Lpi.lt_len (by decide)) (by decide)
    (fun i hi => ?_) ?_
  · rw [hsp₄]
    exact st 328 8 _ (by bv_omega) (by decide) i hi
  rintro Y₅ t₅ hK₅ hA₅ ⟨hr₅, hg₅⟩
  rw [hsp₄, show g₀.rsp - 216#64 - 8 = g₀.rsp - 224#64 from by bv_omega] at hA₅ hg₅
  obtain ⟨V₅, hA₅, hF₅, hra₅⟩ : ∃ V₅, Agree F Y₅.proc.mm.mem V₅ ∧ Fr (MemD G sz) V₅ g₀.rsp g₀.r12 g₀.rbp cn ∧
      rdq(V₅, g₀.rsp - 224#64) = pim_at.add 647 := by
    refine ⟨_, hA₅, ?_, ?_⟩
    · exact ((((hF₂.gl hL.hsp (by ln) (by decide) (by bv_omega)).gl hL.hsp (by ln) (by decide) (by bv_omega)).gl
        hL.hsp (by ln) (by decide) (by bv_omega))).lo hL.hsp (by ln) (by bv_omega) (by bv_omega)
    · rw [vs (by ln) (by bv_omega)]
      exact ofBytesLE_toBytesLE (n := 8) rfl _
  have hsp₅ : Y₅.cpu.gpr.rsp = g₀.rsp - 224#64 := by rw [hg₅]; rfl
  have hdi₅ : Y₅.cpu.gpr.rdi = 8027680#64 := by rw [hg₅, hg₄]; rfl
  have q5 : Kq g₀ Y₅.cpu.gpr := q4.trans (by rw [hg₅]; exact ⟨rfl, rfl, rfl, rfl⟩)
  have e224 : (g₀.rsp - 224#64).toNat = g₀.rsp.toNat - 224 := by bv_omega
  -- `__libc_pthread_init (&__nptl_nthreads…, __reclaim_stacks)`
  refine Lpi.lpi_ok c hfs hinL hinRf hK₅ hA₅ hr₅ (by rw [hsp₅]; bv_omega)
    (by rw [hsp₅]; exact st 272 56 _ (by bv_omega) (by decide))
    (by rw [hsp₅]; exact fun i hi => hL.hws _ (st 328 8 _ (by bv_omega) (by decide) i hi)) hin (j₂ := 647)
    (lt_len (by decide)) (by rw [hsp₅]; exact hra₅) (gl _ 8 (by decide) (by decide))
    (gl _ 88 (by decide) (by decide)) hro (by rw [hsp₅]; bv_omega) (by rw [hsp₅]; bv_omega)
    (tc 24 4 _ rfl (by decide)) (by bv_omega) (by rw [hsp₅]; bv_omega) (by bv_omega)
    ((congrArg (ofBytesLE 32) ((hF₅.rd (by bv_omega) (by bv_omega)).trans
      (MemD_rd (by bv_omega) (by bv_omega)))).trans hmt)
    ((congrArg (ofBytesLE 32) ((hF₅.rd (by decide) (by bv_omega)).trans
      (MemD_rd (by decide) (by decide)))).trans hfl)
    ((congrArg (ofBytesLE 8) ((hF₅.rd (by decide) (by bv_omega)).trans
      (MemD_rd (by decide) (by decide)))).trans hfg) ?_
  intro V₆ g₆ Y₆ t₆ hK₆ hA₆ ho₆ hp₆ hr₆ hg₆ hax₆ hb₆
  subst hg₆
  rw [hsp₅, e224] at ho₆
  rw [hdi₅] at hp₆
  obtain ⟨W, hWi, hWn⟩ : ∃ W : Addr → Byte,
      (∀ a : Addr, g₀.rsp.toNat - 552 ≤ a.toNat ∧ a.toNat < g₀.rsp.toNat → W a = MemD G sz a) ∧
      ∀ a : Addr, ¬ (g₀.rsp.toNat - 552 ≤ a.toNat ∧ a.toNat < g₀.rsp.toNat) → W a = V₆ a :=
    ⟨fun a => if g₀.rsp.toNat - 552 ≤ a.toNat ∧ a.toNat < g₀.rsp.toNat then MemD G sz a else V₆ a,
      fun a h => by simp only [h, and_self, ↓reduceIte], fun a h => by simp only [h, ↓reduceIte]⟩
  have hW : ∀ a : Addr, ¬ (8011552 ≤ a.toNat ∧ a.toNat < 8011640) → ¬ (8029200 ≤ a.toNat ∧ a.toNat < 8029208) →
      W a = MemD G sz a := by
    intro a h1 h2
    by_cases h : g₀.rsp.toNat - 552 ≤ a.toNat ∧ a.toNat < g₀.rsp.toNat
    · exact hWi a h
    · exact (hWn a h).trans ((ho₆ a (fr_sub h) h1 h2).trans (hF₅.out a h))
  have hWo : ∀ a : Addr, ¬ (g₀.rsp.toNat - 552 ≤ a.toNat ∧ a.toNat < g₀.rsp.toNat) → V₆ a = W a :=
    fun a ha => (hWn a ha).symm
  have hF₆ : Fr W V₆ g₀.rsp g₀.r12 g₀.rbp cn :=
    ⟨hWo,
      (congrArg (ofBytesLE 64) (rd_out3 ho₆ (by bv_omega) (by bv_omega) (by bv_omega) (by bv_omega))).trans hF₅.s12,
      (congrArg (ofBytesLE 64) (rd_out3 ho₆ (by bv_omega) (by bv_omega) (by bv_omega) (by bv_omega))).trans hF₅.sbp,
      (congrArg (ofBytesLE 64) (rd_out3 ho₆ (by bv_omega) (by bv_omega) (by bv_omega) (by bv_omega))).trans hF₅.can⟩
  have hpW : rdq(W, 8029200#64) = 8027680#64 :=
    (congrArg (ofBytesLE 64) (Sga.rd_out hWo (by decide) (by bv_omega))).symm.trans hp₆
  have hsp₆ : Y₆.cpu.gpr.rsp = g₀.rsp - 216#64 := by rw [hb₆.1, hsp₅]; bv_omega
  have q6 : Kq g₀ Y₆.cpu.gpr := q5.trans (Kq.of_back hb₆)
  exact k V₆ Y₆ t₆ W hK₆ hA₆ hW hpW hF₆ hr₆ hsp₆ hax₆ q6

set_option maxHeartbeats 1600000 in
/-- From offset 647 to the return, with the tunable of the stack's size not set: the run reaches the return address
with the registers a function keeps; outside the frame the bytes are `MemE W`. -/
theorem pim_d2 {fb : Addr} {g₀ : Gprs} {G W : Addr → Byte} {cn sz : BitVec 64}
    (c : Seg prof F Wl L s₀ o) (hfs : s₀.cpu.seg.fsBase = fb) (hin : CodeIn L pim_at pim)
    (hinP : CodeIn L Pti.pti_at Pti.pti) (hinT : CodeIn L Tgv.tgv_at Tgv.tgv) (hK : KeptW Wl s₀ X)
    (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = pim_at.add 647) (hL : Lay F Wl g₀.rsp fb)
    (hs8 : g₀.rsp.toNat + 8 ≤ 2 ^ 64) (hl : ∀ i < 8, Foot F.data (Addr.add g₀.rsp i))
    (hW : ∀ a : Addr, ¬ (8011552 ≤ a.toNat ∧ a.toNat < 8011640) → ¬ (8029200 ≤ a.toNat ∧ a.toNat < 8029208) →
      W a = MemD G sz a) (hF : Fr W V g₀.rsp g₀.r12 g₀.rbp cn) (hsp : X.cpu.gpr.rsp = g₀.rsp - 216#64)
    (hax : X.cpu.gpr.rax = 8029208#64) (hq : Kq g₀ X.cpu.gpr) (hcn : rdq(G, fb + 40#64) = cn)
    (ht0 : rdd(G, 7936880#64) = 0) (htz : rdb(G, 7936912#64) = 0)
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (hra : rdq(G, g₀.rsp) = e₂.add j₂)
    (k : ∀ V' g' Z t', KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V' →
      (∀ a : Addr, ¬ (g₀.rsp.toNat - 552 ≤ a.toNat ∧ a.toNat < g₀.rsp.toNat) → V' a = MemE W a) →
      Z.cpu.rip = e₂.add j₂ → Z.cpu.gpr = g' → Osv.Back g₀ g' → GoG prof L o gev gP gE Z t') :
    GoG prof L o gev gP gE X t := by
  have hsp' := hL.hsp
  have hfb := hL.hfb
  have hlo := hL.hlo
  have hlt := g₀.rsp.isLt
  have gl : ∀ (x : Addr) (n : Nat), 0x777000 ≤ x.toNat → x.toNat + n ≤ 0x7a9000 → ∀ i < n, Foot Wl (Addr.add x i) :=
    fun x n h1 h2 => hL.gl h1 h2
  have gd : ∀ (x : Addr) (n : Nat), 0x777000 ≤ x.toNat → x.toNat + n ≤ 0x7a9000 →
      ∀ i < n, Foot F.data (Addr.add x i) := fun x n h1 h2 i hi => hL.hws _ (hL.gl h1 h2 i hi)
  have st : ∀ (d n : Nat) (x : Addr), x = g₀.rsp - 552#64 + BitVec.ofNat 64 d → d + n ≤ 552 →
      ∀ i < n, Foot Wl (Addr.add x i) := fun d n x hx hd => off_ft hL.hst d hx hd
  have tc : ∀ (d n : Nat) (x : Addr), x = fb + BitVec.ofNat 64 d → d + n ≤ 1704 →
      ∀ i < n, Foot F.data (Addr.add x i) := fun d n x hx hd i hi => hL.hws _ (off_ft hL.htcb d hx hd i hi)
  have e224 : (g₀.rsp - 224#64).toNat = g₀.rsp.toNat - 224 := by bv_omega
  -- `__is_smp`, the pointer
  refine (c_647 prof fb).run c hfs hin _ hK hA hrip
    (vc_647 (gl _ 4 (by decide) (by decide)) (gl _ 8 (by decide) (by decide))) ?_
  rintro j' g fl V₇ ⟨rfl, rfl, rfl⟩ Y₇ t₇ hK₇ hA₇ hr₇ hg₇ -
  rw [hax] at hA₇
  have hsp₇ : Y₇.cpu.gpr.rsp = g₀.rsp - 216#64 := by rw [hg₇]; exact hsp
  refine c.s_call hK₇ hA₇ hin (lt_len (by decide)) hr₇ (call_664 _) hinP (Pti.lt_len (by decide)) (by decide)
    (fun i hi => ?_) ?_
  · rw [hsp₇]
    exact st 328 8 _ (by bv_omega) (by decide) i hi
  rintro Y₈ t₈ hK₈ hA₈ ⟨hr₈, hg₈⟩
  rw [hsp₇, show g₀.rsp - 216#64 - 8 = g₀.rsp - 224#64 from by bv_omega] at hA₈ hg₈
  obtain ⟨V₈, hA₈, hF₈, hra₈⟩ : ∃ V₈, Agree F Y₈.proc.mm.mem V₈ ∧ Fr (MemE W) V₈ g₀.rsp g₀.r12 g₀.rbp cn ∧
      rdq(V₈, g₀.rsp - 224#64) = pim_at.add 669 := by
    refine ⟨_, hA₈, ?_, ?_⟩
    · exact ((hF.gl hL.hsp (by ln) (by decide) (by bv_omega)).gl hL.hsp (by ln) (by decide) (by bv_omega)).lo
        hL.hsp (by ln) (by bv_omega) (by bv_omega)
    · rw [vs (by ln) (by bv_omega)]
      exact ofBytesLE_toBytesLE (n := 8) rfl _
  have hsp₈ : Y₈.cpu.gpr.rsp = g₀.rsp - 224#64 := by rw [hg₈]; rfl
  have q8 : Kq g₀ Y₈.cpu.gpr := hq.trans (by rw [hg₈, hg₇]; exact ⟨rfl, rfl, rfl, rfl⟩)
  -- `__pthread_tunables_init`
  refine Pti.pti_ok c hfs hinP hinT hK₈ hA₈ hr₈ (by rw [hsp₈]; bv_omega)
    (by rw [hsp₈]; exact st 296 32 _ (by bv_omega) (by decide))
    (by rw [hsp₈]; exact fun i hi => hL.hws _ (st 328 8 _ (by bv_omega) (by decide) i hi)) hin (j₂ := 669)
    (lt_len (by decide)) (by rw [hsp₈]; exact hra₈) (by rw [hsp₈]; bv_omega) (by rw [hsp₈]; bv_omega)
    (tc 40 8 _ rfl (by decide)) (by bv_omega) (by rw [hsp₈]; bv_omega)
    (gd _ 4 (by decide) (by decide)) (gd _ 8 (by decide) (by decide)) (gd _ 1 (by decide) (by decide))
    ((congrArg (ofBytesLE 32) ((hF₈.rd (by decide) (by bv_omega)).trans
      (MemE_rd hW (by decide) (by decide)))).trans ht0)
    ((congrArg (ofBytesLE 8) ((hF₈.rd (by decide) (by bv_omega)).trans
      (MemE_rd hW (by decide) (by decide)))).trans htz) ?_
  intro V₉ g₉ Y₉ t₉ hK₉ hA₉ ho₉ hr₉ hg₉ hb₉
  subst hg₉
  rw [hsp₈, e224] at ho₉
  have hF₉ : Fr (MemE W) V₉ g₀.rsp g₀.r12 g₀.rbp cn := hF₈.of_out hL.hsp ho₉ (by omega) (by omega)
  have hsp₉ : Y₉.cpu.gpr.rsp = g₀.rsp - 216#64 := by rw [hb₉.1, hsp₈]; bv_omega
  have q9 : Kq g₀ Y₉.cpu.gpr := q8.trans (Kq.of_back hb₉)
  have ebp : rdq(V₉, Y₉.cpu.gpr.rsp + 200#64) = g₀.rbp := by
    rw [hsp₉, show g₀.rsp - 216#64 + 200#64 = g₀.rsp - 16#64 from by bv_omega]
    exact hF₉.sbp
  have e12 : rdq(V₉, Y₉.cpu.gpr.rsp + 200#64 + 8) = g₀.r12 := by
    rw [hsp₉, show g₀.rsp - 216#64 + 200#64 + 8 = g₀.rsp - 8#64 from by bv_omega]
    exact hF₉.s12
  -- the stack guard, the frame left
  refine (c_669 prof fb).run c hfs hin _ hK₉ hA₉ hr₉
    (vc_669 (by rw [hsp₉]; exact fun i hi => hL.hws _ (st 520 8 _ (by bv_omega) (by decide) i hi))
      (tc 40 8 _ rfl (by decide)) ?_
      (by rw [hsp₉]; exact fun i hi => hL.hws _ (st 536 8 _ (by bv_omega) (by decide) i hi))
      (by rw [hsp₉]; exact fun i hi => hL.hws _ (st 544 8 _ (by bv_omega) (by decide) i hi))) ?_
  · rw [hsp₉, show g₀.rsp - 216#64 + 184#64 = g₀.rsp - 32#64 from by bv_omega, hF₉.can]
    exact ((congrArg (ofBytesLE 64) ((hF₉.rd (by bv_omega) (by bv_omega)).trans
      (MemE_rd hW (by bv_omega) (by bv_omega)))).trans hcn).symm
  rw [ebp, e12]
  rintro j' g fl V₁₀ ⟨rfl, rfl, rfl⟩ Y₁₀ t₁₀ hK₁₀ hA₁₀ hr₁₀ hg₁₀ -
  have hsp₁₀ : Y₁₀.cpu.gpr.rsp = g₀.rsp := by
    rw [hg₁₀]
    show Y₉.cpu.gpr.rsp + 200#64 + 8 + 8 = _
    rw [hsp₉]
    bv_omega
  refine c.s_ret hK₁₀ hA₁₀ hin (lt_len (by decide)) hr₁₀ (ret_698 _) (by rw [hsp₁₀]; exact hl) hin₂ h₂ ?_ ?_
  · rw [hsp₁₀]
    exact (congrArg (ofBytesLE 64) ((Fr.rd ‹Fr (MemE W) _ g₀.rsp g₀.r12 g₀.rbp cn› hs8 (by omega)).trans
      (MemE_rd hW hs8 (by bv_omega)))).trans hra
  rintro Y₁₁ t₁₁ hK₁₁ hA₁₁ ⟨hr₁₁, hg₁₁⟩
  refine k _ _ Y₁₁ t₁₁ hK₁₁ hA₁₁ (Fr.out ‹Fr (MemE W) _ g₀.rsp g₀.r12 g₀.rbp cn›) hr₁₁ rfl ?_
  have q11 : Kq g₀ Y₁₁.cpu.gpr := q9.trans (by rw [hg₁₁, hg₁₀]; exact ⟨rfl, rfl, rfl, rfl⟩)
  refine ⟨?_, q11.rbx, ?_, ?_, q11.r13, q11.r14, q11.r15⟩
  · rw [hg₁₁]
    show Y₁₀.cpu.gpr.rsp + 8 = _
    rw [hsp₁₀]
    rfl
  · rw [hg₁₁, hg₁₀]
    rfl
  · rw [hg₁₁, hg₁₀]
    rfl

/-- From offset 545 to the return, with the lock of `__default_pthread_attr` free, one thread, the fork handlers'
lock free and their list not set up, and the tunable of the stack's size not set: the run reaches the return address
with the registers a function keeps; outside the frame the bytes are `MemE W`, where `W` is `MemD G sz` apart from
what `__libc_pthread_init` set up. -/
theorem pim_d {fb : Addr} {g₀ : Gprs} {G : Addr → Byte} {cn sz : BitVec 64}
    (c : Seg prof F Wl L s₀ o) (hfs : s₀.cpu.seg.fsBase = fb) (hin : CodeIn L pim_at pim)
    (hinL : CodeIn L Lpi.lpi_at Lpi.lpi) (hinRf : CodeIn L Raf.raf_at Raf.raf)
    (hinP : CodeIn L Pti.pti_at Pti.pti) (hinT : CodeIn L Tgv.tgv_at Tgv.tgv) (hK : KeptW Wl s₀ X)
    (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = pim_at.add 545) (hL : Lay F Wl g₀.rsp fb)
    (hro : ∀ i < 16, Foot F.data (Addr.add 7273168#64 i)) (hs8 : g₀.rsp.toNat + 8 ≤ 2 ^ 64)
    (hl : ∀ i < 8, Foot F.data (Addr.add g₀.rsp i)) (hF : Fr G V g₀.rsp g₀.r12 g₀.rbp cn)
    (hsz : rdq(V, g₀.rsp - 200#64) = sz) (hR : Rg g₀ X.cpu.gpr) (hax : X.cpu.gpr.rax = 0)
    (hdx : X.cpu.gpr.rdx = 1) (hcn : rdq(G, fb + 40#64) = cn) (hlk : rdd(G, 8008032#64) = 0)
    (hmt : rdd(G, fb + 24#64) = 0) (hfl : rdd(G, 8011552#64) = 0) (hfg : rdb(G, 8011556#64) = 0)
    (ht0 : rdd(G, 7936880#64) = 0) (htz : rdb(G, 7936912#64) = 0)
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (hra : rdq(G, g₀.rsp) = e₂.add j₂)
    (k : ∀ V' g' Z t' (W : Addr → Byte), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V' →
      (∀ a : Addr, ¬ (8011552 ≤ a.toNat ∧ a.toNat < 8011640) → ¬ (8029200 ≤ a.toNat ∧ a.toNat < 8029208) →
        W a = MemD G sz a) → rdq(W, 8029200#64) = 8027680#64 →
      (∀ a : Addr, ¬ (g₀.rsp.toNat - 552 ≤ a.toNat ∧ a.toNat < g₀.rsp.toNat) → V' a = MemE W a) →
      Z.cpu.rip = e₂.add j₂ → Z.cpu.gpr = g' → Osv.Back g₀ g' → GoG prof L o gev gP gE Z t') :
    GoG prof L o gev gP gE X t :=
  pim_d1 c hfs hin hinL hinRf hK hA hrip hL hro hF hsz hR hax hdx hlk hmt hfl hfg
    fun _ _ _ W hK₁ hA₁ hW hpW hF₁ hr₁ hsp₁ hax₁ hq₁ =>
      pim_d2 c hfs hin hinP hinT hK₁ hA₁ hr₁ hL hs8 hl hW hF₁ hsp₁ hax₁ hq₁ hcn ht0 htz hin₂ h₂ hra
        fun V' g' Z t' hKZ hAZ ho hrZ hgZ hb => k V' g' Z t' W hKZ hAZ hW hpW ho hrZ hgZ hb

end FV7z.Pim
