import FV7z.Lemmas.FnSys
/-!
# A call of a function by its `ImplementsCall`, a step of a run (PLAN.md G2, glibc `init_cpu_features`)

A run (`Fn.Seg`) that calls a function whose code has its own proof (`ImplementsCall` of a contract `fn`) goes on
past the call by that proof: at the callee's entry the call is a `CallOf` (its footprint, a part of the run's, is
ordinary memory there, the thread may start a call, the stack holds the return address), and the callee's run returns
as its contract says. For the run to go on with what it keeps (`KeptW`), the contract's postcondition says what the
callee kept (`fnK`: `KeptW` of the stack below the slot and `W`), which a proof by `Fn.Call` has at the return.

First: the footprint `G` of the callee, at a state `s` that `KeptW` relates to `s₀`, is `Ok` if its bytes are among
those of `F`, `Ok` at `s₀` (written ones among `F`'s written ones), and its regions fit.
-/
namespace FV7z
open ZellicX86

section
variable {feat : Features} {s₀ s : State} {F G : Footprint} {Wl : List Rgn}

theorem foot_append_iff {rs qs : List Rgn} {a : Addr} : Foot (rs ++ qs) a ↔ Foot rs a ∨ Foot qs a := by
  constructor
  · rintro ⟨r, hr, hm⟩
    rcases List.mem_append.1 hr with h | h
    · exact Or.inl ⟨r, h, hm⟩
    · exact Or.inr ⟨r, h, hm⟩
  · rintro (⟨r, hr, hm⟩ | ⟨r, hr, hm⟩)
    · exact ⟨r, List.mem_append_left _ hr, hm⟩
    · exact ⟨r, List.mem_append_right _ hr, hm⟩

/-- How `G`'s bytes lie among `F`'s: written among written, read among written or read; the same code; nothing
owned. -/
structure Sub (F G : Footprint) : Prop where
  fits : ∀ r ∈ G.writes ++ G.reads, r.Fits
  writes : ∀ y, Foot G.writes y → Foot F.writes y
  reads : ∀ y, Foot G.reads y → Foot F.writes y ∨ Foot F.reads y
  code : G.code = F.code
  own : G.own = []
  fown : F.own = []

namespace Sub
variable (h : Sub F G)
include h

theorem data {y : Addr} (hy : Foot G.data y) : Foot F.data y := by
  unfold Footprint.data at hy ⊢
  rw [h.own] at hy
  rcases foot_append_iff.1 hy with hy | hy
  · rcases foot_append_iff.1 hy with hy | hy
    · exact foot_append_iff.2 (Or.inl (foot_append_iff.2 (Or.inl (h.writes y hy))))
    · obtain ⟨r, hr, -⟩ := hy; simp at hr
  · rcases h.reads y hy with hy | hy
    · exact foot_append_iff.2 (Or.inl (foot_append_iff.2 (Or.inl hy)))
    · exact foot_append_iff.2 (Or.inr hy)

theorem codeRgns : G.codeRgns = F.codeRgns := by simp [Footprint.codeRgns, h.code]

theorem all {y : Addr} (hy : Foot (G.data ++ G.codeRgns) y) : Foot (F.data ++ F.codeRgns) y := by
  rcases foot_append_iff.1 hy with hy | hy
  · exact foot_append_iff.2 (Or.inl (h.data hy))
  · exact foot_append_iff.2 (Or.inr (h.codeRgns ▸ hy))

end Sub

/-- A backing a calm change leaves as a file mapping was that file mapping. -/
theorem file_of_calm {A : Addr → Prop} {m M : Memory} (hc : Calm A m M) {j : Nat} {fp : FilePage}
    (h : M.backings j = .file fp) : m.backings j = .file fp := by
  have hr := hc.refines j
  rw [h] at hr
  revert hr
  cases m.backings j <;> simp [Backing.Refines]
  exact fun e => e.symm

/-- A backing a calm change leaves as a private file mapping not yet written was that mapping. -/
theorem cow_of_calm {A : Addr → Prop} {m M : Memory} (hc : Calm A m M) {j : Nat} {fp : FilePage}
    (h : M.backings j = .cow fp) : m.backings j = .cow fp := by
  have hr := hc.refines j
  rw [h] at hr
  revert hr
  cases m.backings j <;> simp [Backing.Refines]
  exact fun e => e.symm

/-- `Footprint.Ok` of a part `G` of `F`, at a state the run keeps. -/
theorem _root_.ZellicX86.Footprint.Ok.keptW (hok : F.Ok feat s₀) (hrq : RseqQuiet feat s₀) (hws : ∀ y, Foot Wl y → Foot F.data y)
    (hK : KeptW Wl s₀ s) (h : Sub F G) : G.Ok feat s := by
  have hck : ∀ acc x, s.proc.mm.mem.check feat s.cpu.pkru acc x = s₀.proc.mm.mem.check feat s₀.cpu.pkru acc x :=
    fun acc x => by rw [hK.calm.check, hK.pkru]
  have hmap := hK.calm.map
  have hra : rseqArea s = rseqArea s₀ := by simp [rseqArea, hK.thread]
  have hwr : ∀ y, Foot F.writes y → y.canonical feat.la57 = true ∧
      s₀.proc.mm.mem.check feat s₀.cpu.pkru .write y = none := by
    rintro y ⟨q, hq, hm⟩; exact hok.writable q hq y hm
  have hrd : ∀ y, Foot F.writes y ∨ Foot F.reads y → y.canonical feat.la57 = true ∧
      s₀.proc.mm.mem.check feat s₀.cpu.pkru .read y = none := by
    rintro y (hy | ⟨q, hq, hm⟩)
    · obtain ⟨h1, h2⟩ := hwr y hy; exact ⟨h1, check_read_of_write h2⟩
    · exact hok.readable q hq y hm
  -- the backings of `F`'s bytes at `s₀` are neither the kernel's nor freed: so they stay so
  have hstab : ∀ y, Foot (F.data ++ F.codeRgns) y → ∀ m, s.proc.mm.mem.map (pageOf y) = some m →
      BStable (s.proc.mm.mem.backings m.backing) := by
    intro y hy m hm
    rw [hmap] at hm
    have := hok.notKernel y hy m hm
    apply hK.calm.stable
    unfold BStable
    split
    · next f e => exact this.1 f e
    · next f e => exact this.2 f e
    · trivial
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro r hr
    rcases List.mem_append.1 hr with hr | hr
    · unfold Footprint.data at hr
      rw [h.own] at hr
      simp only [List.append_nil] at hr
      exact h.fits r hr
    · rw [h.codeRgns] at hr; exact hok.fits r (List.mem_append_right _ hr)
  · intro r hr a ha
    rw [hck]; exact hwr a (h.writes a ⟨r, hr, ha⟩)
  · intro r hr a ha
    rw [hck]; exact hrd a (h.reads a ⟨r, hr, ha⟩)
  · intro c hc
    rw [h.code] at hc
    have hcb := hok.code c hc
    refine ⟨fun a ha => by rw [hck]; exact hcb.1 a ha, ?_⟩
    have hcr : (⟨c.1, c.2.length⟩ : Rgn) ∈ F.codeRgns := List.mem_map_of_mem (f := fun c : Addr × List Byte => (⟨c.1, c.2.length⟩ : Rgn)) hc
    have hfit := hok.fits _ (List.mem_append_right _ hcr)
    have hmem : ∀ i < c.2.length, (⟨c.1, c.2.length⟩ : Rgn).Mem (c.1.add i) := fun i hi => mem_add_of_fits hi hfit
    have e := hK.calm.readBytes_apart hok hrq hws (fun i hi => ⟨_, List.mem_append_right _ hcr, hmem i hi⟩)
      (fun i hi hw => by
        obtain ⟨q, hq, hqm⟩ := hws _ hw
        exact hok.codeApart q hq _ hcr _ hqm (hmem i hi))
    unfold Bytes
    rw [e]
    exact hcb.2
  · intro a ha m hm
    have := hstab a (h.all ha) m hm
    unfold BStable at this
    refine ⟨fun f e => ?_, fun f e => ?_⟩ <;> rw [e] at this <;> exact this
  · intro a b ha hb hp m n hma hmb
    rw [hra] at ha hb
    have ha' : Foot (F.data ++ F.codeRgns ++ rseqArea s₀) a := by
      rcases foot_append_iff.1 ha with ha | ha
      · exact foot_append_iff.2 (Or.inl (h.all ha))
      · exact foot_append_iff.2 (Or.inr ha)
    have hb' : Foot (F.data ++ F.codeRgns ++ rseqArea s₀) b := by
      rcases foot_append_iff.1 hb with hb | hb
      · exact foot_append_iff.2 (Or.inl (h.all hb))
      · exact foot_append_iff.2 (Or.inr hb)
    rw [hmap] at hma hmb
    obtain ⟨hne, hf⟩ := hok.noAlias a b ha' hb' hp m n hma hmb
    refine ⟨hne, fun fp e => ?_⟩
    obtain ⟨h1, h2⟩ := hf fp (file_of_calm hK.calm e)
    exact ⟨fun e' => h1 (file_of_calm hK.calm e'), fun e' => h2 (cow_of_calm hK.calm e')⟩
  · intro a ha m hm fp e
    rw [h.own, List.append_nil] at ha
    have ha' := h.writes a ha
    have hF : Foot (F.writes ++ F.own) a := foot_append_iff.2 (Or.inl ha')
    rw [hmap] at hm
    have hns := hok.notShared a hF m hm
    have hnk := hok.notKernel a (foot_append_iff.2 (Or.inl (by
      unfold Footprint.data; exact foot_append_iff.2 (Or.inl (foot_append_iff.2 (Or.inl ha')))))) m hm
    have hown : BOwn (s₀.proc.mm.mem.backings m.backing) := by
      unfold BOwn
      split
      · trivial
      · trivial
      · next b h1 h2 =>
        cases hb : s₀.proc.mm.mem.backings m.backing with
        | priv f => exact h1 f hb
        | cow f => exact h2 f hb
        | kernel f => exact hnk.1 f hb
        | freed f => exact hnk.2 f hb
        | file f => exact hns f hb
    have := hK.calm.own _ hown
    rw [e] at this
    exact this
  · intro a ha; rw [h.own] at ha; obtain ⟨r, hr, -⟩ := ha; simp at hr
  · intro r hr q hq a har hqa
    unfold Footprint.data at hr
    rw [h.own, List.append_nil] at hr
    rw [h.codeRgns] at hq
    obtain ⟨r', hr', hm'⟩ := h.data (y := a) (by unfold Footprint.data; rw [h.own, List.append_nil]; exact ⟨r, hr, har⟩)
    exact hok.codeApart r' hr' q hq a hm' hqa
  · intro r hr q hq a har hqa
    rw [hra] at hr
    obtain ⟨q', hq', hm'⟩ := h.all ⟨q, hq, hqa⟩
    exact hok.rseqApart r hr q' hq' a har hm'

/-- A byte of a region is one of its addresses. -/
theorem rgn_mem_add {a x : Addr} {n : Nat} (h : Rgn.Mem ⟨a, n⟩ x) : ∃ j < n, x = a.add j := by
  simp only [Rgn.Mem] at h
  refine ⟨x.toNat - a.toNat, by omega, ?_⟩
  apply BitVec.eq_of_toNat_eq
  simp only [Addr.add, BitVec.toNat_add, BitVec.toNat_ofNat]
  rw [Nat.add_mod_mod, show a.toNat + (x.toNat - a.toNat) = x.toNat by omega, Nat.mod_eq_of_lt x.isLt]

/-- `RseqQuiet` of a state whose area is quiet, of an area that fits. -/
theorem RseqQuiet.of_quiet (hf : ∀ r, s.thread.rseq = some r → r.area.toNat + 32 ≤ 2 ^ 64)
    (hq : Quiet feat s) : RseqQuiet feat s := by
  unfold Quiet AreaQuiet at hq
  unfold RseqQuiet
  rcases hr : s.thread.rseq with _ | r
  · trivial
  rw [hr] at hq
  obtain ⟨hok, -, hw⟩ := hq
  have hb : ∀ x, Rgn.Mem ⟨r.area, 32⟩ x → ∃ j < 32, x = r.area.add j := fun x hx => rgn_mem_add hx
  refine ⟨hf r hr, fun x hx => ?_, fun x hx m hm => ?_, fun x hx m hm fp e => ?_, hw⟩
  · obtain ⟨j, hj, rfl⟩ := hb x hx
    exact ⟨(hok j hj).1, (hok j hj).2.1⟩
  · obtain ⟨q, hq, hqx⟩ := hx
    simp only [List.mem_singleton] at hq; subst hq
    obtain ⟨j, hj, rfl⟩ := hb x hqx
    have := (hok j hj).2.2 m hm
    refine ⟨fun f e => ?_, fun f e => ?_⟩ <;> rw [e] at this <;> exact this
  · obtain ⟨q, hq, hqx⟩ := hx
    simp only [List.mem_singleton] at hq; subst hq
    obtain ⟨j, hj, rfl⟩ := hb x hqx
    have := (hok j hj).2.2 m hm
    rw [e] at this; exact this

/-- `Ready` at a state the run keeps. -/
theorem _root_.ZellicX86.Ready.keptW (hR : Ready feat s₀) (hok : F.Ok feat s₀) (hws : ∀ y, Foot Wl y → Foot F.data y)
    (hK : KeptW Wl s₀ s) : Ready feat s := by
  obtain ⟨⟨h1, h2, h3, h4⟩, hrq, hl⟩ := hR
  refine ⟨⟨hK.tf.trans h1, hK.ac.trans h2, by rw [hK.thread]; exact h3, by rw [hK.thread]; exact h4⟩, ?_, ?_⟩
  · refine RseqQuiet.of_quiet (fun r hr => ?_) (hK.quiet hok hrq hws (quiet_of_rseqQuiet hrq hok.noAlias))
    rw [hK.thread] at hr
    exact RseqQuiet.fits hrq r hr
  · obtain ⟨l1, l2, l3, l4, l5, l6⟩ := hl
    unfold LayoutOk
    rw [hK.calm.map, hK.calm.growsDown, hK.calm.fresh, hK.brk, hK.brkMin]
    exact ⟨l1, l2, l3, l4, l5, l6⟩

end

end FV7z

namespace FV7z
open ZellicX86

/-- `KeptW` of `s` from `s₀`, then of `s'` from `s` for regions among `Wl`'s bytes. -/
theorem KeptW.trans {Wl ws : List Rgn} {s₀ s s' : State} (h : KeptW Wl s₀ s) (k : KeptW ws s s')
    (hsub : ∀ y, Foot ws y → Foot Wl y) : KeptW Wl s₀ s' where
  proc := by rw [k.proc, h.proc]
  calm := h.calm.trans (k.calm.mono fun y hy => by
    rw [h.thread] at hy
    rcases hy with hy | hy
    · exact Or.inl hy
    · exact Or.inr (hsub y hy))
  thread := k.thread.trans h.thread
  seg := k.seg.trans h.seg
  x87 := k.x87.trans h.x87
  mxcsr := k.mxcsr.trans h.mxcsr
  pkru := k.pkru.trans h.pkru
  tf := k.tf.trans h.tf
  ac := k.ac.trans h.ac
  df := k.df.trans h.df

/-- A run that `ReachOrEndsIn` describes, as `RunsFrom` after the events `pre`. -/
theorem runsFrom_of_reach {prof : Profile} {o : Oracle} {env : Oracle → Prop} {s : State} {I : State → Prop}
    {P : State → List Event → Prop} {E' : Outcome → List Event → Prop} (h : ReachOrEndsIn prof env s I P E')
    (ho : env o) (t : Nat) {pre : List Event} {gE : Outcome → List Event → Prop}
    (hE : ∀ out evs, E' out evs → gE out (pre ++ evs)) :
    RunsFrom prof o I pre s t (fun X _ evs => ∃ e, evs = pre ++ e ∧ P X e) gE := by
  obtain ⟨n, st, evs, t', hr, hp, hm⟩ := h o ho t
  refine ⟨n, st, evs, t', hr, hp, ?_⟩
  cases st with
  | running X => exact ⟨evs, rfl, hm⟩
  | done out => exact hE out evs hm

end FV7z

namespace FV7z.Fn
open ZellicX86 Decode FV7z.Leaf

/-- `fn`, whose postcondition also says what the callee kept (`KeptW` of the stack below the slot and `W`): what a
caller's run needs to go on past the call. -/
def fnK (k : Nat) (W R : State → List Rgn) (pre : State → Prop) (post : State → State → Prop) : Contract :=
  fn k W R pre fun s₀ s => post s₀ s ∧ KeptW (ws k W s₀) s₀ s

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle} {F : Footprint} {Wl : List Rgn}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop} {X : State} {t j : Nat}
  {e' : Addr} {code : List Byte} {V : Addr → Byte}
  {k : Nat} {W R : State → List Rgn} {pre : State → Prop} {post : State → State → Prop}

namespace Seg

/-- `F` is a part of itself. -/
theorem sub_self (c : Seg prof F Wl L s₀ o) : Sub F F where
  fits r hr := c.foot.fits r (List.mem_append_left _ (by
    unfold Footprint.data; rw [c.own, List.append_nil]; exact hr))
  writes _ h := h
  reads _ h := Or.inr h
  code := rfl
  own := c.own
  fown := c.own

/-- `call rel32` of a function with its own proof (`ImplementsCall` of `fnK`): the run goes on at the return, from
every state the callee may return in, with the bytes of `F` the callee does not store into as before the call. -/
theorem s_callK (c : Seg prof F Wl L s₀ o) (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V)
    (hin : CodeIn L e' code) (hj : j < code.length) (hrip : X.cpu.rip = e'.add j) {rel len : Nat}
    (hd : Dec prof.feat code j (FV7z.mk .call 64 [.rel rel] len))
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) (h₂ : 0 < code₂.length)
    (htgt : e'.add (j + len) + BitVec.ofNat 64 rel = e₂)
    (hst : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8) i)) (hfit : (X.cpu.gpr.rsp - 8).toNat + 8 ≤ 2 ^ 64)
    (himp : ImplementsCall prof e₂ L (fnK k W R pre post))
    (hdf : s₀.cpu.rflags.df = false) (hx87 : s₀.cpu.x87.full = 0)
    (hcan : (e'.add (j + len)).canonical prof.feat.la57 = true) (hal : X.cpu.gpr.rsp.toNat % 16 = 0)
    (hY : ∀ Y, KeptW Wl s₀ Y →
      Agree F Y.proc.mm.mem (Vst V (X.cpu.gpr.rsp - 8) (toBytesLE (e'.add (j + len)) 8)) →
      Y.cpu.rip = e₂ → Y.cpu.gpr = X.cpu.gpr.set 4 (X.cpu.gpr.rsp - 8) →
      Sub F ((fnK k W R pre post).footprint L Y) ∧ (∀ y, Foot (ws k W Y) y → Foot Wl y) ∧ pre Y ∧
        ∀ i < 8, ¬ Foot (W Y) (Addr.add Y.cpu.gpr.rsp i))
    (k' : ∀ Y Z t', KeptW Wl s₀ Y → Y.cpu.gpr = X.cpu.gpr.set 4 (X.cpu.gpr.rsp - 8) → KeptW Wl s₀ Z →
      (∀ y, Foot F.data y → ¬ Foot (ws k W Y) y →
        Z.proc.mm.mem.readByte y = Vst V (X.cpu.gpr.rsp - 8) (toBytesLE (e'.add (j + len)) 8) y) →
      Returns sysv Y (e'.add (j + len)) Z → post Y Z → GoG prof L o gev gP gE Z t') :
    GoG prof L o gev gP gE X t := by
  refine c.s_call hK hA hin hj hrip hd hin₂ h₂ htgt hst ?_
  rintro Y t₁ hKY hAY ⟨hrY, hgY⟩
  obtain ⟨hsub, hwsW, hpre, -⟩ := hY Y hKY hAY hrY hgY
  have hrsp : Y.cpu.gpr.rsp = X.cpu.gpr.rsp - 8 := by rw [hgY]; rfl
  have hokY : F.Ok prof.feat Y := c.foot.keptW c.ready.rseq c.hws hKY c.sub_self
  have hRY : Ready prof.feat Y := c.ready.keptW c.foot c.hws hKY
  have hGok := c.foot.keptW c.ready.rseq c.hws hKY hsub
  have hword : Word Y Y.cpu.gpr.rsp (e'.add (j + len)) := by
    unfold Word
    rw [hrsp, hAY.read (fun i hi => c.hws _ (hst i hi))]
    have := Vst_self (toBytesLE (e'.add (j + len)) 8) V (X.cpu.gpr.rsp - 8) (by rw [toBytesLE_length]; exact hfit)
    rw [toBytesLE_length] at this
    rw [this]
    exact ofBytesLE_toBytesLE (n := 8) rfl _
  have hent : sysv.entry Y := by
    refine ⟨?_, by rw [hKY.df]; exact hdf, by rw [hKY.x87]; exact hx87⟩
    rw [hrsp, BitVec.sub_add_cancel]; exact hal
  have hcall : CallOf prof e₂ L (fnK k W R pre post) Y (e'.add (j + len)) :=
    ⟨⟨hrY, hword, hcan, hent⟩, hRY, hGok, hpre⟩
  refine RunsFrom.bind (runsFrom_of_reach (himp Y _ hcall) c.env t₁ (gE := gE) fun _ _ h => h.elim) ?_
  rintro Z T _ ⟨evs, rfl, hret, -, ⟨hpost, hKZ⟩, hev⟩
  have hev' : evs = [] := hev
  subst hev'
  rw [List.append_nil]
  refine k' Y Z T hKY hgY (hKY.trans hKZ hwsW) (fun y hy hny => ?_) hret hpost
  have hRq := hRY.rseq
  rw [hKZ.calm.readByte_apart hokY hRq (fun y hy => c.hws y (hwsW y hy)) (foot_append_iff.2 (Or.inl hy)) hny]
  exact hAY y hy

end Seg

end FV7z.Fn
