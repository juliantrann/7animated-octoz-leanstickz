import FV7z.Lemmas.Exec
/-!
# What a run keeps, when it may store into some regions (PLAN.md G2, "Dispatch theo CPUID", 7-Zip)

`Kept` (`Frame.lean`) lets memory change only at the `rseq` ids, as for a leaf function, which stores nothing.
`KeptW ws` lets it change at the bytes of the regions `ws` too: what a function with a stack frame or an output
buffer writes. The lemmas of `Kept` that a run uses at each step, for `KeptW`: the shapes of the next state, a store,
the code and the bytes of the footprint outside `ws` as at the call, the `rseq` area quiet, the frame condition.
-/
namespace FV7z
open ZellicX86

/-- From `s₀` to `s`, all is as it was but the general-purpose registers, `rip`, the flags other than `TF`, `AC` and
`DF`, the vector and opmask registers (`MXCSR` is kept), and memory, which changed only calmly, at the `rseq` ids and
the bytes of `ws`. -/
structure KeptW (ws : List Rgn) (s₀ s : State) : Prop where
  proc : s.proc = { s₀.proc with mm := { s₀.proc.mm with mem := s.proc.mm.mem } }
  calm : Calm (fun y => IdAddr s₀.thread.rseq y ∨ Foot ws y) s₀.proc.mm.mem s.proc.mm.mem
  thread : s.thread = s₀.thread
  seg : s.cpu.seg = s₀.cpu.seg
  x87 : s.cpu.x87 = s₀.cpu.x87
  mxcsr : s.cpu.vec.mxcsr = s₀.cpu.vec.mxcsr
  pkru : s.cpu.pkru = s₀.cpu.pkru
  tf : s.cpu.rflags.tf = s₀.cpu.rflags.tf
  ac : s.cpu.rflags.ac = s₀.cpu.rflags.ac
  df : s.cpu.rflags.df = s₀.cpu.rflags.df

namespace KeptW
variable {ws : List Rgn} {s₀ s : State}

theorem of_kept (h : Kept s₀ s) : KeptW ws s₀ s :=
  ⟨h.proc, h.calm.mono fun _ hy => Or.inl hy, h.thread, h.seg, h.x87, h.mxcsr, h.pkru, h.tf, h.ac, h.df⟩

protected theorem refl (ws : List Rgn) (s : State) : KeptW ws s s := of_kept (Kept.refl s)

/-- A change of memory, calm at the ids and the bytes of `ws`. -/
theorem mem (h : KeptW ws s₀ s) {M : Memory}
    (hc : Calm (fun y => IdAddr s₀.thread.rseq y ∨ Foot ws y) s.proc.mm.mem M) : KeptW ws s₀ (s.withMem M) where
  proc := by
    have e := h.proc
    simp only [State.withMem]
    rw [e]
  calm := h.calm.trans hc
  thread := h.thread
  seg := h.seg
  x87 := h.x87
  mxcsr := h.mxcsr
  pkru := h.pkru
  tf := h.tf
  ac := h.ac
  df := h.df

/-- The kernel's calm stores of the ids. -/
theorem withMem (h : KeptW ws s₀ s) {M : Memory} (hc : Calm (IdAddr s.thread.rseq) s.proc.mm.mem M) :
    KeptW ws s₀ (s.withMem M) := by
  have hc' : Calm (IdAddr s₀.thread.rseq) s.proc.mm.mem M := h.thread ▸ hc
  exact h.mem (hc'.mono fun _ hy => Or.inl hy)

/-- A store of the bytes `bs` at `a`, each a byte of `ws` the process may write, in its own memory. -/
theorem store (h : KeptW ws s₀ s) {feat : Features} {a : Addr} {bs : List Byte}
    (hw : ∀ x ∈ byteAddrs a bs.length, Foot ws x ∧ s.proc.mm.mem.check feat s.cpu.pkru .write x = none ∧
      OwnAt s.proc.mm.mem x) :
    KeptW ws s₀ (s.withMem (writeBytes s.proc.mm.mem a bs)) :=
  h.mem ((writeBytes_calm fun x hx => ⟨(hw x hx).2.1, (hw x hx).2.2⟩).mono fun y hy => Or.inr (hw y hy).1)

/-- A change of the registers, `rip` and the flags that keeps `TF`, `AC`, `DF` and `MXCSR`. -/
theorem modCpu (h : KeptW ws s₀ s) {f : Cpu → Cpu} (hseg : (f s.cpu).seg = s.cpu.seg)
    (hx : (f s.cpu).x87 = s.cpu.x87) (hv : (f s.cpu).vec.mxcsr = s.cpu.vec.mxcsr) (hp : (f s.cpu).pkru = s.cpu.pkru)
    (htf : (f s.cpu).rflags.tf = s.cpu.rflags.tf) (hac : (f s.cpu).rflags.ac = s.cpu.rflags.ac)
    (hdf : (f s.cpu).rflags.df = s.cpu.rflags.df) : KeptW ws s₀ (s.modCpu f) :=
  ⟨h.proc, h.calm, h.thread, hseg.trans h.seg, hx.trans h.x87, hv.trans h.mxcsr, hp.trans h.pkru, htf.trans h.tf,
    hac.trans h.ac, hdf.trans h.df⟩

theorem nx (h : KeptW ws s₀ s) {len : Nat} {g : Gprs} {fl : Rflags}
    (htf : fl.tf = s.cpu.rflags.tf) (hac : fl.ac = s.cpu.rflags.ac) (hdf : fl.df = s.cpu.rflags.df) :
    KeptW ws s₀ (FV7z.nx s len g fl) :=
  h.modCpu rfl rfl rfl rfl htf hac hdf

theorem upd (h : KeptW ws s₀ s) {r : Addr} {g : Gprs} {fl : Rflags}
    (htf : fl.tf = s.cpu.rflags.tf) (hac : fl.ac = s.cpu.rflags.ac) (hdf : fl.df = s.cpu.rflags.df) :
    KeptW ws s₀ (FV7z.upd s r g fl) :=
  h.modCpu rfl rfl rfl rfl htf hac hdf

theorem mem_map (h : KeptW ws s₀ s) : s.proc.mm.mem.map = s₀.proc.mm.mem.map := h.calm.map
theorem files (h : KeptW ws s₀ s) : s.proc.mm.mem.files = s₀.proc.mm.mem.files := h.calm.files
theorem brk (h : KeptW ws s₀ s) : s.proc.mm.brk = s₀.proc.mm.brk := by rw [h.proc]
theorem brkMin (h : KeptW ws s₀ s) : s.proc.mm.brkMin = s₀.proc.mm.brkMin := by rw [h.proc]

/-- The layout is as at the call. -/
theorem keepsEnv (h : KeptW ws s₀ s) : KeepsEnv s₀ s :=
  ⟨h.mem_map, h.calm.refines, h.calm.fresh, h.brk,
    ⟨fun _ _ _ => by rw [h.files], by rw [h.files], h.calm.growsDown, h.brkMin⟩⟩

theorem keepsSettings (h : KeptW ws s₀ s) (hp : Plain s₀) : KeepsSettingsBut [] [] s₀ s where
  pkru _ := h.pkru
  rseq _ := by rw [h.thread]
  fsBase _ := by rw [h.seg]
  gsBase _ := by rw [h.seg]
  sigmask _ := by rw [h.thread]
  altStack _ := by rw [h.thread]
  clearChildTid _ := by rw [h.thread]
  robustList _ := by rw [h.thread]
  tscFaults _ := by rw [h.thread]
  uid _ := by rw [h.thread]
  tid := by rw [h.thread]
  pending := by rw [h.thread]
  plain := ⟨h.tf.trans hp.1, h.ac.trans hp.2.1, by rw [h.thread]; exact hp.2.2.1, by rw [h.thread]; exact hp.2.2.2⟩

theorem keepsProc (h : KeptW ws s₀ s) : KeepsProc [] s₀ s where
  files := by rw [h.proc]
  pos _ _ := by rw [h.proc]
  append _ := by rw [h.proc]
  flags _ := by rw [h.proc]
  next := by rw [h.proc]
  sighand := by rw [h.proc]
  signal := by rw [h.proc]

theorem keepsFiles (h : KeptW ws s₀ s) : KeepsFilesBut [] s₀ s :=
  fun _ _ => ⟨by rw [h.files], fun _ => by rw [h.files]⟩

/-- Memory changed only at the `rseq` ids and the bytes of `ws`, which `foot` holds. -/
theorem changesOnly (h : KeptW ws s₀ s) {foot : List Rgn}
    (hid : ∀ y, IdAddr s₀.thread.rseq y ∨ Foot ws y → Foot foot y) : ChangesOnly s₀ s foot := by
  refine ⟨?_, fun fp o _ _ => by rw [h.files]⟩
  rintro l ⟨a, ha⟩ hk hf hfoot
  rcases hm : s₀.proc.mm.mem.map (pageOf a) with _ | mx
  · simp [byteLoc, hm] at ha
  simp only [byteLoc, hm, Option.map_some, Option.some.injEq] at ha
  subst ha
  have e := h.calm.byte a (by
      intro mp hmp
      rw [hm] at hmp; cases hmp
      unfold BStable
      split
      · next f e => exact hk f e
      · next f e => exact hf f e
      · trivial)
    (by
      intro y hy e
      exact hfoot y (hid y hy) (by simpa [byteLoc, locOf, hm] using e))
  simp only [Memory.readByte, h.mem_map, hm, h.files] at e
  simpa [byteAt, h.files] using e

end KeptW

/-! ## The bytes of a footprint outside `ws` -/

/-- A byte of a footprint's regions, not one of `ws` (data of the footprint), where the kernel stores only the
`rseq` ids, is as at the call. -/
theorem Calm.readByte_apart {feat : Features} {s₀ : State} {fp : Footprint} (hok : fp.Ok feat s₀)
    (hrq : RseqQuiet feat s₀) {ws : List Rgn} (hws : ∀ y, Foot ws y → Foot fp.data y) {M : Memory}
    (hc : Calm (fun y => IdAddr s₀.thread.rseq y ∨ Foot ws y) s₀.proc.mm.mem M) {x : Addr}
    (hx : Foot (fp.data ++ fp.codeRgns) x) (hxw : ¬ Foot ws x) : M.readByte x = s₀.proc.mm.mem.readByte x := by
  rcases hm : s₀.proc.mm.mem.map (pageOf x) with _ | mx
  · simp [Memory.readByte, hc.map, hm]
  obtain ⟨r, hr, hrx⟩ := hx
  apply hc.byte
  · intro mp hmp
    rw [hm] at hmp; cases hmp
    have := hok.notKernel x ⟨r, hr, hrx⟩ mx hm
    unfold BStable
    split
    · next f e => exact this.1 f e
    · next f e => exact this.2 f e
    · trivial
  · intro y hy
    rcases hy with hy | hy
    · obtain ⟨q, hq, hqy⟩ := IdAddr.foot_area (RseqQuiet.fits hrq) hy
      have hne : x ≠ y := fun e => hok.rseqApart q hq r hr y hqy (e ▸ hrx)
      exact locOf_ne_of_noAlias hok.noAlias ⟨r, List.mem_append_left _ hr, hrx⟩
        ⟨q, List.mem_append_right _ hq, hqy⟩ hne (by simp [hm])
    · have hne : x ≠ y := fun e => hxw (e ▸ hy)
      obtain ⟨q, hq, hqy⟩ := hws y hy
      exact locOf_ne_of_noAlias hok.noAlias ⟨r, List.mem_append_left _ hr, hrx⟩
        ⟨q, List.mem_append_left _ (List.mem_append_left _ hq), hqy⟩ hne (by simp [hm])

/-- The bytes `a` to `a + n - 1` of a footprint's regions, none of `ws`, as `readBytes` reads them. -/
theorem Calm.readBytes_apart {feat : Features} {s₀ : State} {fp : Footprint} (hok : fp.Ok feat s₀)
    (hrq : RseqQuiet feat s₀) {ws : List Rgn} (hws : ∀ y, Foot ws y → Foot fp.data y) {M : Memory}
    (hc : Calm (fun y => IdAddr s₀.thread.rseq y ∨ Foot ws y) s₀.proc.mm.mem M) {a : Addr} {n : Nat}
    (hx : ∀ i < n, Foot (fp.data ++ fp.codeRgns) (a.add i)) (hxw : ∀ i < n, ¬ Foot ws (a.add i)) :
    readBytes M a n = readBytes s₀.proc.mm.mem a n := by
  unfold readBytes
  apply List.map_congr_left
  intro x hxa
  obtain ⟨i, hi, rfl⟩ := mem_byteAddrs.1 hxa
  exact hc.readByte_apart hok hrq hws (hx i hi) (hxw i hi)

/-- The code, where the kernel stores only the `rseq` ids and the run only into data of the footprint. -/
theorem KeptW.codeAt {feat : Features} {s₀ s : State} {fp : Footprint} (hok : fp.Ok feat s₀)
    (hrq : RseqQuiet feat s₀) {ws : List Rgn} (hws : ∀ y, Foot ws y → Foot fp.data y) (h : KeptW ws s₀ s) {e : Addr}
    {bs : List Byte} (hin : CodeIn fp.code e bs) : CodeAt feat s.cpu.pkru s.proc.mm.mem e bs := by
  obtain ⟨hc, hf⟩ := codeAt_of_codeIn hok hin
  intro j hj
  obtain ⟨h1, h2, h3⟩ := hc j hj
  obtain ⟨r, hr, hm⟩ := hf j hj
  refine ⟨h1, by rw [h.calm.check, h.pkru]; exact h2, ?_⟩
  rw [h.calm.readByte_apart hok hrq hws ⟨r, List.mem_append_right _ hr, hm⟩ (fun hw => by
      obtain ⟨q, hq, hqm⟩ := hws _ hw
      exact hok.codeApart q hq r hr _ hqm hm)]
  exact h3

/-- `AreaQuiet.of_calm`, for stores at places other than those of the critical-section word. -/
theorem AreaQuiet.of_calm' {feat : Features} {pkru : BitVec 32} {m M : Memory} {r : RseqReg}
    (hq : AreaQuiet feat pkru m (some r)) {A : Addr → Prop} (h : Calm A m M)
    (hA : ∀ y, A y → ∀ j < 32, 8 ≤ j → j < 16 → locOf m y ≠ locOf m (r.area.add j)) :
    AreaQuiet feat pkru M (some r) := by
  obtain ⟨hok, hd, hcs⟩ := hq
  refine ⟨hok.of_calm h, fun j hj k hk e => by simpa [h.locOf_eq] using hd j hj k hk e, ?_⟩
  rw [← hcs]
  congr 1
  unfold readBytes
  apply List.map_congr_left
  intro x hx
  obtain ⟨i, hi, rfl⟩ := mem_byteAddrs.1 hx
  rw [addr_add_add]
  exact h.byte _ ((hok (8 + i) (by omega)).2.2.stableAt) fun y hy => hA y hy (8 + i) (by omega) (by omega) (by omega)

/-- The `rseq` area stays quiet, when the run stores only into data of the footprint. -/
theorem KeptW.quiet {feat : Features} {s₀ s : State} {fp : Footprint} (hok : fp.Ok feat s₀)
    (hrq : RseqQuiet feat s₀) {ws : List Rgn} (hws : ∀ y, Foot ws y → Foot fp.data y) (h : KeptW ws s₀ s)
    (hq : Quiet feat s₀) : Quiet feat s := by
  have hfit := RseqQuiet.fits hrq
  have hna := hok.noAlias
  have hap := hok.rseqApart
  have hc := h.calm
  unfold Quiet at hq ⊢
  rw [h.thread, h.pkru]
  unfold rseqArea at hna hap
  rcases hr : s₀.thread.rseq with _ | r
  · trivial
  rw [hr] at hq hc hna hap
  refine AreaQuiet.of_calm' hq hc fun y hy j hj _ _ => ?_
  rcases hy with ⟨k, hk, rfl⟩ | hy
  · exact hq.2.1 k (by omega) j hj (by omega)
  · obtain ⟨q, hq', hqy⟩ := hws y hy
    have hz : Rgn.Mem ⟨r.area, 32⟩ (r.area.add j) := mem_add_of_fits hj (hfit r hr)
    have hne : r.area.add j ≠ y := fun e => hap _ (List.mem_singleton_self _) q (List.mem_append_left _ hq') _ hz
      (e ▸ hqy)
    exact locOf_ne_of_noAlias hna ⟨_, by simp, hz⟩ ⟨q, List.mem_append_left _ (List.mem_append_left _ hq'), hqy⟩ hne
      (map_ne_none_of_check (hq.1 j hj).2.1)

/-- A step of an undisturbed run from a state `X` whose `rseq` area is quiet: `runsFrom_ins`, for any frame. -/
theorem runsFrom_insQ {prof : Profile} {o : Oracle} {I : State → Prop} {pre : List Event} {X : State} {t : Nat}
    {P : State → Nat → List Event → Prop} {E : Outcome → List Event → Prop}
    (hU : Undisturbed o) (hqX : Quiet prof.feat X) (hI : I X)
    (h : ∀ M, Calm (IdAddr X.thread.rseq) X.proc.mm.mem M → ∃ Y t',
      (instruction prof (X.withMem M)).runStream o (t + 1) = (.running Y none, t') ∧ RunsFrom prof o I pre Y t' P E) :
    RunsFrom prof o I pre X t P E := by
  obtain ⟨-, M, hkd, hc⟩ := envEvents_quiet prof.feat (evsAt prof o t) X hqX fun e he => hU t prof.cpus e he
  obtain ⟨Y, t', hY, k⟩ := h M hc
  exact runsFrom_step hI (step_next hU hqX (by rw [hkd]; exact hY)) (by simpa using k)

end FV7z
