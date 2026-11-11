import FV7z.Lemmas.Step
/-!
# What a call keeps (PLAN.md G2.0)

A function that stores nothing, makes no system call and changes no setting leaves the state as it found it but for
some registers, `rip`, the status flags and the bytes the kernel stores into the thread's `rseq` area at returns to user
mode (`IdAddr`, as `Calm` relates the memories). `Kept s₀ s` says this of a state `s` of a run from `s₀`, and gives
the parts of a contract's frame (`Contract.Frame`) that such a function keeps: the layout (`KeepsEnv`), the settings
(`KeepsSettingsBut`), the process (`KeepsProc`), the files (`KeepsFilesBut`), and memory but the `rseq` ids
(`ChangesOnly`). And what lies in a footprint (`Footprint.Ok`): the bytes of its regions are as at the call
(`Calm.readByte_foot`).
-/
namespace FV7z
open ZellicX86

/-! ## Addresses -/

/-- An address is its page and its offset. -/
theorem eq_of_page {x y : Addr} (hp : pageOf x = pageOf y) (ho : pageOffset x = pageOffset y) : x = y := by
  apply BitVec.eq_of_toNat_eq
  have h1 := congrArg BitVec.toNat hp
  have h2 := congrArg BitVec.toNat ho
  simp only [pageOf, pageOffset, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow] at h1 h2
  have := x.isLt; have := y.isLt
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at h1
  omega

/-- `a.add i` within a region that does not reach past `2 ^ 64`. -/
theorem toNat_add_of_fits {a : Addr} {i n : Nat} (hi : i < n) (hf : a.toNat + n ≤ 2 ^ 64) :
    (a.add i).toNat = a.toNat + i := by
  simp only [Addr.add, BitVec.toNat_add, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (a := i) (by omega), Nat.mod_eq_of_lt (by omega)]

/-- `a.add i` is in the region from `a` of `n` bytes, which fits. -/
theorem mem_add_of_fits {a : Addr} {i n : Nat} (hi : i < n) (hf : a.toNat + n ≤ 2 ^ 64) : Rgn.Mem ⟨a, n⟩ (a.add i) := by
  simp only [Rgn.Mem, toNat_add_of_fits hi hf]; omega

/-- Distinct addresses of regions without aliases are stored at distinct places. -/
theorem locOf_ne_of_noAlias {s : State} {rs : List Rgn} (h : NoAliasOver s rs) {x y : Addr} (hx : Foot rs x)
    (hy : Foot rs y) (hne : x ≠ y) (hm : s.proc.mm.mem.map (pageOf x) ≠ none) :
    locOf s.proc.mm.mem y ≠ locOf s.proc.mm.mem x := by
  intro e
  rcases hmx : s.proc.mm.mem.map (pageOf x) with _ | mx
  · exact hm hmx
  rcases hmy : s.proc.mm.mem.map (pageOf y) with _ | my
  · simp [locOf, hmx, hmy] at e
  simp only [locOf, hmx, hmy, Option.map_some, Option.some.injEq, ByteLoc.mk.injEq] at e
  by_cases hp : pageOf x = pageOf y
  · exact hne (eq_of_page hp e.2.symm)
  · exact (h x y hx hy hp mx my hmx hmy).1 e.1.symm

/-! ## The `rseq` area -/

/-- The id addresses of an area that fits are in it. -/
theorem IdAddr.foot_area {s : State} (hf : ∀ r, s.thread.rseq = some r → r.area.toNat + 32 ≤ 2 ^ 64) {y : Addr}
    (hy : IdAddr s.thread.rseq y) : Foot (rseqArea s) y := by
  unfold rseqArea
  rcases hr : s.thread.rseq with _ | r
  · rw [hr] at hy; exact hy.elim
  · rw [hr] at hy
    obtain ⟨j, hj, rfl⟩ := hy
    exact ⟨_, List.mem_singleton_self _, mem_add_of_fits (by omega) (hf r hr)⟩

/-- The id addresses of an area that fits are those of `rseqIds`. -/
theorem IdAddr.foot_ids {s : State} (hf : ∀ r, s.thread.rseq = some r → r.area.toNat + 32 ≤ 2 ^ 64) {y : Addr}
    (hy : IdAddr s.thread.rseq y) : Foot (rseqIds s) y := by
  unfold rseqIds
  rcases hr : s.thread.rseq with _ | r
  · rw [hr] at hy; exact hy.elim
  · rw [hr] at hy
    obtain ⟨j, hj, rfl⟩ := hy
    have hf := hf r hr
    rcases hj with hj | hj
    · exact ⟨_, List.mem_cons_self, mem_add_of_fits hj (by omega)⟩
    · refine ⟨⟨r.area.add 20, 8⟩, List.mem_cons_of_mem _ List.mem_cons_self, ?_⟩
      simp only [Rgn.Mem, toNat_add_of_fits (show j < 32 by omega) hf,
        toNat_add_of_fits (show 20 < 32 by omega) hf]
      omega

/-- The area of a quiet `rseq` registration fits. -/
theorem RseqQuiet.fits {feat : Features} {s : State} (h : RseqQuiet feat s) :
    ∀ r, s.thread.rseq = some r → r.area.toNat + 32 ≤ 2 ^ 64 := by
  intro r hr
  unfold RseqQuiet at h
  rw [hr] at h
  exact h.1

/-! ## The bytes of a footprint -/

/-- A byte of a footprint's regions, where the kernel stores only the `rseq` ids, is as at the call. -/
theorem Calm.readByte_foot {feat : Features} {s₀ : State} {fp : Footprint} (hok : fp.Ok feat s₀)
    (hrq : RseqQuiet feat s₀) {M : Memory} (hc : Calm (IdAddr s₀.thread.rseq) s₀.proc.mm.mem M) {x : Addr}
    (hx : Foot (fp.data ++ fp.codeRgns) x) : M.readByte x = s₀.proc.mm.mem.readByte x := by
  rcases hm : s₀.proc.mm.mem.map (pageOf x) with _ | mx
  · simp [Memory.readByte, hc.map, hm]
  apply hc.byte
  · intro mp hmp
    rw [hm] at hmp; cases hmp
    have := hok.notKernel x hx mx hm
    unfold BStable
    split
    · next f e => exact this.1 f e
    · next f e => exact this.2 f e
    · trivial
  · intro y hy
    have hya := IdAddr.foot_area (RseqQuiet.fits hrq) hy
    obtain ⟨q, hq, hqy⟩ := hya
    obtain ⟨r, hr, hrx⟩ := hx
    have hne : x ≠ y := fun e => hok.rseqApart q hq r hr y hqy (e ▸ hrx)
    exact locOf_ne_of_noAlias hok.noAlias ⟨r, List.mem_append_left _ hr, hrx⟩ ⟨q, List.mem_append_right _ hq, hqy⟩ hne
      (by simp [hm])

/-- The bytes of a footprint's region, as `readBytes` reads them. -/
theorem Calm.readBytes_foot {feat : Features} {s₀ : State} {fp : Footprint} (hok : fp.Ok feat s₀)
    (hrq : RseqQuiet feat s₀) {M : Memory} (hc : Calm (IdAddr s₀.thread.rseq) s₀.proc.mm.mem M) {a : Addr} {n : Nat}
    (hx : ∀ i < n, Foot (fp.data ++ fp.codeRgns) (a.add i)) : readBytes M a n = readBytes s₀.proc.mm.mem a n := by
  unfold readBytes
  apply List.map_congr_left
  intro x hxa
  obtain ⟨i, hi, rfl⟩ := mem_byteAddrs.1 hxa
  exact hc.readByte_foot hok hrq (hx i hi)

/-! ## Kept -/

/-- From `s₀` to `s`, all is as it was but the general-purpose registers, `rip`, the flags other than `TF`, `AC` and
`DF`, the vector and opmask registers (`MXCSR` is kept), and memory, which changed only calmly, at the `rseq` ids. -/
structure Kept (s₀ s : State) : Prop where
  proc : s.proc = { s₀.proc with mm := { s₀.proc.mm with mem := s.proc.mm.mem } }
  calm : Calm (IdAddr s₀.thread.rseq) s₀.proc.mm.mem s.proc.mm.mem
  thread : s.thread = s₀.thread
  seg : s.cpu.seg = s₀.cpu.seg
  x87 : s.cpu.x87 = s₀.cpu.x87
  mxcsr : s.cpu.vec.mxcsr = s₀.cpu.vec.mxcsr
  pkru : s.cpu.pkru = s₀.cpu.pkru
  tf : s.cpu.rflags.tf = s₀.cpu.rflags.tf
  ac : s.cpu.rflags.ac = s₀.cpu.rflags.ac
  df : s.cpu.rflags.df = s₀.cpu.rflags.df

namespace Kept
variable {s₀ s : State}

protected theorem refl (s : State) : Kept s s :=
  ⟨rfl, Calm.refl _ _, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The kernel's calm stores of the ids. -/
theorem withMem (h : Kept s₀ s) {M : Memory} (hc : Calm (IdAddr s.thread.rseq) s.proc.mm.mem M) :
    Kept s₀ (s.withMem M) where
  proc := by
    have e := h.proc
    simp only [State.withMem]
    rw [e]
  calm := h.calm.trans (h.thread ▸ hc)
  thread := h.thread
  seg := h.seg
  x87 := h.x87
  mxcsr := h.mxcsr
  pkru := h.pkru
  tf := h.tf
  ac := h.ac
  df := h.df

/-- A change of the registers, `rip` and the flags that keeps `TF`, `AC`, `DF` and `MXCSR`. -/
theorem modCpu (h : Kept s₀ s) {f : Cpu → Cpu} (hseg : (f s.cpu).seg = s.cpu.seg) (hx : (f s.cpu).x87 = s.cpu.x87)
    (hv : (f s.cpu).vec.mxcsr = s.cpu.vec.mxcsr) (hp : (f s.cpu).pkru = s.cpu.pkru)
    (htf : (f s.cpu).rflags.tf = s.cpu.rflags.tf) (hac : (f s.cpu).rflags.ac = s.cpu.rflags.ac)
    (hdf : (f s.cpu).rflags.df = s.cpu.rflags.df) : Kept s₀ (s.modCpu f) :=
  ⟨h.proc, h.calm, h.thread, hseg.trans h.seg, hx.trans h.x87, hv.trans h.mxcsr, hp.trans h.pkru, htf.trans h.tf,
    hac.trans h.ac, hdf.trans h.df⟩

theorem mem_map (h : Kept s₀ s) : s.proc.mm.mem.map = s₀.proc.mm.mem.map := h.calm.map
theorem files (h : Kept s₀ s) : s.proc.mm.mem.files = s₀.proc.mm.mem.files := h.calm.files

theorem brk (h : Kept s₀ s) : s.proc.mm.brk = s₀.proc.mm.brk := by rw [h.proc]
theorem brkMin (h : Kept s₀ s) : s.proc.mm.brkMin = s₀.proc.mm.brkMin := by rw [h.proc]

/-- The layout is as at the call. -/
theorem keepsEnv (h : Kept s₀ s) : KeepsEnv s₀ s :=
  ⟨h.mem_map, h.calm.refines, h.calm.fresh, h.brk,
    ⟨fun _ _ _ => by rw [h.files], by rw [h.files], h.calm.growsDown, h.brkMin⟩⟩

theorem keepsSettings (h : Kept s₀ s) (hp : Plain s₀) : KeepsSettingsBut [] [] s₀ s where
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

theorem keepsProc (h : Kept s₀ s) : KeepsProc [] s₀ s where
  files := by rw [h.proc]
  pos _ _ := by rw [h.proc]
  append _ := by rw [h.proc]
  flags _ := by rw [h.proc]
  next := by rw [h.proc]
  sighand := by rw [h.proc]
  signal := by rw [h.proc]

theorem keepsFiles (h : Kept s₀ s) : KeepsFilesBut [] s₀ s :=
  fun _ _ => ⟨by rw [h.files], fun _ => by rw [h.files]⟩

/-- Memory changed only at the `rseq` ids, which `foot` holds. -/
theorem changesOnly (h : Kept s₀ s) {foot : List Rgn} (hid : ∀ y, IdAddr s₀.thread.rseq y → Foot foot y) :
    ChangesOnly s₀ s foot := by
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

end Kept

/-! ## At the call -/

/-- A byte that passes some check is mapped. -/
theorem map_ne_none_of_check {feat : Features} {pkru : BitVec 32} {m : Memory} {acc : Access} {x : Addr}
    (h : m.check feat pkru acc x = none) : m.map (pageOf x) ≠ none := by
  intro e
  rw [check_eq, e] at h
  simp at h

/-- The store of a byte the kernel does not own, may not drop and does not share with a file goes to the process's own
copy. -/
theorem ownAt_of {s : State} {rs : List Rgn} {x : Addr} (hk : NotKernel s rs) (hs : NotShared s rs) (hx : Foot rs x) :
    OwnAt s.proc.mm.mem x := by
  intro mp hmp
  have h1 := hk x hx mp hmp
  have h2 := hs x hx mp hmp
  cases hb : s.proc.mm.mem.backings mp.backing <;> simp only [BOwn] <;>
    first | exact (h1.1 _ hb).elim | exact (h1.2 _ hb).elim | exact (h2 _ hb).elim

/-- A quiet `rseq` registration, with an area without aliases, is quiet in the sense of `AreaQuiet`. -/
theorem quiet_of_rseqQuiet {feat : Features} {s : State} {rs : List Rgn} (h : RseqQuiet feat s)
    (hna : NoAliasOver s (rs ++ rseqArea s)) : Quiet feat s := by
  have hfit := RseqQuiet.fits h
  unfold Quiet AreaQuiet
  unfold RseqQuiet at h
  unfold rseqArea at hna
  rcases hr : s.thread.rseq with _ | r
  · trivial
  rw [hr] at h hna
  obtain ⟨hf, hacc, hk, hs, hw⟩ := h
  have hmem : ∀ j < 32, Rgn.Mem ⟨r.area, 32⟩ (r.area.add j) := fun j hj => mem_add_of_fits hj hf
  have hok : AreaOk feat s.cpu.pkru s.proc.mm.mem r := fun j hj =>
    ⟨(hacc _ (hmem j hj)).1, (hacc _ (hmem j hj)).2,
      ownAt_of hk hs ⟨_, List.mem_singleton_self _, hmem j hj⟩⟩
  refine ⟨hok, ?_, hw⟩
  intro j hj k hk' hjk
  have hne : r.area.add k ≠ r.area.add j := by
    intro e
    have := congrArg BitVec.toNat e
    rw [toNat_add_of_fits hk' hf, toNat_add_of_fits hj hf] at this
    omega
  exact (locOf_ne_of_noAlias hna ⟨_, by simp, hmem k hk'⟩ ⟨_, by simp, hmem j hj⟩ hne
    (map_ne_none_of_check (hok k hk').2.1))

/-- The bytes `bs` of the code at `e` lie in memory, fetchable. -/
theorem codeAt_of_codeIn {feat : Features} {s : State} {fp : Footprint} (hok : fp.Ok feat s) {e : Addr}
    {bs : List Byte} (hin : CodeIn fp.code e bs) :
    CodeAt feat s.cpu.pkru s.proc.mm.mem e bs ∧ ∀ j < bs.length, Foot fp.codeRgns (e.add j) := by
  obtain ⟨c, hc, k, rfl, hpre⟩ := hin
  obtain ⟨hacc, hby⟩ := hok.code c hc
  have hfit : c.1.toNat + c.2.length ≤ 2 ^ 64 :=
    hok.fits _ (List.mem_append_right _ (List.mem_map_of_mem (f := fun c : Addr × List Byte => (⟨c.1, c.2.length⟩ : Rgn)) hc))
  have hlen := hpre.length_le
  simp only [List.length_drop] at hlen
  have hkj : ∀ j < bs.length, k + j < c.2.length := fun j hj => by omega
  have hm : ∀ j < bs.length, Rgn.Mem ⟨c.1, c.2.length⟩ ((c.1.add k).add j) := fun j hj => by
    rw [addr_add_add]; exact mem_add_of_fits (hkj j hj) hfit
  refine ⟨fun j hjl => ⟨(hacc _ (hm j hjl)).1, (hacc _ (hm j hjl)).2, ?_⟩, fun j hjl =>
    ⟨_, List.mem_map_of_mem (f := fun c : Addr × List Byte => (⟨c.1, c.2.length⟩ : Rgn)) hc, hm j hjl⟩⟩
  have h1 : bs[j]? = (c.2.drop k)[j]? := by
    obtain ⟨t, ht⟩ := hpre
    rw [← ht, List.getElem?_append_left hjl]
  rw [h1, List.getElem?_drop]
  unfold Bytes readBytes byteAddrs at hby
  have h2 := congrArg (·[k + j]?) hby
  simp only [List.getElem?_map, List.getElem?_range (hkj j hjl), Option.map_some] at h2
  rw [← h2, addr_add_add]

/-- A state at the code's `j`-th byte is in the code. -/
theorem inCode_of_codeIn {L : List (Addr × List Byte)} {e : Addr} {bs : List Byte} (hin : CodeIn L e bs) {s : State}
    {j : Nat} (hj : j < bs.length) (hrip : s.cpu.rip = e.add j) : InCode L s := by
  obtain ⟨c, hc, k, rfl, hpre⟩ := hin
  have hlen := hpre.length_le
  simp only [List.length_drop] at hlen
  exact ⟨c, hc, k + j, by omega, by rw [hrip, addr_add_add]⟩

/-- The code where the kernel stores only the `rseq` ids. -/
theorem Kept.codeAt {feat : Features} {s₀ s : State} {fp : Footprint} (hok : fp.Ok feat s₀) (hrq : RseqQuiet feat s₀)
    (h : Kept s₀ s) {e : Addr} {bs : List Byte} (hin : CodeIn fp.code e bs) :
    CodeAt feat s.cpu.pkru s.proc.mm.mem e bs := by
  obtain ⟨hc, hf⟩ := codeAt_of_codeIn hok hin
  intro j hj
  obtain ⟨h1, h2, h3⟩ := hc j hj
  refine ⟨h1, by rw [h.calm.check, h.pkru]; exact h2, ?_⟩
  rw [h.calm.readByte_foot hok hrq (by obtain ⟨r, hr, hm⟩ := hf j hj; exact ⟨r, List.mem_append_right _ hr, hm⟩)]
  exact h3

/-- The `rseq` area stays quiet. -/
theorem Kept.quiet {feat : Features} {s₀ s : State} (h : Kept s₀ s) (hq : Quiet feat s₀) : Quiet feat s := by
  unfold Quiet
  rw [h.thread, h.pkru]
  exact AreaQuiet.of_calm hq h.calm

end FV7z
