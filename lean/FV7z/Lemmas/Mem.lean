import FV7z.Lemmas.KeptW
/-!
# Loads after stores (PLAN.md G2, "Dispatch theo CPUID", 7-Zip)

A function with a stack frame reads back what it stored: the return address `call` pushed, a register `push` saved,
the canary it copied into its frame, the words a callee stored into its buffer. What a load reads there:
- after a store of `bs` at `a`, the bytes at `a` are `bs` (`readBytes_writeBytes_self`), when the bytes stored lie
  in the process's own memory at distinct places;
- a change of memory calm at the places of some addresses `A` of a footprint (a store, the kernel's stores of the
  `rseq` ids, a callee's run) leaves the bytes of the footprint outside `A` as they were (`Calm.readByte_apart'`,
  from any memory a run from the call reached calmly).
-/
namespace FV7z
open ZellicX86

/-! ## Addresses -/

@[simp] theorem addr_add_zero (a : Addr) : a.add 0 = a := by simp [Addr.add]

theorem byteAddrs_succ (a : Addr) (n : Nat) : byteAddrs a (n + 1) = a :: byteAddrs (a.add 1) n := by
  simp only [byteAddrs, List.range_succ_eq_map, List.map_cons, List.map_map, addr_add_zero]
  congr 1
  apply List.map_congr_left
  intro i _
  simp [Function.comp, addr_add_add, Nat.add_comm]

theorem writeBytes_cons (m : Memory) (a : Addr) (b : Byte) (bs : List Byte) :
    writeBytes m a (b :: bs) = writeBytes (m.writeByte a b) (a.add 1) bs := by
  simp only [writeBytes, List.length_cons, byteAddrs_succ, List.zip_cons_cons, List.foldl_cons]

theorem readBytes_succ (m : Memory) (a : Addr) (n : Nat) :
    readBytes m a (n + 1) = m.readByte a :: readBytes m (a.add 1) n := by
  simp [readBytes, byteAddrs_succ]

/-! ## One store -/

/-- A store of a byte into the process's own memory, read back. -/
theorem readByte_writeByte_self {m : Memory} {a : Addr} {v : Byte} (ho : OwnAt m a)
    (hm : m.map (pageOf a) ≠ none) : (m.writeByte a v).readByte a = v := by
  unfold Memory.writeByte
  rcases hma : m.map (pageOf a) with _ | ma
  · exact absurd hma hm
  · have hown := ho ma hma
    dsimp only
    rcases hbk : m.backings ma.backing with f | f | fp | fp | f <;> rw [hbk] at hown <;>
      simp only [BOwn] at hown <;>
      simp [Memory.readByte, Memory.setBacking, hma, Backing.frame, Frame.set]

/-! ## Stores of several bytes -/

/-- A store of `bs` at `a`, read back, when its bytes lie in the process's own memory, where it may write, at
distinct places. -/
theorem readBytes_writeBytes_self {feat : Features} {pkru : BitVec 32} :
    ∀ (bs : List Byte) (m : Memory) (a : Addr),
      (∀ i < bs.length, m.check feat pkru .write (a.add i) = none ∧ OwnAt m (a.add i)) →
      (∀ i < bs.length, ∀ j < bs.length, i ≠ j → locOf m (a.add i) ≠ locOf m (a.add j)) →
      readBytes (writeBytes m a bs) a bs.length = bs
  | [], _, _, _, _ => rfl
  | b :: bs, m, a, hw, hd => by
    have h0 := hw 0 (by simp)
    rw [addr_add_zero] at h0
    have c1 : Calm (· = a) m (m.writeByte a b) := writeByte_calm b h0.1 h0.2
    have hw' : ∀ i < bs.length, (m.writeByte a b).check feat pkru .write ((a.add 1).add i) = none ∧
        OwnAt (m.writeByte a b) ((a.add 1).add i) := by
      intro i hi
      have := hw (i + 1) (by simp; omega)
      rw [addr_add_add, Nat.add_comm 1 i]
      exact ⟨by rw [c1.check]; exact this.1, c1.ownAt this.2⟩
    have hd' : ∀ i < bs.length, ∀ j < bs.length, i ≠ j →
        locOf (m.writeByte a b) ((a.add 1).add i) ≠ locOf (m.writeByte a b) ((a.add 1).add j) := by
      intro i hi j hj hij
      rw [c1.locOf_eq, c1.locOf_eq, addr_add_add, addr_add_add, Nat.add_comm 1 i, Nat.add_comm 1 j]
      exact hd (i + 1) (by simp; omega) (j + 1) (by simp; omega) (by omega)
    rw [writeBytes_cons, List.length_cons, readBytes_succ, readBytes_writeBytes_self bs (m.writeByte a b) (a.add 1) hw' hd']
    congr 1
    have c2 := writeBytes_calm (bs := bs) (a := a.add 1) fun x hx => by
      obtain ⟨i, hi, rfl⟩ := mem_byteAddrs.1 hx
      exact hw' i hi
    rw [c2.byte a (c1.ownAt h0.2).stableAt fun y hy => by
      obtain ⟨i, hi, rfl⟩ := mem_byteAddrs.1 hy
      rw [c1.locOf_eq, c1.locOf_eq, addr_add_add, Nat.add_comm 1 i]
      have := hd (i + 1) (by simp; omega) 0 (by simp) (by omega)
      rwa [addr_add_zero] at this]
    exact readByte_writeByte_self h0.2 (map_ne_none_of_check h0.1)

/-! ## Bytes of a footprint, apart from what changed -/

/-- From a memory `m` a run from `s₀` reached calmly, a change calm at the `rseq` ids and at addresses `A` of the
footprint's data leaves a byte of the footprint not in `A` as it was. -/
theorem Calm.readByte_apart' {feat : Features} {s₀ : State} {fp : Footprint} (hok : fp.Ok feat s₀)
    (hrq : RseqQuiet feat s₀) {B : Addr → Prop} {m : Memory} (h₀ : Calm B s₀.proc.mm.mem m) {A : Addr → Prop}
    (hA : ∀ y, A y → Foot fp.data y) {M : Memory} (hc : Calm (fun y => IdAddr s₀.thread.rseq y ∨ A y) m M)
    {x : Addr} (hx : Foot (fp.data ++ fp.codeRgns) x) (hxA : ¬ A x) : M.readByte x = m.readByte x := by
  rcases hm : s₀.proc.mm.mem.map (pageOf x) with _ | mx
  · simp [Memory.readByte, hc.map, h₀.map, hm]
  obtain ⟨r, hr, hrx⟩ := hx
  apply hc.byte
  · apply h₀.stableAt
    intro mp hmp
    rw [hm] at hmp; cases hmp
    have := hok.notKernel x ⟨r, hr, hrx⟩ mx hm
    unfold BStable
    split
    · next f e => exact this.1 f e
    · next f e => exact this.2 f e
    · trivial
  · intro y hy
    rw [h₀.locOf_eq, h₀.locOf_eq]
    rcases hy with hy | hy
    · obtain ⟨q, hq, hqy⟩ := IdAddr.foot_area (RseqQuiet.fits hrq) hy
      have hne : x ≠ y := fun e => hok.rseqApart q hq r hr y hqy (e ▸ hrx)
      exact locOf_ne_of_noAlias hok.noAlias ⟨r, List.mem_append_left _ hr, hrx⟩
        ⟨q, List.mem_append_right _ hq, hqy⟩ hne (by simp [hm])
    · have hne : x ≠ y := fun e => hxA (e ▸ hy)
      obtain ⟨q, hq, hqy⟩ := hA y hy
      exact locOf_ne_of_noAlias hok.noAlias ⟨r, List.mem_append_left _ hr, hrx⟩
        ⟨q, List.mem_append_left _ (List.mem_append_left _ hq), hqy⟩ hne (by simp [hm])

/-- `Calm.readByte_apart'` for the bytes `a` to `a + n - 1`. -/
theorem Calm.readBytes_apart' {feat : Features} {s₀ : State} {fp : Footprint} (hok : fp.Ok feat s₀)
    (hrq : RseqQuiet feat s₀) {B : Addr → Prop} {m : Memory} (h₀ : Calm B s₀.proc.mm.mem m) {A : Addr → Prop}
    (hA : ∀ y, A y → Foot fp.data y) {M : Memory} (hc : Calm (fun y => IdAddr s₀.thread.rseq y ∨ A y) m M)
    {a : Addr} {n : Nat} (hx : ∀ i < n, Foot (fp.data ++ fp.codeRgns) (a.add i)) (hxA : ∀ i < n, ¬ A (a.add i)) :
    readBytes M a n = readBytes m a n := by
  unfold readBytes
  apply List.map_congr_left
  intro x hxa
  obtain ⟨i, hi, rfl⟩ := mem_byteAddrs.1 hxa
  exact Calm.readByte_apart' hok hrq h₀ hA hc (hx i hi) (hxA i hi)

/-- Distinct bytes of a footprint's data that pass a check lie at distinct places, in a memory a run from `s₀`
reached calmly. -/
theorem locOf_ne_foot {feat : Features} {s₀ : State} {fp : Footprint} (hok : fp.Ok feat s₀) {B : Addr → Prop}
    {m : Memory} (h₀ : Calm B s₀.proc.mm.mem m) {x y : Addr} (hx : Foot fp.data x) (hy : Foot fp.data y)
    (hne : x ≠ y) {pkru : BitVec 32} {acc : Access} (hc : m.check feat pkru acc y = none) :
    locOf m x ≠ locOf m y := by
  rw [h₀.locOf_eq, h₀.locOf_eq]
  obtain ⟨r, hr, hrx⟩ := hx
  obtain ⟨q, hq, hqy⟩ := hy
  refine locOf_ne_of_noAlias hok.noAlias ⟨q, List.mem_append_left _ (List.mem_append_left _ hq), hqy⟩
    ⟨r, List.mem_append_left _ (List.mem_append_left _ hr), hrx⟩ (Ne.symm hne) ?_
  rw [← h₀.map]
  exact map_ne_none_of_check hc

end FV7z
