import FV7z.Lemmas.Mem
/-!
# The footprint's bytes as a function (PLAN.md G2, "Dispatch theo CPUID", 7-Zip)

A run of a function with a stack frame stores and loads back. Rather than carry each fact about some bytes through
every step, a proof carries one: the bytes of the footprint's data are those of a function `V : Addr → Byte`
(`Agree`). The kernel's stores of the `rseq` ids keep it (`Agree.kernel`); a store of `bs` at `a` changes `V` as
`writeBytes` changes memory (`Vst`, `Agree.writeBytes`); a load reads `V` (`Agree.read`). What a load after stores
reads is then a fact about functions (`Vst_self`, `Vst_apart`).
-/
namespace FV7z
open ZellicX86

/-- The bytes of the footprint's data `fp.data` in memory `m` are those of `V`. -/
def Agree (fp : Footprint) (m : Memory) (V : Addr → Byte) : Prop :=
  ∀ a, Foot fp.data a → m.readByte a = V a

/-- `V` with byte `b` at `a`. -/
def upd1 (V : Addr → Byte) (a : Addr) (b : Byte) : Addr → Byte := fun x => if x = a then b else V x

/-- `V` with the bytes `bs` stored at `a`, in the order `writeBytes` stores them. -/
def Vst : (Addr → Byte) → Addr → List Byte → Addr → Byte
  | V, _, [] => V
  | V, a, b :: bs => Vst (upd1 V a b) (a.add 1) bs

/-! ## The function -/

theorem Vst_apart : ∀ (bs : List Byte) (V : Addr → Byte) (a x : Addr), (∀ i < bs.length, x ≠ a.add i) →
    Vst V a bs x = V x
  | [], _, _, _, _ => rfl
  | b :: bs, V, a, x, h => by
    simp only [Vst]
    rw [Vst_apart bs _ _ x fun i hi => by
      rw [addr_add_add, Nat.add_comm 1 i]; exact h (i + 1) (by simp; omega)]
    have := h 0 (by simp)
    rw [addr_add_zero] at this
    simp [upd1, this]

theorem Vst_self : ∀ (bs : List Byte) (V : Addr → Byte) (a : Addr), a.toNat + bs.length ≤ 2 ^ 64 →
    (byteAddrs a bs.length).map (Vst V a bs) = bs
  | [], _, _, _ => rfl
  | b :: bs, V, a, hf => by
    simp only [List.length_cons, byteAddrs_succ, List.map_cons, Vst]
    have hf' : (a.add 1).toNat + bs.length ≤ 2 ^ 64 := by
      rcases Nat.eq_zero_or_pos bs.length with h0 | h0
      · rw [h0]; have := (a.add 1).isLt; omega
      · rw [toNat_add_of_fits (n := bs.length + 1) (by omega) (by simpa using hf)]
        simp at hf; omega
    rw [Vst_self bs _ _ hf', Vst_apart bs _ _ a fun i hi => by
      rw [addr_add_add]
      intro e
      have := congrArg BitVec.toNat e
      rw [toNat_add_of_fits (n := bs.length + 1) (by omega) (by simpa using hf)] at this
      omega]
    simp [upd1]

/-! ## Memory -/

/-- A byte of a footprint is stored, if anywhere, in a stable backing, in a memory a run from `s₀` reached calmly. -/
theorem stableAt_foot {feat : Features} {s₀ : State} {fp : Footprint} (hok : fp.Ok feat s₀) {B : Addr → Prop}
    {m : Memory} (h₀ : Calm B s₀.proc.mm.mem m) {x : Addr} (hx : Foot (fp.data ++ fp.codeRgns) x) :
    StableAt m x := by
  apply h₀.stableAt
  intro mp hmp
  have := hok.notKernel x hx mp hmp
  unfold BStable
  split
  · next f e => exact this.1 f e
  · next f e => exact this.2 f e
  · trivial

theorem foot_data {fp : Footprint} {x : Addr} (h : Foot fp.data x) : Foot (fp.data ++ fp.codeRgns) x := by
  obtain ⟨r, hr, hm⟩ := h
  exact ⟨r, List.mem_append_left _ hr, hm⟩

/-- The kernel's stores of the `rseq` ids keep `Agree`. -/
theorem Agree.kernel {feat : Features} {s₀ : State} {fp : Footprint} (hok : fp.Ok feat s₀) (hrq : RseqQuiet feat s₀)
    {B : Addr → Prop} {m : Memory} (h₀ : Calm B s₀.proc.mm.mem m) {V : Addr → Byte} (hA : Agree fp m V) {M : Memory}
    (hc : Calm (IdAddr s₀.thread.rseq) m M) : Agree fp M V := by
  intro a ha
  rw [Calm.readByte_apart' hok hrq h₀ (A := fun _ => False) (fun _ h => h.elim) (hc.mono fun _ hy => Or.inl hy)
    (foot_data ha) id]
  exact hA a ha

/-- A store of a byte of the footprint's data, in the process's own memory where it may write. -/
theorem Agree.writeByte {feat : Features} {s₀ : State} {fp : Footprint} (hok : fp.Ok feat s₀) {B : Addr → Prop}
    {m : Memory} (h₀ : Calm B s₀.proc.mm.mem m) {V : Addr → Byte} (hA : Agree fp m V) {a : Addr}
    (ha : Foot fp.data a) {pkru : BitVec 32} (hc : m.check feat pkru .write a = none) (ho : OwnAt m a) (b : Byte) :
    Agree fp (m.writeByte a b) (upd1 V a b) := by
  intro x hx
  by_cases e : x = a
  · subst e
    simp only [upd1, ite_true]
    exact readByte_writeByte_self ho (map_ne_none_of_check hc)
  · simp only [upd1, e, ite_false]
    rw [(writeByte_calm b hc ho).byte x (stableAt_foot hok h₀ (foot_data hx)) fun y hy => by
      subst hy; exact (locOf_ne_foot hok h₀ hx ha e hc).symm]
    exact hA x hx

/-- A store of bytes of the footprint's data, in the process's own memory where it may write. -/
theorem Agree.writeBytes {feat : Features} {s₀ : State} {fp : Footprint} (hok : fp.Ok feat s₀) {pkru : BitVec 32} :
    ∀ (bs : List Byte) (m : Memory) (a : Addr) (V : Addr → Byte), Calm (fun _ => True) s₀.proc.mm.mem m →
      (∀ i < bs.length, Foot fp.data (a.add i) ∧ m.check feat pkru .write (a.add i) = none ∧ OwnAt m (a.add i)) →
      Agree fp m V → Agree fp (ZellicX86.writeBytes m a bs) (Vst V a bs)
  | [], _, _, _, _, _, hA => hA
  | b :: bs, m, a, V, h₀, hw, hA => by
    have h0 := hw 0 (by simp)
    rw [addr_add_zero] at h0
    have c1 := writeByte_calm b h0.2.1 h0.2.2
    rw [writeBytes_cons]
    show Agree fp _ (Vst (upd1 V a b) (a.add 1) bs)
    refine Agree.writeBytes hok (pkru := pkru) bs _ _ _ (h₀.trans (c1.mono fun _ _ => trivial)) (fun i hi => ?_)
      (hA.writeByte hok h₀ h0.1 h0.2.1 h0.2.2 b)
    have := hw (i + 1) (by simp; omega)
    rw [addr_add_add, Nat.add_comm 1 i]
    exact ⟨this.1, by rw [c1.check]; exact this.2.1, c1.ownAt this.2.2⟩

/-- A load of bytes of the footprint's data reads `V`. -/
theorem Agree.read {fp : Footprint} {m : Memory} {V : Addr → Byte} (hA : Agree fp m V) {a : Addr} {n : Nat}
    (h : ∀ i < n, Foot fp.data (a.add i)) : readBytes m a n = (byteAddrs a n).map V := by
  unfold readBytes
  apply List.map_congr_left
  intro x hx
  obtain ⟨i, hi, rfl⟩ := mem_byteAddrs.1 hx
  exact hA _ (h i hi)

end FV7z
