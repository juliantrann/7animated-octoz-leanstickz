import ZellicX86.Spec.Statement
/-!
# The environment between two instructions (PLAN.md G2.0)

A step (`step`, Zellic `Spec/Step.lean`) first applies the events the environment chose (`envEvents`), then the
instruction. In an `Undisturbed` run every event is ordinary (`EnvEvent.ordinary`): the kernel ran and returned
(`kernelEntry`, which stores the CPU and concurrency ids into a registered `rseq` area), it rewrote a page it owns
(`kernelData`), or it dropped a lazily freed page (`reclaim`). This module shows what that does when the `rseq` area is
quiet (`AreaQuiet`: writable, private memory, no critical section): the step goes on running, with only the memory
changed (`kdata`), and the memory changed only as `Calm` says: the same layout, files and access checks, and the same
byte at every address on a page that is neither the kernel's nor lazily freed and that does not share its place with
the area's id bytes (`IdAddr`).

`step_runStream` is the lemma a proof uses at each instruction. The names follow the lemmas of Zellic's proof exports
(`AreaQuiet`, `kdata`, `envEvents_quiet`, `step_runStream`); the definitions and proofs here are this project's. Here
`kdata` applies the events one at a time, as `envEvents` does, rather than in Zellic's closed form, so that no lemma
on the order of the kernel's stores is needed: what a proof needs of the result is `Calm`.
-/
namespace FV7z
open ZellicX86

/-! ## Where bytes live -/

/-- Where the byte at `a` is stored, if its page is mapped. -/
def locOf (m : Memory) (a : Addr) : Option ByteLoc :=
  (m.map (pageOf a)).map fun mp => ⟨mp.backing, pageOffset a⟩

/-- A backing whose contents only the process and the files change: not the kernel's, not lazily freed. -/
def BStable : Backing → Prop
  | .kernel _ | .freed _ => False
  | _ => True

/-- Private memory or a private file mapping: a store goes to the process's own copy. -/
def BOwn : Backing → Prop
  | .priv _ | .cow _ => True
  | _ => False

theorem BOwn.stable {b : Backing} (h : BOwn b) : BStable b := by
  cases b <;> simp_all [BOwn, BStable]

/-- The byte at `a` is stored, if anywhere, in a `Stable` backing. -/
def StableAt (m : Memory) (a : Addr) : Prop :=
  ∀ mp, m.map (pageOf a) = some mp → BStable (m.backings mp.backing)

/-- The byte at `a` is stored, if anywhere, in an `Own` backing. -/
def OwnAt (m : Memory) (a : Addr) : Prop :=
  ∀ mp, m.map (pageOf a) = some mp → BOwn (m.backings mp.backing)

theorem OwnAt.stableAt {m : Memory} {a : Addr} (h : OwnAt m a) : StableAt m a :=
  fun mp hm => BOwn.stable (h mp hm)

/-! ## Calm changes of memory -/

theorem refines_refl (fs : Files) (b : Backing) : b.Refines fs b := by
  cases b <;> simp [Backing.Refines]

theorem refines_trans {fs : Files} {a b c : Backing} (h : b.Refines fs a) (k : c.Refines fs b) :
    c.Refines fs a := by
  cases a <;> cases b <;> cases c <;> simp_all [Backing.Refines]

/-- From `m` to `M` only backings changed, each as stores and the kernel's updates change it (`Backing.Refines`), none
became the kernel's or lazily freed or stopped being the process's own, every access check is as it was, and every byte
stored in a `Stable` backing at a place no address of `A` maps to is as it was. -/
structure Calm (A : Addr → Prop) (m M : Memory) : Prop where
  rest : { M with backings := m.backings } = m
  refines : ∀ j, (M.backings j).Refines m.files (m.backings j)
  stable : ∀ j, BStable (m.backings j) → BStable (M.backings j)
  own : ∀ j, BOwn (m.backings j) → BOwn (M.backings j)
  check : ∀ feat pkru acc x, M.check feat pkru acc x = m.check feat pkru acc x
  byte : ∀ x, StableAt m x → (∀ y, A y → locOf m y ≠ locOf m x) → M.readByte x = m.readByte x

namespace Calm
variable {A B : Addr → Prop} {m M M' : Memory}

theorem map (h : Calm A m M) : M.map = m.map := by
  simpa using congrArg Memory.map h.rest
theorem files (h : Calm A m M) : M.files = m.files := by
  simpa using congrArg Memory.files h.rest
theorem growsDown (h : Calm A m M) : M.growsDown = m.growsDown := by
  simpa using congrArg Memory.growsDown h.rest
theorem fresh (h : Calm A m M) : M.fresh = m.fresh := by
  simpa using congrArg Memory.fresh h.rest

theorem locOf_eq (h : Calm A m M) (x : Addr) : locOf M x = locOf m x := by simp [locOf, h.map]

theorem stableAt (h : Calm A m M) {x : Addr} (hx : StableAt m x) : StableAt M x := by
  intro mp hm; rw [h.map] at hm; exact h.stable _ (hx mp hm)

theorem ownAt (h : Calm A m M) {x : Addr} (hx : OwnAt m x) : OwnAt M x := by
  intro mp hm; rw [h.map] at hm; exact h.own _ (hx mp hm)

protected theorem refl (A : Addr → Prop) (m : Memory) : Calm A m m :=
  ⟨rfl, fun _ => refines_refl _ _, fun _ h => h, fun _ h => h, fun _ _ _ _ => rfl, fun _ _ _ => rfl⟩

theorem mono (h : Calm A m M) (hAB : ∀ y, A y → B y) : Calm B m M :=
  ⟨h.rest, h.refines, h.stable, h.own, h.check, fun x hx hy => h.byte x hx fun y hA => hy y (hAB y hA)⟩

theorem trans (h : Calm A m M) (k : Calm A M M') : Calm A m M' where
  rest := by
    have e1 := h.rest; have e2 := k.rest
    rw [← e1]; rw [← e2]
  refines j := refines_trans (h.refines j) (by rw [← h.files]; exact k.refines j)
  stable j hj := k.stable j (h.stable j hj)
  own j hj := k.own j (h.own j hj)
  check feat pkru acc x := by rw [k.check, h.check]
  byte x hx hy := by
    rw [k.byte x (h.stableAt hx) (by simpa [h.locOf_eq] using hy), h.byte x hx hy]

end Calm

/-! ## Changing one backing -/

/-- Whether every access to a page of backing `b` faults as not present: a file page wholly beyond the end of its file,
or a kernel page without a source (`Memory.check`). -/
def blocked (fs : Files) (b : Backing) : Bool :=
  match b.filePage with
  | some fp => fs.beyondEof fp
  | none => b.noSource

theorem check_eq (feat : Features) (pkru : BitVec 32) (m : Memory) (acc : Access) (x : Addr) :
    m.check feat pkru acc x =
      match m.map (pageOf x) with
      | none => some .notPresent
      | some mp => if blocked m.files (m.backings mp.backing) then some .notPresent
          else Memory.check.rest feat pkru acc mp := by
  unfold Memory.check
  rcases m.map (pageOf x) with _ | mp
  · rfl
  · simp only [blocked]
    generalize m.backings mp.backing = b
    rcases b with _ | (_ | _) | _ | _ | _ <;> rfl

/-- Replacing backing `b` by `nb` is calm if it keeps whether pages of it are present, stable and the process's own,
and the bytes that `Calm` must keep. -/
theorem setBacking_calm {A : Addr → Prop} {m : Memory} (b : Nat) (nb : Backing)
    (hrf : nb.Refines m.files (m.backings b)) (hst : BStable (m.backings b) → BStable nb) (hown : BOwn (m.backings b) → BOwn nb)
    (hbl : blocked m.files nb = blocked m.files (m.backings b))
    (hfr : ∀ x mx, m.map (pageOf x) = some mx → mx.backing = b → StableAt m x →
      (∀ y, A y → locOf m y ≠ locOf m x) → nb.frame m.files (pageOffset x) = (m.backings b).frame m.files (pageOffset x)) :
    Calm A m (m.setBacking b nb) where
  rest := rfl
  refines j := by
    by_cases e : j = b
    · subst e; simpa [Memory.setBacking] using hrf
    · simpa [Memory.setBacking, e] using refines_refl m.files (m.backings j)
  stable j hj := by
    by_cases e : j = b
    · subst e; simpa [Memory.setBacking] using hst hj
    · simpa [Memory.setBacking, e] using hj
  own j hj := by
    by_cases e : j = b
    · subst e; simpa [Memory.setBacking] using hown hj
    · simpa [Memory.setBacking, e] using hj
  check feat pkru acc x := by
    rw [check_eq, check_eq]
    show (match m.map (pageOf x) with
      | none => some AccessFault.notPresent
      | some mp => if blocked m.files ((m.setBacking b nb).backings mp.backing) then some AccessFault.notPresent
          else Memory.check.rest feat pkru acc mp) = _
    rcases m.map (pageOf x) with _ | mp
    · rfl
    · by_cases e : mp.backing = b
      · simp only [Memory.setBacking, e, ite_true, hbl]
      · simp only [Memory.setBacking, e, ite_false]
  byte x hx hy := by
    unfold Memory.readByte
    show (match m.map (pageOf x) with
      | none => 0
      | some mp => ((m.setBacking b nb).backings mp.backing).frame m.files (pageOffset x)) = _
    rcases hmx : m.map (pageOf x) with _ | mx
    · rfl
    · by_cases e : mx.backing = b
      · simp only [Memory.setBacking, e, ite_true]
        rw [← e]; exact e ▸ hfr x mx hmx e hx hy
      · simp only [Memory.setBacking, e, ite_false]

/-! ## One store -/

theorem writeByte_calm {feat : Features} {pkru : BitVec 32} {m : Memory} {a : Addr} (v : Byte)
    (hc : m.check feat pkru .write a = none) (ho : OwnAt m a) : Calm (· = a) m (m.writeByte a v) := by
  unfold Memory.writeByte
  rcases hma : m.map (pageOf a) with _ | ma
  · exact Calm.refl _ _
  · have hown := ho ma hma
    have hbl : blocked m.files (m.backings ma.backing) = false := by
      rw [check_eq, hma] at hc
      dsimp only at hc
      cases h : blocked m.files (m.backings ma.backing)
      · rfl
      · rw [h] at hc; simp at hc
    have hoff : ∀ x mx, m.map (pageOf x) = some mx → mx.backing = ma.backing →
        (∀ y, y = a → locOf m y ≠ locOf m x) → pageOffset x ≠ pageOffset a := by
      intro x mx hmx hbk hy heq
      apply hy a rfl
      simp [locOf, hma, hmx, hbk, heq]
    dsimp only
    rcases hbk : m.backings ma.backing with f | f | fp | fp | f <;> rw [hbk] at hown hbl <;>
      simp only [BOwn] at hown
    · refine setBacking_calm _ _ (by rw [hbk]; trivial) (fun _ => trivial) (fun _ => trivial) (by rw [hbk, hbl]; rfl) ?_
      intro x mx hmx hb _ hy
      rw [hbk]
      simp [Backing.frame, Frame.set, hoff x mx hmx hb hy]
    · refine setBacking_calm _ _ (by rw [hbk]; simpa [blocked, Backing.filePage, Backing.Refines] using hbl) (fun _ => trivial) (fun _ => trivial) (by rw [hbk, hbl]; rfl) ?_
      intro x mx hmx hb _ hy
      rw [hbk]
      simp [Backing.frame, Frame.set, hoff x mx hmx hb hy]

/-! ## Stores of the kernel -/

/-- Stores `l` (address, byte) in order (`f`, a fold step that stores), each into the process's own memory where it
may write. -/
theorem foldl_writeByte_calm {feat : Features} {pkru : BitVec 32} (f : Memory → Addr × Byte → Memory)
    (hf : ∀ m x b, f m (x, b) = m.writeByte x b) :
    ∀ (l : List (Addr × Byte)) (m : Memory), (∀ p ∈ l, m.check feat pkru .write p.1 = none ∧ OwnAt m p.1) →
      Calm (fun y => ∃ p ∈ l, p.1 = y) m (l.foldl f m)
  | [], m, _ => Calm.refl _ m
  | (x, b) :: l, m, h => by
    have hx := h (x, b) List.mem_cons_self
    have h1 : Calm (· = x) m (f m (x, b)) := by rw [hf]; exact writeByte_calm b hx.1 hx.2
    have h2 := foldl_writeByte_calm f hf l (f m (x, b)) fun q hq =>
      ⟨by rw [h1.check]; exact (h q (List.mem_cons_of_mem _ hq)).1, h1.ownAt (h q (List.mem_cons_of_mem _ hq)).2⟩
    simp only [List.foldl]
    exact (h1.mono fun y hy => ⟨(x, b), List.mem_cons_self, hy.symm⟩).trans
      (h2.mono fun y ⟨q, hq, e⟩ => ⟨q, List.mem_cons_of_mem _ hq, e⟩)

theorem writeBytes_calm {feat : Features} {pkru : BitVec 32} {m : Memory} {a : Addr} {bs : List Byte}
    (h : ∀ x ∈ byteAddrs a bs.length, m.check feat pkru .write x = none ∧ OwnAt m x) :
    Calm (· ∈ byteAddrs a bs.length) m (writeBytes m a bs) := by
  unfold writeBytes
  exact (foldl_writeByte_calm _ (fun _ _ _ => rfl) _ m fun p hp => h p.1 (List.of_mem_zip hp).1).mono
    fun y ⟨p, hp, e⟩ => e ▸ (List.of_mem_zip hp).1

theorem kernelWrite_calm {feat : Features} {s : State} {a : Addr} {bs : List Byte}
    (h : ∀ x ∈ byteAddrs a bs.length, x.canonical feat.la57 = true ∧
      s.proc.mm.mem.check feat s.cpu.pkru .write x = none ∧ OwnAt s.proc.mm.mem x) :
    kernelWrite feat s a bs = some (s.withMem (writeBytes s.proc.mm.mem a bs)) ∧
      Calm (· ∈ byteAddrs a bs.length) s.proc.mm.mem (writeBytes s.proc.mm.mem a bs) := by
  refine ⟨?_, writeBytes_calm fun x hx => ⟨(h x hx).2.1, (h x hx).2.2⟩⟩
  unfold kernelWrite
  rw [if_pos]
  simp only [List.all_eq_true, Bool.and_eq_true, Option.isNone_iff_eq_none]
  exact fun x hx => ⟨(h x hx).1, (h x hx).2.1⟩

private theorem rest_aux (a b c d e f : Bool)
    (h : (if (a && (b || c)) = true then some AccessFault.pkey
      else if (!e) = true then some AccessFault.protection else none) = none) :
    (if (a && b) = true then some AccessFault.pkey
      else if (!(d || e || f)) = true then some AccessFault.protection else none) = none := by
  revert h
  cases a <;> cases b <;> cases c <;> cases d <;> cases e <;> cases f <;> simp

theorem check_read_of_write {feat : Features} {pkru : BitVec 32} {m : Memory} {x : Addr}
    (h : m.check feat pkru .write x = none) : m.check feat pkru .read x = none := by
  rw [check_eq] at h ⊢
  rcases hm : m.map (pageOf x) with _ | mp <;> simp only [hm] at h ⊢
  · simp at h
  · by_cases hb : blocked m.files (m.backings mp.backing) = true
    · simp [hb] at h
    · simp only [hb] at h ⊢
      unfold Memory.check.rest at h ⊢
      simp only [pkeyDenies, Mapping.allows] at h ⊢
      simp only [Bool.false_eq_true, ite_false] at h ⊢
      exact rest_aux _ _ _ _ _ _ h

theorem addr_add_add (a : Addr) (i j : Nat) : (a.add i).add j = a.add (i + j) := by
  simp only [Addr.add, BitVec.add_assoc]
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp [Nat.add_mod]

theorem mem_byteAddrs {a x : Addr} {n : Nat} : x ∈ byteAddrs a n ↔ ∃ i < n, x = a.add i := by
  simp [byteAddrs, eq_comm]

/-! ## The `rseq` area -/

/-- The 32 bytes of `rseq` area `r` lie in the process's own memory, where the kernel may write them. -/
def AreaOk (feat : Features) (pkru : BitVec 32) (m : Memory) (r : RseqReg) : Prop :=
  ∀ j < 32, (r.area.add j).canonical feat.la57 = true ∧ m.check feat pkru .write (r.area.add j) = none ∧
    OwnAt m (r.area.add j)

/-- No `rseq` area, or one whose bytes lie in the process's own memory where the kernel may write them, at distinct
places, with no critical section (`rseq_cs`, the word at offset 8, is 0): the kernel's update at a return to user mode
then only stores the ids. -/
def AreaQuiet (feat : Features) (pkru : BitVec 32) (m : Memory) : Option RseqReg → Prop
  | none => True
  | some r => AreaOk feat pkru m r ∧
      (∀ j < 32, ∀ k < 32, j ≠ k → locOf m (r.area.add j) ≠ locOf m (r.area.add k)) ∧
      ofBytesLE 64 (readBytes m (r.area.add 8) 8) = 0

/-- The addresses of the ids the kernel stores into `rseq` area `R` (`rseqIds`): offsets 0–7 and 20–27. -/
def IdAddr : Option RseqReg → Addr → Prop
  | none, _ => False
  | some r, y => ∃ j, (j < 8 ∨ 20 ≤ j ∧ j < 28) ∧ y = r.area.add j

theorem AreaOk.of_calm {A : Addr → Prop} {feat : Features} {pkru : BitVec 32} {m M : Memory} {r : RseqReg}
    (hq : AreaOk feat pkru m r) (h : Calm A m M) : AreaOk feat pkru M r := fun j hj =>
  ⟨(hq j hj).1, by rw [h.check]; exact (hq j hj).2.1, h.ownAt (hq j hj).2.2⟩

theorem AreaQuiet.of_calm {feat : Features} {pkru : BitVec 32} {m M : Memory} {R : Option RseqReg}
    (hq : AreaQuiet feat pkru m R) (h : Calm (IdAddr R) m M) : AreaQuiet feat pkru M R := by
  cases R with
  | none => trivial
  | some r =>
    obtain ⟨hok, hd, hcs⟩ := hq
    refine ⟨hok.of_calm h, fun j hj k hk e => by simpa [h.locOf_eq] using hd j hj k hk e, ?_⟩
    rw [← hcs]
    congr 1
    unfold readBytes
    apply List.map_congr_left
    intro x hx
    obtain ⟨i, hi, rfl⟩ := mem_byteAddrs.1 hx
    rw [addr_add_add]
    apply h.byte _ ((hok (8 + i) (by omega)).2.2.stableAt)
    rintro y ⟨j, hj, rfl⟩
    exact hd j (by omega) (8 + i) (by omega) (by omega)

theorem withMem_self (s : State) : s.withMem s.proc.mm.mem = s := rfl
@[simp] theorem withMem_withMem (s : State) (M M' : Memory) : (s.withMem M).withMem M' = s.withMem M' := rfl
@[simp] theorem withMem_mem (s : State) (M : Memory) : (s.withMem M).proc.mm.mem = M := rfl
@[simp] theorem withMem_cpu (s : State) (M : Memory) : (s.withMem M).cpu = s.cpu := rfl
@[simp] theorem withMem_thread (s : State) (M : Memory) : (s.withMem M).thread = s.thread := rfl

/-- The kernel's stores of ids (`ws`: offset, value) into the area, as `rseqUpdate` folds them. -/
theorem idsFold_calm {feat : Features} {r : RseqReg} {f : Option State → Nat × BitVec 32 → Option State} :
    ∀ {ws : List (Nat × BitVec 32)} {s : State} {t : Option State}, ws.foldl f (some s) = t →
      (∀ acc o v, f acc (o, v) = acc.bind fun t => kernelWrite feat t (r.area.add o) (toBytesLE v 4)) →
      AreaOk feat s.cpu.pkru s.proc.mm.mem r → (∀ p ∈ ws, p.1 + 4 ≤ 32) →
      ∃ M, t = some (s.withMem M) ∧
        Calm (fun y => ∃ p ∈ ws, ∃ i < 4, y = r.area.add (p.1 + i)) s.proc.mm.mem M
  | [], s, t, ht, _, _, _ => ⟨s.proc.mm.mem, ht.symm, Calm.refl _ _⟩
  | (o, v) :: ws, s, t, ht, hf, hok, hw => by
    have ho : o + 4 ≤ 32 := hw (o, v) List.mem_cons_self
    obtain ⟨hk, c1⟩ := kernelWrite_calm (feat := feat) (s := s) (a := r.area.add o) (bs := toBytesLE v 4) (by
      intro x hx
      obtain ⟨i, hi, rfl⟩ := mem_byteAddrs.1 hx
      simp only [toBytesLE, List.length_map, List.length_range] at hi
      rw [addr_add_add]; exact hok (o + i) (by omega))
    simp only [List.foldl, hf, Option.bind_some, hk] at ht
    obtain ⟨M, rfl, c2⟩ := idsFold_calm ht hf (hok.of_calm c1) (fun p hp => hw p (List.mem_cons_of_mem _ hp))
    refine ⟨M, rfl, ?_⟩
    refine (c1.mono ?_).trans (c2.mono ?_)
    · intro y hy
      obtain ⟨i, hi, rfl⟩ := mem_byteAddrs.1 hy
      simp only [toBytesLE, List.length_map, List.length_range] at hi
      exact ⟨(o, v), List.mem_cons_self, i, hi, addr_add_add _ _ _⟩
    · rintro y ⟨p, hp, i, hi, rfl⟩
      exact ⟨p, List.mem_cons_of_mem _ hp, i, hi, rfl⟩

theorem rseqUpdate_quiet {feat : Features} {s : State} (cpu node mmCid : BitVec 32)
    (hq : AreaQuiet feat s.cpu.pkru s.proc.mm.mem s.thread.rseq) :
    ∃ M, rseqUpdate feat s cpu node mmCid = .ok (some (s.withMem M)) ∧
      Calm (IdAddr s.thread.rseq) s.proc.mm.mem M := by
  unfold rseqUpdate
  rcases hr : s.thread.rseq with _ | r
  · exact ⟨s.proc.mm.mem, rfl, Calm.refl _ _⟩
  · rw [hr] at hq
    obtain ⟨hok, -, hcs⟩ := hq
    have hrd : kernelRead feat s (r.area.add 8) 8 = some (readBytes s.proc.mm.mem (r.area.add 8) 8) := by
      unfold kernelRead kernelReadable
      rw [if_pos]
      simp only [List.all_eq_true, Bool.and_eq_true, Option.isNone_iff_eq_none]
      intro x hx
      obtain ⟨i, hi, rfl⟩ := mem_byteAddrs.1 hx
      rw [addr_add_add]
      exact ⟨(hok (8 + i) (by omega)).1, check_read_of_write (hok (8 + i) (by omega)).2.1⟩
    dsimp only
    rw [hrd]
    dsimp only
    rw [if_neg (by simpa using hcs)]
    split
    · next t ht =>
      obtain ⟨M, e, c⟩ := idsFold_calm ht (fun _ _ _ => rfl) hok (by simp)
      cases e
      refine ⟨M, rfl, c.mono ?_⟩
      rintro y ⟨p, hp, i, hi, rfl⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      refine ⟨p.1 + i, ?_, rfl⟩
      rcases hp with rfl | rfl | rfl | rfl <;> simp <;> omega
    · next ht =>
      obtain ⟨M, e, -⟩ := idsFold_calm ht (fun _ _ _ => rfl) hok (by simp)
      cases e

/-! ## The events of a step -/

theorem envEvent_quiet {feat : Features} {s : State} {e : EnvEvent}
    (hq : AreaQuiet feat s.cpu.pkru s.proc.mm.mem s.thread.rseq) (he : e.ordinary = true) :
    ∃ M, envEvent feat s e = .running (s.withMem M) none ∧ Calm (IdAddr s.thread.rseq) s.proc.mm.mem M := by
  cases e with
  | kernelEntry cpu node mmCid =>
    obtain ⟨M, h, c⟩ := rseqUpdate_quiet cpu node mmCid hq
    exact ⟨M, by simp [envEvent, kernelEntry, h], c⟩
  | kernelData b f =>
    simp only [envEvent]
    split
    · next g hb =>
      refine ⟨_, rfl, setBacking_calm _ _ (by simp [hb, Backing.Refines]) (by simp [hb, BStable]) (by simp [hb, BOwn]) (by simp [hb, blocked,
        Backing.filePage, Backing.noSource]) ?_⟩
      intro x mx hmx he hx _
      have := hx mx hmx; rw [he, hb] at this; exact this.elim
    · exact ⟨_, rfl, Calm.refl _ _⟩
  | reclaim b =>
    simp only [envEvent]
    split
    · next g hb =>
      refine ⟨_, rfl, setBacking_calm _ _ (by simp [hb, Backing.Refines]) (by simp [hb, BStable]) (by simp [hb, BOwn]) (by simp [hb, blocked,
        Backing.filePage, Backing.noSource]) ?_⟩
      intro x mx hmx he hx _
      have := hx mx hmx; rw [he, hb] at this; exact this.elim
    · exact ⟨_, rfl, Calm.refl _ _⟩
  | _ => simp [EnvEvent.ordinary] at he

/-- The state an event that keeps the run going leaves. -/
def kd1 (feat : Features) (s : State) (e : EnvEvent) : State :=
  match envEvent feat s e with
  | .running s' _ => s'
  | _ => s

/-- The state ordinary events `evs` leave, applied in order as `envEvents` does. -/
def kdata (feat : Features) : State → List EnvEvent → State
  | s, [] => s
  | s, e :: es => kdata feat (kd1 feat s e) es

/-- The `rseq` area of the thread in `s` is quiet (`AreaQuiet`). -/
abbrev Quiet (feat : Features) (s : State) : Prop := AreaQuiet feat s.cpu.pkru s.proc.mm.mem s.thread.rseq

theorem envEvents_quiet (feat : Features) : ∀ (evs : List EnvEvent) (s : State), Quiet feat s →
    (∀ e ∈ evs, e.ordinary = true) →
    envEvents feat s evs = .running (kdata feat s evs) none ∧
      ∃ M, kdata feat s evs = s.withMem M ∧ Calm (IdAddr s.thread.rseq) s.proc.mm.mem M
  | [], s, _, _ => ⟨rfl, s.proc.mm.mem, rfl, Calm.refl _ _⟩
  | e :: es, s, hq, ho => by
    obtain ⟨M1, h1, c1⟩ := envEvent_quiet hq (ho e List.mem_cons_self)
    have hq1 : Quiet feat (s.withMem M1) := AreaQuiet.of_calm hq c1
    obtain ⟨h2, M, h3, c2⟩ := envEvents_quiet feat es (s.withMem M1) hq1 fun e he => ho e (List.mem_cons_of_mem _ he)
    have hk : kd1 feat s e = s.withMem M1 := by simp [kd1, h1]
    refine ⟨?_, M, ?_, c1.trans c2⟩
    · simp only [envEvents, h1, kdata, hk]; exact h2
    · simp only [kdata, hk]; exact h3

/-- After ordinary events the `rseq` area is still quiet. -/
theorem Quiet.kdata {feat : Features} {s : State} {evs : List EnvEvent} (hq : Quiet feat s)
    (ho : ∀ e ∈ evs, e.ordinary = true) : Quiet feat (kdata feat s evs) := by
  obtain ⟨-, M, h, c⟩ := envEvents_quiet feat evs s hq ho
  rw [h]; exact AreaQuiet.of_calm hq c

/-- The events between two instructions at position `t` of the answers. -/
def evsAt (prof : Profile) (o : Oracle) (t : Nat) : List EnvEvent := (o t (.between prof.cpus)).val

/-- One step of an undisturbed run from a state whose `rseq` area is quiet: the instruction, from the state the
kernel's ordinary events leave. -/
theorem step_runStream (prof : Profile) (o : Oracle) (t : Nat) (s : State) (hU : Undisturbed o)
    (hq : Quiet prof.feat s) :
    (step prof s).runStream o t = (instruction prof (kdata prof.feat s (evsAt prof o t))).runStream o (t + 1) := by
  have h := (envEvents_quiet prof.feat (evsAt prof o t) s hq fun e he => hU t prof.cpus e he).1
  simp only [step, Req.request, bind, Req.bind, Req.runStream]
  unfold evsAt at h
  rw [h]
  rfl

end FV7z
