import FV7z.Lemmas.FnReg
/-!
# A stretch of straight-line code in one step (PLAN.md G2, pilot `LzmaDec_DecodeReal_3`)

`FnSteps.lean` takes a step lemma, with its side conditions and a continuation, for each instruction. Here a stretch
of instructions is one list of effects (`Op`): on the registers and flags alone (`reg`), with a load (`load`) or a
store (`store`) of bytes of the footprint. `Blk prof code j j' ops`: the code from its `j`-th byte to its `j'`-th
decodes to instructions with the effects `ops`. `Seg.s_blk` runs the stretch: what is left to prove is `wp`, the
accesses' side conditions and the continuation on the registers, flags and bytes the effects compute, which `simp`
unfolds.

The flags an instruction leaves are a set (`P`), not a function: the model leaves the flags the manuals call
undefined open, and a proof seldom follows the others.

`Blk.shift`: a stretch of a pattern of bytes is a stretch of any code holding these bytes, so a proof about a pattern
(the range coder's normalization, the decoding of a bit) is written once.
-/
namespace FV7z
open ZellicX86 Decode

/-- The flags `f` with `RF` cleared, as after an instruction. -/
abbrev rfz (f : Rflags) : Rflags := { f with rf := false }

/-- What an instruction does, the state's registers `g` and flags `f` given. -/
inductive Op where
  /-- New registers `h g f`, and flags of which `P g f` holds. -/
  | reg (h : Gprs → Rflags → Gprs) (P : Gprs → Rflags → Rflags → Prop)
  /-- A load of `n` bytes `bs` at `ea g`: new registers `h g f bs`, and flags of which `P g f bs` holds. -/
  | load (n : Nat) (ea : Gprs → Addr) (h : Gprs → Rflags → List Byte → Gprs)
      (P : Gprs → Rflags → List Byte → Rflags → Prop)
  /-- A store of the `n` bytes `val g` at `ea g`; new registers `h g`, the flags kept. -/
  | store (n : Nat) (ea : Gprs → Addr) (val : Gprs → List Byte) (h : Gprs → Gprs)
  /-- A load of `n` bytes at `ea g` into a vector register: the registers and flags kept, the vector registers
  any. -/
  | vld (n : Nat) (ea : Gprs → Addr)
  /-- A store of `n` bytes from a vector register at `ea g`, whatever they are; the registers and flags kept. -/
  | vst (n : Nat) (ea : Gprs → Addr)

/-- The effect keeps the vector registers. -/
def Op.kv : Op → Bool
  | .vld _ _ => false
  | _ => true

/-- The instruction `i` does `op`. -/
def OpI (prof : Profile) (i : Inst) : Op → Prop
  | .reg h P => ∀ (s : State) (o : Oracle) (t : Nat), s.cpu.rflags.tf = false →
      Decode.decode prof.feat (fetchByte prof.feat s) = .ok i →
      ∃ fl t', (instruction prof s).runStream o t =
          (.running (nx s i.len (h s.cpu.gpr s.cpu.rflags) fl) none, t') ∧
        P s.cpu.gpr s.cpu.rflags fl ∧ fl.tf = s.cpu.rflags.tf ∧ fl.ac = s.cpu.rflags.ac ∧ fl.df = s.cpu.rflags.df
  | .load n ea h P => ∀ (s : State) (o : Oracle) (t : Nat), s.cpu.rflags.tf = false → s.cpu.rflags.ac = false →
      Decode.decode prof.feat (fetchByte prof.feat s) = .ok i → Readable prof s (ea s.cpu.gpr) n →
      ∃ fl t', (instruction prof s).runStream o t =
          (.running (nx s i.len (h s.cpu.gpr s.cpu.rflags (readBytes s.proc.mm.mem (ea s.cpu.gpr) n)) fl) none, t') ∧
        P s.cpu.gpr s.cpu.rflags (readBytes s.proc.mm.mem (ea s.cpu.gpr) n) fl ∧
        fl.tf = s.cpu.rflags.tf ∧ fl.ac = s.cpu.rflags.ac ∧ fl.df = s.cpu.rflags.df
  | .store n ea val h => ∀ (s : State) (o : Oracle) (t : Nat), s.cpu.rflags.tf = false → s.cpu.rflags.ac = false →
      Decode.decode prof.feat (fetchByte prof.feat s) = .ok i → (val s.cpu.gpr).length = n →
      Writable prof s (ea s.cpu.gpr) n →
      ∃ t', (instruction prof s).runStream o t =
        (.running (nx (st s (ea s.cpu.gpr) (val s.cpu.gpr)) i.len (h s.cpu.gpr) (rf0 s)) none, t')
  | .vld n ea => ∀ (s : State) (o : Oracle) (t : Nat), s.cpu.rflags.tf = false →
      s.cpu.rflags.ac = false →
      Decode.decode prof.feat (fetchByte prof.feat s) = .ok i → Readable prof s (ea s.cpu.gpr) n →
      ∃ z t', (instruction prof s).runStream o t = (.running (nxz s i.len s.cpu.gpr (rf0 s) z) none, t')
  | .vst n ea => ∀ (s : State) (o : Oracle) (t : Nat), s.cpu.rflags.tf = false →
      s.cpu.rflags.ac = false →
      Decode.decode prof.feat (fetchByte prof.feat s) = .ok i → Writable prof s (ea s.cpu.gpr) n →
      ∃ bs t', bs.length = n ∧ (instruction prof s).runStream o t =
        (.running (nx (st s (ea s.cpu.gpr) bs) i.len s.cpu.gpr (rf0 s)) none, t')

/-- The code from its `j`-th byte to its `j'`-th: instructions doing `ops`. -/
inductive Blk (prof : Profile) (code : List Byte) : Nat → Nat → List Op → Prop
  | nil (j : Nat) : Blk prof code j j []
  | cons {j j' : Nat} {i : Inst} {op : Op} {ops : List Op} : Leaf.Dec prof.feat code j i → OpI prof i op →
      j < code.length → Blk prof code (j + i.len) j' ops → Blk prof code j j' (op :: ops)

/-- The instruction `i` at the address `x` does `op`: an instruction with an operand `[rip + d]` reads or writes at an
address that the code's place gives. -/
def OpIA (prof : Profile) (x : Addr) (i : Inst) : Op → Prop
  | .reg h P => ∀ (s : State) (o : Oracle) (t : Nat), s.cpu.rip = x → s.cpu.rflags.tf = false →
      Decode.decode prof.feat (fetchByte prof.feat s) = .ok i →
      ∃ fl t', (instruction prof s).runStream o t =
          (.running (nx s i.len (h s.cpu.gpr s.cpu.rflags) fl) none, t') ∧
        P s.cpu.gpr s.cpu.rflags fl ∧ fl.tf = s.cpu.rflags.tf ∧ fl.ac = s.cpu.rflags.ac ∧ fl.df = s.cpu.rflags.df
  | .load n ea h P => ∀ (s : State) (o : Oracle) (t : Nat), s.cpu.rip = x → s.cpu.rflags.tf = false →
      s.cpu.rflags.ac = false →
      Decode.decode prof.feat (fetchByte prof.feat s) = .ok i → Readable prof s (ea s.cpu.gpr) n →
      ∃ fl t', (instruction prof s).runStream o t =
          (.running (nx s i.len (h s.cpu.gpr s.cpu.rflags (readBytes s.proc.mm.mem (ea s.cpu.gpr) n)) fl) none, t') ∧
        P s.cpu.gpr s.cpu.rflags (readBytes s.proc.mm.mem (ea s.cpu.gpr) n) fl ∧
        fl.tf = s.cpu.rflags.tf ∧ fl.ac = s.cpu.rflags.ac ∧ fl.df = s.cpu.rflags.df
  | .store n ea val h => ∀ (s : State) (o : Oracle) (t : Nat), s.cpu.rip = x → s.cpu.rflags.tf = false →
      s.cpu.rflags.ac = false →
      Decode.decode prof.feat (fetchByte prof.feat s) = .ok i → (val s.cpu.gpr).length = n →
      Writable prof s (ea s.cpu.gpr) n →
      ∃ t', (instruction prof s).runStream o t =
        (.running (nx (st s (ea s.cpu.gpr) (val s.cpu.gpr)) i.len (h s.cpu.gpr) (rf0 s)) none, t')
  | .vld n ea => ∀ (s : State) (o : Oracle) (t : Nat), s.cpu.rip = x → s.cpu.rflags.tf = false →
      s.cpu.rflags.ac = false →
      Decode.decode prof.feat (fetchByte prof.feat s) = .ok i → Readable prof s (ea s.cpu.gpr) n →
      ∃ z t', (instruction prof s).runStream o t = (.running (nxz s i.len s.cpu.gpr (rf0 s) z) none, t')
  | .vst n ea => ∀ (s : State) (o : Oracle) (t : Nat), s.cpu.rip = x → s.cpu.rflags.tf = false →
      s.cpu.rflags.ac = false →
      Decode.decode prof.feat (fetchByte prof.feat s) = .ok i → Writable prof s (ea s.cpu.gpr) n →
      ∃ bs t', bs.length = n ∧ (instruction prof s).runStream o t =
        (.running (nx (st s (ea s.cpu.gpr) bs) i.len s.cpu.gpr (rf0 s)) none, t')

/-- What an instruction does wherever it lies, it does at `x`. -/
theorem OpI.at {prof : Profile} {i : Inst} (x : Addr) : ∀ {op : Op}, OpI prof i op → OpIA prof x i op
  | .reg _ _, h => fun s o t _ => h s o t
  | .load _ _ _ _, h => fun s o t _ => h s o t
  | .store _ _ _ _, h => fun s o t _ => h s o t
  | .vld _ _, h => fun s o t _ => h s o t
  | .vst _ _, h => fun s o t _ => h s o t

/-- The code at `e'`, from its `j`-th byte to its `j'`-th: instructions doing `ops` there. -/
inductive BlkA (prof : Profile) (code : List Byte) (e' : Addr) : Nat → Nat → List Op → Prop
  | nil (j : Nat) : BlkA prof code e' j j []
  | cons {j j' : Nat} {i : Inst} {op : Op} {ops : List Op} : Leaf.Dec prof.feat code j i →
      OpIA prof (e'.add j) i op → j < code.length → BlkA prof code e' (j + i.len) j' ops →
      BlkA prof code e' j j' (op :: ops)

/-- A stretch of code is one wherever the code lies. -/
theorem Blk.at {prof : Profile} {code : List Byte} (e' : Addr) {j j' : Nat} {ops : List Op}
    (h : Blk prof code j j' ops) : BlkA prof code e' j j' ops := by
  induction h with
  | nil j => exact .nil _
  | cons hd ho hj _ ih => exact .cons hd (ho.at _) hj ih

/-- What running `ops` from registers `g`, flags `f` and the footprint's bytes `V` needs for `Q` to hold of what it
leaves: every load in the footprint's data, every store in what the run may store into (`Wl`). -/
def wp (F : Footprint) (Wl : List Rgn) : List Op → (Gprs → Rflags → (Addr → Byte) → Prop) →
    Gprs → Rflags → (Addr → Byte) → Prop
  | [], Q, g, f, V => Q g f V
  | .reg h P :: ops, Q, g, f, V => ∀ fl, P g f fl → wp F Wl ops Q (h g f) fl V
  | .load n ea h P :: ops, Q, g, f, V => (∀ i < n, Foot F.data ((ea g).add i)) ∧
      ∀ fl, P g f ((byteAddrs (ea g) n).map V) fl → wp F Wl ops Q (h g f ((byteAddrs (ea g) n).map V)) fl V
  | .store n ea val h :: ops, Q, g, f, V => (val g).length = n ∧ (∀ i < n, Foot Wl ((ea g).add i)) ∧
      wp F Wl ops Q (h g) (rfz f) (Vst V (ea g) (val g))
  | .vld n ea :: ops, Q, g, f, V => (∀ i < n, Foot F.data ((ea g).add i)) ∧ wp F Wl ops Q g (rfz f) V
  | .vst n ea :: ops, Q, g, f, V => (∀ i < n, Foot Wl ((ea g).add i)) ∧
      ∀ bs : List Byte, bs.length = n → wp F Wl ops Q g (rfz f) (Vst V (ea g) bs)

theorem wp_mono {F : Footprint} {Wl : List Rgn} : ∀ (ops : List Op) {Q Q' : Gprs → Rflags → (Addr → Byte) → Prop}
    {g : Gprs} {f : Rflags} {V : Addr → Byte}, (∀ g f V, Q g f V → Q' g f V) → wp F Wl ops Q g f V →
    wp F Wl ops Q' g f V
  | [], _, _, _, _, _, hq, h => hq _ _ _ h
  | .reg _ _ :: ops, _, _, _, _, _, hq, h => fun fl hp => wp_mono ops hq (h fl hp)
  | .load _ _ _ _ :: ops, _, _, _, _, _, hq, h => ⟨h.1, fun fl hp => wp_mono ops hq (h.2 fl hp)⟩
  | .store _ _ _ _ :: ops, _, _, _, _, _, hq, h => ⟨h.1, h.2.1, wp_mono ops hq h.2.2⟩
  | .vld _ _ :: ops, _, _, _, _, _, hq, h => ⟨h.1, wp_mono ops hq h.2⟩
  | .vst _ _ :: ops, _, _, _, _, _, hq, h => ⟨h.1, fun bs hb => wp_mono ops hq (h.2 bs hb)⟩

/-- Two stretches, one after the other. -/
theorem Blk.append {prof : Profile} {code : List Byte} {j j' j'' : Nat} {ops ops' : List Op}
    (h : Blk prof code j j' ops) (h' : Blk prof code j' j'' ops') : Blk prof code j j'' (ops ++ ops') := by
  induction h with
  | nil j => exact h'
  | cons hd ho hj _ ih => exact .cons hd ho hj (ih h')

theorem wp_append {F : Footprint} {Wl : List Rgn} : ∀ (ops ops' : List Op)
    {Q : Gprs → Rflags → (Addr → Byte) → Prop} {g : Gprs} {f : Rflags} {V : Addr → Byte},
    wp F Wl ops (wp F Wl ops' Q) g f V → wp F Wl (ops ++ ops') Q g f V
  | [], _, _, _, _, _, h => h
  | .reg _ _ :: ops, ops', _, _, _, _, h => fun fl hp => wp_append ops ops' (h fl hp)
  | .load _ _ _ _ :: ops, ops', _, _, _, _, h => ⟨h.1, fun fl hp => wp_append ops ops' (h.2 fl hp)⟩
  | .store _ _ _ _ :: ops, ops', _, _, _, _, h => ⟨h.1, h.2.1, wp_append ops ops' h.2.2⟩
  | .vld _ _ :: ops, ops', _, _, _, _, h => ⟨h.1, wp_append ops ops' h.2⟩
  | .vst _ _ :: ops, ops', _, _, _, _, h => ⟨h.1, fun bs hb => wp_append ops ops' (h.2 bs hb)⟩

/-! ## A pattern of bytes in a code -/

/-- Decoding in a code that holds the bytes of `pat` from its `j`-th byte. -/
theorem Dec.shift {feat : Features} {pat code : List Byte} {j k : Nat} {i : Inst} (hd : Leaf.Dec feat pat k i)
    (hw : pat <+: code.drop j) (hk : k ≤ pat.length) : Leaf.Dec feat code (j + k) i := by
  intro f
  obtain ⟨rest, hr⟩ := hw
  have e : code.drop (j + k) = pat.drop k ++ rest := by
    rw [← List.drop_drop, ← hr, List.drop_append_of_le_length hk]
  rw [e]
  have := hd (fetchFrom (pat.drop k ++ rest) f)
  rwa [fetchFrom_eq (fun i hi => by
    unfold fetchFrom
    rw [ite_eq_left (by rw [List.length_append]; omega), List.getElem?_append_left hi])] at this

theorem length_of_prefix {pat code : List Byte} {j : Nat} (hw : pat <+: code.drop j) :
    j + pat.length ≤ code.length ∨ pat.length = 0 := by
  obtain ⟨rest, hr⟩ := hw
  have := congrArg List.length hr
  rw [List.length_append, List.length_drop] at this
  omega

/-- A stretch of a pattern is a stretch of a code holding it. -/
theorem Blk.shift {prof : Profile} {pat code : List Byte} {j k k' : Nat} {ops : List Op}
    (h : Blk prof pat k k' ops) (hw : pat <+: code.drop j) : Blk prof code (j + k) (j + k') ops := by
  induction h with
  | nil k => exact .nil _
  | cons hd ho hk _ ih =>
    refine .cons (Dec.shift hd hw (Nat.le_of_lt hk)) ho ?_ (by rw [Nat.add_assoc]; exact ih)
    rcases length_of_prefix hw with h | h <;> omega

theorem BlkA.append {prof : Profile} {code : List Byte} {e' : Addr} {j j' j'' : Nat} {ops ops' : List Op}
    (h : BlkA prof code e' j j' ops) (h' : BlkA prof code e' j' j'' ops') : BlkA prof code e' j j'' (ops ++ ops') := by
  induction h with
  | nil j => exact h'
  | cons hd ho hj _ ih => exact .cons hd ho hj (ih h')

theorem addr_add_add' (a : Addr) (i j : Nat) : (a.add i).add j = a.add (i + j) := by
  simp only [Addr.add, BitVec.add_assoc, BitVec.ofNat_add]

/-- A stretch of a pattern at `b` is a stretch of a code that holds the pattern there. -/
theorem BlkA.shift {prof : Profile} {pat code : List Byte} {b e' : Addr} {j k k' : Nat} {ops : List Op}
    (h : BlkA prof pat b k k' ops) (hb : b = e'.add j) (hw : pat <+: code.drop j) :
    BlkA prof code e' (j + k) (j + k') ops := by
  subst hb
  induction h with
  | nil k => exact .nil _
  | cons hd ho hk _ ih =>
    refine .cons (Dec.shift hd hw (Nat.le_of_lt hk)) (by rw [← addr_add_add']; exact ho) ?_
      (by rw [Nat.add_assoc]; exact ih)
    rcases length_of_prefix hw with h | h <;> omega

end FV7z

namespace FV7z.Fn
open ZellicX86 Decode FV7z.Leaf

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle} {F : Footprint} {Wl : List Rgn}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {e' : Addr} {code : List Byte}

namespace Seg

/-- A stretch of straight-line code, at the code's place. -/
theorem s_blkA (c : Seg prof F Wl L s₀ o) (hin : CodeIn L e' code) {j j' : Nat} {ops : List Op}
    (hb : BlkA prof code e' j j' ops) :
    ∀ {X : State} {t : Nat} {V : Addr → Byte}, KeptW Wl s₀ X → Agree F X.proc.mm.mem V → X.cpu.rip = e'.add j →
      wp F Wl ops (fun g fl V' => ∀ Y t', KeptW Wl s₀ Y → Agree F Y.proc.mm.mem V' → Y.cpu.rip = e'.add j' →
        Y.cpu.gpr = g → Y.cpu.rflags = fl → GoG prof L o gev gP gE Y t') X.cpu.gpr X.cpu.rflags V →
      GoG prof L o gev gP gE X t := by
  induction hb with
  | nil j => intro X t V hK hA hrip h; exact h X t hK hA hrip rfl rfl
  | @cons j j' i op ops hd ho hj _ ih =>
    intro X t V hK hA hrip h
    cases op with
    | reg hh P =>
      refine c.next (V' := V) (Pr := fun Y => Y.cpu.rip = e'.add (j + i.len) ∧
        P X.cpu.gpr X.cpu.rflags Y.cpu.rflags ∧ Y.cpu.gpr = hh X.cpu.gpr X.cpu.rflags) hK hA hin hj hrip
        (fun M hK' hA' htf _ => ?_) ?_
      · obtain ⟨fl, t', hr, hp, h1, h2, h3⟩ := ho (X.withMem M) o (t + 1) hrip htf (c.dec hK' hin hrip hd)
        exact ⟨_, _, hr, hK'.nx h1 h2 h3, hA', rip_add hrip M i.len, hp, rfl⟩
      · rintro Y t' hKY hAY ⟨hrY, hpY, hgY⟩
        exact ih hKY hAY hrY (by rw [hgY]; exact h _ hpY)
    | load n ea hh P =>
      obtain ⟨hl, h⟩ := h
      refine c.next (V' := V) (Pr := fun Y => Y.cpu.rip = e'.add (j + i.len) ∧
        P X.cpu.gpr X.cpu.rflags ((byteAddrs (ea X.cpu.gpr) n).map V) Y.cpu.rflags ∧
        Y.cpu.gpr = hh X.cpu.gpr X.cpu.rflags ((byteAddrs (ea X.cpu.gpr) n).map V)) hK hA hin hj hrip
        (fun M hK' hA' htf hac => ?_) ?_
      · obtain ⟨hrd, hv⟩ := c.load_ok (X := X.withMem M) hK' hA' hl
        obtain ⟨fl, t', hr, hp, h1, h2, h3⟩ := ho (X.withMem M) o (t + 1) hrip htf hac (c.dec hK' hin hrip hd) hrd
        refine ⟨_, _, hr, hK'.nx h1 h2 h3, hA', rip_add hrip M i.len, ?_, ?_⟩
        · rw [← hv]; exact hp
        · rw [← hv]; rfl
      · rintro Y t' hKY hAY ⟨hrY, hpY, hgY⟩
        exact ih hKY hAY hrY (by rw [hgY]; exact h _ hpY)
    | store n ea val hh =>
      obtain ⟨hlen, hst, h⟩ := h
      refine c.next (V' := Vst V (ea X.cpu.gpr) (val X.cpu.gpr)) (Pr := fun Y => Y.cpu.rip = e'.add (j + i.len) ∧
        Y.cpu.rflags = rfz X.cpu.rflags ∧ Y.cpu.gpr = hh X.cpu.gpr) hK hA hin hj hrip
        (fun M hK' hA' htf hac => ?_) ?_
      · obtain ⟨hwr, hKs, hAs⟩ := c.store_ok (X := X.withMem M) hK' hA'
          (bs := val X.cpu.gpr) (a := ea X.cpu.gpr) (by rw [hlen]; exact hst)
        rw [hlen] at hwr
        obtain ⟨t', hr⟩ := ho (X.withMem M) o (t + 1) hrip htf hac (c.dec hK' hin hrip hd) hlen hwr
        exact ⟨_, _, hr, hKs.nx rfl rfl rfl, hAs, rip_add hrip M i.len, rfl, rfl⟩
      · rintro Y t' hKY hAY ⟨hrY, hfY, hgY⟩
        exact ih hKY hAY hrY (by rw [hgY, hfY]; exact h)
    | vld n ea =>
      obtain ⟨hl, h⟩ := h
      refine c.next (V' := V) (Pr := fun Y => Y.cpu.rip = e'.add (j + i.len) ∧
        Y.cpu.rflags = rfz X.cpu.rflags ∧ Y.cpu.gpr = X.cpu.gpr) hK hA hin hj hrip
        (fun M hK' hA' htf hac => ?_) ?_
      · obtain ⟨hrd, -⟩ := c.load_ok (X := X.withMem M) hK' hA' hl
        obtain ⟨z, t', hr⟩ := ho (X.withMem M) o (t + 1) hrip htf hac (c.dec hK' hin hrip hd) hrd
        exact ⟨_, _, hr, hK'.modCpu rfl rfl rfl rfl rfl rfl rfl, hA', rip_add hrip M i.len, rfl, rfl⟩
      · rintro Y t' hKY hAY ⟨hrY, hfY, hgY⟩
        exact ih hKY hAY hrY (by rw [hgY, hfY]; exact h)
    | vst n ea =>
      obtain ⟨hst, h⟩ := h
      refine c.step hK hin hj hrip fun M hM hK' htf hac => ?_
      have hA' := c.agreeK hK hA hM
      obtain ⟨hwr, -, -⟩ := c.store_ok (X := X.withMem M) hK' hA' (bs := List.replicate n 0) (a := ea X.cpu.gpr)
        (by rw [List.length_replicate]; exact hst)
      rw [List.length_replicate] at hwr
      obtain ⟨bs, t', hlen, hr⟩ := ho (X.withMem M) o (t + 1) hrip htf hac (c.dec hK' hin hrip hd) hwr
      obtain ⟨-, hKs, hAs⟩ := c.store_ok (X := X.withMem M) hK' hA' (bs := bs) (a := ea X.cpu.gpr)
        (by rw [hlen]; exact hst)
      exact ⟨_, _, hr, ih (hKs.nx rfl rfl rfl) hAs (rip_add hrip M i.len) (h bs hlen)⟩

/-- A stretch of straight-line code. -/
theorem s_blk (c : Seg prof F Wl L s₀ o) (hin : CodeIn L e' code) {j j' : Nat} {ops : List Op}
    (hb : Blk prof code j j' ops) :
    ∀ {X : State} {t : Nat} {V : Addr → Byte}, KeptW Wl s₀ X → Agree F X.proc.mm.mem V → X.cpu.rip = e'.add j →
      wp F Wl ops (fun g fl V' => ∀ Y t', KeptW Wl s₀ Y → Agree F Y.proc.mm.mem V' → Y.cpu.rip = e'.add j' →
        Y.cpu.gpr = g → Y.cpu.rflags = fl → GoG prof L o gev gP gE Y t') X.cpu.gpr X.cpu.rflags V →
      GoG prof L o gev gP gE X t :=
  c.s_blkA hin (hb.at e')

end Seg

end FV7z.Fn
