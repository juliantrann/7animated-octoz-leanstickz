import FV7z.Lemmas.SpCall
import FV7z.Lemmas.Wp
/-!
# Code that reads and stores through `fs` (PLAN.md G3, startup)

An instruction with an operand `fs:[…]` reads or stores at the `fs` base plus the operand's address: the thread
control block (`fs:0x28` the stack guard, `fs:0x30` the pointer guard, `errno` and the like at `fs:(reg)`). A run
keeps its `fs` base (`KeptW.seg`), so in a run whose start has the base `fb` such an instruction is an `Op` like any
other, at `fb + …`.

- `OpIF prof x fb i op`, `BlkF prof code e' fb j j' ops`: as `OpIA` and `BlkA`, for states with the `fs` base `fb`.
  `OpIA.fs`, `BlkA.fs`: what holds whatever the base holds with it.
- `Op.ldf`, `Op.stf`: `mov r, fs:[m]` and `mov fs:[m], r`, with `OpIF.ldf`, `OpIF.stf`; `Op.xor8`: `xor r8, x`.
- `Seg.s_blkF`: a stretch runs, in a run whose start has the `fs` base `fb`.
- `SpF prof code e' fb j W`: `Sp` for runs whose start has the `fs` base `fb`, with `Sp`'s rules (`Sp.fs`, `blk`,
  `blkA`, `blkF`, `…_then`, `jmp_then`, `jcc_then`, `table`), and `SpF.at`: its `SpAt` in such a run.
-/
namespace FV7z
open ZellicX86 Decode FV7z.Leaf

/-- The instruction `i` at the address `x` does `op`, in a state with the `fs` base `fb`. -/
def OpIF (prof : Profile) (x fb : Addr) (i : Inst) : Op → Prop
  | .reg h P => ∀ (s : State) (o : Oracle) (t : Nat), s.cpu.rip = x → s.cpu.seg.fsBase = fb →
      s.cpu.rflags.tf = false → Decode.decode prof.feat (fetchByte prof.feat s) = .ok i →
      ∃ fl t', (instruction prof s).runStream o t =
          (.running (nx s i.len (h s.cpu.gpr s.cpu.rflags) fl) none, t') ∧
        P s.cpu.gpr s.cpu.rflags fl ∧ fl.tf = s.cpu.rflags.tf ∧ fl.ac = s.cpu.rflags.ac ∧ fl.df = s.cpu.rflags.df
  | .load n ea h P => ∀ (s : State) (o : Oracle) (t : Nat), s.cpu.rip = x → s.cpu.seg.fsBase = fb →
      s.cpu.rflags.tf = false → s.cpu.rflags.ac = false →
      Decode.decode prof.feat (fetchByte prof.feat s) = .ok i → Readable prof s (ea s.cpu.gpr) n →
      ∃ fl t', (instruction prof s).runStream o t =
          (.running (nx s i.len (h s.cpu.gpr s.cpu.rflags (readBytes s.proc.mm.mem (ea s.cpu.gpr) n)) fl) none, t') ∧
        P s.cpu.gpr s.cpu.rflags (readBytes s.proc.mm.mem (ea s.cpu.gpr) n) fl ∧
        fl.tf = s.cpu.rflags.tf ∧ fl.ac = s.cpu.rflags.ac ∧ fl.df = s.cpu.rflags.df
  | .store n ea val h => ∀ (s : State) (o : Oracle) (t : Nat), s.cpu.rip = x → s.cpu.seg.fsBase = fb →
      s.cpu.rflags.tf = false → s.cpu.rflags.ac = false →
      Decode.decode prof.feat (fetchByte prof.feat s) = .ok i → (val s.cpu.gpr).length = n →
      Writable prof s (ea s.cpu.gpr) n →
      ∃ t', (instruction prof s).runStream o t =
        (.running (nx (st s (ea s.cpu.gpr) (val s.cpu.gpr)) i.len (h s.cpu.gpr) (rf0 s)) none, t')
  | .vld n ea => ∀ (s : State) (o : Oracle) (t : Nat), s.cpu.rip = x → s.cpu.seg.fsBase = fb →
      s.cpu.rflags.tf = false → s.cpu.rflags.ac = false →
      Decode.decode prof.feat (fetchByte prof.feat s) = .ok i → Readable prof s (ea s.cpu.gpr) n →
      ∃ z t', (instruction prof s).runStream o t = (.running (nxz s i.len s.cpu.gpr (rf0 s) z) none, t')
  | .vst n ea => ∀ (s : State) (o : Oracle) (t : Nat), s.cpu.rip = x → s.cpu.seg.fsBase = fb →
      s.cpu.rflags.tf = false → s.cpu.rflags.ac = false →
      Decode.decode prof.feat (fetchByte prof.feat s) = .ok i → Writable prof s (ea s.cpu.gpr) n →
      ∃ bs t', bs.length = n ∧ (instruction prof s).runStream o t =
        (.running (nx (st s (ea s.cpu.gpr) bs) i.len s.cpu.gpr (rf0 s)) none, t')

/-- What an instruction does whatever the `fs` base, it does with the base `fb`. -/
theorem OpIA.fs {prof : Profile} {i : Inst} {x : Addr} (fb : Addr) : ∀ {op : Op}, OpIA prof x i op → OpIF prof x fb i op
  | .reg _ _, h => fun s o t hr _ => h s o t hr
  | .load _ _ _ _, h => fun s o t hr _ => h s o t hr
  | .store _ _ _ _, h => fun s o t hr _ => h s o t hr
  | .vld _ _, h => fun s o t hr _ => h s o t hr
  | .vst _ _, h => fun s o t hr _ => h s o t hr

/-- The code at `e'`, from its `j`-th byte to its `j'`-th: instructions doing `ops` there, with the `fs` base
`fb`. -/
inductive BlkF (prof : Profile) (code : List Byte) (e' fb : Addr) : Nat → Nat → List Op → Prop
  | nil (j : Nat) : BlkF prof code e' fb j j []
  | cons {j j' : Nat} {i : Inst} {op : Op} {ops : List Op} : Leaf.Dec prof.feat code j i →
      OpIF prof (e'.add j) fb i op → j < code.length → BlkF prof code e' fb (j + i.len) j' ops →
      BlkF prof code e' fb j j' (op :: ops)

/-- A stretch of code is one with any `fs` base. -/
theorem BlkA.fs {prof : Profile} {code : List Byte} {e' : Addr} (fb : Addr) {j j' : Nat} {ops : List Op}
    (h : BlkA prof code e' j j' ops) : BlkF prof code e' fb j j' ops := by
  induction h with
  | nil j => exact .nil _
  | cons hd ho hj _ ih => exact .cons hd (ho.fs _) hj ih

/-- A stretch of a pattern at `b` is a stretch of a code that holds the pattern there. -/
theorem BlkF.shift {prof : Profile} {pat code : List Byte} {b e' fb : Addr} {j k k' : Nat} {ops : List Op}
    (h : BlkF prof pat b fb k k' ops) (hb : b = e'.add j) (hw : pat <+: code.drop j) :
    BlkF prof code e' fb (j + k) (j + k') ops := by
  subst hb
  induction h with
  | nil k => exact .nil _
  | cons hd ho hk _ ih =>
    refine .cons (Dec.shift hd hw (Nat.le_of_lt hk)) (by rw [← addr_add_add']; exact ho) ?_
      (by rw [Nat.add_assoc]; exact ih)
    rcases length_of_prefix hw with h | h <;> omega

/-! ## Loads and stores through `fs` -/

/-- The memory operand `fs:[b + i·sc + disp]` of `width` bits, base and index optional. -/
def mf (b i : Option Nat) (sc disp width : Nat) : MemOp :=
  { seg := some .fs, base := b, index := i, scale := sc, disp, ripRel := false, addr32 := false, width }

namespace Op

/-- `mov r, fs:[m]`, the `fs` base `fb`. -/
def ldf (fb : Addr) (w r : Nat) (b i : Option Nat) (sc d : Nat) : Op :=
  .load (w / 8) (fun g => fb + eaG g b i sc d) (fun g _ bs => wr g r (ofBytesLE w bs)) fun _ f _ fl => fl = rfz f
/-- `mov fs:[m], r`, the `fs` base `fb`. -/
def stf (fb : Addr) (w : Nat) (b i : Option Nat) (sc d r : Nat) : Op :=
  .store (w / 8) (fun g => fb + eaG g b i sc d) (fun g => toBytesLE (gv g w r) (w / 8)) fun g => g

end Op

section
set_option linter.unusedSimpArgs false
variable {prof : Profile}

/-- `xor r8, x`. -/
def Op.xor8 (r : Nat) (x : Src) : Op :=
  .reg (fun g _ => wrLo g r (gv g 8 r ^^^ x.val 8 g)) fun g f fl => LogF f (gv g 8 r ^^^ x.val 8 g) fl

theorem OpI.xor8 {r len : Nat} (x : Src) :
    OpI prof (mk .xor 8 [gr 8 r, x.opd 8] len) (Op.xor8 r x) := fun s o t htf hdec => by
  cases x <;> exact ⟨_, _, instruction_next htf hdec rfl, ⟨_, rfl⟩, rfl, rfl, rfl⟩

theorem OpIF.ldf {x fb : Addr} {w r len sc d : Nat} {b i : Option Nat} (hw : w = 32 ∨ w = 64) :
    OpIF prof x fb (mk .mov w [gr w r, .mem (mf b i sc d w)] len) (Op.ldf fb w r b i sc d) := by
  dsimp only [Op.ldf, OpIF]
  intro s o t _ hfs htf hac hdec hld
  subst hfs
  refine ⟨_, t, instruction_next htf hdec ?_, rfl, rfl, rfl, rfl⟩
  rcases hw with rfl | rfl <;> cases b <;> cases i <;>
  · simp only [exec, Sem.mov, mk, mf, gr, bind, Prog.bind, readOp, Bool.false_eq_true, ↓reduceIte, memRef,
      effOffset, pure, Prog.readReg, Prog.read, Prog.run, writeOp, Prog.segBase]
    rw [checkAccess_ok (s := advance s len) hac hld]
    rfl

theorem OpIF.stf {x fb : Addr} {w r len sc d : Nat} {b i : Option Nat} (hw : w = 32 ∨ w = 64) :
    OpIF prof x fb (mk .mov w [.mem (mf b i sc d w), gr w r] len) (Op.stf fb w b i sc d r) := by
  dsimp only [Op.stf, OpIF]
  intro s o t _ hfs htf hac hdec _ hwr
  subst hfs
  refine ⟨t, instruction_next htf hdec ?_⟩
  rcases hw with rfl | rfl <;> cases b <;> cases i <;>
  · simp only [exec, Sem.mov, mk, mf, gr, bind, Prog.bind, readOp, Bool.false_eq_true, ↓reduceIte, memRef,
      effOffset, pure, Prog.readReg, Prog.write, Prog.run, writeOp, Prog.segBase]
    rw [checkAccess_ok (s := advance s len) hac hwr]
    rfl

end

end FV7z

namespace FV7z.Fn
open ZellicX86 Decode FV7z.Leaf

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle} {F : Footprint} {Wl : List Rgn}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {e' fb : Addr} {code : List Byte}

/-- A stretch of straight-line code at the code's place, in a run whose start has the `fs` base `fb`. -/
theorem Seg.s_blkF (c : Seg prof F Wl L s₀ o) (hfs : s₀.cpu.seg.fsBase = fb) (hin : CodeIn L e' code) {j j' : Nat}
    {ops : List Op} (hb : BlkF prof code e' fb j j' ops) :
    ∀ {X : State} {t : Nat} {V : Addr → Byte}, KeptW Wl s₀ X → Agree F X.proc.mm.mem V → X.cpu.rip = e'.add j →
      wp F Wl ops (fun g fl V' => ∀ Y t', KeptW Wl s₀ Y → Agree F Y.proc.mm.mem V' → Y.cpu.rip = e'.add j' →
        Y.cpu.gpr = g → Y.cpu.rflags = fl → GoG prof L o gev gP gE Y t') X.cpu.gpr X.cpu.rflags V →
      GoG prof L o gev gP gE X t := by
  induction hb with
  | nil j => intro X t V hK hA hrip h; exact h X t hK hA hrip rfl rfl
  | @cons j j' i op ops hd ho hj _ ih =>
    intro X t V hK hA hrip h
    have hf : ∀ M, KeptW Wl s₀ (X.withMem M) → (X.withMem M).cpu.seg.fsBase = fb :=
      fun M hK' => by rw [hK'.seg]; exact hfs
    cases op with
    | reg hh P =>
      refine c.next (V' := V) (Pr := fun Y => Y.cpu.rip = e'.add (j + i.len) ∧
        P X.cpu.gpr X.cpu.rflags Y.cpu.rflags ∧ Y.cpu.gpr = hh X.cpu.gpr X.cpu.rflags) hK hA hin hj hrip
        (fun M hK' hA' htf _ => ?_) ?_
      · obtain ⟨fl, t', hr, hp, h1, h2, h3⟩ :=
          ho (X.withMem M) o (t + 1) hrip (hf M hK') htf (c.dec hK' hin hrip hd)
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
        obtain ⟨fl, t', hr, hp, h1, h2, h3⟩ :=
          ho (X.withMem M) o (t + 1) hrip (hf M hK') htf hac (c.dec hK' hin hrip hd) hrd
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
        obtain ⟨t', hr⟩ := ho (X.withMem M) o (t + 1) hrip (hf M hK') htf hac (c.dec hK' hin hrip hd) hlen hwr
        exact ⟨_, _, hr, hKs.nx rfl rfl rfl, hAs, rip_add hrip M i.len, rfl, rfl⟩
      · rintro Y t' hKY hAY ⟨hrY, hfY, hgY⟩
        exact ih hKY hAY hrY (by rw [hgY, hfY]; exact h)
    | vld n ea =>
      obtain ⟨hl, h⟩ := h
      refine c.next (V' := V) (Pr := fun Y => Y.cpu.rip = e'.add (j + i.len) ∧
        Y.cpu.rflags = rfz X.cpu.rflags ∧ Y.cpu.gpr = X.cpu.gpr) hK hA hin hj hrip
        (fun M hK' hA' htf hac => ?_) ?_
      · obtain ⟨hrd, -⟩ := c.load_ok (X := X.withMem M) hK' hA' hl
        obtain ⟨z, t', hr⟩ := ho (X.withMem M) o (t + 1) hrip (hf M hK') htf hac (c.dec hK' hin hrip hd) hrd
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
      obtain ⟨bs, t', hlen, hr⟩ := ho (X.withMem M) o (t + 1) hrip (hf M hK') htf hac (c.dec hK' hin hrip hd) hwr
      obtain ⟨-, hKs, hAs⟩ := c.store_ok (X := X.withMem M) hK' hA' (bs := bs) (a := ea X.cpu.gpr)
        (by rw [hlen]; exact hst)
      exact ⟨_, _, hr, ih (hKs.nx rfl rfl rfl) hAs (rip_add hrip M i.len) (h bs hlen)⟩

end FV7z.Fn

namespace FV7z
open ZellicX86 Decode FV7z.Leaf FV7z.Fn

/-- `Sp`, for runs whose start has the `fs` base `fb`. -/
structure SpF (prof : Profile) (code : List Byte) (e' fb : Addr) (j : Nat) (W : Wpt) : Prop where
  run : ∀ {F : Footprint} {Wl : List Rgn} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle} {gev : List Event}
    {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop},
    Seg prof F Wl L s₀ o → s₀.cpu.seg.fsBase = fb → CodeIn L e' code →
    ∀ {X : State} {t : Nat} {V : Addr → Byte} (Q : Post), KeptW Wl s₀ X → Agree F X.proc.mm.mem V →
      X.cpu.rip = e'.add j → W F Wl Q X.cpu.gpr X.cpu.rflags V →
      (∀ j' g fl V', Q j' g fl V' → ∀ Y t', KeptW Wl s₀ Y → Agree F Y.proc.mm.mem V' → Y.cpu.rip = e'.add j' →
        Y.cpu.gpr = g → Y.cpu.rflags = fl → GoG prof L o gev gP gE Y t') →
      GoG prof L o gev gP gE X t

variable {prof : Profile} {code : List Byte} {e' fb : Addr}

/-- An `Sp` holds with any `fs` base. -/
theorem Sp.fs {j : Nat} {W : Wpt} (h : Sp prof code e' j W) : SpF prof code e' fb j W :=
  ⟨fun c _ hin _ _ _ Q hK hA hrip hW k => h.run c hin Q hK hA hrip hW k⟩

namespace SpF

theorem skip (j : Nat) : SpF prof code e' fb j fun _ _ Q => Q j := (Sp.skip j).fs

theorem never (j : Nat) : SpF prof code e' fb j fun _ _ _ _ _ _ => False := (Sp.never j).fs

theorem mono {j : Nat} {W W' : Wpt} (h : SpF prof code e' fb j W)
    (hw : ∀ F Wl Q g f V, W' F Wl Q g f V → W F Wl Q g f V) : SpF prof code e' fb j W' :=
  ⟨fun c hfs hin _ _ _ Q hK hA hrip hW k => h.run c hfs hin Q hK hA hrip (hw _ _ _ _ _ _ hW) k⟩

theorem blk {j j' : Nat} {ops : List Op} (hb : Blk prof code j j' ops) :
    SpF prof code e' fb j fun F Wl Q => wp F Wl ops (Q j') := (Sp.blk hb).fs

theorem blkA {j j' : Nat} {ops : List Op} (hb : BlkA prof code e' j j' ops) :
    SpF prof code e' fb j fun F Wl Q => wp F Wl ops (Q j') := (Sp.blkA hb).fs

/-- A stretch of straight-line code with instructions through `fs`. -/
theorem blkF {j j' : Nat} {ops : List Op} (hb : BlkF prof code e' fb j j' ops) :
    SpF prof code e' fb j fun F Wl Q => wp F Wl ops (Q j') :=
  ⟨fun c hfs hin _ _ _ _ hK hA hrip hW k => c.s_blkF hfs hin hb hK hA hrip
    (wp_mono ops (fun _ _ _ hq Y t' hKY hAY hrY hg hf => k _ _ _ _ hq Y t' hKY hAY hrY hg hf) hW)⟩

/-- A stretch with instructions through `fs`, then a piece from its end. -/
theorem blkF_then {j j' : Nat} {ops : List Op} {W : Wpt} (hb : BlkF prof code e' fb j j' ops)
    (h : SpF prof code e' fb j' W) : SpF prof code e' fb j fun F Wl Q => wp F Wl ops (W F Wl Q) :=
  ⟨fun c hfs hin _ _ _ Q hK hA hrip hW k => c.s_blkF hfs hin hb hK hA hrip
    (wp_mono ops (fun _ _ _ hq _ _ hKY hAY hrY hg hf => h.run c hfs hin Q hKY hAY hrY (hg ▸ hf ▸ hq) k) hW)⟩

theorem blkA_then {j j' : Nat} {ops : List Op} {W : Wpt} (hb : BlkA prof code e' j j' ops)
    (h : SpF prof code e' fb j' W) : SpF prof code e' fb j fun F Wl Q => wp F Wl ops (W F Wl Q) :=
  blkF_then (hb.fs fb) h

theorem blk_then {j j' : Nat} {ops : List Op} {W : Wpt} (hb : Blk prof code j j' ops)
    (h : SpF prof code e' fb j' W) : SpF prof code e' fb j fun F Wl Q => wp F Wl ops (W F Wl Q) :=
  blkA_then (hb.at e') h

/-- A jump, then a piece from its target. -/
theorem jmp_then {j t : Nat} {W : Wpt} (h : SpF prof code e' fb j fun _ _ Q g f V => Q t g (rfz f) V)
    (h1 : SpF prof code e' fb t W) : SpF prof code e' fb j fun F Wl Q g f V => W F Wl Q g (rfz f) V := by
  refine ⟨?_⟩
  intro F Wl L s₀ o gev gP gE c hfs hin X t' V Q hK hA hrip hW k
  refine h.run c hfs hin (fun j' g f V => j' = t ∧ W F Wl Q g f V) hK hA hrip ⟨rfl, hW⟩ ?_
  rintro j' g fl V' ⟨rfl, hq⟩ Y t'' hKY hAY hrY hg hf
  exact h1.run c hfs hin Q hKY hAY hrY (hg ▸ hf ▸ hq) k

/-- A conditional jump, then a piece from each of its two exits. -/
theorem jcc_then {j t n : Nat} {cc : Cond} {W1 W2 : Wpt}
    (h : SpF prof code e' fb j fun _ _ Q g f V =>
      (f.cond cc = true → Q t g (rfz f) V) ∧ (f.cond cc = false → Q n g (rfz f) V))
    (h1 : SpF prof code e' fb t W1) (h2 : SpF prof code e' fb n W2) :
    SpF prof code e' fb j fun F Wl Q g f V =>
      (f.cond cc = true → W1 F Wl Q g (rfz f) V) ∧ (f.cond cc = false → W2 F Wl Q g (rfz f) V) := by
  refine ⟨?_⟩
  intro F Wl L s₀ o gev gP gE c hfs hin X t' V Q hK hA hrip hW k
  refine h.run c hfs hin (fun j' g f V => (j' = t ∧ W1 F Wl Q g f V) ∨ (j' = n ∧ W2 F Wl Q g f V)) hK hA hrip
    ⟨fun hc => .inl ⟨rfl, hW.1 hc⟩, fun hc => .inr ⟨rfl, hW.2 hc⟩⟩ ?_
  rintro j' g fl V' (⟨rfl, hq⟩ | ⟨rfl, hq⟩) Y t'' hKY hAY hrY hg hf
  · exact h1.run c hfs hin Q hKY hAY hrY (hg ▸ hf ▸ hq) k
  · exact h2.run c hfs hin Q hKY hAY hrY (hg ▸ hf ▸ hq) k

/-- The `SpF` of a table of pieces by their offsets, one more entry. -/
theorem table {ℓ k : Nat} {W W' : Wpt} (h : SpF prof code e' fb k W) (h' : SpF prof code e' fb ℓ W') :
    SpF prof code e' fb ℓ (if ℓ = k then W else W') := by
  split
  · next e => subst e; exact h
  · exact h'

/-- An `SpF` in a run that has its code and whose start has the `fs` base. -/
theorem «at» {j : Nat} {W : Wpt} {F : Footprint} {Wl : List Rgn} {L : List (Addr × List Byte)} {s₀ : State}
    {o : Oracle} (h : SpF prof code e' fb j W) (c : Seg prof F Wl L s₀ o) (hfs : s₀.cpu.seg.fsBase = fb)
    (hin : CodeIn L e' code) : SpAt prof F Wl L s₀ o e' j (W F Wl) :=
  ⟨fun Q hK hA hrip hW k => h.run c hfs hin Q hK hA hrip hW k⟩

end SpF

end FV7z
