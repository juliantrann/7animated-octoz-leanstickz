import FV7z.Lemmas.Xmm3
import FV7z.Lemmas.Mask
/-!
# Stretches with `xmm` registers whose values are followed (PLAN.md G2, `__strlen_sse2`)

glibc's SSE2 string functions (`__strlen_sse2`, `__strrchr_sse2`, `__memset_sse2_unaligned`, …) compare 16 bytes at a
time: `pcmpeqb` against a register of zeros, `pminub` to fold four vectors into one, `pmovmskb` to gather the bytes'
top bits into a mask of a general register. A proof follows the low 128 bits of the vector registers.

- `xsOf z`: the low 128 bits of each vector register; `xset x k v`: `x` with register `k` replaced; `xsOf_with`: a
  legacy SSE write of register `k` (its bits 511–128 kept) is `xset`.
- `peqb`, `pminb`, `pmsk`: what `pcmpeqb`, `pminub` and `pmovmskb` compute; `lane_ofBytes`, `getLsbD_pmsk`.
- `VOp`: an `Op` that keeps the vector registers (`.op`), or a vector instruction (`.v`): a load of `n` bytes at
  `ea g` (`0` for none), aligned to 16 if `al`, new registers `hg g x bs` and new `xmm` registers `hx g x bs`.
  `VOpI`, `BlkV`, `wpV`: as `OpI`, `Blk`, `wp` (`Blk.lean`), with the `xmm` registers `x`.
- `VOpI.pxor`, `pcmpeqb`, `pcmpeqb_m`, `pminub_m`, `movdqa_m`, `movdqu_m`, `pmovmskb`: the instructions.
- `Seg.s_blkV`: a stretch of `VOp`s as one step of a run.
-/
namespace FV7z
open ZellicX86 Decode

attribute [-simp] BitVec.getLsbD_eq_getElem

/-- The low 128 bits of the vector registers. -/
abbrev XRegs := Fin 32 → BitVec 128

/-- The low 128 bits of each of the vector registers `z`. -/
def xsOf (z : Fin 32 → BitVec 512) : XRegs := fun k => (z k).setWidth 128

/-- `x` with register `k` replaced by `v`. -/
def xset (x : XRegs) (k : Fin 32) (v : BitVec 128) : XRegs := fun k' => if k' = k then v else x k'

theorem xsOf_with (z : Fin 32 → BitVec 512) (k : Fin 32) (hi : BitVec 384) (v : BitVec 128) :
    xsOf (withZmm z k (hi ++ v)) = xset (xsOf z) k v := by
  funext k'
  by_cases h : k' = k
  · subst h
    simp only [xsOf, xset, ↓reduceIte]
    exact xlo_with z k' hi v
  · simp only [xsOf, xset, h, ↓reduceIte, withZmm_ne z k k' _ h]

@[simp] theorem xset_same (x : XRegs) (k : Fin 32) (v : BitVec 128) : xset x k v k = v := by
  simp only [xset, ↓reduceIte]

theorem xset_ne (x : XRegs) {k k' : Fin 32} (v : BitVec 128) (h : k' ≠ k) : xset x k v k' = x k' := by
  simp only [xset, h, ↓reduceIte]

/-- The address `[b + d]` of registers `g`. -/
abbrev eaB (g : Gprs) (b d : Nat) : Addr := g.get (regOf b) + BitVec.ofNat 64 d

/-! ## What the instructions compute -/

/-- `pcmpeqb`: each byte all ones where the two are equal, else 0. -/
def peqb (a b : BitVec 128) : BitVec 128 := ofBytes fun j => if lane 8 a j = lane 8 b j then BitVec.allOnes 8 else 0

/-- `pminub`: each byte the smaller of the two, unsigned. -/
def pminb (a b : BitVec 128) : BitVec 128 :=
  ofBytes fun j => if lane 8 a j ≤ lane 8 b j then lane 8 a j else lane 8 b j

/-- `pmovmskb`: bit `j` the top bit of byte `j`. -/
def pmsk (b : BitVec 128) : BitVec 32 :=
  (List.range 16).foldl (fun m j => m ||| ((BitVec.ofBool (lane 8 b j).msb).setWidth 32 <<< j)) (0 : BitVec 32)

theorem lane_ofBytes (f : Nat → BitVec 8) {j : Nat} (hj : j < 16) : lane 8 (ofBytes f) j = f j := by
  have : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 ∨ j = 10 ∨ j = 11 ∨
    j = 12 ∨ j = 13 ∨ j = 14 ∨ j = 15 := by omega
  rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  simp (disch := omega) only [lane, ofBytes, BitVec.extractLsb'_append_eq_of_le, BitVec.extractLsb'_append_eq_right,
    BitVec.extractLsb'_eq_self, Nat.mul_zero, Nat.reduceMul, Nat.reduceSub]

theorem getLsbD_bit (c : Bool) (a i : Nat) :
    ((BitVec.ofBool c).setWidth 32 <<< a).getLsbD i = (decide (a = i) && decide (i < 32) && c) := by
  simp only [BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth, BitVec.getLsbD_ofBool]
  by_cases h : a = i
  · subst h
    cases c <;> simp
  · by_cases h1 : i < a
    · simp [h, h1]
    · have h2 : i - a ≠ 0 := by omega
      simp [h, h1, h2]

theorem getLsbD_foldl_bits (g : Nat → Bool) : ∀ (l : List Nat) (m : BitVec 32) (i : Nat),
    (l.foldl (fun m j => m ||| ((BitVec.ofBool (g j)).setWidth 32 <<< j)) m).getLsbD i =
      (m.getLsbD i || (decide (i ∈ l) && decide (i < 32) && g i))
  | [], m, i => by simp
  | a :: l, m, i => by
    rw [List.foldl_cons, getLsbD_foldl_bits g l, BitVec.getLsbD_or, getLsbD_bit]
    by_cases h : a = i
    · subst h
      cases h1 : decide (a < 32) <;> cases hg : g a <;> cases hm : m.getLsbD a <;> simp [hm, h1]
    · have h' : ¬ i = a := fun e => h e.symm
      simp [h, h', List.mem_cons]

theorem getLsbD_pmsk (b : BitVec 128) (i : Nat) :
    (pmsk b).getLsbD i = (decide (i < 16) && (lane 8 b i).msb) := by
  refine (getLsbD_foldl_bits (fun j => (lane 8 b j).msb) (List.range 16) 0 i).trans ?_
  simp only [BitVec.getLsbD_zero, Bool.false_or, List.mem_range]
  by_cases h : i < 16
  · have h' : i < 32 := by omega
    simp [h, h']
  · simp [h]

/-! ## Stretches -/

/-- What an instruction does to the registers, flags and the low halves of the vector registers. -/
inductive VOp where
  /-- An `Op` that keeps the vector registers. -/
  | op (op : Op)
  /-- A load of `n` bytes `bs` at `ea g` (none for `n = 0`), aligned to 16 if `al`: new registers `hg g x bs`, new
  vector registers' low halves `hx g x bs`, `RF` cleared. -/
  | v (n : Nat) (al : Bool) (ea : Gprs → Addr) (hg : Gprs → XRegs → List Byte → Gprs)
      (hx : Gprs → XRegs → List Byte → XRegs)

variable {prof : Profile}

/-- The instruction `i` does `op`. -/
def VOpI (prof : Profile) (i : Inst) : VOp → Prop
  | .op op => OpI prof i op
  | .v n al ea hg hx => ∀ (s : State) (o : Oracle) (t : Nat), s.cpu.rflags.tf = false → s.cpu.rflags.ac = false →
      Decode.decode prof.feat (fetchByte prof.feat s) = .ok i → Readable prof s (ea s.cpu.gpr) n →
      (al = true → (ea s.cpu.gpr).toNat % 16 = 0) →
      ∃ z t', (instruction prof s).runStream o t = (.running (nxz s i.len
          (hg s.cpu.gpr (xsOf s.cpu.vec.zmm) (readBytes s.proc.mm.mem (ea s.cpu.gpr) n)) (rf0 s) z) none, t') ∧
        xsOf z = hx s.cpu.gpr (xsOf s.cpu.vec.zmm) (readBytes s.proc.mm.mem (ea s.cpu.gpr) n)

/-- The code from its `j`-th byte to its `j'`-th: instructions doing `ops`. -/
inductive BlkV (prof : Profile) (code : List Byte) : Nat → Nat → List VOp → Prop
  | nil (j : Nat) : BlkV prof code j j []
  | cons {j j' : Nat} {i : Inst} {op : VOp} {ops : List VOp} : Leaf.Dec prof.feat code j i → VOpI prof i op →
      j < code.length → BlkV prof code (j + i.len) j' ops → BlkV prof code j j' (op :: ops)

/-- `wp` with the low halves of the vector registers `x`. -/
def wpV (F : Footprint) (Wl : List Rgn) : List VOp → (Gprs → Rflags → XRegs → (Addr → Byte) → Prop) →
    Gprs → Rflags → XRegs → (Addr → Byte) → Prop
  | [], Q, g, f, x, V => Q g f x V
  | .op op :: ops, Q, g, f, x, V => op.kv = true ∧ wp F Wl [op] (fun g' f' V' => wpV F Wl ops Q g' f' x V') g f V
  | .v n al ea hg hx :: ops, Q, g, f, x, V => (∀ i < n, Foot F.data ((ea g).add i)) ∧
      (al = true → (ea g).toNat % 16 = 0) ∧
      wpV F Wl ops Q (hg g x ((byteAddrs (ea g) n).map V)) (rfz f) (hx g x ((byteAddrs (ea g) n).map V)) V

theorem BlkV.append {code : List Byte} {j j' j'' : Nat} {ops ops' : List VOp}
    (h : BlkV prof code j j' ops) (h' : BlkV prof code j' j'' ops') : BlkV prof code j j'' (ops ++ ops') := by
  induction h with
  | nil j => exact h'
  | cons hd ho hj _ ih => exact .cons hd ho hj (ih h')

theorem wpV_append {F : Footprint} {Wl : List Rgn} : ∀ (ops ops' : List VOp)
    {Q : Gprs → Rflags → XRegs → (Addr → Byte) → Prop} {g : Gprs} {f : Rflags} {x : XRegs} {V : Addr → Byte},
    wpV F Wl ops (wpV F Wl ops' Q) g f x V → wpV F Wl (ops ++ ops') Q g f x V
  | [], _, _, _, _, _, _, h => h
  | .op _ :: ops, ops', _, _, _, _, _, h => ⟨h.1, wp_mono _ (fun _ _ _ hq => wpV_append ops ops' hq) h.2⟩
  | .v _ _ _ _ _ :: ops, ops', _, _, _, _, _, h => ⟨h.1, h.2.1, wpV_append ops ops' h.2.2⟩

/-! ## The instructions -/

namespace VOp

/-- `pxor xmmN, xmmM`. -/
def pxor (n m : Nat) : VOp :=
  .v 0 false (fun _ => 0) (fun g _ _ => g) fun _ x _ => xset x (xmmOf n) (x (xmmOf n) ^^^ x (xmmOf m))
/-- `pcmpeqb xmmN, xmmM`. -/
def pcmpeqb (n m : Nat) : VOp :=
  .v 0 false (fun _ => 0) (fun g _ _ => g) fun _ x _ => xset x (xmmOf n) (peqb (x (xmmOf n)) (x (xmmOf m)))
/-- `pcmpeqb xmmN, [b + d]`. -/
def pcmpeqb_m (n b d : Nat) : VOp :=
  .v 16 true (fun g => eaB g b d) (fun g _ _ => g) fun _ x bs =>
    xset x (xmmOf n) (peqb (x (xmmOf n)) (ofBytesLE 128 bs))
/-- `pminub xmmN, [b + d]`. -/
def pminub_m (n b d : Nat) : VOp :=
  .v 16 true (fun g => eaB g b d) (fun g _ _ => g) fun _ x bs =>
    xset x (xmmOf n) (pminb (x (xmmOf n)) (ofBytesLE 128 bs))
/-- `movdqa xmmN, [b + d]`. -/
def movdqa_m (n b d : Nat) : VOp :=
  .v 16 true (fun g => eaB g b d) (fun g _ _ => g) fun _ x bs => xset x (xmmOf n) (ofBytesLE 128 bs)
/-- `movdqu xmmN, [b + d]`. -/
def movdqu_m (n b d : Nat) : VOp :=
  .v 16 false (fun g => eaB g b d) (fun g _ _ => g) fun _ x bs => xset x (xmmOf n) (ofBytesLE 128 bs)
/-- `pmovmskb r32, xmmN`. -/
def pmovmskb (r n : Nat) : VOp :=
  .v 0 false (fun _ => 0) (fun g x _ => g.set (regOf r) ((pmsk (x (xmmOf n))).setWidth 64)) fun _ x _ => x

end VOp

theorem VOpI.pxor {w n m len : Nat} :
    VOpI prof (mk (.sse .pxor) w [.xmm n, .xmm m] len) (VOp.pxor n m) := by
  intro s o t htf _ hdec _ _
  refine ⟨withZmm s.cpu.vec.zmm (xmmOf n) ((s.cpu.vec.zmm (xmmOf n)).extractLsb' 128 384 ++ (xlo s n ^^^ xlo s m)),
    t, instruction_next htf hdec ?_, xsOf_with _ _ _ _⟩
  simp only [exec, execSse, Sem.pxor, packedOp, packed, aligned16, bind, Prog.bind, readOp,
    Bool.false_eq_true, ↓reduceIte, pure, Prog.run, writeOp, Prog.readZmm]
  rfl

theorem VOpI.pcmpeqb {w n m len : Nat} :
    VOpI prof (mk (.sse .pcmpeqb) w [.xmm n, .xmm m] len) (VOp.pcmpeqb n m) := by
  intro s o t htf _ hdec _ _
  refine ⟨withZmm s.cpu.vec.zmm (xmmOf n) ((s.cpu.vec.zmm (xmmOf n)).extractLsb' 128 384 ++ peqb (xlo s n) (xlo s m)),
    t, instruction_next htf hdec ?_, xsOf_with _ _ _ _⟩
  simp only [exec, execSse, Sem.pcmpeqb, packedOp, packed, aligned16, bind, Prog.bind, readOp,
    Bool.false_eq_true, ↓reduceIte, pure, Prog.run, writeOp, Prog.readZmm]
  rfl

theorem VOpI.pcmpeqb_m {w n b d len : Nat} :
    VOpI prof (mk (.sse .pcmpeqb) w [.xmm n, .mem (mbd b d 128)] len) (VOp.pcmpeqb_m n b d) := by
  intro s o t htf hac hdec hld hal
  have hal' : (eaD s b d).toNat % 16 = 0 := hal rfl
  refine ⟨withZmm s.cpu.vec.zmm (xmmOf n) ((s.cpu.vec.zmm (xmmOf n)).extractLsb' 128 384 ++
    peqb (xlo s n) (ofBytesLE 128 (readBytes s.proc.mm.mem (eaD s b d) 16))),
    t, instruction_next htf hdec ?_, xsOf_with _ _ _ _⟩
  simp only [exec, execSse, Sem.pcmpeqb, packedOp, packed, aligned16, Prog.alignedTo, mk, mbd, bind, Prog.bind,
    readOp, Bool.false_eq_true, ↓reduceIte, memRef, effOffset, pure, Prog.readReg, Prog.read, Prog.run,
    BitVec.mul_one, writeOp, Prog.readZmm, eaD_adv, hal', true_or]
  rw [checkAccess_ok (s := advance s len) hac hld]
  rfl

theorem VOpI.pminub_m {w n b d len : Nat} :
    VOpI prof (mk (.sse (.pminu 8)) w [.xmm n, .mem (mbd b d 128)] len) (VOp.pminub_m n b d) := by
  intro s o t htf hac hdec hld hal
  have hal' : (eaD s b d).toNat % 16 = 0 := hal rfl
  refine ⟨withZmm s.cpu.vec.zmm (xmmOf n) ((s.cpu.vec.zmm (xmmOf n)).extractLsb' 128 384 ++
    pminb (xlo s n) (ofBytesLE 128 (readBytes s.proc.mm.mem (eaD s b d) 16))),
    t, instruction_next htf hdec ?_, xsOf_with _ _ _ _⟩
  simp only [exec, execSse, Sem.pminu, if_pos (show (8 : Nat) = 8 from rfl), packedOp, packed, aligned16,
    Prog.alignedTo, mk, mbd, bind, Prog.bind, readOp, Bool.false_eq_true, ↓reduceIte, memRef, effOffset, pure,
    Prog.readReg, Prog.read, Prog.run, BitVec.mul_one, writeOp, Prog.readZmm, eaD_adv, hal', true_or]
  rw [checkAccess_ok (s := advance s len) hac hld]
  rfl

theorem VOpI.movdqa_m {w n b d len : Nat} :
    VOpI prof (mk (.sse .movdqa) w [.xmm n, .mem (mbd b d 128)] len) (VOp.movdqa_m n b d) := by
  intro s o t htf hac hdec hld hal
  have hal' : (eaD s b d).toNat % 16 = 0 := hal rfl
  refine ⟨withZmm s.cpu.vec.zmm (xmmOf n) ((s.cpu.vec.zmm (xmmOf n)).extractLsb' 128 384 ++
    ofBytesLE 128 (readBytes s.proc.mm.mem (eaD s b d) 16)),
    t, instruction_next htf hdec ?_, xsOf_with _ _ _ _⟩
  simp only [exec, execSse, Sem.movdqa, moveAligned, aligned16, Prog.alignedTo, mk, mbd, bind, Prog.bind, readOp,
    Bool.false_eq_true, ↓reduceIte, memRef, effOffset, pure, Prog.readReg, Prog.read, Prog.run, BitVec.mul_one,
    writeOp, Prog.readZmm, eaD_adv, hal', true_or]
  rw [checkAccess_ok (s := advance s len) hac hld]
  rfl

theorem VOpI.movdqu_m {w n b d len : Nat} :
    VOpI prof (mk (.sse .movdqu) w [.xmm n, .mem (mbd b d 128)] len) (VOp.movdqu_m n b d) := by
  intro s o t htf hac hdec hld _
  refine ⟨withZmm s.cpu.vec.zmm (xmmOf n) ((s.cpu.vec.zmm (xmmOf n)).extractLsb' 128 384 ++
    ofBytesLE 128 (readBytes s.proc.mm.mem (eaD s b d) 16)),
    t, instruction_next htf hdec ?_, xsOf_with _ _ _ _⟩
  simp only [exec, execSse, Sem.movdqu, moveBits, mk, mbd, bind, Prog.bind, readOp, Bool.false_eq_true, ↓reduceIte,
    memRef, effOffset, pure, Prog.readReg, Prog.read, Prog.run, BitVec.mul_one, writeOp, Prog.readZmm]
  rw [eaD_adv, checkAccess_ok (s := advance s len) hac hld]
  rfl

theorem VOpI.pmovmskb {w r n len : Nat} :
    VOpI prof (mk (.sse .pmovmskb) w [gr 32 r, .xmm n] len) (VOp.pmovmskb r n) := by
  intro s o t htf _ hdec _ _
  exact ⟨s.cpu.vec.zmm, t, instruction_next htf hdec rfl, rfl⟩

/-- `bsf r64, r64'`, of a source not 0: its lowest set bit. -/
theorem bsf64_rr {s : State} {o : Oracle} {t r q len : Nat} (htf : s.cpu.rflags.tf = false)
    (hdec : Decode.decode prof.feat (fetchByte prof.feat s) = .ok (mk (.bit .bsf) 64 [gr 64 r, gr 64 q] len))
    (hx : rv s 64 q ≠ 0) :
    ∃ fl t', (instruction prof s).runStream o t = (.running (nx s len (s.cpu.gpr.set (regOf r)
      (BitVec.ofNat 64 (lowestSetBit (rv s 64 q)))) fl) none, t') ∧
      fl.tf = s.cpu.rflags.tf ∧ fl.ac = s.cpu.rflags.ac ∧ fl.df = s.cpu.rflags.df := by
  refine ⟨?_, ?_, instruction_next htf hdec ?_, ?_, ?_, ?_⟩
  case refine_3 =>
    have hx' : ((advance s len).cpu.gpr.get (regOf q)).setWidth 64 ≠ 0 := hx
    simp only [exec, execBits, Sem.bsf, bitScan, mk, gr, bind, Prog.bind, readOp, Bool.false_eq_true, ↓reduceIte,
      pure, Prog.readReg, Prog.run, writeOp]
    simp only [hx', ↓reduceIte]
    rfl
  all_goals rfl

end FV7z

namespace FV7z.Fn.Seg
open ZellicX86 Decode FV7z.Leaf

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle} {F : Footprint} {Wl : List Rgn}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {e' : Addr} {code : List Byte}

/-- A stretch of `VOp`s: what is left is `wpV` from the registers, flags, low halves of the vector registers and the
footprint's bytes, and the continuation on what the stretch leaves. -/
theorem s_blkV (c : Seg prof F Wl L s₀ o) (hin : CodeIn L e' code) {j j' : Nat} {ops : List VOp}
    (hb : BlkV prof code j j' ops) :
    ∀ {X : State} {t : Nat} {V : Addr → Byte}, KeptW Wl s₀ X → Agree F X.proc.mm.mem V → X.cpu.rip = e'.add j →
      wpV F Wl ops (fun g fl x V' => ∀ Y t', KeptW Wl s₀ Y → Agree F Y.proc.mm.mem V' → Y.cpu.rip = e'.add j' →
        Y.cpu.gpr = g → Y.cpu.rflags = fl → xsOf Y.cpu.vec.zmm = x → GoG prof L o gev gP gE Y t')
        X.cpu.gpr X.cpu.rflags (xsOf X.cpu.vec.zmm) V →
      GoG prof L o gev gP gE X t := by
  induction hb with
  | nil j => intro X t V hK hA hrip h; exact h X t hK hA hrip rfl rfl rfl
  | @cons j j' i op ops hd ho hj _ ih =>
    intro X t V hK hA hrip h
    cases op with
    | op op =>
      obtain ⟨hkv, h⟩ := h
      exact c.s_blkA_v hin (.cons hd (OpI.at _ ho) hj (.nil _)) X.cpu.vec hK hA hrip rfl
        (by simp only [List.all_cons, List.all_nil, hkv, Bool.and_true])
        (wp_mono [op] (fun g f V' hq Y t' hKY hAY hrY hgY hfY hvY => ih hKY hAY hrY (by rw [hgY, hfY, hvY]; exact hq))
          h)
    | v n al ea hg hx =>
      obtain ⟨hl, hal, h⟩ := h
      refine c.next (V' := V) (Pr := fun Y => Y.cpu.rip = e'.add (j + i.len) ∧ Y.cpu.rflags = rfz X.cpu.rflags ∧
        Y.cpu.gpr = hg X.cpu.gpr (xsOf X.cpu.vec.zmm) ((byteAddrs (ea X.cpu.gpr) n).map V) ∧
        xsOf Y.cpu.vec.zmm = hx X.cpu.gpr (xsOf X.cpu.vec.zmm) ((byteAddrs (ea X.cpu.gpr) n).map V))
        hK hA hin hj hrip (fun M hK' hA' htf hac => ?_) ?_
      · obtain ⟨hrd, hv⟩ := c.load_ok (X := X.withMem M) hK' hA' hl
        obtain ⟨z, t', hr, hz⟩ := ho (X.withMem M) o (t + 1) htf hac (c.dec hK' hin hrip hd) hrd hal
        refine ⟨_, _, hr, hK'.modCpu rfl rfl rfl rfl rfl rfl rfl, hA', rip_add hrip M i.len, rfl, ?_, ?_⟩
        · rw [← hv]; rfl
        · rw [← hv]; exact hz
      · rintro Y t' hKY hAY ⟨hrY, hfY, hgY, hxY⟩
        exact ih hKY hAY hrY (by rw [hgY, hfY, hxY]; exact h)

end FV7z.Fn.Seg
