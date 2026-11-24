import FV7z.Lemmas.BlkOps7
/-!
# `not`, `cqo`, three-operand `imul`, `idiv r64` and `bsr r32` (PLAN.md M, ctor 103: `init_cacheinfo`)

Instructions of glibc's `init_cacheinfo` and `handle_intel` (measured with `tools/blk_gen.py`: `not r9d`,
`cqo; idiv rcx`, `imul rax, [rip + d], 3`, `imul rax, rax, 0x55555556`, `bsr ecx, r9d`).

- `Op.not32`, `Op.cqo`, `Op.imul3`, `Op.imul3ma`: `Op`s of `Blk.lean`; `cqo` (`Mn.cwd` at 64 bits) fills `rdx` with the
  sign of `rax`.
- `idiv64`, `Seg.s_idiv64`: `idiv r64` after `cqo` (`rdx` the sign of `rax`) with a positive divisor, a step of its own:
  it faults when the divisor is 0 or the quotient does not fit (`tdiv_fits`: it fits for a positive divisor).
- `bsr32`, `Seg.s_bsr32`: `bsr r32, r32` with a source not 0, a step of its own: with a source 0 the destination is
  left or, on Intel, its upper half may be cleared (an oracle's choice), which no `Op` says.
-/
namespace FV7z
open ZellicX86 Decode

variable {prof : Profile} {o : Oracle} {t : Nat} {s : State}

/-- `not r32`: no flags change. -/
def Op.not32 (r : Nat) : Op := .reg (fun g _ => wr g r (~~~ gv g 32 r)) fun _ f fl => fl = rfz f

theorem OpI.not32 {r len : Nat} : OpI prof (mk .not 32 [gr 32 r] len) (Op.not32 r) := fun _ _ _ htf hdec =>
  ⟨_, _, instruction_next htf hdec rfl, rfl, rfl, rfl, rfl⟩

/-- `cqo`: `rdx` all ones if `rax` is negative, else 0; no flags change. -/
def Op.cqo : Op :=
  .reg (fun g _ => wr g 2 (if (gv g 64 0).msb then BitVec.allOnes 64 else 0)) fun _ f fl => fl = rfz f

theorem OpI.cqo {len : Nat} : OpI prof (mk .cwd 64 [] len) Op.cqo := fun _ _ _ htf hdec =>
  ⟨_, _, instruction_next htf hdec rfl, rfl, rfl, rfl, rfl⟩

/-- `imul r64, q64, imm`: the flags unconstrained. -/
def Op.imul3 (r q v : Nat) : Op :=
  .reg (fun g _ => wr g r (((gv g 64 q).signExtend (2 * 64) * (BitVec.ofNat 64 v).signExtend (2 * 64)).setWidth 64))
    fun _ _ _ => True

theorem OpI.imul3 {r q v len : Nat} :
    OpI prof (mk .imul 64 [gr 64 r, gr 64 q, .imm 64 v] len) (Op.imul3 r q v) := fun _ _ _ htf hdec =>
  ⟨_, _, instruction_next htf hdec rfl, trivial, rfl, rfl, rfl⟩

/-- `imul r64, [A], imm`, the address fixed: the flags unconstrained. -/
def Op.imul3ma (r A v : Nat) : Op :=
  .load 8 (fun _ => BitVec.ofNat 64 A) (fun g _ bs =>
    wr g r (((ofBytesLE 64 bs).signExtend (2 * 64) * (BitVec.ofNat 64 v).signExtend (2 * 64)).setWidth 64))
    fun _ _ _ _ => True

theorem OpIA.imul3_rip {r len d A v : Nat} {x : Addr} (hA : x.add len + BitVec.ofNat 64 d = BitVec.ofNat 64 A) :
    OpIA prof x (mk .imul 64 [gr 64 r, .mem (mrip d 64), .imm 64 v] len) (Op.imul3ma r A v) := by
  dsimp only [Op.imul3ma, OpIA]
  intro s o t hrip htf hac hdec hld
  have he : eaR s len d = BitVec.ofNat 64 A := by rw [← hA, ← hrip]
  refine ⟨?fl, ?t, instruction_next htf hdec ?h, trivial, ?a, ?b, ?c⟩
  case h =>
    simp only [exec, Sem.imul, imulTrunc, mk, mrip, gr, bind, Prog.bind, readOp, Bool.false_eq_true, ↓reduceIte,
      memRef, effOffset, pure, Prog.readRip, Prog.read, Prog.run, Opd.width, writeOp, BitVec.mul_one,
      Prog.readFlags]
    rw [eaR_adv, he, checkAccess_ok (s := advance s len) hac hld]
    rfl
  all_goals rfl

/-- The dividend `rdx:rax` of `idiv` after `cqo` is `rax`, sign-extended. -/
theorem sx_toInt (x h : BitVec 64) (hh : h = if x.msb then BitVec.allOnes 64 else 0) :
    (BitVec.setWidth (2 * 64) (BitVec.setWidth 64 h ++ BitVec.setWidth 64 x)).toInt = x.toInt := by
  have e : BitVec.setWidth (2 * 64) (BitVec.setWidth 64 h ++ BitVec.setWidth 64 x) = x.signExtend (2 * 64) := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    subst hh
    rw [BitVec.setWidth_eq, BitVec.setWidth_eq, BitVec.setWidth_eq, BitVec.getLsbD_append, BitVec.getLsbD_signExtend]
    by_cases h64 : i < 64
    · simp only [h64, ↓reduceIte, decide_true, Bool.true_and, hi]
    · cases hm : x.msb
      · simp only [h64, ↓reduceIte, hm, Bool.false_eq_true, BitVec.getLsbD_zero, Bool.and_false]
      · simp only [h64, ↓reduceIte, hm, BitVec.getLsbD_allOnes, Bool.and_true]
        exact decide_eq_decide.2 (by omega)
  rw [e, BitVec.toInt_signExtend_of_le (by decide)]

/-- The quotient of a 64-bit signed value by a positive divisor fits in 64 bits. -/
theorem tdiv_fits {a b : Int} (ha1 : -2 ^ (64 - 1) ≤ a) (ha2 : a < 2 ^ (64 - 1)) (hb : 0 < b) :
    ¬ (a.tdiv b < -2 ^ (64 - 1) ∨ 2 ^ (64 - 1) ≤ a.tdiv b) := by
  have e : (2 : Int) ^ (64 - 1) = 9223372036854775808 := by decide
  rw [e] at ha1 ha2 ⊢
  rcases Int.le_total 0 a with h0 | h0
  · have h1 := Int.tdiv_le_self b h0
    have h2 := Int.tdiv_nonneg h0 (Int.le_of_lt hb)
    omega
  · have hn : 0 ≤ -a := Int.neg_nonneg_of_nonpos h0
    have h1 := Int.tdiv_le_self b hn
    have h2 := Int.tdiv_nonneg hn (Int.le_of_lt hb)
    rw [Int.neg_tdiv] at h1 h2
    omega

/-- A positive divisor: not 0 and the sign bit clear. -/
theorem toInt_pos_of {y : BitVec 64} (hne : y ≠ 0) (hpos : y.msb = false) : 0 < y.toInt := by
  rw [BitVec.toInt_eq_toNat_of_msb hpos]
  have : y.toNat ≠ 0 := fun h => hne (BitVec.eq_of_toNat_eq (by rw [h]; rfl))
  omega

/-- `idiv r64` after `cqo` (`rdx` the sign of `rax`), the divisor positive. -/
theorem idiv64 {r len : Nat} (htf : s.cpu.rflags.tf = false)
    (hdec : Decode.decode prof.feat (fetchByte prof.feat s) = .ok (mk .idiv 64 [gr 64 r] len))
    (h2 : s.cpu.gpr.rdx = if s.cpu.gpr.rax.msb then BitVec.allOnes 64 else 0)
    (hne : rv s 64 r ≠ 0) (hpos : (rv s 64 r).msb = false) :
    ∃ fl t', (instruction prof s).runStream o t =
        (.running (nx s len ((s.cpu.gpr.set 0 (BitVec.ofInt 64 (s.cpu.gpr.rax.toInt.tdiv (rv s 64 r).toInt))).set 2
          (BitVec.ofInt 64 (s.cpu.gpr.rax.toInt.tmod (rv s 64 r).toInt))) fl) none, t') ∧
      fl.tf = s.cpu.rflags.tf ∧ fl.ac = s.cpu.rflags.ac ∧ fl.df = s.cpu.rflags.df := by
  suffices h : ∃ fl t', ((exec prof (mk .idiv 64 [gr 64 r] len)).run prof.feat prof.linux.splitLock
      (advance s len)).runStream o t = (.ok .next (nx s len ((s.cpu.gpr.set 0
        (BitVec.ofInt 64 (s.cpu.gpr.rax.toInt.tdiv (rv s 64 r).toInt))).set 2
          (BitVec.ofInt 64 (s.cpu.gpr.rax.toInt.tmod (rv s 64 r).toInt))) fl), t') ∧
      fl.tf = s.cpu.rflags.tf ∧ fl.ac = s.cpu.rflags.ac ∧ fl.df = s.cpu.rflags.df by
    obtain ⟨fl, t', h, h1, h2, h3⟩ := h
    exact ⟨fl, t', instruction_next htf hdec h, h1, h2, h3⟩
  simp only [exec, Sem.idiv, dividend, divResult, mk, gr, bind, Prog.bind, readOp, Bool.false_eq_true, ↓reduceIte,
    pure, Prog.readReg, Prog.run, writeOp, Prog.readFlags, accOf, Nat.reduceEqDiff, true_or]
  have e2 : (advance s len).cpu.gpr.get (regOf 2) = s.cpu.gpr.rdx := rfl
  have e0 : (advance s len).cpu.gpr.get (regOf 0) = s.cpu.gpr.rax := rfl
  have er : BitVec.setWidth 64 ((advance s len).cpu.gpr.get (regOf r)) = rv s 64 r := rfl
  have hq := tdiv_fits (BitVec.le_toInt s.cpu.gpr.rax) BitVec.toInt_lt (toInt_pos_of hne hpos)
  rw [e2, e0, er, sx_toInt _ _ h2]
  simp only [hne, hq, ↓reduceIte]
  exact ⟨_, _, rfl, rfl, rfl, rfl⟩

/-- `bsr r32, q32` with a source not 0: the index of its highest set bit, zero-extended. -/
theorem bsr32 {r q len : Nat} (htf : s.cpu.rflags.tf = false)
    (hdec : Decode.decode prof.feat (fetchByte prof.feat s) = .ok (mk (.bit .bsr) 32 [gr 32 r, gr 32 q] len))
    (hne : rv s 32 q ≠ 0) :
    ∃ fl t', (instruction prof s).runStream o t =
        (.running (nx s len (wr s.cpu.gpr r (BitVec.ofNat 32 (highestSetBit (rv s 32 q)))) fl) none, t') ∧
      fl.tf = s.cpu.rflags.tf ∧ fl.ac = s.cpu.rflags.ac ∧ fl.df = s.cpu.rflags.df := by
  suffices h : ∃ fl t', ((exec prof (mk (.bit .bsr) 32 [gr 32 r, gr 32 q] len)).run prof.feat
      prof.linux.splitLock (advance s len)).runStream o t =
        (.ok .next (nx s len (wr s.cpu.gpr r (BitVec.ofNat 32 (highestSetBit (rv s 32 q)))) fl), t') ∧
      fl.tf = s.cpu.rflags.tf ∧ fl.ac = s.cpu.rflags.ac ∧ fl.df = s.cpu.rflags.df by
    obtain ⟨fl, t', h, h1, h2, h3⟩ := h
    exact ⟨fl, t', instruction_next htf hdec h, h1, h2, h3⟩
  have er : BitVec.setWidth 32 ((advance s len).cpu.gpr.get (regOf q)) = rv s 32 q := rfl
  simp only [exec, execBits, Sem.bsr, bitScan, mk, gr, bind, Prog.bind, readOp, Bool.false_eq_true, ↓reduceIte,
    pure, Prog.readReg, Prog.run, writeOp, Prog.readFlags, er, hne]
  exact ⟨_, _, rfl, rfl, rfl, rfl⟩

end FV7z

namespace FV7z.Fn.Seg
open ZellicX86 Decode FV7z.Leaf

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle} {F : Footprint} {Wl : List Rgn}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {e' : Addr} {code : List Byte} {X : State} {t j : Nat} {V : Addr → Byte}

/-- `idiv r64` after `cqo`, the divisor positive. -/
theorem s_idiv64 (c : Seg prof F Wl L s₀ o) (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V)
    (hin : CodeIn L e' code) (hj : j < code.length) (hrip : X.cpu.rip = e'.add j) {r len : Nat}
    (hd : Dec prof.feat code j (FV7z.mk .idiv 64 [gr 64 r] len))
    (h2 : X.cpu.gpr.rdx = if X.cpu.gpr.rax.msb then BitVec.allOnes 64 else 0)
    (hne : rv X 64 r ≠ 0) (hpos : (rv X 64 r).msb = false)
    (k' : ContG prof F Wl L s₀ o gev gP gE V fun Y => Y.cpu.rip = e'.add (j + len) ∧
      Y.cpu.gpr = (X.cpu.gpr.set 0 (BitVec.ofInt 64 (X.cpu.gpr.rax.toInt.tdiv (rv X 64 r).toInt))).set 2
        (BitVec.ofInt 64 (X.cpu.gpr.rax.toInt.tmod (rv X 64 r).toInt))) :
    GoG prof L o gev gP gE X t :=
  c.next hK hA hin hj hrip (fun M hK' hA' htf _ => by
    obtain ⟨fl, t', hr, h1, h2', h3⟩ :=
      idiv64 (s := X.withMem M) (o := o) (t := t + 1) htf (c.dec hK' hin hrip hd) h2 hne hpos
    exact ⟨_, _, hr, hK'.nx h1 h2' h3, hA', rip_add hrip M len, rfl⟩) k'

/-- `bsr r32, q32` with a source not 0. -/
theorem s_bsr32 (c : Seg prof F Wl L s₀ o) (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V)
    (hin : CodeIn L e' code) (hj : j < code.length) (hrip : X.cpu.rip = e'.add j) {r q len : Nat}
    (hd : Dec prof.feat code j (FV7z.mk (.bit .bsr) 32 [gr 32 r, gr 32 q] len)) (hne : rv X 32 q ≠ 0)
    (k' : ContG prof F Wl L s₀ o gev gP gE V fun Y => Y.cpu.rip = e'.add (j + len) ∧
      Y.cpu.gpr = wr X.cpu.gpr r (BitVec.ofNat 32 (highestSetBit (rv X 32 q)))) :
    GoG prof L o gev gP gE X t :=
  c.next hK hA hin hj hrip (fun M hK' hA' htf _ => by
    obtain ⟨fl, t', hr, h1, h2, h3⟩ :=
      bsr32 (s := X.withMem M) (o := o) (t := t + 1) htf (c.dec hK' hin hrip hd) hne
    exact ⟨_, _, hr, hK'.nx h1 h2 h3, hA', rip_add hrip M len, rfl⟩) k'

end FV7z.Fn.Seg
