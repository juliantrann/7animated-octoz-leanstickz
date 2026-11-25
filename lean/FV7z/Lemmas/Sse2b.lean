import FV7z.Lemmas.Sse2
/-!
# More SSE2 steps (PLAN.md G2, `__strrchr_sse2`)

`__strrchr_sse2` spreads the byte it looks for over the 16 bytes of `xmm1` (`movd xmm1, esi`, `punpcklbw xmm1, xmm1`,
`punpcklwd xmm1, xmm1`, `pshufd xmm1, xmm1, 0`), and copies and folds vectors between registers (`movdqa xmmN, xmmM`,
`pminub xmmN, xmmM`). Their `VOp`s and `VOpI`s, as `Lemmas/Sse2.lean`'s, and the spread's bytes (`lane_bcast`).
-/
namespace FV7z
open ZellicX86 Decode

namespace VOp

/-- `movd xmmN, r32`: the register's low 32 bits, zero-extended. -/
def movd (n r : Nat) : VOp :=
  .v 0 false (fun _ => 0) (fun g _ _ => g) fun g x _ =>
    xset x (xmmOf n) (((g.get (regOf r)).setWidth 32).setWidth 128)
/-- `punpcklbw xmmN, xmmM`. -/
def punpcklbw (n m : Nat) : VOp :=
  .v 0 false (fun _ => 0) (fun g _ _ => g) fun _ x _ =>
    xset x (xmmOf n) (ofBytes (interleave 8 0 (x (xmmOf n)) (x (xmmOf m))))
/-- `punpcklwd xmmN, xmmM`. -/
def punpcklwd (n m : Nat) : VOp :=
  .v 0 false (fun _ => 0) (fun g _ _ => g) fun _ x _ =>
    xset x (xmmOf n) (ofWords (interleave 16 0 (x (xmmOf n)) (x (xmmOf m))))
/-- `pshufd xmmN, xmmM, k`. -/
def pshufd (n m k : Nat) : VOp :=
  .v 0 false (fun _ => 0) (fun g _ _ => g) fun _ x _ =>
    xset x (xmmOf n) (ofDwords fun j => lane 32 (x (xmmOf m)) (k / 4 ^ j % 4))
/-- `movdqa xmmN, xmmM`. -/
def movdqa (n m : Nat) : VOp :=
  .v 0 false (fun _ => 0) (fun g _ _ => g) fun _ x _ => xset x (xmmOf n) (x (xmmOf m))
/-- `pminub xmmN, xmmM`. -/
def pminub (n m : Nat) : VOp :=
  .v 0 false (fun _ => 0) (fun g _ _ => g) fun _ x _ => xset x (xmmOf n) (pminb (x (xmmOf n)) (x (xmmOf m)))

end VOp

variable {prof : Profile}

theorem VOpI.movd {w n r len : Nat} :
    VOpI prof (mk (.sse .movd) w [.xmm n, gr 32 r] len) (VOp.movd n r) := by
  intro s o t htf _ hdec _ _
  refine ⟨withZmm s.cpu.vec.zmm (xmmOf n) ((s.cpu.vec.zmm (xmmOf n)).extractLsb' 128 384 ++
    ((s.cpu.gpr.get (regOf r)).setWidth 32).setWidth 128), t, instruction_next htf hdec ?_, xsOf_with _ _ _ _⟩
  simp only [exec, execSse, Sem.movd, moveBits, gr, bind, Prog.bind, readOp, Bool.false_eq_true, ↓reduceIte,
    pure, Prog.readReg, Prog.run, writeOp, Prog.readZmm]
  rfl

theorem VOpI.punpcklbw {w n m len : Nat} :
    VOpI prof (mk (.sse .punpcklbw) w [.xmm n, .xmm m] len) (VOp.punpcklbw n m) := by
  intro s o t htf _ hdec _ _
  refine ⟨withZmm s.cpu.vec.zmm (xmmOf n) ((s.cpu.vec.zmm (xmmOf n)).extractLsb' 128 384 ++
    ofBytes (interleave 8 0 (xlo s n) (xlo s m))), t, instruction_next htf hdec ?_, xsOf_with _ _ _ _⟩
  simp only [exec, execSse, Sem.punpcklbw, packedOp, packed, aligned16, bind, Prog.bind, readOp,
    Bool.false_eq_true, ↓reduceIte, pure, Prog.run, writeOp, Prog.readZmm]
  rfl

theorem VOpI.punpcklwd {w n m len : Nat} :
    VOpI prof (mk (.sse .punpcklwd) w [.xmm n, .xmm m] len) (VOp.punpcklwd n m) := by
  intro s o t htf _ hdec _ _
  refine ⟨withZmm s.cpu.vec.zmm (xmmOf n) ((s.cpu.vec.zmm (xmmOf n)).extractLsb' 128 384 ++
    ofWords (interleave 16 0 (xlo s n) (xlo s m))), t, instruction_next htf hdec ?_, xsOf_with _ _ _ _⟩
  simp only [exec, execSse, Sem.punpcklwd, packedOp, packed, aligned16, bind, Prog.bind, readOp,
    Bool.false_eq_true, ↓reduceIte, pure, Prog.run, writeOp, Prog.readZmm]
  rfl

theorem VOpI.pshufd {w n m k len : Nat} :
    VOpI prof (mk (.sse .pshufd) w [.xmm n, .xmm m, .imm 8 k] len) (VOp.pshufd n m k) := by
  intro s o t htf _ hdec _ _
  refine ⟨withZmm s.cpu.vec.zmm (xmmOf n) ((s.cpu.vec.zmm (xmmOf n)).extractLsb' 128 384 ++
    ofDwords fun j => lane 32 (xlo s m) (k / 4 ^ j % 4)), t, instruction_next htf hdec ?_, xsOf_with _ _ _ _⟩
  simp only [exec, execSse, Sem.pshufd, aligned16, bind, Prog.bind, readOp, Bool.false_eq_true, ↓reduceIte, pure,
    Prog.run, writeOp, Prog.readZmm]
  rfl

theorem VOpI.movdqa {w n m len : Nat} :
    VOpI prof (mk (.sse .movdqa) w [.xmm n, .xmm m] len) (VOp.movdqa n m) := by
  intro s o t htf _ hdec _ _
  refine ⟨withZmm s.cpu.vec.zmm (xmmOf n) ((s.cpu.vec.zmm (xmmOf n)).extractLsb' 128 384 ++ xlo s m),
    t, instruction_next htf hdec ?_, xsOf_with _ _ _ _⟩
  simp only [exec, execSse, Sem.movdqa, moveAligned, aligned16, bind, Prog.bind, readOp, Bool.false_eq_true,
    ↓reduceIte, pure, Prog.run, writeOp, Prog.readZmm]
  rfl

theorem VOpI.pminub {w n m len : Nat} :
    VOpI prof (mk (.sse (.pminu 8)) w [.xmm n, .xmm m] len) (VOp.pminub n m) := by
  intro s o t htf _ hdec _ _
  refine ⟨withZmm s.cpu.vec.zmm (xmmOf n) ((s.cpu.vec.zmm (xmmOf n)).extractLsb' 128 384 ++
    pminb (xlo s n) (xlo s m)), t, instruction_next htf hdec ?_, xsOf_with _ _ _ _⟩
  simp only [exec, execSse, Sem.pminu, packedOp, packed, aligned16, bind,
    Prog.bind, readOp, Bool.false_eq_true, ↓reduceIte, pure, Prog.run, writeOp, Prog.readZmm]
  rfl

/-! ## The spread byte -/

theorem extractLsb'_extractLsb'' {w s l s' l' : Nat} (x : BitVec w) (h : s' + l' ≤ l) :
    (x.extractLsb' s l).extractLsb' s' l' = x.extractLsb' (s + s') l' := by
  ext k hk
  simp [show s' + k < l by omega, Nat.add_assoc]

/-- A lane of `k` bits inside a lane of `K` bits. -/
theorem lane_in {k K : Nat} (x : BitVec 128) (i q r : Nat) (hr : k * r + k ≤ K) (hi : k * i = K * q + k * r) :
    lane k x i = (lane K x q).extractLsb' (k * r) k := by
  unfold lane
  rw [extractLsb'_extractLsb'' _ hr, hi]

theorem lane_ofWords (f : Nat → BitVec 16) {j : Nat} (hj : j < 8) : lane 16 (ofWords f) j = f j := by
  have : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 := by omega
  rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  simp (disch := omega) only [lane, ofWords, BitVec.extractLsb'_append_eq_of_le, BitVec.extractLsb'_append_eq_right,
    BitVec.extractLsb'_eq_self, Nat.mul_zero, Nat.reduceMul, Nat.reduceSub]

theorem lane_ofDwords (f : Nat → BitVec 32) {j : Nat} (hj : j < 4) : lane 32 (ofDwords f) j = f j := by
  have : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by omega
  rcases this with rfl | rfl | rfl | rfl <;>
  simp (disch := omega) only [lane, ofDwords, BitVec.extractLsb'_append_eq_of_le, BitVec.extractLsb'_append_eq_right,
    BitVec.extractLsb'_eq_self, Nat.mul_zero, Nat.reduceMul, Nat.reduceSub]

theorem interleave_self (k h : Nat) (a : BitVec 128) (j : Nat) : interleave k h a a j = lane k a (h + j / 2) := by
  simp only [interleave, ite_self]

/-- `movd`, `punpcklbw`, `punpcklwd`, `pshufd 0` of one register: each byte the source's low byte. -/
theorem lane_bcast (c : BitVec 64) {i : Nat} (hi : i < 16) :
    lane 8 (ofDwords fun j => lane 32 (ofWords (interleave 16 0
      (ofBytes (interleave 8 0 ((c.setWidth 32).setWidth 128) ((c.setWidth 32).setWidth 128)))
      (ofBytes (interleave 8 0 ((c.setWidth 32).setWidth 128) ((c.setWidth 32).setWidth 128))))) (0 / 4 ^ j % 4)) i =
      c.setWidth 8 := by
  generalize hX : (c.setWidth 32).setWidth 128 = X
  generalize hB : ofBytes (interleave 8 0 X X) = B
  generalize hW : ofWords (interleave 16 0 B B) = W
  have h1 : lane 8 (ofDwords fun j => lane 32 W (0 / 4 ^ j % 4)) i = (lane 32 W 0).extractLsb' (8 * (i % 4)) 8 := by
    rw [lane_in (k := 8) (K := 32) _ i (i / 4) (i % 4) (by omega) (by omega), lane_ofDwords (j := i / 4) _ (by omega)]
    simp only [Nat.zero_div, Nat.zero_mod]
  have h2 : (lane 32 W 0).extractLsb' (8 * (i % 4)) 8 = lane 8 W (i % 4) :=
    (lane_in (k := 8) (K := 32) W (i % 4) 0 (i % 4) (by omega) (by omega)).symm
  have h3 : lane 8 W (i % 4) = (lane 16 B 0).extractLsb' (8 * (i % 2)) 8 := by
    rw [lane_in (k := 8) (K := 16) W (i % 4) (i % 4 / 2) (i % 2) (by omega) (by omega), ← hW,
      lane_ofWords (j := i % 4 / 2) _ (by omega), interleave_self, show 0 + i % 4 / 2 / 2 = 0 by omega]
  have h4 : (lane 16 B 0).extractLsb' (8 * (i % 2)) 8 = lane 8 X 0 := by
    rw [← lane_in (k := 8) (K := 16) B (i % 2) 0 (i % 2) (by omega) (by omega), ← hB,
      lane_ofBytes (j := i % 2) _ (by omega), interleave_self, show 0 + i % 2 / 2 = 0 by omega]
  rw [h1, h2, h3, h4, ← hX]
  ext k hk
  simp [lane, show k < 32 by omega, show k < 128 by omega]

end FV7z
