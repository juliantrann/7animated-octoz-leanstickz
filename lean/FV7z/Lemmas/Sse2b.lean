import FV7z.Lemmas.Sse2
/-!
# More SSE2 steps (PLAN.md G2, `__strrchr_sse2`)

`__strrchr_sse2` spreads the byte it looks for over the 16 bytes of `xmm1` (`movd xmm1, esi`, `punpcklbw xmm1, xmm1`,
`punpcklwd xmm1, xmm1`, `pshufd xmm1, xmm1, 0`), and copies and folds vectors between registers (`movdqa xmmN, xmmM`,
`pminub xmmN, xmmM`). Their `VOp`s and `VOpI`s, as `Lemmas/Sse2.lean`'s.
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
  simp only [exec, execSse, Sem.movd, moveBits, mk, gr, bind, Prog.bind, readOp, Bool.false_eq_true, ↓reduceIte,
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
  simp only [exec, execSse, Sem.pminu, if_pos (show (8 : Nat) = 8 from rfl), packedOp, packed, aligned16, bind,
    Prog.bind, readOp, Bool.false_eq_true, ↓reduceIte, pure, Prog.run, writeOp, Prog.readZmm]
  rfl

end FV7z
