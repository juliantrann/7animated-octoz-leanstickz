import FV7z.Lemmas.Sse2c
/-!
# The SSE2 steps of `__strncmp_sse2` (PLAN.md G3, `strncmp`)

`__strncmp_sse2` loads its first 16 bytes 8 at a time (`movlpd xmmN, [b]`, `movhpd xmmN, [b + 8]`), its aligned
vectors at `[b + i]` (`movdqa xmmN, [b + i]`), marks the bytes that end the comparison by `pcmpeqb` and `psubb`, and
lines up the vector of one string with the other's by byte shifts (`psrldq`, `pslldq`, `por`). Its `VOp`s and
`VOpI`s, as `Lemmas/Sse2.lean`'s, and `xchg` of two registers as an `Op`.

- `psb`: the bytewise differences `psubb` writes.
- `VOp.psubb`, `VOp.por`, `VOp.psrldq`, `VOp.pslldq`, `VOp.movlpd_m`, `VOp.movhpd_m`, `VOp.movdqa_mi`.
- `Op.xchg`, `OpI.xchg`: `xchg r, r'` of 32 or 64 bits.
-/
namespace FV7z
open ZellicX86 Decode

/-- The bytewise differences, wrapping. -/
def psb (a b : BitVec 128) : BitVec 128 := ofBytes fun j => lane 8 a j - lane 8 b j

namespace VOp

/-- `psubb xmmN, xmmM`. -/
def psubb (n m : Nat) : VOp :=
  .v 0 false (fun _ => 0) (fun g _ _ => g) fun _ x _ => xset x (xmmOf n) (psb (x (xmmOf n)) (x (xmmOf m)))
/-- `por xmmN, xmmM`. -/
def por (n m : Nat) : VOp :=
  .v 0 false (fun _ => 0) (fun g _ _ => g) fun _ x _ => xset x (xmmOf n) (x (xmmOf n) ||| x (xmmOf m))
/-- `psrldq xmmN, k`: the register shifted right by `k` bytes. -/
def psrldq (n k : Nat) : VOp :=
  .v 0 false (fun _ => 0) (fun g _ _ => g) fun _ x _ => xset x (xmmOf n) (x (xmmOf n) >>> (8 * k))
/-- `pslldq xmmN, k`: the register shifted left by `k` bytes. -/
def pslldq (n k : Nat) : VOp :=
  .v 0 false (fun _ => 0) (fun g _ _ => g) fun _ x _ => xset x (xmmOf n) (x (xmmOf n) <<< (8 * k))
/-- `movlpd xmmN, qword [b + d]`: the low 8 bytes loaded, the high 8 kept. -/
def movlpd_m (n b d : Nat) : VOp :=
  .v 8 false (fun g => eaB g b d) (fun g _ _ => g) fun _ x bs =>
    xset x (xmmOf n) (lane 64 (x (xmmOf n)) 1 ++ ofBytesLE 64 bs)
/-- `movhpd xmmN, qword [b + d]`: the high 8 bytes loaded, the low 8 kept. -/
def movhpd_m (n b d : Nat) : VOp :=
  .v 8 false (fun g => eaB g b d) (fun g _ _ => g) fun _ x bs =>
    xset x (xmmOf n) (ofBytesLE 64 bs ++ lane 64 (x (xmmOf n)) 0)
/-- `movdqa xmmN, [b + i]`. -/
def movdqa_mi (n b i : Nat) : VOp :=
  .v 16 true (fun g => eaBI g b i 0) (fun g _ _ => g) fun _ x bs => xset x (xmmOf n) (ofBytesLE 128 bs)

end VOp

variable {prof : Profile}

theorem VOpI.psubb {w n m len : Nat} :
    VOpI prof (mk (.sse .psubb) w [.xmm n, .xmm m] len) (VOp.psubb n m) := by
  intro s o t htf _ hdec _ _
  refine ⟨withZmm s.cpu.vec.zmm (xmmOf n) ((s.cpu.vec.zmm (xmmOf n)).extractLsb' 128 384 ++ psb (xlo s n) (xlo s m)),
    t, instruction_next htf hdec ?_, xsOf_with _ _ _ _⟩
  simp only [exec, execSse, Sem.psubb, packedOp, packed, aligned16, bind, Prog.bind, readOp,
    Bool.false_eq_true, ↓reduceIte, pure, Prog.run, writeOp, Prog.readZmm]
  rfl

theorem VOpI.por {w n m len : Nat} :
    VOpI prof (mk (.sse .por) w [.xmm n, .xmm m] len) (VOp.por n m) := by
  intro s o t htf _ hdec _ _
  refine ⟨withZmm s.cpu.vec.zmm (xmmOf n) ((s.cpu.vec.zmm (xmmOf n)).extractLsb' 128 384 ++ (xlo s n ||| xlo s m)),
    t, instruction_next htf hdec ?_, xsOf_with _ _ _ _⟩
  simp only [exec, execSse, Sem.por, packedOp, packed, aligned16, bind, Prog.bind, readOp,
    Bool.false_eq_true, ↓reduceIte, pure, Prog.run, writeOp, Prog.readZmm]
  rfl

theorem VOpI.psrldq {w n k len : Nat} :
    VOpI prof (mk (.sse .psrldq) w [.xmm n, .imm 8 k] len) (VOp.psrldq n k) := by
  intro s o t htf _ hdec _ _
  refine ⟨withZmm s.cpu.vec.zmm (xmmOf n) ((s.cpu.vec.zmm (xmmOf n)).extractLsb' 128 384 ++ (xlo s n >>> (8 * k))),
    t, instruction_next htf hdec ?_, xsOf_with _ _ _ _⟩
  simp only [exec, execSse, Sem.psrldq, shiftBy, bind, Prog.bind, readOp, Bool.false_eq_true, ↓reduceIte, pure,
    Prog.run, writeOp, Prog.readZmm]
  rfl

theorem VOpI.pslldq {w n k len : Nat} :
    VOpI prof (mk (.sse .pslldq) w [.xmm n, .imm 8 k] len) (VOp.pslldq n k) := by
  intro s o t htf _ hdec _ _
  refine ⟨withZmm s.cpu.vec.zmm (xmmOf n) ((s.cpu.vec.zmm (xmmOf n)).extractLsb' 128 384 ++ (xlo s n <<< (8 * k))),
    t, instruction_next htf hdec ?_, xsOf_with _ _ _ _⟩
  simp only [exec, execSse, Sem.pslldq, shiftBy, bind, Prog.bind, readOp, Bool.false_eq_true, ↓reduceIte, pure,
    Prog.run, writeOp, Prog.readZmm]
  rfl

theorem VOpI.movlpd_m {w n b d len : Nat} :
    VOpI prof (mk (.sse .movlpd) w [.xmm n, .mem (mbd b d 64)] len) (VOp.movlpd_m n b d) := by
  intro s o t htf hac hdec hld _
  refine ⟨withZmm s.cpu.vec.zmm (xmmOf n) ((s.cpu.vec.zmm (xmmOf n)).extractLsb' 128 384 ++
    (lane 64 (xlo s n) 1 ++ ofBytesLE 64 (readBytes s.proc.mm.mem (eaD s b d) 8))),
    t, instruction_next htf hdec ?_, xsOf_with _ _ _ _⟩
  simp only [exec, execSse, Sem.movlpd, Sem.movlps, mbd, bind, Prog.bind, readOp, Bool.false_eq_true, ↓reduceIte,
    memRef, effOffset, pure, Prog.readReg, Prog.read, Prog.run, BitVec.mul_one, writeOp, Prog.readZmm]
  rw [eaD_adv, checkAccess_ok (s := advance s len) hac hld]
  rfl

theorem VOpI.movhpd_m {w n b d len : Nat} :
    VOpI prof (mk (.sse .movhpd) w [.xmm n, .mem (mbd b d 64)] len) (VOp.movhpd_m n b d) := by
  intro s o t htf hac hdec hld _
  refine ⟨withZmm s.cpu.vec.zmm (xmmOf n) ((s.cpu.vec.zmm (xmmOf n)).extractLsb' 128 384 ++
    (ofBytesLE 64 (readBytes s.proc.mm.mem (eaD s b d) 8) ++ lane 64 (xlo s n) 0)),
    t, instruction_next htf hdec ?_, xsOf_with _ _ _ _⟩
  simp only [exec, execSse, Sem.movhpd, Sem.movhps, mbd, bind, Prog.bind, readOp, Bool.false_eq_true, ↓reduceIte,
    memRef, effOffset, pure, Prog.readReg, Prog.read, Prog.run, BitVec.mul_one, writeOp, Prog.readZmm]
  rw [eaD_adv, checkAccess_ok (s := advance s len) hac hld]
  rfl

/-- `[b + i + d]` after `rip` moves: as before. -/
theorem eaI_adv (s : State) (len b i d : Nat) :
    (advance s len).cpu.gpr.get (regOf b) + (advance s len).cpu.gpr.get (regOf i) + BitVec.ofNat 64 d =
      eaI s b i d := rfl

theorem VOpI.movdqa_mi {w n b i len : Nat} :
    VOpI prof (mk (.sse .movdqa) w [.xmm n, .mem (mbi b i 0 128)] len) (VOp.movdqa_mi n b i) := by
  intro s o t htf hac hdec hld hal
  have hal' : (eaI s b i 0).toNat % 16 = 0 := hal rfl
  refine ⟨withZmm s.cpu.vec.zmm (xmmOf n) ((s.cpu.vec.zmm (xmmOf n)).extractLsb' 128 384 ++
    ofBytesLE 128 (readBytes s.proc.mm.mem (eaI s b i 0) 16)),
    t, instruction_next htf hdec ?_, xsOf_with _ _ _ _⟩
  simp only [exec, execSse, Sem.movdqa, moveAligned, aligned16, Prog.alignedTo, mk, mbi, bind, Prog.bind, readOp,
    Bool.false_eq_true, ↓reduceIte, memRef, effOffset, pure, Prog.readReg, Prog.read, Prog.run, BitVec.mul_one,
    writeOp, Prog.readZmm, eaI_adv, hal', true_or]
  rw [checkAccess_ok (s := advance s len) hac hld]
  rfl

/-- `xchg r, r'` of `w` bits: each written with the other's value, zero-extended. -/
def Op.xchg (w r q : Nat) : Op :=
  .reg (fun g _ => wr (wr g r (gv g w q)) q (gv g w r)) fun _ f fl => fl = rfz f

theorem OpI.xchg {w r q len : Nat} (hw : w = 32 ∨ w = 64) :
    OpI prof (mk .xchg w [gr w r, gr w q] len) (Op.xchg w r q) := fun s o t htf hdec => by
  rcases hw with rfl | rfl <;> exact ⟨_, _, instruction_next htf hdec rfl, rfl, rfl, rfl, rfl⟩

end FV7z
