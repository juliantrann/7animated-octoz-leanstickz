import FV7z.Lemmas.InsFn
/-!
# Instructions on memory words and the rest of `get_common_indices` (PLAN.md G2, "Dispatch theo CPUID", glibc)

The forms glibc 2.31's `init_cpu_features` in `7zzs` uses, beside those of `Ins.lean`, `InsRip.lean`, `InsFn.lean`:
`or dword [rip + d], imm` (a read-modify-write), `cmp` of a memory word, `add` with a memory word, `mov` of an
immediate to memory, `lea r64, [b + d]`, `test r64, r64`, `bt r32, r32`, `and r8, imm8`.
-/
namespace FV7z
open ZellicX86 Decode

variable {prof : Profile} {o : Oracle} {t : Nat} {s : State}

/-- `or dword [rip + d], imm32`: `AF` undefined. -/
theorem or_m32i_rip {d imm len : Nat} (htf : s.cpu.rflags.tf = false) (hac : s.cpu.rflags.ac = false)
    (hdec : Decode.decode prof.feat (fetchByte prof.feat s) = .ok (mk .or 32 [.mem (mrip d 32), .imm 32 imm] len))
    (hwr : Writable prof s (eaR s len d) 4) :
    ∃ af t', (instruction prof s).runStream o t = (.running (nx (st s (eaR s len d)
      (toBytesLE (ofBytesLE 32 (readBytes s.proc.mm.mem (eaR s len d) 4) ||| BitVec.ofNat 32 imm) 4)) len s.cpu.gpr
      ((rf0 s).arith (ofBytesLE 32 (readBytes s.proc.mm.mem (eaR s len d) 4) ||| BitVec.ofNat 32 imm) false false af))
      none, t') :=
  ⟨_, _, instruction_next htf hdec (by
  have hc := checkAccess_ok (s := advance s len) (feat := prof.feat) (m := ⟨eaR s len d, false⟩) (acc := .write)
    (n := 4) hac hwr
  have hp : ∀ {α : Type} (x : α), Req.runStream o (pure x : Req α) t = (x, t) := fun _ => rfl
  simp only [exec, Sem.or, alu, logicOp, mk, mrip, bind, Prog.bind, readOp, Bool.false_eq_true, ↓reduceIte,
    memRef, effOffset, pure, Prog.readRip, Prog.read, Prog.run, BitVec.mul_one, writeOp]
  rw [eaR_adv, checkAccess_ok (s := advance s len) hac hwr, Req.runStream_bind]
  simp only [hp, Prog.run, Prog.readFlags, Prog.undefinedBit, Prog.write, Prog.writeFlags, Prog.bind,
    Prog.undefined, Nat.reduceDiv]
  simp only [Prog.bind, Prog.run, Req.runStream, bind, pure]
  simp only [Prog.run, eaR_adv, Bool.not_true, Bool.and_false, Bool.false_and, Nat.reduceDiv, hc]
  rfl)⟩

/-- `cmp dword [rip + d], imm32`. -/
theorem cmp_m32i_rip {d imm len : Nat} (htf : s.cpu.rflags.tf = false) (hac : s.cpu.rflags.ac = false)
    (hdec : Decode.decode prof.feat (fetchByte prof.feat s) = .ok (mk .cmp 32 [.mem (mrip d 32), .imm 32 imm] len))
    (hld : Readable prof s (eaR s len d) 4) :
    (instruction prof s).runStream o t = (.running (nx s len s.cpu.gpr
      (subF (rf0 s) (ofBytesLE 32 (readBytes s.proc.mm.mem (eaR s len d) 4)) (BitVec.ofNat 32 imm))) none, t) := by
  refine instruction_next htf hdec ?_
  simp only [exec, Sem.cmp, alu, subOp, mk, mrip, bind, Prog.bind, readOp, Bool.false_eq_true, ↓reduceIte,
    memRef, effOffset, pure, Prog.readRip, Prog.read, Prog.run, BitVec.mul_one]
  rw [eaR_adv, checkAccess_ok (s := advance s len) hac hld]
  rfl

/-- `cmp dword [b + d], imm32`. -/
theorem cmp_m32i {b d imm len : Nat} (htf : s.cpu.rflags.tf = false) (hac : s.cpu.rflags.ac = false)
    (hdec : Decode.decode prof.feat (fetchByte prof.feat s) = .ok (mk .cmp 32 [.mem (mbd b d 32), .imm 32 imm] len))
    (hld : Readable prof s (eaD s b d) 4) :
    (instruction prof s).runStream o t = (.running (nx s len s.cpu.gpr
      (subF (rf0 s) (ofBytesLE 32 (readBytes s.proc.mm.mem (eaD s b d) 4)) (BitVec.ofNat 32 imm))) none, t) := by
  refine instruction_next htf hdec ?_
  simp only [exec, Sem.cmp, alu, subOp, mk, mbd, bind, Prog.bind, readOp, Bool.false_eq_true, ↓reduceIte,
    memRef, effOffset, pure, Prog.readReg, Prog.read, Prog.run, BitVec.mul_one]
  rw [eaD_adv, checkAccess_ok (s := advance s len) hac hld]
  rfl

/-- `add r32, dword [b + d]`. -/
theorem add_rm32 {r b d len : Nat} (htf : s.cpu.rflags.tf = false) (hac : s.cpu.rflags.ac = false)
    (hdec : Decode.decode prof.feat (fetchByte prof.feat s) = .ok (mk .add 32 [gr 32 r, .mem (mbd b d 32)] len))
    (hld : Readable prof s (eaD s b d) 4) :
    (instruction prof s).runStream o t = (.running (nx s len
      (s.cpu.gpr.set (regOf r) ((addR (rv s 32 r) (ofBytesLE 32 (readBytes s.proc.mm.mem (eaD s b d) 4))).setWidth 64))
      (addF (rf0 s) (rv s 32 r) (ofBytesLE 32 (readBytes s.proc.mm.mem (eaD s b d) 4)))) none, t) := by
  refine instruction_next htf hdec ?_
  simp only [exec, Sem.add, alu, addOp, mk, mbd, gr, bind, Prog.bind, readOp, Bool.false_eq_true, ↓reduceIte,
    memRef, effOffset, pure, Prog.readReg, Prog.read, Prog.run, BitVec.mul_one, writeOp]
  rw [eaD_adv, checkAccess_ok (s := advance s len) hac hld]
  rfl

/-- `mov dword [b + d], imm32`. -/
theorem mov_mi32 {b d imm len : Nat} (htf : s.cpu.rflags.tf = false) (hac : s.cpu.rflags.ac = false)
    (hdec : Decode.decode prof.feat (fetchByte prof.feat s) = .ok (mk .mov 32 [.mem (mbd b d 32), .imm 32 imm] len))
    (hwr : Writable prof s (eaD s b d) 4) :
    (instruction prof s).runStream o t = (.running (nx (st s (eaD s b d) (toBytesLE (BitVec.ofNat 32 imm) 4)) len
      s.cpu.gpr (rf0 s)) none, t) := by
  refine instruction_next htf hdec ?_
  simp only [exec, Sem.mov, mk, mbd, bind, Prog.bind, readOp, Bool.false_eq_true, ↓reduceIte, memRef,
    effOffset, pure, Prog.readReg, Prog.write, Prog.run, writeOp, BitVec.mul_one]
  rw [eaD_adv, checkAccess_ok (s := advance s len) hac hwr]
  rfl

/-- `lea r64, [b + d]`. -/
theorem lea_bd {r b d len : Nat} (htf : s.cpu.rflags.tf = false)
    (hdec : Decode.decode prof.feat (fetchByte prof.feat s) = .ok (mk .lea 64 [gr 64 r, .mem (mbd b d 0)] len)) :
    (instruction prof s).runStream o t = (.running (nx s len (s.cpu.gpr.set (regOf r) (eaD s b d)) (rf0 s)) none, t) := by
  refine instruction_next htf hdec ?_
  simp only [exec, Sem.lea, mk, mbd, gr, effOffset, Prog.run, bind, Prog.bind, pure, Prog.readReg, Bool.false_eq_true,
    ↓reduceIte, writeOp, BitVec.mul_one, BitVec.setWidth_eq]
  rw [eaD_adv]
  rfl

/-- `add dword [b + d], r32`: a read-modify-write. -/
theorem add_mr32 {b d r len : Nat} (htf : s.cpu.rflags.tf = false) (hac : s.cpu.rflags.ac = false)
    (hdec : Decode.decode prof.feat (fetchByte prof.feat s) = .ok (mk .add 32 [.mem (mbd b d 32), gr 32 r] len))
    (hwr : Writable prof s (eaD s b d) 4) :
    (instruction prof s).runStream o t = (.running (nx (st s (eaD s b d)
      (toBytesLE (addR (ofBytesLE 32 (readBytes s.proc.mm.mem (eaD s b d) 4)) (rv s 32 r)) 4)) len s.cpu.gpr
      (addF (rf0 s) (ofBytesLE 32 (readBytes s.proc.mm.mem (eaD s b d) 4)) (rv s 32 r))) none, t) := by
  refine instruction_next htf hdec ?_
  have hc := checkAccess_ok (s := advance s len) (feat := prof.feat)
    (m := ⟨eaD s b d, (some b == some 4 || some b == some 5) && !false && !false⟩) (acc := .write) (n := 4) hac hwr
  have hp : ∀ {α : Type} (x : α), Req.runStream o (pure x : Req α) t = (x, t) := fun _ => rfl
  simp only [exec, Sem.add, alu, addOp, mk, mbd, gr, bind, Prog.bind, readOp, Bool.false_eq_true, ↓reduceIte,
    memRef, effOffset, pure, Prog.readReg, Prog.read, Prog.run, BitVec.mul_one, writeOp]
  rw [eaD_adv, checkAccess_ok (s := advance s len) hac hwr, Req.runStream_bind]
  simp only [hp, Prog.run, Prog.readFlags, Prog.write, Prog.writeFlags, Prog.bind, Nat.reduceDiv]
  simp only [Prog.bind, Prog.run, Req.runStream, bind, pure]
  simp only [Prog.run, eaD_adv, Nat.reduceDiv]
  rw [hc]
  rfl

/-- The instruction `i` writes at most the status flags: never `TF`, `AC` or `DF`. -/
def FL (prof : Profile) (i : Inst) : Prop :=
  ∀ (s : State) (o : Oracle) (t : Nat), s.cpu.rflags.tf = false →
    Decode.decode prof.feat (fetchByte prof.feat s) = .ok i →
    ∃ fl t', (instruction prof s).runStream o t = (.running (nx s i.len s.cpu.gpr fl) none, t') ∧
      fl.tf = s.cpu.rflags.tf ∧ fl.ac = s.cpu.rflags.ac ∧ fl.df = s.cpu.rflags.df

theorem fl_test_rr64 {r q len : Nat} : FL prof (mk .test 64 [gr 64 r, gr 64 q] len) :=
  fun _ _ _ htf hdec => ⟨_, _, instruction_next htf hdec rfl, rfl, rfl, rfl⟩

theorem fl_bt_rr32 {r q len : Nat} : FL prof (mk (.bit .bt) 32 [gr 32 r, gr 32 q] len) :=
  fun _ _ _ htf hdec => ⟨_, _, instruction_next htf hdec rfl, rfl, rfl, rfl⟩

theorem fl_cmp_ri32 {r imm len : Nat} : FL prof (mk .cmp 32 [gr 32 r, .imm 32 imm] len) :=
  fun _ _ _ htf hdec => ⟨_, _, instruction_next htf hdec rfl, rfl, rfl, rfl⟩

theorem fl_test_ri32 {r imm len : Nat} : FL prof (mk .test 32 [gr 32 r, .imm 32 imm] len) :=
  fun _ _ _ htf hdec => ⟨_, _, instruction_next htf hdec rfl, rfl, rfl, rfl⟩

theorem fl_test_rr32 {r q len : Nat} : FL prof (mk .test 32 [gr 32 r, gr 32 q] len) :=
  fun _ _ _ htf hdec => ⟨_, _, instruction_next htf hdec rfl, rfl, rfl, rfl⟩

theorem fl_test_h8i {r imm len : Nat} : FL prof (mk .test 8 [gh r, .imm 8 imm] len) :=
  fun _ _ _ htf hdec => ⟨_, _, instruction_next htf hdec rfl, rfl, rfl, rfl⟩

theorem fl_test_r8i {r imm len : Nat} : FL prof (mk .test 8 [gr 8 r, .imm 8 imm] len) :=
  fun _ _ _ htf hdec => ⟨_, _, instruction_next htf hdec rfl, rfl, rfl, rfl⟩

end FV7z
