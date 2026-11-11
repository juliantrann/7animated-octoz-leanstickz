import FV7z.Lemmas.Ins
/-!
# Instructions with a `rip`-relative operand, an immediate move, `test`, a high-byte register, `cmov` (PLAN.md G2,
"Dispatch theo CPUID")

The forms glibc's IFUNC resolvers in `7zzs` use, beside those of `Ins.lean`: they read the words of
`_dl_x86_cpu_features` at fixed addresses (`[rip + d]`), test bits of them, and pick an address (`lea [rip + d]`,
`cmovcc`).
-/
namespace FV7z
open ZellicX86 Decode

/-- The memory operand `[rip + disp]` of `width` bits. -/
def mrip (disp width : Nat) : MemOp :=
  { seg := none, base := none, index := none, scale := 1, disp, ripRel := true, addr32 := false, width }

/-- The high byte (`ah`, `ch`, `dh`, `bh`) of general register `n`. -/
def gh (n : Nat) : Opd := .reg ⟨8, n, true⟩

/-- The address `[rip + d]` of an instruction of `len` bytes at `s`'s `rip`. -/
abbrev eaR (s : State) (len d : Nat) : Addr := s.cpu.rip.add len + BitVec.ofNat 64 d

variable {prof : Profile} {o : Oracle} {t : Nat} {s : State}

theorem eaR_adv (s : State) (len d : Nat) :
    (advance s len).cpu.rip + 0 + BitVec.ofNat 64 d = eaR s len d := by
  show s.cpu.rip.add len + (0 : BitVec 64) + _ = _
  simp

/-- `mov r64, imm64`. -/
theorem mov_ri64 {r imm len : Nat} (htf : s.cpu.rflags.tf = false)
    (hdec : Decode.decode prof.feat (fetchByte prof.feat s) = .ok (mk .mov 64 [gr 64 r, .imm 64 imm] len)) :
    (instruction prof s).runStream o t =
      (.running (nx s len (s.cpu.gpr.set (regOf r) (BitVec.ofNat 64 imm)) (rf0 s)) none, t) :=
  instruction_next htf hdec rfl

/-- `lea r64, [rip + d]`. -/
theorem lea_rip {r d len : Nat} (htf : s.cpu.rflags.tf = false)
    (hdec : Decode.decode prof.feat (fetchByte prof.feat s) = .ok (mk .lea 64 [gr 64 r, .mem (mrip d 0)] len)) :
    (instruction prof s).runStream o t =
      (.running (nx s len (s.cpu.gpr.set (regOf r) (eaR s len d)) (rf0 s)) none, t) := by
  refine instruction_next htf hdec ?_
  simp only [exec, Sem.lea, mk, mrip, gr, effOffset, Prog.run, bind, Prog.bind, pure, Prog.readRip,
    Bool.false_eq_true, ↓reduceIte, writeOp, BitVec.mul_one, BitVec.setWidth_eq]
  rw [eaR_adv]
  rfl

/-- `mov r32, dword [rip + d]`. -/
theorem mov_r32_rip {r d len : Nat} (htf : s.cpu.rflags.tf = false) (hac : s.cpu.rflags.ac = false)
    (hdec : Decode.decode prof.feat (fetchByte prof.feat s) = .ok (mk .mov 32 [gr 32 r, .mem (mrip d 32)] len))
    (hld : Readable prof s (eaR s len d) 4) :
    (instruction prof s).runStream o t = (.running (nx s len (s.cpu.gpr.set (regOf r)
      ((ofBytesLE 32 (readBytes s.proc.mm.mem (eaR s len d) 4)).setWidth 64)) (rf0 s)) none, t) := by
  refine instruction_next htf hdec ?_
  simp only [exec, Sem.mov, mk, mrip, gr, bind, Prog.bind, readOp, Bool.false_eq_true, ↓reduceIte, memRef,
    effOffset, pure, Prog.readRip, Prog.read, Prog.run, Opd.width, writeOp, BitVec.mul_one]
  rw [eaR_adv, checkAccess_ok (s := advance s len) hac hld]
  rfl

/-- `and r64, qword [rip + d]`: `AF` undefined. -/
theorem and_r64_rip {r d len : Nat} (htf : s.cpu.rflags.tf = false) (hac : s.cpu.rflags.ac = false)
    (hdec : Decode.decode prof.feat (fetchByte prof.feat s) = .ok (mk .and 64 [gr 64 r, .mem (mrip d 64)] len))
    (hld : Readable prof s (eaR s len d) 8) :
    ∃ af t', (instruction prof s).runStream o t = (.running (nx s len (s.cpu.gpr.set (regOf r)
      ((rv s 64 r &&& ofBytesLE 64 (readBytes s.proc.mm.mem (eaR s len d) 8)).setWidth 64))
      ((rf0 s).arith (rv s 64 r &&& ofBytesLE 64 (readBytes s.proc.mm.mem (eaR s len d) 8)) false false af))
      none, t') :=
  ⟨_, _, instruction_next htf hdec (by
  simp only [exec, Sem.and, alu, logicOp, mk, mrip, gr, bind, Prog.bind, readOp, Prog.readReg, Bool.false_eq_true, ↓reduceIte,
    memRef, effOffset, pure, Prog.readRip, Prog.read, Prog.run, Opd.width, writeOp, BitVec.mul_one]
  rw [eaR_adv, checkAccess_ok (s := advance s len) hac hld]
  rfl)⟩

/-- `test r32, imm32`: `AF` undefined. -/
theorem test_ri32 {r imm len : Nat} (htf : s.cpu.rflags.tf = false)
    (hdec : Decode.decode prof.feat (fetchByte prof.feat s) = .ok (mk .test 32 [gr 32 r, .imm 32 imm] len)) :
    ∃ af t', (instruction prof s).runStream o t = (.running (nx s len s.cpu.gpr
      ((rf0 s).arith (rv s 32 r &&& BitVec.ofNat 32 imm) false false af)) none, t') :=
  ⟨_, _, instruction_next htf hdec rfl⟩

/-- `test r32, r32'`: `AF` undefined. -/
theorem test_rr32 {r q len : Nat} (htf : s.cpu.rflags.tf = false)
    (hdec : Decode.decode prof.feat (fetchByte prof.feat s) = .ok (mk .test 32 [gr 32 r, gr 32 q] len)) :
    ∃ af t', (instruction prof s).runStream o t = (.running (nx s len s.cpu.gpr
      ((rf0 s).arith (rv s 32 r &&& rv s 32 q) false false af)) none, t') :=
  ⟨_, _, instruction_next htf hdec rfl⟩

/-- `and r8h, imm8` (`ah`, `ch`, `dh`, `bh`): the other bits kept; `AF` undefined. -/
theorem and_h8i {r imm len : Nat} (htf : s.cpu.rflags.tf = false)
    (hdec : Decode.decode prof.feat (fetchByte prof.feat s) = .ok (mk .and 8 [gh r, .imm 8 imm] len)) :
    ∃ af t', (instruction prof s).runStream o t = (.running (nx s len (s.cpu.gpr.set (regOf r)
      ((s.cpu.gpr.get (regOf r) &&& ~~~(BitVec.ofNat 64 ((2 ^ 8 - 1) * 2 ^ 8))) |||
        ((((s.cpu.gpr.get (regOf r)) >>> 8).setWidth 8 &&& BitVec.ofNat 8 imm).setWidth 64 <<< 8)))
      ((rf0 s).arith (((s.cpu.gpr.get (regOf r)) >>> 8).setWidth 8 &&& BitVec.ofNat 8 imm) false false af))
      none, t') :=
  ⟨_, _, instruction_next htf hdec rfl⟩

/-- `test byte [rip + d], imm8`: `AF` undefined. -/
theorem test_m8i_rip {d imm len : Nat} (htf : s.cpu.rflags.tf = false) (hac : s.cpu.rflags.ac = false)
    (hdec : Decode.decode prof.feat (fetchByte prof.feat s) = .ok (mk .test 8 [.mem (mrip d 8), .imm 8 imm] len))
    (hld : Readable prof s (eaR s len d) 1) :
    ∃ af t', (instruction prof s).runStream o t = (.running (nx s len s.cpu.gpr
      ((rf0 s).arith (ofBytesLE 8 (readBytes s.proc.mm.mem (eaR s len d) 1) &&& BitVec.ofNat 8 imm) false false af))
      none, t') :=
  ⟨_, _, instruction_next htf hdec (by
  simp only [exec, Sem.test, alu, logicOp, mk, mrip, bind, Prog.bind, readOp, Bool.false_eq_true, ↓reduceIte,
    memRef, effOffset, pure, Prog.readRip, Prog.read, Prog.run, Opd.width, BitVec.mul_one]
  rw [eaR_adv, checkAccess_ok (s := advance s len) hac hld]
  rfl)⟩

/-- `cmp rW, rW'`. -/
theorem cmp_rr {w r q len : Nat} (htf : s.cpu.rflags.tf = false)
    (hdec : Decode.decode prof.feat (fetchByte prof.feat s) = .ok (mk .cmp w [gr w r, gr w q] len)) :
    (instruction prof s).runStream o t =
      (.running (nx s len s.cpu.gpr (subF (rf0 s) (rv s w r) (rv s w q))) none, t) :=
  instruction_next htf hdec rfl

/-- `mov r64, qword [rip + d]`. -/
theorem mov_r64_rip {r d len : Nat} (htf : s.cpu.rflags.tf = false) (hac : s.cpu.rflags.ac = false)
    (hdec : Decode.decode prof.feat (fetchByte prof.feat s) = .ok (mk .mov 64 [gr 64 r, .mem (mrip d 64)] len))
    (hld : Readable prof s (eaR s len d) 8) :
    (instruction prof s).runStream o t = (.running (nx s len (s.cpu.gpr.set (regOf r)
      ((ofBytesLE 64 (readBytes s.proc.mm.mem (eaR s len d) 8)).setWidth 64)) (rf0 s)) none, t) := by
  refine instruction_next htf hdec ?_
  simp only [exec, Sem.mov, mk, mrip, gr, bind, Prog.bind, readOp, Bool.false_eq_true, ↓reduceIte, memRef,
    effOffset, pure, Prog.readRip, Prog.read, Prog.run, Opd.width, writeOp, BitVec.mul_one]
  rw [eaR_adv, checkAccess_ok (s := advance s len) hac hld]
  rfl

/-- `and r64, r64'`: `AF` undefined. -/
theorem and_rr64 {r q len : Nat} (htf : s.cpu.rflags.tf = false)
    (hdec : Decode.decode prof.feat (fetchByte prof.feat s) = .ok (mk .and 64 [gr 64 r, gr 64 q] len)) :
    ∃ af t', (instruction prof s).runStream o t = (.running (nx s len (s.cpu.gpr.set (regOf r)
      ((rv s 64 r &&& rv s 64 q).setWidth 64)) ((rf0 s).arith (rv s 64 r &&& rv s 64 q) false false af)) none, t') :=
  ⟨_, _, instruction_next htf hdec rfl⟩

/-- `and r32, imm32`: `AF` undefined. -/
theorem and_ri32 {r imm len : Nat} (htf : s.cpu.rflags.tf = false)
    (hdec : Decode.decode prof.feat (fetchByte prof.feat s) = .ok (mk .and 32 [gr 32 r, .imm 32 imm] len)) :
    ∃ af t', (instruction prof s).runStream o t = (.running (nx s len (s.cpu.gpr.set (regOf r)
      ((rv s 32 r &&& BitVec.ofNat 32 imm).setWidth 64))
      ((rf0 s).arith (rv s 32 r &&& BitVec.ofNat 32 imm) false false af)) none, t') :=
  ⟨_, _, instruction_next htf hdec rfl⟩

/-- `test r8h, imm8` (`ah`, `ch`, `dh`, `bh`): `AF` undefined. -/
theorem test_h8i {r imm len : Nat} (htf : s.cpu.rflags.tf = false)
    (hdec : Decode.decode prof.feat (fetchByte prof.feat s) = .ok (mk .test 8 [gh r, .imm 8 imm] len)) :
    ∃ af t', (instruction prof s).runStream o t = (.running (nx s len s.cpu.gpr
      ((rf0 s).arith (((s.cpu.gpr.get (regOf r)) >>> 8).setWidth 8 &&& BitVec.ofNat 8 imm) false false af))
      none, t') :=
  ⟨_, _, instruction_next htf hdec rfl⟩

/-- `test r8, imm8` (the low byte): `AF` undefined. -/
theorem test_r8i {r imm len : Nat} (htf : s.cpu.rflags.tf = false)
    (hdec : Decode.decode prof.feat (fetchByte prof.feat s) = .ok (mk .test 8 [gr 8 r, .imm 8 imm] len)) :
    ∃ af t', (instruction prof s).runStream o t = (.running (nx s len s.cpu.gpr
      ((rf0 s).arith (rv s 8 r &&& BitVec.ofNat 8 imm) false false af)) none, t') :=
  ⟨_, _, instruction_next htf hdec rfl⟩

/-- `RFLAGS` with `RF` cleared, as `advance` leaves it, meets the same conditions. -/
@[simp] theorem cond_rf0 (f : Rflags) (c : Cond) : ({ f with rf := false } : Rflags).cond c = f.cond c := rfl

/-- `cmovcc r64, r64'`, the condition holding. -/
theorem cmov_t {c : Cond} {r q len : Nat} (htf : s.cpu.rflags.tf = false)
    (hdec : Decode.decode prof.feat (fetchByte prof.feat s) = .ok (mk (.cmovcc c) 64 [gr 64 r, gr 64 q] len))
    (hc : s.cpu.rflags.cond c = true) :
    (instruction prof s).runStream o t =
      (.running (nx s len (s.cpu.gpr.set (regOf r) ((rv s 64 q).setWidth 64)) (rf0 s)) none, t) := by
  refine instruction_next htf hdec ?_
  simp only [exec, Sem.cmovcc, mk, gr, Prog.run, bind, Prog.bind, readOp, Prog.readReg, Prog.readFlags, advance,
    State.modCpu, Bool.false_eq_true, ↓reduceIte, done]
  simp only [pure, Prog.run, Prog.bind, cond_rf0, hc, ↓reduceIte]
  rfl

/-- `cmovcc r64, r64'`, the condition failing: the registers kept. -/
theorem cmov_n {c : Cond} {r q len : Nat} (htf : s.cpu.rflags.tf = false)
    (hdec : Decode.decode prof.feat (fetchByte prof.feat s) = .ok (mk (.cmovcc c) 64 [gr 64 r, gr 64 q] len))
    (hc : s.cpu.rflags.cond c = false) :
    (instruction prof s).runStream o t = (.running (nx s len s.cpu.gpr (rf0 s)) none, t) := by
  refine instruction_next htf hdec ?_
  simp only [exec, Sem.cmovcc, mk, gr, Prog.run, bind, Prog.bind, readOp, Prog.readReg, Prog.readFlags, advance,
    State.modCpu, Bool.false_eq_true, ↓reduceIte, done]
  simp only [pure, Prog.run, Prog.bind, cond_rf0, hc, Bool.false_eq_true, ↓reduceIte]
  rfl

end FV7z
