import FV7z.Lemmas.InsRip
/-!
# Instructions of functions with a stack frame (PLAN.md G2, "Dispatch theo CPUID", 7-Zip)

The forms 7-Zip's `CPU_IsSupported_*` and `*Prepare` functions in `7zzs` use, beside those of `Ins.lean` and
`InsRip.lean`: `push`/`pop`, `call rel32`, `jmp rel`, loads and stores `[b + d]`, the stack canary `fs:[0x28]`
(`mov`, `xor`), a store `[rip + d]`, `cpuid` (on whichever CPU the oracle picks), `xgetbv` with `ECX = 0`,
`shr`, `and`, `mov` of 32-bit registers and immediates.
-/
namespace FV7z
open ZellicX86 Decode

variable {prof : Profile} {o : Oracle} {t : Nat} {s : State}


/-- The `n` bytes from `a` can be written. -/
abbrev Writable (prof : Profile) (s : State) (a : Addr) (n : Nat) : Prop :=
  ∀ x ∈ byteAddrs a n, x.canonical prof.feat.la57 = true ∧ s.proc.mm.mem.check prof.feat s.cpu.pkru .write x = none

/-- The memory operand `fs:[disp]` of `width` bits. -/
def mfs (disp width : Nat) : MemOp :=
  { seg := some .fs, base := none, index := none, scale := 1, disp, ripRel := false, addr32 := false, width }

/-- The address `fs:[d]`. -/
abbrev eaF (s : State) (d : Nat) : Addr := s.cpu.seg.fsBase + BitVec.ofNat 64 d

theorem eaF_adv (s : State) (len d : Nat) :
    (advance s len).cpu.seg.fsBase + (0 + 0 + BitVec.ofNat 64 d) = eaF s d := by
  show s.cpu.seg.fsBase + _ = _
  simp

/-- `s` with the bytes `bs` stored at `a`. -/
abbrev st (s : State) (a : Addr) (bs : List Byte) : State := s.withMem (writeBytes s.proc.mm.mem a bs)

/-- `mov r32, imm32`. -/
theorem mov_ri32 {r imm len : Nat} (htf : s.cpu.rflags.tf = false)
    (hdec : Decode.decode prof.feat (fetchByte prof.feat s) = .ok (mk .mov 32 [gr 32 r, .imm 32 imm] len)) :
    (instruction prof s).runStream o t =
      (.running (nx s len (s.cpu.gpr.set (regOf r) ((BitVec.ofNat 32 imm).setWidth 64)) (rf0 s)) none, t) :=
  instruction_next htf hdec rfl

/-- `mov r32, r32'`. -/
theorem mov_rr32 {r q len : Nat} (htf : s.cpu.rflags.tf = false)
    (hdec : Decode.decode prof.feat (fetchByte prof.feat s) = .ok (mk .mov 32 [gr 32 r, gr 32 q] len)) :
    (instruction prof s).runStream o t =
      (.running (nx s len (s.cpu.gpr.set (regOf r) ((rv s 32 q).setWidth 64)) (rf0 s)) none, t) :=
  instruction_next htf hdec rfl

/-- `and r32, r32'`: `AF` undefined. -/
theorem and_rr32 {r q len : Nat} (htf : s.cpu.rflags.tf = false)
    (hdec : Decode.decode prof.feat (fetchByte prof.feat s) = .ok (mk .and 32 [gr 32 r, gr 32 q] len)) :
    ∃ fl t', (instruction prof s).runStream o t = (.running (nx s len
      (s.cpu.gpr.set (regOf r) ((rv s 32 r &&& rv s 32 q).setWidth 64)) fl) none, t') ∧
      fl.tf = s.cpu.rflags.tf ∧ fl.ac = s.cpu.rflags.ac ∧ fl.df = s.cpu.rflags.df :=
  ⟨_, _, instruction_next htf hdec rfl, rfl, rfl, rfl⟩

/-- `shr r32, imm8`, for the counts the code uses: `OF` (but for 1), `AF` undefined. -/
theorem shr_ri32 {r imm len : Nat} (hi : imm ∈ [1, 2, 5, 9, 19, 25, 27, 28, 29]) (htf : s.cpu.rflags.tf = false)
    (hdec : Decode.decode prof.feat (fetchByte prof.feat s) = .ok (mk .shr 32 [gr 32 r, .imm 8 imm] len)) :
    ∃ fl t', (instruction prof s).runStream o t = (.running (nx s len
      (s.cpu.gpr.set (regOf r) ((rv s 32 r >>> imm).setWidth 64)) fl) none, t') ∧
      fl.tf = s.cpu.rflags.tf ∧ fl.ac = s.cpu.rflags.ac ∧ fl.df = s.cpu.rflags.df := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact ⟨_, _, instruction_next htf hdec rfl, rfl, rfl, rfl⟩

/-- `push r64`. -/
theorem push_r {r len : Nat} (htf : s.cpu.rflags.tf = false) (hac : s.cpu.rflags.ac = false)
    (hdec : Decode.decode prof.feat (fetchByte prof.feat s) = .ok (mk .push 64 [gr 64 r] len))
    (hw : Writable prof s (s.cpu.gpr.rsp - 8) 8) :
    (instruction prof s).runStream o t = (.running (nx (st s (s.cpu.gpr.rsp - 8) (toBytesLE (rv s 64 r) 8)) len
      (s.cpu.gpr.set 4 (s.cpu.gpr.rsp - 8)) (rf0 s)) none, t) := by
  refine instruction_next htf hdec ?_
  simp only [exec, Sem.push, push64, gr, readOp, Prog.run, bind, Prog.bind, Prog.readReg, Prog.write, Prog.writeReg,
    pure, Bool.false_eq_true, ↓reduceIte, ne_eq, not_true_eq_false]
  rw [checkAccess_ok (s := advance s len) hac hw]
  rfl

/-- `pop r64`. -/
theorem pop_r {r len : Nat} (htf : s.cpu.rflags.tf = false) (hac : s.cpu.rflags.ac = false)
    (hdec : Decode.decode prof.feat (fetchByte prof.feat s) = .ok (mk .pop 64 [gr 64 r] len))
    (hld : Readable prof s s.cpu.gpr.rsp 8) :
    (instruction prof s).runStream o t = (.running (nx s len
      ((s.cpu.gpr.set 4 (s.cpu.gpr.rsp + 8)).set (regOf r)
        ((ofBytesLE 64 (readBytes s.proc.mm.mem s.cpu.gpr.rsp 8)).setWidth 64)) (rf0 s)) none, t) := by
  refine instruction_next htf hdec ?_
  simp only [exec, Sem.pop, pop64, gr, writeOp, Prog.run, bind, Prog.bind, Prog.readReg, Prog.read, Prog.writeReg,
    pure, Bool.false_eq_true, ↓reduceIte, ne_eq, not_true_eq_false]
  rw [checkAccess_ok (s := advance s len) hac hld]
  rfl

/-- `mov [b + d], rW`. -/
theorem mov_mr {w b d r len : Nat} (hw : w = 32 ∨ w = 64) (htf : s.cpu.rflags.tf = false)
    (hac : s.cpu.rflags.ac = false)
    (hdec : Decode.decode prof.feat (fetchByte prof.feat s) = .ok (mk .mov w [.mem (mbd b d w), gr w r] len))
    (hwr : Writable prof s (eaD s b d) (w / 8)) :
    (instruction prof s).runStream o t = (.running (nx (st s (eaD s b d) (toBytesLE (rv s w r) (w / 8))) len
      s.cpu.gpr (rf0 s)) none, t) := by
  rcases hw with rfl | rfl <;>
  · refine instruction_next htf hdec ?_
    simp only [exec, Sem.mov, mk, mbd, gr, bind, Prog.bind, readOp, Bool.false_eq_true, ↓reduceIte, memRef,
      effOffset, pure, Prog.readReg, Prog.write, Prog.run, Opd.width, writeOp, BitVec.mul_one]
    rw [eaD_adv, checkAccess_ok (s := advance s len) hac hwr]
    rfl

/-- `mov rW, [b + d]`. -/
theorem mov_rm {w r b d len : Nat} (hw : w = 32 ∨ w = 64) (htf : s.cpu.rflags.tf = false)
    (hac : s.cpu.rflags.ac = false)
    (hdec : Decode.decode prof.feat (fetchByte prof.feat s) = .ok (mk .mov w [gr w r, .mem (mbd b d w)] len))
    (hld : Readable prof s (eaD s b d) (w / 8)) :
    (instruction prof s).runStream o t = (.running (nx s len (s.cpu.gpr.set (regOf r)
      ((ofBytesLE w (readBytes s.proc.mm.mem (eaD s b d) (w / 8))).setWidth 64)) (rf0 s)) none, t) := by
  rcases hw with rfl | rfl <;>
  · refine instruction_next htf hdec ?_
    simp only [exec, Sem.mov, mk, mbd, gr, bind, Prog.bind, readOp, Bool.false_eq_true, ↓reduceIte, memRef,
      effOffset, pure, Prog.readReg, Prog.read, Prog.run, Opd.width, writeOp, BitVec.mul_one]
    rw [eaD_adv, checkAccess_ok (s := advance s len) hac hld]
    rfl

/-- `mov r64, fs:[d]`. -/
theorem mov_r64_fs {r d len : Nat} (htf : s.cpu.rflags.tf = false) (hac : s.cpu.rflags.ac = false)
    (hdec : Decode.decode prof.feat (fetchByte prof.feat s) = .ok (mk .mov 64 [gr 64 r, .mem (mfs d 64)] len))
    (hld : Readable prof s (eaF s d) 8) :
    (instruction prof s).runStream o t = (.running (nx s len (s.cpu.gpr.set (regOf r)
      ((ofBytesLE 64 (readBytes s.proc.mm.mem (eaF s d) 8)).setWidth 64)) (rf0 s)) none, t) := by
  refine instruction_next htf hdec ?_
  simp only [exec, Sem.mov, mk, mfs, gr, bind, Prog.bind, readOp, Bool.false_eq_true, ↓reduceIte, memRef,
    effOffset, pure, Prog.segBase, Prog.read, Prog.run, Opd.width, writeOp, BitVec.mul_one, BitVec.zero_add,
    BitVec.zero_mul]
  rw [eaF_adv, checkAccess_ok (s := advance s len) hac hld]
  rfl

/-- `xor r64, fs:[d]`: `AF` undefined. -/
theorem xor_r64_fs {r d len : Nat} (htf : s.cpu.rflags.tf = false) (hac : s.cpu.rflags.ac = false)
    (hdec : Decode.decode prof.feat (fetchByte prof.feat s) = .ok (mk .xor 64 [gr 64 r, .mem (mfs d 64)] len))
    (hld : Readable prof s (eaF s d) 8) :
    ∃ af t', (instruction prof s).runStream o t = (.running (nx s len (s.cpu.gpr.set (regOf r)
      ((rv s 64 r ^^^ ofBytesLE 64 (readBytes s.proc.mm.mem (eaF s d) 8)).setWidth 64))
      ((rf0 s).arith (rv s 64 r ^^^ ofBytesLE 64 (readBytes s.proc.mm.mem (eaF s d) 8)) false false af)) none, t') :=
  ⟨_, _, instruction_next htf hdec (by
    simp only [exec, Sem.xor, alu, logicOp, mk, mfs, gr, bind, Prog.bind, readOp, Prog.readReg, Bool.false_eq_true,
      ↓reduceIte, memRef, effOffset, pure, Prog.segBase, Prog.read, Prog.run, Opd.width, writeOp, BitVec.mul_one,
      BitVec.zero_add, BitVec.zero_mul]
    rw [eaF_adv, checkAccess_ok (s := advance s len) hac hld]
    rfl)⟩

/-- `call rel32`. -/
theorem call_rel {rel len : Nat} (htf : s.cpu.rflags.tf = false) (hac : s.cpu.rflags.ac = false)
    (hdec : Decode.decode prof.feat (fetchByte prof.feat s) = .ok (mk .call 64 [.rel rel] len))
    (hsh : s.thread.shstk = none)
    (hcan : (s.cpu.rip.add len + BitVec.ofNat 64 rel).canonical prof.feat.la57 = true)
    (hw : Writable prof s (s.cpu.gpr.rsp - 8) 8) :
    (instruction prof s).runStream o t = (.running (upd (st s (s.cpu.gpr.rsp - 8) (toBytesLE (s.cpu.rip.add len) 8))
      (s.cpu.rip.add len + BitVec.ofNat 64 rel) (s.cpu.gpr.set 4 (s.cpu.gpr.rsp - 8)) (rf0 s)) none, t) := by
  refine instruction_next htf hdec ?_
  simp only [exec, Sem.call, push64, mk, Prog.run, bind, Prog.bind, Prog.readThread, Prog.readRip, Prog.readReg,
    Prog.write, Prog.writeReg, Prog.writeRip, pure, show (advance s len).thread.shstk = none from hsh,
    Bool.false_eq_true, ↓reduceIte, done]
  rw [show (advance s len).cpu.rip = s.cpu.rip.add len from rfl, hcan]
  simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, Prog.run, bind, Prog.bind, pure]
  rw [checkAccess_ok (s := advance s len) hac hw]
  rfl

/-- `jmp rel`. -/
theorem jmp_rel {rel len : Nat} (htf : s.cpu.rflags.tf = false)
    (hdec : Decode.decode prof.feat (fetchByte prof.feat s) = .ok (mk .jmp 64 [.rel rel] len))
    (hcan : (s.cpu.rip.add len + BitVec.ofNat 64 rel).canonical prof.feat.la57 = true) :
    (instruction prof s).runStream o t =
      (.running (upd s (s.cpu.rip.add len + BitVec.ofNat 64 rel) s.cpu.gpr (rf0 s)) none, t) := by
  refine instruction_next htf hdec ?_
  simp only [exec, Sem.jmp, mk, Prog.run, bind, Prog.bind, Prog.readRip, advance, State.modCpu,
    jumpTo, Bool.false_eq_true, ↓reduceIte, Prog.writeRip, done]
  simp only [hcan, ↓reduceIte]
  rfl

/-- `mov [rip + d], r64`. -/
theorem mov_rip_r64 {d r len : Nat} (htf : s.cpu.rflags.tf = false) (hac : s.cpu.rflags.ac = false)
    (hdec : Decode.decode prof.feat (fetchByte prof.feat s) = .ok (mk .mov 64 [.mem (mrip d 64), gr 64 r] len))
    (hwr : Writable prof s (eaR s len d) 8) :
    (instruction prof s).runStream o t = (.running (nx (st s (eaR s len d) (toBytesLE (rv s 64 r) 8)) len
      s.cpu.gpr (rf0 s)) none, t) := by
  refine instruction_next htf hdec ?_
  simp only [exec, Sem.mov, mk, mrip, gr, bind, Prog.bind, readOp, Bool.false_eq_true, ↓reduceIte, memRef,
    effOffset, pure, Prog.readReg, Prog.readRip, Prog.write, Prog.run, writeOp, BitVec.mul_one]
  rw [eaR_adv, checkAccess_ok (s := advance s len) hac hwr]
  rfl


/-- `cpuid`, on the CPU the oracle picks at position `t`. -/
theorem cpuid_i {len : Nat} (htf : s.cpu.rflags.tf = false)
    (hdec : Decode.decode prof.feat (fetchByte prof.feat s) = .ok (mk .cpuid 32 [] len))
    (hcf : s.thread.cpuidFaults = false) :
    (instruction prof s).runStream o t = (.running (nx s len
      (let r := prof.cpuid (o t (.pick (prof.cpus - 1))).val (s.cpu.gpr.rax.setWidth 32) (s.cpu.gpr.rcx.setWidth 32)
       (((s.cpu.gpr.set 0 (r.eax.setWidth 64)).set 3 (r.ebx.setWidth 64)).set 1 (r.ecx.setWidth 64)).set 2
         (r.edx.setWidth 64)) (rf0 s)) none, t + 1) := by
  refine instruction_next htf hdec ?_
  simp only [exec, Sem.cpuid, mk, Prog.run, bind, Prog.bind, Prog.readThread,
    show (advance s len).thread.cpuidFaults = false from hcf, Bool.false_eq_true, ↓reduceIte]
  rfl

/-- `xgetbv` with `ECX = 0`: `XCR0`. -/
theorem xgetbv0 {len : Nat} (htf : s.cpu.rflags.tf = false)
    (hdec : Decode.decode prof.feat (fetchByte prof.feat s) = .ok (mk .xgetbv 32 [] len))
    {x : BitVec 64} (hx : prof.xcr0 = some x) (hc : s.cpu.gpr.rcx.setWidth 32 = 0) :
    (instruction prof s).runStream o t = (.running (nx s len
      ((s.cpu.gpr.set 0 ((x.setWidth 32).setWidth 64)).set 2 ((x.extractLsb' 32 32).setWidth 64)) (rf0 s)) none, t) := by
  refine instruction_next htf hdec ?_
  have hc' : ((advance s len).cpu.gpr.get 1).setWidth 32 = 0 := hc
  simp only [exec, Sem.xgetbv, mk, Prog.run, bind, Prog.bind, Prog.readReg, hx, Option.isNone_some, Option.getD_some,
    Bool.false_eq_true, ↓reduceIte, hc']
  rfl

/-! ## For `z7_SwapBytesPrepare` -/
/-- `add r32, imm32`. -/
theorem add_ri32 {r imm len : Nat} (htf : s.cpu.rflags.tf = false)
    (hdec : Decode.decode prof.feat (fetchByte prof.feat s) = .ok (mk .add 32 [gr 32 r, .imm 32 imm] len)) :
    (instruction prof s).runStream o t = (.running (nx s len
      (s.cpu.gpr.set (regOf r) ((addR (rv s 32 r) (BitVec.ofNat 32 imm)).setWidth 64))
      (addF (rf0 s) (rv s 32 r) (BitVec.ofNat 32 imm))) none, t) :=
  instruction_next htf hdec rfl

/-- `setcc r8` (a low byte). -/
theorem setcc_r8 {c : Cond} {r len : Nat} (htf : s.cpu.rflags.tf = false)
    (hdec : Decode.decode prof.feat (fetchByte prof.feat s) = .ok (mk (.setcc c) 8 [gr 8 r] len)) :
    (instruction prof s).runStream o t = (.running (nx s len
      (s.cpu.gpr.set (regOf r) ((s.cpu.gpr.get (regOf r) &&& ~~~BitVec.ofNat 64 ((2 ^ 8 - 1) * 2 ^ 0)) |||
        ((BitVec.ofBool (s.cpu.rflags.cond c)).setWidth 8).setWidth 64 <<< 0)) (rf0 s)) none, t) :=
  instruction_next htf hdec rfl

/-- `movzx r32, r8` (a low byte). -/
theorem movzx_rr8 {r q len : Nat} (htf : s.cpu.rflags.tf = false)
    (hdec : Decode.decode prof.feat (fetchByte prof.feat s) = .ok (mk .movzx 32 [gr 32 r, gr 8 q] len)) :
    (instruction prof s).runStream o t = (.running (nx s len
      (s.cpu.gpr.set (regOf r) (((rv s 8 q).setWidth 32).setWidth 64)) (rf0 s)) none, t) :=
  instruction_next htf hdec rfl

/-- `mov [rip + d], r32`. -/
theorem mov_rip_r32 {d r len : Nat} (htf : s.cpu.rflags.tf = false) (hac : s.cpu.rflags.ac = false)
    (hdec : Decode.decode prof.feat (fetchByte prof.feat s) = .ok (mk .mov 32 [.mem (mrip d 32), gr 32 r] len))
    (hwr : Writable prof s (eaR s len d) 4) :
    (instruction prof s).runStream o t = (.running (nx (st s (eaR s len d) (toBytesLE (rv s 32 r) 4)) len
      s.cpu.gpr (rf0 s)) none, t) := by
  refine instruction_next htf hdec ?_
  simp only [exec, Sem.mov, mk, mrip, gr, bind, Prog.bind, readOp, Bool.false_eq_true, ↓reduceIte, memRef,
    effOffset, pure, Prog.readReg, Prog.readRip, Prog.write, Prog.run, writeOp, BitVec.mul_one]
  rw [eaR_adv, checkAccess_ok (s := advance s len) hac hwr]
  rfl

/-- The low byte `setcc` writes, read back. -/
theorem setcc_low (v : BitVec 64) (b : BitVec 8) :
    ((v &&& ~~~BitVec.ofNat 64 ((2 ^ 8 - 1) * 2 ^ 0)) ||| b.setWidth 64 <<< 0).setWidth 8 = b := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp [hi]

/-! ## For `z7_Black2sp_Prepare` -/
/-- `sbb r32, r32`: `r - q - CF`. -/
theorem sbb_rr32 {r q len : Nat} (htf : s.cpu.rflags.tf = false)
    (hdec : Decode.decode prof.feat (fetchByte prof.feat s) = .ok (mk .sbb 32 [gr 32 r, gr 32 q] len)) :
    (instruction prof s).runStream o t = (.running (nx s len
      (s.cpu.gpr.set (regOf r) ((rv s 32 r - rv s 32 q - (BitVec.ofBool s.cpu.rflags.cf).setWidth 32).setWidth 64))
      ((rf0 s).arith (rv s 32 r - rv s 32 q - (BitVec.ofBool s.cpu.rflags.cf).setWidth 32)
        (borrowSub (rv s 32 r) (rv s 32 q) s.cpu.rflags.cf)
        (overflowSub (rv s 32 r) (rv s 32 q) (rv s 32 r - rv s 32 q - (BitVec.ofBool s.cpu.rflags.cf).setWidth 32))
        (auxSub (rv s 32 r) (rv s 32 q) s.cpu.rflags.cf))) none, t) :=
  instruction_next htf hdec rfl

end FV7z
