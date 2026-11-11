import FV7z.Lemmas.Exec
import FV7z.Lemmas.Vec
/-!
# Instructions by their decoded form (PLAN.md G2.1)

What an instruction does, given what it decodes to (`Decode.Inst`), wherever it lies in a function's code.
-/
namespace FV7z
open ZellicX86 Decode

abbrev mk (mn : Mn) (opsz : Nat) (ops : List Opd) (len : Nat) : Inst :=
  { mn, opsz, ops, len, rep := none, lock := false, mask := none, zero := false, fop := 0 }
/-- General register `n` as a `w`-bit operand. -/
def gr (w n : Nat) : Opd := .reg ⟨w, n, false⟩
/-- The memory operand `[b + disp]` of `width` bits. -/
def mbd (b disp width : Nat) : MemOp :=
  { seg := none, base := some b, index := none, scale := 1, disp, ripRel := false, addr32 := false, width }

/-- The memory operand `[b + i + disp]` of `width` bits. -/
def mbi (b i disp width : Nat) : MemOp :=
  { seg := none, base := some b, index := some i, scale := 1, disp, ripRel := false, addr32 := false, width }

/-- `s` with `rip` past `len` bytes, registers `g`, flags `fl` and vector registers `z`. -/
def nxz (s : State) (len : Nat) (g : Gprs) (fl : Rflags) (z : Fin 32 → BitVec 512) : State :=
  s.modCpu fun c => { c with rip := c.rip.add len, rflags := fl, gpr := g, vec := { c.vec with zmm := z } }

variable {prof : Profile} {o : Oracle} {t : Nat} {s : State}

@[simp] theorem nxz_gpr (s : State) (len : Nat) (g : Gprs) (fl : Rflags) (z : Fin 32 → BitVec 512) :
    (nxz s len g fl z).cpu.gpr = g := rfl
@[simp] theorem nxz_rip (s : State) (len : Nat) (g : Gprs) (fl : Rflags) (z : Fin 32 → BitVec 512) :
    (nxz s len g fl z).cpu.rip = s.cpu.rip.add len := rfl
@[simp] theorem nxz_rflags (s : State) (len : Nat) (g : Gprs) (fl : Rflags) (z : Fin 32 → BitVec 512) :
    (nxz s len g fl z).cpu.rflags = fl := rfl
@[simp] theorem nxz_zmm (s : State) (len : Nat) (g : Gprs) (fl : Rflags) (z : Fin 32 → BitVec 512) :
    (nxz s len g fl z).cpu.vec.zmm = z := rfl
@[simp] theorem nxz_mem (s : State) (len : Nat) (g : Gprs) (fl : Rflags) (z : Fin 32 → BitVec 512) :
    (nxz s len g fl z).proc.mm.mem = s.proc.mm.mem := rfl
@[simp] theorem nxz_pkru (s : State) (len : Nat) (g : Gprs) (fl : Rflags) (z : Fin 32 → BitVec 512) :
    (nxz s len g fl z).cpu.pkru = s.cpu.pkru := rfl
@[simp] theorem nxz_thread (s : State) (len : Nat) (g : Gprs) (fl : Rflags) (z : Fin 32 → BitVec 512) :
    (nxz s len g fl z).thread = s.thread := rfl

theorem Kept.nxz {s₀ s : State} (h : Kept s₀ s) {len : Nat} {g : Gprs} {fl : Rflags} {z : Fin 32 → BitVec 512}
    (htf : fl.tf = s.cpu.rflags.tf) (hac : fl.ac = s.cpu.rflags.ac) (hdf : fl.df = s.cpu.rflags.df) :
    Kept s₀ (FV7z.nxz s len g fl z) :=
  h.modCpu rfl rfl rfl rfl htf hac hdf

/-- The flags an instruction starts from (`advance`). -/
abbrev rf0 (s : State) : Rflags := { s.cpu.rflags with rf := false }

/-! ## Scalar instructions -/

/-- `endbr64`. -/
theorem endbr (htf : s.cpu.rflags.tf = false) {len : Nat}
    (hdec : Decode.decode prof.feat (fetchByte prof.feat s) = .ok (mk .endbr64 32 [] len)) :
    (instruction prof s).runStream o t = (.running (nx s len s.cpu.gpr (rf0 s)) none, t) :=
  instruction_next htf hdec rfl

/-- `cmp rW, imm`. -/
theorem cmp_ri {w r imm len : Nat} (htf : s.cpu.rflags.tf = false)
    (hdec : Decode.decode prof.feat (fetchByte prof.feat s) = .ok (mk .cmp w [gr w r, .imm w imm] len)) :
    (instruction prof s).runStream o t = (.running (nx s len s.cpu.gpr ((rf0 s).arith
      ((s.cpu.gpr.get (regOf r)).setWidth w - BitVec.ofNat w imm - (BitVec.ofBool false).setWidth w)
      (borrowSub ((s.cpu.gpr.get (regOf r)).setWidth w) (BitVec.ofNat w imm) false)
      (overflowSub ((s.cpu.gpr.get (regOf r)).setWidth w) (BitVec.ofNat w imm)
        ((s.cpu.gpr.get (regOf r)).setWidth w - BitVec.ofNat w imm - (BitVec.ofBool false).setWidth w))
      (auxSub ((s.cpu.gpr.get (regOf r)).setWidth w) (BitVec.ofNat w imm) false))) none, t) :=
  instruction_next htf hdec rfl

/-- `jcc`, taken. -/
theorem jcc_t {c : Cond} {rel len : Nat} (htf : s.cpu.rflags.tf = false)
    (hdec : Decode.decode prof.feat (fetchByte prof.feat s) = .ok (mk (.jcc c) 64 [.rel rel] len))
    (hc : s.cpu.rflags.cond c = true)
    (hcan : (s.cpu.rip.add len + BitVec.ofNat 64 rel).canonical prof.feat.la57 = true) :
    (instruction prof s).runStream o t =
      (.running (upd s (s.cpu.rip.add len + BitVec.ofNat 64 rel) s.cpu.gpr (rf0 s)) none, t) := by
  refine instruction_next htf hdec ?_
  simp only [exec, Sem.jcc, mk, Prog.run, bind, Prog.bind, Prog.readFlags, Prog.readRip, advance, State.modCpu,
    jumpTo, Bool.false_eq_true, ↓reduceIte, Prog.writeRip, done]
  rw [show ({ s.cpu.rflags with rf := false } : Rflags).cond c = s.cpu.rflags.cond c by
    rfl]
  simp only [hc, ↓reduceIte, hcan, Bool.not_true, Bool.false_eq_true]
  rfl

/-- `jcc`, not taken. -/
theorem jcc_n {c : Cond} {rel len : Nat} (htf : s.cpu.rflags.tf = false)
    (hdec : Decode.decode prof.feat (fetchByte prof.feat s) = .ok (mk (.jcc c) 64 [.rel rel] len))
    (hc : s.cpu.rflags.cond c = false) :
    (instruction prof s).runStream o t = (.running (nx s len s.cpu.gpr (rf0 s)) none, t) := by
  refine instruction_next htf hdec ?_
  simp only [exec, Sem.jcc, mk, Prog.run, bind, Prog.bind, Prog.readFlags, Prog.readRip, advance, State.modCpu,
    Bool.false_eq_true, ↓reduceIte, done]
  rw [show ({ s.cpu.rflags with rf := false } : Rflags).cond c = s.cpu.rflags.cond c by
    rfl]
  simp only [hc, Bool.false_eq_true, ↓reduceIte]
  rfl

/-! ## Arithmetic -/

/-- `x - y`, as `SUB` computes it. -/
def subR {w : Nat} (x y : BitVec w) : BitVec w := x - y - (BitVec.ofBool false).setWidth w
/-- The flags of `SUB x, y` from `f`. -/
def subF {w : Nat} (f : Rflags) (x y : BitVec w) : Rflags :=
  f.arith (subR x y) (borrowSub x y false) (overflowSub x y (subR x y)) (auxSub x y false)
/-- `x + y`, as `ADD` computes it. -/
def addR {w : Nat} (x y : BitVec w) : BitVec w := x + y + (BitVec.ofBool false).setWidth w
/-- The flags of `ADD x, y` from `f`. -/
def addF {w : Nat} (f : Rflags) (x y : BitVec w) : Rflags :=
  f.arith (addR x y) (carryAdd x y false) (overflowAdd x y (addR x y)) (auxAdd x y false)

@[simp] theorem subR_eq {w : Nat} (x y : BitVec w) : subR x y = x - y := by simp [subR]
@[simp] theorem addR_eq {w : Nat} (x y : BitVec w) : addR x y = x + y := by simp [addR]
@[simp] theorem arith_tf {w : Nat} (f : Rflags) (r : BitVec w) (cf of af : Bool) : (f.arith r cf of af).tf = f.tf := rfl
@[simp] theorem arith_ac {w : Nat} (f : Rflags) (r : BitVec w) (cf of af : Bool) : (f.arith r cf of af).ac = f.ac := rfl
@[simp] theorem arith_df {w : Nat} (f : Rflags) (r : BitVec w) (cf of af : Bool) : (f.arith r cf of af).df = f.df := rfl
@[simp] theorem arith_zf {w : Nat} (f : Rflags) (r : BitVec w) (cf of af : Bool) :
    (f.arith r cf of af).zf = (r == 0) := rfl
@[simp] theorem arith_cf {w : Nat} (f : Rflags) (r : BitVec w) (cf of af : Bool) : (f.arith r cf of af).cf = cf := rfl
@[simp] theorem subF_zf {w : Nat} (f : Rflags) (x y : BitVec w) : (subF f x y).zf = decide (x = y) := by
  simp [subF, bv_sub_beq_zero]
@[simp] theorem subF_cf {w : Nat} (f : Rflags) (x y : BitVec w) : (subF f x y).cf = decide (x.toNat < y.toNat) := by
  simp [subF, borrowSub]
@[simp] theorem subF_tf {w : Nat} (f : Rflags) (x y : BitVec w) : (subF f x y).tf = f.tf := rfl
@[simp] theorem subF_ac {w : Nat} (f : Rflags) (x y : BitVec w) : (subF f x y).ac = f.ac := rfl
@[simp] theorem subF_df {w : Nat} (f : Rflags) (x y : BitVec w) : (subF f x y).df = f.df := rfl
@[simp] theorem addF_tf {w : Nat} (f : Rflags) (x y : BitVec w) : (addF f x y).tf = f.tf := rfl
@[simp] theorem addF_ac {w : Nat} (f : Rflags) (x y : BitVec w) : (addF f x y).ac = f.ac := rfl
@[simp] theorem addF_df {w : Nat} (f : Rflags) (x y : BitVec w) : (addF f x y).df = f.df := rfl

/-- The value of general register `r` as a `w`-bit operand. -/
abbrev rv (s : State) (w r : Nat) : BitVec w := (s.cpu.gpr.get (regOf r)).setWidth w

/-- `sub rW, imm`. -/
theorem sub_ri {w r imm len : Nat} (hw : w = 32 ∨ w = 64) (htf : s.cpu.rflags.tf = false)
    (hdec : Decode.decode prof.feat (fetchByte prof.feat s) = .ok (mk .sub w [gr w r, .imm w imm] len)) :
    (instruction prof s).runStream o t = (.running (nx s len
      (s.cpu.gpr.set (regOf r) ((subR (rv s w r) (BitVec.ofNat w imm)).setWidth 64))
      (subF (rf0 s) (rv s w r) (BitVec.ofNat w imm))) none, t) := by
  rcases hw with rfl | rfl <;> exact instruction_next htf hdec rfl

/-- `sub rW, rW'`. -/
theorem sub_rr {w r q len : Nat} (hw : w = 32 ∨ w = 64) (htf : s.cpu.rflags.tf = false)
    (hdec : Decode.decode prof.feat (fetchByte prof.feat s) = .ok (mk .sub w [gr w r, gr w q] len)) :
    (instruction prof s).runStream o t = (.running (nx s len
      (s.cpu.gpr.set (regOf r) ((subR (rv s w r) (rv s w q)).setWidth 64))
      (subF (rf0 s) (rv s w r) (rv s w q))) none, t) := by
  rcases hw with rfl | rfl <;> exact instruction_next htf hdec rfl

/-- `add r64, imm`. -/
theorem add_ri {r imm len : Nat} (htf : s.cpu.rflags.tf = false)
    (hdec : Decode.decode prof.feat (fetchByte prof.feat s) = .ok (mk .add 64 [gr 64 r, .imm 64 imm] len)) :
    (instruction prof s).runStream o t = (.running (nx s len
      (s.cpu.gpr.set (regOf r) ((addR (rv s 64 r) (BitVec.ofNat 64 imm)).setWidth 64))
      (addF (rf0 s) (rv s 64 r) (BitVec.ofNat 64 imm))) none, t) :=
  instruction_next htf hdec rfl

/-- `add r64, r64'`. -/
theorem add_rr {r q len : Nat} (htf : s.cpu.rflags.tf = false)
    (hdec : Decode.decode prof.feat (fetchByte prof.feat s) = .ok (mk .add 64 [gr 64 r, gr 64 q] len)) :
    (instruction prof s).runStream o t = (.running (nx s len
      (s.cpu.gpr.set (regOf r) ((addR (rv s 64 r) (rv s 64 q)).setWidth 64))
      (addF (rf0 s) (rv s 64 r) (rv s 64 q))) none, t) :=
  instruction_next htf hdec rfl

/-- `sbb r32, r32'`. -/
theorem sbb_rr {r q len : Nat} (htf : s.cpu.rflags.tf = false)
    (hdec : Decode.decode prof.feat (fetchByte prof.feat s) = .ok (mk .sbb 32 [gr 32 r, gr 32 q] len)) :
    ∃ fl, (instruction prof s).runStream o t = (.running (nx s len
      (s.cpu.gpr.set (regOf r) ((rv s 32 r - rv s 32 q - (BitVec.ofBool s.cpu.rflags.cf).setWidth 32).setWidth 64))
      fl) none, t) ∧ fl.tf = s.cpu.rflags.tf ∧ fl.ac = s.cpu.rflags.ac ∧ fl.df = s.cpu.rflags.df :=
  ⟨_, instruction_next htf hdec rfl, rfl, rfl, rfl⟩

/-- `and r32, imm`: `AF` undefined. -/
theorem and_ri {r imm len : Nat} (htf : s.cpu.rflags.tf = false)
    (hdec : Decode.decode prof.feat (fetchByte prof.feat s) = .ok (mk .and 32 [gr 32 r, .imm 32 imm] len)) :
    ∃ fl t', (instruction prof s).runStream o t = (.running (nx s len
      (s.cpu.gpr.set (regOf r) ((rv s 32 r &&& BitVec.ofNat 32 imm).setWidth 64)) fl) none, t') ∧
      fl.tf = s.cpu.rflags.tf ∧ fl.ac = s.cpu.rflags.ac ∧ fl.df = s.cpu.rflags.df :=
  ⟨_, _, instruction_next htf hdec rfl, rfl, rfl, rfl⟩

/-- `or r32, imm`: `AF` undefined. -/
theorem or_ri {r imm len : Nat} (htf : s.cpu.rflags.tf = false)
    (hdec : Decode.decode prof.feat (fetchByte prof.feat s) = .ok (mk .or 32 [gr 32 r, .imm 32 imm] len)) :
    ∃ fl t', (instruction prof s).runStream o t = (.running (nx s len
      (s.cpu.gpr.set (regOf r) ((rv s 32 r ||| BitVec.ofNat 32 imm).setWidth 64)) fl) none, t') ∧
      fl.tf = s.cpu.rflags.tf ∧ fl.ac = s.cpu.rflags.ac ∧ fl.df = s.cpu.rflags.df :=
  ⟨_, _, instruction_next htf hdec rfl, rfl, rfl, rfl⟩

/-- `or r64, r64'`: `AF` undefined. -/
theorem or_rr {r q len : Nat} (htf : s.cpu.rflags.tf = false)
    (hdec : Decode.decode prof.feat (fetchByte prof.feat s) = .ok (mk .or 64 [gr 64 r, gr 64 q] len)) :
    ∃ fl t', (instruction prof s).runStream o t = (.running (nx s len
      (s.cpu.gpr.set (regOf r) ((rv s 64 r ||| rv s 64 q).setWidth 64)) fl) none, t') ∧
      fl.tf = s.cpu.rflags.tf ∧ fl.ac = s.cpu.rflags.ac ∧ fl.df = s.cpu.rflags.df :=
  ⟨_, _, instruction_next htf hdec rfl, rfl, rfl, rfl⟩

/-- `xor r32, r32'`: `AF` undefined. -/
theorem xor_rr {r q len : Nat} (htf : s.cpu.rflags.tf = false)
    (hdec : Decode.decode prof.feat (fetchByte prof.feat s) = .ok (mk .xor 32 [gr 32 r, gr 32 q] len)) :
    ∃ fl t', (instruction prof s).runStream o t = (.running (nx s len
      (s.cpu.gpr.set (regOf r) ((rv s 32 r ^^^ rv s 32 q).setWidth 64)) fl) none, t') ∧
      fl.tf = s.cpu.rflags.tf ∧ fl.ac = s.cpu.rflags.ac ∧ fl.df = s.cpu.rflags.df :=
  ⟨_, _, instruction_next htf hdec rfl, rfl, rfl, rfl⟩

/-- `shl r64, 32`: `OF`, `AF` undefined. -/
theorem shl64_32 {r len : Nat} (htf : s.cpu.rflags.tf = false)
    (hdec : Decode.decode prof.feat (fetchByte prof.feat s) = .ok (mk .shl 64 [gr 64 r, .imm 8 32] len)) :
    ∃ fl t', (instruction prof s).runStream o t = (.running (nx s len
      (s.cpu.gpr.set (regOf r) ((rv s 64 r <<< 32).setWidth 64)) fl) none, t') ∧
      fl.tf = s.cpu.rflags.tf ∧ fl.ac = s.cpu.rflags.ac ∧ fl.df = s.cpu.rflags.df :=
  ⟨_, _, instruction_next htf hdec rfl, rfl, rfl, rfl⟩

/-- `shl r32, 8`: `OF`, `AF` undefined. -/
theorem shl32_8 {r len : Nat} (htf : s.cpu.rflags.tf = false)
    (hdec : Decode.decode prof.feat (fetchByte prof.feat s) = .ok (mk .shl 32 [gr 32 r, .imm 8 8] len)) :
    ∃ fl t', (instruction prof s).runStream o t = (.running (nx s len
      (s.cpu.gpr.set (regOf r) ((rv s 32 r <<< 8).setWidth 64)) fl) none, t') ∧
      fl.tf = s.cpu.rflags.tf ∧ fl.ac = s.cpu.rflags.ac ∧ fl.df = s.cpu.rflags.df :=
  ⟨_, _, instruction_next htf hdec rfl, rfl, rfl, rfl⟩

/-- `bswap r32`. -/
theorem bswap32 {r len : Nat} (htf : s.cpu.rflags.tf = false)
    (hdec : Decode.decode prof.feat (fetchByte prof.feat s) = .ok (mk .bswap 32 [gr 32 r] len)) :
    (instruction prof s).runStream o t = (.running (nx s len
      (s.cpu.gpr.set (regOf r) ((ZellicX86.bswap (rv s 32 r)).setWidth 64)) (rf0 s)) none, t) :=
  instruction_next htf hdec rfl

/-- `mov r64, r64'`. -/
theorem mov_rr {r q len : Nat} (htf : s.cpu.rflags.tf = false)
    (hdec : Decode.decode prof.feat (fetchByte prof.feat s) = .ok (mk .mov 64 [gr 64 r, gr 64 q] len)) :
    (instruction prof s).runStream o t = (.running (nx s len
      (s.cpu.gpr.set (regOf r) ((rv s 64 q).setWidth 64)) (rf0 s)) none, t) :=
  instruction_next htf hdec rfl

/-- `lea r64, [b + i + d]`. -/
theorem lea {r b i d len : Nat} (htf : s.cpu.rflags.tf = false)
    (hdec : Decode.decode prof.feat (fetchByte prof.feat s) = .ok (mk .lea 64 [gr 64 r, .mem (mbi b i d 0)] len)) :
    (instruction prof s).runStream o t = (.running (nx s len
      (s.cpu.gpr.set (regOf r) (s.cpu.gpr.get (regOf b) + s.cpu.gpr.get (regOf i) + BitVec.ofNat 64 d)) (rf0 s))
      none, t) := by
  refine instruction_next htf hdec ?_
  simp only [exec, Sem.lea, mk, mbi, gr, effOffset, Prog.run, bind, Prog.bind, pure, Prog.readReg, Bool.false_eq_true,
    ↓reduceIte, writeOp, BitVec.mul_one, BitVec.setWidth_eq]
  rfl

/-! ## Loads -/

/-- The address `[b + d]`. -/
abbrev eaD (s : State) (b d : Nat) : Addr := s.cpu.gpr.get (regOf b) + BitVec.ofNat 64 d
/-- The address `[b + i + d]`. -/
abbrev eaI (s : State) (b i d : Nat) : Addr := s.cpu.gpr.get (regOf b) + s.cpu.gpr.get (regOf i) + BitVec.ofNat 64 d

/-- The `n` bytes from `a` can be read. -/
abbrev Readable (prof : Profile) (s : State) (a : Addr) (n : Nat) : Prop :=
  ∀ x ∈ byteAddrs a n, x.canonical prof.feat.la57 = true ∧ s.proc.mm.mem.check prof.feat s.cpu.pkru .read x = none

theorem eaD_adv (s : State) (len b d : Nat) :
    (advance s len).cpu.gpr.get (regOf b) + 0 + BitVec.ofNat 64 d = eaD s b d := by
  show s.cpu.gpr.get (regOf b) + (0 : BitVec 64) + _ = _
  simp

/-- `movzx r32, byte [b + i + d]`. -/
theorem movzx8_i {r b i d len : Nat} (htf : s.cpu.rflags.tf = false) (hac : s.cpu.rflags.ac = false)
    (hdec : Decode.decode prof.feat (fetchByte prof.feat s) = .ok (mk .movzx 32 [gr 32 r, .mem (mbi b i d 8)] len))
    (hld : Readable prof s (eaI s b i d) 1) :
    (instruction prof s).runStream o t = (.running (nx s len (s.cpu.gpr.set (regOf r)
      (((ofBytesLE 8 (readBytes s.proc.mm.mem (eaI s b i d) 1)).setWidth 32).setWidth 64)) (rf0 s)) none, t) := by
  refine instruction_next htf hdec ?_
  simp only [exec, Sem.movzx, mk, mbi, gr, bind, Prog.bind, readOp, Bool.false_eq_true, ↓reduceIte, memRef,
    effOffset, pure, Prog.readReg, Prog.read, Prog.run, BitVec.mul_one, Opd.width, writeOp]
  rw [checkAccess_ok (s := advance s len) hac hld]
  rfl

/-- `movzx r32, byte [b]`. -/
theorem movzx8_d {r b len : Nat} (htf : s.cpu.rflags.tf = false) (hac : s.cpu.rflags.ac = false)
    (hdec : Decode.decode prof.feat (fetchByte prof.feat s) = .ok (mk .movzx 32 [gr 32 r, .mem (mbd b 0 8)] len))
    (hld : Readable prof s (eaD s b 0) 1) :
    (instruction prof s).runStream o t = (.running (nx s len (s.cpu.gpr.set (regOf r)
      (((ofBytesLE 8 (readBytes s.proc.mm.mem (eaD s b 0) 1)).setWidth 32).setWidth 64)) (rf0 s)) none, t) := by
  refine instruction_next htf hdec ?_
  simp only [exec, Sem.movzx, mk, mbd, gr, bind, Prog.bind, readOp, Bool.false_eq_true, ↓reduceIte, memRef,
    effOffset, pure, Prog.readReg, Prog.read, Prog.run, Opd.width, writeOp, BitVec.mul_one]
  rw [eaD_adv, checkAccess_ok (s := advance s len) hac hld]
  rfl

/-- `movzx r32, word [b]`. -/
theorem movzx16_d {r b len : Nat} (htf : s.cpu.rflags.tf = false) (hac : s.cpu.rflags.ac = false)
    (hdec : Decode.decode prof.feat (fetchByte prof.feat s) = .ok (mk .movzx 32 [gr 32 r, .mem (mbd b 0 16)] len))
    (hld : Readable prof s (eaD s b 0) 2) :
    (instruction prof s).runStream o t = (.running (nx s len (s.cpu.gpr.set (regOf r)
      (((ofBytesLE 16 (readBytes s.proc.mm.mem (eaD s b 0) 2)).setWidth 32).setWidth 64)) (rf0 s)) none, t) := by
  refine instruction_next htf hdec ?_
  simp only [exec, Sem.movzx, mk, mbd, gr, bind, Prog.bind, readOp, Bool.false_eq_true, ↓reduceIte, memRef,
    effOffset, pure, Prog.readReg, Prog.read, Prog.run, Opd.width, writeOp, BitVec.mul_one]
  rw [eaD_adv, checkAccess_ok (s := advance s len) hac hld]
  rfl

/-- `mov r8, byte [b + i + d]`: bits 63–8 kept. -/
theorem mov8_i {r b i d len : Nat} (htf : s.cpu.rflags.tf = false) (hac : s.cpu.rflags.ac = false)
    (hdec : Decode.decode prof.feat (fetchByte prof.feat s) = .ok (mk .mov 8 [gr 8 r, .mem (mbi b i d 8)] len))
    (hld : Readable prof s (eaI s b i d) 1) :
    (instruction prof s).runStream o t = (.running (nx s len (s.cpu.gpr.set (regOf r)
      ((s.cpu.gpr.get (regOf r) &&& ~~~(BitVec.ofNat 64 ((2 ^ 8 - 1) * 2 ^ 0))) |||
        ((ofBytesLE 8 (readBytes s.proc.mm.mem (eaI s b i d) 1)).setWidth 64 <<< 0))) (rf0 s)) none, t) := by
  refine instruction_next htf hdec ?_
  simp only [exec, Sem.mov, mk, mbi, gr, bind, Prog.bind, readOp, Bool.false_eq_true, ↓reduceIte, memRef,
    effOffset, pure, Prog.readReg, Prog.read, Prog.run, BitVec.mul_one, Opd.width]
  rw [checkAccess_ok (s := advance s len) hac hld]
  rfl

/-- `movbe r32, [b]`. -/
theorem movbe_d {r b len : Nat} (htf : s.cpu.rflags.tf = false) (hac : s.cpu.rflags.ac = false)
    (hdec : Decode.decode prof.feat (fetchByte prof.feat s) = .ok (mk .movbe 32 [gr 32 r, .mem (mbd b 0 32)] len))
    (hld : Readable prof s (eaD s b 0) 4) :
    (instruction prof s).runStream o t = (.running (nx s len (s.cpu.gpr.set (regOf r)
      ((ZellicX86.bswap (ofBytesLE 32 (readBytes s.proc.mm.mem (eaD s b 0) 4))).setWidth 64)) (rf0 s)) none, t) := by
  refine instruction_next htf hdec ?_
  simp only [exec, Sem.movbe, mk, mbd, gr, bind, Prog.bind, readOp, Bool.false_eq_true, ↓reduceIte, memRef,
    effOffset, pure, Prog.readReg, Prog.read, Prog.run, Opd.width, writeOp, BitVec.mul_one]
  rw [eaD_adv, checkAccess_ok (s := advance s len) hac hld]
  rfl

/-- `movbe r32, [b + i + d]`. -/
theorem movbe_i {r b i d len : Nat} (htf : s.cpu.rflags.tf = false) (hac : s.cpu.rflags.ac = false)
    (hdec : Decode.decode prof.feat (fetchByte prof.feat s) = .ok (mk .movbe 32 [gr 32 r, .mem (mbi b i d 32)] len))
    (hld : Readable prof s (eaI s b i d) 4) :
    (instruction prof s).runStream o t = (.running (nx s len (s.cpu.gpr.set (regOf r)
      ((ZellicX86.bswap (ofBytesLE 32 (readBytes s.proc.mm.mem (eaI s b i d) 4))).setWidth 64)) (rf0 s)) none, t) := by
  refine instruction_next htf hdec ?_
  simp only [exec, Sem.movbe, mk, mbi, gr, bind, Prog.bind, readOp, Bool.false_eq_true, ↓reduceIte, memRef,
    effOffset, pure, Prog.readReg, Prog.read, Prog.run, BitVec.mul_one, Opd.width, writeOp]
  rw [checkAccess_ok (s := advance s len) hac hld]
  rfl

/-- `tzcnt r32, r32'` (with BMI1) or `bsf r32, r32'` (without), of a source not 0: its lowest set bit. -/
theorem tzcnt_rr {r q len : Nat} (htf : s.cpu.rflags.tf = false)
    (hdec : Decode.decode prof.feat (fetchByte prof.feat s) = .ok (mk (.bit .tzcnt) 32 [gr 32 r, gr 32 q] len) ∨
      Decode.decode prof.feat (fetchByte prof.feat s) = .ok (mk (.bit .bsf) 32 [gr 32 r, gr 32 q] len))
    (hx : rv s 32 q ≠ 0) :
    ∃ fl t', (instruction prof s).runStream o t = (.running (nx s len (s.cpu.gpr.set (regOf r)
      ((BitVec.ofNat 32 (lowestSetBit (rv s 32 q))).setWidth 64)) fl) none, t') ∧
      fl.tf = s.cpu.rflags.tf ∧ fl.ac = s.cpu.rflags.ac ∧ fl.df = s.cpu.rflags.df := by
  rcases hdec with hdec | hdec
  · exact ⟨_, _, instruction_next htf hdec rfl, rfl, rfl, rfl⟩
  · refine ⟨?_, ?_, instruction_next htf hdec ?_, ?_, ?_, ?_⟩
    case refine_3 =>
      have hx' : ((advance s len).cpu.gpr.get (regOf q)).setWidth 32 ≠ 0 := hx
      simp only [exec, execBits, Sem.bsf, bitScan, mk, gr, bind, Prog.bind, readOp, Bool.false_eq_true, ↓reduceIte,
        pure, Prog.readReg, Prog.run, writeOp]
      simp only [hx', ↓reduceIte]
      rfl
    all_goals rfl

/-! ## Vector instructions -/

/-- The bytes `[x, y)` of a vector, equal where equal (`VPCMPEQB`). -/
abbrev eqb {w : Nat} (a b : BitVec w) : BitVec w :=
  lanes 8 (fun x y => if (x == y) = true then BitVec.allOnes 8 else 0) a b

/-- `vmovdqu xmmN/ymmN, [rB + d]`. -/
theorem vmovdqu_ld {w n b d len : Nat} (htf : s.cpu.rflags.tf = false) (hac : s.cpu.rflags.ac = false)
    (hdec : Decode.decode prof.feat (fetchByte prof.feat s) =
      .ok (mk (.avx .vmovdqu) 32 [.vreg n w, .mem (mbd b d w)] len))
    (hld : Readable prof s (eaD s b d) (w / 8)) :
    (instruction prof s).runStream o t =
      (.running (nxz s len s.cpu.gpr (rf0 s) (withZmm s.cpu.vec.zmm (xmmOf n)
        ((ofBytesLE w (readBytes s.proc.mm.mem (eaD s b d) (w / 8))).setWidth 512))) none, t) := by
  refine instruction_next htf hdec ?_
  simp only [exec, execAvx, Sem.vmovdqu, vmove, mk, mbd, maskBits, bind, Prog.bind, readSrc, Inst.masked,
    readOp, Bool.false_eq_true, ↓reduceIte, memRef, effOffset, pure, Prog.readReg, Prog.read, Prog.run,
    BitVec.mul_one, writeMasked, writeOp, Opd.width]
  rw [eaD_adv, checkAccess_ok (s := advance s len) hac hld]
  rfl

/-- `vmovq xmmN, qword [rB]`. -/
theorem vmovq_ld {n b len : Nat} (htf : s.cpu.rflags.tf = false) (hac : s.cpu.rflags.ac = false)
    (hdec : Decode.decode prof.feat (fetchByte prof.feat s) =
      .ok (mk (.avx .vmovq) 32 [.vreg n 128, .mem (mbd b 0 64)] len))
    (hld : Readable prof s (eaD s b 0) 8) :
    (instruction prof s).runStream o t =
      (.running (nxz s len s.cpu.gpr (rf0 s) (withZmm s.cpu.vec.zmm (xmmOf n)
        ((ofBytesLE 64 (readBytes s.proc.mm.mem (eaD s b 0) 8)).setWidth 512))) none, t) := by
  refine instruction_next htf hdec ?_
  simp only [exec, execAvx, Sem.vmovq, vmovLow, mk, mbd, bind, Prog.bind, readOp, Bool.false_eq_true, ↓reduceIte,
    memRef, effOffset, pure, Prog.readReg, Prog.read, Prog.run, BitVec.mul_one, writeOp, Opd.width]
  rw [eaD_adv, checkAccess_ok (s := advance s len) hac hld]
  rfl

/-- `vpcmpeqb vN, vA, [rB + d]`. -/
theorem vpcmpeqb_m {w n a b d len : Nat} (htf : s.cpu.rflags.tf = false) (hac : s.cpu.rflags.ac = false)
    (hdec : Decode.decode prof.feat (fetchByte prof.feat s) =
      .ok (mk (.avx (.vpcmpeq 8)) 32 [.vreg n w, .vreg a w, .mem (mbd b d w)] len))
    (hld : Readable prof s (eaD s b d) (w / 8)) :
    (instruction prof s).runStream o t =
      (.running (nxz s len s.cpu.gpr (rf0 s) (withZmm s.cpu.vec.zmm (xmmOf n)
        ((eqb ((s.cpu.vec.zmm (xmmOf a)).setWidth w)
          (ofBytesLE w (readBytes s.proc.mm.mem (eaD s b d) (w / 8)))).setWidth 512))) none, t) := by
  refine instruction_next htf hdec ?_
  simp only [exec, execAvx, Sem.vpcmpeq, vcompare, vbinop, mk, mbd, maskBits, bind, Prog.bind, readSrc,
    Inst.masked, readOp, Bool.false_eq_true, ↓reduceIte, memRef, effOffset, pure, Prog.readReg, Prog.read, Prog.run,
    BitVec.mul_one, writeMasked, writeOp, Opd.width, Prog.readZmm]
  rw [eaD_adv, checkAccess_ok (s := advance s len) hac hld]
  rfl

/-- `vpcmpeqb vN, vA, vC`. -/
theorem vpcmpeqb_r {w n a c len : Nat} (htf : s.cpu.rflags.tf = false)
    (hdec : Decode.decode prof.feat (fetchByte prof.feat s) =
      .ok (mk (.avx (.vpcmpeq 8)) 32 [.vreg n w, .vreg a w, .vreg c w] len)) :
    (instruction prof s).runStream o t =
      (.running (nxz s len s.cpu.gpr (rf0 s) (withZmm s.cpu.vec.zmm (xmmOf n)
        ((eqb ((s.cpu.vec.zmm (xmmOf a)).setWidth w) ((s.cpu.vec.zmm (xmmOf c)).setWidth w)).setWidth 512))) none, t) :=
  instruction_next htf hdec rfl

/-- `vpand ymmN, ymmA, ymmC`. -/
theorem vpand {n a c len : Nat} (htf : s.cpu.rflags.tf = false)
    (hdec : Decode.decode prof.feat (fetchByte prof.feat s) =
      .ok (mk (.avx .vpand) 32 [.vreg n 256, .vreg a 256, .vreg c 256] len)) :
    (instruction prof s).runStream o t =
      (.running (nxz s len s.cpu.gpr (rf0 s) (withZmm s.cpu.vec.zmm (xmmOf n)
        (((s.cpu.vec.zmm (xmmOf a)).setWidth 256 &&& (s.cpu.vec.zmm (xmmOf c)).setWidth 256).setWidth 512))) none, t) :=
  instruction_next htf hdec rfl

/-- `vpmovmskb r32, vN`. -/
theorem vpmovmskb {w r n len : Nat} (htf : s.cpu.rflags.tf = false)
    (hdec : Decode.decode prof.feat (fetchByte prof.feat s) =
      .ok (mk (.avx .vpmovmskb) 32 [gr 32 r, .vreg n w] len)) :
    (instruction prof s).runStream o t =
      (.running (nx s len (s.cpu.gpr.set (regOf r)
        ((ofBits 32 fun j => decide (j < w / 8) && (elem 8 ((s.cpu.vec.zmm (xmmOf n)).setWidth w) j).msb).setWidth 64))
        (rf0 s)) none, t) :=
  instruction_next htf hdec rfl

/-- `vptest ymmA, ymmC`. -/
theorem vptest {a c len : Nat} (htf : s.cpu.rflags.tf = false)
    (hdec : Decode.decode prof.feat (fetchByte prof.feat s) =
      .ok (mk (.avx .vptest) 32 [.vreg a 256, .vreg c 256] len)) :
    (instruction prof s).runStream o t =
      (.running (nx s len s.cpu.gpr { rf0 s with
        zf := ((s.cpu.vec.zmm (xmmOf a)).setWidth 256 &&& (s.cpu.vec.zmm (xmmOf c)).setWidth 256) == 0,
        cf := (~~~(s.cpu.vec.zmm (xmmOf a)).setWidth 256 &&& (s.cpu.vec.zmm (xmmOf c)).setWidth 256) == 0,
        af := false, of := false, pf := false, sf := false }) none, t) := by
  refine instruction_next htf hdec ?_
  simp only [exec, execAvx, Sem.vptest, mk, bind, Prog.bind, readOp, pure, Prog.run, Opd.width, Prog.readZmm,
    Prog.readFlags, Prog.writeFlags, done]
  rfl

/-- The vector registers `z` with bits 511–128 of `ZMM0` … `ZMM(n-1)` cleared, as `Sem.zeroUpper n` leaves them. -/
def zup : Nat → (Fin 32 → BitVec 512) → (Fin 32 → BitVec 512)
  | 0, z => z
  | n + 1, z => zup n (withZmm z (xmmOf n) (((z (xmmOf n)).setWidth 128).setWidth 512))

theorem run_zeroUpper (feat : Features) (sl : SplitLock) {α : Type} : ∀ (n : Nat) (s : State) (k : Unit → Prog α),
    Prog.run feat sl (Prog.bind (Sem.zeroUpper n) k) s =
      Prog.run feat sl (k ()) (s.modCpu fun c => { c with vec := { c.vec with zmm := zup n c.vec.zmm } })
  | 0, s, k => rfl
  | n + 1, s, k => by
    simp only [Sem.zeroUpper, bind, Prog.bind, Prog.readZmm, Prog.writeZmm, Prog.run]
    rw [run_zeroUpper feat sl n]
    rfl

/-- `vzeroupper`: the vector registers change, nothing else. -/
theorem vzeroupper {len : Nat} (htf : s.cpu.rflags.tf = false)
    (hdec : Decode.decode prof.feat (fetchByte prof.feat s) = .ok (mk (.avx .vzeroupper) 32 [] len)) :
    (instruction prof s).runStream o t =
      (.running (nxz s len s.cpu.gpr (rf0 s) (zup 16 s.cpu.vec.zmm)) none, t) := by
  refine instruction_next htf hdec ?_
  simp only [exec, execAvx, Sem.vzeroupper, Sem.vzeroCheck, mk, bind, Prog.bind, pure, Nat.reduceEqDiff,
    ↓reduceIte, Prog.run, Bool.false_eq_true]
  rw [run_zeroUpper]
  rfl

/-- `ret`, to the address `ra` on top of the stack. -/
theorem ret {ra : Addr} (htf : s.cpu.rflags.tf = false) (hac : s.cpu.rflags.ac = false)
    (hdec : Decode.decode prof.feat (fetchByte prof.feat s) = .ok (mk .ret 64 [] 1))
    (hsh : s.thread.shstk = none)
    (hw : ofBytesLE 64 (readBytes s.proc.mm.mem s.cpu.gpr.rsp 8) = ra) (hcan : ra.canonical prof.feat.la57 = true)
    (hld : Readable prof s s.cpu.gpr.rsp 8) :
    (instruction prof s).runStream o t =
      (.running (upd s ra (s.cpu.gpr.set 4 (s.cpu.gpr.rsp + 8)) (rf0 s)) none, t) := by
  refine instruction_next htf hdec ?_
  simp only [exec, Sem.ret, mk, Prog.run, bind, Prog.bind, Prog.readThread, Prog.readReg, Prog.read, pure,
    show (advance s 1).thread.shstk = none from hsh, Bool.false_eq_true, ↓reduceIte]
  rw [checkAccess_ok (s := advance s 1) hac hld]
  have hw' : ofBytesLE 64 (readBytes (advance s 1).proc.mm.mem ((advance s 1).cpu.gpr.get 4) 8) = ra := hw
  simp only [Nat.reduceDiv, hw', hcan, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  rfl

end FV7z
