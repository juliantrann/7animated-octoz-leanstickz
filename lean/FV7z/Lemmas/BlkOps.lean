import FV7z.Lemmas.Blk
import FV7z.Lemmas.FnSib
/-!
# What the instructions of compiled code do (PLAN.md G2, pilot `LzmaDec_DecodeReal_3`)

For each form of instruction of `LzmaDec_DecodeReal_3` (83 forms of the model's decoder in its 1433 instructions,
measured with `decshow`), its effect as an `Op` of `Blk.lean` and the proof (`OpI`). A register or immediate source is
one argument (`Src`), a memory operand `[b + i·sc + d]` with base and index optional another (`mg`), so one lemma
covers the forms of an instruction.

The flags: exact after `sub`, `cmp`, `add`, `inc`, `dec`, `neg` and the moves; after the logical instructions up to
`AF`, which the manuals leave undefined; unconstrained after shifts, `imul` and `sbb`, whose flags the code does not
read (measured: the `jcc`, `cmovcc` and `sbb` of the function read the flags of `sub`, `cmp`, `test`, `or`, `inc`,
`dec` only).
-/
namespace FV7z
open ZellicX86 Decode

/-- Register `r` as a `w`-bit operand. -/
abbrev gv (g : Gprs) (w r : Nat) : BitVec w := (g.get (regOf r)).setWidth w

/-- Register `r` written with a 32- or 64-bit value: zero-extended. -/
abbrev wr (g : Gprs) (r : Nat) {w : Nat} (v : BitVec w) : Gprs := g.set (regOf r) (v.setWidth 64)

/-- Register `r` written with an 8- or 16-bit value: the other bits kept. -/
abbrev wrLo (g : Gprs) (r : Nat) {w : Nat} (v : BitVec w) : Gprs :=
  g.set (regOf r) ((g.get (regOf r) &&& ~~~(BitVec.ofNat 64 ((2 ^ w - 1) * 2 ^ 0))) ||| (v.setWidth 64 <<< 0))

/-- A source operand: a register or an immediate. -/
inductive Src where
  | r (n : Nat)
  | i (v : Nat)

/-- The operand, `w` bits wide. -/
def Src.opd (w : Nat) : Src → Opd
  | .r n => gr w n
  | .i v => .imm w v

/-- Its value. -/
def Src.val (w : Nat) (g : Gprs) : Src → BitVec w
  | .r n => gv g w n
  | .i v => BitVec.ofNat w v

/-- The memory operand `[b + i·sc + disp]` of `width` bits, base and index optional. -/
def mg (b i : Option Nat) (sc disp width : Nat) : MemOp :=
  { seg := none, base := b, index := i, scale := sc, disp, ripRel := false, addr32 := false, width }

/-- An optional register's value: `0` without one. -/
def optV (g : Gprs) : Option Nat → Addr
  | some b => g.get (regOf b)
  | none => 0

/-- The address `[b + i·sc + d]`. -/
abbrev eaG (g : Gprs) (b i : Option Nat) (sc d : Nat) : Addr :=
  optV g b + optV g i * BitVec.ofNat 64 sc + BitVec.ofNat 64 d

/-- The flags a logical instruction with result `r` leaves: `AF` undefined. -/
def LogF {w : Nat} (f : Rflags) (r : BitVec w) (fl : Rflags) : Prop := ∃ af, fl = (rfz f).arith r false false af

namespace Op

/-! ## Registers alone -/

/-- `sub r, x`. -/
def sub (w r : Nat) (x : Src) : Op :=
  .reg (fun g _ => wr g r (subR (gv g w r) (x.val w g))) fun g f fl => fl = subF (rfz f) (gv g w r) (x.val w g)
/-- `cmp r, x`. -/
def cmp (w r : Nat) (x : Src) : Op :=
  .reg (fun g _ => g) fun g f fl => fl = subF (rfz f) (gv g w r) (x.val w g)
/-- `add r, x`. -/
def add (w r : Nat) (x : Src) : Op :=
  .reg (fun g _ => wr g r (addR (gv g w r) (x.val w g))) fun g f fl => fl = addF (rfz f) (gv g w r) (x.val w g)
/-- `add r8, x`. -/
def add8 (r : Nat) (x : Src) : Op :=
  .reg (fun g _ => wrLo g r (addR (gv g 8 r) (x.val 8 g))) fun g f fl => fl = addF (rfz f) (gv g 8 r) (x.val 8 g)
/-- `and r, x`. -/
def and (w r : Nat) (x : Src) : Op :=
  .reg (fun g _ => wr g r (gv g w r &&& x.val w g)) fun g f fl => LogF f (gv g w r &&& x.val w g) fl
/-- `or r, x`. -/
def or (w r : Nat) (x : Src) : Op :=
  .reg (fun g _ => wr g r (gv g w r ||| x.val w g)) fun g f fl => LogF f (gv g w r ||| x.val w g) fl
/-- `xor r, x`. -/
def xor (w r : Nat) (x : Src) : Op :=
  .reg (fun g _ => wr g r (gv g w r ^^^ x.val w g)) fun g f fl => LogF f (gv g w r ^^^ x.val w g) fl
/-- `test r, x`. -/
def test (w r : Nat) (x : Src) : Op :=
  .reg (fun g _ => g) fun g f fl => LogF f (gv g w r &&& x.val w g) fl
/-- `inc r`: `CF` kept. -/
def inc (w r : Nat) : Op :=
  .reg (fun g _ => wr g r (addR (gv g w r) 1)) fun g f fl => fl = { addF (rfz f) (gv g w r) 1 with cf := f.cf }
/-- `dec r`: `CF` kept. -/
def dec (w r : Nat) : Op :=
  .reg (fun g _ => wr g r (subR (gv g w r) 1)) fun g f fl => fl = { subF (rfz f) (gv g w r) 1 with cf := f.cf }
/-- `neg r`. -/
def neg (w r : Nat) : Op :=
  .reg (fun g _ => wr g r (subR 0 (gv g w r))) fun g f fl => fl = subF (rfz f) 0 (gv g w r)
/-- `sbb r, x`. -/
def sbb (w r : Nat) (x : Src) : Op :=
  .reg (fun g f => wr g r (gv g w r - x.val w g - (BitVec.ofBool f.cf).setWidth w)) fun _ _ _ => True
/-- `mov r, x`. -/
def mov (w r : Nat) (x : Src) : Op :=
  .reg (fun g _ => wr g r (x.val w g)) fun _ f fl => fl = rfz f
/-- `cmovcc r32, q`: the register is written either way. -/
def cmov32 (cc : Cond) (r q : Nat) : Op :=
  .reg (fun g f => wr g r (if f.cond cc then gv g 32 q else gv g 32 r)) fun _ f fl => fl = rfz f
/-- `cmovcc r64, q`. -/
def cmov64 (cc : Cond) (r q : Nat) : Op :=
  .reg (fun g f => if f.cond cc then wr g r (gv g 64 q) else g) fun _ f fl => fl = rfz f
/-- `imul r32, q`. -/
def imul (r q : Nat) : Op :=
  .reg (fun g _ => wr g r (((gv g 32 r).signExtend (2 * 32) * (gv g 32 q).signExtend (2 * 32)).setWidth 32))
    fun _ _ _ => True
/-- `nop`. -/
def nop : Op := .reg (fun g _ => g) fun _ f fl => fl = rfz f

/-- `shl r32, x`: the count taken modulo 32. -/
def shl (r : Nat) (x : Src) : Op :=
  .reg (fun g _ => wr g r (gv g 32 r <<< ((x.val 8 g).toNat % 32))) fun _ _ _ => True
/-- `shr r32, x`. -/
def shr (r : Nat) (x : Src) : Op :=
  .reg (fun g _ => wr g r (gv g 32 r >>> ((x.val 8 g).toNat % 32))) fun _ _ _ => True
/-- `sar r32, x`. -/
def sar (r : Nat) (x : Src) : Op :=
  .reg (fun g _ => wr g r ((gv g 32 r).sshiftRight ((x.val 8 g).toNat % 32))) fun _ _ _ => True
/-- `lea r, [b + i·sc + d]`. -/
def lea (w r : Nat) (b i : Option Nat) (sc d : Nat) : Op :=
  .reg (fun g _ => wr g r ((eaG g b i sc d).setWidth w)) fun _ f fl => fl = rfz f
/-- `lea r32, [b + i·sc + d]` with a 32-bit address. -/
def lea32a (r : Nat) (b i : Option Nat) (sc d : Nat) : Op :=
  .reg (fun g _ => wr g r ((((eaG g b i sc d).setWidth 32).setWidth 64).setWidth 32)) fun _ f fl => fl = rfz f

/-! ## Loads -/

/-- `mov r, [m]`. -/
def ld (w r : Nat) (b i : Option Nat) (sc d : Nat) : Op :=
  .load (w / 8) (fun g => eaG g b i sc d) (fun g _ bs => wr g r (ofBytesLE w bs)) fun _ f _ fl => fl = rfz f
/-- `mov r8, [m]`: bits 63–8 kept. -/
def ld8 (r : Nat) (b i : Option Nat) (sc d : Nat) : Op :=
  .load 1 (fun g => eaG g b i sc d) (fun g _ bs => wrLo g r (ofBytesLE 8 bs)) fun _ f _ fl => fl = rfz f
/-- `movzx r32, [m]` of `v` bits. -/
def ldzx (v r : Nat) (b i : Option Nat) (sc d : Nat) : Op :=
  .load (v / 8) (fun g => eaG g b i sc d) (fun g _ bs => wr g r ((ofBytesLE v bs).setWidth 32))
    fun _ f _ fl => fl = rfz f
/-- `sub r, [m]`. -/
def subm (w r : Nat) (b i : Option Nat) (sc d : Nat) : Op :=
  .load (w / 8) (fun g => eaG g b i sc d) (fun g _ bs => wr g r (subR (gv g w r) (ofBytesLE w bs)))
    fun g f bs fl => fl = subF (rfz f) (gv g w r) (ofBytesLE w bs)
/-- `cmp r, [m]`. -/
def cmpm (w r : Nat) (b i : Option Nat) (sc d : Nat) : Op :=
  .load (w / 8) (fun g => eaG g b i sc d) (fun g _ _ => g)
    fun g f bs fl => fl = subF (rfz f) (gv g w r) (ofBytesLE w bs)
/-- `add r, [m]`. -/
def addm (w r : Nat) (b i : Option Nat) (sc d : Nat) : Op :=
  .load (w / 8) (fun g => eaG g b i sc d) (fun g _ bs => wr g r (addR (gv g w r) (ofBytesLE w bs)))
    fun g f bs fl => fl = addF (rfz f) (gv g w r) (ofBytesLE w bs)
/-- `and r, [m]`. -/
def andm (w r : Nat) (b i : Option Nat) (sc d : Nat) : Op :=
  .load (w / 8) (fun g => eaG g b i sc d) (fun g _ bs => wr g r (gv g w r &&& ofBytesLE w bs))
    fun g f bs fl => LogF f (gv g w r &&& ofBytesLE w bs) fl
/-- `pop r`. -/
def pop (r : Nat) : Op :=
  .load 8 (fun g => g.rsp) (fun g _ bs => (g.set 4 (g.rsp + 8)).set (regOf r) ((ofBytesLE 64 bs).setWidth 64))
    fun _ f _ fl => fl = rfz f

/-! ## Stores -/

/-- `mov [m], r`. -/
def st (w : Nat) (b i : Option Nat) (sc d r : Nat) : Op :=
  .store (w / 8) (fun g => eaG g b i sc d) (fun g => toBytesLE (gv g w r) (w / 8)) fun g => g
/-- `mov [m], imm`. -/
def sti (w : Nat) (b i : Option Nat) (sc d v : Nat) : Op :=
  .store (w / 8) (fun g => eaG g b i sc d) (fun _ => toBytesLE (BitVec.ofNat w v) (w / 8)) fun g => g
/-- `push r`. -/
def push (r : Nat) : Op :=
  .store 8 (fun g => g.rsp - 8) (fun g => toBytesLE (gv g 64 r) 8) fun g => g.set 4 (g.rsp - 8)

end Op

section
set_option linter.unusedSimpArgs false
variable {prof : Profile}

theorem OpI.sub {w r len : Nat} (x : Src) (hw : w = 32 ∨ w = 64) :
    OpI prof (mk .sub w [gr w r, x.opd w] len) (Op.sub w r x) := fun s o t htf hdec => by
  rcases hw with rfl | rfl <;> cases x <;> exact ⟨_, _, instruction_next htf hdec rfl, rfl, rfl, rfl, rfl⟩

theorem OpI.cmp {w r len : Nat} (x : Src) (hw : w = 32 ∨ w = 64) :
    OpI prof (mk .cmp w [gr w r, x.opd w] len) (Op.cmp w r x) := fun s o t htf hdec => by
  rcases hw with rfl | rfl <;> cases x <;> exact ⟨_, _, instruction_next htf hdec rfl, rfl, rfl, rfl, rfl⟩

theorem OpI.add {w r len : Nat} (x : Src) (hw : w = 32 ∨ w = 64) :
    OpI prof (mk .add w [gr w r, x.opd w] len) (Op.add w r x) := fun s o t htf hdec => by
  rcases hw with rfl | rfl <;> cases x <;> exact ⟨_, _, instruction_next htf hdec rfl, rfl, rfl, rfl, rfl⟩

theorem OpI.add8 {r len : Nat} (x : Src) :
    OpI prof (mk .add 8 [gr 8 r, x.opd 8] len) (Op.add8 r x) := fun s o t htf hdec => by
  cases x <;> exact ⟨_, _, instruction_next htf hdec rfl, rfl, rfl, rfl, rfl⟩

theorem OpI.and {w r len : Nat} (x : Src) (hw : w = 32 ∨ w = 64) :
    OpI prof (mk .and w [gr w r, x.opd w] len) (Op.and w r x) := fun s o t htf hdec => by
  rcases hw with rfl | rfl <;> cases x <;> exact ⟨_, _, instruction_next htf hdec rfl, ⟨_, rfl⟩, rfl, rfl, rfl⟩

theorem OpI.or {w r len : Nat} (x : Src) (hw : w = 32 ∨ w = 64) :
    OpI prof (mk .or w [gr w r, x.opd w] len) (Op.or w r x) := fun s o t htf hdec => by
  rcases hw with rfl | rfl <;> cases x <;> exact ⟨_, _, instruction_next htf hdec rfl, ⟨_, rfl⟩, rfl, rfl, rfl⟩

theorem OpI.xor {w r len : Nat} (x : Src) (hw : w = 32 ∨ w = 64) :
    OpI prof (mk .xor w [gr w r, x.opd w] len) (Op.xor w r x) := fun s o t htf hdec => by
  rcases hw with rfl | rfl <;> cases x <;> exact ⟨_, _, instruction_next htf hdec rfl, ⟨_, rfl⟩, rfl, rfl, rfl⟩

theorem OpI.test {w r len : Nat} (x : Src) (hw : w = 32 ∨ w = 64) :
    OpI prof (mk .test w [gr w r, x.opd w] len) (Op.test w r x) := fun s o t htf hdec => by
  rcases hw with rfl | rfl <;> cases x <;> exact ⟨_, _, instruction_next htf hdec rfl, ⟨_, rfl⟩, rfl, rfl, rfl⟩

theorem OpI.inc {w r len : Nat} (hw : w = 32 ∨ w = 64) :
    OpI prof (mk .inc w [gr w r] len) (Op.inc w r) := fun s o t htf hdec => by
  rcases hw with rfl | rfl <;> exact ⟨_, _, instruction_next htf hdec rfl, rfl, rfl, rfl, rfl⟩

theorem OpI.dec {w r len : Nat} (hw : w = 32 ∨ w = 64) :
    OpI prof (mk .dec w [gr w r] len) (Op.dec w r) := fun s o t htf hdec => by
  rcases hw with rfl | rfl <;> exact ⟨_, _, instruction_next htf hdec rfl, rfl, rfl, rfl, rfl⟩

theorem OpI.neg {w r len : Nat} (hw : w = 32 ∨ w = 64) :
    OpI prof (mk .neg w [gr w r] len) (Op.neg w r) := fun s o t htf hdec => by
  rcases hw with rfl | rfl <;> exact ⟨_, _, instruction_next htf hdec rfl, rfl, rfl, rfl, rfl⟩

theorem OpI.sbb {w r len : Nat} (x : Src) (hw : w = 32 ∨ w = 64) :
    OpI prof (mk .sbb w [gr w r, x.opd w] len) (Op.sbb w r x) := fun s o t htf hdec => by
  rcases hw with rfl | rfl <;> cases x <;> exact ⟨_, _, instruction_next htf hdec rfl, trivial, rfl, rfl, rfl⟩

theorem OpI.mov {w r len : Nat} (x : Src) (hw : w = 32 ∨ w = 64) :
    OpI prof (mk .mov w [gr w r, x.opd w] len) (Op.mov w r x) := fun s o t htf hdec => by
  rcases hw with rfl | rfl <;> cases x <;> exact ⟨_, _, instruction_next htf hdec rfl, rfl, rfl, rfl, rfl⟩

theorem OpI.imul {r q len : Nat} :
    OpI prof (mk .imul 32 [gr 32 r, gr 32 q] len) (Op.imul r q) := fun _ _ _ htf hdec =>
  ⟨_, _, instruction_next htf hdec rfl, trivial, rfl, rfl, rfl⟩

theorem OpI.nop {w len : Nat} {ops : List Opd} :
    OpI prof (mk .nop w ops len) Op.nop := fun _ _ _ htf hdec =>
  ⟨_, _, instruction_next htf hdec rfl, rfl, rfl, rfl, rfl⟩

theorem rfz_cond (f : Rflags) (cc : Cond) : (rfz f).cond cc = f.cond cc := by
  unfold Rflags.cond; split <;> rfl

theorem OpI.cmov32 {cc : Cond} {r q len : Nat} :
    OpI prof (mk (.cmovcc cc) 32 [gr 32 r, gr 32 q] len) (Op.cmov32 cc r q) := by
  dsimp only [Op.cmov32, OpI]
  intro s o t htf hdec
  have hc' : (advance s len).cpu.rflags.cond cc = s.cpu.rflags.cond cc := rfz_cond _ cc
  cases hc : s.cpu.rflags.cond cc <;> rw [hc] at hc' <;>
  · refine ⟨_, t, instruction_next htf hdec ?_, rfl, rfl, rfl, rfl⟩
    simp only [exec, Sem.cmovcc, mk, gr, bind, Prog.bind, readOp, writeOp, Prog.readReg, Prog.readFlags,
      Prog.writeReg, Bool.false_eq_true, ↓reduceIte, pure, Prog.run, done, hc']
    rfl

theorem OpI.cmov64 {cc : Cond} {r q len : Nat} :
    OpI prof (mk (.cmovcc cc) 64 [gr 64 r, gr 64 q] len) (Op.cmov64 cc r q) := by
  dsimp only [Op.cmov64, OpI]
  intro s o t htf hdec
  have hc' : (advance s len).cpu.rflags.cond cc = s.cpu.rflags.cond cc := rfz_cond _ cc
  cases hc : s.cpu.rflags.cond cc <;> rw [hc] at hc' <;>
  · refine ⟨_, t, instruction_next htf hdec ?_, rfl, rfl, rfl, rfl⟩
    simp only [exec, Sem.cmovcc, mk, gr, bind, Prog.bind, readOp, writeOp, Prog.readReg, Prog.readFlags,
      Prog.writeReg, Bool.false_eq_true, ↓reduceIte, pure, Prog.run, done, hc']
    rfl

theorem OpI.lea {w r len sc d : Nat} {b i : Option Nat} (hw : w = 32 ∨ w = 64) :
    OpI prof (mk .lea w [gr w r, .mem (mg b i sc d 0)] len) (Op.lea w r b i sc d) := by
  dsimp only [Op.lea, OpI]
  intro s o t htf hdec
  refine ⟨_, t, instruction_next htf hdec ?_, rfl, rfl, rfl, rfl⟩
  rcases hw with rfl | rfl <;> cases b <;> cases i <;>
  · simp only [exec, Sem.lea, mk, mg, gr, effOffset, Prog.run, bind, Prog.bind, pure, Prog.readReg,
      Bool.false_eq_true, ↓reduceIte, writeOp]
    rfl

theorem OpI.ld {w r len sc d : Nat} {b i : Option Nat} (hw : w = 32 ∨ w = 64) :
    OpI prof (mk .mov w [gr w r, .mem (mg b i sc d w)] len) (Op.ld w r b i sc d) := by
  dsimp only [Op.ld, OpI]
  intro s o t htf hac hdec hld
  refine ⟨_, t, instruction_next htf hdec ?_, rfl, rfl, rfl, rfl⟩
  rcases hw with rfl | rfl <;> cases b <;> cases i <;>
  · simp only [exec, Sem.mov, mk, mg, gr, bind, Prog.bind, readOp, Bool.false_eq_true, ↓reduceIte, memRef,
      effOffset, pure, Prog.readReg, Prog.read, Prog.run, writeOp]
    rw [checkAccess_ok (s := advance s len) hac hld]
    rfl

theorem OpI.ld8 {r len sc d : Nat} {b i : Option Nat} :
    OpI prof (mk .mov 8 [gr 8 r, .mem (mg b i sc d 8)] len) (Op.ld8 r b i sc d) := by
  dsimp only [Op.ld8, OpI]
  intro s o t htf hac hdec hld
  refine ⟨_, t, instruction_next htf hdec ?_, rfl, rfl, rfl, rfl⟩
  cases b <;> cases i <;>
  · simp only [exec, Sem.mov, mk, mg, gr, bind, Prog.bind, readOp, Bool.false_eq_true, ↓reduceIte, memRef,
      effOffset, pure, Prog.readReg, Prog.read, Prog.run, writeOp, Prog.readFlags]
    rw [checkAccess_ok (s := advance s len) hac hld]
    rfl

theorem OpI.ldzx {v r len sc d : Nat} {b i : Option Nat} (hw : v = 8 ∨ v = 16) :
    OpI prof (mk .movzx 32 [gr 32 r, .mem (mg b i sc d v)] len) (Op.ldzx v r b i sc d) := by
  dsimp only [Op.ldzx, OpI]
  intro s o t htf hac hdec hld
  refine ⟨_, t, instruction_next htf hdec ?_, rfl, rfl, rfl, rfl⟩
  rcases hw with rfl | rfl <;> cases b <;> cases i <;>
  · simp only [exec, Sem.movzx, mk, mg, gr, bind, Prog.bind, readOp, Bool.false_eq_true, ↓reduceIte, memRef,
      effOffset, pure, Prog.readReg, Prog.read, Prog.run, writeOp, Prog.readFlags, Opd.width]
    rw [checkAccess_ok (s := advance s len) hac hld]
    rfl

theorem OpI.subm {w r len sc d : Nat} {b i : Option Nat} (hw : w = 32 ∨ w = 64) :
    OpI prof (mk .sub w [gr w r, .mem (mg b i sc d w)] len) (Op.subm w r b i sc d) := by
  dsimp only [Op.subm, OpI]
  intro s o t htf hac hdec hld
  refine ⟨_, t, instruction_next htf hdec ?_, rfl, rfl, rfl, rfl⟩
  rcases hw with rfl | rfl <;> cases b <;> cases i <;>
  · simp only [exec, Sem.sub, alu, subOp, mk, mg, gr, bind, Prog.bind, readOp, Bool.false_eq_true, ↓reduceIte, memRef,
      effOffset, pure, Prog.readReg, Prog.read, Prog.run, writeOp, Prog.readFlags]
    rw [checkAccess_ok (s := advance s len) hac hld]
    rfl

theorem OpI.cmpm {w r len sc d : Nat} {b i : Option Nat} (hw : w = 32 ∨ w = 64) :
    OpI prof (mk .cmp w [gr w r, .mem (mg b i sc d w)] len) (Op.cmpm w r b i sc d) := by
  dsimp only [Op.cmpm, OpI]
  intro s o t htf hac hdec hld
  refine ⟨_, t, instruction_next htf hdec ?_, rfl, rfl, rfl, rfl⟩
  rcases hw with rfl | rfl <;> cases b <;> cases i <;>
  · simp only [exec, Sem.cmp, alu, subOp, mk, mg, gr, bind, Prog.bind, readOp, Bool.false_eq_true, ↓reduceIte, memRef,
      effOffset, pure, Prog.readReg, Prog.read, Prog.run, writeOp, Prog.readFlags]
    rw [checkAccess_ok (s := advance s len) hac hld]
    rfl

theorem OpI.addm {w r len sc d : Nat} {b i : Option Nat} (hw : w = 32 ∨ w = 64) :
    OpI prof (mk .add w [gr w r, .mem (mg b i sc d w)] len) (Op.addm w r b i sc d) := by
  dsimp only [Op.addm, OpI]
  intro s o t htf hac hdec hld
  refine ⟨_, t, instruction_next htf hdec ?_, rfl, rfl, rfl, rfl⟩
  rcases hw with rfl | rfl <;> cases b <;> cases i <;>
  · simp only [exec, Sem.add, alu, addOp, mk, mg, gr, bind, Prog.bind, readOp, Bool.false_eq_true, ↓reduceIte, memRef,
      effOffset, pure, Prog.readReg, Prog.read, Prog.run, writeOp, Prog.readFlags]
    rw [checkAccess_ok (s := advance s len) hac hld]
    rfl

theorem OpI.pop {r len : Nat} : OpI prof (mk .pop 64 [gr 64 r] len) (Op.pop r) := by
  dsimp only [Op.pop, OpI]
  intro s o t htf hac hdec hld
  refine ⟨_, t, instruction_next htf hdec ?_, rfl, rfl, rfl, rfl⟩
  simp only [exec, Sem.pop, pop64, gr, writeOp, Prog.run, bind, Prog.bind, Prog.readReg, Prog.read, Prog.writeReg,
    pure, Bool.false_eq_true, ↓reduceIte, ne_eq, not_true_eq_false]
  rw [checkAccess_ok (s := advance s len) hac hld]
  rfl

theorem OpI.st {w r len sc d : Nat} {b i : Option Nat} (hw : w = 8 ∨ w = 16 ∨ w = 32 ∨ w = 64) :
    OpI prof (mk .mov w [.mem (mg b i sc d w), gr w r] len) (Op.st w b i sc d r) := by
  dsimp only [Op.st, OpI]
  intro s o t htf hac hdec _ hwr
  refine ⟨t, instruction_next htf hdec ?_⟩
  rcases hw with rfl | rfl | rfl | rfl <;> cases b <;> cases i <;>
  · simp only [exec, Sem.mov, mk, mg, gr, bind, Prog.bind, readOp, Bool.false_eq_true, ↓reduceIte, memRef,
      effOffset, pure, Prog.readReg, Prog.write, Prog.run, writeOp]
    rw [checkAccess_ok (s := advance s len) hac hwr]
    rfl

theorem OpI.sti {w v len sc d : Nat} {b i : Option Nat} (hw : w = 8 ∨ w = 16 ∨ w = 32 ∨ w = 64) :
    OpI prof (mk .mov w [.mem (mg b i sc d w), .imm w v] len) (Op.sti w b i sc d v) := by
  dsimp only [Op.sti, OpI]
  intro s o t htf hac hdec _ hwr
  refine ⟨t, instruction_next htf hdec ?_⟩
  rcases hw with rfl | rfl | rfl | rfl <;> cases b <;> cases i <;>
  · simp only [exec, Sem.mov, mk, mg, gr, bind, Prog.bind, readOp, Bool.false_eq_true, ↓reduceIte, memRef,
      effOffset, pure, Prog.readReg, Prog.write, Prog.run, writeOp]
    rw [checkAccess_ok (s := advance s len) hac hwr]
    rfl

theorem OpI.push {r len : Nat} : OpI prof (mk .push 64 [gr 64 r] len) (Op.push r) := by
  dsimp only [Op.push, OpI]
  intro s o t htf hac hdec _ hwr
  refine ⟨t, instruction_next htf hdec ?_⟩
  simp only [exec, Sem.push, push64, gr, readOp, Prog.run, bind, Prog.bind, Prog.readReg, Prog.write, Prog.writeReg,
    pure, Bool.false_eq_true, ↓reduceIte, ne_eq, not_true_eq_false]
  rw [checkAccess_ok (s := advance s len) hac hwr]
  rfl

theorem OpI.andm {w r len sc d : Nat} {b i : Option Nat} (hw : w = 32 ∨ w = 64) :
    OpI prof (mk .and w [gr w r, .mem (mg b i sc d w)] len) (Op.andm w r b i sc d) := by
  dsimp only [Op.andm, OpI]
  intro s o t htf hac hdec hld
  refine ⟨_, ?t', instruction_next htf hdec ?h, ⟨?af, rfl⟩, rfl, rfl, rfl⟩
  case h =>
    rcases hw with rfl | rfl <;> cases b <;> cases i <;>
    · simp only [exec, Sem.and, alu, logicOp, mk, mg, gr, bind, Prog.bind, readOp, Bool.false_eq_true, ↓reduceIte,
        memRef, effOffset, pure, Prog.readReg, Prog.read, Prog.run, writeOp, Prog.readFlags]
      rw [checkAccess_ok (s := advance s len) hac hld]
      rfl

/-- The memory operand `[b + i·sc + disp]` with a 32-bit address (prefix `67`). -/
def mga (b i : Option Nat) (sc disp width : Nat) : MemOp :=
  { seg := none, base := b, index := i, scale := sc, disp, ripRel := false, addr32 := true, width }

theorem OpI.lea32a {r len sc d : Nat} {b i : Option Nat} :
    OpI prof (mk .lea 32 [gr 32 r, .mem (mga b i sc d 0)] len) (Op.lea32a r b i sc d) := by
  dsimp only [Op.lea32a, OpI]
  intro s o t htf hdec
  refine ⟨_, t, instruction_next htf hdec ?_, rfl, rfl, rfl, rfl⟩
  cases b <;> cases i <;>
  · simp only [exec, Sem.lea, mk, mga, gr, effOffset, Prog.run, bind, Prog.bind, pure, Prog.readReg,
      Bool.false_eq_true, ↓reduceIte, writeOp]
    rfl

theorem advance_gpr (s : State) (len : Nat) : (advance s len).cpu.gpr = s.cpu.gpr := rfl

theorem OpI.shl {r len : Nat} (x : Src) : OpI prof (mk .shl 32 [gr 32 r, x.opd 8] len) (Op.shl r x) := by
  dsimp only [Op.shl, OpI]
  intro s o t htf hdec
  suffices h : ∃ fl t', ((exec prof (mk .shl 32 [gr 32 r, x.opd 8] len)).run prof.feat prof.linux.splitLock
      (advance s len)).runStream o t = (.ok .next (nx s len (wr s.cpu.gpr r
        (gv s.cpu.gpr 32 r <<< ((x.val 8 s.cpu.gpr).toNat % 32))) fl), t') ∧
      fl.tf = s.cpu.rflags.tf ∧ fl.ac = s.cpu.rflags.ac ∧ fl.df = s.cpu.rflags.df by
    obtain ⟨fl, t', h, h1, h2, h3⟩ := h
    exact ⟨fl, t', instruction_next htf hdec h, trivial, h1, h2, h3⟩
  cases x with
  | r q =>
    simp only [exec, Sem.shl, shiftInst, shiftRot, mk, gr, Src.opd, Src.val, gv, bind, Prog.bind, readOp,
      Bool.false_eq_true, ↓reduceIte, pure, Prog.readReg, Prog.run, writeOp, Prog.readFlags, advance_gpr,
      Nat.reduceEqDiff, or_true, false_or]
    by_cases h0 : (BitVec.setWidth 8 (s.cpu.gpr.get (regOf q))).toNat % 32 = 0
    · simp only [h0, ↓reduceIte, BitVec.shiftLeft_zero]
      exact ⟨_, _, rfl, rfl, rfl, rfl⟩
    · have hlt : (BitVec.setWidth 8 (s.cpu.gpr.get (regOf q))).toNat % 32 < 32 := Nat.mod_lt _ (by decide)
      by_cases h1 : (BitVec.setWidth 8 (s.cpu.gpr.get (regOf q))).toNat % 32 = 1 <;> simp only [h0, hlt, h1, ↓reduceIte] <;>
        exact ⟨_, _, rfl, rfl, rfl, rfl⟩
  | i v =>
    simp only [exec, Sem.shl, shiftInst, shiftRot, mk, gr, Src.opd, Src.val, gv, bind, Prog.bind, readOp,
      Bool.false_eq_true, ↓reduceIte, pure, Prog.readReg, Prog.run, writeOp, Prog.readFlags, advance_gpr,
      Nat.reduceEqDiff, or_true, false_or]
    by_cases h0 : (BitVec.ofNat 8 v).toNat % 32 = 0
    · simp only [h0, ↓reduceIte, BitVec.shiftLeft_zero]
      exact ⟨_, _, rfl, rfl, rfl, rfl⟩
    · have hlt : (BitVec.ofNat 8 v).toNat % 32 < 32 := Nat.mod_lt _ (by decide)
      by_cases h1 : (BitVec.ofNat 8 v).toNat % 32 = 1 <;> simp only [h0, hlt, h1, ↓reduceIte] <;>
        exact ⟨_, _, rfl, rfl, rfl, rfl⟩

theorem OpI.shr {r len : Nat} (x : Src) : OpI prof (mk .shr 32 [gr 32 r, x.opd 8] len) (Op.shr r x) := by
  dsimp only [Op.shr, OpI]
  intro s o t htf hdec
  suffices h : ∃ fl t', ((exec prof (mk .shr 32 [gr 32 r, x.opd 8] len)).run prof.feat prof.linux.splitLock
      (advance s len)).runStream o t = (.ok .next (nx s len (wr s.cpu.gpr r
        (gv s.cpu.gpr 32 r >>> ((x.val 8 s.cpu.gpr).toNat % 32))) fl), t') ∧
      fl.tf = s.cpu.rflags.tf ∧ fl.ac = s.cpu.rflags.ac ∧ fl.df = s.cpu.rflags.df by
    obtain ⟨fl, t', h, h1, h2, h3⟩ := h
    exact ⟨fl, t', instruction_next htf hdec h, trivial, h1, h2, h3⟩
  cases x with
  | r q =>
    simp only [exec, Sem.shr, shiftInst, shiftRot, mk, gr, Src.opd, Src.val, gv, bind, Prog.bind, readOp,
      Bool.false_eq_true, ↓reduceIte, pure, Prog.readReg, Prog.run, writeOp, Prog.readFlags, advance_gpr,
      Nat.reduceEqDiff, or_true, false_or]
    by_cases h0 : (BitVec.setWidth 8 (s.cpu.gpr.get (regOf q))).toNat % 32 = 0
    · simp only [h0, ↓reduceIte, BitVec.ushiftRight_zero]
      exact ⟨_, _, rfl, rfl, rfl, rfl⟩
    · have hlt : (BitVec.setWidth 8 (s.cpu.gpr.get (regOf q))).toNat % 32 < 32 := Nat.mod_lt _ (by decide)
      by_cases h1 : (BitVec.setWidth 8 (s.cpu.gpr.get (regOf q))).toNat % 32 = 1 <;> simp only [h0, hlt, h1, ↓reduceIte] <;>
        exact ⟨_, _, rfl, rfl, rfl, rfl⟩
  | i v =>
    simp only [exec, Sem.shr, shiftInst, shiftRot, mk, gr, Src.opd, Src.val, gv, bind, Prog.bind, readOp,
      Bool.false_eq_true, ↓reduceIte, pure, Prog.readReg, Prog.run, writeOp, Prog.readFlags, advance_gpr,
      Nat.reduceEqDiff, or_true, false_or]
    by_cases h0 : (BitVec.ofNat 8 v).toNat % 32 = 0
    · simp only [h0, ↓reduceIte, BitVec.ushiftRight_zero]
      exact ⟨_, _, rfl, rfl, rfl, rfl⟩
    · have hlt : (BitVec.ofNat 8 v).toNat % 32 < 32 := Nat.mod_lt _ (by decide)
      by_cases h1 : (BitVec.ofNat 8 v).toNat % 32 = 1 <;> simp only [h0, hlt, h1, ↓reduceIte] <;>
        exact ⟨_, _, rfl, rfl, rfl, rfl⟩

theorem OpI.sar {r len : Nat} (x : Src) : OpI prof (mk .sar 32 [gr 32 r, x.opd 8] len) (Op.sar r x) := by
  dsimp only [Op.sar, OpI]
  intro s o t htf hdec
  suffices h : ∃ fl t', ((exec prof (mk .sar 32 [gr 32 r, x.opd 8] len)).run prof.feat prof.linux.splitLock
      (advance s len)).runStream o t = (.ok .next (nx s len (wr s.cpu.gpr r
        ((gv s.cpu.gpr 32 r).sshiftRight ((x.val 8 s.cpu.gpr).toNat % 32))) fl), t') ∧
      fl.tf = s.cpu.rflags.tf ∧ fl.ac = s.cpu.rflags.ac ∧ fl.df = s.cpu.rflags.df by
    obtain ⟨fl, t', h, h1, h2, h3⟩ := h
    exact ⟨fl, t', instruction_next htf hdec h, trivial, h1, h2, h3⟩
  cases x with
  | r q =>
    simp only [exec, Sem.sar, shiftInst, shiftRot, mk, gr, Src.opd, Src.val, gv, bind, Prog.bind, readOp,
      Bool.false_eq_true, ↓reduceIte, pure, Prog.readReg, Prog.run, writeOp, Prog.readFlags, advance_gpr,
      Nat.reduceEqDiff, or_true, false_or]
    by_cases h0 : (BitVec.setWidth 8 (s.cpu.gpr.get (regOf q))).toNat % 32 = 0
    · simp only [h0, ↓reduceIte, BitVec.sshiftRight_zero]
      exact ⟨_, _, rfl, rfl, rfl, rfl⟩
    · have hlt : (BitVec.setWidth 8 (s.cpu.gpr.get (regOf q))).toNat % 32 < 32 := Nat.mod_lt _ (by decide)
      by_cases h1 : (BitVec.setWidth 8 (s.cpu.gpr.get (regOf q))).toNat % 32 = 1 <;> simp only [h0, hlt, h1, ↓reduceIte] <;>
        exact ⟨_, _, rfl, rfl, rfl, rfl⟩
  | i v =>
    simp only [exec, Sem.sar, shiftInst, shiftRot, mk, gr, Src.opd, Src.val, gv, bind, Prog.bind, readOp,
      Bool.false_eq_true, ↓reduceIte, pure, Prog.readReg, Prog.run, writeOp, Prog.readFlags, advance_gpr,
      Nat.reduceEqDiff, or_true, false_or]
    by_cases h0 : (BitVec.ofNat 8 v).toNat % 32 = 0
    · simp only [h0, ↓reduceIte, BitVec.sshiftRight_zero]
      exact ⟨_, _, rfl, rfl, rfl, rfl⟩
    · have hlt : (BitVec.ofNat 8 v).toNat % 32 < 32 := Nat.mod_lt _ (by decide)
      by_cases h1 : (BitVec.ofNat 8 v).toNat % 32 = 1 <;> simp only [h0, hlt, h1, ↓reduceIte] <;>
        exact ⟨_, _, rfl, rfl, rfl, rfl⟩

end

end FV7z
