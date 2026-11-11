import FV7z.Lemmas.Sp
import FV7z.Lemmas.InsRip
import FV7z.Lemmas.FnJt
/-!
# What more instructions of compiled code do (PLAN.md G3, startup)

The forms glibc's startup code in `7zzs` has beside those of `BlkOps.lean` (measured with `decshow` on
`__tunables_init`): `endbr64`, the 8-bit `cmp` and `test` of registers, `cmp` of a byte or a doubleword in memory with
an immediate, and the instructions with an operand `[rip + d]`: a load from a fixed address and `lea`. What the latter
do depends on where the instruction lies (`OpIA` of `Blk.lean`): at `x`, an instruction of `len` bytes addresses
`x + len + d`, the address `A` in the `Op`.

And those of `_dl_aux_init`: `setcc`, `xor r, [m]`, `movsxd r64, dword [m]`, `movzx` from and stores to a fixed address,
and the jump through a register of its jump table (`Sp.jmpr`).
-/
namespace FV7z
open ZellicX86 Decode

namespace Op

/-- `cmp [m], imm`. -/
def cmpmi (w : Nat) (b i : Option Nat) (sc d v : Nat) : Op :=
  .load (w / 8) (fun g => eaG g b i sc d) (fun g _ _ => g)
    fun _ f bs fl => fl = subF (rfz f) (ofBytesLE w bs) (BitVec.ofNat w v)

/-- `cmp [A], imm`, the address fixed. -/
def cmpmia (w A v : Nat) : Op :=
  .load (w / 8) (fun _ => BitVec.ofNat 64 A) (fun g _ _ => g)
    fun _ f bs fl => fl = subF (rfz f) (ofBytesLE w bs) (BitVec.ofNat w v)

/-- `mov r, [A]`, the address fixed. -/
def lda (w r A : Nat) : Op :=
  .load (w / 8) (fun _ => BitVec.ofNat 64 A) (fun g _ bs => wr g r (ofBytesLE w bs)) fun _ f _ fl => fl = rfz f

/-- `setcc r8`: bits 63–8 kept. -/
def setcc (cc : Cond) (r : Nat) : Op :=
  .reg (fun g f => wrLo g r ((BitVec.ofBool (f.cond cc)).setWidth 8)) fun _ f fl => fl = rfz f

/-- `xor r, [m]`. -/
def xorm (w r : Nat) (b i : Option Nat) (sc d : Nat) : Op :=
  .load (w / 8) (fun g => eaG g b i sc d) (fun g _ bs => wr g r (gv g w r ^^^ ofBytesLE w bs))
    fun g f bs fl => LogF f (gv g w r ^^^ ofBytesLE w bs) fl

/-- `movsxd r64, dword [m]`. -/
def ldsx (r : Nat) (b i : Option Nat) (sc d : Nat) : Op :=
  .load 4 (fun g => eaG g b i sc d) (fun g _ bs => wr g r ((ofBytesLE 32 bs).signExtend 64)) fun _ f _ fl => fl = rfz f

/-- `movzx r32, [A]` of `v` bits, the address fixed. -/
def ldzxa (v r A : Nat) : Op :=
  .load (v / 8) (fun _ => BitVec.ofNat 64 A) (fun g _ bs => wr g r ((ofBytesLE v bs).setWidth 32))
    fun _ f _ fl => fl = rfz f

/-- `mov [A], r`, the address fixed. -/
def sta (w A r : Nat) : Op :=
  .store (w / 8) (fun _ => BitVec.ofNat 64 A) (fun g => toBytesLE (gv g w r) (w / 8)) fun g => g

/-- `mov [A], imm`, the address fixed. -/
def stia (w A v : Nat) : Op :=
  .store (w / 8) (fun _ => BitVec.ofNat 64 A) (fun _ => toBytesLE (BitVec.ofNat w v) (w / 8)) fun g => g

end Op

section
set_option linter.unusedSimpArgs false
variable {prof : Profile}

theorem OpI.endbr {len : Nat} : OpI prof (mk .endbr64 32 [] len) Op.nop := fun _ _ _ htf hdec =>
  ⟨_, _, instruction_next htf hdec rfl, rfl, rfl, rfl, rfl⟩

theorem OpI.cmp8 {r len : Nat} (x : Src) :
    OpI prof (mk .cmp 8 [gr 8 r, x.opd 8] len) (Op.cmp 8 r x) := fun s o t htf hdec => by
  cases x <;> exact ⟨_, _, instruction_next htf hdec rfl, rfl, rfl, rfl, rfl⟩

theorem OpI.test8 {r len : Nat} (x : Src) :
    OpI prof (mk .test 8 [gr 8 r, x.opd 8] len) (Op.test 8 r x) := fun s o t htf hdec => by
  cases x <;> exact ⟨_, _, instruction_next htf hdec rfl, ⟨_, rfl⟩, rfl, rfl, rfl⟩

theorem OpI.cmpmi {w v len sc d : Nat} {b i : Option Nat} (hw : w = 8 ∨ w = 32) :
    OpI prof (mk .cmp w [.mem (mg b i sc d w), .imm w v] len) (Op.cmpmi w b i sc d v) := by
  dsimp only [Op.cmpmi, OpI]
  intro s o t htf hac hdec hld
  refine ⟨_, t, instruction_next htf hdec ?_, rfl, rfl, rfl, rfl⟩
  rcases hw with rfl | rfl <;> cases b <;> cases i <;>
  · simp only [exec, Sem.cmp, alu, subOp, mk, mg, gr, bind, Prog.bind, readOp, Bool.false_eq_true, ↓reduceIte, memRef,
      effOffset, pure, Prog.readReg, Prog.read, Prog.run, writeOp, Prog.readFlags]
    rw [checkAccess_ok (s := advance s len) hac hld]
    rfl

/-- `cmp qword [m], imm`. -/
theorem OpI.cmpmi64 {v len sc d : Nat} {b i : Option Nat} :
    OpI prof (mk .cmp 64 [.mem (mg b i sc d 64), .imm 64 v] len) (Op.cmpmi 64 b i sc d v) := by
  dsimp only [Op.cmpmi, OpI]
  intro s o t htf hac hdec hld
  refine ⟨_, t, instruction_next htf hdec ?_, rfl, rfl, rfl, rfl⟩
  cases b <;> cases i <;>
  · simp only [exec, Sem.cmp, alu, subOp, mk, mg, gr, bind, Prog.bind, readOp, Bool.false_eq_true, ↓reduceIte, memRef,
      effOffset, pure, Prog.readReg, Prog.read, Prog.run, writeOp, Prog.readFlags]
    rw [checkAccess_ok (s := advance s len) hac hld]
    rfl

/-- `cmp [rip + d], imm`, at `x`. -/
theorem OpIA.cmpmi_rip {w v len d A : Nat} {x : Addr} (hw : w = 32 ∨ w = 64)
    (hA : x.add len + BitVec.ofNat 64 d = BitVec.ofNat 64 A) :
    OpIA prof x (mk .cmp w [.mem (mrip d w), .imm w v] len) (Op.cmpmia w A v) := by
  dsimp only [Op.cmpmia, OpIA]
  intro s o t hrip htf hac hdec hld
  have he : eaR s len d = BitVec.ofNat 64 A := by rw [← hA, ← hrip]
  refine ⟨_, t, instruction_next htf hdec ?_, rfl, rfl, rfl, rfl⟩
  rcases hw with rfl | rfl <;>
  · simp only [exec, Sem.cmp, alu, subOp, mk, mrip, gr, bind, Prog.bind, readOp, Bool.false_eq_true, ↓reduceIte, memRef,
      effOffset, pure, Prog.readRip, Prog.read, Prog.run, Opd.width, writeOp, BitVec.mul_one, Prog.readFlags]
    rw [eaR_adv, he, checkAccess_ok (s := advance s len) hac hld]
    rfl

/-- `mov r, [rip + d]`, at `x`. -/
theorem OpIA.ld_rip {w r len d A : Nat} {x : Addr} (hw : w = 32 ∨ w = 64)
    (hA : x.add len + BitVec.ofNat 64 d = BitVec.ofNat 64 A) :
    OpIA prof x (mk .mov w [gr w r, .mem (mrip d w)] len) (Op.lda w r A) := by
  dsimp only [Op.lda, OpIA]
  intro s o t hrip htf hac hdec hld
  have he : eaR s len d = BitVec.ofNat 64 A := by rw [← hA, ← hrip]
  refine ⟨_, t, instruction_next htf hdec ?_, rfl, rfl, rfl, rfl⟩
  rcases hw with rfl | rfl <;>
  · simp only [exec, Sem.mov, mk, mrip, gr, bind, Prog.bind, readOp, Bool.false_eq_true, ↓reduceIte, memRef,
      effOffset, pure, Prog.readRip, Prog.read, Prog.run, Opd.width, writeOp, BitVec.mul_one]
    rw [eaR_adv, he, checkAccess_ok (s := advance s len) hac hld]
    rfl

/-- `lea r64, [rip + d]`, at `x`. -/
theorem OpIA.lea_rip {r len d A : Nat} {x : Addr} (hA : x.add len + BitVec.ofNat 64 d = BitVec.ofNat 64 A) :
    OpIA prof x (mk .lea 64 [gr 64 r, .mem (mrip d 0)] len) (Op.mov 64 r (.i A)) := by
  dsimp only [Op.mov, OpIA]
  intro s o t hrip htf hdec
  have he : eaR s len d = BitVec.ofNat 64 A := by rw [← hA, ← hrip]
  refine ⟨_, t, ?_, rfl, rfl, rfl, rfl⟩
  rw [FV7z.lea_rip htf hdec, he]
  rfl

theorem OpI.setcc {cc : Cond} {r len : Nat} : OpI prof (mk (.setcc cc) 8 [gr 8 r] len) (Op.setcc cc r) :=
  fun _ _ _ htf hdec => ⟨_, _, setcc_r8 htf hdec, rfl, rfl, rfl, rfl⟩

theorem OpI.xorm {w r len sc d : Nat} {b i : Option Nat} (hw : w = 32 ∨ w = 64) :
    OpI prof (mk .xor w [gr w r, .mem (mg b i sc d w)] len) (Op.xorm w r b i sc d) := by
  dsimp only [Op.xorm, OpI]
  intro s o t htf hac hdec hld
  refine ⟨_, ?t', instruction_next htf hdec ?h, ⟨?af, rfl⟩, rfl, rfl, rfl⟩
  case h =>
    rcases hw with rfl | rfl <;> cases b <;> cases i <;>
    · simp only [exec, Sem.xor, alu, logicOp, mk, mg, gr, bind, Prog.bind, readOp, Bool.false_eq_true, ↓reduceIte,
        memRef, effOffset, pure, Prog.readReg, Prog.read, Prog.run, writeOp, Prog.readFlags]
      rw [checkAccess_ok (s := advance s len) hac hld]
      rfl

theorem OpI.ldsx {r len sc d : Nat} {b i : Option Nat} :
    OpI prof (mk .movsxd 64 [gr 64 r, .mem (mg b i sc d 32)] len) (Op.ldsx r b i sc d) := by
  dsimp only [Op.ldsx, OpI]
  intro s o t htf hac hdec hld
  refine ⟨_, t, instruction_next htf hdec ?_, rfl, rfl, rfl, rfl⟩
  cases b <;> cases i <;>
  · simp only [exec, Sem.movsxd, movSigned, mk, mg, gr, bind, Prog.bind, readOp, Bool.false_eq_true, ↓reduceIte, memRef,
      effOffset, pure, Prog.readReg, Prog.read, Prog.run, writeOp, Opd.width, Nat.reduceDiv]
    rw [checkAccess_ok (s := advance s len) hac hld]
    rfl

/-- `movzx r32, [rip + d]`, at `x`. -/
theorem OpIA.ldzx_rip {v r len d A : Nat} {x : Addr} (hw : v = 8 ∨ v = 16)
    (hA : x.add len + BitVec.ofNat 64 d = BitVec.ofNat 64 A) :
    OpIA prof x (mk .movzx 32 [gr 32 r, .mem (mrip d v)] len) (Op.ldzxa v r A) := by
  dsimp only [Op.ldzxa, OpIA]
  intro s o t hrip htf hac hdec hld
  have he : eaR s len d = BitVec.ofNat 64 A := by rw [← hA, ← hrip]
  refine ⟨_, t, instruction_next htf hdec ?_, rfl, rfl, rfl, rfl⟩
  rcases hw with rfl | rfl <;>
  · simp only [exec, Sem.movzx, mk, mrip, gr, bind, Prog.bind, readOp, Bool.false_eq_true, ↓reduceIte, memRef,
      effOffset, pure, Prog.readRip, Prog.read, Prog.run, Opd.width, writeOp, BitVec.mul_one, Prog.readFlags]
    rw [eaR_adv, he, checkAccess_ok (s := advance s len) hac hld]
    rfl

/-- `mov [rip + d], r`, at `x`. -/
theorem OpIA.st_rip {w r len d A : Nat} {x : Addr} (hw : w = 16 ∨ w = 32 ∨ w = 64)
    (hA : x.add len + BitVec.ofNat 64 d = BitVec.ofNat 64 A) :
    OpIA prof x (mk .mov w [.mem (mrip d w), gr w r] len) (Op.sta w A r) := by
  dsimp only [Op.sta, OpIA]
  intro s o t hrip htf hac hdec _ hwr
  have he : eaR s len d = BitVec.ofNat 64 A := by rw [← hA, ← hrip]
  refine ⟨t, instruction_next htf hdec ?_⟩
  rcases hw with rfl | rfl | rfl <;>
  · simp only [exec, Sem.mov, mk, mrip, gr, bind, Prog.bind, readOp, Bool.false_eq_true, ↓reduceIte, memRef,
      effOffset, pure, Prog.readReg, Prog.readRip, Prog.write, Prog.run, Opd.width, writeOp, BitVec.mul_one]
    rw [eaR_adv, he, checkAccess_ok (s := advance s len) hac hwr]
    rfl

/-- `mov [rip + d], imm`, at `x`. -/
theorem OpIA.sti_rip {w v len d A : Nat} {x : Addr} (hw : w = 16 ∨ w = 32 ∨ w = 64)
    (hA : x.add len + BitVec.ofNat 64 d = BitVec.ofNat 64 A) :
    OpIA prof x (mk .mov w [.mem (mrip d w), .imm w v] len) (Op.stia w A v) := by
  dsimp only [Op.stia, OpIA]
  intro s o t hrip htf hac hdec _ hwr
  have he : eaR s len d = BitVec.ofNat 64 A := by rw [← hA, ← hrip]
  refine ⟨t, instruction_next htf hdec ?_⟩
  rcases hw with rfl | rfl | rfl <;>
  · simp only [exec, Sem.mov, mk, mrip, gr, bind, Prog.bind, readOp, Bool.false_eq_true, ↓reduceIte, memRef,
      effOffset, pure, Prog.readReg, Prog.readRip, Prog.write, Prog.run, Opd.width, writeOp, BitVec.mul_one]
    rw [eaR_adv, he, checkAccess_ok (s := advance s len) hac hwr]
    rfl

end

/-- `jmp r64`, to the `tgt`-th byte: the register holds its address. -/
theorem Sp.jmpr {prof : Profile} {code : List Byte} {e' : Addr} {j r len : Nat}
    (hd : Leaf.Dec prof.feat code j (FV7z.mk .jmp 64 [gr 64 r] len)) (hj : j < code.length) :
    Sp prof code e' j fun _ _ Q g f V =>
      ∃ tgt, tgt < code.length ∧ g.get (regOf r) = e'.add tgt ∧ Q tgt g (rfz f) V := by
  refine ⟨?_⟩
  intro F Wl L s₀ o gev gP gE c hin X t V Q hK hA hrip hW k
  obtain ⟨tgt, ht, hr, hQ⟩ := hW
  refine c.next (V' := V) (Pr := fun Y => Y.cpu.rip = e'.add tgt ∧ Y.cpu.gpr = X.cpu.gpr ∧
    Y.cpu.rflags = rfz X.cpu.rflags) hK hA hin hj hrip (fun M hK' hA' htf _ => ?_)
    (fun Y t' hKY hAY ⟨h1, h2, h3⟩ => k _ _ _ _ hQ Y t' hKY hAY h1 h2 h3)
  have hca := ((c.codeAt hK' hin) tgt ht).1
  have ha : (X.withMem M).cpu.gpr.get (regOf r) = e'.add tgt := hr
  exact ⟨_, _, jmp_r (s := X.withMem M) htf (c.dec hK' hin hrip hd) (by rw [ha]; exact hca),
    hK'.upd rfl rfl rfl, hA', ha, rfl, rfl⟩

end FV7z
