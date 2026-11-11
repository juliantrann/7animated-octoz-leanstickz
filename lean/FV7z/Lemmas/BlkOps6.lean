import FV7z.Lemmas.SpFs
/-!
# Effects of more instructions with operands `fs:[…]` (PLAN.md G3, startup)

What `__pthread_initialize_minimal` needs beyond `Op.ldf` and `Op.stf` (`Lemmas/SpFs.lean`): stores of a byte into the
thread control block (`Op.stf8`, `Op.stfi`) and the stack guard's check, `xor r, fs:[m]` (`Op.xormf`).
-/
namespace FV7z
open ZellicX86 Decode FV7z.Leaf

namespace Op

/-- `mov byte fs:[m], r8`, the `fs` base `fb`. -/
def stf8 (fb : Addr) (b i : Option Nat) (sc d r : Nat) : Op :=
  .store 1 (fun g => fb + eaG g b i sc d) (fun g => toBytesLE (gv g 8 r) 1) fun g => g
/-- `mov fs:[m], imm`, the `fs` base `fb`. -/
def stfi (fb : Addr) (w : Nat) (b i : Option Nat) (sc d v : Nat) : Op :=
  .store (w / 8) (fun g => fb + eaG g b i sc d) (fun _ => toBytesLE (BitVec.ofNat w v) (w / 8)) fun g => g
/-- `xor r, fs:[m]`, the `fs` base `fb`. -/
def xormf (fb : Addr) (w r : Nat) (b i : Option Nat) (sc d : Nat) : Op :=
  .load (w / 8) (fun g => fb + eaG g b i sc d) (fun g _ bs => wr g r (gv g w r ^^^ ofBytesLE w bs))
    fun g f bs fl => LogF f (gv g w r ^^^ ofBytesLE w bs) fl

end Op

section
set_option linter.unusedSimpArgs false
variable {prof : Profile}

theorem OpIF.stf8 {x fb : Addr} {r len sc d : Nat} {b i : Option Nat} :
    OpIF prof x fb (mk .mov 8 [.mem (mf b i sc d 8), gr 8 r] len) (Op.stf8 fb b i sc d r) := by
  dsimp only [Op.stf8, OpIF]
  intro s o t _ hfs htf hac hdec _ hwr
  subst hfs
  refine ⟨t, instruction_next htf hdec ?_⟩
  cases b <;> cases i <;>
  · simp only [exec, Sem.mov, mk, mf, gr, bind, Prog.bind, readOp, Bool.false_eq_true, ↓reduceIte, memRef,
      effOffset, pure, Prog.readReg, Prog.write, Prog.run, writeOp, Prog.segBase]
    rw [checkAccess_ok (s := advance s len) hac hwr]
    rfl

theorem OpIF.stfi {x fb : Addr} {w v len sc d : Nat} {b i : Option Nat} (hw : w = 8 ∨ w = 16 ∨ w = 32 ∨ w = 64) :
    OpIF prof x fb (mk .mov w [.mem (mf b i sc d w), .imm w v] len) (Op.stfi fb w b i sc d v) := by
  dsimp only [Op.stfi, OpIF]
  intro s o t _ hfs htf hac hdec _ hwr
  subst hfs
  refine ⟨t, instruction_next htf hdec ?_⟩
  rcases hw with rfl | rfl | rfl | rfl <;> cases b <;> cases i <;>
  · simp only [exec, Sem.mov, mk, mf, gr, bind, Prog.bind, readOp, Bool.false_eq_true, ↓reduceIte, memRef,
      effOffset, pure, Prog.readReg, Prog.write, Prog.run, writeOp, Prog.segBase]
    rw [checkAccess_ok (s := advance s len) hac hwr]
    rfl

theorem OpIF.xormf {x fb : Addr} {w r len sc d : Nat} {b i : Option Nat} (hw : w = 32 ∨ w = 64) :
    OpIF prof x fb (mk .xor w [gr w r, .mem (mf b i sc d w)] len) (Op.xormf fb w r b i sc d) := by
  dsimp only [Op.xormf, OpIF]
  intro s o t _ hfs htf hac hdec hld
  subst hfs
  refine ⟨_, ?t', instruction_next htf hdec ?h, ⟨?af, rfl⟩, rfl, rfl, rfl⟩
  case h =>
    rcases hw with rfl | rfl <;> cases b <;> cases i <;>
    · simp only [exec, Sem.xor, alu, logicOp, mk, mf, gr, bind, Prog.bind, readOp, Bool.false_eq_true, ↓reduceIte,
        memRef, effOffset, pure, Prog.readReg, Prog.read, Prog.run, writeOp, Prog.readFlags, Prog.segBase]
      rw [checkAccess_ok (s := advance s len) hac hld]
      rfl

end

end FV7z
