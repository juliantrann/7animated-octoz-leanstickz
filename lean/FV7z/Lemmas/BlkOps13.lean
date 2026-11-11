import FV7z.Lemmas.BlkOps12
/-!
# `cmp fs:[m], imm` (PLAN.md G3, `malloc`)

The form `_int_malloc` has beside those of the earlier `BlkOps` files:

- `Op.cmpmif`: `cmp fs:[m], imm` of 32 or 64 bits, the `fs` base `fb` in the `Op` (`OpIF.cmpmif`): the test of the
  thread's cache (`fs:[-0x28]`).
-/
namespace FV7z
open ZellicX86 Decode

namespace Op

/-- `cmp fs:[m], imm`. -/
def cmpmif (fb : Addr) (w : Nat) (b i : Option Nat) (sc d v : Nat) : Op :=
  .load (w / 8) (fun g => fb + eaG g b i sc d) (fun g _ _ => g)
    fun _ f bs fl => fl = subF (rfz f) (ofBytesLE w bs) (BitVec.ofNat w v)

end Op

section
set_option linter.unusedSimpArgs false
variable {prof : Profile}

theorem OpIF.cmpmif {x fb : Addr} {w v len sc d : Nat} {b i : Option Nat} (hw : w = 32 ∨ w = 64) :
    OpIF prof x fb (mk .cmp w [.mem (mf b i sc d w), .imm w v] len) (Op.cmpmif fb w b i sc d v) := by
  dsimp only [Op.cmpmif, OpIF]
  intro s o t _ hfs htf hac hdec hld
  subst hfs
  refine ⟨_, t, instruction_next htf hdec ?_, rfl, rfl, rfl, rfl⟩
  rcases hw with rfl | rfl <;> cases b <;> cases i <;>
  · simp only [exec, Sem.cmp, alu, subOp, mk, mf, gr, bind, Prog.bind, readOp, Bool.false_eq_true, ↓reduceIte,
      memRef, effOffset, pure, Prog.readReg, Prog.read, Prog.run, writeOp, Prog.readFlags, Prog.segBase]
    rw [checkAccess_ok (s := advance s len) hac hld]
    rfl

end

end FV7z
