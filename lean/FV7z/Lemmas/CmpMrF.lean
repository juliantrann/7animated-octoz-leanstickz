import FV7z.Lemmas.BlkOps13
/-!
# `cmp fs:[m], r` (PLAN.md §M, M1)

glibc's `_nl_postload_ctype` compares the thread's locale (`fs:[-0x80]`) with `_nl_global_locale`'s address:
`cmp fs:[rdi], rsi`. `Op.cmpmrf`: `cmp fs:[m], r` of 32 or 64 bits, the `fs` base `fb` in the `Op`
(`OpIF.cmpmrf`), as `OpIF.cmpmif` (`FV7z/Lemmas/BlkOps13.lean`) with a register for the immediate.
-/
namespace FV7z
open ZellicX86 Decode

namespace Op

/-- `cmp fs:[m], r`. -/
def cmpmrf (fb : Addr) (w : Nat) (b i : Option Nat) (sc d r : Nat) : Op :=
  .load (w / 8) (fun g => fb + eaG g b i sc d) (fun g _ _ => g)
    fun g f bs fl => fl = subF (rfz f) (ofBytesLE w bs) (gv g w r)

end Op

section
set_option linter.unusedSimpArgs false
variable {prof : Profile}

theorem OpIF.cmpmrf {x fb : Addr} {w r len sc d : Nat} {b i : Option Nat} (hw : w = 32 ∨ w = 64) :
    OpIF prof x fb (mk .cmp w [.mem (mf b i sc d w), gr w r] len) (Op.cmpmrf fb w b i sc d r) := by
  dsimp only [Op.cmpmrf, OpIF]
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
