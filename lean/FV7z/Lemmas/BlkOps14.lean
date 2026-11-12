import FV7z.Lemmas.BlkOps13
/-!
# `movzx r32, r8`, `test r16, x`, `cmp byte fs:[m], imm` (PLAN.md G3, `malloc`)

The forms `_int_malloc`'s second call and `malloc_hook_ini` have beside those of the earlier `BlkOps` files:

- `Op.zxr`: `movzx r32, r8` (`OpI.zxr`): the arena's flag after `setne` in the split of the top;
- `OpI.test16`: `test r16, x` (`Op.test 16`): the count of the thread's cache's bin;
- `OpIF.cmpmif8`: `cmp byte fs:[m], imm` (`Op.cmpmif fb 8`): the test of `tcache_shutting_down`.
-/
namespace FV7z
open ZellicX86 Decode

namespace Op

/-- `movzx r32, r8`. -/
def zxr (r q : Nat) : Op := .reg (fun g _ => wr g r ((gv g 8 q).setWidth 32)) fun _ f fl => fl = rfz f

end Op

section
set_option linter.unusedSimpArgs false
variable {prof : Profile}

theorem OpI.zxr {r q len : Nat} : OpI prof (mk .movzx 32 [gr 32 r, gr 8 q] len) (Op.zxr r q) :=
  fun _ _ _ htf hdec => ⟨_, _, movzx_rr8 htf hdec, rfl, rfl, rfl, rfl⟩

theorem OpI.test16 {r len : Nat} (x : Src) :
    OpI prof (mk .test 16 [gr 16 r, x.opd 16] len) (Op.test 16 r x) := fun s o t htf hdec => by
  cases x <;> exact ⟨_, _, instruction_next htf hdec rfl, ⟨_, rfl⟩, rfl, rfl, rfl⟩

theorem OpIF.cmpmif8 {x fb : Addr} {v len sc d : Nat} {b i : Option Nat} :
    OpIF prof x fb (mk .cmp 8 [.mem (mf b i sc d 8), .imm 8 v] len) (Op.cmpmif fb 8 b i sc d v) := by
  dsimp only [Op.cmpmif, OpIF]
  intro s o t _ hfs htf hac hdec hld
  subst hfs
  refine ⟨_, t, instruction_next htf hdec ?_, rfl, rfl, rfl, rfl⟩
  cases b <;> cases i <;>
  · simp only [exec, Sem.cmp, alu, subOp, mk, mf, gr, bind, Prog.bind, readOp, Bool.false_eq_true, ↓reduceIte,
      memRef, effOffset, pure, Prog.readReg, Prog.read, Prog.run, writeOp, Prog.readFlags, Prog.segBase]
    rw [checkAccess_ok (s := advance s len) hac hld]
    rfl

end

end FV7z
