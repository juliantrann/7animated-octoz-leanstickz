import FV7z.Lemmas.BlkOps18
/-!
# `pxor xmm, xmm` with the register's value not followed (PLAN.md G3, constructors)

`__pthread_mutex_init` with a null `attr` zeroes the mutex through `xmm0` (`pxor xmm0, xmm0`, then `movups` stores).
Where the proof does not need the stored bytes (`Op.vs`: bytes that are any), `pxor` is `Op.vld 0`: no byte read,
the registers and flags kept, the vector registers any.

- `OpI.vz_pxor`.
-/
namespace FV7z
open ZellicX86 Decode

variable {prof : Profile}

theorem OpI.vz_pxor {w n m len : Nat} :
    OpI prof (mk (.sse .pxor) w [.xmm n, .xmm m] len) (Op.vld 0 fun _ => 0) := by
  dsimp only [OpI]
  intro s o t htf _ hdec _
  refine ⟨?_, t, instruction_next htf hdec ?_⟩
  rotate_left
  · simp only [exec, execSse, Sem.pxor, packedOp, packed, aligned16, bind, Prog.bind, readOp,
      Bool.false_eq_true, ↓reduceIte, pure, Prog.run, writeOp, Prog.readZmm]
    rfl

end FV7z
