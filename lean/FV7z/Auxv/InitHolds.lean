import FV7z.Auxv.Holds
/-!
# The theorems of `checks/aux-init` (PLAN.md G3, startup)

Under the names and statements of `Challenges/V2606/AuxInit.lean`: the bytes the file holds at `0x66f410` are `aux`
(`aux_pin`), which keep the contract of `_dl_aux_init` (`aux_holds`); and the jump table the contract assumes in
memory is what the file holds at `0x6f3660` (`aux_jt_pin`).
-/
namespace FV7z.V2606
open ZellicX86

theorem auxInit_holds : ∀ code, Exe.bytesAt zzs.blob 0x66f410 1041 = some code →
    ∀ (L : List (Addr × List Byte)) (prof : Profile), CodeIn L 0x66f410 code →
      ∀ X : List (BitVec 64 × BitVec 64), ImplementsCall prof 0x66f410 L (AuxInit.contract X) := by
  intro code hc L prof hin X
  rw [Auxv.aux_pin] at hc
  obtain rfl := Option.some.inj hc
  exact Auxv.aux_holds L prof hin X

theorem auxInit_table : Exe.bytesAt zzs.blob 0x6f3660 124 = some AuxInit.jumpTable :=
  Auxv.aux_jt_pin.trans (congrArg some Auxv.jt_eq.symm)

end FV7z.V2606
