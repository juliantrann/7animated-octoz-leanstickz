import FV7z.Sjs.Holds
/-!
# The theorem of `checks/sigjmp-save` (PLAN.md G3, startup)

Under the name and statement of `Challenges/V2606/SigjmpSave.lean`: the bytes the file holds at `0x67e0b0` are
`sjs` (`sjs_pin`), which keep the contract of `__sigjmp_save` without a mask to save (`sjs_holds`).
-/
namespace FV7z.V2606
open ZellicX86

theorem sigjmpSave_holds : ∀ code, Exe.bytesAt zzs.blob 0x67e0b0 52 = some code →
    ∀ (L : List (Addr × List Byte)) (prof : Profile), CodeIn L 0x67e0b0 code →
      ImplementsCall prof 0x67e0b0 L SigjmpSave.contract := by
  intro code hc L prof hin
  rw [Sjs.sjs_pin] at hc
  obtain rfl := Option.some.inj hc
  exact Sjs.sjs_holds L prof hin

end FV7z.V2606
