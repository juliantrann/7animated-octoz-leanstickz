import FV7z.Ini.Holds
/-!
# The theorem of `checks/init-fn` (PLAN.md G3, startup)

Under the name and statement of `Challenges/V2606/InitFn.lean`: the bytes the file holds at `0x401000` are `ini`
(`ini_pin`), which keep the contract of `_init` (`ini_holds`).
-/
namespace FV7z.V2606
open ZellicX86

theorem initFn_holds : ∀ code, Exe.bytesAt zzs.blob 0x401000 27 = some code →
    ∀ (L : List (Addr × List Byte)) (prof : Profile), CodeIn L 0x401000 code →
      ImplementsCall prof 0x401000 L InitFn.contract := by
  intro code hc L prof hin
  rw [Ini.ini_pin] at hc
  obtain rfl := Option.some.inj hc
  exact Ini.ini_holds L prof hin

end FV7z.V2606
