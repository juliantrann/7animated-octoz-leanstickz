import FV7z.Dbg.Holds
/-!
# The theorem of `checks/debug-init` (PLAN.md G3, startup)

Under the name and statement of `Challenges/V2606/DebugInit.lean`: the bytes the file holds at `0x66e4a0` are
`dbg` (`dbg_pin`), which keep the contract of `_dl_debug_initialize` (`dbg_holds`).
-/
namespace FV7z.V2606
open ZellicX86

theorem debugInit_holds : ∀ code, Exe.bytesAt zzs.blob 0x66e4a0 124 = some code →
    ∀ (L : List (Addr × List Byte)) (prof : Profile), CodeIn L 0x66e4a0 code →
      ImplementsCall prof 0x66e4a0 L DebugInit.contract := by
  intro code hc L prof hin
  rw [Dbg.dbg_pin] at hc
  obtain rfl := Option.some.inj hc
  exact Dbg.dbg_holds L prof hin

end FV7z.V2606
