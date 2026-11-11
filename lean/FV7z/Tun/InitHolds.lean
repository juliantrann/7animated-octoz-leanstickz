import FV7z.Tun.Holds
/-!
# The theorem of `checks/tunables-init` (PLAN.md G3, startup)

Under the name and statement of `Challenges/V2606/TunablesInit.lean`: the bytes the file holds at `0x66ee10` are
`tin` (`tin_pin`), which keep the contract of `__tunables_init` (`tin_holds`).
-/
namespace FV7z.V2606
open ZellicX86

theorem tunablesInit_holds : ∀ code, Exe.bytesAt zzs.blob 0x66ee10 1413 = some code →
    ∀ (L : List (Addr × List Byte)) (prof : Profile), CodeIn L 0x66ee10 code →
      ∀ A E : List (Addr × List Byte), ImplementsCall prof 0x66ee10 L (Tunables.contract A E) := by
  intro code hc L prof hin A E
  rw [Tun.tin_pin] at hc
  obtain rfl := Option.some.inj hc
  exact Tun.tin_holds L prof hin A E

end FV7z.V2606
