import FV7z.Dtc.Holds
/-!
# The theorem of `checks/dereg-tm` (PLAN.md G3, startup)

Under the name and statement of `Challenges/V2606/DeregTm.lean`: the bytes the file holds at `0x41d390` are `dtc`
(`dtc_pin`), which keep the contract of `deregister_tm_clones` (`dtc_holds`).
-/
namespace FV7z.V2606
open ZellicX86

theorem deregTm_holds : ∀ code, Exe.bytesAt zzs.blob 0x41d390 33 = some code →
    ∀ (L : List (Addr × List Byte)) (prof : Profile), CodeIn L 0x41d390 code →
      ImplementsCall prof 0x41d390 L DeregTm.contract := by
  intro code hc L prof hin
  rw [Dtc.dtc_pin] at hc
  obtain rfl := Option.some.inj hc
  exact Dtc.dtc_holds L prof hin

end FV7z.V2606
