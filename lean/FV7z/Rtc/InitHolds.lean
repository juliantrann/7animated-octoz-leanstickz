import FV7z.Rtc.Holds
/-!
# The theorem of `checks/reg-tm` (PLAN.md G3, startup)

Under the name and statement of `Challenges/V2606/RegTm.lean`: the bytes the file holds at `0x41d3c0` are `rtc`
(`rtc_pin`), which keep the contract of `register_tm_clones` (`rtc_holds`).
-/
namespace FV7z.V2606
open ZellicX86

theorem regTm_holds : ∀ code, Exe.bytesAt zzs.blob 0x41d3c0 49 = some code →
    ∀ (L : List (Addr × List Byte)) (prof : Profile), CodeIn L 0x41d3c0 code →
      ImplementsCall prof 0x41d3c0 L RegTm.contract := by
  intro code hc L prof hin
  rw [Rtc.rtc_pin] at hc
  obtain rfl := Option.some.inj hc
  exact Rtc.rtc_holds L prof hin

end FV7z.V2606
