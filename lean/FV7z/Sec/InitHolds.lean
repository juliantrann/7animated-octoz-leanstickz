import FV7z.Sec.Holds
/-!
# The theorem of `checks/init-secure` (PLAN.md G3, startup)

Under the name and statement of `Challenges/V2606/InitSecure.lean`: the bytes the file holds at `0x6706a0` are
`sec` (`sec_pin`), which keep the contract of `__libc_init_secure` (`sec_holds`).
-/
namespace FV7z.V2606
open ZellicX86

theorem initSecure_holds : ∀ code, Exe.bytesAt zzs.blob 0x6706a0 78 = some code →
    ∀ (L : List (Addr × List Byte)) (prof : Profile), CodeIn L 0x6706a0 code →
      ImplementsCall prof 0x6706a0 L InitSecure.contract := by
  intro code hc L prof hin
  rw [Sec.sec_pin] at hc
  obtain rfl := Option.some.inj hc
  exact Sec.sec_holds L prof hin

end FV7z.V2606
