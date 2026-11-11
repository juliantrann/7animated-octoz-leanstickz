import FV7z.Fin.Holds
/-!
# The theorem of `checks/fini-fn` (PLAN.md G3, startup)

Under the name and statement of `Challenges/V2606/FiniFn.lean`: the bytes the file holds at `0x6d7670` are `fin`
(`fin_pin`), which keep the contract of `_fini` (`fin_holds`).
-/
namespace FV7z.V2606
open ZellicX86

theorem finiFn_holds : ∀ code, Exe.bytesAt zzs.blob 0x6d7670 13 = some code →
    ∀ (L : List (Addr × List Byte)) (prof : Profile), CodeIn L 0x6d7670 code →
      ImplementsCall prof 0x6d7670 L FiniFn.contract := by
  intro code hc L prof hin
  rw [Fin.fin_pin] at hc
  obtain rfl := Option.some.inj hc
  exact Fin.fin_holds L prof hin

end FV7z.V2606
