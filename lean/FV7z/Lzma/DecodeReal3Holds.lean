import FV7z.Lzma.Holds
/-!
# The theorem of `checks/lzma-decode-real3` (PLAN.md G2.2)

Under the name and statement of `Challenges/V2606/LzmaDecodeReal3.lean`: the bytes the file holds at `0x6d4040` are
`dr3` (`dr3_pin`), which keep the contract of `LzmaDec_DecodeReal_3` (`dr3_holds`).
-/
namespace FV7z.V2606
open ZellicX86

theorem lzmaDecodeReal3_holds : ∀ code, Exe.bytesAt zzs.blob 0x6d4040 4719 = some code →
    ∀ (L : List (Addr × List Byte)) (prof : Profile) (e : Addr), CodeIn L e code →
      ImplementsCall prof e L LzmaDec.contract := by
  intro code hc L prof e hin
  rw [Lzma.dr3_pin] at hc
  obtain rfl := Option.some.inj hc
  exact Lzma.dr3_holds L prof e hin

end FV7z.V2606
