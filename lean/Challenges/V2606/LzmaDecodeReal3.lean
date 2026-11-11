import ZellicX86.Spec.Executable
import FV7z.Image
import FV7z.Spec.LzmaDec
-- The challenge of `checks/lzma-decode-real3` (PLAN.md G2.2): the theorem of `FV7z.Lzma.DecodeReal3Holds` as stated,
-- without its proof (`sorry`). Lean warns that it uses `sorry`: that is expected; `lake comparator` holds the proof
-- export to exactly this statement and refuses a proof that uses `sorry` (`tools/check.sh`).
--
-- In words: the 4719 bytes of `7zzs` 26.06 at `0x6d4040`, as Zellic's ELF reader reads them from the file
-- (`LzmaDec_DecodeReal_3`, the LZMA decoder's loop, from `Asm/x86/LzmaDecOpt.asm`), placed anywhere, on any processor
-- profile, keep `LzmaDec.contract` (`FV7z/Spec/LzmaDec.lean`): called with a `CLzmaDec` as `LzmaDec.c` keeps it
-- between calls (`LzmaDec.Pre`), whatever bytes the input holds, every call returns to its caller, having read only
-- the `CLzmaDec`, the dictionary's buffer, the array of probabilities and the input up to 20 bytes past `bufLimit`,
-- written only its stack frame, the dictionary's buffer from `dicPos` to `limit`, the array of probabilities and
-- the `CLzmaDec`'s fields from `dicPos` to `remainLen`, made no system call, kept the callee-saved registers, and
-- executed no byte outside the code it was given; and the `CLzmaDec` is then as `LzmaDec.Post` says.
namespace FV7z.V2606
open ZellicX86

theorem lzmaDecodeReal3_holds : ∀ code, Exe.bytesAt zzs.blob 0x6d4040 4719 = some code →
    ∀ (L : List (Addr × List Byte)) (prof : Profile) (e : Addr), CodeIn L e code →
      ImplementsCall prof e L LzmaDec.contract := by
  sorry

end FV7z.V2606
