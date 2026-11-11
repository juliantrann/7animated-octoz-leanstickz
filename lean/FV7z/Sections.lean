import ZellicX86.Spec.Executable
import FV7z.Image
/-!
# Sanity facts about the loaded `7zzs` image

Checked by the kernel's evaluation of Zellic's ELF readers on the file's bytes. They guard against loading the wrong
file or a reader that does not see the file the way `readelf` does; they are not part of any statement's meaning.
-/
namespace FV7z.V2606
open ZellicX86

/-- The file is an executable Zellic's model reads (`Exe.valid`: ELF64, little-endian, `ET_EXEC`, x86-64, sane
segments and sections). -/
theorem zzs_valid : Exe.valid zzs.blob = true := by decide +kernel

/-- The hand-written LZMA decoder (`Asm/x86/LzmaDecOpt.asm`, `LzmaDec_DecodeReal_3`) is the section
`.text$LZMADECOPT`: 4719 bytes at `0x6d4040` (`readelf -S`). -/
theorem lzmaDecOpt_sec :
    (Exe.sec zzs.blob ".text$LZMADECOPT").map (fun p => (p.1, p.2.length)) = some (0x6d4040, 4719) := by
  decide +kernel

end FV7z.V2606
