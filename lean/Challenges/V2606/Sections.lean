import ZellicX86.Spec.Executable
import FV7z.Image
-- The challenge of `checks/sections`: the theorems of `FV7z.Sections` as stated, without their proofs (`sorry`).
-- Lean warns that it uses `sorry`: that is expected; `lake comparator` holds the proof export to exactly these
-- statements and refuses a proof that uses `sorry` (`tools/check.sh`).
namespace FV7z.V2606
open ZellicX86

theorem zzs_valid : Exe.valid zzs.blob = true := by sorry

theorem lzmaDecOpt_sec :
    (Exe.sec zzs.blob ".text$LZMADECOPT").map (fun p => (p.1, p.2.length)) = some (0x6d4040, 4719) := by
  sorry

end FV7z.V2606
