import ZellicX86.Spec.Executable
import FV7z.Image
import FV7z.Lemmas.InsFn
/-!
# The first bytes of `_int_free` in `7zzs` (PLAN.md G3, `free`)

glibc 2.31's `_int_free (av, p, have_lock)` (`malloc/malloc.c`) begins at `0x62f990`: its first 16 bytes, as a list,
and the fact that they are the file's (`ifr_pin`). Enough for a jump to its entry (`Fre.fre_ok`); its blocks come
later.
-/
namespace FV7z.Ifr
set_option maxRecDepth 100000
open ZellicX86

/-- `_int_free`, `0x62f990` to `0x62f99f` of `7zzs`. -/
def ifr : List Byte := [
  0x41, 0x57, 0x41, 0x56, 0x41, 0x55, 0x41, 0x89, 0xd5, 0x41, 0x54, 0x55, 0x53, 0x48, 0x83, 0xec]

theorem ifr_pin : Exe.bytesAt V2606.zzs.blob 0x62f990 16 = some ifr := by decide +kernel
theorem ifr_length : ifr.length = 16 := by decide +kernel

/-- Where the code lies in `7zzs`. -/
abbrev ifr_at : Addr := 0x62f990

end FV7z.Ifr
