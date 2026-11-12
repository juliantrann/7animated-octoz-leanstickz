import FV7z.Mal.Cuts
import FV7z.Mhi.Holds
/-!
# `malloc` with the hook set: the jump to the hook (PLAN.md G3, `malloc`)

glibc 2.31's `__libc_malloc (n)` at `0x633160` in `7zzs` (`malloc/malloc.c`): three pushes, `__malloc_hook`
(`0x792a30`) read; not 0, so the return address to `rsi`, three pops and `jmp rax`. The first `malloc` of the process
finds the hook as the file has it, `malloc_hook_ini` (`0x632ba0`), which returns to `malloc`'s caller.

- `jmp_377`: the `jmp rax`. `Vm`: the bytes after the three pushes; `regs3`: the pops read them back.
- `vc_0`: from the entry to the `jmp rax` (377).
- `mal_hook`: from the entry to the hook's first byte: the registers as at the entry but `rax` (the hook) and `rsi`
  (the return address); the 24 bytes below the stack pointer written.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn FV7z.Start
open FV7z.Tun (rd_Vst rd_Vst_self Vst_out)
namespace FV7z.Mal
variable {F : Footprint} {Wl : List Rgn}

/-- `jmp rax`. -/
def pj : List Byte := [0xff, 0xe0]
theorem pj_0 : ∀ feat, Dec feat pj 0 (FV7z.mk .jmp 64 [gr 64 0] 2) := by dec_rfl
theorem w_377 : pj <+: mal.drop 377 := by decide +kernel
theorem jmp_377 (feat : Features) : Dec feat mal 377 (FV7z.mk .jmp 64 [gr 64 0] 2) :=
  Dec.shift (j := 377) (k := 0) (pj_0 feat) w_377 (Nat.zero_le _)


end FV7z.Mal
