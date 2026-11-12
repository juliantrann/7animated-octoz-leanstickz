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

/-- The slots of the pushes and the return address, from the stack pointer `r`. -/
theorem offs (r : Addr) (h : 24 ≤ r.toNat) (h' : r.toNat + 8 ≤ 2 ^ 64) :
    (r - 8 - 8 - 8).toNat = r.toNat - 24 + 0 ∧ (r - 8 - 8 - 8 + 8).toNat = r.toNat - 24 + 8 ∧
      (r - 8 - 8 - 8 + 8 + 8).toNat = r.toNat - 24 + 16 ∧ (r - 8 - 8 - 8 + 24#64).toNat = r.toNat - 24 + 24 :=
  ⟨by bv_omega, by bv_omega, by bv_omega, by bv_omega⟩

theorem addk (r x : Addr) (k i : Nat) (hx : x.toNat = r.toNat - 24 + k) (h : 24 ≤ r.toNat) (hk : k + i < 32)
    (h' : r.toNat + 8 ≤ 2 ^ 64) : Addr.add (r - 24) (k + i) = Addr.add x i := by
  simp only [Addr.add]
  bv_omega


end FV7z.Mal
