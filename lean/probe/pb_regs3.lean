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

/-- The bytes after the three pushes (`r12`, `rbp`, `rbx`). -/
abbrev Vm (g : Gprs) (V : Addr → Byte) : Addr → Byte :=
  Vst (Vst (Vst V (g.rsp - 8) (toBytesLE g.r12 8)) (g.rsp - 8 - 8) (toBytesLE g.rbp 8)) (g.rsp - 8 - 8 - 8)
    (toBytesLE g.rbx 8)

/-- The pops and the load of the return address read back what the pushes left. -/
theorem regs3 (g : Gprs) (V : Addr → Byte) (h : 24 ≤ g.rsp.toNat) (h' : g.rsp.toNat + 8 ≤ 2 ^ 64) :
    rdq(Vm g V, g.rsp - 8 - 8 - 8) = g.rbx ∧ rdq(Vm g V, g.rsp - 8 - 8 - 8 + 8) = g.rbp ∧
      rdq(Vm g V, g.rsp - 8 - 8 - 8 + 8 + 8) = g.r12 ∧ rdq(Vm g V, g.rsp - 8 - 8 - 8 + 24#64) = rdq(V, g.rsp) ∧
      g.rsp - 8 - 8 - 8 + 8 + 8 + 8 = g.rsp := by
  have a4 : g.rsp - 8 - 8 - 8 + 8 + 8 + 8 = g.rsp := by bv_omega
  have a2 : g.rsp - 8 - 8 - 8 + 8 + 8 = g.rsp - 8 := by bv_omega
  have a3 : g.rsp - 8 - 8 - 8 + 24#64 = g.rsp := by bv_omega
  have a1 : g.rsp - 8 - 8 - 8 + 8 = g.rsp - 8 - 8 := by bv_omega
  have e1 : (g.rsp - 8).toNat = g.rsp.toNat - 8 := by bv_omega
  have e2 : (g.rsp - 8 - 8).toNat = g.rsp.toNat - 16 := by bv_omega
  have e3 : (g.rsp - 8 - 8 - 8).toNat = g.rsp.toNat - 24 := by bv_omega
  have l : ∀ v : Addr, (toBytesLE v 8).length = 8 := fun v => toBytesLE_length _ _
  have hR := g.rsp.isLt
  rw [a4, a2, a3, a1]
  unfold Vm
  refine ⟨?_, ?_, ?_, ?_, rfl⟩
  · rw [rd_Vst_self _ _ _ (l _) (by rw [e3]; omega)]
    exact ofBytesLE_toBytesLE (n := 8) rfl _
  · rw [rd_Vst _ _ _ _ _ (by rw [l, e3]; omega) (by rw [e2]; omega) (.inl (by rw [l, e3, e2]; omega)),
      rd_Vst_self _ _ _ (l _) (by rw [e2]; omega)]
    exact ofBytesLE_toBytesLE (n := 8) rfl _
  · rw [rd_Vst _ _ _ _ _ (by rw [l, e3]; omega) (by rw [e1]; omega) (.inl (by rw [l, e3, e1]; omega)),
      rd_Vst _ _ _ _ _ (by rw [l, e2]; omega) (by rw [e1]; omega) (.inl (by rw [l, e2, e1]; omega)),
      rd_Vst_self _ _ _ (l _) (by rw [e1]; omega)]
    exact ofBytesLE_toBytesLE (n := 8) rfl _
  · rw [rd_Vst _ _ _ _ _ (by rw [l, e3]; omega) h' (.inl (by rw [l, e3]; omega)),
      rd_Vst _ _ _ _ _ (by rw [l, e2]; omega) h' (.inl (by rw [l, e2]; omega)),
      rd_Vst _ _ _ _ _ (by rw [l, e1]; omega) h' (.inl (by rw [l, e1]; omega))]


end FV7z.Mal
