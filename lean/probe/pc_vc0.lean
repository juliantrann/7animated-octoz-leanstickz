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

/-- From the entry to the `jmp rax`, the hook not 0. -/
theorem vc_0 {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (hk : rdq(V, 7940656#64) ≠ 0#64) (hfh : ∀ i < 8, Foot F.data (Addr.add (7940656#64) i))
    (hsp : 7940664 + 8 ≤ g.rsp.toNat)
    (hst : ∀ i < 24, Foot Wl (Addr.add (g.rsp - 24) i))
    (r0 : ∀ i < 8, Foot F.data (Addr.add (g.rsp - 8 - 8 - 8) i))
    (r1 : ∀ i < 8, Foot F.data (Addr.add (g.rsp - 8 - 8 - 8 + 8) i))
    (r2 : ∀ i < 8, Foot F.data (Addr.add (g.rsp - 8 - 8 - 8 + 8 + 8) i))
    (r3 : ∀ i < 8, Foot F.data (Addr.add (g.rsp - 8 - 8 - 8 + 24#64) i)) :
    W_0 F Wl (fun j' g' _ V' => j' = 377 ∧ V' = Vm g V ∧
      g' = { g with rax := rdq(V, 7940656#64), rsi := rdq(Vm g V, g.rsp - 8 - 8 - 8 + 24#64),
        rbx := rdq(Vm g V, g.rsp - 8 - 8 - 8), rbp := rdq(Vm g V, g.rsp - 8 - 8 - 8 + 8),
        r12 := rdq(Vm g V, g.rsp - 8 - 8 - 8 + 8 + 8), rsp := g.rsp - 8 - 8 - 8 + 8 + 8 + 8 }) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hsp hst r0 r1 r2 r3 ⊢
  obtain ⟨s1, s2, s3⟩ := Mhi.push3 hst
  have hR := rsp.isLt
  have e8 : (rsp - 8).toNat = rsp.toNat - 8 := by bv_omega
  have l : (toBytesLE r12 8).length = 8 := toBytesLE_length _ _
  have e0 : (7940656#64 : Addr).toNat = 7940656 := rfl
  have e : List.map (Vst V (rsp - 8) (toBytesLE r12 8)) (byteAddrs 7940656#64 8) =
      List.map V (byteAddrs 7940656#64 8) :=
    rd_Vst _ _ _ _ _ (by rw [l, e8]; omega) (by rw [e0]; omega) (.inr (by rw [e0, e8]; omega))
  have hk' : (rdq(V, 7940656#64) == 0#64) = false := beq_eq_false_iff_ne.2 hk
  wpx [W_0, W_368, o0, o1, Op.lda, Vm, BitVec.and_self, e, hk']
  trace_state
  sorry


end FV7z.Mal
