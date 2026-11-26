import FV7z.Exit.Cuts
import FV7z.Lemmas.SysExit
/-!
# `_Exit` ends the run (PLAN.md §M, M1)

glibc 2.31's `_Exit (status)` at `0x664a70` in `7zzs`: `edx` = `edi`, `r8d` = 231, a `jmp` to the `syscall`
`exit_group (status)`; the run ends there with `status`'s low 8 bits (`Seg.s_exit_group`, `Lemmas/SysExit.lean`), so
the `syscall` `exit` and the `hlt` after it are never reached.

- `vc_0`: from the entry to the `syscall` (52): `rax` = 231, `rdi`'s low 8 bits those of the `status` passed.
- `exit_ok`: called with `status` in `rdi`, the run ends with `.exited .exitGroup` of its low 8 bits.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Exit

/-- The `syscall`. -/
def psys : List Byte := [0x0f, 0x05]
theorem psys_0 : ∀ feat, Dec feat psys 0 (FV7z.mk .syscall 32 [] 2) := by dec_rfl
theorem w_52 : psys <+: ext.drop 52 := by decide +kernel
theorem sys_52 (feat : Features) : Dec feat ext 52 (FV7z.mk .syscall 32 [] 2) :=
  Dec.shift (j := 52) (k := 0) (psys_0 feat) w_52 (Nat.zero_le _)

variable {F : Footprint} {Wl : List Rgn}

/-- To the `syscall` `exit_group`: `eax` is 231, `edi` the `status` passed (`edx` between). -/
theorem vc_0 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} :
    W_0 fb F Wl (fun j' g' _ _ => j' = 52 ∧ g'.rax = 231#64 ∧ g'.rdi.setWidth 8 = g.rdi.setWidth 8) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_0, W_47, o0, o1]
  first
  | exact ⟨rfl, by simp⟩
  | exact ⟨by decide, by simp⟩
  | (simp; done)
  | exact ⟨rfl, rfl, by simp⟩

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop} {X : State}
  {t : Nat} {V : Addr → Byte}

/-- `_Exit (status)` from its entry: the run ends with `.exited .exitGroup` of `status`'s low 8 bits, which the goal
for ends has to allow, of the events before. -/
theorem exit_ok {fb : Addr} (c : Seg prof F Wl L s₀ o) (hfs : s₀.cpu.seg.fsBase = fb)
    (hin : CodeIn L ext_at ext) (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = ext_at)
    (hE : gE (.exited .exitGroup (X.cpu.gpr.rdi.setWidth 8)) gev) :
    GoG prof L o gev gP gE X t := by
  refine (c_0 prof fb).run c hfs hin
    (fun j' g' _ _ => j' = 52 ∧ g'.rax = 231#64 ∧ g'.rdi.setWidth 8 = X.cpu.gpr.rdi.setWidth 8) hK hA
    (by rw [addr_add_zero]; exact hrip) vc_0 ?_
  rintro j' g fl V₁ ⟨rfl, hax, hdi⟩ Y t₁ hKY hAY hrY hgY -
  refine c.s_exit_group hKY hin (lt_len (by decide)) hrY (sys_52 _) (by rw [hgY, hax] <;> decide) ?_
  rw [hgY, hdi]
  exact hE

end FV7z.Exit
