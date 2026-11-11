import FV7z.Grl.Cuts
import FV7z.Start.TaskSeg
/-!
# `__getrlimit` asks the kernel for a limit (PLAN.md G3, startup)

glibc 2.31's `__getrlimit64 (resource, rlim)` at `0x666310` in `7zzs`: `prlimit64 (0, resource, NULL, rlim)`, and 0
returned when the kernel's answer is not an error. Two pieces of the code, to the `syscall` (18) and from after it
(20) to the `ret` (28), around the kernel's `prlimit64` of `Lemmas/SysTask.lean` (`Seg.s_getrlimit`).

- `grl_ok`: called with a resource `r < 16` and `rlim`'s 16 bytes in what the run may store into, below the end of
  the user address space, the run reaches the `ret` with the limit of the run's start in them, soft then hard, and
  `rax` 0.

The way to the `ret` with `errno` set is not one of these runs.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Grl

/-- The `syscall`. -/
def psys : List Byte := [0x0f, 0x05]
theorem psys_0 : ∀ feat, Dec feat psys 0 (FV7z.mk .syscall 32 [] 2) := by dec_rfl
theorem w_18 : psys <+: grl.drop 18 := by decide +kernel
theorem sys_18 (feat : Features) : Dec feat grl 18 (FV7z.mk .syscall 32 [] 2) :=
  Dec.shift (j := 18) (k := 0) (psys_0 feat) w_18 (Nat.zero_le _)

/-- The `ret`. -/
def pret : List Byte := [0xc3]
theorem pret_0 : ∀ feat, Dec feat pret 0 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem w_28 : pret <+: grl.drop 28 := by decide +kernel
theorem ret_28 (feat : Features) : Dec feat grl 28 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 28) (k := 0) (pret_0 feat) w_28 (Nat.zero_le _)

variable {F : Footprint} {Wl : List Rgn}

/-- The registers at the `syscall`: `prlimit64 (0, resource, NULL, rlim)`. -/
abbrev g0 (g : Gprs) : Gprs :=
  { g with rax := 302, rdx := 0, rsi := (g.rdi.setWidth 32).setWidth 64, rdi := 0, r10 := g.rsi }

/-- To the `syscall`. -/
theorem vc_0 {g : Gprs} {f : Rflags} {V : Addr → Byte} :
    W_0 F Wl (fun j' g' _ V' => j' = 18 ∧ g' = g0 g ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_0, o0, BitVec.xor_self]
  rfl

/-- From the `syscall` to the `ret`, the kernel's answer 0. -/
theorem vc_20 {g : Gprs} {f : Rflags} {V : Addr → Byte} (h0 : g.rax = 0) :
    W_20 F Wl (fun j' g' _ V' => j' = 28 ∧ g' = g ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  have h0' : rax = 0 := h0
  subst h0'
  wpx [W_20, o1]
  decide

/-- The event of `prlimit64` from `__getrlimit` called with registers `g`, the kernel's answer the bytes `bs`. -/
abbrev grlEv (g : Gprs) (bs : List Byte) : Event :=
  ⟨302, [0, (g.rdi.setWidth 32).setWidth 64, 0, g.rsi, g.r8, g.r9], 0, [], bs⟩

theorem gpr_ret (g : Gprs) (rc r11 : BitVec 64) :
    (((g0 g).set 1 rc).set 11 r11).set 0 0 = (((g0 g).set 0 0).set 1 rc).set 11 r11 := rfl

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop} {X : State} {t : Nat}
  {V : Addr → Byte}

/-- `__getrlimit (r, rlim)` with `r < 16` and `rlim`'s 16 bytes in what the run may store into, from its entry to
its `ret`: the bytes are the limit `r` of the run's start, `rax` is 0, `rcx` and `r11` are the kernel's; `rdx` and
`rdi` are 0, `rsi` is `r` and `r10` is `rlim`. -/
theorem grl_ok (c : Seg prof F Wl L s₀ o) (hin : CodeIn L grl_at grl) (hK : KeptW Wl s₀ X)
    (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = grl_at) {r : Nat} (hr : r < 16)
    (hres : X.cpu.gpr.rdi.toNat % 2 ^ 32 = r) (hold : X.cpu.gpr.rsi ≠ 0)
    (htop : X.cpu.gpr.rsi.toNat + 16 ≤ userPtrMax prof.feat)
    (hst : ∀ i < 16, Foot Wl (Addr.add X.cpu.gpr.rsi i))
    (k : ∀ rc r11 Z t', KeptW Wl s₀ Z →
      Agree F Z.proc.mm.mem (Vst V X.cpu.gpr.rsi (s₀.proc.signal.rlimits ⟨r, hr⟩).bytes) →
      Z.cpu.rip = grl_at.add 28 → Z.cpu.gpr = (((g0 X.cpu.gpr).set 0 0).set 1 rc).set 11 r11 →
      GoG prof L o (gev ++ [grlEv X.cpu.gpr (s₀.proc.signal.rlimits ⟨r, hr⟩).bytes]) gP gE Z t') :
    GoG prof L o gev gP gE X t := by
  refine (c_0 prof).run c hin (fun j' g' _ V' => j' = 18 ∧ g' = g0 X.cpu.gpr ∧ V' = V) hK hA
    (by rw [addr_add_zero]; exact hrip) vc_0 ?_
  rintro j' g fl V' ⟨rfl, rfl, rfl⟩ Y t₁ hKY hAY hrY hgY -
  have h10 : Y.cpu.gpr.r10 = X.cpu.gpr.rsi := by rw [hgY]
  refine c.s_getrlimit hKY hAY hin (lt_len (by decide)) hrY hr (sys_18 _) (by rw [hgY]; rfl) (by rw [hgY]; rfl)
    (by rw [hgY]; simpa [arg32] using hres) (by rw [hgY]) (by rw [h10]; exact hold) (by rw [h10]; exact htop)
    (by rw [h10]; exact hst) ?_
  rintro Z t₂ hKZ hAZ ⟨hrZ, hgZ⟩
  have hev : sysEvOut Y (s₀.proc.signal.rlimits ⟨r, hr⟩).bytes =
      grlEv X.cpu.gpr (s₀.proc.signal.rlimits ⟨r, hr⟩).bytes := by
    simp only [sysEvOut, hgY]
  rw [hev]
  rw [h10] at hAZ
  refine (c_20 prof).run c hin _ hKZ hAZ hrZ (vc_20 (by rw [hgZ]; rfl)) ?_
  rintro j' g fl V' ⟨rfl, rfl, rfl⟩ U t₃ hKU hAU hrU hgU -
  refine k (Y.cpu.rip.add 2) (rf0 Y).toBits U t₃ hKU hAU hrU ?_
  rw [hgU, hgZ]
  unfold sysGpr
  rw [hgY]
  exact gpr_ret _ _ _

end FV7z.Grl
