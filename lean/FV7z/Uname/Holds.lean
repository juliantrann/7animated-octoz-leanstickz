import FV7z.Uname.Cuts
import FV7z.Lemmas.SysUname
/-!
# `__uname` asks the kernel for the system's names (PLAN.md G3, startup)

glibc 2.31's `__uname (buf)` at `0x6649e0` in `7zzs`: `uname (buf)`, and 0 returned when the kernel's answer is not an
error. Two pieces of the code, to the `syscall` (9) and from after it (11) to the `ret` (19), around the kernel's
`uname` of `Lemmas/SysUname.lean`.

- `uname_ok`: called with `buf`'s 390 bytes in what the run may store into, below the end of the user address space,
  the run reaches the `ret` with the kernel's answer `u` (a `struct new_utsname`, `UtsnameOk`) in them, `rax` 0,
  `rcx` and `r11` the kernel's; the registers else are as at the entry.

The way to the `ret` with `errno` set (the kernel's answer an error: `EFAULT`) is not one of these runs.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Uname

/-- The `syscall`. -/
def psys : List Byte := [0x0f, 0x05]
theorem psys_0 : ∀ feat, Dec feat psys 0 (FV7z.mk .syscall 32 [] 2) := by dec_rfl
theorem w_9 : psys <+: unm.drop 9 := by decide +kernel
theorem sys_9 (feat : Features) : Dec feat unm 9 (FV7z.mk .syscall 32 [] 2) :=
  Dec.shift (j := 9) (k := 0) (psys_0 feat) w_9 (Nat.zero_le _)

/-- The `ret`. -/
def pret : List Byte := [0xc3]
theorem pret_0 : ∀ feat, Dec feat pret 0 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem w_19 : pret <+: unm.drop 19 := by decide +kernel
theorem ret_19 (feat : Features) : Dec feat unm 19 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 19) (k := 0) (pret_0 feat) w_19 (Nat.zero_le _)

variable {F : Footprint} {Wl : List Rgn}

/-- To the `syscall`: `eax` is 63. -/
theorem vc_0 {g : Gprs} {f : Rflags} {V : Addr → Byte} :
    W_0 F Wl (fun j' g' _ V' => j' = 9 ∧ g' = g.set 0 63 ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_0, o0]
  rfl

/-- From the `syscall` to the `ret`, the kernel's answer 0. -/
theorem vc_11 {g : Gprs} {f : Rflags} {V : Addr → Byte} (h0 : g.rax = 0) :
    W_11 F Wl (fun j' g' _ V' => j' = 19 ∧ g' = g ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  have h0' : rax = 0 := h0
  subst h0'
  wpx [W_11, o1]
  decide

/-- The event of `uname` from `__uname` called with registers `g`, the kernel's answer the bytes `u`. -/
abbrev unEv (g : Gprs) (u : List Byte) : Event := ⟨63, [g.rdi, g.rsi, g.rdx, g.r10, g.r8, g.r9], 0, [], u⟩

theorem gpr_ret (g : Gprs) (rc r11 : BitVec 64) :
    (((g.set 0 63).set 1 rc).set 11 r11).set 0 0 = ((g.set 0 0).set 1 rc).set 11 r11 := rfl

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop} {X : State} {t : Nat}
  {V : Addr → Byte}

/-- `__uname (buf)` with `buf`'s 390 bytes in what the run may store into, from its entry to its `ret`: the bytes are
the kernel's answer `u`, `eax` is 0, `rcx` and `r11` are the kernel's; the registers else are as at the entry. -/
theorem uname_ok (c : Seg prof F Wl L s₀ o) (hin : CodeIn L unm_at unm) (hK : KeptW Wl s₀ X)
    (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = unm_at)
    (htop : X.cpu.gpr.rdi.toNat + 390 ≤ userPtrMax prof.feat)
    (hst : ∀ i < 390, Foot Wl (Addr.add X.cpu.gpr.rdi i)) {P : List Byte → Prop} (hP : ∀ t, P (o t .uname).val)
    (k : ∀ u rc r11 Z t', UtsnameOk u → P u → KeptW Wl s₀ Z → Agree F Z.proc.mm.mem (Vst V X.cpu.gpr.rdi u) →
      Z.cpu.rip = unm_at.add 19 → Z.cpu.gpr = ((X.cpu.gpr.set 0 0).set 1 rc).set 11 r11 →
      GoG prof L o (gev ++ [unEv X.cpu.gpr u]) gP gE Z t') :
    GoG prof L o gev gP gE X t := by
  refine (c_0 prof).run c hin (fun j' g' _ V' => j' = 9 ∧ g' = X.cpu.gpr.set 0 63 ∧ V' = V) hK hA
    (by rw [addr_add_zero]; exact hrip) vc_0 ?_
  rintro j' g fl V' ⟨rfl, rfl, rfl⟩ Y t₁ hKY hAY hrY hgY -
  have hdi : Y.cpu.gpr.rdi = X.cpu.gpr.rdi := by rw [hgY]; rfl
  refine c.s_uname hKY hAY hin (lt_len (by decide)) hrY (sys_9 _) (by rw [hgY]; rfl) (by rw [hdi]; exact htop)
    (by rw [hdi]; exact hst) hP ?_
  rintro u hu hPu Z t₂ hKZ hAZ ⟨hrZ, hgZ⟩
  have hev : unameEv Y.cpu.gpr u = unEv X.cpu.gpr u := by
    simp only [unameEv, hgY]
    rfl
  rw [hev]
  rw [hdi] at hAZ
  refine (c_11 prof).run c hin _ hKZ hAZ hrZ (vc_11 (by rw [hgZ]; rfl)) ?_
  rintro j' g fl V' ⟨rfl, rfl, rfl⟩ U t₃ hKU hAU hrU hgU -
  refine k u (Y.cpu.rip.add 2) (rf0 Y).toBits U t₃ hu hPu hKU hAU hrU ?_
  rw [hgU, hgZ]
  unfold sysGpr
  rw [hgY]
  exact gpr_ret _ _ _

end FV7z.Uname
