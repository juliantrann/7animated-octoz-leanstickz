import FV7z.Getpid.Cuts
import FV7z.Lemmas.SysPid
/-!
# `__getpid` asks the kernel for the process's id (PLAN.md G3, startup)

glibc 2.31's `__getpid ()` at `0x664ad0` in `7zzs`: `getpid ()`, which has no error return. One piece of the code, to
the `syscall` (9), then the kernel's `getpid` of `Lemmas/SysPid.lean`, to the `ret` (11).

- `getpid_ok`: from the entry the run reaches the `ret` with the thread's id (the process's) in `rax`, `rcx` and
  `r11` the kernel's; the registers else, the memory and the rest of the state are as at the entry.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Getpid

/-- The `syscall`. -/
def psys : List Byte := [0x0f, 0x05]
theorem psys_0 : ∀ feat, Dec feat psys 0 (FV7z.mk .syscall 32 [] 2) := by dec_rfl
theorem w_9 : psys <+: gpd.drop 9 := by decide +kernel
theorem sys_9 (feat : Features) : Dec feat gpd 9 (FV7z.mk .syscall 32 [] 2) :=
  Dec.shift (j := 9) (k := 0) (psys_0 feat) w_9 (Nat.zero_le _)

/-- The `ret`. -/
def pret : List Byte := [0xc3]
theorem pret_0 : ∀ feat, Dec feat pret 0 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem w_11 : pret <+: gpd.drop 11 := by decide +kernel
theorem ret_11 (feat : Features) : Dec feat gpd 11 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 11) (k := 0) (pret_0 feat) w_11 (Nat.zero_le _)

variable {F : Footprint} {Wl : List Rgn}

/-- To the `syscall`: `eax` is 39. -/
theorem vc_0 {g : Gprs} {f : Rflags} {V : Addr → Byte} :
    W_0 F Wl (fun j' g' _ V' => j' = 9 ∧ g' = g.set 0 39 ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_0, o0]
  rfl

/-- The event of `getpid` from `__getpid` called with registers `g`, the kernel's answer `v`. -/
abbrev pidEv (g : Gprs) (v : BitVec 64) : Event := ⟨39, [g.rdi, g.rsi, g.rdx, g.r10, g.r8, g.r9], v, [], []⟩

theorem gpr_ret (g : Gprs) (v rc r11 : BitVec 64) :
    (((g.set 0 39).set 1 rc).set 11 r11).set 0 v = ((g.set 0 v).set 1 rc).set 11 r11 := rfl

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop} {X : State} {t : Nat}
  {V : Addr → Byte}

/-- `__getpid ()` from its entry to its `ret`: `rax` is the thread's id (the process's), `rcx` and `r11` are the
kernel's; the registers else are as at the entry, the footprint's bytes too. -/
theorem getpid_ok (c : Seg prof F Wl L s₀ o) (hin : CodeIn L gpd_at gpd) (hK : KeptW Wl s₀ X)
    (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = gpd_at)
    (k : ∀ rc r11 Z t', KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V → Z.cpu.rip = gpd_at.add 11 →
      Z.cpu.gpr = ((X.cpu.gpr.set 0 (BitVec.ofNat 64 s₀.thread.tid)).set 1 rc).set 11 r11 →
      GoG prof L o (gev ++ [pidEv X.cpu.gpr (BitVec.ofNat 64 s₀.thread.tid)]) gP gE Z t') :
    GoG prof L o gev gP gE X t := by
  refine (c_0 prof).run c hin (fun j' g' _ V' => j' = 9 ∧ g' = X.cpu.gpr.set 0 39 ∧ V' = V) hK hA
    (by rw [addr_add_zero]; exact hrip) vc_0 ?_
  rintro j' g fl V' ⟨rfl, rfl, rfl⟩ Y t₁ hKY hAY hrY hgY -
  refine c.s_getpid hKY hAY hin (lt_len (by decide)) hrY (sys_9 _) (by rw [hgY]; rfl) ?_
  rintro Z t₂ hKZ hAZ ⟨hrZ, hgZ⟩
  have hev : sysEv Y (BitVec.ofNat 64 Y.thread.tid) = pidEv X.cpu.gpr (BitVec.ofNat 64 s₀.thread.tid) := by
    simp only [sysEv, hgY, hKY.thread]
    try rfl
  rw [hev]
  refine k (Y.cpu.rip.add 2) (rf0 Y).toBits Z t₂ hKZ hAZ hrZ ?_
  rw [hgZ, hKY.thread]
  unfold sysGpr
  rw [hgY]
  all_goals exact gpr_ret _ _ _ _

end FV7z.Getpid
