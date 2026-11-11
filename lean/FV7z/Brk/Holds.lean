import FV7z.Brk.Cuts
import FV7z.Start.Base
/-!
# `__brk` asks the kernel for the break and stores the answer (PLAN.md G3, startup)

glibc 2.31's `__brk (addr)` at `0x6a2a00` in `7zzs`: `brk (addr)`, the answer stored in `__curbrk` (`0x7a4c38`), 0
returned when the answer is not below `addr`. Two pieces of the code, to the `syscall` (9) and from after it (11) to
the `ret` (33), around the kernel's `brk` of `Start/SysSeg.lean` and `Start/Base.lean`.

- `brk_keep`: called with an address below the lowest break (`__brk (0)`, how `__sbrk` asks where the break is), the
  run reaches the `ret` with `__curbrk` the break, `rax` 0, the process as it was.
- `brk_grow`: called from a run whose start has `Base`, with an address whose page is above the break's and not above
  the `lim`-th, the kernel not refusing memory, the run reaches the `ret` from a new start: the regions `N` of the
  new pages are in the footprint, their bytes 0, `Base` holds with the new break, `__curbrk` is the address, `rax` 0.

The way to the `ret` with `ENOMEM` (the kernel's answer below `addr`) is not one of these runs.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn FV7z.Start
namespace FV7z.Brk

/-- The `syscall`. -/
def psys : List Byte := [0x0f, 0x05]
theorem psys_0 : ∀ feat, Dec feat psys 0 (FV7z.mk .syscall 32 [] 2) := by dec_rfl
theorem w_9 : psys <+: brk.drop 9 := by decide +kernel
theorem sys_9 (feat : Features) : Dec feat brk 9 (FV7z.mk .syscall 32 [] 2) :=
  Dec.shift (j := 9) (k := 0) (psys_0 feat) w_9 (Nat.zero_le _)

/-- The `ret`. -/
def pret : List Byte := [0xc3]
theorem pret_0 : ∀ feat, Dec feat pret 0 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem w_33 : pret <+: brk.drop 33 := by decide +kernel
theorem ret_33 (feat : Features) : Dec feat brk 33 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 33) (k := 0) (pret_0 feat) w_33 (Nat.zero_le _)

/-- `__curbrk`. -/
abbrev curbrk : Addr := 0x7a4c38

variable {F : Footprint} {Wl : List Rgn}

/-- To the `syscall`: `eax` is 12. -/
theorem vc_0 {g : Gprs} {f : Rflags} {V : Addr → Byte} :
    W_0 F Wl (fun j' g' _ V' => j' = 9 ∧ g' = g.set 0 12 ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_0, o0]
  rfl

/-- From the `syscall` to the `ret`, with a break in `rax` that is not below what was asked for: it is stored in
`__curbrk`, and `eax` is 0. -/
theorem vc_11 {g : Gprs} {f : Rflags} {V : Addr → Byte} (hc : ∀ i < 8, Foot Wl (curbrk.add i))
    (h1 : g.rax.toNat ≤ 2 ^ 47) (h2 : g.rdi.toNat ≤ g.rax.toNat) :
    W_11 F Wl (fun j' g' _ V' => j' = 33 ∧ g' = g.set 0 0 ∧ V' = Vst V curbrk (toBytesLE g.rax 8)) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  have h1' : rax.toNat ≤ 2 ^ 47 := h1
  have h2' : rdi.toNat ≤ rax.toNat := h2
  wpx [W_11, W_19, W_31, o1, o2, o3, Op.sta]
  refine ⟨fun h => ?_, fun _ => ⟨hc, fun h => ?_, fun _ => ⟨?_, rfl⟩⟩⟩
  · simp only [Bool.not_eq_true', Bool.or_eq_false_iff] at h
    have h3 := of_decide_eq_false h.1
    omega
  · simp only [Bool.not_eq_true', Bool.or_eq_false_iff] at h
    have h3 := of_decide_eq_false h.1
    have h4 : rdi.toNat ≠ rax.toNat := fun e => of_decide_eq_false h.2 (BitVec.eq_of_toNat_eq e)
    omega
  · have e : BitVec.setWidth 64 (BitVec.setWidth 32 rax ^^^ BitVec.setWidth 32 rax) = 0 := by
      rw [BitVec.xor_self]
      rfl
    rw [e]
    rfl

theorem sys_rdi (Y : State) (len : Nat) (v : BitVec 64) : ((sysGpr Y len).set 0 v).rdi = Y.cpu.gpr.rdi := rfl

theorem gpr_ret (g : Gprs) (rc r11 v : BitVec 64) :
    ((((g.set 0 12).set 1 rc).set 11 r11).set 0 v).set 0 0 = ((g.set 0 0).set 1 rc).set 11 r11 := rfl

/-- The event of `brk` from `__brk` called in `X`, the kernel's answer `v`. -/
abbrev brkEv (X : State) (v : BitVec 64) : Event :=
  ⟨12, [X.cpu.gpr.rdi, X.cpu.gpr.rsi, X.cpu.gpr.rdx, X.cpu.gpr.r10, X.cpu.gpr.r8, X.cpu.gpr.r9], v, [], []⟩

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop} {X : State} {t : Nat}
  {V : Addr → Byte}

/-- `__brk (a)` with `a` below the lowest break (`__brk (0)`), from its entry to its `ret`: the break is in
`__curbrk`, `eax` is 0, `rcx` and `r11` are the kernel's; the registers else are as at the entry. -/
theorem brk_keep (c : Seg prof F Wl L s₀ o) (hin : CodeIn L brk_at brk) (hK : KeptW Wl s₀ X)
    (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = brk_at) (hcur : ∀ i < 8, Foot Wl (curbrk.add i))
    (hlow : X.cpu.gpr.rdi.toNat < s₀.proc.mm.brkMin.toNat) (hb : s₀.proc.mm.brk.toNat ≤ 2 ^ 47)
    (k : ∀ rc r11 Z t', KeptW Wl s₀ Z → Agree F Z.proc.mm.mem (Vst V curbrk (toBytesLE s₀.proc.mm.brk 8)) →
      Z.cpu.rip = brk_at.add 33 → Z.cpu.gpr = ((X.cpu.gpr.set 0 0).set 1 rc).set 11 r11 →
      GoG prof L o (gev ++ [brkEv X s₀.proc.mm.brk]) gP gE Z t') :
    GoG prof L o gev gP gE X t := by
  refine (c_0 prof).run c hin (fun j' g' _ V' => j' = 9 ∧ g' = X.cpu.gpr.set 0 12 ∧ V' = V) hK hA
    (by rw [addr_add_zero]; exact hrip) vc_0 ?_
  rintro j' g fl V' ⟨rfl, rfl, rfl⟩ Y t₁ hKY hAY hrY hgY -
  have hlo := c.ready.layout.2.2.2.1
  have hev : sysEv Y Y.proc.mm.brk = brkEv X s₀.proc.mm.brk := by
    simp only [sysEv, hgY, hKY.brk]
    rfl
  refine c.s_brk_keep hKY hAY hin (lt_len (by decide)) hrY (sys_9 _) (by rw [hgY]; rfl)
    (by rw [hgY, hKY.brkMin]; exact hlow) ?_
  rw [hev]
  rintro Z t₂ hKZ hAZ ⟨hrZ, hgZ⟩
  have hax : Z.cpu.gpr.rax = s₀.proc.mm.brk := by rw [hgZ, hKY.brk]; rfl
  have hdi : Z.cpu.gpr.rdi = X.cpu.gpr.rdi := by rw [hgZ, sys_rdi, hgY]; rfl
  refine (c_11 prof).run c hin _ hKZ hAZ hrZ (vc_11 hcur (by rw [hax]; exact hb) (by rw [hax, hdi]; omega)) ?_
  rintro j' g fl V' ⟨rfl, rfl, rfl⟩ U t₃ hKU hAU hrU hgU -
  rw [hax] at hAU
  refine k (Y.cpu.rip.add 2) (rf0 Y).toBits U t₃ hKU hAU hrU ?_
  rw [hgU, hgZ]
  unfold sysGpr
  rw [hgY]
  exact gpr_ret _ _ _ _

/-- `__brk (a)` that grows the break of a start with `Base`, the kernel not refusing memory, from its entry to its
`ret`: the run goes on from a new start with the regions `N` of the new pages, their bytes 0, and `Base` with the
break `a`, which is in `__curbrk`; `eax` is 0. -/
theorem brk_grow {lim : Nat} {b fsb : Addr} {ks : Kst} (c : Seg prof F Wl L s₀ o) (hB : Base s₀ lim b fsb ks)
    (hin : CodeIn L brk_at brk) (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = brk_at)
    (hcur : ∀ i < 8, Foot Wl (curbrk.add i)) (hmg : ∀ t p, o t (.memFail p) = none)
    (hgt : pageUp b.toNat / 4096 < pageUp X.cpu.gpr.rdi.toNat / 4096)
    (hlim : pageUp X.cpu.gpr.rdi.toNat / 4096 ≤ lim)
    {N : List Rgn} (hN : ∀ r ∈ N, r.In (pageUp b.toNat / 4096 * 4096) (pageUp X.cpu.gpr.rdi.toNat / 4096 * 4096))
    (k : ∀ rc r11 s₁ Z t', Seg prof (withNew F N) (N ++ Wl) L s₁ o → Base s₁ lim X.cpu.gpr.rdi fsb ks →
      KeptW (N ++ Wl) s₁ Z →
      Agree (withNew F N) Z.proc.mm.mem
        (Vst (Vz V (pageUp b.toNat / 4096 * 4096) (pageUp X.cpu.gpr.rdi.toNat / 4096 * 4096)) curbrk
          (toBytesLE X.cpu.gpr.rdi 8)) →
      Z.cpu.rip = brk_at.add 33 → Z.cpu.gpr = ((X.cpu.gpr.set 0 0).set 1 rc).set 11 r11 →
      GoG prof L o (gev ++ [brkEv X X.cpu.gpr.rdi]) gP gE Z t') :
    GoG prof L o gev gP gE X t := by
  refine (c_0 prof).run c hin (fun j' g' _ V' => j' = 9 ∧ g' = X.cpu.gpr.set 0 12 ∧ V' = V) hK hA
    (by rw [addr_add_zero]; exact hrip) vc_0 ?_
  rintro j' g fl V₁ ⟨rfl, rfl, rfl⟩ Y t₁ hKY hAY hrY hgY -
  have hdiY : Y.cpu.gpr.rdi = X.cpu.gpr.rdi := by rw [hgY]; rfl
  have hev : sysEv Y Y.cpu.gpr.rdi = brkEv X X.cpu.gpr.rdi := by
    simp only [sysEv, hgY]
    rfl
  refine c.b_brk_grow hB hKY hAY hin (lt_len (by decide)) hrY (sys_9 _) (by rw [hgY]; rfl) hmg
    (by rw [hdiY]; exact hgt) (by rw [hdiY]; exact hlim) (by rw [hdiY]; exact hN) ?_
  rw [hev, hdiY]
  intro s₁ t₂ c' hB' hA' hr' hg'
  have hax : s₁.cpu.gpr.rax = X.cpu.gpr.rdi := by rw [hg']; rfl
  have hdi : s₁.cpu.gpr.rdi = X.cpu.gpr.rdi := by rw [hg', sys_rdi, hgY]; rfl
  have htop := hB.top
  have hle : X.cpu.gpr.rdi.toNat ≤ 2 ^ 47 := by
    have h := hlim
    unfold pageUp at h
    omega
  refine (c_11 prof).run c' hin _ (KeptW.refl _ _) hA' hr'
    (vc_11 (fun i hi => foot_append_iff.2 (.inr (hcur i hi))) (by rw [hax]; exact hle) (by rw [hax, hdi]; omega)) ?_
  rintro j' g fl V₂ ⟨rfl, rfl, rfl⟩ U t₃ hKU hAU hrU hgU -
  rw [hax] at hAU
  refine k (Y.cpu.rip.add 2) (rf0 Y).toBits s₁ U t₃ c' hB' hKU hAU hrU ?_
  rw [hgU, hg']
  unfold sysGpr
  rw [hgY]
  exact gpr_ret _ _ _ _

end FV7z.Brk
