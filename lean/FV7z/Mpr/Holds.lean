import FV7z.Mpr.Cuts
import FV7z.Start.Prot
/-!
# `__mprotect` makes pages read-only (PLAN.md G3, startup)

glibc 2.31's `__mprotect (addr, len, prot)` at `0x666600` in `7zzs`: `mprotect (addr, len, prot)`, 0 returned when the
kernel's answer is not an error. Two pieces of the code, to the `syscall` (9) and from after it (11) to the `ret`
(19), around the kernel's `mprotect` of `Start/Prot.lean`.

- `mprotect_ro`: called from a run whose start has `Base` with `prot` `PROT_READ`, `addr` a page's address, `len` not
  0, every page of the range mapped and none special, the kernel not refusing, the run reaches the `ret` from a new
  start: the pages are read-only, the footprint is `G`, which does not write into them, `Base` holds as before, `eax`
  is 0.

The way to the `ret` with `errno` set (the kernel's answer an error) is not one of these runs.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn FV7z.Start
namespace FV7z.Mpr

/-- The `syscall`. -/
def psys : List Byte := [0x0f, 0x05]
theorem psys_0 : ∀ feat, Dec feat psys 0 (FV7z.mk .syscall 32 [] 2) := by dec_rfl
theorem w_9 : psys <+: mpr.drop 9 := by decide +kernel
theorem sys_9 (feat : Features) : Dec feat mpr 9 (FV7z.mk .syscall 32 [] 2) :=
  Dec.shift (j := 9) (k := 0) (psys_0 feat) w_9 (Nat.zero_le _)

/-- The `ret`. -/
def pret : List Byte := [0xc3]
theorem pret_0 : ∀ feat, Dec feat pret 0 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem w_19 : pret <+: mpr.drop 19 := by decide +kernel
theorem ret_19 (feat : Features) : Dec feat mpr 19 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 19) (k := 0) (pret_0 feat) w_19 (Nat.zero_le _)

variable {F : Footprint} {Wl : List Rgn}

/-- To the `syscall`: `eax` is 10. -/
theorem vc_0 {g : Gprs} {f : Rflags} {V : Addr → Byte} :
    W_0 F Wl (fun j' g' _ V' => j' = 9 ∧ g' = g.set 0 10 ∧ V' = V) g f V := by
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

/-- The event of `mprotect` from `__mprotect` called with registers `g`, the kernel's answer 0. -/
abbrev mpEv (g : Gprs) : Event := ⟨10, [g.rdi, g.rsi, g.rdx, g.r10, g.r8, g.r9], 0, [], []⟩

theorem gpr_ret (g : Gprs) (rc r11 : BitVec 64) :
    (((g.set 0 10).set 1 rc).set 11 r11).set 0 0 = ((g.set 0 0).set 1 rc).set 11 r11 := rfl

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop} {X : State} {t : Nat}
  {V : Addr → Byte}

/-- `__mprotect (a, len, PROT_READ)` of mapped pages, none special, from a start with `Base`, the kernel not
refusing, from its entry to its `ret`: the run goes on from a new start with the footprint `G`, whose bytes are bytes
of `F`, those it writes outside the pages, and `Base` as before; `eax` is 0, `rcx` and `r11` are the kernel's. -/
theorem mprotect_ro {lim : Nat} {b fsb : Addr} {ks : Kst} (c : Seg prof F Wl L s₀ o) (hB : Base s₀ lim b fsb ks)
    (hin : CodeIn L mpr_at mpr) (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = mpr_at)
    (hprot : X.cpu.gpr.rdx.toNat = 1) (hal : X.cpu.gpr.rdi.toNat % 4096 = 0) (hlen : 0 < X.cpu.gpr.rsi.toNat)
    (hwrap : X.cpu.gpr.rdi.toNat + pageUp X.cpu.gpr.rsi.toNat < 2 ^ 64)
    (hmg : ∀ t p, o t (.memFail p) = none)
    (hmap : ∀ i < pageUp X.cpu.gpr.rsi.toNat / 4096, ∃ m,
      s₀.proc.mm.mem.mapAt (X.cpu.gpr.rdi.toNat / 4096 + i) = some m ∧ m.special = false)
    {G : Footprint} {Wl' : List Rgn} (hGo : G.own = []) (hGc : G.code = F.code)
    (hfit : ∀ r ∈ G.writes ++ G.reads, r.Fits)
    (hGw : ∀ r ∈ G.writes, ∀ a, r.Mem a → Foot F.writes a ∧
      inPages (X.cpu.gpr.rdi.toNat / 4096) (pageUp X.cpu.gpr.rsi.toNat / 4096) (pageOf a) = false)
    (hGr : ∀ r ∈ G.reads, ∀ a, r.Mem a → Foot F.writes a ∨ Foot F.reads a)
    (hcode : ∀ a, Foot F.codeRgns a →
      inPages (X.cpu.gpr.rdi.toNat / 4096) (pageUp X.cpu.gpr.rsi.toNat / 4096) (pageOf a) = false)
    (hww : ∀ y, Foot Wl' y → ∃ q ∈ G.writes, q.Mem y)
    (k : ∀ rc r11 s₁ Z t', Seg prof G Wl' L s₁ o → Base s₁ lim b fsb ks → KeptW Wl' s₁ Z →
      Agree G Z.proc.mm.mem V → Z.cpu.rip = mpr_at.add 19 →
      Z.cpu.gpr = ((X.cpu.gpr.set 0 0).set 1 rc).set 11 r11 →
      GoG prof L o (gev ++ [mpEv X.cpu.gpr]) gP gE Z t') :
    GoG prof L o gev gP gE X t := by
  refine (c_0 prof).run c hin (fun j' g' _ V' => j' = 9 ∧ g' = X.cpu.gpr.set 0 10 ∧ V' = V) hK hA
    (by rw [addr_add_zero]; exact hrip) vc_0 ?_
  rintro j' g fl V₁ ⟨rfl, rfl, rfl⟩ Y t₁ hKY hAY hrY hgY -
  have hdi : Y.cpu.gpr.rdi = X.cpu.gpr.rdi := by rw [hgY]; rfl
  have hsi : Y.cpu.gpr.rsi = X.cpu.gpr.rsi := by rw [hgY]; rfl
  have hdx : Y.cpu.gpr.rdx = X.cpu.gpr.rdx := by rw [hgY]; rfl
  have hev : sysEv Y 0 = mpEv X.cpu.gpr := by
    simp only [sysEv, hgY]
    rfl
  have hmap' : ∀ i < pageUp X.cpu.gpr.rsi.toNat / 4096, ∃ m,
      Y.proc.mm.mem.mapAt (X.cpu.gpr.rdi.toNat / 4096 + i) = some m ∧ m.special = false := by
    intro i hi
    obtain ⟨m, hm, hs⟩ := hmap i hi
    refine ⟨m, ?_, hs⟩
    simp only [Memory.mapAt, hKY.mem_map] at hm ⊢
    exact hm
  refine c.b_mprotect_ro hB hKY hAY hin (lt_len (by decide)) hrY (sys_9 _) (by rw [hgY]; rfl)
    (by rw [hdx]; exact hprot) (by rw [hdi]; exact hal) (by rw [hsi]; exact hlen) (by rw [hdi, hsi]; exact hwrap)
    hmg (by rw [hdi, hsi]; exact hmap') hGo hGc hfit (by rw [hdi, hsi]; exact hGw) hGr
    (by rw [hdi, hsi]; exact hcode) hww ?_
  rw [hev]
  intro s₁ t₂ c' hB' hA' hr' hg'
  refine (c_11 prof).run c' hin _ (KeptW.refl _ _) hA' hr' (vc_11 (by rw [hg']; rfl)) ?_
  rintro j' g fl V₂ ⟨rfl, rfl, rfl⟩ U t₃ hKU hAU hrU hgU -
  refine k (Y.cpu.rip.add 2) (rf0 Y).toBits s₁ U t₃ c' hB' hKU hAU hrU ?_
  rw [hgU, hg']
  unfold sysGpr
  rw [hgY]
  exact gpr_ret _ _ _

end FV7z.Mpr
