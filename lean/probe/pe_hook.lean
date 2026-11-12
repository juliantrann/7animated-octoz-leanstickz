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
theorem pj_0 : ∀ feat, Dec feat pj 0 (FV7z.mk .jmp 64 [gr 64 0] 2) := sorry
theorem w_377 : pj <+: mal.drop 377 := sorry
theorem jmp_377 (feat : Features) : Dec feat mal 377 (FV7z.mk .jmp 64 [gr 64 0] 2) := sorry
/-- The bytes after the three pushes (`r12`, `rbp`, `rbx`). -/
abbrev Vm (g : Gprs) (V : Addr → Byte) : Addr → Byte :=
  Vst (Vst (Vst V (g.rsp - 8) (toBytesLE g.r12 8)) (g.rsp - 8 - 8) (toBytesLE g.rbp 8)) (g.rsp - 8 - 8 - 8)
    (toBytesLE g.rbx 8)

/-- The slots of the pushes and the return address, from the stack pointer `r`. -/
theorem offs (r : Addr) (h : 24 ≤ r.toNat) (h' : r.toNat + 8 ≤ 2 ^ 64) :
    (r - 8 - 8 - 8).toNat = r.toNat - 24 + 0 ∧ (r - 8 - 8 - 8 + 8).toNat = r.toNat - 24 + 8 ∧
      (r - 8 - 8 - 8 + 8 + 8).toNat = r.toNat - 24 + 16 ∧ (r - 8 - 8 - 8 + 24#64).toNat = r.toNat - 24 + 24 :=
  ⟨by bv_omega, by bv_omega, by bv_omega, by bv_omega⟩

theorem addk (r x : Addr) (k i : Nat) (hx : x.toNat = r.toNat - 24 + k) (h : 24 ≤ r.toNat) (hk : k + i < 32)
    (h' : r.toNat + 8 ≤ 2 ^ 64) : Addr.add (r - 24) (k + i) = Addr.add x i := by
  simp only [Addr.add]
  bv_omega

theorem p8 (x : Addr) (n : Nat) (h : x.toNat = n) (hn : n + 8 < 2 ^ 64) : (x + 8).toNat = n + 8 := by sorry
/-- The pops and the load of the return address read back what the pushes left. -/
theorem regs3 (g : Gprs) (V : Addr → Byte) (h : 24 ≤ g.rsp.toNat) (h' : g.rsp.toNat + 8 ≤ 2 ^ 64) :
    rdq(Vm g V, g.rsp - 8 - 8 - 8) = g.rbx ∧ rdq(Vm g V, g.rsp - 8 - 8 - 8 + 8) = g.rbp ∧
      rdq(Vm g V, g.rsp - 8 - 8 - 8 + 8 + 8) = g.r12 ∧ rdq(Vm g V, g.rsp - 8 - 8 - 8 + 24#64) = rdq(V, g.rsp) ∧
      g.rsp - 8 - 8 - 8 + 8 + 8 + 8 = g.rsp := by sorry
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
                    r12 := rdq(Vm g V, g.rsp - 8 - 8 - 8 + 8 + 8), rsp := g.rsp - 8 - 8 - 8 + 8 + 8 + 8 }) g f V := by sorry
variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ X : State} {o : Oracle} {t : Nat}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop} {V : Addr → Byte}

/-- `malloc` with the hook set (not 0): from the entry to the hook's first byte, `e₂ + j₂`. The registers are the
entry's but `rax` (the hook) and `rsi` (the return address, at the stack pointer); the bytes are `Vm` (the three
pushes, below the stack pointer). -/
theorem mal_hook (c : Seg prof F Wl L s₀ o) (hin : CodeIn L mal_at mal) (hK : KeptW Wl s₀ X)
    (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = mal_at)
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (hk : rdq(V, 7940656#64) = e₂.add j₂) (hk0 : e₂.add j₂ ≠ 0#64)
    (hfh : ∀ i < 8, Foot F.data (Addr.add (7940656#64) i))
    (hsp : 7940664 + 8 ≤ X.cpu.gpr.rsp.toNat) (hs : X.cpu.gpr.rsp.toNat + 8 ≤ 2 ^ 64)
    (hst : ∀ i < 32, Foot Wl (Addr.add (X.cpu.gpr.rsp - 24) i))
    (k : ∀ Z t', KeptW Wl s₀ Z → Agree F Z.proc.mm.mem (Vm X.cpu.gpr V) → Z.cpu.rip = e₂.add j₂ →
      Z.cpu.gpr = { X.cpu.gpr with rax := e₂.add j₂, rsi := rdq(V, X.cpu.gpr.rsp) } →
      GoG prof L o gev gP gE Z t') :
    GoG prof L o gev gP gE X t := by
  have w : ∀ (x : Addr) (k : Nat), k + 8 ≤ 32 → x.toNat = X.cpu.gpr.rsp.toNat - 24 + k →
      ∀ i < 8, Foot F.data (Addr.add x i) := by
    intro x k hk hx i hi
    have := c.hws _ (hst (k + i) (by omega))
    rwa [addk _ x k i hx (by omega) (by omega) hs] at this
  obtain ⟨q0, q8, q16, q24⟩ := offs _ (by omega) hs
  have r0 := w (X.cpu.gpr.rsp - 8 - 8 - 8) 0 (by omega) q0
  have r1 := w (X.cpu.gpr.rsp - 8 - 8 - 8 + 8) 8 (by omega) q8
  have r2 := w (X.cpu.gpr.rsp - 8 - 8 - 8 + 8 + 8) 16 (by omega) q16
  have r3 := w (X.cpu.gpr.rsp - 8 - 8 - 8 + 24#64) 24 (by omega) q24
  refine (c_0 prof).run c hin _ hK hA (by rw [addr_add_zero]; exact hrip)
    (vc_0 (by rw [hk]; exact hk0) hfh hsp (fun i hi => hst i (by omega)) r0 r1 r2 r3) ?_
  rintro j' g fl V₁ ⟨rfl, rfl, rfl⟩ Y t₁ hK₁ hA₁ hr₁ hg₁ -
  refine c.s_jmp_rx hK₁ hA₁ hin (lt_len (by decide)) hr₁ (jmp_377 _) hin₂ h₂ (by rw [hg₁]; exact hk) ?_
  rintro Z t' hKZ hAZ ⟨hrZ, hgZ⟩
  refine k Z t' hKZ hAZ hrZ ?_
  obtain ⟨b1, b2, b3, b4, b5⟩ := regs3 X.cpu.gpr V (by omega) hs
  rw [hgZ, hg₁, hk, b1, b2, b3, b4, b5]

end FV7z.Mal
