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
theorem pj_0 : ∀ feat, Dec feat pj 0 (FV7z.mk .jmp 64 [gr 64 0] 2) := by dec_rfl
theorem w_377 : pj <+: mal.drop 377 := by decide +kernel
theorem jmp_377 (feat : Features) : Dec feat mal 377 (FV7z.mk .jmp 64 [gr 64 0] 2) :=
  Dec.shift (j := 377) (k := 0) (pj_0 feat) w_377 (Nat.zero_le _)

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

set_option maxHeartbeats 1000000 in
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
  all_goals first
    | assumption
    | rfl
    | (and_intros <;> first | assumption | rfl | exact fun h => absurd h (by decide))

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
    have e : Addr.add (X.cpu.gpr.rsp - 24) (k + i) = Addr.add x i := by simp only [Addr.add]; bv_omega
    rwa [e] at this
  have r0 := w (X.cpu.gpr.rsp - 8 - 8 - 8) 0 (by omega) (by bv_omega)
  have r1 := w (X.cpu.gpr.rsp - 8 - 8 - 8 + 8) 8 (by omega) (by bv_omega)
  have r2 := w (X.cpu.gpr.rsp - 8 - 8 - 8 + 8 + 8) 16 (by omega) (by bv_omega)
  have r3 := w (X.cpu.gpr.rsp - 8 - 8 - 8 + 24#64) 24 (by omega) (by bv_omega)
  refine (c_0 prof).run c hin _ hK hA (by rw [addr_add_zero]; exact hrip)
    (vc_0 (by rw [hk]; exact hk0) hfh hsp (fun i hi => hst i (by omega)) r0 r1 r2 r3) ?_
  rintro j' g fl V₁ ⟨rfl, rfl, rfl⟩ Y t₁ hK₁ hA₁ hr₁ hg₁ -
  refine c.s_jmp_rx hK₁ hA₁ hin (lt_len (by decide)) hr₁ (jmp_377 _) hin₂ h₂ (by rw [hg₁]; exact hk) ?_
  rintro Z t' hKZ hAZ ⟨hrZ, hgZ⟩
  refine k Z t' hKZ hAZ hrZ ?_
  obtain ⟨b1, b2, b3, b4, b5⟩ := regs3 X.cpu.gpr V (by omega) hs
  rw [hgZ, hg₁, hk, b1, b2, b3, b4, b5]
