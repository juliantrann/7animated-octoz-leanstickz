import FV7z.Gor.Vc
/-!
# `_dl_get_origin`: the loop back to the last `/` (PLAN.md G3, startup)

From 114 with `ecx = n` (`1 ≤ n < 4096`) and `rax` the end of the `n` bytes at `B`: the loop stops at the last `/` at
an index from 1 to `n - 1`, `sl V B n` (`Gor/Mem.lean`): at 278 (`malloc (s + 2)`, `ebx = s`) if there is one, else
at 124 (`malloc (2)`), the bytes as they were. By induction on `n`.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Gor

theorem Kp.trans {g₁ g₂ g₃ : Gprs} (h₁ : Kp g₁ g₂) (h₂ : Kp g₂ g₃) : Kp g₁ g₃ :=
  ⟨h₂.1.trans h₁.1, h₂.2.1.trans h₁.2.1, h₂.2.2.1.trans h₁.2.2.1, h₂.2.2.2.trans h₁.2.2.2⟩

theorem sl_succ2 (V : Addr → Byte) (B : Addr) (c : Nat) :
    sl V B (c + 1 + 1) = if V (B.add (c + 1)) = 0x2f then c + 1 else sl V B (c + 1) := rfl

variable {prof : Profile} {F : Footprint} {Wl : List Rgn} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}

/-- The loop from 114, `ecx = n`, `rax = B + n`, `rbp = B`: on to 124 (`s = 0`, no `/` after the first byte) or to 278
(`edi = s + 2`, `ebx = s`), `s = sl V B n`; `rsp`, `rbp`, `r14`, `r15` as at the start (`Kp`), the bytes as they
were. -/
theorem loop (c : Seg prof F Wl L s₀ o) (hin : CodeIn L gor_at gor) {V : Addr → Byte} {B : Addr} {g₀ : Gprs}
    {s : Nat} (hbp : g₀.rbp = B) (hB : ∀ i < 4096, Foot F.data (Addr.add B i))
    (k1 : ∀ Z t', KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V → Z.cpu.rip = gor_at.add 124 →
      Z.cpu.gpr.rdi = BitVec.ofNat 64 2 → Kp g₀ Z.cpu.gpr → s = 0 → GoG prof L o gev gP gE Z t')
    (k2 : ∀ Z t', KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V → Z.cpu.rip = gor_at.add 278 →
      Z.cpu.gpr.rdi = BitVec.ofNat 64 (s + 2) → Z.cpu.gpr.rbx = BitVec.ofNat 64 s → Kp g₀ Z.cpu.gpr → 1 ≤ s →
      GoG prof L o gev gP gE Z t') :
    ∀ (n : Nat), 1 ≤ n → n < 4096 → sl V B n = s → ∀ (X : State) (t : Nat), KeptW Wl s₀ X →
      Agree F X.proc.mm.mem V → X.cpu.rip = gor_at.add 114 → X.cpu.gpr.rcx = BitVec.ofNat 64 n →
      X.cpu.gpr.rax = B + BitVec.ofNat 64 n → Kp g₀ X.cpu.gpr → GoG prof L o gev gP gE X t := by
  intro n
  induction n with
  | zero => intro h; omega
  | succ n ih =>
    intro h1 h2 hs X t hK hA hrip hcx hax hkp
    have hbp' : X.cpu.gpr.rbp = B := hkp.2.1.trans hbp
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · -- `ecx = 1`
      refine (c_114 prof).run c hin _ hK hA hrip (vc_114o hcx) ?_
      rintro j' g fl V' ⟨rfl, hdi, hkp', rfl⟩ Y t' hKY hAY hrY hgY -
      subst hgY
      exact k1 Y t' hKY hAY hrY hdi (hkp.trans hkp') (by rw [← hs]; rfl)
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have hax' : X.cpu.gpr.rax = X.cpu.gpr.rbp + BitVec.ofNat 64 (m + 1 + 1) := by rw [hax, hbp']
    have ea : X.cpu.gpr.rbp + BitVec.ofNat 64 (m + 1 + 1 - 1) = Addr.add B (m + 1) := by
      rw [hbp', Nat.add_sub_cancel]
      rfl
    refine (c_114 prof).run c hin _ hK hA hrip
      (vc_114 (c := m + 1 + 1) (by omega) h2 hcx hax' fun i hi => ?_) ?_
    · obtain rfl : i = 0 := by omega
      rw [addr_add_zero, ea]
      exact hB (m + 1) (by omega)
    rintro j' g fl V' hq Y t' hKY hAY hrY hgY -
    subst hgY
    rw [ea] at hq
    have hs' := hs
    rw [sl_succ2] at hs'
    rcases hq with ⟨hsl, rfl, hdi, hbx, hkp', rfl⟩ | ⟨hsl, rfl, hcx', hax'', hkp', rfl⟩
    · -- the last `/` at `m + 1`
      rw [if_pos hsl] at hs'
      subst hs'
      exact k2 Y t' hKY hAY hrY (by rw [hdi]) (by rw [hbx, Nat.add_sub_cancel]) (hkp.trans hkp') (by omega)
    · rw [if_neg hsl] at hs'
      exact ih (by omega) (by omega) hs' Y t' hKY hAY hrY (by rw [hcx', Nat.add_sub_cancel])
        (by rw [hax'']; rfl) (hkp.trans hkp')

end FV7z.Gor
