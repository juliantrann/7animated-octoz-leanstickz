import FV7z.Ecq.Loop1
/-!
# `CExtractCallbackConsole::QueryInterface`: the fourth and fifth loop (PLAN.md §M, M1)

The fourth loop (192, 203, exits 213 and 225) and the fifth (240, 251, exits 261 and 273) compare the 16 bytes of
`iid` (`rsi`) with the IIDs at `0x6eb780` and `0x6eb790`, `rax` the index.

- `loop4`: from 192, on to the `AddRef` at 48 (`*ppv = this + 24`) or on a mismatch to the fifth loop at 240.
- `loop5`: from 240, on to the `AddRef` at 48 (`*ppv = this + 32`) or on a mismatch to the `ret` at 278 with
  `E_NOINTERFACE`. Both by induction on `15 - j`.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Ecq

variable {F : Footprint} {Wl : List Rgn} {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State}
  {o : Oracle} {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}

/-- The fourth loop from 192 at the index `j` (`j ≤ 15`), the bytes of `iid` before `j` those of the IID at
`0x6eb780`: on to the `AddRef` at 48 with all 16 equal and `*ppv = this + 24`, or on a mismatch to the fifth
loop at 240. -/
theorem loop4 (c : Seg prof F Wl L s₀ o) (hin : CodeIn L ecq_at ecq) {W : Addr → Byte} {g₀ : Gprs}
    (hfa : ∀ j < 16, ∀ i : Nat, i < 1 → Foot F.data (Addr.add (BitVec.ofNat 64 j + 7255936#64) i))
    (hfb : ∀ j < 16, ∀ i : Nat, i < 1 → Foot F.data (Addr.add (g₀.rsi + BitVec.ofNat 64 j) i))
    (hfw : ∀ i < 8, Foot Wl (Addr.add g₀.rdx i))
    (k48 : ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y →
      Agree F Y.proc.mm.mem (Vst W g₀.rdx (toBytesLE (g₀.rdi + 24#64) 8)) → Y.cpu.rip = ecq_at.add 48 →
      Kq g₀ Y.cpu.gpr → Y.cpu.gpr.rax = g₀.rdi + 24#64 → (∀ i < 16, Eqb W g₀.rsi 7255936#64 i) →
      GoG prof L o gev gP gE Y t')
    (k240 : ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y → Agree F Y.proc.mm.mem W → Y.cpu.rip = ecq_at.add 240 →
      Kq g₀ Y.cpu.gpr → Y.cpu.gpr.rax = 0#64 → Y.cpu.gpr.rcx = 7255952#64 →
      (∃ i < 16, ¬ Eqb W g₀.rsi 7255936#64 i) → GoG prof L o gev gP gE Y t') :
    ∀ (m j : Nat), j + m = 15 → ∀ (X : State) (t : Nat), KeptW Wl s₀ X → Agree F X.proc.mm.mem W →
      X.cpu.rip = ecq_at.add 192 → X.cpu.gpr.rax = BitVec.ofNat 64 j → X.cpu.gpr.rcx = 7255936#64 →
      Kq g₀ X.cpu.gpr → (∀ i < j, Eqb W g₀.rsi 7255936#64 i) → GoG prof L o gev gP gE X t := by
  intro m
  induction m with
  | zero =>
    intro j hj X t hK hA hrip hax hcx hks hpre
    refine (c_192 prof).run c hin
      (fun j' g' _ V' => Kq g₀ g' ∧
        ((j' = 48 ∧ V' = Vst W g₀.rdx (toBytesLE (g₀.rdi + 24#64) 8) ∧ g'.rax = g₀.rdi + 24#64 ∧
           ∀ i < 16, Eqb W g₀.rsi 7255936#64 i) ∨
         (j' = 240 ∧ V' = W ∧ g'.rax = 0#64 ∧ g'.rcx = 7255952#64 ∧ ∃ i < 16, ¬ Eqb W g₀.rsi 7255936#64 i)))
      hK hA hrip (vc_192 ?_ ?_ ?_ ?_ ?_ ?_) ?_
    · rw [hax, hcx]; exact hfa j (by omega)
    · rw [hax, hks.2.1]; exact hfb j (by omega)
    · rw [hks.1]; exact hfw
    · intro _ hn _
      exfalso; apply hn
      rw [hax, ofNat_succ, ofNat_eq16 (j := j + 1) (by omega)]
      omega
    · intro he _ _
      refine ⟨hks, Or.inl ⟨rfl, by rw [hks.1, hks.2.2.1], ?_, fun i hi => ?_⟩⟩
      · show X.cpu.gpr.rdi + 24#64 = _
        rw [hks.2.2.1]
      · rcases Nat.lt_or_ge i j with h | h
        · exact hpre i h
        · obtain rfl : i = j := by omega
          rw [hax, hcx, hks.2.1] at he
          exact he
    · intro he _
      refine ⟨hks, Or.inr ⟨rfl, rfl, rfl, rfl, j, by omega, ?_⟩⟩
      rw [hax, hcx, hks.2.1] at he
      exact he
    · rintro j' g fl V' ⟨hks', hc⟩ Y t' hKY hAY hrY hgY -
      subst hgY
      rcases hc with ⟨rfl, rfl, h0, hall⟩ | ⟨rfl, rfl, h0, h1, hx⟩
      · exact k48 Y t' hKY hAY hrY hks' h0 hall
      · exact k240 Y t' hKY hAY hrY hks' h0 h1 hx
  | succ m ih =>
    intro j hj X t hK hA hrip hax hcx hks hpre
    refine (c_192 prof).run c hin
      (fun j' g' _ V' => Kq g₀ g' ∧
        ((j' = 192 ∧ V' = W ∧ g'.rax = BitVec.ofNat 64 (j + 1) ∧ g'.rcx = 7255936#64 ∧
           Eqb W g₀.rsi 7255936#64 j) ∨
         (j' = 240 ∧ V' = W ∧ g'.rax = 0#64 ∧ g'.rcx = 7255952#64 ∧ ∃ i < 16, ¬ Eqb W g₀.rsi 7255936#64 i)))
      hK hA hrip (vc_192 ?_ ?_ ?_ ?_ ?_ ?_) ?_
    · rw [hax, hcx]; exact hfa j (by omega)
    · rw [hax, hks.2.1]; exact hfb j (by omega)
    · rw [hks.1]; exact hfw
    · intro he _ _
      refine ⟨hks, Or.inl ⟨rfl, rfl, ?_, hcx, ?_⟩⟩
      · show X.cpu.gpr.rax + 1#64 = _
        rw [hax, ofNat_succ]
      · rw [hax, hcx, hks.2.1] at he
        exact he
    · intro _ hn _
      exfalso
      rw [hax, ofNat_succ, ofNat_eq16 (j := j + 1) (by omega)] at hn
      omega
    · intro he _
      refine ⟨hks, Or.inr ⟨rfl, rfl, rfl, rfl, j, by omega, ?_⟩⟩
      rw [hax, hcx, hks.2.1] at he
      exact he
    · rintro j' g fl V' ⟨hks', hc⟩ Y t' hKY hAY hrY hgY -
      subst hgY
      rcases hc with ⟨rfl, rfl, h0, h1, he⟩ | ⟨rfl, rfl, h0, h1, hx⟩
      · refine ih (j + 1) (by omega) Y t' hKY hAY hrY h0 h1 hks' fun i hi => ?_
        rcases Nat.lt_or_ge i j with h | h
        · exact hpre i h
        · obtain rfl : i = j := by omega
          exact he
      · exact k240 Y t' hKY hAY hrY hks' h0 h1 hx

/-- The fifth loop from 240 at the index `j` (`j ≤ 15`), the bytes of `iid` before `j` those of the IID at
`0x6eb790`: on to the `AddRef` at 48 with all 16 equal and `*ppv = this + 32`, or on a mismatch to the `ret`
at 278 with `rax` = `E_NOINTERFACE`. -/
theorem loop5 (c : Seg prof F Wl L s₀ o) (hin : CodeIn L ecq_at ecq) {W : Addr → Byte} {g₀ : Gprs}
    (hfa : ∀ j < 16, ∀ i : Nat, i < 1 → Foot F.data (Addr.add (BitVec.ofNat 64 j + 7255952#64) i))
    (hfb : ∀ j < 16, ∀ i : Nat, i < 1 → Foot F.data (Addr.add (g₀.rsi + BitVec.ofNat 64 j) i))
    (hfw : ∀ i < 8, Foot Wl (Addr.add g₀.rdx i))
    (k48 : ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y →
      Agree F Y.proc.mm.mem (Vst W g₀.rdx (toBytesLE (g₀.rdi + 32#64) 8)) → Y.cpu.rip = ecq_at.add 48 →
      Kq g₀ Y.cpu.gpr → Y.cpu.gpr.rax = g₀.rdi + 32#64 → (∀ i < 16, Eqb W g₀.rsi 7255952#64 i) →
      GoG prof L o gev gP gE Y t')
    (k278 : ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y → Agree F Y.proc.mm.mem W → Y.cpu.rip = ecq_at.add 278 →
      Kq g₀ Y.cpu.gpr → Y.cpu.gpr.rax = 2147500034#64 →
      (∃ i < 16, ¬ Eqb W g₀.rsi 7255952#64 i) → GoG prof L o gev gP gE Y t') :
    ∀ (m j : Nat), j + m = 15 → ∀ (X : State) (t : Nat), KeptW Wl s₀ X → Agree F X.proc.mm.mem W →
      X.cpu.rip = ecq_at.add 240 → X.cpu.gpr.rax = BitVec.ofNat 64 j → X.cpu.gpr.rcx = 7255952#64 →
      Kq g₀ X.cpu.gpr → (∀ i < j, Eqb W g₀.rsi 7255952#64 i) → GoG prof L o gev gP gE X t := by
  intro m
  induction m with
  | zero =>
    intro j hj X t hK hA hrip hax hcx hks hpre
    refine (c_240 prof).run c hin
      (fun j' g' _ V' => Kq g₀ g' ∧
        ((j' = 48 ∧ V' = Vst W g₀.rdx (toBytesLE (g₀.rdi + 32#64) 8) ∧ g'.rax = g₀.rdi + 32#64 ∧
           ∀ i < 16, Eqb W g₀.rsi 7255952#64 i) ∨
         (j' = 278 ∧ V' = W ∧ g'.rax = 2147500034#64 ∧ ∃ i < 16, ¬ Eqb W g₀.rsi 7255952#64 i)))
      hK hA hrip (vc_240 ?_ ?_ ?_ ?_ ?_ ?_) ?_
    · rw [hax, hcx]; exact hfa j (by omega)
    · rw [hax, hks.2.1]; exact hfb j (by omega)
    · rw [hks.1]; exact hfw
    · intro _ hn _
      exfalso; apply hn
      rw [hax, ofNat_succ, ofNat_eq16 (j := j + 1) (by omega)]
      omega
    · intro he _ _
      refine ⟨hks, Or.inl ⟨rfl, by rw [hks.1, hks.2.2.1], ?_, fun i hi => ?_⟩⟩
      · show X.cpu.gpr.rdi + 32#64 = _
        rw [hks.2.2.1]
      · rcases Nat.lt_or_ge i j with h | h
        · exact hpre i h
        · obtain rfl : i = j := by omega
          rw [hax, hcx, hks.2.1] at he
          exact he
    · intro he _
      refine ⟨hks, Or.inr ⟨rfl, rfl, rfl, j, by omega, ?_⟩⟩
      rw [hax, hcx, hks.2.1] at he
      exact he
    · rintro j' g fl V' ⟨hks', hc⟩ Y t' hKY hAY hrY hgY -
      subst hgY
      rcases hc with ⟨rfl, rfl, h0, hall⟩ | ⟨rfl, rfl, h0, hx⟩
      · exact k48 Y t' hKY hAY hrY hks' h0 hall
      · exact k278 Y t' hKY hAY hrY hks' h0 hx
  | succ m ih =>
    intro j hj X t hK hA hrip hax hcx hks hpre
    refine (c_240 prof).run c hin
      (fun j' g' _ V' => Kq g₀ g' ∧
        ((j' = 240 ∧ V' = W ∧ g'.rax = BitVec.ofNat 64 (j + 1) ∧ g'.rcx = 7255952#64 ∧
           Eqb W g₀.rsi 7255952#64 j) ∨
         (j' = 278 ∧ V' = W ∧ g'.rax = 2147500034#64 ∧ ∃ i < 16, ¬ Eqb W g₀.rsi 7255952#64 i)))
      hK hA hrip (vc_240 ?_ ?_ ?_ ?_ ?_ ?_) ?_
    · rw [hax, hcx]; exact hfa j (by omega)
    · rw [hax, hks.2.1]; exact hfb j (by omega)
    · rw [hks.1]; exact hfw
    · intro he _ _
      refine ⟨hks, Or.inl ⟨rfl, rfl, ?_, hcx, ?_⟩⟩
      · show X.cpu.gpr.rax + 1#64 = _
        rw [hax, ofNat_succ]
      · rw [hax, hcx, hks.2.1] at he
        exact he
    · intro _ hn _
      exfalso
      rw [hax, ofNat_succ, ofNat_eq16 (j := j + 1) (by omega)] at hn
      omega
    · intro he _
      refine ⟨hks, Or.inr ⟨rfl, rfl, rfl, j, by omega, ?_⟩⟩
      rw [hax, hcx, hks.2.1] at he
      exact he
    · rintro j' g fl V' ⟨hks', hc⟩ Y t' hKY hAY hrY hgY -
      subst hgY
      rcases hc with ⟨rfl, rfl, h0, h1, he⟩ | ⟨rfl, rfl, h0, hx⟩
      · refine ih (j + 1) (by omega) Y t' hKY hAY hrY h0 h1 hks' fun i hi => ?_
        rcases Nat.lt_or_ge i j with h | h
        · exact hpre i h
        · obtain rfl : i = j := by omega
          exact he
      · exact k278 Y t' hKY hAY hrY hks' h0 hx

end FV7z.Ecq
