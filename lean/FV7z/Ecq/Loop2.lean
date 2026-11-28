import FV7z.Ecq.Loop1
/-!
# `CExtractCallbackConsole::QueryInterface`: the second loop (PLAN.md §M, M1)

The second loop (88, 98) compares the 16 bytes of `iid` (`rsi`) with the IID at `0x6eb590`, `rax` the index; the
first loop's mismatch exit has already compared the first byte (64).

- `loop2`: from 88 at the index `j` with the bytes up to `j` equal, on to 45 with all 16 equal or on a mismatch to
  109. By induction on `15 - j`.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Ecq

variable {F : Footprint} {Wl : List Rgn} {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State}
  {o : Oracle} {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}

/-- The second loop from 88 at the index `j` (`j ≤ 15`), the bytes of `iid` up to `j` those of the IID at
`0x6eb590`: on to 45 with all 16 equal, or on a mismatch to 109. -/
theorem loop2 (c : Seg prof F Wl L s₀ o) (hin : CodeIn L ecq_at ecq) {W : Addr → Byte} {g₀ : Gprs}
    (hfa : ∀ j < 16, ∀ i : Nat, i < 1 → Foot F.data (Addr.add (BitVec.ofNat 64 j + 7255440#64) i))
    (hfb : ∀ j < 16, ∀ i : Nat, i < 1 → Foot F.data (Addr.add (g₀.rsi + BitVec.ofNat 64 j) i))
    (k45 : ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y → Agree F Y.proc.mm.mem W → Y.cpu.rip = ecq_at.add 45 →
      Kq g₀ Y.cpu.gpr → (∀ i < 16, Eqb W g₀.rsi 7255440#64 i) → GoG prof L o gev gP gE Y t')
    (k109 : ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y → Agree F Y.proc.mm.mem W → Y.cpu.rip = ecq_at.add 109 →
      Kq g₀ Y.cpu.gpr → (∃ i < 16, ¬ Eqb W g₀.rsi 7255440#64 i) → GoG prof L o gev gP gE Y t') :
    ∀ (m j : Nat), j + m = 15 → ∀ (X : State) (t : Nat), KeptW Wl s₀ X → Agree F X.proc.mm.mem W →
      X.cpu.rip = ecq_at.add 88 → X.cpu.gpr.rax = BitVec.ofNat 64 j → X.cpu.gpr.rcx = 7255440#64 →
      Kq g₀ X.cpu.gpr → (∀ i ≤ j, Eqb W g₀.rsi 7255440#64 i) → GoG prof L o gev gP gE X t := by
  intro m
  induction m with
  | zero =>
    intro j hj X t hK hA hrip hax hcx hks hpre
    refine (c_88 prof).run c hin
      (fun j' g' _ V' => Kq g₀ g' ∧ V' = W ∧ j' = 45 ∧ ∀ i < 16, Eqb W g₀.rsi 7255440#64 i)
      hK hA hrip (vc_88 ?_ ?_ ?_ ?_ ?_) ?_
    · rw [hax, hcx, ofNat_succ]; exact hfa (j + 1) (by omega)
    · rw [hax, hks.2.1, ofNat_succ]; exact hfb (j + 1) (by omega)
    · intro _ _
      exact ⟨hks, rfl, rfl, fun i hi => hpre i (by omega)⟩
    · intro hn _ _
      exfalso; apply hn
      rw [hax, ofNat_succ, ofNat_eq16 (j := j + 1) (by omega)]
      omega
    · intro hn _ _
      exfalso; apply hn
      rw [hax, ofNat_succ, ofNat_eq16 (j := j + 1) (by omega)]
      omega
    · rintro j' g fl V' ⟨hks', rfl, rfl, hall⟩ Y t' hKY hAY hrY hgY -
      subst hgY
      exact k45 Y t' hKY hAY hrY hks' hall
  | succ m ih =>
    intro j hj X t hK hA hrip hax hcx hks hpre
    refine (c_88 prof).run c hin
      (fun j' g' _ V' => Kq g₀ g' ∧ V' = W ∧
        ((j' = 88 ∧ g'.rax = BitVec.ofNat 64 (j + 1) ∧ g'.rcx = 7255440#64 ∧ Eqb W g₀.rsi 7255440#64 (j + 1)) ∨
         (j' = 109 ∧ ∃ i < 16, ¬ Eqb W g₀.rsi 7255440#64 i)))
      hK hA hrip (vc_88 ?_ ?_ ?_ ?_ ?_) ?_
    · rw [hax, hcx, ofNat_succ]; exact hfa (j + 1) (by omega)
    · rw [hax, hks.2.1, ofNat_succ]; exact hfb (j + 1) (by omega)
    · intro hn _
      exfalso
      rw [hax, ofNat_succ, ofNat_eq16 (j := j + 1) (by omega)] at hn
      omega
    · intro _ he _
      refine ⟨hks, rfl, Or.inl ⟨rfl, ?_, hcx, ?_⟩⟩
      · show X.cpu.gpr.rax + 1#64 = _
        rw [hax, ofNat_succ]
      · rw [hax, hcx, hks.2.1, ofNat_succ] at he
        exact he
    · intro _ he _
      refine ⟨hks, rfl, Or.inr ⟨rfl, j + 1, by omega, ?_⟩⟩
      rw [hax, hcx, hks.2.1, ofNat_succ] at he
      exact he
    · rintro j' g fl V' ⟨hks', rfl, hc⟩ Y t' hKY hAY hrY hgY -
      subst hgY
      rcases hc with ⟨rfl, h0, h1, he⟩ | ⟨rfl, hx⟩
      · refine ih (j + 1) (by omega) Y t' hKY hAY hrY h0 h1 hks' fun i hi => ?_
        rcases Nat.lt_or_ge i (j + 1) with h | h
        · exact hpre i (by omega)
        · obtain rfl : i = j + 1 := by omega
          exact he
      · exact k109 Y t' hKY hAY hrY hks' hx

end FV7z.Ecq
