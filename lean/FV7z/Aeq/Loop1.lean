import FV7z.Aeq.Holds
import FV7z.Ecq.Loop1
/-!
# `CArchiveExtractCallback::QueryInterface`: the first loop (PLAN.md §M, M1)

The first loop of `CArchiveExtractCallback::QueryInterface` (24, 35, and on a mismatch the second loop's first
compare at 64) compares the 16 bytes of `iid` (`rsi`) with the IID at `0x6eb970`, `rax` the index. `Kq`,
`ofNat_succ`, `ofNat_eq16` and `Eqb` are `FV7z.Ecq`'s.

- `loop1`: from 24 at the index `j` with the bytes before `j` equal, on to 45 with all 16 equal, or on a mismatch to
  88 (the first byte of the IID at `0x6eb890` equal) or 109. By induction on `15 - j`.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
open FV7z.Ecq (bq Kq ofNat_succ ofNat_eq16 Eqb)
namespace FV7z.Aeq

variable {F : Footprint} {Wl : List Rgn} {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State}
  {o : Oracle} {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}

/-- The first loop from 24 at the index `j` (`j ≤ 15`), the bytes of `iid` before `j` those of the IID at
`0x6eb970`: on to 45 with all 16 equal, or on a mismatch (the second loop's first compare done) to 88 or 109. -/
theorem loop1 (c : Seg prof F Wl L s₀ o) (hin : CodeIn L aeq_at aeq) {W : Addr → Byte} {g₀ : Gprs}
    (hfa : ∀ j < 16, ∀ i : Nat, i < 1 → Foot F.data (Addr.add (BitVec.ofNat 64 j + 7256432#64) i))
    (hfb : ∀ j < 16, ∀ i : Nat, i < 1 → Foot F.data (Addr.add (g₀.rsi + BitVec.ofNat 64 j) i))
    (hfc : ∀ i : Nat, i < 1 → Foot F.data (Addr.add (0#64 + 7256208#64) i))
    (hfd : ∀ i : Nat, i < 1 → Foot F.data (Addr.add g₀.rsi i))
    (k45 : ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y → Agree F Y.proc.mm.mem W → Y.cpu.rip = aeq_at.add 45 →
      Kq g₀ Y.cpu.gpr → (∀ i < 16, Eqb W g₀.rsi 7256432#64 i) → GoG prof L o gev gP gE Y t')
    (k88 : ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y → Agree F Y.proc.mm.mem W → Y.cpu.rip = aeq_at.add 88 →
      Kq g₀ Y.cpu.gpr → Y.cpu.gpr.rax = 0#64 → Y.cpu.gpr.rcx = 7256208#64 →
      (∃ i < 16, ¬ Eqb W g₀.rsi 7256432#64 i) → bq W g₀.rsi = bq W (0#64 + 7256208#64) →
      GoG prof L o gev gP gE Y t')
    (k109 : ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y → Agree F Y.proc.mm.mem W → Y.cpu.rip = aeq_at.add 109 →
      Kq g₀ Y.cpu.gpr → (∃ i < 16, ¬ Eqb W g₀.rsi 7256432#64 i) → ¬ bq W g₀.rsi = bq W (0#64 + 7256208#64) →
      GoG prof L o gev gP gE Y t') :
    ∀ (m j : Nat), j + m = 15 → ∀ (X : State) (t : Nat), KeptW Wl s₀ X → Agree F X.proc.mm.mem W →
      X.cpu.rip = aeq_at.add 24 → X.cpu.gpr.rax = BitVec.ofNat 64 j → X.cpu.gpr.rcx = 7256432#64 →
      Kq g₀ X.cpu.gpr → (∀ i < j, Eqb W g₀.rsi 7256432#64 i) → GoG prof L o gev gP gE X t := by
  intro m
  induction m with
  | zero =>
    intro j hj X t hK hA hrip hax hcx hks hpre
    refine (c_24 prof).run c hin
      (fun j' g' _ V' => V' = W ∧ Kq g₀ g' ∧
        ((j' = 45 ∧ ∀ i < 16, Eqb W g₀.rsi 7256432#64 i) ∨
         (j' = 88 ∧ g'.rax = 0#64 ∧ g'.rcx = 7256208#64 ∧ (∃ i < 16, ¬ Eqb W g₀.rsi 7256432#64 i) ∧
           bq W g₀.rsi = bq W (0#64 + 7256208#64)) ∨
         (j' = 109 ∧ (∃ i < 16, ¬ Eqb W g₀.rsi 7256432#64 i) ∧ ¬ bq W g₀.rsi = bq W (0#64 + 7256208#64))))
      hK hA hrip (vc_24 ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_) ?_
    · rw [hax, hcx]; exact hfa j (by omega)
    · rw [hax, hks.2.1]; exact hfb j (by omega)
    · exact hfc
    · rw [hks.2.1]; exact hfd
    · intro _ hn _
      exfalso; apply hn
      rw [hax, ofNat_succ, ofNat_eq16 (j := j + 1) (by omega)]
      omega
    · intro he _ _
      refine ⟨rfl, hks, Or.inl ⟨rfl, fun i hi => ?_⟩⟩
      rcases Nat.lt_or_ge i j with h | h
      · exact hpre i h
      · obtain rfl : i = j := by omega
        rw [hax, hcx, hks.2.1] at he
        exact he.symm
    · intro he he2 _
      rw [hks.2.1] at he2
      refine ⟨rfl, hks, Or.inr (Or.inr ⟨rfl, ⟨j, by omega, ?_⟩, he2⟩)⟩
      rw [hax, hcx, hks.2.1] at he
      exact fun h => he h.symm
    · intro he he2 _
      rw [hks.2.1] at he2
      refine ⟨rfl, hks, Or.inr (Or.inl ⟨rfl, rfl, rfl, ⟨j, by omega, ?_⟩, he2⟩)⟩
      rw [hax, hcx, hks.2.1] at he
      exact fun h => he h.symm
    · rintro j' g fl V' ⟨rfl, hks', hc⟩ Y t' hKY hAY hrY hgY -
      subst hgY
      rcases hc with ⟨rfl, hall⟩ | ⟨rfl, h0, h1, hx, h2⟩ | ⟨rfl, hx, h2⟩
      · exact k45 Y t' hKY hAY hrY hks' hall
      · exact k88 Y t' hKY hAY hrY hks' h0 h1 hx h2
      · exact k109 Y t' hKY hAY hrY hks' hx h2
  | succ m ih =>
    intro j hj X t hK hA hrip hax hcx hks hpre
    refine (c_24 prof).run c hin
      (fun j' g' _ V' => V' = W ∧ Kq g₀ g' ∧
        ((j' = 24 ∧ g'.rax = BitVec.ofNat 64 (j + 1) ∧ g'.rcx = 7256432#64 ∧ Eqb W g₀.rsi 7256432#64 j) ∨
         (j' = 88 ∧ g'.rax = 0#64 ∧ g'.rcx = 7256208#64 ∧ (∃ i < 16, ¬ Eqb W g₀.rsi 7256432#64 i) ∧
           bq W g₀.rsi = bq W (0#64 + 7256208#64)) ∨
         (j' = 109 ∧ (∃ i < 16, ¬ Eqb W g₀.rsi 7256432#64 i) ∧ ¬ bq W g₀.rsi = bq W (0#64 + 7256208#64))))
      hK hA hrip (vc_24 ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_) ?_
    · rw [hax, hcx]; exact hfa j (by omega)
    · rw [hax, hks.2.1]; exact hfb j (by omega)
    · exact hfc
    · rw [hks.2.1]; exact hfd
    · intro he _ _
      refine ⟨rfl, hks, Or.inl ⟨rfl, ?_, hcx, ?_⟩⟩
      · show X.cpu.gpr.rax + 1#64 = _
        rw [hax, ofNat_succ]
      · rw [hax, hcx, hks.2.1] at he
        exact he.symm
    · intro _ hn _
      exfalso
      rw [hax, ofNat_succ, ofNat_eq16 (j := j + 1) (by omega)] at hn
      omega
    · intro he he2 _
      rw [hks.2.1] at he2
      refine ⟨rfl, hks, Or.inr (Or.inr ⟨rfl, ⟨j, by omega, ?_⟩, he2⟩)⟩
      rw [hax, hcx, hks.2.1] at he
      exact fun h => he h.symm
    · intro he he2 _
      rw [hks.2.1] at he2
      refine ⟨rfl, hks, Or.inr (Or.inl ⟨rfl, rfl, rfl, ⟨j, by omega, ?_⟩, he2⟩)⟩
      rw [hax, hcx, hks.2.1] at he
      exact fun h => he h.symm
    · rintro j' g fl V' ⟨rfl, hks', hc⟩ Y t' hKY hAY hrY hgY -
      subst hgY
      rcases hc with ⟨rfl, h0, h1, he⟩ | ⟨rfl, h0, h1, hx, h2⟩ | ⟨rfl, hx, h2⟩
      · refine ih (j + 1) (by omega) Y t' hKY hAY hrY h0 h1 hks' fun i hi => ?_
        rcases Nat.lt_or_ge i j with h | h
        · exact hpre i h
        · obtain rfl : i = j := by omega
          exact he
      · exact k88 Y t' hKY hAY hrY hks' h0 h1 hx h2
      · exact k109 Y t' hKY hAY hrY hks' hx h2

end FV7z.Aeq
