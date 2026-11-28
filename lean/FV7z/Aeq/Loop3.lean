import FV7z.Aeq.Loop1
/-!
# `CArchiveExtractCallback::QueryInterface`: the third loop (PLAN.md §M, M1)

The third loop (128, 139, and its exits 149 and 168) compares the 16 bytes of `iid` (`rsi`) with the IID at
`0x6eb780`, `rax` the index.

- `loop3`: from 128 at the index `j` with the bytes before `j` equal, on to the `AddRef` at 158 with all 16 equal
  (`*ppv = this + 16`, `rax` = 0), or on a mismatch to the fourth loop at 184. By induction on `15 - j`.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
open FV7z.Ecq (bq Kq ofNat_succ ofNat_eq16 Eqb)
namespace FV7z.Aeq

variable {F : Footprint} {Wl : List Rgn} {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State}
  {o : Oracle} {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}

/-- The third loop from 128 at the index `j` (`j ≤ 15`), the bytes of `iid` before `j` those of the IID at
`0x6eb780`: on to 158 with all 16 equal and `*ppv = this + 16`, or on a mismatch to the fourth loop at 184. -/
theorem loop3 (c : Seg prof F Wl L s₀ o) (hin : CodeIn L aeq_at aeq) {W : Addr → Byte} {g₀ : Gprs}
    (hfa : ∀ j < 16, ∀ i : Nat, i < 1 → Foot F.data (Addr.add (BitVec.ofNat 64 j + 7255936#64) i))
    (hfb : ∀ j < 16, ∀ i : Nat, i < 1 → Foot F.data (Addr.add (g₀.rsi + BitVec.ofNat 64 j) i))
    (hfw : ∀ i < 8, Foot Wl (Addr.add g₀.rdx i))
    (k158 : ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y →
      Agree F Y.proc.mm.mem (Vst W g₀.rdx (toBytesLE (g₀.rdi + 16#64) 8)) → Y.cpu.rip = aeq_at.add 158 →
      Kq g₀ Y.cpu.gpr → Y.cpu.gpr.rax = 0#64 → (∀ i < 16, Eqb W g₀.rsi 7255936#64 i) →
      GoG prof L o gev gP gE Y t')
    (k184 : ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y → Agree F Y.proc.mm.mem W → Y.cpu.rip = aeq_at.add 184 →
      Kq g₀ Y.cpu.gpr → Y.cpu.gpr.rax = 0#64 → Y.cpu.gpr.rcx = 7255904#64 →
      (∃ i < 16, ¬ Eqb W g₀.rsi 7255936#64 i) → GoG prof L o gev gP gE Y t') :
    ∀ (m j : Nat), j + m = 15 → ∀ (X : State) (t : Nat), KeptW Wl s₀ X → Agree F X.proc.mm.mem W →
      X.cpu.rip = aeq_at.add 128 → X.cpu.gpr.rax = BitVec.ofNat 64 j → X.cpu.gpr.rcx = 7255936#64 →
      Kq g₀ X.cpu.gpr → (∀ i < j, Eqb W g₀.rsi 7255936#64 i) → GoG prof L o gev gP gE X t := by
  intro m
  induction m with
  | zero =>
    intro j hj X t hK hA hrip hax hcx hks hpre
    refine (c_128 prof).run c hin
      (fun j' g' _ V' => Kq g₀ g' ∧
        ((j' = 158 ∧ V' = Vst W g₀.rdx (toBytesLE (g₀.rdi + 16#64) 8) ∧ g'.rax = 0#64 ∧
           ∀ i < 16, Eqb W g₀.rsi 7255936#64 i) ∨
         (j' = 184 ∧ V' = W ∧ g'.rax = 0#64 ∧ g'.rcx = 7255904#64 ∧ ∃ i < 16, ¬ Eqb W g₀.rsi 7255936#64 i)))
      hK hA hrip (vc_128 ?_ ?_ ?_ ?_ ?_ ?_) ?_
    · rw [hax, hcx]; exact hfa j (by omega)
    · rw [hax, hks.2.1]; exact hfb j (by omega)
    · rw [hks.1]; exact hfw
    · intro _ hn _
      exfalso; apply hn
      rw [hax, ofNat_succ, ofNat_eq16 (j := j + 1) (by omega)]
      omega
    · intro he _ _
      refine ⟨hks, Or.inl ⟨rfl, by rw [hks.1, hks.2.2.1], rfl, fun i hi => ?_⟩⟩
      rcases Nat.lt_or_ge i j with h | h
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
      · exact k158 Y t' hKY hAY hrY hks' h0 hall
      · exact k184 Y t' hKY hAY hrY hks' h0 h1 hx
  | succ m ih =>
    intro j hj X t hK hA hrip hax hcx hks hpre
    refine (c_128 prof).run c hin
      (fun j' g' _ V' => Kq g₀ g' ∧
        ((j' = 128 ∧ V' = W ∧ g'.rax = BitVec.ofNat 64 (j + 1) ∧ g'.rcx = 7255936#64 ∧
           Eqb W g₀.rsi 7255936#64 j) ∨
         (j' = 184 ∧ V' = W ∧ g'.rax = 0#64 ∧ g'.rcx = 7255904#64 ∧ ∃ i < 16, ¬ Eqb W g₀.rsi 7255936#64 i)))
      hK hA hrip (vc_128 ?_ ?_ ?_ ?_ ?_ ?_) ?_
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
      · exact k184 Y t' hKY hAY hrY hks' h0 h1 hx

end FV7z.Aeq
