import FV7z.Aeq.Loop1
/-!
# `CArchiveExtractCallback::QueryInterface`: the fourth to seventh loop (PLAN.md §M, M1)

The fourth to seventh loop (184, 232, 280, 328, each with its counter and two exits) compare the 16 bytes of `iid`
(`rsi`) with the IIDs at `0x6eb760`, `0x6eb7f0`, `0x6eb7e0` and `0x6eb790`, `rax` the index.

- `loop4`, `loop5`, `loop6`: on to the `AddRef` at 52 (`*ppv = this + 24`, `+ 32`, `+ 40`) or on a mismatch to the
  next loop.
- `loop7`: on to the `AddRef` at 52 (`*ppv = this + 48`) or on a mismatch to the `ret` at 366 with
  `E_NOINTERFACE`. All by induction on `15 - j`.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
open FV7z.Ecq (bq Kq ofNat_succ ofNat_eq16 Eqb)
namespace FV7z.Aeq

variable {F : Footprint} {Wl : List Rgn} {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State}
  {o : Oracle} {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}

/-- The fourth loop from 184 at the index `j` (`j ≤ 15`), the bytes of `iid` before `j` those of the IID at
`0x6eb760`: on to the `AddRef` at 52 with all 16 equal and `*ppv = this + 24`, or on a mismatch to the fifth
loop at 232. -/
theorem loop4 (c : Seg prof F Wl L s₀ o) (hin : CodeIn L aeq_at aeq) {W : Addr → Byte} {g₀ : Gprs}
    (hfa : ∀ j < 16, ∀ i : Nat, i < 1 → Foot F.data (Addr.add (BitVec.ofNat 64 j + 7255904#64) i))
    (hfb : ∀ j < 16, ∀ i : Nat, i < 1 → Foot F.data (Addr.add (g₀.rsi + BitVec.ofNat 64 j) i))
    (hfw : ∀ i < 8, Foot Wl (Addr.add g₀.rdx i))
    (k52 : ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y →
      Agree F Y.proc.mm.mem (Vst W g₀.rdx (toBytesLE (g₀.rdi + 24#64) 8)) → Y.cpu.rip = aeq_at.add 52 →
      Kq g₀ Y.cpu.gpr → Y.cpu.gpr.rax = g₀.rdi + 24#64 → (∀ i < 16, Eqb W g₀.rsi 7255904#64 i) →
      GoG prof L o gev gP gE Y t')
    (k232 : ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y → Agree F Y.proc.mm.mem W → Y.cpu.rip = aeq_at.add 232 →
      Kq g₀ Y.cpu.gpr → Y.cpu.gpr.rax = 0#64 → Y.cpu.gpr.rcx = 7256048#64 →
      (∃ i < 16, ¬ Eqb W g₀.rsi 7255904#64 i) → GoG prof L o gev gP gE Y t') :
    ∀ (m j : Nat), j + m = 15 → ∀ (X : State) (t : Nat), KeptW Wl s₀ X → Agree F X.proc.mm.mem W →
      X.cpu.rip = aeq_at.add 184 → X.cpu.gpr.rax = BitVec.ofNat 64 j → X.cpu.gpr.rcx = 7255904#64 →
      Kq g₀ X.cpu.gpr → (∀ i < j, Eqb W g₀.rsi 7255904#64 i) → GoG prof L o gev gP gE X t := by
  intro m
  induction m with
  | zero =>
    intro j hj X t hK hA hrip hax hcx hks hpre
    refine (c_184 prof).run c hin
      (fun j' g' _ V' => Kq g₀ g' ∧
        ((j' = 52 ∧ V' = Vst W g₀.rdx (toBytesLE (g₀.rdi + 24#64) 8) ∧ g'.rax = g₀.rdi + 24#64 ∧
           ∀ i < 16, Eqb W g₀.rsi 7255904#64 i) ∨
         (j' = 232 ∧ V' = W ∧ g'.rax = 0#64 ∧ g'.rcx = 7256048#64 ∧ ∃ i < 16, ¬ Eqb W g₀.rsi 7255904#64 i)))
      hK hA hrip (vc_184 ?_ ?_ ?_ ?_ ?_ ?_) ?_
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
      · exact k52 Y t' hKY hAY hrY hks' h0 hall
      · exact k232 Y t' hKY hAY hrY hks' h0 h1 hx
  | succ m ih =>
    intro j hj X t hK hA hrip hax hcx hks hpre
    refine (c_184 prof).run c hin
      (fun j' g' _ V' => Kq g₀ g' ∧
        ((j' = 184 ∧ V' = W ∧ g'.rax = BitVec.ofNat 64 (j + 1) ∧ g'.rcx = 7255904#64 ∧
           Eqb W g₀.rsi 7255904#64 j) ∨
         (j' = 232 ∧ V' = W ∧ g'.rax = 0#64 ∧ g'.rcx = 7256048#64 ∧ ∃ i < 16, ¬ Eqb W g₀.rsi 7255904#64 i)))
      hK hA hrip (vc_184 ?_ ?_ ?_ ?_ ?_ ?_) ?_
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
      · exact k232 Y t' hKY hAY hrY hks' h0 h1 hx

/-- The fifth loop from 232 at the index `j` (`j ≤ 15`), the bytes of `iid` before `j` those of the IID at
`0x6eb7f0`: on to the `AddRef` at 52 with all 16 equal and `*ppv = this + 32`, or on a mismatch to the sixth
loop at 280. -/
theorem loop5 (c : Seg prof F Wl L s₀ o) (hin : CodeIn L aeq_at aeq) {W : Addr → Byte} {g₀ : Gprs}
    (hfa : ∀ j < 16, ∀ i : Nat, i < 1 → Foot F.data (Addr.add (BitVec.ofNat 64 j + 7256048#64) i))
    (hfb : ∀ j < 16, ∀ i : Nat, i < 1 → Foot F.data (Addr.add (g₀.rsi + BitVec.ofNat 64 j) i))
    (hfw : ∀ i < 8, Foot Wl (Addr.add g₀.rdx i))
    (k52 : ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y →
      Agree F Y.proc.mm.mem (Vst W g₀.rdx (toBytesLE (g₀.rdi + 32#64) 8)) → Y.cpu.rip = aeq_at.add 52 →
      Kq g₀ Y.cpu.gpr → Y.cpu.gpr.rax = g₀.rdi + 32#64 → (∀ i < 16, Eqb W g₀.rsi 7256048#64 i) →
      GoG prof L o gev gP gE Y t')
    (k280 : ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y → Agree F Y.proc.mm.mem W → Y.cpu.rip = aeq_at.add 280 →
      Kq g₀ Y.cpu.gpr → Y.cpu.gpr.rax = 0#64 → Y.cpu.gpr.rcx = 7256032#64 →
      (∃ i < 16, ¬ Eqb W g₀.rsi 7256048#64 i) → GoG prof L o gev gP gE Y t') :
    ∀ (m j : Nat), j + m = 15 → ∀ (X : State) (t : Nat), KeptW Wl s₀ X → Agree F X.proc.mm.mem W →
      X.cpu.rip = aeq_at.add 232 → X.cpu.gpr.rax = BitVec.ofNat 64 j → X.cpu.gpr.rcx = 7256048#64 →
      Kq g₀ X.cpu.gpr → (∀ i < j, Eqb W g₀.rsi 7256048#64 i) → GoG prof L o gev gP gE X t := by
  intro m
  induction m with
  | zero =>
    intro j hj X t hK hA hrip hax hcx hks hpre
    refine (c_232 prof).run c hin
      (fun j' g' _ V' => Kq g₀ g' ∧
        ((j' = 52 ∧ V' = Vst W g₀.rdx (toBytesLE (g₀.rdi + 32#64) 8) ∧ g'.rax = g₀.rdi + 32#64 ∧
           ∀ i < 16, Eqb W g₀.rsi 7256048#64 i) ∨
         (j' = 280 ∧ V' = W ∧ g'.rax = 0#64 ∧ g'.rcx = 7256032#64 ∧ ∃ i < 16, ¬ Eqb W g₀.rsi 7256048#64 i)))
      hK hA hrip (vc_232 ?_ ?_ ?_ ?_ ?_ ?_) ?_
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
      refine ⟨hks, Or.inr ⟨rfl, rfl, rfl, rfl, j, by omega, ?_⟩⟩
      rw [hax, hcx, hks.2.1] at he
      exact he
    · rintro j' g fl V' ⟨hks', hc⟩ Y t' hKY hAY hrY hgY -
      subst hgY
      rcases hc with ⟨rfl, rfl, h0, hall⟩ | ⟨rfl, rfl, h0, h1, hx⟩
      · exact k52 Y t' hKY hAY hrY hks' h0 hall
      · exact k280 Y t' hKY hAY hrY hks' h0 h1 hx
  | succ m ih =>
    intro j hj X t hK hA hrip hax hcx hks hpre
    refine (c_232 prof).run c hin
      (fun j' g' _ V' => Kq g₀ g' ∧
        ((j' = 232 ∧ V' = W ∧ g'.rax = BitVec.ofNat 64 (j + 1) ∧ g'.rcx = 7256048#64 ∧
           Eqb W g₀.rsi 7256048#64 j) ∨
         (j' = 280 ∧ V' = W ∧ g'.rax = 0#64 ∧ g'.rcx = 7256032#64 ∧ ∃ i < 16, ¬ Eqb W g₀.rsi 7256048#64 i)))
      hK hA hrip (vc_232 ?_ ?_ ?_ ?_ ?_ ?_) ?_
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
      · exact k280 Y t' hKY hAY hrY hks' h0 h1 hx

/-- The sixth loop from 280 at the index `j` (`j ≤ 15`), the bytes of `iid` before `j` those of the IID at
`0x6eb7e0`: on to the `AddRef` at 52 with all 16 equal and `*ppv = this + 40`, or on a mismatch to the seventh
loop at 328. -/
theorem loop6 (c : Seg prof F Wl L s₀ o) (hin : CodeIn L aeq_at aeq) {W : Addr → Byte} {g₀ : Gprs}
    (hfa : ∀ j < 16, ∀ i : Nat, i < 1 → Foot F.data (Addr.add (BitVec.ofNat 64 j + 7256032#64) i))
    (hfb : ∀ j < 16, ∀ i : Nat, i < 1 → Foot F.data (Addr.add (g₀.rsi + BitVec.ofNat 64 j) i))
    (hfw : ∀ i < 8, Foot Wl (Addr.add g₀.rdx i))
    (k52 : ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y →
      Agree F Y.proc.mm.mem (Vst W g₀.rdx (toBytesLE (g₀.rdi + 40#64) 8)) → Y.cpu.rip = aeq_at.add 52 →
      Kq g₀ Y.cpu.gpr → Y.cpu.gpr.rax = g₀.rdi + 40#64 → (∀ i < 16, Eqb W g₀.rsi 7256032#64 i) →
      GoG prof L o gev gP gE Y t')
    (k328 : ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y → Agree F Y.proc.mm.mem W → Y.cpu.rip = aeq_at.add 328 →
      Kq g₀ Y.cpu.gpr → Y.cpu.gpr.rax = 0#64 → Y.cpu.gpr.rcx = 7255952#64 →
      (∃ i < 16, ¬ Eqb W g₀.rsi 7256032#64 i) → GoG prof L o gev gP gE Y t') :
    ∀ (m j : Nat), j + m = 15 → ∀ (X : State) (t : Nat), KeptW Wl s₀ X → Agree F X.proc.mm.mem W →
      X.cpu.rip = aeq_at.add 280 → X.cpu.gpr.rax = BitVec.ofNat 64 j → X.cpu.gpr.rcx = 7256032#64 →
      Kq g₀ X.cpu.gpr → (∀ i < j, Eqb W g₀.rsi 7256032#64 i) → GoG prof L o gev gP gE X t := by
  intro m
  induction m with
  | zero =>
    intro j hj X t hK hA hrip hax hcx hks hpre
    refine (c_280 prof).run c hin
      (fun j' g' _ V' => Kq g₀ g' ∧
        ((j' = 52 ∧ V' = Vst W g₀.rdx (toBytesLE (g₀.rdi + 40#64) 8) ∧ g'.rax = g₀.rdi + 40#64 ∧
           ∀ i < 16, Eqb W g₀.rsi 7256032#64 i) ∨
         (j' = 328 ∧ V' = W ∧ g'.rax = 0#64 ∧ g'.rcx = 7255952#64 ∧ ∃ i < 16, ¬ Eqb W g₀.rsi 7256032#64 i)))
      hK hA hrip (vc_280 ?_ ?_ ?_ ?_ ?_ ?_) ?_
    · rw [hax, hcx]; exact hfa j (by omega)
    · rw [hax, hks.2.1]; exact hfb j (by omega)
    · rw [hks.1]; exact hfw
    · intro _ hn _
      exfalso; apply hn
      rw [hax, ofNat_succ, ofNat_eq16 (j := j + 1) (by omega)]
      omega
    · intro he _ _
      refine ⟨hks, Or.inl ⟨rfl, by rw [hks.1, hks.2.2.1], ?_, fun i hi => ?_⟩⟩
      · show X.cpu.gpr.rdi + 40#64 = _
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
      · exact k52 Y t' hKY hAY hrY hks' h0 hall
      · exact k328 Y t' hKY hAY hrY hks' h0 h1 hx
  | succ m ih =>
    intro j hj X t hK hA hrip hax hcx hks hpre
    refine (c_280 prof).run c hin
      (fun j' g' _ V' => Kq g₀ g' ∧
        ((j' = 280 ∧ V' = W ∧ g'.rax = BitVec.ofNat 64 (j + 1) ∧ g'.rcx = 7256032#64 ∧
           Eqb W g₀.rsi 7256032#64 j) ∨
         (j' = 328 ∧ V' = W ∧ g'.rax = 0#64 ∧ g'.rcx = 7255952#64 ∧ ∃ i < 16, ¬ Eqb W g₀.rsi 7256032#64 i)))
      hK hA hrip (vc_280 ?_ ?_ ?_ ?_ ?_ ?_) ?_
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
      · exact k328 Y t' hKY hAY hrY hks' h0 h1 hx

/-- The seventh loop from 328 at the index `j` (`j ≤ 15`), the bytes of `iid` before `j` those of the IID at
`0x6eb790`: on to the `AddRef` at 52 with all 16 equal and `*ppv = this + 48`, or on a mismatch to the `ret`
at 366 with `rax` = `E_NOINTERFACE`. -/
theorem loop7 (c : Seg prof F Wl L s₀ o) (hin : CodeIn L aeq_at aeq) {W : Addr → Byte} {g₀ : Gprs}
    (hfa : ∀ j < 16, ∀ i : Nat, i < 1 → Foot F.data (Addr.add (BitVec.ofNat 64 j + 7255952#64) i))
    (hfb : ∀ j < 16, ∀ i : Nat, i < 1 → Foot F.data (Addr.add (g₀.rsi + BitVec.ofNat 64 j) i))
    (hfw : ∀ i < 8, Foot Wl (Addr.add g₀.rdx i))
    (k52 : ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y →
      Agree F Y.proc.mm.mem (Vst W g₀.rdx (toBytesLE (g₀.rdi + 48#64) 8)) → Y.cpu.rip = aeq_at.add 52 →
      Kq g₀ Y.cpu.gpr → Y.cpu.gpr.rax = g₀.rdi + 48#64 → (∀ i < 16, Eqb W g₀.rsi 7255952#64 i) →
      GoG prof L o gev gP gE Y t')
    (k366 : ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y → Agree F Y.proc.mm.mem W → Y.cpu.rip = aeq_at.add 366 →
      Kq g₀ Y.cpu.gpr → Y.cpu.gpr.rax = 2147500034#64 →
      (∃ i < 16, ¬ Eqb W g₀.rsi 7255952#64 i) → GoG prof L o gev gP gE Y t') :
    ∀ (m j : Nat), j + m = 15 → ∀ (X : State) (t : Nat), KeptW Wl s₀ X → Agree F X.proc.mm.mem W →
      X.cpu.rip = aeq_at.add 328 → X.cpu.gpr.rax = BitVec.ofNat 64 j → X.cpu.gpr.rcx = 7255952#64 →
      Kq g₀ X.cpu.gpr → (∀ i < j, Eqb W g₀.rsi 7255952#64 i) → GoG prof L o gev gP gE X t := by
  intro m
  induction m with
  | zero =>
    intro j hj X t hK hA hrip hax hcx hks hpre
    refine (c_328 prof).run c hin
      (fun j' g' _ V' => Kq g₀ g' ∧
        ((j' = 52 ∧ V' = Vst W g₀.rdx (toBytesLE (g₀.rdi + 48#64) 8) ∧ g'.rax = g₀.rdi + 48#64 ∧
           ∀ i < 16, Eqb W g₀.rsi 7255952#64 i) ∨
         (j' = 366 ∧ V' = W ∧ g'.rax = 2147500034#64 ∧ ∃ i < 16, ¬ Eqb W g₀.rsi 7255952#64 i)))
      hK hA hrip (vc_328 ?_ ?_ ?_ ?_ ?_ ?_) ?_
    · rw [hax, hcx]; exact hfa j (by omega)
    · rw [hax, hks.2.1]; exact hfb j (by omega)
    · rw [hks.1]; exact hfw
    · intro _ hn _
      exfalso; apply hn
      rw [hax, ofNat_succ, ofNat_eq16 (j := j + 1) (by omega)]
      omega
    · intro he _ _
      refine ⟨hks, Or.inl ⟨rfl, by rw [hks.1, hks.2.2.1], ?_, fun i hi => ?_⟩⟩
      · show X.cpu.gpr.rdi + 48#64 = _
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
      · exact k52 Y t' hKY hAY hrY hks' h0 hall
      · exact k366 Y t' hKY hAY hrY hks' h0 hx
  | succ m ih =>
    intro j hj X t hK hA hrip hax hcx hks hpre
    refine (c_328 prof).run c hin
      (fun j' g' _ V' => Kq g₀ g' ∧
        ((j' = 328 ∧ V' = W ∧ g'.rax = BitVec.ofNat 64 (j + 1) ∧ g'.rcx = 7255952#64 ∧
           Eqb W g₀.rsi 7255952#64 j) ∨
         (j' = 366 ∧ V' = W ∧ g'.rax = 2147500034#64 ∧ ∃ i < 16, ¬ Eqb W g₀.rsi 7255952#64 i)))
      hK hA hrip (vc_328 ?_ ?_ ?_ ?_ ?_ ?_) ?_
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
      · exact k366 Y t' hKY hAY hrY hks' h0 hx

end FV7z.Aeq
