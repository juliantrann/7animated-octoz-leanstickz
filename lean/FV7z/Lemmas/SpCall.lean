import FV7z.Lemmas.Sp
/-!
# Calls inside code with branches (PLAN.md G3, startup)

`Sp` is of a piece of code wherever it runs. A function that calls another needs the callee's code too, so here the
run is fixed (`F`, `Wl`, `L`, `s₀`, `o`):

- `SpAt … e' j W`: `Sp`'s statement in that run (`Sp.at`), for the code at `e'`;
- `FnAt … e₂ jr T`: the function at `e₂`, entered with `T R` of the registers and the footprint's bytes, goes on to
  its `ret` (its `jr`-th byte) with `R` of what it leaves there (`fnAt_cfg`: from the function's `Sp`s, invariants
  and conditions, by `Seg.cfg`);
- `SpAt.call`: a `call rel32` of such a function, from the `call` to the instruction after it: the return address is
  pushed into bytes the run may store into, the callee runs, and its `ret` pops the return address, which the callee
  has left in place. The flags after the call are not followed;
- `cfgAt`: `Seg.cfg` with an `SpAt` at each cut point, so that a `call` may be one.
-/
namespace FV7z.Fn
open ZellicX86 Decode FV7z.Leaf

/-- `Sp`'s statement in one run. -/
structure SpAt (prof : Profile) (F : Footprint) (Wl : List Rgn) (L : List (Addr × List Byte)) (s₀ : State) (o : Oracle)
    (e' : Addr) (j : Nat) (W : Post → Gprs → Rflags → (Addr → Byte) → Prop) : Prop where
  run : ∀ {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
    {X : State} {t : Nat} {V : Addr → Byte} (Q : Post), KeptW Wl s₀ X → Agree F X.proc.mm.mem V →
    X.cpu.rip = e'.add j → W Q X.cpu.gpr X.cpu.rflags V →
    (∀ j' g fl V', Q j' g fl V' → ∀ Y t', KeptW Wl s₀ Y → Agree F Y.proc.mm.mem V' → Y.cpu.rip = e'.add j' →
      Y.cpu.gpr = g → Y.cpu.rflags = fl → GoG prof L o gev gP gE Y t') →
    GoG prof L o gev gP gE X t

/-- A function inside a run, from its entry to its `ret`. -/
structure FnAt (prof : Profile) (F : Footprint) (Wl : List Rgn) (L : List (Addr × List Byte)) (s₀ : State) (o : Oracle)
    (e₂ : Addr) (jr : Nat) (T : (Gprs → (Addr → Byte) → Prop) → Gprs → (Addr → Byte) → Prop) : Prop where
  run : ∀ {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
    {X : State} {t : Nat} {V : Addr → Byte} (R : Gprs → (Addr → Byte) → Prop), KeptW Wl s₀ X →
    Agree F X.proc.mm.mem V → X.cpu.rip = e₂ → T R X.cpu.gpr V →
    (∀ g V', R g V' → ∀ Y t', KeptW Wl s₀ Y → Agree F Y.proc.mm.mem V' → Y.cpu.rip = e₂.add jr → Y.cpu.gpr = g →
      GoG prof L o gev gP gE Y t') →
    GoG prof L o gev gP gE X t

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle} {F : Footprint} {Wl : List Rgn}
  {e' : Addr} {code : List Byte}

/-- An `Sp` in a run that has its code. -/
theorem _root_.FV7z.Sp.at {j : Nat} {W : Wpt} (h : Sp prof code e' j W) (c : Seg prof F Wl L s₀ o)
    (hin : CodeIn L e' code) : SpAt prof F Wl L s₀ o e' j (W F Wl) :=
  ⟨fun Q hK hA hrip hW k => h.run c hin Q hK hA hrip hW k⟩

/-- A stronger condition. -/
theorem SpAt.mono {j : Nat} {W W' : Post → Gprs → Rflags → (Addr → Byte) → Prop}
    (h : SpAt prof F Wl L s₀ o e' j W) (hw : ∀ Q g f V, W' Q g f V → W Q g f V) :
    SpAt prof F Wl L s₀ o e' j W' :=
  ⟨fun Q hK hA hrip hW k => h.run Q hK hA hrip (hw _ _ _ _ hW) k⟩

/-- A stronger condition at the entry. -/
theorem FnAt.mono {e₂ : Addr} {jr : Nat} {T T' : (Gprs → (Addr → Byte) → Prop) → Gprs → (Addr → Byte) → Prop}
    (h : FnAt prof F Wl L s₀ o e₂ jr T) (hw : ∀ R g V, T' R g V → T R g V) : FnAt prof F Wl L s₀ o e₂ jr T' :=
  ⟨fun R hK hA hrip hT k => h.run R hK hA hrip (hw _ _ _ hT) k⟩

/-- A function's run from its entry to its `ret` at `jr`: by its cut points, with `Inv 0 n₀` at the entry and `Fin`
at the `ret` alone. -/
theorem fnAt_cfg (c : Seg prof F Wl L s₀ o) {e₂ : Addr} {code₂ : List Byte} (hin : CodeIn L e₂ code₂) {W : Nat → Wpt}
    (hsp : ∀ ℓ, Sp prof code₂ e₂ ℓ (W ℓ)) (jr : Nat)
    {ι : Type} (Inv : ι → Nat → Nat → Gprs → (Addr → Byte) → Prop) (Fin : ι → Gprs → (Addr → Byte) → Prop)
    (ok : ι → Prop) (n₀ : ι → Nat)
    (vc : ∀ K, ok K → ∀ ℓ n g f V, Inv K ℓ n g V →
      W ℓ F Wl (fun j' g' _ V' => (∃ n', n' < n ∧ Inv K j' n' g' V') ∨ (j' = jr ∧ Fin K g' V')) g f V) :
    FnAt prof F Wl L s₀ o e₂ jr fun R g V =>
      ∃ K, ok K ∧ Inv K 0 (n₀ K) g V ∧ ∀ g' V', Fin K g' V' → R g' V' := by
  refine ⟨?_⟩
  rintro gev gP gE X t V R hK hA hrip ⟨K, hok, hI, hR⟩ k
  refine c.cfg hin hsp (fun ℓ n g _ V => Inv K ℓ n g V) (fun j' g' _ V' => j' = jr ∧ Fin K g' V')
    (fun ℓ n g f V h => vc K hok ℓ n g f V h) ?_ (n₀ K) 0 hK hA (by rw [addr_add_zero]; exact hrip) hI
  rintro j' g fl V' ⟨rfl, hF⟩ Y t' hKY hAY hrY rfl rfl
  exact k _ _ (hR _ _ hF) Y t' hKY hAY hrY rfl

/-- What a `call` at the `j`-th byte of the code at `e'` needs, of a function with `T`: the return address's slot is
the run's to store into; with the return address there, the function's condition `T`; and at its `ret`, the return
address still in bytes the run may read, and `Q` at the instruction after the `call`, whatever the flags. -/
def CallW (F : Footprint) (Wl : List Rgn) (e' : Addr) (j : Nat)
    (T : (Gprs → (Addr → Byte) → Prop) → Gprs → (Addr → Byte) → Prop) :
    Post → Gprs → Rflags → (Addr → Byte) → Prop :=
  fun Q g _ V =>
    (∀ i < 8, Foot Wl (Addr.add (g.rsp - 8) i)) ∧
    T (fun g' V' => (∀ i < 8, Foot F.data (Addr.add g'.rsp i)) ∧
        ofBytesLE 64 ((byteAddrs g'.rsp 8).map V') = e'.add j ∧
        ∀ fl, Q j (g'.set 4 (g'.rsp + 8)) fl V')
      (g.set 4 (g.rsp - 8)) (Vst V (g.rsp - 8) (toBytesLE (e'.add j) 8))

/-- `call rel32` of a function inside the run, to the instruction after the `call`. -/
theorem SpAt.call (c : Seg prof F Wl L s₀ o) (hin : CodeIn L e' code) {j rel len : Nat} (hj : j < code.length)
    (hd : Dec prof.feat code j (FV7z.mk .call 64 [.rel rel] len)) (hjl : j + len < code.length)
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) (h₂ : 0 < code₂.length)
    (htgt : e'.add (j + len) + BitVec.ofNat 64 rel = e₂)
    {jr : Nat} (hjr : jr < code₂.length) (hdr : Dec prof.feat code₂ jr (FV7z.mk .ret 64 [] 1))
    {T : (Gprs → (Addr → Byte) → Prop) → Gprs → (Addr → Byte) → Prop} (hT : FnAt prof F Wl L s₀ o e₂ jr T) :
    SpAt prof F Wl L s₀ o e' j (CallW F Wl e' (j + len) T) := by
  refine ⟨?_⟩
  rintro gev gP gE X t V Q hK hA hrip ⟨hst, hW⟩ k
  refine c.s_call hK hA hin hj hrip hd hin₂ h₂ htgt hst ?_
  rintro Y t₁ hKY hAY ⟨hrY, hgY⟩
  refine hT.run _ hKY hAY hrY (hgY ▸ hW) ?_
  rintro g V' ⟨hl, hra, hQ⟩ Z t₂ hKZ hAZ hrZ rfl
  refine c.s_ret hKZ hAZ hin₂ hjr hrZ hdr hl hin hjl hra ?_
  rintro U t₃ hKU hAU ⟨hrU, hgU⟩
  exact k _ _ _ _ (hQ U.cpu.rflags) U t₃ hKU hAU hrU hgU rfl

variable {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}

/-- `Seg.cfg` with the cut points' pieces in the run. -/
theorem cfgAt {W : Nat → Post → Gprs → Rflags → (Addr → Byte) → Prop}
    (hsp : ∀ ℓ, SpAt prof F Wl L s₀ o e' ℓ (W ℓ)) (Inv : Nat → Nat → Gprs → Rflags → (Addr → Byte) → Prop)
    (Fin : Post)
    (vc : ∀ ℓ n g f V, Inv ℓ n g f V →
      W ℓ (fun j' g' f' V' => (∃ n' < n, Inv j' n' g' f' V') ∨ Fin j' g' f' V') g f V)
    (hfin : ∀ j' g fl V', Fin j' g fl V' → ∀ Y t', KeptW Wl s₀ Y → Agree F Y.proc.mm.mem V' →
      Y.cpu.rip = e'.add j' → Y.cpu.gpr = g → Y.cpu.rflags = fl → GoG prof L o gev gP gE Y t') :
    ∀ (n ℓ : Nat) {X : State} {t : Nat} {V : Addr → Byte}, KeptW Wl s₀ X → Agree F X.proc.mm.mem V →
      X.cpu.rip = e'.add ℓ → Inv ℓ n X.cpu.gpr X.cpu.rflags V → GoG prof L o gev gP gE X t := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro ℓ X t V hK hA hrip hI
    refine (hsp ℓ).run _ hK hA hrip (vc ℓ n _ _ _ hI) ?_
    rintro j' g fl V' (⟨n', hn, hI'⟩ | hF) Y t' hKY hAY hrY hg hf
    · exact ih n' hn j' hKY hAY hrY (hg ▸ hf ▸ hI')
    · exact hfin _ _ _ _ hF Y t' hKY hAY hrY hg hf

end FV7z.Fn
