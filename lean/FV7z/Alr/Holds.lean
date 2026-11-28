import FV7z.Alr.Pieces
/-!
# `CArchiveLink::Release` (PLAN.md §M, M1): the runs through the callees, part 1

The pieces of `FV7z/Alr/Pieces.lean` joined into runs. `S` the stack pointer and `g0` the registers at the entry,
`A` = `g0.rdi` (`this`, kept in `r13`); the five pushes as in `FV7z/Lemmas/Fr40.lean` (`aR S` = `S - 40`).

The callees are continuations (`KC`, as in `FV7z/Spp/Holds.lean`), each with the bytes it returns with: from its
return the run goes on with `rsp` as it was and the callee-saved registers (`KS`) as at the `call`. The bytes are
tracked by invariants the caller chooses, indexed by the step: with `k + 1` arcs left, `I (k + 1)` at the loop's head
(64, `rax` = `k + 1`); the arc `p` = `pA W A k` (the 8 bytes at `ea W A k` = `_items + 8 (k + 1) - 8`); null gives
`D k` (`hP0`), else `J k p` (`hJ`), kept by every callee of `~CArc ()` (`kD`, `kR`, `kB`) and given up for `D k` by
`operator delete (p, 0x110)` (`kE`). `D k` gives the size `k + 1` at `A + 8` (`hsz`) and, after the size's store,
`I k` (`hdec`); `I 0` gives the stack (`hI`, `StkF`). The arc's fields are readable (`FA`, `hfa`); its interfaces
(`p + 0x18`, `0x10`, `8`) and its `CMyComPtr` (`p`) not null are objects whose vtable's `Release` (the word at 16)
is code (`Com`; `h24`, `h16`, `h8`, `hB`).

- `Fm`, `Fa`: the frame (with the arc `p` in `rbp`); `KC`, `AtJ`, `Ev`: the callees, the runs from an offset, the
  hypotheses of the runs; `callK`, `callMK`, `callRK`: a direct `call`, `call [rax + 0x10]`, `call rax`.
- `tail493`: the pops and the `ret`, to `kr`; `S476`: the size one less, to the epilogue or the head with `I k`;
  `B64`: the head; `R99`, …, `R222`: the arc's fields; `R237`: its `CMyComPtr` (the `Release` in line to 270, the
  continuation `h270`; else `call rax` (515) and `jmp` 463); `R463`: `operator delete (p, 0x110)`, to 476.

Left for part 2: the `Release` in line (270–463: `Seg.s_sub_mi32`, `~CHandler ()`, the items' loop by `Ocv.rbx0`
as `Spp`'s clear), the loop by induction on `k`, the start (0–64: `ClearErrors`, `Z1`) and `alr_ok`.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Alr
set_option linter.unusedVariables false

open FV7z.Fr40 (KS StkF FtsF r5)

/-! ## The frame -/

/-- The stack pointer after the five pushes. -/
abbrev aR (S : Addr) : Addr := S - 8 - 8 - 8 - 8 - 8

/-- The frame: `rsp` = `aR S`, `r13` = `this`, `r15` as at the entry. -/
abbrev Fm (S : Addr) (g0 g : Gprs) : Prop := g.rsp = aR S ∧ g.r13 = g0.rdi ∧ g.r15 = g0.r15

/-- The frame of the arc `p`: `Fm`, `rbp` = `p`. -/
abbrev Fa (S : Addr) (g0 : Gprs) (p : Addr) (g : Gprs) : Prop :=
  g.rsp = aR S ∧ g.r13 = g0.rdi ∧ g.r15 = g0.r15 ∧ g.rbp = p

theorem Fm.fr {S : Addr} {g0 g g' : Gprs} (h : Fm S g0 g) (h' : Fr g g') : Fm S g0 g' :=
  ⟨h'.1.trans h.1, h'.2.2.2.2.1.trans h.2.1, h'.2.2.2.2.2.2.trans h.2.2⟩

theorem fm_ret {S : Addr} {g0 g g' : Gprs} (h : Fm S g0 g) (hs : g'.rsp = aR S) (hk : KS g g') : Fm S g0 g' :=
  ⟨hs, hk.2.2.2.1.trans h.2.1, hk.2.2.2.2.2.trans h.2.2⟩

theorem Fa.fr {S : Addr} {g0 : Gprs} {p : Addr} {g g' : Gprs} (h : Fa S g0 p g) (h' : Fr g g') : Fa S g0 p g' :=
  ⟨h'.1.trans h.1, h'.2.2.2.2.1.trans h.2.1, h'.2.2.2.2.2.2.trans h.2.2.1, h'.2.2.1.trans h.2.2.2⟩

theorem fa_ret {S : Addr} {g0 : Gprs} {p : Addr} {g g' : Gprs} (h : Fa S g0 p g) (hs : g'.rsp = aR S)
    (hk : KS g g') : Fa S g0 p g' :=
  ⟨hs, hk.2.2.2.1.trans h.2.1, hk.2.2.2.2.2.trans h.2.2.1, hk.2.1.trans h.2.2.2⟩

/-- The slot of the arc at the step `k` (`k + 1` arcs, `a` = `this`): `_items + 8 (k + 1) - 8`. -/
abbrev ea (W : Addr → Byte) (a : Addr) (k : Nat) : Addr :=
  rdq(W, a) + BitVec.setWidth 64 (BitVec.ofNat 32 (k + 1)) * 8#64 + 18446744073709551608#64

/-- The arc at the step `k`. -/
abbrev pA (W : Addr → Byte) (a : Addr) (k : Nat) : Addr := rdq(W, ea W a k)

/-- The arc's fields read: the chars at `0xf8`, `0xe8`, `0xc0`, `0xb0`, `0x48`, `0x38`, `0x28`, the interfaces at
`0x18`, `0x10`, `8`, the `CMyComPtr` at 0. -/
structure FA (F : Footprint) (p : Addr) : Prop where
  f0 : ∀ i < 8, Foot F.data (Addr.add p i)
  f8 : ∀ i < 8, Foot F.data (Addr.add (p + 8#64) i)
  f16 : ∀ i < 8, Foot F.data (Addr.add (p + 16#64) i)
  f24 : ∀ i < 8, Foot F.data (Addr.add (p + 24#64) i)
  f40 : ∀ i < 8, Foot F.data (Addr.add (p + 40#64) i)
  f56 : ∀ i < 8, Foot F.data (Addr.add (p + 56#64) i)
  f72 : ∀ i < 8, Foot F.data (Addr.add (p + 72#64) i)
  f176 : ∀ i < 8, Foot F.data (Addr.add (p + 176#64) i)
  f192 : ∀ i < 8, Foot F.data (Addr.add (p + 192#64) i)
  f232 : ∀ i < 8, Foot F.data (Addr.add (p + 232#64) i)
  f248 : ∀ i < 8, Foot F.data (Addr.add (p + 248#64) i)

/-- An object `v` (the bytes `W`): its vtable pointer and the vtable's word at 16 readable, that word code. -/
abbrev Com (F : Footprint) (L : List (Addr × List Byte)) (W : Addr → Byte) (v : Addr) : Prop :=
  (∀ i < 8, Foot F.data (Addr.add v i)) ∧ (∀ i < 8, Foot F.data (Addr.add (rdq(W, v) + 16#64) i)) ∧
    ∃ code : List Byte, CodeIn L (rdq(W, rdq(W, v) + 16#64)) code ∧ 0 < code.length

theorem ne1 (k : Nat) (hk : k + 1 + 1 < 4294967296) : BitVec.ofNat 32 (k + 1 + 1) ≠ 1#32 := by
  intro h
  have h' := congrArg BitVec.toNat h
  simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod] at h'
  omega

theorem sub1 (k : Nat) (hk : k + 1 + 1 < 4294967296) :
    BitVec.ofNat 32 (k + 1 + 1) - 1#32 = BitVec.ofNat 32 (k + 1) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
  omega

/-! ## The callees and the hypotheses of the runs -/

/-- A callee from the `call` before `j` (entry `ent`, the bytes `W`, the registers `A`): at its entry, and from its
return at `j` with `rsp` = `aR S`, the callee-saved registers as at its entry and bytes with `N`, the run goes on to
the goal. -/
def KC (prof : Profile) (F : Footprint) (Wl : List Rgn) (L : List (Addr × List Byte)) (s₀ : State) (o : Oracle)
    (gev : List Event) (gP : State → Nat → List Event → Prop) (gE : Outcome → List Event → Prop)
    (S ent : Addr) (j : Nat) (W : Addr → Byte) (A : Gprs → Prop) (N : (Addr → Byte) → Prop) : Prop :=
  ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y →
    Agree F Y.proc.mm.mem (Vst W (aR S - 8) (toBytesLE (alr_at.add j) 8)) →
    Y.cpu.rip = ent → Y.cpu.gpr.rsp = aR S - 8 → A Y.cpu.gpr →
    (∀ (Z : State) (W' : Addr → Byte) (t'' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem W' →
      Z.cpu.rip = alr_at.add j → Z.cpu.gpr.rsp = aR S → KS Y.cpu.gpr Z.cpu.gpr → N W' →
      GoG prof L o gev gP gE Z t'') →
    GoG prof L o gev gP gE Y t'

/-- From offset `j` with registers and bytes for which `P` holds, the run goes on to the goal. -/
def AtJ (prof : Profile) (F : Footprint) (Wl : List Rgn) (L : List (Addr × List Byte)) (s₀ : State) (o : Oracle)
    (gev : List Event) (gP : State → Nat → List Event → Prop) (gE : Outcome → List Event → Prop) (j : Nat)
    (P : Gprs → (Addr → Byte) → Prop) : Prop :=
  ∀ (Y : State) (W : Addr → Byte) (t : Nat), KeptW Wl s₀ Y → Agree F Y.proc.mm.mem W →
    Y.cpu.rip = alr_at.add j → P Y.cpu.gpr W → GoG prof L o gev gP gE Y t

/-- In `~CArc ()` of the arc `p` at the step `k`: `J k p`, the frame `Fa`. -/
abbrev PA (S : Addr) (g0 : Gprs) (J : Nat → Addr → (Addr → Byte) → Prop) (k : Nat) (p : Addr) :
    Gprs → (Addr → Byte) → Prop := fun g W => J k p W ∧ Fa S g0 p g

/-- The hypotheses of the runs (`S`, `g0` the entry's stack pointer and registers, `e₂.add j₂` the return address,
`I`, `D`, `J` the invariants of the bytes). -/
structure Ev (prof : Profile) (F : Footprint) (Wl : List Rgn) (L : List (Addr × List Byte)) (s₀ : State)
    (o : Oracle) (gev : List Event) (gP : State → Nat → List Event → Prop) (gE : Outcome → List Event → Prop)
    (S : Addr) (g0 : Gprs) (e₂ : Addr) (code₂ : List Byte) (j₂ : Nat) (I D : Nat → (Addr → Byte) → Prop)
    (J : Nat → Addr → (Addr → Byte) → Prop) : Prop where
  c : Seg prof F Wl L s₀ o
  hin : CodeIn L alr_at alr
  hin₂ : CodeIn L e₂ code₂
  h₂ : j₂ < code₂.length
  ft : FtsF F S
  hr8 : ∀ i < 8, Foot Wl (Addr.add (aR S - 8) i)
  hI : ∀ W, I 0 W → StkF W S g0 (e₂.add j₂)
  fA : ∀ i < 8, Foot F.data (Addr.add g0.rdi i)
  f8 : ∀ i < 4, Foot F.data (Addr.add (g0.rdi + 8#64) i)
  w8 : ∀ i < 4, Foot Wl (Addr.add (g0.rdi + 8#64) i)
  fe : ∀ k W, I (k + 1) W → ∀ i < 8, Foot F.data (Addr.add (ea W g0.rdi k) i)
  hP0 : ∀ k W, I (k + 1) W → pA W g0.rdi k = 0 → D k W
  hJ : ∀ k W, I (k + 1) W → pA W g0.rdi k ≠ 0 → J k (pA W g0.rdi k) W
  hsz : ∀ k W, D k W → rdd(W, g0.rdi + 8#64) = BitVec.ofNat 32 (k + 1)
  hdec : ∀ k W, D k W → I k (Vst W (g0.rdi + 8#64) (toBytesLE (BitVec.ofNat 32 (k + 1) - 1#32) 4))
  hfa : ∀ k p W, J k p W → FA F p
  h24 : ∀ k p W, J k p W → ¬rdq(W, p + 24#64) = 0 → Com F L W (rdq(W, p + 24#64))
  h16 : ∀ k p W, J k p W → ¬rdq(W, p + 16#64) = 0 → Com F L W (rdq(W, p + 16#64))
  h8 : ∀ k p W, J k p W → ¬rdq(W, p + 8#64) = 0 → Com F L W (rdq(W, p + 8#64))
  hB : ∀ k p W, J k p W → ¬rdq(W, p) = 0 → Com F L W (rdq(W, p))
  cD : ∃ code : List Byte, CodeIn L 0x6014f0#64 code ∧ 0 < code.length
  cE : ∃ code : List Byte, CodeIn L 0x6014e0#64 code ∧ 0 < code.length
  kD : ∀ k p W j, J k p W → KC prof F Wl L s₀ o gev gP gE S 0x6014f0#64 j W (fun _ => True) (J k p)
  kR : ∀ k p W v j, J k p W → Com F L W v →
    KC prof F Wl L s₀ o gev gP gE S (rdq(W, rdq(W, v) + 16#64)) j W (fun g => g.rdi = v) (J k p)
  kB : ∀ k p W j, J k p W → ¬rdq(W, p) = 0 →
    KC prof F Wl L s₀ o gev gP gE S (rdq(W, rdq(W, rdq(W, p)) + 16#64)) j W (fun g => g.rdi = rdq(W, p)) (J k p)
  kE : ∀ k p W, J k p W →
    KC prof F Wl L s₀ o gev gP gE S 0x6014e0#64 476 W (fun g => g.rdi = p ∧ g.rsi = 272#64) (D k)
  kr : ∀ (W : Addr → Byte) (Z' : State) (t' : Nat), KeptW Wl s₀ Z' → Agree F Z'.proc.mm.mem W →
    Z'.cpu.rip = e₂.add j₂ → Z'.cpu.gpr.rsp = S + 8 → KS g0 Z'.cpu.gpr → I 0 W → GoG prof L o gev gP gE Z' t'

/-! ## The runs -/

section Runs

variable {prof : Profile} {F : Footprint} {Wl : List Rgn} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {S : Addr} {g0 : Gprs} {e₂ : Addr} {code₂ : List Byte} {j₂ : Nat} {I D : Nat → (Addr → Byte) → Prop}
  {J : Nat → Addr → (Addr → Byte) → Prop} {Y : State} {t : Nat} {W : Addr → Byte}

/-- A `call` at `j` (`rsp` = `aR S`, the bytes `W`) of the callee `k`, and from its return at `j + 5`. -/
theorem callK (E : Ev prof F Wl L s₀ o gev gP gE S g0 e₂ code₂ j₂ I D J) {U : State} {t₁ : Nat}
    {j R : Nat} {ent : Addr} {A : Gprs → Prop} {N : (Addr → Byte) → Prop} (hKU : KeptW Wl s₀ U)
    (hAU : Agree F U.proc.mm.mem W) (hrU : U.cpu.rip = alr_at.add j) (hs : U.cpu.gpr.rsp = aR S)
    (hj : j < alr.length) (hd : Dec prof.feat alr j (FV7z.mk .call 64 [.rel R] 5))
    (htgt : alr_at.add (j + 5) + BitVec.ofNat 64 R = ent)
    (hc : ∃ code : List Byte, CodeIn L ent code ∧ 0 < code.length)
    (k : KC prof F Wl L s₀ o gev gP gE S ent (j + 5) W A N) (hA : A (U.cpu.gpr.set 4 (aR S - 8)))
    (h : ∀ (Z : State) (W' : Addr → Byte) (t'' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem W' →
      Z.cpu.rip = alr_at.add (j + 5) → Z.cpu.gpr.rsp = aR S → KS U.cpu.gpr Z.cpu.gpr → N W' →
      GoG prof L o gev gP gE Z t'') :
    GoG prof L o gev gP gE U t₁ := by
  have hU : U.cpu.gpr.rsp - 8 = aR S - 8 := by rw [hs]
  obtain ⟨cc, hinc, hcc⟩ := hc
  refine E.c.s_call hKU hAU E.hin hj hrU hd hinc hcc htgt (by rw [hU]; exact E.hr8) ?_
  rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
  rw [hU] at hA₂
  refine k Y₂ t₂ hK₂ hA₂ hr₂ (by rw [hg₂]; exact hU) (by rw [hg₂, hU]; exact hA) ?_
  intro Z W' t₃ hKZ hAZ hrZ hsZ hkZ hNZ
  rw [hg₂] at hkZ
  exact h Z W' t₃ hKZ hAZ hrZ hsZ hkZ hNZ

/-- `call [rax + 0x10]` at `j` (`rax` = the vtable of the object `v`), and from its return at `j + 3`. -/
theorem callMK (E : Ev prof F Wl L s₀ o gev gP gE S g0 e₂ code₂ j₂ I D J) {U : State} {t₁ : Nat}
    {j : Nat} {v : Addr} {A : Gprs → Prop} {N : (Addr → Byte) → Prop} (hKU : KeptW Wl s₀ U)
    (hAU : Agree F U.proc.mm.mem W) (hrU : U.cpu.rip = alr_at.add j) (hs : U.cpu.gpr.rsp = aR S)
    (hj : j < alr.length) (hd : Dec prof.feat alr j (FV7z.mk .call 64 [.mem (mbd 0 16 64)] 3))
    (hrax : U.cpu.gpr.rax = rdq(W, v)) (hcm : Com F L W v)
    (k : KC prof F Wl L s₀ o gev gP gE S (rdq(W, rdq(W, v) + 16#64)) (j + 3) W A N)
    (hA : A (U.cpu.gpr.set 4 (aR S - 8)))
    (h : ∀ (Z : State) (W' : Addr → Byte) (t'' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem W' →
      Z.cpu.rip = alr_at.add (j + 3) → Z.cpu.gpr.rsp = aR S → KS U.cpu.gpr Z.cpu.gpr → N W' →
      GoG prof L o gev gP gE Z t'') :
    GoG prof L o gev gP gE U t₁ := by
  have hU : U.cpu.gpr.rsp - 8 = aR S - 8 := by rw [hs]
  have he : eaD U 0 16 = rdq(W, v) + 16#64 := by
    show U.cpu.gpr.get (regOf 0) + BitVec.ofNat 64 16 = _
    rw [show U.cpu.gpr.get (regOf 0) = U.cpu.gpr.rax from rfl, hrax]
  obtain ⟨-, hft, cg, hinG, hcg⟩ := hcm
  refine E.c.s_callM hKU hAU E.hin hj hrU hd (by rw [he]; exact hft) hinG hcg (by rw [he])
    (by rw [hU]; exact E.hr8) ?_
  rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
  rw [hU] at hA₂
  refine k Y₂ t₂ hK₂ hA₂ hr₂ (by rw [hg₂]; exact hU) (by rw [hg₂, hU]; exact hA) ?_
  intro Z W' t₃ hKZ hAZ hrZ hsZ hkZ hNZ
  rw [hg₂] at hkZ
  exact h Z W' t₃ hKZ hAZ hrZ hsZ hkZ hNZ

/-- `call rax` at `j` (`rax` = `ent`), and from its return at `j + 2`. -/
theorem callRK (E : Ev prof F Wl L s₀ o gev gP gE S g0 e₂ code₂ j₂ I D J) {U : State} {t₁ : Nat}
    {j : Nat} {ent : Addr} {A : Gprs → Prop} {N : (Addr → Byte) → Prop} (hKU : KeptW Wl s₀ U)
    (hAU : Agree F U.proc.mm.mem W) (hrU : U.cpu.rip = alr_at.add j) (hs : U.cpu.gpr.rsp = aR S)
    (hj : j < alr.length) (hd : Dec prof.feat alr j (FV7z.mk .call 64 [gr 64 0] 2))
    (hrax : U.cpu.gpr.rax = ent) (hc : ∃ code : List Byte, CodeIn L ent code ∧ 0 < code.length)
    (k : KC prof F Wl L s₀ o gev gP gE S ent (j + 2) W A N) (hA : A (U.cpu.gpr.set 4 (aR S - 8)))
    (h : ∀ (Z : State) (W' : Addr → Byte) (t'' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem W' →
      Z.cpu.rip = alr_at.add (j + 2) → Z.cpu.gpr.rsp = aR S → KS U.cpu.gpr Z.cpu.gpr → N W' →
      GoG prof L o gev gP gE Z t'') :
    GoG prof L o gev gP gE U t₁ := by
  have hU : U.cpu.gpr.rsp - 8 = aR S - 8 := by rw [hs]
  obtain ⟨cc, hinc, hcc⟩ := hc
  refine E.c.s_callr hKU hAU E.hin hj hrU hd hinc hcc hrax (by rw [hU]; exact E.hr8) ?_
  rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
  rw [hU] at hA₂
  refine k Y₂ t₂ hK₂ hA₂ hr₂ (by rw [hg₂]; exact hU) (by rw [hg₂, hU]; exact hA) ?_
  intro Z W' t₃ hKZ hAZ hrZ hsZ hkZ hNZ
  rw [hg₂] at hkZ
  exact h Z W' t₃ hKZ hAZ hrZ hsZ hkZ hNZ

/-! ### The tail and the size -/

/-- From 493 (the frame, the bytes `W` with `I 0`): the pops, the `ret`, to `kr`. -/
theorem tail493 (E : Ev prof F Wl L s₀ o gev gP gE S g0 e₂ code₂ j₂ I D J) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = alr_at.add 493) (hm : Fm S g0 Y.cpu.gpr) (hIW : I 0 W) :
    GoG prof L o gev gP gE Y t := by
  obtain ⟨s1, s2, s3, s4, s5, s6⟩ := E.hI W hIW
  obtain ⟨f1, f2, f3, f4, f5, f6⟩ := E.ft
  have hs := hm.1
  refine (c_493 prof).run E.c E.hin (fun j' g' _ V' => j' = 501 ∧ V' = W ∧
      g'.rsp = Y.cpu.gpr.rsp + 8 + 8 + 8 + 8 + 8 ∧ g'.rbx = rdq(W, Y.cpu.gpr.rsp) ∧
      g'.rbp = rdq(W, Y.cpu.gpr.rsp + 8) ∧ g'.r12 = rdq(W, Y.cpu.gpr.rsp + 8 + 8) ∧
      g'.r13 = rdq(W, Y.cpu.gpr.rsp + 8 + 8 + 8) ∧ g'.r14 = rdq(W, Y.cpu.gpr.rsp + 8 + 8 + 8 + 8) ∧
      g'.r15 = Y.cpu.gpr.r15) hK hA hr
    (vc_493 (by rw [hs]; exact f1) (by rw [hs]; exact f2) (by rw [hs]; exact f3) (by rw [hs]; exact f4)
      (by rw [hs]; exact f5) fun _ a b d e f g h _ => ⟨rfl, rfl, a, b, d, e, f, g, h⟩) ?_
  rintro j' g fl V₁ ⟨rfl, hV₁, gs, gx, gp, g12, g13, g14, g15⟩ U t₁ hKU hAU hrU hgU -
  subst V₁ hgU
  have hsU : U.cpu.gpr.rsp = S := by rw [gs, hs]; exact r5 S
  have e1 : rdq(W, Y.cpu.gpr.rsp) = g0.rbx := by rw [hs]; exact s1
  have e2 : rdq(W, Y.cpu.gpr.rsp + 8) = g0.rbp := by rw [hs]; exact s2
  have e3 : rdq(W, Y.cpu.gpr.rsp + 8 + 8) = g0.r12 := by rw [hs]; exact s3
  have e4 : rdq(W, Y.cpu.gpr.rsp + 8 + 8 + 8) = g0.r13 := by rw [hs]; exact s4
  have e5 : rdq(W, Y.cpu.gpr.rsp + 8 + 8 + 8 + 8) = g0.r14 := by rw [hs]; exact s5
  refine E.c.s_ret hKU hAU E.hin (lt_len (by decide)) hrU (ret_501 _) (by rw [hsU]; exact f6) E.hin₂ E.h₂
    (by rw [hsU]; exact s6) ?_
  rintro Z' t₂ hKZ' hAZ' ⟨hrZ', hgZ'⟩
  refine E.kr W Z' t₂ hKZ' hAZ' hrZ' ?_ ?_ hIW
  · rw [hgZ']
    show U.cpu.gpr.rsp + 8 = _
    rw [hsU]
  · rw [hgZ']
    exact ⟨gx.trans e1, gp.trans e2, g12.trans e3, g13.trans e4, g14.trans e5, g15.trans hm.2.2⟩

/-- 476 at the step `k` (`D k`): the size one less, stored; after the step 0 to the epilogue with `I 0`, else to 64
with `I (k' + 1)`, `k = k' + 1` (`hnx`). -/
theorem S476 (E : Ev prof F Wl L s₀ o gev gP gE S g0 e₂ code₂ j₂ I D J) (k : Nat) (hk : k + 1 < 4294967296)
    (hnx : ∀ k', k = k' + 1 → AtJ prof F Wl L s₀ o gev gP gE 64 fun g W => I (k' + 1) W ∧ Fm S g0 g ∧
      g.rax = BitVec.setWidth 64 (BitVec.ofNat 32 (k' + 1))) :
    AtJ prof F Wl L s₀ o gev gP gE 476 fun g W => D k W ∧ Fm S g0 g := by
  rintro Y W t hK hA hr ⟨hD, hm⟩
  have hc := E.hsz k W hD
  cases k with
  | zero =>
    refine (c_476 prof).run E.c E.hin (fun j' g' _ V' => j' = 493 ∧
        V' = Vst W (g0.rdi + 8#64) (toBytesLE (BitVec.ofNat 32 (0 + 1) - 1#32) 4) ∧ Fr Y.cpu.gpr g') hK hA hr
      (vc_476 (c := BitVec.ofNat 32 (0 + 1)) (by rw [hm.2.1]; exact E.f8) (by rw [hm.2.1]; exact E.w8)
        (by rw [hm.2.1]; exact hc) (fun _ _ a _ => ⟨rfl, by rw [hm.2.1], a⟩) (fun hne => (hne rfl).elim)) ?_
    rintro j' g fl V₁ ⟨rfl, hV₁, gf⟩ U t₁ hKU hAU hrU hgU -
    subst V₁ hgU
    exact tail493 E hKU hAU hrU (Fm.fr hm gf) (E.hdec 0 W hD)
  | succ k =>
    refine (c_476 prof).run E.c E.hin (fun j' g' _ V' => j' = 64 ∧
        V' = Vst W (g0.rdi + 8#64) (toBytesLE (BitVec.ofNat 32 (k + 1 + 1) - 1#32) 4) ∧ Fr Y.cpu.gpr g' ∧
        g'.rax = BitVec.setWidth 64 (BitVec.ofNat 32 (k + 1 + 1) - 1#32)) hK hA hr
      (vc_476 (c := BitVec.ofNat 32 (k + 1 + 1)) (by rw [hm.2.1]; exact E.f8) (by rw [hm.2.1]; exact E.w8)
        (by rw [hm.2.1]; exact hc) (fun he => absurd he (ne1 k hk))
        (fun _ _ a b _ => ⟨rfl, by rw [hm.2.1], a, b⟩)) ?_
    rintro j' g fl V₁ ⟨rfl, hV₁, gf, gax⟩ U t₁ hKU hAU hrU hgU -
    subst V₁ hgU
    exact hnx k rfl U _ t₁ hKU hAU hrU ⟨E.hdec (k + 1) W hD, Fm.fr hm gf, by rw [gax, sub1 k hk]⟩

/-! ### The loop's head and the arc -/

/-- 64 at the step `k` (`I (k + 1)`, `rax` = `k + 1`): the arc `p`; null to 476 (`D k`), else its chars at `0xf8`
freed unless null (94, `kD`) and to 99 (`J k p`). -/
theorem B64 (E : Ev prof F Wl L s₀ o gev gP gE S g0 e₂ code₂ j₂ I D J) (k : Nat)
    (h476 : AtJ prof F Wl L s₀ o gev gP gE 476 fun g W => D k W ∧ Fm S g0 g)
    (h99 : ∀ p, AtJ prof F Wl L s₀ o gev gP gE 99 (PA S g0 J k p)) :
    AtJ prof F Wl L s₀ o gev gP gE 64 fun g W => I (k + 1) W ∧ Fm S g0 g ∧
      g.rax = BitVec.setWidth 64 (BitVec.ofNat 32 (k + 1)) := by
  rintro Y W t hK hA hr ⟨hI, hm, hax⟩
  refine (c_64 prof).run E.c E.hin (fun j' g' _ V' => V' = W ∧ Fp Y.cpu.gpr g' ∧ g'.rbp = pA W g0.rdi k ∧
      ((j' = 476 ∧ pA W g0.rdi k = 0) ∨ (j' = 99 ∧ pA W g0.rdi k ≠ 0) ∨ (j' = 94 ∧ pA W g0.rdi k ≠ 0))) hK hA hr
    (vc_64 (it := rdq(W, g0.rdi)) (p := pA W g0.rdi k) (q := rdq(W, pA W g0.rdi k + 248#64)) (by rw [hm.2.1])
      (by rw [hm.2.1]; exact E.fA) (by rw [hax]) (by rw [hax]; exact E.fe k W hI) rfl
      (fun h0 => (E.hfa k _ W (E.hJ k W hI h0)).f248)
      (fun h0 _ a b _ => ⟨rfl, a, b, Or.inl ⟨rfl, h0⟩⟩)
      (fun h0 _ _ a b _ => ⟨rfl, a, b, Or.inr (Or.inl ⟨rfl, h0⟩)⟩)
      (fun h0 _ _ a b _ _ => ⟨rfl, a, b, Or.inr (Or.inr ⟨rfl, h0⟩)⟩)) ?_
  rintro j' g fl V₁ ⟨hV₁, gf, gbp, hj⟩ U t₁ hKU hAU hrU hgU -
  subst V₁ hgU
  have hmU : Fm S g0 U.cpu.gpr := ⟨gf.1.trans hm.1, gf.2.2.2.1.trans hm.2.1, gf.2.2.2.2.2.trans hm.2.2⟩
  have haU : Fa S g0 (pA W g0.rdi k) U.cpu.gpr := ⟨hmU.1, hmU.2.1, hmU.2.2, gbp⟩
  rcases hj with ⟨rfl, h0⟩ | ⟨rfl, h0⟩ | ⟨rfl, h0⟩
  · exact h476 U W t₁ hKU hAU hrU ⟨E.hP0 k W hI h0, hmU⟩
  · exact h99 _ U W t₁ hKU hAU hrU ⟨E.hJ k W hI h0, haU⟩
  · refine callK E hKU hAU hrU hmU.1 (lt_len (by decide)) (call_94 _) tgt_94 E.cD (E.kD k _ W _ (E.hJ k W hI h0))
      trivial ?_
    intro Z W' t₃ hKZ hAZ hrZ hsZ hkZ hJZ
    exact h99 _ Z W' t₃ hKZ hAZ hrZ ⟨hJZ, fa_ret haU hsZ hkZ⟩


/-- 99: the chars at `0xe8` freed unless null (111, `kD`), to 116. -/
theorem R99 (E : Ev prof F Wl L s₀ o gev gP gE S g0 e₂ code₂ j₂ I D J) (k : Nat) (p : Addr)
    (hn : AtJ prof F Wl L s₀ o gev gP gE 116 (PA S g0 J k p)) : AtJ prof F Wl L s₀ o gev gP gE 99 (PA S g0 J k p) := by
  rintro Y W t hK hA hr ⟨hJ, hm⟩
  refine (c_99 prof).run E.c E.hin (fun j' g' _ V' => V' = W ∧ Fr Y.cpu.gpr g' ∧ (j' = 116 ∨ j' = 111)) hK hA hr
    (vc_99 (by rw [hm.2.2.2]; exact (E.hfa k p W hJ).f232) (fun _ _ a _ => ⟨rfl, a, Or.inl rfl⟩)
      (fun _ _ a _ _ => ⟨rfl, a, Or.inr rfl⟩)) ?_
  rintro j' g fl V₁ ⟨hV₁, gf, hj⟩ U t₁ hKU hAU hrU hgU -
  subst V₁ hgU
  have hmU := Fa.fr hm gf
  rcases hj with rfl | rfl
  · exact hn U W t₁ hKU hAU hrU ⟨hJ, hmU⟩
  · refine callK E hKU hAU hrU hmU.1 (lt_len (by decide)) (call_111 _) tgt_111 E.cD (E.kD k p W _ hJ) trivial ?_
    intro Z W' t₃ hKZ hAZ hrZ hsZ hkZ hJZ
    exact hn Z W' t₃ hKZ hAZ hrZ ⟨hJZ, fa_ret hmU hsZ hkZ⟩

/-- 116: the chars at `0xc0` freed unless null (128, `kD`), to 133. -/
theorem R116 (E : Ev prof F Wl L s₀ o gev gP gE S g0 e₂ code₂ j₂ I D J) (k : Nat) (p : Addr)
    (hn : AtJ prof F Wl L s₀ o gev gP gE 133 (PA S g0 J k p)) : AtJ prof F Wl L s₀ o gev gP gE 116 (PA S g0 J k p) := by
  rintro Y W t hK hA hr ⟨hJ, hm⟩
  refine (c_116 prof).run E.c E.hin (fun j' g' _ V' => V' = W ∧ Fr Y.cpu.gpr g' ∧ (j' = 133 ∨ j' = 128)) hK hA hr
    (vc_116 (by rw [hm.2.2.2]; exact (E.hfa k p W hJ).f192) (fun _ _ a _ => ⟨rfl, a, Or.inl rfl⟩)
      (fun _ _ a _ _ => ⟨rfl, a, Or.inr rfl⟩)) ?_
  rintro j' g fl V₁ ⟨hV₁, gf, hj⟩ U t₁ hKU hAU hrU hgU -
  subst V₁ hgU
  have hmU := Fa.fr hm gf
  rcases hj with rfl | rfl
  · exact hn U W t₁ hKU hAU hrU ⟨hJ, hmU⟩
  · refine callK E hKU hAU hrU hmU.1 (lt_len (by decide)) (call_128 _) tgt_128 E.cD (E.kD k p W _ hJ) trivial ?_
    intro Z W' t₃ hKZ hAZ hrZ hsZ hkZ hJZ
    exact hn Z W' t₃ hKZ hAZ hrZ ⟨hJZ, fa_ret hmU hsZ hkZ⟩

/-- 133: the chars at `0xb0` freed unless null (145, `kD`), to 150. -/
theorem R133 (E : Ev prof F Wl L s₀ o gev gP gE S g0 e₂ code₂ j₂ I D J) (k : Nat) (p : Addr)
    (hn : AtJ prof F Wl L s₀ o gev gP gE 150 (PA S g0 J k p)) : AtJ prof F Wl L s₀ o gev gP gE 133 (PA S g0 J k p) := by
  rintro Y W t hK hA hr ⟨hJ, hm⟩
  refine (c_133 prof).run E.c E.hin (fun j' g' _ V' => V' = W ∧ Fr Y.cpu.gpr g' ∧ (j' = 150 ∨ j' = 145)) hK hA hr
    (vc_133 (by rw [hm.2.2.2]; exact (E.hfa k p W hJ).f176) (fun _ _ a _ => ⟨rfl, a, Or.inl rfl⟩)
      (fun _ _ a _ _ => ⟨rfl, a, Or.inr rfl⟩)) ?_
  rintro j' g fl V₁ ⟨hV₁, gf, hj⟩ U t₁ hKU hAU hrU hgU -
  subst V₁ hgU
  have hmU := Fa.fr hm gf
  rcases hj with rfl | rfl
  · exact hn U W t₁ hKU hAU hrU ⟨hJ, hmU⟩
  · refine callK E hKU hAU hrU hmU.1 (lt_len (by decide)) (call_145 _) tgt_145 E.cD (E.kD k p W _ hJ) trivial ?_
    intro Z W' t₃ hKZ hAZ hrZ hsZ hkZ hJZ
    exact hn Z W' t₃ hKZ hAZ hrZ ⟨hJZ, fa_ret hmU hsZ hkZ⟩

/-- 150: the chars at `0x48` freed unless null (159, `kD`), to 164. -/
theorem R150 (E : Ev prof F Wl L s₀ o gev gP gE S g0 e₂ code₂ j₂ I D J) (k : Nat) (p : Addr)
    (hn : AtJ prof F Wl L s₀ o gev gP gE 164 (PA S g0 J k p)) : AtJ prof F Wl L s₀ o gev gP gE 150 (PA S g0 J k p) := by
  rintro Y W t hK hA hr ⟨hJ, hm⟩
  refine (c_150 prof).run E.c E.hin (fun j' g' _ V' => V' = W ∧ Fr Y.cpu.gpr g' ∧ (j' = 164 ∨ j' = 159)) hK hA hr
    (vc_150 (by rw [hm.2.2.2]; exact (E.hfa k p W hJ).f72) (fun _ _ a _ => ⟨rfl, a, Or.inl rfl⟩)
      (fun _ _ a _ _ => ⟨rfl, a, Or.inr rfl⟩)) ?_
  rintro j' g fl V₁ ⟨hV₁, gf, hj⟩ U t₁ hKU hAU hrU hgU -
  subst V₁ hgU
  have hmU := Fa.fr hm gf
  rcases hj with rfl | rfl
  · exact hn U W t₁ hKU hAU hrU ⟨hJ, hmU⟩
  · refine callK E hKU hAU hrU hmU.1 (lt_len (by decide)) (call_159 _) tgt_159 E.cD (E.kD k p W _ hJ) trivial ?_
    intro Z W' t₃ hKZ hAZ hrZ hsZ hkZ hJZ
    exact hn Z W' t₃ hKZ hAZ hrZ ⟨hJZ, fa_ret hmU hsZ hkZ⟩

/-- 164: the chars at `0x38` freed unless null (173, `kD`), to 178. -/
theorem R164 (E : Ev prof F Wl L s₀ o gev gP gE S g0 e₂ code₂ j₂ I D J) (k : Nat) (p : Addr)
    (hn : AtJ prof F Wl L s₀ o gev gP gE 178 (PA S g0 J k p)) : AtJ prof F Wl L s₀ o gev gP gE 164 (PA S g0 J k p) := by
  rintro Y W t hK hA hr ⟨hJ, hm⟩
  refine (c_164 prof).run E.c E.hin (fun j' g' _ V' => V' = W ∧ Fr Y.cpu.gpr g' ∧ (j' = 178 ∨ j' = 173)) hK hA hr
    (vc_164 (by rw [hm.2.2.2]; exact (E.hfa k p W hJ).f56) (fun _ _ a _ => ⟨rfl, a, Or.inl rfl⟩)
      (fun _ _ a _ _ => ⟨rfl, a, Or.inr rfl⟩)) ?_
  rintro j' g fl V₁ ⟨hV₁, gf, hj⟩ U t₁ hKU hAU hrU hgU -
  subst V₁ hgU
  have hmU := Fa.fr hm gf
  rcases hj with rfl | rfl
  · exact hn U W t₁ hKU hAU hrU ⟨hJ, hmU⟩
  · refine callK E hKU hAU hrU hmU.1 (lt_len (by decide)) (call_173 _) tgt_173 E.cD (E.kD k p W _ hJ) trivial ?_
    intro Z W' t₃ hKZ hAZ hrZ hsZ hkZ hJZ
    exact hn Z W' t₃ hKZ hAZ hrZ ⟨hJZ, fa_ret hmU hsZ hkZ⟩

/-- 178: the chars at `0x28` freed unless null (187, `kD`), to 192. -/
theorem R178 (E : Ev prof F Wl L s₀ o gev gP gE S g0 e₂ code₂ j₂ I D J) (k : Nat) (p : Addr)
    (hn : AtJ prof F Wl L s₀ o gev gP gE 192 (PA S g0 J k p)) : AtJ prof F Wl L s₀ o gev gP gE 178 (PA S g0 J k p) := by
  rintro Y W t hK hA hr ⟨hJ, hm⟩
  refine (c_178 prof).run E.c E.hin (fun j' g' _ V' => V' = W ∧ Fr Y.cpu.gpr g' ∧ (j' = 192 ∨ j' = 187)) hK hA hr
    (vc_178 (by rw [hm.2.2.2]; exact (E.hfa k p W hJ).f40) (fun _ _ a _ => ⟨rfl, a, Or.inl rfl⟩)
      (fun _ _ a _ _ => ⟨rfl, a, Or.inr rfl⟩)) ?_
  rintro j' g fl V₁ ⟨hV₁, gf, hj⟩ U t₁ hKU hAU hrU hgU -
  subst V₁ hgU
  have hmU := Fa.fr hm gf
  rcases hj with rfl | rfl
  · exact hn U W t₁ hKU hAU hrU ⟨hJ, hmU⟩
  · refine callK E hKU hAU hrU hmU.1 (lt_len (by decide)) (call_187 _) tgt_187 E.cD (E.kD k p W _ hJ) trivial ?_
    intro Z W' t₃ hKZ hAZ hrZ hsZ hkZ hJZ
    exact hn Z W' t₃ hKZ hAZ hrZ ⟨hJZ, fa_ret hmU hsZ hkZ⟩

/-- 192: the interface at `p + 0x18` released unless null (`call [rax + 0x10]` at 204, `kR`), to 207. -/
theorem R192 (E : Ev prof F Wl L s₀ o gev gP gE S g0 e₂ code₂ j₂ I D J) (k : Nat) (p : Addr)
    (hn : AtJ prof F Wl L s₀ o gev gP gE 207 (PA S g0 J k p)) : AtJ prof F Wl L s₀ o gev gP gE 192 (PA S g0 J k p) := by
  rintro Y W t hK hA hr ⟨hJ, hm⟩
  have hb : Y.cpu.gpr.rbp = p := hm.2.2.2
  refine (c_192 prof).run E.c E.hin (fun j' g' _ V' => V' = W ∧ Fr Y.cpu.gpr g' ∧ (j' = 207 ∨
      (j' = 204 ∧ ¬rdq(W, Y.cpu.gpr.rbp + 24#64) = 0 ∧ g'.rdi = rdq(W, Y.cpu.gpr.rbp + 24#64) ∧
        g'.rax = rdq(W, rdq(W, Y.cpu.gpr.rbp + 24#64))))) hK hA hr
    (vc_192 (by rw [hb]; exact (E.hfa k p W hJ).f24) (fun hv => by rw [hb] at hv ⊢; exact (E.h24 k p W hJ hv).1)
      (fun _ _ a _ => ⟨rfl, a, Or.inl rfl⟩) (fun hv _ a d e _ => ⟨rfl, a, Or.inr ⟨rfl, hv, d, e⟩⟩)) ?_
  rintro j' g fl V₁ ⟨hV₁, gf, hj⟩ U t₁ hKU hAU hrU hgU -
  subst V₁ hgU
  have hmU := Fa.fr hm gf
  rcases hj with rfl | ⟨rfl, hv, gdi, gax⟩
  · exact hn U W t₁ hKU hAU hrU ⟨hJ, hmU⟩
  · rw [hb] at hv gdi gax
    refine callMK E hKU hAU hrU hmU.1 (lt_len (by decide)) (callm_204 _) gax (E.h24 k p W hJ hv)
      (E.kR k p W _ _ hJ (E.h24 k p W hJ hv)) gdi ?_
    intro Z W' t₃ hKZ hAZ hrZ hsZ hkZ hJZ
    exact hn Z W' t₃ hKZ hAZ hrZ ⟨hJZ, fa_ret hmU hsZ hkZ⟩

/-- 207: the interface at `p + 0x10` released unless null (`call [rax + 0x10]` at 219, `kR`), to 222. -/
theorem R207 (E : Ev prof F Wl L s₀ o gev gP gE S g0 e₂ code₂ j₂ I D J) (k : Nat) (p : Addr)
    (hn : AtJ prof F Wl L s₀ o gev gP gE 222 (PA S g0 J k p)) : AtJ prof F Wl L s₀ o gev gP gE 207 (PA S g0 J k p) := by
  rintro Y W t hK hA hr ⟨hJ, hm⟩
  have hb : Y.cpu.gpr.rbp = p := hm.2.2.2
  refine (c_207 prof).run E.c E.hin (fun j' g' _ V' => V' = W ∧ Fr Y.cpu.gpr g' ∧ (j' = 222 ∨
      (j' = 219 ∧ ¬rdq(W, Y.cpu.gpr.rbp + 16#64) = 0 ∧ g'.rdi = rdq(W, Y.cpu.gpr.rbp + 16#64) ∧
        g'.rax = rdq(W, rdq(W, Y.cpu.gpr.rbp + 16#64))))) hK hA hr
    (vc_207 (by rw [hb]; exact (E.hfa k p W hJ).f16) (fun hv => by rw [hb] at hv ⊢; exact (E.h16 k p W hJ hv).1)
      (fun _ _ a _ => ⟨rfl, a, Or.inl rfl⟩) (fun hv _ a d e _ => ⟨rfl, a, Or.inr ⟨rfl, hv, d, e⟩⟩)) ?_
  rintro j' g fl V₁ ⟨hV₁, gf, hj⟩ U t₁ hKU hAU hrU hgU -
  subst V₁ hgU
  have hmU := Fa.fr hm gf
  rcases hj with rfl | ⟨rfl, hv, gdi, gax⟩
  · exact hn U W t₁ hKU hAU hrU ⟨hJ, hmU⟩
  · rw [hb] at hv gdi gax
    refine callMK E hKU hAU hrU hmU.1 (lt_len (by decide)) (callm_219 _) gax (E.h16 k p W hJ hv)
      (E.kR k p W _ _ hJ (E.h16 k p W hJ hv)) gdi ?_
    intro Z W' t₃ hKZ hAZ hrZ hsZ hkZ hJZ
    exact hn Z W' t₃ hKZ hAZ hrZ ⟨hJZ, fa_ret hmU hsZ hkZ⟩

/-- 222: the interface at `p + 8` released unless null (`call [rax + 0x10]` at 234, `kR`), to 237. -/
theorem R222 (E : Ev prof F Wl L s₀ o gev gP gE S g0 e₂ code₂ j₂ I D J) (k : Nat) (p : Addr)
    (hn : AtJ prof F Wl L s₀ o gev gP gE 237 (PA S g0 J k p)) : AtJ prof F Wl L s₀ o gev gP gE 222 (PA S g0 J k p) := by
  rintro Y W t hK hA hr ⟨hJ, hm⟩
  have hb : Y.cpu.gpr.rbp = p := hm.2.2.2
  refine (c_222 prof).run E.c E.hin (fun j' g' _ V' => V' = W ∧ Fr Y.cpu.gpr g' ∧ (j' = 237 ∨
      (j' = 234 ∧ ¬rdq(W, Y.cpu.gpr.rbp + 8#64) = 0 ∧ g'.rdi = rdq(W, Y.cpu.gpr.rbp + 8#64) ∧
        g'.rax = rdq(W, rdq(W, Y.cpu.gpr.rbp + 8#64))))) hK hA hr
    (vc_222 (by rw [hb]; exact (E.hfa k p W hJ).f8) (fun hv => by rw [hb] at hv ⊢; exact (E.h8 k p W hJ hv).1)
      (fun _ _ a _ => ⟨rfl, a, Or.inl rfl⟩) (fun hv _ a d e _ => ⟨rfl, a, Or.inr ⟨rfl, hv, d, e⟩⟩)) ?_
  rintro j' g fl V₁ ⟨hV₁, gf, hj⟩ U t₁ hKU hAU hrU hgU -
  subst V₁ hgU
  have hmU := Fa.fr hm gf
  rcases hj with rfl | ⟨rfl, hv, gdi, gax⟩
  · exact hn U W t₁ hKU hAU hrU ⟨hJ, hmU⟩
  · rw [hb] at hv gdi gax
    refine callMK E hKU hAU hrU hmU.1 (lt_len (by decide)) (callm_234 _) gax (E.h8 k p W hJ hv)
      (E.kR k p W _ _ hJ (E.h8 k p W hJ hv)) gdi ?_
    intro Z W' t₃ hKZ hAZ hrZ hsZ hkZ hJZ
    exact hn Z W' t₃ hKZ hAZ hrZ ⟨hJZ, fa_ret hmU hsZ hkZ⟩

/-- 237: `r14` = the `CMyComPtr` `b` at `p`: null to 463; its `Release` the one in line to 270 (`h270`); else
`call rax` (515, `kB`), from its return the `jmp` (517) to 463. -/
theorem R237 (E : Ev prof F Wl L s₀ o gev gP gE S g0 e₂ code₂ j₂ I D J) (k : Nat) (p : Addr)
    (h463 : AtJ prof F Wl L s₀ o gev gP gE 463 (PA S g0 J k p))
    (h270 : ∀ b : Addr, b ≠ 0 → AtJ prof F Wl L s₀ o gev gP gE 270 fun g W => J k p W ∧ Fa S g0 p g ∧ g.r14 = b) :
    AtJ prof F Wl L s₀ o gev gP gE 237 (PA S g0 J k p) := by
  rintro Y W t hK hA hr ⟨hJ, hm⟩
  have hb : Y.cpu.gpr.rbp = p := hm.2.2.2
  refine (c_237 prof).run E.c E.hin (fun j' g' _ V' => V' = W ∧ Ft Y.cpu.gpr g' ∧ g'.r14 = rdq(W, p) ∧
      (j' = 463 ∨ (j' = 270 ∧ rdq(W, p) ≠ 0) ∨
        (j' = 515 ∧ rdq(W, p) ≠ 0 ∧ g'.rax = rdq(W, rdq(W, rdq(W, p)) + 16#64) ∧ g'.rdi = rdq(W, p)))) hK hA hr
    (vc_237 (b := rdq(W, p)) (fn := rdq(W, rdq(W, rdq(W, p)) + 16#64)) (by rw [hb]; exact (E.hfa k p W hJ).f0)
      (by rw [hb]) (fun h0 => (E.hB k p W hJ h0).1) (fun h0 => (E.hB k p W hJ h0).2.1) rfl
      (fun _ _ a b _ => ⟨rfl, a, b, Or.inl rfl⟩) (fun h0 _ _ a b _ => ⟨rfl, a, b, Or.inr (Or.inl ⟨rfl, h0⟩)⟩)
      (fun h0 _ _ a b d e _ => ⟨rfl, a, b, Or.inr (Or.inr ⟨rfl, h0, d, e⟩)⟩)) ?_
  rintro j' g fl V₁ ⟨hV₁, gf, g14, hj⟩ U t₁ hKU hAU hrU hgU -
  subst V₁ hgU
  have haU : Fa S g0 p U.cpu.gpr :=
    ⟨gf.1.trans hm.1, gf.2.2.2.2.1.trans hm.2.1, gf.2.2.2.2.2.trans hm.2.2.1, gf.2.2.1.trans hm.2.2.2⟩
  rcases hj with rfl | ⟨rfl, h0⟩ | ⟨rfl, h0, gax, gdi⟩
  · exact h463 U W t₁ hKU hAU hrU ⟨hJ, haU⟩
  · exact h270 _ h0 U W t₁ hKU hAU hrU ⟨hJ, haU, g14⟩
  · refine callRK E hKU hAU hrU haU.1 (lt_len (by decide)) (callr_515 _) gax (E.hB k p W hJ h0).2.2
      (E.kB k p W _ hJ h0) gdi ?_
    intro Z W' t₃ hKZ hAZ hrZ hsZ hkZ hJZ
    have haZ := fa_ret haU hsZ hkZ
    refine (c_517 prof).run E.c E.hin (fun j' g' _ V' => j' = 463 ∧ V' = W' ∧ g' = Z.cpu.gpr) hKZ hAZ hrZ
      (vc_517 fun _ => ⟨rfl, rfl, rfl⟩) ?_
    rintro j' g fl V₁ ⟨rfl, hV₁, hg⟩ U' t₄ hKU' hAU' hrU' hgU' -
    subst V₁
    exact h463 U' W' t₄ hKU' hAU' hrU' ⟨hJZ, by rw [hgU', hg]; exact haZ⟩

/-- 463: `operator delete (p, 0x110)` (471, `kE`), from its return to 476 with `D k`. -/
theorem R463 (E : Ev prof F Wl L s₀ o gev gP gE S g0 e₂ code₂ j₂ I D J) (k : Nat) (p : Addr)
    (hn : AtJ prof F Wl L s₀ o gev gP gE 476 fun g W => D k W ∧ Fm S g0 g) :
    AtJ prof F Wl L s₀ o gev gP gE 463 (PA S g0 J k p) := by
  rintro Y W t hK hA hr ⟨hJ, hm⟩
  refine (c_463 prof).run E.c E.hin (fun j' g' _ V' => j' = 471 ∧ V' = W ∧ Fr Y.cpu.gpr g' ∧
      g'.rdi = Y.cpu.gpr.rbp ∧ g'.rsi = 272#64) hK hA hr (vc_463 fun _ a b d _ => ⟨rfl, rfl, a, b, d⟩) ?_
  rintro j' g fl V₁ ⟨rfl, hV₁, gf, gdi, gsi⟩ U t₁ hKU hAU hrU hgU -
  subst V₁ hgU
  have hmU := Fa.fr hm gf
  refine callK E hKU hAU hrU hmU.1 (lt_len (by decide)) (call_471 _) tgt_471 E.cE (E.kE k p W hJ)
    ⟨gdi.trans hm.2.2.2, gsi⟩ ?_
  intro Z W' t₃ hKZ hAZ hrZ hsZ hkZ hDZ
  exact hn Z W' t₃ hKZ hAZ hrZ ⟨hDZ, fm_ret ⟨hmU.1, hmU.2.1, hmU.2.2.1⟩ hsZ hkZ⟩

end Runs

end FV7z.Alr
