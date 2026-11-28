import FV7z.Spp.Pieces
/-!
# `SplitPathToParts` (PLAN.md §M, M1): the run through the callees

The pieces of `FV7z/Spp/Pieces.lean` joined into the run from the entry to the return address. `S` the stack pointer
and `g0` the registers at the entry: `path` = `g0.rdi`, `pathParts` = `g0.rsi`.

The callees are continuations (`KC`, as in `FV7z/Oci/Holds.lean`), each with the bytes it returns with: from its
return the run goes on with `rsp` as it was and the callee-saved registers (`KS`) as at the `call`. The bytes are
tracked by invariants the caller chooses: `I (k + 1)` before the step `k` of `pathParts.Clear ()` (the size `n`, the
items `it`; `J k p` after the item's chars, `I k` after the item, as in `Oci`), `I 0` from the clear's end on. `I 0`
is kept by the stores `Ok` allows (`hcl`: the size, `_items`, `_capacity`, the stack slots at `aR S + 16` and
`aR S + 24`, the slot `_items[_size]`) and by every later callee; it gives the stack (`Stk`: the saved registers, the
return address, the guard, `path` at `aR S + 8`), `path._chars` = `ch` (`hch`) and `path._len` = `ln` (`hln`): the
chars `ch + 4 k` for `k < ln` are readable (`fc`).

- `Stk`, `Fc`, `Fa`, `Fb`, `Fs`, `KC`, `AtJ`, `Ev`: the stack, the frames (the clear; the `Add` of the step `i`; the
  tail; the scan at the step `i`), the callees, the runs from an offset, the hypotheses of the runs; `callK`: a
  `call`; `sInc`, `sLn`, `sI1`, `sR14`, `sGo`, `sEnd`: the scan's arithmetic.
- `tail135`, `from593`, `from557`, …, `from432`: the tail; `from362`, …, `from259`, `R254`: the first `Add`
  (to 378, `h378`); `S378c`, `S378x`, `S221c`, `S221x`, `L221`: the scan, by induction on the steps left;
  `from189`, `from114`: the start of the scan; `A91`, `B64`, `S104`, `L64`: the clear, by induction on the step.
- `spp_ok`: from the entry to the return address.
-/

open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn

namespace FV7z.Spp

set_option linter.unusedVariables false

open FV7z.Fr40 (KS)
open FV7z.Ocv (pk rbx0 rbx0_eq rb_step rb_ne rb_last)

/-! ## The frame -/

/-- The stack (`fb` the `fs` base, `ra` the return address): the six saved registers, the return address, the stack
guard as at `fs:0x28`, `path` at `aR S + 8`. -/
abbrev Stk (fb : Addr) (W : Addr → Byte) (S : Addr) (g0 : Gprs) (ra : Addr) : Prop :=
  rdq(W, S - 8 - 8 - 8 - 8 - 8 - 8) = g0.rbx ∧ rdq(W, S - 8 - 8 - 8 - 8 - 8) = g0.rbp ∧
    rdq(W, S - 8 - 8 - 8 - 8) = g0.r12 ∧ rdq(W, S - 8 - 8 - 8) = g0.r13 ∧ rdq(W, S - 8 - 8) = g0.r14 ∧
    rdq(W, S - 8) = g0.r15 ∧ rdq(W, S) = ra ∧ rdq(W, aR S + 56#64) = rdq(W, fb + 40#64) ∧
    rdq(W, aR S + 8#64) = g0.rdi

/-- The frame of the clear: `rsp` = `aR S`, `rbp` = `pathParts`. -/
abbrev Fc (S : Addr) (g0 g : Gprs) : Prop := g.rsp = aR S ∧ g.rbp = g0.rsi

/-- The frame of the tail: `rsp` = `aR S`, `rbp` = `pathParts`, `r15` = `&name`. -/
abbrev Fb (S : Addr) (g0 g : Gprs) : Prop := g.rsp = aR S ∧ g.rbp = g0.rsi ∧ g.r15 = aR S + 32#64

/-- The frame of the `Add` at the step `i`: `Fb`, `rbx` = `i`, `r12` = `len`, `r14` = `i` (32 bits). -/
abbrev Fa (S : Addr) (g0 : Gprs) (ln : BitVec 32) (i : Nat) (g : Gprs) : Prop :=
  g.rsp = aR S ∧ g.rbp = g0.rsi ∧ g.r15 = aR S + 32#64 ∧ g.rbx = BitVec.ofNat 64 i ∧
    g.r12 = BitVec.setWidth 64 ln ∧ g.r14 = BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 64 i))

/-- The frame of the scan at the step `i`: `Fb`, `rbx` = `i`, `r12` = `len`, `rax` = `path._chars`. -/
abbrev Fs (S : Addr) (g0 : Gprs) (ln : BitVec 32) (ch : BitVec 64) (i : Nat) (g : Gprs) : Prop :=
  g.rsp = aR S ∧ g.rbp = g0.rsi ∧ g.r15 = aR S + 32#64 ∧ g.rbx = BitVec.ofNat 64 i ∧
    g.r12 = BitVec.setWidth 64 ln ∧ g.rax = ch

theorem Fc.fr {S : Addr} {g0 g g' : Gprs} (h : Fc S g0 g) (h' : Fr g g') : Fc S g0 g' :=
  ⟨h'.1.trans h.1, h'.2.1.trans h.2⟩

theorem fc_ret {S : Addr} {g0 g g' : Gprs} (h : Fc S g0 g) (hs : g'.rsp = aR S) (hk : KS g g') : Fc S g0 g' :=
  ⟨hs, hk.2.1.trans h.2⟩

theorem Fb.fr {S : Addr} {g0 g g' : Gprs} (h : Fb S g0 g) (h' : Fr g g') : Fb S g0 g' :=
  ⟨h'.1.trans h.1, h'.2.1.trans h.2.1, h'.2.2.trans h.2.2⟩

theorem fb_ret {S : Addr} {g0 g g' : Gprs} (h : Fb S g0 g) (hs : g'.rsp = aR S) (hk : KS g g') : Fb S g0 g' :=
  ⟨hs, hk.2.1.trans h.2.1, hk.2.2.2.2.2.trans h.2.2⟩

theorem Fa.fk {S : Addr} {g0 g g' : Gprs} {ln : BitVec 32} {i : Nat} (h : Fa S g0 ln i g) (h' : Fk g g') :
    Fa S g0 ln i g' :=
  ⟨h'.1.trans h.1, h'.2.1.trans h.2.1, h'.2.2.1.trans h.2.2.1, h'.2.2.2.1.trans h.2.2.2.1,
    h'.2.2.2.2.1.trans h.2.2.2.2.1, h'.2.2.2.2.2.trans h.2.2.2.2.2⟩

theorem fa_ret {S : Addr} {g0 g g' : Gprs} {ln : BitVec 32} {i : Nat} (h : Fa S g0 ln i g) (hs : g'.rsp = aR S)
    (hk : KS g g') : Fa S g0 ln i g' :=
  ⟨hs, hk.2.1.trans h.2.1, hk.2.2.2.2.2.trans h.2.2.1, hk.1.trans h.2.2.2.1, hk.2.2.1.trans h.2.2.2.2.1,
    hk.2.2.2.2.1.trans h.2.2.2.2.2⟩

/-! ## The scan's arithmetic -/

theorem sInc (i : Nat) : BitVec.ofNat 64 i + 1#64 = BitVec.ofNat 64 (i + 1) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.reducePow]
  omega

theorem sLn (ln : BitVec 32) : (BitVec.setWidth 32 (BitVec.setWidth 64 ln)).toNat = ln.toNat := by
  have : ln.toNat < 4294967296 := ln.isLt
  simp only [BitVec.toNat_setWidth, Nat.reducePow]
  omega

theorem sI1 (i : Nat) (h : i + 1 < 4294967296) : (BitVec.setWidth 32 (BitVec.ofNat 64 i + 1#64)).toNat = i + 1 := by
  simp only [BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.reducePow]
  omega

theorem sR14 (i : Nat) (h : i + 1 < 4294967296) :
    (BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 64 i)) + 1#64)).toNat = i + 1 := by
  simp only [BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.reducePow]
  omega

/-- `jbe` not taken: `i + 1 < len`. -/
theorem sGo {r b : BitVec 64} {N i : Nat} (hr : (BitVec.setWidth 32 r).toNat = N)
    (hb : (BitVec.setWidth 32 b).toNat = i + 1) (h : i + 1 < N) :
    ¬((BitVec.setWidth 32 r).toNat < (BitVec.setWidth 32 b).toNat ∨
      BitVec.setWidth 32 r = BitVec.setWidth 32 b) := by
  rintro (h1 | h1)
  · omega
  · have := congrArg BitVec.toNat h1
    omega

/-- `jbe` taken: `i + 1 = len`. -/
theorem sEnd {r b : BitVec 64} {N i : Nat} (hr : (BitVec.setWidth 32 r).toNat = N)
    (hb : (BitVec.setWidth 32 b).toNat = i + 1) (h : i + 1 = N) :
    (BitVec.setWidth 32 r).toNat < (BitVec.setWidth 32 b).toNat ∨
      BitVec.setWidth 32 r = BitVec.setWidth 32 b :=
  Or.inr (BitVec.eq_of_toNat_eq (by omega))

/-! ## The callees and the hypotheses of the runs -/

/-- A callee from the `call` before `j` (entry `ent`, the bytes `W`, the registers `A`): at its entry, and from its
return at `j` with `rsp` = `aR S`, the callee-saved registers as at its entry and bytes with `N`, the run goes on to
the goal. -/
def KC (prof : Profile) (F : Footprint) (Wl : List Rgn) (L : List (Addr × List Byte)) (s₀ : State) (o : Oracle)
    (gev : List Event) (gP : State → Nat → List Event → Prop) (gE : Outcome → List Event → Prop)
    (S ent : Addr) (j : Nat) (W : Addr → Byte) (A : Gprs → Prop) (N : (Addr → Byte) → Prop) : Prop :=
  ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y →
    Agree F Y.proc.mm.mem (Vst W (aR S - 8) (toBytesLE (spp_at.add j) 8)) →
    Y.cpu.rip = ent → Y.cpu.gpr.rsp = aR S - 8 → A Y.cpu.gpr →
    (∀ (Z : State) (W' : Addr → Byte) (t'' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem W' →
      Z.cpu.rip = spp_at.add j → Z.cpu.gpr.rsp = aR S → KS Y.cpu.gpr Z.cpu.gpr → N W' →
      GoG prof L o gev gP gE Z t'') →
    GoG prof L o gev gP gE Y t'

/-- From offset `j` with registers and bytes for which `P` holds, the run goes on to the goal. -/
def AtJ (prof : Profile) (F : Footprint) (Wl : List Rgn) (L : List (Addr × List Byte)) (s₀ : State) (o : Oracle)
    (gev : List Event) (gP : State → Nat → List Event → Prop) (gE : Outcome → List Event → Prop) (j : Nat)
    (P : Gprs → (Addr → Byte) → Prop) : Prop :=
  ∀ (Y : State) (W : Addr → Byte) (t : Nat), KeptW Wl s₀ Y → Agree F Y.proc.mm.mem W →
    Y.cpu.rip = spp_at.add j → P Y.cpu.gpr W → GoG prof L o gev gP gE Y t

/-- The hypotheses of the runs from the cut points (`S`, `g0` the entry's stack pointer and registers, `e₂.add j₂`
the return address, `n` the size and `it` the items before the clear, `ch` and `ln` `path`'s chars and length, `I`,
`J` the invariants of the bytes, `Ok` the stores that keep `I 0`). -/
structure Ev (prof : Profile) (F : Footprint) (Wl : List Rgn) (L : List (Addr × List Byte)) (s₀ : State)
    (o : Oracle) (gev : List Event) (gP : State → Nat → List Event → Prop) (gE : Outcome → List Event → Prop)
    (fb S : Addr) (g0 : Gprs) (e₂ : Addr) (code₂ : List Byte) (j₂ : Nat) (n : Nat) (it ch : BitVec 64)
    (ln : BitVec 32) (I : Nat → (Addr → Byte) → Prop) (J : Nat → BitVec 64 → (Addr → Byte) → Prop)
    (Ok : Addr → Nat → Prop) : Prop where
  c : Seg prof F Wl L s₀ o
  hfs : s₀.cpu.seg.fsBase = fb
  hin : CodeIn L spp_at spp
  hin₂ : CodeIn L e₂ code₂
  h₂ : j₂ < code₂.length
  hn : n < 4294967296
  hI : ∀ W, I 0 W → Stk fb W S g0 (e₂.add j₂)
  hch : ∀ W, I 0 W → rdq(W, g0.rdi) = ch
  hln : ∀ W, I 0 W → rdd(W, g0.rdi + 8#64) = ln
  hok : ∀ a m, Ok a m → ∀ i < m, Foot Wl (Addr.add a i)
  hcl : ∀ (W : Addr → Byte) (a : Addr) (m : Nat) (bs : List Byte), bs.length = m → Ok a m → I 0 W →
    I 0 (Vst W a bs)
  o0 : Ok g0.rsi 8
  o8 : Ok (g0.rsi + 8#64) 4
  o12 : Ok (g0.rsi + 12#64) 4
  os16 : Ok (aR S + 16#64) 4
  os16q : Ok (aR S + 16#64) 8
  os24 : Ok (aR S + 24#64) 8
  hsl : ∀ W, I 0 W → Ok (rdq(W, g0.rsi) + BitVec.setWidth 64 rdd(W, g0.rsi + 8#64) * 8#64) 8
  fcl : ∀ i < 8, Foot F.data (Addr.add (fb + 40#64) i)
  fg : ∀ i < 8, Foot F.data (Addr.add (aR S + 56#64) i)
  f8s : ∀ i < 8, Foot F.data (Addr.add (aR S + 8#64) i)
  f32 : ∀ i < 8, Foot F.data (Addr.add (aR S + 32#64) i)
  fb48 : ∀ i < 8, Foot F.data (Addr.add (S - 8 - 8 - 8 - 8 - 8 - 8) i)
  fb40 : ∀ i < 8, Foot F.data (Addr.add (S - 8 - 8 - 8 - 8 - 8) i)
  fb32 : ∀ i < 8, Foot F.data (Addr.add (S - 8 - 8 - 8 - 8) i)
  fb24 : ∀ i < 8, Foot F.data (Addr.add (S - 8 - 8 - 8) i)
  fb16 : ∀ i < 8, Foot F.data (Addr.add (S - 8 - 8) i)
  fb8 : ∀ i < 8, Foot F.data (Addr.add (S - 8) i)
  hl : ∀ i < 8, Foot F.data (Addr.add S i)
  hr8 : ∀ i < 8, Foot Wl (Addr.add (aR S - 8) i)
  fp0 : ∀ i < 8, Foot F.data (Addr.add g0.rdi i)
  fp8 : ∀ i < 4, Foot F.data (Addr.add (g0.rdi + 8#64) i)
  fc : ∀ k < ln.toNat, ∀ i < 4, Foot F.data (Addr.add (ch + BitVec.ofNat 64 k * 4#64) i)
  fe : ∀ k < n, ∀ i < 8, Foot F.data (Addr.add (it + BitVec.ofNat 64 (8 * k)) i)
  fp : ∀ k < n, ∀ W, I (k + 1) W → pk W it k ≠ 0 → ∀ i < 8, Foot F.data (Addr.add (pk W it k) i)
  hIt : ∀ k < n, ∀ W, I (k + 1) W → rdq(W, g0.rsi) = it
  hP0 : ∀ k < n, ∀ W, I (k + 1) W → pk W it k = 0 → I k W
  hQ0 : ∀ k < n, ∀ W, I (k + 1) W → pk W it k ≠ 0 → rdq(W, pk W it k) = 0 → J k (pk W it k) W
  cD : ∃ code : List Byte, CodeIn L 0x6014f0#64 code ∧ 0 < code.length
  cE : ∃ code : List Byte, CodeIn L 0x6014e0#64 code ∧ 0 < code.length
  cC : ∃ code : List Byte, CodeIn L 0x44d3e0#64 code ∧ 0 < code.length
  cS : ∃ code : List Byte, CodeIn L 0x44d790#64 code ∧ 0 < code.length
  cN2 : ∃ code : List Byte, CodeIn L 0x6029b0#64 code ∧ 0 < code.length
  cM : ∃ code : List Byte, CodeIn L 0x401070#64 code ∧ 0 < code.length
  cN : ∃ code : List Byte, CodeIn L 0x602970#64 code ∧ 0 < code.length
  cU : ∃ code : List Byte, CodeIn L 0x44d5d0#64 code ∧ 0 < code.length
  cT2 : ∃ code : List Byte, CodeIn L 0x4017c2#64 code ∧ 0 < code.length
  cT7 : ∃ code : List Byte, CodeIn L 0x4017c7#64 code ∧ 0 < code.length
  k86 : ∀ k < n, ∀ W, I (k + 1) W → pk W it k ≠ 0 → rdq(W, pk W it k) ≠ 0 →
    KC prof F Wl L s₀ o gev gP gE S 0x6014f0#64 91 W (fun g => g.rdi = rdq(W, pk W it k)) (J k (pk W it k))
  k99 : ∀ k < n, ∀ p W, p ≠ 0 → J k p W →
    KC prof F Wl L s₀ o gev gP gE S 0x6014e0#64 104 W (fun g => g.rdi = p ∧ g.rsi = 16#64) (I k)
  k184 : ∀ W, I 0 W → KC prof F Wl L s₀ o gev gP gE S 0x44d3e0#64 189 W (fun g => g.rdi = aR S + 32#64) (I 0)
  k254 : ∀ W, I 0 W → KC prof F Wl L s₀ o gev gP gE S 0x44d790#64 259 W (fun g => g.rdi = aR S + 32#64) (I 0)
  k309 : ∀ W, I 0 W → KC prof F Wl L s₀ o gev gP gE S 0x6029b0#64 314 W (fun _ => True) (I 0)
  k627 : ∀ W, I 0 W → KC prof F Wl L s₀ o gev gP gE S 0x401070#64 632 W (fun _ => True) (I 0)
  k648 : ∀ W, I 0 W → KC prof F Wl L s₀ o gev gP gE S 0x6014f0#64 653 W (fun _ => True) (I 0)
  k357 : ∀ W, I 0 W → KC prof F Wl L s₀ o gev gP gE S 0x602970#64 362 W (fun _ => True) (I 0)
  k373 : ∀ W, I 0 W → KC prof F Wl L s₀ o gev gP gE S 0x44d5d0#64 378 W (fun _ => True) (I 0)
  k440 : ∀ W, I 0 W → KC prof F Wl L s₀ o gev gP gE S 0x44d790#64 445 W (fun g => g.rdi = aR S + 32#64) (I 0)
  k494 : ∀ W, I 0 W → KC prof F Wl L s₀ o gev gP gE S 0x6029b0#64 499 W (fun _ => True) (I 0)
  k686 : ∀ W, I 0 W → KC prof F Wl L s₀ o gev gP gE S 0x401070#64 691 W (fun _ => True) (I 0)
  k694 : ∀ W, I 0 W → KC prof F Wl L s₀ o gev gP gE S 0x6014f0#64 699 W (fun _ => True) (I 0)
  k538 : ∀ W, I 0 W → KC prof F Wl L s₀ o gev gP gE S 0x602970#64 543 W (fun _ => True) (I 0)
  k552 : ∀ W, I 0 W → KC prof F Wl L s₀ o gev gP gE S 0x44d5d0#64 557 W (fun _ => True) (I 0)
  k588 : ∀ W, I 0 W → KC prof F Wl L s₀ o gev gP gE S 0x6014f0#64 593 W (fun _ => True) (I 0)
  kt2 : ∀ W, I 0 W → ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y → Agree F Y.proc.mm.mem W →
    Y.cpu.rip = 0x4017c2#64 → Y.cpu.gpr.rsp = aR S → GoG prof L o gev gP gE Y t'
  kt7 : ∀ W, I 0 W → ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y → Agree F Y.proc.mm.mem W →
    Y.cpu.rip = 0x4017c7#64 → Y.cpu.gpr.rsp = aR S → GoG prof L o gev gP gE Y t'
  kr : ∀ (W : Addr → Byte) (Z' : State) (t' : Nat), KeptW Wl s₀ Z' → Agree F Z'.proc.mm.mem W →
    Z'.cpu.rip = e₂.add j₂ → Z'.cpu.gpr.rsp = S + 8 → KS g0 Z'.cpu.gpr → I 0 W →
      GoG prof L o gev gP gE Z' t'

/-! ## The runs -/

section Runs

variable {prof : Profile} {F : Footprint} {Wl : List Rgn} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {fb S : Addr} {g0 : Gprs} {e₂ : Addr} {code₂ : List Byte} {j₂ : Nat} {n : Nat} {it ch : BitVec 64}
  {ln : BitVec 32} {I : Nat → (Addr → Byte) → Prop} {J : Nat → BitVec 64 → (Addr → Byte) → Prop}
  {Ok : Addr → Nat → Prop} {Y : State} {t : Nat} {W : Addr → Byte}

/-- A store's footprint in `F.data`. -/
theorem Ev.fd (E : Ev prof F Wl L s₀ o gev gP gE fb S g0 e₂ code₂ j₂ n it ch ln I J Ok) {a : Addr} {m : Nat}
    (h : Ok a m) : ∀ i < m, Foot F.data (Addr.add a i) := fun i hi => E.c.hws _ (E.hok _ _ h i hi)

/-- A `call` at `j` (`rsp` = `aR S`, the bytes `W`) of the callee `k`, and from its return at `j + 5`. -/
theorem callK (E : Ev prof F Wl L s₀ o gev gP gE fb S g0 e₂ code₂ j₂ n it ch ln I J Ok) {U : State} {t₁ : Nat}
    {j R : Nat} {ent : Addr} {A : Gprs → Prop} {N : (Addr → Byte) → Prop} (hKU : KeptW Wl s₀ U)
    (hAU : Agree F U.proc.mm.mem W) (hrU : U.cpu.rip = spp_at.add j) (hs : U.cpu.gpr.rsp = aR S)
    (hj : j < spp.length) (hd : Dec prof.feat spp j (FV7z.mk .call 64 [.rel R] 5))
    (htgt : spp_at.add (j + 5) + BitVec.ofNat 64 R = ent)
    (hc : ∃ code : List Byte, CodeIn L ent code ∧ 0 < code.length)
    (k : KC prof F Wl L s₀ o gev gP gE S ent (j + 5) W A N) (hA : A (U.cpu.gpr.set 4 (aR S - 8)))
    (h : ∀ (Z : State) (W' : Addr → Byte) (t'' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem W' →
      Z.cpu.rip = spp_at.add (j + 5) → Z.cpu.gpr.rsp = aR S → KS U.cpu.gpr Z.cpu.gpr → N W' →
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

/-! ### The tail -/

/-- From 135 (`rsp` = `aR S`, the bytes `W` with `I 0`): the guard's check, the epilogue, the `ret`, to `kr`. -/
theorem tail135 (E : Ev prof F Wl L s₀ o gev gP gE fb S g0 e₂ code₂ j₂ n it ch ln I J Ok) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = spp_at.add 135) (hs : Y.cpu.gpr.rsp = aR S) (hIW : I 0 W) :
    GoG prof L o gev gP gE Y t := by
  obtain ⟨s1, s2, s3, s4, s5, s6, s7, s8, -⟩ := E.hI W hIW
  have e1 : rdq(W, Y.cpu.gpr.rsp + 72#64) = g0.rbx := by rw [hs, q1]; exact s1
  have e2 : rdq(W, Y.cpu.gpr.rsp + 72#64 + 8) = g0.rbp := by rw [hs, q2]; exact s2
  have e3 : rdq(W, Y.cpu.gpr.rsp + 72#64 + 8 + 8) = g0.r12 := by rw [hs, q3]; exact s3
  have e4 : rdq(W, Y.cpu.gpr.rsp + 72#64 + 8 + 8 + 8) = g0.r13 := by rw [hs, q4]; exact s4
  have e5 : rdq(W, Y.cpu.gpr.rsp + 72#64 + 8 + 8 + 8 + 8) = g0.r14 := by rw [hs, q5]; exact s5
  have e6 : rdq(W, Y.cpu.gpr.rsp + 72#64 + 8 + 8 + 8 + 8 + 8) = g0.r15 := by rw [hs, q6]; exact s6
  refine (c_135 prof fb).run E.c E.hfs E.hin (fun j' g' _ V' => j' = 169 ∧ V' = W ∧
      g'.rsp = Y.cpu.gpr.rsp + 72#64 + 8 + 8 + 8 + 8 + 8 + 8 ∧ g'.rbx = rdq(W, Y.cpu.gpr.rsp + 72#64) ∧
      g'.rbp = rdq(W, Y.cpu.gpr.rsp + 72#64 + 8) ∧ g'.r12 = rdq(W, Y.cpu.gpr.rsp + 72#64 + 8 + 8) ∧
      g'.r13 = rdq(W, Y.cpu.gpr.rsp + 72#64 + 8 + 8 + 8) ∧ g'.r14 = rdq(W, Y.cpu.gpr.rsp + 72#64 + 8 + 8 + 8 + 8) ∧
      g'.r15 = rdq(W, Y.cpu.gpr.rsp + 72#64 + 8 + 8 + 8 + 8 + 8))
    hK hA hr
    (vc_135 (by rw [hs]; exact s8) (by rw [hs]; exact E.fg) E.fcl (by rw [hs, q1]; exact E.fb48)
      (by rw [hs, q2]; exact E.fb40) (by rw [hs, q3]; exact E.fb32) (by rw [hs, q4]; exact E.fb24)
      (by rw [hs, q5]; exact E.fb16) (by rw [hs, q6]; exact E.fb8)
      fun _ a b d e f g h _ => ⟨rfl, rfl, a, b, d, e, f, g, h⟩) ?_
  rintro j' g fl V₁ ⟨rfl, hV₁, gs, gx, gp, g12, g13, g14, g15⟩ U t₁ hKU hAU hrU hgU -
  subst V₁ hgU
  have hsU : U.cpu.gpr.rsp = S := by rw [gs, hs]; exact q7 S
  refine E.c.s_ret hKU hAU E.hin (lt_len (by decide)) hrU (ret_169 _) (by rw [hsU]; exact E.hl) E.hin₂ E.h₂
    (by rw [hsU]; exact s7) ?_
  rintro Z' t₂ hKZ' hAZ' ⟨hrZ', hgZ'⟩
  refine E.kr W Z' t₂ hKZ' hAZ' hrZ' ?_ ?_ hIW
  · rw [hgZ']
    show U.cpu.gpr.rsp + 8 = _
    rw [hsU]
  · rw [hgZ']
    exact ⟨gx.trans e1, gp.trans e2, g12.trans e3, g13.trans e4, g14.trans e5, g15.trans e6⟩

/-- From 593 (back from `delete []` of `name`'s chars): `jmp` to 135. -/
theorem from593 (E : Ev prof F Wl L s₀ o gev gP gE fb S g0 e₂ code₂ j₂ n it ch ln I J Ok) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = spp_at.add 593) (hs : Y.cpu.gpr.rsp = aR S) (hIW : I 0 W) :
    GoG prof L o gev gP gE Y t := by
  refine (c_593 prof fb).run E.c E.hfs E.hin (fun j' g' _ V' => j' = 135 ∧ g' = Y.cpu.gpr ∧ V' = W)
    hK hA hr (vc_593 fun _ => ⟨rfl, rfl, rfl⟩) ?_
  rintro j' g fl V₁ ⟨rfl, rfl, hV₁⟩ U t₁ hKU hAU hrU hgU -
  subst V₁ hgU
  exact tail135 E hKU hAU hrU hs hIW

/-- From 557 (back from the last item's `UString (name)`): the slot, the size; `name`'s chars freed unless 0 (588);
to 135. -/
theorem from557 (E : Ev prof F Wl L s₀ o gev gP gE fb S g0 e₂ code₂ j₂ n it ch ln I J Ok) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = spp_at.add 557) (hm : Fb S g0 Y.cpu.gpr) (hIW : I 0 W) :
    GoG prof L o gev gP gE Y t := by
  refine (c_557 prof fb).run E.c E.hfs E.hin (fun j' g' _ V' => I 0 V' ∧ Fr Y.cpu.gpr g' ∧ (j' = 135 ∨ j' = 588))
    hK hA hr
    (vc_557 (by rw [hm.2.1]; exact E.fd E.o8) (by rw [hm.2.1]; exact E.fd E.o0)
      (by rw [hm.2.1]; exact E.hok _ _ E.o8) (by rw [hm.2.1]; exact E.o8)
      (by rw [hm.2.1]; exact E.hok _ _ (E.hsl W hIW)) (by rw [hm.2.1]; exact E.hsl W hIW)
      (by rw [hm.1]; exact E.f32) hIW E.hcl (fun _ _ hI a _ => ⟨hI, a, Or.inl rfl⟩)
      (fun _ _ hI a _ => ⟨hI, a, Or.inr rfl⟩)) ?_
  rintro j' g fl V₁ ⟨hI1, gf, hj⟩ U t₁ hKU hAU hrU hgU -
  subst hgU
  have hmU := Fb.fr hm gf
  rcases hj with rfl | rfl
  · exact tail135 E hKU hAU hrU hmU.1 hI1
  · refine callK E hKU hAU hrU hmU.1 (lt_len (by decide)) (call_588 _) tgt_588 E.cD (E.k588 _ hI1) trivial ?_
    intro Z W' t₃ hKZ hAZ hrZ hsZ hkZ hIZ
    exact from593 E hKZ hAZ hrZ hsZ hIZ

/-- From 543 (back from `operator new`): the item's `UString (name)` (552), from its return to 557. -/
theorem from543 (E : Ev prof F Wl L s₀ o gev gP gE fb S g0 e₂ code₂ j₂ n it ch ln I J Ok) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = spp_at.add 543) (hm : Fb S g0 Y.cpu.gpr) (hIW : I 0 W) :
    GoG prof L o gev gP gE Y t := by
  refine (c_543 prof fb).run E.c E.hfs E.hin (fun j' g' _ V' => j' = 552 ∧ V' = W ∧ Fr Y.cpu.gpr g') hK hA hr
    (vc_543 fun _ a _ => ⟨rfl, rfl, a⟩) ?_
  rintro j' g fl V₁ ⟨rfl, hV₁, gf⟩ U t₁ hKU hAU hrU hgU -
  subst V₁ hgU
  have hmU := Fb.fr hm gf
  refine callK E hKU hAU hrU hmU.1 (lt_len (by decide)) (call_552 _) tgt_552 E.cU (E.k552 _ hIW) trivial ?_
  intro Z W' t₃ hKZ hAZ hrZ hsZ hkZ hIZ
  exact from557 E hKZ hAZ hrZ (fb_ret hmU hsZ hkZ) hIZ

/-- From 533: `operator new (16)` (538), from its return to 543. -/
theorem from533 (E : Ev prof F Wl L s₀ o gev gP gE fb S g0 e₂ code₂ j₂ n it ch ln I J Ok) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = spp_at.add 533) (hm : Fb S g0 Y.cpu.gpr) (hIW : I 0 W) :
    GoG prof L o gev gP gE Y t := by
  refine (c_533 prof fb).run E.c E.hfs E.hin (fun j' g' _ V' => j' = 538 ∧ V' = W ∧ Fr Y.cpu.gpr g') hK hA hr
    (vc_533 fun _ a _ => ⟨rfl, rfl, a⟩) ?_
  rintro j' g fl V₁ ⟨rfl, hV₁, gf⟩ U t₁ hKU hAU hrU hgU -
  subst V₁ hgU
  have hmU := Fb.fr hm gf
  refine callK E hKU hAU hrU hmU.1 (lt_len (by decide)) (call_538 _) tgt_538 E.cN (E.k538 _ hIW) trivial ?_
  intro Z W' t₃ hKZ hAZ hrZ hsZ hkZ hIZ
  exact from543 E hKZ hAZ hrZ (fb_ret hmU hsZ hkZ) hIZ

/-- From 526: the new `_items` and `_capacity` stored; to 533. -/
theorem from526 (E : Ev prof F Wl L s₀ o gev gP gE fb S g0 e₂ code₂ j₂ n it ch ln I J Ok) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = spp_at.add 526) (hm : Fb S g0 Y.cpu.gpr) (hIW : I 0 W) :
    GoG prof L o gev gP gE Y t := by
  refine (c_526 prof fb).run E.c E.hfs E.hin (fun j' g' _ V' => j' = 533 ∧ I 0 V' ∧ Fr Y.cpu.gpr g') hK hA hr
    (vc_526 (by rw [hm.2.1]; exact E.hok _ _ E.o0) (by rw [hm.2.1]; exact E.hok _ _ E.o12)
      (by rw [hm.2.1]; exact E.o0) (by rw [hm.2.1]; exact E.o12) hIW E.hcl fun _ _ hI a _ => ⟨rfl, hI, a⟩) ?_
  rintro j' g fl V₁ ⟨rfl, hI1, gf⟩ U t₁ hKU hAU hrU hgU -
  subst hgU
  exact from533 E hKU hAU hrU (Fb.fr hm gf) hI1

/-- From 699 (back from `delete []` of the old items): `jmp` to 526. -/
theorem from699 (E : Ev prof F Wl L s₀ o gev gP gE fb S g0 e₂ code₂ j₂ n it ch ln I J Ok) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = spp_at.add 699) (hm : Fb S g0 Y.cpu.gpr) (hIW : I 0 W) :
    GoG prof L o gev gP gE Y t := by
  refine (c_699 prof fb).run E.c E.hfs E.hin (fun j' g' _ V' => j' = 526 ∧ g' = Y.cpu.gpr ∧ V' = W)
    hK hA hr (vc_699 fun _ => ⟨rfl, rfl, rfl⟩) ?_
  rintro j' g fl V₁ ⟨rfl, rfl, hV₁⟩ U t₁ hKU hAU hrU hgU -
  subst V₁ hgU
  exact from526 E hKU hAU hrU hm hIW

/-- From 691 (back from `memcpy`, or the old items not copied): `delete []` of the old items (694), to 699. -/
theorem from691 (E : Ev prof F Wl L s₀ o gev gP gE fb S g0 e₂ code₂ j₂ n it ch ln I J Ok) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = spp_at.add 691) (hm : Fb S g0 Y.cpu.gpr) (hIW : I 0 W) :
    GoG prof L o gev gP gE Y t := by
  refine (c_691 prof fb).run E.c E.hfs E.hin (fun j' g' _ V' => j' = 694 ∧ V' = W ∧ Fr Y.cpu.gpr g') hK hA hr
    (vc_691 fun _ a _ => ⟨rfl, rfl, a⟩) ?_
  rintro j' g fl V₁ ⟨rfl, hV₁, gf⟩ U t₁ hKU hAU hrU hgU -
  subst V₁ hgU
  have hmU := Fb.fr hm gf
  refine callK E hKU hAU hrU hmU.1 (lt_len (by decide)) (call_694 _) tgt_694 E.cD (E.k694 _ hIW) trivial ?_
  intro Z W' t₃ hKZ hAZ hrZ hsZ hkZ hIZ
  exact from699 E hKZ hAZ hrZ (fb_ret hmU hsZ hkZ) hIZ

/-- From 499 (back from `operator new []`): the old items copied (686) unless the size is 0, freed (691) unless
null; else to 526. -/
theorem from499 (E : Ev prof F Wl L s₀ o gev gP gE fb S g0 e₂ code₂ j₂ n it ch ln I J Ok) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = spp_at.add 499) (hm : Fb S g0 Y.cpu.gpr) (hIW : I 0 W) :
    GoG prof L o gev gP gE Y t := by
  refine (c_499 prof fb).run E.c E.hfs E.hin (fun j' g' _ V' => V' = W ∧ Fr Y.cpu.gpr g' ∧
      (j' = 686 ∨ j' = 691 ∨ j' = 526)) hK hA hr
    (vc_499 (by rw [hm.2.1]; exact E.fd E.o8) (by rw [hm.2.1]; exact E.fd E.o0)
      (fun _ a _ => ⟨rfl, a, Or.inl rfl⟩) (fun _ a _ => ⟨rfl, a, Or.inr (Or.inl rfl)⟩)
      (fun _ a _ => ⟨rfl, a, Or.inr (Or.inr rfl)⟩)) ?_
  rintro j' g fl V₁ ⟨hV₁, gf, hj⟩ U t₁ hKU hAU hrU hgU -
  subst V₁ hgU
  have hmU := Fb.fr hm gf
  rcases hj with rfl | rfl | rfl
  · refine callK E hKU hAU hrU hmU.1 (lt_len (by decide)) (call_686 _) tgt_686 E.cM (E.k686 _ hIW) trivial ?_
    intro Z W' t₃ hKZ hAZ hrZ hsZ hkZ hIZ
    exact from691 E hKZ hAZ hrZ (fb_ret hmU hsZ hkZ) hIZ
  · exact from691 E hKU hAU hrU hmU hIW
  · exact from526 E hKU hAU hrU hmU hIW

/-- From 464 (the growth): `operator new []` (494), from its return to 499. -/
theorem from464 (E : Ev prof F Wl L s₀ o gev gP gE fb S g0 e₂ code₂ j₂ n it ch ln I J Ok) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = spp_at.add 464) (hm : Fb S g0 Y.cpu.gpr) (hIW : I 0 W) :
    GoG prof L o gev gP gE Y t := by
  refine (c_464 prof fb).run E.c E.hfs E.hin (fun j' g' _ V' => j' = 494 ∧ V' = W ∧ Fr Y.cpu.gpr g') hK hA hr
    (vc_464 fun _ a _ => ⟨rfl, rfl, a⟩) ?_
  rintro j' g fl V₁ ⟨rfl, hV₁, gf⟩ U t₁ hKU hAU hrU hgU -
  subst V₁ hgU
  have hmU := Fb.fr hm gf
  refine callK E hKU hAU hrU hmU.1 (lt_len (by decide)) (call_494 _) tgt_494 E.cN2 (E.k494 _ hIW) trivial ?_
  intro Z W' t₃ hKZ hAZ hrZ hsZ hkZ hIZ
  exact from499 E hKZ hAZ hrZ (fb_ret hmU hsZ hkZ) hIZ

/-- From 458: the `ja` to the throw at `0x4017c7` (`kt7`), else to 464. -/
theorem from458 (E : Ev prof F Wl L s₀ o gev gP gE fb S g0 e₂ code₂ j₂ n it ch ln I J Ok) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = spp_at.add 458) (hm : Fb S g0 Y.cpu.gpr) (hIW : I 0 W) :
    GoG prof L o gev gP gE Y t := by
  obtain ⟨cT, hinT, hT⟩ := E.cT7
  refine E.c.s_jcc_x hK hA E.hin (lt_len (by decide)) hr (ja_458 _) hinT hT tja_458 ?_ ?_
  · intro _ Y₁ t₂ hK₁ hA₁ ⟨hr₁, hg₁⟩
    exact E.kt7 W hIW Y₁ t₂ hK₁ hA₁ (by rw [hr₁, addr_add_zero]) (by rw [hg₁]; exact hm.1)
  · intro _ Y₁ t₂ hK₁ hA₁ ⟨hr₁, hg₁⟩
    exact from464 E hK₁ hA₁ hr₁ (by rw [hg₁]; exact hm) hIW

/-- From 445 (back from `name.SetFrom`): room in `_items` to 533, else to the growth (458). -/
theorem from445 (E : Ev prof F Wl L s₀ o gev gP gE fb S g0 e₂ code₂ j₂ n it ch ln I J Ok) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = spp_at.add 445) (hm : Fb S g0 Y.cpu.gpr) (hIW : I 0 W) :
    GoG prof L o gev gP gE Y t := by
  refine (c_445 prof fb).run E.c E.hfs E.hin (fun j' g' _ V' => V' = W ∧ Fr Y.cpu.gpr g' ∧ (j' = 533 ∨ j' = 458))
    hK hA hr
    (vc_445 (by rw [hm.2.1]; exact E.fd E.o12) (by rw [hm.2.1]; exact E.fd E.o8)
      (fun _ a _ => ⟨rfl, a, Or.inl rfl⟩) (fun _ a _ => ⟨rfl, a, Or.inr rfl⟩)) ?_
  rintro j' g fl V₁ ⟨hV₁, gf, hj⟩ U t₁ hKU hAU hrU hgU -
  subst V₁ hgU
  rcases hj with rfl | rfl
  · exact from533 E hKU hAU hrU (Fb.fr hm gf) hIW
  · exact from458 E hKU hAU hrU (Fb.fr hm gf) hIW

/-- From 432 (the scan's end): `name.SetFrom` (440, `rdi` = `&name`), from its return to 445. -/
theorem from432 (E : Ev prof F Wl L s₀ o gev gP gE fb S g0 e₂ code₂ j₂ n it ch ln I J Ok) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = spp_at.add 432) (hm : Fb S g0 Y.cpu.gpr) (hIW : I 0 W) :
    GoG prof L o gev gP gE Y t := by
  refine (c_432 prof fb).run E.c E.hfs E.hin (fun j' g' _ V' => j' = 440 ∧ V' = W ∧ Fr Y.cpu.gpr g' ∧
      g'.rdi = Y.cpu.gpr.r15) hK hA hr (vc_432 fun _ a b _ => ⟨rfl, rfl, a, b⟩) ?_
  rintro j' g fl V₁ ⟨rfl, hV₁, gf, gdi⟩ U t₁ hKU hAU hrU hgU -
  subst V₁ hgU
  have hmU := Fb.fr hm gf
  refine callK E hKU hAU hrU hmU.1 (lt_len (by decide)) (call_440 _) tgt_440 E.cS (E.k440 _ hIW)
    (gdi.trans hm.2.2) ?_
  intro Z W' t₃ hKZ hAZ hrZ hsZ hkZ hIZ
  exact from445 E hKZ hAZ hrZ (fb_ret hmU hsZ hkZ) hIZ

/-! ### The `Add` in the scan, to 378 -/

/-- From 362 (back from `operator new`): the item kept at `rsp + 16`; its `UString (name)` (373), to 378. -/
theorem from362 (E : Ev prof F Wl L s₀ o gev gP gE fb S g0 e₂ code₂ j₂ n it ch ln I J Ok) {i : Nat}
    (h378 : AtJ prof F Wl L s₀ o gev gP gE 378 fun g W => I 0 W ∧ Fa S g0 ln i g) :
    AtJ prof F Wl L s₀ o gev gP gE 362 fun g W => I 0 W ∧ Fa S g0 ln i g := by
  rintro Y W t hK hA hr ⟨hIW, hm⟩
  refine (c_362 prof fb).run E.c E.hfs E.hin (fun j' g' _ V' => j' = 373 ∧ I 0 V' ∧ Fk Y.cpu.gpr g') hK hA hr
    (vc_362 (by rw [hm.1]; exact E.hok _ _ E.os16q) (by rw [hm.1]; exact E.os16q) hIW E.hcl
      fun _ _ hI a _ => ⟨rfl, hI, a⟩) ?_
  rintro j' g fl V₁ ⟨rfl, hI1, gf⟩ U t₁ hKU hAU hrU hgU -
  subst hgU
  have hmU := Fa.fk hm gf
  refine callK E hKU hAU hrU hmU.1 (lt_len (by decide)) (call_373 _) tgt_373 E.cU (E.k373 _ hI1) trivial ?_
  intro Z W' t₃ hKZ hAZ hrZ hsZ hkZ hIZ
  exact h378 Z W' t₃ hKZ hAZ hrZ ⟨hIZ, fa_ret hmU hsZ hkZ⟩

/-- From 352: `operator new (16)` (357), to 362. -/
theorem from352 (E : Ev prof F Wl L s₀ o gev gP gE fb S g0 e₂ code₂ j₂ n it ch ln I J Ok) {i : Nat}
    (h378 : AtJ prof F Wl L s₀ o gev gP gE 378 fun g W => I 0 W ∧ Fa S g0 ln i g) :
    AtJ prof F Wl L s₀ o gev gP gE 352 fun g W => I 0 W ∧ Fa S g0 ln i g := by
  rintro Y W t hK hA hr ⟨hIW, hm⟩
  refine (c_352 prof fb).run E.c E.hfs E.hin (fun j' g' _ V' => j' = 357 ∧ V' = W ∧ Fk Y.cpu.gpr g') hK hA hr
    (vc_352 fun _ a _ => ⟨rfl, rfl, a⟩) ?_
  rintro j' g fl V₁ ⟨rfl, hV₁, gf⟩ U t₁ hKU hAU hrU hgU -
  subst V₁ hgU
  have hmU := Fa.fk hm gf
  refine callK E hKU hAU hrU hmU.1 (lt_len (by decide)) (call_357 _) tgt_357 E.cN (E.k357 _ hIW) trivial ?_
  intro Z W' t₃ hKZ hAZ hrZ hsZ hkZ hIZ
  exact from362 E h378 Z W' t₃ hKZ hAZ hrZ ⟨hIZ, fa_ret hmU hsZ hkZ⟩

/-- From 341: the new `_items` and `_capacity` stored; to 352. -/
theorem from341 (E : Ev prof F Wl L s₀ o gev gP gE fb S g0 e₂ code₂ j₂ n it ch ln I J Ok) {i : Nat}
    (h378 : AtJ prof F Wl L s₀ o gev gP gE 378 fun g W => I 0 W ∧ Fa S g0 ln i g) :
    AtJ prof F Wl L s₀ o gev gP gE 341 fun g W => I 0 W ∧ Fa S g0 ln i g := by
  rintro Y W t hK hA hr ⟨hIW, hm⟩
  refine (c_341 prof fb).run E.c E.hfs E.hin (fun j' g' _ V' => j' = 352 ∧ I 0 V' ∧ Fk Y.cpu.gpr g') hK hA hr
    (vc_341 (by rw [hm.1]; exact E.fd E.os16) (by rw [hm.2.1]; exact E.hok _ _ E.o0)
      (by rw [hm.2.1]; exact E.hok _ _ E.o12) (by rw [hm.2.1]; exact E.o0) (by rw [hm.2.1]; exact E.o12) hIW E.hcl
      fun _ _ hI a _ => ⟨rfl, hI, a⟩) ?_
  rintro j' g fl V₁ ⟨rfl, hI1, gf⟩ U t₁ hKU hAU hrU hgU -
  subst hgU
  exact from352 E h378 U V₁ t₁ hKU hAU hrU ⟨hI1, Fa.fk hm gf⟩

/-- From 653 (back from `delete []` of the old items): to 341. -/
theorem from653 (E : Ev prof F Wl L s₀ o gev gP gE fb S g0 e₂ code₂ j₂ n it ch ln I J Ok) {i : Nat}
    (h378 : AtJ prof F Wl L s₀ o gev gP gE 378 fun g W => I 0 W ∧ Fa S g0 ln i g) :
    AtJ prof F Wl L s₀ o gev gP gE 653 fun g W => I 0 W ∧ Fa S g0 ln i g := by
  rintro Y W t hK hA hr ⟨hIW, hm⟩
  refine (c_653 prof fb).run E.c E.hfs E.hin (fun j' g' _ V' => j' = 341 ∧ V' = W ∧ Fk Y.cpu.gpr g') hK hA hr
    (vc_653 (by rw [hm.1]; exact E.fd E.os24) fun _ a _ => ⟨rfl, rfl, a⟩) ?_
  rintro j' g fl V₁ ⟨rfl, hV₁, gf⟩ U t₁ hKU hAU hrU hgU -
  subst V₁ hgU
  exact from341 E h378 U W t₁ hKU hAU hrU ⟨hIW, Fa.fk hm gf⟩

/-- From 640: the new array kept at `rsp + 24`; `delete []` of the old items (648), to 653. -/
theorem from640 (E : Ev prof F Wl L s₀ o gev gP gE fb S g0 e₂ code₂ j₂ n it ch ln I J Ok) {i : Nat}
    (h378 : AtJ prof F Wl L s₀ o gev gP gE 378 fun g W => I 0 W ∧ Fa S g0 ln i g) :
    AtJ prof F Wl L s₀ o gev gP gE 640 fun g W => I 0 W ∧ Fa S g0 ln i g := by
  rintro Y W t hK hA hr ⟨hIW, hm⟩
  refine (c_640 prof fb).run E.c E.hfs E.hin (fun j' g' _ V' => j' = 648 ∧ I 0 V' ∧ Fk Y.cpu.gpr g') hK hA hr
    (vc_640 (by rw [hm.1]; exact E.hok _ _ E.os24) (by rw [hm.1]; exact E.os24) hIW E.hcl
      fun _ _ hI a _ => ⟨rfl, hI, a⟩) ?_
  rintro j' g fl V₁ ⟨rfl, hI1, gf⟩ U t₁ hKU hAU hrU hgU -
  subst hgU
  have hmU := Fa.fk hm gf
  refine callK E hKU hAU hrU hmU.1 (lt_len (by decide)) (call_648 _) tgt_648 E.cD (E.k648 _ hI1) trivial ?_
  intro Z W' t₃ hKZ hAZ hrZ hsZ hkZ hIZ
  exact from653 E h378 Z W' t₃ hKZ hAZ hrZ ⟨hIZ, fa_ret hmU hsZ hkZ⟩

/-- From 632 (back from `memcpy`): to 640. -/
theorem from632 (E : Ev prof F Wl L s₀ o gev gP gE fb S g0 e₂ code₂ j₂ n it ch ln I J Ok) {i : Nat}
    (h378 : AtJ prof F Wl L s₀ o gev gP gE 378 fun g W => I 0 W ∧ Fa S g0 ln i g) :
    AtJ prof F Wl L s₀ o gev gP gE 632 fun g W => I 0 W ∧ Fa S g0 ln i g := by
  rintro Y W t hK hA hr ⟨hIW, hm⟩
  refine (c_632 prof fb).run E.c E.hfs E.hin (fun j' g' _ V' => j' = 640 ∧ V' = W ∧ Fk Y.cpu.gpr g') hK hA hr
    (vc_632 (by rw [hm.1]; exact E.fd E.os24) fun _ a _ => ⟨rfl, rfl, a⟩) ?_
  rintro j' g fl V₁ ⟨rfl, hV₁, gf⟩ U t₁ hKU hAU hrU hgU -
  subst V₁ hgU
  exact from640 E h378 U W t₁ hKU hAU hrU ⟨hIW, Fa.fk hm gf⟩

/-- From 314 (back from `operator new []`): the old items copied (627) unless the size is 0, freed (640) unless
null; else to 341. -/
theorem from314 (E : Ev prof F Wl L s₀ o gev gP gE fb S g0 e₂ code₂ j₂ n it ch ln I J Ok) {i : Nat}
    (h378 : AtJ prof F Wl L s₀ o gev gP gE 378 fun g W => I 0 W ∧ Fa S g0 ln i g) :
    AtJ prof F Wl L s₀ o gev gP gE 314 fun g W => I 0 W ∧ Fa S g0 ln i g := by
  rintro Y W t hK hA hr ⟨hIW, hm⟩
  refine (c_314 prof fb).run E.c E.hfs E.hin (fun j' g' _ V' => I 0 V' ∧ Fk Y.cpu.gpr g' ∧
      (j' = 627 ∨ j' = 640 ∨ j' = 341)) hK hA hr
    (vc_314 (by rw [hm.2.1]; exact E.fd E.o8) (by rw [hm.2.1]; exact E.fd E.o0)
      (by rw [hm.1]; exact E.hok _ _ E.os24) (by rw [hm.1]; exact E.os24) hIW E.hcl
      (fun _ _ hI a _ => ⟨hI, a, Or.inl rfl⟩) (fun _ _ hI a _ => ⟨hI, a, Or.inr (Or.inl rfl)⟩)
      (fun _ _ hI a _ => ⟨hI, a, Or.inr (Or.inr rfl)⟩)) ?_
  rintro j' g fl V₁ ⟨hI1, gf, hj⟩ U t₁ hKU hAU hrU hgU -
  subst hgU
  have hmU := Fa.fk hm gf
  rcases hj with rfl | rfl | rfl
  · refine callK E hKU hAU hrU hmU.1 (lt_len (by decide)) (call_627 _) tgt_627 E.cM (E.k627 _ hI1) trivial ?_
    intro Z W' t₃ hKZ hAZ hrZ hsZ hkZ hIZ
    exact from632 E h378 Z W' t₃ hKZ hAZ hrZ ⟨hIZ, fa_ret hmU hsZ hkZ⟩
  · exact from640 E h378 U V₁ t₁ hKU hAU hrU ⟨hI1, hmU⟩
  · exact from341 E h378 U V₁ t₁ hKU hAU hrU ⟨hI1, hmU⟩

/-- From 278 (the growth): the new capacity kept at `rsp + 16`; `operator new []` (309), to 314. -/
theorem from278 (E : Ev prof F Wl L s₀ o gev gP gE fb S g0 e₂ code₂ j₂ n it ch ln I J Ok) {i : Nat}
    (h378 : AtJ prof F Wl L s₀ o gev gP gE 378 fun g W => I 0 W ∧ Fa S g0 ln i g) :
    AtJ prof F Wl L s₀ o gev gP gE 278 fun g W => I 0 W ∧ Fa S g0 ln i g := by
  rintro Y W t hK hA hr ⟨hIW, hm⟩
  refine (c_278 prof fb).run E.c E.hfs E.hin (fun j' g' _ V' => j' = 309 ∧ I 0 V' ∧ Fk Y.cpu.gpr g') hK hA hr
    (vc_278 (by rw [hm.1]; exact E.hok _ _ E.os16) (by rw [hm.1]; exact E.os16) hIW E.hcl
      fun _ _ hI a _ => ⟨rfl, hI, a⟩) ?_
  rintro j' g fl V₁ ⟨rfl, hI1, gf⟩ U t₁ hKU hAU hrU hgU -
  subst hgU
  have hmU := Fa.fk hm gf
  refine callK E hKU hAU hrU hmU.1 (lt_len (by decide)) (call_309 _) tgt_309 E.cN2 (E.k309 _ hI1) trivial ?_
  intro Z W' t₃ hKZ hAZ hrZ hsZ hkZ hIZ
  exact from314 E h378 Z W' t₃ hKZ hAZ hrZ ⟨hIZ, fa_ret hmU hsZ hkZ⟩

/-- From 272: the `ja` to the throw at `0x4017c2` (`kt2`), else to 278. -/
theorem from272 (E : Ev prof F Wl L s₀ o gev gP gE fb S g0 e₂ code₂ j₂ n it ch ln I J Ok) {i : Nat}
    (h378 : AtJ prof F Wl L s₀ o gev gP gE 378 fun g W => I 0 W ∧ Fa S g0 ln i g) :
    AtJ prof F Wl L s₀ o gev gP gE 272 fun g W => I 0 W ∧ Fa S g0 ln i g := by
  rintro Y W t hK hA hr ⟨hIW, hm⟩
  obtain ⟨cT, hinT, hT⟩ := E.cT2
  refine E.c.s_jcc_x hK hA E.hin (lt_len (by decide)) hr (ja_272 _) hinT hT tja_272 ?_ ?_
  · intro _ Y₁ t₂ hK₁ hA₁ ⟨hr₁, hg₁⟩
    exact E.kt2 W hIW Y₁ t₂ hK₁ hA₁ (by rw [hr₁, addr_add_zero]) (by rw [hg₁]; exact hm.1)
  · intro _ Y₁ t₂ hK₁ hA₁ ⟨hr₁, hg₁⟩
    exact from278 E h378 Y₁ W t₂ hK₁ hA₁ hr₁ ⟨hIW, by rw [hg₁]; exact hm⟩

/-- From 259 (back from `name.SetFrom`): room in `_items` to 352, else to the growth (272). -/
theorem from259 (E : Ev prof F Wl L s₀ o gev gP gE fb S g0 e₂ code₂ j₂ n it ch ln I J Ok) {i : Nat}
    (h378 : AtJ prof F Wl L s₀ o gev gP gE 378 fun g W => I 0 W ∧ Fa S g0 ln i g) :
    AtJ prof F Wl L s₀ o gev gP gE 259 fun g W => I 0 W ∧ Fa S g0 ln i g := by
  rintro Y W t hK hA hr ⟨hIW, hm⟩
  refine (c_259 prof fb).run E.c E.hfs E.hin (fun j' g' _ V' => V' = W ∧ Fk Y.cpu.gpr g' ∧ (j' = 352 ∨ j' = 272))
    hK hA hr
    (vc_259 (by rw [hm.2.1]; exact E.fd E.o12) (by rw [hm.2.1]; exact E.fd E.o8)
      (fun _ a _ => ⟨rfl, a, Or.inl rfl⟩) (fun _ a _ => ⟨rfl, a, Or.inr rfl⟩)) ?_
  rintro j' g fl V₁ ⟨hV₁, gf, hj⟩ U t₁ hKU hAU hrU hgU -
  subst V₁ hgU
  rcases hj with rfl | rfl
  · exact from352 E h378 U W t₁ hKU hAU hrU ⟨hIW, Fa.fk hm gf⟩
  · exact from272 E h378 U W t₁ hKU hAU hrU ⟨hIW, Fa.fk hm gf⟩

/-- 254 (`rdi` = `&name`): `name.SetFrom` (254), from its return to 259. -/
theorem R254 (E : Ev prof F Wl L s₀ o gev gP gE fb S g0 e₂ code₂ j₂ n it ch ln I J Ok) {i : Nat}
    (h378 : AtJ prof F Wl L s₀ o gev gP gE 378 fun g W => I 0 W ∧ Fa S g0 ln i g) :
    AtJ prof F Wl L s₀ o gev gP gE 254 fun g W => (I 0 W ∧ Fa S g0 ln i g) ∧ g.rdi = aR S + 32#64 := by
  rintro Y W t hK hA hr ⟨⟨hIW, hm⟩, hdi⟩
  refine callK E hK hA hr hm.1 (lt_len (by decide)) (call_254 _) tgt_254 E.cS (E.k254 _ hIW) hdi ?_
  intro Z W' t₃ hKZ hAZ hrZ hsZ hkZ hIZ
  exact from259 E h378 Z W' t₃ hKZ hAZ hrZ ⟨hIZ, fa_ret hm hsZ hkZ⟩

/-! ### The scan -/

/-- 378 at the step `i` with `i + 1 < len`: the slot, the size, `rbx` = `i + 1`, `rax` = `path._chars`; to 221 with
the step `i + 1`. -/
theorem S378c (E : Ev prof F Wl L s₀ o gev gP gE fb S g0 e₂ code₂ j₂ n it ch ln I J Ok) (i : Nat)
    (hlt : i + 1 < ln.toNat)
    (hnx : AtJ prof F Wl L s₀ o gev gP gE 221 fun g W => I 0 W ∧ Fs S g0 ln ch (i + 1) g) :
    AtJ prof F Wl L s₀ o gev gP gE 378 fun g W => I 0 W ∧ Fa S g0 ln i g := by
  rintro Y W t hK hA hr ⟨hIW, hm⟩
  obtain ⟨ms, mp, m15, mx, m12, m14⟩ := hm
  have hl : ln.toNat < 4294967296 := ln.isLt
  have hc := sGo (r := Y.cpu.gpr.r12) (b := Y.cpu.gpr.r14 + 1#64) (by rw [m12]; exact sLn ln)
    (by rw [m14]; exact sR14 i (by omega)) hlt
  refine (c_378 prof fb).run E.c E.hfs E.hin (fun j' g' _ V' => j' = 221 ∧ I 0 V' ∧ Fr Y.cpu.gpr g' ∧
      g'.rbx = Y.cpu.gpr.rbx + 1#64 ∧ g'.r12 = Y.cpu.gpr.r12 ∧ g'.rax = rdq(V', rdq(V', Y.cpu.gpr.rsp + 8#64)))
    hK hA hr
    (vc_378c (by rw [mp]; exact E.fd E.o8) (by rw [mp]; exact E.fd E.o0) (by rw [mp]; exact E.hok _ _ E.o8)
      (by rw [mp]; exact E.o8) (by rw [ms]; exact E.fd E.os16q) (by rw [mp]; exact E.hok _ _ (E.hsl W hIW))
      (by rw [mp]; exact E.hsl W hIW) (by rw [ms]; exact E.f8s)
      (fun W' hW' => by rw [ms, (E.hI W' hW').2.2.2.2.2.2.2.2]; exact E.fp0) hIW E.hcl hc
      fun _ _ hI a b d e _ => ⟨rfl, hI, a, b, d, e⟩) ?_
  rintro j' g fl V₁ ⟨rfl, hI1, gf, gbx, g12, gax⟩ U t₁ hKU hAU hrU hgU -
  subst hgU
  exact hnx U V₁ t₁ hKU hAU hrU ⟨hI1, gf.1.trans ms, gf.2.1.trans mp, gf.2.2.trans m15,
    by rw [gbx, mx]; exact sInc i, g12.trans m12,
    by rw [gax, ms, (E.hI V₁ hI1).2.2.2.2.2.2.2.2]; exact E.hch V₁ hI1⟩

/-- 378 at the step `i` with `i + 1 = len`: the slot, the size; to 432. -/
theorem S378x (E : Ev prof F Wl L s₀ o gev gP gE fb S g0 e₂ code₂ j₂ n it ch ln I J Ok) (i : Nat)
    (hi : i + 1 = ln.toNat) :
    AtJ prof F Wl L s₀ o gev gP gE 378 fun g W => I 0 W ∧ Fa S g0 ln i g := by
  rintro Y W t hK hA hr ⟨hIW, hm⟩
  obtain ⟨ms, mp, m15, mx, m12, m14⟩ := hm
  have hl : ln.toNat < 4294967296 := ln.isLt
  have hc := sEnd (r := Y.cpu.gpr.r12) (b := Y.cpu.gpr.r14 + 1#64) (by rw [m12]; exact sLn ln)
    (by rw [m14]; exact sR14 i (by omega)) hi
  refine (c_378 prof fb).run E.c E.hfs E.hin (fun j' g' _ V' => j' = 432 ∧ I 0 V' ∧ Fr Y.cpu.gpr g') hK hA hr
    (vc_378x (by rw [mp]; exact E.fd E.o8) (by rw [mp]; exact E.fd E.o0) (by rw [mp]; exact E.hok _ _ E.o8)
      (by rw [mp]; exact E.o8) (by rw [ms]; exact E.fd E.os16q) (by rw [mp]; exact E.hok _ _ (E.hsl W hIW))
      (by rw [mp]; exact E.hsl W hIW) (by rw [ms]; exact E.f8s)
      (fun W' hW' => by rw [ms, (E.hI W' hW').2.2.2.2.2.2.2.2]; exact E.fp0) hIW E.hcl hc
      fun _ _ hI a _ => ⟨rfl, hI, a⟩) ?_
  rintro j' g fl V₁ ⟨rfl, hI1, gf⟩ U t₁ hKU hAU hrU hgU -
  subst hgU
  exact from432 E hKU hAU hrU ⟨gf.1.trans ms, gf.2.1.trans mp, gf.2.2.trans m15⟩ hI1

/-- 221 at the step `i` with `i + 1 < len`: a char not `'/'` to 221 with the step `i + 1`, a `'/'` to the `Add`
(254, `R254`) and 378 (`S378c`). -/
theorem S221c (E : Ev prof F Wl L s₀ o gev gP gE fb S g0 e₂ code₂ j₂ n it ch ln I J Ok) (i : Nat)
    (hlt : i + 1 < ln.toNat)
    (hnx : AtJ prof F Wl L s₀ o gev gP gE 221 fun g W => I 0 W ∧ Fs S g0 ln ch (i + 1) g) :
    AtJ prof F Wl L s₀ o gev gP gE 221 fun g W => I 0 W ∧ Fs S g0 ln ch i g := by
  rintro Y W t hK hA hr ⟨hIW, hm⟩
  obtain ⟨ms, mp, m15, mx, m12, ma⟩ := hm
  have hl : ln.toNat < 4294967296 := ln.isLt
  have hc := sGo (r := Y.cpu.gpr.r12) (b := Y.cpu.gpr.rbx + 1#64) (by rw [m12]; exact sLn ln)
    (by rw [mx]; exact sI1 i (by omega)) hlt
  refine (c_221 prof fb).run E.c E.hfs E.hin (fun j' g' _ V' => V' = W ∧ Fr Y.cpu.gpr g' ∧
      g'.rax = Y.cpu.gpr.rax ∧ g'.r12 = Y.cpu.gpr.r12 ∧ ((j' = 221 ∧ g'.rbx = Y.cpu.gpr.rbx + 1#64) ∨
        (j' = 254 ∧ g'.rbx = Y.cpu.gpr.rbx ∧ g'.r14 = BitVec.setWidth 64 (BitVec.setWidth 32 Y.cpu.gpr.rbx) ∧
          g'.rdi = Y.cpu.gpr.r15))) hK hA hr
    (vc_221c (by rw [ma, mx]; exact E.fc i (by omega)) hc (fun _ a b d e _ => ⟨rfl, a, b, e, Or.inl ⟨rfl, d⟩⟩)
      (fun _ a b d e f h _ => ⟨rfl, a, b, e, Or.inr ⟨rfl, d, f, h⟩⟩)) ?_
  rintro j' g fl V₁ ⟨hV₁, gf, gax, g12, hj⟩ U t₁ hKU hAU hrU hgU -
  subst V₁ hgU
  rcases hj with ⟨rfl, gbx⟩ | ⟨rfl, gbx, g14, gdi⟩
  · exact hnx U W t₁ hKU hAU hrU ⟨hIW, gf.1.trans ms, gf.2.1.trans mp, gf.2.2.trans m15,
      by rw [gbx, mx]; exact sInc i, g12.trans m12, gax.trans ma⟩
  · exact R254 E (S378c E i hlt hnx) U W t₁ hKU hAU hrU ⟨⟨hIW, gf.1.trans ms, gf.2.1.trans mp, gf.2.2.trans m15,
      gbx.trans mx, g12.trans m12, by rw [g14, mx]⟩, gdi.trans (gf.2.2.trans m15)⟩

/-- 221 at the step `i` with `i + 1 = len`: a char not `'/'` to 432, a `'/'` to the `Add` (254, `R254`) and 378
(`S378x`). -/
theorem S221x (E : Ev prof F Wl L s₀ o gev gP gE fb S g0 e₂ code₂ j₂ n it ch ln I J Ok) (i : Nat)
    (hi : i + 1 = ln.toNat) :
    AtJ prof F Wl L s₀ o gev gP gE 221 fun g W => I 0 W ∧ Fs S g0 ln ch i g := by
  rintro Y W t hK hA hr ⟨hIW, hm⟩
  obtain ⟨ms, mp, m15, mx, m12, ma⟩ := hm
  have hl : ln.toNat < 4294967296 := ln.isLt
  have hc := sEnd (r := Y.cpu.gpr.r12) (b := Y.cpu.gpr.rbx + 1#64) (by rw [m12]; exact sLn ln)
    (by rw [mx]; exact sI1 i (by omega)) hi
  refine (c_221 prof fb).run E.c E.hfs E.hin (fun j' g' _ V' => V' = W ∧ Fr Y.cpu.gpr g' ∧
      (j' = 432 ∨ (j' = 254 ∧ g'.rax = Y.cpu.gpr.rax ∧ g'.rbx = Y.cpu.gpr.rbx ∧ g'.r12 = Y.cpu.gpr.r12 ∧
        g'.r14 = BitVec.setWidth 64 (BitVec.setWidth 32 Y.cpu.gpr.rbx) ∧ g'.rdi = Y.cpu.gpr.r15))) hK hA hr
    (vc_221x (by rw [ma, mx]; exact E.fc i (by omega)) hc (fun _ a _ => ⟨rfl, a, Or.inl rfl⟩)
      (fun _ a b d e f h _ => ⟨rfl, a, Or.inr ⟨rfl, b, d, e, f, h⟩⟩)) ?_
  rintro j' g fl V₁ ⟨hV₁, gf, hj⟩ U t₁ hKU hAU hrU hgU -
  subst V₁ hgU
  rcases hj with rfl | ⟨rfl, gax, gbx, g12, g14, gdi⟩
  · exact from432 E hKU hAU hrU ⟨gf.1.trans ms, gf.2.1.trans mp, gf.2.2.trans m15⟩ hIW
  · exact R254 E (S378x E i hi) U W t₁ hKU hAU hrU ⟨⟨hIW, gf.1.trans ms, gf.2.1.trans mp, gf.2.2.trans m15,
      gbx.trans mx, g12.trans m12, by rw [g14, mx]⟩, gdi.trans (gf.2.2.trans m15)⟩

/-- The scan, by induction on the steps left. -/
theorem L221 (E : Ev prof F Wl L s₀ o gev gP gE fb S g0 e₂ code₂ j₂ n it ch ln I J Ok) : ∀ d i,
    i + d + 1 = ln.toNat → AtJ prof F Wl L s₀ o gev gP gE 221 fun g W => I 0 W ∧ Fs S g0 ln ch i g := by
  intro d
  induction d with
  | zero => exact fun i hi => S221x E i hi
  | succ d ih => exact fun i hi => S221c E i (by omega) (ih (i + 1) (by omega))

/-- From 189 (back from `name`'s constructor, `rbx` = `path`, `r12` = `len` not 0): `rax` = `path._chars`,
`rbx` = 0; the scan from the step 0. -/
theorem from189 (E : Ev prof F Wl L s₀ o gev gP gE fb S g0 e₂ code₂ j₂ n it ch ln I J Ok) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = spp_at.add 189) (hm : Fc S g0 Y.cpu.gpr)
    (h15 : Y.cpu.gpr.r15 = aR S + 32#64) (hbx : Y.cpu.gpr.rbx = g0.rdi) (h12 : Y.cpu.gpr.r12 = BitVec.setWidth 64 ln)
    (hpos : 0 < ln.toNat) (hIW : I 0 W) :
    GoG prof L o gev gP gE Y t := by
  refine (c_189 prof fb).run E.c E.hfs E.hin (fun j' g' _ V' => j' = 221 ∧ V' = W ∧ Fr Y.cpu.gpr g' ∧
      g'.rax = rdq(W, Y.cpu.gpr.rbx) ∧ g'.rbx = 0#64 ∧ g'.r12 = Y.cpu.gpr.r12) hK hA hr
    (vc_189 (by rw [hbx]; exact E.fp0) fun _ a b d e _ => ⟨rfl, rfl, a, b, d, e⟩) ?_
  rintro j' g fl V₁ ⟨rfl, hV₁, gf, gax, gbx, g12⟩ U t₁ hKU hAU hrU hgU -
  subst V₁ hgU
  exact L221 E (ln.toNat - 1) 0 (by omega) U W t₁ hKU hAU hrU ⟨hIW, gf.1.trans hm.1, gf.2.1.trans hm.2,
    gf.2.2.trans h15, gbx.trans rfl, g12.trans h12, by rw [gax, hbx]; exact E.hch W hIW⟩

/-- From 114 (the clear's end, bytes with `I 0`): the size 0; `len` 0 to 135, else `name`'s constructor (184),
from its return to 189. -/
theorem from114 (E : Ev prof F Wl L s₀ o gev gP gE fb S g0 e₂ code₂ j₂ n it ch ln I J Ok) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = spp_at.add 114) (hm : Fc S g0 Y.cpu.gpr) (hIW : I 0 W) :
    GoG prof L o gev gP gE Y t := by
  have hp8 : rdq(W, Y.cpu.gpr.rsp + 8#64) = g0.rdi := by rw [hm.1]; exact (E.hI W hIW).2.2.2.2.2.2.2.2
  refine (c_114 prof fb).run E.c E.hfs E.hin (fun j' g' _ V' => I 0 V' ∧ g'.rsp = Y.cpu.gpr.rsp ∧
      g'.rbp = Y.cpu.gpr.rbp ∧ (j' = 135 ∨ (j' = 184 ∧ ¬rdd(V', g0.rdi + 8#64) = 0 ∧ g'.rbx = g0.rdi ∧
        g'.r12 = BitVec.setWidth 64 rdd(V', g0.rdi + 8#64) ∧ g'.r15 = Y.cpu.gpr.rsp + 32#64 ∧
        g'.rdi = Y.cpu.gpr.rsp + 32#64))) hK hA hr
    (vc_114 (by rw [hm.1]; exact E.f8s) (by rw [hm.2]; exact E.hok _ _ E.o8) (by rw [hm.2]; exact E.o8) hIW E.hcl
      (by rw [hp8]; exact E.fp8) (fun _ _ hI _ a _ => ⟨hI, a.1, a.2.1, Or.inl rfl⟩)
      (fun _ _ hI hz a b d e f h _ => ⟨hI, a, b, Or.inr ⟨rfl, by rw [hp8] at hz; exact hz, d.trans hp8,
        by rw [e, hp8], f, h⟩⟩)) ?_
  rintro j' g fl V₁ ⟨hI1, gs, gp, hj⟩ U t₁ hKU hAU hrU hgU -
  subst hgU
  rcases hj with rfl | ⟨rfl, hz, gbx, g12, g15, gdi⟩
  · exact tail135 E hKU hAU hrU (gs.trans hm.1) hI1
  · have hsU : U.cpu.gpr.rsp = aR S := gs.trans hm.1
    have hln := E.hln V₁ hI1
    rw [hm.1] at g15 gdi
    rw [hln] at hz g12
    have hpos : 0 < ln.toNat := by
      have : ln.toNat ≠ 0 := fun e => hz (BitVec.eq_of_toNat_eq (e.trans rfl))
      omega
    refine callK E hKU hAU hrU hsU (lt_len (by decide)) (call_184 _) tgt_184 E.cC (E.k184 _ hI1) gdi ?_
    intro Z W' t₃ hKZ hAZ hrZ hsZ hkZ hIZ
    exact from189 E hKZ hAZ hrZ ⟨hsZ, hkZ.2.1.trans (gp.trans hm.2)⟩ (hkZ.2.2.2.2.2.trans g15) (hkZ.1.trans gbx)
      (hkZ.2.2.1.trans g12) hpos hIZ

/-! ### The clear -/

/-- 91 (the step `k`, the item `p` with null or freed chars): `operator delete (p, 16)` (`k99`), from its return to
104. -/
theorem A91 (E : Ev prof F Wl L s₀ o gev gP gE fb S g0 e₂ code₂ j₂ n it ch ln I J Ok) (k : Nat) (hk : k < n)
    (p : BitVec 64) (hp : p ≠ 0)
    (h104 : AtJ prof F Wl L s₀ o gev gP gE 104 fun g W => I k W ∧ Fc S g0 g ∧ g.rbx = BitVec.ofNat 64 (8 * k)) :
    AtJ prof F Wl L s₀ o gev gP gE 91 fun g W => J k p W ∧ Fc S g0 g ∧ g.rbx = BitVec.ofNat 64 (8 * k) ∧
      g.r12 = p := by
  rintro Y W t hK hA hr ⟨hJ, hm, hb, h12⟩
  refine (c_91 prof fb).run E.c E.hfs E.hin (fun j' g' _ V' => j' = 99 ∧ V' = W ∧ Fr Y.cpu.gpr g' ∧
      g'.rbx = Y.cpu.gpr.rbx ∧ g'.rdi = Y.cpu.gpr.r12 ∧ g'.rsi = 16#64) hK hA hr
    (vc_91 fun _ a b d e _ => ⟨rfl, rfl, a, b, d, e⟩) ?_
  rintro j' g fl V₁ ⟨rfl, hV₁, gf, gbx, gdi, gsi⟩ U t₁ hKU hAU hrU hgU -
  subst V₁ hgU
  have hmU := Fc.fr hm gf
  refine callK E hKU hAU hrU hmU.1 (lt_len (by decide)) (call_99 _) tgt_99 E.cE (E.k99 k hk p W hp hJ)
    ⟨gdi.trans h12, gsi⟩ ?_
  intro Z W' t₃ hKZ hAZ hrZ hsZ hkZ hIZ
  exact h104 Z W' t₃ hKZ hAZ hrZ ⟨hIZ, fc_ret hmU hsZ hkZ, hkZ.1.trans (gbx.trans hb)⟩

/-- 64, the step `k` (`rbx` = `8 k`): the item `p` = `_items[k]`; null to 104, else its chars freed unless null
(`k86`) and to 91. -/
theorem B64 (E : Ev prof F Wl L s₀ o gev gP gE fb S g0 e₂ code₂ j₂ n it ch ln I J Ok) (k : Nat) (hk : k < n)
    (h104 : AtJ prof F Wl L s₀ o gev gP gE 104 fun g W => I k W ∧ Fc S g0 g ∧ g.rbx = BitVec.ofNat 64 (8 * k)) :
    AtJ prof F Wl L s₀ o gev gP gE 64 fun g W => I (k + 1) W ∧ Fc S g0 g ∧ g.rbx = BitVec.ofNat 64 (8 * k) := by
  rintro Y W t hK hA hr ⟨hIk, hm, hb⟩
  have hea : it + Y.cpu.gpr.rbx = it + BitVec.ofNat 64 (8 * k) := by rw [hb]
  refine (c_64 prof fb).run E.c E.hfs E.hin (fun j' g' _ V' => V' = W ∧ Fr Y.cpu.gpr g' ∧
      g'.rbx = Y.cpu.gpr.rbx ∧ ((pk W it k = 0 ∧ j' = 104) ∨
        (pk W it k ≠ 0 ∧ rdq(W, pk W it k) = 0 ∧ j' = 91 ∧ g'.r12 = pk W it k) ∨
        (pk W it k ≠ 0 ∧ rdq(W, pk W it k) ≠ 0 ∧ j' = 86 ∧ g'.r12 = pk W it k ∧ g'.rdi = rdq(W, pk W it k))))
    hK hA hr
    (vc_64 (it := it) (p := pk W it k) (q := rdq(W, pk W it k)) (by rw [hm.2]; exact E.hIt k hk W hIk)
      (by rw [hm.2]; exact E.fd E.o0) (by rw [hea]) (by rw [hea]; exact E.fe k hk) rfl (E.fp k hk W hIk)
      (fun h0 _ a b _ => ⟨rfl, a, b, Or.inl ⟨h0, rfl⟩⟩)
      (fun h0 hq _ a b d _ => ⟨rfl, a, b, Or.inr (Or.inl ⟨h0, hq, rfl, d⟩)⟩)
      (fun h0 hq _ a b d e _ => ⟨rfl, a, b, Or.inr (Or.inr ⟨h0, hq, rfl, d, e⟩)⟩)) ?_
  rintro j' g fl V₁ ⟨hV₁, gf, gbx, hj⟩ U t₁ hKU hAU hrU hgU -
  subst V₁ hgU
  have hmU := Fc.fr hm gf
  have hbU : U.cpu.gpr.rbx = BitVec.ofNat 64 (8 * k) := gbx.trans hb
  rcases hj with ⟨hp0, rfl⟩ | ⟨hp0, hq0, rfl, g12⟩ | ⟨hp0, hq0, rfl, g12, gdi⟩
  · exact h104 U W t₁ hKU hAU hrU ⟨E.hP0 k hk W hIk hp0, hmU, hbU⟩
  · exact A91 E k hk _ hp0 h104 U W t₁ hKU hAU hrU ⟨E.hQ0 k hk W hIk hp0 hq0, hmU, hbU, g12⟩
  · refine callK E hKU hAU hrU hmU.1 (lt_len (by decide)) (call_86 _) tgt_86 E.cD (E.k86 k hk W hIk hp0 hq0)
      gdi ?_
    intro Z W' t₃ hKZ hAZ hrZ hsZ hkZ hJZ
    exact A91 E k hk _ hp0 h104 Z W' t₃ hKZ hAZ hrZ
      ⟨hJZ, fc_ret hmU hsZ hkZ, hkZ.1.trans hbU, hkZ.2.2.1.trans g12⟩

/-- 104, the step `k`: `rbx` -= 8; after the step 0 to 114, else to 64 with the step `k - 1` (`hnx`). -/
theorem S104 (E : Ev prof F Wl L s₀ o gev gP gE fb S g0 e₂ code₂ j₂ n it ch ln I J Ok) (k : Nat) (hk : k < n)
    (hnx : ∀ k', k = k' + 1 → AtJ prof F Wl L s₀ o gev gP gE 64 fun g W => I (k' + 1) W ∧ Fc S g0 g ∧
      g.rbx = BitVec.ofNat 64 (8 * k')) :
    AtJ prof F Wl L s₀ o gev gP gE 104 fun g W => I k W ∧ Fc S g0 g ∧ g.rbx = BitVec.ofNat 64 (8 * k) := by
  rintro Y W t hK hA hr ⟨hIk, hm, hb⟩
  have hn := E.hn
  cases k with
  | zero =>
    refine (c_104 prof fb).run E.c E.hfs E.hin (fun j' g' _ V' => j' = 114 ∧ V' = W ∧ Fr Y.cpu.gpr g') hK hA hr
      (vc_104 (fun _ _ a _ => ⟨rfl, rfl, a⟩)
        (fun hne => absurd (show Y.cpu.gpr.rbx - 8#64 = 18446744073709551608#64 by rw [hb]; exact rb_last) hne))
      ?_
    rintro j' g fl V₁ ⟨rfl, hV₁, gf⟩ U t₁ hKU hAU hrU hgU -
    subst V₁ hgU
    exact from114 E hKU hAU hrU (Fc.fr hm gf) hIk
  | succ k =>
    have hne : ¬Y.cpu.gpr.rbx - 8#64 = 18446744073709551608#64 := by
      rw [hb, rb_step k (by omega)]; exact rb_ne k (by omega)
    refine (c_104 prof fb).run E.c E.hfs E.hin (fun j' g' _ V' => j' = 64 ∧ V' = W ∧ Fr Y.cpu.gpr g' ∧
        g'.rbx = Y.cpu.gpr.rbx - 8#64) hK hA hr
      (vc_104 (fun hc => absurd hc hne) fun _ _ a b _ => ⟨rfl, rfl, a, b⟩) ?_
    rintro j' g fl V₁ ⟨rfl, hV₁, gf, gbx⟩ U t₁ hKU hAU hrU hgU -
    subst V₁ hgU
    exact hnx k rfl U W t₁ hKU hAU hrU ⟨hIk, Fc.fr hm gf, by rw [gbx, hb]; exact rb_step k (by omega)⟩

/-- The clear, by induction on the step. -/
theorem L64 (E : Ev prof F Wl L s₀ o gev gP gE fb S g0 e₂ code₂ j₂ n it ch ln I J Ok) : ∀ k, k < n →
    AtJ prof F Wl L s₀ o gev gP gE 64 fun g W => I (k + 1) W ∧ Fc S g0 g ∧ g.rbx = BitVec.ofNat 64 (8 * k) := by
  intro k
  induction k with
  | zero => exact fun hk => B64 E 0 hk (S104 E 0 hk fun k' e => absurd e (by omega))
  | succ k ih =>
    exact fun hk => B64 E (k + 1) hk (S104 E (k + 1) hk fun k' e => by
      obtain rfl : k = k' := by omega
      exact ih (by omega))

end Runs

variable {prof : Profile} {F : Footprint} {Wl : List Rgn} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {X : State} {t : Nat} {V : Addr → Byte}

/-- `SplitPathToParts (path, pathParts)` (`path` = `rdi`, `pathParts` = `rsi`) from its entry, `fb` the `fs` base:
the pushes' slots, the slots of `path` and the guard (`hw8`, `hw56`) and the calls' return address slot in what the
run may store into; the guard at `fs:0x28`, `name`'s chars pointer (`f32`), the return address, `path`'s fields
(`fp0`, `fp8`), its chars (`fc`) readable. The guard read is `cn` (`hcn`), the size `n32` (`hn`); `I n32` holds after
the prologue (`hI0`). The clear: `I (k + 1)` keeps `_items` (`hIt`), gives `I k` when `_items[k]` is null (`hP0`),
`J k p` when its chars are null (`hQ0`); the chars' `delete []` (`k86`) gives `J k p`, the item's `operator delete`
(`k99`) gives `I k`. `I 0` survives the stores `Ok` allows (`hok`, `hcl`: the size, `_items`, `_capacity`, the stack
slots at `aR S + 16` and `aR S + 24`, the slot `_items[_size]`), is kept by every later callee, gives the stack
(`hI`), `path._chars` = `ch` (`hch`) and `path._len` = `ln` (`hln`). The throws (`kt2`, `kt7`), and at the return
address (`kr`): `rsp` 8 above the entry's, the callee-saved registers as they were, bytes with `I 0`. -/
theorem spp_ok {fb : Addr} {cn : BitVec 64} {n32 ln : BitVec 32} {it ch : BitVec 64}
    {I : Nat → (Addr → Byte) → Prop} {J : Nat → BitVec 64 → (Addr → Byte) → Prop} {Ok : Addr → Nat → Prop}
    {e₂ : Addr} {code₂ : List Byte} {j₂ : Nat}
    (c : Seg prof F Wl L s₀ o) (hfs : s₀.cpu.seg.fsBase = fb) (hin : CodeIn L spp_at spp)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = spp_at)
    (hcn : rdq(V0 V X.cpu.gpr, fb + 40#64) = cn) (hn : rdd(V1 V X.cpu.gpr cn, X.cpu.gpr.rsi + 8#64) = n32)
    (hcl : ∀ i < 8, Foot F.data (Addr.add (fb + 40#64) i))
    (hs1 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8) i))
    (hs2 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8 - 8) i))
    (hs3 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8 - 8 - 8) i))
    (hs4 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8 - 8 - 8 - 8) i))
    (hs5 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8 - 8 - 8 - 8 - 8) i))
    (hs6 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8 - 8 - 8 - 8 - 8 - 8) i))
    (hw8 : ∀ i < 8, Foot Wl (Addr.add (aR X.cpu.gpr.rsp + 8#64) i))
    (hw56 : ∀ i < 8, Foot Wl (Addr.add (aR X.cpu.gpr.rsp + 56#64) i))
    (f32 : ∀ i < 8, Foot F.data (Addr.add (aR X.cpu.gpr.rsp + 32#64) i))
    (hr8 : ∀ i < 8, Foot Wl (Addr.add (aR X.cpu.gpr.rsp - 8) i))
    (hl : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsp i))
    (hin₂ : CodeIn L e₂ code₂) (h₂ : j₂ < code₂.length)
    (fp0 : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rdi i))
    (fp8 : ∀ i < 4, Foot F.data (Addr.add (X.cpu.gpr.rdi + 8#64) i))
    (fc : ∀ k < ln.toNat, ∀ i < 4, Foot F.data (Addr.add (ch + BitVec.ofNat 64 k * 4#64) i))
    (fe : ∀ k < n32.toNat, ∀ i < 8, Foot F.data (Addr.add (it + BitVec.ofNat 64 (8 * k)) i))
    (fp : ∀ k < n32.toNat, ∀ W, I (k + 1) W → pk W it k ≠ 0 → ∀ i < 8, Foot F.data (Addr.add (pk W it k) i))
    (hIt : ∀ k < n32.toNat, ∀ W, I (k + 1) W → rdq(W, X.cpu.gpr.rsi) = it)
    (hP0 : ∀ k < n32.toNat, ∀ W, I (k + 1) W → pk W it k = 0 → I k W)
    (hQ0 : ∀ k < n32.toNat, ∀ W, I (k + 1) W → pk W it k ≠ 0 → rdq(W, pk W it k) = 0 → J k (pk W it k) W)
    (hI0 : I n32.toNat (V1 V X.cpu.gpr cn))
    (hI : ∀ W, I 0 W → Stk fb W X.cpu.gpr.rsp X.cpu.gpr (e₂.add j₂))
    (hch : ∀ W, I 0 W → rdq(W, X.cpu.gpr.rdi) = ch)
    (hln : ∀ W, I 0 W → rdd(W, X.cpu.gpr.rdi + 8#64) = ln)
    (hok : ∀ a m, Ok a m → ∀ i < m, Foot Wl (Addr.add a i))
    (hcl0 : ∀ (W : Addr → Byte) (a : Addr) (m : Nat) (bs : List Byte), bs.length = m → Ok a m → I 0 W →
      I 0 (Vst W a bs))
    (o0 : Ok X.cpu.gpr.rsi 8) (o8 : Ok (X.cpu.gpr.rsi + 8#64) 4) (o12 : Ok (X.cpu.gpr.rsi + 12#64) 4)
    (os16 : Ok (aR X.cpu.gpr.rsp + 16#64) 4) (os16q : Ok (aR X.cpu.gpr.rsp + 16#64) 8)
    (os24 : Ok (aR X.cpu.gpr.rsp + 24#64) 8)
    (hsl : ∀ W, I 0 W →
      Ok (rdq(W, X.cpu.gpr.rsi) + BitVec.setWidth 64 rdd(W, X.cpu.gpr.rsi + 8#64) * 8#64) 8)
    (cD : ∃ code : List Byte, CodeIn L 0x6014f0#64 code ∧ 0 < code.length)
    (cE : ∃ code : List Byte, CodeIn L 0x6014e0#64 code ∧ 0 < code.length)
    (cC : ∃ code : List Byte, CodeIn L 0x44d3e0#64 code ∧ 0 < code.length)
    (cS : ∃ code : List Byte, CodeIn L 0x44d790#64 code ∧ 0 < code.length)
    (cN2 : ∃ code : List Byte, CodeIn L 0x6029b0#64 code ∧ 0 < code.length)
    (cM : ∃ code : List Byte, CodeIn L 0x401070#64 code ∧ 0 < code.length)
    (cN : ∃ code : List Byte, CodeIn L 0x602970#64 code ∧ 0 < code.length)
    (cU : ∃ code : List Byte, CodeIn L 0x44d5d0#64 code ∧ 0 < code.length)
    (cT2 : ∃ code : List Byte, CodeIn L 0x4017c2#64 code ∧ 0 < code.length)
    (cT7 : ∃ code : List Byte, CodeIn L 0x4017c7#64 code ∧ 0 < code.length)
    (k86 : ∀ k < n32.toNat, ∀ W, I (k + 1) W → pk W it k ≠ 0 → rdq(W, pk W it k) ≠ 0 →
      KC prof F Wl L s₀ o gev gP gE X.cpu.gpr.rsp 0x6014f0#64 91 W (fun g => g.rdi = rdq(W, pk W it k))
        (J k (pk W it k)))
    (k99 : ∀ k < n32.toNat, ∀ p W, p ≠ 0 → J k p W →
      KC prof F Wl L s₀ o gev gP gE X.cpu.gpr.rsp 0x6014e0#64 104 W (fun g => g.rdi = p ∧ g.rsi = 16#64) (I k))
    (k184 : ∀ W, I 0 W → KC prof F Wl L s₀ o gev gP gE X.cpu.gpr.rsp 0x44d3e0#64 189 W
      (fun g => g.rdi = aR X.cpu.gpr.rsp + 32#64) (I 0))
    (k254 : ∀ W, I 0 W → KC prof F Wl L s₀ o gev gP gE X.cpu.gpr.rsp 0x44d790#64 259 W
      (fun g => g.rdi = aR X.cpu.gpr.rsp + 32#64) (I 0))
    (k309 : ∀ W, I 0 W → KC prof F Wl L s₀ o gev gP gE X.cpu.gpr.rsp 0x6029b0#64 314 W (fun _ => True) (I 0))
    (k627 : ∀ W, I 0 W → KC prof F Wl L s₀ o gev gP gE X.cpu.gpr.rsp 0x401070#64 632 W (fun _ => True) (I 0))
    (k648 : ∀ W, I 0 W → KC prof F Wl L s₀ o gev gP gE X.cpu.gpr.rsp 0x6014f0#64 653 W (fun _ => True) (I 0))
    (k357 : ∀ W, I 0 W → KC prof F Wl L s₀ o gev gP gE X.cpu.gpr.rsp 0x602970#64 362 W (fun _ => True) (I 0))
    (k373 : ∀ W, I 0 W → KC prof F Wl L s₀ o gev gP gE X.cpu.gpr.rsp 0x44d5d0#64 378 W (fun _ => True) (I 0))
    (k440 : ∀ W, I 0 W → KC prof F Wl L s₀ o gev gP gE X.cpu.gpr.rsp 0x44d790#64 445 W
      (fun g => g.rdi = aR X.cpu.gpr.rsp + 32#64) (I 0))
    (k494 : ∀ W, I 0 W → KC prof F Wl L s₀ o gev gP gE X.cpu.gpr.rsp 0x6029b0#64 499 W (fun _ => True) (I 0))
    (k686 : ∀ W, I 0 W → KC prof F Wl L s₀ o gev gP gE X.cpu.gpr.rsp 0x401070#64 691 W (fun _ => True) (I 0))
    (k694 : ∀ W, I 0 W → KC prof F Wl L s₀ o gev gP gE X.cpu.gpr.rsp 0x6014f0#64 699 W (fun _ => True) (I 0))
    (k538 : ∀ W, I 0 W → KC prof F Wl L s₀ o gev gP gE X.cpu.gpr.rsp 0x602970#64 543 W (fun _ => True) (I 0))
    (k552 : ∀ W, I 0 W → KC prof F Wl L s₀ o gev gP gE X.cpu.gpr.rsp 0x44d5d0#64 557 W (fun _ => True) (I 0))
    (k588 : ∀ W, I 0 W → KC prof F Wl L s₀ o gev gP gE X.cpu.gpr.rsp 0x6014f0#64 593 W (fun _ => True) (I 0))
    (kt2 : ∀ W, I 0 W → ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y → Agree F Y.proc.mm.mem W →
      Y.cpu.rip = 0x4017c2#64 → Y.cpu.gpr.rsp = aR X.cpu.gpr.rsp → GoG prof L o gev gP gE Y t')
    (kt7 : ∀ W, I 0 W → ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y → Agree F Y.proc.mm.mem W →
      Y.cpu.rip = 0x4017c7#64 → Y.cpu.gpr.rsp = aR X.cpu.gpr.rsp → GoG prof L o gev gP gE Y t')
    (kr : ∀ (W : Addr → Byte) (Z' : State) (t' : Nat), KeptW Wl s₀ Z' → Agree F Z'.proc.mm.mem W →
      Z'.cpu.rip = e₂.add j₂ → Z'.cpu.gpr.rsp = X.cpu.gpr.rsp + 8 → KS X.cpu.gpr Z'.cpu.gpr → I 0 W →
      GoG prof L o gev gP gE Z' t') :
    GoG prof L o gev gP gE X t := by
  have E : Ev prof F Wl L s₀ o gev gP gE fb X.cpu.gpr.rsp X.cpu.gpr e₂ code₂ j₂ n32.toNat it ch ln I J Ok :=
    { c := c, hfs := hfs, hin := hin, hin₂ := hin₂, h₂ := h₂, hn := n32.isLt, hI := hI, hch := hch, hln := hln,
      hok := hok, hcl := hcl0, o0 := o0, o8 := o8, o12 := o12, os16 := os16, os16q := os16q, os24 := os24,
      hsl := hsl, fcl := hcl, fg := fun i hi => c.hws _ (hw56 i hi), f8s := fun i hi => c.hws _ (hw8 i hi),
      f32 := f32,
      fb48 := fun i hi => c.hws _ (hs6 i hi), fb40 := fun i hi => c.hws _ (hs5 i hi),
      fb32 := fun i hi => c.hws _ (hs4 i hi), fb24 := fun i hi => c.hws _ (hs3 i hi),
      fb16 := fun i hi => c.hws _ (hs2 i hi), fb8 := fun i hi => c.hws _ (hs1 i hi), hl := hl, hr8 := hr8,
      fp0 := fp0, fp8 := fp8, fc := fc, fe := fe, fp := fp, hIt := hIt, hP0 := hP0, hQ0 := hQ0,
      cD := cD, cE := cE, cC := cC, cS := cS, cN2 := cN2, cM := cM, cN := cN, cU := cU, cT2 := cT2, cT7 := cT7,
      k86 := k86, k99 := k99, k184 := k184, k254 := k254, k309 := k309, k627 := k627, k648 := k648,
      k357 := k357, k373 := k373, k440 := k440, k494 := k494, k686 := k686, k694 := k694, k538 := k538,
      k552 := k552, k588 := k588, kt2 := kt2, kt7 := kt7, kr := kr }
  -- the prologue, to 114 (the size 0) or the clear from the step `n32 - 1`
  have hrip' : X.cpu.rip = spp_at.add 0 := by rw [addr_add_zero]; exact hrip
  refine (c_0 prof fb).run c hfs hin (fun j' g' _ V' => V' = V1 V X.cpu.gpr cn ∧ Fc X.cpu.gpr.rsp X.cpu.gpr g' ∧
      ((n32 = 0 ∧ j' = 114) ∨ (¬n32 = 0 ∧ j' = 64 ∧ g'.rbx = rbx0 n32))) hK hA hrip'
    (vc_0 hcn hn hs1 hs2 hs3 hs4 hs5 hs6 hcl hw8 hw56 (fun i hi => c.hws _ (hok _ _ o8 i hi))
      (fun h0 _ a b _ _ => ⟨rfl, ⟨a, b⟩, Or.inl ⟨h0, rfl⟩⟩)
      (fun h0 _ a b _ d _ => ⟨rfl, ⟨a, b⟩, Or.inr ⟨h0, rfl, d⟩⟩)) ?_
  rintro j' g fl V₁ ⟨hV₁, hm, hj⟩ Y t₁ hKY hAY hrY hgY -
  subst V₁ hgY
  rcases hj with ⟨hn0, rfl⟩ | ⟨hn0, rfl, gbx⟩
  · have e0 : n32.toNat = 0 := (congrArg BitVec.toNat hn0).trans rfl
    exact from114 E hKY hAY hrY hm (e0 ▸ hI0)
  · have hnz : n32.toNat ≠ 0 := fun e => hn0 (BitVec.eq_of_toNat_eq (e.trans rfl))
    have e1 : n32.toNat - 1 + 1 = n32.toNat := by omega
    exact L64 E (n32.toNat - 1) (by omega) Y _ t₁ hKY hAY hrY
      ⟨by rw [e1]; exact hI0, hm, by rw [gbx, rbx0_eq hn0]⟩

end FV7z.Spp
