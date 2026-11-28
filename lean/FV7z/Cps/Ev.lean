import FV7z.Cps.Pieces1
import FV7z.Cps.Pieces2
import FV7z.Cps.Pieces3
/-!
# `NCommandLineParser::CParser::ParseString`: the hypotheses of the runs, the tail and the error paths (PLAN.md §M, M1)

- `e24`, the arithmetic of the indices (`w32`, `i32`, `nxe`, `s64`, `pl`, `kexit`, `knext`, `sz24_eq`).
- `Fo` (a switch form's fields the code reads), `Ro` (a switch result's fields it stores into), `Ky` (a key: its
  length below `2^32`, its bytes readable, nonzero before the NUL), `Lp`, `Bt` (the switch loop's registers), `Nx`
  (the next round of the switch loop as a continuation).
- `Ev`: the hypotheses of the runs from the cut points; `callK`: a `call` of a callee given as `KC`.
- `tail331`: the stack guard's check, the epilogue, the `ret`; the error messages (`AString::operator=` at 407, 504,
  725, 754, 783) and the paths to 331.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
open FV7z.Api (P6 Stk KS)
namespace FV7z.Cps
set_option linter.unusedVariables false

/-! ## Values -/

/-- The `k`-th 24-byte entry from `b` (the switch forms, the switch results). -/
abbrev e24 (b : Addr) (k : Nat) : Addr := b + BitVec.ofNat 64 (24 * k)

theorem e24z (b : Addr) : e24 b 0 = b := BitVec.add_zero b

theorem e24s (b : Addr) (k : Nat) : e24 b k + 24#64 = e24 b (k + 1) := by
  show b + BitVec.ofNat 64 (24 * k) + 24#64 = b + BitVec.ofNat 64 (24 * (k + 1))
  rw [show 24 * (k + 1) = 24 * k + 24 by omega, BitVec.ofNat_add, BitVec.add_assoc]

theorem sz24_eq {N : Nat} (hN : 24 * N < 18446744073709551616) :
    sz24 (BitVec.ofNat 64 N) = BitVec.ofNat 64 (24 * N) := by
  apply BitVec.eq_of_toNat_eq
  simp only [sz24, BitVec.toNat_shiftLeft, BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat, Nat.shiftLeft_eq,
    Nat.reducePow, Nat.reduceMod]
  omega

theorem w32 {k : Nat} (hk : k < 4294967296) :
    BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 64 k)) = BitVec.ofNat 64 k := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.reducePow]
  omega

theorem i32 {k : Nat} (hk : k + 1 < 4294967296) :
    BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 64 k) + 1#32) = BitVec.ofNat 64 (k + 1) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
  omega

theorem nxe {j : Nat} (hj : j + 1 < 4294967296) : nx (BitVec.ofNat 64 j) = BitVec.ofNat 64 (j + 1) := by
  apply BitVec.eq_of_toNat_eq
  simp only [nx, BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
  omega

theorem s64 (x : BitVec 32) : BitVec.setWidth 32 (BitVec.setWidth 64 x) = x := by
  apply BitVec.eq_of_toNat_eq
  have h : x.toNat < 4294967296 := x.isLt
  simp only [BitVec.toNat_setWidth, Nat.reducePow]
  omega

/-- `rem` = `len - pos` is 1 (`len` not 0): `pos` below `len`. -/
theorem pl {ln p : BitVec 32} (h0 : ln ≠ 0) (h : BitVec.setWidth 32 (BitVec.setWidth 64 (ln - p)) = 1#32) :
    p.toNat < ln.toNat := by
  rw [s64] at h
  have h1 := congrArg BitVec.toNat h
  have h2 : ln.toNat ≠ 0 := fun e => h0 (BitVec.eq_of_toNat_eq (by rw [e]; rfl))
  have hl : ln.toNat < 4294967296 := ln.isLt
  have hp : p.toNat < 4294967296 := p.isLt
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod] at h1
  omega

/-- The switch loop's exit (`cmp ecx, r12d` equal after `add r12d, 1`): `k + 1` = the count. -/
theorem kexit {n : BitVec 32} {k : Nat} (hk : k < n.toNat) (h : n = BitVec.setWidth 32 (BitVec.ofNat 64 k) + 1#32) :
    k + 1 = n.toNat := by
  have h1 := congrArg BitVec.toNat h
  have hn : n.toNat < 4294967296 := n.isLt
  simp only [BitVec.toNat_add, BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod] at h1
  omega

/-- The switch loop goes on: `k + 1` below the count. -/
theorem knext {n : BitVec 32} {k : Nat} (hk : k < n.toNat)
    (h : ¬n = BitVec.setWidth 32 (BitVec.ofNat 64 k) + 1#32) : k + 1 < n.toNat := by
  rcases Nat.lt_or_ge (k + 1) n.toNat with h1 | h1
  · exact h1
  · exfalso
    apply h
    apply BitVec.eq_of_toNat_eq
    have hn : n.toNat < 4294967296 := n.isLt
    simp only [BitVec.toNat_add, BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
    omega

/-! ## The forms, the results, the keys, the switch loop -/

/-- `numSwitches`. -/
abbrev nS (g0 : Gprs) : Nat := (BitVec.setWidth 32 g0.rcx).toNat

theorem nS_lt (g0 : Gprs) : nS g0 < 4294967296 := (BitVec.setWidth 32 g0.rcx).isLt

/-- A switch form's fields the code reads (at `a`): `Key`, `Type`, `Multi`, `MinLen`, `PostCharSet`. -/
abbrev Fo (F : Footprint) (a : Addr) : Prop :=
  (∀ i < 8, Foot F.data (Addr.add a i)) ∧ (∀ i < 1, Foot F.data (Addr.add (a + 8#64) i)) ∧
    (∀ i < 1, Foot F.data (Addr.add (a + 9#64) i)) ∧ (∀ i < 1, Foot F.data (Addr.add (a + 10#64) i)) ∧
    (∀ i < 8, Foot F.data (Addr.add (a + 16#64) i))

/-- A switch result's fields the code stores into (at `r`): `ThereIs`, `WithMinus`, `PostCharIndex`,
`PostStrings._items`, `_size`, `_capacity`, the slot `_items[_size]`. -/
abbrev Ro (I : (Addr → Byte) → Prop) (Ok : Addr → Nat → Prop) (r : Addr) : Prop :=
  Ok r 1 ∧ Ok (r + 1#64) 1 ∧ Ok (r + 4#64) 4 ∧ Ok (r + 8#64) 8 ∧ Ok (r + 16#64) 4 ∧ Ok (r + 20#64) 4 ∧
    ∀ W, I W → Ok (rdq(W, r + 8#64) + BitVec.setWidth 64 rdd(W, r + 16#64) * 8#64) 8

/-- A key at `p` of length `l`: below `2^32`, its bytes and the NUL readable, nonzero before the NUL. -/
abbrev Ky (F : Footprint) (I : (Addr → Byte) → Prop) (p : Addr) (l : Nat) : Prop :=
  l < 4294967296 ∧ (∀ j ≤ l, ∀ i < 1, Foot F.data (Addr.add (p + BitVec.ofNat 64 j) i)) ∧
    ∀ W, I W → (∀ j < l, W (p + BitVec.ofNat 64 j) ≠ 0#8) ∧ W (p + BitVec.ofNat 64 l) = 0#8

/-- The switch loop at the form `k`: `rsp`, `r14` = `s`, `ecx` = `numSwitches`, `r13` = the form, `r12` = `k`. -/
abbrev Lp (S : Addr) (g0 : Gprs) (k : Nat) (g : Gprs) : Prop :=
  g.rsp = aR S ∧ g.r14 = g0.rsi ∧ BitVec.setWidth 32 g.rcx = BitVec.setWidth 32 g0.rcx ∧ g.r13 = e24 g0.rdx k ∧
    g.r12 = BitVec.ofNat 64 k

/-- The best match so far: none (`r15d` = -1), or `rbp` an index below `k`. -/
abbrev Bt (k : Nat) (g : Gprs) : Prop :=
  BitVec.setWidth 32 g.r15 = 4294967295#32 ∨ ∃ b, b < k ∧ g.rbp = BitVec.ofNat 64 b

theorem Lp.lk {S : Addr} {g0 g g' : Gprs} {k : Nat} (h : Lp S g0 k g) (l : Lk g g') : Lp S g0 k g' :=
  ⟨l.1.trans h.1, l.2.1.trans h.2.1, by rw [l.2.2.1]; exact h.2.2.1, l.2.2.2.1.trans h.2.2.2.1,
    l.2.2.2.2.1.trans h.2.2.2.2⟩

theorem Bt.eq {g g' : Gprs} {k : Nat} (h : Bt k g) (e15 : g'.r15 = g.r15) (ebp : g'.rbp = g.rbp) : Bt k g' := by
  rcases h with h | ⟨b, hb, e⟩
  · exact Or.inl (by rw [e15]; exact h)
  · exact Or.inr ⟨b, hb, ebp.trans e⟩

theorem Bt.lk {g g' : Gprs} {k : Nat} (h : Bt k g) (l : Lk g g') : Bt k g' :=
  Bt.eq h l.2.2.2.2.2.1 l.2.2.2.2.2.2

theorem Bt.mono {g : Gprs} {k k' : Nat} (h : Bt k g) (hk : k ≤ k') : Bt k' g := by
  rcases h with h | ⟨b, hb, e⟩
  · exact Or.inl h
  · exact Or.inr ⟨b, by omega, e⟩

/-! ## The hypotheses of the runs -/

/-- The hypotheses of the runs from the cut points (`fb` the `fs` base, `S`, `g0` the entry's stack pointer and
registers, `e₂.add j₂` the return address, `I` the invariant of the bytes, `Ok` the stores that keep it; `s` =
`g0.rsi` with `_chars` = `ch` and `_len` = `ln`, `this` = `g0.rdi` with `_switches` = `sp`, the forms at `g0.rdx`
with the keys at `kp k`, `numSwitches` = `ecx`). -/
structure Ev (prof : Profile) (F : Footprint) (Wl : List Rgn) (L : List (Addr × List Byte)) (s₀ : State)
    (o : Oracle) (gev : List Event) (gP : State → Nat → List Event → Prop) (gE : Outcome → List Event → Prop)
    (fb S : Addr) (g0 : Gprs) (e₂ : Addr) (code₂ : List Byte) (j₂ : Nat) (I : (Addr → Byte) → Prop)
    (Ok : Addr → Nat → Prop) (ch : Addr) (ln : BitVec 32) (sp : Addr) (kp : Nat → Addr) : Prop where
  c : Seg prof F Wl L s₀ o
  hfs : s₀.cpu.seg.fsBase = fb
  hin : CodeIn L cps_at cps
  hin₂ : CodeIn L e₂ code₂
  h₂ : j₂ < code₂.length
  hI : ∀ W, I W → Sk fb W S g0 (e₂.add j₂)
  hF : ∀ W, I W → rdq(W, aR S + 16#64) = g0.rdx ∧ rdq(W, aR S + 24#64) = g0.rdi
  hs : ∀ W, I W → rdq(W, g0.rsi) = ch ∧ rdd(W, g0.rsi + 8#64) = ln ∧ rdq(W, g0.rdi) = sp
  hkp : ∀ W, I W → ∀ k < nS g0, rdq(W, e24 g0.rdx k) = kp k
  hok : ∀ a n, Ok a n → ∀ i < n, Foot Wl (Addr.add a i)
  hcl : ∀ (W : Addr → Byte) (a : Addr) (n : Nat) (bs : List Byte), bs.length = n → Ok a n → I W → I (Vst W a bs)
  hc12 : ∀ (W : Addr → Byte) (bs : List Byte), bs.length = 4 → I W → I (Vst W (aR S + 12#64) bs)
  hr12 : ∀ (W : Addr → Byte) (v : BitVec 32), rdd(Vst W (aR S + 12#64) (toBytesLE v 4), aR S + 12#64) = v
  w12 : ∀ i < 4, Foot Wl (Addr.add (aR S + 12#64) i)
  f16 : ∀ i < 8, Foot F.data (Addr.add (aR S + 16#64) i)
  f24 : ∀ i < 8, Foot F.data (Addr.add (aR S + 24#64) i)
  f32 : ∀ i < 8, Foot F.data (Addr.add (aR S + 32#64) i)
  f56 : ∀ i < 8, Foot F.data (Addr.add (aR S + 56#64) i)
  fcl : ∀ i < 8, Foot F.data (Addr.add (fb + 40#64) i)
  fb48 : ∀ i < 8, Foot F.data (Addr.add (S - 8 - 8 - 8 - 8 - 8 - 8) i)
  fb40 : ∀ i < 8, Foot F.data (Addr.add (S - 8 - 8 - 8 - 8 - 8) i)
  fb32 : ∀ i < 8, Foot F.data (Addr.add (S - 8 - 8 - 8 - 8) i)
  fb24 : ∀ i < 8, Foot F.data (Addr.add (S - 8 - 8 - 8) i)
  fb16 : ∀ i < 8, Foot F.data (Addr.add (S - 8 - 8) i)
  fb8 : ∀ i < 8, Foot F.data (Addr.add (S - 8) i)
  hl : ∀ i < 8, Foot F.data (Addr.add S i)
  hr8 : ∀ i < 8, Foot Wl (Addr.add (aR S - 8) i)
  fs0 : ∀ i < 8, Foot F.data (Addr.add g0.rsi i)
  fs8 : ∀ i < 4, Foot F.data (Addr.add (g0.rsi + 8#64) i)
  fth : ∀ i < 8, Foot F.data (Addr.add g0.rdi i)
  fch0 : ln ≠ 0 → ∀ i < 4, Foot F.data (Addr.add ch i)
  fch : ∀ p : BitVec 32, p.toNat < ln.toNat → ∀ i < 4, Foot F.data (Addr.add (ch + BitVec.setWidth 64 p * 4#64) i)
  ffo : ∀ k < nS g0, Fo F (e24 g0.rdx k)
  hky : ∀ k < nS g0, ∃ l, Ky F I (kp k) l
  hro : ∀ k < nS g0, Ro I Ok (e24 sp k)
  cT : ∃ code : List Byte, CodeIn L 0x412d7c#64 code ∧ 0 < code.length
  cK : ∃ code : List Byte, CodeIn L 0x44bde0#64 code ∧ 0 < code.length
  cE : ∃ code : List Byte, CodeIn L 0x44c4c0#64 code ∧ 0 < code.length
  cF : ∃ code : List Byte, CodeIn L 0x44b960#64 code ∧ 0 < code.length
  cU : ∃ code : List Byte, CodeIn L 0x44d480#64 code ∧ 0 < code.length
  cA : ∃ code : List Byte, CodeIn L 0x6029b0#64 code ∧ 0 < code.length
  cD : ∃ code : List Byte, CodeIn L 0x6014f0#64 code ∧ 0 < code.length
  cN : ∃ code : List Byte, CodeIn L 0x602970#64 code ∧ 0 < code.length
  cC : ∃ code : List Byte, CodeIn L 0x44d5d0#64 code ∧ 0 < code.length
  cM : ∃ code : List Byte, CodeIn L 0x401070#64 code ∧ 0 < code.length
  k151 : ∀ M W, I W → rdd(W, aR S + 12#64) = M → KC prof F Wl L s₀ o gev gP gE S
    (fun W' => I W' ∧ rdd(W', aR S + 12#64) = M) 0x44bde0#64 156 W (fun _ => True) (fun _ => True)
  k407 : ∀ W, I W → KC prof F Wl L s₀ o gev gP gE S I 0x44c4c0#64 412 W (fun _ => True) (fun _ => True)
  k504 : ∀ W, I W → KC prof F Wl L s₀ o gev gP gE S I 0x44c4c0#64 509 W (fun _ => True) (fun _ => True)
  k725 : ∀ W, I W → KC prof F Wl L s₀ o gev gP gE S I 0x44c4c0#64 730 W (fun _ => True) (fun _ => True)
  k754 : ∀ W, I W → KC prof F Wl L s₀ o gev gP gE S I 0x44c4c0#64 759 W (fun _ => True) (fun _ => True)
  k783 : ∀ W, I W → KC prof F Wl L s₀ o gev gP gE S I 0x44c4c0#64 788 W (fun _ => True) (fun _ => True)
  k467 : ∀ W, I W → KC prof F Wl L s₀ o gev gP gE S I 0x44b960#64 472 W (fun _ => True) (fun _ => True)
  k529 : ∀ W, I W → KC prof F Wl L s₀ o gev gP gE S I 0x44d480#64 534 W (fun _ => True) (fun _ => True)
  k587 : ∀ W, I W → KC prof F Wl L s₀ o gev gP gE S I 0x6029b0#64 592 W (fun _ => True) (fun _ => True)
  k621 : ∀ W, I W → KC prof F Wl L s₀ o gev gP gE S I 0x6014f0#64 626 W (fun _ => True) (fun _ => True)
  k641 : ∀ W, I W → KC prof F Wl L s₀ o gev gP gE S I 0x602970#64 646 W (fun _ => True) (fun _ => True)
  k655 : ∀ W, I W → KC prof F Wl L s₀ o gev gP gE S I 0x44d5d0#64 660 W (fun _ => True) (fun _ => True)
  k696 : ∀ W, I W → KC prof F Wl L s₀ o gev gP gE S I 0x6014f0#64 701 W (fun _ => True) (fun _ => True)
  k804 : ∀ W, I W → KC prof F Wl L s₀ o gev gP gE S I 0x401070#64 809 W (fun _ => True) (fun _ => True)
  kt : ∀ W, I W → ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y → Agree F Y.proc.mm.mem W →
    Y.cpu.rip = 0x412d7c#64 → Y.cpu.gpr.rsp = aR S → GoG prof L o gev gP gE Y t'
  kr : ∀ (W : Addr → Byte) (Z' : State) (t' : Nat), KeptW Wl s₀ Z' → Agree F Z'.proc.mm.mem W →
    Z'.cpu.rip = e₂.add j₂ → Z'.cpu.gpr.rsp = S + 8 → KS g0 Z'.cpu.gpr → I W → GoG prof L o gev gP gE Z' t'

/-- The next round of the switch loop (from 96 at the form `k + 1`), as a continuation. -/
abbrev Nx (prof : Profile) (F : Footprint) (Wl : List Rgn) (L : List (Addr × List Byte)) (s₀ : State) (o : Oracle)
    (gev : List Event) (gP : State → Nat → List Event → Prop) (gE : Outcome → List Event → Prop)
    (S : Addr) (g0 : Gprs) (I : (Addr → Byte) → Prop) (k : Nat) : Prop :=
  ∀ (U : State) (W' : Addr → Byte) (t' : Nat), KeptW Wl s₀ U → Agree F U.proc.mm.mem W' →
    U.cpu.rip = cps_at.add 96 → Lp S g0 (k + 1) U.cpu.gpr → Bt (k + 1) U.cpu.gpr → I W' → k + 1 < nS g0 →
    GoG prof L o gev gP gE U t'

section Runs
variable {prof : Profile} {F : Footprint} {Wl : List Rgn} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {fb S : Addr} {g0 : Gprs} {e₂ : Addr} {code₂ : List Byte} {j₂ : Nat} {I : (Addr → Byte) → Prop}
  {Ok : Addr → Nat → Prop} {ch : Addr} {ln : BitVec 32} {sp : Addr} {kp : Nat → Addr}
  {Y : State} {t : Nat} {W : Addr → Byte}

/-- A store's footprint in `F.data`. -/
theorem Ev.fd (E : Ev prof F Wl L s₀ o gev gP gE fb S g0 e₂ code₂ j₂ I Ok ch ln sp kp) {a : Addr} {n : Nat}
    (h : Ok a n) : ∀ i < n, Foot F.data (Addr.add a i) := fun i hi => E.c.hws _ (E.hok _ _ h i hi)

/-- The slot of `ecx` readable. -/
theorem Ev.f12 (E : Ev prof F Wl L s₀ o gev gP gE fb S g0 e₂ code₂ j₂ I Ok ch ln sp kp) :
    ∀ i < 4, Foot F.data (Addr.add (aR S + 12#64) i) := fun i hi => E.c.hws _ (E.w12 i hi)

/-- A `call` at `j` (`rsp` = `aR S`, the bytes `W`) of the callee `k`, and from its return at `j + 5`. -/
theorem callK (E : Ev prof F Wl L s₀ o gev gP gE fb S g0 e₂ code₂ j₂ I Ok ch ln sp kp)
    {J : (Addr → Byte) → Prop} {U : State} {t₁ : Nat} {j R : Nat} {ent : Addr} {A B : Gprs → Prop}
    (hKU : KeptW Wl s₀ U) (hAU : Agree F U.proc.mm.mem W) (hrU : U.cpu.rip = cps_at.add j)
    (hs : U.cpu.gpr.rsp = aR S) (hj : j < cps.length) (hd : Dec prof.feat cps j (FV7z.mk .call 64 [.rel R] 5))
    (htgt : cps_at.add (j + 5) + BitVec.ofNat 64 R = ent)
    (hc : ∃ code : List Byte, CodeIn L ent code ∧ 0 < code.length)
    (k : KC prof F Wl L s₀ o gev gP gE S J ent (j + 5) W A B) (hA : A (U.cpu.gpr.set 4 (aR S - 8)))
    (h : ∀ (Z : State) (W' : Addr → Byte) (t'' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem W' →
      Z.cpu.rip = cps_at.add (j + 5) → Z.cpu.gpr.rsp = aR S → KS U.cpu.gpr Z.cpu.gpr → B Z.cpu.gpr → J W' →
      GoG prof L o gev gP gE Z t'') :
    GoG prof L o gev gP gE U t₁ := by
  have hU : U.cpu.gpr.rsp - 8 = aR S - 8 := by rw [hs]
  obtain ⟨cc, hinc, hcc⟩ := hc
  refine E.c.s_call hKU hAU E.hin hj hrU hd hinc hcc htgt (by rw [hU]; exact E.hr8) ?_
  rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
  rw [hU] at hA₂
  refine k Y₂ t₂ hK₂ hA₂ hr₂ (by rw [hg₂]; exact hU) (by rw [hg₂, hU]; exact hA) ?_
  intro Z W' t₃ hKZ hAZ hrZ hsZ hkZ hBZ hIZ
  rw [hg₂] at hkZ
  exact h Z W' t₃ hKZ hAZ hrZ hsZ hkZ hBZ hIZ

/-- From 331 (`rsp` = `aR S`, the bytes `W` with `I`): the stack guard's check, the epilogue, the `ret`, to `kr`. -/
theorem tail331 (E : Ev prof F Wl L s₀ o gev gP gE fb S g0 e₂ code₂ j₂ I Ok ch ln sp kp) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = cps_at.add 331) (hs : Y.cpu.gpr.rsp = aR S) (hIW : I W) :
    GoG prof L o gev gP gE Y t := by
  obtain ⟨⟨s1, s2, s3, s4, s5, s6, s7⟩, sc⟩ := E.hI W hIW
  refine (c_331 prof fb).run E.c E.hfs E.hin (fun j' g' _ V' => j' = 359 ∧ V' = W ∧
      g'.rsp = Y.cpu.gpr.rsp + 72#64 + 8 ∧ g'.rbx = rdq(W, Y.cpu.gpr.rsp + 72#64)) hK hA hr
    (vc_331 (by rw [hs]; exact sc) (by rw [hs]; exact E.f56) E.fcl (by rw [hs, q1]; exact E.fb48)
      fun _ a b _ _ => ⟨rfl, rfl, a, b⟩) ?_
  rintro j' g fl V₁ ⟨rfl, hV₁, gs, gx⟩ U t₁ hKU hAU hrU hgU -
  subst V₁ hgU
  have e1 : rdq(W, Y.cpu.gpr.rsp + 72#64) = g0.rbx := by rw [hs, q1]; exact s1
  have e2 : rdq(W, U.cpu.gpr.rsp) = g0.rbp := by rw [gs, hs, q2]; exact s2
  have e3 : rdq(W, U.cpu.gpr.rsp + 8) = g0.r12 := by rw [gs, hs, q3]; exact s3
  have e4 : rdq(W, U.cpu.gpr.rsp + 8 + 8) = g0.r13 := by rw [gs, hs, q4]; exact s4
  have e5 : rdq(W, U.cpu.gpr.rsp + 8 + 8 + 8) = g0.r14 := by rw [gs, hs, q5]; exact s5
  have e6 : rdq(W, U.cpu.gpr.rsp + 8 + 8 + 8 + 8) = g0.r15 := by rw [gs, hs, q6]; exact s6
  refine (c_359 prof fb).run E.c E.hfs E.hin (fun j' g' _ V' => j' = 368 ∧ V' = W ∧
      g'.rsp = U.cpu.gpr.rsp + 8 + 8 + 8 + 8 + 8 ∧ g'.rbp = rdq(W, U.cpu.gpr.rsp) ∧
      g'.r12 = rdq(W, U.cpu.gpr.rsp + 8) ∧ g'.r13 = rdq(W, U.cpu.gpr.rsp + 8 + 8) ∧
      g'.r14 = rdq(W, U.cpu.gpr.rsp + 8 + 8 + 8) ∧ g'.r15 = rdq(W, U.cpu.gpr.rsp + 8 + 8 + 8 + 8) ∧
      g'.rbx = U.cpu.gpr.rbx) hKU hAU hrU
    (vc_359 (by rw [gs, hs, q2]; exact E.fb40) (by rw [gs, hs, q3]; exact E.fb32)
      (by rw [gs, hs, q4]; exact E.fb24) (by rw [gs, hs, q5]; exact E.fb16) (by rw [gs, hs, q6]; exact E.fb8)
      fun _ a1 a2 a3 a4 a5 a6 a7 _ _ => ⟨rfl, rfl, a1, a2, a3, a4, a5, a6, a7⟩) ?_
  rintro j' g fl V₂ ⟨rfl, hV₂, g1, g2, g3, g4, g5, g6, g7⟩ Z t₂ hKZ hAZ hrZ hgZ -
  subst V₂ hgZ
  have hsZ : Z.cpu.gpr.rsp = S := by rw [g1, gs, hs]; exact q7 S
  refine E.c.s_ret hKZ hAZ E.hin (lt_len (by decide)) hrZ (ret_368 _) (by rw [hsZ]; exact E.hl) E.hin₂ E.h₂
    (by rw [hsZ]; exact s7) ?_
  rintro Z' t₃ hKZ' hAZ' ⟨hrZ', hgZ'⟩
  refine E.kr W Z' t₃ hKZ' hAZ' hrZ' ?_ ?_ hIW
  · rw [hgZ']
    show Z.cpu.gpr.rsp + 8 = _
    rw [hsZ]
  · rw [hgZ']
    exact ⟨g7.trans (gx.trans e1), g2.trans e2, g3.trans e3, g4.trans e4, g5.trans e5, g6.trans e6⟩

/-! ## To 331 -/

theorem from317 (E : Ev prof F Wl L s₀ o gev gP gE fb S g0 e₂ code₂ j₂ I Ok ch ln sp kp) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = cps_at.add 317) (hs : Y.cpu.gpr.rsp = aR S) (hIW : I W) :
    GoG prof L o gev gP gE Y t := by
  refine (c_317 prof fb).run E.c E.hfs E.hin (fun j' g' _ V' => j' = 331 ∧ V' = W ∧ g'.rsp = Y.cpu.gpr.rsp)
    hK hA hr (vc_317 fun _ a _ => ⟨rfl, rfl, a⟩) ?_
  rintro j' g fl V₁ ⟨rfl, hV₁, gs⟩ U t₁ hKU hAU hrU hgU -
  subst V₁ hgU
  exact tail331 E hKU hAU hrU (gs.trans hs) hIW

theorem from328 (E : Ev prof F Wl L s₀ o gev gP gE fb S g0 e₂ code₂ j₂ I Ok ch ln sp kp) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = cps_at.add 328) (hs : Y.cpu.gpr.rsp = aR S) (hIW : I W) :
    GoG prof L o gev gP gE Y t := by
  refine (c_328 prof fb).run E.c E.hfs E.hin (fun j' g' _ V' => j' = 331 ∧ V' = W ∧ g'.rsp = Y.cpu.gpr.rsp)
    hK hA hr (vc_328 fun _ a _ => ⟨rfl, rfl, a⟩) ?_
  rintro j' g fl V₁ ⟨rfl, hV₁, gs⟩ U t₁ hKU hAU hrU hgU -
  subst V₁ hgU
  exact tail331 E hKU hAU hrU (gs.trans hs) hIW

theorem from701 (E : Ev prof F Wl L s₀ o gev gP gE fb S g0 e₂ code₂ j₂ I Ok ch ln sp kp) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = cps_at.add 701) (hs : Y.cpu.gpr.rsp = aR S) (hIW : I W) :
    GoG prof L o gev gP gE Y t := by
  refine (c_701 prof fb).run E.c E.hfs E.hin (fun j' g' _ V' => j' = 317 ∧ g' = Y.cpu.gpr ∧ V' = W)
    hK hA hr (vc_701 fun _ => ⟨rfl, rfl, rfl⟩) ?_
  rintro j' g fl V₁ ⟨rfl, rfl, hV₁⟩ U t₁ hKU hAU hrU hgU -
  subst V₁
  exact from317 E hKU hAU hrU (by rw [hgU]; exact hs) hIW

theorem from412 (E : Ev prof F Wl L s₀ o gev gP gE fb S g0 e₂ code₂ j₂ I Ok ch ln sp kp) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = cps_at.add 412) (hs : Y.cpu.gpr.rsp = aR S) (hIW : I W) :
    GoG prof L o gev gP gE Y t := by
  refine (c_412 prof fb).run E.c E.hfs E.hin (fun j' g' _ V' => j' = 331 ∧ g' = Y.cpu.gpr ∧ V' = W)
    hK hA hr (vc_412 fun _ => ⟨rfl, rfl, rfl⟩) ?_
  rintro j' g fl V₁ ⟨rfl, rfl, hV₁⟩ U t₁ hKU hAU hrU hgU -
  subst V₁
  exact tail331 E hKU hAU hrU (by rw [hgU]; exact hs) hIW

theorem from509 (E : Ev prof F Wl L s₀ o gev gP gE fb S g0 e₂ code₂ j₂ I Ok ch ln sp kp) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = cps_at.add 509) (hs : Y.cpu.gpr.rsp = aR S) (hIW : I W) :
    GoG prof L o gev gP gE Y t := by
  refine (c_509 prof fb).run E.c E.hfs E.hin (fun j' g' _ V' => j' = 331 ∧ g' = Y.cpu.gpr ∧ V' = W)
    hK hA hr (vc_509 fun _ => ⟨rfl, rfl, rfl⟩) ?_
  rintro j' g fl V₁ ⟨rfl, rfl, hV₁⟩ U t₁ hKU hAU hrU hgU -
  subst V₁
  exact tail331 E hKU hAU hrU (by rw [hgU]; exact hs) hIW

theorem from730 (E : Ev prof F Wl L s₀ o gev gP gE fb S g0 e₂ code₂ j₂ I Ok ch ln sp kp) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = cps_at.add 730) (hs : Y.cpu.gpr.rsp = aR S) (hIW : I W) :
    GoG prof L o gev gP gE Y t := by
  refine (c_730 prof fb).run E.c E.hfs E.hin (fun j' g' _ V' => j' = 331 ∧ g' = Y.cpu.gpr ∧ V' = W)
    hK hA hr (vc_730 fun _ => ⟨rfl, rfl, rfl⟩) ?_
  rintro j' g fl V₁ ⟨rfl, rfl, hV₁⟩ U t₁ hKU hAU hrU hgU -
  subst V₁
  exact tail331 E hKU hAU hrU (by rw [hgU]; exact hs) hIW

theorem from759 (E : Ev prof F Wl L s₀ o gev gP gE fb S g0 e₂ code₂ j₂ I Ok ch ln sp kp) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = cps_at.add 759) (hs : Y.cpu.gpr.rsp = aR S) (hIW : I W) :
    GoG prof L o gev gP gE Y t := by
  refine (c_759 prof fb).run E.c E.hfs E.hin (fun j' g' _ V' => j' = 331 ∧ g' = Y.cpu.gpr ∧ V' = W)
    hK hA hr (vc_759 fun _ => ⟨rfl, rfl, rfl⟩) ?_
  rintro j' g fl V₁ ⟨rfl, rfl, hV₁⟩ U t₁ hKU hAU hrU hgU -
  subst V₁
  exact tail331 E hKU hAU hrU (by rw [hgU]; exact hs) hIW

theorem from788 (E : Ev prof F Wl L s₀ o gev gP gE fb S g0 e₂ code₂ j₂ I Ok ch ln sp kp) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = cps_at.add 788) (hs : Y.cpu.gpr.rsp = aR S) (hIW : I W) :
    GoG prof L o gev gP gE Y t := by
  refine (c_788 prof fb).run E.c E.hfs E.hin (fun j' g' _ V' => j' = 331 ∧ g' = Y.cpu.gpr ∧ V' = W)
    hK hA hr (vc_788 fun _ => ⟨rfl, rfl, rfl⟩) ?_
  rintro j' g fl V₁ ⟨rfl, rfl, hV₁⟩ U t₁ hKU hAU hrU hgU -
  subst V₁
  exact tail331 E hKU hAU hrU (by rw [hgU]; exact hs) hIW

/-! ## The error messages -/

theorem from407 (E : Ev prof F Wl L s₀ o gev gP gE fb S g0 e₂ code₂ j₂ I Ok ch ln sp kp) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = cps_at.add 407) (hs : Y.cpu.gpr.rsp = aR S) (hIW : I W) :
    GoG prof L o gev gP gE Y t := by
  refine callK E hK hA hr hs (lt_len (by decide)) (call_407 _) tgt_407 E.cE (E.k407 _ hIW) trivial ?_
  intro Z W' t₃ hKZ hAZ hrZ hsZ _ _ hIZ
  exact from412 E hKZ hAZ hrZ hsZ hIZ

theorem from504 (E : Ev prof F Wl L s₀ o gev gP gE fb S g0 e₂ code₂ j₂ I Ok ch ln sp kp) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = cps_at.add 504) (hs : Y.cpu.gpr.rsp = aR S) (hIW : I W) :
    GoG prof L o gev gP gE Y t := by
  refine callK E hK hA hr hs (lt_len (by decide)) (call_504 _) tgt_504 E.cE (E.k504 _ hIW) trivial ?_
  intro Z W' t₃ hKZ hAZ hrZ hsZ _ _ hIZ
  exact from509 E hKZ hAZ hrZ hsZ hIZ

theorem from725 (E : Ev prof F Wl L s₀ o gev gP gE fb S g0 e₂ code₂ j₂ I Ok ch ln sp kp) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = cps_at.add 725) (hs : Y.cpu.gpr.rsp = aR S) (hIW : I W) :
    GoG prof L o gev gP gE Y t := by
  refine callK E hK hA hr hs (lt_len (by decide)) (call_725 _) tgt_725 E.cE (E.k725 _ hIW) trivial ?_
  intro Z W' t₃ hKZ hAZ hrZ hsZ _ _ hIZ
  exact from730 E hKZ hAZ hrZ hsZ hIZ

theorem from754 (E : Ev prof F Wl L s₀ o gev gP gE fb S g0 e₂ code₂ j₂ I Ok ch ln sp kp) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = cps_at.add 754) (hs : Y.cpu.gpr.rsp = aR S) (hIW : I W) :
    GoG prof L o gev gP gE Y t := by
  refine callK E hK hA hr hs (lt_len (by decide)) (call_754 _) tgt_754 E.cE (E.k754 _ hIW) trivial ?_
  intro Z W' t₃ hKZ hAZ hrZ hsZ _ _ hIZ
  exact from759 E hKZ hAZ hrZ hsZ hIZ

theorem from783 (E : Ev prof F Wl L s₀ o gev gP gE fb S g0 e₂ code₂ j₂ I Ok ch ln sp kp) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = cps_at.add 783) (hs : Y.cpu.gpr.rsp = aR S) (hIW : I W) :
    GoG prof L o gev gP gE Y t := by
  refine callK E hK hA hr hs (lt_len (by decide)) (call_783 _) tgt_783 E.cE (E.k783 _ hIW) trivial ?_
  intro Z W' t₃ hKZ hAZ hrZ hsZ _ _ hIZ
  exact from788 E hKZ hAZ hrZ hsZ hIZ

/-- "Incorrect postfix" (485). -/
theorem from485 (E : Ev prof F Wl L s₀ o gev gP gE fb S g0 e₂ code₂ j₂ I Ok ch ln sp kp) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = cps_at.add 485) (hs : Y.cpu.gpr.rsp = aR S) (hIW : I W) :
    GoG prof L o gev gP gE Y t := by
  refine (c_485 prof fb).run E.c E.hfs E.hin (fun j' g' _ V' => j' = 504 ∧ V' = W ∧ g'.rsp = Y.cpu.gpr.rsp)
    hK hA hr (vc_485 (by rw [hs]; exact E.f24) fun _ a _ _ => ⟨rfl, rfl, a⟩) ?_
  rintro j' g fl V₁ ⟨rfl, hV₁, gs⟩ U t₁ hKU hAU hrU hgU -
  subst V₁ hgU
  exact from504 E hKU hAU hrU (gs.trans hs) hIW

/-- "Too short" (706). -/
theorem from706 (E : Ev prof F Wl L s₀ o gev gP gE fb S g0 e₂ code₂ j₂ I Ok ch ln sp kp) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = cps_at.add 706) (hs : Y.cpu.gpr.rsp = aR S) (hIW : I W) :
    GoG prof L o gev gP gE Y t := by
  refine (c_706 prof fb).run E.c E.hfs E.hin (fun j' g' _ V' => j' = 725 ∧ V' = W ∧ g'.rsp = Y.cpu.gpr.rsp)
    hK hA hr (vc_706 (by rw [hs]; exact E.f24) fun _ a _ _ => ⟨rfl, rfl, a⟩) ?_
  rintro j' g fl V₁ ⟨rfl, hV₁, gs⟩ U t₁ hKU hAU hrU hgU -
  subst V₁ hgU
  exact from725 E hKU hAU hrU (gs.trans hs) hIW

/-- "Unknown switch" (735). -/
theorem from735 (E : Ev prof F Wl L s₀ o gev gP gE fb S g0 e₂ code₂ j₂ I Ok ch ln sp kp) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = cps_at.add 735) (hs : Y.cpu.gpr.rsp = aR S) (hIW : I W) :
    GoG prof L o gev gP gE Y t := by
  refine (c_735 prof fb).run E.c E.hfs E.hin (fun j' g' _ V' => j' = 754 ∧ V' = W ∧ g'.rsp = Y.cpu.gpr.rsp)
    hK hA hr (vc_735 (by rw [hs]; exact E.f24) fun _ a _ _ => ⟨rfl, rfl, a⟩) ?_
  rintro j' g fl V₁ ⟨rfl, hV₁, gs⟩ U t₁ hKU hAU hrU hgU -
  subst V₁ hgU
  exact from754 E hKU hAU hrU (gs.trans hs) hIW

/-- `kSimple` (307): `pos` = `len` to 317, else "Too long" (783). -/
theorem from307 (E : Ev prof F Wl L s₀ o gev gP gE fb S g0 e₂ code₂ j₂ I Ok ch ln sp kp) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = cps_at.add 307) (hs : Y.cpu.gpr.rsp = aR S)
    (h14 : Y.cpu.gpr.r14 = g0.rsi) (hIW : I W) :
    GoG prof L o gev gP gE Y t := by
  refine (c_307 prof fb).run E.c E.hfs E.hin (fun j' g' _ V' => V' = W ∧ g'.rsp = Y.cpu.gpr.rsp ∧
      (j' = 783 ∨ j' = 317)) hK hA hr
    (vc_307 (by rw [h14]; exact E.fs8) (by rw [hs]; exact E.f24) (fun _ a _ _ => ⟨rfl, a, Or.inl rfl⟩)
      fun _ => ⟨rfl, rfl, Or.inr rfl⟩) ?_
  rintro j' g fl V₁ ⟨hV₁, gs, hj⟩ U t₁ hKU hAU hrU hgU -
  subst V₁ hgU
  rcases hj with rfl | rfl
  · exact from783 E hKU hAU hrU (gs.trans hs) hIW
  · exact from317 E hKU hAU hrU (gs.trans hs) hIW

/-- After the `sete` (435): `WithMinus` to 317, else 485. -/
theorem from435 (E : Ev prof F Wl L s₀ o gev gP gE fb S g0 e₂ code₂ j₂ I Ok ch ln sp kp) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = cps_at.add 435) (hs : Y.cpu.gpr.rsp = aR S) (hIW : I W) :
    GoG prof L o gev gP gE Y t := by
  refine (c_435 prof fb).run E.c E.hfs E.hin (fun j' g' _ V' => V' = W ∧ g' = Y.cpu.gpr ∧ (j' = 317 ∨ j' = 485))
    hK hA hr (vc_435 (fun _ => ⟨rfl, rfl, Or.inl rfl⟩) fun _ => ⟨rfl, rfl, Or.inr rfl⟩) ?_
  rintro j' g fl V₁ ⟨hV₁, rfl, hj⟩ U t₁ hKU hAU hrU hgU -
  subst V₁
  rcases hj with rfl | rfl
  · exact from317 E hKU hAU hrU (by rw [hgU]; exact hs) hIW
  · exact from485 E hKU hAU hrU (by rw [hgU]; exact hs) hIW

/-- After `FindCharPosInString` (472): `PostCharIndex` stored; not negative to 317, else 485. -/
theorem from472 (E : Ev prof F Wl L s₀ o gev gP gE fb S g0 e₂ code₂ j₂ I Ok ch ln sp kp) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = cps_at.add 472) (hs : Y.cpu.gpr.rsp = aR S) {b : Nat}
    (hb : b < nS g0) (h12 : Y.cpu.gpr.r12 = e24 sp b) (hIW : I W) :
    GoG prof L o gev gP gE Y t := by
  refine (c_472 prof fb).run E.c E.hfs E.hin (fun j' g' _ V' => I V' ∧ g'.rsp = Y.cpu.gpr.rsp ∧
      (j' = 317 ∨ j' = 485)) hK hA hr
    (vc_472 (by rw [h12]; exact E.hok _ _ (E.hro b hb).2.2.1) (by rw [h12]; exact (E.hro b hb).2.2.1) hIW E.hcl
      (fun _ V' hI a _ => ⟨hI, a, Or.inl rfl⟩) fun _ V' hI a _ => ⟨hI, a, Or.inr rfl⟩) ?_
  rintro j' g fl V₁ ⟨hI1, gs, hj⟩ U t₁ hKU hAU hrU hgU -
  subst hgU
  rcases hj with rfl | rfl
  · exact from317 E hKU hAU hrU (gs.trans hs) hI1
  · exact from485 E hKU hAU hrU (gs.trans hs) hI1

/-- `FindCharPosInString (PostCharSet, c)` (`k467`), from its return 472. -/
theorem from467 (E : Ev prof F Wl L s₀ o gev gP gE fb S g0 e₂ code₂ j₂ I Ok ch ln sp kp) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = cps_at.add 467) (hs : Y.cpu.gpr.rsp = aR S) {b : Nat}
    (hb : b < nS g0) (h12 : Y.cpu.gpr.r12 = e24 sp b) (hIW : I W) :
    GoG prof L o gev gP gE Y t := by
  refine callK E hK hA hr hs (lt_len (by decide)) (call_467 _) tgt_467 E.cF (E.k467 _ hIW) trivial ?_
  intro Z W' t₃ hKZ hAZ hrZ hsZ hkZ _ hIZ
  exact from472 E hKZ hAZ hrZ hsZ hb (hkZ.2.2.1.trans h12) hIZ

end Runs

end FV7z.Cps
