import FV7z.Api.Cuts
import FV7z.Lemmas.LeafRet
import FV7z.Lemmas.FnFar
/-!
# `NWildcard::CCensor::AddPreItem` (PLAN.md §M, M1): the run through the callees

7-Zip 26.06's `NWildcard::CCensor::AddPreItem (include, path, props)` (`CPP/Common/Wildcard.cpp`; `objdump -d`) at
`0x453650` in `7zzs`: `this` = `rdi` (`rbx`), `include` = `esi` (`r13`, zero-extended), `path` = `rdx` (`r14`),
`props` = `rcx` (`r12`). `_preItems` is a `CObjectVector` at `this + 0x18` (`_items`), `_size` at `+ 0x20`,
`_capacity` at `+ 0x24`. `S` the stack pointer and `g0` the registers at the entry: six pushes (`r15`, `r14`, `r13`,
`r12`, `rbp`, `rbx`) and `sub rsp, 0x18` (`aR S`). When `_size` = `_capacity` (0..36, to 43), above 0x7ffffffe the
`ja` at 43 to the throw at `0x4018c6` (`kt`); else (49) the new capacity (`cmova`), `operator new []` (80,
`0x6029b0`), and (85) `memcpy` of the old items (223, `0x401070`; the old `_items` kept at `rsp + 8` across it) when
`_size` is not 0, `delete []` of the old array (236, `0x6014f0`) when not null, then (108) `_items` and `_capacity`
stored. At 115 `operator new (0x18)` (120, `0x602970`), (125) the item's `UString` made (131, `0x44d3e0`), (136) the
item's flags word, `_size + 1` and the slot `_items[_size]` stored, `item.Path = path` (166, `0x44d710`), (171)
`item.Include` and the three bytes of `props`, the epilogue, `ret` (207). Not covered: the landing pad (246..).

The callees are continuations (`KC`, as in `FV7z/Dfn/Holds.lean`), with what they give back (`B`: for `operator new`,
the item's fields writable, `Ob`). The bytes are tracked by an invariant `I` the caller chooses: it holds after the
pushes (`hI0`), every callee returns with it, it gives the saved registers and the return address (`Stk`), and it
is kept by a store of `n` bytes at `a` when `Ok a n` (`hcl`); `Ok` gives the store's footprint (`hok`), holds for
`_items`, `_size`, `_capacity` (`o24`, `o32`, `o36`), the stack slot at `aR S + 8` (`os8`) and the slot
`_items[_size]` (`hsl`).

- `Fm`, `Fr`, `KS`, `Stk`, `Ob`, `KC`, `Ev`: the frame, what a piece keeps, the callee-saved registers, the stack,
  the item's fields, the callees, the hypotheses of the runs; `callK`: a `call` and the callee's return.
- `vc_*`: the pieces; `tail171`, `from136`, `from125`, `from115`, `from108`, `from241`, `from233`, `from228`,
  `from85`, `from49`: the runs from the cut points.
- `api_ok`: from the entry to the return address (or the throw).
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Api
set_option linter.unusedVariables false

/-! ## The instructions outside the blocks -/

/-- The `ja` to the throw. -/
def pja : List Byte := [0x0f, 0x87, 0x45, 0xe2, 0xfa, 0xff]
theorem pja_0 : ∀ feat, Dec feat pja 0 (FV7z.mk (.jcc 7) 64 [.rel 18446744073709216325] 6) := by dec_rfl
theorem wa_43 : pja <+: api.drop 43 := by decide +kernel
theorem ja_43 (feat : Features) : Dec feat api 43 (FV7z.mk (.jcc 7) 64 [.rel 18446744073709216325] 6) :=
  Dec.shift (j := 43) (k := 0) (pja_0 feat) wa_43 (Nat.zero_le _)

/-- The `call` of `operator new []`. -/
def pc80 : List Byte := [0xe8, 0x0b, 0xf3, 0x1a, 0x00]
theorem pc80_0 : ∀ feat, Dec feat pc80 0 (FV7z.mk .call 64 [.rel 1766155] 5) := by dec_rfl
theorem wc_80 : pc80 <+: api.drop 80 := by decide +kernel
theorem call_80 (feat : Features) : Dec feat api 80 (FV7z.mk .call 64 [.rel 1766155] 5) :=
  Dec.shift (j := 80) (k := 0) (pc80_0 feat) wc_80 (Nat.zero_le _)
theorem tgt_80 : api_at.add (80 + 5) + BitVec.ofNat 64 1766155 = 0x6029b0#64 := by decide

/-- The `call` of `operator new`. -/
def pc120 : List Byte := [0xe8, 0xa3, 0xf2, 0x1a, 0x00]
theorem pc120_0 : ∀ feat, Dec feat pc120 0 (FV7z.mk .call 64 [.rel 1766051] 5) := by dec_rfl
theorem wc_120 : pc120 <+: api.drop 120 := by decide +kernel
theorem call_120 (feat : Features) : Dec feat api 120 (FV7z.mk .call 64 [.rel 1766051] 5) :=
  Dec.shift (j := 120) (k := 0) (pc120_0 feat) wc_120 (Nat.zero_le _)
theorem tgt_120 : api_at.add (120 + 5) + BitVec.ofNat 64 1766051 = 0x602970#64 := by decide

/-- The `call` of the item's `UString` constructor. -/
def pc131 : List Byte := [0xe8, 0x08, 0x9d, 0xff, 0xff]
theorem pc131_0 : ∀ feat, Dec feat pc131 0 (FV7z.mk .call 64 [.rel 18446744073709526280] 5) := by dec_rfl
theorem wc_131 : pc131 <+: api.drop 131 := by decide +kernel
theorem call_131 (feat : Features) : Dec feat api 131 (FV7z.mk .call 64 [.rel 18446744073709526280] 5) :=
  Dec.shift (j := 131) (k := 0) (pc131_0 feat) wc_131 (Nat.zero_le _)
theorem tgt_131 : api_at.add (131 + 5) + BitVec.ofNat 64 18446744073709526280 = 0x44d3e0#64 := by decide

/-- The `call` of `UString::operator =`. -/
def pc166 : List Byte := [0xe8, 0x15, 0xa0, 0xff, 0xff]
theorem pc166_0 : ∀ feat, Dec feat pc166 0 (FV7z.mk .call 64 [.rel 18446744073709527061] 5) := by dec_rfl
theorem wc_166 : pc166 <+: api.drop 166 := by decide +kernel
theorem call_166 (feat : Features) : Dec feat api 166 (FV7z.mk .call 64 [.rel 18446744073709527061] 5) :=
  Dec.shift (j := 166) (k := 0) (pc166_0 feat) wc_166 (Nat.zero_le _)
theorem tgt_166 : api_at.add (166 + 5) + BitVec.ofNat 64 18446744073709527061 = 0x44d710#64 := by decide

/-- The `call` of `memcpy`. -/
def pc223 : List Byte := [0xe8, 0x3c, 0xd9, 0xfa, 0xff]
theorem pc223_0 : ∀ feat, Dec feat pc223 0 (FV7z.mk .call 64 [.rel 18446744073709214012] 5) := by dec_rfl
theorem wc_223 : pc223 <+: api.drop 223 := by decide +kernel
theorem call_223 (feat : Features) : Dec feat api 223 (FV7z.mk .call 64 [.rel 18446744073709214012] 5) :=
  Dec.shift (j := 223) (k := 0) (pc223_0 feat) wc_223 (Nat.zero_le _)
theorem tgt_223 : api_at.add (223 + 5) + BitVec.ofNat 64 18446744073709214012 = 0x401070#64 := by decide

/-- The `call` of `operator delete []`. -/
def pc236 : List Byte := [0xe8, 0xaf, 0xdd, 0x1a, 0x00]
theorem pc236_0 : ∀ feat, Dec feat pc236 0 (FV7z.mk .call 64 [.rel 1760687] 5) := by dec_rfl
theorem wc_236 : pc236 <+: api.drop 236 := by decide +kernel
theorem call_236 (feat : Features) : Dec feat api 236 (FV7z.mk .call 64 [.rel 1760687] 5) :=
  Dec.shift (j := 236) (k := 0) (pc236_0 feat) wc_236 (Nat.zero_le _)
theorem tgt_236 : api_at.add (236 + 5) + BitVec.ofNat 64 1760687 = 0x6014f0#64 := by decide

/-- The `ret`. -/
def pret : List Byte := [0xc3]
theorem pret_0 : ∀ feat, Dec feat pret 0 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem wt_207 : pret <+: api.drop 207 := by decide +kernel
theorem ret_207 (feat : Features) : Dec feat api 207 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 207) (k := 0) (pret_0 feat) wt_207 (Nat.zero_le _)

/-! ## The frame -/

/-- The stack pointer after the six pushes and `sub rsp, 0x18`. -/
abbrev aR (S : Addr) : Addr := S - 8 - 8 - 8 - 8 - 8 - 8 - 24#64

/-- The bytes after the six pushes (`r15`, `r14`, `r13`, `r12`, `rbp`, `rbx`). -/
abbrev P6 (V : Addr → Byte) (g : Gprs) : Addr → Byte :=
  Vst (Vst (Vst (Vst (Vst (Vst V (g.rsp - 8) (toBytesLE g.r15 8)) (g.rsp - 8 - 8) (toBytesLE g.r14 8))
    (g.rsp - 8 - 8 - 8) (toBytesLE g.r13 8)) (g.rsp - 8 - 8 - 8 - 8) (toBytesLE g.r12 8))
    (g.rsp - 8 - 8 - 8 - 8 - 8) (toBytesLE g.rbp 8)) (g.rsp - 8 - 8 - 8 - 8 - 8 - 8) (toBytesLE g.rbx 8)

theorem q1 (S : Addr) : aR S + 24#64 = S - 8 - 8 - 8 - 8 - 8 - 8 := by
  show S - 8 - 8 - 8 - 8 - 8 - 8 - 24#64 + 24#64 = _; bv_omega
theorem q2 (S : Addr) : aR S + 24#64 + 8 = S - 8 - 8 - 8 - 8 - 8 := by
  show S - 8 - 8 - 8 - 8 - 8 - 8 - 24#64 + 24#64 + 8 = _; bv_omega
theorem q3 (S : Addr) : aR S + 24#64 + 8 + 8 = S - 8 - 8 - 8 - 8 := by
  show S - 8 - 8 - 8 - 8 - 8 - 8 - 24#64 + 24#64 + 8 + 8 = _; bv_omega
theorem q4 (S : Addr) : aR S + 24#64 + 8 + 8 + 8 = S - 8 - 8 - 8 := by
  show S - 8 - 8 - 8 - 8 - 8 - 8 - 24#64 + 24#64 + 8 + 8 + 8 = _; bv_omega
theorem q5 (S : Addr) : aR S + 24#64 + 8 + 8 + 8 + 8 = S - 8 - 8 := by
  show S - 8 - 8 - 8 - 8 - 8 - 8 - 24#64 + 24#64 + 8 + 8 + 8 + 8 = _; bv_omega
theorem q6 (S : Addr) : aR S + 24#64 + 8 + 8 + 8 + 8 + 8 = S - 8 := by
  show S - 8 - 8 - 8 - 8 - 8 - 8 - 24#64 + 24#64 + 8 + 8 + 8 + 8 + 8 = _; bv_omega
theorem q7 (S : Addr) : aR S + 24#64 + 8 + 8 + 8 + 8 + 8 + 8 = S := by
  show S - 8 - 8 - 8 - 8 - 8 - 8 - 24#64 + 24#64 + 8 + 8 + 8 + 8 + 8 + 8 = _; bv_omega

/-- The frame from the prologue on: `rsp` = `aR S`, `rbx` = `this`, `r12` = `props`, `r13` = `include`
(zero-extended), `r14` = `path`. -/
abbrev Fm (S : Addr) (g0 g : Gprs) : Prop :=
  g.rsp = aR S ∧ g.rbx = g0.rdi ∧ g.r12 = g0.rcx ∧ g.r13 = BitVec.setWidth 64 (BitVec.setWidth 32 g0.rsi) ∧
    g.r14 = g0.rdx

/-- What a piece keeps: `rsp`, `rbx`, `r12`, `r13`, `r14`. -/
abbrev Fr (g g' : Gprs) : Prop :=
  g'.rsp = g.rsp ∧ g'.rbx = g.rbx ∧ g'.r12 = g.r12 ∧ g'.r13 = g.r13 ∧ g'.r14 = g.r14

/-- The callee-saved registers as in `g`. -/
abbrev KS (g g' : Gprs) : Prop :=
  g'.rbx = g.rbx ∧ g'.rbp = g.rbp ∧ g'.r12 = g.r12 ∧ g'.r13 = g.r13 ∧ g'.r14 = g.r14 ∧ g'.r15 = g.r15

theorem Fm.fr {S : Addr} {g0 g g' : Gprs} (h : Fm S g0 g) (h' : Fr g g') : Fm S g0 g' :=
  ⟨h'.1.trans h.1, h'.2.1.trans h.2.1, h'.2.2.1.trans h.2.2.1, h'.2.2.2.1.trans h.2.2.2.1,
    h'.2.2.2.2.trans h.2.2.2.2⟩

/-- Back from a callee: `rsp` as before the `call`, the callee-saved registers kept. -/
theorem fm_ret {S : Addr} {g0 g g' : Gprs} (h : Fm S g0 g) (hs : g'.rsp = aR S) (hk : KS g g') : Fm S g0 g' :=
  ⟨hs, hk.1.trans h.2.1, hk.2.2.1.trans h.2.2.1, hk.2.2.2.1.trans h.2.2.2.1, hk.2.2.2.2.1.trans h.2.2.2.2⟩

/-- The stack (`ra` the return address): the six saved registers and the return address. -/
abbrev Stk (W : Addr → Byte) (S : Addr) (g0 : Gprs) (ra : Addr) : Prop :=
  rdq(W, S - 8 - 8 - 8 - 8 - 8 - 8) = g0.rbx ∧ rdq(W, S - 8 - 8 - 8 - 8 - 8) = g0.rbp ∧
    rdq(W, S - 8 - 8 - 8 - 8) = g0.r12 ∧ rdq(W, S - 8 - 8 - 8) = g0.r13 ∧ rdq(W, S - 8 - 8) = g0.r14 ∧
    rdq(W, S - 8) = g0.r15 ∧ rdq(W, S) = ra

/-- The item's fields the code stores into (at `p`): the flags word, `Include`, the three bytes of `props`. -/
abbrev Ob (Ok : Addr → Nat → Prop) (p : Addr) : Prop :=
  Ok (p + 16#64) 4 ∧ Ok (p + 16#64) 1 ∧ Ok (p + 17#64) 2 ∧ Ok (p + 19#64) 1

/-- A callee from the `call` before `j` (entry `ent`, the bytes `W`, the registers `A`): at its entry, and from its
return at `j` with `rsp` = `aR S`, the callee-saved registers as at its entry, `B` and the invariant `I`, the run
goes on to the goal. -/
def KC (prof : Profile) (F : Footprint) (Wl : List Rgn) (L : List (Addr × List Byte)) (s₀ : State) (o : Oracle)
    (gev : List Event) (gP : State → Nat → List Event → Prop) (gE : Outcome → List Event → Prop)
    (S : Addr) (I : (Addr → Byte) → Prop) (ent : Addr) (j : Nat) (W : Addr → Byte) (A B : Gprs → Prop) : Prop :=
  ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y →
    Agree F Y.proc.mm.mem (Vst W (aR S - 8) (toBytesLE (api_at.add j) 8)) →
    Y.cpu.rip = ent → Y.cpu.gpr.rsp = aR S - 8 → A Y.cpu.gpr →
    (∀ (Z : State) (W' : Addr → Byte) (t'' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem W' →
      Z.cpu.rip = api_at.add j → Z.cpu.gpr.rsp = aR S → KS Y.cpu.gpr Z.cpu.gpr → B Z.cpu.gpr → I W' →
      GoG prof L o gev gP gE Z t'') →
    GoG prof L o gev gP gE Y t'

/-- The hypotheses of the runs from the cut points (`S`, `g0` the entry's stack pointer and registers, `e₂.add j₂`
the return address, `I` the invariant of the bytes, `Ok` the stores that keep it). -/
structure Ev (prof : Profile) (F : Footprint) (Wl : List Rgn) (L : List (Addr × List Byte)) (s₀ : State)
    (o : Oracle) (gev : List Event) (gP : State → Nat → List Event → Prop) (gE : Outcome → List Event → Prop)
    (S : Addr) (g0 : Gprs) (e₂ : Addr) (code₂ : List Byte) (j₂ : Nat) (I : (Addr → Byte) → Prop)
    (Ok : Addr → Nat → Prop) : Prop where
  c : Seg prof F Wl L s₀ o
  hin : CodeIn L api_at api
  hin₂ : CodeIn L e₂ code₂
  h₂ : j₂ < code₂.length
  hI : ∀ W, I W → Stk W S g0 (e₂.add j₂)
  hok : ∀ a n, Ok a n → ∀ i < n, Foot Wl (Addr.add a i)
  hcl : ∀ (W : Addr → Byte) (a : Addr) (n : Nat) (bs : List Byte), bs.length = n → Ok a n → I W → I (Vst W a bs)
  o24 : Ok (g0.rdi + 24#64) 8
  o32 : Ok (g0.rdi + 32#64) 4
  o36 : Ok (g0.rdi + 36#64) 4
  os8 : Ok (aR S + 8#64) 8
  hsl : ∀ W, I W → Ok (rdq(W, g0.rdi + 24#64) + BitVec.setWidth 64 rdd(W, g0.rdi + 32#64) * 8#64) 8
  fp0 : ∀ i < 2, Foot F.data (Addr.add g0.rcx i)
  fp2 : ∀ i < 1, Foot F.data (Addr.add (g0.rcx + 2#64) i)
  fb48 : ∀ i < 8, Foot F.data (Addr.add (S - 8 - 8 - 8 - 8 - 8 - 8) i)
  fb40 : ∀ i < 8, Foot F.data (Addr.add (S - 8 - 8 - 8 - 8 - 8) i)
  fb32 : ∀ i < 8, Foot F.data (Addr.add (S - 8 - 8 - 8 - 8) i)
  fb24 : ∀ i < 8, Foot F.data (Addr.add (S - 8 - 8 - 8) i)
  fb16 : ∀ i < 8, Foot F.data (Addr.add (S - 8 - 8) i)
  fb8 : ∀ i < 8, Foot F.data (Addr.add (S - 8) i)
  hl : ∀ i < 8, Foot F.data (Addr.add S i)
  hr8 : ∀ i < 8, Foot Wl (Addr.add (aR S - 8) i)
  cN2 : ∃ code : List Byte, CodeIn L 0x6029b0#64 code ∧ 0 < code.length
  cN : ∃ code : List Byte, CodeIn L 0x602970#64 code ∧ 0 < code.length
  cC : ∃ code : List Byte, CodeIn L 0x44d3e0#64 code ∧ 0 < code.length
  cA : ∃ code : List Byte, CodeIn L 0x44d710#64 code ∧ 0 < code.length
  cM : ∃ code : List Byte, CodeIn L 0x401070#64 code ∧ 0 < code.length
  cD : ∃ code : List Byte, CodeIn L 0x6014f0#64 code ∧ 0 < code.length
  k80 : ∀ W, I W → KC prof F Wl L s₀ o gev gP gE S I 0x6029b0#64 85 W (fun _ => True) (fun _ => True)
  k120 : ∀ W, I W → KC prof F Wl L s₀ o gev gP gE S I 0x602970#64 125 W (fun _ => True) (fun g => Ob Ok g.rax)
  k131 : ∀ W, I W → KC prof F Wl L s₀ o gev gP gE S I 0x44d3e0#64 136 W (fun _ => True) (fun _ => True)
  k166 : ∀ W, I W → KC prof F Wl L s₀ o gev gP gE S I 0x44d710#64 171 W (fun g => g.rsi = g0.rdx) (fun _ => True)
  k223 : ∀ W, I W → KC prof F Wl L s₀ o gev gP gE S I 0x401070#64 228 W (fun _ => True) (fun _ => True)
  k236 : ∀ W, I W → KC prof F Wl L s₀ o gev gP gE S I 0x6014f0#64 241 W (fun _ => True) (fun _ => True)
  kr : ∀ (W : Addr → Byte) (Z' : State) (t' : Nat), KeptW Wl s₀ Z' → Agree F Z'.proc.mm.mem W →
    Z'.cpu.rip = e₂.add j₂ → Z'.cpu.gpr.rsp = S + 8 → KS g0 Z'.cpu.gpr → I W → GoG prof L o gev gP gE Z' t'

/-! ## The pieces -/

section Pieces
variable {F : Footprint} {Wl : List Rgn} {I : (Addr → Byte) → Prop} {Ok : Addr → Nat → Prop}

/-- The pushes, `r14` = `path`, `r13d` = `include`, `r12` = `props`, `rbx` = `this`, the frame, `eax` =
`_capacity` compared with `_size`: to 115, or (equal) `cmp eax, 0x7ffffffe` to the `ja` at 43. -/
theorem vc_0 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (hs1 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8) i)) (hs2 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8) i))
    (hs3 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8 - 8) i))
    (hs4 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8 - 8 - 8) i))
    (hs5 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8 - 8 - 8 - 8) i))
    (hs6 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8 - 8 - 8 - 8 - 8) i))
    (f36 : ∀ i < 4, Foot F.data (Addr.add (g.rdi + 36#64) i))
    (f32 : ∀ i < 4, Foot F.data (Addr.add (g.rdi + 32#64) i))
    (h115 : ∀ g', g'.rsp = aR g.rsp → g'.rbx = g.rdi → g'.r12 = g.rcx →
      g'.r13 = BitVec.setWidth 64 (BitVec.setWidth 32 g.rsi) → g'.r14 = g.rdx → ∀ fl, Q 115 g' fl (P6 V g))
    (h43 : ∀ g', g'.rsp = aR g.rsp → g'.rbx = g.rdi → g'.r12 = g.rcx →
      g'.r13 = BitVec.setWidth 64 (BitVec.setWidth 32 g.rsi) → g'.r14 = g.rdx → ∀ fl, Q 43 g' fl (P6 V g)) :
    W_0 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [aR, P6] at hs1 hs2 hs3 hs4 hs5 hs6 f36 f32 h115 h43 ⊢
  wpx [W_0, W_38, o0, o1, Op.cmpmr]
  all_goals repeat' (first
    | refine h115 _ ?_ ?_ ?_ ?_ ?_ _
    | refine h43 _ ?_ ?_ ?_ ?_ ?_ _
    | with_reducible rfl
    | with_reducible exact hs1
    | with_reducible exact hs2
    | with_reducible exact hs3
    | with_reducible exact hs4
    | with_reducible exact hs5
    | with_reducible exact hs6
    | with_reducible exact f36
    | with_reducible exact f32
    | apply And.intro
    | intro _)

/-- The new capacity (`cmova`), `rdi` = 8 times it: to `operator new []` (80). -/
theorem vc_49 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (h : ∀ g', Fr g g' → ∀ fl, Q 80 g' fl V) :
    W_49 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_49, o2, Op.shl64]
  all_goals repeat' (first
    | refine h _ ?_ _
    | with_reducible rfl
    | apply And.intro
    | intro _)

/-- `_size`, the old `_items`, `r15` = the new array: `_size` not 0, the old `_items` kept at `rsp + 8`, to
`memcpy` (223); else the old `_items` not null to `delete []` (233), or to 108. -/
theorem vc_85 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (f32 : ∀ i < 4, Foot F.data (Addr.add (g.rbx + 32#64) i))
    (f24 : ∀ i < 8, Foot F.data (Addr.add (g.rbx + 24#64) i))
    (ws8 : ∀ i < 8, Foot Wl (Addr.add (g.rsp + 8#64) i)) (os8 : Ok (g.rsp + 8#64) 8) (hI : I V)
    (hcl : ∀ (W : Addr → Byte) (a : Addr) (n : Nat) (bs : List Byte), bs.length = n → Ok a n → I W →
      I (Vst W a bs))
    (h223 : ∀ g' V', I V' → Fr g g' → ∀ fl, Q 223 g' fl V')
    (h233 : ∀ g' V', I V' → Fr g g' → ∀ fl, Q 233 g' fl V')
    (h108 : ∀ g' V', I V' → Fr g g' → ∀ fl, Q 108 g' fl V') :
    W_85 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at f32 f24 ws8 os8 h223 h233 h108 ⊢
  wpx [W_85, W_208, W_99, o3, o10, o4, Op.shl64]
  all_goals repeat' (first
    | refine h223 _ _ ?_ ?_ _
    | refine h233 _ _ ?_ ?_ _
    | refine h108 _ _ ?_ ?_ _
    | with_reducible rfl
    | with_reducible exact hI
    | refine hcl _ _ _ _ (toBytesLE_length _ _) ?_ ?_
    | with_reducible exact f32
    | with_reducible exact f24
    | with_reducible exact ws8
    | with_reducible exact os8
    | apply And.intro
    | intro _)

/-- `_items` = the new array, `_capacity` = the new capacity: to 115. -/
theorem vc_108 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (w24 : ∀ i < 8, Foot Wl (Addr.add (g.rbx + 24#64) i)) (w36 : ∀ i < 4, Foot Wl (Addr.add (g.rbx + 36#64) i))
    (o24 : Ok (g.rbx + 24#64) 8) (o36 : Ok (g.rbx + 36#64) 4) (hI : I V)
    (hcl : ∀ (W : Addr → Byte) (a : Addr) (n : Nat) (bs : List Byte), bs.length = n → Ok a n → I W →
      I (Vst W a bs))
    (h : ∀ g' V', I V' → Fr g g' → ∀ fl, Q 115 g' fl V') :
    W_108 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at w24 w36 o24 o36 h ⊢
  wpx [W_108, o5]
  all_goals repeat' (first
    | refine h _ _ ?_ ?_ _
    | with_reducible rfl
    | with_reducible exact hI
    | refine hcl _ _ _ _ (toBytesLE_length _ _) ?_ ?_
    | with_reducible exact w24
    | with_reducible exact w36
    | with_reducible exact o24
    | with_reducible exact o36
    | apply And.intro
    | intro _)

/-- `edi` = 0x18, to `operator new` (120). -/
theorem vc_115 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} (hI : I V)
    (h : ∀ g' V', I V' → Fr g g' → ∀ fl, Q 120 g' fl V') :
    W_115 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_115, o6]
  all_goals repeat' (first
    | refine h _ _ ?_ ?_ _
    | with_reducible rfl
    | with_reducible exact hI
    | apply And.intro
    | intro _)

/-- `rdi` = `rbp` = the item, to its `UString`'s constructor (131). -/
theorem vc_125 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} (hI : I V)
    (h : ∀ g' V', I V' → g'.rbp = g.rax → g'.rdi = g.rax → Fr g g' → ∀ fl, Q 131 g' fl V') :
    W_125 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h ⊢
  wpx [W_125, o7]
  all_goals repeat' (first
    | refine h _ _ ?_ ?_ ?_ ?_ _
    | with_reducible rfl
    | with_reducible exact hI
    | apply And.intro
    | intro _)

/-- The item's flags word, `_size + 1`, the slot `_items[_size]` = the item; `rsi` = `path`, `rdi` = the item: to
`UString::operator =` (166). -/
theorem vc_136 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (f32 : ∀ i < 4, Foot F.data (Addr.add (g.rbx + 32#64) i))
    (f24 : ∀ i < 8, Foot F.data (Addr.add (g.rbx + 24#64) i))
    (wob : ∀ i < 4, Foot Wl (Addr.add (g.rbp + 16#64) i)) (w32 : ∀ i < 4, Foot Wl (Addr.add (g.rbx + 32#64) i))
    (wsl : ∀ i < 8, Foot Wl (Addr.add (rdq(V, g.rbx + 24#64) + BitVec.setWidth 64 rdd(V, g.rbx + 32#64) * 8#64) i))
    (oob : Ok (g.rbp + 16#64) 4) (o32 : Ok (g.rbx + 32#64) 4)
    (osl : Ok (rdq(V, g.rbx + 24#64) + BitVec.setWidth 64 rdd(V, g.rbx + 32#64) * 8#64) 8) (hI : I V)
    (hcl : ∀ (W : Addr → Byte) (a : Addr) (n : Nat) (bs : List Byte), bs.length = n → Ok a n → I W →
      I (Vst W a bs))
    (h : ∀ g' V', I V' → g'.rdi = g.rbp → g'.rsi = g.r14 → g'.rbp = g.rbp → Fr g g' → ∀ fl, Q 166 g' fl V') :
    W_136 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at f32 f24 wob w32 wsl oob o32 osl h ⊢
  wpx [W_136, o8]
  all_goals repeat' (first
    | refine h _ _ ?_ ?_ ?_ ?_ ?_ _
    | with_reducible rfl
    | with_reducible exact hI
    | refine hcl _ _ _ _ (toBytesLE_length _ _) ?_ ?_
    | refine hcl _ _ 4 _ rfl ?_ ?_
    | with_reducible exact f32
    | with_reducible exact f24
    | with_reducible exact wob
    | with_reducible exact w32
    | with_reducible exact wsl
    | with_reducible exact oob
    | with_reducible exact o32
    | with_reducible exact osl
    | apply And.intro
    | intro _)

/-- `item.Include`, the three bytes of `props`, `add rsp, 0x18`, the six pops, to the `ret`. -/
theorem vc_171 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (fp0 : ∀ i < 2, Foot F.data (Addr.add g.r12 i)) (fp2 : ∀ i < 1, Foot F.data (Addr.add (g.r12 + 2#64) i))
    (w16 : ∀ i < 1, Foot Wl (Addr.add (g.rbp + 16#64) i)) (w17 : ∀ i < 2, Foot Wl (Addr.add (g.rbp + 17#64) i))
    (w19 : ∀ i < 1, Foot Wl (Addr.add (g.rbp + 19#64) i))
    (o16 : Ok (g.rbp + 16#64) 1) (o17 : Ok (g.rbp + 17#64) 2) (o19 : Ok (g.rbp + 19#64) 1) (hI : I V)
    (hcl : ∀ (W : Addr → Byte) (a : Addr) (n : Nat) (bs : List Byte), bs.length = n → Ok a n → I W →
      I (Vst W a bs))
    (f1 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 24#64) i))
    (f2 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 24#64 + 8) i))
    (f3 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 24#64 + 8 + 8) i))
    (f4 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 24#64 + 8 + 8 + 8) i))
    (f5 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 24#64 + 8 + 8 + 8 + 8) i))
    (f6 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 24#64 + 8 + 8 + 8 + 8 + 8) i))
    (h : ∀ g' V', I V' → g'.rsp = g.rsp + 24#64 + 8 + 8 + 8 + 8 + 8 + 8 → g'.rbx = rdq(V', g.rsp + 24#64) →
      g'.rbp = rdq(V', g.rsp + 24#64 + 8) → g'.r12 = rdq(V', g.rsp + 24#64 + 8 + 8) →
      g'.r13 = rdq(V', g.rsp + 24#64 + 8 + 8 + 8) → g'.r14 = rdq(V', g.rsp + 24#64 + 8 + 8 + 8 + 8) →
      g'.r15 = rdq(V', g.rsp + 24#64 + 8 + 8 + 8 + 8 + 8) → ∀ fl, Q 207 g' fl V') :
    W_171 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at fp0 fp2 w16 w17 w19 o16 o17 o19 f1 f2 f3 f4 f5 f6 h ⊢
  wpx [W_171, o9]
  all_goals repeat' (first
    | refine h _ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ _
    | with_reducible rfl
    | with_reducible exact hI
    | refine hcl _ _ _ _ (toBytesLE_length _ _) ?_ ?_
    | with_reducible exact fp0
    | with_reducible exact fp2
    | with_reducible exact w16
    | with_reducible exact w17
    | with_reducible exact w19
    | with_reducible exact o16
    | with_reducible exact o17
    | with_reducible exact o19
    | with_reducible exact f1
    | with_reducible exact f2
    | with_reducible exact f3
    | with_reducible exact f4
    | with_reducible exact f5
    | with_reducible exact f6
    | apply And.intro
    | intro _)

/-- Back from `memcpy`: the old `_items` from `rsp + 8`, to 233. -/
theorem vc_228 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (f8 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8#64) i)) (hI : I V)
    (h : ∀ g' V', I V' → Fr g g' → ∀ fl, Q 233 g' fl V') :
    W_228 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at f8 h ⊢
  wpx [W_228, o11]
  all_goals repeat' (first
    | refine h _ _ ?_ ?_ _
    | with_reducible rfl
    | with_reducible exact hI
    | with_reducible exact f8
    | apply And.intro
    | intro _)

/-- `rdi` = the old `_items`, to `delete []` (236). -/
theorem vc_233 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} (hI : I V)
    (h : ∀ g' V', I V' → Fr g g' → ∀ fl, Q 236 g' fl V') :
    W_233 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_233, o12]
  all_goals repeat' (first
    | refine h _ _ ?_ ?_ _
    | with_reducible rfl
    | with_reducible exact hI
    | apply And.intro
    | intro _)

/-- `jmp` to 108. -/
theorem vc_241 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} (h : ∀ fl, Q 108 g fl V) :
    W_241 F Wl Q g f V := h _

end Pieces

/-! ## The runs -/

section Runs
variable {prof : Profile} {F : Footprint} {Wl : List Rgn} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {S : Addr} {g0 : Gprs} {e₂ : Addr} {code₂ : List Byte} {j₂ : Nat} {I : (Addr → Byte) → Prop}
  {Ok : Addr → Nat → Prop} {Y : State} {t : Nat} {W : Addr → Byte}

/-- A store's footprint in `F.data`. -/
theorem Ev.fd (E : Ev prof F Wl L s₀ o gev gP gE S g0 e₂ code₂ j₂ I Ok) {a : Addr} {n : Nat} (h : Ok a n) :
    ∀ i < n, Foot F.data (Addr.add a i) := fun i hi => E.c.hws _ (E.hok _ _ h i hi)

/-- A `call` at `j` (`rsp` = `aR S`, the bytes `W`) of the callee `k`, and from its return at `j + 5`. -/
theorem callK (E : Ev prof F Wl L s₀ o gev gP gE S g0 e₂ code₂ j₂ I Ok) {U : State} {t₁ : Nat} {j R : Nat}
    {ent : Addr} {A B : Gprs → Prop} (hKU : KeptW Wl s₀ U) (hAU : Agree F U.proc.mm.mem W)
    (hrU : U.cpu.rip = api_at.add j) (hs : U.cpu.gpr.rsp = aR S) (hj : j < api.length)
    (hd : Dec prof.feat api j (FV7z.mk .call 64 [.rel R] 5)) (htgt : api_at.add (j + 5) + BitVec.ofNat 64 R = ent)
    (hc : ∃ code : List Byte, CodeIn L ent code ∧ 0 < code.length)
    (k : KC prof F Wl L s₀ o gev gP gE S I ent (j + 5) W A B) (hA : A (U.cpu.gpr.set 4 (aR S - 8)))
    (h : ∀ (Z : State) (W' : Addr → Byte) (t'' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem W' →
      Z.cpu.rip = api_at.add (j + 5) → Z.cpu.gpr.rsp = aR S → KS U.cpu.gpr Z.cpu.gpr → B Z.cpu.gpr → I W' →
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

/-- From 171 (`rbp` = the item): the item's fields, the epilogue, the `ret`, to `kr`. -/
theorem tail171 (E : Ev prof F Wl L s₀ o gev gP gE S g0 e₂ code₂ j₂ I Ok) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = api_at.add 171) (hm : Fm S g0 Y.cpu.gpr)
    (hob : Ob Ok Y.cpu.gpr.rbp) (hIW : I W) :
    GoG prof L o gev gP gE Y t := by
  obtain ⟨ms, mx, m12, m13, m14⟩ := hm
  refine (c_171 prof).run E.c E.hin (fun j' g' _ V' => j' = 207 ∧ I V' ∧
      g'.rsp = Y.cpu.gpr.rsp + 24#64 + 8 + 8 + 8 + 8 + 8 + 8 ∧ g'.rbx = rdq(V', Y.cpu.gpr.rsp + 24#64) ∧
      g'.rbp = rdq(V', Y.cpu.gpr.rsp + 24#64 + 8) ∧ g'.r12 = rdq(V', Y.cpu.gpr.rsp + 24#64 + 8 + 8) ∧
      g'.r13 = rdq(V', Y.cpu.gpr.rsp + 24#64 + 8 + 8 + 8) ∧ g'.r14 = rdq(V', Y.cpu.gpr.rsp + 24#64 + 8 + 8 + 8 + 8) ∧
      g'.r15 = rdq(V', Y.cpu.gpr.rsp + 24#64 + 8 + 8 + 8 + 8 + 8))
    hK hA hr
    (vc_171 (by rw [m12]; exact E.fp0) (by rw [m12]; exact E.fp2) (E.hok _ _ hob.2.1) (E.hok _ _ hob.2.2.1)
      (E.hok _ _ hob.2.2.2) hob.2.1 hob.2.2.1 hob.2.2.2 hIW E.hcl (by rw [ms, q1]; exact E.fb48)
      (by rw [ms, q2]; exact E.fb40) (by rw [ms, q3]; exact E.fb32) (by rw [ms, q4]; exact E.fb24)
      (by rw [ms, q5]; exact E.fb16) (by rw [ms, q6]; exact E.fb8)
      fun _ V' hI a b d e f g h _ => ⟨rfl, hI, a, b, d, e, f, g, h⟩) ?_
  rintro j' g fl V₁ ⟨rfl, hI1, gs, gx, gp, g12, g13, g14, g15⟩ U t₁ hKU hAU hrU hgU -
  subst hgU
  obtain ⟨s1, s2, s3, s4, s5, s6, s7⟩ := E.hI V₁ hI1
  have e1 : rdq(V₁, Y.cpu.gpr.rsp + 24#64) = g0.rbx := by rw [ms, q1]; exact s1
  have e2 : rdq(V₁, Y.cpu.gpr.rsp + 24#64 + 8) = g0.rbp := by rw [ms, q2]; exact s2
  have e3 : rdq(V₁, Y.cpu.gpr.rsp + 24#64 + 8 + 8) = g0.r12 := by rw [ms, q3]; exact s3
  have e4 : rdq(V₁, Y.cpu.gpr.rsp + 24#64 + 8 + 8 + 8) = g0.r13 := by rw [ms, q4]; exact s4
  have e5 : rdq(V₁, Y.cpu.gpr.rsp + 24#64 + 8 + 8 + 8 + 8) = g0.r14 := by rw [ms, q5]; exact s5
  have e6 : rdq(V₁, Y.cpu.gpr.rsp + 24#64 + 8 + 8 + 8 + 8 + 8) = g0.r15 := by rw [ms, q6]; exact s6
  have hsU : U.cpu.gpr.rsp = S := by rw [gs, ms]; exact q7 S
  refine E.c.s_ret hKU hAU E.hin (lt_len (by decide)) hrU (ret_207 _) (by rw [hsU]; exact E.hl) E.hin₂ E.h₂
    (by rw [hsU]; exact s7) ?_
  rintro Z' t₂ hKZ' hAZ' ⟨hrZ', hgZ'⟩
  refine E.kr V₁ Z' t₂ hKZ' hAZ' hrZ' ?_ ?_ hI1
  · rw [hgZ']
    show U.cpu.gpr.rsp + 8 = _
    rw [hsU]
  · rw [hgZ']
    exact ⟨gx.trans e1, gp.trans e2, g12.trans e3, g13.trans e4, g14.trans e5, g15.trans e6⟩

/-- From 136 (`rbp` = the item): the item's flags word, `_size + 1`, the slot; `item.Path = path` (`k166`), from its
return 171. -/
theorem from136 (E : Ev prof F Wl L s₀ o gev gP gE S g0 e₂ code₂ j₂ I Ok) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = api_at.add 136) (hm : Fm S g0 Y.cpu.gpr)
    (hob : Ob Ok Y.cpu.gpr.rbp) (hIW : I W) :
    GoG prof L o gev gP gE Y t := by
  have hsl : Ok (rdq(W, Y.cpu.gpr.rbx + 24#64) + BitVec.setWidth 64 rdd(W, Y.cpu.gpr.rbx + 32#64) * 8#64) 8 := by
    rw [hm.2.1]; exact E.hsl W hIW
  refine (c_136 prof).run E.c E.hin (fun j' g' _ V' => j' = 166 ∧ I V' ∧ g'.rdi = Y.cpu.gpr.rbp ∧
      g'.rsi = Y.cpu.gpr.r14 ∧ g'.rbp = Y.cpu.gpr.rbp ∧ Fr Y.cpu.gpr g') hK hA hr
    (vc_136 (by rw [hm.2.1]; exact E.fd E.o32) (by rw [hm.2.1]; exact E.fd E.o24) (E.hok _ _ hob.1)
      (by rw [hm.2.1]; exact E.hok _ _ E.o32) (E.hok _ _ hsl) hob.1 (by rw [hm.2.1]; exact E.o32) hsl hIW E.hcl
      fun _ V' hI a b d e _ => ⟨rfl, hI, a, b, d, e⟩) ?_
  rintro j' g fl V₁ ⟨rfl, hI1, gdi, gsi, gbp, gf⟩ U t₁ hKU hAU hrU hgU -
  subst hgU
  have hmU := Fm.fr hm gf
  refine callK E hKU hAU hrU hmU.1 (lt_len (by decide)) (call_166 _) tgt_166 E.cA (E.k166 _ hI1)
    (gsi.trans hm.2.2.2.2) ?_
  intro Z W' t₃ hKZ hAZ hrZ hsZ hkZ _ hIZ
  exact tail171 E hKZ hAZ hrZ (fm_ret hmU hsZ hkZ) (by rw [hkZ.2.1, gbp]; exact hob) hIZ

/-- From 125 (back from `operator new`, `rax` = the item): its `UString` (`k131`), from its return 136. -/
theorem from125 (E : Ev prof F Wl L s₀ o gev gP gE S g0 e₂ code₂ j₂ I Ok) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = api_at.add 125) (hm : Fm S g0 Y.cpu.gpr)
    (hob : Ob Ok Y.cpu.gpr.rax) (hIW : I W) :
    GoG prof L o gev gP gE Y t := by
  refine (c_125 prof).run E.c E.hin (fun j' g' _ V' => j' = 131 ∧ I V' ∧ g'.rbp = Y.cpu.gpr.rax ∧
      Fr Y.cpu.gpr g') hK hA hr (vc_125 hIW fun _ V' hI a _ e _ => ⟨rfl, hI, a, e⟩) ?_
  rintro j' g fl V₁ ⟨rfl, hI1, gbp, gf⟩ U t₁ hKU hAU hrU hgU -
  subst hgU
  have hmU := Fm.fr hm gf
  refine callK E hKU hAU hrU hmU.1 (lt_len (by decide)) (call_131 _) tgt_131 E.cC (E.k131 _ hI1) trivial ?_
  intro Z W' t₃ hKZ hAZ hrZ hsZ hkZ _ hIZ
  exact from136 E hKZ hAZ hrZ (fm_ret hmU hsZ hkZ) (by rw [hkZ.2.1, gbp]; exact hob) hIZ

/-- From 115: `operator new (0x18)` (`k120`), from its return 125. -/
theorem from115 (E : Ev prof F Wl L s₀ o gev gP gE S g0 e₂ code₂ j₂ I Ok) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = api_at.add 115) (hm : Fm S g0 Y.cpu.gpr) (hIW : I W) :
    GoG prof L o gev gP gE Y t := by
  refine (c_115 prof).run E.c E.hin (fun j' g' _ V' => j' = 120 ∧ I V' ∧ Fr Y.cpu.gpr g') hK hA hr
    (vc_115 hIW fun _ V' hI e _ => ⟨rfl, hI, e⟩) ?_
  rintro j' g fl V₁ ⟨rfl, hI1, gf⟩ U t₁ hKU hAU hrU hgU -
  subst hgU
  have hmU := Fm.fr hm gf
  refine callK E hKU hAU hrU hmU.1 (lt_len (by decide)) (call_120 _) tgt_120 E.cN (E.k120 _ hI1) trivial ?_
  intro Z W' t₃ hKZ hAZ hrZ hsZ hkZ hB hIZ
  exact from125 E hKZ hAZ hrZ (fm_ret hmU hsZ hkZ) hB hIZ

/-- From 108: `_items`, `_capacity` stored, to 115. -/
theorem from108 (E : Ev prof F Wl L s₀ o gev gP gE S g0 e₂ code₂ j₂ I Ok) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = api_at.add 108) (hm : Fm S g0 Y.cpu.gpr) (hIW : I W) :
    GoG prof L o gev gP gE Y t := by
  refine (c_108 prof).run E.c E.hin (fun j' g' _ V' => j' = 115 ∧ I V' ∧ Fr Y.cpu.gpr g') hK hA hr
    (vc_108 (by rw [hm.2.1]; exact E.hok _ _ E.o24) (by rw [hm.2.1]; exact E.hok _ _ E.o36)
      (by rw [hm.2.1]; exact E.o24) (by rw [hm.2.1]; exact E.o36) hIW E.hcl fun _ V' hI e _ => ⟨rfl, hI, e⟩) ?_
  rintro j' g fl V₁ ⟨rfl, hI1, gf⟩ U t₁ hKU hAU hrU hgU -
  subst hgU
  exact from115 E hKU hAU hrU (Fm.fr hm gf) hI1

/-- From 241 (back from `delete []`): `jmp` to 108. -/
theorem from241 (E : Ev prof F Wl L s₀ o gev gP gE S g0 e₂ code₂ j₂ I Ok) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = api_at.add 241) (hm : Fm S g0 Y.cpu.gpr) (hIW : I W) :
    GoG prof L o gev gP gE Y t := by
  refine (c_241 prof).run E.c E.hin (fun j' g' _ V' => j' = 108 ∧ g' = Y.cpu.gpr ∧ V' = W)
    hK hA hr (vc_241 fun _ => ⟨rfl, rfl, rfl⟩) ?_
  rintro j' g fl V₁ ⟨rfl, rfl, hV₁⟩ U t₁ hKU hAU hrU hgU -
  subst V₁
  exact from108 E hKU hAU hrU (by rw [hgU]; exact hm) hIW

/-- From 233: `delete []` of the old array (`k236`), from its return 241. -/
theorem from233 (E : Ev prof F Wl L s₀ o gev gP gE S g0 e₂ code₂ j₂ I Ok) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = api_at.add 233) (hm : Fm S g0 Y.cpu.gpr) (hIW : I W) :
    GoG prof L o gev gP gE Y t := by
  refine (c_233 prof).run E.c E.hin (fun j' g' _ V' => j' = 236 ∧ I V' ∧ Fr Y.cpu.gpr g') hK hA hr
    (vc_233 hIW fun _ V' hI e _ => ⟨rfl, hI, e⟩) ?_
  rintro j' g fl V₁ ⟨rfl, hI1, gf⟩ U t₁ hKU hAU hrU hgU -
  subst hgU
  have hmU := Fm.fr hm gf
  refine callK E hKU hAU hrU hmU.1 (lt_len (by decide)) (call_236 _) tgt_236 E.cD (E.k236 _ hI1) trivial ?_
  intro Z W' t₃ hKZ hAZ hrZ hsZ hkZ _ hIZ
  exact from241 E hKZ hAZ hrZ (fm_ret hmU hsZ hkZ) hIZ

/-- From 228 (back from `memcpy`): to 233. -/
theorem from228 (E : Ev prof F Wl L s₀ o gev gP gE S g0 e₂ code₂ j₂ I Ok) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = api_at.add 228) (hm : Fm S g0 Y.cpu.gpr) (hIW : I W) :
    GoG prof L o gev gP gE Y t := by
  refine (c_228 prof).run E.c E.hin (fun j' g' _ V' => j' = 233 ∧ I V' ∧ Fr Y.cpu.gpr g') hK hA hr
    (vc_228 (by rw [hm.1]; exact E.fd E.os8) hIW fun _ V' hI e _ => ⟨rfl, hI, e⟩) ?_
  rintro j' g fl V₁ ⟨rfl, hI1, gf⟩ U t₁ hKU hAU hrU hgU -
  subst hgU
  exact from233 E hKU hAU hrU (Fm.fr hm gf) hI1

/-- From 85 (back from `operator new []`): `memcpy` (`k223`) and from its return 228; or to 233; or to 108. -/
theorem from85 (E : Ev prof F Wl L s₀ o gev gP gE S g0 e₂ code₂ j₂ I Ok) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = api_at.add 85) (hm : Fm S g0 Y.cpu.gpr) (hIW : I W) :
    GoG prof L o gev gP gE Y t := by
  refine (c_85 prof).run E.c E.hin (fun j' g' _ V' => I V' ∧ Fr Y.cpu.gpr g' ∧ (j' = 223 ∨ j' = 233 ∨ j' = 108))
    hK hA hr
    (vc_85 (by rw [hm.2.1]; exact E.fd E.o32) (by rw [hm.2.1]; exact E.fd E.o24) (by rw [hm.1]; exact E.hok _ _ E.os8)
      (by rw [hm.1]; exact E.os8) hIW E.hcl (fun _ V' hI e _ => ⟨hI, e, Or.inl rfl⟩)
      (fun _ V' hI e _ => ⟨hI, e, Or.inr (Or.inl rfl)⟩) (fun _ V' hI e _ => ⟨hI, e, Or.inr (Or.inr rfl)⟩)) ?_
  rintro j' g fl V₁ ⟨hI1, gf, hj⟩ U t₁ hKU hAU hrU hgU -
  subst hgU
  have hmU := Fm.fr hm gf
  rcases hj with rfl | rfl | rfl
  · refine callK E hKU hAU hrU hmU.1 (lt_len (by decide)) (call_223 _) tgt_223 E.cM (E.k223 _ hI1) trivial ?_
    intro Z W' t₃ hKZ hAZ hrZ hsZ hkZ _ hIZ
    exact from228 E hKZ hAZ hrZ (fm_ret hmU hsZ hkZ) hIZ
  · exact from233 E hKU hAU hrU hmU hI1
  · exact from108 E hKU hAU hrU hmU hI1

/-- From 49 (the `ja` not taken): the new capacity, `operator new []` (`k80`), from its return 85. -/
theorem from49 (E : Ev prof F Wl L s₀ o gev gP gE S g0 e₂ code₂ j₂ I Ok) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = api_at.add 49) (hm : Fm S g0 Y.cpu.gpr) (hIW : I W) :
    GoG prof L o gev gP gE Y t := by
  refine (c_49 prof).run E.c E.hin (fun j' g' _ V' => j' = 80 ∧ V' = W ∧ Fr Y.cpu.gpr g') hK hA hr
    (vc_49 fun _ e _ => ⟨rfl, rfl, e⟩) ?_
  rintro j' g fl V₁ ⟨rfl, hV₁, gf⟩ U t₁ hKU hAU hrU hgU -
  subst V₁ hgU
  have hmU := Fm.fr hm gf
  refine callK E hKU hAU hrU hmU.1 (lt_len (by decide)) (call_80 _) tgt_80 E.cN2 (E.k80 _ hIW) trivial ?_
  intro Z W' t₃ hKZ hAZ hrZ hsZ hkZ _ hIZ
  exact from85 E hKZ hAZ hrZ (fm_ret hmU hsZ hkZ) hIZ

end Runs

variable {prof : Profile} {F : Footprint} {Wl : List Rgn} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {X : State} {t : Nat} {V : Addr → Byte}

/-- `NWildcard::CCensor::AddPreItem (include, path, props)` (`this` = `rdi`, `include` = `esi`, `path` = `rdx`,
`props` = `rcx`) from its entry, `I` an invariant of the bytes kept by the stores `Ok` allows (`hcl`, `hok`): the
pushes' slots and the calls' return address slot in what the run may store into, the return address readable;
`Ok` for `_items`, `_size`, `_capacity` (`o24`, `o32`, `o36`), the stack slot at `aR S + 8` (`os8`) and the slot
`_items[_size]` (`hsl`); the three bytes of `props` readable. `I` holds after the pushes (`hI0`) and gives the stack
(`hI`). The throw (`kt`, the frame `Fm`, bytes with `I`), and the callees, each from its return with `rsp` as it was,
the callee-saved registers as at its entry and `I`: `operator new []` (`k80`), `memcpy` (`k223`), `delete []`
(`k236`), `operator new` (`k120`, giving back the item's fields in `Ok`, `Ob`), the item's `UString` (`k131`),
`item.Path = path` (`k166`, `rsi` = `path`). At the return address (`kr`): `rsp` 8 above the entry's, the
callee-saved registers as they were, bytes with `I`. -/
theorem api_ok {I : (Addr → Byte) → Prop} {Ok : Addr → Nat → Prop} {e₂ : Addr} {code₂ : List Byte} {j₂ : Nat}
    (c : Seg prof F Wl L s₀ o) (hin : CodeIn L api_at api)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = api_at)
    (hs1 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8) i))
    (hs2 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8 - 8) i))
    (hs3 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8 - 8 - 8) i))
    (hs4 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8 - 8 - 8 - 8) i))
    (hs5 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8 - 8 - 8 - 8 - 8) i))
    (hs6 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8 - 8 - 8 - 8 - 8 - 8) i))
    (hr8 : ∀ i < 8, Foot Wl (Addr.add (aR X.cpu.gpr.rsp - 8) i))
    (hl : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsp i))
    (hin₂ : CodeIn L e₂ code₂) (h₂ : j₂ < code₂.length)
    (hok : ∀ a n, Ok a n → ∀ i < n, Foot Wl (Addr.add a i))
    (hcl : ∀ (W : Addr → Byte) (a : Addr) (n : Nat) (bs : List Byte), bs.length = n → Ok a n → I W →
      I (Vst W a bs))
    (o24 : Ok (X.cpu.gpr.rdi + 24#64) 8) (o32 : Ok (X.cpu.gpr.rdi + 32#64) 4)
    (o36 : Ok (X.cpu.gpr.rdi + 36#64) 4) (os8 : Ok (aR X.cpu.gpr.rsp + 8#64) 8)
    (hsl : ∀ W, I W →
      Ok (rdq(W, X.cpu.gpr.rdi + 24#64) + BitVec.setWidth 64 rdd(W, X.cpu.gpr.rdi + 32#64) * 8#64) 8)
    (fp0 : ∀ i < 2, Foot F.data (Addr.add X.cpu.gpr.rcx i))
    (fp2 : ∀ i < 1, Foot F.data (Addr.add (X.cpu.gpr.rcx + 2#64) i))
    (hI : ∀ W, I W → Stk W X.cpu.gpr.rsp X.cpu.gpr (e₂.add j₂)) (hI0 : I (P6 V X.cpu.gpr))
    {codeT : List Byte} (hinT : CodeIn L 0x4018c6#64 codeT) (hT : 0 < codeT.length)
    (cN2 : ∃ code : List Byte, CodeIn L 0x6029b0#64 code ∧ 0 < code.length)
    (cN : ∃ code : List Byte, CodeIn L 0x602970#64 code ∧ 0 < code.length)
    (cC : ∃ code : List Byte, CodeIn L 0x44d3e0#64 code ∧ 0 < code.length)
    (cA : ∃ code : List Byte, CodeIn L 0x44d710#64 code ∧ 0 < code.length)
    (cM : ∃ code : List Byte, CodeIn L 0x401070#64 code ∧ 0 < code.length)
    (cD : ∃ code : List Byte, CodeIn L 0x6014f0#64 code ∧ 0 < code.length)
    (k80 : ∀ W, I W → KC prof F Wl L s₀ o gev gP gE X.cpu.gpr.rsp I 0x6029b0#64 85 W (fun _ => True)
      (fun _ => True))
    (k120 : ∀ W, I W → KC prof F Wl L s₀ o gev gP gE X.cpu.gpr.rsp I 0x602970#64 125 W (fun _ => True)
      (fun g => Ob Ok g.rax))
    (k131 : ∀ W, I W → KC prof F Wl L s₀ o gev gP gE X.cpu.gpr.rsp I 0x44d3e0#64 136 W (fun _ => True)
      (fun _ => True))
    (k166 : ∀ W, I W → KC prof F Wl L s₀ o gev gP gE X.cpu.gpr.rsp I 0x44d710#64 171 W
      (fun g => g.rsi = X.cpu.gpr.rdx) (fun _ => True))
    (k223 : ∀ W, I W → KC prof F Wl L s₀ o gev gP gE X.cpu.gpr.rsp I 0x401070#64 228 W (fun _ => True)
      (fun _ => True))
    (k236 : ∀ W, I W → KC prof F Wl L s₀ o gev gP gE X.cpu.gpr.rsp I 0x6014f0#64 241 W (fun _ => True)
      (fun _ => True))
    (kt : ∀ W, I W → ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y → Agree F Y.proc.mm.mem W →
      Y.cpu.rip = 0x4018c6#64 → Fm X.cpu.gpr.rsp X.cpu.gpr Y.cpu.gpr → GoG prof L o gev gP gE Y t')
    (kr : ∀ (W : Addr → Byte) (Z' : State) (t' : Nat), KeptW Wl s₀ Z' → Agree F Z'.proc.mm.mem W →
      Z'.cpu.rip = e₂.add j₂ → Z'.cpu.gpr.rsp = X.cpu.gpr.rsp + 8 → KS X.cpu.gpr Z'.cpu.gpr → I W →
      GoG prof L o gev gP gE Z' t') :
    GoG prof L o gev gP gE X t := by
  have E : Ev prof F Wl L s₀ o gev gP gE X.cpu.gpr.rsp X.cpu.gpr e₂ code₂ j₂ I Ok :=
    { c := c, hin := hin, hin₂ := hin₂, h₂ := h₂, hI := hI, hok := hok, hcl := hcl,
      o24 := o24, o32 := o32, o36 := o36, os8 := os8, hsl := hsl, fp0 := fp0, fp2 := fp2,
      fb48 := fun i hi => c.hws _ (hs6 i hi), fb40 := fun i hi => c.hws _ (hs5 i hi),
      fb32 := fun i hi => c.hws _ (hs4 i hi), fb24 := fun i hi => c.hws _ (hs3 i hi),
      fb16 := fun i hi => c.hws _ (hs2 i hi), fb8 := fun i hi => c.hws _ (hs1 i hi), hl := hl, hr8 := hr8,
      cN2 := cN2, cN := cN, cC := cC, cA := cA, cM := cM, cD := cD,
      k80 := k80, k120 := k120, k131 := k131, k166 := k166, k223 := k223, k236 := k236, kr := kr }
  -- the prologue, to 115 or to the `ja`
  refine (c_0 prof).run c hin (fun j' g' _ V' => V' = P6 V X.cpu.gpr ∧ Fm X.cpu.gpr.rsp X.cpu.gpr g' ∧
      (j' = 115 ∨ j' = 43)) hK hA (by rw [addr_add_zero]; exact hrip)
    (vc_0 hs1 hs2 hs3 hs4 hs5 hs6 (fun i hi => c.hws _ (hok _ _ o36 i hi)) (fun i hi => c.hws _ (hok _ _ o32 i hi))
      (fun _ a b d e i _ => ⟨rfl, ⟨a, b, d, e, i⟩, Or.inl rfl⟩)
      (fun _ a b d e i _ => ⟨rfl, ⟨a, b, d, e, i⟩, Or.inr rfl⟩)) ?_
  rintro j' g fl V₁ ⟨hV₁, hmY, hj⟩ Y t₁ hKY hAY hrY hgY -
  subst V₁ hgY
  rcases hj with rfl | rfl
  · exact from115 E hKY hAY hrY hmY hI0
  · refine c.s_jcc_x hKY hAY hin (lt_len (by decide)) hrY (ja_43 _) hinT hT (tgt := 0) (by decide) ?_ ?_
    · -- the throw
      intro _ Y₁ t₂ hK₁ hA₁ ⟨hr₁, hg₁⟩
      exact kt _ hI0 Y₁ t₂ hK₁ hA₁ (by rw [hr₁, addr_add_zero]) (by rw [hg₁]; exact hmY)
    · intro _ Y₁ t₂ hK₁ hA₁ ⟨hr₁, hg₁⟩
      exact from49 E hK₁ hA₁ hr₁ (by rw [hg₁]; exact hmY) hI0

end FV7z.Api
