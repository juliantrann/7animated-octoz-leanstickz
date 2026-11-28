import FV7z.Pus.Cuts
import FV7z.Api.Holds
import FV7z.Tun.Inv
/-!
# `CStdOutStream::PrintUString`: the instructions outside the blocks, the frame (PLAN.md §M, M1)

7-Zip 26.06's `CStdOutStream::PrintUString (s, temp)` (`CPP/Common/StdOutStream.cpp`; `objdump -d`) at `0x5a14f0`
in `7zzs`: `this` = `rdi` (`rbp`), `s` = `rsi`, `temp` = `rdx` (`rbx`). `S` the stack pointer at the entry: two
pushes (`rbp`, `rbx`) and 8 bytes of frame (`aR S`). The callees: `Convert_UString_to_AString (s, temp)` at
`0x5a14a0` (16) and `fputs (temp._chars, _stream)` at `0x624cc0` (28).

- The `call`s (`call_*`, `tgt_*`), the `ret` (`ret_39`).
- `aR`, `V0`, `q1`..`q3`: the frame, the bytes after the pushes, the pops' addresses.
- `Fm`, `Fr`, `Stk`, `KC`, `Ev`: the frame's registers, what a piece keeps, the stack, a callee as a continuation,
  the hypotheses of the runs; `callK`: a `call` and the run from its return.
- `ostep`: one step of the closers of the pieces.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
open FV7z.Api (KS)
namespace FV7z.Pus
set_option linter.unusedVariables false

/-! ## The instructions outside the blocks -/

/-- The `call` of `Convert_UString_to_AString` (16). -/
def pc16 : List Byte := [0xe8, 0x9b, 0xff, 0xff, 0xff]
theorem pc16_0 : ∀ feat, Dec feat pc16 0 (FV7z.mk .call 64 [.rel 18446744073709551515] 5) := by dec_rfl
theorem wc_16 : pc16 <+: pus.drop 16 := by decide +kernel
theorem call_16 (feat : Features) : Dec feat pus 16 (FV7z.mk .call 64 [.rel 18446744073709551515] 5) :=
  Dec.shift (j := 16) (k := 0) (pc16_0 feat) wc_16 (Nat.zero_le _)
theorem tgt_16 : pus_at.add (16 + 5) + BitVec.ofNat 64 18446744073709551515 = 0x5a14a0#64 := by decide

/-- The `call` of `fputs` (28). -/
def pc28 : List Byte := [0xe8, 0xaf, 0x37, 0x08, 0x00]
theorem pc28_0 : ∀ feat, Dec feat pc28 0 (FV7z.mk .call 64 [.rel 538543] 5) := by dec_rfl
theorem wc_28 : pc28 <+: pus.drop 28 := by decide +kernel
theorem call_28 (feat : Features) : Dec feat pus 28 (FV7z.mk .call 64 [.rel 538543] 5) :=
  Dec.shift (j := 28) (k := 0) (pc28_0 feat) wc_28 (Nat.zero_le _)
theorem tgt_28 : pus_at.add (28 + 5) + BitVec.ofNat 64 538543 = 0x624cc0#64 := by decide

/-- The `ret` (39). -/
def pret : List Byte := [0xc3]
theorem pret_0 : ∀ feat, Dec feat pret 0 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem w_39 : pret <+: pus.drop 39 := by decide +kernel
theorem ret_39 (feat : Features) : Dec feat pus 39 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 39) (k := 0) (pret_0 feat) w_39 (Nat.zero_le _)

/-! ## The frame -/

/-- The stack pointer after the two pushes and `sub rsp, 8`. -/
abbrev aR (S : Addr) : Addr := S - 8 - 8 - 8#64

/-- The bytes after the two pushes (`rbp`, `rbx`). -/
abbrev V0 (V : Addr → Byte) (g : Gprs) : Addr → Byte :=
  Vst (Vst V (g.rsp - 8) (toBytesLE g.rbp 8)) (g.rsp - 8 - 8) (toBytesLE g.rbx 8)

theorem q1 (S : Addr) : aR S + 8#64 = S - 8 - 8 := BitVec.sub_add_cancel _ _
theorem q2 (S : Addr) : aR S + 8#64 + 8 = S - 8 := by rw [q1, BitVec.sub_add_cancel]
theorem q3 (S : Addr) : aR S + 8#64 + 8 + 8 = S := by rw [q2, BitVec.sub_add_cancel]

/-- The frame from the prologue on: `rsp` = `aR S`, `rbx` = `temp`, `rbp` = `this`, `r12`..`r15` as at the
entry. -/
abbrev Fm (S : Addr) (g0 g : Gprs) : Prop :=
  g.rsp = aR S ∧ g.rbx = g0.rdx ∧ g.rbp = g0.rdi ∧ g.r12 = g0.r12 ∧ g.r13 = g0.r13 ∧ g.r14 = g0.r14 ∧
    g.r15 = g0.r15

/-- What a piece keeps: `rsp`, `rbx`, `rbp`, `r12`..`r15`. -/
abbrev Fr (g g' : Gprs) : Prop :=
  g'.rsp = g.rsp ∧ g'.rbx = g.rbx ∧ g'.rbp = g.rbp ∧ g'.r12 = g.r12 ∧ g'.r13 = g.r13 ∧ g'.r14 = g.r14 ∧
    g'.r15 = g.r15

theorem Fm.fr {S : Addr} {g0 g g' : Gprs} (h : Fm S g0 g) (h' : Fr g g') : Fm S g0 g' :=
  ⟨h'.1.trans h.1, h'.2.1.trans h.2.1, h'.2.2.1.trans h.2.2.1, h'.2.2.2.1.trans h.2.2.2.1,
    h'.2.2.2.2.1.trans h.2.2.2.2.1, h'.2.2.2.2.2.1.trans h.2.2.2.2.2.1, h'.2.2.2.2.2.2.trans h.2.2.2.2.2.2⟩

/-- Back from a callee: `rsp` as before the `call`, the callee-saved registers kept. -/
theorem fm_ret {S : Addr} {g0 g g' : Gprs} (h : Fm S g0 g) (hs : g'.rsp = aR S) (hk : KS g g') : Fm S g0 g' :=
  ⟨hs, hk.1.trans h.2.1, hk.2.1.trans h.2.2.1, hk.2.2.1.trans h.2.2.2.1, hk.2.2.2.1.trans h.2.2.2.2.1,
    hk.2.2.2.2.1.trans h.2.2.2.2.2.1, hk.2.2.2.2.2.trans h.2.2.2.2.2.2⟩

/-- The stack (`ra` the return address): the two saved registers, the return address. -/
abbrev Stk (W : Addr → Byte) (S : Addr) (g0 : Gprs) (ra : Addr) : Prop :=
  rdq(W, S - 8 - 8) = g0.rbx ∧ rdq(W, S - 8) = g0.rbp ∧ rdq(W, S) = ra

/-- A callee from the `call` before `j` (entry `ent`, the bytes `W`, the registers `A`): at its entry, and from its
return at `j` with `rsp` = `aR S`, the callee-saved registers as at its entry, `B` and the invariant `J`, the run
goes on to the goal. -/
def KC (prof : Profile) (F : Footprint) (Wl : List Rgn) (L : List (Addr × List Byte)) (s₀ : State) (o : Oracle)
    (gev : List Event) (gP : State → Nat → List Event → Prop) (gE : Outcome → List Event → Prop)
    (S : Addr) (J : (Addr → Byte) → Prop) (ent : Addr) (j : Nat) (W : Addr → Byte) (A B : Gprs → Prop) : Prop :=
  ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y →
    Agree F Y.proc.mm.mem (Vst W (aR S - 8) (toBytesLE (pus_at.add j) 8)) →
    Y.cpu.rip = ent → Y.cpu.gpr.rsp = aR S - 8 → A Y.cpu.gpr →
    (∀ (Z : State) (W' : Addr → Byte) (t'' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem W' →
      Z.cpu.rip = pus_at.add j → Z.cpu.gpr.rsp = aR S → KS Y.cpu.gpr Z.cpu.gpr → B Z.cpu.gpr → J W' →
      GoG prof L o gev gP gE Z t'') →
    GoG prof L o gev gP gE Y t'

/-! ## The hypotheses of the runs -/

/-- The hypotheses of the runs from the cut points (`S`, `g0` the entry's stack pointer and registers, `e₂.add j₂`
the return address, `I` the invariant of the bytes): the stack (`fb16`..`hr8`), `this`'s first 8 bytes (`_stream`,
`fth`) and `temp`'s (`_chars`, `ftm`) readable; the callees keep `I`, from any return offset; the return. -/
structure Ev (prof : Profile) (F : Footprint) (Wl : List Rgn) (L : List (Addr × List Byte)) (s₀ : State)
    (o : Oracle) (gev : List Event) (gP : State → Nat → List Event → Prop) (gE : Outcome → List Event → Prop)
    (S : Addr) (g0 : Gprs) (e₂ : Addr) (code₂ : List Byte) (j₂ : Nat) (I : (Addr → Byte) → Prop) :
    Prop where
  c : Seg prof F Wl L s₀ o
  hin : CodeIn L pus_at pus
  hin₂ : CodeIn L e₂ code₂
  h₂ : j₂ < code₂.length
  hI : ∀ W, I W → Stk W S g0 (e₂.add j₂)
  fth : ∀ i < 8, Foot F.data (Addr.add g0.rdi i)
  ftm : ∀ i < 8, Foot F.data (Addr.add g0.rdx i)
  fb16 : ∀ i < 8, Foot F.data (Addr.add (S - 8 - 8) i)
  fb8 : ∀ i < 8, Foot F.data (Addr.add (S - 8) i)
  hl : ∀ i < 8, Foot F.data (Addr.add S i)
  hr8 : ∀ i < 8, Foot Wl (Addr.add (aR S - 8) i)
  cC : ∃ code : List Byte, CodeIn L 0x5a14a0#64 code ∧ 0 < code.length
  cP : ∃ code : List Byte, CodeIn L 0x624cc0#64 code ∧ 0 < code.length
  kC : ∀ j W, I W → KC prof F Wl L s₀ o gev gP gE S I 0x5a14a0#64 j W (fun _ => True) (fun _ => True)
  kP : ∀ j W, I W → KC prof F Wl L s₀ o gev gP gE S I 0x624cc0#64 j W (fun _ => True) (fun _ => True)
  kr : ∀ (W : Addr → Byte) (Z' : State) (t' : Nat), KeptW Wl s₀ Z' → Agree F Z'.proc.mm.mem W →
    Z'.cpu.rip = e₂.add j₂ → Z'.cpu.gpr.rsp = S + 8 → KS g0 Z'.cpu.gpr → I W → GoG prof L o gev gP gE Z' t'

section Runs
variable {prof : Profile} {F : Footprint} {Wl : List Rgn} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {S : Addr} {g0 : Gprs} {e₂ : Addr} {code₂ : List Byte} {j₂ : Nat} {I : (Addr → Byte) → Prop}
  {W : Addr → Byte}

/-- A `call` at `j` (`rsp` = `aR S`, the bytes `W`) of the callee `k`, and from its return at `j + 5`. -/
theorem callK (E : Ev prof F Wl L s₀ o gev gP gE S g0 e₂ code₂ j₂ I)
    {J : (Addr → Byte) → Prop} {U : State} {t₁ : Nat} {j R : Nat} {ent : Addr} {A B : Gprs → Prop}
    (hKU : KeptW Wl s₀ U) (hAU : Agree F U.proc.mm.mem W) (hrU : U.cpu.rip = pus_at.add j)
    (hs : U.cpu.gpr.rsp = aR S) (hj : j < pus.length) (hd : Dec prof.feat pus j (FV7z.mk .call 64 [.rel R] 5))
    (htgt : pus_at.add (j + 5) + BitVec.ofNat 64 R = ent)
    (hc : ∃ code : List Byte, CodeIn L ent code ∧ 0 < code.length)
    (k : KC prof F Wl L s₀ o gev gP gE S J ent (j + 5) W A B) (hA : A (U.cpu.gpr.set 4 (aR S - 8)))
    (h : ∀ (Z : State) (W' : Addr → Byte) (t'' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem W' →
      Z.cpu.rip = pus_at.add (j + 5) → Z.cpu.gpr.rsp = aR S → KS U.cpu.gpr Z.cpu.gpr → B Z.cpu.gpr → J W' →
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

end Runs

/-! ## Tactics -/

/-- One step of the closers of the pieces. -/
macro "ostep" : tactic => `(tactic| first
  | with_reducible rfl
  | with_reducible assumption
  | exact rfl
  | apply And.intro
  | intro _)

end FV7z.Pus
