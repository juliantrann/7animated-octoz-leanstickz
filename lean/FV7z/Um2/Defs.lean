import FV7z.Um2.Cuts
import FV7z.Api.Holds
import FV7z.Tun.Inv
/-!
# `UnicodeStringToMultiByte2`: the instructions outside the blocks, the frame (PLAN.md §M, M1)

7-Zip 26.06's `UnicodeStringToMultiByte2 (dest, src, codePage)` (`CPP/Common/StringConvert.cpp`; `objdump -d`) at
`0x450d20` in `7zzs`: `S` the stack pointer at the entry, a frame of 24 bytes (`aR S`) with the stack guard
(`fs:0x28`) at `aR S + 8` and the `bool defaultCharWasUsed` at `aR S + 7`; the callee
`UnicodeStringToMultiByte (dest, src, codePage, '_', &defaultCharWasUsed)` at `0x450750` (34).

- The `call` (`call_34`, `tgt_34`), the `ret` (`ret_59`).
- `aR`, `V0`, `q1`: the frame, the bytes after the prologue, the return address's slot.
- `Fm`, `Stk`, `KC`, `Ev`: the frame's registers, the stack, the callee as a continuation, the hypotheses of the runs.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
open FV7z.Api (KS)
namespace FV7z.Um2
set_option linter.unusedVariables false

/-! ## The instructions outside the blocks -/

/-- The `call` of `UnicodeStringToMultiByte` (34). -/
def pc34 : List Byte := [0xe8, 0x09, 0xfa, 0xff, 0xff]
theorem pc34_0 : ∀ feat, Dec feat pc34 0 (FV7z.mk .call 64 [.rel 18446744073709550089] 5) := by dec_rfl
theorem wc_34 : pc34 <+: um2.drop 34 := by decide +kernel
theorem call_34 (feat : Features) : Dec feat um2 34 (FV7z.mk .call 64 [.rel 18446744073709550089] 5) :=
  Dec.shift (j := 34) (k := 0) (pc34_0 feat) wc_34 (Nat.zero_le _)
theorem tgt_34 : um2_at.add (34 + 5) + BitVec.ofNat 64 18446744073709550089 = 0x450750#64 := by decide

/-- The `ret` (59). -/
def pret : List Byte := [0xc3]
theorem pret_0 : ∀ feat, Dec feat pret 0 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem w_59 : pret <+: um2.drop 59 := by decide +kernel
theorem ret_59 (feat : Features) : Dec feat um2 59 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 59) (k := 0) (pret_0 feat) w_59 (Nat.zero_le _)

/-! ## The frame -/

/-- The stack pointer after `sub rsp, 0x18`. -/
abbrev aR (S : Addr) : Addr := S - 24#64

/-- The bytes after the prologue: the stack guard stored. -/
abbrev V0 (fb : Addr) (V : Addr → Byte) (g : Gprs) : Addr → Byte :=
  Vst V (aR g.rsp + 8#64) (toBytesLE rdq(V, fb + 40#64) 8)

theorem q1 (S : Addr) : aR S + 24#64 = S := BitVec.sub_add_cancel _ _

/-- The frame from the prologue on: `rsp` = `aR S`, the callee-saved registers as at the entry. -/
abbrev Fm (S : Addr) (g0 g : Gprs) : Prop :=
  g.rsp = aR S ∧ g.rbx = g0.rbx ∧ g.rbp = g0.rbp ∧ g.r12 = g0.r12 ∧ g.r13 = g0.r13 ∧ g.r14 = g0.r14 ∧
    g.r15 = g0.r15

/-- Back from the callee: `rsp` as before the `call`, the callee-saved registers kept. -/
theorem fm_ret {S : Addr} {g0 g g' : Gprs} (h : Fm S g0 g) (hs : g'.rsp = aR S) (hk : KS g g') : Fm S g0 g' :=
  ⟨hs, hk.1.trans h.2.1, hk.2.1.trans h.2.2.1, hk.2.2.1.trans h.2.2.2.1, hk.2.2.2.1.trans h.2.2.2.2.1,
    hk.2.2.2.2.1.trans h.2.2.2.2.2.1, hk.2.2.2.2.2.trans h.2.2.2.2.2.2⟩

/-- The stack (`fb` the `fs` base, `ra` the return address): the return address, the stack guard as at
`fs:0x28`. -/
abbrev Stk (fb : Addr) (W : Addr → Byte) (S : Addr) (ra : Addr) : Prop :=
  rdq(W, S) = ra ∧ rdq(W, aR S + 8#64) = rdq(W, fb + 40#64)

/-- The callee from the `call` before `j` (entry `ent`, the bytes `W`, the registers `A`): at its entry, and from its
return at `j` with `rsp` = `aR S`, the callee-saved registers as at its entry, `B` and the invariant `J`, the run
goes on to the goal. -/
def KC (prof : Profile) (F : Footprint) (Wl : List Rgn) (L : List (Addr × List Byte)) (s₀ : State) (o : Oracle)
    (gev : List Event) (gP : State → Nat → List Event → Prop) (gE : Outcome → List Event → Prop)
    (S : Addr) (J : (Addr → Byte) → Prop) (ent : Addr) (j : Nat) (W : Addr → Byte) (A B : Gprs → Prop) : Prop :=
  ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y →
    Agree F Y.proc.mm.mem (Vst W (aR S - 8) (toBytesLE (um2_at.add j) 8)) →
    Y.cpu.rip = ent → Y.cpu.gpr.rsp = aR S - 8 → A Y.cpu.gpr →
    (∀ (Z : State) (W' : Addr → Byte) (t'' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem W' →
      Z.cpu.rip = um2_at.add j → Z.cpu.gpr.rsp = aR S → KS Y.cpu.gpr Z.cpu.gpr → B Z.cpu.gpr → J W' →
      GoG prof L o gev gP gE Z t'') →
    GoG prof L o gev gP gE Y t'

/-! ## The hypotheses of the runs -/

/-- The hypotheses of the runs (`fb` the `fs` base, `S`, `g0` the entry's stack pointer and registers, `e₂.add j₂`
the return address, `I` the invariant of the bytes): the stack; the callee keeps `I`; the return. -/
structure Ev (prof : Profile) (F : Footprint) (Wl : List Rgn) (L : List (Addr × List Byte)) (s₀ : State)
    (o : Oracle) (gev : List Event) (gP : State → Nat → List Event → Prop) (gE : Outcome → List Event → Prop)
    (fb S : Addr) (g0 : Gprs) (e₂ : Addr) (code₂ : List Byte) (j₂ : Nat) (I : (Addr → Byte) → Prop) :
    Prop where
  c : Seg prof F Wl L s₀ o
  hfs : s₀.cpu.seg.fsBase = fb
  hin : CodeIn L um2_at um2
  hin₂ : CodeIn L e₂ code₂
  h₂ : j₂ < code₂.length
  hI : ∀ W, I W → Stk fb W S (e₂.add j₂)
  hcl : ∀ i < 8, Foot F.data (Addr.add (fb + 40#64) i)
  fg : ∀ i < 8, Foot F.data (Addr.add (aR S + 8#64) i)
  hl : ∀ i < 8, Foot F.data (Addr.add S i)
  hr8 : ∀ i < 8, Foot Wl (Addr.add (aR S - 8) i)
  cU : ∃ code : List Byte, CodeIn L 0x450750#64 code ∧ 0 < code.length
  kU : ∀ j W, I W → KC prof F Wl L s₀ o gev gP gE S I 0x450750#64 j W (fun _ => True) (fun _ => True)
  kr : ∀ (W : Addr → Byte) (Z' : State) (t' : Nat), KeptW Wl s₀ Z' → Agree F Z'.proc.mm.mem W →
    Z'.cpu.rip = e₂.add j₂ → Z'.cpu.gpr.rsp = S + 8 → KS g0 Z'.cpu.gpr → I W → GoG prof L o gev gP gE Z' t'

/-! ## Tactics -/

/-- One step of the closers of the pieces. -/
macro "ostep" : tactic => `(tactic| first
  | with_reducible rfl
  | with_reducible assumption
  | exact rfl
  | apply And.intro
  | intro _)

end FV7z.Um2
