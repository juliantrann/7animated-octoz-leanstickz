import FV7z.Mbc.Cuts
import FV7z.Api.Holds
import FV7z.Tun.Inv
/-!
# `MultiByteToUnicodeString (const char *, UINT)`: the instructions outside the blocks, the frame (PLAN.md §M, M1)

7-Zip 26.06's `MultiByteToUnicodeString (src, codePage)` (`CPP/Common/StringConvert.cpp`; `objdump -d`) at
`0x450ca0` in `7zzs`: the result's `UString` slot = `rdi` (`r12`), `src` = `rsi`, `codePage` = `edx` (`r13d`); it
returns the slot (`rax`). `S` the stack pointer at the entry: three pushes (`r13`, `r12`, `rbp`) and 32 bytes of
frame (`aR S`, also in `rbp`): a local `AString` at `aR S`, the stack guard (`fs:0x28`) at `aR S + 24`. The callees:
`AString::AString (const char *)` at `0x44c3c0` (41), `MultiByteToUnicodeString (const AString &, UINT)` at
`0x450c60` (55) and `delete []` at `0x6014f0` (69).

- The `call`s (`call_*`, `tgt_*`), the `ret` (`ret_102`).
- `aR`, `P3`, `V0`, `q1`..`q4`: the frame, the bytes after the pushes and after the prologue, the pops' addresses.
- `Fm`, `Fr`, `Stk`, `KC`, `Ev`: the frame's registers, what a piece keeps, the stack, a callee as a continuation,
  the hypotheses of the runs; `callK`: a `call` and the run from its return.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
open FV7z.Api (KS)
namespace FV7z.Mbc
set_option linter.unusedVariables false

/-! ## The instructions outside the blocks -/

/-- The `call` of `AString::AString (const char *)` (41). -/
def pc41 : List Byte := [0xe8, 0xf2, 0xb6, 0xff, 0xff]
theorem pc41_0 : ∀ feat, Dec feat pc41 0 (FV7z.mk .call 64 [.rel 18446744073709532914] 5) := by dec_rfl
theorem wc_41 : pc41 <+: mbc.drop 41 := by decide +kernel
theorem call_41 (feat : Features) : Dec feat mbc 41 (FV7z.mk .call 64 [.rel 18446744073709532914] 5) :=
  Dec.shift (j := 41) (k := 0) (pc41_0 feat) wc_41 (Nat.zero_le _)
theorem tgt_41 : mbc_at.add (41 + 5) + BitVec.ofNat 64 18446744073709532914 = 0x44c3c0#64 := by decide

/-- The `call` of `MultiByteToUnicodeString (const AString &, UINT)` (55). -/
def pc55 : List Byte := [0xe8, 0x84, 0xff, 0xff, 0xff]
theorem pc55_0 : ∀ feat, Dec feat pc55 0 (FV7z.mk .call 64 [.rel 18446744073709551492] 5) := by dec_rfl
theorem wc_55 : pc55 <+: mbc.drop 55 := by decide +kernel
theorem call_55 (feat : Features) : Dec feat mbc 55 (FV7z.mk .call 64 [.rel 18446744073709551492] 5) :=
  Dec.shift (j := 55) (k := 0) (pc55_0 feat) wc_55 (Nat.zero_le _)
theorem tgt_55 : mbc_at.add (55 + 5) + BitVec.ofNat 64 18446744073709551492 = 0x450c60#64 := by decide

/-- The `call` of `delete []` (69). -/
def pc69 : List Byte := [0xe8, 0x06, 0x08, 0x1b, 0x00]
theorem pc69_0 : ∀ feat, Dec feat pc69 0 (FV7z.mk .call 64 [.rel 1771526] 5) := by dec_rfl
theorem wc_69 : pc69 <+: mbc.drop 69 := by decide +kernel
theorem call_69 (feat : Features) : Dec feat mbc 69 (FV7z.mk .call 64 [.rel 1771526] 5) :=
  Dec.shift (j := 69) (k := 0) (pc69_0 feat) wc_69 (Nat.zero_le _)
theorem tgt_69 : mbc_at.add (69 + 5) + BitVec.ofNat 64 1771526 = 0x6014f0#64 := by decide

/-- The `ret` (102). -/
def pret : List Byte := [0xc3]
theorem pret_0 : ∀ feat, Dec feat pret 0 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem w_102 : pret <+: mbc.drop 102 := by decide +kernel
theorem ret_102 (feat : Features) : Dec feat mbc 102 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 102) (k := 0) (pret_0 feat) w_102 (Nat.zero_le _)

/-! ## The frame -/

/-- The stack pointer after the three pushes and `sub rsp, 0x20`. -/
abbrev aR (S : Addr) : Addr := S - 8 - 8 - 8 - 32#64

/-- The bytes after the three pushes (`r13`, `r12`, `rbp`). -/
abbrev P3 (V : Addr → Byte) (g : Gprs) : Addr → Byte :=
  Vst (Vst (Vst V (g.rsp - 8) (toBytesLE g.r13 8)) (g.rsp - 8 - 8) (toBytesLE g.r12 8))
    (g.rsp - 8 - 8 - 8) (toBytesLE g.rbp 8)

/-- The bytes after the prologue: the pushes, the stack guard stored. -/
abbrev V0 (fb : Addr) (V : Addr → Byte) (g : Gprs) : Addr → Byte :=
  Vst (P3 V g) (aR g.rsp + 24#64) (toBytesLE rdq(P3 V g, fb + 40#64) 8)

theorem q1 (S : Addr) : aR S + 32#64 = S - 8 - 8 - 8 := BitVec.sub_add_cancel _ _
theorem q2 (S : Addr) : aR S + 32#64 + 8 = S - 8 - 8 := by rw [q1, BitVec.sub_add_cancel]
theorem q3 (S : Addr) : aR S + 32#64 + 8 + 8 = S - 8 := by rw [q2, BitVec.sub_add_cancel]
theorem q4 (S : Addr) : aR S + 32#64 + 8 + 8 + 8 = S := by rw [q3, BitVec.sub_add_cancel]

/-- The frame from the prologue on: `rsp` = `aR S`, `r12` = the slot, `rbx`, `r14`, `r15` as at the entry. -/
abbrev Fm (S : Addr) (g0 g : Gprs) : Prop :=
  g.rsp = aR S ∧ g.rbx = g0.rbx ∧ g.r12 = g0.rdi ∧ g.r14 = g0.r14 ∧ g.r15 = g0.r15

/-- What a piece keeps: `rsp`, `rbx`, `r12`, `r14`, `r15`. -/
abbrev Fr (g g' : Gprs) : Prop :=
  g'.rsp = g.rsp ∧ g'.rbx = g.rbx ∧ g'.r12 = g.r12 ∧ g'.r14 = g.r14 ∧ g'.r15 = g.r15

theorem Fm.fr {S : Addr} {g0 g g' : Gprs} (h : Fm S g0 g) (h' : Fr g g') : Fm S g0 g' :=
  ⟨h'.1.trans h.1, h'.2.1.trans h.2.1, h'.2.2.1.trans h.2.2.1, h'.2.2.2.1.trans h.2.2.2.1,
    h'.2.2.2.2.trans h.2.2.2.2⟩

/-- Back from a callee: `rsp` as before the `call`, the callee-saved registers kept. -/
theorem fm_ret {S : Addr} {g0 g g' : Gprs} (h : Fm S g0 g) (hs : g'.rsp = aR S) (hk : KS g g') : Fm S g0 g' :=
  ⟨hs, hk.1.trans h.2.1, hk.2.2.1.trans h.2.2.1, hk.2.2.2.2.1.trans h.2.2.2.1, hk.2.2.2.2.2.trans h.2.2.2.2⟩

/-- The stack (`fb` the `fs` base, `ra` the return address): the three saved registers, the return address, the
stack guard as at `fs:0x28`. -/
abbrev Stk (fb : Addr) (W : Addr → Byte) (S : Addr) (g0 : Gprs) (ra : Addr) : Prop :=
  rdq(W, S - 8 - 8 - 8) = g0.rbp ∧ rdq(W, S - 8 - 8) = g0.r12 ∧ rdq(W, S - 8) = g0.r13 ∧ rdq(W, S) = ra ∧
    rdq(W, aR S + 24#64) = rdq(W, fb + 40#64)

/-- A callee from the `call` before `j` (entry `ent`, the bytes `W`, the registers `A`): at its entry, and from its
return at `j` with `rsp` = `aR S`, the callee-saved registers as at its entry, `B` and the invariant `J`, the run
goes on to the goal. -/
def KC (prof : Profile) (F : Footprint) (Wl : List Rgn) (L : List (Addr × List Byte)) (s₀ : State) (o : Oracle)
    (gev : List Event) (gP : State → Nat → List Event → Prop) (gE : Outcome → List Event → Prop)
    (S : Addr) (J : (Addr → Byte) → Prop) (ent : Addr) (j : Nat) (W : Addr → Byte) (A B : Gprs → Prop) : Prop :=
  ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y →
    Agree F Y.proc.mm.mem (Vst W (aR S - 8) (toBytesLE (mbc_at.add j) 8)) →
    Y.cpu.rip = ent → Y.cpu.gpr.rsp = aR S - 8 → A Y.cpu.gpr →
    (∀ (Z : State) (W' : Addr → Byte) (t'' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem W' →
      Z.cpu.rip = mbc_at.add j → Z.cpu.gpr.rsp = aR S → KS Y.cpu.gpr Z.cpu.gpr → B Z.cpu.gpr → J W' →
      GoG prof L o gev gP gE Z t'') →
    GoG prof L o gev gP gE Y t'

/-! ## The hypotheses of the runs -/

/-- The hypotheses of the runs from the cut points (`fb` the `fs` base, `S`, `g0` the entry's stack pointer and
registers, `e₂.add j₂` the return address, `I` the invariant of the bytes): the stack (`hcl`..`hr8`); the callees
keep `I`, from any return offset; the return with `rax` = the slot. -/
structure Ev (prof : Profile) (F : Footprint) (Wl : List Rgn) (L : List (Addr × List Byte)) (s₀ : State)
    (o : Oracle) (gev : List Event) (gP : State → Nat → List Event → Prop) (gE : Outcome → List Event → Prop)
    (fb S : Addr) (g0 : Gprs) (e₂ : Addr) (code₂ : List Byte) (j₂ : Nat) (I : (Addr → Byte) → Prop) :
    Prop where
  c : Seg prof F Wl L s₀ o
  hfs : s₀.cpu.seg.fsBase = fb
  hin : CodeIn L mbc_at mbc
  hin₂ : CodeIn L e₂ code₂
  h₂ : j₂ < code₂.length
  hI : ∀ W, I W → Stk fb W S g0 (e₂.add j₂)
  hcl : ∀ i < 8, Foot F.data (Addr.add (fb + 40#64) i)
  fg : ∀ i < 8, Foot F.data (Addr.add (aR S + 24#64) i)
  fl0 : ∀ i < 8, Foot F.data (Addr.add (aR S) i)
  fb24 : ∀ i < 8, Foot F.data (Addr.add (S - 8 - 8 - 8) i)
  fb16 : ∀ i < 8, Foot F.data (Addr.add (S - 8 - 8) i)
  fb8 : ∀ i < 8, Foot F.data (Addr.add (S - 8) i)
  hl : ∀ i < 8, Foot F.data (Addr.add S i)
  hr8 : ∀ i < 8, Foot Wl (Addr.add (aR S - 8) i)
  cA : ∃ code : List Byte, CodeIn L 0x44c3c0#64 code ∧ 0 < code.length
  cS : ∃ code : List Byte, CodeIn L 0x450c60#64 code ∧ 0 < code.length
  cD : ∃ code : List Byte, CodeIn L 0x6014f0#64 code ∧ 0 < code.length
  kA : ∀ j W, I W → KC prof F Wl L s₀ o gev gP gE S I 0x44c3c0#64 j W (fun _ => True) (fun _ => True)
  kS : ∀ j W, I W → KC prof F Wl L s₀ o gev gP gE S I 0x450c60#64 j W (fun _ => True) (fun _ => True)
  kD : ∀ j W, I W → KC prof F Wl L s₀ o gev gP gE S I 0x6014f0#64 j W (fun _ => True) (fun _ => True)
  kr : ∀ (W : Addr → Byte) (Z' : State) (t' : Nat), KeptW Wl s₀ Z' → Agree F Z'.proc.mm.mem W →
    Z'.cpu.rip = e₂.add j₂ → Z'.cpu.gpr.rsp = S + 8 → KS g0 Z'.cpu.gpr → Z'.cpu.gpr.rax = g0.rdi → I W →
    GoG prof L o gev gP gE Z' t'

section Runs
variable {prof : Profile} {F : Footprint} {Wl : List Rgn} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {fb S : Addr} {g0 : Gprs} {e₂ : Addr} {code₂ : List Byte} {j₂ : Nat} {I : (Addr → Byte) → Prop}
  {W : Addr → Byte}

/-- A `call` at `j` (`rsp` = `aR S`, the bytes `W`) of the callee `k`, and from its return at `j + 5`. -/
theorem callK (E : Ev prof F Wl L s₀ o gev gP gE fb S g0 e₂ code₂ j₂ I)
    {J : (Addr → Byte) → Prop} {U : State} {t₁ : Nat} {j R : Nat} {ent : Addr} {A B : Gprs → Prop}
    (hKU : KeptW Wl s₀ U) (hAU : Agree F U.proc.mm.mem W) (hrU : U.cpu.rip = mbc_at.add j)
    (hs : U.cpu.gpr.rsp = aR S) (hj : j < mbc.length) (hd : Dec prof.feat mbc j (FV7z.mk .call 64 [.rel R] 5))
    (htgt : mbc_at.add (j + 5) + BitVec.ofNat 64 R = ent)
    (hc : ∃ code : List Byte, CodeIn L ent code ∧ 0 < code.length)
    (k : KC prof F Wl L s₀ o gev gP gE S J ent (j + 5) W A B) (hA : A (U.cpu.gpr.set 4 (aR S - 8)))
    (h : ∀ (Z : State) (W' : Addr → Byte) (t'' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem W' →
      Z.cpu.rip = mbc_at.add (j + 5) → Z.cpu.gpr.rsp = aR S → KS U.cpu.gpr Z.cpu.gpr → B Z.cpu.gpr → J W' →
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
macro "mbcstep" : tactic => `(tactic| first
  | with_reducible rfl
  | with_reducible assumption
  | exact rfl
  | apply And.intro
  | intro _)

end FV7z.Mbc
