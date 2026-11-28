import FV7z.Owc.Cuts
import FV7z.Api.Holds
import FV7z.Tun.Inv
/-!
# `CStdOutStream::operator<< (const wchar_t *)`: the instructions outside the blocks, the frame (PLAN.md §M, M1)

7-Zip 26.06's `CStdOutStream::operator<< (s)` (`CPP/Common/StdOutStream.cpp`; `objdump -d`) at `0x5a1530` in
`7zzs`: `this` = `rdi` (`r12`), `s` = `rsi` (`rbp`); it returns `this` (`rax`). `S` the stack pointer at the entry:
four pushes (`r14`, `r13`, `r12`, `rbp`) and 56 bytes of frame (`aR S`, also in `r14`): a local `AString` at `aR S`,
a local `UString` at `aR S + 16` (also in `r13`), the stack guard (`fs:0x28`) at `aR S + 40`. The callees:
`AString::AString ()` at `0x44c360` (48), `UString::UString (const wchar_t *)` at `0x44d480` (59),
`CStdOutStream::PrintUString` at `0x5a14f0` (73) and `delete []` at `0x6014f0` (88, 102).

- The `call`s (`call_*`, `tgt_*`), the `ret` (`ret_137`).
- `aR`, `P4`, `V0`, `q1`..`q5`: the frame, the bytes after the pushes and after the prologue, the pops' addresses.
- `Fm`, `Fr`, `Stk`, `KC`, `Ev`: the frame's registers, what a piece keeps, the stack, a callee as a continuation,
  the hypotheses of the runs; `callK`: a `call` and the run from its return.
- `ostep`: one step of the closers of the pieces.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
open FV7z.Api (KS)
namespace FV7z.Owc
set_option linter.unusedVariables false

/-! ## The instructions outside the blocks -/

/-- The `call` of `AString::AString ()` (48). -/
def pc48 : List Byte := [0xe8, 0xfb, 0xad, 0xea, 0xff]
theorem pc48_0 : ∀ feat, Dec feat pc48 0 (FV7z.mk .call 64 [.rel 18446744073708154363] 5) := by dec_rfl
theorem wc_48 : pc48 <+: owc.drop 48 := by decide +kernel
theorem call_48 (feat : Features) : Dec feat owc 48 (FV7z.mk .call 64 [.rel 18446744073708154363] 5) :=
  Dec.shift (j := 48) (k := 0) (pc48_0 feat) wc_48 (Nat.zero_le _)
theorem tgt_48 : owc_at.add (48 + 5) + BitVec.ofNat 64 18446744073708154363 = 0x44c360#64 := by decide

/-- The `call` of `UString::UString (const wchar_t *)` (59). -/
def pc59 : List Byte := [0xe8, 0x10, 0xbf, 0xea, 0xff]
theorem pc59_0 : ∀ feat, Dec feat pc59 0 (FV7z.mk .call 64 [.rel 18446744073708158736] 5) := by dec_rfl
theorem wc_59 : pc59 <+: owc.drop 59 := by decide +kernel
theorem call_59 (feat : Features) : Dec feat owc 59 (FV7z.mk .call 64 [.rel 18446744073708158736] 5) :=
  Dec.shift (j := 59) (k := 0) (pc59_0 feat) wc_59 (Nat.zero_le _)
theorem tgt_59 : owc_at.add (59 + 5) + BitVec.ofNat 64 18446744073708158736 = 0x44d480#64 := by decide

/-- The `call` of `CStdOutStream::PrintUString` (73). -/
def pc73 : List Byte := [0xe8, 0x72, 0xff, 0xff, 0xff]
theorem pc73_0 : ∀ feat, Dec feat pc73 0 (FV7z.mk .call 64 [.rel 18446744073709551474] 5) := by dec_rfl
theorem wc_73 : pc73 <+: owc.drop 73 := by decide +kernel
theorem call_73 (feat : Features) : Dec feat owc 73 (FV7z.mk .call 64 [.rel 18446744073709551474] 5) :=
  Dec.shift (j := 73) (k := 0) (pc73_0 feat) wc_73 (Nat.zero_le _)
theorem tgt_73 : owc_at.add (73 + 5) + BitVec.ofNat 64 18446744073709551474 = 0x5a14f0#64 := by decide

/-- The `call` of `delete []` (88). -/
def pc88 : List Byte := [0xe8, 0x63, 0xff, 0x05, 0x00]
theorem pc88_0 : ∀ feat, Dec feat pc88 0 (FV7z.mk .call 64 [.rel 393059] 5) := by dec_rfl
theorem wc_88 : pc88 <+: owc.drop 88 := by decide +kernel
theorem call_88 (feat : Features) : Dec feat owc 88 (FV7z.mk .call 64 [.rel 393059] 5) :=
  Dec.shift (j := 88) (k := 0) (pc88_0 feat) wc_88 (Nat.zero_le _)
theorem tgt_88 : owc_at.add (88 + 5) + BitVec.ofNat 64 393059 = 0x6014f0#64 := by decide

/-- The `call` of `delete []` (102). -/
def pc102 : List Byte := [0xe8, 0x55, 0xff, 0x05, 0x00]
theorem pc102_0 : ∀ feat, Dec feat pc102 0 (FV7z.mk .call 64 [.rel 393045] 5) := by dec_rfl
theorem wc_102 : pc102 <+: owc.drop 102 := by decide +kernel
theorem call_102 (feat : Features) : Dec feat owc 102 (FV7z.mk .call 64 [.rel 393045] 5) :=
  Dec.shift (j := 102) (k := 0) (pc102_0 feat) wc_102 (Nat.zero_le _)
theorem tgt_102 : owc_at.add (102 + 5) + BitVec.ofNat 64 393045 = 0x6014f0#64 := by decide

/-- The `ret` (137). -/
def pret : List Byte := [0xc3]
theorem pret_0 : ∀ feat, Dec feat pret 0 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem w_137 : pret <+: owc.drop 137 := by decide +kernel
theorem ret_137 (feat : Features) : Dec feat owc 137 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 137) (k := 0) (pret_0 feat) w_137 (Nat.zero_le _)

/-! ## The frame -/

/-- The stack pointer after the four pushes and `sub rsp, 0x38`. -/
abbrev aR (S : Addr) : Addr := S - 8 - 8 - 8 - 8 - 56#64

/-- The bytes after the four pushes (`r14`, `r13`, `r12`, `rbp`). -/
abbrev P4 (V : Addr → Byte) (g : Gprs) : Addr → Byte :=
  Vst (Vst (Vst (Vst V (g.rsp - 8) (toBytesLE g.r14 8)) (g.rsp - 8 - 8) (toBytesLE g.r13 8))
    (g.rsp - 8 - 8 - 8) (toBytesLE g.r12 8)) (g.rsp - 8 - 8 - 8 - 8) (toBytesLE g.rbp 8)

/-- The bytes after the prologue: the pushes, the stack guard stored. -/
abbrev V0 (fb : Addr) (V : Addr → Byte) (g : Gprs) : Addr → Byte :=
  Vst (P4 V g) (aR g.rsp + 40#64) (toBytesLE rdq(P4 V g, fb + 40#64) 8)

theorem q1 (S : Addr) : aR S + 56#64 = S - 8 - 8 - 8 - 8 := BitVec.sub_add_cancel _ _
theorem q2 (S : Addr) : aR S + 56#64 + 8 = S - 8 - 8 - 8 := by rw [q1, BitVec.sub_add_cancel]
theorem q3 (S : Addr) : aR S + 56#64 + 8 + 8 = S - 8 - 8 := by rw [q2, BitVec.sub_add_cancel]
theorem q4 (S : Addr) : aR S + 56#64 + 8 + 8 + 8 = S - 8 := by rw [q3, BitVec.sub_add_cancel]
theorem q5 (S : Addr) : aR S + 56#64 + 8 + 8 + 8 + 8 = S := by rw [q4, BitVec.sub_add_cancel]

/-- The frame from the prologue on: `rsp` = `aR S`, `r12` = `this`, `rbx`, `r15` as at the entry. -/
abbrev Fm (S : Addr) (g0 g : Gprs) : Prop :=
  g.rsp = aR S ∧ g.rbx = g0.rbx ∧ g.r12 = g0.rdi ∧ g.r15 = g0.r15

/-- What a piece keeps: `rsp`, `rbx`, `r12`, `r15`. -/
abbrev Fr (g g' : Gprs) : Prop :=
  g'.rsp = g.rsp ∧ g'.rbx = g.rbx ∧ g'.r12 = g.r12 ∧ g'.r15 = g.r15

theorem Fm.fr {S : Addr} {g0 g g' : Gprs} (h : Fm S g0 g) (h' : Fr g g') : Fm S g0 g' :=
  ⟨h'.1.trans h.1, h'.2.1.trans h.2.1, h'.2.2.1.trans h.2.2.1, h'.2.2.2.trans h.2.2.2⟩

/-- Back from a callee: `rsp` as before the `call`, the callee-saved registers kept. -/
theorem fm_ret {S : Addr} {g0 g g' : Gprs} (h : Fm S g0 g) (hs : g'.rsp = aR S) (hk : KS g g') : Fm S g0 g' :=
  ⟨hs, hk.1.trans h.2.1, hk.2.2.1.trans h.2.2.1, hk.2.2.2.2.2.trans h.2.2.2⟩

/-- The stack (`fb` the `fs` base, `ra` the return address): the four saved registers, the return address, the
stack guard as at `fs:0x28`. -/
abbrev Stk (fb : Addr) (W : Addr → Byte) (S : Addr) (g0 : Gprs) (ra : Addr) : Prop :=
  rdq(W, S - 8 - 8 - 8 - 8) = g0.rbp ∧ rdq(W, S - 8 - 8 - 8) = g0.r12 ∧ rdq(W, S - 8 - 8) = g0.r13 ∧
    rdq(W, S - 8) = g0.r14 ∧ rdq(W, S) = ra ∧ rdq(W, aR S + 40#64) = rdq(W, fb + 40#64)

/-- A callee from the `call` before `j` (entry `ent`, the bytes `W`, the registers `A`): at its entry, and from its
return at `j` with `rsp` = `aR S`, the callee-saved registers as at its entry, `B` and the invariant `J`, the run
goes on to the goal. -/
def KC (prof : Profile) (F : Footprint) (Wl : List Rgn) (L : List (Addr × List Byte)) (s₀ : State) (o : Oracle)
    (gev : List Event) (gP : State → Nat → List Event → Prop) (gE : Outcome → List Event → Prop)
    (S : Addr) (J : (Addr → Byte) → Prop) (ent : Addr) (j : Nat) (W : Addr → Byte) (A B : Gprs → Prop) : Prop :=
  ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y →
    Agree F Y.proc.mm.mem (Vst W (aR S - 8) (toBytesLE (owc_at.add j) 8)) →
    Y.cpu.rip = ent → Y.cpu.gpr.rsp = aR S - 8 → A Y.cpu.gpr →
    (∀ (Z : State) (W' : Addr → Byte) (t'' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem W' →
      Z.cpu.rip = owc_at.add j → Z.cpu.gpr.rsp = aR S → KS Y.cpu.gpr Z.cpu.gpr → B Z.cpu.gpr → J W' →
      GoG prof L o gev gP gE Z t'') →
    GoG prof L o gev gP gE Y t'

/-! ## The hypotheses of the runs -/

/-- The hypotheses of the runs from the cut points (`fb` the `fs` base, `S`, `g0` the entry's stack pointer and
registers, `e₂.add j₂` the return address, `I` the invariant of the bytes): the stack (`hcl`..`hr8`); the callees
keep `I`, from any return offset; the return with `rax` = `this`. -/
structure Ev (prof : Profile) (F : Footprint) (Wl : List Rgn) (L : List (Addr × List Byte)) (s₀ : State)
    (o : Oracle) (gev : List Event) (gP : State → Nat → List Event → Prop) (gE : Outcome → List Event → Prop)
    (fb S : Addr) (g0 : Gprs) (e₂ : Addr) (code₂ : List Byte) (j₂ : Nat) (I : (Addr → Byte) → Prop) :
    Prop where
  c : Seg prof F Wl L s₀ o
  hfs : s₀.cpu.seg.fsBase = fb
  hin : CodeIn L owc_at owc
  hin₂ : CodeIn L e₂ code₂
  h₂ : j₂ < code₂.length
  hI : ∀ W, I W → Stk fb W S g0 (e₂.add j₂)
  hcl : ∀ i < 8, Foot F.data (Addr.add (fb + 40#64) i)
  fg : ∀ i < 8, Foot F.data (Addr.add (aR S + 40#64) i)
  fl0 : ∀ i < 8, Foot F.data (Addr.add (aR S) i)
  fl16 : ∀ i < 8, Foot F.data (Addr.add (aR S + 16#64) i)
  fb32 : ∀ i < 8, Foot F.data (Addr.add (S - 8 - 8 - 8 - 8) i)
  fb24 : ∀ i < 8, Foot F.data (Addr.add (S - 8 - 8 - 8) i)
  fb16 : ∀ i < 8, Foot F.data (Addr.add (S - 8 - 8) i)
  fb8 : ∀ i < 8, Foot F.data (Addr.add (S - 8) i)
  hl : ∀ i < 8, Foot F.data (Addr.add S i)
  hr8 : ∀ i < 8, Foot Wl (Addr.add (aR S - 8) i)
  cA : ∃ code : List Byte, CodeIn L 0x44c360#64 code ∧ 0 < code.length
  cU : ∃ code : List Byte, CodeIn L 0x44d480#64 code ∧ 0 < code.length
  cP : ∃ code : List Byte, CodeIn L 0x5a14f0#64 code ∧ 0 < code.length
  cD : ∃ code : List Byte, CodeIn L 0x6014f0#64 code ∧ 0 < code.length
  kA : ∀ j W, I W → KC prof F Wl L s₀ o gev gP gE S I 0x44c360#64 j W (fun _ => True) (fun _ => True)
  kU : ∀ j W, I W → KC prof F Wl L s₀ o gev gP gE S I 0x44d480#64 j W (fun _ => True) (fun _ => True)
  kP : ∀ j W, I W → KC prof F Wl L s₀ o gev gP gE S I 0x5a14f0#64 j W (fun _ => True) (fun _ => True)
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
    (hKU : KeptW Wl s₀ U) (hAU : Agree F U.proc.mm.mem W) (hrU : U.cpu.rip = owc_at.add j)
    (hs : U.cpu.gpr.rsp = aR S) (hj : j < owc.length) (hd : Dec prof.feat owc j (FV7z.mk .call 64 [.rel R] 5))
    (htgt : owc_at.add (j + 5) + BitVec.ofNat 64 R = ent)
    (hc : ∃ code : List Byte, CodeIn L ent code ∧ 0 < code.length)
    (k : KC prof F Wl L s₀ o gev gP gE S J ent (j + 5) W A B) (hA : A (U.cpu.gpr.set 4 (aR S - 8)))
    (h : ∀ (Z : State) (W' : Addr → Byte) (t'' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem W' →
      Z.cpu.rip = owc_at.add (j + 5) → Z.cpu.gpr.rsp = aR S → KS U.cpu.gpr Z.cpu.gpr → B Z.cpu.gpr → J W' →
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

end FV7z.Owc
