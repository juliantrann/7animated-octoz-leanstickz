import FV7z.Nps.Cuts
import FV7z.Api.Holds
import FV7z.Tun.Inv
/-!
# `CStdOutStream::NormalizePrint_UString (const UString &)`: the instructions outside the blocks, the frame
(PLAN.md §M, M1)

7-Zip 26.06's `CStdOutStream::NormalizePrint_UString (s)` (`CPP/Common/StdOutStream.cpp`; `objdump -d`) at
`0x5a1870` in `7zzs`: `this` = `rdi` (`rbp`), `s` = `rsi`. `S` the stack pointer at the entry: three pushes (`r13`,
`r12`, `rbp`) and 48 bytes of frame (`aR S`, also in `r12`): a local `UString` at `aR S`, a local `AString` at
`aR S + 16` (also in `r13`), the stack guard (`fs:0x28`) at `aR S + 40`. The callees:
`UString::UString (const UString &)` at `0x44d5d0` (38), `CStdOutStream::Normalize_UString (UString &)` at
`0x5a15e0` (49), `AString::AString ()` at `0x44c360` (62), `CStdOutStream::PrintUString (const UString &, AString &)`
at `0x5a14f0` (76) and `delete []` at `0x6014f0` (91, 105).

- The `call`s (`call_*`, `tgt_*`), the `ret` (`ret_135`).
- `aR`, `P3`, `V0`, `q1`..`q4`: the frame, the bytes after the pushes and after the prologue, the pops' addresses.
- `Fm`, `Fr`, `Stk`, `KC`, `Ev`: the frame's registers, what a piece keeps, the stack, a callee as a continuation,
  the hypotheses of the runs; `callK`: a `call` and the run from its return.
- `sstep`: one step of the closers of the pieces.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
open FV7z.Api (KS)
namespace FV7z.Nps
set_option linter.unusedVariables false

/-! ## The instructions outside the blocks -/

/-- The `call` of `UString::UString (const UString &)` (38). -/
def pc38 : List Byte := [0xe8, 0x35, 0xbd, 0xea, 0xff]
theorem pc38_0 : ∀ feat, Dec feat pc38 0 (FV7z.mk .call 64 [.rel 18446744073708158261] 5) := by dec_rfl
theorem wc_38 : pc38 <+: nps.drop 38 := by decide +kernel
theorem call_38 (feat : Features) : Dec feat nps 38 (FV7z.mk .call 64 [.rel 18446744073708158261] 5) :=
  Dec.shift (j := 38) (k := 0) (pc38_0 feat) wc_38 (Nat.zero_le _)
theorem tgt_38 : nps_at.add (38 + 5) + BitVec.ofNat 64 18446744073708158261 = 0x44d5d0#64 := by decide

/-- The `call` of `CStdOutStream::Normalize_UString (UString &)` (49). -/
def pc49 : List Byte := [0xe8, 0x3a, 0xfd, 0xff, 0xff]
theorem pc49_0 : ∀ feat, Dec feat pc49 0 (FV7z.mk .call 64 [.rel 18446744073709550906] 5) := by dec_rfl
theorem wc_49 : pc49 <+: nps.drop 49 := by decide +kernel
theorem call_49 (feat : Features) : Dec feat nps 49 (FV7z.mk .call 64 [.rel 18446744073709550906] 5) :=
  Dec.shift (j := 49) (k := 0) (pc49_0 feat) wc_49 (Nat.zero_le _)
theorem tgt_49 : nps_at.add (49 + 5) + BitVec.ofNat 64 18446744073709550906 = 0x5a15e0#64 := by decide

/-- The `call` of `AString::AString ()` (62). -/
def pc62 : List Byte := [0xe8, 0xad, 0xaa, 0xea, 0xff]
theorem pc62_0 : ∀ feat, Dec feat pc62 0 (FV7z.mk .call 64 [.rel 18446744073708153517] 5) := by dec_rfl
theorem wc_62 : pc62 <+: nps.drop 62 := by decide +kernel
theorem call_62 (feat : Features) : Dec feat nps 62 (FV7z.mk .call 64 [.rel 18446744073708153517] 5) :=
  Dec.shift (j := 62) (k := 0) (pc62_0 feat) wc_62 (Nat.zero_le _)
theorem tgt_62 : nps_at.add (62 + 5) + BitVec.ofNat 64 18446744073708153517 = 0x44c360#64 := by decide

/-- The `call` of `CStdOutStream::PrintUString (const UString &, AString &)` (76). -/
def pc76 : List Byte := [0xe8, 0x2f, 0xfc, 0xff, 0xff]
theorem pc76_0 : ∀ feat, Dec feat pc76 0 (FV7z.mk .call 64 [.rel 18446744073709550639] 5) := by dec_rfl
theorem wc_76 : pc76 <+: nps.drop 76 := by decide +kernel
theorem call_76 (feat : Features) : Dec feat nps 76 (FV7z.mk .call 64 [.rel 18446744073709550639] 5) :=
  Dec.shift (j := 76) (k := 0) (pc76_0 feat) wc_76 (Nat.zero_le _)
theorem tgt_76 : nps_at.add (76 + 5) + BitVec.ofNat 64 18446744073709550639 = 0x5a14f0#64 := by decide

/-- The `call` of `delete []` (91). -/
def pc91 : List Byte := [0xe8, 0x20, 0xfc, 0x05, 0x00]
theorem pc91_0 : ∀ feat, Dec feat pc91 0 (FV7z.mk .call 64 [.rel 392224] 5) := by dec_rfl
theorem wc_91 : pc91 <+: nps.drop 91 := by decide +kernel
theorem call_91 (feat : Features) : Dec feat nps 91 (FV7z.mk .call 64 [.rel 392224] 5) :=
  Dec.shift (j := 91) (k := 0) (pc91_0 feat) wc_91 (Nat.zero_le _)
theorem tgt_91 : nps_at.add (91 + 5) + BitVec.ofNat 64 392224 = 0x6014f0#64 := by decide

/-- The `call` of `delete []` (105). -/
def pc105 : List Byte := [0xe8, 0x12, 0xfc, 0x05, 0x00]
theorem pc105_0 : ∀ feat, Dec feat pc105 0 (FV7z.mk .call 64 [.rel 392210] 5) := by dec_rfl
theorem wc_105 : pc105 <+: nps.drop 105 := by decide +kernel
theorem call_105 (feat : Features) : Dec feat nps 105 (FV7z.mk .call 64 [.rel 392210] 5) :=
  Dec.shift (j := 105) (k := 0) (pc105_0 feat) wc_105 (Nat.zero_le _)
theorem tgt_105 : nps_at.add (105 + 5) + BitVec.ofNat 64 392210 = 0x6014f0#64 := by decide

/-- The `ret` (135). -/
def pret : List Byte := [0xc3]
theorem pret_0 : ∀ feat, Dec feat pret 0 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem w_135 : pret <+: nps.drop 135 := by decide +kernel
theorem ret_135 (feat : Features) : Dec feat nps 135 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 135) (k := 0) (pret_0 feat) w_135 (Nat.zero_le _)

/-! ## The frame -/

/-- The stack pointer after the three pushes and `sub rsp, 0x30`. -/
abbrev aR (S : Addr) : Addr := S - 8 - 8 - 8 - 48#64

/-- The bytes after the three pushes (`r13`, `r12`, `rbp`). -/
abbrev P3 (V : Addr → Byte) (g : Gprs) : Addr → Byte :=
  Vst (Vst (Vst V (g.rsp - 8) (toBytesLE g.r13 8)) (g.rsp - 8 - 8) (toBytesLE g.r12 8)) (g.rsp - 8 - 8 - 8)
    (toBytesLE g.rbp 8)

/-- The bytes after the prologue: the pushes, the stack guard stored. -/
abbrev V0 (fb : Addr) (V : Addr → Byte) (g : Gprs) : Addr → Byte :=
  Vst (P3 V g) (aR g.rsp + 40#64) (toBytesLE rdq(P3 V g, fb + 40#64) 8)

theorem q1 (S : Addr) : aR S + 48#64 = S - 8 - 8 - 8 := BitVec.sub_add_cancel _ _
theorem q2 (S : Addr) : aR S + 48#64 + 8 = S - 8 - 8 := by rw [q1, BitVec.sub_add_cancel]
theorem q3 (S : Addr) : aR S + 48#64 + 8 + 8 = S - 8 := by rw [q2, BitVec.sub_add_cancel]
theorem q4 (S : Addr) : aR S + 48#64 + 8 + 8 + 8 = S := by rw [q3, BitVec.sub_add_cancel]

/-- The frame from the prologue on: `rsp` = `aR S`, `rbx`, `r14`, `r15` as at the entry. -/
abbrev Fm (S : Addr) (g0 g : Gprs) : Prop :=
  g.rsp = aR S ∧ g.rbx = g0.rbx ∧ g.r14 = g0.r14 ∧ g.r15 = g0.r15

/-- What a piece keeps: `rsp`, `rbx`, `r14`, `r15`. -/
abbrev Fr (g g' : Gprs) : Prop :=
  g'.rsp = g.rsp ∧ g'.rbx = g.rbx ∧ g'.r14 = g.r14 ∧ g'.r15 = g.r15

theorem Fm.fr {S : Addr} {g0 g g' : Gprs} (h : Fm S g0 g) (h' : Fr g g') : Fm S g0 g' :=
  ⟨h'.1.trans h.1, h'.2.1.trans h.2.1, h'.2.2.1.trans h.2.2.1, h'.2.2.2.trans h.2.2.2⟩

/-- Back from a callee: `rsp` as before the `call`, the callee-saved registers kept. -/
theorem fm_ret {S : Addr} {g0 g g' : Gprs} (h : Fm S g0 g) (hs : g'.rsp = aR S) (hk : KS g g') : Fm S g0 g' :=
  ⟨hs, hk.1.trans h.2.1, hk.2.2.2.2.1.trans h.2.2.1, hk.2.2.2.2.2.trans h.2.2.2⟩

/-- The stack (`fb` the `fs` base, `ra` the return address): the three saved registers, the return address, the
stack guard as at `fs:0x28`. -/
abbrev Stk (fb : Addr) (W : Addr → Byte) (S : Addr) (g0 : Gprs) (ra : Addr) : Prop :=
  rdq(W, S - 8 - 8 - 8) = g0.rbp ∧ rdq(W, S - 8 - 8) = g0.r12 ∧ rdq(W, S - 8) = g0.r13 ∧ rdq(W, S) = ra ∧
    rdq(W, aR S + 40#64) = rdq(W, fb + 40#64)

/-- A callee from the `call` before `j` (entry `ent`, the bytes `W`, the registers `A`): at its entry, and from its
return at `j` with `rsp` = `aR S`, the callee-saved registers as at its entry, `B` and the invariant `J`, the run
goes on to the goal. -/
def KC (prof : Profile) (F : Footprint) (Wl : List Rgn) (L : List (Addr × List Byte)) (s₀ : State) (o : Oracle)
    (gev : List Event) (gP : State → Nat → List Event → Prop) (gE : Outcome → List Event → Prop)
    (S : Addr) (J : (Addr → Byte) → Prop) (ent : Addr) (j : Nat) (W : Addr → Byte) (A B : Gprs → Prop) : Prop :=
  ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y →
    Agree F Y.proc.mm.mem (Vst W (aR S - 8) (toBytesLE (nps_at.add j) 8)) →
    Y.cpu.rip = ent → Y.cpu.gpr.rsp = aR S - 8 → A Y.cpu.gpr →
    (∀ (Z : State) (W' : Addr → Byte) (t'' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem W' →
      Z.cpu.rip = nps_at.add j → Z.cpu.gpr.rsp = aR S → KS Y.cpu.gpr Z.cpu.gpr → B Z.cpu.gpr → J W' →
      GoG prof L o gev gP gE Z t'') →
    GoG prof L o gev gP gE Y t'

/-! ## The hypotheses of the runs -/

/-- The hypotheses of the runs from the cut points (`fb` the `fs` base, `S`, `g0` the entry's stack pointer and
registers, `e₂.add j₂` the return address, `I` the invariant of the bytes): the stack (`hcl`..`hr8`); the callees
keep `I`, from any return offset. -/
structure Ev (prof : Profile) (F : Footprint) (Wl : List Rgn) (L : List (Addr × List Byte)) (s₀ : State)
    (o : Oracle) (gev : List Event) (gP : State → Nat → List Event → Prop) (gE : Outcome → List Event → Prop)
    (fb S : Addr) (g0 : Gprs) (e₂ : Addr) (code₂ : List Byte) (j₂ : Nat) (I : (Addr → Byte) → Prop) :
    Prop where
  c : Seg prof F Wl L s₀ o
  hfs : s₀.cpu.seg.fsBase = fb
  hin : CodeIn L nps_at nps
  hin₂ : CodeIn L e₂ code₂
  h₂ : j₂ < code₂.length
  hI : ∀ W, I W → Stk fb W S g0 (e₂.add j₂)
  hcl : ∀ i < 8, Foot F.data (Addr.add (fb + 40#64) i)
  fg : ∀ i < 8, Foot F.data (Addr.add (aR S + 40#64) i)
  fl0 : ∀ i < 8, Foot F.data (Addr.add (aR S) i)
  fl16 : ∀ i < 8, Foot F.data (Addr.add (aR S + 16#64) i)
  fb24 : ∀ i < 8, Foot F.data (Addr.add (S - 8 - 8 - 8) i)
  fb16 : ∀ i < 8, Foot F.data (Addr.add (S - 8 - 8) i)
  fb8 : ∀ i < 8, Foot F.data (Addr.add (S - 8) i)
  hl : ∀ i < 8, Foot F.data (Addr.add S i)
  hr8 : ∀ i < 8, Foot Wl (Addr.add (aR S - 8) i)
  cU : ∃ code : List Byte, CodeIn L 0x44d5d0#64 code ∧ 0 < code.length
  cN : ∃ code : List Byte, CodeIn L 0x5a15e0#64 code ∧ 0 < code.length
  cA : ∃ code : List Byte, CodeIn L 0x44c360#64 code ∧ 0 < code.length
  cP : ∃ code : List Byte, CodeIn L 0x5a14f0#64 code ∧ 0 < code.length
  cD : ∃ code : List Byte, CodeIn L 0x6014f0#64 code ∧ 0 < code.length
  kU : ∀ j W, I W → KC prof F Wl L s₀ o gev gP gE S I 0x44d5d0#64 j W (fun _ => True) (fun _ => True)
  kN : ∀ j W, I W → KC prof F Wl L s₀ o gev gP gE S I 0x5a15e0#64 j W (fun _ => True) (fun _ => True)
  kA : ∀ j W, I W → KC prof F Wl L s₀ o gev gP gE S I 0x44c360#64 j W (fun _ => True) (fun _ => True)
  kP : ∀ j W, I W → KC prof F Wl L s₀ o gev gP gE S I 0x5a14f0#64 j W (fun _ => True) (fun _ => True)
  kD : ∀ j W, I W → KC prof F Wl L s₀ o gev gP gE S I 0x6014f0#64 j W (fun _ => True) (fun _ => True)
  kr : ∀ (W : Addr → Byte) (Z' : State) (t' : Nat), KeptW Wl s₀ Z' → Agree F Z'.proc.mm.mem W →
    Z'.cpu.rip = e₂.add j₂ → Z'.cpu.gpr.rsp = S + 8 → KS g0 Z'.cpu.gpr → I W →
    GoG prof L o gev gP gE Z' t'

section Runs
variable {prof : Profile} {F : Footprint} {Wl : List Rgn} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {fb S : Addr} {g0 : Gprs} {e₂ : Addr} {code₂ : List Byte} {j₂ : Nat} {I : (Addr → Byte) → Prop}
  {W : Addr → Byte}

/-- A `call` at `j` (`rsp` = `aR S`, the bytes `W`) of the callee `k`, and from its return at `j + 5`. -/
theorem callK (E : Ev prof F Wl L s₀ o gev gP gE fb S g0 e₂ code₂ j₂ I)
    {J : (Addr → Byte) → Prop} {U : State} {t₁ : Nat} {j R : Nat} {ent : Addr} {A B : Gprs → Prop}
    (hKU : KeptW Wl s₀ U) (hAU : Agree F U.proc.mm.mem W) (hrU : U.cpu.rip = nps_at.add j)
    (hs : U.cpu.gpr.rsp = aR S) (hj : j < nps.length) (hd : Dec prof.feat nps j (FV7z.mk .call 64 [.rel R] 5))
    (htgt : nps_at.add (j + 5) + BitVec.ofNat 64 R = ent)
    (hc : ∃ code : List Byte, CodeIn L ent code ∧ 0 < code.length)
    (k : KC prof F Wl L s₀ o gev gP gE S J ent (j + 5) W A B) (hA : A (U.cpu.gpr.set 4 (aR S - 8)))
    (h : ∀ (Z : State) (W' : Addr → Byte) (t'' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem W' →
      Z.cpu.rip = nps_at.add (j + 5) → Z.cpu.gpr.rsp = aR S → KS U.cpu.gpr Z.cpu.gpr → B Z.cpu.gpr → J W' →
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
macro "sstep" : tactic => `(tactic| first
  | with_reducible rfl
  | with_reducible assumption
  | exact rfl
  | apply And.intro
  | intro _)

end FV7z.Nps
