import FV7z.Mbs.Cuts
import FV7z.Api.Holds
import FV7z.Tun.Inv
/-!
# `MultiByteToUnicodeString (const AString &, UINT)`: the instructions outside the blocks, the frame (PLAN.md §M, M1)

7-Zip 26.06's `MultiByteToUnicodeString (src, codePage)` (`CPP/Common/StringConvert.cpp`; `objdump -d`) at
`0x450c60` in `7zzs`: the result's `UString` slot = `rdi` (`r12`), `src` = `rsi` (`rbp`), `codePage` = `edx`
(`r13d`); it returns the slot (`rax`). `S` the stack pointer at the entry: three pushes (`r13`, `r12`, `rbp`), no
other frame (`aR S`). It reads no `fs`; `fb` (the `fs` base) only for the same shape as its callers' proofs. The
callees: `UString::UString ()` at `0x44d3e0` (18) and `MultiByteToUnicodeString2` at `0x450a60` (32).

- The `call`s (`call_*`, `tgt_*`), the `ret` (`ret_45`).
- `aR`, `P3`, `q1`..`q3`: the frame, the bytes after the pushes, the pops' addresses.
- `Fm`, `Fr`, `Stk`, `KC`, `Ev`: the frame's registers, what a piece keeps, the stack, a callee as a continuation,
  the hypotheses of the runs; `callK`: a `call` and the run from its return.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
open FV7z.Api (KS)
namespace FV7z.Mbs
set_option linter.unusedVariables false

/-! ## The instructions outside the blocks -/

/-- The `call` of `UString::UString ()` (18). -/
def pc18 : List Byte := [0xe8, 0x69, 0xc7, 0xff, 0xff]
theorem pc18_0 : ∀ feat, Dec feat pc18 0 (FV7z.mk .call 64 [.rel 18446744073709537129] 5) := by dec_rfl
theorem wc_18 : pc18 <+: mbs.drop 18 := by decide +kernel
theorem call_18 (feat : Features) : Dec feat mbs 18 (FV7z.mk .call 64 [.rel 18446744073709537129] 5) :=
  Dec.shift (j := 18) (k := 0) (pc18_0 feat) wc_18 (Nat.zero_le _)
theorem tgt_18 : mbs_at.add (18 + 5) + BitVec.ofNat 64 18446744073709537129 = 0x44d3e0#64 := by decide

/-- The `call` of `MultiByteToUnicodeString2` (32). -/
def pc32 : List Byte := [0xe8, 0xdb, 0xfd, 0xff, 0xff]
theorem pc32_0 : ∀ feat, Dec feat pc32 0 (FV7z.mk .call 64 [.rel 18446744073709551067] 5) := by dec_rfl
theorem wc_32 : pc32 <+: mbs.drop 32 := by decide +kernel
theorem call_32 (feat : Features) : Dec feat mbs 32 (FV7z.mk .call 64 [.rel 18446744073709551067] 5) :=
  Dec.shift (j := 32) (k := 0) (pc32_0 feat) wc_32 (Nat.zero_le _)
theorem tgt_32 : mbs_at.add (32 + 5) + BitVec.ofNat 64 18446744073709551067 = 0x450a60#64 := by decide

/-- The `ret` (45). -/
def pret : List Byte := [0xc3]
theorem pret_0 : ∀ feat, Dec feat pret 0 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem w_45 : pret <+: mbs.drop 45 := by decide +kernel
theorem ret_45 (feat : Features) : Dec feat mbs 45 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 45) (k := 0) (pret_0 feat) w_45 (Nat.zero_le _)

/-! ## The frame -/

/-- The stack pointer after the three pushes. -/
abbrev aR (S : Addr) : Addr := S - 8 - 8 - 8

/-- The bytes after the three pushes (`r13`, `r12`, `rbp`). -/
abbrev P3 (V : Addr → Byte) (g : Gprs) : Addr → Byte :=
  Vst (Vst (Vst V (g.rsp - 8) (toBytesLE g.r13 8)) (g.rsp - 8 - 8) (toBytesLE g.r12 8))
    (g.rsp - 8 - 8 - 8) (toBytesLE g.rbp 8)

theorem q1 (S : Addr) : aR S + 8 = S - 8 - 8 := BitVec.sub_add_cancel _ _
theorem q2 (S : Addr) : aR S + 8 + 8 = S - 8 := by rw [q1, BitVec.sub_add_cancel]
theorem q3 (S : Addr) : aR S + 8 + 8 + 8 = S := by rw [q2, BitVec.sub_add_cancel]

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

/-- The stack (`ra` the return address): the three saved registers, the return address. -/
abbrev Stk (W : Addr → Byte) (S : Addr) (g0 : Gprs) (ra : Addr) : Prop :=
  rdq(W, S - 8 - 8 - 8) = g0.rbp ∧ rdq(W, S - 8 - 8) = g0.r12 ∧ rdq(W, S - 8) = g0.r13 ∧ rdq(W, S) = ra

/-- A callee from the `call` before `j` (entry `ent`, the bytes `W`, the registers `A`): at its entry, and from its
return at `j` with `rsp` = `aR S`, the callee-saved registers as at its entry, `B` and the invariant `J`, the run
goes on to the goal. -/
def KC (prof : Profile) (F : Footprint) (Wl : List Rgn) (L : List (Addr × List Byte)) (s₀ : State) (o : Oracle)
    (gev : List Event) (gP : State → Nat → List Event → Prop) (gE : Outcome → List Event → Prop)
    (S : Addr) (J : (Addr → Byte) → Prop) (ent : Addr) (j : Nat) (W : Addr → Byte) (A B : Gprs → Prop) : Prop :=
  ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y →
    Agree F Y.proc.mm.mem (Vst W (aR S - 8) (toBytesLE (mbs_at.add j) 8)) →
    Y.cpu.rip = ent → Y.cpu.gpr.rsp = aR S - 8 → A Y.cpu.gpr →
    (∀ (Z : State) (W' : Addr → Byte) (t'' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem W' →
      Z.cpu.rip = mbs_at.add j → Z.cpu.gpr.rsp = aR S → KS Y.cpu.gpr Z.cpu.gpr → B Z.cpu.gpr → J W' →
      GoG prof L o gev gP gE Z t'') →
    GoG prof L o gev gP gE Y t'

/-! ## The hypotheses of the runs -/

/-- The hypotheses of the runs from the cut points (`fb` the `fs` base, `S`, `g0` the entry's stack pointer and
registers, `e₂.add j₂` the return address, `I` the invariant of the bytes): the stack (`fb24`..`hr8`); the callees
keep `I`, from any return offset; the return with `rax` = the slot. -/
structure Ev (prof : Profile) (F : Footprint) (Wl : List Rgn) (L : List (Addr × List Byte)) (s₀ : State)
    (o : Oracle) (gev : List Event) (gP : State → Nat → List Event → Prop) (gE : Outcome → List Event → Prop)
    (fb S : Addr) (g0 : Gprs) (e₂ : Addr) (code₂ : List Byte) (j₂ : Nat) (I : (Addr → Byte) → Prop) :
    Prop where
  c : Seg prof F Wl L s₀ o
  hfs : s₀.cpu.seg.fsBase = fb
  hin : CodeIn L mbs_at mbs
  hin₂ : CodeIn L e₂ code₂
  h₂ : j₂ < code₂.length
  hI : ∀ W, I W → Stk W S g0 (e₂.add j₂)
  fb24 : ∀ i < 8, Foot F.data (Addr.add (S - 8 - 8 - 8) i)
  fb16 : ∀ i < 8, Foot F.data (Addr.add (S - 8 - 8) i)
  fb8 : ∀ i < 8, Foot F.data (Addr.add (S - 8) i)
  hl : ∀ i < 8, Foot F.data (Addr.add S i)
  hr8 : ∀ i < 8, Foot Wl (Addr.add (aR S - 8) i)
  cU : ∃ code : List Byte, CodeIn L 0x44d3e0#64 code ∧ 0 < code.length
  cM : ∃ code : List Byte, CodeIn L 0x450a60#64 code ∧ 0 < code.length
  kU : ∀ j W, I W → KC prof F Wl L s₀ o gev gP gE S I 0x44d3e0#64 j W (fun _ => True) (fun _ => True)
  kM : ∀ j W, I W → KC prof F Wl L s₀ o gev gP gE S I 0x450a60#64 j W (fun _ => True) (fun _ => True)
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
    (hKU : KeptW Wl s₀ U) (hAU : Agree F U.proc.mm.mem W) (hrU : U.cpu.rip = mbs_at.add j)
    (hs : U.cpu.gpr.rsp = aR S) (hj : j < mbs.length) (hd : Dec prof.feat mbs j (FV7z.mk .call 64 [.rel R] 5))
    (htgt : mbs_at.add (j + 5) + BitVec.ofNat 64 R = ent)
    (hc : ∃ code : List Byte, CodeIn L ent code ∧ 0 < code.length)
    (k : KC prof F Wl L s₀ o gev gP gE S J ent (j + 5) W A B) (hA : A (U.cpu.gpr.set 4 (aR S - 8)))
    (h : ∀ (Z : State) (W' : Addr → Byte) (t'' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem W' →
      Z.cpu.rip = mbs_at.add (j + 5) → Z.cpu.gpr.rsp = aR S → KS U.cpu.gpr Z.cpu.gpr → B Z.cpu.gpr → J W' →
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
macro "mbsstep" : tactic => `(tactic| first
  | with_reducible rfl
  | with_reducible assumption
  | exact rfl
  | apply And.intro
  | intro _)

end FV7z.Mbs
