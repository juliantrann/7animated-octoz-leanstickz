import FV7z.Bop.Cuts
import FV7z.Api.Holds
import FV7z.Lemmas.AddMi64
import FV7z.Tun.Inv
/-!
# `CExtractCallbackConsole::BeforeOpen`: the instructions outside the blocks, the frame (PLAN.md §M, M1)

7-Zip 26.06's `CExtractCallbackConsole::BeforeOpen (name, testMode)` (`CPP/7zip/UI/Console/ExtractCallbackConsole.cpp`;
`objdump -d`) at `0x5e7b70` in `7zzs`: `this` = `rdi` (`rbx` from 16 on), the fields read and stored below `this + 456`.
`S` the stack pointer at the entry: four pushes (`r13`, `r12`, `rbp`, `rbx`) and 8 bytes of frame (`aR S`). The callees:
`UString::operator=` at `0x44d670` (30), `endl` at `0x5a1470` (130, 187), `fputs` at `0x624cc0` (160),
`CStdOutStream::NormalizePrint_UString` at `0x5a17c0` (175), `AString::operator=` at `0x44c4c0` (216) and
`CPercentPrinter::ClosePrint` at `0x5f67c0` (262). `add qword [rbx + 0x180], 1` (61, `Seg.s_add_mi64`) is
`NumTryArcs++`; the break counter `NConsoleClose::g_BreakCounter` is the 4 bytes at `0x79f088`.

- The `call`s (`call_*`, `tgt_*`), the `add` (`add_61`), the `ret` (`ret_233`).
- `aR`, `r1`..`r5`: the frame; `P4`: the bytes after the pushes; `St`: the stack the run keeps; `KC`: a callee as a
  continuation (as in Aec).
- `Ev`: the hypotheses of the runs (`hso`: the stream `_so` at `this + 264` readable when not null); `callK`: a
  `call` and the run from its return.
- `astep`: one step of the closers of the pieces.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
open FV7z.Api (KS)
namespace FV7z.Bop
set_option linter.unusedVariables false

/-! ## The instructions outside the blocks -/

/-- The `call` of `UString::operator=` (30). -/
def pc30 : List Byte := [0xe8, 0xdd, 0x5a, 0xe6, 0xff]
theorem pc30_0 : ∀ feat, Dec feat pc30 0 (FV7z.mk .call 64 [.rel 18446744073707870941] 5) := by dec_rfl
theorem wc_30 : pc30 <+: bop.drop 30 := by decide +kernel
theorem call_30 (feat : Features) : Dec feat bop 30 (FV7z.mk .call 64 [.rel 18446744073707870941] 5) :=
  Dec.shift (j := 30) (k := 0) (pc30_0 feat) wc_30 (Nat.zero_le _)
theorem tgt_30 : bop_at.add (30 + 5) + BitVec.ofNat 64 18446744073707870941 = 0x44d670#64 := by decide

/-- The `call` of `endl` (130). -/
def pc130 : List Byte := [0xe8, 0x79, 0x98, 0xfb, 0xff]
theorem pc130_0 : ∀ feat, Dec feat pc130 0 (FV7z.mk .call 64 [.rel 18446744073709262969] 5) := by dec_rfl
theorem wc_130 : pc130 <+: bop.drop 130 := by decide +kernel
theorem call_130 (feat : Features) : Dec feat bop 130 (FV7z.mk .call 64 [.rel 18446744073709262969] 5) :=
  Dec.shift (j := 130) (k := 0) (pc130_0 feat) wc_130 (Nat.zero_le _)
theorem tgt_130 : bop_at.add (130 + 5) + BitVec.ofNat 64 18446744073709262969 = 0x5a1470#64 := by decide

/-- The `call` of `fputs` (160). -/
def pc160 : List Byte := [0xe8, 0xab, 0xd0, 0x03, 0x00]
theorem pc160_0 : ∀ feat, Dec feat pc160 0 (FV7z.mk .call 64 [.rel 250027] 5) := by dec_rfl
theorem wc_160 : pc160 <+: bop.drop 160 := by decide +kernel
theorem call_160 (feat : Features) : Dec feat bop 160 (FV7z.mk .call 64 [.rel 250027] 5) :=
  Dec.shift (j := 160) (k := 0) (pc160_0 feat) wc_160 (Nat.zero_le _)
theorem tgt_160 : bop_at.add (160 + 5) + BitVec.ofNat 64 250027 = 0x624cc0#64 := by decide

/-- The `call` of `CStdOutStream::NormalizePrint_UString` (175). -/
def pc175 : List Byte := [0xe8, 0x9c, 0x9b, 0xfb, 0xff]
theorem pc175_0 : ∀ feat, Dec feat pc175 0 (FV7z.mk .call 64 [.rel 18446744073709263772] 5) := by dec_rfl
theorem wc_175 : pc175 <+: bop.drop 175 := by decide +kernel
theorem call_175 (feat : Features) : Dec feat bop 175 (FV7z.mk .call 64 [.rel 18446744073709263772] 5) :=
  Dec.shift (j := 175) (k := 0) (pc175_0 feat) wc_175 (Nat.zero_le _)
theorem tgt_175 : bop_at.add (175 + 5) + BitVec.ofNat 64 18446744073709263772 = 0x5a17c0#64 := by decide

/-- The `call` of `endl` (187). -/
def pc187 : List Byte := [0xe8, 0x40, 0x98, 0xfb, 0xff]
theorem pc187_0 : ∀ feat, Dec feat pc187 0 (FV7z.mk .call 64 [.rel 18446744073709262912] 5) := by dec_rfl
theorem wc_187 : pc187 <+: bop.drop 187 := by decide +kernel
theorem call_187 (feat : Features) : Dec feat bop 187 (FV7z.mk .call 64 [.rel 18446744073709262912] 5) :=
  Dec.shift (j := 187) (k := 0) (pc187_0 feat) wc_187 (Nat.zero_le _)
theorem tgt_187 : bop_at.add (187 + 5) + BitVec.ofNat 64 18446744073709262912 = 0x5a1470#64 := by decide

/-- The `call` of `AString::operator=` (216). -/
def pc216 : List Byte := [0xe8, 0x73, 0x48, 0xe6, 0xff]
theorem pc216_0 : ∀ feat, Dec feat pc216 0 (FV7z.mk .call 64 [.rel 18446744073707866227] 5) := by dec_rfl
theorem wc_216 : pc216 <+: bop.drop 216 := by decide +kernel
theorem call_216 (feat : Features) : Dec feat bop 216 (FV7z.mk .call 64 [.rel 18446744073707866227] 5) :=
  Dec.shift (j := 216) (k := 0) (pc216_0 feat) wc_216 (Nat.zero_le _)
theorem tgt_216 : bop_at.add (216 + 5) + BitVec.ofNat 64 18446744073707866227 = 0x44c4c0#64 := by decide

/-- The `call` of `CPercentPrinter::ClosePrint` (262). -/
def pc262 : List Byte := [0xe8, 0x45, 0xeb, 0x00, 0x00]
theorem pc262_0 : ∀ feat, Dec feat pc262 0 (FV7z.mk .call 64 [.rel 60229] 5) := by dec_rfl
theorem wc_262 : pc262 <+: bop.drop 262 := by decide +kernel
theorem call_262 (feat : Features) : Dec feat bop 262 (FV7z.mk .call 64 [.rel 60229] 5) :=
  Dec.shift (j := 262) (k := 0) (pc262_0 feat) wc_262 (Nat.zero_le _)
theorem tgt_262 : bop_at.add (262 + 5) + BitVec.ofNat 64 60229 = 0x5f67c0#64 := by decide

/-- `add qword [rbx + 0x180], 1` (61). -/
def pad : List Byte := [0x48, 0x83, 0x83, 0x80, 0x01, 0x00, 0x00, 0x01]
theorem pad_0 : ∀ feat, Dec feat pad 0 (FV7z.mk .add 64 [.mem (mbd 3 384 64), .imm 64 1] 8) := by dec_rfl
theorem w_61 : pad <+: bop.drop 61 := by decide +kernel
theorem add_61 (feat : Features) : Dec feat bop 61 (FV7z.mk .add 64 [.mem (mbd 3 384 64), .imm 64 1] 8) :=
  Dec.shift (j := 61) (k := 0) (pad_0 feat) w_61 (Nat.zero_le _)

/-- The `ret` (233). -/
def pret : List Byte := [0xc3]
theorem pret_0 : ∀ feat, Dec feat pret 0 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem w_233 : pret <+: bop.drop 233 := by decide +kernel
theorem ret_233 (feat : Features) : Dec feat bop 233 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 233) (k := 0) (pret_0 feat) w_233 (Nat.zero_le _)

/-! ## The frame -/

/-- The stack pointer after the four pushes and `sub rsp, 8`. -/
abbrev aR (S : Addr) : Addr := S - 8 - 8 - 8 - 8 - 8

theorem r1 (S : Addr) : aR S + 8#64 = S - 8 - 8 - 8 - 8 := BitVec.sub_add_cancel _ _
theorem r2 (S : Addr) : S - 8 - 8 - 8 - 8 + 8 = S - 8 - 8 - 8 := BitVec.sub_add_cancel _ _
theorem r3 (S : Addr) : S - 8 - 8 - 8 + 8 = S - 8 - 8 := BitVec.sub_add_cancel _ _
theorem r4 (S : Addr) : S - 8 - 8 + 8 = S - 8 := BitVec.sub_add_cancel _ _
theorem r5 (S : Addr) : S - 8 + 8 = S := BitVec.sub_add_cancel _ _

/-- The bytes after the four pushes. -/
abbrev P4 (V : Addr → Byte) (g : Gprs) : Addr → Byte :=
  Vst (Vst (Vst (Vst V (g.rsp - 8) (toBytesLE g.r13 8)) (g.rsp - 8 - 8) (toBytesLE g.r12 8))
    (g.rsp - 8 - 8 - 8) (toBytesLE g.rbp 8)) (g.rsp - 8 - 8 - 8 - 8) (toBytesLE g.rbx 8)

/-- The stack (`ra` the return address): the four saved registers, the return address. -/
abbrev St (W : Addr → Byte) (S : Addr) (g0 : Gprs) (ra : Addr) : Prop :=
  rdq(W, S - 8 - 8 - 8 - 8) = g0.rbx ∧ rdq(W, S - 8 - 8 - 8) = g0.rbp ∧ rdq(W, S - 8 - 8) = g0.r12 ∧
    rdq(W, S - 8) = g0.r13 ∧ rdq(W, S) = ra

/-- A callee from the `call` before `j` (entry `ent`, the bytes `W`, the registers `A`): at its entry, and from its
return at `j` with `rsp` = `aR S`, the callee-saved registers as at its entry, `B` and the invariant `J`, the run
goes on to the goal. -/
def KC (prof : Profile) (F : Footprint) (Wl : List Rgn) (L : List (Addr × List Byte)) (s₀ : State) (o : Oracle)
    (gev : List Event) (gP : State → Nat → List Event → Prop) (gE : Outcome → List Event → Prop)
    (S : Addr) (J : (Addr → Byte) → Prop) (ent : Addr) (j : Nat) (W : Addr → Byte) (A B : Gprs → Prop) : Prop :=
  ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y →
    Agree F Y.proc.mm.mem (Vst W (aR S - 8) (toBytesLE (bop_at.add j) 8)) →
    Y.cpu.rip = ent → Y.cpu.gpr.rsp = aR S - 8 → A Y.cpu.gpr →
    (∀ (Z : State) (W' : Addr → Byte) (t'' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem W' →
      Z.cpu.rip = bop_at.add j → Z.cpu.gpr.rsp = aR S → KS Y.cpu.gpr Z.cpu.gpr → B Z.cpu.gpr → J W' →
      GoG prof L o gev gP gE Z t'') →
    GoG prof L o gev gP gE Y t'

/-! ## The hypotheses of the runs -/

/-- The hypotheses of the runs from the cut points (`S`, `g0` the entry's stack pointer and registers, `e₂.add j₂`
the return address, `I` the invariant of the bytes): the fields of the object at `this` = `g0.rdi` below 456 may be
read and stored into (`hrd`, `hob`), the stores keep `I` (`hcl`), the stream `_so` (`this + 264`) may be read when
not null (`hso`), the break counter may be read (`hbr`), and the callees keep `I`, from any return offset. -/
structure Ev (prof : Profile) (F : Footprint) (Wl : List Rgn) (L : List (Addr × List Byte)) (s₀ : State)
    (o : Oracle) (gev : List Event) (gP : State → Nat → List Event → Prop) (gE : Outcome → List Event → Prop)
    (S : Addr) (g0 : Gprs) (e₂ : Addr) (code₂ : List Byte) (j₂ : Nat) (I : (Addr → Byte) → Prop) : Prop where
  c : Seg prof F Wl L s₀ o
  hin : CodeIn L bop_at bop
  hin₂ : CodeIn L e₂ code₂
  h₂ : j₂ < code₂.length
  hI : ∀ W, I W → St W S g0 (e₂.add j₂)
  hob : ∀ (k : BitVec 64) (n : Nat), k.toNat + n ≤ 456 → ∀ i < n, Foot Wl (Addr.add (g0.rdi + k) i)
  hrd : ∀ (k : BitVec 64) (n : Nat), k.toNat + n ≤ 456 → ∀ i < n, Foot F.data (Addr.add (g0.rdi + k) i)
  hcl : ∀ (W : Addr → Byte) (k : BitVec 64) (n : Nat) (bs : List Byte), bs.length = n → k.toNat + n ≤ 456 →
    I W → I (Vst W (g0.rdi + k) bs)
  hso : ∀ W, I W → rdq(W, g0.rdi + 264#64) ≠ 0 → ∀ i < 8, Foot F.data (Addr.add rdq(W, g0.rdi + 264#64) i)
  hbr : ∀ i < 4, Foot F.data (Addr.add 7991432#64 i)
  hs1 : ∀ i < 8, Foot Wl (Addr.add (S - 8) i)
  hs2 : ∀ i < 8, Foot Wl (Addr.add (S - 8 - 8) i)
  hs3 : ∀ i < 8, Foot Wl (Addr.add (S - 8 - 8 - 8) i)
  hs4 : ∀ i < 8, Foot Wl (Addr.add (S - 8 - 8 - 8 - 8) i)
  hl : ∀ i < 8, Foot F.data (Addr.add S i)
  hr8 : ∀ i < 8, Foot Wl (Addr.add (aR S - 8) i)
  cU : ∃ code : List Byte, CodeIn L 0x44d670#64 code ∧ 0 < code.length
  cE : ∃ code : List Byte, CodeIn L 0x5a1470#64 code ∧ 0 < code.length
  cF : ∃ code : List Byte, CodeIn L 0x624cc0#64 code ∧ 0 < code.length
  cN : ∃ code : List Byte, CodeIn L 0x5a17c0#64 code ∧ 0 < code.length
  cA : ∃ code : List Byte, CodeIn L 0x44c4c0#64 code ∧ 0 < code.length
  cC : ∃ code : List Byte, CodeIn L 0x5f67c0#64 code ∧ 0 < code.length
  kU : ∀ j W, I W → KC prof F Wl L s₀ o gev gP gE S I 0x44d670#64 j W (fun _ => True) (fun _ => True)
  kE : ∀ j W, I W → KC prof F Wl L s₀ o gev gP gE S I 0x5a1470#64 j W (fun _ => True) (fun _ => True)
  kF : ∀ j W, I W → KC prof F Wl L s₀ o gev gP gE S I 0x624cc0#64 j W (fun _ => True) (fun _ => True)
  kN : ∀ j W, I W → KC prof F Wl L s₀ o gev gP gE S I 0x5a17c0#64 j W (fun _ => True) (fun _ => True)
  kA : ∀ j W, I W → KC prof F Wl L s₀ o gev gP gE S I 0x44c4c0#64 j W (fun _ => True) (fun _ => True)
  kC : ∀ j W, I W → KC prof F Wl L s₀ o gev gP gE S I 0x5f67c0#64 j W (fun _ => True) (fun _ => True)
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
    (hKU : KeptW Wl s₀ U) (hAU : Agree F U.proc.mm.mem W) (hrU : U.cpu.rip = bop_at.add j)
    (hs : U.cpu.gpr.rsp = aR S) (hj : j < bop.length) (hd : Dec prof.feat bop j (FV7z.mk .call 64 [.rel R] 5))
    (htgt : bop_at.add (j + 5) + BitVec.ofNat 64 R = ent)
    (hc : ∃ code : List Byte, CodeIn L ent code ∧ 0 < code.length)
    (k : KC prof F Wl L s₀ o gev gP gE S J ent (j + 5) W A B) (hA : A (U.cpu.gpr.set 4 (aR S - 8)))
    (h : ∀ (Z : State) (W' : Addr → Byte) (t'' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem W' →
      Z.cpu.rip = bop_at.add (j + 5) → Z.cpu.gpr.rsp = aR S → KS U.cpu.gpr Z.cpu.gpr → B Z.cpu.gpr → J W' →
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
macro "astep" : tactic => `(tactic| first
  | with_reducible rfl
  | with_reducible assumption
  | exact rfl
  | apply And.intro
  | intro _)

end FV7z.Bop
