import FV7z.Cps.Cuts
import FV7z.Api.Holds
import FV7z.Lemmas.SetccM
import FV7z.Tun.Inv
/-!
# `NCommandLineParser::CParser::ParseString`: the instructions outside the blocks and the frame (PLAN.md §M, M1)

7-Zip 26.06's `CParser::ParseString (this, s, switchForms, numSwitches)` (`CPP/Common/CommandLineParser.cpp`;
`objdump -d`) at `0x5a0650` in `7zzs`: `this` = `rdi`, the command string `s` = `rsi` (a `UString`: `_chars` at `+ 0`,
`_len` at `+ 8`), `switchForms` = `rdx` (24-byte `CSwitchForm`s: `Key` at `+ 0`, `Type` at `+ 8`, `Multi` at `+ 9`,
`MinLen` at `+ 10`, `PostCharSet` at `+ 16`), `numSwitches` = `ecx`. `S` the stack pointer at the entry: six pushes and
`sub rsp, 0x48` (`aR S`); `this` at `aR S + 24`, `switchForms` at `+ 16`, `ecx` kept over the `call` at 151 at `+ 12`,
a local `UString` at `+ 32`, the stack guard at `+ 56`.

- The `call`s (`call_*`, `tgt_*`), the `ja` to the throw (`ja_551`), the `sete` (`set_429`), the `ret` (`ret_368`).
- `aR`, `q1`..`q7`: the frame; `P4`, `B12`: the bytes after the pieces at 0 and 12; `Sk`: the stack the run keeps
  (`Api.Stk` and the stack guard); `KC`: a callee as a continuation (as in Ais); `nx`, `sz24`, `Lk`: the strlen
  loop's next index, `24 c`, what a piece of the switch loop keeps.
- `cpx`: `wpx` with the branch conditions as propositions, the one-byte reads and `xor r, r`; `cstep`: one step of
  the closers of the pieces.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
open FV7z.Api (P6 Stk KS)
namespace FV7z.Cps
set_option linter.unusedVariables false

/-! ## The instructions outside the blocks -/

/-- The `call` of `IsString1PrefixedByString2_NoCase_Ascii` (151). -/
def pc151 : List Byte := [0xe8, 0xf4, 0xb6, 0xea, 0xff]
theorem pc151_0 : ∀ feat, Dec feat pc151 0 (FV7z.mk .call 64 [.rel 18446744073708156660] 5) := by dec_rfl
theorem wc_151 : pc151 <+: cps.drop 151 := by decide +kernel
theorem call_151 (feat : Features) : Dec feat cps 151 (FV7z.mk .call 64 [.rel 18446744073708156660] 5) :=
  Dec.shift (j := 151) (k := 0) (pc151_0 feat) wc_151 (Nat.zero_le _)
theorem tgt_151 : cps_at.add (151 + 5) + BitVec.ofNat 64 18446744073708156660 = 0x44bde0#64 := by decide

/-- The `call` of `AString::operator=` (407). -/
def pc407 : List Byte := [0xe8, 0xd4, 0xbc, 0xea, 0xff]
theorem pc407_0 : ∀ feat, Dec feat pc407 0 (FV7z.mk .call 64 [.rel 18446744073708158164] 5) := by dec_rfl
theorem wc_407 : pc407 <+: cps.drop 407 := by decide +kernel
theorem call_407 (feat : Features) : Dec feat cps 407 (FV7z.mk .call 64 [.rel 18446744073708158164] 5) :=
  Dec.shift (j := 407) (k := 0) (pc407_0 feat) wc_407 (Nat.zero_le _)
theorem tgt_407 : cps_at.add (407 + 5) + BitVec.ofNat 64 18446744073708158164 = 0x44c4c0#64 := by decide

/-- The `call` of `FindCharPosInString` (467). -/
def pc467 : List Byte := [0xe8, 0x38, 0xb1, 0xea, 0xff]
theorem pc467_0 : ∀ feat, Dec feat pc467 0 (FV7z.mk .call 64 [.rel 18446744073708155192] 5) := by dec_rfl
theorem wc_467 : pc467 <+: cps.drop 467 := by decide +kernel
theorem call_467 (feat : Features) : Dec feat cps 467 (FV7z.mk .call 64 [.rel 18446744073708155192] 5) :=
  Dec.shift (j := 467) (k := 0) (pc467_0 feat) wc_467 (Nat.zero_le _)
theorem tgt_467 : cps_at.add (467 + 5) + BitVec.ofNat 64 18446744073708155192 = 0x44b960#64 := by decide

/-- The `call` of `AString::operator=` (504). -/
def pc504 : List Byte := [0xe8, 0x73, 0xbc, 0xea, 0xff]
theorem pc504_0 : ∀ feat, Dec feat pc504 0 (FV7z.mk .call 64 [.rel 18446744073708158067] 5) := by dec_rfl
theorem wc_504 : pc504 <+: cps.drop 504 := by decide +kernel
theorem call_504 (feat : Features) : Dec feat cps 504 (FV7z.mk .call 64 [.rel 18446744073708158067] 5) :=
  Dec.shift (j := 504) (k := 0) (pc504_0 feat) wc_504 (Nat.zero_le _)
theorem tgt_504 : cps_at.add (504 + 5) + BitVec.ofNat 64 18446744073708158067 = 0x44c4c0#64 := by decide

/-- The `call` of the `UString` constructor (529). -/
def pc529 : List Byte := [0xe8, 0x1a, 0xcc, 0xea, 0xff]
theorem pc529_0 : ∀ feat, Dec feat pc529 0 (FV7z.mk .call 64 [.rel 18446744073708162074] 5) := by dec_rfl
theorem wc_529 : pc529 <+: cps.drop 529 := by decide +kernel
theorem call_529 (feat : Features) : Dec feat cps 529 (FV7z.mk .call 64 [.rel 18446744073708162074] 5) :=
  Dec.shift (j := 529) (k := 0) (pc529_0 feat) wc_529 (Nat.zero_le _)
theorem tgt_529 : cps_at.add (529 + 5) + BitVec.ofNat 64 18446744073708162074 = 0x44d480#64 := by decide

/-- The `call` of `operator new []` (587). -/
def pc587 : List Byte := [0xe8, 0x10, 0x21, 0x06, 0x00]
theorem pc587_0 : ∀ feat, Dec feat pc587 0 (FV7z.mk .call 64 [.rel 401680] 5) := by dec_rfl
theorem wc_587 : pc587 <+: cps.drop 587 := by decide +kernel
theorem call_587 (feat : Features) : Dec feat cps 587 (FV7z.mk .call 64 [.rel 401680] 5) :=
  Dec.shift (j := 587) (k := 0) (pc587_0 feat) wc_587 (Nat.zero_le _)
theorem tgt_587 : cps_at.add (587 + 5) + BitVec.ofNat 64 401680 = 0x6029b0#64 := by decide

/-- The `call` of `operator delete []` (621). -/
def pc621 : List Byte := [0xe8, 0x2e, 0x0c, 0x06, 0x00]
theorem pc621_0 : ∀ feat, Dec feat pc621 0 (FV7z.mk .call 64 [.rel 396334] 5) := by dec_rfl
theorem wc_621 : pc621 <+: cps.drop 621 := by decide +kernel
theorem call_621 (feat : Features) : Dec feat cps 621 (FV7z.mk .call 64 [.rel 396334] 5) :=
  Dec.shift (j := 621) (k := 0) (pc621_0 feat) wc_621 (Nat.zero_le _)
theorem tgt_621 : cps_at.add (621 + 5) + BitVec.ofNat 64 396334 = 0x6014f0#64 := by decide

/-- The `call` of `operator new` (641). -/
def pc641 : List Byte := [0xe8, 0x9a, 0x20, 0x06, 0x00]
theorem pc641_0 : ∀ feat, Dec feat pc641 0 (FV7z.mk .call 64 [.rel 401562] 5) := by dec_rfl
theorem wc_641 : pc641 <+: cps.drop 641 := by decide +kernel
theorem call_641 (feat : Features) : Dec feat cps 641 (FV7z.mk .call 64 [.rel 401562] 5) :=
  Dec.shift (j := 641) (k := 0) (pc641_0 feat) wc_641 (Nat.zero_le _)
theorem tgt_641 : cps_at.add (641 + 5) + BitVec.ofNat 64 401562 = 0x602970#64 := by decide

/-- The `call` of the `UString` copy (655). -/
def pc655 : List Byte := [0xe8, 0xec, 0xcc, 0xea, 0xff]
theorem pc655_0 : ∀ feat, Dec feat pc655 0 (FV7z.mk .call 64 [.rel 18446744073708162284] 5) := by dec_rfl
theorem wc_655 : pc655 <+: cps.drop 655 := by decide +kernel
theorem call_655 (feat : Features) : Dec feat cps 655 (FV7z.mk .call 64 [.rel 18446744073708162284] 5) :=
  Dec.shift (j := 655) (k := 0) (pc655_0 feat) wc_655 (Nat.zero_le _)
theorem tgt_655 : cps_at.add (655 + 5) + BitVec.ofNat 64 18446744073708162284 = 0x44d5d0#64 := by decide

/-- The `call` of `operator delete []` (696). -/
def pc696 : List Byte := [0xe8, 0xe3, 0x0b, 0x06, 0x00]
theorem pc696_0 : ∀ feat, Dec feat pc696 0 (FV7z.mk .call 64 [.rel 396259] 5) := by dec_rfl
theorem wc_696 : pc696 <+: cps.drop 696 := by decide +kernel
theorem call_696 (feat : Features) : Dec feat cps 696 (FV7z.mk .call 64 [.rel 396259] 5) :=
  Dec.shift (j := 696) (k := 0) (pc696_0 feat) wc_696 (Nat.zero_le _)
theorem tgt_696 : cps_at.add (696 + 5) + BitVec.ofNat 64 396259 = 0x6014f0#64 := by decide

/-- The `call` of `AString::operator=` (725). -/
def pc725 : List Byte := [0xe8, 0x96, 0xbb, 0xea, 0xff]
theorem pc725_0 : ∀ feat, Dec feat pc725 0 (FV7z.mk .call 64 [.rel 18446744073708157846] 5) := by dec_rfl
theorem wc_725 : pc725 <+: cps.drop 725 := by decide +kernel
theorem call_725 (feat : Features) : Dec feat cps 725 (FV7z.mk .call 64 [.rel 18446744073708157846] 5) :=
  Dec.shift (j := 725) (k := 0) (pc725_0 feat) wc_725 (Nat.zero_le _)
theorem tgt_725 : cps_at.add (725 + 5) + BitVec.ofNat 64 18446744073708157846 = 0x44c4c0#64 := by decide

/-- The `call` of `AString::operator=` (754). -/
def pc754 : List Byte := [0xe8, 0x79, 0xbb, 0xea, 0xff]
theorem pc754_0 : ∀ feat, Dec feat pc754 0 (FV7z.mk .call 64 [.rel 18446744073708157817] 5) := by dec_rfl
theorem wc_754 : pc754 <+: cps.drop 754 := by decide +kernel
theorem call_754 (feat : Features) : Dec feat cps 754 (FV7z.mk .call 64 [.rel 18446744073708157817] 5) :=
  Dec.shift (j := 754) (k := 0) (pc754_0 feat) wc_754 (Nat.zero_le _)
theorem tgt_754 : cps_at.add (754 + 5) + BitVec.ofNat 64 18446744073708157817 = 0x44c4c0#64 := by decide

/-- The `call` of `AString::operator=` (783). -/
def pc783 : List Byte := [0xe8, 0x5c, 0xbb, 0xea, 0xff]
theorem pc783_0 : ∀ feat, Dec feat pc783 0 (FV7z.mk .call 64 [.rel 18446744073708157788] 5) := by dec_rfl
theorem wc_783 : pc783 <+: cps.drop 783 := by decide +kernel
theorem call_783 (feat : Features) : Dec feat cps 783 (FV7z.mk .call 64 [.rel 18446744073708157788] 5) :=
  Dec.shift (j := 783) (k := 0) (pc783_0 feat) wc_783 (Nat.zero_le _)
theorem tgt_783 : cps_at.add (783 + 5) + BitVec.ofNat 64 18446744073708157788 = 0x44c4c0#64 := by decide

/-- The `call` of `memcpy` (804). -/
def pc804 : List Byte := [0xe8, 0xf7, 0x06, 0xe6, 0xff]
theorem pc804_0 : ∀ feat, Dec feat pc804 0 (FV7z.mk .call 64 [.rel 18446744073707849463] 5) := by dec_rfl
theorem wc_804 : pc804 <+: cps.drop 804 := by decide +kernel
theorem call_804 (feat : Features) : Dec feat cps 804 (FV7z.mk .call 64 [.rel 18446744073707849463] 5) :=
  Dec.shift (j := 804) (k := 0) (pc804_0 feat) wc_804 (Nat.zero_le _)
theorem tgt_804 : cps_at.add (804 + 5) + BitVec.ofNat 64 18446744073707849463 = 0x401070#64 := by decide

/-- The `ja` to the throw (551). -/
def pja : List Byte := [0x0f, 0x87, 0xff, 0x24, 0xe7, 0xff]
theorem pja_0 : ∀ feat, Dec feat pja 0 (FV7z.mk (.jcc 7) 64 [.rel 18446744073707922687] 6) := by dec_rfl
theorem wa_551 : pja <+: cps.drop 551 := by decide +kernel
theorem ja_551 (feat : Features) : Dec feat cps 551 (FV7z.mk (.jcc 7) 64 [.rel 18446744073707922687] 6) :=
  Dec.shift (j := 551) (k := 0) (pja_0 feat) wa_551 (Nat.zero_le _)

/-- The `sete` into `WithMinus` (429). -/
def pset : List Byte := [0x41, 0x0f, 0x94, 0x44, 0x24, 0x01]
theorem pset_0 : ∀ feat, Dec feat pset 0 (FV7z.mk (.setcc 4) 8 [.mem (mbd 12 1 8)] 6) := by dec_rfl
theorem ws_429 : pset <+: cps.drop 429 := by decide +kernel
theorem set_429 (feat : Features) : Dec feat cps 429 (FV7z.mk (.setcc 4) 8 [.mem (mbd 12 1 8)] 6) :=
  Dec.shift (j := 429) (k := 0) (pset_0 feat) ws_429 (Nat.zero_le _)

/-- The `ret`. -/
def pret : List Byte := [0xc3]
theorem pret_0 : ∀ feat, Dec feat pret 0 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem wt_368 : pret <+: cps.drop 368 := by decide +kernel
theorem ret_368 (feat : Features) : Dec feat cps 368 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 368) (k := 0) (pret_0 feat) wt_368 (Nat.zero_le _)

/-! ## The frame -/

/-- The stack pointer after the six pushes and `sub rsp, 0x48`. -/
abbrev aR (S : Addr) : Addr := S - 8 - 8 - 8 - 8 - 8 - 8 - 72#64

theorem q1 (S : Addr) : aR S + 72#64 = S - 8 - 8 - 8 - 8 - 8 - 8 := BitVec.sub_add_cancel _ _
theorem q2 (S : Addr) : aR S + 72#64 + 8 = S - 8 - 8 - 8 - 8 - 8 := by
  rw [q1]; exact BitVec.sub_add_cancel _ _
theorem q3 (S : Addr) : aR S + 72#64 + 8 + 8 = S - 8 - 8 - 8 - 8 := by
  rw [q2]; exact BitVec.sub_add_cancel _ _
theorem q4 (S : Addr) : aR S + 72#64 + 8 + 8 + 8 = S - 8 - 8 - 8 := by
  rw [q3]; exact BitVec.sub_add_cancel _ _
theorem q5 (S : Addr) : aR S + 72#64 + 8 + 8 + 8 + 8 = S - 8 - 8 := by
  rw [q4]; exact BitVec.sub_add_cancel _ _
theorem q6 (S : Addr) : aR S + 72#64 + 8 + 8 + 8 + 8 + 8 = S - 8 := by
  rw [q5]; exact BitVec.sub_add_cancel _ _
theorem q7 (S : Addr) : aR S + 72#64 + 8 + 8 + 8 + 8 + 8 + 8 = S := by
  rw [q6]; exact BitVec.sub_add_cancel _ _

/-- The bytes after the first four pushes (`r15`, `r14`, `r13`, `r12`). -/
abbrev P4 (V : Addr → Byte) (g : Gprs) : Addr → Byte :=
  Vst (Vst (Vst (Vst V (g.rsp - 8) (toBytesLE g.r15 8)) (g.rsp - 8 - 8) (toBytesLE g.r14 8))
    (g.rsp - 8 - 8 - 8) (toBytesLE g.r13 8)) (g.rsp - 8 - 8 - 8 - 8) (toBytesLE g.r12 8)

/-- The bytes after the piece at 12 from `g`: `rbp`, `rbx` pushed, `rdi` and `rdx` stored in the frame. -/
abbrev B12 (V : Addr → Byte) (g : Gprs) : Addr → Byte :=
  Vst (Vst (Vst (Vst V (g.rsp - 8) (toBytesLE g.rbp 8)) (g.rsp - 8 - 8) (toBytesLE g.rbx 8))
    (g.rsp - 8 - 8 - 72#64 + 24#64) (toBytesLE g.rdi 8)) (g.rsp - 8 - 8 - 72#64 + 16#64) (toBytesLE g.rdx 8)

/-- The stack (`fb` the `fs` base, `ra` the return address): the six saved registers, the return address, the stack
guard as at `fs:0x28`. -/
abbrev Sk (fb : Addr) (W : Addr → Byte) (S : Addr) (g0 : Gprs) (ra : Addr) : Prop :=
  Stk W S g0 ra ∧ rdq(W, aR S + 56#64) = rdq(W, fb + 40#64)

/-- A callee from the `call` before `j` (entry `ent`, the bytes `W`, the registers `A`): at its entry, and from its
return at `j` with `rsp` = `aR S`, the callee-saved registers as at its entry, `B` and the invariant `J`, the run
goes on to the goal. -/
def KC (prof : Profile) (F : Footprint) (Wl : List Rgn) (L : List (Addr × List Byte)) (s₀ : State) (o : Oracle)
    (gev : List Event) (gP : State → Nat → List Event → Prop) (gE : Outcome → List Event → Prop)
    (S : Addr) (J : (Addr → Byte) → Prop) (ent : Addr) (j : Nat) (W : Addr → Byte) (A B : Gprs → Prop) : Prop :=
  ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y →
    Agree F Y.proc.mm.mem (Vst W (aR S - 8) (toBytesLE (cps_at.add j) 8)) →
    Y.cpu.rip = ent → Y.cpu.gpr.rsp = aR S - 8 → A Y.cpu.gpr →
    (∀ (Z : State) (W' : Addr → Byte) (t'' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem W' →
      Z.cpu.rip = cps_at.add j → Z.cpu.gpr.rsp = aR S → KS Y.cpu.gpr Z.cpu.gpr → B Z.cpu.gpr → J W' →
      GoG prof L o gev gP gE Z t'') →
    GoG prof L o gev gP gE Y t'

/-! ## Values -/

/-- The strlen loop's next index: `lea edx, [rax + 1]`. -/
abbrev nx (x : BitVec 64) : BitVec 64 := BitVec.setWidth 64 (BitVec.setWidth 32 (x + 1#64))

/-- `lea rax, [r8 + r8 * 2]; shl rax, 3`: `24 c`. -/
abbrev sz24 (c : BitVec 64) : BitVec 64 := (c + c * 2#64) <<< 3

/-- What a piece of the switch loop (96..183) keeps: `rsp`, `r14` = `s`, `rcx` = `numSwitches`, `r13` = the form,
`r12` = its index, `r15` = the longest key's length so far, `rbp` = its index. -/
abbrev Lk (g g' : Gprs) : Prop :=
  g'.rsp = g.rsp ∧ g'.r14 = g.r14 ∧ g'.rcx = g.rcx ∧ g'.r13 = g.r13 ∧ g'.r12 = g.r12 ∧ g'.r15 = g.r15 ∧
    g'.rbp = g.rbp

/-! ## Tactics -/

/-- `wpx` with the branch conditions as propositions, the one-byte reads and `xor r, r`. -/
macro "cpx" "[" ls:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| wpx [BitVec.and_self, beq_iff_eq, beq_eq_false_iff_ne, Bool.not_eq_true', Bool.not_eq_false',
    decide_eq_true_eq, decide_eq_false_iff_not, Tun.rd1, BitVec.xor_self, BitVec.setWidth_zero, $ls,*])

/-- One step of the closers of the pieces. -/
macro "cstep" : tactic => `(tactic| first
  | with_reducible rfl
  | with_reducible assumption
  | apply And.intro
  | intro _)

end FV7z.Cps
