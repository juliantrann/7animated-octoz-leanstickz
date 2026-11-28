import FV7z.Pew.Cuts
import FV7z.Api.Holds
import FV7z.Tun.Inv
/-!
# `Print_ErrorFormatIndex_Warning`: the instructions outside the blocks, the frame (PLAN.md §M, M1)

7-Zip 26.06's `Print_ErrorFormatIndex_Warning (_so, codecs, arc)` (`CPP/7zip/UI/Console/ExtractCallbackConsole.cpp`;
`objdump -d`) at `0x5e96e0` in `7zzs`: `_so` = `rdi` (`rbp` up to 195), `codecs` = `rsi` (`r13`), `arc` = `rdx`
(`rbx`). `S` the stack pointer at the entry: four pushes (`r13`, `r12`, `rbp`, `rbx`) and 40 bytes of frame (`aR S`,
also in `r12` from 64 on): the stack guard (`fs:0x28`) at `aR S + 24`, a local `UString` at `aR S`. It reads
`_so->_stream` (`[rdi]`), `arc.FormatIndex` and `arc.ErrorInfo.ErrorFormatIndex` (the 4 bytes at `arc + 88`,
`arc + 164`), and for an index not negative `codecs->Formats` (`codecs + 16`), its item and the item's name (at
`+ 24`). The callees: `fwrite` at `0x624e40` (59), `CStdOutStream::NormalizePrint_UString_Path` at `0x5a1710` (74),
`UString::UString ()` at `0x44d3e0` (82), `Add_Messsage_Pre_ArcType` at `0x5e7a50` (136, 178),
`CStdOutStream::operator<< (const wchar_t *)` at `0x5a1530` (190), `endl` at `0x5a1470` (201, 209), `delete []` at
`0x6014f0` (223), `UString::Add_LF` at `0x44dab0` (259) and `UString::operator+= (const char *)` at `0x44dbe0` (274).

- The `call`s (`call_*`, `tgt_*`), the `ret` (`ret_254`); `sw_sx`: a 32-bit value sign-extended and cut back.
- `aR`, `P4`, `V0`, `q1`..`q5`: the frame, the bytes after the pushes and after the prologue, the pops' addresses.
- `Fm`, `Fr`, `Stk`, `KC`, `Ev`: the frame's registers, what a piece keeps, the stack, a callee as a continuation,
  the hypotheses of the runs; `callK`: a `call` and the run from its return.
- `pstep`: one step of the closers of the pieces.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
open FV7z.Api (KS)
namespace FV7z.Pew
set_option linter.unusedVariables false

/-! ## The instructions outside the blocks -/

/-- The `call` of `fwrite` (59). -/
def pc59 : List Byte := [0xe8, 0x20, 0xb7, 0x03, 0x00]
theorem pc59_0 : ∀ feat, Dec feat pc59 0 (FV7z.mk .call 64 [.rel 243488] 5) := by dec_rfl
theorem wc_59 : pc59 <+: pew.drop 59 := by decide +kernel
theorem call_59 (feat : Features) : Dec feat pew 59 (FV7z.mk .call 64 [.rel 243488] 5) :=
  Dec.shift (j := 59) (k := 0) (pc59_0 feat) wc_59 (Nat.zero_le _)
theorem tgt_59 : pew_at.add (59 + 5) + BitVec.ofNat 64 243488 = 0x624e40#64 := by decide

/-- The `call` of `CStdOutStream::NormalizePrint_UString_Path` (74). -/
def pc74 : List Byte := [0xe8, 0xe1, 0x7f, 0xfb, 0xff]
theorem pc74_0 : ∀ feat, Dec feat pc74 0 (FV7z.mk .call 64 [.rel 18446744073709256673] 5) := by dec_rfl
theorem wc_74 : pc74 <+: pew.drop 74 := by decide +kernel
theorem call_74 (feat : Features) : Dec feat pew 74 (FV7z.mk .call 64 [.rel 18446744073709256673] 5) :=
  Dec.shift (j := 74) (k := 0) (pc74_0 feat) wc_74 (Nat.zero_le _)
theorem tgt_74 : pew_at.add (74 + 5) + BitVec.ofNat 64 18446744073709256673 = 0x5a1710#64 := by decide

/-- The `call` of `UString::UString ()` (82). -/
def pc82 : List Byte := [0xe8, 0xa9, 0x3c, 0xe6, 0xff]
theorem pc82_0 : ∀ feat, Dec feat pc82 0 (FV7z.mk .call 64 [.rel 18446744073707863209] 5) := by dec_rfl
theorem wc_82 : pc82 <+: pew.drop 82 := by decide +kernel
theorem call_82 (feat : Features) : Dec feat pew 82 (FV7z.mk .call 64 [.rel 18446744073707863209] 5) :=
  Dec.shift (j := 82) (k := 0) (pc82_0 feat) wc_82 (Nat.zero_le _)
theorem tgt_82 : pew_at.add (82 + 5) + BitVec.ofNat 64 18446744073707863209 = 0x44d3e0#64 := by decide

/-- The `call` of `Add_Messsage_Pre_ArcType` (136). -/
def pc136 : List Byte := [0xe8, 0xe3, 0xe2, 0xff, 0xff]
theorem pc136_0 : ∀ feat, Dec feat pc136 0 (FV7z.mk .call 64 [.rel 18446744073709544163] 5) := by dec_rfl
theorem wc_136 : pc136 <+: pew.drop 136 := by decide +kernel
theorem call_136 (feat : Features) : Dec feat pew 136 (FV7z.mk .call 64 [.rel 18446744073709544163] 5) :=
  Dec.shift (j := 136) (k := 0) (pc136_0 feat) wc_136 (Nat.zero_le _)
theorem tgt_136 : pew_at.add (136 + 5) + BitVec.ofNat 64 18446744073709544163 = 0x5e7a50#64 := by decide

/-- The `call` of `Add_Messsage_Pre_ArcType` (178). -/
def pc178 : List Byte := [0xe8, 0xb9, 0xe2, 0xff, 0xff]
theorem pc178_0 : ∀ feat, Dec feat pc178 0 (FV7z.mk .call 64 [.rel 18446744073709544121] 5) := by dec_rfl
theorem wc_178 : pc178 <+: pew.drop 178 := by decide +kernel
theorem call_178 (feat : Features) : Dec feat pew 178 (FV7z.mk .call 64 [.rel 18446744073709544121] 5) :=
  Dec.shift (j := 178) (k := 0) (pc178_0 feat) wc_178 (Nat.zero_le _)
theorem tgt_178 : pew_at.add (178 + 5) + BitVec.ofNat 64 18446744073709544121 = 0x5e7a50#64 := by decide

/-- The `call` of `CStdOutStream::operator<< (const wchar_t *)` (190). -/
def pc190 : List Byte := [0xe8, 0x8d, 0x7d, 0xfb, 0xff]
theorem pc190_0 : ∀ feat, Dec feat pc190 0 (FV7z.mk .call 64 [.rel 18446744073709256077] 5) := by dec_rfl
theorem wc_190 : pc190 <+: pew.drop 190 := by decide +kernel
theorem call_190 (feat : Features) : Dec feat pew 190 (FV7z.mk .call 64 [.rel 18446744073709256077] 5) :=
  Dec.shift (j := 190) (k := 0) (pc190_0 feat) wc_190 (Nat.zero_le _)
theorem tgt_190 : pew_at.add (190 + 5) + BitVec.ofNat 64 18446744073709256077 = 0x5a1530#64 := by decide

/-- The `call` of `endl` (201). -/
def pc201 : List Byte := [0xe8, 0xc2, 0x7c, 0xfb, 0xff]
theorem pc201_0 : ∀ feat, Dec feat pc201 0 (FV7z.mk .call 64 [.rel 18446744073709255874] 5) := by dec_rfl
theorem wc_201 : pc201 <+: pew.drop 201 := by decide +kernel
theorem call_201 (feat : Features) : Dec feat pew 201 (FV7z.mk .call 64 [.rel 18446744073709255874] 5) :=
  Dec.shift (j := 201) (k := 0) (pc201_0 feat) wc_201 (Nat.zero_le _)
theorem tgt_201 : pew_at.add (201 + 5) + BitVec.ofNat 64 18446744073709255874 = 0x5a1470#64 := by decide

/-- The `call` of `endl` (209). -/
def pc209 : List Byte := [0xe8, 0xba, 0x7c, 0xfb, 0xff]
theorem pc209_0 : ∀ feat, Dec feat pc209 0 (FV7z.mk .call 64 [.rel 18446744073709255866] 5) := by dec_rfl
theorem wc_209 : pc209 <+: pew.drop 209 := by decide +kernel
theorem call_209 (feat : Features) : Dec feat pew 209 (FV7z.mk .call 64 [.rel 18446744073709255866] 5) :=
  Dec.shift (j := 209) (k := 0) (pc209_0 feat) wc_209 (Nat.zero_le _)
theorem tgt_209 : pew_at.add (209 + 5) + BitVec.ofNat 64 18446744073709255866 = 0x5a1470#64 := by decide

/-- The `call` of `delete []` (223). -/
def pc223 : List Byte := [0xe8, 0x2c, 0x7d, 0x01, 0x00]
theorem pc223_0 : ∀ feat, Dec feat pc223 0 (FV7z.mk .call 64 [.rel 97580] 5) := by dec_rfl
theorem wc_223 : pc223 <+: pew.drop 223 := by decide +kernel
theorem call_223 (feat : Features) : Dec feat pew 223 (FV7z.mk .call 64 [.rel 97580] 5) :=
  Dec.shift (j := 223) (k := 0) (pc223_0 feat) wc_223 (Nat.zero_le _)
theorem tgt_223 : pew_at.add (223 + 5) + BitVec.ofNat 64 97580 = 0x6014f0#64 := by decide

/-- The `call` of `UString::Add_LF` (259). -/
def pc259 : List Byte := [0xe8, 0xc8, 0x42, 0xe6, 0xff]
theorem pc259_0 : ∀ feat, Dec feat pc259 0 (FV7z.mk .call 64 [.rel 18446744073707864776] 5) := by dec_rfl
theorem wc_259 : pc259 <+: pew.drop 259 := by decide +kernel
theorem call_259 (feat : Features) : Dec feat pew 259 (FV7z.mk .call 64 [.rel 18446744073707864776] 5) :=
  Dec.shift (j := 259) (k := 0) (pc259_0 feat) wc_259 (Nat.zero_le _)
theorem tgt_259 : pew_at.add (259 + 5) + BitVec.ofNat 64 18446744073707864776 = 0x44dab0#64 := by decide

/-- The `call` of `UString::operator+= (const char *)` (274). -/
def pc274 : List Byte := [0xe8, 0xe9, 0x43, 0xe6, 0xff]
theorem pc274_0 : ∀ feat, Dec feat pc274 0 (FV7z.mk .call 64 [.rel 18446744073707865065] 5) := by dec_rfl
theorem wc_274 : pc274 <+: pew.drop 274 := by decide +kernel
theorem call_274 (feat : Features) : Dec feat pew 274 (FV7z.mk .call 64 [.rel 18446744073707865065] 5) :=
  Dec.shift (j := 274) (k := 0) (pc274_0 feat) wc_274 (Nat.zero_le _)
theorem tgt_274 : pew_at.add (274 + 5) + BitVec.ofNat 64 18446744073707865065 = 0x44dbe0#64 := by decide

/-- The `ret` (254). -/
def pret : List Byte := [0xc3]
theorem pret_0 : ∀ feat, Dec feat pret 0 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem w_254 : pret <+: pew.drop 254 := by decide +kernel
theorem ret_254 (feat : Features) : Dec feat pew 254 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 254) (k := 0) (pret_0 feat) w_254 (Nat.zero_le _)

/-- `movsxd` then a 32-bit use: the value read. -/
theorem sw_sx (x : BitVec 32) : (x.signExtend 64).setWidth 32 = x := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_setWidth, BitVec.getLsbD_signExtend]
  simp [hi, show i < 64 by omega]

/-! ## The frame -/

/-- The stack pointer after the four pushes and `sub rsp, 0x28`. -/
abbrev aR (S : Addr) : Addr := S - 8 - 8 - 8 - 8 - 40#64

/-- The bytes after the four pushes (`r13`, `r12`, `rbp`, `rbx`). -/
abbrev P4 (V : Addr → Byte) (g : Gprs) : Addr → Byte :=
  Vst (Vst (Vst (Vst V (g.rsp - 8) (toBytesLE g.r13 8)) (g.rsp - 8 - 8) (toBytesLE g.r12 8))
    (g.rsp - 8 - 8 - 8) (toBytesLE g.rbp 8)) (g.rsp - 8 - 8 - 8 - 8) (toBytesLE g.rbx 8)

/-- The bytes after the prologue: the pushes, the stack guard stored. -/
abbrev V0 (fb : Addr) (V : Addr → Byte) (g : Gprs) : Addr → Byte :=
  Vst (P4 V g) (aR g.rsp + 24#64) (toBytesLE rdq(P4 V g, fb + 40#64) 8)

theorem q1 (S : Addr) : aR S + 40#64 = S - 8 - 8 - 8 - 8 := BitVec.sub_add_cancel _ _
theorem q2 (S : Addr) : aR S + 40#64 + 8 = S - 8 - 8 - 8 := by rw [q1, BitVec.sub_add_cancel]
theorem q3 (S : Addr) : aR S + 40#64 + 8 + 8 = S - 8 - 8 := by rw [q2, BitVec.sub_add_cancel]
theorem q4 (S : Addr) : aR S + 40#64 + 8 + 8 + 8 = S - 8 := by rw [q3, BitVec.sub_add_cancel]
theorem q5 (S : Addr) : aR S + 40#64 + 8 + 8 + 8 + 8 = S := by rw [q4, BitVec.sub_add_cancel]

/-- The frame from the prologue on: `rsp` = `aR S`, `rbx` = `arc`, `r13` = `codecs`, `r14`, `r15` as at the entry. -/
abbrev Fm (S : Addr) (g0 g : Gprs) : Prop :=
  g.rsp = aR S ∧ g.rbx = g0.rdx ∧ g.r13 = g0.rsi ∧ g.r14 = g0.r14 ∧ g.r15 = g0.r15

/-- What a piece keeps: `rsp`, `rbx`, `r13`..`r15`. -/
abbrev Fr (g g' : Gprs) : Prop :=
  g'.rsp = g.rsp ∧ g'.rbx = g.rbx ∧ g'.r13 = g.r13 ∧ g'.r14 = g.r14 ∧ g'.r15 = g.r15

theorem Fm.fr {S : Addr} {g0 g g' : Gprs} (h : Fm S g0 g) (h' : Fr g g') : Fm S g0 g' :=
  ⟨h'.1.trans h.1, h'.2.1.trans h.2.1, h'.2.2.1.trans h.2.2.1, h'.2.2.2.1.trans h.2.2.2.1,
    h'.2.2.2.2.trans h.2.2.2.2⟩

/-- Back from a callee: `rsp` as before the `call`, the callee-saved registers kept. -/
theorem fm_ret {S : Addr} {g0 g g' : Gprs} (h : Fm S g0 g) (hs : g'.rsp = aR S) (hk : KS g g') : Fm S g0 g' :=
  ⟨hs, hk.1.trans h.2.1, hk.2.2.2.1.trans h.2.2.1, hk.2.2.2.2.1.trans h.2.2.2.1, hk.2.2.2.2.2.trans h.2.2.2.2⟩

/-- The stack (`fb` the `fs` base, `ra` the return address): the four saved registers, the return address, the
stack guard as at `fs:0x28`. -/
abbrev Stk (fb : Addr) (W : Addr → Byte) (S : Addr) (g0 : Gprs) (ra : Addr) : Prop :=
  rdq(W, S - 8 - 8 - 8 - 8) = g0.rbx ∧ rdq(W, S - 8 - 8 - 8) = g0.rbp ∧ rdq(W, S - 8 - 8) = g0.r12 ∧
    rdq(W, S - 8) = g0.r13 ∧ rdq(W, S) = ra ∧ rdq(W, aR S + 24#64) = rdq(W, fb + 40#64)

/-- A callee from the `call` before `j` (entry `ent`, the bytes `W`, the registers `A`): at its entry, and from its
return at `j` with `rsp` = `aR S`, the callee-saved registers as at its entry, `B` and the invariant `J`, the run
goes on to the goal. -/
def KC (prof : Profile) (F : Footprint) (Wl : List Rgn) (L : List (Addr × List Byte)) (s₀ : State) (o : Oracle)
    (gev : List Event) (gP : State → Nat → List Event → Prop) (gE : Outcome → List Event → Prop)
    (S : Addr) (J : (Addr → Byte) → Prop) (ent : Addr) (j : Nat) (W : Addr → Byte) (A B : Gprs → Prop) : Prop :=
  ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y →
    Agree F Y.proc.mm.mem (Vst W (aR S - 8) (toBytesLE (pew_at.add j) 8)) →
    Y.cpu.rip = ent → Y.cpu.gpr.rsp = aR S - 8 → A Y.cpu.gpr →
    (∀ (Z : State) (W' : Addr → Byte) (t'' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem W' →
      Z.cpu.rip = pew_at.add j → Z.cpu.gpr.rsp = aR S → KS Y.cpu.gpr Z.cpu.gpr → B Z.cpu.gpr → J W' →
      GoG prof L o gev gP gE Z t'') →
    GoG prof L o gev gP gE Y t'

/-! ## The hypotheses of the runs -/

/-- The hypotheses of the runs from the cut points (`fb` the `fs` base, `S`, `g0` the entry's stack pointer and
registers, `e₂.add j₂` the return address, `I` the invariant of the bytes). The stack (`hcl`..`hr8`); `_so->_stream`
(`hso`), the two format indices of `arc` (`f88`, `f164`) and `codecs->Formats` (`f16`) may be read, and for an index
not negative in bytes `W` with `I W`, the item of `Formats` and its name (`fe`); the callees keep `I`, from any
return offset. -/
structure Ev (prof : Profile) (F : Footprint) (Wl : List Rgn) (L : List (Addr × List Byte)) (s₀ : State)
    (o : Oracle) (gev : List Event) (gP : State → Nat → List Event → Prop) (gE : Outcome → List Event → Prop)
    (fb S : Addr) (g0 : Gprs) (e₂ : Addr) (code₂ : List Byte) (j₂ : Nat) (I : (Addr → Byte) → Prop) :
    Prop where
  c : Seg prof F Wl L s₀ o
  hfs : s₀.cpu.seg.fsBase = fb
  hin : CodeIn L pew_at pew
  hin₂ : CodeIn L e₂ code₂
  h₂ : j₂ < code₂.length
  hI : ∀ W, I W → Stk fb W S g0 (e₂.add j₂)
  hcl : ∀ i < 8, Foot F.data (Addr.add (fb + 40#64) i)
  fg : ∀ i < 8, Foot F.data (Addr.add (aR S + 24#64) i)
  fl0 : ∀ i < 8, Foot F.data (Addr.add (aR S) i)
  fb32 : ∀ i < 8, Foot F.data (Addr.add (S - 8 - 8 - 8 - 8) i)
  fb24 : ∀ i < 8, Foot F.data (Addr.add (S - 8 - 8 - 8) i)
  fb16 : ∀ i < 8, Foot F.data (Addr.add (S - 8 - 8) i)
  fb8 : ∀ i < 8, Foot F.data (Addr.add (S - 8) i)
  hl : ∀ i < 8, Foot F.data (Addr.add S i)
  hr8 : ∀ i < 8, Foot Wl (Addr.add (aR S - 8) i)
  hso : ∀ i < 8, Foot F.data (Addr.add g0.rdi i)
  f88 : ∀ i < 4, Foot F.data (Addr.add (g0.rdx + 88#64) i)
  f164 : ∀ i < 4, Foot F.data (Addr.add (g0.rdx + 164#64) i)
  f16 : ∀ i < 8, Foot F.data (Addr.add (g0.rsi + 16#64) i)
  fe : ∀ W, I W → ∀ d : Addr, d = 88#64 ∨ d = 164#64 → (rdd(W, g0.rdx + d)).msb = false →
    (∀ i < 8, Foot F.data (Addr.add (rdq(W, g0.rsi + 16#64) + (rdd(W, g0.rdx + d)).signExtend 64 * 8#64) i)) ∧
    ∀ i < 8, Foot F.data
      (Addr.add (rdq(W, rdq(W, g0.rsi + 16#64) + (rdd(W, g0.rdx + d)).signExtend 64 * 8#64) + 24#64) i)
  cW : ∃ code : List Byte, CodeIn L 0x624e40#64 code ∧ 0 < code.length
  cU : ∃ code : List Byte, CodeIn L 0x5a1710#64 code ∧ 0 < code.length
  cA : ∃ code : List Byte, CodeIn L 0x44d3e0#64 code ∧ 0 < code.length
  cN : ∃ code : List Byte, CodeIn L 0x5e7a50#64 code ∧ 0 < code.length
  cO : ∃ code : List Byte, CodeIn L 0x5a1530#64 code ∧ 0 < code.length
  cE : ∃ code : List Byte, CodeIn L 0x5a1470#64 code ∧ 0 < code.length
  cD : ∃ code : List Byte, CodeIn L 0x6014f0#64 code ∧ 0 < code.length
  cB : ∃ code : List Byte, CodeIn L 0x44dab0#64 code ∧ 0 < code.length
  cP : ∃ code : List Byte, CodeIn L 0x44dbe0#64 code ∧ 0 < code.length
  kW : ∀ j W, I W → KC prof F Wl L s₀ o gev gP gE S I 0x624e40#64 j W (fun _ => True) (fun _ => True)
  kU : ∀ j W, I W → KC prof F Wl L s₀ o gev gP gE S I 0x5a1710#64 j W (fun _ => True) (fun _ => True)
  kA : ∀ j W, I W → KC prof F Wl L s₀ o gev gP gE S I 0x44d3e0#64 j W (fun _ => True) (fun _ => True)
  kN : ∀ j W, I W → KC prof F Wl L s₀ o gev gP gE S I 0x5e7a50#64 j W (fun _ => True) (fun _ => True)
  kO : ∀ j W, I W → KC prof F Wl L s₀ o gev gP gE S I 0x5a1530#64 j W (fun _ => True) (fun _ => True)
  kE : ∀ j W, I W → KC prof F Wl L s₀ o gev gP gE S I 0x5a1470#64 j W (fun _ => True) (fun _ => True)
  kD : ∀ j W, I W → KC prof F Wl L s₀ o gev gP gE S I 0x6014f0#64 j W (fun _ => True) (fun _ => True)
  kB : ∀ j W, I W → KC prof F Wl L s₀ o gev gP gE S I 0x44dab0#64 j W (fun _ => True) (fun _ => True)
  kP : ∀ j W, I W → KC prof F Wl L s₀ o gev gP gE S I 0x44dbe0#64 j W (fun _ => True) (fun _ => True)
  kr : ∀ (W : Addr → Byte) (Z' : State) (t' : Nat), KeptW Wl s₀ Z' → Agree F Z'.proc.mm.mem W →
    Z'.cpu.rip = e₂.add j₂ → Z'.cpu.gpr.rsp = S + 8 → KS g0 Z'.cpu.gpr → I W → GoG prof L o gev gP gE Z' t'

section Runs
variable {prof : Profile} {F : Footprint} {Wl : List Rgn} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {fb S : Addr} {g0 : Gprs} {e₂ : Addr} {code₂ : List Byte} {j₂ : Nat} {I : (Addr → Byte) → Prop}
  {W : Addr → Byte}

/-- A `call` at `j` (`rsp` = `aR S`, the bytes `W`) of the callee `k`, and from its return at `j + 5`. -/
theorem callK (E : Ev prof F Wl L s₀ o gev gP gE fb S g0 e₂ code₂ j₂ I)
    {J : (Addr → Byte) → Prop} {U : State} {t₁ : Nat} {j R : Nat} {ent : Addr} {A B : Gprs → Prop}
    (hKU : KeptW Wl s₀ U) (hAU : Agree F U.proc.mm.mem W) (hrU : U.cpu.rip = pew_at.add j)
    (hs : U.cpu.gpr.rsp = aR S) (hj : j < pew.length) (hd : Dec prof.feat pew j (FV7z.mk .call 64 [.rel R] 5))
    (htgt : pew_at.add (j + 5) + BitVec.ofNat 64 R = ent)
    (hc : ∃ code : List Byte, CodeIn L ent code ∧ 0 < code.length)
    (k : KC prof F Wl L s₀ o gev gP gE S J ent (j + 5) W A B) (hA : A (U.cpu.gpr.set 4 (aR S - 8)))
    (h : ∀ (Z : State) (W' : Addr → Byte) (t'' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem W' →
      Z.cpu.rip = pew_at.add (j + 5) → Z.cpu.gpr.rsp = aR S → KS U.cpu.gpr Z.cpu.gpr → B Z.cpu.gpr → J W' →
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
macro "pstep" : tactic => `(tactic| first
  | with_reducible rfl
  | with_reducible assumption
  | exact rfl
  | apply And.intro
  | intro _)

end FV7z.Pew
