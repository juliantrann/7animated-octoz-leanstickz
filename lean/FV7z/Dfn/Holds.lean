import FV7z.Dfn.Cuts
import FV7z.Lemmas.LeafRet
/-!
# `GetDefaultName2` (PLAN.md §M, M1): the run through the callees

7-Zip 26.06's `GetDefaultName3 (name, ext, addSubExtension)` (as `GetDefaultName2`,
`CPP/7zip/UI/Common/DefaultName.cpp`; `objdump -d`) at `0x5bfdd0` in `7zzs`, `UString`s of 4-byte characters (`_chars` at `+ 0`, `_len` at `+ 8`): the result
`UString` at `rdi` (`r12`), `name` = `rsi` (`rbp`), `ext` = `rdx`, `addSubExtension` = `rcx` (`r13`). `S` the stack
pointer and `g0` the registers at the entry: `push r15, r14, r13, r12, rbp; sub rsp, 0x20`, the stack guard
(`fs:0x28`) at `aR S + 24`, a local `UString` at `aR S`. If `name._len` is above `ext._len` and the character before
the last `ext._len` ones is '.' (55..76: `cmp dword [rcx + rsi*4], '.'`), `rdi` = `ext._chars`, `rsi` = the tail of
`name` and the `call` (247) at `0x44ba80` (the comparison); if it says equal (252), `Left` (272, `0x44d240`) into the
local and `res = local + addSubExtension` (286, `0x44d330`), then the local's buffer freed (220..234: `delete[]` at
229, `0x6014f0`, unless null), to 118. Else (77) `ReverseFind_Dot` (85, `0x44dd40`): a dot (above 0, 192) `Left`
(201) into the local, `res = local + addSubExtension` (215), to 220; else an empty `addSubExtension` (168) gives
`res = name + '~'` (179, `0x44d280`), else `res = name + addSubExtension` (113). At 118 `res.Replace…` (121,
`0x44de20`, `rdi` = `res`), the guard's check, the epilogue, `ret` (162) with `rax` = `res`. Not covered:
`__stack_chk_fail` (293), the landing pads.

The callees are continuations (`KC`, as in `FV7z/Lza/Run.lean`): each is given its arguments and the bytes, and from
its return the run goes on with `rsp` as it was and the callee-saved registers (`KS`) as at the `call`. The bytes are
tracked by an invariant `I` the caller chooses: the bytes after the prologue have it (`hI0`), every callee returns
with it, and it gives the saved registers, the return address and the stack guard (`Stk`).

- `Fm`, `Fr`, `KS`, `Stk`, `KC`, `Ev`: the frame, what a piece keeps, the callee-saved registers, the stack, the
  callees, the hypotheses of the runs; `callK`: a `call` and the callee's return.
- `vc_*`: the pieces; `tail126`, `from118`, `from220`, `from206`, `from277`, `from184`, `from90`, `from77`,
  `from252`: the runs from the cut points.
- `dfn_ok`: from the entry to the return address.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Dfn
set_option linter.unusedVariables false

/-! ## The instructions outside the blocks -/

/-- The `call` of `ReverseFind_Dot`. -/
def pc85 : List Byte := [0xe8, 0x16, 0xdf, 0xe8, 0xff]
theorem pc85_0 : ∀ feat, Dec feat pc85 0 (FV7z.mk .call 64 [.rel 18446744073708035862] 5) := by dec_rfl
theorem wc_85 : pc85 <+: dfn.drop 85 := by decide +kernel
theorem call_85 (feat : Features) : Dec feat dfn 85 (FV7z.mk .call 64 [.rel 18446744073708035862] 5) :=
  Dec.shift (j := 85) (k := 0) (pc85_0 feat) wc_85 (Nat.zero_le _)
theorem tgt_85 : dfn_at.add (85 + 5) + BitVec.ofNat 64 18446744073708035862 = 0x44dd40#64 := by decide

/-- The `call` of the concatenation (113). -/
def pc113 : List Byte := [0xe8, 0xea, 0xd4, 0xe8, 0xff]
theorem pc113_0 : ∀ feat, Dec feat pc113 0 (FV7z.mk .call 64 [.rel 18446744073708033258] 5) := by dec_rfl
theorem wc_113 : pc113 <+: dfn.drop 113 := by decide +kernel
theorem call_113 (feat : Features) : Dec feat dfn 113 (FV7z.mk .call 64 [.rel 18446744073708033258] 5) :=
  Dec.shift (j := 113) (k := 0) (pc113_0 feat) wc_113 (Nat.zero_le _)
theorem tgt_113 : dfn_at.add (113 + 5) + BitVec.ofNat 64 18446744073708033258 = 0x44d330#64 := by decide

/-- The `call` at 121. -/
def pc121 : List Byte := [0xe8, 0xd2, 0xdf, 0xe8, 0xff]
theorem pc121_0 : ∀ feat, Dec feat pc121 0 (FV7z.mk .call 64 [.rel 18446744073708036050] 5) := by dec_rfl
theorem wc_121 : pc121 <+: dfn.drop 121 := by decide +kernel
theorem call_121 (feat : Features) : Dec feat dfn 121 (FV7z.mk .call 64 [.rel 18446744073708036050] 5) :=
  Dec.shift (j := 121) (k := 0) (pc121_0 feat) wc_121 (Nat.zero_le _)
theorem tgt_121 : dfn_at.add (121 + 5) + BitVec.ofNat 64 18446744073708036050 = 0x44de20#64 := by decide

/-- The `call` of `name + '~'` (179). -/
def pc179 : List Byte := [0xe8, 0xf8, 0xd3, 0xe8, 0xff]
theorem pc179_0 : ∀ feat, Dec feat pc179 0 (FV7z.mk .call 64 [.rel 18446744073708033016] 5) := by dec_rfl
theorem wc_179 : pc179 <+: dfn.drop 179 := by decide +kernel
theorem call_179 (feat : Features) : Dec feat dfn 179 (FV7z.mk .call 64 [.rel 18446744073708033016] 5) :=
  Dec.shift (j := 179) (k := 0) (pc179_0 feat) wc_179 (Nat.zero_le _)
theorem tgt_179 : dfn_at.add (179 + 5) + BitVec.ofNat 64 18446744073708033016 = 0x44d280#64 := by decide

/-- The `call` of `Left` (201). -/
def pc201 : List Byte := [0xe8, 0xa2, 0xd3, 0xe8, 0xff]
theorem pc201_0 : ∀ feat, Dec feat pc201 0 (FV7z.mk .call 64 [.rel 18446744073708032930] 5) := by dec_rfl
theorem wc_201 : pc201 <+: dfn.drop 201 := by decide +kernel
theorem call_201 (feat : Features) : Dec feat dfn 201 (FV7z.mk .call 64 [.rel 18446744073708032930] 5) :=
  Dec.shift (j := 201) (k := 0) (pc201_0 feat) wc_201 (Nat.zero_le _)
theorem tgt_201 : dfn_at.add (201 + 5) + BitVec.ofNat 64 18446744073708032930 = 0x44d240#64 := by decide

/-- The `call` of the concatenation (215). -/
def pc215 : List Byte := [0xe8, 0x84, 0xd4, 0xe8, 0xff]
theorem pc215_0 : ∀ feat, Dec feat pc215 0 (FV7z.mk .call 64 [.rel 18446744073708033156] 5) := by dec_rfl
theorem wc_215 : pc215 <+: dfn.drop 215 := by decide +kernel
theorem call_215 (feat : Features) : Dec feat dfn 215 (FV7z.mk .call 64 [.rel 18446744073708033156] 5) :=
  Dec.shift (j := 215) (k := 0) (pc215_0 feat) wc_215 (Nat.zero_le _)
theorem tgt_215 : dfn_at.add (215 + 5) + BitVec.ofNat 64 18446744073708033156 = 0x44d330#64 := by decide

/-- The `call` of `delete[]` (229). -/
def pc229 : List Byte := [0xe8, 0x36, 0x16, 0x04, 0x00]
theorem pc229_0 : ∀ feat, Dec feat pc229 0 (FV7z.mk .call 64 [.rel 267830] 5) := by dec_rfl
theorem wc_229 : pc229 <+: dfn.drop 229 := by decide +kernel
theorem call_229 (feat : Features) : Dec feat dfn 229 (FV7z.mk .call 64 [.rel 267830] 5) :=
  Dec.shift (j := 229) (k := 0) (pc229_0 feat) wc_229 (Nat.zero_le _)
theorem tgt_229 : dfn_at.add (229 + 5) + BitVec.ofNat 64 267830 = 0x6014f0#64 := by decide

/-- The `call` of the comparison (247). -/
def pc247 : List Byte := [0xe8, 0xb4, 0xbb, 0xe8, 0xff]
theorem pc247_0 : ∀ feat, Dec feat pc247 0 (FV7z.mk .call 64 [.rel 18446744073708026804] 5) := by dec_rfl
theorem wc_247 : pc247 <+: dfn.drop 247 := by decide +kernel
theorem call_247 (feat : Features) : Dec feat dfn 247 (FV7z.mk .call 64 [.rel 18446744073708026804] 5) :=
  Dec.shift (j := 247) (k := 0) (pc247_0 feat) wc_247 (Nat.zero_le _)
theorem tgt_247 : dfn_at.add (247 + 5) + BitVec.ofNat 64 18446744073708026804 = 0x44ba80#64 := by decide

/-- The `call` of `Left` (272). -/
def pc272 : List Byte := [0xe8, 0x5b, 0xd3, 0xe8, 0xff]
theorem pc272_0 : ∀ feat, Dec feat pc272 0 (FV7z.mk .call 64 [.rel 18446744073708032859] 5) := by dec_rfl
theorem wc_272 : pc272 <+: dfn.drop 272 := by decide +kernel
theorem call_272 (feat : Features) : Dec feat dfn 272 (FV7z.mk .call 64 [.rel 18446744073708032859] 5) :=
  Dec.shift (j := 272) (k := 0) (pc272_0 feat) wc_272 (Nat.zero_le _)
theorem tgt_272 : dfn_at.add (272 + 5) + BitVec.ofNat 64 18446744073708032859 = 0x44d240#64 := by decide

/-- The `call` of the concatenation (286). -/
def pc286 : List Byte := [0xe8, 0x3d, 0xd4, 0xe8, 0xff]
theorem pc286_0 : ∀ feat, Dec feat pc286 0 (FV7z.mk .call 64 [.rel 18446744073708033085] 5) := by dec_rfl
theorem wc_286 : pc286 <+: dfn.drop 286 := by decide +kernel
theorem call_286 (feat : Features) : Dec feat dfn 286 (FV7z.mk .call 64 [.rel 18446744073708033085] 5) :=
  Dec.shift (j := 286) (k := 0) (pc286_0 feat) wc_286 (Nat.zero_le _)
theorem tgt_286 : dfn_at.add (286 + 5) + BitVec.ofNat 64 18446744073708033085 = 0x44d330#64 := by decide

/-- The `ret`. -/
def pret : List Byte := [0xc3]
theorem pret_0 : ∀ feat, Dec feat pret 0 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem wt_162 : pret <+: dfn.drop 162 := by decide +kernel
theorem ret_162 (feat : Features) : Dec feat dfn 162 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 162) (k := 0) (pret_0 feat) wt_162 (Nat.zero_le _)

/-! ## The frame -/

/-- The stack pointer after the five pushes and `sub rsp, 0x20`; the local `UString` there. -/
abbrev aR (S : Addr) : Addr := S - 8 - 8 - 8 - 8 - 8 - 32#64

/-- The bytes after the five pushes (`r15`, `r14`, `r13`, `r12`, `rbp`). -/
abbrev P5 (V : Addr → Byte) (g : Gprs) : Addr → Byte :=
  Vst (Vst (Vst (Vst (Vst V (g.rsp - 8) (toBytesLE g.r15 8)) (g.rsp - 8 - 8) (toBytesLE g.r14 8))
    (g.rsp - 8 - 8 - 8) (toBytesLE g.r13 8)) (g.rsp - 8 - 8 - 8 - 8) (toBytesLE g.r12 8))
    (g.rsp - 8 - 8 - 8 - 8 - 8) (toBytesLE g.rbp 8)

/-- The bytes after the prologue: the pushes, the stack guard stored. -/
abbrev V0 (fb : Addr) (V : Addr → Byte) (g : Gprs) : Addr → Byte :=
  Vst (P5 V g) (aR g.rsp + 24#64) (toBytesLE rdq(P5 V g, fb + 40#64) 8)

/-- The character the code at 55 compares with '.': `name._chars[name._len - ext._len - 1]` (32-bit index). -/
abbrev cmA (fb : Addr) (V : Addr → Byte) (g : Gprs) : Addr :=
  rdq(V0 fb V g, g.rsi) + BitVec.setWidth 64 (BitVec.setWidth 32
    (BitVec.setWidth 64 (rdd(V0 fb V g, g.rsi + 8#64) - rdd(P5 V g, g.rdx + 8#64)) + 18446744073709551615#64)) * 4#64

theorem q1 (S : Addr) : aR S + 32#64 = S - 8 - 8 - 8 - 8 - 8 := by
  show S - 8 - 8 - 8 - 8 - 8 - 32#64 + 32#64 = _; bv_omega
theorem q2 (S : Addr) : aR S + 32#64 + 8 = S - 8 - 8 - 8 - 8 := by
  show S - 8 - 8 - 8 - 8 - 8 - 32#64 + 32#64 + 8 = _; bv_omega
theorem q3 (S : Addr) : aR S + 32#64 + 8 + 8 = S - 8 - 8 - 8 := by
  show S - 8 - 8 - 8 - 8 - 8 - 32#64 + 32#64 + 8 + 8 = _; bv_omega
theorem q4 (S : Addr) : aR S + 32#64 + 8 + 8 + 8 = S - 8 - 8 := by
  show S - 8 - 8 - 8 - 8 - 8 - 32#64 + 32#64 + 8 + 8 + 8 = _; bv_omega
theorem q5 (S : Addr) : aR S + 32#64 + 8 + 8 + 8 + 8 = S - 8 := by
  show S - 8 - 8 - 8 - 8 - 8 - 32#64 + 32#64 + 8 + 8 + 8 + 8 = _; bv_omega
theorem q6 (S : Addr) : aR S + 32#64 + 8 + 8 + 8 + 8 + 8 = S := by
  show S - 8 - 8 - 8 - 8 - 8 - 32#64 + 32#64 + 8 + 8 + 8 + 8 + 8 = _; bv_omega

/-- The frame from the prologue on: `rsp` = `aR S`, `rbx` as at the entry, `rbp` = `name`, `r12` = the result,
`r13` = `addSubExtension`. -/
abbrev Fm (S : Addr) (g0 g : Gprs) : Prop :=
  g.rsp = aR S ∧ g.rbx = g0.rbx ∧ g.rbp = g0.rsi ∧ g.r12 = g0.rdi ∧ g.r13 = g0.rcx

/-- What a piece keeps: `rsp`, `rbx`, `rbp`, `r12`, `r13`. -/
abbrev Fr (g g' : Gprs) : Prop :=
  g'.rsp = g.rsp ∧ g'.rbx = g.rbx ∧ g'.rbp = g.rbp ∧ g'.r12 = g.r12 ∧ g'.r13 = g.r13

/-- The callee-saved registers as in `g`. -/
abbrev KS (g g' : Gprs) : Prop :=
  g'.rbx = g.rbx ∧ g'.rbp = g.rbp ∧ g'.r12 = g.r12 ∧ g'.r13 = g.r13 ∧ g'.r14 = g.r14 ∧ g'.r15 = g.r15

theorem Fm.fr {S : Addr} {g0 g g' : Gprs} (h : Fm S g0 g) (h' : Fr g g') : Fm S g0 g' :=
  ⟨h'.1.trans h.1, h'.2.1.trans h.2.1, h'.2.2.1.trans h.2.2.1, h'.2.2.2.1.trans h.2.2.2.1,
    h'.2.2.2.2.trans h.2.2.2.2⟩

/-- Back from a callee: `rsp` as before the `call`, the callee-saved registers kept. -/
theorem fm_ret {S : Addr} {g0 g g' : Gprs} (h : Fm S g0 g) (hs : g'.rsp = aR S) (hk : KS g g') : Fm S g0 g' :=
  ⟨hs, hk.1.trans h.2.1, hk.2.1.trans h.2.2.1, hk.2.2.1.trans h.2.2.2.1, hk.2.2.2.1.trans h.2.2.2.2⟩

/-- The stack (`fb` the `fs` base, `ra` the return address): the five saved registers, the return address, the stack
guard as at `fs:0x28`. -/
abbrev Stk (fb : Addr) (W : Addr → Byte) (S : Addr) (g0 : Gprs) (ra : Addr) : Prop :=
  rdq(W, S - 8 - 8 - 8 - 8 - 8) = g0.rbp ∧ rdq(W, S - 8 - 8 - 8 - 8) = g0.r12 ∧ rdq(W, S - 8 - 8 - 8) = g0.r13 ∧
    rdq(W, S - 8 - 8) = g0.r14 ∧ rdq(W, S - 8) = g0.r15 ∧ rdq(W, S) = ra ∧
    rdq(W, aR S + 24#64) = rdq(W, fb + 40#64)

/-- A callee from the `call` before `j` (entry `ent`, the bytes `W`, the registers `A`): at its entry, and from its
return at `j` with `rsp` = `aR S`, the callee-saved registers as at its entry and the invariant `I`, the run goes on
to the goal. -/
def KC (prof : Profile) (F : Footprint) (Wl : List Rgn) (L : List (Addr × List Byte)) (s₀ : State) (o : Oracle)
    (gev : List Event) (gP : State → Nat → List Event → Prop) (gE : Outcome → List Event → Prop)
    (S : Addr) (I : (Addr → Byte) → Prop) (ent : Addr) (j : Nat) (W : Addr → Byte) (A : Gprs → Prop) : Prop :=
  ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y →
    Agree F Y.proc.mm.mem (Vst W (aR S - 8) (toBytesLE (dfn_at.add j) 8)) →
    Y.cpu.rip = ent → Y.cpu.gpr.rsp = aR S - 8 → A Y.cpu.gpr →
    (∀ (Z : State) (W' : Addr → Byte) (t'' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem W' →
      Z.cpu.rip = dfn_at.add j → Z.cpu.gpr.rsp = aR S → KS Y.cpu.gpr Z.cpu.gpr → I W' →
      GoG prof L o gev gP gE Z t'') →
    GoG prof L o gev gP gE Y t'

/-- The hypotheses of the runs from the cut points (`S`, `g0` the entry's stack pointer and registers, `e₂.add j₂`
the return address, `I` the invariant of the bytes). -/
structure Ev (prof : Profile) (F : Footprint) (Wl : List Rgn) (L : List (Addr × List Byte)) (s₀ : State)
    (o : Oracle) (gev : List Event) (gP : State → Nat → List Event → Prop) (gE : Outcome → List Event → Prop)
    (fb S : Addr) (g0 : Gprs) (e₂ : Addr) (code₂ : List Byte) (j₂ : Nat) (I : (Addr → Byte) → Prop) : Prop where
  c : Seg prof F Wl L s₀ o
  hfs : s₀.cpu.seg.fsBase = fb
  hin : CodeIn L dfn_at dfn
  hin₂ : CodeIn L e₂ code₂
  h₂ : j₂ < code₂.length
  hI : ∀ W, I W → Stk fb W S g0 (e₂.add j₂)
  hcl : ∀ i < 8, Foot F.data (Addr.add (fb + 40#64) i)
  fg : ∀ i < 8, Foot F.data (Addr.add (aR S + 24#64) i)
  f0 : ∀ i < 8, Foot F.data (Addr.add (aR S) i)
  fb40 : ∀ i < 8, Foot F.data (Addr.add (S - 8 - 8 - 8 - 8 - 8) i)
  fb32 : ∀ i < 8, Foot F.data (Addr.add (S - 8 - 8 - 8 - 8) i)
  fb24 : ∀ i < 8, Foot F.data (Addr.add (S - 8 - 8 - 8) i)
  fb16 : ∀ i < 8, Foot F.data (Addr.add (S - 8 - 8) i)
  fb8 : ∀ i < 8, Foot F.data (Addr.add (S - 8) i)
  hl : ∀ i < 8, Foot F.data (Addr.add S i)
  hr8 : ∀ i < 8, Foot Wl (Addr.add (aR S - 8) i)
  fx8 : ∀ i < 4, Foot F.data (Addr.add (g0.rcx + 8#64) i)
  cR : ∃ code : List Byte, CodeIn L 0x44dd40#64 code ∧ 0 < code.length
  cS : ∃ code : List Byte, CodeIn L 0x44d330#64 code ∧ 0 < code.length
  cN : ∃ code : List Byte, CodeIn L 0x44de20#64 code ∧ 0 < code.length
  cT : ∃ code : List Byte, CodeIn L 0x44d280#64 code ∧ 0 < code.length
  cL : ∃ code : List Byte, CodeIn L 0x44d240#64 code ∧ 0 < code.length
  cD : ∃ code : List Byte, CodeIn L 0x6014f0#64 code ∧ 0 < code.length
  k85 : ∀ W, I W → KC prof F Wl L s₀ o gev gP gE S I 0x44dd40#64 90 W (fun g => g.rdi = g0.rsi)
  k113 : ∀ W, I W → KC prof F Wl L s₀ o gev gP gE S I 0x44d330#64 118 W
    (fun g => g.rdi = g0.rdi ∧ g.rsi = g0.rsi ∧ g.rdx = g0.rcx)
  k121 : ∀ W, I W → KC prof F Wl L s₀ o gev gP gE S I 0x44de20#64 126 W (fun g => g.rdi = g0.rdi)
  k179 : ∀ W, I W → KC prof F Wl L s₀ o gev gP gE S I 0x44d280#64 184 W
    (fun g => g.rdi = g0.rdi ∧ g.rsi = g0.rsi)
  k201 : ∀ W, I W → KC prof F Wl L s₀ o gev gP gE S I 0x44d240#64 206 W
    (fun g => g.rdi = aR S ∧ g.rdx = g0.rsi)
  k215 : ∀ W, I W → KC prof F Wl L s₀ o gev gP gE S I 0x44d330#64 220 W
    (fun g => g.rdi = g0.rdi ∧ g.rsi = aR S ∧ g.rdx = g0.rcx)
  k229 : ∀ W, I W → KC prof F Wl L s₀ o gev gP gE S I 0x6014f0#64 234 W (fun g => g.rdi = rdq(W, aR S))
  k272 : ∀ W, I W → KC prof F Wl L s₀ o gev gP gE S I 0x44d240#64 277 W
    (fun g => g.rdi = aR S ∧ g.rdx = g0.rsi)
  k286 : ∀ W, I W → KC prof F Wl L s₀ o gev gP gE S I 0x44d330#64 291 W
    (fun g => g.rdi = g0.rdi ∧ g.rsi = aR S ∧ g.rdx = g0.rcx)
  kr : ∀ (W : Addr → Byte) (Z' : State) (t' : Nat), KeptW Wl s₀ Z' → Agree F Z'.proc.mm.mem W →
    Z'.cpu.rip = e₂.add j₂ → Z'.cpu.gpr.rsp = S + 8 → KS g0 Z'.cpu.gpr → Z'.cpu.gpr.rax = g0.rdi → I W →
    GoG prof L o gev gP gE Z' t'

/-! ## The pieces -/

section Pieces
variable {F : Footprint} {Wl : List Rgn}

/-- The prologue: the pushes, `r13` = `addSubExtension`, `r12` = the result, `rbp` = `name`, the frame, the stack
guard stored, `ecx` = `ext._len`, `eax` = `name._len`: to 77, or to 55. The guard's value is named (`cn`). -/
theorem vc_0 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} {cn : BitVec 64}
    (hcn : rdq(P5 V g, fb + 40#64) = cn)
    (hs1 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8) i)) (hs2 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8) i))
    (hs3 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8 - 8) i))
    (hs4 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8 - 8 - 8) i))
    (hs5 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8 - 8 - 8 - 8) i))
    (hcl : ∀ i < 8, Foot F.data (Addr.add (fb + 40#64) i))
    (hw : ∀ i < 8, Foot Wl (Addr.add (aR g.rsp + 24#64) i))
    (fe : ∀ i < 4, Foot F.data (Addr.add (g.rdx + 8#64) i)) (fnm : ∀ i < 4, Foot F.data (Addr.add (g.rsi + 8#64) i))
    (h77 : ∀ g', g'.rsp = aR g.rsp → g'.rbx = g.rbx → g'.rbp = g.rsi → g'.r12 = g.rdi → g'.r13 = g.rcx →
      ∀ fl, Q 77 g' fl (Vst (P5 V g) (aR g.rsp + 24#64) (toBytesLE cn 8)))
    (h55 : ∀ g', g'.rsp = aR g.rsp → g'.rbx = g.rbx → g'.rbp = g.rsi → g'.r12 = g.rdi → g'.r13 = g.rcx →
      g'.rdx = g.rdx →
      g'.rax = BitVec.setWidth 64 rdd(Vst (P5 V g) (aR g.rsp + 24#64) (toBytesLE cn 8), g.rsi + 8#64) →
      g'.rcx = BitVec.setWidth 64 rdd(P5 V g, g.rdx + 8#64) →
      ∀ fl, W_55 fb F Wl Q g' fl (Vst (P5 V g) (aR g.rsp + 24#64) (toBytesLE cn 8))) :
    W_0 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [aR, P5] at hcn hs1 hs2 hs3 hs4 hs5 hw fe fnm h77 h55 ⊢
  wpx [W_0, o0, Op.ldf, hcn]
  all_goals repeat' (first
    | refine h77 _ ?_ ?_ ?_ ?_ ?_ _
    | refine h55 _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ _
    | with_reducible rfl
    | with_reducible exact hs1
    | with_reducible exact hs2
    | with_reducible exact hs3
    | with_reducible exact hs4
    | with_reducible exact hs5
    | with_reducible exact hcl
    | with_reducible exact hw
    | with_reducible exact fe
    | with_reducible exact fnm
    | apply And.intro
    | intro _)

/-- `eax` -= `ecx`, `rcx` = `name._chars`, the character before the tail compared with '.': to 77, or `rdi` =
`ext._chars`, `rsi` = the tail, to the comparison's `call` (247). -/
theorem vc_55 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (fnm : ∀ i < 8, Foot F.data (Addr.add g.rbp i))
    (fcm : ∀ i < 4, Foot F.data (Addr.add (rdq(V, g.rbp) + BitVec.setWidth 64 (BitVec.setWidth 32
      (BitVec.setWidth 64 (BitVec.setWidth 32 g.rax - BitVec.setWidth 32 g.rcx) + 18446744073709551615#64)) *
      4#64) i))
    (fx : ∀ i < 8, Foot F.data (Addr.add g.rdx i))
    (h77 : ∀ g', Fr g g' → ∀ fl, Q 77 g' fl V)
    (h247 : ∀ g', g'.rdi = rdq(V, g.rdx) → Fr g g' → ∀ fl, Q 247 g' fl V) :
    W_55 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at fnm fcm fx h77 h247 ⊢
  wpx [W_55, W_240, o1, o13, Op.cmpmi]
  all_goals repeat' (first
    | refine h247 _ ?_ ?_ _
    | refine h77 _ ?_ _
    | with_reducible rfl
    | with_reducible exact fnm
    | with_reducible exact fcm
    | with_reducible exact fx
    | apply And.intro
    | intro _)

/-- `esi` = '.', `rdi` = `name`, to `ReverseFind_Dot`. -/
theorem vc_77 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (h : ∀ g', g'.rdi = g.rbp → Fr g g' → ∀ fl, Q 85 g' fl V) :
    W_77 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h ⊢
  wpx [W_77, o2]
  all_goals repeat' (first
    | refine h _ ?_ ?_ _
    | with_reducible rfl
    | apply And.intro
    | intro _)

/-- The dot's position: above 0, `r14` = `rdi` = the local, `rdx` = `name` to `Left` (201); else an empty
`addSubExtension` to `name + '~'` (179), else to `name + addSubExtension` (113). -/
theorem vc_90 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (f13 : ∀ i < 4, Foot F.data (Addr.add (g.r13 + 8#64) i))
    (h201 : ∀ g', g'.rdi = g.rsp → g'.rdx = g.rbp → g'.r14 = g.rsp → Fr g g' → ∀ fl, Q 201 g' fl V)
    (h179 : ∀ g', g'.rdi = g.r12 → g'.rsi = g.rbp → Fr g g' → ∀ fl, Q 179 g' fl V)
    (h113 : ∀ g', g'.rdi = g.r12 → g'.rsi = g.rbp → g'.rdx = g.r13 → Fr g g' → ∀ fl, Q 113 g' fl V) :
    W_90 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at f13 h201 h179 h113 ⊢
  wpx [W_90, W_192, W_96, W_168, W_104, o3, o10, o4, o9, o5]
  all_goals repeat' (first
    | refine h201 _ ?_ ?_ ?_ ?_ _
    | refine h179 _ ?_ ?_ ?_ _
    | refine h113 _ ?_ ?_ ?_ ?_ _
    | with_reducible rfl
    | with_reducible exact f13
    | apply And.intro
    | intro _)

/-- `rdi` = the result, to the `call` at 121. -/
theorem vc_118 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (h : ∀ g', g'.rdi = g.r12 → Fr g g' → ∀ fl, Q 121 g' fl V) :
    W_118 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h ⊢
  wpx [W_118, o6]
  all_goals repeat' (first
    | refine h _ ?_ ?_ _
    | with_reducible rfl
    | apply And.intro
    | intro _)

/-- The stack guard checked (as at `fs:0x28`: `jne` not taken), `add rsp, 0x20; mov rax, r12`, the five pops, to the
`ret`. -/
theorem vc_126 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (hc : rdq(V, g.rsp + 24#64) = rdq(V, fb + 40#64)) (f24 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 24#64) i))
    (fcl : ∀ i < 8, Foot F.data (Addr.add (fb + 40#64) i))
    (f1 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 32#64) i))
    (f2 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 32#64 + 8) i))
    (f3 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 32#64 + 8 + 8) i))
    (f4 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 32#64 + 8 + 8 + 8) i))
    (f5 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 32#64 + 8 + 8 + 8 + 8) i))
    (h : ∀ g', g'.rsp = g.rsp + 32#64 + 8 + 8 + 8 + 8 + 8 → g'.rbp = rdq(V, g.rsp + 32#64) →
      g'.r12 = rdq(V, g.rsp + 32#64 + 8) → g'.r13 = rdq(V, g.rsp + 32#64 + 8 + 8) →
      g'.r14 = rdq(V, g.rsp + 32#64 + 8 + 8 + 8) → g'.r15 = rdq(V, g.rsp + 32#64 + 8 + 8 + 8 + 8) →
      g'.rbx = g.rbx → g'.rax = g.r12 → ∀ fl, Q 162 g' fl V) :
    W_126 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hc f24 f1 f2 f3 f4 f5 h ⊢
  have z0 : ((0#64 : BitVec 64) == 0) = true := by decide
  wpx [W_126, W_146, o7, o8, Op.xormf, hc, BitVec.xor_self, z0, decide_true, Bool.not_true, Bool.false_eq_true,
    false_implies, eq_self_iff_true, true_implies]
  all_goals repeat' (first
    | refine h _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ _
    | with_reducible rfl
    | with_reducible exact f24
    | with_reducible exact fcl
    | with_reducible exact f1
    | with_reducible exact f2
    | with_reducible exact f3
    | with_reducible exact f4
    | with_reducible exact f5
    | apply And.intro
    | intro _)

/-- `jmp` to 118. -/
theorem vc_184 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} (h : ∀ fl, Q 118 g fl V) :
    W_184 fb F Wl Q g f V := h _

/-- `rdx` = `addSubExtension`, `rsi` = `r14`, `rdi` = the result, to the concatenation (215). -/
theorem vc_206 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (h : ∀ g', g'.rdi = g.r12 → g'.rsi = g.r14 → g'.rdx = g.r13 → Fr g g' → ∀ fl, Q 215 g' fl V) :
    W_206 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h ⊢
  wpx [W_206, o11]
  all_goals repeat' (first
    | refine h _ ?_ ?_ ?_ ?_ _
    | with_reducible rfl
    | apply And.intro
    | intro _)

/-- `rdi` = the local's `_chars`: null to 118, else to `delete[]` (229). -/
theorem vc_220 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (f0 : ∀ i < 8, Foot F.data (Addr.add g.rsp i))
    (h118 : ∀ g', Fr g g' → ∀ fl, Q 118 g' fl V)
    (h229 : ∀ g', g'.rdi = rdq(V, g.rsp) → Fr g g' → ∀ fl, Q 229 g' fl V) :
    W_220 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at f0 h118 h229 ⊢
  wpx [W_220, o12]
  all_goals repeat' (first
    | refine h118 _ ?_ _
    | refine h229 _ ?_ ?_ _
    | with_reducible rfl
    | with_reducible exact f0
    | apply And.intro
    | intro _)

/-- `jmp` to 118. -/
theorem vc_234 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} (h : ∀ fl, Q 118 g fl V) :
    W_234 fb F Wl Q g f V := h _

/-- The comparison's result: zero to 77, else `r15` = `rdi` = the local, `rdx` = `name`, to `Left` (272). -/
theorem vc_252 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (h77 : ∀ g', Fr g g' → ∀ fl, Q 77 g' fl V)
    (h272 : ∀ g', g'.rdi = g.rsp → g'.rdx = g.rbp → g'.r15 = g.rsp → Fr g g' → ∀ fl, Q 272 g' fl V) :
    W_252 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h77 h272 ⊢
  wpx [W_252, W_260, o14, o15]
  all_goals repeat' (first
    | refine h77 _ ?_ _
    | refine h272 _ ?_ ?_ ?_ ?_ _
    | with_reducible rfl
    | apply And.intro
    | intro _)

/-- `rdx` = `addSubExtension`, `rsi` = `r15`, `rdi` = the result, to the concatenation (286). -/
theorem vc_277 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (h : ∀ g', g'.rdi = g.r12 → g'.rsi = g.r15 → g'.rdx = g.r13 → Fr g g' → ∀ fl, Q 286 g' fl V) :
    W_277 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h ⊢
  wpx [W_277, o16]
  all_goals repeat' (first
    | refine h _ ?_ ?_ ?_ ?_ _
    | with_reducible rfl
    | apply And.intro
    | intro _)

/-- `jmp` to 220. -/
theorem vc_291 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} (h : ∀ fl, Q 220 g fl V) :
    W_291 fb F Wl Q g f V := h _

end Pieces

/-! ## The runs -/

section Runs
variable {prof : Profile} {F : Footprint} {Wl : List Rgn} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {fb S : Addr} {g0 : Gprs} {e₂ : Addr} {code₂ : List Byte} {j₂ : Nat} {I : (Addr → Byte) → Prop}
  {Y : State} {t : Nat} {W : Addr → Byte}

/-- A `call` at `j` (`rsp` = `aR S`, the bytes `W`) of the callee `k`, and from its return at `j + 5`. -/
theorem callK (E : Ev prof F Wl L s₀ o gev gP gE fb S g0 e₂ code₂ j₂ I) {U : State} {t₁ : Nat} {j R : Nat}
    {ent : Addr} {A : Gprs → Prop} (hKU : KeptW Wl s₀ U) (hAU : Agree F U.proc.mm.mem W)
    (hrU : U.cpu.rip = dfn_at.add j) (hs : U.cpu.gpr.rsp = aR S) (hj : j < dfn.length)
    (hd : Dec prof.feat dfn j (FV7z.mk .call 64 [.rel R] 5)) (htgt : dfn_at.add (j + 5) + BitVec.ofNat 64 R = ent)
    (hc : ∃ code : List Byte, CodeIn L ent code ∧ 0 < code.length)
    (k : KC prof F Wl L s₀ o gev gP gE S I ent (j + 5) W A) (hA : A (U.cpu.gpr.set 4 (aR S - 8)))
    (h : ∀ (Z : State) (W' : Addr → Byte) (t'' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem W' →
      Z.cpu.rip = dfn_at.add (j + 5) → Z.cpu.gpr.rsp = aR S → KS U.cpu.gpr Z.cpu.gpr → I W' →
      GoG prof L o gev gP gE Z t'') :
    GoG prof L o gev gP gE U t₁ := by
  have hU : U.cpu.gpr.rsp - 8 = aR S - 8 := by rw [hs]
  obtain ⟨cc, hinc, hcc⟩ := hc
  refine E.c.s_call hKU hAU E.hin hj hrU hd hinc hcc htgt (by rw [hU]; exact E.hr8) ?_
  rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
  rw [hU] at hA₂
  refine k Y₂ t₂ hK₂ hA₂ hr₂ (by rw [hg₂]; exact hU) (by rw [hg₂, hU]; exact hA) ?_
  intro Z W' t₃ hKZ hAZ hrZ hsZ hkZ hIZ
  rw [hg₂] at hkZ
  exact h Z W' t₃ hKZ hAZ hrZ hsZ hkZ hIZ

/-- From 126 (the frame, the bytes `W` with `I`): the guard's check, the epilogue, the `ret`, to `kr`. -/
theorem tail126 (E : Ev prof F Wl L s₀ o gev gP gE fb S g0 e₂ code₂ j₂ I) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = dfn_at.add 126) (hm : Fm S g0 Y.cpu.gpr) (hIW : I W) :
    GoG prof L o gev gP gE Y t := by
  obtain ⟨ms, mx, mp, m12, m13⟩ := hm
  obtain ⟨s1, s2, s3, s4, s5, s6, s7⟩ := E.hI W hIW
  have e1 : rdq(W, Y.cpu.gpr.rsp + 32#64) = g0.rbp := by rw [ms, q1]; exact s1
  have e2 : rdq(W, Y.cpu.gpr.rsp + 32#64 + 8) = g0.r12 := by rw [ms, q2]; exact s2
  have e3 : rdq(W, Y.cpu.gpr.rsp + 32#64 + 8 + 8) = g0.r13 := by rw [ms, q3]; exact s3
  have e4 : rdq(W, Y.cpu.gpr.rsp + 32#64 + 8 + 8 + 8) = g0.r14 := by rw [ms, q4]; exact s4
  have e5 : rdq(W, Y.cpu.gpr.rsp + 32#64 + 8 + 8 + 8 + 8) = g0.r15 := by rw [ms, q5]; exact s5
  refine (c_126 prof fb).run E.c E.hfs E.hin (fun j' g' _ V' => j' = 162 ∧ V' = W ∧
      g'.rsp = Y.cpu.gpr.rsp + 32#64 + 8 + 8 + 8 + 8 + 8 ∧ g'.rbp = rdq(W, Y.cpu.gpr.rsp + 32#64) ∧
      g'.r12 = rdq(W, Y.cpu.gpr.rsp + 32#64 + 8) ∧ g'.r13 = rdq(W, Y.cpu.gpr.rsp + 32#64 + 8 + 8) ∧
      g'.r14 = rdq(W, Y.cpu.gpr.rsp + 32#64 + 8 + 8 + 8) ∧ g'.r15 = rdq(W, Y.cpu.gpr.rsp + 32#64 + 8 + 8 + 8 + 8) ∧
      g'.rbx = Y.cpu.gpr.rbx ∧ g'.rax = Y.cpu.gpr.r12)
    hK hA hr
    (vc_126 (by rw [ms]; exact s7) (by rw [ms]; exact E.fg) E.hcl (by rw [ms, q1]; exact E.fb40)
      (by rw [ms, q2]; exact E.fb32) (by rw [ms, q3]; exact E.fb24) (by rw [ms, q4]; exact E.fb16)
      (by rw [ms, q5]; exact E.fb8)
      fun _ a b d e f g h i _ => ⟨rfl, rfl, a, b, d, e, f, g, h, i⟩) ?_
  rintro j' g fl V₁ ⟨rfl, hV₁, gs, gp, g12, g13, g14, g15, gx, ga⟩ U t₁ hKU hAU hrU hgU -
  subst V₁ hgU
  have hsU : U.cpu.gpr.rsp = S := by rw [gs, ms]; exact q6 S
  refine E.c.s_ret hKU hAU E.hin (lt_len (by decide)) hrU (ret_162 _) (by rw [hsU]; exact E.hl) E.hin₂ E.h₂
    (by rw [hsU]; exact s6) ?_
  rintro Z' t₂ hKZ' hAZ' ⟨hrZ', hgZ'⟩
  refine E.kr W Z' t₂ hKZ' hAZ' hrZ' ?_ ?_ ?_ hIW
  · rw [hgZ']
    show U.cpu.gpr.rsp + 8 = _
    rw [hsU]
  · rw [hgZ']
    exact ⟨gx.trans mx, gp.trans e1, g12.trans e2, g13.trans e3, g14.trans e4, g15.trans e5⟩
  · rw [hgZ']
    exact ga.trans m12

/-- From 118: `rdi` = the result, the `call` at 121 (`k121`), from its return 126. -/
theorem from118 (E : Ev prof F Wl L s₀ o gev gP gE fb S g0 e₂ code₂ j₂ I) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = dfn_at.add 118) (hm : Fm S g0 Y.cpu.gpr) (hIW : I W) :
    GoG prof L o gev gP gE Y t := by
  refine (c_118 prof fb).run E.c E.hfs E.hin (fun j' g' _ V' => j' = 121 ∧ V' = W ∧ g'.rdi = Y.cpu.gpr.r12 ∧
      Fr Y.cpu.gpr g') hK hA hr (vc_118 fun _ a b _ => ⟨rfl, rfl, a, b⟩) ?_
  rintro j' g fl V₁ ⟨rfl, hV₁, gdi, gf⟩ U t₁ hKU hAU hrU hgU -
  subst V₁ hgU
  have hmU := Fm.fr hm gf
  refine callK E hKU hAU hrU hmU.1 (lt_len (by decide)) (call_121 _) tgt_121 E.cN (E.k121 _ hIW)
    (gdi.trans hm.2.2.2.1) ?_
  intro Z W' t₃ hKZ hAZ hrZ hsZ hkZ hIZ
  exact tail126 E hKZ hAZ hrZ (fm_ret hmU hsZ hkZ) hIZ

/-- From 184 (back from `name + '~'`): `jmp` to 118. -/
theorem from184 (E : Ev prof F Wl L s₀ o gev gP gE fb S g0 e₂ code₂ j₂ I) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = dfn_at.add 184) (hm : Fm S g0 Y.cpu.gpr) (hIW : I W) :
    GoG prof L o gev gP gE Y t := by
  refine (c_184 prof fb).run E.c E.hfs E.hin (fun j' g' _ V' => j' = 118 ∧ g' = Y.cpu.gpr ∧ V' = W)
    hK hA hr (vc_184 fun _ => ⟨rfl, rfl, rfl⟩) ?_
  rintro j' g fl V₁ ⟨rfl, rfl, hV₁⟩ U t₁ hKU hAU hrU hgU -
  subst V₁
  exact from118 E hKU hAU hrU (by rw [hgU]; exact hm) hIW

/-- From 220: the local's buffer, null to 118, else `delete[]` (`k229`) and from its return (234) to 118. -/
theorem from220 (E : Ev prof F Wl L s₀ o gev gP gE fb S g0 e₂ code₂ j₂ I) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = dfn_at.add 220) (hm : Fm S g0 Y.cpu.gpr) (hIW : I W) :
    GoG prof L o gev gP gE Y t := by
  refine (c_220 prof fb).run E.c E.hfs E.hin (fun j' g' _ V' => V' = W ∧ Fr Y.cpu.gpr g' ∧
      (j' = 118 ∨ (j' = 229 ∧ g'.rdi = rdq(W, Y.cpu.gpr.rsp)))) hK hA hr
    (vc_220 (by rw [hm.1]; exact E.f0) (fun _ a _ => ⟨rfl, a, Or.inl rfl⟩)
      (fun _ a b _ => ⟨rfl, b, Or.inr ⟨rfl, a⟩⟩)) ?_
  rintro j' g fl V₁ ⟨hV₁, gf, hpost⟩ U t₁ hKU hAU hrU hgU -
  subst V₁ hgU
  have hmU := Fm.fr hm gf
  rcases hpost with rfl | ⟨rfl, gdi⟩
  · exact from118 E hKU hAU hrU hmU hIW
  · refine callK E hKU hAU hrU hmU.1 (lt_len (by decide)) (call_229 _) tgt_229 E.cD (E.k229 _ hIW)
      (by show U.cpu.gpr.rdi = _; rw [gdi, hm.1]) ?_
    intro Z W' t₃ hKZ hAZ hrZ hsZ hkZ hIZ
    refine (c_234 prof fb).run E.c E.hfs E.hin (fun j' g' _ V' => j' = 118 ∧ g' = Z.cpu.gpr ∧ V' = W')
      hKZ hAZ hrZ (vc_234 fun _ => ⟨rfl, rfl, rfl⟩) ?_
    rintro j' g fl V₁ ⟨rfl, rfl, hV₁⟩ U' t₄ hKU' hAU' hrU' hgU' -
    subst V₁
    exact from118 E hKU' hAU' hrU' (by rw [hgU']; exact fm_ret hmU hsZ hkZ) hIZ

/-- From 206 (back from `Left`, `r14` = the local): the concatenation (`k215`), from its return 220. -/
theorem from206 (E : Ev prof F Wl L s₀ o gev gP gE fb S g0 e₂ code₂ j₂ I) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = dfn_at.add 206) (hm : Fm S g0 Y.cpu.gpr)
    (h14 : Y.cpu.gpr.r14 = aR S) (hIW : I W) :
    GoG prof L o gev gP gE Y t := by
  refine (c_206 prof fb).run E.c E.hfs E.hin (fun j' g' _ V' => j' = 215 ∧ V' = W ∧ g'.rdi = Y.cpu.gpr.r12 ∧
      g'.rsi = Y.cpu.gpr.r14 ∧ g'.rdx = Y.cpu.gpr.r13 ∧ Fr Y.cpu.gpr g') hK hA hr
    (vc_206 fun _ a b d e _ => ⟨rfl, rfl, a, b, d, e⟩) ?_
  rintro j' g fl V₁ ⟨rfl, hV₁, gdi, gsi, gdx, gf⟩ U t₁ hKU hAU hrU hgU -
  subst V₁ hgU
  have hmU := Fm.fr hm gf
  refine callK E hKU hAU hrU hmU.1 (lt_len (by decide)) (call_215 _) tgt_215 E.cS (E.k215 _ hIW)
    ⟨gdi.trans hm.2.2.2.1, gsi.trans h14, gdx.trans hm.2.2.2.2⟩ ?_
  intro Z W' t₃ hKZ hAZ hrZ hsZ hkZ hIZ
  exact from220 E hKZ hAZ hrZ (fm_ret hmU hsZ hkZ) hIZ

/-- From 277 (back from `Left`, `r15` = the local): the concatenation (`k286`), from its return (291) to 220. -/
theorem from277 (E : Ev prof F Wl L s₀ o gev gP gE fb S g0 e₂ code₂ j₂ I) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = dfn_at.add 277) (hm : Fm S g0 Y.cpu.gpr)
    (h15 : Y.cpu.gpr.r15 = aR S) (hIW : I W) :
    GoG prof L o gev gP gE Y t := by
  refine (c_277 prof fb).run E.c E.hfs E.hin (fun j' g' _ V' => j' = 286 ∧ V' = W ∧ g'.rdi = Y.cpu.gpr.r12 ∧
      g'.rsi = Y.cpu.gpr.r15 ∧ g'.rdx = Y.cpu.gpr.r13 ∧ Fr Y.cpu.gpr g') hK hA hr
    (vc_277 fun _ a b d e _ => ⟨rfl, rfl, a, b, d, e⟩) ?_
  rintro j' g fl V₁ ⟨rfl, hV₁, gdi, gsi, gdx, gf⟩ U t₁ hKU hAU hrU hgU -
  subst V₁ hgU
  have hmU := Fm.fr hm gf
  refine callK E hKU hAU hrU hmU.1 (lt_len (by decide)) (call_286 _) tgt_286 E.cS (E.k286 _ hIW)
    ⟨gdi.trans hm.2.2.2.1, gsi.trans h15, gdx.trans hm.2.2.2.2⟩ ?_
  intro Z W' t₃ hKZ hAZ hrZ hsZ hkZ hIZ
  refine (c_291 prof fb).run E.c E.hfs E.hin (fun j' g' _ V' => j' = 220 ∧ g' = Z.cpu.gpr ∧ V' = W')
    hKZ hAZ hrZ (vc_291 fun _ => ⟨rfl, rfl, rfl⟩) ?_
  rintro j' g fl V₁ ⟨rfl, rfl, hV₁⟩ U' t₄ hKU' hAU' hrU' hgU' -
  subst V₁
  exact from220 E hKU' hAU' hrU' (by rw [hgU']; exact fm_ret hmU hsZ hkZ) hIZ

/-- From 90 (back from `ReverseFind_Dot`): `Left` (`k201`) and from its return 206; or `name + '~'` (`k179`) and from
its return 184; or `name + addSubExtension` (`k113`) and from its return 118. -/
theorem from90 (E : Ev prof F Wl L s₀ o gev gP gE fb S g0 e₂ code₂ j₂ I) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = dfn_at.add 90) (hm : Fm S g0 Y.cpu.gpr) (hIW : I W) :
    GoG prof L o gev gP gE Y t := by
  refine (c_90 prof fb).run E.c E.hfs E.hin (fun j' g' _ V' => V' = W ∧ Fr Y.cpu.gpr g' ∧
      ((j' = 201 ∧ g'.rdi = Y.cpu.gpr.rsp ∧ g'.rdx = Y.cpu.gpr.rbp ∧ g'.r14 = Y.cpu.gpr.rsp) ∨
        (j' = 179 ∧ g'.rdi = Y.cpu.gpr.r12 ∧ g'.rsi = Y.cpu.gpr.rbp) ∨
        (j' = 113 ∧ g'.rdi = Y.cpu.gpr.r12 ∧ g'.rsi = Y.cpu.gpr.rbp ∧ g'.rdx = Y.cpu.gpr.r13))) hK hA hr
    (vc_90 (by rw [hm.2.2.2.2]; exact E.fx8) (fun _ a b d e _ => ⟨rfl, e, Or.inl ⟨rfl, a, b, d⟩⟩)
      (fun _ a b e _ => ⟨rfl, e, Or.inr (Or.inl ⟨rfl, a, b⟩)⟩)
      (fun _ a b d e _ => ⟨rfl, e, Or.inr (Or.inr ⟨rfl, a, b, d⟩)⟩)) ?_
  rintro j' g fl V₁ ⟨hV₁, gf, hpost⟩ U t₁ hKU hAU hrU hgU -
  subst V₁ hgU
  have hmU := Fm.fr hm gf
  rcases hpost with ⟨rfl, gdi, gdx, g14⟩ | ⟨rfl, gdi, gsi⟩ | ⟨rfl, gdi, gsi, gdx⟩
  · refine callK E hKU hAU hrU hmU.1 (lt_len (by decide)) (call_201 _) tgt_201 E.cL (E.k201 _ hIW)
      ⟨gdi.trans hm.1, gdx.trans hm.2.2.1⟩ ?_
    intro Z W' t₃ hKZ hAZ hrZ hsZ hkZ hIZ
    exact from206 E hKZ hAZ hrZ (fm_ret hmU hsZ hkZ) (hkZ.2.2.2.2.1.trans (g14.trans hm.1)) hIZ
  · refine callK E hKU hAU hrU hmU.1 (lt_len (by decide)) (call_179 _) tgt_179 E.cT (E.k179 _ hIW)
      ⟨gdi.trans hm.2.2.2.1, gsi.trans hm.2.2.1⟩ ?_
    intro Z W' t₃ hKZ hAZ hrZ hsZ hkZ hIZ
    exact from184 E hKZ hAZ hrZ (fm_ret hmU hsZ hkZ) hIZ
  · refine callK E hKU hAU hrU hmU.1 (lt_len (by decide)) (call_113 _) tgt_113 E.cS (E.k113 _ hIW)
      ⟨gdi.trans hm.2.2.2.1, gsi.trans hm.2.2.1, gdx.trans hm.2.2.2.2⟩ ?_
    intro Z W' t₃ hKZ hAZ hrZ hsZ hkZ hIZ
    exact from118 E hKZ hAZ hrZ (fm_ret hmU hsZ hkZ) hIZ

/-- From 77: `ReverseFind_Dot` (`k85`), from its return 90. -/
theorem from77 (E : Ev prof F Wl L s₀ o gev gP gE fb S g0 e₂ code₂ j₂ I) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = dfn_at.add 77) (hm : Fm S g0 Y.cpu.gpr) (hIW : I W) :
    GoG prof L o gev gP gE Y t := by
  refine (c_77 prof fb).run E.c E.hfs E.hin (fun j' g' _ V' => j' = 85 ∧ V' = W ∧ g'.rdi = Y.cpu.gpr.rbp ∧
      Fr Y.cpu.gpr g') hK hA hr (vc_77 fun _ a b _ => ⟨rfl, rfl, a, b⟩) ?_
  rintro j' g fl V₁ ⟨rfl, hV₁, gdi, gf⟩ U t₁ hKU hAU hrU hgU -
  subst V₁ hgU
  have hmU := Fm.fr hm gf
  refine callK E hKU hAU hrU hmU.1 (lt_len (by decide)) (call_85 _) tgt_85 E.cR (E.k85 _ hIW)
    (gdi.trans hm.2.2.1) ?_
  intro Z W' t₃ hKZ hAZ hrZ hsZ hkZ hIZ
  exact from90 E hKZ hAZ hrZ (fm_ret hmU hsZ hkZ) hIZ

/-- From 252 (back from the comparison): to 77, or `Left` (`k272`) and from its return 277. -/
theorem from252 (E : Ev prof F Wl L s₀ o gev gP gE fb S g0 e₂ code₂ j₂ I) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = dfn_at.add 252) (hm : Fm S g0 Y.cpu.gpr) (hIW : I W) :
    GoG prof L o gev gP gE Y t := by
  refine (c_252 prof fb).run E.c E.hfs E.hin (fun j' g' _ V' => V' = W ∧ Fr Y.cpu.gpr g' ∧
      (j' = 77 ∨ (j' = 272 ∧ g'.rdi = Y.cpu.gpr.rsp ∧ g'.rdx = Y.cpu.gpr.rbp ∧ g'.r15 = Y.cpu.gpr.rsp))) hK hA hr
    (vc_252 (fun _ a _ => ⟨rfl, a, Or.inl rfl⟩) (fun _ a b d e _ => ⟨rfl, e, Or.inr ⟨rfl, a, b, d⟩⟩)) ?_
  rintro j' g fl V₁ ⟨hV₁, gf, hpost⟩ U t₁ hKU hAU hrU hgU -
  subst V₁ hgU
  have hmU := Fm.fr hm gf
  rcases hpost with rfl | ⟨rfl, gdi, gdx, g15⟩
  · exact from77 E hKU hAU hrU hmU hIW
  · refine callK E hKU hAU hrU hmU.1 (lt_len (by decide)) (call_272 _) tgt_272 E.cL (E.k272 _ hIW)
      ⟨gdi.trans hm.1, gdx.trans hm.2.2.1⟩ ?_
    intro Z W' t₃ hKZ hAZ hrZ hsZ hkZ hIZ
    exact from277 E hKZ hAZ hrZ (fm_ret hmU hsZ hkZ) (hkZ.2.2.2.2.2.trans (g15.trans hm.1)) hIZ

end Runs

variable {prof : Profile} {F : Footprint} {Wl : List Rgn} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {X : State} {t : Nat} {V : Addr → Byte}

/-- `GetDefaultName2 (name, ext, addSubExtension)` (the result at `rdi`, `name` = `rsi`, `ext` = `rdx`,
`addSubExtension` = `rcx`) from its entry, `fb` the `fs` base, `I` an invariant of the bytes: the pushes' slots, the
guard's slot and the calls' return address slot in what the run may store into, the local, the return address and
the guard at `fs:0x28` readable; `name`'s and `ext`'s `_chars` and `_len`, the compared character (`cmA`) and
`addSubExtension._len` readable. `I` holds after the prologue (`hI0`) and gives the stack (`hI`). The callees, each
from its return with `rsp` as it was, the callee-saved registers as at its entry and `I`: the comparison (`k247`,
`rdi` = `ext._chars`), `ReverseFind_Dot (name, '.')` (`k85`), `Left` into the local (`k201`, `k272`), the
concatenations into the result (`k113`, `k215`, `k286`), `name + '~'` (`k179`), `delete[]` of the local's buffer
(`k229`), the call at 121 on the result (`k121`). At the return address (`kr`): `rsp` 8 above the entry's, the
callee-saved registers as they were, `rax` = the result, bytes with `I`. -/
theorem dfn_ok {fb : Addr} {I : (Addr → Byte) → Prop} {e₂ : Addr} {code₂ : List Byte} {j₂ : Nat}
    (c : Seg prof F Wl L s₀ o) (hfs : s₀.cpu.seg.fsBase = fb) (hin : CodeIn L dfn_at dfn)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = dfn_at)
    (hcl : ∀ i < 8, Foot F.data (Addr.add (fb + 40#64) i))
    (hs1 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8) i))
    (hs2 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8 - 8) i))
    (hs3 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8 - 8 - 8) i))
    (hs4 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8 - 8 - 8 - 8) i))
    (hs5 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8 - 8 - 8 - 8 - 8) i))
    (hw : ∀ i < 8, Foot Wl (Addr.add (aR X.cpu.gpr.rsp + 24#64) i))
    (f0 : ∀ i < 8, Foot F.data (Addr.add (aR X.cpu.gpr.rsp) i))
    (hr8 : ∀ i < 8, Foot Wl (Addr.add (aR X.cpu.gpr.rsp - 8) i))
    (hl : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsp i))
    (hin₂ : CodeIn L e₂ code₂) (h₂ : j₂ < code₂.length)
    (fe : ∀ i < 4, Foot F.data (Addr.add (X.cpu.gpr.rdx + 8#64) i))
    (fnm : ∀ i < 4, Foot F.data (Addr.add (X.cpu.gpr.rsi + 8#64) i))
    (fx : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rdx i))
    (fnc : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsi i))
    (fcm : ∀ i < 4, Foot F.data (Addr.add (cmA fb V X.cpu.gpr) i))
    (fx8 : ∀ i < 4, Foot F.data (Addr.add (X.cpu.gpr.rcx + 8#64) i))
    (hI : ∀ W, I W → Stk fb W X.cpu.gpr.rsp X.cpu.gpr (e₂.add j₂)) (hI0 : I (V0 fb V X.cpu.gpr))
    (cE : ∃ code : List Byte, CodeIn L 0x44ba80#64 code ∧ 0 < code.length)
    (cR : ∃ code : List Byte, CodeIn L 0x44dd40#64 code ∧ 0 < code.length)
    (cS : ∃ code : List Byte, CodeIn L 0x44d330#64 code ∧ 0 < code.length)
    (cN : ∃ code : List Byte, CodeIn L 0x44de20#64 code ∧ 0 < code.length)
    (cT : ∃ code : List Byte, CodeIn L 0x44d280#64 code ∧ 0 < code.length)
    (cL : ∃ code : List Byte, CodeIn L 0x44d240#64 code ∧ 0 < code.length)
    (cD : ∃ code : List Byte, CodeIn L 0x6014f0#64 code ∧ 0 < code.length)
    (k247 : KC prof F Wl L s₀ o gev gP gE X.cpu.gpr.rsp I 0x44ba80#64 252 (V0 fb V X.cpu.gpr)
      (fun g => g.rdi = rdq(V0 fb V X.cpu.gpr, X.cpu.gpr.rdx)))
    (k85 : ∀ W, I W → KC prof F Wl L s₀ o gev gP gE X.cpu.gpr.rsp I 0x44dd40#64 90 W
      (fun g => g.rdi = X.cpu.gpr.rsi))
    (k113 : ∀ W, I W → KC prof F Wl L s₀ o gev gP gE X.cpu.gpr.rsp I 0x44d330#64 118 W
      (fun g => g.rdi = X.cpu.gpr.rdi ∧ g.rsi = X.cpu.gpr.rsi ∧ g.rdx = X.cpu.gpr.rcx))
    (k121 : ∀ W, I W → KC prof F Wl L s₀ o gev gP gE X.cpu.gpr.rsp I 0x44de20#64 126 W
      (fun g => g.rdi = X.cpu.gpr.rdi))
    (k179 : ∀ W, I W → KC prof F Wl L s₀ o gev gP gE X.cpu.gpr.rsp I 0x44d280#64 184 W
      (fun g => g.rdi = X.cpu.gpr.rdi ∧ g.rsi = X.cpu.gpr.rsi))
    (k201 : ∀ W, I W → KC prof F Wl L s₀ o gev gP gE X.cpu.gpr.rsp I 0x44d240#64 206 W
      (fun g => g.rdi = aR X.cpu.gpr.rsp ∧ g.rdx = X.cpu.gpr.rsi))
    (k215 : ∀ W, I W → KC prof F Wl L s₀ o gev gP gE X.cpu.gpr.rsp I 0x44d330#64 220 W
      (fun g => g.rdi = X.cpu.gpr.rdi ∧ g.rsi = aR X.cpu.gpr.rsp ∧ g.rdx = X.cpu.gpr.rcx))
    (k229 : ∀ W, I W → KC prof F Wl L s₀ o gev gP gE X.cpu.gpr.rsp I 0x6014f0#64 234 W
      (fun g => g.rdi = rdq(W, aR X.cpu.gpr.rsp)))
    (k272 : ∀ W, I W → KC prof F Wl L s₀ o gev gP gE X.cpu.gpr.rsp I 0x44d240#64 277 W
      (fun g => g.rdi = aR X.cpu.gpr.rsp ∧ g.rdx = X.cpu.gpr.rsi))
    (k286 : ∀ W, I W → KC prof F Wl L s₀ o gev gP gE X.cpu.gpr.rsp I 0x44d330#64 291 W
      (fun g => g.rdi = X.cpu.gpr.rdi ∧ g.rsi = aR X.cpu.gpr.rsp ∧ g.rdx = X.cpu.gpr.rcx))
    (kr : ∀ (W : Addr → Byte) (Z' : State) (t' : Nat), KeptW Wl s₀ Z' → Agree F Z'.proc.mm.mem W →
      Z'.cpu.rip = e₂.add j₂ → Z'.cpu.gpr.rsp = X.cpu.gpr.rsp + 8 → KS X.cpu.gpr Z'.cpu.gpr →
      Z'.cpu.gpr.rax = X.cpu.gpr.rdi → I W → GoG prof L o gev gP gE Z' t') :
    GoG prof L o gev gP gE X t := by
  have E : Ev prof F Wl L s₀ o gev gP gE fb X.cpu.gpr.rsp X.cpu.gpr e₂ code₂ j₂ I :=
    { c := c, hfs := hfs, hin := hin, hin₂ := hin₂, h₂ := h₂, hI := hI, hcl := hcl,
      fg := fun i hi => c.hws _ (hw i hi), f0 := f0,
      fb40 := fun i hi => c.hws _ (hs5 i hi), fb32 := fun i hi => c.hws _ (hs4 i hi),
      fb24 := fun i hi => c.hws _ (hs3 i hi), fb16 := fun i hi => c.hws _ (hs2 i hi),
      fb8 := fun i hi => c.hws _ (hs1 i hi), hl := hl, hr8 := hr8, fx8 := fx8,
      cR := cR, cS := cS, cN := cN, cT := cT, cL := cL, cD := cD,
      k85 := k85, k113 := k113, k121 := k121, k179 := k179, k201 := k201, k215 := k215, k229 := k229,
      k272 := k272, k286 := k286, kr := kr }
  -- the prologue, to 77 or to the comparison's `call`
  refine (c_0 prof fb).run c hfs hin (fun j' g' _ V' => V' = V0 fb V X.cpu.gpr ∧ Fm X.cpu.gpr.rsp X.cpu.gpr g' ∧
      (j' = 77 ∨ (j' = 247 ∧ g'.rdi = rdq(V0 fb V X.cpu.gpr, X.cpu.gpr.rdx)))) hK hA
    (by rw [addr_add_zero]; exact hrip)
    (vc_0 rfl hs1 hs2 hs3 hs4 hs5 hcl hw fe fnm (fun _ a b d e i _ => ⟨rfl, ⟨a, b, d, e, i⟩, Or.inl rfl⟩)
      (fun g' a b d e i gdx gax gcx fl => vc_55 (by rw [d]; exact fnc)
        (by rw [gax, gcx, d, sw_64_32, sw_64_32]; exact fcm) (by rw [gdx]; exact fx)
        (fun _ hf _ => ⟨rfl, Fm.fr ⟨a, b, d, e, i⟩ hf, Or.inl rfl⟩)
        (fun _ hdi hf _ => ⟨rfl, Fm.fr ⟨a, b, d, e, i⟩ hf, Or.inr ⟨rfl, by rw [hdi, gdx]⟩⟩))) ?_
  rintro j' g fl V₁ ⟨hV₁, hmY, hpost⟩ Y t₁ hKY hAY hrY hgY -
  subst V₁ hgY
  rcases hpost with rfl | ⟨rfl, gdi⟩
  · exact from77 E hKY hAY hrY hmY hI0
  · refine callK E hKY hAY hrY hmY.1 (lt_len (by decide)) (call_247 _) tgt_247 cE k247 gdi ?_
    intro Z W' t₃ hKZ hAZ hrZ hsZ hkZ hIZ
    exact from252 E hKZ hAZ hrZ (fm_ret hmY hsZ hkZ) hIZ

end FV7z.Dfn
