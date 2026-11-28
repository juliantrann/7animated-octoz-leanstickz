import FV7z.Gdp.Cuts
import FV7z.Lemmas.LeafRet
import FV7z.Lemmas.CallM
import FV7z.Lemmas.Fr40
/-!
# `CArc::GetItem_DefaultPath` (PLAN.md §M, M1): the run through the callees

7-Zip 26.06's `CArc::GetItem_DefaultPath (index, result)` at `0x5d2040` in `7zzs`
(`CPP/7zip/UI/Common/OpenArchive.cpp`; `objdump -d`): `this` in `rdi` (`rbx`), `index` in `esi` (`r13d`), `result` (a
`UString`) in `rdx` (`rbp`). `S` the stack pointer and `g0` the registers at the entry: `push r14, r13, r12, rbp,
rbx; sub rsp, 0x30` (`aR S`), the stack guard (`fs:0x28`) at `aR S + 40`, `isDir` at `aR S + 15`, a `CPropVariant`
at `aR S + 16` (its `vt` the 2 bytes there, its value the 8 at `aR S + 24`). `result.Empty ()` inline (the 4 bytes
at `result + 8` and at `result._chars` set to 0), `Archive_IsItem_Dir (Archive, index, &isDir)` (65, `0x5d1670`);
its result not 0, or `isDir`, to the epilogue (84). Else `result = DefaultName` (140, `0x44d710`, `rsi` = `this +
72`), `prop` cleared, `Archive->GetProperty (index, kpidExtension, &prop)` (179, `call qword [rax + 0x30]` through
`Archive`'s vtable, `Seg.s_callM`); its result not 0 to 205; `vt` = `VT_BSTR` (8): `result.Add_Dot ()` (243,
`0x44d9b0`), `result += prop.bstrVal` (256, `0x44db10`), to 205; another `vt` not 0: `E_FAIL`, to 205; at 205
`prop.Clear ()` (208, `0x456f60`), to 84: the guard's check, the epilogue, `ret` (119). Not covered:
`__stack_chk_fail` (263), the landing pad.

The callees are continuations (`KC`, as in `FV7z/Dfn/Holds.lean`): from its return the run goes on with `rsp` as it
was and the callee-saved registers (`KS`) as at the `call`, and bytes with the invariant `I` the caller chooses. `I`
holds after the pushes and the guard's store (`hI0`), survives the stores of 0 (`zL`, `zC`, `z16`, `z24`), gives
the stack (`Stk`), `Archive` (`har`) and the vtable's entry (`htg`).

- `aR`, `q1`–`q6`, `P5`, `V1`, `Stk`, `Fm`, `Fr`, `KC`, `Ev`: the frame, the bytes after the pushes and the guard's
  store, the stack, the frame's registers, what a piece keeps, the callees, the hypotheses of the runs; `callK`: a
  `call`.
- `vc_*`: the pieces; `tail84`, `from213`, `from205`, `from261`, `from248`, `from182`, `from145`, `from70`: the runs
  from the cut points.
- `gdp_ok`: from the entry to the return address.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Gdp
set_option linter.unusedVariables false

open FV7z.Fr40 (KS r1 r2 r3 r4 r5)

/-! ## The instructions outside the blocks -/

/-- The `call` at 65 (`0x5d1670`). -/
def pc65 : List Byte := [0xe8, 0xea, 0xf5, 0xff, 0xff]
theorem pc65_0 : ∀ feat, Dec feat pc65 0 (FV7z.mk .call 64 [.rel 18446744073709549034] 5) := by dec_rfl
theorem wc_65 : pc65 <+: gdp.drop 65 := by decide +kernel
theorem call_65 (feat : Features) : Dec feat gdp 65 (FV7z.mk .call 64 [.rel 18446744073709549034] 5) :=
  Dec.shift (j := 65) (k := 0) (pc65_0 feat) wc_65 (Nat.zero_le _)
theorem tgt_65 : gdp_at.add (65 + 5) + BitVec.ofNat 64 18446744073709549034 = 0x5d1670#64 := by decide

/-- The `call` at 140 (`0x44d710`). -/
def pc140 : List Byte := [0xe8, 0x3f, 0xb6, 0xe7, 0xff]
theorem pc140_0 : ∀ feat, Dec feat pc140 0 (FV7z.mk .call 64 [.rel 18446744073707959871] 5) := by dec_rfl
theorem wc_140 : pc140 <+: gdp.drop 140 := by decide +kernel
theorem call_140 (feat : Features) : Dec feat gdp 140 (FV7z.mk .call 64 [.rel 18446744073707959871] 5) :=
  Dec.shift (j := 140) (k := 0) (pc140_0 feat) wc_140 (Nat.zero_le _)
theorem tgt_140 : gdp_at.add (140 + 5) + BitVec.ofNat 64 18446744073707959871 = 0x44d710#64 := by decide

/-- The `call` at 208 (`0x456f60`). -/
def pc208 : List Byte := [0xe8, 0x4b, 0x4e, 0xe8, 0xff]
theorem pc208_0 : ∀ feat, Dec feat pc208 0 (FV7z.mk .call 64 [.rel 18446744073707998795] 5) := by dec_rfl
theorem wc_208 : pc208 <+: gdp.drop 208 := by decide +kernel
theorem call_208 (feat : Features) : Dec feat gdp 208 (FV7z.mk .call 64 [.rel 18446744073707998795] 5) :=
  Dec.shift (j := 208) (k := 0) (pc208_0 feat) wc_208 (Nat.zero_le _)
theorem tgt_208 : gdp_at.add (208 + 5) + BitVec.ofNat 64 18446744073707998795 = 0x456f60#64 := by decide

/-- The `call` at 243 (`0x44d9b0`). -/
def pc243 : List Byte := [0xe8, 0x78, 0xb8, 0xe7, 0xff]
theorem pc243_0 : ∀ feat, Dec feat pc243 0 (FV7z.mk .call 64 [.rel 18446744073707960440] 5) := by dec_rfl
theorem wc_243 : pc243 <+: gdp.drop 243 := by decide +kernel
theorem call_243 (feat : Features) : Dec feat gdp 243 (FV7z.mk .call 64 [.rel 18446744073707960440] 5) :=
  Dec.shift (j := 243) (k := 0) (pc243_0 feat) wc_243 (Nat.zero_le _)
theorem tgt_243 : gdp_at.add (243 + 5) + BitVec.ofNat 64 18446744073707960440 = 0x44d9b0#64 := by decide

/-- The `call` at 256 (`0x44db10`). -/
def pc256 : List Byte := [0xe8, 0xcb, 0xb9, 0xe7, 0xff]
theorem pc256_0 : ∀ feat, Dec feat pc256 0 (FV7z.mk .call 64 [.rel 18446744073707960779] 5) := by dec_rfl
theorem wc_256 : pc256 <+: gdp.drop 256 := by decide +kernel
theorem call_256 (feat : Features) : Dec feat gdp 256 (FV7z.mk .call 64 [.rel 18446744073707960779] 5) :=
  Dec.shift (j := 256) (k := 0) (pc256_0 feat) wc_256 (Nat.zero_le _)
theorem tgt_256 : gdp_at.add (256 + 5) + BitVec.ofNat 64 18446744073707960779 = 0x44db10#64 := by decide

/-- The `call` through the vtable. -/
def pcm : List Byte := [0xff, 0x50, 0x30]
theorem pcm_0 : ∀ feat, Dec feat pcm 0 (FV7z.mk .call 64 [.mem (mbd 0 48 64)] 3) := by dec_rfl
theorem wc_179 : pcm <+: gdp.drop 179 := by decide +kernel
theorem call_179 (feat : Features) : Dec feat gdp 179 (FV7z.mk .call 64 [.mem (mbd 0 48 64)] 3) :=
  Dec.shift (j := 179) (k := 0) (pcm_0 feat) wc_179 (Nat.zero_le _)

/-- The `ret`. -/
def pret : List Byte := [0xc3]
theorem pret_0 : ∀ feat, Dec feat pret 0 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem wt_119 : pret <+: gdp.drop 119 := by decide +kernel
theorem ret_119 (feat : Features) : Dec feat gdp 119 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 119) (k := 0) (pret_0 feat) wt_119 (Nat.zero_le _)

/-! ## The frame -/

/-- The stack pointer after the five pushes and `sub rsp, 0x30`. -/
abbrev aR (S : Addr) : Addr := S - 8 - 8 - 8 - 8 - 8 - 48#64

theorem q1 (S : Addr) : aR S + 48#64 = S - 8 - 8 - 8 - 8 - 8 := BitVec.sub_add_cancel _ _
theorem q2 (S : Addr) : aR S + 48#64 + 8 = S - 8 - 8 - 8 - 8 := by rw [q1]; exact r1 S
theorem q3 (S : Addr) : aR S + 48#64 + 8 + 8 = S - 8 - 8 - 8 := by rw [q1]; exact r2 S
theorem q4 (S : Addr) : aR S + 48#64 + 8 + 8 + 8 = S - 8 - 8 := by rw [q1]; exact r3 S
theorem q5 (S : Addr) : aR S + 48#64 + 8 + 8 + 8 + 8 = S - 8 := by rw [q1]; exact r4 S
theorem q6 (S : Addr) : aR S + 48#64 + 8 + 8 + 8 + 8 + 8 = S := by rw [q1]; exact r5 S

/-- The bytes after the five pushes (`r14`, `r13`, `r12`, `rbp`, `rbx`). -/
abbrev P5 (V : Addr → Byte) (g : Gprs) : Addr → Byte :=
  Vst (Vst (Vst (Vst (Vst V (g.rsp - 8) (toBytesLE g.r14 8)) (g.rsp - 8 - 8) (toBytesLE g.r13 8))
    (g.rsp - 8 - 8 - 8) (toBytesLE g.r12 8)) (g.rsp - 8 - 8 - 8 - 8) (toBytesLE g.rbp 8))
    (g.rsp - 8 - 8 - 8 - 8 - 8) (toBytesLE g.rbx 8)

/-- The bytes after the pushes and the stack guard's store. -/
abbrev V1 (fb : Addr) (V : Addr → Byte) (g : Gprs) : Addr → Byte :=
  Vst (P5 V g) (aR g.rsp + 40#64) (toBytesLE rdq(P5 V g, fb + 40#64) 8)

/-- The stack (`fb` the `fs` base, `ra` the return address): the five saved registers, the return address, the stack
guard as at `fs:0x28`. -/
abbrev Stk (fb : Addr) (W : Addr → Byte) (S : Addr) (g0 : Gprs) (ra : Addr) : Prop :=
  rdq(W, S - 8 - 8 - 8 - 8 - 8) = g0.rbx ∧ rdq(W, S - 8 - 8 - 8 - 8) = g0.rbp ∧ rdq(W, S - 8 - 8 - 8) = g0.r12 ∧
    rdq(W, S - 8 - 8) = g0.r13 ∧ rdq(W, S - 8) = g0.r14 ∧ rdq(W, S) = ra ∧
    rdq(W, aR S + 40#64) = rdq(W, fb + 40#64)

/-- The frame: `rsp` = `aR S`, `rbx` = `this`, `rbp` = `result`, `r13` = `index` (zero-extended), `r15` as at the
entry. -/
abbrev Fm (S : Addr) (g0 g : Gprs) : Prop :=
  g.rsp = aR S ∧ g.rbx = g0.rdi ∧ g.rbp = g0.rdx ∧ g.r13 = BitVec.setWidth 64 (BitVec.setWidth 32 g0.rsi) ∧
    g.r15 = g0.r15

/-- What a piece keeps: `rsp`, `rbx`, `rbp`, `r13`, `r15`. -/
abbrev Fr (g g' : Gprs) : Prop :=
  g'.rsp = g.rsp ∧ g'.rbx = g.rbx ∧ g'.rbp = g.rbp ∧ g'.r13 = g.r13 ∧ g'.r15 = g.r15

theorem Fm.fr {S : Addr} {g0 g g' : Gprs} (h : Fm S g0 g) (h' : Fr g g') : Fm S g0 g' :=
  ⟨h'.1.trans h.1, h'.2.1.trans h.2.1, h'.2.2.1.trans h.2.2.1, h'.2.2.2.1.trans h.2.2.2.1,
    h'.2.2.2.2.trans h.2.2.2.2⟩

/-- Back from a callee: `rsp` as before the `call`, the callee-saved registers kept. -/
theorem fm_ret {S : Addr} {g0 g g' : Gprs} (h : Fm S g0 g) (hs : g'.rsp = aR S) (hk : KS g g') : Fm S g0 g' :=
  ⟨hs, hk.1.trans h.2.1, hk.2.1.trans h.2.2.1, hk.2.2.2.1.trans h.2.2.2.1, hk.2.2.2.2.2.trans h.2.2.2.2⟩

/-- A callee from the `call` before `j` (entry `ent`, the bytes `W`, the registers `A`): at its entry, and from its
return at `j` with `rsp` = `aR S`, the callee-saved registers as at its entry and bytes with `I`, the run goes on to
the goal. -/
def KC (prof : Profile) (F : Footprint) (Wl : List Rgn) (L : List (Addr × List Byte)) (s₀ : State) (o : Oracle)
    (gev : List Event) (gP : State → Nat → List Event → Prop) (gE : Outcome → List Event → Prop)
    (S : Addr) (I : (Addr → Byte) → Prop) (ent : Addr) (j : Nat) (W : Addr → Byte) (A : Gprs → Prop) : Prop :=
  ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y →
    Agree F Y.proc.mm.mem (Vst W (aR S - 8) (toBytesLE (gdp_at.add j) 8)) →
    Y.cpu.rip = ent → Y.cpu.gpr.rsp = aR S - 8 → A Y.cpu.gpr →
    (∀ (Z : State) (W' : Addr → Byte) (t'' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem W' →
      Z.cpu.rip = gdp_at.add j → Z.cpu.gpr.rsp = aR S → KS Y.cpu.gpr Z.cpu.gpr → I W' →
      GoG prof L o gev gP gE Z t'') →
    GoG prof L o gev gP gE Y t'

/-- The hypotheses of the runs from the cut points (`S`, `g0` the entry's stack pointer and registers, `e₂.add j₂`
the return address, `I` the invariant of the bytes, `ar` = `Archive`, `eG` its `GetProperty`). -/
structure Ev (prof : Profile) (F : Footprint) (Wl : List Rgn) (L : List (Addr × List Byte)) (s₀ : State)
    (o : Oracle) (gev : List Event) (gP : State → Nat → List Event → Prop) (gE : Outcome → List Event → Prop)
    (fb S : Addr) (g0 : Gprs) (e₂ : Addr) (code₂ : List Byte) (j₂ : Nat) (I : (Addr → Byte) → Prop)
    (ar eG : Addr) : Prop where
  c : Seg prof F Wl L s₀ o
  hfs : s₀.cpu.seg.fsBase = fb
  hin : CodeIn L gdp_at gdp
  hin₂ : CodeIn L e₂ code₂
  h₂ : j₂ < code₂.length
  hI : ∀ W, I W → Stk fb W S g0 (e₂.add j₂)
  hcl : ∀ i < 8, Foot F.data (Addr.add (fb + 40#64) i)
  fg : ∀ i < 8, Foot F.data (Addr.add (aR S + 40#64) i)
  fb40 : ∀ i < 8, Foot F.data (Addr.add (S - 8 - 8 - 8 - 8 - 8) i)
  fb32 : ∀ i < 8, Foot F.data (Addr.add (S - 8 - 8 - 8 - 8) i)
  fb24 : ∀ i < 8, Foot F.data (Addr.add (S - 8 - 8 - 8) i)
  fb16 : ∀ i < 8, Foot F.data (Addr.add (S - 8 - 8) i)
  fb8 : ∀ i < 8, Foot F.data (Addr.add (S - 8) i)
  hl : ∀ i < 8, Foot F.data (Addr.add S i)
  hr8 : ∀ i < 8, Foot Wl (Addr.add (aR S - 8) i)
  f15 : ∀ i < 1, Foot F.data (Addr.add (aR S + 15#64) i)
  f16 : ∀ i < 2, Foot F.data (Addr.add (aR S + 16#64) i)
  f24 : ∀ i < 8, Foot F.data (Addr.add (aR S + 24#64) i)
  w16 : ∀ i < 4, Foot Wl (Addr.add (aR S + 16#64) i)
  w24 : ∀ i < 8, Foot Wl (Addr.add (aR S + 24#64) i)
  fa : ∀ i < 8, Foot F.data (Addr.add g0.rdi i)
  z16 : ∀ W bs, I W → I (Vst W (aR S + 16#64) bs)
  z24 : ∀ W bs, I W → I (Vst W (aR S + 24#64) bs)
  har : ∀ W, I W → rdq(W, g0.rdi) = ar
  fvp : ∀ i < 8, Foot F.data (Addr.add ar i)
  fv : ∀ W, I W → ∀ i < 8, Foot F.data (Addr.add (rdq(W, ar) + 48#64) i)
  htg : ∀ W, I W → rdq(W, rdq(W, ar) + 48#64) = eG
  cO : ∃ code : List Byte, CodeIn L 0x44d710#64 code ∧ 0 < code.length
  cG : ∃ code : List Byte, CodeIn L eG code ∧ 0 < code.length
  cX : ∃ code : List Byte, CodeIn L 0x456f60#64 code ∧ 0 < code.length
  cT : ∃ code : List Byte, CodeIn L 0x44d9b0#64 code ∧ 0 < code.length
  cP : ∃ code : List Byte, CodeIn L 0x44db10#64 code ∧ 0 < code.length
  kO : ∀ W, I W → KC prof F Wl L s₀ o gev gP gE S I 0x44d710#64 145 W
    (fun g => g.rdi = g0.rdx ∧ g.rsi = g0.rdi + 72#64)
  kG : ∀ W, I W → KC prof F Wl L s₀ o gev gP gE S I eG 182 W
    (fun g => g.rdi = ar ∧ g.rsi = BitVec.setWidth 64 (BitVec.setWidth 32 g0.rsi) ∧ g.rdx = 5#64 ∧
      g.rcx = aR S + 16#64)
  kX : ∀ W, I W → KC prof F Wl L s₀ o gev gP gE S I 0x456f60#64 213 W (fun g => g.rdi = aR S + 16#64)
  kT : ∀ W, I W → KC prof F Wl L s₀ o gev gP gE S I 0x44d9b0#64 248 W (fun g => g.rdi = g0.rdx)
  kP : ∀ W, I W → KC prof F Wl L s₀ o gev gP gE S I 0x44db10#64 261 W
    (fun g => g.rdi = g0.rdx ∧ g.rsi = rdq(W, aR S + 24#64))
  kr : ∀ (W : Addr → Byte) (Z' : State) (t' : Nat), KeptW Wl s₀ Z' → Agree F Z'.proc.mm.mem W →
    Z'.cpu.rip = e₂.add j₂ → Z'.cpu.gpr.rsp = S + 8 → KS g0 Z'.cpu.gpr → I W → GoG prof L o gev gP gE Z' t'

/-! ## The pieces -/

section Pieces
variable {F : Footprint} {Wl : List Rgn}

/-- The prologue: the pushes, `r13d` = `index`, `rbp` = `result`, `rbx` = `this`, `rdi` = `Archive`, the frame, the
stack guard stored (its value named `cn`), `result.Empty ()` (the 4 bytes at `result + 8` and at `result._chars` =
`ca`; their bytes named `b1`, `b2`), `rdx` = `&isDir`: to the `call` at 65. -/
theorem vc_0 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} {cn ca : BitVec 64}
    (hcn : rdq(P5 V g, fb + 40#64) = cn)
    (hca : rdq(Vst (P5 V g) (aR g.rsp + 40#64) (toBytesLE cn 8), g.rdx) = ca)
    (hs1 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8) i)) (hs2 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8) i))
    (hs3 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8 - 8) i))
    (hs4 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8 - 8 - 8) i))
    (hs5 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8 - 8 - 8 - 8) i))
    (hcl : ∀ i < 8, Foot F.data (Addr.add (fb + 40#64) i))
    (hw : ∀ i < 8, Foot Wl (Addr.add (aR g.rsp + 40#64) i))
    (fa : ∀ i < 8, Foot F.data (Addr.add g.rdi i)) (fr0 : ∀ i < 8, Foot F.data (Addr.add g.rdx i))
    (wl8 : ∀ i < 4, Foot Wl (Addr.add (g.rdx + 8#64) i)) (wca : ∀ i < 4, Foot Wl (Addr.add ca i))
    (h : ∀ g' (b1 b2 : List Byte), g'.rsp = aR g.rsp → g'.rbx = g.rdi → g'.rbp = g.rdx →
      g'.r13 = BitVec.setWidth 64 (BitVec.setWidth 32 g.rsi) → g'.r15 = g.r15 → g'.rdi = rdq(P5 V g, g.rdi) →
      g'.rsi = g.rsi → g'.rdx = aR g.rsp + 15#64 → ∀ fl,
      Q 65 g' fl (Vst (Vst (Vst (P5 V g) (aR g.rsp + 40#64) (toBytesLE cn 8)) (g.rdx + 8#64) b1) ca b2)) :
    W_0 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [aR, P5] at hcn hca hs1 hs2 hs3 hs4 hs5 hw fa fr0 wl8 h ⊢
  wpx [W_0, o0, Op.ldf, hcn, hca]
  all_goals repeat' (first
    | refine h _ _ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ _
    | with_reducible rfl
    | with_reducible exact hs1
    | with_reducible exact hs2
    | with_reducible exact hs3
    | with_reducible exact hs4
    | with_reducible exact hs5
    | with_reducible exact hcl
    | with_reducible exact hw
    | with_reducible exact fa
    | with_reducible exact fr0
    | with_reducible exact wl8
    | with_reducible exact wca
    | apply And.intro
    | intro _)

/-- `r12d` = `Archive_IsItem_Dir`'s result: not 0, or `isDir` 0 … to 84; else `rsi` = `this + 72`, `rdi` = `result`,
`r14` = `&prop`: to the `call` at 140. -/
theorem vc_70 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (f15 : ∀ i < 1, Foot F.data (Addr.add (g.rsp + 15#64) i))
    (h84 : ∀ g', Fr g g' → ∀ fl, Q 84 g' fl V)
    (h140 : ∀ g', Fr g g' → g'.rsi = g.rbx + 72#64 → g'.rdi = g.rbp → g'.r14 = g.rsp + 16#64 → ∀ fl,
      Q 140 g' fl V) :
    W_70 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at f15 h84 h140 ⊢
  wpx [W_70, W_77, W_128, o1, o2, o5, Op.cmpmi]
  all_goals repeat' (first
    | refine h84 _ ?_ _
    | refine h140 _ ?_ ?_ ?_ ?_ _
    | with_reducible rfl
    | with_reducible exact f15
    | apply And.intro
    | intro _)

/-- The stack guard checked (as at `fs:0x28`: `jne` not taken), `add rsp, 0x30`, the five pops, to the `ret`. -/
theorem vc_84 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (hc : rdq(V, g.rsp + 40#64) = rdq(V, fb + 40#64)) (f40 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 40#64) i))
    (fcl : ∀ i < 8, Foot F.data (Addr.add (fb + 40#64) i))
    (f1 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 48#64) i))
    (f2 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 48#64 + 8) i))
    (f3 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 48#64 + 8 + 8) i))
    (f4 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 48#64 + 8 + 8 + 8) i))
    (f5 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 48#64 + 8 + 8 + 8 + 8) i))
    (h : ∀ g', g'.rsp = g.rsp + 48#64 + 8 + 8 + 8 + 8 + 8 → g'.rbx = rdq(V, g.rsp + 48#64) →
      g'.rbp = rdq(V, g.rsp + 48#64 + 8) → g'.r12 = rdq(V, g.rsp + 48#64 + 8 + 8) →
      g'.r13 = rdq(V, g.rsp + 48#64 + 8 + 8 + 8) → g'.r14 = rdq(V, g.rsp + 48#64 + 8 + 8 + 8 + 8) →
      g'.r15 = g.r15 → ∀ fl, Q 119 g' fl V) :
    W_84 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hc f40 f1 f2 f3 f4 f5 h ⊢
  have z0 : ((0#64 : BitVec 64) == 0) = true := by decide
  wpx [W_84, W_104, o3, o4, Op.xormf, hc, BitVec.xor_self, z0, decide_true, Bool.not_true, Bool.false_eq_true,
    false_implies, eq_self_iff_true, true_implies]
  all_goals repeat' (first
    | refine h _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ _
    | with_reducible rfl
    | with_reducible exact f40
    | with_reducible exact fcl
    | with_reducible exact f1
    | with_reducible exact f2
    | with_reducible exact f3
    | with_reducible exact f4
    | with_reducible exact f5
    | apply And.intro
    | intro _)

/-- `rdi` = `Archive`, `rcx` = `&prop`, `edx` = `kpidExtension` (5), `prop` cleared (its 4 and 8 bytes named `b1`,
`b2`), `esi` = `index`, `rax` = the vtable: to the `call` at 179. -/
theorem vc_145 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} {ar : Addr}
    (har : rdq(V, g.rbx) = ar) (fa : ∀ i < 8, Foot F.data (Addr.add g.rbx i))
    (w16 : ∀ i < 4, Foot Wl (Addr.add (g.rsp + 16#64) i)) (w24 : ∀ i < 8, Foot Wl (Addr.add (g.rsp + 24#64) i))
    (fvp : ∀ i < 8, Foot F.data (Addr.add ar i))
    (h : ∀ g' (b1 b2 : List Byte), Fr g g' → g'.r14 = g.r14 → g'.rdi = ar → g'.rcx = g.r14 → g'.rdx = 5#64 →
      g'.rsi = BitVec.setWidth 64 (BitVec.setWidth 32 g.r13) →
      g'.rax = rdq(Vst (Vst V (g.rsp + 16#64) b1) (g.rsp + 24#64) b2, ar) → ∀ fl,
      Q 179 g' fl (Vst (Vst V (g.rsp + 16#64) b1) (g.rsp + 24#64) b2)) :
    W_145 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at har fa w16 w24 h ⊢
  wpx [W_145, o6, har, BitVec.reduceSetWidth]
  all_goals repeat' (first
    | refine h _ _ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ _
    | with_reducible rfl
    | with_reducible exact fa
    | with_reducible exact w16
    | with_reducible exact w24
    | with_reducible exact fvp
    | apply And.intro
    | intro _)

/-- `r12d` = `GetProperty`'s result: not 0 to 205; `vt` = `VT_BSTR` (8): `rdi` = `result`, to the `call` at 243;
another `vt` not 0: `r12d` = `E_FAIL`, to 205; else 205. -/
theorem vc_182 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (f16 : ∀ i < 2, Foot F.data (Addr.add (g.rsp + 16#64) i))
    (h205 : ∀ g', Fr g g' → g'.r14 = g.r14 → ∀ fl, Q 205 g' fl V)
    (h243 : ∀ g', Fr g g' → g'.r14 = g.r14 → g'.rdi = g.rbp → ∀ fl, Q 243 g' fl V) :
    W_182 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at f16 h205 h243 ⊢
  wpx [W_182, W_189, W_200, W_224, W_240, o1, o7, o8, o10, o11]
  all_goals repeat' (first
    | refine h205 _ ?_ ?_ _
    | refine h243 _ ?_ ?_ ?_ _
    | with_reducible rfl
    | with_reducible exact f16
    | apply And.intro
    | intro _)

/-- `rdi` = `&prop`: to the `call` at 208. -/
theorem vc_205 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (h : ∀ g', Fr g g' → g'.r14 = g.r14 → g'.rdi = g.r14 → ∀ fl, Q 208 g' fl V) :
    W_205 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h ⊢
  wpx [W_205, o9]
  all_goals repeat' (first
    | refine h _ ?_ ?_ ?_ _
    | with_reducible rfl
    | apply And.intro
    | intro _)

/-- `jmp` to 84. -/
theorem vc_213 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} (h : ∀ fl, Q 84 g fl V) :
    W_213 fb F Wl Q g f V := h _

/-- `rsi` = `prop.bstrVal`, `rdi` = `result`: to the `call` at 256. -/
theorem vc_248 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (f24 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 24#64) i))
    (h : ∀ g', Fr g g' → g'.r14 = g.r14 → g'.rsi = rdq(V, g.rsp + 24#64) → g'.rdi = g.rbp → ∀ fl,
      Q 256 g' fl V) :
    W_248 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at f24 h ⊢
  wpx [W_248, o12]
  all_goals repeat' (first
    | refine h _ ?_ ?_ ?_ ?_ _
    | with_reducible rfl
    | with_reducible exact f24
    | apply And.intro
    | intro _)

/-- `jmp` to 205. -/
theorem vc_261 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} (h : ∀ fl, Q 205 g fl V) :
    W_261 fb F Wl Q g f V := h _

end Pieces

/-! ## The runs from the cut points -/

section Runs
variable {prof : Profile} {F : Footprint} {Wl : List Rgn} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {fb S : Addr} {g0 : Gprs} {e₂ : Addr} {code₂ : List Byte} {j₂ : Nat} {I : (Addr → Byte) → Prop}
  {ar eG : Addr}
  {Y : State} {t : Nat} {W : Addr → Byte}

/-- A `call` at `j` (`rsp` = `aR S`, the bytes `W`) of the callee `k`, and from its return at `j + 5`. -/
theorem callK (E : Ev prof F Wl L s₀ o gev gP gE fb S g0 e₂ code₂ j₂ I ar eG) {U : State} {t₁ : Nat}
    {j R : Nat} {ent : Addr} {A : Gprs → Prop} (hKU : KeptW Wl s₀ U)
    (hAU : Agree F U.proc.mm.mem W) (hrU : U.cpu.rip = gdp_at.add j) (hs : U.cpu.gpr.rsp = aR S)
    (hj : j < gdp.length) (hd : Dec prof.feat gdp j (FV7z.mk .call 64 [.rel R] 5))
    (htgt : gdp_at.add (j + 5) + BitVec.ofNat 64 R = ent)
    (hc : ∃ code : List Byte, CodeIn L ent code ∧ 0 < code.length)
    (k : KC prof F Wl L s₀ o gev gP gE S I ent (j + 5) W A) (hA : A (U.cpu.gpr.set 4 (aR S - 8)))
    (h : ∀ (Z : State) (W' : Addr → Byte) (t'' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem W' →
      Z.cpu.rip = gdp_at.add (j + 5) → Z.cpu.gpr.rsp = aR S → KS U.cpu.gpr Z.cpu.gpr → I W' →
      GoG prof L o gev gP gE Z t'') :
    GoG prof L o gev gP gE U t₁ := by
  have hU : U.cpu.gpr.rsp - 8 = aR S - 8 := by rw [hs]
  obtain ⟨cc, hinc, hcc⟩ := hc
  refine E.c.s_call hKU hAU E.hin hj hrU hd hinc hcc htgt (by rw [hU]; exact E.hr8) ?_
  rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
  rw [hU] at hA₂
  refine k Y₂ t₂ hK₂ hA₂ hr₂ (by rw [hg₂]; exact hU) (by rw [hg₂, hU]; exact hA) ?_
  intro Z W' t₃ hKZ hAZ hrZ hsZ hkZ hNZ
  rw [hg₂] at hkZ
  exact h Z W' t₃ hKZ hAZ hrZ hsZ hkZ hNZ

/-- From 84 (`rsp` = `aR S`, `r15` as at the entry, the bytes `W` with `I`): the guard's check, the epilogue, the
`ret`, to `kr`. -/
theorem tail84 (E : Ev prof F Wl L s₀ o gev gP gE fb S g0 e₂ code₂ j₂ I ar eG) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = gdp_at.add 84) (hs : Y.cpu.gpr.rsp = aR S)
    (h15 : Y.cpu.gpr.r15 = g0.r15) (hIW : I W) :
    GoG prof L o gev gP gE Y t := by
  obtain ⟨s1, s2, s3, s4, s5, s6, s7⟩ := E.hI W hIW
  have e1 : rdq(W, Y.cpu.gpr.rsp + 48#64) = g0.rbx := by rw [hs, q1]; exact s1
  have e2 : rdq(W, Y.cpu.gpr.rsp + 48#64 + 8) = g0.rbp := by rw [hs, q2]; exact s2
  have e3 : rdq(W, Y.cpu.gpr.rsp + 48#64 + 8 + 8) = g0.r12 := by rw [hs, q3]; exact s3
  have e4 : rdq(W, Y.cpu.gpr.rsp + 48#64 + 8 + 8 + 8) = g0.r13 := by rw [hs, q4]; exact s4
  have e5 : rdq(W, Y.cpu.gpr.rsp + 48#64 + 8 + 8 + 8 + 8) = g0.r14 := by rw [hs, q5]; exact s5
  refine (c_84 prof fb).run E.c E.hfs E.hin (fun j' g' _ V' => j' = 119 ∧ V' = W ∧
      g'.rsp = Y.cpu.gpr.rsp + 48#64 + 8 + 8 + 8 + 8 + 8 ∧ g'.rbx = rdq(W, Y.cpu.gpr.rsp + 48#64) ∧
      g'.rbp = rdq(W, Y.cpu.gpr.rsp + 48#64 + 8) ∧ g'.r12 = rdq(W, Y.cpu.gpr.rsp + 48#64 + 8 + 8) ∧
      g'.r13 = rdq(W, Y.cpu.gpr.rsp + 48#64 + 8 + 8 + 8) ∧ g'.r14 = rdq(W, Y.cpu.gpr.rsp + 48#64 + 8 + 8 + 8 + 8) ∧
      g'.r15 = Y.cpu.gpr.r15)
    hK hA hr
    (vc_84 (by rw [hs]; exact s7) (by rw [hs]; exact E.fg) E.hcl (by rw [hs, q1]; exact E.fb40)
      (by rw [hs, q2]; exact E.fb32) (by rw [hs, q3]; exact E.fb24) (by rw [hs, q4]; exact E.fb16)
      (by rw [hs, q5]; exact E.fb8)
      fun _ a b d e f g h _ => ⟨rfl, rfl, a, b, d, e, f, g, h⟩) ?_
  rintro j' g fl V₁ ⟨rfl, hV₁, gs, gx, gp, g12, g13, g14, g15⟩ U t₁ hKU hAU hrU hgU -
  subst V₁ hgU
  have hsU : U.cpu.gpr.rsp = S := by rw [gs, hs]; exact q6 S
  refine E.c.s_ret hKU hAU E.hin (lt_len (by decide)) hrU (ret_119 _) (by rw [hsU]; exact E.hl) E.hin₂ E.h₂
    (by rw [hsU]; exact s6) ?_
  rintro Z' t₂ hKZ' hAZ' ⟨hrZ', hgZ'⟩
  refine E.kr W Z' t₂ hKZ' hAZ' hrZ' ?_ ?_ hIW
  · rw [hgZ']
    show U.cpu.gpr.rsp + 8 = _
    rw [hsU]
  · rw [hgZ']
    exact ⟨gx.trans e1, gp.trans e2, g12.trans e3, g13.trans e4, g14.trans e5, g15.trans h15⟩

/-- From 213 (back from `prop.Clear ()`): `jmp` to 84. -/
theorem from213 (E : Ev prof F Wl L s₀ o gev gP gE fb S g0 e₂ code₂ j₂ I ar eG) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = gdp_at.add 213) (hs : Y.cpu.gpr.rsp = aR S)
    (h15 : Y.cpu.gpr.r15 = g0.r15) (hIW : I W) :
    GoG prof L o gev gP gE Y t := by
  refine (c_213 prof fb).run E.c E.hfs E.hin (fun j' g' _ V' => j' = 84 ∧ g' = Y.cpu.gpr ∧ V' = W)
    hK hA hr (vc_213 fun _ => ⟨rfl, rfl, rfl⟩) ?_
  rintro j' g fl V₁ ⟨rfl, rfl, hV₁⟩ U t₁ hKU hAU hrU hgU -
  subst V₁
  exact tail84 E hKU hAU hrU (by rw [hgU]; exact hs) (by rw [hgU]; exact h15) hIW

/-- From 205 (`r14` = `&prop`): `prop.Clear ()` (`kX`), from its return 213. -/
theorem from205 (E : Ev prof F Wl L s₀ o gev gP gE fb S g0 e₂ code₂ j₂ I ar eG) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = gdp_at.add 205) (hm : Fm S g0 Y.cpu.gpr)
    (h14 : Y.cpu.gpr.r14 = aR S + 16#64) (hIW : I W) :
    GoG prof L o gev gP gE Y t := by
  refine (c_205 prof fb).run E.c E.hfs E.hin (fun j' g' _ V' => j' = 208 ∧ V' = W ∧ Fr Y.cpu.gpr g' ∧
      g'.rdi = Y.cpu.gpr.r14) hK hA hr (vc_205 fun _ a _ d _ => ⟨rfl, rfl, a, d⟩) ?_
  rintro j' g fl V₁ ⟨rfl, hV₁, gf, gdi⟩ U t₁ hKU hAU hrU hgU -
  subst V₁ hgU
  have hmU := Fm.fr hm gf
  refine callK E hKU hAU hrU hmU.1 (lt_len (by decide)) (call_208 _) tgt_208 E.cX (E.kX _ hIW)
    (gdi.trans h14) ?_
  intro Z W' t₃ hKZ hAZ hrZ hsZ hkZ hIZ
  exact from213 E hKZ hAZ hrZ hsZ (fm_ret hmU hsZ hkZ).2.2.2.2 hIZ

/-- From 261 (back from `result += prop.bstrVal`): `jmp` to 205. -/
theorem from261 (E : Ev prof F Wl L s₀ o gev gP gE fb S g0 e₂ code₂ j₂ I ar eG) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = gdp_at.add 261) (hm : Fm S g0 Y.cpu.gpr)
    (h14 : Y.cpu.gpr.r14 = aR S + 16#64) (hIW : I W) :
    GoG prof L o gev gP gE Y t := by
  refine (c_261 prof fb).run E.c E.hfs E.hin (fun j' g' _ V' => j' = 205 ∧ g' = Y.cpu.gpr ∧ V' = W)
    hK hA hr (vc_261 fun _ => ⟨rfl, rfl, rfl⟩) ?_
  rintro j' g fl V₁ ⟨rfl, rfl, hV₁⟩ U t₁ hKU hAU hrU hgU -
  subst V₁
  exact from205 E hKU hAU hrU (by rw [hgU]; exact hm) (by rw [hgU]; exact h14) hIW

/-- From 248 (back from `result.Add_Dot ()`): `result += prop.bstrVal` (`kP`), from its return 261. -/
theorem from248 (E : Ev prof F Wl L s₀ o gev gP gE fb S g0 e₂ code₂ j₂ I ar eG) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = gdp_at.add 248) (hm : Fm S g0 Y.cpu.gpr)
    (h14 : Y.cpu.gpr.r14 = aR S + 16#64) (hIW : I W) :
    GoG prof L o gev gP gE Y t := by
  have e24 : rdq(W, Y.cpu.gpr.rsp + 24#64) = rdq(W, aR S + 24#64) := by rw [hm.1]
  refine (c_248 prof fb).run E.c E.hfs E.hin (fun j' g' _ V' => j' = 256 ∧ V' = W ∧ Fr Y.cpu.gpr g' ∧
      g'.r14 = Y.cpu.gpr.r14 ∧ g'.rsi = rdq(W, Y.cpu.gpr.rsp + 24#64) ∧ g'.rdi = Y.cpu.gpr.rbp) hK hA hr
    (vc_248 (by rw [hm.1]; exact E.f24) fun _ a b d e _ => ⟨rfl, rfl, a, b, d, e⟩) ?_
  rintro j' g fl V₁ ⟨rfl, hV₁, gf, g14, gsi, gdi⟩ U t₁ hKU hAU hrU hgU -
  subst V₁ hgU
  have hmU := Fm.fr hm gf
  refine callK E hKU hAU hrU hmU.1 (lt_len (by decide)) (call_256 _) tgt_256 E.cP (E.kP _ hIW)
    ⟨gdi.trans hm.2.2.1, gsi.trans e24⟩ ?_
  intro Z W' t₃ hKZ hAZ hrZ hsZ hkZ hIZ
  exact from261 E hKZ hAZ hrZ (fm_ret hmU hsZ hkZ) (hkZ.2.2.2.2.1.trans (g14.trans h14)) hIZ

/-- From 182 (back from `GetProperty`): to 205, or `result.Add_Dot ()` (`kT`) and from its return 248. -/
theorem from182 (E : Ev prof F Wl L s₀ o gev gP gE fb S g0 e₂ code₂ j₂ I ar eG) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = gdp_at.add 182) (hm : Fm S g0 Y.cpu.gpr)
    (h14 : Y.cpu.gpr.r14 = aR S + 16#64) (hIW : I W) :
    GoG prof L o gev gP gE Y t := by
  refine (c_182 prof fb).run E.c E.hfs E.hin (fun j' g' _ V' => V' = W ∧ Fr Y.cpu.gpr g' ∧
      g'.r14 = Y.cpu.gpr.r14 ∧ (j' = 205 ∨ j' = 243 ∧ g'.rdi = Y.cpu.gpr.rbp)) hK hA hr
    (vc_182 (by rw [hm.1]; exact E.f16) (fun _ a b _ => ⟨rfl, a, b, Or.inl rfl⟩)
      (fun _ a b d _ => ⟨rfl, a, b, Or.inr ⟨rfl, d⟩⟩)) ?_
  rintro j' g fl V₁ ⟨hV₁, gf, g14, hj⟩ U t₁ hKU hAU hrU hgU -
  subst V₁ hgU
  have hmU := Fm.fr hm gf
  have h14U : U.cpu.gpr.r14 = aR S + 16#64 := g14.trans h14
  rcases hj with rfl | ⟨rfl, gdi⟩
  · exact from205 E hKU hAU hrU hmU h14U hIW
  · refine callK E hKU hAU hrU hmU.1 (lt_len (by decide)) (call_243 _) tgt_243 E.cT (E.kT _ hIW)
      (gdi.trans hm.2.2.1) ?_
    intro Z W' t₃ hKZ hAZ hrZ hsZ hkZ hIZ
    exact from248 E hKZ hAZ hrZ (fm_ret hmU hsZ hkZ) (hkZ.2.2.2.2.1.trans h14U) hIZ

/-- From 145 (back from `result = DefaultName`, `r14` = `&prop`): `prop` cleared, `GetProperty` through the vtable
(179, `Seg.s_callM`, `kG`), from its return 182. -/
theorem from145 (E : Ev prof F Wl L s₀ o gev gP gE fb S g0 e₂ code₂ j₂ I ar eG) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = gdp_at.add 145) (hm : Fm S g0 Y.cpu.gpr)
    (h14 : Y.cpu.gpr.r14 = aR S + 16#64) (hIW : I W) :
    GoG prof L o gev gP gE Y t := by
  have har : rdq(W, Y.cpu.gpr.rbx) = ar := by rw [hm.2.1]; exact E.har W hIW
  have z16 : ∀ W bs, I W → I (Vst W (Y.cpu.gpr.rsp + 16#64) bs) := by rw [hm.1]; exact E.z16
  have z24 : ∀ W bs, I W → I (Vst W (Y.cpu.gpr.rsp + 24#64) bs) := by rw [hm.1]; exact E.z24
  refine (c_145 prof fb).run E.c E.hfs E.hin (fun j' g' _ V' => j' = 179 ∧ I V' ∧ Fr Y.cpu.gpr g' ∧
      g'.r14 = Y.cpu.gpr.r14 ∧ g'.rdi = ar ∧ g'.rcx = Y.cpu.gpr.r14 ∧ g'.rdx = 5#64 ∧
      g'.rsi = BitVec.setWidth 64 (BitVec.setWidth 32 Y.cpu.gpr.r13) ∧ g'.rax = rdq(V', ar)) hK hA hr
    (vc_145 har (by rw [hm.2.1]; exact E.fa) (by rw [hm.1]; exact E.w16) (by rw [hm.1]; exact E.w24) E.fvp
      fun _ b1 b2 a b d e f k l _ => ⟨rfl, z24 _ b2 (z16 _ b1 hIW), a, b, d, e, f, k, l⟩) ?_
  rintro j' g fl V₁ ⟨rfl, hIV, gf, g14, gdi, gcx, gdx, gsi, ga⟩ U t₁ hKU hAU hrU hgU -
  subst hgU
  have hmU := Fm.fr hm gf
  have he : eaD U 0 48 = rdq(V₁, ar) + 48#64 := by
    show U.cpu.gpr.get (regOf 0) + BitVec.ofNat 64 48 = _
    rw [show U.cpu.gpr.get (regOf 0) = U.cpu.gpr.rax from rfl, ga]
  have hU : U.cpu.gpr.rsp - 8 = aR S - 8 := by rw [hmU.1]
  have e14 : U.cpu.gpr.r14 = aR S + 16#64 := g14.trans h14
  have esi : U.cpu.gpr.rsi = BitVec.setWidth 64 (BitVec.setWidth 32 g0.rsi) := by
    rw [gsi, hm.2.2.2.1, sw_64_32]
  obtain ⟨cg, hinG, hcg⟩ := E.cG
  refine E.c.s_callM hKU hAU E.hin (lt_len (by decide)) hrU (call_179 _) (by rw [he]; exact E.fv V₁ hIV) hinG
    hcg (by rw [he]; exact E.htg V₁ hIV) (by rw [hU]; exact E.hr8) ?_
  rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
  rw [hU] at hA₂
  refine E.kG V₁ hIV Y₂ t₂ hK₂ hA₂ hr₂ (by rw [hg₂]; exact hU)
    (by rw [hg₂]; exact ⟨gdi, esi, gdx, gcx.trans h14⟩) ?_
  intro Z W' t₃ hKZ hAZ hrZ hsZ hkZ hIZ
  rw [hg₂] at hkZ
  exact from182 E hKZ hAZ hrZ (fm_ret hmU hsZ hkZ) (hkZ.2.2.2.2.1.trans e14) hIZ

/-- From 70 (back from `Archive_IsItem_Dir`): to 84, or `result = DefaultName` (`kO`) and from its return 145. -/
theorem from70 (E : Ev prof F Wl L s₀ o gev gP gE fb S g0 e₂ code₂ j₂ I ar eG) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = gdp_at.add 70) (hm : Fm S g0 Y.cpu.gpr) (hIW : I W) :
    GoG prof L o gev gP gE Y t := by
  refine (c_70 prof fb).run E.c E.hfs E.hin (fun j' g' _ V' => V' = W ∧ Fr Y.cpu.gpr g' ∧
      (j' = 84 ∨ j' = 140 ∧ g'.rsi = Y.cpu.gpr.rbx + 72#64 ∧ g'.rdi = Y.cpu.gpr.rbp ∧
        g'.r14 = Y.cpu.gpr.rsp + 16#64)) hK hA hr
    (vc_70 (by rw [hm.1]; exact E.f15) (fun _ a _ => ⟨rfl, a, Or.inl rfl⟩)
      (fun _ a b d e _ => ⟨rfl, a, Or.inr ⟨rfl, b, d, e⟩⟩)) ?_
  rintro j' g fl V₁ ⟨hV₁, gf, hj⟩ U t₁ hKU hAU hrU hgU -
  subst V₁ hgU
  have hmU := Fm.fr hm gf
  rcases hj with rfl | ⟨rfl, gsi, gdi, g14⟩
  · exact tail84 E hKU hAU hrU hmU.1 hmU.2.2.2.2 hIW
  · have e72 : Y.cpu.gpr.rbx + 72#64 = g0.rdi + 72#64 := by rw [hm.2.1]
    have e16 : Y.cpu.gpr.rsp + 16#64 = aR S + 16#64 := by rw [hm.1]
    refine callK E hKU hAU hrU hmU.1 (lt_len (by decide)) (call_140 _) tgt_140 E.cO (E.kO _ hIW)
      ⟨gdi.trans hm.2.2.1, gsi.trans e72⟩ ?_
    intro Z W' t₃ hKZ hAZ hrZ hsZ hkZ hIZ
    exact from145 E hKZ hAZ hrZ (fm_ret hmU hsZ hkZ) (hkZ.2.2.2.2.1.trans (g14.trans e16)) hIZ

end Runs

variable {prof : Profile} {F : Footprint} {Wl : List Rgn} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {X : State} {t : Nat} {V : Addr → Byte}

/-- `CArc::GetItem_DefaultPath (index, result)` (`this` = `rdi`, `index` = `esi`, `result` = `rdx`) from its entry,
`fb` the `fs` base: the pushes' slots, the guard's slot, the locals, the calls' return address slot, `result`'s two
stores of 0, the callees as `KC` (the `call` at 65 among them), `Archive` and its `GetProperty` through `I`: to the
return address `e₂.add j₂` (`kr`). -/
theorem gdp_ok {fb : Addr} {I : (Addr → Byte) → Prop} {e₂ : Addr} {code₂ : List Byte} {j₂ : Nat}
    {ar eG : Addr}
    (c : Seg prof F Wl L s₀ o) (hfs : s₀.cpu.seg.fsBase = fb) (hin : CodeIn L gdp_at gdp)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = gdp_at)
    (hcl : ∀ i < 8, Foot F.data (Addr.add (fb + 40#64) i))
    (hs1 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8) i))
    (hs2 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8 - 8) i))
    (hs3 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8 - 8 - 8) i))
    (hs4 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8 - 8 - 8 - 8) i))
    (hs5 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8 - 8 - 8 - 8 - 8) i))
    (hw : ∀ i < 8, Foot Wl (Addr.add (aR X.cpu.gpr.rsp + 40#64) i))
    (hr8 : ∀ i < 8, Foot Wl (Addr.add (aR X.cpu.gpr.rsp - 8) i))
    (hl : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsp i))
    (hin₂ : CodeIn L e₂ code₂) (h₂ : j₂ < code₂.length)
    (f15 : ∀ i < 1, Foot F.data (Addr.add (aR X.cpu.gpr.rsp + 15#64) i))
    (w16 : ∀ i < 4, Foot Wl (Addr.add (aR X.cpu.gpr.rsp + 16#64) i))
    (w24 : ∀ i < 8, Foot Wl (Addr.add (aR X.cpu.gpr.rsp + 24#64) i))
    (fa : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rdi i))
    (fr0 : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rdx i))
    (wl8 : ∀ i < 4, Foot Wl (Addr.add (X.cpu.gpr.rdx + 8#64) i))
    (wca : ∀ i < 4, Foot Wl (Addr.add (rdq(V1 fb V X.cpu.gpr, X.cpu.gpr.rdx)) i))
    (hI0 : I (V1 fb V X.cpu.gpr))
    (zL : ∀ W bs, I W → I (Vst W (X.cpu.gpr.rdx + 8#64) bs))
    (zC : ∀ W bs, I W → I (Vst W (rdq(V1 fb V X.cpu.gpr, X.cpu.gpr.rdx)) bs))
    (hI : ∀ W, I W → Stk fb W X.cpu.gpr.rsp X.cpu.gpr (e₂.add j₂))
    (z16 : ∀ W bs, I W → I (Vst W (aR X.cpu.gpr.rsp + 16#64) bs))
    (z24 : ∀ W bs, I W → I (Vst W (aR X.cpu.gpr.rsp + 24#64) bs))
    (har : ∀ W, I W → rdq(W, X.cpu.gpr.rdi) = ar)
    (fvp : ∀ i < 8, Foot F.data (Addr.add ar i))
    (fv : ∀ W, I W → ∀ i < 8, Foot F.data (Addr.add (rdq(W, ar) + 48#64) i))
    (htg : ∀ W, I W → rdq(W, rdq(W, ar) + 48#64) = eG)
    (cA : ∃ code : List Byte, CodeIn L 0x5d1670#64 code ∧ 0 < code.length)
    (cO : ∃ code : List Byte, CodeIn L 0x44d710#64 code ∧ 0 < code.length)
    (cG : ∃ code : List Byte, CodeIn L eG code ∧ 0 < code.length)
    (cX : ∃ code : List Byte, CodeIn L 0x456f60#64 code ∧ 0 < code.length)
    (cT : ∃ code : List Byte, CodeIn L 0x44d9b0#64 code ∧ 0 < code.length)
    (cP : ∃ code : List Byte, CodeIn L 0x44db10#64 code ∧ 0 < code.length)
    (k65 : ∀ W, I W → KC prof F Wl L s₀ o gev gP gE X.cpu.gpr.rsp I 0x5d1670#64 70 W
      (fun g => g.rdi = rdq(P5 V X.cpu.gpr, X.cpu.gpr.rdi) ∧ g.rsi = X.cpu.gpr.rsi ∧
        g.rdx = aR X.cpu.gpr.rsp + 15#64))
    (kO : ∀ W, I W → KC prof F Wl L s₀ o gev gP gE X.cpu.gpr.rsp I 0x44d710#64 145 W
      (fun g => g.rdi = X.cpu.gpr.rdx ∧ g.rsi = X.cpu.gpr.rdi + 72#64))
    (kG : ∀ W, I W → KC prof F Wl L s₀ o gev gP gE X.cpu.gpr.rsp I eG 182 W
      (fun g => g.rdi = ar ∧ g.rsi = BitVec.setWidth 64 (BitVec.setWidth 32 X.cpu.gpr.rsi) ∧ g.rdx = 5#64 ∧
        g.rcx = aR X.cpu.gpr.rsp + 16#64))
    (kX : ∀ W, I W → KC prof F Wl L s₀ o gev gP gE X.cpu.gpr.rsp I 0x456f60#64 213 W
      (fun g => g.rdi = aR X.cpu.gpr.rsp + 16#64))
    (kT : ∀ W, I W → KC prof F Wl L s₀ o gev gP gE X.cpu.gpr.rsp I 0x44d9b0#64 248 W
      (fun g => g.rdi = X.cpu.gpr.rdx))
    (kP : ∀ W, I W → KC prof F Wl L s₀ o gev gP gE X.cpu.gpr.rsp I 0x44db10#64 261 W
      (fun g => g.rdi = X.cpu.gpr.rdx ∧ g.rsi = rdq(W, aR X.cpu.gpr.rsp + 24#64)))
    (kr : ∀ (W : Addr → Byte) (Z' : State) (t' : Nat), KeptW Wl s₀ Z' → Agree F Z'.proc.mm.mem W →
      Z'.cpu.rip = e₂.add j₂ → Z'.cpu.gpr.rsp = X.cpu.gpr.rsp + 8 → KS X.cpu.gpr Z'.cpu.gpr → I W →
      GoG prof L o gev gP gE Z' t') :
    GoG prof L o gev gP gE X t := by
  have E : Ev prof F Wl L s₀ o gev gP gE fb X.cpu.gpr.rsp X.cpu.gpr e₂ code₂ j₂ I ar eG :=
    { c := c, hfs := hfs, hin := hin, hin₂ := hin₂, h₂ := h₂, hI := hI, hcl := hcl,
      fg := fun i hi => c.hws _ (hw i hi),
      fb40 := fun i hi => c.hws _ (hs5 i hi), fb32 := fun i hi => c.hws _ (hs4 i hi),
      fb24 := fun i hi => c.hws _ (hs3 i hi), fb16 := fun i hi => c.hws _ (hs2 i hi),
      fb8 := fun i hi => c.hws _ (hs1 i hi), hl := hl, hr8 := hr8, f15 := f15,
      f16 := fun i hi => c.hws _ (w16 i (by omega)), f24 := fun i hi => c.hws _ (w24 i hi),
      w16 := w16, w24 := w24, fa := fa, z16 := z16, z24 := z24, har := har, fvp := fvp, fv := fv, htg := htg,
      cO := cO, cG := cG, cX := cX, cT := cT, cP := cP, kO := kO, kG := kG, kX := kX, kT := kT, kP := kP, kr := kr }
  -- the prologue, to the first `call`
  have hrip' : X.cpu.rip = gdp_at.add 0 := by rw [addr_add_zero]; exact hrip
  refine (c_0 prof fb).run c hfs hin (fun j' g' _ V' => j' = 65 ∧ I V' ∧ Fm X.cpu.gpr.rsp X.cpu.gpr g' ∧
      g'.rdi = rdq(P5 V X.cpu.gpr, X.cpu.gpr.rdi) ∧ g'.rsi = X.cpu.gpr.rsi ∧ g'.rdx = aR X.cpu.gpr.rsp + 15#64)
    hK hA hrip'
    (vc_0 rfl rfl hs1 hs2 hs3 hs4 hs5 hcl hw fa fr0 wl8 wca
      fun _ b1 b2 a b d e i r s x _ => ⟨rfl, zC _ b2 (zL _ b1 hI0), ⟨a, b, d, e, i⟩, r, s, x⟩) ?_
  rintro j' g fl V₁ ⟨rfl, hIV, hm, gdi, gsi, gdx⟩ Y t₁ hKY hAY hrY hgY -
  subst hgY
  refine callK E hKY hAY hrY hm.1 (lt_len (by decide)) (call_65 _) tgt_65 cA (k65 _ hIV) ⟨gdi, gsi, gdx⟩ ?_
  intro Z W' t₃ hKZ hAZ hrZ hsZ hkZ hIZ
  exact from70 E hKZ hAZ hrZ (fm_ret hm hsZ hkZ) hIZ

end FV7z.Gdp
