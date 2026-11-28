import FV7z.Fch.Cuts
import FV7z.Lemmas.LeafRet
/-!
# `FindCharset` (PLAN.md §M, M1)

7-Zip 26.06's `FindCharset (parser, keyIndex, byteOnlyAllowed, defaultVal)` at `0x5a67b0` in `7zzs`
(`CPP/7zip/UI/Common/ArchiveCommandLine.cpp`; `objdump -d`), `parser` in `rdi`, `keyIndex` in `esi`,
`byteOnlyAllowed` in `dl`, `defaultVal` in `ecx`, `S` the stack pointer at the entry: `push r13; push r12; push rbp;
push rbx; sub rsp, 0x38` (`aR S`), the stack guard (`fs:0x28`) stored at `aR S + 40`, `rdx` = `3 keyIndex`
(`rxE`). At 37 the switch record `ia` (`parser._switches + 24 keyIndex`); its `ThereIs` byte 0 (`Off`): to 49.
Else (88) `rsi` = its last post string (`ps`), the `call` (105) of `UString (const UString &)` into `aR S + 16`
(`k1`). Back (110): the chars' first `wchar_t` 0 to 160, else the `call` (126) of `StringToUInt32 (chars,
aR S + 12)` (`k2`); back (131) either way to 160 or (a number below `0x10000`) to 252. At 160 the `call` of
`MyStringLower_Ascii (chars)` (`k3`); back (165) `r13` = 3 or 5 (`sbb` on `bl`: the table's length `n`), `r12` =
`rbp` = the table `0x77e400` (`tE`), `ebx` = 0, `rsi` = the first name, and the loop (224) at the index `k`: the
`call` (229) of `StringsAreEqual_Ascii (chars, name)` (`k4`); back (234) equal: `r12d` = the code page, to 252;
else `k + 1` (208) and `n` reached: the throw path 284 (`kx`); else `rsi` = the next name (`nm`) and 224. At 252
the chars, unless NULL, freed (`delete []`, 261, `k5`), to 49: the stack guard checked, `add rsp, 0x38` and the four
pops to the `ret` (82).

The memory is the caller's invariant `I` (as in `FV7z/Wst/Holds.lean`): it holds of the bytes after the prologue
(`hI0`), gives the stack (`hIs`: `Stk`, the saved registers, the return address and the guard equal to the one at
`fs:0x28`) and the chars readable (`fc`), and the callees keep it. Each callee is a hypothesis (`KC`: at its entry
with the return address at `aR S - 8`, the registers it is given, and from its return the frame `Fm`, `B`, `I`). The
loop is by induction on `n - k` (`k < n ≤ 5`, `Lr`). The return value is not followed. Not covered:
`__stack_chk_fail` (279) and the throw (284, `kx`).

- `aR`, `Stk`, `V1`, `V0c`, `V0`, `rxE`, `ia`, `ps`, `Off`, `tE`, `nm`, `Fm`, `Kf`, `Lr`, `KS`, `KC`: the frame,
  registers, bytes, contracts.
- `vc_0`, `vc_37`, `vc_49`, `vc_110`, `vc_131`, `vc_165`, `vc_224`, `vc_234m`, `vc_234e`, `vc_234c`, `vc_252`,
  `vc_266`: the pieces' verification conditions.
- `tail49`: the run from 49; `fch_ok`: the function.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Fch
set_option linter.unusedVariables false

/-! ## The instructions outside the blocks -/

/-- The `call` (105) of `UString (const UString &)`. -/
def pc1 : List Byte := [0xe8, 0xb2, 0x6d, 0xea, 0xff]
theorem pc1_0 : ∀ feat, Dec feat pc1 0 (FV7z.mk .call 64 [.rel 18446744073708137906] 5) := by intro feat f; rfl
theorem wc_105 : pc1 <+: fch.drop 105 := by decide +kernel
theorem call_105 (feat : Features) : Dec feat fch 105 (FV7z.mk .call 64 [.rel 18446744073708137906] 5) :=
  Dec.shift (j := 105) (k := 0) (pc1_0 feat) wc_105 (Nat.zero_le _)
theorem tgt_105 : fch_at.add (105 + 5) + BitVec.ofNat 64 18446744073708137906 = 0x44d5d0#64 := by decide

/-- The `call` (126) of `StringToUInt32`. -/
def pc2 : List Byte := [0xe8, 0x2d, 0xff, 0xff, 0xff]
theorem pc2_0 : ∀ feat, Dec feat pc2 0 (FV7z.mk .call 64 [.rel 18446744073709551405] 5) := by intro feat f; rfl
theorem wc_126 : pc2 <+: fch.drop 126 := by decide +kernel
theorem call_126 (feat : Features) : Dec feat fch 126 (FV7z.mk .call 64 [.rel 18446744073709551405] 5) :=
  Dec.shift (j := 126) (k := 0) (pc2_0 feat) wc_126 (Nat.zero_le _)
theorem tgt_126 : fch_at.add (126 + 5) + BitVec.ofNat 64 18446744073709551405 = 0x5a6760#64 := by decide

/-- The `call` (160) of `MyStringLower_Ascii`. -/
def pc3 : List Byte := [0xe8, 0xbb, 0x51, 0xea, 0xff]
theorem pc3_0 : ∀ feat, Dec feat pc3 0 (FV7z.mk .call 64 [.rel 18446744073708130747] 5) := by intro feat f; rfl
theorem wc_160 : pc3 <+: fch.drop 160 := by decide +kernel
theorem call_160 (feat : Features) : Dec feat fch 160 (FV7z.mk .call 64 [.rel 18446744073708130747] 5) :=
  Dec.shift (j := 160) (k := 0) (pc3_0 feat) wc_160 (Nat.zero_le _)
theorem tgt_160 : fch_at.add (160 + 5) + BitVec.ofNat 64 18446744073708130747 = 0x44ba10#64 := by decide

/-- The `call` (229) of `StringsAreEqual_Ascii`. -/
def pc4 : List Byte := [0xe8, 0xc6, 0x52, 0xea, 0xff]
theorem pc4_0 : ∀ feat, Dec feat pc4 0 (FV7z.mk .call 64 [.rel 18446744073708131014] 5) := by intro feat f; rfl
theorem wc_229 : pc4 <+: fch.drop 229 := by decide +kernel
theorem call_229 (feat : Features) : Dec feat fch 229 (FV7z.mk .call 64 [.rel 18446744073708131014] 5) :=
  Dec.shift (j := 229) (k := 0) (pc4_0 feat) wc_229 (Nat.zero_le _)
theorem tgt_229 : fch_at.add (229 + 5) + BitVec.ofNat 64 18446744073708131014 = 0x44bb60#64 := by decide

/-- The `call` (261) of `operator delete []`. -/
def pc5 : List Byte := [0xe8, 0x36, 0xac, 0x05, 0x00]
theorem pc5_0 : ∀ feat, Dec feat pc5 0 (FV7z.mk .call 64 [.rel 371766] 5) := by intro feat f; rfl
theorem wc_261 : pc5 <+: fch.drop 261 := by decide +kernel
theorem call_261 (feat : Features) : Dec feat fch 261 (FV7z.mk .call 64 [.rel 371766] 5) :=
  Dec.shift (j := 261) (k := 0) (pc5_0 feat) wc_261 (Nat.zero_le _)
theorem tgt_261 : fch_at.add (261 + 5) + BitVec.ofNat 64 371766 = 0x6014f0#64 := by decide

/-- The `ret`. -/
def pret : List Byte := [0xc3]
theorem pret_0 : ∀ feat, Dec feat pret 0 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem w_82 : pret <+: fch.drop 82 := by decide +kernel
theorem ret_82 (feat : Features) : Dec feat fch 82 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 82) (k := 0) (pret_0 feat) w_82 (Nat.zero_le _)

/-! ## The frame -/

/-- The stack pointer after the four pushes and `sub rsp, 0x38`. -/
abbrev aR (S : Addr) : Addr := S - 8 - 8 - 8 - 8 - 56#64

theorem e56 (S : Addr) : aR S + 56#64 = S - 8 - 8 - 8 - 8 := BitVec.sub_add_cancel _ _
theorem sa8 (x : Addr) : x - 8 + 8 = x := BitVec.sub_add_cancel _ _

/-- The stack (`fb` the `fs` base, `g0` the registers at the entry, `ra` the return address): the saved `r13`,
`r12`, `rbp`, `rbx`, the return address, the stack guard as at `fs:0x28`. -/
abbrev Stk (fb : Addr) (W : Addr → Byte) (S : Addr) (g0 : Gprs) (ra : Addr) : Prop :=
  rdq(W, S - 8) = g0.r13 ∧ rdq(W, S - 8 - 8) = g0.r12 ∧ rdq(W, S - 8 - 8 - 8) = g0.rbp ∧
    rdq(W, S - 8 - 8 - 8 - 8) = g0.rbx ∧ rdq(W, S) = ra ∧ rdq(W, aR S + 40#64) = rdq(W, fb + 40#64)

/-- The bytes after the pushes. -/
abbrev V1 (V : Addr → Byte) (g : Gprs) : Addr → Byte :=
  Vst (Vst (Vst (Vst V (g.rsp - 8) (toBytesLE g.r13 8)) (g.rsp - 8 - 8) (toBytesLE g.r12 8))
    (g.rsp - 8 - 8 - 8) (toBytesLE g.rbp 8)) (g.rsp - 8 - 8 - 8 - 8) (toBytesLE g.rbx 8)

/-- The bytes after the prologue, the guard's value `cn`. -/
abbrev V0c (V : Addr → Byte) (g : Gprs) (cn : BitVec 64) : Addr → Byte :=
  Vst (V1 V g) (aR g.rsp + 40#64) (toBytesLE cn 8)

/-- `V0c` with the guard read from `fs:0x28`. -/
abbrev V0 (fb : Addr) (V : Addr → Byte) (g : Gprs) : Addr → Byte := V0c V g rdq(V1 V g, fb + 40#64)

/-- `rdx` after `mov esi, esi; lea rdx, [rsi + rsi*2]` (`s` the entry's `rsi`). -/
abbrev rxE (s : BitVec 64) : Addr :=
  BitVec.setWidth 64 (BitVec.setWidth 32 s) + BitVec.setWidth 64 (BitVec.setWidth 32 s) * 2#64

/-- The switch record (`di` the parser, `dx` = `rxE`). -/
abbrev ia (V : Addr → Byte) (di dx : Addr) : Addr := rdq(V, di) + dx * 8#64

/-- The record's last post string (`PostStrings.Back ()`). -/
abbrev ps (V : Addr → Byte) (a : Addr) : Addr :=
  rdq(V, rdq(V, a + 8#64) + BitVec.setWidth 64 rdd(V, a + 16#64) * 8#64 + 18446744073709551608#64)

/-- The record's `ThereIs` byte 0. -/
abbrev Off (V : Addr → Byte) (a : Addr) : Prop := ofBytesLE 8 ((byteAddrs a 1).map V) = 0#8

/-- The table's entry `k` (a name, then the code page at 8). -/
def tE (k : Nat) : Addr := BitVec.ofNat 64 (7857152 + 16 * k)

/-- The name compared at the index `k`: the first one a constant, the next ones read from the table. -/
def nm (W : Addr → Byte) (k : Nat) : Addr := if k = 0 then 7239906#64 else rdq(W, tE k)

theorem nm_zero (W : Addr → Byte) : nm W 0 = 7239906#64 := if_pos rfl
theorem nm_succ (W : Addr → Byte) (k : Nat) : nm W (k + 1) = rdq(W, tE (k + 1)) := if_neg (Nat.succ_ne_zero k)

theorem tE0 : (7857152#64 : Addr) = tE 0 := by decide

theorem tE_succ {k : Nat} (hk : k < 5) : tE k + 16#64 = tE (k + 1) := by
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4) with rfl | rfl | rfl | rfl | rfl <;> decide

theorem bx_succ {k : Nat} (hk : k < 5) :
    BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 64 k) + 1#32) = BitVec.ofNat 64 (k + 1) := by
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4) with rfl | rfl | rfl | rfl | rfl <;> decide

theorem nx_succ {n k : Nat} (hk : k < n) (hn : n ≤ 5)
    (h : ¬ BitVec.setWidth 32 (BitVec.ofNat 64 n) = BitVec.setWidth 32 (BitVec.ofNat 64 k) + 1#32) : k + 1 < n := by
  rcases Nat.lt_or_ge (k + 1) n with h' | h'
  · exact h'
  · exfalso
    apply h
    have e : n = k + 1 := by omega
    subst e
    rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4) with rfl | rfl | rfl | rfl | rfl <;> decide

/-- The frame from 37 on: `rsp` = `aR S`, `r14`, `r15` as at the entry. -/
abbrev Fm (S : Addr) (g0 g : Gprs) : Prop := g.rsp = aR S ∧ g.r14 = g0.r14 ∧ g.r15 = g0.r15

/-- What a callee is given of the frame. -/
abbrev Kf (g0 g : Gprs) : Prop := g.r14 = g0.r14 ∧ g.r15 = g0.r15

/-- The loop's registers at the index `k` of `n`. -/
abbrev Lr (n k : Nat) (g : Gprs) : Prop :=
  g.rbx = BitVec.ofNat 64 k ∧ g.rbp = tE k ∧ g.r12 = 7857152#64 ∧ g.r13 = BitVec.ofNat 64 n

/-- The callee-saved registers as at the entry. -/
abbrev KS (g0 g : Gprs) : Prop :=
  g.rbx = g0.rbx ∧ g.rbp = g0.rbp ∧ g.r12 = g0.r12 ∧ g.r13 = g0.r13 ∧ g.r14 = g0.r14 ∧ g.r15 = g0.r15

/-- A callee from the `call` before `j` (entry `ent`, the bytes `W`, the registers `A`): at its entry, and from its
return at `j` with the frame, `B` and `N`, the run goes on to the goal. -/
def KC (prof : Profile) (F : Footprint) (Wl : List Rgn) (L : List (Addr × List Byte)) (s₀ : State) (o : Oracle)
    (gev : List Event) (gP : State → Nat → List Event → Prop) (gE : Outcome → List Event → Prop)
    (S : Addr) (g0 : Gprs) (ent : Addr) (j : Nat) (W : Addr → Byte) (A B : Gprs → Prop)
    (N : (Addr → Byte) → Prop) : Prop :=
  ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y →
    Agree F Y.proc.mm.mem (Vst W (aR S - 8) (toBytesLE (fch_at.add j) 8)) →
    Y.cpu.rip = ent → Y.cpu.gpr.rsp = aR S - 8 → A Y.cpu.gpr →
    (∀ (Z : State) (W' : Addr → Byte) (t'' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem W' →
      Z.cpu.rip = fch_at.add j → Fm S g0 Z.cpu.gpr → B Z.cpu.gpr → N W' → GoG prof L o gev gP gE Z t'') →
    GoG prof L o gev gP gE Y t'

/-! ## The pieces -/

variable {F : Footprint} {Wl : List Rgn}

/-- The prologue (the guard's value named `cn`), to 37. -/
theorem vc_0 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} {cn : BitVec 64}
    (hcn : rdq(V1 V g, fb + 40#64) = cn)
    (hs1 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8) i)) (hs2 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8) i))
    (hs3 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8 - 8) i))
    (hs4 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8 - 8 - 8) i))
    (hcl : ∀ i < 8, Foot F.data (Addr.add (fb + 40#64) i))
    (hw40 : ∀ i < 8, Foot Wl (Addr.add (aR g.rsp + 40#64) i))
    (h : ∀ g', g'.rsp = aR g.rsp → g'.rdi = g.rdi → g'.rdx = rxE g.rsi → g'.r14 = g.r14 → g'.r15 = g.r15 →
      ∀ fl, Q 37 g' fl (V0c V g cn)) :
    W_0 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [aR, V1, V0c, rxE] at hcn hs1 hs2 hs3 hs4 hw40 h ⊢
  wpx [W_0, o0, Op.ldf, hcn, BitVec.xor_self, BitVec.reduceSetWidth]
  all_goals repeat' (first
    | refine h _ ?_ ?_ ?_ ?_ ?_ _
    | with_reducible rfl
    | with_reducible exact hs1
    | with_reducible exact hs2
    | with_reducible exact hs3
    | with_reducible exact hs4
    | with_reducible exact hcl
    | with_reducible exact hw40
    | apply And.intro
    | intro _)

/-- The switch record's `ThereIs` byte: 0 to 49; else (88) `rdi` = `rsp + 16`, `rsi` = the last post string, to the
`call` (105). -/
theorem vc_37 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (fdi : ∀ i < 8, Foot F.data (Addr.add g.rdi i))
    (fth : ∀ i < 1, Foot F.data (Addr.add (ia V g.rdi g.rdx) i))
    (fp : ¬ Off V (ia V g.rdi g.rdx) → (∀ i < 4, Foot F.data (Addr.add (ia V g.rdi g.rdx + 16#64) i)) ∧
      (∀ i < 8, Foot F.data (Addr.add (ia V g.rdi g.rdx + 8#64) i)) ∧
      (∀ i < 8, Foot F.data (Addr.add (rdq(V, ia V g.rdi g.rdx + 8#64) +
        BitVec.setWidth 64 rdd(V, ia V g.rdi g.rdx + 16#64) * 8#64 + 18446744073709551608#64) i)))
    (h49 : ∀ g', g'.rsp = g.rsp → g'.r14 = g.r14 → g'.r15 = g.r15 → ∀ fl, Q 49 g' fl V)
    (h105 : ∀ g', g'.rsp = g.rsp → g'.rdi = g.rsp + 16#64 → g'.rsi = ps V (ia V g.rdi g.rdx) → g'.r14 = g.r14 →
      g'.r15 = g.r15 → ∀ fl, Q 105 g' fl V) :
    W_37 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [ia, ps, Off] at fdi fth fp h49 h105 ⊢
  by_cases h1 : ofBytesLE 8 ((byteAddrs (rdq(V, rdi) + rdx * 8#64) 1).map V) = 0#8
  · wpx [W_37, W_88, o1, o4, Op.cmpmi, h1, eq_self_iff_true, decide_false, decide_true, Bool.not_true,
      Bool.not_false, Bool.false_eq_true, Bool.true_eq_false, false_implies, implies_true]
    all_goals repeat' (first
      | refine h49 _ ?_ ?_ ?_ _
      | with_reducible rfl
      | with_reducible exact fdi
      | with_reducible exact fth
      | apply And.intro
      | intro _)
  · obtain ⟨f16, f8, fs⟩ := fp h1
    wpx [W_37, W_88, o1, o4, Op.cmpmi, h1, eq_self_iff_true, decide_false, decide_true, Bool.not_true,
      Bool.not_false, Bool.false_eq_true, Bool.true_eq_false, false_implies, implies_true]
    all_goals repeat' (first
      | refine h105 _ ?_ ?_ ?_ ?_ ?_ _
      | with_reducible rfl
      | with_reducible exact fdi
      | with_reducible exact fth
      | with_reducible exact f16
      | with_reducible exact f8
      | with_reducible exact fs
      | apply And.intro
      | intro _)

/-- The stack guard checked (as at `fs:0x28`: `jne` not taken), `add rsp, 0x38` and the four pops to the `ret`. -/
theorem vc_49 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (hc : rdq(V, g.rsp + 40#64) = rdq(V, fb + 40#64)) (f40 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 40#64) i))
    (fcl : ∀ i < 8, Foot F.data (Addr.add (fb + 40#64) i))
    (p1 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 56#64) i))
    (p2 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 56#64 + 8) i))
    (p3 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 56#64 + 8 + 8) i))
    (p4 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 56#64 + 8 + 8 + 8) i))
    (h : ∀ g', g'.rsp = g.rsp + 56#64 + 8 + 8 + 8 + 8 → g'.rbx = rdq(V, g.rsp + 56#64) →
      g'.rbp = rdq(V, g.rsp + 56#64 + 8) → g'.r12 = rdq(V, g.rsp + 56#64 + 8 + 8) →
      g'.r13 = rdq(V, g.rsp + 56#64 + 8 + 8 + 8) → g'.r14 = g.r14 → g'.r15 = g.r15 → ∀ fl, Q 82 g' fl V) :
    W_49 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hc f40 p1 p2 p3 p4 h ⊢
  have z0 : ((0#64 : BitVec 64) == 0) = true := by decide
  wpx [W_49, W_69, o2, o3, Op.xormf, hc, BitVec.xor_self, z0, decide_true, Bool.not_true, Bool.false_eq_true,
    false_implies, eq_self_iff_true, true_implies]
  all_goals repeat' (first
    | refine h _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ _
    | with_reducible rfl
    | with_reducible exact f40
    | with_reducible exact fcl
    | with_reducible exact p1
    | with_reducible exact p2
    | with_reducible exact p3
    | with_reducible exact p4
    | apply And.intro
    | intro _)

/-- Back from the copy: `rdi` = the chars; their first `wchar_t` 0 to 160, else `rsi` = `rsp + 12` to the `call`
(126). -/
theorem vc_110 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (f16 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 16#64) i))
    (fc : ∀ i < 4, Foot F.data (Addr.add (rdq(V, g.rsp + 16#64)) i))
    (h160 : ∀ g', g'.rsp = g.rsp → g'.rdi = rdq(V, g.rsp + 16#64) → g'.r14 = g.r14 → g'.r15 = g.r15 →
      ∀ fl, Q 160 g' fl V)
    (h126 : ∀ g', g'.rsp = g.rsp → g'.rdi = rdq(V, g.rsp + 16#64) → g'.rsi = g.rsp + 12#64 → g'.r14 = g.r14 →
      g'.r15 = g.r15 → ∀ fl, Q 126 g' fl V) :
    W_110 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at f16 fc h160 h126 ⊢
  wpx [W_110, W_121, o5, o6, BitVec.and_self]
  all_goals repeat' (first
    | refine h160 _ ?_ ?_ ?_ ?_ _
    | refine h126 _ ?_ ?_ ?_ ?_ ?_ _
    | with_reducible rfl
    | with_reducible exact f16
    | with_reducible exact fc
    | apply And.intro
    | intro _)

/-- Back from `StringToUInt32`: `al` 0 (`rdi` = the chars) to 160; else `r12d` = the number, `rdi` = the chars, and
to 252 (at most `0xffff`) or 160. -/
theorem vc_131 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (f16 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 16#64) i))
    (f12 : ∀ i < 4, Foot F.data (Addr.add (g.rsp + 12#64) i))
    (h160 : ∀ g', g'.rsp = g.rsp → g'.rdi = rdq(V, g.rsp + 16#64) → g'.r14 = g.r14 → g'.r15 = g.r15 →
      ∀ fl, Q 160 g' fl V)
    (h252 : ∀ g', g'.rsp = g.rsp → g'.rdi = rdq(V, g.rsp + 16#64) → g'.r14 = g.r14 → g'.r15 = g.r15 →
      ∀ fl, Q 252 g' fl V) :
    W_131 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at f16 f12 h160 h252 ⊢
  wpx [W_131, W_272, W_139, W_158, o7, o8, o9, o13, BitVec.and_self]
  all_goals repeat' (first
    | refine h160 _ ?_ ?_ ?_ ?_ _
    | refine h252 _ ?_ ?_ ?_ ?_ _
    | with_reducible rfl
    | with_reducible exact f16
    | with_reducible exact f12
    | apply And.intro
    | intro _)

/-- Back from `MyStringLower_Ascii`: `r13` = 5 (`bl` 0) or 3, `r12` = `rbp` = the table, `rsi` = the first name,
`ebx` = 0, to 224. -/
theorem vc_165 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (h : ∀ n : Nat, (n = 3 ∨ n = 5) → ∀ g', g'.rsp = g.rsp → g'.rbx = 0#64 → g'.rbp = 7857152#64 →
      g'.r12 = 7857152#64 → g'.r13 = BitVec.ofNat 64 n → g'.rsi = 7239906#64 → g'.r14 = g.r14 → g'.r15 = g.r15 →
      ∀ fl, Q 224 g' fl V) :
    W_165 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h ⊢
  by_cases hc : (BitVec.setWidth 8 rbx).toNat < 1
  · have hd : decide ((BitVec.setWidth 8 rbx).toNat < 1) = true := decide_eq_true hc
    have h5 := h 5 (Or.inr rfl)
    wpx [W_165, o10, hd, BitVec.ofBool_true, BitVec.sub_self, BitVec.xor_self, BitVec.reduceSetWidth,
      BitVec.reduceSub, BitVec.reduceAnd, BitVec.reduceAdd]
    all_goals repeat' (first
      | refine h5 _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ _
      | with_reducible rfl
      | apply And.intro
      | intro _)
  · have hd : decide ((BitVec.setWidth 8 rbx).toNat < 1) = false := decide_eq_false hc
    have h3 := h 3 (Or.inl rfl)
    wpx [W_165, o10, hd, BitVec.ofBool_false, BitVec.sub_self, BitVec.xor_self, BitVec.reduceSetWidth,
      BitVec.reduceSub, BitVec.reduceAnd, BitVec.reduceAdd]
    all_goals repeat' (first
      | refine h3 _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ _
      | with_reducible rfl
      | apply And.intro
      | intro _)

/-- The loop's head: `rdi` = the chars, to the `call` (229). -/
theorem vc_224 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (f16 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 16#64) i))
    (h : ∀ g', g'.rdi = rdq(V, g.rsp + 16#64) → g'.rsp = g.rsp → g'.rbx = g.rbx → g'.rbp = g.rbp →
      g'.r12 = g.r12 → g'.r13 = g.r13 → g'.rsi = g.rsi → g'.r14 = g.r14 → g'.r15 = g.r15 → ∀ fl, Q 229 g' fl V) :
    W_224 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at f16 h ⊢
  wpx [W_224, o13]
  all_goals repeat' (first
    | refine h _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ _
    | with_reducible rfl
    | with_reducible exact f16
    | apply And.intro
    | intro _)

/-- Not equal and `ebx + 1` short of `r13d`: `rbp += 16`, `rsi` = the next name, to 224. -/
theorem vc_234m {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (hz : (BitVec.setWidth 8 g.rax == 0) = true)
    (hp : decide (BitVec.setWidth 32 g.r13 = BitVec.setWidth 32 g.rbx + 1#32) = false)
    (fn : ∀ i < 8, Foot F.data (Addr.add (g.rbp + 16#64) i))
    (h : ∀ g', g'.rsp = g.rsp → g'.rbx = BitVec.setWidth 64 (BitVec.setWidth 32 g.rbx + 1#32) →
      g'.rbp = g.rbp + 16#64 → g'.r12 = g.r12 → g'.r13 = g.r13 → g'.rsi = rdq(V, g.rbp + 16#64) →
      g'.r14 = g.r14 → g'.r15 = g.r15 → ∀ fl, Q 224 g' fl V) :
    W_234 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hz hp fn h ⊢
  wpx [W_234, W_208, W_220, o7, o11, o12, hz, hp, BitVec.and_self, eq_self_iff_true, Bool.false_eq_true,
    Bool.true_eq_false, false_implies, implies_true]
  all_goals repeat' (first
    | refine h _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ _
    | with_reducible rfl
    | with_reducible exact fn
    | apply And.intro
    | intro _)

/-- Not equal and `ebx + 1` = `r13d`: to the throw path (284). -/
theorem vc_234e {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (hz : (BitVec.setWidth 8 g.rax == 0) = true)
    (hp : decide (BitVec.setWidth 32 g.r13 = BitVec.setWidth 32 g.rbx + 1#32) = true)
    (h : ∀ g', g'.rsp = g.rsp → g'.r14 = g.r14 → g'.r15 = g.r15 → ∀ fl, Q 284 g' fl V) :
    W_234 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hz hp h ⊢
  wpx [W_234, W_208, o7, o11, hz, hp, BitVec.and_self, eq_self_iff_true, Bool.false_eq_true,
    Bool.true_eq_false, false_implies, implies_true]
  all_goals repeat' (first
    | refine h _ ?_ ?_ ?_ _
    | with_reducible rfl
    | apply And.intro
    | intro _)

/-- Equal: `r12d` = the code page (`[r12 + 16 rbx + 8]`), `rdi` = the chars, to 252. -/
theorem vc_234c {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (hz : (BitVec.setWidth 8 g.rax == 0) = false)
    (f16 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 16#64) i))
    (ft : ∀ i < 4, Foot F.data (Addr.add (g.r12 + (g.rbx <<< 4) + 8#64) i))
    (h : ∀ g', g'.rsp = g.rsp → g'.rdi = rdq(V, g.rsp + 16#64) → g'.r14 = g.r14 → g'.r15 = g.r15 →
      ∀ fl, Q 252 g' fl V) :
    W_234 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hz f16 ft h ⊢
  wpx [W_234, W_238, o7, o14, Op.shl64, hz, BitVec.and_self, eq_self_iff_true, Bool.false_eq_true,
    Bool.true_eq_false, false_implies, implies_true]
  all_goals repeat' (first
    | refine h _ ?_ ?_ ?_ ?_ _
    | with_reducible rfl
    | with_reducible exact f16
    | with_reducible exact ft
    | apply And.intro
    | intro _)

/-- `test rdi, rdi`: NULL to 49, else to the `call` (261). -/
theorem vc_252 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (h49 : ∀ g', g'.rsp = g.rsp → g'.r14 = g.r14 → g'.r15 = g.r15 → ∀ fl, Q 49 g' fl V)
    (h261 : ∀ g', g'.rsp = g.rsp → g'.rdi = g.rdi → g'.r14 = g.r14 → g'.r15 = g.r15 → ∀ fl, Q 261 g' fl V) :
    W_252 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h49 h261 ⊢
  wpx [W_252, o15, BitVec.and_self]
  all_goals repeat' (first
    | refine h49 _ ?_ ?_ ?_ _
    | refine h261 _ ?_ ?_ ?_ ?_ _
    | with_reducible rfl
    | apply And.intro
    | intro _)

/-- `jmp 49`. -/
theorem vc_266 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} (h : ∀ fl, Q 49 g fl V) :
    W_266 fb F Wl Q g f V := h _

/-! ## The runs -/

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {X : State} {t : Nat} {V : Addr → Byte} {e₂ : Addr} {code₂ : List Byte} {j₂ : Nat}

/-- From 49 (the frame `Fm`, the stack `Stk`) to the return address `e₂.add j₂`. -/
theorem tail49 {fb : Addr} {W : Addr → Byte} {S : Addr} {g0 : Gprs} {Y : State} (c : Seg prof F Wl L s₀ o)
    (hfs : s₀.cpu.seg.fsBase = fb) (hin : CodeIn L fch_at fch) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = fch_at.add 49) (hm : Fm S g0 Y.cpu.gpr)
    (hst : Stk fb W S g0 (e₂.add j₂))
    (hcl : ∀ i < 8, Foot F.data (Addr.add (fb + 40#64) i))
    (f40 : ∀ i < 8, Foot F.data (Addr.add (aR S + 40#64) i))
    (g1 : ∀ i < 8, Foot F.data (Addr.add (S - 8) i)) (g2 : ∀ i < 8, Foot F.data (Addr.add (S - 8 - 8) i))
    (g3 : ∀ i < 8, Foot F.data (Addr.add (S - 8 - 8 - 8) i))
    (g4 : ∀ i < 8, Foot F.data (Addr.add (S - 8 - 8 - 8 - 8) i))
    (hl : ∀ i < 8, Foot F.data (Addr.add S i)) (hin₂ : CodeIn L e₂ code₂) (h₂ : j₂ < code₂.length)
    (k : ∀ (Z' : State) (t' : Nat), KeptW Wl s₀ Z' → Agree F Z'.proc.mm.mem W → Z'.cpu.rip = e₂.add j₂ →
      Z'.cpu.gpr.rsp = S + 8 → KS g0 Z'.cpu.gpr → GoG prof L o gev gP gE Z' t') :
    GoG prof L o gev gP gE Y t := by
  obtain ⟨s1, s2, s3, s4, s5, s6⟩ := hst
  obtain ⟨hs, h14, h15⟩ := hm
  have q1 : Y.cpu.gpr.rsp + 56#64 = S - 8 - 8 - 8 - 8 := by rw [hs, e56]
  have q2 : Y.cpu.gpr.rsp + 56#64 + 8 = S - 8 - 8 - 8 := by rw [q1, sa8]
  have q3 : Y.cpu.gpr.rsp + 56#64 + 8 + 8 = S - 8 - 8 := by rw [q2, sa8]
  have q4 : Y.cpu.gpr.rsp + 56#64 + 8 + 8 + 8 = S - 8 := by rw [q3, sa8]
  have q5 : Y.cpu.gpr.rsp + 56#64 + 8 + 8 + 8 + 8 = S := by rw [q4, sa8]
  refine (c_49 prof fb).run c hfs hin (fun j' g' _ V' => j' = 82 ∧ V' = W ∧ g'.rsp = S ∧
      g'.rbx = g0.rbx ∧ g'.rbp = g0.rbp ∧ g'.r12 = g0.r12 ∧ g'.r13 = g0.r13 ∧ g'.r14 = g0.r14 ∧
      g'.r15 = g0.r15) hK hA hr
    (vc_49 (by rw [hs]; exact s6) (by rw [hs]; exact f40) hcl (by rw [q1]; exact g4) (by rw [q2]; exact g3)
      (by rw [q3]; exact g2) (by rw [q4]; exact g1)
      fun _ a1 a2 a3 a4 a5 a6 a7 _ => ⟨rfl, rfl, a1.trans q5, a2.trans (by rw [q1]; exact s4),
        a3.trans (by rw [q2]; exact s3), a4.trans (by rw [q3]; exact s2), a5.trans (by rw [q4]; exact s1),
        a6.trans h14, a7.trans h15⟩) ?_
  rintro j' g fl V₁ ⟨rfl, hV₁, gs, gb, gp, g12, g13, g14, g15⟩ U t₁ hKU hAU hrU hgU -
  subst V₁ hgU
  refine c.s_ret hKU hAU hin (lt_len (by decide)) hrU (ret_82 _) (by rw [gs]; exact hl) hin₂ h₂
    (by rw [gs]; exact s5) ?_
  rintro Z' t₂ hKZ' hAZ' ⟨hrZ', hgZ'⟩
  refine k Z' t₂ hKZ' hAZ' hrZ' ?_ ?_
  · rw [hgZ']
    show U.cpu.gpr.rsp + 8 = _
    rw [gs]
  · rw [hgZ']
    exact ⟨gb, gp, g12, g13, g14, g15⟩

set_option maxHeartbeats 1000000 in
/-- `FindCharset` from its entry (`X`'s registers `g0`, `S` = `g0.rsp`), `fb` the `fs` base: the pushes' slots, the
guard's slot and the `call`s' return address slot in what the run may store into; the guard at `fs:0x28`, the
frame's `UString` (`aR S + 16`), the number (`aR S + 12`), the return address, the parser's switches, the switch
record (its post string when `ThereIs`) and the table readable. The memory invariant `I`: of the bytes after the
prologue (`hI0`), giving the stack (`hIs`) and the chars readable (`fc`). The callees `k1`–`k5` (entries
`0x44d5d0`, `0x5a6760`, `0x44ba10`, `0x44bb60`, `0x6014f0`) keep `I`, the frame and (`k4`) the loop's registers.
The throw path (`kx`, at 284). At the return address (`kr`): `rsp` 8 above the entry's, the callee-saved registers
as they were. -/
theorem fch_ok {fb : Addr} {g0 : Gprs} {I : (Addr → Byte) → Prop}
    {cC cP cO cE cD : List Byte}
    (c : Seg prof F Wl L s₀ o) (hfs : s₀.cpu.seg.fsBase = fb) (hin : CodeIn L fch_at fch)
    (hinC : CodeIn L 0x44d5d0#64 cC) (hC : 0 < cC.length) (hinP : CodeIn L 0x5a6760#64 cP) (hP : 0 < cP.length)
    (hinO : CodeIn L 0x44ba10#64 cO) (hO : 0 < cO.length) (hinE : CodeIn L 0x44bb60#64 cE) (hE : 0 < cE.length)
    (hinD : CodeIn L 0x6014f0#64 cD) (hD : 0 < cD.length)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = fch_at) (hg0 : X.cpu.gpr = g0)
    (hcl : ∀ i < 8, Foot F.data (Addr.add (fb + 40#64) i))
    (hs1 : ∀ i < 8, Foot Wl (Addr.add (g0.rsp - 8) i)) (hs2 : ∀ i < 8, Foot Wl (Addr.add (g0.rsp - 8 - 8) i))
    (hs3 : ∀ i < 8, Foot Wl (Addr.add (g0.rsp - 8 - 8 - 8) i))
    (hs4 : ∀ i < 8, Foot Wl (Addr.add (g0.rsp - 8 - 8 - 8 - 8) i))
    (hw40 : ∀ i < 8, Foot Wl (Addr.add (aR g0.rsp + 40#64) i))
    (hr8 : ∀ i < 8, Foot Wl (Addr.add (aR g0.rsp - 8) i))
    (f16 : ∀ i < 8, Foot F.data (Addr.add (aR g0.rsp + 16#64) i))
    (f12 : ∀ i < 4, Foot F.data (Addr.add (aR g0.rsp + 12#64) i))
    (hl : ∀ i < 8, Foot F.data (Addr.add g0.rsp i))
    (fdi : ∀ i < 8, Foot F.data (Addr.add g0.rdi i))
    (fth : ∀ i < 1, Foot F.data (Addr.add (ia (V0 fb V g0) g0.rdi (rxE g0.rsi)) i))
    (fp : ¬ Off (V0 fb V g0) (ia (V0 fb V g0) g0.rdi (rxE g0.rsi)) →
      (∀ i < 4, Foot F.data (Addr.add (ia (V0 fb V g0) g0.rdi (rxE g0.rsi) + 16#64) i)) ∧
      (∀ i < 8, Foot F.data (Addr.add (ia (V0 fb V g0) g0.rdi (rxE g0.rsi) + 8#64) i)) ∧
      (∀ i < 8, Foot F.data (Addr.add (rdq(V0 fb V g0, ia (V0 fb V g0) g0.rdi (rxE g0.rsi) + 8#64) +
        BitVec.setWidth 64 rdd(V0 fb V g0, ia (V0 fb V g0) g0.rdi (rxE g0.rsi) + 16#64) * 8#64 +
        18446744073709551608#64) i)))
    (ft : ∀ k < 5, ∀ i < 8, Foot F.data (Addr.add (tE k) i))
    (ft8 : ∀ k < 5, ∀ i < 4, Foot F.data (Addr.add (7857152#64 + (BitVec.ofNat 64 k <<< 4) + 8#64) i))
    (hin₂ : CodeIn L e₂ code₂) (h₂ : j₂ < code₂.length)
    (hI0 : I (V0 fb V g0)) (hIs : ∀ W, I W → Stk fb W g0.rsp g0 (e₂.add j₂))
    (fc : ∀ W, I W → ∀ i < 4, Foot F.data (Addr.add (rdq(W, aR g0.rsp + 16#64)) i))
    (k1 : KC prof F Wl L s₀ o gev gP gE g0.rsp g0 0x44d5d0#64 110 (V0 fb V g0)
      (fun g => Kf g0 g ∧ g.rdi = aR g0.rsp + 16#64 ∧
        g.rsi = ps (V0 fb V g0) (ia (V0 fb V g0) g0.rdi (rxE g0.rsi))) (fun _ => True) I)
    (k2 : ∀ W, I W → KC prof F Wl L s₀ o gev gP gE g0.rsp g0 0x5a6760#64 131 W
      (fun g => Kf g0 g ∧ g.rdi = rdq(W, aR g0.rsp + 16#64) ∧ g.rsi = aR g0.rsp + 12#64) (fun _ => True) I)
    (k3 : ∀ W, I W → KC prof F Wl L s₀ o gev gP gE g0.rsp g0 0x44ba10#64 165 W
      (fun g => Kf g0 g ∧ g.rdi = rdq(W, aR g0.rsp + 16#64)) (fun _ => True) I)
    (k4 : ∀ (n k : Nat) (W : Addr → Byte), I W → KC prof F Wl L s₀ o gev gP gE g0.rsp g0 0x44bb60#64 234 W
      (fun g => Kf g0 g ∧ Lr n k g ∧ g.rdi = rdq(W, aR g0.rsp + 16#64) ∧ g.rsi = nm W k) (Lr n k) I)
    (k5 : ∀ W, I W → KC prof F Wl L s₀ o gev gP gE g0.rsp g0 0x6014f0#64 266 W
      (fun g => Kf g0 g ∧ g.rdi = rdq(W, aR g0.rsp + 16#64)) (fun _ => True) I)
    (kx : ∀ (Y : State) (W : Addr → Byte) (t' : Nat), KeptW Wl s₀ Y → Agree F Y.proc.mm.mem W →
      Y.cpu.rip = fch_at.add 284 → Fm g0.rsp g0 Y.cpu.gpr → I W → GoG prof L o gev gP gE Y t')
    (kr : ∀ (W' : Addr → Byte) (Z' : State) (t' : Nat), KeptW Wl s₀ Z' → Agree F Z'.proc.mm.mem W' →
      Z'.cpu.rip = e₂.add j₂ → Z'.cpu.gpr.rsp = g0.rsp + 8 → KS g0 Z'.cpu.gpr →
      GoG prof L o gev gP gE Z' t') :
    GoG prof L o gev gP gE X t := by
  subst hg0
  have f40 : ∀ i < 8, Foot F.data (Addr.add (aR X.cpu.gpr.rsp + 40#64) i) := fun i hi => c.hws _ (hw40 i hi)
  have g1 : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rsp - 8) i) := fun i hi => c.hws _ (hs1 i hi)
  have g2 : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rsp - 8 - 8) i) := fun i hi => c.hws _ (hs2 i hi)
  have g3 : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rsp - 8 - 8 - 8) i) := fun i hi => c.hws _ (hs3 i hi)
  have g4 : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rsp - 8 - 8 - 8 - 8) i) := fun i hi => c.hws _ (hs4 i hi)
  -- from 49
  have T49 : ∀ (Y : State) (W : Addr → Byte) (t' : Nat), KeptW Wl s₀ Y → Agree F Y.proc.mm.mem W →
      Y.cpu.rip = fch_at.add 49 → Fm X.cpu.gpr.rsp X.cpu.gpr Y.cpu.gpr → I W →
      GoG prof L o gev gP gE Y t' := fun Y W t' hKY hAY hrY hmY hIW =>
    tail49 c hfs hin hKY hAY hrY hmY (hIs W hIW) hcl f40 g1 g2 g3 g4 hl hin₂ h₂
      fun Z' t'' a b d e f => kr W Z' t'' a b d e f
  -- from 252: `delete []` unless NULL, to 49
  have T252 : ∀ (Y : State) (W : Addr → Byte) (t' : Nat), KeptW Wl s₀ Y → Agree F Y.proc.mm.mem W →
      Y.cpu.rip = fch_at.add 252 → Fm X.cpu.gpr.rsp X.cpu.gpr Y.cpu.gpr →
      Y.cpu.gpr.rdi = rdq(W, aR X.cpu.gpr.rsp + 16#64) → I W → GoG prof L o gev gP gE Y t' := by
    intro Y W t' hKY hAY hrY hmY hdY hIW
    obtain ⟨ys, y14, y15⟩ := hmY
    refine (c_252 prof fb).run c hfs hin (fun j' g' _ V' => V' = W ∧ g'.rsp = aR X.cpu.gpr.rsp ∧
        g'.r14 = X.cpu.gpr.r14 ∧ g'.r15 = X.cpu.gpr.r15 ∧
        (j' = 49 ∨ (j' = 261 ∧ g'.rdi = rdq(W, aR X.cpu.gpr.rsp + 16#64)))) hKY hAY hrY
      (vc_252 (fun _ a b d _ => ⟨rfl, a.trans ys, b.trans y14, d.trans y15, Or.inl rfl⟩)
        (fun _ a b d e _ => ⟨rfl, a.trans ys, d.trans y14, e.trans y15, Or.inr ⟨rfl, b.trans hdY⟩⟩)) ?_
    rintro j' g fl V₁ ⟨hV₁, gs, g14, g15, hpost⟩ U t₁ hKU hAU hrU hgU -
    subst V₁ hgU
    rcases hpost with rfl | ⟨rfl, gdi⟩
    · exact T49 U W t₁ hKU hAU hrU ⟨gs, g14, g15⟩ hIW
    · have hU : U.cpu.gpr.rsp - 8 = aR X.cpu.gpr.rsp - 8 := by rw [gs]
      refine c.s_call hKU hAU hin (lt_len (by decide)) hrU (call_261 _) hinD hD tgt_261 (by rw [hU]; exact hr8) ?_
      rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
      rw [hU] at hA₂
      refine k5 W hIW Y₂ t₂ hK₂ hA₂ hr₂ (by rw [hg₂]; exact hU) (by rw [hg₂]; exact ⟨⟨g14, g15⟩, gdi⟩) ?_
      intro Z W' t₃ hKZ hAZ hrZ hmZ _ hIW'
      refine (c_266 prof fb).run c hfs hin (fun j' g' _ V' => j' = 49 ∧ V' = W' ∧ g' = Z.cpu.gpr) hKZ hAZ hrZ
        (vc_266 fun _ => ⟨rfl, rfl, rfl⟩) ?_
      rintro j' g fl V₁ ⟨rfl, hV₁, rfl⟩ U₂ t₄ hKU₂ hAU₂ hrU₂ hgU₂ -
      subst V₁
      exact T49 U₂ W' t₄ hKU₂ hAU₂ hrU₂ (by rw [hgU₂]; exact hmZ) hIW'
  -- the loop from 224 at the index `k` of `n`, by induction on `n - k`
  have LP : ∀ (n : Nat), n ≤ 5 → ∀ (m k : Nat) (Y : State) (W : Addr → Byte) (t' : Nat), k < n → n - k ≤ m →
      KeptW Wl s₀ Y → Agree F Y.proc.mm.mem W → Y.cpu.rip = fch_at.add 224 →
      Fm X.cpu.gpr.rsp X.cpu.gpr Y.cpu.gpr → Lr n k Y.cpu.gpr → Y.cpu.gpr.rsi = nm W k → I W →
      GoG prof L o gev gP gE Y t' := by
    intro n hn m
    induction m with
    | zero => intro k Y W t' hk hm; exact absurd hm (by omega)
    | succ m ih =>
      intro k Y W t' hk hm hKY hAY hrY hmY hLY hsY hIW
      obtain ⟨ys, y14, y15⟩ := hmY
      obtain ⟨yb, yp, y12, y13⟩ := hLY
      have hk5 : k < 5 := by omega
      refine (c_224 prof fb).run c hfs hin (fun j' g' _ V' => j' = 229 ∧ V' = W ∧
          g'.rdi = rdq(W, aR X.cpu.gpr.rsp + 16#64) ∧ Fm X.cpu.gpr.rsp X.cpu.gpr g' ∧ Lr n k g' ∧
          g'.rsi = nm W k) hKY hAY hrY
        (vc_224 (by rw [ys]; exact f16) fun _ a1 a2 a3 a4 a5 a6 a7 a8 a9 _ =>
          ⟨rfl, rfl, by rw [a1, ys], ⟨a2.trans ys, a8.trans y14, a9.trans y15⟩,
            ⟨a3.trans yb, a4.trans yp, a5.trans y12, a6.trans y13⟩, a7.trans hsY⟩) ?_
      rintro j' g fl V₁ ⟨rfl, hV₁, gdi, ⟨gs, g14, g15⟩, ⟨gb, gp, g12, g13⟩, gsi⟩ U t₁ hKU hAU hrU hgU -
      subst V₁ hgU
      have hU : U.cpu.gpr.rsp - 8 = aR X.cpu.gpr.rsp - 8 := by rw [gs]
      refine c.s_call hKU hAU hin (lt_len (by decide)) hrU (call_229 _) hinE hE tgt_229 (by rw [hU]; exact hr8) ?_
      rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
      rw [hU] at hA₂
      refine k4 n k W hIW Y₂ t₂ hK₂ hA₂ hr₂ (by rw [hg₂]; exact hU)
        (by rw [hg₂]; exact ⟨⟨g14, g15⟩, ⟨gb, gp, g12, g13⟩, gdi, gsi⟩) ?_
      -- back from the compare, at 234
      intro Z W' t₃ hKZ hAZ hrZ hmZ hLZ hIW'
      obtain ⟨zs, z14, z15⟩ := hmZ
      obtain ⟨zb, zp, z12, z13⟩ := hLZ
      by_cases ha : BitVec.setWidth 8 Z.cpu.gpr.rax = 0
      · by_cases hP : BitVec.setWidth 32 (BitVec.ofNat 64 n) = BitVec.setWidth 32 (BitVec.ofNat 64 k) + 1#32
        · -- no name left: the throw path
          refine (c_234 prof fb).run c hfs hin (fun j' g' _ V' => j' = 284 ∧ V' = W' ∧ g'.rsp = Z.cpu.gpr.rsp ∧
              g'.r14 = Z.cpu.gpr.r14 ∧ g'.r15 = Z.cpu.gpr.r15) hKZ hAZ hrZ
            (vc_234e (beq_iff_eq.2 ha) (by rw [z13, zb]; exact decide_eq_true hP)
              fun _ a b d _ => ⟨rfl, rfl, a, b, d⟩) ?_
          rintro j' g fl V₁ ⟨rfl, hV₁, gs', g14', g15'⟩ U₂ t₄ hKU₂ hAU₂ hrU₂ hgU₂ -
          subst V₁ hgU₂
          exact kx U₂ W' t₄ hKU₂ hAU₂ hrU₂ ⟨gs'.trans zs, g14'.trans z14, g15'.trans z15⟩ hIW'
        · -- the next name
          have hk1 : k + 1 < n := nx_succ hk hn hP
          have hk15 : k + 1 < 5 := by omega
          refine (c_234 prof fb).run c hfs hin (fun j' g' _ V' => j' = 224 ∧ V' = W' ∧ g'.rsp = Z.cpu.gpr.rsp ∧
              g'.rbx = BitVec.setWidth 64 (BitVec.setWidth 32 Z.cpu.gpr.rbx + 1#32) ∧
              g'.rbp = Z.cpu.gpr.rbp + 16#64 ∧ g'.r12 = Z.cpu.gpr.r12 ∧ g'.r13 = Z.cpu.gpr.r13 ∧
              g'.rsi = rdq(W', Z.cpu.gpr.rbp + 16#64) ∧ g'.r14 = Z.cpu.gpr.r14 ∧ g'.r15 = Z.cpu.gpr.r15) hKZ hAZ hrZ
            (vc_234m (beq_iff_eq.2 ha) (by rw [z13, zb]; exact decide_eq_false hP)
              (by rw [zp, tE_succ hk5]; exact ft (k + 1) hk15)
              fun _ a1 a2 a3 a4 a5 a6 a7 a8 _ => ⟨rfl, rfl, a1, a2, a3, a4, a5, a6, a7, a8⟩) ?_
          rintro j' g fl V₁ ⟨rfl, hV₁, gs', gb', gp', g12', g13', gsi', g14', g15'⟩ U₂ t₄ hKU₂ hAU₂ hrU₂ hgU₂ -
          subst V₁ hgU₂
          rw [zb, bx_succ hk5] at gb'
          rw [zp, tE_succ hk5] at gp' gsi'
          exact ih (k + 1) U₂ W' t₄ hk1 (by omega) hKU₂ hAU₂ hrU₂
            ⟨gs'.trans zs, g14'.trans z14, g15'.trans z15⟩ ⟨gb', gp', g12'.trans z12, g13'.trans z13⟩
            (gsi'.trans (nm_succ W' k).symm) hIW'
      · -- a match: the code page, to 252
        refine (c_234 prof fb).run c hfs hin (fun j' g' _ V' => j' = 252 ∧ V' = W' ∧ g'.rsp = Z.cpu.gpr.rsp ∧
            g'.rdi = rdq(W', Z.cpu.gpr.rsp + 16#64) ∧ g'.r14 = Z.cpu.gpr.r14 ∧ g'.r15 = Z.cpu.gpr.r15) hKZ hAZ hrZ
          (vc_234c (beq_eq_false_iff_ne.2 ha) (by rw [zs]; exact f16) (by rw [z12, zb]; exact ft8 k hk5)
            fun _ a b d e _ => ⟨rfl, rfl, a, b, d, e⟩) ?_
        rintro j' g fl V₁ ⟨rfl, hV₁, gs', gdi', g14', g15'⟩ U₂ t₄ hKU₂ hAU₂ hrU₂ hgU₂ -
        subst V₁ hgU₂
        exact T252 U₂ W' t₄ hKU₂ hAU₂ hrU₂ ⟨gs'.trans zs, g14'.trans z14, g15'.trans z15⟩ (by rw [gdi', zs]) hIW'
  -- from 160: `MyStringLower_Ascii`, then the table's set up, to the loop
  have T160 : ∀ (Y : State) (W : Addr → Byte) (t' : Nat), KeptW Wl s₀ Y → Agree F Y.proc.mm.mem W →
      Y.cpu.rip = fch_at.add 160 → Fm X.cpu.gpr.rsp X.cpu.gpr Y.cpu.gpr →
      Y.cpu.gpr.rdi = rdq(W, aR X.cpu.gpr.rsp + 16#64) → I W → GoG prof L o gev gP gE Y t' := by
    intro Y W t' hKY hAY hrY hmY hdY hIW
    obtain ⟨ys, y14, y15⟩ := hmY
    have hU : Y.cpu.gpr.rsp - 8 = aR X.cpu.gpr.rsp - 8 := by rw [ys]
    refine c.s_call hKY hAY hin (lt_len (by decide)) hrY (call_160 _) hinO hO tgt_160 (by rw [hU]; exact hr8) ?_
    rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
    rw [hU] at hA₂
    refine k3 W hIW Y₂ t₂ hK₂ hA₂ hr₂ (by rw [hg₂]; exact hU) (by rw [hg₂]; exact ⟨⟨y14, y15⟩, hdY⟩) ?_
    intro Z W' t₃ hKZ hAZ hrZ hmZ _ hIW'
    obtain ⟨zs, z14, z15⟩ := hmZ
    refine (c_165 prof fb).run c hfs hin (fun j' g' _ V' => j' = 224 ∧ V' = W' ∧ ∃ n, (n = 3 ∨ n = 5) ∧
        Fm X.cpu.gpr.rsp X.cpu.gpr g' ∧ Lr n 0 g' ∧ g'.rsi = nm W' 0) hKZ hAZ hrZ
      (vc_165 fun n hn _ a1 a2 a3 a4 a5 a6 a7 a8 _ => ⟨rfl, rfl, n, hn, ⟨a1.trans zs, a7.trans z14, a8.trans z15⟩,
        ⟨a2, a3.trans tE0, a4, a5⟩, a6.trans (nm_zero W').symm⟩) ?_
    rintro j' g fl V₁ ⟨rfl, hV₁, n, hn, hmg, hLg, hsg⟩ U t₁ hKU hAU hrU hgU -
    subst V₁ hgU
    exact LP n (by omega) n 0 U W' t₁ (by omega) (by omega) hKU hAU hrU hmg hLg hsg hIW'
  -- from 131: back from `StringToUInt32`
  have T131 : ∀ (Y : State) (W : Addr → Byte) (t' : Nat), KeptW Wl s₀ Y → Agree F Y.proc.mm.mem W →
      Y.cpu.rip = fch_at.add 131 → Fm X.cpu.gpr.rsp X.cpu.gpr Y.cpu.gpr → I W →
      GoG prof L o gev gP gE Y t' := by
    intro Y W t' hKY hAY hrY hmY hIW
    obtain ⟨ys, y14, y15⟩ := hmY
    refine (c_131 prof fb).run c hfs hin (fun j' g' _ V' => V' = W ∧ (j' = 160 ∨ j' = 252) ∧
        Fm X.cpu.gpr.rsp X.cpu.gpr g' ∧ g'.rdi = rdq(W, aR X.cpu.gpr.rsp + 16#64)) hKY hAY hrY
      (vc_131 (by rw [ys]; exact f16) (by rw [ys]; exact f12)
        (fun _ a b d e _ => ⟨rfl, Or.inl rfl, ⟨a.trans ys, d.trans y14, e.trans y15⟩, by rw [b, ys]⟩)
        (fun _ a b d e _ => ⟨rfl, Or.inr rfl, ⟨a.trans ys, d.trans y14, e.trans y15⟩, by rw [b, ys]⟩)) ?_
    rintro j' g fl V₁ ⟨hV₁, hj, hmg, hdg⟩ U t₁ hKU hAU hrU hgU -
    subst V₁ hgU
    rcases hj with rfl | rfl
    · exact T160 U W t₁ hKU hAU hrU hmg hdg hIW
    · exact T252 U W t₁ hKU hAU hrU hmg hdg hIW
  -- from 110: back from the copy
  have T110 : ∀ (Y : State) (W : Addr → Byte) (t' : Nat), KeptW Wl s₀ Y → Agree F Y.proc.mm.mem W →
      Y.cpu.rip = fch_at.add 110 → Fm X.cpu.gpr.rsp X.cpu.gpr Y.cpu.gpr → I W →
      GoG prof L o gev gP gE Y t' := by
    intro Y W t' hKY hAY hrY hmY hIW
    obtain ⟨ys, y14, y15⟩ := hmY
    refine (c_110 prof fb).run c hfs hin (fun j' g' _ V' => V' = W ∧ Fm X.cpu.gpr.rsp X.cpu.gpr g' ∧
        g'.rdi = rdq(W, aR X.cpu.gpr.rsp + 16#64) ∧ (j' = 160 ∨ (j' = 126 ∧ g'.rsi = aR X.cpu.gpr.rsp + 12#64)))
        hKY hAY hrY
      (vc_110 (by rw [ys]; exact f16) (by rw [ys]; exact fc W hIW)
        (fun _ a b d e _ => ⟨rfl, ⟨a.trans ys, d.trans y14, e.trans y15⟩, by rw [b, ys], Or.inl rfl⟩)
        (fun _ a b d e f _ => ⟨rfl, ⟨a.trans ys, e.trans y14, f.trans y15⟩, by rw [b, ys],
          Or.inr ⟨rfl, by rw [d, ys]⟩⟩)) ?_
    rintro j' g fl V₁ ⟨hV₁, hmg, hdg, hpost⟩ U t₁ hKU hAU hrU hgU -
    subst V₁ hgU
    rcases hpost with rfl | ⟨rfl, hsg⟩
    · exact T160 U W t₁ hKU hAU hrU hmg hdg hIW
    · obtain ⟨us, u14, u15⟩ := hmg
      have hU : U.cpu.gpr.rsp - 8 = aR X.cpu.gpr.rsp - 8 := by rw [us]
      refine c.s_call hKU hAU hin (lt_len (by decide)) hrU (call_126 _) hinP hP tgt_126 (by rw [hU]; exact hr8) ?_
      rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
      rw [hU] at hA₂
      refine k2 W hIW Y₂ t₂ hK₂ hA₂ hr₂ (by rw [hg₂]; exact hU) (by rw [hg₂]; exact ⟨⟨u14, u15⟩, hdg, hsg⟩) ?_
      intro Z W' t₃ hKZ hAZ hrZ hmZ _ hIW'
      exact T131 Z W' t₃ hKZ hAZ hrZ hmZ hIW'
  -- the entry
  have hrip' : X.cpu.rip = fch_at.add 0 := by rw [addr_add_zero]; exact hrip
  refine (c_0 prof fb).run c hfs hin (fun j' g' _ V' => j' = 37 ∧ V' = V0 fb V X.cpu.gpr ∧
      g'.rsp = aR X.cpu.gpr.rsp ∧ g'.rdi = X.cpu.gpr.rdi ∧ g'.rdx = rxE X.cpu.gpr.rsi ∧
      g'.r14 = X.cpu.gpr.r14 ∧ g'.r15 = X.cpu.gpr.r15) hK hA hrip'
    (vc_0 rfl hs1 hs2 hs3 hs4 hcl hw40 fun _ a b d e f _ => ⟨rfl, rfl, a, b, d, e, f⟩) ?_
  rintro j' g fl V₁ ⟨rfl, hV₁, gs, gdi, gdx, g14, g15⟩ Y t₁ hKY hAY hrY hgY -
  subst V₁ hgY
  refine (c_37 prof fb).run c hfs hin (fun j' g' _ V' => V' = V0 fb V X.cpu.gpr ∧
      Fm X.cpu.gpr.rsp X.cpu.gpr g' ∧ (j' = 49 ∨ (j' = 105 ∧ g'.rdi = aR X.cpu.gpr.rsp + 16#64 ∧
        g'.rsi = ps (V0 fb V X.cpu.gpr) (ia (V0 fb V X.cpu.gpr) X.cpu.gpr.rdi (rxE X.cpu.gpr.rsi))))) hKY hAY hrY
    (vc_37 (by rw [gdi]; exact fdi) (by rw [gdi, gdx]; exact fth) (by rw [gdi, gdx]; exact fp)
      (fun _ a b d _ => ⟨rfl, ⟨a.trans gs, b.trans g14, d.trans g15⟩, Or.inl rfl⟩)
      (fun _ a b d e f _ => ⟨rfl, ⟨a.trans gs, e.trans g14, f.trans g15⟩,
        Or.inr ⟨rfl, by rw [b, gs], by rw [d, gdi, gdx]⟩⟩)) ?_
  rintro j' g fl V₁ ⟨hV₁, hmg, hpost⟩ U t₂ hKU hAU hrU hgU -
  subst V₁ hgU
  rcases hpost with rfl | ⟨rfl, gdi', gsi'⟩
  · exact T49 U _ t₂ hKU hAU hrU hmg hI0
  · obtain ⟨us, u14, u15⟩ := hmg
    have hU : U.cpu.gpr.rsp - 8 = aR X.cpu.gpr.rsp - 8 := by rw [us]
    refine c.s_call hKU hAU hin (lt_len (by decide)) hrU (call_105 _) hinC hC tgt_105 (by rw [hU]; exact hr8) ?_
    rintro Y₂ t₃ hK₂ hA₂ ⟨hr₂, hg₂⟩
    rw [hU] at hA₂
    refine k1 Y₂ t₃ hK₂ hA₂ hr₂ (by rw [hg₂]; exact hU) (by rw [hg₂]; exact ⟨⟨u14, u15⟩, gdi', gsi'⟩) ?_
    intro Z W' t₄ hKZ hAZ hrZ hmZ _ hIW'
    exact T110 Z W' t₄ hKZ hAZ hrZ hmZ hIW'

end FV7z.Fch
