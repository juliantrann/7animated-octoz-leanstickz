import FV7z.Oci.Cuts
import FV7z.Lemmas.LeafRet
import FV7z.Lemmas.Fr40
import FV7z.Dfn.Holds
import FV7z.Ocv.Holds
/-!
# `COpenCallbackImp::Init2` (PLAN.md §M, M1): the run through the callees

7-Zip 26.06's `COpenCallbackImp::Init2 (folderPrefix, fileName)` at `0x5b32e0` in `7zzs`
(`CPP/7zip/UI/Common/ArchiveOpenCallback.cpp`; `objdump -d`): `this` in `rdi` (`rbx`), `folderPrefix` in `rsi`
(`r13`), `fileName` in `rdx` (`r12`). `S` the stack pointer and `g0` the registers at the entry: `push r14, r13, r12,
rbp, rbx; sub rsp, 0x20` (`aR S`, as in `FV7z.Dfn`), the stack guard (`fs:0x28`) at `aR S + 24`, a local `UString`
(the path) at `aR S`. The `call` at 48 (`0x5b3260`, `rdi` = `this + 0x108`: `FileNames.Clear ()`); then
`FileNames_WasUsed` (the 4-byte size `n` at `this + 56`, the items `it` at `this + 48`) from the last item down (the
loop, head 72, `rbp` = `8 k`): an item `p` = `it[k]` not 0 has its chars (the 8 bytes at `p`) freed unless 0 (93,
`operator delete []` at `0x6014f0`) and is freed (106, `operator delete (p, 16)` at `0x6014e0`); `rbp` -= 8 (111).
At 121 the size, the 4 bytes at `this + 72` and `this + 88` and the 2 at `this + 44` set to 0, `_folderPrefix =
folderPrefix` (158, `0x44c550`, `rdi` = `this + 112`), the path `_folderPrefix + fileName` (172, `0x44c2b0`), `ebx`
= `_fileInfo.Find (path, true)` (193, `0x455b80`, `rdi` = `this + 144`), `delete []` of the path's chars unless 0
(209); `bl` 0 gives `GetLastError_noZero_HRESULT ()` (256, `0x456000`), `jmp` to 220; at 220 the guard's check, the
epilogue, `ret` (248). Not covered: `__stack_chk_fail` (263), the landing pad.

The callees are continuations (`KC`, as in `FV7z/Dfn/Holds.lean`), each with the bytes it returns with (`N`): from
its return the run goes on with `rsp` as it was and the callee-saved registers (`KS`) as at the `call`. The bytes
are tracked by invariants the caller chooses, as in `FV7z/Cxd/Holds.lean`: `I (k + 1)` before the step `k` (the
first callee returns with `I n` and the size `n`), `J k p` after the item's chars, `I k` after the item; `I 0` from
the loop's end on, kept by the four stores (`z56`, `z72`, `z88`, `z44`), by every later callee, and giving the stack
(`Stk`). The loop by induction on the step (`L72`).

- `P5`, `V0`, `Stk`, `Fm`, `Fr`, `KC`, `AtJ`, `Ev`: the bytes after the pushes and the prologue, the stack, the
  frame, what a piece keeps, the callees, the runs from an offset, the hypotheses of the runs; `callK`: a `call`.
- `vc_*`: the pieces; `tail220`, `from261`, `from214`, `from198`, `from177`, `from163`, `from121`, `A98`, `B72`,
  `S111`, `L72`: the runs from the cut points.
- `oci_ok`: from the entry to the return address.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Oci
set_option linter.unusedVariables false

open FV7z.Dfn (aR q1 q2 q3 q4 q5 q6)
open FV7z.Fr40 (KS)
open FV7z.Ocv (pk rbx0 rbx0_eq rb_step rb_ne rb_last)

/-! ## The instructions outside the blocks -/

/-- The `call` at 48: `FileNames.Clear ()`-like (`0x5b3260`). -/
def pc48 : List Byte := [0xe8, 0x4b, 0xff, 0xff, 0xff]
theorem pc48_0 : ∀ feat, Dec feat pc48 0 (FV7z.mk .call 64 [.rel 18446744073709551435] 5) := by dec_rfl
theorem wc_48 : pc48 <+: oci.drop 48 := by decide +kernel
theorem call_48 (feat : Features) : Dec feat oci 48 (FV7z.mk .call 64 [.rel 18446744073709551435] 5) :=
  Dec.shift (j := 48) (k := 0) (pc48_0 feat) wc_48 (Nat.zero_le _)
theorem tgt_48 : oci_at.add (48 + 5) + BitVec.ofNat 64 18446744073709551435 = 0x5b3260#64 := by decide

/-- The `call` at 93: `operator delete []` of an item's chars (`0x6014f0`). -/
def pc93 : List Byte := [0xe8, 0xae, 0xe1, 0x04, 0x00]
theorem pc93_0 : ∀ feat, Dec feat pc93 0 (FV7z.mk .call 64 [.rel 319918] 5) := by dec_rfl
theorem wc_93 : pc93 <+: oci.drop 93 := by decide +kernel
theorem call_93 (feat : Features) : Dec feat oci 93 (FV7z.mk .call 64 [.rel 319918] 5) :=
  Dec.shift (j := 93) (k := 0) (pc93_0 feat) wc_93 (Nat.zero_le _)
theorem tgt_93 : oci_at.add (93 + 5) + BitVec.ofNat 64 319918 = 0x6014f0#64 := by decide

/-- The `call` at 106: `operator delete (item, 16)` (`0x6014e0`). -/
def pc106 : List Byte := [0xe8, 0x91, 0xe1, 0x04, 0x00]
theorem pc106_0 : ∀ feat, Dec feat pc106 0 (FV7z.mk .call 64 [.rel 319889] 5) := by dec_rfl
theorem wc_106 : pc106 <+: oci.drop 106 := by decide +kernel
theorem call_106 (feat : Features) : Dec feat oci 106 (FV7z.mk .call 64 [.rel 319889] 5) :=
  Dec.shift (j := 106) (k := 0) (pc106_0 feat) wc_106 (Nat.zero_le _)
theorem tgt_106 : oci_at.add (106 + 5) + BitVec.ofNat 64 319889 = 0x6014e0#64 := by decide

/-- The `call` at 158: `_folderPrefix = folderPrefix` (`0x44c550`). -/
def pc158 : List Byte := [0xe8, 0xcd, 0x91, 0xe9, 0xff]
theorem pc158_0 : ∀ feat, Dec feat pc158 0 (FV7z.mk .call 64 [.rel 18446744073708081613] 5) := by dec_rfl
theorem wc_158 : pc158 <+: oci.drop 158 := by decide +kernel
theorem call_158 (feat : Features) : Dec feat oci 158 (FV7z.mk .call 64 [.rel 18446744073708081613] 5) :=
  Dec.shift (j := 158) (k := 0) (pc158_0 feat) wc_158 (Nat.zero_le _)
theorem tgt_158 : oci_at.add (158 + 5) + BitVec.ofNat 64 18446744073708081613 = 0x44c550#64 := by decide

/-- The `call` at 172: the path `_folderPrefix + fileName` (`0x44c2b0`). -/
def pc172 : List Byte := [0xe8, 0x1f, 0x8f, 0xe9, 0xff]
theorem pc172_0 : ∀ feat, Dec feat pc172 0 (FV7z.mk .call 64 [.rel 18446744073708080927] 5) := by dec_rfl
theorem wc_172 : pc172 <+: oci.drop 172 := by decide +kernel
theorem call_172 (feat : Features) : Dec feat oci 172 (FV7z.mk .call 64 [.rel 18446744073708080927] 5) :=
  Dec.shift (j := 172) (k := 0) (pc172_0 feat) wc_172 (Nat.zero_le _)
theorem tgt_172 : oci_at.add (172 + 5) + BitVec.ofNat 64 18446744073708080927 = 0x44c2b0#64 := by decide

/-- The `call` at 193: `_fileInfo.Find (path, true)` (`0x455b80`). -/
def pc193 : List Byte := [0xe8, 0xda, 0x27, 0xea, 0xff]
theorem pc193_0 : ∀ feat, Dec feat pc193 0 (FV7z.mk .call 64 [.rel 18446744073708120026] 5) := by dec_rfl
theorem wc_193 : pc193 <+: oci.drop 193 := by decide +kernel
theorem call_193 (feat : Features) : Dec feat oci 193 (FV7z.mk .call 64 [.rel 18446744073708120026] 5) :=
  Dec.shift (j := 193) (k := 0) (pc193_0 feat) wc_193 (Nat.zero_le _)
theorem tgt_193 : oci_at.add (193 + 5) + BitVec.ofNat 64 18446744073708120026 = 0x455b80#64 := by decide

/-- The `call` at 209: `operator delete []` of the path (`0x6014f0`). -/
def pc209 : List Byte := [0xe8, 0x3a, 0xe1, 0x04, 0x00]
theorem pc209_0 : ∀ feat, Dec feat pc209 0 (FV7z.mk .call 64 [.rel 319802] 5) := by dec_rfl
theorem wc_209 : pc209 <+: oci.drop 209 := by decide +kernel
theorem call_209 (feat : Features) : Dec feat oci 209 (FV7z.mk .call 64 [.rel 319802] 5) :=
  Dec.shift (j := 209) (k := 0) (pc209_0 feat) wc_209 (Nat.zero_le _)
theorem tgt_209 : oci_at.add (209 + 5) + BitVec.ofNat 64 319802 = 0x6014f0#64 := by decide

/-- The `call` at 256: `GetLastError_noZero_HRESULT ()` (`0x456000`). -/
def pc256 : List Byte := [0xe8, 0x1b, 0x2c, 0xea, 0xff]
theorem pc256_0 : ∀ feat, Dec feat pc256 0 (FV7z.mk .call 64 [.rel 18446744073708121115] 5) := by dec_rfl
theorem wc_256 : pc256 <+: oci.drop 256 := by decide +kernel
theorem call_256 (feat : Features) : Dec feat oci 256 (FV7z.mk .call 64 [.rel 18446744073708121115] 5) :=
  Dec.shift (j := 256) (k := 0) (pc256_0 feat) wc_256 (Nat.zero_le _)
theorem tgt_256 : oci_at.add (256 + 5) + BitVec.ofNat 64 18446744073708121115 = 0x456000#64 := by decide

/-- The `ret`. -/
def pret : List Byte := [0xc3]
theorem pret_0 : ∀ feat, Dec feat pret 0 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem wt_248 : pret <+: oci.drop 248 := by decide +kernel
theorem ret_248 (feat : Features) : Dec feat oci 248 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 248) (k := 0) (pret_0 feat) wt_248 (Nat.zero_le _)

/-! ## The frame -/

/-- The bytes after the five pushes (`r14`, `r13`, `r12`, `rbp`, `rbx`). -/
abbrev P5 (V : Addr → Byte) (g : Gprs) : Addr → Byte :=
  Vst (Vst (Vst (Vst (Vst V (g.rsp - 8) (toBytesLE g.r14 8)) (g.rsp - 8 - 8) (toBytesLE g.r13 8))
    (g.rsp - 8 - 8 - 8) (toBytesLE g.r12 8)) (g.rsp - 8 - 8 - 8 - 8) (toBytesLE g.rbp 8))
    (g.rsp - 8 - 8 - 8 - 8 - 8) (toBytesLE g.rbx 8)

/-- The bytes after the prologue: the pushes, the stack guard stored. -/
abbrev V0 (fb : Addr) (V : Addr → Byte) (g : Gprs) : Addr → Byte :=
  Vst (P5 V g) (aR g.rsp + 24#64) (toBytesLE rdq(P5 V g, fb + 40#64) 8)

/-- The stack (`fb` the `fs` base, `ra` the return address): the five saved registers, the return address, the stack
guard as at `fs:0x28`. -/
abbrev Stk (fb : Addr) (W : Addr → Byte) (S : Addr) (g0 : Gprs) (ra : Addr) : Prop :=
  rdq(W, S - 8 - 8 - 8 - 8 - 8) = g0.rbx ∧ rdq(W, S - 8 - 8 - 8 - 8) = g0.rbp ∧ rdq(W, S - 8 - 8 - 8) = g0.r12 ∧
    rdq(W, S - 8 - 8) = g0.r13 ∧ rdq(W, S - 8) = g0.r14 ∧ rdq(W, S) = ra ∧
    rdq(W, aR S + 24#64) = rdq(W, fb + 40#64)

/-- The frame up to 198: `rsp` = `aR S`, `rbx` = `this`, `r12` = `fileName`, `r13` = `folderPrefix`, `r15` as at
the entry. -/
abbrev Fm (S : Addr) (g0 g : Gprs) : Prop :=
  g.rsp = aR S ∧ g.rbx = g0.rdi ∧ g.r12 = g0.rdx ∧ g.r13 = g0.rsi ∧ g.r15 = g0.r15

/-- What a piece keeps: `rsp`, `rbx`, `r12`, `r13`, `r15`. -/
abbrev Fr (g g' : Gprs) : Prop :=
  g'.rsp = g.rsp ∧ g'.rbx = g.rbx ∧ g'.r12 = g.r12 ∧ g'.r13 = g.r13 ∧ g'.r15 = g.r15

theorem Fm.fr {S : Addr} {g0 g g' : Gprs} (h : Fm S g0 g) (h' : Fr g g') : Fm S g0 g' :=
  ⟨h'.1.trans h.1, h'.2.1.trans h.2.1, h'.2.2.1.trans h.2.2.1, h'.2.2.2.1.trans h.2.2.2.1,
    h'.2.2.2.2.trans h.2.2.2.2⟩

/-- Back from a callee: `rsp` as before the `call`, the callee-saved registers kept. -/
theorem fm_ret {S : Addr} {g0 g g' : Gprs} (h : Fm S g0 g) (hs : g'.rsp = aR S) (hk : KS g g') : Fm S g0 g' :=
  ⟨hs, hk.1.trans h.2.1, hk.2.2.1.trans h.2.2.1, hk.2.2.2.1.trans h.2.2.2.1, hk.2.2.2.2.2.trans h.2.2.2.2⟩

/-- A callee from the `call` before `j` (entry `ent`, the bytes `W`, the registers `A`): at its entry, and from its
return at `j` with `rsp` = `aR S`, the callee-saved registers as at its entry and bytes with `N`, the run goes on to
the goal. -/
def KC (prof : Profile) (F : Footprint) (Wl : List Rgn) (L : List (Addr × List Byte)) (s₀ : State) (o : Oracle)
    (gev : List Event) (gP : State → Nat → List Event → Prop) (gE : Outcome → List Event → Prop)
    (S ent : Addr) (j : Nat) (W : Addr → Byte) (A : Gprs → Prop) (N : (Addr → Byte) → Prop) : Prop :=
  ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y →
    Agree F Y.proc.mm.mem (Vst W (aR S - 8) (toBytesLE (oci_at.add j) 8)) →
    Y.cpu.rip = ent → Y.cpu.gpr.rsp = aR S - 8 → A Y.cpu.gpr →
    (∀ (Z : State) (W' : Addr → Byte) (t'' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem W' →
      Z.cpu.rip = oci_at.add j → Z.cpu.gpr.rsp = aR S → KS Y.cpu.gpr Z.cpu.gpr → N W' →
      GoG prof L o gev gP gE Z t'') →
    GoG prof L o gev gP gE Y t'

/-- From offset `j` with registers and bytes for which `P` holds, the run goes on to the goal. -/
def AtJ (prof : Profile) (F : Footprint) (Wl : List Rgn) (L : List (Addr × List Byte)) (s₀ : State) (o : Oracle)
    (gev : List Event) (gP : State → Nat → List Event → Prop) (gE : Outcome → List Event → Prop) (j : Nat)
    (P : Gprs → (Addr → Byte) → Prop) : Prop :=
  ∀ (Y : State) (W : Addr → Byte) (t : Nat), KeptW Wl s₀ Y → Agree F Y.proc.mm.mem W →
    Y.cpu.rip = oci_at.add j → P Y.cpu.gpr W → GoG prof L o gev gP gE Y t

/-- The hypotheses of the runs from the cut points (`S`, `g0` the entry's stack pointer and registers, `e₂.add j₂`
the return address, `n` the size and `it` the items, `I`, `J` the invariants of the bytes). -/
structure Ev (prof : Profile) (F : Footprint) (Wl : List Rgn) (L : List (Addr × List Byte)) (s₀ : State)
    (o : Oracle) (gev : List Event) (gP : State → Nat → List Event → Prop) (gE : Outcome → List Event → Prop)
    (fb S : Addr) (g0 : Gprs) (e₂ : Addr) (code₂ : List Byte) (j₂ : Nat) (n : Nat) (it : BitVec 64)
    (I : Nat → (Addr → Byte) → Prop) (J : Nat → BitVec 64 → (Addr → Byte) → Prop) : Prop where
  c : Seg prof F Wl L s₀ o
  hfs : s₀.cpu.seg.fsBase = fb
  hin : CodeIn L oci_at oci
  hin₂ : CodeIn L e₂ code₂
  h₂ : j₂ < code₂.length
  hn : n < 4294967296
  hI : ∀ W, I 0 W → Stk fb W S g0 (e₂.add j₂)
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
  fa : ∀ i < 8, Foot F.data (Addr.add (g0.rdi + 48#64) i)
  w56 : ∀ i < 4, Foot Wl (Addr.add (g0.rdi + 56#64) i)
  w72 : ∀ i < 4, Foot Wl (Addr.add (g0.rdi + 72#64) i)
  w88 : ∀ i < 4, Foot Wl (Addr.add (g0.rdi + 88#64) i)
  w44 : ∀ i < 2, Foot Wl (Addr.add (g0.rdi + 44#64) i)
  fe : ∀ k < n, ∀ i < 8, Foot F.data (Addr.add (it + BitVec.ofNat 64 (8 * k)) i)
  fp : ∀ k < n, ∀ W, I (k + 1) W → pk W it k ≠ 0 → ∀ i < 8, Foot F.data (Addr.add (pk W it k) i)
  hIt : ∀ k < n, ∀ W, I (k + 1) W → rdq(W, g0.rdi + 48#64) = it
  hP0 : ∀ k < n, ∀ W, I (k + 1) W → pk W it k = 0 → I k W
  hQ0 : ∀ k < n, ∀ W, I (k + 1) W → pk W it k ≠ 0 → rdq(W, pk W it k) = 0 → J k (pk W it k) W
  z56 : ∀ W bs, I 0 W → I 0 (Vst W (g0.rdi + 56#64) bs)
  z72 : ∀ W bs, I 0 W → I 0 (Vst W (g0.rdi + 72#64) bs)
  z88 : ∀ W bs, I 0 W → I 0 (Vst W (g0.rdi + 88#64) bs)
  z44 : ∀ W bs, I 0 W → I 0 (Vst W (g0.rdi + 44#64) bs)
  cD : ∃ code : List Byte, CodeIn L 0x6014f0#64 code ∧ 0 < code.length
  cE : ∃ code : List Byte, CodeIn L 0x6014e0#64 code ∧ 0 < code.length
  cP : ∃ code : List Byte, CodeIn L 0x44c550#64 code ∧ 0 < code.length
  cC : ∃ code : List Byte, CodeIn L 0x44c2b0#64 code ∧ 0 < code.length
  cF : ∃ code : List Byte, CodeIn L 0x455b80#64 code ∧ 0 < code.length
  cG : ∃ code : List Byte, CodeIn L 0x456000#64 code ∧ 0 < code.length
  k93 : ∀ k < n, ∀ W, I (k + 1) W → pk W it k ≠ 0 → rdq(W, pk W it k) ≠ 0 →
    KC prof F Wl L s₀ o gev gP gE S 0x6014f0#64 98 W (fun g => g.rdi = rdq(W, pk W it k)) (J k (pk W it k))
  k106 : ∀ k < n, ∀ p W, p ≠ 0 → J k p W →
    KC prof F Wl L s₀ o gev gP gE S 0x6014e0#64 111 W (fun g => g.rdi = p ∧ g.rsi = 16#64) (I k)
  k158 : ∀ W, I 0 W → KC prof F Wl L s₀ o gev gP gE S 0x44c550#64 163 W
    (fun g => g.rdi = g0.rdi + 112#64 ∧ g.rsi = g0.rsi) (I 0)
  k172 : ∀ W, I 0 W → KC prof F Wl L s₀ o gev gP gE S 0x44c2b0#64 177 W
    (fun g => g.rdi = aR S ∧ g.rsi = g0.rdi + 112#64 ∧ g.rdx = g0.rdx) (I 0)
  k193 : ∀ W, I 0 W → KC prof F Wl L s₀ o gev gP gE S 0x455b80#64 198 W
    (fun g => g.rdi = g0.rdi + 144#64 ∧ g.rsi = rdq(W, aR S) ∧ g.rdx = 1#64) (I 0)
  k209 : ∀ W, I 0 W → KC prof F Wl L s₀ o gev gP gE S 0x6014f0#64 214 W (fun g => g.rdi = rdq(W, aR S)) (I 0)
  k256 : ∀ W, I 0 W → KC prof F Wl L s₀ o gev gP gE S 0x456000#64 261 W (fun _ => True) (I 0)
  kr : ∀ (W : Addr → Byte) (Z' : State) (t' : Nat), KeptW Wl s₀ Z' → Agree F Z'.proc.mm.mem W →
    Z'.cpu.rip = e₂.add j₂ → Z'.cpu.gpr.rsp = S + 8 → KS g0 Z'.cpu.gpr → I 0 W →
      GoG prof L o gev gP gE Z' t'

/-! ## The pieces -/

section Pieces
variable {F : Footprint} {Wl : List Rgn}

/-- The prologue: the pushes, `r13` = `folderPrefix`, `r12` = `fileName`, `rbx` = `this`, `rdi` = `this + 0x108`,
the frame, the stack guard stored (its value named `cn`): to the `call` at 48. -/
theorem vc_0 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} {cn : BitVec 64}
    (hcn : rdq(P5 V g, fb + 40#64) = cn)
    (hs1 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8) i)) (hs2 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8) i))
    (hs3 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8 - 8) i))
    (hs4 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8 - 8 - 8) i))
    (hs5 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8 - 8 - 8 - 8) i))
    (hcl : ∀ i < 8, Foot F.data (Addr.add (fb + 40#64) i))
    (hw : ∀ i < 8, Foot Wl (Addr.add (aR g.rsp + 24#64) i))
    (h : ∀ g', g'.rsp = aR g.rsp → g'.rbx = g.rdi → g'.r12 = g.rdx → g'.r13 = g.rsi → g'.r15 = g.r15 →
      g'.rdi = g.rdi + 264#64 → ∀ fl, Q 48 g' fl (Vst (P5 V g) (aR g.rsp + 24#64) (toBytesLE cn 8))) :
    W_0 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [aR, P5] at hcn hs1 hs2 hs3 hs4 hs5 hw h ⊢
  wpx [W_0, o0, Op.ldf, hcn]
  all_goals repeat' (first
    | refine h _ ?_ ?_ ?_ ?_ ?_ ?_ _
    | with_reducible rfl
    | with_reducible exact hs1
    | with_reducible exact hs2
    | with_reducible exact hs3
    | with_reducible exact hs4
    | with_reducible exact hs5
    | with_reducible exact hcl
    | with_reducible exact hw
    | apply And.intro
    | intro _)

/-- The size `n32` (the 4 bytes at `this + 56`) 0: to 121. -/
theorem vc_53z {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} {n32 : BitVec 32}
    (hn : rdd(V, g.rbx + 56#64) = n32) (hn0 : n32 = 0) (fn : ∀ i < 4, Foot F.data (Addr.add (g.rbx + 56#64) i))
    (h : ∀ g', Fr g g' → ∀ fl, Q 121 g' fl V) :
    W_53 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hn fn h ⊢
  have e : (n32 == 0) = true := beq_iff_eq.2 hn0
  wpx [W_53, W_60, o1, o2, Op.shl64, hn, e, BitVec.and_self, Bool.false_eq_true, Bool.true_eq_false,
    false_implies, eq_self_iff_true, true_implies, implies_true]
  all_goals repeat' (first
    | refine h _ ?_ _
    | with_reducible rfl
    | with_reducible exact fn
    | apply And.intro
    | intro _)

/-- The size `n32` not 0: `rbp` = `8 (n32 - 1)` (`Ocv.rbx0`), to the loop's head 72. -/
theorem vc_53n {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} {n32 : BitVec 32}
    (hn : rdd(V, g.rbx + 56#64) = n32) (hn0 : n32 ≠ 0) (fn : ∀ i < 4, Foot F.data (Addr.add (g.rbx + 56#64) i))
    (h : ∀ g', Fr g g' → g'.rbp = rbx0 n32 → ∀ fl, Q 72 g' fl V) :
    W_53 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hn fn h ⊢
  have e : (n32 == 0) = false := beq_eq_false_iff_ne.2 hn0
  wpx [W_53, W_60, o1, o2, Op.shl64, hn, e, BitVec.and_self, Bool.false_eq_true, Bool.true_eq_false,
    false_implies, eq_self_iff_true, true_implies, implies_true]
  all_goals repeat' (first
    | refine h _ ?_ ?_ _
    | with_reducible rfl
    | with_reducible exact fn
    | exact rfl
    | apply And.intro
    | intro _)

/-- The loop's head with the item `p` (the 8 bytes at `it + rbp`) 0: to 111. -/
theorem vc_72z {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} {it p : BitVec 64}
    (hit : rdq(V, g.rbx + 48#64) = it) (fa : ∀ i < 8, Foot F.data (Addr.add (g.rbx + 48#64) i))
    (hp : rdq(V, it + g.rbp) = p) (fp : ∀ i < 8, Foot F.data (Addr.add (it + g.rbp) i)) (hp0 : p = 0)
    (h : ∀ g', Fr g g' → g'.rbp = g.rbp → ∀ fl, Q 111 g' fl V) :
    W_72 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hit fa hp fp h ⊢
  have e : (p == 0) = true := beq_iff_eq.2 hp0
  wpx [W_72, W_85, o3, o4, hit, hp, e, BitVec.and_self, Bool.false_eq_true, Bool.true_eq_false, false_implies,
    eq_self_iff_true, true_implies, implies_true]
  all_goals repeat' (first
    | refine h _ ?_ ?_ _
    | with_reducible rfl
    | with_reducible exact fa
    | with_reducible exact fp
    | apply And.intro
    | intro _)

/-- The loop's head with the item `p` not 0: `r14` = `p`, `rdi` = `q` (its chars, the 8 bytes at `p`); to 98 when
`q` is 0, else to the `call` at 93. -/
theorem vc_72n {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} {it p q : BitVec 64}
    (hit : rdq(V, g.rbx + 48#64) = it) (fa : ∀ i < 8, Foot F.data (Addr.add (g.rbx + 48#64) i))
    (hp : rdq(V, it + g.rbp) = p) (fp : ∀ i < 8, Foot F.data (Addr.add (it + g.rbp) i)) (hp0 : p ≠ 0)
    (hq : rdq(V, p) = q) (fq : ∀ i < 8, Foot F.data (Addr.add p i))
    (h98 : q = 0 → ∀ g', Fr g g' → g'.rbp = g.rbp → g'.r14 = p → ∀ fl, Q 98 g' fl V)
    (h93 : q ≠ 0 → ∀ g', Fr g g' → g'.rbp = g.rbp → g'.r14 = p → g'.rdi = q → ∀ fl, Q 93 g' fl V) :
    W_72 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hit fa hp fp h98 h93 ⊢
  have e : (p == 0) = false := beq_eq_false_iff_ne.2 hp0
  wpx [W_72, W_85, o3, o4, hit, hp, hq, e, BitVec.and_self, beq_iff_eq, beq_eq_false_iff_ne, Bool.false_eq_true,
    Bool.true_eq_false, false_implies, eq_self_iff_true, true_implies, implies_true]
  all_goals repeat' (first
    | refine h98 ?_ _ ?_ ?_ ?_ _
    | refine h93 ?_ _ ?_ ?_ ?_ ?_ _
    | with_reducible rfl
    | with_reducible exact fa
    | with_reducible exact fp
    | with_reducible exact fq
    | assumption
    | apply And.intro
    | intro _)

/-- `esi` = 16, `rdi` = the item: to the `call` at 106. -/
theorem vc_98 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (h : ∀ g', Fr g g' → g'.rbp = g.rbp → g'.rdi = g.r14 → g'.rsi = 16#64 → ∀ fl, Q 106 g' fl V) :
    W_98 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h ⊢
  wpx [W_98, o5, BitVec.reduceSetWidth]
  all_goals repeat' (first
    | refine h _ ?_ ?_ ?_ ?_ _
    | with_reducible rfl
    | apply And.intro
    | intro _)

/-- `rbp` -= 8 gives `-8` (the last step): to 121. -/
theorem vc_111l {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (hb : g.rbp - 8#64 = 18446744073709551608#64) (h : ∀ g', Fr g g' → ∀ fl, Q 121 g' fl V) :
    W_111 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hb h ⊢
  have e := decide_eq_true hb
  wpx [W_111, o6, e, Bool.not_true, Bool.not_false, Bool.false_eq_true, Bool.true_eq_false, false_implies,
    eq_self_iff_true, true_implies, implies_true]
  all_goals repeat' (first
    | refine h _ ?_ _
    | with_reducible rfl
    | apply And.intro
    | intro _)

/-- `rbp` -= 8, not the last step: back to 72. -/
theorem vc_111c {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (hb : g.rbp - 8#64 ≠ 18446744073709551608#64)
    (h : ∀ g', Fr g g' → g'.rbp = g.rbp - 8#64 → ∀ fl, Q 72 g' fl V) :
    W_111 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hb h ⊢
  have e := decide_eq_false hb
  wpx [W_111, o6, e, Bool.not_true, Bool.not_false, Bool.false_eq_true, Bool.true_eq_false, false_implies,
    eq_self_iff_true, true_implies, implies_true]
  all_goals repeat' (first
    | refine h _ ?_ ?_ _
    | with_reducible rfl
    | apply And.intro
    | intro _)

/-- The stores of 0 (the size, `this + 72`, `this + 88`, the 2 bytes at `this + 44`), kept by `P`; `rbp` = `rdi` =
`this + 112`, `rsi` = `folderPrefix`: to the `call` at 158. -/
theorem vc_121 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} {P : (Addr → Byte) → Prop}
    (w56 : ∀ i < 4, Foot Wl (Addr.add (g.rbx + 56#64) i)) (w72 : ∀ i < 4, Foot Wl (Addr.add (g.rbx + 72#64) i))
    (w88 : ∀ i < 4, Foot Wl (Addr.add (g.rbx + 88#64) i)) (w44 : ∀ i < 2, Foot Wl (Addr.add (g.rbx + 44#64) i))
    (hP : P V) (z56 : ∀ W bs, P W → P (Vst W (g.rbx + 56#64) bs))
    (z72 : ∀ W bs, P W → P (Vst W (g.rbx + 72#64) bs)) (z88 : ∀ W bs, P W → P (Vst W (g.rbx + 88#64) bs))
    (z44 : ∀ W bs, P W → P (Vst W (g.rbx + 44#64) bs))
    (h : ∀ g' V', P V' → Fr g g' → g'.rbp = g.rbx + 112#64 → g'.rsi = g.r13 → g'.rdi = g.rbx + 112#64 →
      ∀ fl, Q 158 g' fl V') :
    W_121 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at w56 w72 w88 w44 z56 z72 z88 z44 h ⊢
  wpx [W_121, o7]
  all_goals repeat' (first
    | refine h _ _ ?_ ?_ ?_ ?_ ?_ _
    | with_reducible exact hP
    | refine z44 _ _ ?_
    | refine z88 _ _ ?_
    | refine z72 _ _ ?_
    | refine z56 _ _ ?_
    | with_reducible rfl
    | with_reducible exact w56
    | with_reducible exact w72
    | with_reducible exact w88
    | with_reducible exact w44
    | apply And.intro
    | intro _)

/-- `rdi` = the local, `rdx` = `fileName`, `rsi` = `this + 112`: to the `call` at 172. -/
theorem vc_163 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (h : ∀ g', Fr g g' → g'.rdi = g.rsp → g'.rdx = g.r12 → g'.rsi = g.rbp → ∀ fl, Q 172 g' fl V) :
    W_163 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h ⊢
  wpx [W_163, o8]
  all_goals repeat' (first
    | refine h _ ?_ ?_ ?_ ?_ _
    | with_reducible rfl
    | apply And.intro
    | intro _)

/-- `rsi` = the path's chars, `edx` = 1, `rdi` = `this + 144`: to the `call` at 193. -/
theorem vc_177 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (f0 : ∀ i < 8, Foot F.data (Addr.add g.rsp i))
    (h : ∀ g', Fr g g' → g'.rsi = rdq(V, g.rsp) → g'.rdx = 1#64 → g'.rdi = g.rbx + 144#64 →
      ∀ fl, Q 193 g' fl V) :
    W_177 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at f0 h ⊢
  wpx [W_177, o9, BitVec.reduceSetWidth]
  all_goals repeat' (first
    | refine h _ ?_ ?_ ?_ ?_ _
    | with_reducible rfl
    | with_reducible exact f0
    | apply And.intro
    | intro _)

/-- `rdi` = the path's chars, `ebx` = `Find`'s result: to 214 when the chars are 0, else to the `call` at 209. -/
theorem vc_198 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (f0 : ∀ i < 8, Foot F.data (Addr.add g.rsp i))
    (h214 : ∀ g', g'.rsp = g.rsp → g'.r15 = g.r15 → ∀ fl, Q 214 g' fl V)
    (h209 : ∀ g', g'.rsp = g.rsp → g'.r15 = g.r15 → g'.rdi = rdq(V, g.rsp) → ∀ fl, Q 209 g' fl V) :
    W_198 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at f0 h214 h209 ⊢
  wpx [W_198, o10]
  all_goals repeat' (first
    | refine h214 _ ?_ ?_ _
    | refine h209 _ ?_ ?_ ?_ _
    | with_reducible rfl
    | with_reducible exact f0
    | apply And.intro
    | intro _)

/-- `eax` = 0, `bl` 0 to the `call` at 256, else to 220. -/
theorem vc_214 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (h256 : ∀ g', g'.rsp = g.rsp → g'.r15 = g.r15 → ∀ fl, Q 256 g' fl V)
    (h220 : ∀ g', g'.rsp = g.rsp → g'.r15 = g.r15 → ∀ fl, Q 220 g' fl V) :
    W_214 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h256 h220 ⊢
  wpx [W_214, o11]
  all_goals repeat' (first
    | refine h256 _ ?_ ?_ _
    | refine h220 _ ?_ ?_ _
    | with_reducible rfl
    | apply And.intro
    | intro _)

/-- The stack guard checked (as at `fs:0x28`: `jne` not taken), `add rsp, 0x20`, the five pops, to the `ret`. -/
theorem vc_220 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (hc : rdq(V, g.rsp + 24#64) = rdq(V, fb + 40#64)) (f24 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 24#64) i))
    (fcl : ∀ i < 8, Foot F.data (Addr.add (fb + 40#64) i))
    (f1 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 32#64) i))
    (f2 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 32#64 + 8) i))
    (f3 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 32#64 + 8 + 8) i))
    (f4 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 32#64 + 8 + 8 + 8) i))
    (f5 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 32#64 + 8 + 8 + 8 + 8) i))
    (h : ∀ g', g'.rsp = g.rsp + 32#64 + 8 + 8 + 8 + 8 + 8 → g'.rbx = rdq(V, g.rsp + 32#64) →
      g'.rbp = rdq(V, g.rsp + 32#64 + 8) → g'.r12 = rdq(V, g.rsp + 32#64 + 8 + 8) →
      g'.r13 = rdq(V, g.rsp + 32#64 + 8 + 8 + 8) → g'.r14 = rdq(V, g.rsp + 32#64 + 8 + 8 + 8 + 8) →
      g'.r15 = g.r15 → ∀ fl, Q 248 g' fl V) :
    W_220 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hc f24 f1 f2 f3 f4 f5 h ⊢
  have z0 : ((0#64 : BitVec 64) == 0) = true := by decide
  wpx [W_220, W_236, o12, o13, Op.xormf, hc, BitVec.xor_self, z0, decide_true, Bool.not_true, Bool.false_eq_true,
    false_implies, eq_self_iff_true, true_implies]
  all_goals repeat' (first
    | refine h _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ _
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

/-- `jmp` to 220. -/
theorem vc_261 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} (h : ∀ fl, Q 220 g fl V) :
    W_261 fb F Wl Q g f V := h _

end Pieces

/-! ## The runs from the cut points -/

section Runs
variable {prof : Profile} {F : Footprint} {Wl : List Rgn} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {fb S : Addr} {g0 : Gprs} {e₂ : Addr} {code₂ : List Byte} {j₂ : Nat} {n : Nat} {it : BitVec 64}
  {I : Nat → (Addr → Byte) → Prop} {J : Nat → BitVec 64 → (Addr → Byte) → Prop}
  {Y : State} {t : Nat} {W : Addr → Byte}

/-- A `call` at `j` (`rsp` = `aR S`, the bytes `W`) of the callee `k`, and from its return at `j + 5`. -/
theorem callK (E : Ev prof F Wl L s₀ o gev gP gE fb S g0 e₂ code₂ j₂ n it I J) {U : State} {t₁ : Nat}
    {j R : Nat} {ent : Addr} {A : Gprs → Prop} {N : (Addr → Byte) → Prop} (hKU : KeptW Wl s₀ U)
    (hAU : Agree F U.proc.mm.mem W) (hrU : U.cpu.rip = oci_at.add j) (hs : U.cpu.gpr.rsp = aR S)
    (hj : j < oci.length) (hd : Dec prof.feat oci j (FV7z.mk .call 64 [.rel R] 5))
    (htgt : oci_at.add (j + 5) + BitVec.ofNat 64 R = ent)
    (hc : ∃ code : List Byte, CodeIn L ent code ∧ 0 < code.length)
    (k : KC prof F Wl L s₀ o gev gP gE S ent (j + 5) W A N) (hA : A (U.cpu.gpr.set 4 (aR S - 8)))
    (h : ∀ (Z : State) (W' : Addr → Byte) (t'' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem W' →
      Z.cpu.rip = oci_at.add (j + 5) → Z.cpu.gpr.rsp = aR S → KS U.cpu.gpr Z.cpu.gpr → N W' →
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

/-- From 220 (`rsp` = `aR S`, `r15` as at the entry, the bytes `W` with `I 0`): the guard's check, the epilogue, the
`ret`, to `kr`. -/
theorem tail220 (E : Ev prof F Wl L s₀ o gev gP gE fb S g0 e₂ code₂ j₂ n it I J) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = oci_at.add 220) (hs : Y.cpu.gpr.rsp = aR S)
    (h15 : Y.cpu.gpr.r15 = g0.r15) (hIW : I 0 W) :
    GoG prof L o gev gP gE Y t := by
  obtain ⟨s1, s2, s3, s4, s5, s6, s7⟩ := E.hI W hIW
  have e1 : rdq(W, Y.cpu.gpr.rsp + 32#64) = g0.rbx := by rw [hs, q1]; exact s1
  have e2 : rdq(W, Y.cpu.gpr.rsp + 32#64 + 8) = g0.rbp := by rw [hs, q2]; exact s2
  have e3 : rdq(W, Y.cpu.gpr.rsp + 32#64 + 8 + 8) = g0.r12 := by rw [hs, q3]; exact s3
  have e4 : rdq(W, Y.cpu.gpr.rsp + 32#64 + 8 + 8 + 8) = g0.r13 := by rw [hs, q4]; exact s4
  have e5 : rdq(W, Y.cpu.gpr.rsp + 32#64 + 8 + 8 + 8 + 8) = g0.r14 := by rw [hs, q5]; exact s5
  refine (c_220 prof fb).run E.c E.hfs E.hin (fun j' g' _ V' => j' = 248 ∧ V' = W ∧
      g'.rsp = Y.cpu.gpr.rsp + 32#64 + 8 + 8 + 8 + 8 + 8 ∧ g'.rbx = rdq(W, Y.cpu.gpr.rsp + 32#64) ∧
      g'.rbp = rdq(W, Y.cpu.gpr.rsp + 32#64 + 8) ∧ g'.r12 = rdq(W, Y.cpu.gpr.rsp + 32#64 + 8 + 8) ∧
      g'.r13 = rdq(W, Y.cpu.gpr.rsp + 32#64 + 8 + 8 + 8) ∧ g'.r14 = rdq(W, Y.cpu.gpr.rsp + 32#64 + 8 + 8 + 8 + 8) ∧
      g'.r15 = Y.cpu.gpr.r15)
    hK hA hr
    (vc_220 (by rw [hs]; exact s7) (by rw [hs]; exact E.fg) E.hcl (by rw [hs, q1]; exact E.fb40)
      (by rw [hs, q2]; exact E.fb32) (by rw [hs, q3]; exact E.fb24) (by rw [hs, q4]; exact E.fb16)
      (by rw [hs, q5]; exact E.fb8)
      fun _ a b d e f g h _ => ⟨rfl, rfl, a, b, d, e, f, g, h⟩) ?_
  rintro j' g fl V₁ ⟨rfl, hV₁, gs, gx, gp, g12, g13, g14, g15⟩ U t₁ hKU hAU hrU hgU -
  subst V₁ hgU
  have hsU : U.cpu.gpr.rsp = S := by rw [gs, hs]; exact q6 S
  refine E.c.s_ret hKU hAU E.hin (lt_len (by decide)) hrU (ret_248 _) (by rw [hsU]; exact E.hl) E.hin₂ E.h₂
    (by rw [hsU]; exact s6) ?_
  rintro Z' t₂ hKZ' hAZ' ⟨hrZ', hgZ'⟩
  refine E.kr W Z' t₂ hKZ' hAZ' hrZ' ?_ ?_ hIW
  · rw [hgZ']
    show U.cpu.gpr.rsp + 8 = _
    rw [hsU]
  · rw [hgZ']
    exact ⟨gx.trans e1, gp.trans e2, g12.trans e3, g13.trans e4, g14.trans e5, g15.trans h15⟩

/-- From 261 (back from `__stack_chk_fail`'s neighbour, the `call` at 256): `jmp` to 220. -/
theorem from261 (E : Ev prof F Wl L s₀ o gev gP gE fb S g0 e₂ code₂ j₂ n it I J) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = oci_at.add 261) (hs : Y.cpu.gpr.rsp = aR S)
    (h15 : Y.cpu.gpr.r15 = g0.r15) (hIW : I 0 W) :
    GoG prof L o gev gP gE Y t := by
  refine (c_261 prof fb).run E.c E.hfs E.hin (fun j' g' _ V' => j' = 220 ∧ g' = Y.cpu.gpr ∧ V' = W)
    hK hA hr (vc_261 fun _ => ⟨rfl, rfl, rfl⟩) ?_
  rintro j' g fl V₁ ⟨rfl, rfl, hV₁⟩ U t₁ hKU hAU hrU hgU -
  subst V₁
  exact tail220 E hKU hAU hrU (by rw [hgU]; exact hs) (by rw [hgU]; exact h15) hIW

/-- From 214 (`bl` = `Find`'s result): to 220, or the `call` at 256 (`k256`) and from its return 261. -/
theorem from214 (E : Ev prof F Wl L s₀ o gev gP gE fb S g0 e₂ code₂ j₂ n it I J) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = oci_at.add 214) (hs : Y.cpu.gpr.rsp = aR S)
    (h15 : Y.cpu.gpr.r15 = g0.r15) (hIW : I 0 W) :
    GoG prof L o gev gP gE Y t := by
  refine (c_214 prof fb).run E.c E.hfs E.hin (fun j' g' _ V' => V' = W ∧ g'.rsp = Y.cpu.gpr.rsp ∧
      g'.r15 = Y.cpu.gpr.r15 ∧ (j' = 256 ∨ j' = 220)) hK hA hr
    (vc_214 (fun _ a b _ => ⟨rfl, a, b, Or.inl rfl⟩) (fun _ a b _ => ⟨rfl, a, b, Or.inr rfl⟩)) ?_
  rintro j' g fl V₁ ⟨hV₁, gs, g15, hj⟩ U t₁ hKU hAU hrU hgU -
  subst V₁ hgU
  have hsU : U.cpu.gpr.rsp = aR S := gs.trans hs
  have h15U : U.cpu.gpr.r15 = g0.r15 := g15.trans h15
  rcases hj with rfl | rfl
  · refine callK E hKU hAU hrU hsU (lt_len (by decide)) (call_256 _) tgt_256 E.cG (E.k256 _ hIW) trivial ?_
    intro Z W' t₃ hKZ hAZ hrZ hsZ hkZ hIZ
    exact from261 E hKZ hAZ hrZ hsZ (hkZ.2.2.2.2.2.trans h15U) hIZ
  · exact tail220 E hKU hAU hrU hsU h15U hIW

/-- From 198 (back from `Find`): the local's chars, null to 214, else `delete[]` (`k209`) and from its return 214. -/
theorem from198 (E : Ev prof F Wl L s₀ o gev gP gE fb S g0 e₂ code₂ j₂ n it I J) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = oci_at.add 198) (hs : Y.cpu.gpr.rsp = aR S)
    (h15 : Y.cpu.gpr.r15 = g0.r15) (hIW : I 0 W) :
    GoG prof L o gev gP gE Y t := by
  refine (c_198 prof fb).run E.c E.hfs E.hin (fun j' g' _ V' => V' = W ∧ g'.rsp = Y.cpu.gpr.rsp ∧
      g'.r15 = Y.cpu.gpr.r15 ∧ (j' = 214 ∨ (j' = 209 ∧ g'.rdi = rdq(W, Y.cpu.gpr.rsp)))) hK hA hr
    (vc_198 (by rw [hs]; exact E.f0) (fun _ a b _ => ⟨rfl, a, b, Or.inl rfl⟩)
      (fun _ a b d _ => ⟨rfl, a, b, Or.inr ⟨rfl, d⟩⟩)) ?_
  rintro j' g fl V₁ ⟨hV₁, gs, g15, hj⟩ U t₁ hKU hAU hrU hgU -
  subst V₁ hgU
  have hsU : U.cpu.gpr.rsp = aR S := gs.trans hs
  have h15U : U.cpu.gpr.r15 = g0.r15 := g15.trans h15
  rcases hj with rfl | ⟨rfl, gdi⟩
  · exact from214 E hKU hAU hrU hsU h15U hIW
  · refine callK E hKU hAU hrU hsU (lt_len (by decide)) (call_209 _) tgt_209 E.cD (E.k209 _ hIW)
      (by show U.cpu.gpr.rdi = _; rw [gdi, hs]) ?_
    intro Z W' t₃ hKZ hAZ hrZ hsZ hkZ hIZ
    exact from214 E hKZ hAZ hrZ hsZ (hkZ.2.2.2.2.2.trans h15U) hIZ

/-- From 177 (back from the concatenation into the local): `Find (local, true)` on `this + 144` (`k193`), from its
return 198. -/
theorem from177 (E : Ev prof F Wl L s₀ o gev gP gE fb S g0 e₂ code₂ j₂ n it I J) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = oci_at.add 177) (hm : Fm S g0 Y.cpu.gpr) (hIW : I 0 W) :
    GoG prof L o gev gP gE Y t := by
  refine (c_177 prof fb).run E.c E.hfs E.hin (fun j' g' _ V' => j' = 193 ∧ V' = W ∧ Fr Y.cpu.gpr g' ∧
      g'.rsi = rdq(W, Y.cpu.gpr.rsp) ∧ g'.rdx = 1#64 ∧ g'.rdi = Y.cpu.gpr.rbx + 144#64) hK hA hr
    (vc_177 (by rw [hm.1]; exact E.f0) fun _ a b d e _ => ⟨rfl, rfl, a, b, d, e⟩) ?_
  rintro j' g fl V₁ ⟨rfl, hV₁, gf, gsi, gdx, gdi⟩ U t₁ hKU hAU hrU hgU -
  subst V₁ hgU
  have hmU := Fm.fr hm gf
  refine callK E hKU hAU hrU hmU.1 (lt_len (by decide)) (call_193 _) tgt_193 E.cF (E.k193 _ hIW)
    ⟨by show U.cpu.gpr.rdi = _; rw [gdi, hm.2.1], by show U.cpu.gpr.rsi = _; rw [gsi, hm.1], gdx⟩ ?_
  intro Z W' t₃ hKZ hAZ hrZ hsZ hkZ hIZ
  exact from198 E hKZ hAZ hrZ hsZ (hkZ.2.2.2.2.2.trans hmU.2.2.2.2) hIZ

/-- From 163 (back from `folderPrefix` copied to `this + 112`, `rbp` = `this + 112`): the concatenation
`this->_folderPrefix + fileName` into the local (`k172`), from its return 177. -/
theorem from163 (E : Ev prof F Wl L s₀ o gev gP gE fb S g0 e₂ code₂ j₂ n it I J) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = oci_at.add 163) (hm : Fm S g0 Y.cpu.gpr)
    (hbp : Y.cpu.gpr.rbp = g0.rdi + 112#64) (hIW : I 0 W) :
    GoG prof L o gev gP gE Y t := by
  refine (c_163 prof fb).run E.c E.hfs E.hin (fun j' g' _ V' => j' = 172 ∧ V' = W ∧ Fr Y.cpu.gpr g' ∧
      g'.rdi = Y.cpu.gpr.rsp ∧ g'.rdx = Y.cpu.gpr.r12 ∧ g'.rsi = Y.cpu.gpr.rbp) hK hA hr
    (vc_163 fun _ a b d e _ => ⟨rfl, rfl, a, b, d, e⟩) ?_
  rintro j' g fl V₁ ⟨rfl, hV₁, gf, gdi, gdx, gsi⟩ U t₁ hKU hAU hrU hgU -
  subst V₁ hgU
  have hmU := Fm.fr hm gf
  refine callK E hKU hAU hrU hmU.1 (lt_len (by decide)) (call_172 _) tgt_172 E.cC (E.k172 _ hIW)
    ⟨gdi.trans hm.1, gsi.trans hbp, gdx.trans hm.2.2.1⟩ ?_
  intro Z W' t₃ hKZ hAZ hrZ hsZ hkZ hIZ
  exact from177 E hKZ hAZ hrZ (fm_ret hmU hsZ hkZ) hIZ

/-- From 121 (after the loop): the stores of 0, `folderPrefix` copied to `this + 112` (`k158`), from its return
163. -/
theorem from121 (E : Ev prof F Wl L s₀ o gev gP gE fb S g0 e₂ code₂ j₂ n it I J) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = oci_at.add 121) (hm : Fm S g0 Y.cpu.gpr) (hIW : I 0 W) :
    GoG prof L o gev gP gE Y t := by
  have e112 : Y.cpu.gpr.rbx + 112#64 = g0.rdi + 112#64 := by rw [hm.2.1]
  refine (c_121 prof fb).run E.c E.hfs E.hin (fun j' g' _ V' => j' = 158 ∧ I 0 V' ∧ Fr Y.cpu.gpr g' ∧
      g'.rbp = Y.cpu.gpr.rbx + 112#64 ∧ g'.rsi = Y.cpu.gpr.r13 ∧ g'.rdi = Y.cpu.gpr.rbx + 112#64) hK hA hr
    (vc_121 (P := I 0) (by rw [hm.2.1]; exact E.w56) (by rw [hm.2.1]; exact E.w72) (by rw [hm.2.1]; exact E.w88)
      (by rw [hm.2.1]; exact E.w44) hIW (by rw [hm.2.1]; exact E.z56) (by rw [hm.2.1]; exact E.z72)
      (by rw [hm.2.1]; exact E.z88) (by rw [hm.2.1]; exact E.z44)
      fun _ _ a b d e i _ => ⟨rfl, a, b, d, e, i⟩) ?_
  rintro j' g fl V₁ ⟨rfl, hIV, gf, gbp, gsi, gdi⟩ U t₁ hKU hAU hrU hgU -
  subst hgU
  have hmU := Fm.fr hm gf
  refine callK E hKU hAU hrU hmU.1 (lt_len (by decide)) (call_158 _) tgt_158 E.cP (E.k158 _ hIV)
    ⟨gdi.trans e112, gsi.trans hm.2.2.2.1⟩ ?_
  intro Z W' t₃ hKZ hAZ hrZ hsZ hkZ hIZ
  exact from163 E hKZ hAZ hrZ (fm_ret hmU hsZ hkZ) (hkZ.2.1.trans (gbp.trans e112)) hIZ

/-- 98 (the step `k`, the item `p` with null chars or freed chars): `operator delete (p, 16)` (`k106`), from its
return to 111. -/
theorem A98 (E : Ev prof F Wl L s₀ o gev gP gE fb S g0 e₂ code₂ j₂ n it I J) (k : Nat) (hk : k < n)
    (p : BitVec 64) (hp : p ≠ 0)
    (h111 : AtJ prof F Wl L s₀ o gev gP gE 111 fun g W => I k W ∧ Fm S g0 g ∧ g.rbp = BitVec.ofNat 64 (8 * k)) :
    AtJ prof F Wl L s₀ o gev gP gE 98 fun g W => J k p W ∧ Fm S g0 g ∧ g.rbp = BitVec.ofNat 64 (8 * k) ∧
      g.r14 = p := by
  rintro Y W t hK hA hr ⟨hJ, hm, hb, h14⟩
  refine (c_98 prof fb).run E.c E.hfs E.hin (fun j' g' _ V' => j' = 106 ∧ V' = W ∧ Fr Y.cpu.gpr g' ∧
      g'.rbp = Y.cpu.gpr.rbp ∧ g'.rdi = Y.cpu.gpr.r14 ∧ g'.rsi = 16#64) hK hA hr
    (vc_98 fun _ a b d e _ => ⟨rfl, rfl, a, b, d, e⟩) ?_
  rintro j' g fl V₁ ⟨rfl, hV₁, gf, gbp, gdi, gsi⟩ U t₁ hKU hAU hrU hgU -
  subst V₁ hgU
  have hmU := Fm.fr hm gf
  refine callK E hKU hAU hrU hmU.1 (lt_len (by decide)) (call_106 _) tgt_106 E.cE (E.k106 k hk p W hp hJ)
    ⟨gdi.trans h14, gsi⟩ ?_
  intro Z W' t₃ hKZ hAZ hrZ hsZ hkZ hIZ
  exact h111 Z W' t₃ hKZ hAZ hrZ ⟨hIZ, fm_ret hmU hsZ hkZ, hkZ.2.1.trans (gbp.trans hb)⟩

/-- 72, the step `k` (`rbp` = `8 k`): the item `p` = `_items[k]`; null to 111, else its chars freed unless null
(`k93`) and to 98. -/
theorem B72 (E : Ev prof F Wl L s₀ o gev gP gE fb S g0 e₂ code₂ j₂ n it I J) (k : Nat) (hk : k < n)
    (h111 : AtJ prof F Wl L s₀ o gev gP gE 111 fun g W => I k W ∧ Fm S g0 g ∧ g.rbp = BitVec.ofNat 64 (8 * k)) :
    AtJ prof F Wl L s₀ o gev gP gE 72 fun g W => I (k + 1) W ∧ Fm S g0 g ∧ g.rbp = BitVec.ofNat 64 (8 * k) := by
  rintro Y W t hK hA hr ⟨hIk, hm, hb⟩
  have hit := E.hIt k hk W hIk
  have hea : it + Y.cpu.gpr.rbp = it + BitVec.ofNat 64 (8 * k) := by rw [hb]
  by_cases hp0 : pk W it k = 0
  · refine (c_72 prof fb).run E.c E.hfs E.hin (fun j' g' _ V' => j' = 111 ∧ V' = W ∧ Fr Y.cpu.gpr g' ∧
        g'.rbp = Y.cpu.gpr.rbp) hK hA hr
      (vc_72z (it := it) (p := pk W it k) (by rw [hm.2.1]; exact hit) (by rw [hm.2.1]; exact E.fa) (by rw [hea])
        (by rw [hea]; exact E.fe k hk) hp0 fun _ a b _ => ⟨rfl, rfl, a, b⟩) ?_
    rintro j' g fl V₁ ⟨rfl, hV₁, gf, gbp⟩ U t₁ hKU hAU hrU hgU -
    subst V₁ hgU
    exact h111 U W t₁ hKU hAU hrU ⟨E.hP0 k hk W hIk hp0, Fm.fr hm gf, gbp.trans hb⟩
  · have fpp := E.fp k hk W hIk hp0
    refine (c_72 prof fb).run E.c E.hfs E.hin (fun j' g' _ V' => V' = W ∧ Fr Y.cpu.gpr g' ∧
        g'.rbp = Y.cpu.gpr.rbp ∧ g'.r14 = pk W it k ∧ ((rdq(W, pk W it k) = 0 ∧ j' = 98) ∨
          (rdq(W, pk W it k) ≠ 0 ∧ j' = 93 ∧ g'.rdi = rdq(W, pk W it k)))) hK hA hr
      (vc_72n (it := it) (p := pk W it k) (q := rdq(W, pk W it k)) (by rw [hm.2.1]; exact hit)
        (by rw [hm.2.1]; exact E.fa) (by rw [hea]) (by rw [hea]; exact E.fe k hk) hp0 rfl fpp
        (fun hq _ a b d _ => ⟨rfl, a, b, d, Or.inl ⟨hq, rfl⟩⟩)
        (fun hq _ a b d e _ => ⟨rfl, a, b, d, Or.inr ⟨hq, rfl, e⟩⟩)) ?_
    rintro j' g fl V₁ ⟨hV₁, gf, gbp, g14, hj⟩ U t₁ hKU hAU hrU hgU -
    subst V₁ hgU
    have hmU := Fm.fr hm gf
    have hbU : U.cpu.gpr.rbp = BitVec.ofNat 64 (8 * k) := gbp.trans hb
    rcases hj with ⟨hq0, rfl⟩ | ⟨hq0, rfl, gdi⟩
    · exact A98 E k hk _ hp0 h111 U W t₁ hKU hAU hrU ⟨E.hQ0 k hk W hIk hp0 hq0, hmU, hbU, g14⟩
    · refine callK E hKU hAU hrU hmU.1 (lt_len (by decide)) (call_93 _) tgt_93 E.cD
        (E.k93 k hk W hIk hp0 hq0) gdi ?_
      intro Z W' t₃ hKZ hAZ hrZ hsZ hkZ hJZ
      exact A98 E k hk _ hp0 h111 Z W' t₃ hKZ hAZ hrZ
        ⟨hJZ, fm_ret hmU hsZ hkZ, hkZ.2.1.trans hbU, hkZ.2.2.2.2.1.trans g14⟩

/-- 111, the step `k`: `rbp` -= 8; after the step 0 to 121, else to 72 with the step `k - 1` (`hnx`). -/
theorem S111 (E : Ev prof F Wl L s₀ o gev gP gE fb S g0 e₂ code₂ j₂ n it I J) (k : Nat) (hk : k < n)
    (hnx : ∀ k', k = k' + 1 → AtJ prof F Wl L s₀ o gev gP gE 72 fun g W => I (k' + 1) W ∧ Fm S g0 g ∧
      g.rbp = BitVec.ofNat 64 (8 * k')) :
    AtJ prof F Wl L s₀ o gev gP gE 111 fun g W => I k W ∧ Fm S g0 g ∧ g.rbp = BitVec.ofNat 64 (8 * k) := by
  rintro Y W t hK hA hr ⟨hIk, hm, hb⟩
  have hn := E.hn
  cases k with
  | zero =>
    refine (c_111 prof fb).run E.c E.hfs E.hin (fun j' g' _ V' => j' = 121 ∧ V' = W ∧ Fr Y.cpu.gpr g') hK hA hr
      (vc_111l (by rw [hb]; exact rb_last) fun _ a _ => ⟨rfl, rfl, a⟩) ?_
    rintro j' g fl V₁ ⟨rfl, hV₁, gf⟩ U t₁ hKU hAU hrU hgU -
    subst V₁ hgU
    exact from121 E hKU hAU hrU (Fm.fr hm gf) hIk
  | succ k =>
    refine (c_111 prof fb).run E.c E.hfs E.hin (fun j' g' _ V' => j' = 72 ∧ V' = W ∧ Fr Y.cpu.gpr g' ∧
        g'.rbp = Y.cpu.gpr.rbp - 8#64) hK hA hr
      (vc_111c (by rw [hb, rb_step k (by omega)]; exact rb_ne k (by omega)) fun _ a b _ => ⟨rfl, rfl, a, b⟩) ?_
    rintro j' g fl V₁ ⟨rfl, hV₁, gf, gbp⟩ U t₁ hKU hAU hrU hgU -
    subst V₁ hgU
    exact hnx k rfl U W t₁ hKU hAU hrU ⟨hIk, Fm.fr hm gf, by rw [gbp, hb]; exact rb_step k (by omega)⟩

/-- The loop, by induction on the step. -/
theorem L72 (E : Ev prof F Wl L s₀ o gev gP gE fb S g0 e₂ code₂ j₂ n it I J) : ∀ k, k < n →
    AtJ prof F Wl L s₀ o gev gP gE 72 fun g W => I (k + 1) W ∧ Fm S g0 g ∧ g.rbp = BitVec.ofNat 64 (8 * k) := by
  intro k
  induction k with
  | zero => exact fun hk => B72 E 0 hk (S111 E 0 hk fun k' e => absurd e (by omega))
  | succ k ih =>
    exact fun hk => B72 E (k + 1) hk (S111 E (k + 1) hk fun k' e => by
      obtain rfl : k = k' := by omega
      exact ih (by omega))

end Runs

variable {prof : Profile} {F : Footprint} {Wl : List Rgn} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {X : State} {t : Nat} {V : Addr → Byte}

/-- `COpenCallbackImp::Init2 (folderPrefix, fileName)` (`this` = `rdi`, `folderPrefix` = `rsi`, `fileName` = `rdx`)
from its entry, `fb` the `fs` base: the pushes' slots, the guard's slot, the calls' return address slot and the four
stores of 0 in what the run may store into; the local, the return address, the guard at `fs:0x28`, the size, `_items`
and the items readable. The first callee (`k48`, `rdi` = `this + 0x108`) returns with the size `n32` and bytes with
`I n32`; `I (k + 1)` keeps `_items` (`hIt`), and gives `I k` when `_items[k]` is null (`hP0`), `J k p` when its chars
are null (`hQ0`); the chars' `delete[]` (`k93`) gives `J k p`, the item's `operator delete` (`k106`) gives `I k`.
`I 0` survives the stores of 0 (`z56`–`z44`), is kept by the other callees (`k158`: `folderPrefix` copied to
`this + 112`, `k172`: the concatenation into the local, `k193`: `Find` on `this + 144`, `k209`: the local's
`delete[]`, `k256`), and gives the stack (`hI`). At the return address (`kr`): `rsp` 8 above the entry's, the
callee-saved registers as they were, bytes with `I 0`. -/
theorem oci_ok {fb : Addr} {n32 : BitVec 32} {it : BitVec 64} {I : Nat → (Addr → Byte) → Prop}
    {J : Nat → BitVec 64 → (Addr → Byte) → Prop} {e₂ : Addr} {code₂ : List Byte} {j₂ : Nat}
    (c : Seg prof F Wl L s₀ o) (hfs : s₀.cpu.seg.fsBase = fb) (hin : CodeIn L oci_at oci)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = oci_at)
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
    (fn : ∀ i < 4, Foot F.data (Addr.add (X.cpu.gpr.rdi + 56#64) i))
    (fa : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rdi + 48#64) i))
    (w56 : ∀ i < 4, Foot Wl (Addr.add (X.cpu.gpr.rdi + 56#64) i))
    (w72 : ∀ i < 4, Foot Wl (Addr.add (X.cpu.gpr.rdi + 72#64) i))
    (w88 : ∀ i < 4, Foot Wl (Addr.add (X.cpu.gpr.rdi + 88#64) i))
    (w44 : ∀ i < 2, Foot Wl (Addr.add (X.cpu.gpr.rdi + 44#64) i))
    (fe : ∀ k < n32.toNat, ∀ i < 8, Foot F.data (Addr.add (it + BitVec.ofNat 64 (8 * k)) i))
    (fp : ∀ k < n32.toNat, ∀ W, I (k + 1) W → pk W it k ≠ 0 → ∀ i < 8, Foot F.data (Addr.add (pk W it k) i))
    (hIt : ∀ k < n32.toNat, ∀ W, I (k + 1) W → rdq(W, X.cpu.gpr.rdi + 48#64) = it)
    (hP0 : ∀ k < n32.toNat, ∀ W, I (k + 1) W → pk W it k = 0 → I k W)
    (hQ0 : ∀ k < n32.toNat, ∀ W, I (k + 1) W → pk W it k ≠ 0 → rdq(W, pk W it k) = 0 → J k (pk W it k) W)
    (hI : ∀ W, I 0 W → Stk fb W X.cpu.gpr.rsp X.cpu.gpr (e₂.add j₂))
    (z56 : ∀ W bs, I 0 W → I 0 (Vst W (X.cpu.gpr.rdi + 56#64) bs))
    (z72 : ∀ W bs, I 0 W → I 0 (Vst W (X.cpu.gpr.rdi + 72#64) bs))
    (z88 : ∀ W bs, I 0 W → I 0 (Vst W (X.cpu.gpr.rdi + 88#64) bs))
    (z44 : ∀ W bs, I 0 W → I 0 (Vst W (X.cpu.gpr.rdi + 44#64) bs))
    (cA : ∃ code : List Byte, CodeIn L 0x5b3260#64 code ∧ 0 < code.length)
    (cD : ∃ code : List Byte, CodeIn L 0x6014f0#64 code ∧ 0 < code.length)
    (cE : ∃ code : List Byte, CodeIn L 0x6014e0#64 code ∧ 0 < code.length)
    (cP : ∃ code : List Byte, CodeIn L 0x44c550#64 code ∧ 0 < code.length)
    (cC : ∃ code : List Byte, CodeIn L 0x44c2b0#64 code ∧ 0 < code.length)
    (cF : ∃ code : List Byte, CodeIn L 0x455b80#64 code ∧ 0 < code.length)
    (cG : ∃ code : List Byte, CodeIn L 0x456000#64 code ∧ 0 < code.length)
    (k48 : KC prof F Wl L s₀ o gev gP gE X.cpu.gpr.rsp 0x5b3260#64 53 (V0 fb V X.cpu.gpr)
      (fun g => g.rdi = X.cpu.gpr.rdi + 264#64) (fun W => I n32.toNat W ∧ rdd(W, X.cpu.gpr.rdi + 56#64) = n32))
    (k93 : ∀ k < n32.toNat, ∀ W, I (k + 1) W → pk W it k ≠ 0 → rdq(W, pk W it k) ≠ 0 →
      KC prof F Wl L s₀ o gev gP gE X.cpu.gpr.rsp 0x6014f0#64 98 W (fun g => g.rdi = rdq(W, pk W it k))
        (J k (pk W it k)))
    (k106 : ∀ k < n32.toNat, ∀ p W, p ≠ 0 → J k p W →
      KC prof F Wl L s₀ o gev gP gE X.cpu.gpr.rsp 0x6014e0#64 111 W (fun g => g.rdi = p ∧ g.rsi = 16#64) (I k))
    (k158 : ∀ W, I 0 W → KC prof F Wl L s₀ o gev gP gE X.cpu.gpr.rsp 0x44c550#64 163 W
      (fun g => g.rdi = X.cpu.gpr.rdi + 112#64 ∧ g.rsi = X.cpu.gpr.rsi) (I 0))
    (k172 : ∀ W, I 0 W → KC prof F Wl L s₀ o gev gP gE X.cpu.gpr.rsp 0x44c2b0#64 177 W
      (fun g => g.rdi = aR X.cpu.gpr.rsp ∧ g.rsi = X.cpu.gpr.rdi + 112#64 ∧ g.rdx = X.cpu.gpr.rdx) (I 0))
    (k193 : ∀ W, I 0 W → KC prof F Wl L s₀ o gev gP gE X.cpu.gpr.rsp 0x455b80#64 198 W
      (fun g => g.rdi = X.cpu.gpr.rdi + 144#64 ∧ g.rsi = rdq(W, aR X.cpu.gpr.rsp) ∧ g.rdx = 1#64) (I 0))
    (k209 : ∀ W, I 0 W → KC prof F Wl L s₀ o gev gP gE X.cpu.gpr.rsp 0x6014f0#64 214 W
      (fun g => g.rdi = rdq(W, aR X.cpu.gpr.rsp)) (I 0))
    (k256 : ∀ W, I 0 W → KC prof F Wl L s₀ o gev gP gE X.cpu.gpr.rsp 0x456000#64 261 W (fun _ => True) (I 0))
    (kr : ∀ (W : Addr → Byte) (Z' : State) (t' : Nat), KeptW Wl s₀ Z' → Agree F Z'.proc.mm.mem W →
      Z'.cpu.rip = e₂.add j₂ → Z'.cpu.gpr.rsp = X.cpu.gpr.rsp + 8 → KS X.cpu.gpr Z'.cpu.gpr → I 0 W →
      GoG prof L o gev gP gE Z' t') :
    GoG prof L o gev gP gE X t := by
  have E : Ev prof F Wl L s₀ o gev gP gE fb X.cpu.gpr.rsp X.cpu.gpr e₂ code₂ j₂ n32.toNat it I J :=
    { c := c, hfs := hfs, hin := hin, hin₂ := hin₂, h₂ := h₂, hn := n32.isLt, hI := hI, hcl := hcl,
      fg := fun i hi => c.hws _ (hw i hi), f0 := f0,
      fb40 := fun i hi => c.hws _ (hs5 i hi), fb32 := fun i hi => c.hws _ (hs4 i hi),
      fb24 := fun i hi => c.hws _ (hs3 i hi), fb16 := fun i hi => c.hws _ (hs2 i hi),
      fb8 := fun i hi => c.hws _ (hs1 i hi), hl := hl, hr8 := hr8, fa := fa,
      w56 := w56, w72 := w72, w88 := w88, w44 := w44, fe := fe, fp := fp, hIt := hIt, hP0 := hP0, hQ0 := hQ0,
      z56 := z56, z72 := z72, z88 := z88, z44 := z44,
      cD := cD, cE := cE, cP := cP, cC := cC, cF := cF, cG := cG,
      k93 := k93, k106 := k106, k158 := k158, k172 := k172, k193 := k193, k209 := k209, k256 := k256, kr := kr }
  -- the prologue, to the first `call`
  have hrip' : X.cpu.rip = oci_at.add 0 := by rw [addr_add_zero]; exact hrip
  refine (c_0 prof fb).run c hfs hin (fun j' g' _ V' => j' = 48 ∧ V' = V0 fb V X.cpu.gpr ∧
      Fm X.cpu.gpr.rsp X.cpu.gpr g' ∧ g'.rdi = X.cpu.gpr.rdi + 264#64) hK hA hrip'
    (vc_0 rfl hs1 hs2 hs3 hs4 hs5 hcl hw fun _ a b d e i r _ => ⟨rfl, rfl, ⟨a, b, d, e, i⟩, r⟩) ?_
  rintro j' g fl V₁ ⟨rfl, hV₁, hm, gdi⟩ Y t₁ hKY hAY hrY hgY -
  subst V₁ hgY
  refine callK E hKY hAY hrY hm.1 (lt_len (by decide)) (call_48 _) tgt_48 cA k48 gdi ?_
  intro Z W' t₃ hKZ hAZ hrZ hsZ hkZ ⟨hIn, hn⟩
  have hmZ := fm_ret hm hsZ hkZ
  have hn' : rdd(W', Z.cpu.gpr.rbx + 56#64) = n32 := by rw [hmZ.2.1]; exact hn
  have fn' : ∀ i < 4, Foot F.data (Addr.add (Z.cpu.gpr.rbx + 56#64) i) := by rw [hmZ.2.1]; exact fn
  -- 53: the size 0 to 121, else the loop from the step `n32 - 1`
  by_cases hn0 : n32 = 0
  · refine (c_53 prof fb).run c hfs hin (fun j' g' _ V' => j' = 121 ∧ V' = W' ∧ Fr Z.cpu.gpr g') hKZ hAZ hrZ
      (vc_53z hn' hn0 fn' fun _ a _ => ⟨rfl, rfl, a⟩) ?_
    rintro j' g fl V₁ ⟨rfl, hV₁, gf⟩ U t₄ hKU hAU hrU hgU -
    subst V₁ hgU
    have e0 : n32.toNat = 0 := (congrArg BitVec.toNat hn0).trans rfl
    exact from121 E hKU hAU hrU (Fm.fr hmZ gf) (e0 ▸ hIn)
  · refine (c_53 prof fb).run c hfs hin (fun j' g' _ V' => j' = 72 ∧ V' = W' ∧ Fr Z.cpu.gpr g' ∧
        g'.rbp = rbx0 n32) hKZ hAZ hrZ (vc_53n hn' hn0 fn' fun _ a b _ => ⟨rfl, rfl, a, b⟩) ?_
    rintro j' g fl V₁ ⟨rfl, hV₁, gf, gbp⟩ U t₄ hKU hAU hrU hgU -
    subst V₁ hgU
    have hnz : n32.toNat ≠ 0 := fun e => hn0 (BitVec.eq_of_toNat_eq (e.trans rfl))
    have e1 : n32.toNat - 1 + 1 = n32.toNat := by omega
    exact L72 E (n32.toNat - 1) (by omega) U W' t₄ hKU hAU hrU
      ⟨by rw [e1]; exact hIn, Fm.fr hmZ gf, by rw [gbp, rbx0_eq hn0]⟩

end FV7z.Oci
