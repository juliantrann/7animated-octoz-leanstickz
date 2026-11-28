import FV7z.Cpr.Cuts
import FV7z.Ais.Holds
import FV7z.Ocv.Holds
/-!
# `NWildcard::CCensorNode::CheckPathToRoot` (PLAN.md §M, M1): the run through the callees

7-Zip 26.06's `NWildcard::CCensorNode::CheckPathToRoot (include, pathParts, isFile)` at `0x454330` in `7zzs`
(`CPP/Common/Wildcard.cpp`; `objdump -d`): `this` = `rdi` (`rbx`), `include` = `sil` (`r13d`), `pathParts` = `rdx`
(`rbp`, a `CObjectVector<UString>`: `_items` at `+ 0`, `_size` at `+ 8`), `isFile` = `cl` (`r14d`). `S` the stack
pointer and `g0` the registers at the entry: six pushes and `sub rsp, 0x48` (`aR S`), the stack guard (`fs:0x28`) at
`aR S + 56`, a local `UStringVector pathParts2` at `aR S + 32` (`_items` at `+ 32`, `_size` at `+ 40`, `_capacity` at
`+ 44`), scratch slots at `+ 8`, `+ 16`, `+ 24`.

The code: `CheckPathCurrent (include, pathParts, isFile)` (54, `0x453050`); its `al` not 0, or `Parent` (the 8
bytes at `this`) null, to the epilogue (333). Else (80) `pathParts2` cleared, `operator new [] (8)` (112), (117)
`_items` and `_size` null in this run (`h117`), (146) `_items` = the new array, `_capacity` = 1, `operator new (0x10)`
(169), the `UString` copy of `this + 8` (183, `0x44d5d0`), (188) appended (`_size` + 1, `_items[_size]` = the copy);
`pathParts._size` (`nn`) 0 to 221, else (416) the throws (425 `js`, 434 `ja`), the growth (440..677) and the copy loop
(480..553) appending `pathParts` to `pathParts2`, to 221. At 221 `Parent->CheckPathToRoot_Change (include,
pathParts2, isFile)` (238, `0x4530c0`), its `al` the result (`r12d`); (243) `pathParts2` destroyed from its last item
down (the loop 272..321, `rbx` = `8 k`): an item `p` not null has its chars freed unless null (290, `operator delete
[]` at `0x6014f0`) and is freed (303, `operator delete (p, 16)` at `0x6014e0`); `rdi` reloaded from `_items` (308);
(323) `_items` freed unless null (328); at 333 the guard's check, the epilogue, `ret` (370). Not covered here: the run
from 425 (the growth and the copy loop: an `AtJ 425` hypothesis, `h425`), `__stack_chk_fail` (679), the landing pads.

The callees are continuations (`KC`, as in `FV7z/Oci/Holds.lean`, the bytes and the registers at the return tied by
`J`): from the return the run goes on with `rsp` as it was and the callee-saved registers (`KS`) as at the `call`. The
bytes are tracked by invariants the caller chooses, each tied to the stores the code makes: `I0` from the prologue on
(`k54` keeps it), `I1` after the two stores of 0 (`z80`), `I2` (with the registers) after `operator new []`, whose
`_items` and `_size` slots are 0 (`h117`), `I3` after the stores at 146 (`z146`), `I4 r` after `operator new (0x10)`
returned `r`, `I5 r` after the copy into `r`, with the slot `_items[_size]` writable (`wsl`); after the append
(`St188`) `P` when `nn` is 0 (`z221`), else `Q4 nn (_size + 1)` (`z425`). From 221: `P` gives `D A N` (`k238`) with
`A`, `N` the vector's `_items` and `_size` as stored; the destruction keeps `D A k` (`k` the items left, `hP0`, `k303`)
and `Jd A k p` (the item `p`'s chars freed, `hQ0`, `k290`), `D` gives `_items` back at `aR S + 32` (`hDa`); `D 0 0`
(`hA0`) or the free of `_items` (`k328`) gives `Iz`, which gives the stack and the guard (`hIz`). The loop by induction
on the step (`L272`, as `Oci.L72`). No byte of the frame is read back by this module: what a slot holds is what the
invariants say, so a caller makes them as strong as the stores allow.

- `inc32`: `_size + 1`; `aR`, `q1`–`q7`, `V0`, `Gd`, `St188`, `Fm`, `Fr`, `Lp`, `KC`, `AtJ`, `Ev`: the frame, the
  bytes after the prologue, the guard, the bytes after the append, what a piece keeps, the loop's frame, the callees,
  the runs from an offset, the hypotheses of the runs; `callK`: a `call`.
- `vc_*`: the pieces; `tail333`, `from323`, `A295`, `B272`, `S313`, `L272`, `from243`, `from221`, `from188`,
  `from174`, `from117`, `from59`: the runs from the cut points.
- `cpr_ok`: from the entry to the return address, the run from 425 a hypothesis.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
open FV7z.Api (P6 Stk KS)
open FV7z.Ais (nz32)
open FV7z.Ocv (pk rbx0 rbx0_eq rb_step rb_ne rb_last)
namespace FV7z.Cpr
set_option linter.unusedVariables false

/-! ## The instructions outside the blocks -/

/-- The `js` to the throw. -/
def pjs : List Byte := [0x0f, 0x88, 0xfb, 0xd4, 0xfa, 0xff]
theorem pjs_0 : ∀ feat, Dec feat pjs 0 (FV7z.mk (.jcc 8) 64 [.rel 18446744073709212923] 6) := by dec_rfl
theorem wjs_425 : pjs <+: cpr.drop 425 := by decide +kernel
theorem js_425 (feat : Features) : Dec feat cpr 425 (FV7z.mk (.jcc 8) 64 [.rel 18446744073709212923] 6) :=
  Dec.shift (j := 425) (k := 0) (pjs_0 feat) wjs_425 (Nat.zero_le _)

/-- The `ja` to the throw. -/
def pja : List Byte := [0x0f, 0x87, 0xf2, 0xd4, 0xfa, 0xff]
theorem pja_0 : ∀ feat, Dec feat pja 0 (FV7z.mk (.jcc 7) 64 [.rel 18446744073709212914] 6) := by dec_rfl
theorem wja_434 : pja <+: cpr.drop 434 := by decide +kernel
theorem ja_434 (feat : Features) : Dec feat cpr 434 (FV7z.mk (.jcc 7) 64 [.rel 18446744073709212914] 6) :=
  Dec.shift (j := 434) (k := 0) (pja_0 feat) wja_434 (Nat.zero_le _)

/-- The `call` of `CheckPathCurrent` (`0x453050`). -/
def pc54 : List Byte := [0xe8, 0xe5, 0xec, 0xff, 0xff]
theorem pc54_0 : ∀ feat, Dec feat pc54 0 (FV7z.mk .call 64 [.rel 18446744073709546725] 5) := by dec_rfl
theorem wc_54 : pc54 <+: cpr.drop 54 := by decide +kernel
theorem call_54 (feat : Features) : Dec feat cpr 54 (FV7z.mk .call 64 [.rel 18446744073709546725] 5) :=
  Dec.shift (j := 54) (k := 0) (pc54_0 feat) wc_54 (Nat.zero_le _)
theorem tgt_54 : cpr_at.add (54 + 5) + BitVec.ofNat 64 18446744073709546725 = 0x453050#64 := by decide

/-- The `call` of `operator new []` (`0x6029b0`). -/
def pc112 : List Byte := [0xe8, 0x0b, 0xe6, 0x1a, 0x00]
theorem pc112_0 : ∀ feat, Dec feat pc112 0 (FV7z.mk .call 64 [.rel 1762827] 5) := by dec_rfl
theorem wc_112 : pc112 <+: cpr.drop 112 := by decide +kernel
theorem call_112 (feat : Features) : Dec feat cpr 112 (FV7z.mk .call 64 [.rel 1762827] 5) :=
  Dec.shift (j := 112) (k := 0) (pc112_0 feat) wc_112 (Nat.zero_le _)
theorem tgt_112 : cpr_at.add (112 + 5) + BitVec.ofNat 64 1762827 = 0x6029b0#64 := by decide

/-- The `call` of `operator new` (`0x602970`). -/
def pc169 : List Byte := [0xe8, 0x92, 0xe5, 0x1a, 0x00]
theorem pc169_0 : ∀ feat, Dec feat pc169 0 (FV7z.mk .call 64 [.rel 1762706] 5) := by dec_rfl
theorem wc_169 : pc169 <+: cpr.drop 169 := by decide +kernel
theorem call_169 (feat : Features) : Dec feat cpr 169 (FV7z.mk .call 64 [.rel 1762706] 5) :=
  Dec.shift (j := 169) (k := 0) (pc169_0 feat) wc_169 (Nat.zero_le _)
theorem tgt_169 : cpr_at.add (169 + 5) + BitVec.ofNat 64 1762706 = 0x602970#64 := by decide

/-- The `call` of the `UString` copy (`0x44d5d0`). -/
def pc183 : List Byte := [0xe8, 0xe4, 0x91, 0xff, 0xff]
theorem pc183_0 : ∀ feat, Dec feat pc183 0 (FV7z.mk .call 64 [.rel 18446744073709523428] 5) := by dec_rfl
theorem wc_183 : pc183 <+: cpr.drop 183 := by decide +kernel
theorem call_183 (feat : Features) : Dec feat cpr 183 (FV7z.mk .call 64 [.rel 18446744073709523428] 5) :=
  Dec.shift (j := 183) (k := 0) (pc183_0 feat) wc_183 (Nat.zero_le _)
theorem tgt_183 : cpr_at.add (183 + 5) + BitVec.ofNat 64 18446744073709523428 = 0x44d5d0#64 := by decide

/-- The `call` of `Parent->CheckPathToRoot_Change` (`0x4530c0`). -/
def pc238 : List Byte := [0xe8, 0x9d, 0xec, 0xff, 0xff]
theorem pc238_0 : ∀ feat, Dec feat pc238 0 (FV7z.mk .call 64 [.rel 18446744073709546653] 5) := by dec_rfl
theorem wc_238 : pc238 <+: cpr.drop 238 := by decide +kernel
theorem call_238 (feat : Features) : Dec feat cpr 238 (FV7z.mk .call 64 [.rel 18446744073709546653] 5) :=
  Dec.shift (j := 238) (k := 0) (pc238_0 feat) wc_238 (Nat.zero_le _)
theorem tgt_238 : cpr_at.add (238 + 5) + BitVec.ofNat 64 18446744073709546653 = 0x4530c0#64 := by decide

/-- The `call` of `operator delete []` (`0x6014f0`). -/
def pc290 : List Byte := [0xe8, 0x99, 0xd0, 0x1a, 0x00]
theorem pc290_0 : ∀ feat, Dec feat pc290 0 (FV7z.mk .call 64 [.rel 1757337] 5) := by dec_rfl
theorem wc_290 : pc290 <+: cpr.drop 290 := by decide +kernel
theorem call_290 (feat : Features) : Dec feat cpr 290 (FV7z.mk .call 64 [.rel 1757337] 5) :=
  Dec.shift (j := 290) (k := 0) (pc290_0 feat) wc_290 (Nat.zero_le _)
theorem tgt_290 : cpr_at.add (290 + 5) + BitVec.ofNat 64 1757337 = 0x6014f0#64 := by decide

/-- The `call` of `operator delete` (`0x6014e0`). -/
def pc303 : List Byte := [0xe8, 0x7c, 0xd0, 0x1a, 0x00]
theorem pc303_0 : ∀ feat, Dec feat pc303 0 (FV7z.mk .call 64 [.rel 1757308] 5) := by dec_rfl
theorem wc_303 : pc303 <+: cpr.drop 303 := by decide +kernel
theorem call_303 (feat : Features) : Dec feat cpr 303 (FV7z.mk .call 64 [.rel 1757308] 5) :=
  Dec.shift (j := 303) (k := 0) (pc303_0 feat) wc_303 (Nat.zero_le _)
theorem tgt_303 : cpr_at.add (303 + 5) + BitVec.ofNat 64 1757308 = 0x6014e0#64 := by decide

/-- The `call` of `operator delete []` (`0x6014f0`). -/
def pc328 : List Byte := [0xe8, 0x73, 0xd0, 0x1a, 0x00]
theorem pc328_0 : ∀ feat, Dec feat pc328 0 (FV7z.mk .call 64 [.rel 1757299] 5) := by dec_rfl
theorem wc_328 : pc328 <+: cpr.drop 328 := by decide +kernel
theorem call_328 (feat : Features) : Dec feat cpr 328 (FV7z.mk .call 64 [.rel 1757299] 5) :=
  Dec.shift (j := 328) (k := 0) (pc328_0 feat) wc_328 (Nat.zero_le _)
theorem tgt_328 : cpr_at.add (328 + 5) + BitVec.ofNat 64 1757299 = 0x6014f0#64 := by decide

/-- The `call` of `operator new` (`0x602970`). -/
def pc503 : List Byte := [0xe8, 0x44, 0xe4, 0x1a, 0x00]
theorem pc503_0 : ∀ feat, Dec feat pc503 0 (FV7z.mk .call 64 [.rel 1762372] 5) := by dec_rfl
theorem wc_503 : pc503 <+: cpr.drop 503 := by decide +kernel
theorem call_503 (feat : Features) : Dec feat cpr 503 (FV7z.mk .call 64 [.rel 1762372] 5) :=
  Dec.shift (j := 503) (k := 0) (pc503_0 feat) wc_503 (Nat.zero_le _)
theorem tgt_503 : cpr_at.add (503 + 5) + BitVec.ofNat 64 1762372 = 0x602970#64 := by decide

/-- The `call` of the `UString` copy (`0x44d5d0`). -/
def pc519 : List Byte := [0xe8, 0x94, 0x90, 0xff, 0xff]
theorem pc519_0 : ∀ feat, Dec feat pc519 0 (FV7z.mk .call 64 [.rel 18446744073709523092] 5) := by dec_rfl
theorem wc_519 : pc519 <+: cpr.drop 519 := by decide +kernel
theorem call_519 (feat : Features) : Dec feat cpr 519 (FV7z.mk .call 64 [.rel 18446744073709523092] 5) :=
  Dec.shift (j := 519) (k := 0) (pc519_0 feat) wc_519 (Nat.zero_le _)
theorem tgt_519 : cpr_at.add (519 + 5) + BitVec.ofNat 64 18446744073709523092 = 0x44d5d0#64 := by decide

/-- The `call` of `operator new []` (`0x6029b0`). -/
def pc593 : List Byte := [0xe8, 0x2a, 0xe4, 0x1a, 0x00]
theorem pc593_0 : ∀ feat, Dec feat pc593 0 (FV7z.mk .call 64 [.rel 1762346] 5) := by dec_rfl
theorem wc_593 : pc593 <+: cpr.drop 593 := by decide +kernel
theorem call_593 (feat : Features) : Dec feat cpr 593 (FV7z.mk .call 64 [.rel 1762346] 5) :=
  Dec.shift (j := 593) (k := 0) (pc593_0 feat) wc_593 (Nat.zero_le _)
theorem tgt_593 : cpr_at.add (593 + 5) + BitVec.ofNat 64 1762346 = 0x6029b0#64 := by decide

/-- The `call` of `memcpy` (`0x401070`). -/
def pc659 : List Byte := [0xe8, 0xa8, 0xca, 0xfa, 0xff]
theorem pc659_0 : ∀ feat, Dec feat pc659 0 (FV7z.mk .call 64 [.rel 18446744073709210280] 5) := by dec_rfl
theorem wc_659 : pc659 <+: cpr.drop 659 := by decide +kernel
theorem call_659 (feat : Features) : Dec feat cpr 659 (FV7z.mk .call 64 [.rel 18446744073709210280] 5) :=
  Dec.shift (j := 659) (k := 0) (pc659_0 feat) wc_659 (Nat.zero_le _)
theorem tgt_659 : cpr_at.add (659 + 5) + BitVec.ofNat 64 18446744073709210280 = 0x401070#64 := by decide

/-- The `call` of `operator delete []` (`0x6014f0`). -/
def pc672 : List Byte := [0xe8, 0x1b, 0xcf, 0x1a, 0x00]
theorem pc672_0 : ∀ feat, Dec feat pc672 0 (FV7z.mk .call 64 [.rel 1756955] 5) := by dec_rfl
theorem wc_672 : pc672 <+: cpr.drop 672 := by decide +kernel
theorem call_672 (feat : Features) : Dec feat cpr 672 (FV7z.mk .call 64 [.rel 1756955] 5) :=
  Dec.shift (j := 672) (k := 0) (pc672_0 feat) wc_672 (Nat.zero_le _)
theorem tgt_672 : cpr_at.add (672 + 5) + BitVec.ofNat 64 1756955 = 0x6014f0#64 := by decide

/-- The `ret`. -/
def pret : List Byte := [0xc3]
theorem pret_0 : ∀ feat, Dec feat pret 0 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem wt_370 : pret <+: cpr.drop 370 := by decide +kernel
theorem ret_370 (feat : Features) : Dec feat cpr 370 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 370) (k := 0) (pret_0 feat) wt_370 (Nat.zero_le _)

/-! ## Values -/

/-- `lea edx, [rax + 1]` with `rax` the zero-extended size `n`: `n + 1`. -/
theorem inc32 (n : BitVec 32) : BitVec.setWidth 32 (BitVec.setWidth 64 n + 1#64) = n + 1#32 := by
  apply BitVec.eq_of_toNat_eq
  have h2 : n.toNat < 4294967296 := n.isLt
  have l64 : 4294967297 ≤ 2 ^ 64 := by decide
  have eA : (BitVec.setWidth 64 n).toNat = n.toNat := by
    rw [BitVec.toNat_setWidth]
    exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le h2 (Nat.le_trans (Nat.le_succ _) l64))
  have eB : (BitVec.setWidth 64 n + 1#64).toNat = n.toNat + 1 := by
    rw [BitVec.toNat_add, eA, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 1) (b := 2 ^ 64) (by decide)]
    exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (Nat.succ_lt_succ h2) l64)
  rw [BitVec.toNat_setWidth, eB, BitVec.toNat_add, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (a := 1) (b := 2 ^ 32) (by decide)]

/-- `jne` not taken after `test x, x`. -/
theorem z32 {x : BitVec 32} (h : (!(x &&& x == 0)) = false) : x = 0 := by
  simpa [BitVec.and_self] using h

/-! ## The frame -/

/-- The stack pointer after the six pushes and `sub rsp, 0x48`. -/
abbrev aR (S : Addr) : Addr := S - 8 - 8 - 8 - 8 - 8 - 8 - 72#64

theorem q1 (S : Addr) : aR S + 72#64 = S - 8 - 8 - 8 - 8 - 8 - 8 := by
  show S - 8 - 8 - 8 - 8 - 8 - 8 - 72#64 + 72#64 = _; bv_omega
theorem q2 (S : Addr) : aR S + 72#64 + 8 = S - 8 - 8 - 8 - 8 - 8 := by
  show S - 8 - 8 - 8 - 8 - 8 - 8 - 72#64 + 72#64 + 8 = _; bv_omega
theorem q3 (S : Addr) : aR S + 72#64 + 8 + 8 = S - 8 - 8 - 8 - 8 := by
  show S - 8 - 8 - 8 - 8 - 8 - 8 - 72#64 + 72#64 + 8 + 8 = _; bv_omega
theorem q4 (S : Addr) : aR S + 72#64 + 8 + 8 + 8 = S - 8 - 8 - 8 := by
  show S - 8 - 8 - 8 - 8 - 8 - 8 - 72#64 + 72#64 + 8 + 8 + 8 = _; bv_omega
theorem q5 (S : Addr) : aR S + 72#64 + 8 + 8 + 8 + 8 = S - 8 - 8 := by
  show S - 8 - 8 - 8 - 8 - 8 - 8 - 72#64 + 72#64 + 8 + 8 + 8 + 8 = _; bv_omega
theorem q6 (S : Addr) : aR S + 72#64 + 8 + 8 + 8 + 8 + 8 = S - 8 := by
  show S - 8 - 8 - 8 - 8 - 8 - 8 - 72#64 + 72#64 + 8 + 8 + 8 + 8 + 8 = _; bv_omega
theorem q7 (S : Addr) : aR S + 72#64 + 8 + 8 + 8 + 8 + 8 + 8 = S := by
  show S - 8 - 8 - 8 - 8 - 8 - 8 - 72#64 + 72#64 + 8 + 8 + 8 + 8 + 8 + 8 = _; bv_omega

/-- The bytes after the prologue: the pushes (`Api.P6`), the stack guard stored. -/
abbrev V0 (fb : Addr) (V : Addr → Byte) (g : Gprs) : Addr → Byte :=
  Vst (P6 V g) (aR g.rsp + 56#64) (toBytesLE rdq(P6 V g, fb + 40#64) 8)

/-- The stack guard's slot as at `fs:0x28`. -/
abbrev Gd (fb : Addr) (W : Addr → Byte) (S : Addr) : Prop := rdq(W, aR S + 56#64) = rdq(W, fb + 40#64)

/-- The bytes after the append at 188 (the copy `r`): `_size + 1`, `_items[_size]` = `r`. -/
abbrev St188 (S : Addr) (r : BitVec 64) (W : Addr → Byte) : Addr → Byte :=
  Vst (Vst W (aR S + 40#64) (toBytesLE (rdd(W, aR S + 40#64) + 1#32) 4))
    (rdq(W, aR S + 32#64) + BitVec.setWidth 64 rdd(W, aR S + 40#64) * 8#64) (toBytesLE r 8)

/-- The frame up to 243: `rsp` = `aR S`, `rbx` = `this`, `rbp` = `pathParts`. -/
abbrev Fm (S : Addr) (g0 g : Gprs) : Prop := g.rsp = aR S ∧ g.rbx = g0.rdi ∧ g.rbp = g0.rdx

/-- What a piece keeps: `rsp`, `rbx`, `rbp`. -/
abbrev Fr (g g' : Gprs) : Prop := g'.rsp = g.rsp ∧ g'.rbx = g.rbx ∧ g'.rbp = g.rbp

theorem Fm.fr {S : Addr} {g0 g g' : Gprs} (h : Fm S g0 g) (h' : Fr g g') : Fm S g0 g' :=
  ⟨h'.1.trans h.1, h'.2.1.trans h.2.1, h'.2.2.trans h.2.2⟩

/-- Back from a callee: `rsp` as before the `call`, the callee-saved registers kept. -/
theorem fm_ret {S : Addr} {g0 g g' : Gprs} (h : Fm S g0 g) (hs : g'.rsp = aR S) (hk : KS g g') : Fm S g0 g' :=
  ⟨hs, hk.1.trans h.2.1, hk.2.1.trans h.2.2⟩

/-- The destruction's frame at the step `k`: `rbx` = `8 k`, `rdi` = `_items` (`A`). -/
abbrev Lp (S : Addr) (A : BitVec 64) (k : Nat) (g : Gprs) : Prop :=
  g.rsp = aR S ∧ g.rbx = BitVec.ofNat 64 (8 * k) ∧ g.rdi = A

/-- A callee from the `call` before `j` (entry `ent`, the bytes `W`, the registers `A`): at its entry, and from its
return at `j` with `rsp` = `aR S`, the callee-saved registers as at its entry and registers and bytes with `J`, the
run goes on to the goal. -/
def KC (prof : Profile) (F : Footprint) (Wl : List Rgn) (L : List (Addr × List Byte)) (s₀ : State) (o : Oracle)
    (gev : List Event) (gP : State → Nat → List Event → Prop) (gE : Outcome → List Event → Prop)
    (S ent : Addr) (j : Nat) (W : Addr → Byte) (A : Gprs → Prop) (J : Gprs → (Addr → Byte) → Prop) : Prop :=
  ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y →
    Agree F Y.proc.mm.mem (Vst W (aR S - 8) (toBytesLE (cpr_at.add j) 8)) →
    Y.cpu.rip = ent → Y.cpu.gpr.rsp = aR S - 8 → A Y.cpu.gpr →
    (∀ (Z : State) (W' : Addr → Byte) (t'' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem W' →
      Z.cpu.rip = cpr_at.add j → Z.cpu.gpr.rsp = aR S → KS Y.cpu.gpr Z.cpu.gpr → J Z.cpu.gpr W' →
      GoG prof L o gev gP gE Z t'') →
    GoG prof L o gev gP gE Y t'

/-- From offset `j` with registers and bytes for which `P` holds, the run goes on to the goal. -/
def AtJ (prof : Profile) (F : Footprint) (Wl : List Rgn) (L : List (Addr × List Byte)) (s₀ : State) (o : Oracle)
    (gev : List Event) (gP : State → Nat → List Event → Prop) (gE : Outcome → List Event → Prop) (j : Nat)
    (P : Gprs → (Addr → Byte) → Prop) : Prop :=
  ∀ (Y : State) (W : Addr → Byte) (t : Nat), KeptW Wl s₀ Y → Agree F Y.proc.mm.mem W →
    Y.cpu.rip = cpr_at.add j → P Y.cpu.gpr W → GoG prof L o gev gP gE Y t

/-- The hypotheses of the runs from the cut points (`S`, `g0` the entry's stack pointer and registers, `e₂.add j₂`
the return address, `I0`–`I5`, `P`, `Q4`, `D`, `Jd`, `Iz` the invariants of the bytes). -/
structure Ev (prof : Profile) (F : Footprint) (Wl : List Rgn) (L : List (Addr × List Byte)) (s₀ : State)
    (o : Oracle) (gev : List Event) (gP : State → Nat → List Event → Prop) (gE : Outcome → List Event → Prop)
    (fb S : Addr) (g0 : Gprs) (e₂ : Addr) (code₂ : List Byte) (j₂ : Nat)
    (I0 I1 I3 : (Addr → Byte) → Prop) (I2 : Gprs → (Addr → Byte) → Prop) (I4 I5 : BitVec 64 → (Addr → Byte) → Prop)
    (P : (Addr → Byte) → Prop) (Q4 : BitVec 32 → BitVec 32 → (Addr → Byte) → Prop)
    (D : BitVec 64 → Nat → (Addr → Byte) → Prop) (Jd : BitVec 64 → Nat → BitVec 64 → (Addr → Byte) → Prop)
    (Iz : (Addr → Byte) → Prop) : Prop where
  c : Seg prof F Wl L s₀ o
  hfs : s₀.cpu.seg.fsBase = fb
  hin : CodeIn L cpr_at cpr
  hin₂ : CodeIn L e₂ code₂
  h₂ : j₂ < code₂.length
  hIz : ∀ W, Iz W → Stk W S g0 (e₂.add j₂) ∧ Gd fb W S
  hcl : ∀ i < 8, Foot F.data (Addr.add (fb + 40#64) i)
  fg : ∀ i < 8, Foot F.data (Addr.add (aR S + 56#64) i)
  w32 : ∀ i < 8, Foot Wl (Addr.add (aR S + 32#64) i)
  w40 : ∀ i < 8, Foot Wl (Addr.add (aR S + 40#64) i)
  w44 : ∀ i < 4, Foot Wl (Addr.add (aR S + 44#64) i)
  f32 : ∀ i < 8, Foot F.data (Addr.add (aR S + 32#64) i)
  f40 : ∀ i < 4, Foot F.data (Addr.add (aR S + 40#64) i)
  fpar : ∀ i < 8, Foot F.data (Addr.add g0.rdi i)
  fn8 : ∀ i < 4, Foot F.data (Addr.add (g0.rdx + 8#64) i)
  fb48 : ∀ i < 8, Foot F.data (Addr.add (S - 8 - 8 - 8 - 8 - 8 - 8) i)
  fb40 : ∀ i < 8, Foot F.data (Addr.add (S - 8 - 8 - 8 - 8 - 8) i)
  fb32 : ∀ i < 8, Foot F.data (Addr.add (S - 8 - 8 - 8 - 8) i)
  fb24 : ∀ i < 8, Foot F.data (Addr.add (S - 8 - 8 - 8) i)
  fb16 : ∀ i < 8, Foot F.data (Addr.add (S - 8 - 8) i)
  fb8 : ∀ i < 8, Foot F.data (Addr.add (S - 8) i)
  hl : ∀ i < 8, Foot F.data (Addr.add S i)
  hr8 : ∀ i < 8, Foot Wl (Addr.add (aR S - 8) i)
  hz0 : ∀ W, I0 W → Iz W
  z80 : ∀ W, I0 W → I1 (Vst (Vst W (aR S + 32#64) (toBytesLE 0#64 8)) (aR S + 40#64) (toBytesLE 0#64 8))
  h117 : ∀ g W, I2 g W → rdd(W, aR S + 40#64) = 0#32 ∧ rdq(W, aR S + 32#64) = 0#64
  z146 : ∀ g W, I2 g W →
    I3 (Vst (Vst W (aR S + 32#64) (toBytesLE g.rax 8)) (aR S + 44#64) (toBytesLE 1#32 4))
  wsl : ∀ r W, I5 r W →
    ∀ i < 8, Foot Wl (Addr.add (rdq(W, aR S + 32#64) + BitVec.setWidth 64 rdd(W, aR S + 40#64) * 8#64) i)
  z221 : ∀ r W, I5 r W → rdd(W, g0.rdx + 8#64) = 0 → P (St188 S r W)
  z425 : ∀ r W, I5 r W → rdd(W, g0.rdx + 8#64) ≠ 0 →
    Q4 rdd(W, g0.rdx + 8#64) (rdd(W, aR S + 40#64) + 1#32) (St188 S r W)
  hDa : ∀ A k W, D A k W → rdq(W, aR S + 32#64) = A
  fe : ∀ A k W, D A (k + 1) W → ∀ i < 8, Foot F.data (Addr.add (A + BitVec.ofNat 64 (8 * k)) i)
  fp : ∀ A k W, D A (k + 1) W → pk W A k ≠ 0 → ∀ i < 8, Foot F.data (Addr.add (pk W A k) i)
  hP0 : ∀ A k W, D A (k + 1) W → pk W A k = 0 → D A k W
  hQ0 : ∀ A k W, D A (k + 1) W → pk W A k ≠ 0 → rdq(W, pk W A k) = 0 → Jd A k (pk W A k) W
  hA0 : ∀ W, D 0 0 W → Iz W
  cA : ∃ code : List Byte, CodeIn L 0x6029b0#64 code ∧ 0 < code.length
  cN : ∃ code : List Byte, CodeIn L 0x602970#64 code ∧ 0 < code.length
  cU : ∃ code : List Byte, CodeIn L 0x44d5d0#64 code ∧ 0 < code.length
  cP : ∃ code : List Byte, CodeIn L 0x4530c0#64 code ∧ 0 < code.length
  cD : ∃ code : List Byte, CodeIn L 0x6014f0#64 code ∧ 0 < code.length
  cE : ∃ code : List Byte, CodeIn L 0x6014e0#64 code ∧ 0 < code.length
  k112 : ∀ W, I1 W → KC prof F Wl L s₀ o gev gP gE S 0x6029b0#64 117 W (fun g => g.rdi = 8#64) I2
  k169 : ∀ W, I3 W → KC prof F Wl L s₀ o gev gP gE S 0x602970#64 174 W (fun g => g.rdi = 16#64)
    (fun g W' => I4 g.rax W')
  k183 : ∀ r W, I4 r W → KC prof F Wl L s₀ o gev gP gE S 0x44d5d0#64 188 W (fun g => g.rdi = r) (fun _ => I5 r)
  k238 : ∀ W, P W → KC prof F Wl L s₀ o gev gP gE S 0x4530c0#64 243 W (fun g => g.rdx = aR S + 32#64)
    (fun _ W' => D rdq(W', aR S + 32#64) rdd(W', aR S + 40#64).toNat W')
  k290 : ∀ A k W, D A (k + 1) W → pk W A k ≠ 0 → rdq(W, pk W A k) ≠ 0 →
    KC prof F Wl L s₀ o gev gP gE S 0x6014f0#64 295 W (fun g => g.rdi = rdq(W, pk W A k))
      (fun _ => Jd A k (pk W A k))
  k303 : ∀ A k p W, p ≠ 0 → Jd A k p W →
    KC prof F Wl L s₀ o gev gP gE S 0x6014e0#64 308 W (fun g => g.rdi = p ∧ g.rsi = 16#64) (fun _ => D A k)
  k328 : ∀ A W, A ≠ 0 → D A 0 W → KC prof F Wl L s₀ o gev gP gE S 0x6014f0#64 333 W (fun g => g.rdi = A)
    (fun _ => Iz)
  h425 : AtJ prof F Wl L s₀ o gev gP gE 425 fun g W => Fm S g0 g ∧
    ∃ m x, g.r15 = BitVec.setWidth 64 m ∧ g.rdx = BitVec.setWidth 64 x ∧ Q4 m x W
  kr : ∀ (W : Addr → Byte) (Z' : State) (t' : Nat), KeptW Wl s₀ Z' → Agree F Z'.proc.mm.mem W →
    Z'.cpu.rip = e₂.add j₂ → Z'.cpu.gpr.rsp = S + 8 → KS g0 Z'.cpu.gpr → Iz W →
      GoG prof L o gev gP gE Z' t'

/-! ## The pieces -/

section Pieces
variable {F : Footprint} {Wl : List Rgn}

/-- The prologue: the pushes, `r14d` = `isFile`, `r13d` = `include`, `rbp` = `pathParts`, `rbx` = `this`, the frame,
the stack guard stored (its value named `cn`): to the `call` at 54. -/
theorem vc_0 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} {cn : BitVec 64}
    (hcn : rdq(P6 V g, fb + 40#64) = cn)
    (hs1 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8) i)) (hs2 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8) i))
    (hs3 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8 - 8) i))
    (hs4 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8 - 8 - 8) i))
    (hs5 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8 - 8 - 8 - 8) i))
    (hs6 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8 - 8 - 8 - 8 - 8) i))
    (hcl : ∀ i < 8, Foot F.data (Addr.add (fb + 40#64) i))
    (hw : ∀ i < 8, Foot Wl (Addr.add (aR g.rsp + 56#64) i))
    (h : ∀ g', g'.rsp = aR g.rsp → g'.rbx = g.rdi → g'.rbp = g.rdx → g'.rdi = g.rdi → g'.rdx = g.rdx →
      ∀ fl, Q 54 g' fl (Vst (P6 V g) (aR g.rsp + 56#64) (toBytesLE cn 8))) :
    W_0 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [aR, P6] at hcn hs1 hs2 hs3 hs4 hs5 hs6 hw h ⊢
  wpx [W_0, o0, Op.ldf, Op.zxr, hcn]
  all_goals repeat' (first
    | refine h _ ?_ ?_ ?_ ?_ ?_ _
    | with_reducible rfl
    | with_reducible exact hs1
    | with_reducible exact hs2
    | with_reducible exact hs3
    | with_reducible exact hs4
    | with_reducible exact hs5
    | with_reducible exact hs6
    | with_reducible exact hcl
    | with_reducible exact hw
    | apply And.intro
    | intro _)

/-- `r12d` = `CheckPathToRoot_Change`'s result: its `al` not 0, or `Parent` (the 8 bytes at `rbx`) null, to 333;
else `edi` = 8, the vector's `_items` and its `_size`, `_capacity` stored as 0: to `operator new []` (112). -/
theorem vc_59 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (f0 : ∀ i < 8, Foot F.data (Addr.add g.rbx i))
    (w32 : ∀ i < 8, Foot Wl (Addr.add (g.rsp + 32#64) i)) (w40 : ∀ i < 8, Foot Wl (Addr.add (g.rsp + 40#64) i))
    (h333 : ∀ g', Fr g g' → ∀ fl, Q 333 g' fl V)
    (h112 : ∀ g', Fr g g' → g'.rdi = 8#64 → ∀ fl, Q 112 g' fl
      (Vst (Vst V (g.rsp + 32#64) (toBytesLE 0#64 8)) (g.rsp + 40#64) (toBytesLE 0#64 8))) :
    W_59 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at f0 w32 w40 h333 h112 ⊢
  wpx [W_59, W_70, W_80, o1, o2, o3, Op.cmpmi, BitVec.reduceSetWidth]
  all_goals repeat' (first
    | refine h333 _ ?_ _
    | refine h112 _ ?_ ?_ _
    | with_reducible rfl
    | exact rfl
    | with_reducible exact f0
    | with_reducible exact w32
    | with_reducible exact w40
    | apply And.intro
    | intro _)

/-- Back from `operator new []`: `_size` (`n32`) and `_items` (`p`) 0, `r12` = the new array: to 146. -/
theorem vc_117 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} {n32 : BitVec 32} {p : BitVec 64}
    (hn : rdd(V, g.rsp + 40#64) = n32) (hn0 : n32 = 0) (hp : rdq(V, g.rsp + 32#64) = p) (hp0 : p = 0)
    (f40 : ∀ i < 4, Foot F.data (Addr.add (g.rsp + 40#64) i))
    (f32 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 32#64) i))
    (h : ∀ g', Fr g g' → g'.r12 = g.rax → ∀ fl, Q 146 g' fl V) :
    W_117 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hn hp f40 f32 h ⊢
  have e1 : (n32 == 0) = true := beq_iff_eq.2 hn0
  have e2 : (p == 0) = true := beq_iff_eq.2 hp0
  wpx [W_117, W_376, W_137, o4, o20, o5, Op.shl64, hn, hp, e1, e2, BitVec.and_self, Bool.not_true, Bool.not_false,
    Bool.false_eq_true, Bool.true_eq_false, false_implies, eq_self_iff_true, true_implies, implies_true]
  all_goals repeat' (first
    | refine h _ ?_ ?_ _
    | with_reducible rfl
    | with_reducible exact f40
    | with_reducible exact f32
    | apply And.intro
    | intro _)

/-- `edi` = 0x10, `_items` = the new array (`r12`), `_capacity` = 1: to `operator new` (169). -/
theorem vc_146 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (w32 : ∀ i < 8, Foot Wl (Addr.add (g.rsp + 32#64) i)) (w44 : ∀ i < 4, Foot Wl (Addr.add (g.rsp + 44#64) i))
    (h : ∀ g', Fr g g' → g'.rdi = 16#64 → ∀ fl, Q 169 g' fl
      (Vst (Vst V (g.rsp + 32#64) (toBytesLE g.r12 8)) (g.rsp + 44#64) (toBytesLE 1#32 4))) :
    W_146 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at w32 w44 h ⊢
  wpx [W_146, o6, BitVec.reduceSetWidth]
  all_goals repeat' (first
    | refine h _ ?_ ?_ _
    | with_reducible rfl
    | exact rfl
    | with_reducible exact w32
    | with_reducible exact w44
    | apply And.intro
    | intro _)

/-- `rdi` = `r12` = the new `UString`, `rsi` = `this + 8`: to its copy (183). -/
theorem vc_174 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (h : ∀ g', Fr g g' → g'.rdi = g.rax → g'.r12 = g.rax → ∀ fl, Q 183 g' fl V) :
    W_174 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h ⊢
  wpx [W_174, o7]
  all_goals repeat' (first
    | refine h _ ?_ ?_ ?_ _
    | with_reducible rfl
    | apply And.intro
    | intro _)

/-- The append (`_size` + 1 as `x`, `_items[_size]` = `r12`), `r15d` = `pathParts._size`: 0 to 221; else `eax` =
`0x7fffffff - edx`, to the `js` at 425. -/
theorem vc_188 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (f40 : ∀ i < 4, Foot F.data (Addr.add (g.rsp + 40#64) i))
    (f32 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 32#64) i))
    (f8 : ∀ i < 4, Foot F.data (Addr.add (g.rbp + 8#64) i))
    (w40 : ∀ i < 4, Foot Wl (Addr.add (g.rsp + 40#64) i))
    (wsl : ∀ i < 8, Foot Wl (Addr.add (rdq(V, g.rsp + 32#64) + BitVec.setWidth 64 rdd(V, g.rsp + 40#64) * 8#64) i))
    (h221 : ∀ g' (x : BitVec 32), x = rdd(V, g.rsp + 40#64) + 1#32 → rdd(V, g.rbp + 8#64) = 0 → Fr g g' →
      ∀ fl, Q 221 g' fl (Vst (Vst V (g.rsp + 40#64) (toBytesLE x 4))
        (rdq(V, g.rsp + 32#64) + BitVec.setWidth 64 rdd(V, g.rsp + 40#64) * 8#64) (toBytesLE g.r12 8)))
    (h425 : ∀ g' (x : BitVec 32), x = rdd(V, g.rsp + 40#64) + 1#32 → rdd(V, g.rbp + 8#64) ≠ 0 → Fr g g' →
      g'.r15 = BitVec.setWidth 64 rdd(V, g.rbp + 8#64) → g'.rdx = BitVec.setWidth 64 x →
      ∀ fl, Q 425 g' fl (Vst (Vst V (g.rsp + 40#64) (toBytesLE x 4))
        (rdq(V, g.rsp + 32#64) + BitVec.setWidth 64 rdd(V, g.rsp + 40#64) * 8#64) (toBytesLE g.r12 8))) :
    W_188 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at f40 f32 f8 w40 wsl h221 h425 ⊢
  wpx [W_188, W_416, o8, o23]
  all_goals repeat' (first
    | refine h221 _ _ ?_ ?_ ?_ _
    | refine h425 _ _ ?_ ?_ ?_ ?_ ?_ _
    | with_reducible rfl
    | exact inc32 _
    | exact rfl
    | exact nz32 ‹_›
    | exact z32 ‹_›
    | with_reducible exact f40
    | with_reducible exact f32
    | with_reducible exact f8
    | with_reducible exact w40
    | with_reducible exact wsl
    | apply And.intro
    | intro _)

/-- `rdx` = the vector (`rsp + 32`), `rdi` = `Parent` (the 8 bytes at `rbx`): to its `CheckPathToRoot_Change`
(238). -/
theorem vc_221 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (f0 : ∀ i < 8, Foot F.data (Addr.add g.rbx i))
    (h : ∀ g', Fr g g' → g'.rdx = g.rsp + 32#64 → ∀ fl, Q 238 g' fl V) :
    W_221 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at f0 h ⊢
  wpx [W_221, o9]
  all_goals repeat' (first
    | refine h _ ?_ ?_ _
    | with_reducible rfl
    | with_reducible exact f0
    | apply And.intro
    | intro _)

/-- The result in `r12d`, the vector's `_size` (`n32`) 0: `rdi` = `_items`, to 323. -/
theorem vc_243z {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} {n32 : BitVec 32}
    (hn : rdd(V, g.rsp + 40#64) = n32) (hn0 : n32 = 0)
    (f40 : ∀ i < 4, Foot F.data (Addr.add (g.rsp + 40#64) i))
    (f32 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 32#64) i))
    (h : ∀ g', g'.rsp = g.rsp → g'.rdi = rdq(V, g.rsp + 32#64) → ∀ fl, Q 323 g' fl V) :
    W_243 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hn f40 f32 h ⊢
  have e : (n32 == 0) = true := beq_iff_eq.2 hn0
  wpx [W_243, W_259, o10, o11, Op.shl64, hn, e, BitVec.and_self, Bool.false_eq_true, Bool.true_eq_false,
    false_implies, eq_self_iff_true, true_implies, implies_true]
  all_goals repeat' (first
    | refine h _ ?_ ?_ _
    | with_reducible rfl
    | with_reducible exact f40
    | with_reducible exact f32
    | apply And.intro
    | intro _)

/-- The vector's `_size` (`n32`) not 0: `rdi` = `_items`, `rbx` = `8 (n32 - 1)` (`Ocv.rbx0`), to the loop's head
272. -/
theorem vc_243n {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} {n32 : BitVec 32}
    (hn : rdd(V, g.rsp + 40#64) = n32) (hn0 : n32 ≠ 0)
    (f40 : ∀ i < 4, Foot F.data (Addr.add (g.rsp + 40#64) i))
    (f32 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 32#64) i))
    (h : ∀ g', g'.rsp = g.rsp → g'.rdi = rdq(V, g.rsp + 32#64) → g'.rbx = rbx0 n32 → ∀ fl, Q 272 g' fl V) :
    W_243 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hn f40 f32 h ⊢
  have e : (n32 == 0) = false := beq_eq_false_iff_ne.2 hn0
  wpx [W_243, W_259, o10, o11, Op.shl64, hn, e, BitVec.and_self, Bool.false_eq_true, Bool.true_eq_false,
    false_implies, eq_self_iff_true, true_implies, implies_true]
  all_goals repeat' (first
    | refine h _ ?_ ?_ ?_ _
    | with_reducible rfl
    | with_reducible exact f40
    | with_reducible exact f32
    | exact rfl
    | apply And.intro
    | intro _)

/-- The loop's head with the item `p` (the 8 bytes at `rdi + rbx`) 0: to 313. -/
theorem vc_272z {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} {p : BitVec 64}
    (hp : rdq(V, g.rdi + g.rbx) = p) (fp : ∀ i < 8, Foot F.data (Addr.add (g.rdi + g.rbx) i)) (hp0 : p = 0)
    (h : ∀ g', g'.rsp = g.rsp → g'.rbx = g.rbx → g'.rdi = g.rdi → ∀ fl, Q 313 g' fl V) :
    W_272 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hp fp h ⊢
  have e : (p == 0) = true := beq_iff_eq.2 hp0
  wpx [W_272, W_281, o12, o13, hp, e, BitVec.and_self, Bool.false_eq_true, Bool.true_eq_false, false_implies,
    eq_self_iff_true, true_implies, implies_true]
  all_goals repeat' (first
    | refine h _ ?_ ?_ ?_ _
    | with_reducible rfl
    | with_reducible exact fp
    | apply And.intro
    | intro _)

/-- The loop's head with the item `p` not 0: `rbp` = `p`, `rdi` = `q` (its chars, the 8 bytes at `p`); to 295 when
`q` is 0, else to the `call` at 290. -/
theorem vc_272n {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} {p q : BitVec 64}
    (hp : rdq(V, g.rdi + g.rbx) = p) (fp : ∀ i < 8, Foot F.data (Addr.add (g.rdi + g.rbx) i)) (hp0 : p ≠ 0)
    (hq : rdq(V, p) = q) (fq : ∀ i < 8, Foot F.data (Addr.add p i))
    (h295 : q = 0 → ∀ g', g'.rsp = g.rsp → g'.rbx = g.rbx → g'.rbp = p → ∀ fl, Q 295 g' fl V)
    (h290 : q ≠ 0 → ∀ g', g'.rsp = g.rsp → g'.rbx = g.rbx → g'.rbp = p → g'.rdi = q → ∀ fl, Q 290 g' fl V) :
    W_272 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hp fp h295 h290 ⊢
  have e : (p == 0) = false := beq_eq_false_iff_ne.2 hp0
  wpx [W_272, W_281, o12, o13, hp, hq, e, BitVec.and_self, beq_iff_eq, beq_eq_false_iff_ne, Bool.false_eq_true,
    Bool.true_eq_false, false_implies, eq_self_iff_true, true_implies, implies_true]
  all_goals repeat' (first
    | refine h295 ?_ _ ?_ ?_ ?_ _
    | refine h290 ?_ _ ?_ ?_ ?_ ?_ _
    | with_reducible rfl
    | with_reducible exact fp
    | with_reducible exact fq
    | assumption
    | apply And.intro
    | intro _)

/-- `rdi` = the item, `esi` = 16: to the `call` at 303. -/
theorem vc_295 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (h : ∀ g', g'.rsp = g.rsp → g'.rbx = g.rbx → g'.rdi = g.rbp → g'.rsi = 16#64 → ∀ fl, Q 303 g' fl V) :
    W_295 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h ⊢
  wpx [W_295, o14, BitVec.reduceSetWidth]
  all_goals repeat' (first
    | refine h _ ?_ ?_ ?_ ?_ _
    | with_reducible rfl
    | apply And.intro
    | intro _)

/-- `rdi` = `_items` again: to 313. -/
theorem vc_308 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (f32 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 32#64) i))
    (h : ∀ g', g'.rsp = g.rsp → g'.rbx = g.rbx → g'.rdi = rdq(V, g.rsp + 32#64) → ∀ fl, Q 313 g' fl V) :
    W_308 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at f32 h ⊢
  wpx [W_308, o15]
  all_goals repeat' (first
    | refine h _ ?_ ?_ ?_ _
    | with_reducible rfl
    | with_reducible exact f32
    | apply And.intro
    | intro _)

/-- `rbx` -= 8 gives `-8` (the last step): to 323. -/
theorem vc_313l {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (hb : g.rbx - 8#64 = 18446744073709551608#64)
    (h : ∀ g', g'.rsp = g.rsp → g'.rdi = g.rdi → ∀ fl, Q 323 g' fl V) :
    W_313 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hb h ⊢
  have e := decide_eq_true hb
  wpx [W_313, o16, e, Bool.not_true, Bool.not_false, Bool.false_eq_true, Bool.true_eq_false, false_implies,
    eq_self_iff_true, true_implies, implies_true]
  all_goals repeat' (first
    | refine h _ ?_ ?_ _
    | with_reducible rfl
    | apply And.intro
    | intro _)

/-- `rbx` -= 8, not the last step: back to 272. -/
theorem vc_313c {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (hb : g.rbx - 8#64 ≠ 18446744073709551608#64)
    (h : ∀ g', g'.rsp = g.rsp → g'.rbx = g.rbx - 8#64 → g'.rdi = g.rdi → ∀ fl, Q 272 g' fl V) :
    W_313 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hb h ⊢
  have e := decide_eq_false hb
  wpx [W_313, o16, e, Bool.not_true, Bool.not_false, Bool.false_eq_true, Bool.true_eq_false, false_implies,
    eq_self_iff_true, true_implies, implies_true]
  all_goals repeat' (first
    | refine h _ ?_ ?_ ?_ _
    | with_reducible rfl
    | apply And.intro
    | intro _)

/-- `_items` null: to 333. -/
theorem vc_323z {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (hA : g.rdi = 0) (h : ∀ g', g'.rsp = g.rsp → ∀ fl, Q 333 g' fl V) :
    W_323 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hA h ⊢
  have e : (rdi == 0) = true := beq_iff_eq.2 hA
  wpx [W_323, o17, e, BitVec.and_self, Bool.false_eq_true, Bool.true_eq_false, false_implies, eq_self_iff_true,
    true_implies, implies_true]
  all_goals repeat' (first
    | refine h _ ?_ _
    | with_reducible rfl
    | apply And.intro
    | intro _)

/-- `_items` not null: to its `delete []` (328). -/
theorem vc_323n {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (hA : g.rdi ≠ 0) (h : ∀ g', g'.rsp = g.rsp → g'.rdi = g.rdi → ∀ fl, Q 328 g' fl V) :
    W_323 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hA h ⊢
  have e : (rdi == 0) = false := beq_eq_false_iff_ne.2 hA
  wpx [W_323, o17, e, BitVec.and_self, Bool.false_eq_true, Bool.true_eq_false, false_implies, eq_self_iff_true,
    true_implies, implies_true]
  all_goals repeat' (first
    | refine h _ ?_ ?_ _
    | with_reducible rfl
    | apply And.intro
    | intro _)

/-- The stack guard checked (as at `fs:0x28`: `jne` not taken), `add rsp, 0x48`, `eax` = `r12d`, the six pops, to
the `ret`. -/
theorem vc_333 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (hc : rdq(V, g.rsp + 56#64) = rdq(V, fb + 40#64)) (f56 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 56#64) i))
    (fcl : ∀ i < 8, Foot F.data (Addr.add (fb + 40#64) i))
    (f1 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 72#64) i))
    (f2 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 72#64 + 8) i))
    (f3 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 72#64 + 8 + 8) i))
    (f4 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 72#64 + 8 + 8 + 8) i))
    (f5 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 72#64 + 8 + 8 + 8 + 8) i))
    (f6 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 72#64 + 8 + 8 + 8 + 8 + 8) i))
    (h : ∀ g', g'.rsp = g.rsp + 72#64 + 8 + 8 + 8 + 8 + 8 + 8 → g'.rbx = rdq(V, g.rsp + 72#64) →
      g'.rbp = rdq(V, g.rsp + 72#64 + 8) → g'.r12 = rdq(V, g.rsp + 72#64 + 8 + 8) →
      g'.r13 = rdq(V, g.rsp + 72#64 + 8 + 8 + 8) → g'.r14 = rdq(V, g.rsp + 72#64 + 8 + 8 + 8 + 8) →
      g'.r15 = rdq(V, g.rsp + 72#64 + 8 + 8 + 8 + 8 + 8) → ∀ fl, Q 370 g' fl V) :
    W_333 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hc f56 f1 f2 f3 f4 f5 f6 h ⊢
  have z0 : ((0#64 : BitVec 64) == 0) = true := by decide
  wpx [W_333, W_353, o18, o19, Op.xormf, hc, BitVec.xor_self, z0, decide_true, Bool.not_true, Bool.false_eq_true,
    false_implies, eq_self_iff_true, true_implies]
  all_goals repeat' (first
    | refine h _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ _
    | with_reducible rfl
    | with_reducible exact f56
    | with_reducible exact fcl
    | with_reducible exact f1
    | with_reducible exact f2
    | with_reducible exact f3
    | with_reducible exact f4
    | with_reducible exact f5
    | with_reducible exact f6
    | apply And.intro
    | intro _)

end Pieces

/-! ## The runs from the cut points -/

section Runs
variable {prof : Profile} {F : Footprint} {Wl : List Rgn} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {fb S : Addr} {g0 : Gprs} {e₂ : Addr} {code₂ : List Byte} {j₂ : Nat}
  {I0 I1 I3 : (Addr → Byte) → Prop} {I2 : Gprs → (Addr → Byte) → Prop} {I4 I5 : BitVec 64 → (Addr → Byte) → Prop}
  {P : (Addr → Byte) → Prop} {Q4 : BitVec 32 → BitVec 32 → (Addr → Byte) → Prop}
  {D : BitVec 64 → Nat → (Addr → Byte) → Prop} {Jd : BitVec 64 → Nat → BitVec 64 → (Addr → Byte) → Prop}
  {Iz : (Addr → Byte) → Prop} {Y : State} {t : Nat} {W : Addr → Byte}

/-- A `call` at `j` (`rsp` = `aR S`, the bytes `W`) of the callee `k`, and from its return at `j + 5`. -/
theorem callK (E : Ev prof F Wl L s₀ o gev gP gE fb S g0 e₂ code₂ j₂ I0 I1 I3 I2 I4 I5 P Q4 D Jd Iz)
    {U : State} {t₁ : Nat} {j R : Nat} {ent : Addr} {A : Gprs → Prop} {N : Gprs → (Addr → Byte) → Prop}
    (hKU : KeptW Wl s₀ U) (hAU : Agree F U.proc.mm.mem W) (hrU : U.cpu.rip = cpr_at.add j)
    (hs : U.cpu.gpr.rsp = aR S) (hj : j < cpr.length) (hd : Dec prof.feat cpr j (FV7z.mk .call 64 [.rel R] 5))
    (htgt : cpr_at.add (j + 5) + BitVec.ofNat 64 R = ent)
    (hc : ∃ code : List Byte, CodeIn L ent code ∧ 0 < code.length)
    (k : KC prof F Wl L s₀ o gev gP gE S ent (j + 5) W A N) (hA : A (U.cpu.gpr.set 4 (aR S - 8)))
    (h : ∀ (Z : State) (W' : Addr → Byte) (t'' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem W' →
      Z.cpu.rip = cpr_at.add (j + 5) → Z.cpu.gpr.rsp = aR S → KS U.cpu.gpr Z.cpu.gpr → N Z.cpu.gpr W' →
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

/-- From 333 (`rsp` = `aR S`, the bytes `W` with `Iz`): the guard's check, the epilogue, the `ret`, to `kr`. -/
theorem tail333 (E : Ev prof F Wl L s₀ o gev gP gE fb S g0 e₂ code₂ j₂ I0 I1 I3 I2 I4 I5 P Q4 D Jd Iz)
    (hK : KeptW Wl s₀ Y) (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = cpr_at.add 333)
    (hs : Y.cpu.gpr.rsp = aR S) (hIW : Iz W) :
    GoG prof L o gev gP gE Y t := by
  obtain ⟨⟨s1, s2, s3, s4, s5, s6, s7⟩, sg⟩ := E.hIz W hIW
  have e1 : rdq(W, Y.cpu.gpr.rsp + 72#64) = g0.rbx := by rw [hs, q1]; exact s1
  have e2 : rdq(W, Y.cpu.gpr.rsp + 72#64 + 8) = g0.rbp := by rw [hs, q2]; exact s2
  have e3 : rdq(W, Y.cpu.gpr.rsp + 72#64 + 8 + 8) = g0.r12 := by rw [hs, q3]; exact s3
  have e4 : rdq(W, Y.cpu.gpr.rsp + 72#64 + 8 + 8 + 8) = g0.r13 := by rw [hs, q4]; exact s4
  have e5 : rdq(W, Y.cpu.gpr.rsp + 72#64 + 8 + 8 + 8 + 8) = g0.r14 := by rw [hs, q5]; exact s5
  have e6 : rdq(W, Y.cpu.gpr.rsp + 72#64 + 8 + 8 + 8 + 8 + 8) = g0.r15 := by rw [hs, q6]; exact s6
  refine (c_333 prof fb).run E.c E.hfs E.hin (fun j' g' _ V' => j' = 370 ∧ V' = W ∧
      g'.rsp = Y.cpu.gpr.rsp + 72#64 + 8 + 8 + 8 + 8 + 8 + 8 ∧ g'.rbx = rdq(W, Y.cpu.gpr.rsp + 72#64) ∧
      g'.rbp = rdq(W, Y.cpu.gpr.rsp + 72#64 + 8) ∧ g'.r12 = rdq(W, Y.cpu.gpr.rsp + 72#64 + 8 + 8) ∧
      g'.r13 = rdq(W, Y.cpu.gpr.rsp + 72#64 + 8 + 8 + 8) ∧
      g'.r14 = rdq(W, Y.cpu.gpr.rsp + 72#64 + 8 + 8 + 8 + 8) ∧
      g'.r15 = rdq(W, Y.cpu.gpr.rsp + 72#64 + 8 + 8 + 8 + 8 + 8))
    hK hA hr
    (vc_333 (by rw [hs]; exact sg) (by rw [hs]; exact E.fg) E.hcl (by rw [hs, q1]; exact E.fb48)
      (by rw [hs, q2]; exact E.fb40) (by rw [hs, q3]; exact E.fb32) (by rw [hs, q4]; exact E.fb24)
      (by rw [hs, q5]; exact E.fb16) (by rw [hs, q6]; exact E.fb8)
      fun _ a b d e f g h _ => ⟨rfl, rfl, a, b, d, e, f, g, h⟩) ?_
  rintro j' g fl V₁ ⟨rfl, hV₁, gs, gx, gp, g12, g13, g14, g15⟩ U t₁ hKU hAU hrU hgU -
  subst V₁ hgU
  have hsU : U.cpu.gpr.rsp = S := by rw [gs, hs]; exact q7 S
  refine E.c.s_ret hKU hAU E.hin (lt_len (by decide)) hrU (ret_370 _) (by rw [hsU]; exact E.hl) E.hin₂ E.h₂
    (by rw [hsU]; exact s7) ?_
  rintro Z' t₂ hKZ' hAZ' ⟨hrZ', hgZ'⟩
  refine E.kr W Z' t₂ hKZ' hAZ' hrZ' ?_ ?_ hIW
  · rw [hgZ']
    show U.cpu.gpr.rsp + 8 = _
    rw [hsU]
  · rw [hgZ']
    exact ⟨gx.trans e1, gp.trans e2, g12.trans e3, g13.trans e4, g14.trans e5, g15.trans e6⟩

/-- From 323 (`rdi` = `_items` = `A`, the bytes with `D A 0`): null to 333 (`hA0`), else `delete []` (`k328`) and
from its return 333. -/
theorem from323 (E : Ev prof F Wl L s₀ o gev gP gE fb S g0 e₂ code₂ j₂ I0 I1 I3 I2 I4 I5 P Q4 D Jd Iz)
    (A : BitVec 64) :
    AtJ prof F Wl L s₀ o gev gP gE 323 fun g W => D A 0 W ∧ g.rsp = aR S ∧ g.rdi = A := by
  rintro Y W t hK hA hr ⟨hD, hs, hdi⟩
  by_cases hA0 : A = 0
  · subst hA0
    refine (c_323 prof fb).run E.c E.hfs E.hin (fun j' g' _ V' => j' = 333 ∧ V' = W ∧ g'.rsp = Y.cpu.gpr.rsp)
      hK hA hr (vc_323z hdi fun _ a _ => ⟨rfl, rfl, a⟩) ?_
    rintro j' g fl V₁ ⟨rfl, hV₁, gs⟩ U t₁ hKU hAU hrU hgU -
    subst V₁ hgU
    exact tail333 E hKU hAU hrU (gs.trans hs) (E.hA0 W hD)
  · refine (c_323 prof fb).run E.c E.hfs E.hin (fun j' g' _ V' => j' = 328 ∧ V' = W ∧ g'.rsp = Y.cpu.gpr.rsp ∧
        g'.rdi = Y.cpu.gpr.rdi) hK hA hr (vc_323n (by rw [hdi]; exact hA0) fun _ a b _ => ⟨rfl, rfl, a, b⟩) ?_
    rintro j' g fl V₁ ⟨rfl, hV₁, gs, gdi⟩ U t₁ hKU hAU hrU hgU -
    subst V₁ hgU
    refine callK E hKU hAU hrU (gs.trans hs) (lt_len (by decide)) (call_328 _) tgt_328 E.cD
      (E.k328 A W hA0 hD) (by show U.cpu.gpr.rdi = _; rw [gdi, hdi]) ?_
    intro Z W' t₃ hKZ hAZ hrZ hsZ hkZ hIZ
    exact tail333 E hKZ hAZ hrZ hsZ hIZ

/-- 295 (the step `k`, the item `p` with null or freed chars): `operator delete (p, 16)` (`k303`), from its return
308 (`rdi` = `_items` again) to 313. -/
theorem A295 (E : Ev prof F Wl L s₀ o gev gP gE fb S g0 e₂ code₂ j₂ I0 I1 I3 I2 I4 I5 P Q4 D Jd Iz)
    (A : BitVec 64) (k : Nat) (p : BitVec 64) (hp : p ≠ 0)
    (h313 : AtJ prof F Wl L s₀ o gev gP gE 313 fun g W => D A k W ∧ Lp S A k g) :
    AtJ prof F Wl L s₀ o gev gP gE 295 fun g W => Jd A k p W ∧ g.rsp = aR S ∧ g.rbx = BitVec.ofNat 64 (8 * k) ∧
      g.rbp = p := by
  rintro Y W t hK hA hr ⟨hJ, hs, hb, hbp⟩
  refine (c_295 prof fb).run E.c E.hfs E.hin (fun j' g' _ V' => j' = 303 ∧ V' = W ∧ g'.rsp = Y.cpu.gpr.rsp ∧
      g'.rbx = Y.cpu.gpr.rbx ∧ g'.rdi = Y.cpu.gpr.rbp ∧ g'.rsi = 16#64) hK hA hr
    (vc_295 fun _ a b d e _ => ⟨rfl, rfl, a, b, d, e⟩) ?_
  rintro j' g fl V₁ ⟨rfl, hV₁, gs, gb, gdi, gsi⟩ U t₁ hKU hAU hrU hgU -
  subst V₁ hgU
  refine callK E hKU hAU hrU (gs.trans hs) (lt_len (by decide)) (call_303 _) tgt_303 E.cE
    (E.k303 A k p W hp hJ) ⟨gdi.trans hbp, gsi⟩ ?_
  intro Z W' t₃ hKZ hAZ hrZ hsZ hkZ hDZ
  have hbZ : Z.cpu.gpr.rbx = BitVec.ofNat 64 (8 * k) := hkZ.1.trans (gb.trans hb)
  refine (c_308 prof fb).run E.c E.hfs E.hin (fun j' g' _ V' => j' = 313 ∧ V' = W' ∧ g'.rsp = Z.cpu.gpr.rsp ∧
      g'.rbx = Z.cpu.gpr.rbx ∧ g'.rdi = rdq(W', Z.cpu.gpr.rsp + 32#64)) hKZ hAZ hrZ
    (vc_308 (by rw [hsZ]; exact E.f32) fun _ a b d _ => ⟨rfl, rfl, a, b, d⟩) ?_
  rintro j' g fl V₁ ⟨rfl, hV₁, gs', gb', gdi'⟩ U' t₄ hKU' hAU' hrU' hgU' -
  subst V₁ hgU'
  refine h313 U' W' t₄ hKU' hAU' hrU' ⟨hDZ, gs'.trans hsZ, gb'.trans hbZ, ?_⟩
  rw [gdi', hsZ]
  exact E.hDa A k W' hDZ

/-- 272, the step `k` (`rbx` = `8 k`): the item `p` = `_items[k]`; null to 313, else its chars freed unless null
(`k290`) and to 295. -/
theorem B272 (E : Ev prof F Wl L s₀ o gev gP gE fb S g0 e₂ code₂ j₂ I0 I1 I3 I2 I4 I5 P Q4 D Jd Iz)
    (A : BitVec 64) (k : Nat)
    (h313 : AtJ prof F Wl L s₀ o gev gP gE 313 fun g W => D A k W ∧ Lp S A k g) :
    AtJ prof F Wl L s₀ o gev gP gE 272 fun g W => D A (k + 1) W ∧ Lp S A k g := by
  rintro Y W t hK hA hr ⟨hD, hs, hb, hdi⟩
  have hea : Y.cpu.gpr.rdi + Y.cpu.gpr.rbx = A + BitVec.ofNat 64 (8 * k) := by rw [hdi, hb]
  have fe := E.fe A k W hD
  by_cases hp0 : pk W A k = 0
  · refine (c_272 prof fb).run E.c E.hfs E.hin (fun j' g' _ V' => j' = 313 ∧ V' = W ∧ g'.rsp = Y.cpu.gpr.rsp ∧
        g'.rbx = Y.cpu.gpr.rbx ∧ g'.rdi = Y.cpu.gpr.rdi) hK hA hr
      (vc_272z (p := pk W A k) (by rw [hea]) (by rw [hea]; exact fe) hp0
        fun _ a b d _ => ⟨rfl, rfl, a, b, d⟩) ?_
    rintro j' g fl V₁ ⟨rfl, hV₁, gs, gb, gdi⟩ U t₁ hKU hAU hrU hgU -
    subst V₁ hgU
    exact h313 U W t₁ hKU hAU hrU ⟨E.hP0 A k W hD hp0, gs.trans hs, gb.trans hb, gdi.trans hdi⟩
  · have fpp := E.fp A k W hD hp0
    refine (c_272 prof fb).run E.c E.hfs E.hin (fun j' g' _ V' => V' = W ∧ g'.rsp = Y.cpu.gpr.rsp ∧
        g'.rbx = Y.cpu.gpr.rbx ∧ g'.rbp = pk W A k ∧ ((rdq(W, pk W A k) = 0 ∧ j' = 295) ∨
          (rdq(W, pk W A k) ≠ 0 ∧ j' = 290 ∧ g'.rdi = rdq(W, pk W A k)))) hK hA hr
      (vc_272n (p := pk W A k) (q := rdq(W, pk W A k)) (by rw [hea]) (by rw [hea]; exact fe) hp0 rfl fpp
        (fun hq _ a b d _ => ⟨rfl, a, b, d, Or.inl ⟨hq, rfl⟩⟩)
        (fun hq _ a b d e _ => ⟨rfl, a, b, d, Or.inr ⟨hq, rfl, e⟩⟩)) ?_
    rintro j' g fl V₁ ⟨hV₁, gs, gb, gbp, hj⟩ U t₁ hKU hAU hrU hgU -
    subst V₁ hgU
    have hsU : U.cpu.gpr.rsp = aR S := gs.trans hs
    have hbU : U.cpu.gpr.rbx = BitVec.ofNat 64 (8 * k) := gb.trans hb
    rcases hj with ⟨hq0, rfl⟩ | ⟨hq0, rfl, gdi⟩
    · exact A295 E A k _ hp0 h313 U W t₁ hKU hAU hrU ⟨E.hQ0 A k W hD hp0 hq0, hsU, hbU, gbp⟩
    · refine callK E hKU hAU hrU hsU (lt_len (by decide)) (call_290 _) tgt_290 E.cD
        (E.k290 A k W hD hp0 hq0) gdi ?_
      intro Z W' t₃ hKZ hAZ hrZ hsZ hkZ hJZ
      exact A295 E A k _ hp0 h313 Z W' t₃ hKZ hAZ hrZ ⟨hJZ, hsZ, hkZ.1.trans hbU, hkZ.2.1.trans gbp⟩

/-- 313, the step `k`: `rbx` -= 8; after the step 0 to 323, else to 272 with the step `k - 1` (`hnx`). -/
theorem S313 (E : Ev prof F Wl L s₀ o gev gP gE fb S g0 e₂ code₂ j₂ I0 I1 I3 I2 I4 I5 P Q4 D Jd Iz)
    (A : BitVec 64) (k : Nat) (hk : k < 4294967296)
    (h323 : AtJ prof F Wl L s₀ o gev gP gE 323 fun g W => D A 0 W ∧ g.rsp = aR S ∧ g.rdi = A)
    (hnx : ∀ k', k = k' + 1 → AtJ prof F Wl L s₀ o gev gP gE 272 fun g W => D A (k' + 1) W ∧ Lp S A k' g) :
    AtJ prof F Wl L s₀ o gev gP gE 313 fun g W => D A k W ∧ Lp S A k g := by
  rintro Y W t hK hA hr ⟨hD, hs, hb, hdi⟩
  cases k with
  | zero =>
    refine (c_313 prof fb).run E.c E.hfs E.hin (fun j' g' _ V' => j' = 323 ∧ V' = W ∧ g'.rsp = Y.cpu.gpr.rsp ∧
        g'.rdi = Y.cpu.gpr.rdi) hK hA hr
      (vc_313l (by rw [hb]; exact rb_last) fun _ a b _ => ⟨rfl, rfl, a, b⟩) ?_
    rintro j' g fl V₁ ⟨rfl, hV₁, gs, gdi⟩ U t₁ hKU hAU hrU hgU -
    subst V₁ hgU
    exact h323 U W t₁ hKU hAU hrU ⟨hD, gs.trans hs, gdi.trans hdi⟩
  | succ k =>
    refine (c_313 prof fb).run E.c E.hfs E.hin (fun j' g' _ V' => j' = 272 ∧ V' = W ∧ g'.rsp = Y.cpu.gpr.rsp ∧
        g'.rbx = Y.cpu.gpr.rbx - 8#64 ∧ g'.rdi = Y.cpu.gpr.rdi) hK hA hr
      (vc_313c (by rw [hb, rb_step k (by omega)]; exact rb_ne k (by omega))
        fun _ a b d _ => ⟨rfl, rfl, a, b, d⟩) ?_
    rintro j' g fl V₁ ⟨rfl, hV₁, gs, gb, gdi⟩ U t₁ hKU hAU hrU hgU -
    subst V₁ hgU
    exact hnx k rfl U W t₁ hKU hAU hrU
      ⟨hD, gs.trans hs, by rw [gb, hb]; exact rb_step k (by omega), gdi.trans hdi⟩

/-- The destruction loop, by induction on the step. -/
theorem L272 (E : Ev prof F Wl L s₀ o gev gP gE fb S g0 e₂ code₂ j₂ I0 I1 I3 I2 I4 I5 P Q4 D Jd Iz)
    (A : BitVec 64) (h323 : AtJ prof F Wl L s₀ o gev gP gE 323 fun g W => D A 0 W ∧ g.rsp = aR S ∧ g.rdi = A) :
    ∀ k, k < 4294967296 → AtJ prof F Wl L s₀ o gev gP gE 272 fun g W => D A (k + 1) W ∧ Lp S A k g := by
  intro k
  induction k with
  | zero => exact fun hk => B272 E A 0 (S313 E A 0 hk h323 fun k' e => absurd e (by omega))
  | succ k ih =>
    exact fun hk => B272 E A (k + 1) (S313 E A (k + 1) hk h323 fun k' e => by
      obtain rfl : k = k' := by omega
      exact ih (by omega))

/-- From 243 (back from `CheckPathToRoot_Change`, the bytes with `D A N` for the vector's `_items` `A` and `_size`
`N`): `N` 0 to 323, else the loop from the step `N - 1`. -/
theorem from243 (E : Ev prof F Wl L s₀ o gev gP gE fb S g0 e₂ code₂ j₂ I0 I1 I3 I2 I4 I5 P Q4 D Jd Iz)
    (hK : KeptW Wl s₀ Y) (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = cpr_at.add 243)
    (hs : Y.cpu.gpr.rsp = aR S) (hD : D rdq(W, aR S + 32#64) rdd(W, aR S + 40#64).toNat W) :
    GoG prof L o gev gP gE Y t := by
  obtain ⟨N, hN⟩ : ∃ N, rdd(W, aR S + 40#64) = N := ⟨_, rfl⟩
  obtain ⟨A, hAa⟩ : ∃ A, rdq(W, aR S + 32#64) = A := ⟨_, rfl⟩
  rw [hN, hAa] at hD
  have hn' : rdd(W, Y.cpu.gpr.rsp + 40#64) = N := by rw [hs]; exact hN
  have hA' : rdq(W, Y.cpu.gpr.rsp + 32#64) = A := by rw [hs]; exact hAa
  have f40 : ∀ i < 4, Foot F.data (Addr.add (Y.cpu.gpr.rsp + 40#64) i) := by rw [hs]; exact E.f40
  have f32 : ∀ i < 8, Foot F.data (Addr.add (Y.cpu.gpr.rsp + 32#64) i) := by rw [hs]; exact E.f32
  by_cases hn0 : N = 0
  · refine (c_243 prof fb).run E.c E.hfs E.hin (fun j' g' _ V' => j' = 323 ∧ V' = W ∧ g'.rsp = Y.cpu.gpr.rsp ∧
        g'.rdi = rdq(W, Y.cpu.gpr.rsp + 32#64)) hK hA hr
      (vc_243z hn' hn0 f40 f32 fun _ a b _ => ⟨rfl, rfl, a, b⟩) ?_
    rintro j' g fl V₁ ⟨rfl, hV₁, gs, gdi⟩ U t₁ hKU hAU hrU hgU -
    subst V₁ hgU
    have e0 : N.toNat = 0 := (congrArg BitVec.toNat hn0).trans rfl
    rw [e0] at hD
    exact from323 E A U W t₁ hKU hAU hrU ⟨hD, gs.trans hs, gdi.trans hA'⟩
  · refine (c_243 prof fb).run E.c E.hfs E.hin (fun j' g' _ V' => j' = 272 ∧ V' = W ∧ g'.rsp = Y.cpu.gpr.rsp ∧
        g'.rdi = rdq(W, Y.cpu.gpr.rsp + 32#64) ∧ g'.rbx = rbx0 N) hK hA hr
      (vc_243n hn' hn0 f40 f32 fun _ a b d _ => ⟨rfl, rfl, a, b, d⟩) ?_
    rintro j' g fl V₁ ⟨rfl, hV₁, gs, gdi, gb⟩ U t₁ hKU hAU hrU hgU -
    subst V₁ hgU
    have hnz : N.toNat ≠ 0 := fun e => hn0 (BitVec.eq_of_toNat_eq (e.trans rfl))
    have h2 : N.toNat < 4294967296 := N.isLt
    have e1 : N.toNat - 1 + 1 = N.toNat := by omega
    rw [← e1] at hD
    exact L272 E A (from323 E A) (N.toNat - 1) (by omega) U W t₁ hKU hAU hrU
      ⟨hD, gs.trans hs, by rw [gb, rbx0_eq hn0], gdi.trans hA'⟩

/-- From 221 (the bytes with `P`): `Parent->CheckPathToRoot_Change (include, pathParts2, isFile)` (`k238`), from its
return 243. -/
theorem from221 (E : Ev prof F Wl L s₀ o gev gP gE fb S g0 e₂ code₂ j₂ I0 I1 I3 I2 I4 I5 P Q4 D Jd Iz)
    (hK : KeptW Wl s₀ Y) (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = cpr_at.add 221)
    (hm : Fm S g0 Y.cpu.gpr) (hP : P W) :
    GoG prof L o gev gP gE Y t := by
  refine (c_221 prof fb).run E.c E.hfs E.hin (fun j' g' _ V' => j' = 238 ∧ V' = W ∧ Fr Y.cpu.gpr g' ∧
      g'.rdx = Y.cpu.gpr.rsp + 32#64) hK hA hr
    (vc_221 (by rw [hm.2.1]; exact E.fpar) fun _ a b _ => ⟨rfl, rfl, a, b⟩) ?_
  rintro j' g fl V₁ ⟨rfl, hV₁, gf, gdx⟩ U t₁ hKU hAU hrU hgU -
  subst V₁ hgU
  have hmU := Fm.fr hm gf
  refine callK E hKU hAU hrU hmU.1 (lt_len (by decide)) (call_238 _) tgt_238 E.cP (E.k238 W hP)
    (by show U.cpu.gpr.rdx = _; rw [gdx, hm.1]) ?_
  intro Z W' t₃ hKZ hAZ hrZ hsZ hkZ hDZ
  exact from243 E hKZ hAZ hrZ hsZ hDZ

/-- From 188 (back from the copy `r` = `r12`, the bytes with `I5 r`): the append, then `pathParts._size` 0 to 221
(`z221`), else to 425 (`z425`, `h425`). -/
theorem from188 (E : Ev prof F Wl L s₀ o gev gP gE fb S g0 e₂ code₂ j₂ I0 I1 I3 I2 I4 I5 P Q4 D Jd Iz)
    {r : BitVec 64} (hK : KeptW Wl s₀ Y) (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = cpr_at.add 188)
    (hm : Fm S g0 Y.cpu.gpr) (h12 : Y.cpu.gpr.r12 = r) (hI : I5 r W) :
    GoG prof L o gev gP gE Y t := by
  have e40 : Y.cpu.gpr.rsp + 40#64 = aR S + 40#64 := by rw [hm.1]
  have e32 : Y.cpu.gpr.rsp + 32#64 = aR S + 32#64 := by rw [hm.1]
  have e8 : Y.cpu.gpr.rbp + 8#64 = g0.rdx + 8#64 := by rw [hm.2.2]
  refine (c_188 prof fb).run E.c E.hfs E.hin (fun j' g' _ V' => Fr Y.cpu.gpr g' ∧ V' = St188 S r W ∧
      ((j' = 221 ∧ rdd(W, g0.rdx + 8#64) = 0) ∨ (j' = 425 ∧ rdd(W, g0.rdx + 8#64) ≠ 0 ∧
        g'.r15 = BitVec.setWidth 64 rdd(W, g0.rdx + 8#64) ∧
        g'.rdx = BitVec.setWidth 64 (rdd(W, aR S + 40#64) + 1#32)))) hK hA hr
    (vc_188 (by rw [e40]; exact E.f40) (by rw [e32]; exact E.f32) (by rw [e8]; exact E.fn8)
      (by rw [e40]; exact fun i hi => E.w40 i (by omega)) (by rw [e40, e32]; exact E.wsl r W hI)
      (fun _ x hx h0 a _ => ⟨a, by rw [hx, h12, e40, e32], Or.inl ⟨rfl, by rw [← e8]; exact h0⟩⟩)
      (fun _ x hx h0 a d e _ => ⟨a, by rw [hx, h12, e40, e32],
        Or.inr ⟨rfl, by rw [← e8]; exact h0, by rw [d, e8], by rw [e, hx, e40]⟩⟩)) ?_
  rintro j' g fl V₁ ⟨gf, rfl, hj⟩ U t₁ hKU hAU hrU hgU -
  subst hgU
  have hmU := Fm.fr hm gf
  rcases hj with ⟨rfl, h0⟩ | ⟨rfl, h0, g15, gdx⟩
  · exact from221 E hKU hAU hrU hmU (E.z221 r W hI h0)
  · exact E.h425 U _ t₁ hKU hAU hrU ⟨hmU, _, _, g15, gdx, E.z425 r W hI h0⟩

/-- From 174 (back from `operator new (0x10)`, its result `rax`, the bytes with `I4 rax`): the copy of `Name` into it
(`k183`), from its return 188. -/
theorem from174 (E : Ev prof F Wl L s₀ o gev gP gE fb S g0 e₂ code₂ j₂ I0 I1 I3 I2 I4 I5 P Q4 D Jd Iz)
    (hK : KeptW Wl s₀ Y) (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = cpr_at.add 174)
    (hm : Fm S g0 Y.cpu.gpr) (hI : I4 Y.cpu.gpr.rax W) :
    GoG prof L o gev gP gE Y t := by
  refine (c_174 prof fb).run E.c E.hfs E.hin (fun j' g' _ V' => j' = 183 ∧ V' = W ∧ Fr Y.cpu.gpr g' ∧
      g'.rdi = Y.cpu.gpr.rax ∧ g'.r12 = Y.cpu.gpr.rax) hK hA hr
    (vc_174 fun _ a b d _ => ⟨rfl, rfl, a, b, d⟩) ?_
  rintro j' g fl V₁ ⟨rfl, hV₁, gf, gdi, g12⟩ U t₁ hKU hAU hrU hgU -
  subst V₁ hgU
  have hmU := Fm.fr hm gf
  refine callK E hKU hAU hrU hmU.1 (lt_len (by decide)) (call_183 _) tgt_183 E.cU (E.k183 _ _ hI) gdi ?_
  intro Z W' t₃ hKZ hAZ hrZ hsZ hkZ hIZ
  exact from188 E hKZ hAZ hrZ (fm_ret hmU hsZ hkZ) (hkZ.2.2.1.trans g12) hIZ

/-- From 117 (back from `operator new [] (8)`, the bytes with `I2`): the slots 0 (`h117`), the stores at 146,
`operator new (0x10)` (`k169`), from its return 174. -/
theorem from117 (E : Ev prof F Wl L s₀ o gev gP gE fb S g0 e₂ code₂ j₂ I0 I1 I3 I2 I4 I5 P Q4 D Jd Iz)
    (hK : KeptW Wl s₀ Y) (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = cpr_at.add 117)
    (hm : Fm S g0 Y.cpu.gpr) (hI : I2 Y.cpu.gpr W) :
    GoG prof L o gev gP gE Y t := by
  obtain ⟨hn, hp⟩ := E.h117 _ W hI
  refine (c_117 prof fb).run E.c E.hfs E.hin (fun j' g' _ V' => j' = 146 ∧ V' = W ∧ Fr Y.cpu.gpr g' ∧
      g'.r12 = Y.cpu.gpr.rax) hK hA hr
    (vc_117 (n32 := 0#32) (p := 0#64) (by rw [hm.1]; exact hn) rfl (by rw [hm.1]; exact hp) rfl
      (by rw [hm.1]; exact E.f40) (by rw [hm.1]; exact E.f32) fun _ a b _ => ⟨rfl, rfl, a, b⟩) ?_
  rintro j' g fl V₁ ⟨rfl, hV₁, gf, g12⟩ U t₁ hKU hAU hrU hgU -
  subst V₁ hgU
  have hmU := Fm.fr hm gf
  refine (c_146 prof fb).run E.c E.hfs E.hin (fun j' g' _ V' => j' = 169 ∧
      V' = Vst (Vst W (U.cpu.gpr.rsp + 32#64) (toBytesLE U.cpu.gpr.r12 8)) (U.cpu.gpr.rsp + 44#64)
        (toBytesLE 1#32 4) ∧ Fr U.cpu.gpr g' ∧ g'.rdi = 16#64) hKU hAU hrU
    (vc_146 (by rw [hmU.1]; exact E.w32) (by rw [hmU.1]; exact E.w44) fun _ a b _ => ⟨rfl, rfl, a, b⟩) ?_
  rintro j' g fl V₂ ⟨rfl, hV₂, gf₂, gdi₂⟩ U₂ t₂ hKU₂ hAU₂ hrU₂ hgU₂ -
  subst V₂ hgU₂
  rw [hmU.1, g12] at hAU₂
  have hmU₂ := Fm.fr hmU gf₂
  refine callK E hKU₂ hAU₂ hrU₂ hmU₂.1 (lt_len (by decide)) (call_169 _) tgt_169 E.cN
    (E.k169 _ (E.z146 _ _ hI)) gdi₂ ?_
  intro Z W' t₃ hKZ hAZ hrZ hsZ hkZ hIZ
  exact from174 E hKZ hAZ hrZ (fm_ret hmU₂ hsZ hkZ) hIZ

/-- From 59 (back from `CheckPathCurrent`, the bytes with `I0`): its result or `Parent` null to 333 (`hz0`), else
the stores of 0 (`z80`), `operator new [] (8)` (`k112`), from its return 117. -/
theorem from59 (E : Ev prof F Wl L s₀ o gev gP gE fb S g0 e₂ code₂ j₂ I0 I1 I3 I2 I4 I5 P Q4 D Jd Iz)
    (hK : KeptW Wl s₀ Y) (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = cpr_at.add 59)
    (hm : Fm S g0 Y.cpu.gpr) (hI : I0 W) :
    GoG prof L o gev gP gE Y t := by
  refine (c_59 prof fb).run E.c E.hfs E.hin (fun j' g' _ V' => Fr Y.cpu.gpr g' ∧ ((j' = 333 ∧ V' = W) ∨
      (j' = 112 ∧ g'.rdi = 8#64 ∧ V' = Vst (Vst W (Y.cpu.gpr.rsp + 32#64) (toBytesLE 0#64 8))
        (Y.cpu.gpr.rsp + 40#64) (toBytesLE 0#64 8)))) hK hA hr
    (vc_59 (by rw [hm.2.1]; exact E.fpar) (by rw [hm.1]; exact E.w32) (by rw [hm.1]; exact E.w40)
      (fun _ a _ => ⟨a, Or.inl ⟨rfl, rfl⟩⟩) (fun _ a b _ => ⟨a, Or.inr ⟨rfl, b, rfl⟩⟩)) ?_
  rintro j' g fl V₁ ⟨gf, ⟨rfl, rfl⟩ | ⟨rfl, gdi, rfl⟩⟩ U t₁ hKU hAU hrU hgU -
  · subst hgU
    exact tail333 E hKU hAU hrU (gf.1.trans hm.1) (E.hz0 W hI)
  · subst hgU
    have hmU := Fm.fr hm gf
    rw [hm.1] at hAU
    refine callK E hKU hAU hrU hmU.1 (lt_len (by decide)) (call_112 _) tgt_112 E.cA (E.k112 _ (E.z80 W hI))
      gdi ?_
    intro Z W' t₃ hKZ hAZ hrZ hsZ hkZ hIZ
    exact from117 E hKZ hAZ hrZ (fm_ret hmU hsZ hkZ) hIZ

end Runs

variable {prof : Profile} {F : Footprint} {Wl : List Rgn} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {X : State} {t : Nat} {V : Addr → Byte}

/-- `NWildcard::CCensorNode::CheckPathToRoot (include, pathParts, isFile)` from its entry, `fb` the `fs` base, the
run from 425 (`pathParts` not empty: the growth and the copy loop) a hypothesis (`h425`): the pushes' slots, the
guard's slot, the local's slots and the calls' return address slot in what the run may store into; the guard at
`fs:0x28`, `Parent`, `pathParts._size`, the return address readable. The callees and the invariants as in `Ev`
(`k54`: `CheckPathCurrent`, from its return the bytes with `I0`). At the return address (`kr`): `rsp` 8 above the
entry's, the callee-saved registers as they were, bytes with `Iz`. -/
theorem cpr_ok {fb : Addr} {e₂ : Addr} {code₂ : List Byte} {j₂ : Nat}
    {I0 I1 I3 : (Addr → Byte) → Prop} {I2 : Gprs → (Addr → Byte) → Prop} {I4 I5 : BitVec 64 → (Addr → Byte) → Prop}
    {P : (Addr → Byte) → Prop} {Q4 : BitVec 32 → BitVec 32 → (Addr → Byte) → Prop}
    {D : BitVec 64 → Nat → (Addr → Byte) → Prop} {Jd : BitVec 64 → Nat → BitVec 64 → (Addr → Byte) → Prop}
    {Iz : (Addr → Byte) → Prop}
    (c : Seg prof F Wl L s₀ o) (hfs : s₀.cpu.seg.fsBase = fb) (hin : CodeIn L cpr_at cpr)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = cpr_at)
    (hcl : ∀ i < 8, Foot F.data (Addr.add (fb + 40#64) i))
    (hs1 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8) i))
    (hs2 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8 - 8) i))
    (hs3 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8 - 8 - 8) i))
    (hs4 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8 - 8 - 8 - 8) i))
    (hs5 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8 - 8 - 8 - 8 - 8) i))
    (hs6 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8 - 8 - 8 - 8 - 8 - 8) i))
    (hw : ∀ i < 8, Foot Wl (Addr.add (aR X.cpu.gpr.rsp + 56#64) i))
    (w32 : ∀ i < 8, Foot Wl (Addr.add (aR X.cpu.gpr.rsp + 32#64) i))
    (w40 : ∀ i < 8, Foot Wl (Addr.add (aR X.cpu.gpr.rsp + 40#64) i))
    (w44 : ∀ i < 4, Foot Wl (Addr.add (aR X.cpu.gpr.rsp + 44#64) i))
    (hr8 : ∀ i < 8, Foot Wl (Addr.add (aR X.cpu.gpr.rsp - 8) i))
    (hl : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsp i))
    (hin₂ : CodeIn L e₂ code₂) (h₂ : j₂ < code₂.length)
    (fpar : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rdi i))
    (fn8 : ∀ i < 4, Foot F.data (Addr.add (X.cpu.gpr.rdx + 8#64) i))
    (hIz : ∀ W, Iz W → Stk W X.cpu.gpr.rsp X.cpu.gpr (e₂.add j₂) ∧ Gd fb W X.cpu.gpr.rsp)
    (hz0 : ∀ W, I0 W → Iz W)
    (z80 : ∀ W, I0 W → I1 (Vst (Vst W (aR X.cpu.gpr.rsp + 32#64) (toBytesLE 0#64 8)) (aR X.cpu.gpr.rsp + 40#64)
      (toBytesLE 0#64 8)))
    (h117 : ∀ g W, I2 g W → rdd(W, aR X.cpu.gpr.rsp + 40#64) = 0#32 ∧ rdq(W, aR X.cpu.gpr.rsp + 32#64) = 0#64)
    (z146 : ∀ g W, I2 g W → I3 (Vst (Vst W (aR X.cpu.gpr.rsp + 32#64) (toBytesLE g.rax 8))
      (aR X.cpu.gpr.rsp + 44#64) (toBytesLE 1#32 4)))
    (wsl : ∀ r W, I5 r W → ∀ i < 8, Foot Wl (Addr.add (rdq(W, aR X.cpu.gpr.rsp + 32#64) +
      BitVec.setWidth 64 rdd(W, aR X.cpu.gpr.rsp + 40#64) * 8#64) i))
    (z221 : ∀ r W, I5 r W → rdd(W, X.cpu.gpr.rdx + 8#64) = 0 → P (St188 X.cpu.gpr.rsp r W))
    (z425 : ∀ r W, I5 r W → rdd(W, X.cpu.gpr.rdx + 8#64) ≠ 0 →
      Q4 rdd(W, X.cpu.gpr.rdx + 8#64) (rdd(W, aR X.cpu.gpr.rsp + 40#64) + 1#32) (St188 X.cpu.gpr.rsp r W))
    (hDa : ∀ A k W, D A k W → rdq(W, aR X.cpu.gpr.rsp + 32#64) = A)
    (fe : ∀ A k W, D A (k + 1) W → ∀ i < 8, Foot F.data (Addr.add (A + BitVec.ofNat 64 (8 * k)) i))
    (fp : ∀ A k W, D A (k + 1) W → pk W A k ≠ 0 → ∀ i < 8, Foot F.data (Addr.add (pk W A k) i))
    (hP0 : ∀ A k W, D A (k + 1) W → pk W A k = 0 → D A k W)
    (hQ0 : ∀ A k W, D A (k + 1) W → pk W A k ≠ 0 → rdq(W, pk W A k) = 0 → Jd A k (pk W A k) W)
    (hA0 : ∀ W, D 0 0 W → Iz W)
    (cK : ∃ code : List Byte, CodeIn L 0x453050#64 code ∧ 0 < code.length)
    (cA : ∃ code : List Byte, CodeIn L 0x6029b0#64 code ∧ 0 < code.length)
    (cN : ∃ code : List Byte, CodeIn L 0x602970#64 code ∧ 0 < code.length)
    (cU : ∃ code : List Byte, CodeIn L 0x44d5d0#64 code ∧ 0 < code.length)
    (cP : ∃ code : List Byte, CodeIn L 0x4530c0#64 code ∧ 0 < code.length)
    (cD : ∃ code : List Byte, CodeIn L 0x6014f0#64 code ∧ 0 < code.length)
    (cE : ∃ code : List Byte, CodeIn L 0x6014e0#64 code ∧ 0 < code.length)
    (k54 : KC prof F Wl L s₀ o gev gP gE X.cpu.gpr.rsp 0x453050#64 59 (V0 fb V X.cpu.gpr)
      (fun g => g.rdi = X.cpu.gpr.rdi ∧ g.rdx = X.cpu.gpr.rdx) (fun _ => I0))
    (k112 : ∀ W, I1 W → KC prof F Wl L s₀ o gev gP gE X.cpu.gpr.rsp 0x6029b0#64 117 W (fun g => g.rdi = 8#64) I2)
    (k169 : ∀ W, I3 W → KC prof F Wl L s₀ o gev gP gE X.cpu.gpr.rsp 0x602970#64 174 W (fun g => g.rdi = 16#64)
      (fun g W' => I4 g.rax W'))
    (k183 : ∀ r W, I4 r W → KC prof F Wl L s₀ o gev gP gE X.cpu.gpr.rsp 0x44d5d0#64 188 W (fun g => g.rdi = r)
      (fun _ => I5 r))
    (k238 : ∀ W, P W → KC prof F Wl L s₀ o gev gP gE X.cpu.gpr.rsp 0x4530c0#64 243 W
      (fun g => g.rdx = aR X.cpu.gpr.rsp + 32#64)
      (fun _ W' => D rdq(W', aR X.cpu.gpr.rsp + 32#64) rdd(W', aR X.cpu.gpr.rsp + 40#64).toNat W'))
    (k290 : ∀ A k W, D A (k + 1) W → pk W A k ≠ 0 → rdq(W, pk W A k) ≠ 0 →
      KC prof F Wl L s₀ o gev gP gE X.cpu.gpr.rsp 0x6014f0#64 295 W (fun g => g.rdi = rdq(W, pk W A k))
        (fun _ => Jd A k (pk W A k)))
    (k303 : ∀ A k p W, p ≠ 0 → Jd A k p W →
      KC prof F Wl L s₀ o gev gP gE X.cpu.gpr.rsp 0x6014e0#64 308 W (fun g => g.rdi = p ∧ g.rsi = 16#64)
        (fun _ => D A k))
    (k328 : ∀ A W, A ≠ 0 → D A 0 W →
      KC prof F Wl L s₀ o gev gP gE X.cpu.gpr.rsp 0x6014f0#64 333 W (fun g => g.rdi = A) (fun _ => Iz))
    (h425 : AtJ prof F Wl L s₀ o gev gP gE 425 fun g W => Fm X.cpu.gpr.rsp X.cpu.gpr g ∧
      ∃ m x, g.r15 = BitVec.setWidth 64 m ∧ g.rdx = BitVec.setWidth 64 x ∧ Q4 m x W)
    (kr : ∀ (W : Addr → Byte) (Z' : State) (t' : Nat), KeptW Wl s₀ Z' → Agree F Z'.proc.mm.mem W →
      Z'.cpu.rip = e₂.add j₂ → Z'.cpu.gpr.rsp = X.cpu.gpr.rsp + 8 → KS X.cpu.gpr Z'.cpu.gpr → Iz W →
      GoG prof L o gev gP gE Z' t') :
    GoG prof L o gev gP gE X t := by
  have E : Ev prof F Wl L s₀ o gev gP gE fb X.cpu.gpr.rsp X.cpu.gpr e₂ code₂ j₂ I0 I1 I3 I2 I4 I5 P Q4 D Jd Iz :=
    { c := c, hfs := hfs, hin := hin, hin₂ := hin₂, h₂ := h₂, hIz := hIz, hcl := hcl,
      fg := fun i hi => c.hws _ (hw i hi), w32 := w32, w40 := w40, w44 := w44,
      f32 := fun i hi => c.hws _ (w32 i hi), f40 := fun i hi => c.hws _ (w40 i (by omega)),
      fpar := fpar, fn8 := fn8,
      fb48 := fun i hi => c.hws _ (hs6 i hi), fb40 := fun i hi => c.hws _ (hs5 i hi),
      fb32 := fun i hi => c.hws _ (hs4 i hi), fb24 := fun i hi => c.hws _ (hs3 i hi),
      fb16 := fun i hi => c.hws _ (hs2 i hi), fb8 := fun i hi => c.hws _ (hs1 i hi), hl := hl, hr8 := hr8,
      hz0 := hz0, z80 := z80, h117 := h117, z146 := z146, wsl := wsl, z221 := z221, z425 := z425,
      hDa := hDa, fe := fe, fp := fp, hP0 := hP0, hQ0 := hQ0, hA0 := hA0,
      cA := cA, cN := cN, cU := cU, cP := cP, cD := cD, cE := cE,
      k112 := k112, k169 := k169, k183 := k183, k238 := k238, k290 := k290, k303 := k303, k328 := k328,
      h425 := h425, kr := kr }
  -- the prologue, to the first `call`
  have hrip' : X.cpu.rip = cpr_at.add 0 := by rw [addr_add_zero]; exact hrip
  refine (c_0 prof fb).run c hfs hin (fun j' g' _ V' => j' = 54 ∧ V' = V0 fb V X.cpu.gpr ∧
      Fm X.cpu.gpr.rsp X.cpu.gpr g' ∧ g'.rdi = X.cpu.gpr.rdi ∧ g'.rdx = X.cpu.gpr.rdx) hK hA hrip'
    (vc_0 rfl hs1 hs2 hs3 hs4 hs5 hs6 hcl hw fun _ a b d e i _ => ⟨rfl, rfl, ⟨a, b, d⟩, e, i⟩) ?_
  rintro j' g fl V₁ ⟨rfl, hV₁, hm, gdi, gdx⟩ Y t₁ hKY hAY hrY hgY -
  subst V₁ hgY
  refine callK E hKY hAY hrY hm.1 (lt_len (by decide)) (call_54 _) tgt_54 cK k54 ⟨gdi, gdx⟩ ?_
  intro Z W' t₃ hKZ hAZ hrZ hsZ hkZ hIZ
  exact from59 E hKZ hAZ hrZ (fm_ret hm hsZ hkZ) hIZ

end FV7z.Cpr
