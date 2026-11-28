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
    (h : ∀ g', g'.rsp = aR g.rsp → g'.rbx = g.rdi → g'.rbp = g.rdx →
      ∀ fl, Q 54 g' fl (Vst (P6 V g) (aR g.rsp + 56#64) (toBytesLE cn 8))) :
    W_0 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [aR, P6] at hcn hs1 hs2 hs3 hs4 hs5 hs6 hw h ⊢
  wpx [W_0, o0, Op.ldf, Op.zxr, hcn]
  all_goals repeat' (first
    | refine h _ ?_ ?_ ?_ _
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

end FV7z.Cpr
