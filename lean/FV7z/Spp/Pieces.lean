import FV7z.Spp.Cuts
import FV7z.Lemmas.LeafRet
import FV7z.Lemmas.Fr40
import FV7z.Ocv.Holds
/-!
# `SplitPathToParts` (PLAN.md §M, M1): the instructions outside the blocks, the frame, the pieces

7-Zip 26.06's `SplitPathToParts (const UString &path, UStringVector &pathParts)` at `0x452500` in `7zzs`
(`CPP/Common/Wildcard.cpp`; `objdump -d`): `path` in `rdi`, `pathParts` in `rsi` (`rbp`). `S` the stack pointer at
the entry: `push r15, r14, r13, r12, rbp, rbx; sub rsp, 0x48` (`aR S`), `path` kept at `aR S + 8`, the stack guard
(`fs:0x28`) at `aR S + 56`, a local `UString` (`name`) at `aR S + 32` (`r15`).

- `pathParts.Clear ()` inlined (0–112): the size `n32` (the 4 bytes at `pathParts + 8`) not 0 gives `rbx` =
  `8 (n32 - 1)` (`Ocv.rbx0`) and the loop (head 64) from the last item down: an item `p` (the 8 bytes at
  `_items + rbx`) not 0 has its chars (the 8 bytes at `p`) freed unless 0 (86, `operator delete []` at `0x6014f0`)
  and is freed (99, `operator delete (p, 16)` at `0x6014e0`); `rbx` -= 8 (104).
- 114: the size set to 0, `r12d` = `len` (the 4 bytes at `path + 8`); 0 gives the epilogue (135). Else `name`'s
  constructor (184, `0x44d3e0`), `rax` = `path._chars`, `ecx` = `ebx` = 0.
- The scan (head 221, `rbx` = `i`): a char not `'/'` (the 4 bytes at `_chars + 4 i`) goes on with `i + 1` (208) while
  `i + 1 < len`; a `'/'` gives `name.SetFrom (_chars + start, i - start)` (254, `0x44d790`), `pathParts.Add (name)`
  inlined (259: the growth when full, `ja` to the throw at 272 when the capacity is `0x7fffffff`, `operator new []`
  at 309 (`0x6029b0`), `memcpy` (627, `0x401070`) and `delete []` (648) of the old items; `operator new (16)` at 357
  (`0x602970`), the item's `UString (name)` at 373 (`0x44d5d0`), the slot and the size (378)), `start = i + 1`, and
  back to 221 while `i + 1 < len`.
- 432: the last part the same way (440, 445–557: `ja` at 458, 494, 686, 694, 538, 552), `delete []` of `name`'s
  chars unless 0 (588), the guard's check and the epilogue (135), `ret` (169). Not covered: `__stack_chk_fail` (704),
  the landing pads.

The pieces (`vc_*`) are stated on the registers and the bytes: the loads before a store by named values (`hit`, `hp`,
`hn`), the bytes after a piece's stores by an invariant `I` the caller chooses and the stores that keep it (`Ok`,
`hcl`, as in `FV7z/Api/Holds.lean`). A loop's exit is a hypothesis on the compared registers (`hc`, as in
`FV7z/Ffp/Holds.lean`). The chars' values are not tracked: both ways of the `'/'` test are pieces' continuations.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Spp
set_option linter.unusedVariables false

open FV7z.Fr40 (KS r1 r2 r3 r4 r5)
open FV7z.Ocv (rbx0)

/-! ## The instructions outside the blocks -/

/-- The `call` at 86: `operator delete []` (`0x6014f0`). -/
def pc86 : List Byte := [0xe8, 0x95, 0xef, 0x1a, 0x00]
theorem pc86_0 : ∀ feat, Dec feat pc86 0 (FV7z.mk .call 64 [.rel 1765269] 5) := by dec_rfl
theorem wc_86 : pc86 <+: spp.drop 86 := by decide +kernel
theorem call_86 (feat : Features) : Dec feat spp 86 (FV7z.mk .call 64 [.rel 1765269] 5) :=
  Dec.shift (j := 86) (k := 0) (pc86_0 feat) wc_86 (Nat.zero_le _)
theorem tgt_86 : spp_at.add (86 + 5) + BitVec.ofNat 64 1765269 = 0x6014f0#64 := by decide

/-- The `call` at 99: `operator delete (p, 16)` (`0x6014e0`). -/
def pc99 : List Byte := [0xe8, 0x78, 0xef, 0x1a, 0x00]
theorem pc99_0 : ∀ feat, Dec feat pc99 0 (FV7z.mk .call 64 [.rel 1765240] 5) := by dec_rfl
theorem wc_99 : pc99 <+: spp.drop 99 := by decide +kernel
theorem call_99 (feat : Features) : Dec feat spp 99 (FV7z.mk .call 64 [.rel 1765240] 5) :=
  Dec.shift (j := 99) (k := 0) (pc99_0 feat) wc_99 (Nat.zero_le _)
theorem tgt_99 : spp_at.add (99 + 5) + BitVec.ofNat 64 1765240 = 0x6014e0#64 := by decide

/-- The `call` at 184: `UString::UString ()` (`0x44d3e0`). -/
def pc184 : List Byte := [0xe8, 0x23, 0xae, 0xff, 0xff]
theorem pc184_0 : ∀ feat, Dec feat pc184 0 (FV7z.mk .call 64 [.rel 18446744073709530659] 5) := by dec_rfl
theorem wc_184 : pc184 <+: spp.drop 184 := by decide +kernel
theorem call_184 (feat : Features) : Dec feat spp 184 (FV7z.mk .call 64 [.rel 18446744073709530659] 5) :=
  Dec.shift (j := 184) (k := 0) (pc184_0 feat) wc_184 (Nat.zero_le _)
theorem tgt_184 : spp_at.add (184 + 5) + BitVec.ofNat 64 18446744073709530659 = 0x44d3e0#64 := by decide

/-- The `call` at 254: `UString::SetFrom` (`0x44d790`). -/
def pc254 : List Byte := [0xe8, 0x8d, 0xb1, 0xff, 0xff]
theorem pc254_0 : ∀ feat, Dec feat pc254 0 (FV7z.mk .call 64 [.rel 18446744073709531533] 5) := by dec_rfl
theorem wc_254 : pc254 <+: spp.drop 254 := by decide +kernel
theorem call_254 (feat : Features) : Dec feat spp 254 (FV7z.mk .call 64 [.rel 18446744073709531533] 5) :=
  Dec.shift (j := 254) (k := 0) (pc254_0 feat) wc_254 (Nat.zero_le _)
theorem tgt_254 : spp_at.add (254 + 5) + BitVec.ofNat 64 18446744073709531533 = 0x44d790#64 := by decide

/-- The `call` at 309: `operator new []` (`0x6029b0`). -/
def pc309 : List Byte := [0xe8, 0x76, 0x03, 0x1b, 0x00]
theorem pc309_0 : ∀ feat, Dec feat pc309 0 (FV7z.mk .call 64 [.rel 1770358] 5) := by dec_rfl
theorem wc_309 : pc309 <+: spp.drop 309 := by decide +kernel
theorem call_309 (feat : Features) : Dec feat spp 309 (FV7z.mk .call 64 [.rel 1770358] 5) :=
  Dec.shift (j := 309) (k := 0) (pc309_0 feat) wc_309 (Nat.zero_le _)
theorem tgt_309 : spp_at.add (309 + 5) + BitVec.ofNat 64 1770358 = 0x6029b0#64 := by decide

/-- The `call` at 357: `operator new` (`0x602970`). -/
def pc357 : List Byte := [0xe8, 0x06, 0x03, 0x1b, 0x00]
theorem pc357_0 : ∀ feat, Dec feat pc357 0 (FV7z.mk .call 64 [.rel 1770246] 5) := by dec_rfl
theorem wc_357 : pc357 <+: spp.drop 357 := by decide +kernel
theorem call_357 (feat : Features) : Dec feat spp 357 (FV7z.mk .call 64 [.rel 1770246] 5) :=
  Dec.shift (j := 357) (k := 0) (pc357_0 feat) wc_357 (Nat.zero_le _)
theorem tgt_357 : spp_at.add (357 + 5) + BitVec.ofNat 64 1770246 = 0x602970#64 := by decide

/-- The `call` at 373: `UString::UString (const UString &)` (`0x44d5d0`). -/
def pc373 : List Byte := [0xe8, 0x56, 0xaf, 0xff, 0xff]
theorem pc373_0 : ∀ feat, Dec feat pc373 0 (FV7z.mk .call 64 [.rel 18446744073709530966] 5) := by dec_rfl
theorem wc_373 : pc373 <+: spp.drop 373 := by decide +kernel
theorem call_373 (feat : Features) : Dec feat spp 373 (FV7z.mk .call 64 [.rel 18446744073709530966] 5) :=
  Dec.shift (j := 373) (k := 0) (pc373_0 feat) wc_373 (Nat.zero_le _)
theorem tgt_373 : spp_at.add (373 + 5) + BitVec.ofNat 64 18446744073709530966 = 0x44d5d0#64 := by decide

/-- The `call` at 440: `UString::SetFrom` (`0x44d790`). -/
def pc440 : List Byte := [0xe8, 0xd3, 0xb0, 0xff, 0xff]
theorem pc440_0 : ∀ feat, Dec feat pc440 0 (FV7z.mk .call 64 [.rel 18446744073709531347] 5) := by dec_rfl
theorem wc_440 : pc440 <+: spp.drop 440 := by decide +kernel
theorem call_440 (feat : Features) : Dec feat spp 440 (FV7z.mk .call 64 [.rel 18446744073709531347] 5) :=
  Dec.shift (j := 440) (k := 0) (pc440_0 feat) wc_440 (Nat.zero_le _)
theorem tgt_440 : spp_at.add (440 + 5) + BitVec.ofNat 64 18446744073709531347 = 0x44d790#64 := by decide

/-- The `call` at 494: `operator new []` (`0x6029b0`). -/
def pc494 : List Byte := [0xe8, 0xbd, 0x02, 0x1b, 0x00]
theorem pc494_0 : ∀ feat, Dec feat pc494 0 (FV7z.mk .call 64 [.rel 1770173] 5) := by dec_rfl
theorem wc_494 : pc494 <+: spp.drop 494 := by decide +kernel
theorem call_494 (feat : Features) : Dec feat spp 494 (FV7z.mk .call 64 [.rel 1770173] 5) :=
  Dec.shift (j := 494) (k := 0) (pc494_0 feat) wc_494 (Nat.zero_le _)
theorem tgt_494 : spp_at.add (494 + 5) + BitVec.ofNat 64 1770173 = 0x6029b0#64 := by decide

/-- The `call` at 538: `operator new` (`0x602970`). -/
def pc538 : List Byte := [0xe8, 0x51, 0x02, 0x1b, 0x00]
theorem pc538_0 : ∀ feat, Dec feat pc538 0 (FV7z.mk .call 64 [.rel 1770065] 5) := by dec_rfl
theorem wc_538 : pc538 <+: spp.drop 538 := by decide +kernel
theorem call_538 (feat : Features) : Dec feat spp 538 (FV7z.mk .call 64 [.rel 1770065] 5) :=
  Dec.shift (j := 538) (k := 0) (pc538_0 feat) wc_538 (Nat.zero_le _)
theorem tgt_538 : spp_at.add (538 + 5) + BitVec.ofNat 64 1770065 = 0x602970#64 := by decide

/-- The `call` at 552: `UString::UString (const UString &)` (`0x44d5d0`). -/
def pc552 : List Byte := [0xe8, 0xa3, 0xae, 0xff, 0xff]
theorem pc552_0 : ∀ feat, Dec feat pc552 0 (FV7z.mk .call 64 [.rel 18446744073709530787] 5) := by dec_rfl
theorem wc_552 : pc552 <+: spp.drop 552 := by decide +kernel
theorem call_552 (feat : Features) : Dec feat spp 552 (FV7z.mk .call 64 [.rel 18446744073709530787] 5) :=
  Dec.shift (j := 552) (k := 0) (pc552_0 feat) wc_552 (Nat.zero_le _)
theorem tgt_552 : spp_at.add (552 + 5) + BitVec.ofNat 64 18446744073709530787 = 0x44d5d0#64 := by decide

/-- The `call` at 588: `operator delete []` (`0x6014f0`). -/
def pc588 : List Byte := [0xe8, 0x9f, 0xed, 0x1a, 0x00]
theorem pc588_0 : ∀ feat, Dec feat pc588 0 (FV7z.mk .call 64 [.rel 1764767] 5) := by dec_rfl
theorem wc_588 : pc588 <+: spp.drop 588 := by decide +kernel
theorem call_588 (feat : Features) : Dec feat spp 588 (FV7z.mk .call 64 [.rel 1764767] 5) :=
  Dec.shift (j := 588) (k := 0) (pc588_0 feat) wc_588 (Nat.zero_le _)
theorem tgt_588 : spp_at.add (588 + 5) + BitVec.ofNat 64 1764767 = 0x6014f0#64 := by decide

/-- The `call` at 627: `memcpy` (`0x401070`). -/
def pc627 : List Byte := [0xe8, 0xf8, 0xe8, 0xfa, 0xff]
theorem pc627_0 : ∀ feat, Dec feat pc627 0 (FV7z.mk .call 64 [.rel 18446744073709218040] 5) := by dec_rfl
theorem wc_627 : pc627 <+: spp.drop 627 := by decide +kernel
theorem call_627 (feat : Features) : Dec feat spp 627 (FV7z.mk .call 64 [.rel 18446744073709218040] 5) :=
  Dec.shift (j := 627) (k := 0) (pc627_0 feat) wc_627 (Nat.zero_le _)
theorem tgt_627 : spp_at.add (627 + 5) + BitVec.ofNat 64 18446744073709218040 = 0x401070#64 := by decide

/-- The `call` at 648: `operator delete []` (`0x6014f0`). -/
def pc648 : List Byte := [0xe8, 0x63, 0xed, 0x1a, 0x00]
theorem pc648_0 : ∀ feat, Dec feat pc648 0 (FV7z.mk .call 64 [.rel 1764707] 5) := by dec_rfl
theorem wc_648 : pc648 <+: spp.drop 648 := by decide +kernel
theorem call_648 (feat : Features) : Dec feat spp 648 (FV7z.mk .call 64 [.rel 1764707] 5) :=
  Dec.shift (j := 648) (k := 0) (pc648_0 feat) wc_648 (Nat.zero_le _)
theorem tgt_648 : spp_at.add (648 + 5) + BitVec.ofNat 64 1764707 = 0x6014f0#64 := by decide

/-- The `call` at 686: `memcpy` (`0x401070`). -/
def pc686 : List Byte := [0xe8, 0xbd, 0xe8, 0xfa, 0xff]
theorem pc686_0 : ∀ feat, Dec feat pc686 0 (FV7z.mk .call 64 [.rel 18446744073709217981] 5) := by dec_rfl
theorem wc_686 : pc686 <+: spp.drop 686 := by decide +kernel
theorem call_686 (feat : Features) : Dec feat spp 686 (FV7z.mk .call 64 [.rel 18446744073709217981] 5) :=
  Dec.shift (j := 686) (k := 0) (pc686_0 feat) wc_686 (Nat.zero_le _)
theorem tgt_686 : spp_at.add (686 + 5) + BitVec.ofNat 64 18446744073709217981 = 0x401070#64 := by decide

/-- The `call` at 694: `operator delete []` (`0x6014f0`). -/
def pc694 : List Byte := [0xe8, 0x35, 0xed, 0x1a, 0x00]
theorem pc694_0 : ∀ feat, Dec feat pc694 0 (FV7z.mk .call 64 [.rel 1764661] 5) := by dec_rfl
theorem wc_694 : pc694 <+: spp.drop 694 := by decide +kernel
theorem call_694 (feat : Features) : Dec feat spp 694 (FV7z.mk .call 64 [.rel 1764661] 5) :=
  Dec.shift (j := 694) (k := 0) (pc694_0 feat) wc_694 (Nat.zero_le _)
theorem tgt_694 : spp_at.add (694 + 5) + BitVec.ofNat 64 1764661 = 0x6014f0#64 := by decide

/-- The `ja` at 272 to the throw at `0x4017c2`. -/
def pja272 : List Byte := [0x0f, 0x87, 0xac, 0xf1, 0xfa, 0xff]
theorem pja272_0 : ∀ feat, Dec feat pja272 0 (FV7z.mk (.jcc 7) 64 [.rel 18446744073709220268] 6) := by dec_rfl
theorem wa_272 : pja272 <+: spp.drop 272 := by decide +kernel
theorem ja_272 (feat : Features) : Dec feat spp 272 (FV7z.mk (.jcc 7) 64 [.rel 18446744073709220268] 6) :=
  Dec.shift (j := 272) (k := 0) (pja272_0 feat) wa_272 (Nat.zero_le _)
theorem tja_272 : spp_at.add (272 + 6) + BitVec.ofNat 64 18446744073709220268 = (0x4017c2#64 : Addr).add 0 := by decide

/-- The `ja` at 458 to the throw at `0x4017c7`. -/
def pja458 : List Byte := [0x0f, 0x87, 0xf7, 0xf0, 0xfa, 0xff]
theorem pja458_0 : ∀ feat, Dec feat pja458 0 (FV7z.mk (.jcc 7) 64 [.rel 18446744073709220087] 6) := by dec_rfl
theorem wa_458 : pja458 <+: spp.drop 458 := by decide +kernel
theorem ja_458 (feat : Features) : Dec feat spp 458 (FV7z.mk (.jcc 7) 64 [.rel 18446744073709220087] 6) :=
  Dec.shift (j := 458) (k := 0) (pja458_0 feat) wa_458 (Nat.zero_le _)
theorem tja_458 : spp_at.add (458 + 6) + BitVec.ofNat 64 18446744073709220087 = (0x4017c7#64 : Addr).add 0 := by decide

/-- The `ret`. -/
def pret : List Byte := [0xc3]
theorem pret_0 : ∀ feat, Dec feat pret 0 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem wt_169 : pret <+: spp.drop 169 := by decide +kernel
theorem ret_169 (feat : Features) : Dec feat spp 169 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 169) (k := 0) (pret_0 feat) wt_169 (Nat.zero_le _)


/-! ## The frame -/

/-- The stack pointer after the six pushes and `sub rsp, 0x48`. -/
abbrev aR (S : Addr) : Addr := S - 8 - 8 - 8 - 8 - 8 - 8 - 72#64

theorem q1 (S : Addr) : aR S + 72#64 = S - 8 - 8 - 8 - 8 - 8 - 8 := BitVec.sub_add_cancel _ _
theorem q2 (S : Addr) : aR S + 72#64 + 8 = S - 8 - 8 - 8 - 8 - 8 := by rw [q1]; exact BitVec.sub_add_cancel _ _
theorem q3 (S : Addr) : aR S + 72#64 + 8 + 8 = S - 8 - 8 - 8 - 8 := by rw [q2]; exact r1 S
theorem q4 (S : Addr) : aR S + 72#64 + 8 + 8 + 8 = S - 8 - 8 - 8 := by rw [q2]; exact r2 S
theorem q5 (S : Addr) : aR S + 72#64 + 8 + 8 + 8 + 8 = S - 8 - 8 := by rw [q2]; exact r3 S
theorem q6 (S : Addr) : aR S + 72#64 + 8 + 8 + 8 + 8 + 8 = S - 8 := by rw [q2]; exact r4 S
theorem q7 (S : Addr) : aR S + 72#64 + 8 + 8 + 8 + 8 + 8 + 8 = S := by rw [q2]; exact r5 S

/-- The bytes after the six pushes (`r15`, `r14`, `r13`, `r12`, `rbp`, `rbx`). -/
abbrev P6 (V : Addr → Byte) (g : Gprs) : Addr → Byte :=
  Vst (Vst (Vst (Vst (Vst (Vst V (g.rsp - 8) (toBytesLE g.r15 8)) (g.rsp - 8 - 8) (toBytesLE g.r14 8))
    (g.rsp - 8 - 8 - 8) (toBytesLE g.r13 8)) (g.rsp - 8 - 8 - 8 - 8) (toBytesLE g.r12 8))
    (g.rsp - 8 - 8 - 8 - 8 - 8) (toBytesLE g.rbp 8)) (g.rsp - 8 - 8 - 8 - 8 - 8 - 8) (toBytesLE g.rbx 8)

/-- The bytes after the pushes and `path`'s store. -/
abbrev V0 (V : Addr → Byte) (g : Gprs) : Addr → Byte := Vst (P6 V g) (aR g.rsp + 8#64) (toBytesLE g.rdi 8)

/-- The bytes after the prologue: the stack guard (`cn`) stored. -/
abbrev V1 (V : Addr → Byte) (g : Gprs) (cn : BitVec 64) : Addr → Byte :=
  Vst (V0 V g) (aR g.rsp + 56#64) (toBytesLE cn 8)

/-- What a piece keeps: `rsp`, `rbp` (`pathParts`), `r15`. -/
abbrev Fr (g g' : Gprs) : Prop := g'.rsp = g.rsp ∧ g'.rbp = g.rbp ∧ g'.r15 = g.r15

/-- What a piece of `Add` (259–378) keeps: also `rbx` (`i`), `r12` (`len`), `r14`. -/
abbrev Fk (g g' : Gprs) : Prop :=
  g'.rsp = g.rsp ∧ g'.rbp = g.rbp ∧ g'.r15 = g.r15 ∧ g'.rbx = g.rbx ∧ g'.r12 = g.r12 ∧ g'.r14 = g.r14

/-! ## The pieces -/

section Pieces
variable {F : Footprint} {Wl : List Rgn} {I : (Addr → Byte) → Prop} {Ok : Addr → Nat → Prop}

/-- The prologue: the pushes, `rbp` = `pathParts`, `path` stored at `aR S + 8`, the stack guard (`cn`) at
`aR S + 56`, `eax` = the size `n32`: 0 to 114, else `rbx` = `8 (n32 - 1)` and to the loop's head 64. -/
theorem vc_0 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} {cn : BitVec 64} {n32 : BitVec 32}
    (hcn : rdq(V0 V g, fb + 40#64) = cn) (hn : rdd(V1 V g cn, g.rsi + 8#64) = n32)
    (hs1 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8) i)) (hs2 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8) i))
    (hs3 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8 - 8) i))
    (hs4 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8 - 8 - 8) i))
    (hs5 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8 - 8 - 8 - 8) i))
    (hs6 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8 - 8 - 8 - 8 - 8) i))
    (hcl : ∀ i < 8, Foot F.data (Addr.add (fb + 40#64) i))
    (hw8 : ∀ i < 8, Foot Wl (Addr.add (aR g.rsp + 8#64) i)) (hw56 : ∀ i < 8, Foot Wl (Addr.add (aR g.rsp + 56#64) i))
    (fn : ∀ i < 4, Foot F.data (Addr.add (g.rsi + 8#64) i))
    (h114 : n32 = 0 → ∀ g', g'.rsp = aR g.rsp → g'.rbp = g.rsi → g'.r15 = g.r15 → ∀ fl, Q 114 g' fl (V1 V g cn))
    (h64 : ¬n32 = 0 → ∀ g', g'.rsp = aR g.rsp → g'.rbp = g.rsi → g'.r15 = g.r15 → g'.rbx = rbx0 n32 →
      ∀ fl, Q 64 g' fl (V1 V g cn)) :
    W_0 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [aR, P6, V0, V1] at hcn hn hs1 hs2 hs3 hs4 hs5 hs6 hw8 hw56 fn h114 h64 ⊢
  wpx [W_0, W_49, o0, o1, Op.ldf, Op.shl64, hcn, hn, BitVec.and_self, beq_iff_eq, beq_eq_false_iff_ne, ne_eq,
    Bool.not_eq_true', Bool.not_eq_false', Bool.false_eq_true, Bool.true_eq_false, false_implies]
  all_goals repeat' (first
    | refine h114 ?_ _ ?_ ?_ ?_ _
    | refine h64 ?_ _ ?_ ?_ ?_ ?_ _
    | with_reducible rfl
    | exact rfl
    | assumption
    | with_reducible exact hs1
    | with_reducible exact hs2
    | with_reducible exact hs3
    | with_reducible exact hs4
    | with_reducible exact hs5
    | with_reducible exact hs6
    | with_reducible exact hcl
    | with_reducible exact hw8
    | with_reducible exact hw56
    | with_reducible exact fn
    | apply And.intro
    | intro _)

/-- The loop's head: `rax` = `_items` (`it`), `r12` = the item `p` (the 8 bytes at `it + rbx`); 0 to 104; else
`rdi` = its chars `q` (the 8 bytes at `p`), 0 to 91, else to the `call` at 86. -/
theorem vc_64 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} {it p q : BitVec 64}
    (hit : rdq(V, g.rbp) = it) (fa : ∀ i < 8, Foot F.data (Addr.add g.rbp i))
    (hp : rdq(V, it + g.rbx) = p) (fp : ∀ i < 8, Foot F.data (Addr.add (it + g.rbx) i))
    (hq : rdq(V, p) = q) (fq : ¬p = 0 → ∀ i < 8, Foot F.data (Addr.add p i))
    (h104 : p = 0 → ∀ g', Fr g g' → g'.rbx = g.rbx → ∀ fl, Q 104 g' fl V)
    (h91 : ¬p = 0 → q = 0 → ∀ g', Fr g g' → g'.rbx = g.rbx → g'.r12 = p → ∀ fl, Q 91 g' fl V)
    (h86 : ¬p = 0 → ¬q = 0 → ∀ g', Fr g g' → g'.rbx = g.rbx → g'.r12 = p → g'.rdi = q → ∀ fl, Q 86 g' fl V) :
    W_64 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hit fa hp fp hq fq h104 h91 h86 ⊢
  wpx [W_64, W_77, o2, o3, hit, hp, hq, BitVec.and_self, beq_iff_eq, beq_eq_false_iff_ne, ne_eq,
    Bool.not_eq_true', Bool.not_eq_false', Bool.false_eq_true, Bool.true_eq_false, false_implies]
  all_goals repeat' (first
    | refine h104 ?_ _ ?_ ?_ _
    | refine h91 ?_ ?_ _ ?_ ?_ ?_ _
    | refine h86 ?_ ?_ _ ?_ ?_ ?_ ?_ _
    | with_reducible rfl
    | assumption
    | with_reducible exact fa
    | with_reducible exact fp
    | (with_reducible exact fq (by assumption))
    | apply And.intro
    | intro _)

/-- `esi` = 16, `rdi` = the item: to the `call` at 99. -/
theorem vc_91 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (h : ∀ g', Fr g g' → g'.rbx = g.rbx → g'.rdi = g.r12 → g'.rsi = 16#64 → ∀ fl, Q 99 g' fl V) :
    W_91 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h ⊢
  wpx [W_91, o4, BitVec.reduceSetWidth]
  all_goals repeat' (first
    | refine h _ ?_ ?_ ?_ ?_ _
    | with_reducible rfl
    | apply And.intro
    | intro _)

/-- `rbx` -= 8: `-8` (the last step) to 114, else back to 64. -/
theorem vc_104 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (h114 : g.rbx - 8#64 = 18446744073709551608#64 → ∀ g', Fr g g' → ∀ fl, Q 114 g' fl V)
    (h64 : ¬g.rbx - 8#64 = 18446744073709551608#64 → ∀ g', Fr g g' → g'.rbx = g.rbx - 8#64 →
      ∀ fl, Q 64 g' fl V) :
    W_104 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h114 h64 ⊢
  wpx [W_104, o5, Bool.not_eq_true', Bool.not_eq_false', decide_eq_true_eq, decide_eq_false_iff_not]
  all_goals repeat' (first
    | refine h114 ?_ _ ?_ _
    | refine h64 ?_ _ ?_ ?_ _
    | with_reducible rfl
    | assumption
    | apply And.intro
    | intro _)

/-- `rbx` = `path` (from `aR S + 8`), the size set to 0, `r12d` = `len` (the 4 bytes at `path + 8`): 0 to 135; else
`r15` = `rdi` = `&name`, to the `call` at 184. -/
theorem vc_114 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (fs8 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8#64) i))
    (w8 : ∀ i < 4, Foot Wl (Addr.add (g.rbp + 8#64) i)) (o8 : Ok (g.rbp + 8#64) 4) (hI : I V)
    (hcl : ∀ (W : Addr → Byte) (a : Addr) (n : Nat) (bs : List Byte), bs.length = n → Ok a n → I W →
      I (Vst W a bs))
    (fl8 : ∀ i < 4, Foot F.data (Addr.add (rdq(V, g.rsp + 8#64) + 8#64) i))
    (h135 : ∀ g' V', I V' → rdd(V', rdq(V, g.rsp + 8#64) + 8#64) = 0 → Fr g g' → ∀ fl, Q 135 g' fl V')
    (h184 : ∀ g' V', I V' → ¬rdd(V', rdq(V, g.rsp + 8#64) + 8#64) = 0 → g'.rsp = g.rsp → g'.rbp = g.rbp →
      g'.rbx = rdq(V, g.rsp + 8#64) → g'.r12 = BitVec.setWidth 64 rdd(V', rdq(V, g.rsp + 8#64) + 8#64) →
      g'.r15 = g.rsp + 32#64 → g'.rdi = g.rsp + 32#64 → ∀ fl, Q 184 g' fl V') :
    W_114 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at fs8 w8 o8 fl8 h135 h184 ⊢
  wpx [W_114, W_176, o6, o9, BitVec.and_self, beq_iff_eq, beq_eq_false_iff_ne, ne_eq,
    Bool.not_eq_true', Bool.not_eq_false', Bool.false_eq_true, Bool.true_eq_false, false_implies]
  all_goals repeat' (first
    | refine h135 _ _ ?_ ?_ ?_ _
    | refine h184 _ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ _
    | with_reducible rfl
    | assumption
    | with_reducible exact hI
    | refine hcl _ _ _ _ (toBytesLE_length _ _) ?_ ?_
    | refine hcl _ _ 4 _ rfl ?_ ?_
    | with_reducible exact fs8
    | with_reducible exact w8
    | with_reducible exact o8
    | with_reducible exact fl8
    | apply And.intro
    | intro _)

/-- The stack guard checked (as at `fs:0x28`: `jne` not taken), `add rsp, 0x48`, the six pops, to the `ret`. -/
theorem vc_135 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
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
      g'.r15 = rdq(V, g.rsp + 72#64 + 8 + 8 + 8 + 8 + 8) → ∀ fl, Q 169 g' fl V) :
    W_135 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hc f56 f1 f2 f3 f4 f5 f6 h ⊢
  have z0 : ((0#64 : BitVec 64) == 0) = true := by decide
  wpx [W_135, W_155, o7, o8, Op.xormf, hc, BitVec.xor_self, z0, decide_true, Bool.not_true, Bool.false_eq_true,
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

/-- `rax` = `path._chars`, `ecx` = `ebx` = 0: `jmp` to 221. -/
theorem vc_189 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (fb0 : ∀ i < 8, Foot F.data (Addr.add g.rbx i))
    (h : ∀ g', Fr g g' → g'.rax = rdq(V, g.rbx) → g'.rbx = 0#64 → g'.r12 = g.r12 → ∀ fl, Q 221 g' fl V) :
    W_189 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at fb0 h ⊢
  wpx [W_189, o10, BitVec.xor_self, BitVec.reduceSetWidth]
  all_goals repeat' (first
    | refine h _ ?_ ?_ ?_ ?_ _
    | with_reducible rfl
    | exact rfl
    | with_reducible exact fb0
    | apply And.intro
    | intro _)

/-- The scan's step with `i + 1` below `len` (`r12d`): a char not `'/'` back to 221 with `i + 1`; a `'/'`
(`r14` = `i`, `rdi` = `&name`) to the `call` at 254. -/
theorem vc_221c {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (fch : ∀ i < 4, Foot F.data (Addr.add (g.rax + g.rbx * 4#64) i))
    (hc : ¬((BitVec.setWidth 32 g.r12).toNat < (BitVec.setWidth 32 (g.rbx + 1#64)).toNat ∨
      BitVec.setWidth 32 g.r12 = BitVec.setWidth 32 (g.rbx + 1#64)))
    (h221 : ∀ g', Fr g g' → g'.rax = g.rax → g'.rbx = g.rbx + 1#64 → g'.r12 = g.r12 → ∀ fl, Q 221 g' fl V)
    (h254 : ∀ g', Fr g g' → g'.rax = g.rax → g'.rbx = g.rbx → g'.r12 = g.r12 →
      g'.r14 = BitVec.setWidth 64 (BitVec.setWidth 32 g.rbx) → g'.rdi = g.r15 → ∀ fl, Q 254 g' fl V) :
    W_221 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at fch hc h221 h254 ⊢
  wpx [W_221, W_208, W_247, o12, o11, o13, Op.cmpmi, BitVec.and_self, beq_iff_eq, beq_eq_false_iff_ne, ne_eq,
    Bool.not_eq_true', Bool.not_eq_false', Bool.or_eq_true, Bool.or_eq_false_iff, decide_eq_true_eq,
    decide_eq_false_iff_not]
  all_goals repeat' (first
    | exact trivial
    | (intro hh; exact absurd hh hc)
    | refine h221 _ ?_ ?_ ?_ ?_ _
    | refine h254 _ ?_ ?_ ?_ ?_ ?_ ?_ _
    | with_reducible rfl
    | with_reducible exact fch
    | apply And.intro
    | intro _)

/-- The scan's step with `i + 1` not below `len`: a char not `'/'` to 432; a `'/'` to the `call` at 254. -/
theorem vc_221x {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (fch : ∀ i < 4, Foot F.data (Addr.add (g.rax + g.rbx * 4#64) i))
    (hc : (BitVec.setWidth 32 g.r12).toNat < (BitVec.setWidth 32 (g.rbx + 1#64)).toNat ∨
      BitVec.setWidth 32 g.r12 = BitVec.setWidth 32 (g.rbx + 1#64))
    (h432 : ∀ g', Fr g g' → ∀ fl, Q 432 g' fl V)
    (h254 : ∀ g', Fr g g' → g'.rax = g.rax → g'.rbx = g.rbx → g'.r12 = g.r12 →
      g'.r14 = BitVec.setWidth 64 (BitVec.setWidth 32 g.rbx) → g'.rdi = g.r15 → ∀ fl, Q 254 g' fl V) :
    W_221 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at fch hc h432 h254 ⊢
  wpx [W_221, W_208, W_247, o12, o11, o13, Op.cmpmi, BitVec.and_self, beq_iff_eq, beq_eq_false_iff_ne, ne_eq,
    Bool.not_eq_true', Bool.not_eq_false', Bool.or_eq_true, Bool.or_eq_false_iff, decide_eq_true_eq,
    decide_eq_false_iff_not]
  all_goals repeat' (first
    | exact trivial
    | (intro hh; exact absurd hc (not_or.2 hh))
    | refine h432 _ ?_ _
    | refine h254 _ ?_ ?_ ?_ ?_ ?_ ?_ _
    | with_reducible rfl
    | with_reducible exact fch
    | apply And.intro
    | intro _)

/-- `Add`'s check (`eax` = `_capacity`, compared with `_size`): not full to 352; else `cmp eax, 0x7ffffffe`, to the
`ja` at 272. -/
theorem vc_259 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (f12 : ∀ i < 4, Foot F.data (Addr.add (g.rbp + 12#64) i)) (f8 : ∀ i < 4, Foot F.data (Addr.add (g.rbp + 8#64) i))
    (h352 : ∀ g', Fk g g' → ∀ fl, Q 352 g' fl V) (h272 : ∀ g', Fk g g' → ∀ fl, Q 272 g' fl V) :
    W_259 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at f12 f8 h352 h272 ⊢
  wpx [W_259, W_267, o14, o15, Op.cmpmr]
  all_goals repeat' (first
    | refine h352 _ ?_ _
    | refine h272 _ ?_ _
    | with_reducible rfl
    | with_reducible exact f12
    | with_reducible exact f8
    | apply And.intro
    | intro _)

/-- The new capacity (`cmova`) stored at `rsp + 16`, `rdi` = 8 times it: to `operator new []` (309). -/
theorem vc_278 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (ws16 : ∀ i < 4, Foot Wl (Addr.add (g.rsp + 16#64) i)) (os16 : Ok (g.rsp + 16#64) 4) (hI : I V)
    (hcl : ∀ (W : Addr → Byte) (a : Addr) (n : Nat) (bs : List Byte), bs.length = n → Ok a n → I W →
      I (Vst W a bs))
    (h : ∀ g' V', I V' → Fk g g' → ∀ fl, Q 309 g' fl V') :
    W_278 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at ws16 os16 h ⊢
  wpx [W_278, o16, Op.shl64]
  all_goals repeat' (first
    | refine h _ _ ?_ ?_ _
    | with_reducible rfl
    | with_reducible exact hI
    | refine hcl _ _ _ _ (toBytesLE_length _ _) ?_ ?_
    | with_reducible exact ws16
    | with_reducible exact os16
    | apply And.intro
    | intro _)

/-- `rcx` = the new array, `_size`, the old `_items` (`r8`): `_size` not 0, the old `_items` kept at `rsp + 24`, to
`memcpy` (627); else the old `_items` not null to `delete []` (640), or to 341. -/
theorem vc_314 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (f8 : ∀ i < 4, Foot F.data (Addr.add (g.rbp + 8#64) i)) (f0 : ∀ i < 8, Foot F.data (Addr.add g.rbp i))
    (ws24 : ∀ i < 8, Foot Wl (Addr.add (g.rsp + 24#64) i)) (os24 : Ok (g.rsp + 24#64) 8) (hI : I V)
    (hcl : ∀ (W : Addr → Byte) (a : Addr) (n : Nat) (bs : List Byte), bs.length = n → Ok a n → I W →
      I (Vst W a bs))
    (h627 : ∀ g' V', I V' → Fk g g' → ∀ fl, Q 627 g' fl V')
    (h640 : ∀ g' V', I V' → Fk g g' → ∀ fl, Q 640 g' fl V')
    (h341 : ∀ g' V', I V' → Fk g g' → ∀ fl, Q 341 g' fl V') :
    W_314 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at f8 f0 ws24 os24 h627 h640 h341 ⊢
  wpx [W_314, W_608, W_332, o17, o30, o18]
  all_goals repeat' (first
    | refine h627 _ _ ?_ ?_ _
    | refine h640 _ _ ?_ ?_ _
    | refine h341 _ _ ?_ ?_ _
    | with_reducible rfl
    | with_reducible exact hI
    | refine hcl _ _ _ _ (toBytesLE_length _ _) ?_ ?_
    | with_reducible exact f8
    | with_reducible exact f0
    | with_reducible exact ws24
    | with_reducible exact os24
    | apply And.intro
    | intro _)

/-- `_items` = the new array, `_capacity` = the new capacity (from `rsp + 16`): to 352. -/
theorem vc_341 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (f16 : ∀ i < 4, Foot F.data (Addr.add (g.rsp + 16#64) i))
    (w0 : ∀ i < 8, Foot Wl (Addr.add g.rbp i)) (w12 : ∀ i < 4, Foot Wl (Addr.add (g.rbp + 12#64) i))
    (o0 : Ok g.rbp 8) (o12 : Ok (g.rbp + 12#64) 4) (hI : I V)
    (hcl : ∀ (W : Addr → Byte) (a : Addr) (n : Nat) (bs : List Byte), bs.length = n → Ok a n → I W →
      I (Vst W a bs))
    (h : ∀ g' V', I V' → Fk g g' → ∀ fl, Q 352 g' fl V') :
    W_341 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at f16 w0 w12 o0 o12 h ⊢
  wpx [W_341, o19]
  all_goals repeat' (first
    | refine h _ _ ?_ ?_ _
    | with_reducible rfl
    | with_reducible exact hI
    | refine hcl _ _ _ _ (toBytesLE_length _ _) ?_ ?_
    | with_reducible exact f16
    | with_reducible exact w0
    | with_reducible exact w12
    | with_reducible exact o0
    | with_reducible exact o12
    | apply And.intro
    | intro _)

/-- `edi` = 16: to `operator new` (357). -/
theorem vc_352 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (h : ∀ g', Fk g g' → ∀ fl, Q 357 g' fl V) : W_352 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h ⊢
  wpx [W_352, o20]
  all_goals repeat' (first
    | refine h _ ?_ _
    | with_reducible rfl
    | apply And.intro
    | intro _)

/-- The new item kept at `rsp + 16`, `rdi` = it, `rsi` = `&name`: to its `UString (name)` (373). -/
theorem vc_362 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (ws16 : ∀ i < 8, Foot Wl (Addr.add (g.rsp + 16#64) i)) (os16 : Ok (g.rsp + 16#64) 8) (hI : I V)
    (hcl : ∀ (W : Addr → Byte) (a : Addr) (n : Nat) (bs : List Byte), bs.length = n → Ok a n → I W →
      I (Vst W a bs))
    (h : ∀ g' V', I V' → Fk g g' → ∀ fl, Q 373 g' fl V') :
    W_362 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at ws16 os16 h ⊢
  wpx [W_362, o21]
  all_goals repeat' (first
    | refine h _ _ ?_ ?_ _
    | with_reducible rfl
    | with_reducible exact hI
    | refine hcl _ _ _ _ (toBytesLE_length _ _) ?_ ?_
    | with_reducible exact ws16
    | with_reducible exact os16
    | apply And.intro
    | intro _)

/-- `_size + 1`, the slot `_items[_size]` = the new item (from `rsp + 16`), `rbx` = `i + 1`, `rax` = `path._chars`
again, `edx` = `start` = `r14d + 1`: with `start` below `len` back to 221. -/
theorem vc_378c {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (f8 : ∀ i < 4, Foot F.data (Addr.add (g.rbp + 8#64) i)) (f0 : ∀ i < 8, Foot F.data (Addr.add g.rbp i))
    (w8 : ∀ i < 4, Foot Wl (Addr.add (g.rbp + 8#64) i)) (o8 : Ok (g.rbp + 8#64) 4)
    (fs16 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 16#64) i))
    (wsl : ∀ i < 8, Foot Wl (Addr.add (rdq(V, g.rbp) + BitVec.setWidth 64 rdd(V, g.rbp + 8#64) * 8#64) i))
    (osl : Ok (rdq(V, g.rbp) + BitVec.setWidth 64 rdd(V, g.rbp + 8#64) * 8#64) 8)
    (fs8 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8#64) i))
    (fpc : ∀ W, I W → ∀ i < 8, Foot F.data (Addr.add rdq(W, g.rsp + 8#64) i)) (hI : I V)
    (hcl : ∀ (W : Addr → Byte) (a : Addr) (n : Nat) (bs : List Byte), bs.length = n → Ok a n → I W →
      I (Vst W a bs))
    (hc : ¬((BitVec.setWidth 32 g.r12).toNat < (BitVec.setWidth 32 (g.r14 + 1#64)).toNat ∨
      BitVec.setWidth 32 g.r12 = BitVec.setWidth 32 (g.r14 + 1#64)))
    (h : ∀ g' V', I V' → Fr g g' → g'.rbx = g.rbx + 1#64 → g'.r12 = g.r12 →
      g'.rax = rdq(V', rdq(V', g.rsp + 8#64)) → ∀ fl, Q 221 g' fl V') :
    W_378 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at f8 f0 w8 o8 fs16 wsl osl fs8 fpc hc h ⊢
  wpx [W_378, o22, Bool.not_eq_true', Bool.not_eq_false', Bool.or_eq_true, Bool.or_eq_false_iff,
    decide_eq_true_eq, decide_eq_false_iff_not]
  all_goals repeat' (first
    | exact trivial
    | (intro hh; exact absurd hh hc)
    | refine h _ _ ?_ ?_ ?_ ?_ ?_ _
    | with_reducible rfl
    | with_reducible exact hI
    | refine hcl _ _ _ _ (toBytesLE_length _ _) ?_ ?_
    | with_reducible exact f8
    | with_reducible exact f0
    | with_reducible exact w8
    | with_reducible exact o8
    | with_reducible exact fs16
    | with_reducible exact wsl
    | with_reducible exact osl
    | with_reducible exact fs8
    | refine fpc _ ?_
    | apply And.intro
    | intro _)

/-- As `vc_378c`, with `start` not below `len`: to 432. -/
theorem vc_378x {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (f8 : ∀ i < 4, Foot F.data (Addr.add (g.rbp + 8#64) i)) (f0 : ∀ i < 8, Foot F.data (Addr.add g.rbp i))
    (w8 : ∀ i < 4, Foot Wl (Addr.add (g.rbp + 8#64) i)) (o8 : Ok (g.rbp + 8#64) 4)
    (fs16 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 16#64) i))
    (wsl : ∀ i < 8, Foot Wl (Addr.add (rdq(V, g.rbp) + BitVec.setWidth 64 rdd(V, g.rbp + 8#64) * 8#64) i))
    (osl : Ok (rdq(V, g.rbp) + BitVec.setWidth 64 rdd(V, g.rbp + 8#64) * 8#64) 8)
    (fs8 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8#64) i))
    (fpc : ∀ W, I W → ∀ i < 8, Foot F.data (Addr.add rdq(W, g.rsp + 8#64) i)) (hI : I V)
    (hcl : ∀ (W : Addr → Byte) (a : Addr) (n : Nat) (bs : List Byte), bs.length = n → Ok a n → I W →
      I (Vst W a bs))
    (hc : (BitVec.setWidth 32 g.r12).toNat < (BitVec.setWidth 32 (g.r14 + 1#64)).toNat ∨
      BitVec.setWidth 32 g.r12 = BitVec.setWidth 32 (g.r14 + 1#64))
    (h : ∀ g' V', I V' → Fr g g' → ∀ fl, Q 432 g' fl V') :
    W_378 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at f8 f0 w8 o8 fs16 wsl osl fs8 fpc hc h ⊢
  wpx [W_378, o22, Bool.not_eq_true', Bool.not_eq_false', Bool.or_eq_true, Bool.or_eq_false_iff,
    decide_eq_true_eq, decide_eq_false_iff_not]
  all_goals repeat' (first
    | exact trivial
    | (intro hh; exact absurd hc (not_or.2 hh))
    | refine h _ _ ?_ ?_ _
    | with_reducible rfl
    | with_reducible exact hI
    | refine hcl _ _ _ _ (toBytesLE_length _ _) ?_ ?_
    | with_reducible exact f8
    | with_reducible exact f0
    | with_reducible exact w8
    | with_reducible exact o8
    | with_reducible exact fs16
    | with_reducible exact wsl
    | with_reducible exact osl
    | with_reducible exact fs8
    | refine fpc _ ?_
    | apply And.intro
    | intro _)

/-- `edx` = `len - start`, `rdi` = `&name`: to the `call` at 440. -/
theorem vc_432 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (h : ∀ g', Fr g g' → g'.rdi = g.r15 → ∀ fl, Q 440 g' fl V) : W_432 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h ⊢
  wpx [W_432, o23]
  all_goals repeat' (first
    | refine h _ ?_ ?_ _
    | with_reducible rfl
    | apply And.intro
    | intro _)

/-- The last part's `Add` check: not full to 533; else to the `ja` at 458. -/
theorem vc_445 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (f12 : ∀ i < 4, Foot F.data (Addr.add (g.rbp + 12#64) i)) (f8 : ∀ i < 4, Foot F.data (Addr.add (g.rbp + 8#64) i))
    (h533 : ∀ g', Fr g g' → ∀ fl, Q 533 g' fl V) (h458 : ∀ g', Fr g g' → ∀ fl, Q 458 g' fl V) :
    W_445 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at f12 f8 h533 h458 ⊢
  wpx [W_445, W_453, o14, o15, Op.cmpmr]
  all_goals repeat' (first
    | refine h533 _ ?_ _
    | refine h458 _ ?_ _
    | with_reducible rfl
    | with_reducible exact f12
    | with_reducible exact f8
    | apply And.intro
    | intro _)

/-- The new capacity in `rbx`, `rdi` = 8 times it: to `operator new []` (494). -/
theorem vc_464 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (h : ∀ g', Fr g g' → ∀ fl, Q 494 g' fl V) : W_464 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h ⊢
  wpx [W_464, o24, Op.shl64]
  all_goals repeat' (first
    | refine h _ ?_ _
    | with_reducible rfl
    | apply And.intro
    | intro _)

/-- `r12` = the new array, `_size`, the old `_items` (`r13`): to `memcpy` (686), `delete []` (691), or 526. -/
theorem vc_499 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (f8 : ∀ i < 4, Foot F.data (Addr.add (g.rbp + 8#64) i)) (f0 : ∀ i < 8, Foot F.data (Addr.add g.rbp i))
    (h686 : ∀ g', Fr g g' → ∀ fl, Q 686 g' fl V) (h691 : ∀ g', Fr g g' → ∀ fl, Q 691 g' fl V)
    (h526 : ∀ g', Fr g g' → ∀ fl, Q 526 g' fl V) :
    W_499 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at f8 f0 h686 h691 h526 ⊢
  wpx [W_499, W_672, W_517, o25, o34, o26]
  all_goals repeat' (first
    | refine h686 _ ?_ _
    | refine h691 _ ?_ _
    | refine h526 _ ?_ _
    | with_reducible rfl
    | with_reducible exact f8
    | with_reducible exact f0
    | apply And.intro
    | intro _)

/-- `_items` = the new array, `_capacity` = the new capacity: to 533. -/
theorem vc_526 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (w0 : ∀ i < 8, Foot Wl (Addr.add g.rbp i)) (w12 : ∀ i < 4, Foot Wl (Addr.add (g.rbp + 12#64) i))
    (o0 : Ok g.rbp 8) (o12 : Ok (g.rbp + 12#64) 4) (hI : I V)
    (hcl : ∀ (W : Addr → Byte) (a : Addr) (n : Nat) (bs : List Byte), bs.length = n → Ok a n → I W →
      I (Vst W a bs))
    (h : ∀ g' V', I V' → Fr g g' → ∀ fl, Q 533 g' fl V') :
    W_526 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at w0 w12 o0 o12 h ⊢
  wpx [W_526, o27]
  all_goals repeat' (first
    | refine h _ _ ?_ ?_ _
    | with_reducible rfl
    | with_reducible exact hI
    | refine hcl _ _ _ _ (toBytesLE_length _ _) ?_ ?_
    | with_reducible exact w0
    | with_reducible exact w12
    | with_reducible exact o0
    | with_reducible exact o12
    | apply And.intro
    | intro _)

/-- `edi` = 16: to `operator new` (538). -/
theorem vc_533 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (h : ∀ g', Fr g g' → ∀ fl, Q 538 g' fl V) : W_533 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h ⊢
  wpx [W_533, o20]
  all_goals repeat' (first
    | refine h _ ?_ _
    | with_reducible rfl
    | apply And.intro
    | intro _)

/-- `rdi` = `r12` = the new item, `rsi` = `&name`: to its `UString (name)` (552). -/
theorem vc_543 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (h : ∀ g', Fr g g' → ∀ fl, Q 552 g' fl V) : W_543 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h ⊢
  wpx [W_543, o28]
  all_goals repeat' (first
    | refine h _ ?_ _
    | with_reducible rfl
    | apply And.intro
    | intro _)

/-- `_size + 1`, the slot = the new item, `rdi` = `name._chars`: 0 to 135, else to `delete []` (588). -/
theorem vc_557 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (f8 : ∀ i < 4, Foot F.data (Addr.add (g.rbp + 8#64) i)) (f0 : ∀ i < 8, Foot F.data (Addr.add g.rbp i))
    (w8 : ∀ i < 4, Foot Wl (Addr.add (g.rbp + 8#64) i)) (o8 : Ok (g.rbp + 8#64) 4)
    (wsl : ∀ i < 8, Foot Wl (Addr.add (rdq(V, g.rbp) + BitVec.setWidth 64 rdd(V, g.rbp + 8#64) * 8#64) i))
    (osl : Ok (rdq(V, g.rbp) + BitVec.setWidth 64 rdd(V, g.rbp + 8#64) * 8#64) 8)
    (fs32 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 32#64) i)) (hI : I V)
    (hcl : ∀ (W : Addr → Byte) (a : Addr) (n : Nat) (bs : List Byte), bs.length = n → Ok a n → I W →
      I (Vst W a bs))
    (h135 : ∀ g' V', I V' → Fr g g' → ∀ fl, Q 135 g' fl V')
    (h588 : ∀ g' V', I V' → Fr g g' → ∀ fl, Q 588 g' fl V') :
    W_557 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at f8 f0 w8 o8 wsl osl fs32 h135 h588 ⊢
  wpx [W_557, o29]
  all_goals repeat' (first
    | refine h135 _ _ ?_ ?_ _
    | refine h588 _ _ ?_ ?_ _
    | with_reducible rfl
    | with_reducible exact hI
    | refine hcl _ _ _ _ (toBytesLE_length _ _) ?_ ?_
    | with_reducible exact f8
    | with_reducible exact f0
    | with_reducible exact w8
    | with_reducible exact o8
    | with_reducible exact wsl
    | with_reducible exact osl
    | with_reducible exact fs32
    | apply And.intro
    | intro _)

/-- `jmp` to 135. -/
theorem vc_593 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} (h : ∀ fl, Q 135 g fl V) :
    W_593 fb F Wl Q g f V := h _

/-- Back from `memcpy`: `r8` = the old `_items` (from `rsp + 24`), `rcx` = the new array: to 640. -/
theorem vc_632 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (fs24 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 24#64) i))
    (h : ∀ g', Fk g g' → ∀ fl, Q 640 g' fl V) : W_632 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at fs24 h ⊢
  wpx [W_632, o31]
  all_goals repeat' (first
    | refine h _ ?_ _
    | with_reducible rfl
    | with_reducible exact fs24
    | apply And.intro
    | intro _)

/-- `rdi` = the old `_items`, the new array kept at `rsp + 24`: to `delete []` (648). -/
theorem vc_640 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (ws24 : ∀ i < 8, Foot Wl (Addr.add (g.rsp + 24#64) i)) (os24 : Ok (g.rsp + 24#64) 8) (hI : I V)
    (hcl : ∀ (W : Addr → Byte) (a : Addr) (n : Nat) (bs : List Byte), bs.length = n → Ok a n → I W →
      I (Vst W a bs))
    (h : ∀ g' V', I V' → Fk g g' → ∀ fl, Q 648 g' fl V') :
    W_640 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at ws24 os24 h ⊢
  wpx [W_640, o32]
  all_goals repeat' (first
    | refine h _ _ ?_ ?_ _
    | with_reducible rfl
    | with_reducible exact hI
    | refine hcl _ _ _ _ (toBytesLE_length _ _) ?_ ?_
    | with_reducible exact ws24
    | with_reducible exact os24
    | apply And.intro
    | intro _)

/-- Back from `delete []`: `rcx` = the new array (from `rsp + 24`), `jmp` to 341. -/
theorem vc_653 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (fs24 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 24#64) i))
    (h : ∀ g', Fk g g' → ∀ fl, Q 341 g' fl V) : W_653 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at fs24 h ⊢
  wpx [W_653, o33]
  all_goals repeat' (first
    | refine h _ ?_ _
    | with_reducible rfl
    | with_reducible exact fs24
    | apply And.intro
    | intro _)

/-- `rdi` = the old `_items`: to `delete []` (694). -/
theorem vc_691 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (h : ∀ g', Fr g g' → ∀ fl, Q 694 g' fl V) : W_691 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h ⊢
  wpx [W_691, o35]
  all_goals repeat' (first
    | refine h _ ?_ _
    | with_reducible rfl
    | apply And.intro
    | intro _)

/-- `jmp` to 526. -/
theorem vc_699 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} (h : ∀ fl, Q 526 g fl V) :
    W_699 fb F Wl Q g f V := h _

end Pieces

end FV7z.Spp
