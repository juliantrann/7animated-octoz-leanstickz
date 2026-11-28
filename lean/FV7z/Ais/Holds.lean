import FV7z.Ais.Cuts
import FV7z.Api.Holds
/-!
# `NWildcard::CCensorNode::AddItemSimple` (PLAN.md §M, M1): the run through the callees

7-Zip 26.06's `NWildcard::CCensorNode::AddItemSimple (include, item)` (`CPP/Common/Wildcard.cpp`; `objdump -d`) at
`0x452bc0` in `7zzs`: `this` = `rdi`, `include` = `sil`, `item` = `rdx` (`r12`). The vector `vb` (`rbx`) is
`IncludeItems` (`this + 0x28`) or `ExcludeItems` (`+ 0x38`), by `cmove`: a `CObjectVector<CItem>` (`_items` at `+ 0`,
`_size` at `+ 8`, `_capacity` at `+ 0xc`). `S` the stack pointer and `g0` the registers at the entry: six pushes and
`sub rsp, 0x18` (`aR S`, as in `FV7z/Api/Holds.lean`, whose frame lemmas are reused). When `_size` = `_capacity`
(0..44), above 0x7ffffffe the `ja` at 49 to the throw at `0x40180a` (`kt`); else (55) the new capacity, `operator new
[]` (86, `0x6029b0`), (91) `memcpy` of the old items (338, `0x401070`; the old array in `r14`) when `_size` is not 0,
`delete []` (346, `0x6014f0`) when the old array is not null, (117) `_items` and `_capacity` stored. At 123 `operator
new (0x18)` (128, `0x602970`), (133) the new `CItem` `p` (`rbp`) cleared; `item.PathParts._size` (`nn`) not 0:
`operator new []` (215) and (220) `p.PathParts` set up, the count `8 nn` at `rsp + 8`; the loop (256..316): `operator
new (0x10)` (269), the `UString` copy (283, `0x44d5d0`) of `item.PathParts[k]`, appended to `p.PathParts`; (161) the
flags word, `p` appended to `vb`, the epilogue, `ret` (199). Not covered: the landing pads (356..).

The callees are continuations (`KC`, as in Api), the bytes tracked by an invariant `I` the caller chooses, kept by a
store of `n` bytes at `a` when `Ok a n` (`hcl`) and by the store of the stack slot `rsp + 8` (`hcs`); the stores
`Ok` allows leave that slot (`hfr`). What `operator new (0x18)` gives back (`Ob`): the fields of `p` in `Ok`. The
loop is by induction on what is left (`loop`, one round `step`), with the invariant `I` and the count in the slot;
`item.PathParts` (`pp`, `nn`) is as `I` says (`hpp`), its first `nn` slots readable (`fpp`).

- `Fm`, `Fr`, `Lf`, `Vk`, `Ob`, `KC`, `Ev`: the frame, what a piece keeps, the loop's frame, the vector's and the new
  item's fields, the callees, the hypotheses of the runs; `callK`: a `call` and the callee's return.
- `vc_*`: the pieces; `tail161`, `step`, `loop`, `from220`, `from133`, `from123`, `from117`, `from351`, `from343`,
  `from91`, `from55`: the runs from the cut points.
- `ais_ok`: from the entry to the return address (or the throw).
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
open FV7z.Api (aR P6 q1 q2 q3 q4 q5 q6 q7 Stk KS)
namespace FV7z.Ais
set_option linter.unusedVariables false

/-! ## The instructions outside the blocks -/

/-- The `ja` to the throw. -/
def pja : List Byte := [0x0f, 0x87, 0x13, 0xec, 0xfa, 0xff]
theorem pja_0 : ∀ feat, Dec feat pja 0 (FV7z.mk (.jcc 7) 64 [.rel 18446744073709218835] 6) := by dec_rfl
theorem wa_49 : pja <+: ais.drop 49 := by decide +kernel
theorem ja_49 (feat : Features) : Dec feat ais 49 (FV7z.mk (.jcc 7) 64 [.rel 18446744073709218835] 6) :=
  Dec.shift (j := 49) (k := 0) (pja_0 feat) wa_49 (Nat.zero_le _)

/-- The `call` of `operator new []` (86). -/
def pc86 : List Byte := [0xe8, 0x95, 0xfd, 0x1a, 0x00]
theorem pc86_0 : ∀ feat, Dec feat pc86 0 (FV7z.mk .call 64 [.rel 1768853] 5) := by dec_rfl
theorem wc_86 : pc86 <+: ais.drop 86 := by decide +kernel
theorem call_86 (feat : Features) : Dec feat ais 86 (FV7z.mk .call 64 [.rel 1768853] 5) :=
  Dec.shift (j := 86) (k := 0) (pc86_0 feat) wc_86 (Nat.zero_le _)
theorem tgt_86 : ais_at.add (86 + 5) + BitVec.ofNat 64 1768853 = 0x6029b0#64 := by decide

/-- The `call` of `operator new` (128). -/
def pc128 : List Byte := [0xe8, 0x2b, 0xfd, 0x1a, 0x00]
theorem pc128_0 : ∀ feat, Dec feat pc128 0 (FV7z.mk .call 64 [.rel 1768747] 5) := by dec_rfl
theorem wc_128 : pc128 <+: ais.drop 128 := by decide +kernel
theorem call_128 (feat : Features) : Dec feat ais 128 (FV7z.mk .call 64 [.rel 1768747] 5) :=
  Dec.shift (j := 128) (k := 0) (pc128_0 feat) wc_128 (Nat.zero_le _)
theorem tgt_128 : ais_at.add (128 + 5) + BitVec.ofNat 64 1768747 = 0x602970#64 := by decide

/-- The `call` of `operator new []` (215). -/
def pc215 : List Byte := [0xe8, 0x14, 0xfd, 0x1a, 0x00]
theorem pc215_0 : ∀ feat, Dec feat pc215 0 (FV7z.mk .call 64 [.rel 1768724] 5) := by dec_rfl
theorem wc_215 : pc215 <+: ais.drop 215 := by decide +kernel
theorem call_215 (feat : Features) : Dec feat ais 215 (FV7z.mk .call 64 [.rel 1768724] 5) :=
  Dec.shift (j := 215) (k := 0) (pc215_0 feat) wc_215 (Nat.zero_le _)
theorem tgt_215 : ais_at.add (215 + 5) + BitVec.ofNat 64 1768724 = 0x6029b0#64 := by decide

/-- The `call` of `operator new` (269). -/
def pc269 : List Byte := [0xe8, 0x9e, 0xfc, 0x1a, 0x00]
theorem pc269_0 : ∀ feat, Dec feat pc269 0 (FV7z.mk .call 64 [.rel 1768606] 5) := by dec_rfl
theorem wc_269 : pc269 <+: ais.drop 269 := by decide +kernel
theorem call_269 (feat : Features) : Dec feat ais 269 (FV7z.mk .call 64 [.rel 1768606] 5) :=
  Dec.shift (j := 269) (k := 0) (pc269_0 feat) wc_269 (Nat.zero_le _)
theorem tgt_269 : ais_at.add (269 + 5) + BitVec.ofNat 64 1768606 = 0x602970#64 := by decide

/-- The `call` of the `UString` copy (283). -/
def pc283 : List Byte := [0xe8, 0xf0, 0xa8, 0xff, 0xff]
theorem pc283_0 : ∀ feat, Dec feat pc283 0 (FV7z.mk .call 64 [.rel 18446744073709529328] 5) := by dec_rfl
theorem wc_283 : pc283 <+: ais.drop 283 := by decide +kernel
theorem call_283 (feat : Features) : Dec feat ais 283 (FV7z.mk .call 64 [.rel 18446744073709529328] 5) :=
  Dec.shift (j := 283) (k := 0) (pc283_0 feat) wc_283 (Nat.zero_le _)
theorem tgt_283 : ais_at.add (283 + 5) + BitVec.ofNat 64 18446744073709529328 = 0x44d5d0#64 := by decide

/-- The `call` of `memcpy` (338). -/
def pc338 : List Byte := [0xe8, 0x59, 0xe3, 0xfa, 0xff]
theorem pc338_0 : ∀ feat, Dec feat pc338 0 (FV7z.mk .call 64 [.rel 18446744073709216601] 5) := by dec_rfl
theorem wc_338 : pc338 <+: ais.drop 338 := by decide +kernel
theorem call_338 (feat : Features) : Dec feat ais 338 (FV7z.mk .call 64 [.rel 18446744073709216601] 5) :=
  Dec.shift (j := 338) (k := 0) (pc338_0 feat) wc_338 (Nat.zero_le _)
theorem tgt_338 : ais_at.add (338 + 5) + BitVec.ofNat 64 18446744073709216601 = 0x401070#64 := by decide

/-- The `call` of `operator delete []` (346). -/
def pc346 : List Byte := [0xe8, 0xd1, 0xe7, 0x1a, 0x00]
theorem pc346_0 : ∀ feat, Dec feat pc346 0 (FV7z.mk .call 64 [.rel 1763281] 5) := by dec_rfl
theorem wc_346 : pc346 <+: ais.drop 346 := by decide +kernel
theorem call_346 (feat : Features) : Dec feat ais 346 (FV7z.mk .call 64 [.rel 1763281] 5) :=
  Dec.shift (j := 346) (k := 0) (pc346_0 feat) wc_346 (Nat.zero_le _)
theorem tgt_346 : ais_at.add (346 + 5) + BitVec.ofNat 64 1763281 = 0x6014f0#64 := by decide

/-- The `ret`. -/
def pret : List Byte := [0xc3]
theorem pret_0 : ∀ feat, Dec feat pret 0 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem wt_199 : pret <+: ais.drop 199 := by decide +kernel
theorem ret_199 (feat : Features) : Dec feat ais 199 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 199) (k := 0) (pret_0 feat) wt_199 (Nat.zero_le _)

/-! ## Values -/

/-- `jne` taken after `cmp x, y`. -/
theorem ne_c5 {x y : BitVec 64} (h : (!decide (x = y)) = true) : x ≠ y := by
  intro e; subst e; simp at h

/-- `jne` taken after `test x, x`. -/
theorem nz32 {x : BitVec 32} (h : (!(x &&& x == 0)) = true) : x ≠ 0 := by
  intro e; subst e; simp at h

/-- `lea eax, [r13 - 1]` with `r13` = `nn` (as `Ocv.rbx0_eq`): `nn - 1`. -/
theorem m_lea {nn : BitVec 32} (h1 : nn.toNat ≠ 0) :
    (BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.setWidth 64 nn + 18446744073709551615#64))).toNat =
      nn.toNat - 1 := by
  have h2 : nn.toNat < 4294967296 := nn.isLt
  have l64 : 4294967296 ≤ 2 ^ 64 := by decide
  have eA : (BitVec.setWidth 64 nn).toNat = nn.toNat := by
    rw [BitVec.toNat_setWidth]
    exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le h2 l64)
  have eB : (BitVec.setWidth 64 nn + 18446744073709551615#64).toNat = nn.toNat - 1 := by
    rw [BitVec.toNat_add, eA, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (a := 18446744073709551615) (b := 2 ^ 64) (by decide)]
    have e : nn.toNat + 18446744073709551615 = (nn.toNat - 1) + 2 ^ 64 := by
      rw [show (2 : Nat) ^ 64 = 18446744073709551616 from rfl]
      omega
    rw [e, Nat.add_mod_right]
    exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.sub_le _ _) (Nat.lt_of_lt_of_le h2 l64))
  have eC : (BitVec.setWidth 32 (BitVec.setWidth 64 nn + 18446744073709551615#64)).toNat = nn.toNat - 1 := by
    rw [BitVec.toNat_setWidth, eB]
    exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.sub_le _ _) h2)
  rw [BitVec.toNat_setWidth, eC]
  exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.sub_le _ _) (Nat.lt_of_lt_of_le h2 l64))

/-- `8 (n - 1) + 8` = `8 n` below `2^64`, `n` not 0 and below `2^32`. -/
theorem m_nat {n : Nat} (h1 : n ≠ 0) (h2 : n < 4294967296) :
    ((n - 1) * (8 % 2 ^ 64) % 2 ^ 64 + 8 % 2 ^ 64) % 2 ^ 64 = 8 * n % 2 ^ 64 := by
  have e8 : 8 % 2 ^ 64 = 8 := Nat.mod_eq_of_lt (by decide)
  have l5 : (n - 1) * 8 < 2 ^ 64 := by
    rw [show (2 : Nat) ^ 64 = 18446744073709551616 from rfl]
    omega
  have l6 : (n - 1) * 8 + 8 = 8 * n := by omega
  rw [e8, Nat.mod_eq_of_lt l5, l6]

/-- The count at `rsp + 8`: `8 nn` from `lea eax, [r13 - 1]; lea rax, [rax*8 + 8]`, `nn` not 0. -/
theorem m_eq (nn : BitVec 32) (h : nn ≠ 0) :
    BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.setWidth 64 nn + 18446744073709551615#64)) * 8#64 + 8#64 =
      BitVec.ofNat 64 (8 * nn.toNat) := by
  have h1 : nn.toNat ≠ 0 := fun e => h (BitVec.eq_of_toNat_eq (e.trans rfl))
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_mul, m_lea h1, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  exact m_nat h1 nn.isLt

/-- The loop's offset one round on. -/
theorem r14_succ (k : Nat) : BitVec.ofNat 64 (8 * k) + 8#64 = BitVec.ofNat 64 (8 * (k + 1)) := by
  rw [show 8 * (k + 1) = 8 * k + 8 by omega, BitVec.ofNat_add]

/-! ## The frame -/

/-- The frame from the prologue on: `rsp` = `aR S`, `rbx` = the vector `vb`, `r12` = `item`. -/
abbrev Fm (S : Addr) (g0 : Gprs) (vb : Addr) (g : Gprs) : Prop :=
  g.rsp = aR S ∧ g.rbx = vb ∧ g.r12 = g0.rdx

/-- What a piece keeps: `rsp`, `rbx`, `r12`. -/
abbrev Fr (g g' : Gprs) : Prop := g'.rsp = g.rsp ∧ g'.rbx = g.rbx ∧ g'.r12 = g.r12

theorem Fm.fr {S vb : Addr} {g0 g g' : Gprs} (h : Fm S g0 vb g) (h' : Fr g g') : Fm S g0 vb g' :=
  ⟨h'.1.trans h.1, h'.2.1.trans h.2.1, h'.2.2.trans h.2.2⟩

/-- Back from a callee: `rsp` as before the `call`, the callee-saved registers kept. -/
theorem fm_ret {S vb : Addr} {g0 g g' : Gprs} (h : Fm S g0 vb g) (hs : g'.rsp = aR S) (hk : KS g g') :
    Fm S g0 vb g' :=
  ⟨hs, hk.1.trans h.2.1, hk.2.2.1.trans h.2.2⟩

/-- The loop's frame: `rbp` = the new item `p`, `r14` = the offset `r`. -/
abbrev Lf (S : Addr) (g0 : Gprs) (vb p r : Addr) (g : Gprs) : Prop := Fm S g0 vb g ∧ g.rbp = p ∧ g.r14 = r

theorem Lf.fr {S vb p r : Addr} {g0 g g' : Gprs} (h : Lf S g0 vb p r g) (hb : g'.rbp = g.rbp)
    (h14 : g'.r14 = g.r14) (hf : Fr g g') : Lf S g0 vb p r g' :=
  ⟨Fm.fr h.1 hf, hb.trans h.2.1, h14.trans h.2.2⟩

theorem Lf.ret {S vb p r : Addr} {g0 g g' : Gprs} (h : Lf S g0 vb p r g) (hs : g'.rsp = aR S) (hk : KS g g') :
    Lf S g0 vb p r g' :=
  ⟨fm_ret h.1 hs hk, hk.2.1.trans h.2.1, hk.2.2.2.2.1.trans h.2.2⟩

/-- The vector's fields the code stores into: `_items`, `_size`, `_capacity`, the slot `_items[_size]`. -/
abbrev Vk (I : (Addr → Byte) → Prop) (Ok : Addr → Nat → Prop) (vb : Addr) : Prop :=
  Ok vb 8 ∧ Ok (vb + 8#64) 4 ∧ Ok (vb + 12#64) 4 ∧
    ∀ W W', I W → I W' → Ok (rdq(W, vb) + BitVec.setWidth 64 rdd(W', vb + 8#64) * 8#64) 8

/-- The new item's fields (at `p`): `PathParts._items`, the 8 bytes at `+ 8`, `_capacity`, `_size`, the flags word,
the slot `PathParts._items[_size]`. -/
abbrev Ob (I : (Addr → Byte) → Prop) (Ok : Addr → Nat → Prop) (p : Addr) : Prop :=
  Ok p 8 ∧ Ok (p + 8#64) 8 ∧ Ok (p + 12#64) 4 ∧ Ok (p + 8#64) 4 ∧ Ok (p + 16#64) 4 ∧
    ∀ W, I W → Ok (rdq(W, p) + BitVec.setWidth 64 rdd(W, p + 8#64) * 8#64) 8

/-- A callee from the `call` before `j` (entry `ent`, the bytes `W`, the registers `A`): at its entry, and from its
return at `j` with `rsp` = `aR S`, the callee-saved registers as at its entry, `B` and the invariant `J`, the run
goes on to the goal. -/
def KC (prof : Profile) (F : Footprint) (Wl : List Rgn) (L : List (Addr × List Byte)) (s₀ : State) (o : Oracle)
    (gev : List Event) (gP : State → Nat → List Event → Prop) (gE : Outcome → List Event → Prop)
    (S : Addr) (J : (Addr → Byte) → Prop) (ent : Addr) (j : Nat) (W : Addr → Byte) (A B : Gprs → Prop) : Prop :=
  ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y →
    Agree F Y.proc.mm.mem (Vst W (aR S - 8) (toBytesLE (ais_at.add j) 8)) →
    Y.cpu.rip = ent → Y.cpu.gpr.rsp = aR S - 8 → A Y.cpu.gpr →
    (∀ (Z : State) (W' : Addr → Byte) (t'' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem W' →
      Z.cpu.rip = ais_at.add j → Z.cpu.gpr.rsp = aR S → KS Y.cpu.gpr Z.cpu.gpr → B Z.cpu.gpr → J W' →
      GoG prof L o gev gP gE Z t'') →
    GoG prof L o gev gP gE Y t'

/-- The hypotheses of the runs from the cut points (`S`, `g0` the entry's stack pointer and registers, `vb` the
vector, `e₂.add j₂` the return address, `I` the invariant of the bytes, `Ok` the stores that keep it, `pp`, `nn`
`item.PathParts`' `_items` and `_size`). -/
structure Ev (prof : Profile) (F : Footprint) (Wl : List Rgn) (L : List (Addr × List Byte)) (s₀ : State)
    (o : Oracle) (gev : List Event) (gP : State → Nat → List Event → Prop) (gE : Outcome → List Event → Prop)
    (S : Addr) (g0 : Gprs) (vb : Addr) (e₂ : Addr) (code₂ : List Byte) (j₂ : Nat) (I : (Addr → Byte) → Prop)
    (Ok : Addr → Nat → Prop) (pp : Addr) (nn : BitVec 32) : Prop where
  c : Seg prof F Wl L s₀ o
  hin : CodeIn L ais_at ais
  hin₂ : CodeIn L e₂ code₂
  h₂ : j₂ < code₂.length
  hI : ∀ W, I W → Stk W S g0 (e₂.add j₂)
  hok : ∀ a n, Ok a n → ∀ i < n, Foot Wl (Addr.add a i)
  hcl : ∀ (W : Addr → Byte) (a : Addr) (n : Nat) (bs : List Byte), bs.length = n → Ok a n → I W → I (Vst W a bs)
  hcs : ∀ (W : Addr → Byte) (bs : List Byte), bs.length = 8 → I W → I (Vst W (aR S + 8#64) bs)
  hfr : ∀ (W : Addr → Byte) (a : Addr) (n : Nat) (bs : List Byte), bs.length = n → Ok a n →
    rdq(Vst W a bs, aR S + 8#64) = rdq(W, aR S + 8#64)
  hrd : ∀ (W : Addr → Byte) (v : BitVec 64), rdq(Vst W (aR S + 8#64) (toBytesLE v 8), aR S + 8#64) = v
  ws8 : ∀ i < 8, Foot Wl (Addr.add (aR S + 8#64) i)
  fs8 : ∀ i < 8, Foot F.data (Addr.add (aR S + 8#64) i)
  hv : Vk I Ok vb
  fi0 : ∀ i < 8, Foot F.data (Addr.add g0.rdx i)
  fi8 : ∀ i < 4, Foot F.data (Addr.add (g0.rdx + 8#64) i)
  fi16 : ∀ i < 4, Foot F.data (Addr.add (g0.rdx + 16#64) i)
  hpp : ∀ W, I W → rdq(W, g0.rdx) = pp ∧ rdd(W, g0.rdx + 8#64) = nn
  fpp : ∀ k < nn.toNat, ∀ i < 8, Foot F.data (Addr.add (pp + BitVec.ofNat 64 (8 * k)) i)
  fb48 : ∀ i < 8, Foot F.data (Addr.add (S - 8 - 8 - 8 - 8 - 8 - 8) i)
  fb40 : ∀ i < 8, Foot F.data (Addr.add (S - 8 - 8 - 8 - 8 - 8) i)
  fb32 : ∀ i < 8, Foot F.data (Addr.add (S - 8 - 8 - 8 - 8) i)
  fb24 : ∀ i < 8, Foot F.data (Addr.add (S - 8 - 8 - 8) i)
  fb16 : ∀ i < 8, Foot F.data (Addr.add (S - 8 - 8) i)
  fb8 : ∀ i < 8, Foot F.data (Addr.add (S - 8) i)
  hl : ∀ i < 8, Foot F.data (Addr.add S i)
  hr8 : ∀ i < 8, Foot Wl (Addr.add (aR S - 8) i)
  cA : ∃ code : List Byte, CodeIn L 0x6029b0#64 code ∧ 0 < code.length
  cN : ∃ code : List Byte, CodeIn L 0x602970#64 code ∧ 0 < code.length
  cU : ∃ code : List Byte, CodeIn L 0x44d5d0#64 code ∧ 0 < code.length
  cM : ∃ code : List Byte, CodeIn L 0x401070#64 code ∧ 0 < code.length
  cD : ∃ code : List Byte, CodeIn L 0x6014f0#64 code ∧ 0 < code.length
  k86 : ∀ W, I W → KC prof F Wl L s₀ o gev gP gE S I 0x6029b0#64 91 W (fun _ => True) (fun _ => True)
  k128 : ∀ W, I W → KC prof F Wl L s₀ o gev gP gE S I 0x602970#64 133 W (fun _ => True) (fun g => Ob I Ok g.rax)
  k215 : ∀ W, I W → KC prof F Wl L s₀ o gev gP gE S I 0x6029b0#64 220 W (fun _ => True) (fun _ => True)
  k269 : ∀ M W, I W → rdq(W, aR S + 8#64) = M → KC prof F Wl L s₀ o gev gP gE S
    (fun W' => I W' ∧ rdq(W', aR S + 8#64) = M) 0x602970#64 274 W (fun _ => True) (fun _ => True)
  k283 : ∀ M W, I W → rdq(W, aR S + 8#64) = M → KC prof F Wl L s₀ o gev gP gE S
    (fun W' => I W' ∧ rdq(W', aR S + 8#64) = M) 0x44d5d0#64 288 W (fun _ => True) (fun _ => True)
  k338 : ∀ W, I W → KC prof F Wl L s₀ o gev gP gE S I 0x401070#64 343 W (fun _ => True) (fun _ => True)
  k346 : ∀ W, I W → KC prof F Wl L s₀ o gev gP gE S I 0x6014f0#64 351 W (fun _ => True) (fun _ => True)
  kr : ∀ (W : Addr → Byte) (Z' : State) (t' : Nat), KeptW Wl s₀ Z' → Agree F Z'.proc.mm.mem W →
    Z'.cpu.rip = e₂.add j₂ → Z'.cpu.gpr.rsp = S + 8 → KS g0 Z'.cpu.gpr → I W → GoG prof L o gev gP gE Z' t'

/-! ## The pieces -/

section Pieces
variable {F : Footprint} {Wl : List Rgn} {I : (Addr → Byte) → Prop} {Ok : Addr → Nat → Prop}

/-- The pushes, `r12` = `item`, `rbx` = `this + 0x28`, or `this + 0x38` when `include` is 0, the frame, `eax` =
`_capacity` compared with `_size`: to 123, or (equal) `cmp eax, 0x7ffffffe` to the `ja` at 49. -/
theorem vc_0 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (hs1 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8) i)) (hs2 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8) i))
    (hs3 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8 - 8) i))
    (hs4 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8 - 8 - 8) i))
    (hs5 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8 - 8 - 8 - 8) i))
    (hs6 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8 - 8 - 8 - 8 - 8) i))
    (hv : ∀ vb, (vb = g.rdi + 40#64 ∨ vb = g.rdi + 56#64) →
      (∀ i < 4, Foot F.data (Addr.add (vb + 12#64) i)) ∧ (∀ i < 4, Foot F.data (Addr.add (vb + 8#64) i)))
    (h123 : ∀ g', g'.rsp = aR g.rsp → (g'.rbx = g.rdi + 40#64 ∨ g'.rbx = g.rdi + 56#64) → g'.r12 = g.rdx →
      ∀ fl, Q 123 g' fl (P6 V g))
    (h49 : ∀ g', g'.rsp = aR g.rsp → (g'.rbx = g.rdi + 40#64 ∨ g'.rbx = g.rdi + 56#64) → g'.r12 = g.rdx →
      ∀ fl, Q 49 g' fl (P6 V g)) :
    W_0 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [aR, P6] at hs1 hs2 hs3 hs4 hs5 hs6 hv h123 h49 ⊢
  by_cases hc : (BitVec.setWidth 8 rsi &&& BitVec.setWidth 8 rsi == 0) = true
  all_goals wpx [W_0, W_44, o0, o1, Op.cmpmr, hc, ↓reduceIte, Bool.false_eq_true]
  all_goals repeat' (first
    | refine h123 _ ?_ ?_ ?_ _
    | refine h49 _ ?_ ?_ ?_ _
    | with_reducible rfl
    | with_reducible exact hs1
    | with_reducible exact hs2
    | with_reducible exact hs3
    | with_reducible exact hs4
    | with_reducible exact hs5
    | with_reducible exact hs6
    | with_reducible exact (hv _ (Or.inl rfl)).1
    | with_reducible exact (hv _ (Or.inr rfl)).1
    | with_reducible exact (hv _ (Or.inl rfl)).2
    | with_reducible exact (hv _ (Or.inr rfl)).2
    | with_reducible exact Or.inl rfl
    | with_reducible exact Or.inr rfl
    | apply And.intro
    | (exfalso; contradiction)
    | intro _)

/-- The new capacity (`cmova`), `rdi` = 8 times it: to `operator new []` (86). -/
theorem vc_55 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (h : ∀ g', Fr g g' → ∀ fl, Q 86 g' fl V) :
    W_55 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_55, o2, Op.shl64]
  all_goals repeat' (first
    | refine h _ ?_ _
    | with_reducible rfl
    | apply And.intro
    | intro _)

/-- `_size`, the old `_items` (`r14`), `r13` = the new array: `_size` not 0 to `memcpy` (338); else the old array not
null to `delete []` (343), or to 117. -/
theorem vc_91 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (f8 : ∀ i < 4, Foot F.data (Addr.add (g.rbx + 8#64) i)) (f0 : ∀ i < 8, Foot F.data (Addr.add g.rbx i))
    (h338 : ∀ g', Fr g g' → ∀ fl, Q 338 g' fl V) (h343 : ∀ g', Fr g g' → ∀ fl, Q 343 g' fl V)
    (h117 : ∀ g', Fr g g' → ∀ fl, Q 117 g' fl V) :
    W_91 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at f8 f0 ⊢
  wpx [W_91, W_328, W_108, o3, o14, o4, Op.shl64]
  all_goals repeat' (first
    | refine h338 _ ?_ _
    | refine h343 _ ?_ _
    | refine h117 _ ?_ _
    | with_reducible rfl
    | with_reducible exact f8
    | with_reducible exact f0
    | apply And.intro
    | intro _)

/-- `_items` = the new array, `_capacity` = the new capacity: to 123. -/
theorem vc_117 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (w0 : ∀ i < 8, Foot Wl (Addr.add g.rbx i)) (w12 : ∀ i < 4, Foot Wl (Addr.add (g.rbx + 12#64) i))
    (o0 : Ok g.rbx 8) (o12 : Ok (g.rbx + 12#64) 4) (hI : I V)
    (hcl : ∀ (W : Addr → Byte) (a : Addr) (n : Nat) (bs : List Byte), bs.length = n → Ok a n → I W →
      I (Vst W a bs))
    (h : ∀ g' V', I V' → Fr g g' → ∀ fl, Q 123 g' fl V') :
    W_117 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at w0 w12 o0 o12 ⊢
  wpx [W_117, o5]
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

/-- `edi` = 0x18, to `operator new` (128). -/
theorem vc_123 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} (hI : I V)
    (h : ∀ g' V', I V' → Fr g g' → ∀ fl, Q 128 g' fl V') :
    W_123 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_123, o6]
  all_goals repeat' (first
    | refine h _ _ ?_ ?_ _
    | with_reducible rfl
    | with_reducible exact hI
    | apply And.intro
    | intro _)

/-- `r13` = `item.PathParts._size`, the new item (`rbp`) cleared: not 0, `rdi` = 8 times it, to `operator new []`
(215); else to 161. -/
theorem vc_133 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (f8 : ∀ i < 4, Foot F.data (Addr.add (g.r12 + 8#64) i))
    (w0 : ∀ i < 8, Foot Wl (Addr.add g.rax i)) (w8 : ∀ i < 8, Foot Wl (Addr.add (g.rax + 8#64) i))
    (o0 : Ok g.rax 8) (o8 : Ok (g.rax + 8#64) 8) (hI : I V)
    (hcl : ∀ (W : Addr → Byte) (a : Addr) (n : Nat) (bs : List Byte), bs.length = n → Ok a n → I W →
      I (Vst W a bs))
    (h215 : ∀ g' V', I V' → rdd(V, g.r12 + 8#64) ≠ 0 → g'.r13 = BitVec.setWidth 64 rdd(V, g.r12 + 8#64) →
      g'.rbp = g.rax → Fr g g' → ∀ fl, Q 215 g' fl V')
    (h161 : ∀ g' V', I V' → g'.rbp = g.rax → Fr g g' → ∀ fl, Q 161 g' fl V') :
    W_133 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at f8 w0 w8 o0 o8 h215 h161 ⊢
  wpx [W_133, W_208, o7, o9, Op.shl64]
  all_goals repeat' (first
    | refine h215 _ _ ?_ ?_ ?_ ?_ ?_ _
    | refine h161 _ _ ?_ ?_ ?_ _
    | with_reducible rfl
    | with_reducible exact hI
    | refine hcl _ _ _ _ (toBytesLE_length _ _) ?_ ?_
    | with_reducible exact f8
    | with_reducible exact w0
    | with_reducible exact w8
    | with_reducible exact o0
    | with_reducible exact o8
    | exact nz32 ‹_›
    | apply And.intro
    | intro _)

/-- The flags word of the new item, `_size + 1`, the slot `_items[_size]` = the item, `add rsp, 0x18`, the six pops,
to the `ret`. -/
theorem vc_161 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (fi16 : ∀ i < 4, Foot F.data (Addr.add (g.r12 + 16#64) i)) (fv0 : ∀ i < 8, Foot F.data (Addr.add g.rbx i))
    (fv8 : ∀ i < 4, Foot F.data (Addr.add (g.rbx + 8#64) i))
    (w16 : ∀ i < 4, Foot Wl (Addr.add (g.rbp + 16#64) i)) (wv8 : ∀ i < 4, Foot Wl (Addr.add (g.rbx + 8#64) i))
    (wsl : ∀ W', I W' →
      ∀ i < 8, Foot Wl (Addr.add (rdq(V, g.rbx) + BitVec.setWidth 64 rdd(W', g.rbx + 8#64) * 8#64) i))
    (o16 : Ok (g.rbp + 16#64) 4) (ov8 : Ok (g.rbx + 8#64) 4)
    (osl : ∀ W', I W' → Ok (rdq(V, g.rbx) + BitVec.setWidth 64 rdd(W', g.rbx + 8#64) * 8#64) 8) (hI : I V)
    (hcl : ∀ (W : Addr → Byte) (a : Addr) (n : Nat) (bs : List Byte), bs.length = n → Ok a n → I W →
      I (Vst W a bs))
    (f1 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 24#64) i))
    (f2 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 24#64 + 8) i))
    (f3 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 24#64 + 8 + 8) i))
    (f4 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 24#64 + 8 + 8 + 8) i))
    (f5 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 24#64 + 8 + 8 + 8 + 8) i))
    (f6 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 24#64 + 8 + 8 + 8 + 8 + 8) i))
    (h : ∀ g' V', I V' → g'.rsp = g.rsp + 24#64 + 8 + 8 + 8 + 8 + 8 + 8 → g'.rbx = rdq(V', g.rsp + 24#64) →
      g'.rbp = rdq(V', g.rsp + 24#64 + 8) → g'.r12 = rdq(V', g.rsp + 24#64 + 8 + 8) →
      g'.r13 = rdq(V', g.rsp + 24#64 + 8 + 8 + 8) → g'.r14 = rdq(V', g.rsp + 24#64 + 8 + 8 + 8 + 8) →
      g'.r15 = rdq(V', g.rsp + 24#64 + 8 + 8 + 8 + 8 + 8) → ∀ fl, Q 199 g' fl V') :
    W_161 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at fi16 fv0 fv8 w16 wv8 wsl o16 ov8 osl f1 f2 f3 f4 f5 f6 h ⊢
  wpx [W_161, o8]
  all_goals repeat' (first
    | refine h _ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ _
    | with_reducible rfl
    | with_reducible exact hI
    | refine hcl _ _ _ _ (toBytesLE_length _ _) ?_ ?_
    | refine osl _ ?_
    | refine wsl _ ?_
    | with_reducible exact fi16
    | with_reducible exact fv0
    | with_reducible exact fv8
    | with_reducible exact w16
    | with_reducible exact wv8
    | with_reducible exact o16
    | with_reducible exact ov8
    | with_reducible exact f1
    | with_reducible exact f2
    | with_reducible exact f3
    | with_reducible exact f4
    | with_reducible exact f5
    | with_reducible exact f6
    | apply And.intro
    | intro _)

/-- `PathParts._items` = the new array, `_capacity` = `r13d`, `r14` = 0, the count `8 r13d` at `rsp + 8`: to the
loop (256). -/
theorem vc_220 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (w0 : ∀ i < 8, Foot Wl (Addr.add g.rbp i)) (w12 : ∀ i < 4, Foot Wl (Addr.add (g.rbp + 12#64) i))
    (ws8 : ∀ i < 8, Foot Wl (Addr.add (g.rsp + 8#64) i))
    (o0 : Ok g.rbp 8) (o12 : Ok (g.rbp + 12#64) 4) (hI : I V)
    (hcl : ∀ (W : Addr → Byte) (a : Addr) (n : Nat) (bs : List Byte), bs.length = n → Ok a n → I W →
      I (Vst W a bs))
    (hcs : ∀ (W : Addr → Byte) (bs : List Byte), bs.length = 8 → I W → I (Vst W (g.rsp + 8#64) bs))
    (hrd : ∀ (W : Addr → Byte) (v : BitVec 64), rdq(Vst W (g.rsp + 8#64) (toBytesLE v 8), g.rsp + 8#64) = v)
    (h : ∀ g' V', I V' → rdq(V', g.rsp + 8#64) = g'.rax →
      g'.rax = BitVec.setWidth 64 (BitVec.setWidth 32 (g.r13 + 18446744073709551615#64)) * 8#64 + 8#64 →
      g'.r14 = 0#64 → g'.rbp = g.rbp → Fr g g' → ∀ fl, Q 256 g' fl V') :
    W_220 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at w0 w12 ws8 o0 o12 hcs hrd h ⊢
  wpx [W_220, o10, BitVec.xor_self, BitVec.setWidth_zero]
  all_goals repeat' (first
    | refine h _ _ ?_ ?_ ?_ ?_ ?_ ?_ _
    | with_reducible rfl
    | with_reducible exact hI
    | with_reducible exact hrd _ _
    | with_reducible refine hcs _ _ (toBytesLE_length _ _) ?_
    | refine hcl _ _ _ _ (toBytesLE_length _ _) ?_ ?_
    | with_reducible exact w0
    | with_reducible exact w12
    | with_reducible exact ws8
    | with_reducible exact o0
    | with_reducible exact o12
    | apply And.intro
    | intro _)

/-- The loop's head: `r15` = `item.PathParts._items[k]`, `edi` = 0x10, to `operator new` (269). -/
theorem vc_256 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (fp0 : ∀ i < 8, Foot F.data (Addr.add g.r12 i))
    (fpk : ∀ i < 8, Foot F.data (Addr.add (rdq(V, g.r12) + g.r14) i))
    (h : ∀ g', g'.rbp = g.rbp → g'.r14 = g.r14 → Fr g g' → ∀ fl, Q 269 g' fl V) :
    W_256 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at fp0 fpk h ⊢
  wpx [W_256, o11]
  all_goals repeat' (first
    | refine h _ ?_ ?_ ?_ _
    | with_reducible rfl
    | with_reducible exact fp0
    | with_reducible exact fpk
    | apply And.intro
    | intro _)

/-- `rsi` = `r15`, `rdi` = `r13` = the new `UString`, to its copy (283). -/
theorem vc_274 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (h : ∀ g', g'.rbp = g.rbp → g'.r14 = g.r14 → Fr g g' → ∀ fl, Q 283 g' fl V) :
    W_274 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h ⊢
  wpx [W_274, o12]
  all_goals repeat' (first
    | refine h _ ?_ ?_ ?_ _
    | with_reducible rfl
    | apply And.intro
    | intro _)

/-- `PathParts._size + 1`, the slot `PathParts._items[_size]` = `r13`, `r14 + 8` compared with the count: not equal
back to 256, else to 161. -/
theorem vc_288 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (fb8 : ∀ i < 4, Foot F.data (Addr.add (g.rbp + 8#64) i)) (fb0 : ∀ i < 8, Foot F.data (Addr.add g.rbp i))
    (wb8 : ∀ i < 4, Foot Wl (Addr.add (g.rbp + 8#64) i))
    (wsl : ∀ i < 8, Foot Wl (Addr.add (rdq(V, g.rbp) + BitVec.setWidth 64 rdd(V, g.rbp + 8#64) * 8#64) i))
    (ob8 : Ok (g.rbp + 8#64) 4) (osl : Ok (rdq(V, g.rbp) + BitVec.setWidth 64 rdd(V, g.rbp + 8#64) * 8#64) 8)
    (fs8 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8#64) i)) (hI : I V)
    (hcl : ∀ (W : Addr → Byte) (a : Addr) (n : Nat) (bs : List Byte), bs.length = n → Ok a n → I W →
      I (Vst W a bs))
    (h256 : ∀ g' V', I V' → g'.r14 = g.r14 + 8#64 → rdq(V', g.rsp + 8#64) ≠ g'.r14 → g'.rbp = g.rbp → Fr g g' →
      ∀ fl, Q 256 g' fl V')
    (h161 : ∀ g' V', I V' → g'.rbp = g.rbp → Fr g g' → ∀ fl, Q 161 g' fl V') :
    W_288 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at fb8 fb0 wb8 wsl ob8 osl fs8 h256 h161 ⊢
  wpx [W_288, W_316, o13, Op.cmpmr]
  all_goals repeat' (first
    | refine h256 _ _ ?_ ?_ ?_ ?_ ?_ _
    | refine h161 _ _ ?_ ?_ ?_ _
    | with_reducible rfl
    | with_reducible exact hI
    | refine hcl _ _ _ _ (toBytesLE_length _ _) ?_ ?_
    | with_reducible exact fb8
    | with_reducible exact fb0
    | with_reducible exact wb8
    | with_reducible exact wsl
    | with_reducible exact ob8
    | with_reducible exact osl
    | with_reducible exact fs8
    | exact ne_c5 ‹_›
    | apply And.intro
    | intro _)

/-- `rdi` = the old array, to `delete []` (346). -/
theorem vc_343 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (h : ∀ g', Fr g g' → ∀ fl, Q 346 g' fl V) :
    W_343 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_343, o15]
  all_goals repeat' (first
    | refine h _ ?_ _
    | with_reducible rfl
    | apply And.intro
    | intro _)

/-- `jmp` to 117. -/
theorem vc_351 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} (h : ∀ fl, Q 117 g fl V) :
    W_351 F Wl Q g f V := h _

end Pieces

/-! ## The runs -/

section Runs
variable {prof : Profile} {F : Footprint} {Wl : List Rgn} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {S : Addr} {g0 : Gprs} {vb : Addr} {e₂ : Addr} {code₂ : List Byte} {j₂ : Nat} {I : (Addr → Byte) → Prop}
  {Ok : Addr → Nat → Prop} {pp : Addr} {nn : BitVec 32} {Y : State} {t : Nat} {W : Addr → Byte}

/-- A store's footprint in `F.data`. -/
theorem Ev.fd (E : Ev prof F Wl L s₀ o gev gP gE S g0 vb e₂ code₂ j₂ I Ok pp nn) {a : Addr} {n : Nat}
    (h : Ok a n) : ∀ i < n, Foot F.data (Addr.add a i) := fun i hi => E.c.hws _ (E.hok _ _ h i hi)

/-- The invariant with the count in the stack slot, kept by the stores `Ok` allows. -/
theorem Ev.jcl (E : Ev prof F Wl L s₀ o gev gP gE S g0 vb e₂ code₂ j₂ I Ok pp nn) (M : BitVec 64) :
    ∀ (W : Addr → Byte) (a : Addr) (n : Nat) (bs : List Byte), bs.length = n → Ok a n →
      (I W ∧ rdq(W, aR S + 8#64) = M) → (I (Vst W a bs) ∧ rdq(Vst W a bs, aR S + 8#64) = M) :=
  fun W a n bs hl ho h => ⟨E.hcl W a n bs hl ho h.1, (E.hfr W a n bs hl ho).trans h.2⟩

/-- A `call` at `j` (`rsp` = `aR S`, the bytes `W`) of the callee `k`, and from its return at `j + 5`. -/
theorem callK (E : Ev prof F Wl L s₀ o gev gP gE S g0 vb e₂ code₂ j₂ I Ok pp nn) {J : (Addr → Byte) → Prop}
    {U : State} {t₁ : Nat} {j R : Nat} {ent : Addr} {A B : Gprs → Prop} (hKU : KeptW Wl s₀ U)
    (hAU : Agree F U.proc.mm.mem W) (hrU : U.cpu.rip = ais_at.add j) (hs : U.cpu.gpr.rsp = aR S)
    (hj : j < ais.length) (hd : Dec prof.feat ais j (FV7z.mk .call 64 [.rel R] 5))
    (htgt : ais_at.add (j + 5) + BitVec.ofNat 64 R = ent)
    (hc : ∃ code : List Byte, CodeIn L ent code ∧ 0 < code.length)
    (k : KC prof F Wl L s₀ o gev gP gE S J ent (j + 5) W A B) (hA : A (U.cpu.gpr.set 4 (aR S - 8)))
    (h : ∀ (Z : State) (W' : Addr → Byte) (t'' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem W' →
      Z.cpu.rip = ais_at.add (j + 5) → Z.cpu.gpr.rsp = aR S → KS U.cpu.gpr Z.cpu.gpr → B Z.cpu.gpr → J W' →
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

/-- From 161 (`rbp` = the new item): its flags word, appended to `vb`, the epilogue, the `ret`, to `kr`. -/
theorem tail161 (E : Ev prof F Wl L s₀ o gev gP gE S g0 vb e₂ code₂ j₂ I Ok pp nn) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = ais_at.add 161) (hm : Fm S g0 vb Y.cpu.gpr)
    (hob : Ob I Ok Y.cpu.gpr.rbp) (hIW : I W) :
    GoG prof L o gev gP gE Y t := by
  obtain ⟨ms, mx, m12⟩ := hm
  obtain ⟨ov0, ov8, ov12, ovs⟩ := E.hv
  refine (c_161 prof).run E.c E.hin (fun j' g' _ V' => j' = 199 ∧ I V' ∧
      g'.rsp = Y.cpu.gpr.rsp + 24#64 + 8 + 8 + 8 + 8 + 8 + 8 ∧ g'.rbx = rdq(V', Y.cpu.gpr.rsp + 24#64) ∧
      g'.rbp = rdq(V', Y.cpu.gpr.rsp + 24#64 + 8) ∧ g'.r12 = rdq(V', Y.cpu.gpr.rsp + 24#64 + 8 + 8) ∧
      g'.r13 = rdq(V', Y.cpu.gpr.rsp + 24#64 + 8 + 8 + 8) ∧ g'.r14 = rdq(V', Y.cpu.gpr.rsp + 24#64 + 8 + 8 + 8 + 8) ∧
      g'.r15 = rdq(V', Y.cpu.gpr.rsp + 24#64 + 8 + 8 + 8 + 8 + 8))
    hK hA hr
    (vc_161 (by rw [m12]; exact E.fi16) (by rw [mx]; exact E.fd ov0) (by rw [mx]; exact E.fd ov8)
      (E.hok _ _ hob.2.2.2.2.1) (by rw [mx]; exact E.hok _ _ ov8)
      (fun W' h => by rw [mx]; exact E.hok _ _ (ovs W W' hIW h)) hob.2.2.2.2.1 (by rw [mx]; exact ov8)
      (fun W' h => by rw [mx]; exact ovs W W' hIW h) hIW E.hcl (by rw [ms, q1]; exact E.fb48)
      (by rw [ms, q2]; exact E.fb40) (by rw [ms, q3]; exact E.fb32) (by rw [ms, q4]; exact E.fb24)
      (by rw [ms, q5]; exact E.fb16) (by rw [ms, q6]; exact E.fb8)
      fun _ V' hI a b d e f g h _ => ⟨rfl, hI, a, b, d, e, f, g, h⟩) ?_
  rintro j' g fl V₁ ⟨rfl, hI1, gs, gx, gp, g12, g13, g14, g15⟩ U t₁ hKU hAU hrU hgU -
  subst hgU
  obtain ⟨s1, s2, s3, s4, s5, s6, s7⟩ := E.hI V₁ hI1
  have e1 : rdq(V₁, Y.cpu.gpr.rsp + 24#64) = g0.rbx := by rw [ms, q1]; exact s1
  have e2 : rdq(V₁, Y.cpu.gpr.rsp + 24#64 + 8) = g0.rbp := by rw [ms, q2]; exact s2
  have e3 : rdq(V₁, Y.cpu.gpr.rsp + 24#64 + 8 + 8) = g0.r12 := by rw [ms, q3]; exact s3
  have e4 : rdq(V₁, Y.cpu.gpr.rsp + 24#64 + 8 + 8 + 8) = g0.r13 := by rw [ms, q4]; exact s4
  have e5 : rdq(V₁, Y.cpu.gpr.rsp + 24#64 + 8 + 8 + 8 + 8) = g0.r14 := by rw [ms, q5]; exact s5
  have e6 : rdq(V₁, Y.cpu.gpr.rsp + 24#64 + 8 + 8 + 8 + 8 + 8) = g0.r15 := by rw [ms, q6]; exact s6
  have hsU : U.cpu.gpr.rsp = S := by rw [gs, ms]; exact q7 S
  refine E.c.s_ret hKU hAU E.hin (lt_len (by decide)) hrU (ret_199 _) (by rw [hsU]; exact E.hl) E.hin₂ E.h₂
    (by rw [hsU]; exact s7) ?_
  rintro Z' t₂ hKZ' hAZ' ⟨hrZ', hgZ'⟩
  refine E.kr V₁ Z' t₂ hKZ' hAZ' hrZ' ?_ ?_ hI1
  · rw [hgZ']
    show U.cpu.gpr.rsp + 8 = _
    rw [hsU]
  · rw [hgZ']
    exact ⟨gx.trans e1, gp.trans e2, g12.trans e3, g13.trans e4, g14.trans e5, g15.trans e6⟩

/-- One round of the loop from 256 (`r14` = `8 k`, `k` below `nn`, the count `8 nn` in the slot): `operator new`
(`k269`), the `UString` copy (`k283`), appended; then to 161, or back to 256 with `k + 1` below `nn` (`hc`). -/
theorem step (E : Ev prof F Wl L s₀ o gev gP gE S g0 vb e₂ code₂ j₂ I Ok pp nn) {p : Addr} {k : Nat}
    (hk : k < nn.toNat) (hK : KeptW Wl s₀ Y) (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = ais_at.add 256)
    (hl : Lf S g0 vb p (BitVec.ofNat 64 (8 * k)) Y.cpu.gpr) (hob : Ob I Ok p) (hIW : I W)
    (hMW : rdq(W, aR S + 8#64) = BitVec.ofNat 64 (8 * nn.toNat))
    (hc : ∀ (U : State) (W' : Addr → Byte) (t' : Nat), KeptW Wl s₀ U → Agree F U.proc.mm.mem W' →
      U.cpu.rip = ais_at.add 256 → Lf S g0 vb p (BitVec.ofNat 64 (8 * (k + 1))) U.cpu.gpr → I W' →
      rdq(W', aR S + 8#64) = BitVec.ofNat 64 (8 * nn.toNat) → k + 1 < nn.toNat → GoG prof L o gev gP gE U t') :
    GoG prof L o gev gP gE Y t := by
  obtain ⟨hm, hbp, h14⟩ := hl
  refine (c_256 prof).run E.c E.hin (fun j' g' _ V' => j' = 269 ∧ V' = W ∧ g'.rbp = Y.cpu.gpr.rbp ∧
      g'.r14 = Y.cpu.gpr.r14 ∧ Fr Y.cpu.gpr g') hK hA hr
    (vc_256 (by rw [hm.2.2]; exact E.fi0) (by rw [hm.2.2, (E.hpp W hIW).1, h14]; exact E.fpp k hk)
      fun _ a b e _ => ⟨rfl, rfl, a, b, e⟩) ?_
  rintro j' g fl V₁ ⟨rfl, hV₁, gbp, g14, gf⟩ U t₁ hKU hAU hrU hgU -
  subst V₁ hgU
  have hl1 : Lf S g0 vb p (BitVec.ofNat 64 (8 * k)) U.cpu.gpr := ⟨Fm.fr hm gf, gbp.trans hbp, g14.trans h14⟩
  refine callK E hKU hAU hrU hl1.1.1 (lt_len (by decide)) (call_269 _) tgt_269 E.cN (E.k269 _ W hIW hMW)
    trivial ?_
  intro Z W₂ t₂ hKZ hAZ hrZ hsZ hkZ _ hJ2
  have hl2 := Lf.ret hl1 hsZ hkZ
  refine (c_274 prof).run E.c E.hin (fun j' g' _ V' => j' = 283 ∧ V' = W₂ ∧ g'.rbp = Z.cpu.gpr.rbp ∧
      g'.r14 = Z.cpu.gpr.r14 ∧ Fr Z.cpu.gpr g') hKZ hAZ hrZ (vc_274 fun _ a b e _ => ⟨rfl, rfl, a, b, e⟩) ?_
  rintro j' g fl V₂ ⟨rfl, hV₂, gbp, g14, gf⟩ U₂ t₃ hKU₂ hAU₂ hrU₂ hgU₂ -
  subst V₂ hgU₂
  have hl3 := Lf.fr hl2 gbp g14 gf
  refine callK E hKU₂ hAU₂ hrU₂ hl3.1.1 (lt_len (by decide)) (call_283 _) tgt_283 E.cU
    (E.k283 _ W₂ hJ2.1 hJ2.2) trivial ?_
  intro Z₂ W₃ t₄ hKZ₂ hAZ₂ hrZ₂ hsZ₂ hkZ₂ _ hJ3
  obtain ⟨hm4, hbp4, h144⟩ := Lf.ret hl3 hsZ₂ hkZ₂
  refine (c_288 prof).run E.c E.hin (fun j' g' _ V' =>
      (I V' ∧ rdq(V', aR S + 8#64) = BitVec.ofNat 64 (8 * nn.toNat)) ∧ g'.rbp = Z₂.cpu.gpr.rbp ∧
      Fr Z₂.cpu.gpr g' ∧ (j' = 161 ∨ (j' = 256 ∧ g'.r14 = Z₂.cpu.gpr.r14 + 8#64 ∧
        rdq(V', Z₂.cpu.gpr.rsp + 8#64) ≠ g'.r14))) hKZ₂ hAZ₂ hrZ₂
    (vc_288 (I := fun W' => I W' ∧ rdq(W', aR S + 8#64) = BitVec.ofNat 64 (8 * nn.toNat))
      (by rw [hbp4]; exact E.fd hob.2.2.2.1) (by rw [hbp4]; exact E.fd hob.1)
      (by rw [hbp4]; exact E.hok _ _ hob.2.2.2.1) (by rw [hbp4]; exact E.hok _ _ (hob.2.2.2.2.2 W₃ hJ3.1))
      (by rw [hbp4]; exact hob.2.2.2.1) (by rw [hbp4]; exact hob.2.2.2.2.2 W₃ hJ3.1) (by rw [hm4.1]; exact E.fs8)
      hJ3 (E.jcl _) (fun _ V' hJ a hne b e _ => ⟨hJ, b, e, Or.inr ⟨rfl, a, hne⟩⟩)
      (fun _ V' hJ b e _ => ⟨hJ, b, e, Or.inl rfl⟩)) ?_
  rintro j' g fl V₃ ⟨hJ4, gbp, gf, hj⟩ U₃ t₅ hKU₃ hAU₃ hrU₃ hgU₃ -
  subst hgU₃
  have hm5 : Fm S g0 vb U₃.cpu.gpr := Fm.fr hm4 gf
  have hbp5 : U₃.cpu.gpr.rbp = p := gbp.trans hbp4
  rcases hj with rfl | ⟨rfl, g14, hne⟩
  · exact tail161 E hKU₃ hAU₃ hrU₃ hm5 (by rw [hbp5]; exact hob) hJ4.1
  · have h145 : U₃.cpu.gpr.r14 = BitVec.ofNat 64 (8 * (k + 1)) := by rw [g14, h144]; exact r14_succ k
    have hne' := hne
    rw [hm4.1, hJ4.2, h145] at hne'
    have hk1 : k + 1 < nn.toNat := by
      rcases Nat.lt_or_ge (k + 1) nn.toNat with h | h
      · exact h
      · exfalso
        apply hne'
        rw [show k + 1 = nn.toNat by omega]
    exact hc U₃ V₃ t₅ hKU₃ hAU₃ hrU₃ ⟨hm5, hbp5, h145⟩ hJ4.1 hJ4.2 hk1

/-- The loop from 256, by induction on what is left (`d`). -/
theorem loop (E : Ev prof F Wl L s₀ o gev gP gE S g0 vb e₂ code₂ j₂ I Ok pp nn) {p : Addr} :
    ∀ (d k : Nat) (Y : State) (W : Addr → Byte) (t : Nat), k + d + 1 = nn.toNat → KeptW Wl s₀ Y →
      Agree F Y.proc.mm.mem W → Y.cpu.rip = ais_at.add 256 →
      Lf S g0 vb p (BitVec.ofNat 64 (8 * k)) Y.cpu.gpr → Ob I Ok p → I W →
      rdq(W, aR S + 8#64) = BitVec.ofNat 64 (8 * nn.toNat) → GoG prof L o gev gP gE Y t := by
  intro d
  induction d with
  | zero =>
    intro k Y W t hd hK hA hr hl hob hIW hMW
    exact step E (by omega) hK hA hr hl hob hIW hMW fun U W' t' _ _ _ _ _ _ hk1 => absurd hk1 (by omega)
  | succ d ih =>
    intro k Y W t hd hK hA hr hl hob hIW hMW
    exact step E (by omega) hK hA hr hl hob hIW hMW fun U W' t' hKU hAU hrU hlU hIU hMU _ =>
      ih (k + 1) U W' t' (by omega) hKU hAU hrU hlU hob hIU hMU

/-- From 220 (back from `operator new []`, `rbp` = the new item, `r13` = `nn`, not 0): `PathParts` set up, the
count, the loop. -/
theorem from220 (E : Ev prof F Wl L s₀ o gev gP gE S g0 vb e₂ code₂ j₂ I Ok pp nn) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = ais_at.add 220) (hm : Fm S g0 vb Y.cpu.gpr)
    (hob : Ob I Ok Y.cpu.gpr.rbp) (hnn : nn ≠ 0) (h13 : Y.cpu.gpr.r13 = BitVec.setWidth 64 nn) (hIW : I W) :
    GoG prof L o gev gP gE Y t := by
  refine (c_220 prof).run E.c E.hin (fun j' g' _ V' => j' = 256 ∧ I V' ∧ rdq(V', Y.cpu.gpr.rsp + 8#64) = g'.rax ∧
      g'.rax = BitVec.setWidth 64 (BitVec.setWidth 32 (Y.cpu.gpr.r13 + 18446744073709551615#64)) * 8#64 + 8#64 ∧
      g'.r14 = 0#64 ∧ g'.rbp = Y.cpu.gpr.rbp ∧ Fr Y.cpu.gpr g') hK hA hr
    (vc_220 (E.hok _ _ hob.1) (E.hok _ _ hob.2.2.1) (by rw [hm.1]; exact E.ws8) hob.1 hob.2.2.1 hIW E.hcl
      (by rw [hm.1]; exact E.hcs) (by rw [hm.1]; exact E.hrd)
      fun _ V' hI a b d e f _ => ⟨rfl, hI, a, b, d, e, f⟩) ?_
  rintro j' g fl V₁ ⟨rfl, hI1, hrq, hax, h14, gbp, gf⟩ U t₁ hKU hAU hrU hgU -
  subst hgU
  have hn0 : nn.toNat ≠ 0 := fun e => hnn (BitVec.eq_of_toNat_eq (by rw [e]; rfl))
  have hM : U.cpu.gpr.rax = BitVec.ofNat 64 (8 * nn.toNat) := by rw [hax, h13]; exact m_eq nn hnn
  rw [hm.1] at hrq
  exact loop E (nn.toNat - 1) 0 U V₁ t₁ (by omega) hKU hAU hrU
    ⟨Fm.fr hm gf, gbp, by rw [h14]⟩ hob hI1 (hrq.trans hM)

/-- From 133 (back from `operator new`, `rax` = the new item): cleared; `nn` not 0, `operator new []` (`k215`) and
from its return 220; else to 161. -/
theorem from133 (E : Ev prof F Wl L s₀ o gev gP gE S g0 vb e₂ code₂ j₂ I Ok pp nn) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = ais_at.add 133) (hm : Fm S g0 vb Y.cpu.gpr)
    (hob : Ob I Ok Y.cpu.gpr.rax) (hIW : I W) :
    GoG prof L o gev gP gE Y t := by
  have hn : rdd(W, Y.cpu.gpr.r12 + 8#64) = nn := by rw [hm.2.2]; exact (E.hpp W hIW).2
  refine (c_133 prof).run E.c E.hin (fun j' g' _ V' => I V' ∧ Fr Y.cpu.gpr g' ∧ g'.rbp = Y.cpu.gpr.rax ∧
      (j' = 161 ∨ (j' = 215 ∧ rdd(W, Y.cpu.gpr.r12 + 8#64) ≠ 0 ∧
        g'.r13 = BitVec.setWidth 64 rdd(W, Y.cpu.gpr.r12 + 8#64)))) hK hA hr
    (vc_133 (by rw [hm.2.2]; exact E.fi8) (E.hok _ _ hob.1) (E.hok _ _ hob.2.1) hob.1 hob.2.1 hIW E.hcl
      (fun _ V' hI a b d e _ => ⟨hI, e, d, Or.inr ⟨rfl, a, b⟩⟩) (fun _ V' hI d e _ => ⟨hI, e, d, Or.inl rfl⟩)) ?_
  rintro j' g fl V₁ ⟨hI1, gf, gbp, hj⟩ U t₁ hKU hAU hrU hgU -
  subst hgU
  have hmU := Fm.fr hm gf
  rcases hj with rfl | ⟨rfl, hnz, g13⟩
  · exact tail161 E hKU hAU hrU hmU (by rw [gbp]; exact hob) hI1
  · refine callK E hKU hAU hrU hmU.1 (lt_len (by decide)) (call_215 _) tgt_215 E.cA (E.k215 _ hI1) trivial ?_
    intro Z W' t₃ hKZ hAZ hrZ hsZ hkZ _ hIZ
    exact from220 E hKZ hAZ hrZ (fm_ret hmU hsZ hkZ) (by rw [hkZ.2.1, gbp]; exact hob) (by rw [← hn]; exact hnz)
      (by rw [hkZ.2.2.2.1, g13, hn]) hIZ

/-- From 123: `operator new (0x18)` (`k128`), from its return 133. -/
theorem from123 (E : Ev prof F Wl L s₀ o gev gP gE S g0 vb e₂ code₂ j₂ I Ok pp nn) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = ais_at.add 123) (hm : Fm S g0 vb Y.cpu.gpr) (hIW : I W) :
    GoG prof L o gev gP gE Y t := by
  refine (c_123 prof).run E.c E.hin (fun j' g' _ V' => j' = 128 ∧ I V' ∧ Fr Y.cpu.gpr g') hK hA hr
    (vc_123 hIW fun _ V' hI e _ => ⟨rfl, hI, e⟩) ?_
  rintro j' g fl V₁ ⟨rfl, hI1, gf⟩ U t₁ hKU hAU hrU hgU -
  subst hgU
  have hmU := Fm.fr hm gf
  refine callK E hKU hAU hrU hmU.1 (lt_len (by decide)) (call_128 _) tgt_128 E.cN (E.k128 _ hI1) trivial ?_
  intro Z W' t₃ hKZ hAZ hrZ hsZ hkZ hB hIZ
  exact from133 E hKZ hAZ hrZ (fm_ret hmU hsZ hkZ) hB hIZ

/-- From 117: `_items`, `_capacity` stored, to 123. -/
theorem from117 (E : Ev prof F Wl L s₀ o gev gP gE S g0 vb e₂ code₂ j₂ I Ok pp nn) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = ais_at.add 117) (hm : Fm S g0 vb Y.cpu.gpr) (hIW : I W) :
    GoG prof L o gev gP gE Y t := by
  refine (c_117 prof).run E.c E.hin (fun j' g' _ V' => j' = 123 ∧ I V' ∧ Fr Y.cpu.gpr g') hK hA hr
    (vc_117 (by rw [hm.2.1]; exact E.hok _ _ E.hv.1) (by rw [hm.2.1]; exact E.hok _ _ E.hv.2.2.1)
      (by rw [hm.2.1]; exact E.hv.1) (by rw [hm.2.1]; exact E.hv.2.2.1) hIW E.hcl
      fun _ V' hI e _ => ⟨rfl, hI, e⟩) ?_
  rintro j' g fl V₁ ⟨rfl, hI1, gf⟩ U t₁ hKU hAU hrU hgU -
  subst hgU
  exact from123 E hKU hAU hrU (Fm.fr hm gf) hI1

/-- From 351 (back from `delete []`): `jmp` to 117. -/
theorem from351 (E : Ev prof F Wl L s₀ o gev gP gE S g0 vb e₂ code₂ j₂ I Ok pp nn) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = ais_at.add 351) (hm : Fm S g0 vb Y.cpu.gpr) (hIW : I W) :
    GoG prof L o gev gP gE Y t := by
  refine (c_351 prof).run E.c E.hin (fun j' g' _ V' => j' = 117 ∧ g' = Y.cpu.gpr ∧ V' = W)
    hK hA hr (vc_351 fun _ => ⟨rfl, rfl, rfl⟩) ?_
  rintro j' g fl V₁ ⟨rfl, rfl, hV₁⟩ U t₁ hKU hAU hrU hgU -
  subst V₁
  exact from117 E hKU hAU hrU (by rw [hgU]; exact hm) hIW

/-- From 343: `delete []` of the old array (`k346`), from its return 351. -/
theorem from343 (E : Ev prof F Wl L s₀ o gev gP gE S g0 vb e₂ code₂ j₂ I Ok pp nn) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = ais_at.add 343) (hm : Fm S g0 vb Y.cpu.gpr) (hIW : I W) :
    GoG prof L o gev gP gE Y t := by
  refine (c_343 prof).run E.c E.hin (fun j' g' _ V' => j' = 346 ∧ V' = W ∧ Fr Y.cpu.gpr g') hK hA hr
    (vc_343 fun _ e _ => ⟨rfl, rfl, e⟩) ?_
  rintro j' g fl V₁ ⟨rfl, hV₁, gf⟩ U t₁ hKU hAU hrU hgU -
  subst V₁ hgU
  have hmU := Fm.fr hm gf
  refine callK E hKU hAU hrU hmU.1 (lt_len (by decide)) (call_346 _) tgt_346 E.cD (E.k346 _ hIW) trivial ?_
  intro Z W' t₃ hKZ hAZ hrZ hsZ hkZ _ hIZ
  exact from351 E hKZ hAZ hrZ (fm_ret hmU hsZ hkZ) hIZ

/-- From 91 (back from `operator new []`): `memcpy` (`k338`) and from its return 343; or to 343; or to 117. -/
theorem from91 (E : Ev prof F Wl L s₀ o gev gP gE S g0 vb e₂ code₂ j₂ I Ok pp nn) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = ais_at.add 91) (hm : Fm S g0 vb Y.cpu.gpr) (hIW : I W) :
    GoG prof L o gev gP gE Y t := by
  refine (c_91 prof).run E.c E.hin (fun j' g' _ V' => V' = W ∧ Fr Y.cpu.gpr g' ∧
      (j' = 338 ∨ j' = 343 ∨ j' = 117)) hK hA hr
    (vc_91 (by rw [hm.2.1]; exact E.fd E.hv.2.1) (by rw [hm.2.1]; exact E.fd E.hv.1)
      (fun _ e _ => ⟨rfl, e, Or.inl rfl⟩) (fun _ e _ => ⟨rfl, e, Or.inr (Or.inl rfl)⟩)
      (fun _ e _ => ⟨rfl, e, Or.inr (Or.inr rfl)⟩)) ?_
  rintro j' g fl V₁ ⟨hV₁, gf, hj⟩ U t₁ hKU hAU hrU hgU -
  subst V₁ hgU
  have hmU := Fm.fr hm gf
  rcases hj with rfl | rfl | rfl
  · refine callK E hKU hAU hrU hmU.1 (lt_len (by decide)) (call_338 _) tgt_338 E.cM (E.k338 _ hIW) trivial ?_
    intro Z W' t₃ hKZ hAZ hrZ hsZ hkZ _ hIZ
    exact from343 E hKZ hAZ hrZ (fm_ret hmU hsZ hkZ) hIZ
  · exact from343 E hKU hAU hrU hmU hIW
  · exact from117 E hKU hAU hrU hmU hIW

/-- From 55 (the `ja` not taken): the new capacity, `operator new []` (`k86`), from its return 91. -/
theorem from55 (E : Ev prof F Wl L s₀ o gev gP gE S g0 vb e₂ code₂ j₂ I Ok pp nn) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = ais_at.add 55) (hm : Fm S g0 vb Y.cpu.gpr) (hIW : I W) :
    GoG prof L o gev gP gE Y t := by
  refine (c_55 prof).run E.c E.hin (fun j' g' _ V' => j' = 86 ∧ V' = W ∧ Fr Y.cpu.gpr g') hK hA hr
    (vc_55 fun _ e _ => ⟨rfl, rfl, e⟩) ?_
  rintro j' g fl V₁ ⟨rfl, hV₁, gf⟩ U t₁ hKU hAU hrU hgU -
  subst V₁ hgU
  have hmU := Fm.fr hm gf
  refine callK E hKU hAU hrU hmU.1 (lt_len (by decide)) (call_86 _) tgt_86 E.cA (E.k86 _ hIW) trivial ?_
  intro Z W' t₃ hKZ hAZ hrZ hsZ hkZ _ hIZ
  exact from91 E hKZ hAZ hrZ (fm_ret hmU hsZ hkZ) hIZ

end Runs

variable {prof : Profile} {F : Footprint} {Wl : List Rgn} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {X : State} {t : Nat} {V : Addr → Byte}

/-- `NWildcard::CCensorNode::AddItemSimple (include, item)` (`this` = `rdi`, `include` = `sil`, `item` = `rdx`) from
its entry, `I` an invariant of the bytes kept by the stores `Ok` allows (`hcl`, `hok`) and by the store of the stack
slot `aR S + 8` (`hcs`), which those stores leave (`hfr`): the pushes' slots, the calls' return address slot and the
stack slot in what the run may store into (the stack slot not wrapping, `hnw`), the return address readable; for
either vector (`hV`) `Ok` for its `_items`, `_size`, `_capacity` and the slot `_items[_size]` (`Vk`); `item`'s
`PathParts._items`, `_size` and flags word readable (`fi0`, `fi8`, `fi16`), `PathParts` as `I` says (`hpp`), its
first `nn` slots readable (`fpp`). `I` holds after the pushes (`hI0`) and gives the stack (`hI`). The throw (`kt`),
and the callees, each from its return with `rsp` as it was, the callee-saved registers as at its entry and `I`:
`operator new []` (`k86`, `k215`), `memcpy` (`k338`), `delete []` (`k346`), `operator new (0x18)` (`k128`, giving
back the new item's fields in `Ok`, `Ob`); in the loop `operator new (0x10)` (`k269`) and the `UString` copy
(`k283`), also leaving the stack slot. At the return address (`kr`): `rsp` 8 above the entry's, the callee-saved
registers as they were, bytes with `I`. -/
theorem ais_ok {I : (Addr → Byte) → Prop} {Ok : Addr → Nat → Prop} {e₂ : Addr} {code₂ : List Byte} {j₂ : Nat}
    {pp : Addr} {nn : BitVec 32}
    (c : Seg prof F Wl L s₀ o) (hin : CodeIn L ais_at ais)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = ais_at)
    (hs1 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8) i))
    (hs2 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8 - 8) i))
    (hs3 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8 - 8 - 8) i))
    (hs4 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8 - 8 - 8 - 8) i))
    (hs5 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8 - 8 - 8 - 8 - 8) i))
    (hs6 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8 - 8 - 8 - 8 - 8 - 8) i))
    (hr8 : ∀ i < 8, Foot Wl (Addr.add (aR X.cpu.gpr.rsp - 8) i))
    (ws8 : ∀ i < 8, Foot Wl (Addr.add (aR X.cpu.gpr.rsp + 8#64) i))
    (hnw : (aR X.cpu.gpr.rsp + 8#64).toNat + 8 ≤ 2 ^ 64)
    (hl : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsp i))
    (hin₂ : CodeIn L e₂ code₂) (h₂ : j₂ < code₂.length)
    (hok : ∀ a n, Ok a n → ∀ i < n, Foot Wl (Addr.add a i))
    (hcl : ∀ (W : Addr → Byte) (a : Addr) (n : Nat) (bs : List Byte), bs.length = n → Ok a n → I W →
      I (Vst W a bs))
    (hcs : ∀ (W : Addr → Byte) (bs : List Byte), bs.length = 8 → I W → I (Vst W (aR X.cpu.gpr.rsp + 8#64) bs))
    (hfr : ∀ (W : Addr → Byte) (a : Addr) (n : Nat) (bs : List Byte), bs.length = n → Ok a n →
      rdq(Vst W a bs, aR X.cpu.gpr.rsp + 8#64) = rdq(W, aR X.cpu.gpr.rsp + 8#64))
    (hV : ∀ vb, (vb = X.cpu.gpr.rdi + 40#64 ∨ vb = X.cpu.gpr.rdi + 56#64) → Vk I Ok vb)
    (fi0 : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rdx i))
    (fi8 : ∀ i < 4, Foot F.data (Addr.add (X.cpu.gpr.rdx + 8#64) i))
    (fi16 : ∀ i < 4, Foot F.data (Addr.add (X.cpu.gpr.rdx + 16#64) i))
    (hpp : ∀ W, I W → rdq(W, X.cpu.gpr.rdx) = pp ∧ rdd(W, X.cpu.gpr.rdx + 8#64) = nn)
    (fpp : ∀ k < nn.toNat, ∀ i < 8, Foot F.data (Addr.add (pp + BitVec.ofNat 64 (8 * k)) i))
    (hI : ∀ W, I W → Stk W X.cpu.gpr.rsp X.cpu.gpr (e₂.add j₂)) (hI0 : I (P6 V X.cpu.gpr))
    {codeT : List Byte} (hinT : CodeIn L 0x40180a#64 codeT) (hT : 0 < codeT.length)
    (cA : ∃ code : List Byte, CodeIn L 0x6029b0#64 code ∧ 0 < code.length)
    (cN : ∃ code : List Byte, CodeIn L 0x602970#64 code ∧ 0 < code.length)
    (cU : ∃ code : List Byte, CodeIn L 0x44d5d0#64 code ∧ 0 < code.length)
    (cM : ∃ code : List Byte, CodeIn L 0x401070#64 code ∧ 0 < code.length)
    (cD : ∃ code : List Byte, CodeIn L 0x6014f0#64 code ∧ 0 < code.length)
    (k86 : ∀ W, I W → KC prof F Wl L s₀ o gev gP gE X.cpu.gpr.rsp I 0x6029b0#64 91 W (fun _ => True)
      (fun _ => True))
    (k128 : ∀ W, I W → KC prof F Wl L s₀ o gev gP gE X.cpu.gpr.rsp I 0x602970#64 133 W (fun _ => True)
      (fun g => Ob I Ok g.rax))
    (k215 : ∀ W, I W → KC prof F Wl L s₀ o gev gP gE X.cpu.gpr.rsp I 0x6029b0#64 220 W (fun _ => True)
      (fun _ => True))
    (k269 : ∀ M W, I W → rdq(W, aR X.cpu.gpr.rsp + 8#64) = M → KC prof F Wl L s₀ o gev gP gE X.cpu.gpr.rsp
      (fun W' => I W' ∧ rdq(W', aR X.cpu.gpr.rsp + 8#64) = M) 0x602970#64 274 W (fun _ => True) (fun _ => True))
    (k283 : ∀ M W, I W → rdq(W, aR X.cpu.gpr.rsp + 8#64) = M → KC prof F Wl L s₀ o gev gP gE X.cpu.gpr.rsp
      (fun W' => I W' ∧ rdq(W', aR X.cpu.gpr.rsp + 8#64) = M) 0x44d5d0#64 288 W (fun _ => True) (fun _ => True))
    (k338 : ∀ W, I W → KC prof F Wl L s₀ o gev gP gE X.cpu.gpr.rsp I 0x401070#64 343 W (fun _ => True)
      (fun _ => True))
    (k346 : ∀ W, I W → KC prof F Wl L s₀ o gev gP gE X.cpu.gpr.rsp I 0x6014f0#64 351 W (fun _ => True)
      (fun _ => True))
    (kt : ∀ W, I W → ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y → Agree F Y.proc.mm.mem W →
      Y.cpu.rip = 0x40180a#64 → Y.cpu.gpr.rsp = aR X.cpu.gpr.rsp → GoG prof L o gev gP gE Y t')
    (kr : ∀ (W : Addr → Byte) (Z' : State) (t' : Nat), KeptW Wl s₀ Z' → Agree F Z'.proc.mm.mem W →
      Z'.cpu.rip = e₂.add j₂ → Z'.cpu.gpr.rsp = X.cpu.gpr.rsp + 8 → KS X.cpu.gpr Z'.cpu.gpr → I W →
      GoG prof L o gev gP gE Z' t') :
    GoG prof L o gev gP gE X t := by
  -- the prologue, to 123 or to the `ja`
  refine (c_0 prof).run c hin (fun j' g' _ V' => V' = P6 V X.cpu.gpr ∧ g'.rsp = aR X.cpu.gpr.rsp ∧
      (g'.rbx = X.cpu.gpr.rdi + 40#64 ∨ g'.rbx = X.cpu.gpr.rdi + 56#64) ∧ g'.r12 = X.cpu.gpr.rdx ∧
      (j' = 123 ∨ j' = 49)) hK hA (by rw [addr_add_zero]; exact hrip)
    (vc_0 hs1 hs2 hs3 hs4 hs5 hs6
      (fun vb h => ⟨fun i hi => c.hws _ (hok _ _ (hV vb h).2.2.1 i hi),
        fun i hi => c.hws _ (hok _ _ (hV vb h).2.1 i hi)⟩)
      (fun _ a b d _ => ⟨rfl, a, b, d, Or.inl rfl⟩) (fun _ a b d _ => ⟨rfl, a, b, d, Or.inr rfl⟩)) ?_
  rintro j' g fl V₁ ⟨hV₁, hsY, hbY, h12Y, hj⟩ Y t₁ hKY hAY hrY hgY -
  subst V₁ hgY
  obtain ⟨vb, hvb⟩ : ∃ vb, Y.cpu.gpr.rbx = vb := ⟨_, rfl⟩
  have hmY : Fm X.cpu.gpr.rsp X.cpu.gpr vb Y.cpu.gpr := ⟨hsY, hvb, h12Y⟩
  have E : Ev prof F Wl L s₀ o gev gP gE X.cpu.gpr.rsp X.cpu.gpr vb e₂ code₂ j₂ I Ok pp nn :=
    { c := c, hin := hin, hin₂ := hin₂, h₂ := h₂, hI := hI, hok := hok, hcl := hcl, hcs := hcs, hfr := hfr,
      hrd := fun W v => by
        rw [Tun.rd_Vst_self _ _ _ (toBytesLE_length _ _) hnw]; exact ofBytesLE_toBytesLE (n := 8) rfl v,
      ws8 := ws8, fs8 := fun i hi => c.hws _ (ws8 i hi),
      hv := hV vb (by rw [← hvb]; exact hbY), fi0 := fi0, fi8 := fi8, fi16 := fi16, hpp := hpp, fpp := fpp,
      fb48 := fun i hi => c.hws _ (hs6 i hi), fb40 := fun i hi => c.hws _ (hs5 i hi),
      fb32 := fun i hi => c.hws _ (hs4 i hi), fb24 := fun i hi => c.hws _ (hs3 i hi),
      fb16 := fun i hi => c.hws _ (hs2 i hi), fb8 := fun i hi => c.hws _ (hs1 i hi), hl := hl, hr8 := hr8,
      cA := cA, cN := cN, cU := cU, cM := cM, cD := cD,
      k86 := k86, k128 := k128, k215 := k215, k269 := k269, k283 := k283, k338 := k338, k346 := k346, kr := kr }
  rcases hj with rfl | rfl
  · exact from123 E hKY hAY hrY hmY hI0
  · refine c.s_jcc_x hKY hAY hin (lt_len (by decide)) hrY (ja_49 _) hinT hT (tgt := 0) (by decide) ?_ ?_
    · -- the throw
      intro _ Y₁ t₂ hK₁ hA₁ ⟨hr₁, hg₁⟩
      exact kt _ hI0 Y₁ t₂ hK₁ hA₁ (by rw [hr₁, addr_add_zero]) (by rw [hg₁]; exact hsY)
    · intro _ Y₁ t₂ hK₁ hA₁ ⟨hr₁, hg₁⟩
      exact from55 E hK₁ hA₁ hr₁ (by rw [hg₁]; exact hmY) hI0

end FV7z.Ais
