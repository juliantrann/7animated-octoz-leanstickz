import FV7z.Cpr.Holds
import FV7z.Lemmas.Fr40
/-!
# `NWildcard::CCensorNode::CheckPathToRoot` (PLAN.md §M, M1): the run from 425

The run of `CheckPathToRoot` from 425 (`pathParts._size` = `m` not 0, the local `pathParts2` with `x` items after
the first append): `js` (425, `x` negative) and `ja` (434, `m` above `0x7fffffff - x`) to the throw at `0x4019da`
(`kth`); (440) `x + m` above `_capacity` (`aR S + 44`) to the growth: (560) the new capacity `c` stored at `aR S + 8`,
`operator new [] (8 c)` (593, `0x6029b0`), its result `r` in `r12`; (598) `_size` not 0: the old `_items` saved at
`aR S + 16`, `memcpy (r, _items, 8 _size)` (659, `0x401070`), (664) `rdi` = the saved `_items`; else `_items` not null
(614) to 669; (669) `operator delete [] (_items)` (672, `0x6014f0`), (677) to 619; (619) `_items` = `r`, `_capacity`
= `c`, to 450. (450) the end offset `8 m` stored at `aR S + 16`, `aR S + 32` at `aR S + 24`, `r15` = 0; the copy
loop (480..553, `r15` = `8 i`): `pathParts._items[i]` stored at `aR S + 8`, `operator new (0x10)` (503), the `UString`
copy of the item into it (519, `0x44d5d0`), the append (524, as at 188: `St188`), `r15` + 8 against the end offset:
not equal back to 480, else (555) to 221 (`Cpr.from221`).

The bytes are tracked by invariants the caller chooses (`Lh`), each tied to the stores the code makes, as in
`Cpr.Ev`: `Q4 m x` at 425 (from `Ev.z425`); `Hg m` at 450 (`hQ`, or after the growth `z619`); `Gc m` after the store
at 560 (`z560`), `Gr m r` after `operator new []` (`k593`), `Gm m r` after `memcpy` (`k659`), `Go m r p` before
`operator delete [] (p)` (`z614`, `z664`), `Gf m r` after it (`k672`, or `zf0` when there is nothing to free); in the
loop `G m i` at 480 (`z450` for `i` = 0), `G1 m i` after the item's store (`z480`), `G2 m i r` after `operator new`
(`k503`), `G3 m i r` after the copy (`k519`), the end offset read back after the append (`hL`), and after it
`G m (i + 1)` or, at the last item, `Ev`'s `P` (`zst`). No byte of the frame is read back by this module: what a
slot holds is what the invariants say.

- `tjs_425`, `tja_434`: the throws' target; `eq_c5`: `je` taken after `cmp`; `l450`: the end offset `8 m`; `sS`:
  `r15` + 8; `ne8`: offsets of different items differ; `ap32`: `_items` apart from `_size`; `Sx`: the bytes after the
  append at 524.
- `vc_431`, `vc_440`, `vc_450`, `vc_480`, `vc_508`, `vc_524`, `vc_598`, `vc_619`, `vc_664`, `vc_669`, `vc_677`: the
  pieces.
- `Lh`: the hypotheses of the run from 425; `P480`: what holds at 480 at the step `i`; `S480`: one step of the loop,
  `L480`: the loop (induction on the steps left); `from450`, `from619`, `from669`, `from664`, `from598`, `from440`,
  `from431`, `from425`: the runs from the cut points.
- `cpr_full`: `Cpr.cpr_ok` with the run from 425 discharged by `from425`.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
open FV7z.Api (P6 Stk KS)
open FV7z.Ais (nz32 ne_c5)
open FV7z.Ocv (pk)
namespace FV7z.Cpr
set_option linter.unusedVariables false

/-! ## Values -/

theorem tjs_425 : cpr_at.add (425 + 6) + BitVec.ofNat 64 18446744073709212923 = (0x4019da#64 : Addr).add 0 := by
  decide
theorem tja_434 : cpr_at.add (434 + 6) + BitVec.ofNat 64 18446744073709212914 = (0x4019da#64 : Addr).add 0 := by
  decide

/-- `je` taken after `cmp x, y` (`jne` not taken). -/
theorem eq_c5 {x y : BitVec 64} (h : (!decide (x = y)) = false) : x = y := by
  cases hd : decide (x = y)
  · rw [hd] at h
    exact absurd h (by decide)
  · exact of_decide_eq_true hd

/-- `lea eax, [r15 - 1]; lea rax, [rax * 8 + 8]` with `r15` the zero-extended `m` not 0: `8 m`. -/
theorem l450 {m : BitVec 32} (h : m ≠ 0) :
    BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.setWidth 64 m + 18446744073709551615#64)) * 8#64 + 8#64 =
      BitVec.ofNat 64 (8 * m.toNat) := by
  have h1 : m.toNat ≠ 0 := fun e => h (BitVec.eq_of_toNat_eq (e.trans rfl))
  have h2 : m.toNat < 4294967296 := m.isLt
  have l64 : 4294967296 ≤ 2 ^ 64 := by decide
  have eA : (BitVec.setWidth 64 m).toNat = m.toNat := by
    rw [BitVec.toNat_setWidth]
    exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le h2 l64)
  have eB : (BitVec.setWidth 64 m + 18446744073709551615#64).toNat = m.toNat - 1 := by
    rw [BitVec.toNat_add, eA, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (a := 18446744073709551615) (b := 2 ^ 64) (by decide)]
    have e : m.toNat + 18446744073709551615 = (m.toNat - 1) + 2 ^ 64 := by
      rw [show (2 : Nat) ^ 64 = 18446744073709551616 from rfl]
      omega
    rw [e, Nat.add_mod_right]
    exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.sub_le _ _) (Nat.lt_of_lt_of_le h2 l64))
  have eC : (BitVec.setWidth 32 (BitVec.setWidth 64 m + 18446744073709551615#64)).toNat = m.toNat - 1 := by
    rw [BitVec.toNat_setWidth, eB]
    exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.sub_le _ _) h2)
  have eD : (BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.setWidth 64 m + 18446744073709551615#64))).toNat =
      m.toNat - 1 := by
    rw [BitVec.toNat_setWidth, eC]
    exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.sub_le _ _) (Nat.lt_of_lt_of_le h2 l64))
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_mul, eD]
  simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
  omega

/-- `add r15, 8` at the step `i`. -/
theorem sS (i : Nat) : BitVec.ofNat 64 (8 * i) + 8#64 = BitVec.ofNat 64 (8 * (i + 1)) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
  omega

/-- The offsets of different items (below `2 ^ 32`) differ. -/
theorem ne8 (a b : Nat) (ha : a < 4294967296) (hb : b < 4294967296) (h : a ≠ b) :
    BitVec.ofNat 64 (8 * a) ≠ BitVec.ofNat 64 (8 * b) := by
  intro e
  have e' := congrArg BitVec.toNat e
  simp only [BitVec.toNat_ofNat, Nat.reducePow] at e'
  omega

/-- `_items` (8 bytes at `b + 32`) apart from `_size` (4 at `b + 40`). -/
theorem ap32 (b : Addr) : FV7z.Fr40.Ap (b + 32#64) (b + 40#64) 4 := by
  intro c hc i hi h
  simp only [Addr.add] at h
  bv_omega

/-- The bytes after the append at 524 (`x` the new `_size`, `r` the copy): as `St188` for `x` = `_size + 1`. -/
abbrev Sx (V : Addr → Byte) (a : Addr) (x : BitVec 32) (r : BitVec 64) : Addr → Byte :=
  Vst (Vst V (a + 40#64) (toBytesLE x 4)) (rdq(V, a + 32#64) + BitVec.setWidth 64 rdd(V, a + 40#64) * 8#64)
    (toBytesLE r 8)

/-! ## The pieces -/

section Pieces
variable {F : Footprint} {Wl : List Rgn}

/-- `cmp r15d, eax`: to the `ja` at 434. -/
theorem vc_431 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (h : ∀ g', Fr g g' → g'.r15 = g.r15 → ∀ fl, Q 434 g' fl V) :
    W_431 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h ⊢
  wpx [W_431, o24]
  all_goals repeat' (first
    | refine h _ ?_ ?_ _
    | with_reducible rfl
    | apply And.intro
    | intro _)

/-- `x + m` against `_capacity`: above to the growth (the new capacity stored at `rsp + 8`), to 593; else to 450. -/
theorem vc_440 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (f44 : ∀ i < 4, Foot F.data (Addr.add (g.rsp + 44#64) i))
    (w8 : ∀ i < 4, Foot Wl (Addr.add (g.rsp + 8#64) i))
    (h593 : ∀ g' (c : BitVec 32), Fr g g' → g'.r15 = g.r15 →
      ∀ fl, Q 593 g' fl (Vst V (g.rsp + 8#64) (toBytesLE c 4)))
    (h450 : ∀ g', Fr g g' → g'.r15 = g.r15 → ∀ fl, Q 450 g' fl V) :
    W_440 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at f44 w8 h593 h450 ⊢
  wpx [W_440, W_560, o25, o30, Op.shl64]
  all_goals repeat' (first
    | refine h593 _ _ ?_ ?_ _
    | refine h450 _ ?_ ?_ _
    | with_reducible rfl
    | with_reducible exact f44
    | with_reducible exact w8
    | apply And.intro
    | intro _)

/-- The end offset (`8 (m - 1) + 8`) at `rsp + 16`, `rsp + 32` at `rsp + 24`, `r15` = 0: to 480. -/
theorem vc_450 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (w16 : ∀ i < 8, Foot Wl (Addr.add (g.rsp + 16#64) i))
    (w24 : ∀ i < 8, Foot Wl (Addr.add (g.rsp + 24#64) i))
    (h : ∀ g', Fr g g' → g'.r15 = 0#64 → ∀ fl, Q 480 g' fl (Vst (Vst V (g.rsp + 16#64)
      (toBytesLE (BitVec.setWidth 64 (BitVec.setWidth 32 (g.r15 + 18446744073709551615#64)) * 8#64 + 8#64) 8))
      (g.rsp + 24#64) (toBytesLE (g.rsp + 32#64) 8))) :
    W_450 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at w16 w24 h ⊢
  wpx [W_450, o26, BitVec.xor_self, BitVec.setWidth_zero, BitVec.reduceSetWidth]
  all_goals repeat' (first
    | refine h _ ?_ ?_ _
    | with_reducible rfl
    | exact rfl
    | with_reducible exact w16
    | with_reducible exact w24
    | apply And.intro
    | intro _)

/-- The item (`_items` at `rbp`, the offset `r15`) at `rsp + 8`, `edi` = 16: to `operator new` (503). -/
theorem vc_480 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (fb0 : ∀ i < 8, Foot F.data (Addr.add g.rbp i))
    (f24 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 24#64) i))
    (fit : ∀ i < 8, Foot F.data (Addr.add (rdq(V, g.rbp) + g.r15) i))
    (w8 : ∀ i < 8, Foot Wl (Addr.add (g.rsp + 8#64) i))
    (h : ∀ g', Fr g g' → g'.rdi = 16#64 → g'.r15 = g.r15 → ∀ fl, Q 503 g' fl
      (Vst V (g.rsp + 8#64) (toBytesLE rdq(V, rdq(V, g.rbp) + g.r15) 8))) :
    W_480 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at fb0 f24 fit w8 h ⊢
  wpx [W_480, o27, BitVec.reduceSetWidth]
  all_goals repeat' (first
    | refine h _ ?_ ?_ ?_ _
    | with_reducible rfl
    | exact rfl
    | with_reducible exact fb0
    | with_reducible exact f24
    | with_reducible exact fit
    | with_reducible exact w8
    | apply And.intro
    | intro _)

/-- `rdi` = `r12` = the new object, `rsi` = the item: to its copy (519). -/
theorem vc_508 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (f8 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8#64) i))
    (h : ∀ g', Fr g g' → g'.rdi = g.rax → g'.rsi = rdq(V, g.rsp + 8#64) → g'.r12 = g.rax → g'.r15 = g.r15 →
      ∀ fl, Q 519 g' fl V) :
    W_508 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at f8 h ⊢
  wpx [W_508, o28]
  all_goals repeat' (first
    | refine h _ ?_ ?_ ?_ ?_ ?_ _
    | with_reducible rfl
    | with_reducible exact f8
    | apply And.intro
    | intro _)

/-- The append (`_size` + 1 as `x`, `_items[_size]` = `r12`), `r15` + 8 against the end offset: not equal to 480,
else to 221. -/
theorem vc_524 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (f40 : ∀ i < 4, Foot F.data (Addr.add (g.rsp + 40#64) i))
    (f32 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 32#64) i))
    (f16 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 16#64) i))
    (w40 : ∀ i < 4, Foot Wl (Addr.add (g.rsp + 40#64) i))
    (e32 : ∀ x : BitVec 32, rdq(Vst V (g.rsp + 40#64) (toBytesLE x 4), g.rsp + 32#64) = rdq(V, g.rsp + 32#64))
    (wsl : ∀ i < 8, Foot Wl (Addr.add (rdq(V, g.rsp + 32#64) + BitVec.setWidth 64 rdd(V, g.rsp + 40#64) * 8#64) i))
    (h480 : ∀ g' (x : BitVec 32), x = rdd(V, g.rsp + 40#64) + 1#32 → Fr g g' → g'.r15 = g.r15 + 8#64 →
      rdq(Sx V g.rsp x g.r12, g.rsp + 16#64) ≠ g.r15 + 8#64 → ∀ fl, Q 480 g' fl (Sx V g.rsp x g.r12))
    (h221 : ∀ g' (x : BitVec 32), x = rdd(V, g.rsp + 40#64) + 1#32 → Fr g g' → g'.r15 = g.r15 + 8#64 →
      rdq(Sx V g.rsp x g.r12, g.rsp + 16#64) = g.r15 + 8#64 → ∀ fl, Q 221 g' fl (Sx V g.rsp x g.r12)) :
    W_524 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at f40 f32 f16 w40 e32 wsl h480 h221 ⊢
  wpx [W_524, W_555, o29, Op.cmpmr, e32]
  all_goals repeat' (first
    | refine h480 _ _ ?_ ?_ ?_ ?_ _
    | refine h221 _ _ ?_ ?_ ?_ ?_ _
    | with_reducible rfl
    | exact inc32 _
    | exact ne_c5 ‹_›
    | exact eq_c5 ‹_›
    | with_reducible exact f40
    | with_reducible exact f32
    | with_reducible exact f16
    | with_reducible exact w40
    | with_reducible exact wsl
    | apply And.intro
    | intro _)

/-- Back from `operator new []` (`rax` the new array, to `r12`): `_size` not 0 to `memcpy` (659, the old `_items`
saved at `rsp + 16`); else `_items` not null to 669, null to 619. -/
theorem vc_598 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (f40 : ∀ i < 4, Foot F.data (Addr.add (g.rsp + 40#64) i))
    (f32 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 32#64) i))
    (w16 : ∀ i < 8, Foot Wl (Addr.add (g.rsp + 16#64) i))
    (h659 : ∀ g', Fr g g' → g'.r12 = g.rax → g'.r15 = g.r15 → g'.rdi = g.rax → g'.rsi = rdq(V, g.rsp + 32#64) →
      g'.rdx = BitVec.setWidth 64 rdd(V, g.rsp + 40#64) * 8#64 →
      ∀ fl, Q 659 g' fl (Vst V (g.rsp + 16#64) (toBytesLE rdq(V, g.rsp + 32#64) 8)))
    (h669 : ∀ g', Fr g g' → g'.r12 = g.rax → g'.r15 = g.r15 → g'.r8 = rdq(V, g.rsp + 32#64) →
      ∀ fl, Q 669 g' fl V)
    (h619 : ∀ g', Fr g g' → g'.r12 = g.rax → g'.r15 = g.r15 → ∀ fl, Q 619 g' fl V) :
    W_598 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at f40 f32 w16 h659 h669 h619 ⊢
  wpx [W_598, W_640, W_614, o31, o33, o5]
  all_goals repeat' (first
    | refine h659 _ ?_ ?_ ?_ ?_ ?_ ?_ _
    | refine h669 _ ?_ ?_ ?_ ?_ _
    | refine h619 _ ?_ ?_ ?_ _
    | with_reducible rfl
    | exact rfl
    | with_reducible exact f40
    | with_reducible exact f32
    | with_reducible exact w16
    | apply And.intro
    | intro _)

/-- `_items` = `r12`, `_capacity` = the new capacity (at `rsp + 8`): to 450. -/
theorem vc_619 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (f8 : ∀ i < 4, Foot F.data (Addr.add (g.rsp + 8#64) i))
    (w32 : ∀ i < 8, Foot Wl (Addr.add (g.rsp + 32#64) i))
    (w44 : ∀ i < 4, Foot Wl (Addr.add (g.rsp + 44#64) i))
    (h : ∀ g', Fr g g' → g'.r15 = g.r15 → ∀ fl, Q 450 g' fl
      (Vst (Vst V (g.rsp + 32#64) (toBytesLE g.r12 8)) (g.rsp + 44#64) (toBytesLE rdd(V, g.rsp + 8#64) 4))) :
    W_619 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at f8 w32 w44 h ⊢
  wpx [W_619, o32]
  all_goals repeat' (first
    | refine h _ ?_ ?_ _
    | with_reducible rfl
    | with_reducible exact f8
    | with_reducible exact w32
    | with_reducible exact w44
    | apply And.intro
    | intro _)

/-- Back from `memcpy`: `r8` = the saved `_items`, to 669. -/
theorem vc_664 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (f16 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 16#64) i))
    (h : ∀ g', Fr g g' → g'.r12 = g.r12 → g'.r15 = g.r15 → g'.r8 = rdq(V, g.rsp + 16#64) → ∀ fl, Q 669 g' fl V) :
    W_664 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at f16 h ⊢
  wpx [W_664, o34]
  all_goals repeat' (first
    | refine h _ ?_ ?_ ?_ ?_ _
    | with_reducible rfl
    | with_reducible exact f16
    | apply And.intro
    | intro _)

/-- `rdi` = `r8`: to `operator delete []` (672). -/
theorem vc_669 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (h : ∀ g', Fr g g' → g'.r12 = g.r12 → g'.r15 = g.r15 → g'.rdi = g.r8 → ∀ fl, Q 672 g' fl V) :
    W_669 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h ⊢
  wpx [W_669, o22]
  all_goals repeat' (first
    | refine h _ ?_ ?_ ?_ ?_ _
    | with_reducible rfl
    | apply And.intro
    | intro _)

/-- Back from `operator delete []`: to 619. -/
theorem vc_677 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} (h : ∀ fl, Q 619 g fl V) :
    W_677 fb F Wl Q g f V :=
  h _

end Pieces

/-! ## The runs -/

/-- The hypotheses of the run from 425 (`S`, `g0` the entry's stack pointer and registers, `P` and `Q4` as in `Ev`,
`Hg`, `Gc`, `Gr`, `Gm`, `Go`, `Gf`, `G`, `G1`, `G2`, `G3` the invariants of the bytes). -/
structure Lh (prof : Profile) (F : Footprint) (Wl : List Rgn) (L : List (Addr × List Byte)) (s₀ : State)
    (o : Oracle) (gev : List Event) (gP : State → Nat → List Event → Prop) (gE : Outcome → List Event → Prop)
    (S : Addr) (g0 : Gprs) (P : (Addr → Byte) → Prop) (Q4 : BitVec 32 → BitVec 32 → (Addr → Byte) → Prop)
    (Hg Gc : BitVec 32 → (Addr → Byte) → Prop) (Gr Gm Gf : BitVec 32 → BitVec 64 → (Addr → Byte) → Prop)
    (Go : BitVec 32 → BitVec 64 → BitVec 64 → (Addr → Byte) → Prop) (G G1 : BitVec 32 → Nat → (Addr → Byte) → Prop)
    (G2 G3 : BitVec 32 → Nat → BitVec 64 → (Addr → Byte) → Prop) : Prop where
  w8 : ∀ i < 8, Foot Wl (Addr.add (aR S + 8#64) i)
  w16 : ∀ i < 8, Foot Wl (Addr.add (aR S + 16#64) i)
  w24 : ∀ i < 8, Foot Wl (Addr.add (aR S + 24#64) i)
  fpp : ∀ i < 8, Foot F.data (Addr.add g0.rdx i)
  cM : ∃ code : List Byte, CodeIn L 0x401070#64 code ∧ 0 < code.length
  cT : ∃ code : List Byte, CodeIn L 0x4019da#64 code ∧ 0 < code.length
  kth : ∀ m x W, Q4 m x W → ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y → Agree F Y.proc.mm.mem W →
    Y.cpu.rip = 0x4019da#64 → Y.cpu.gpr.rsp = aR S → GoG prof L o gev gP gE Y t'
  hQm : ∀ m x W, Q4 m x W → m ≠ 0
  hQ : ∀ m x W, Q4 m x W → Hg m W
  z560 : ∀ m x W, Q4 m x W → ∀ c : BitVec 32, Gc m (Vst W (aR S + 8#64) (toBytesLE c 4))
  k593 : ∀ m W, Gc m W → KC prof F Wl L s₀ o gev gP gE S 0x6029b0#64 598 W (fun _ => True)
    (fun g W' => Gr m g.rax W')
  k659 : ∀ m r W, Gr m r W → KC prof F Wl L s₀ o gev gP gE S 0x401070#64 664
    (Vst W (aR S + 16#64) (toBytesLE rdq(W, aR S + 32#64) 8))
    (fun g => g.rdi = r ∧ g.rsi = rdq(W, aR S + 32#64) ∧ g.rdx = BitVec.setWidth 64 rdd(W, aR S + 40#64) * 8#64)
    (fun _ => Gm m r)
  z664 : ∀ m r W, Gm m r W → Go m r rdq(W, aR S + 16#64) W
  z614 : ∀ m r W, Gr m r W → Go m r rdq(W, aR S + 32#64) W
  k672 : ∀ m r p W, Go m r p W → KC prof F Wl L s₀ o gev gP gE S 0x6014f0#64 677 W (fun g => g.rdi = p)
    (fun _ => Gf m r)
  zf0 : ∀ m r W, Gr m r W → Gf m r W
  z619 : ∀ m r W, Gf m r W →
    Hg m (Vst (Vst W (aR S + 32#64) (toBytesLE r 8)) (aR S + 44#64) (toBytesLE rdd(W, aR S + 8#64) 4))
  z450 : ∀ m W, Hg m W → G m 0 (Vst (Vst W (aR S + 16#64) (toBytesLE (BitVec.ofNat 64 (8 * m.toNat)) 8))
    (aR S + 24#64) (toBytesLE (aR S + 32#64) 8))
  fi : ∀ m i W, G m i W → ∀ j < 8, Foot F.data (Addr.add (rdq(W, g0.rdx) + BitVec.ofNat 64 (8 * i)) j)
  z480 : ∀ m i W, G m i W →
    G1 m i (Vst W (aR S + 8#64) (toBytesLE rdq(W, rdq(W, g0.rdx) + BitVec.ofNat 64 (8 * i)) 8))
  k503 : ∀ m i W, G1 m i W → KC prof F Wl L s₀ o gev gP gE S 0x602970#64 508 W (fun g => g.rdi = 16#64)
    (fun g W' => G2 m i g.rax W')
  k519 : ∀ m i r W, G2 m i r W → KC prof F Wl L s₀ o gev gP gE S 0x44d5d0#64 524 W
    (fun g => g.rdi = r ∧ g.rsi = rdq(W, aR S + 8#64)) (fun _ => G3 m i r)
  wsl : ∀ m i r W, G3 m i r W →
    ∀ j < 8, Foot Wl (Addr.add (rdq(W, aR S + 32#64) + BitVec.setWidth 64 rdd(W, aR S + 40#64) * 8#64) j)
  hL : ∀ m i r W, G3 m i r W → rdq(St188 S r W, aR S + 16#64) = BitVec.ofNat 64 (8 * m.toNat)
  zst : ∀ m i r W, G3 m i r W →
    (i + 1 < m.toNat → G m (i + 1) (St188 S r W)) ∧ (i + 1 = m.toNat → P (St188 S r W))

/-- At 480 at the step `i` of `m`: the frame, `r15` = `8 i`, the bytes with `G m i`. -/
abbrev P480 (S : Addr) (g0 : Gprs) (G : BitVec 32 → Nat → (Addr → Byte) → Prop) (m : BitVec 32) (i : Nat) :
    Gprs → (Addr → Byte) → Prop := fun g W => Fm S g0 g ∧ g.r15 = BitVec.ofNat 64 (8 * i) ∧ G m i W

section Runs
variable {prof : Profile} {F : Footprint} {Wl : List Rgn} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {fb S : Addr} {g0 : Gprs} {e₂ : Addr} {code₂ : List Byte} {j₂ : Nat}
  {I0 I1 I3 : (Addr → Byte) → Prop} {I2 : Gprs → (Addr → Byte) → Prop} {I4 I5 : BitVec 64 → (Addr → Byte) → Prop}
  {P : (Addr → Byte) → Prop} {Q4 : BitVec 32 → BitVec 32 → (Addr → Byte) → Prop}
  {D : BitVec 64 → Nat → (Addr → Byte) → Prop} {Jd : BitVec 64 → Nat → BitVec 64 → (Addr → Byte) → Prop}
  {Iz : (Addr → Byte) → Prop}
  {Hg Gc : BitVec 32 → (Addr → Byte) → Prop} {Gr Gm Gf : BitVec 32 → BitVec 64 → (Addr → Byte) → Prop}
  {Go : BitVec 32 → BitVec 64 → BitVec 64 → (Addr → Byte) → Prop} {G G1 : BitVec 32 → Nat → (Addr → Byte) → Prop}
  {G2 G3 : BitVec 32 → Nat → BitVec 64 → (Addr → Byte) → Prop}
  {Y : State} {t : Nat} {W : Addr → Byte}

/-- One step of the copy loop from 480 (`i + 1 ≤ m`): the item copied and appended, then the next step (`hn`) or,
at the last item, 221. -/
theorem S480 (E : Ev prof F Wl L s₀ o gev gP gE fb S g0 e₂ code₂ j₂ I0 I1 I3 I2 I4 I5 P Q4 D Jd Iz)
    (H : Lh prof F Wl L s₀ o gev gP gE S g0 P Q4 Hg Gc Gr Gm Gf Go G G1 G2 G3) (m : BitVec 32) (i : Nat)
    (hi : i + 1 ≤ m.toNat)
    (hn : i + 1 < m.toNat → AtJ prof F Wl L s₀ o gev gP gE 480 (P480 S g0 G m (i + 1))) :
    AtJ prof F Wl L s₀ o gev gP gE 480 (P480 S g0 G m i) := by
  rintro Y W t hK hA hr ⟨hm, h15, hG⟩
  have e8 : Y.cpu.gpr.rsp + 8#64 = aR S + 8#64 := by rw [hm.1]
  have e24 : Y.cpu.gpr.rsp + 24#64 = aR S + 24#64 := by rw [hm.1]
  have eit : rdq(W, Y.cpu.gpr.rbp) + Y.cpu.gpr.r15 = rdq(W, g0.rdx) + BitVec.ofNat 64 (8 * i) := by
    rw [hm.2.2, h15]
  refine (c_480 prof fb).run E.c E.hfs E.hin (fun j' g' _ V' => j' = 503 ∧
      V' = Vst W (aR S + 8#64) (toBytesLE rdq(W, rdq(W, g0.rdx) + BitVec.ofNat 64 (8 * i)) 8) ∧
      Fr Y.cpu.gpr g' ∧ g'.rdi = 16#64 ∧ g'.r15 = Y.cpu.gpr.r15) hK hA hr
    (vc_480 (by rw [hm.2.2]; exact H.fpp) (by rw [e24]; exact fun j hj => E.c.hws _ (H.w24 j hj))
      (by rw [eit]; exact H.fi m i W hG) (by rw [e8]; exact H.w8)
      fun _ a b d _ => ⟨rfl, by rw [e8, eit], a, b, d⟩) ?_
  rintro j' g fl V₁ ⟨rfl, rfl, gf, gdi, g15⟩ U t₁ hKU hAU hrU hgU -
  subst hgU
  have hmU := Fm.fr hm gf
  refine callK E hKU hAU hrU hmU.1 (lt_len (by decide)) (call_503 _) tgt_503 E.cN (H.k503 m i _ (H.z480 m i W hG))
    gdi ?_
  intro Z W' t₃ hKZ hAZ hrZ hsZ hkZ hIZ
  have hmZ := fm_ret hmU hsZ hkZ
  have h15Z : Z.cpu.gpr.r15 = BitVec.ofNat 64 (8 * i) := by rw [hkZ.2.2.2.2.2, g15, h15]
  refine (c_508 prof fb).run E.c E.hfs E.hin (fun j' g' _ V' => j' = 519 ∧ V' = W' ∧ Fr Z.cpu.gpr g' ∧
      g'.rdi = Z.cpu.gpr.rax ∧ g'.rsi = rdq(W', aR S + 8#64) ∧ g'.r12 = Z.cpu.gpr.rax ∧ g'.r15 = Z.cpu.gpr.r15)
    hKZ hAZ hrZ
    (vc_508 (by rw [hmZ.1]; exact fun j hj => E.c.hws _ (H.w8 j hj))
      fun _ a b d e k _ => ⟨rfl, rfl, a, b, by rw [d, hmZ.1], e, k⟩) ?_
  rintro j' g fl V₁ ⟨rfl, hV₁, gf2, gdi2, gsi2, g12, g15b⟩ U₂ t₄ hKU₂ hAU₂ hrU₂ hgU₂ -
  subst V₁ hgU₂
  have hmU₂ := Fm.fr hmZ gf2
  refine callK E hKU₂ hAU₂ hrU₂ hmU₂.1 (lt_len (by decide)) (call_519 _) tgt_519 E.cU (H.k519 m i _ _ hIZ)
    ⟨gdi2, gsi2⟩ ?_
  intro Z₂ W₂ t₅ hKZ₂ hAZ₂ hrZ₂ hsZ₂ hkZ₂ hIZ₂
  have hmZ₂ := fm_ret hmU₂ hsZ₂ hkZ₂
  have h12Z : Z₂.cpu.gpr.r12 = Z.cpu.gpr.rax := hkZ₂.2.2.1.trans g12
  have h15Z₂ : Z₂.cpu.gpr.r15 = BitVec.ofNat 64 (8 * i) := by rw [hkZ₂.2.2.2.2.2, g15b, h15Z]
  have e40 : Z₂.cpu.gpr.rsp + 40#64 = aR S + 40#64 := by rw [hmZ₂.1]
  have e32 : Z₂.cpu.gpr.rsp + 32#64 = aR S + 32#64 := by rw [hmZ₂.1]
  have e16 : Z₂.cpu.gpr.rsp + 16#64 = aR S + 16#64 := by rw [hmZ₂.1]
  have hsx : ∀ x, x = rdd(W₂, Z₂.cpu.gpr.rsp + 40#64) + 1#32 →
      Sx W₂ Z₂.cpu.gpr.rsp x Z₂.cpu.gpr.r12 = St188 S Z.cpu.gpr.rax W₂ := by
    intro x hx
    rw [hx, h12Z, hmZ₂.1]
  have hs1 : Z₂.cpu.gpr.r15 + 8#64 = BitVec.ofNat 64 (8 * (i + 1)) := by rw [h15Z₂]; exact sS i
  refine (c_524 prof fb).run E.c E.hfs E.hin (fun j' g' _ V' => V' = St188 S Z.cpu.gpr.rax W₂ ∧
      Fr Z₂.cpu.gpr g' ∧ g'.r15 = BitVec.ofNat 64 (8 * (i + 1)) ∧
      ((j' = 480 ∧ rdq(St188 S Z.cpu.gpr.rax W₂, aR S + 16#64) ≠ BitVec.ofNat 64 (8 * (i + 1))) ∨
        (j' = 221 ∧ rdq(St188 S Z.cpu.gpr.rax W₂, aR S + 16#64) = BitVec.ofNat 64 (8 * (i + 1)))))
    hKZ₂ hAZ₂ hrZ₂
    (vc_524 (by rw [e40]; exact E.f40) (by rw [e32]; exact E.f32)
      (by rw [e16]; exact fun j hj => E.c.hws _ (H.w16 j hj)) (by rw [e40]; exact fun j hj => E.w40 j (by omega))
      (by rw [hmZ₂.1]; exact fun x => FV7z.Fr40.rdSt (toBytesLE_length _ _) (ap32 _))
      (by rw [e40, e32]; exact H.wsl m i _ W₂ hIZ₂)
      (fun _ x hx a b c _ => ⟨hsx x hx, a, b.trans hs1,
        Or.inl ⟨rfl, by rw [← hsx x hx, ← e16, ← hs1]; exact c⟩⟩)
      (fun _ x hx a b c _ => ⟨hsx x hx, a, b.trans hs1,
        Or.inr ⟨rfl, by rw [← hsx x hx, ← e16, ← hs1]; exact c⟩⟩)) ?_
  rintro j' g fl V₁ ⟨rfl, gf3, g15c, hj⟩ U₃ t₆ hKU₃ hAU₃ hrU₃ hgU₃ -
  subst hgU₃
  have hmU₃ := Fm.fr hmZ₂ gf3
  have hL := H.hL m i _ W₂ hIZ₂
  have hz := H.zst m i _ W₂ hIZ₂
  have hm32 : m.toNat < 4294967296 := m.isLt
  rcases hj with ⟨rfl, hne⟩ | ⟨rfl, heq⟩
  · have hlt : i + 1 < m.toNat := by
      refine Nat.lt_of_le_of_ne hi fun e => hne ?_
      rw [hL, e]
    exact hn hlt U₃ _ t₆ hKU₃ hAU₃ hrU₃ ⟨hmU₃, g15c, hz.1 hlt⟩
  · have hm1 : i + 1 = m.toNat := by
      refine Classical.byContradiction fun hc => ne8 (i + 1) m.toNat (by omega) hm32 hc ?_
      rw [← hL, heq]
    exact from221 E hKU₃ hAU₃ hrU₃ hmU₃ (hz.2 hm1)

/-- The copy loop from 480, `d + 1` steps left. -/
theorem L480 (E : Ev prof F Wl L s₀ o gev gP gE fb S g0 e₂ code₂ j₂ I0 I1 I3 I2 I4 I5 P Q4 D Jd Iz)
    (H : Lh prof F Wl L s₀ o gev gP gE S g0 P Q4 Hg Gc Gr Gm Gf Go G G1 G2 G3) (m : BitVec 32) :
    ∀ d i, i + d + 1 = m.toNat → AtJ prof F Wl L s₀ o gev gP gE 480 (P480 S g0 G m i) := by
  intro d
  induction d with
  | zero => intro i h; exact S480 E H m i (by omega) fun h' => absurd h' (by omega)
  | succ d ih => intro i h; exact S480 E H m i (by omega) fun _ => ih (i + 1) (by omega)

/-- From 450 (`r15` = `m` not 0, the bytes with `Hg m`): the end offset stored, the loop from its first step. -/
theorem from450 (E : Ev prof F Wl L s₀ o gev gP gE fb S g0 e₂ code₂ j₂ I0 I1 I3 I2 I4 I5 P Q4 D Jd Iz)
    (H : Lh prof F Wl L s₀ o gev gP gE S g0 P Q4 Hg Gc Gr Gm Gf Go G G1 G2 G3) {m : BitVec 32}
    (hK : KeptW Wl s₀ Y) (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = cpr_at.add 450)
    (hm : Fm S g0 Y.cpu.gpr) (h15 : Y.cpu.gpr.r15 = BitVec.setWidth 64 m) (hm0 : m ≠ 0) (hI : Hg m W) :
    GoG prof L o gev gP gE Y t := by
  have e16 : Y.cpu.gpr.rsp + 16#64 = aR S + 16#64 := by rw [hm.1]
  have e24 : Y.cpu.gpr.rsp + 24#64 = aR S + 24#64 := by rw [hm.1]
  have eL : BitVec.setWidth 64 (BitVec.setWidth 32 (Y.cpu.gpr.r15 + 18446744073709551615#64)) * 8#64 + 8#64 =
      BitVec.ofNat 64 (8 * m.toNat) := by rw [h15]; exact l450 hm0
  refine (c_450 prof fb).run E.c E.hfs E.hin (fun j' g' _ V' => j' = 480 ∧
      V' = Vst (Vst W (aR S + 16#64) (toBytesLE (BitVec.ofNat 64 (8 * m.toNat)) 8)) (aR S + 24#64)
        (toBytesLE (aR S + 32#64) 8) ∧ Fr Y.cpu.gpr g' ∧ g'.r15 = 0#64) hK hA hr
    (vc_450 (by rw [e16]; exact H.w16) (by rw [e24]; exact H.w24) fun _ a b _ => ⟨rfl, by rw [eL, hm.1], a, b⟩) ?_
  rintro j' g fl V₁ ⟨rfl, rfl, gf, g15⟩ U t₁ hKU hAU hrU hgU -
  subst hgU
  have hpos : 0 + (m.toNat - 1) + 1 = m.toNat := by
    have : m.toNat ≠ 0 := fun e => hm0 (BitVec.eq_of_toNat_eq (e.trans rfl))
    omega
  exact L480 E H m (m.toNat - 1) 0 hpos U _ t₁ hKU hAU hrU ⟨Fm.fr hm gf, g15, H.z450 m W hI⟩

/-- From 619 (the new array `r` in `r12`, the bytes with `Gf m r`): `_items` and `_capacity` stored, to 450. -/
theorem from619 (E : Ev prof F Wl L s₀ o gev gP gE fb S g0 e₂ code₂ j₂ I0 I1 I3 I2 I4 I5 P Q4 D Jd Iz)
    (H : Lh prof F Wl L s₀ o gev gP gE S g0 P Q4 Hg Gc Gr Gm Gf Go G G1 G2 G3) {m : BitVec 32} {r : BitVec 64}
    (hK : KeptW Wl s₀ Y) (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = cpr_at.add 619)
    (hm : Fm S g0 Y.cpu.gpr) (h15 : Y.cpu.gpr.r15 = BitVec.setWidth 64 m) (h12 : Y.cpu.gpr.r12 = r) (hm0 : m ≠ 0)
    (hI : Gf m r W) :
    GoG prof L o gev gP gE Y t := by
  refine (c_619 prof fb).run E.c E.hfs E.hin (fun j' g' _ V' => j' = 450 ∧
      V' = Vst (Vst W (aR S + 32#64) (toBytesLE r 8)) (aR S + 44#64) (toBytesLE rdd(W, aR S + 8#64) 4) ∧
      Fr Y.cpu.gpr g' ∧ g'.r15 = Y.cpu.gpr.r15) hK hA hr
    (vc_619 (by rw [hm.1]; exact fun j hj => E.c.hws _ (H.w8 j (by omega))) (by rw [hm.1]; exact E.w32)
      (by rw [hm.1]; exact E.w44) fun _ a b _ => ⟨rfl, by rw [h12, hm.1], a, b⟩) ?_
  rintro j' g fl V₁ ⟨rfl, rfl, gf, g15⟩ U t₁ hKU hAU hrU hgU -
  subst hgU
  exact from450 E H hKU hAU hrU (Fm.fr hm gf) (g15.trans h15) hm0 (H.z619 m r W hI)

/-- From 669 (`r8` = `p`, the bytes with `Go m r p`): `operator delete [] (p)` (`k672`), from its return 677 to
619. -/
theorem from669 (E : Ev prof F Wl L s₀ o gev gP gE fb S g0 e₂ code₂ j₂ I0 I1 I3 I2 I4 I5 P Q4 D Jd Iz)
    (H : Lh prof F Wl L s₀ o gev gP gE S g0 P Q4 Hg Gc Gr Gm Gf Go G G1 G2 G3) {m : BitVec 32} {r p : BitVec 64}
    (hK : KeptW Wl s₀ Y) (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = cpr_at.add 669)
    (hm : Fm S g0 Y.cpu.gpr) (h15 : Y.cpu.gpr.r15 = BitVec.setWidth 64 m) (h12 : Y.cpu.gpr.r12 = r)
    (h8 : Y.cpu.gpr.r8 = p) (hm0 : m ≠ 0) (hI : Go m r p W) :
    GoG prof L o gev gP gE Y t := by
  refine (c_669 prof fb).run E.c E.hfs E.hin (fun j' g' _ V' => j' = 672 ∧ V' = W ∧ Fr Y.cpu.gpr g' ∧
      g'.r12 = Y.cpu.gpr.r12 ∧ g'.r15 = Y.cpu.gpr.r15 ∧ g'.rdi = Y.cpu.gpr.r8) hK hA hr
    (vc_669 fun _ a b d e _ => ⟨rfl, rfl, a, b, d, e⟩) ?_
  rintro j' g fl V₁ ⟨rfl, hV₁, gf, g12, g15, gdi⟩ U t₁ hKU hAU hrU hgU -
  subst V₁ hgU
  have hmU := Fm.fr hm gf
  refine callK E hKU hAU hrU hmU.1 (lt_len (by decide)) (call_672 _) tgt_672 E.cD (H.k672 m r p W hI)
    (gdi.trans h8) ?_
  intro Z W' t₃ hKZ hAZ hrZ hsZ hkZ hIZ
  refine (c_677 prof fb).run E.c E.hfs E.hin (fun j' g' _ V' => j' = 619 ∧ V' = W' ∧ g' = Z.cpu.gpr) hKZ hAZ hrZ
    (vc_677 fun _ => ⟨rfl, rfl, rfl⟩) ?_
  rintro j' g fl V₁ ⟨rfl, hV₁, hg⟩ U₂ t₄ hKU₂ hAU₂ hrU₂ hgU₂ -
  subst V₁ hgU₂
  have hmU₂ : Fm S g0 U₂.cpu.gpr := by rw [hg]; exact fm_ret hmU hsZ hkZ
  exact from619 E H hKU₂ hAU₂ hrU₂ hmU₂ (by rw [hg, hkZ.2.2.2.2.2, g15, h15]) (by rw [hg, hkZ.2.2.1, g12, h12])
    hm0 hIZ

/-- From 664 (back from `memcpy`, the bytes with `Gm m r`): `r8` = the saved `_items`, to 669. -/
theorem from664 (E : Ev prof F Wl L s₀ o gev gP gE fb S g0 e₂ code₂ j₂ I0 I1 I3 I2 I4 I5 P Q4 D Jd Iz)
    (H : Lh prof F Wl L s₀ o gev gP gE S g0 P Q4 Hg Gc Gr Gm Gf Go G G1 G2 G3) {m : BitVec 32} {r : BitVec 64}
    (hK : KeptW Wl s₀ Y) (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = cpr_at.add 664)
    (hm : Fm S g0 Y.cpu.gpr) (h15 : Y.cpu.gpr.r15 = BitVec.setWidth 64 m) (h12 : Y.cpu.gpr.r12 = r) (hm0 : m ≠ 0)
    (hI : Gm m r W) :
    GoG prof L o gev gP gE Y t := by
  refine (c_664 prof fb).run E.c E.hfs E.hin (fun j' g' _ V' => j' = 669 ∧ V' = W ∧ Fr Y.cpu.gpr g' ∧
      g'.r12 = Y.cpu.gpr.r12 ∧ g'.r15 = Y.cpu.gpr.r15 ∧ g'.r8 = rdq(W, aR S + 16#64)) hK hA hr
    (vc_664 (by rw [hm.1]; exact fun j hj => E.c.hws _ (H.w16 j hj))
      fun _ a b d e _ => ⟨rfl, rfl, a, b, d, by rw [e, hm.1]⟩) ?_
  rintro j' g fl V₁ ⟨rfl, hV₁, gf, g12, g15, g8⟩ U t₁ hKU hAU hrU hgU -
  subst V₁ hgU
  exact from669 E H hKU hAU hrU (Fm.fr hm gf) (g15.trans h15) (g12.trans h12) g8 hm0 (H.z664 m r W hI)

/-- From 598 (back from `operator new []`, its result `rax`, the bytes with `Gr m rax`): `_size` not 0 to `memcpy`
(`k659`) and from its return 664; else to 669 (`z614`) or 619 (`zf0`). -/
theorem from598 (E : Ev prof F Wl L s₀ o gev gP gE fb S g0 e₂ code₂ j₂ I0 I1 I3 I2 I4 I5 P Q4 D Jd Iz)
    (H : Lh prof F Wl L s₀ o gev gP gE S g0 P Q4 Hg Gc Gr Gm Gf Go G G1 G2 G3) {m : BitVec 32}
    (hK : KeptW Wl s₀ Y) (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = cpr_at.add 598)
    (hm : Fm S g0 Y.cpu.gpr) (h15 : Y.cpu.gpr.r15 = BitVec.setWidth 64 m) (hm0 : m ≠ 0)
    (hI : Gr m Y.cpu.gpr.rax W) :
    GoG prof L o gev gP gE Y t := by
  have e40 : Y.cpu.gpr.rsp + 40#64 = aR S + 40#64 := by rw [hm.1]
  have e32 : Y.cpu.gpr.rsp + 32#64 = aR S + 32#64 := by rw [hm.1]
  have e16 : Y.cpu.gpr.rsp + 16#64 = aR S + 16#64 := by rw [hm.1]
  refine (c_598 prof fb).run E.c E.hfs E.hin (fun j' g' _ V' => Fr Y.cpu.gpr g' ∧ g'.r12 = Y.cpu.gpr.rax ∧
      g'.r15 = Y.cpu.gpr.r15 ∧
      ((j' = 659 ∧ V' = Vst W (aR S + 16#64) (toBytesLE rdq(W, aR S + 32#64) 8) ∧ g'.rdi = Y.cpu.gpr.rax ∧
          g'.rsi = rdq(W, aR S + 32#64) ∧ g'.rdx = BitVec.setWidth 64 rdd(W, aR S + 40#64) * 8#64) ∨
        (j' = 669 ∧ V' = W ∧ g'.r8 = rdq(W, aR S + 32#64)) ∨ (j' = 619 ∧ V' = W))) hK hA hr
    (vc_598 (by rw [e40]; exact E.f40) (by rw [e32]; exact E.f32) (by rw [e16]; exact H.w16)
      (fun _ a b d e i k _ => ⟨a, b, d, Or.inl ⟨rfl, by rw [e16, e32], e, by rw [i, e32], by rw [k, e40]⟩⟩)
      (fun _ a b d e _ => ⟨a, b, d, Or.inr (Or.inl ⟨rfl, rfl, by rw [e, e32]⟩)⟩)
      (fun _ a b d _ => ⟨a, b, d, Or.inr (Or.inr ⟨rfl, rfl⟩)⟩)) ?_
  rintro j' g fl V₁ ⟨gf, g12, g15, hj⟩ U t₁ hKU hAU hrU hgU -
  subst hgU
  have hmU := Fm.fr hm gf
  rcases hj with ⟨rfl, rfl, gdi, gsi, gdx⟩ | ⟨rfl, hV₁, g8⟩ | ⟨rfl, hV₁⟩
  · refine callK E hKU hAU hrU hmU.1 (lt_len (by decide)) (call_659 _) tgt_659 H.cM (H.k659 m _ W hI)
      ⟨gdi, gsi, gdx⟩ ?_
    intro Z W' t₃ hKZ hAZ hrZ hsZ hkZ hIZ
    exact from664 E H hKZ hAZ hrZ (fm_ret hmU hsZ hkZ) (by rw [hkZ.2.2.2.2.2, g15, h15]) (by rw [hkZ.2.2.1, g12])
      hm0 hIZ
  · subst V₁
    exact from669 E H hKU hAU hrU hmU (g15.trans h15) g12 g8 hm0 (H.z614 m _ W hI)
  · subst V₁
    exact from619 E H hKU hAU hrU hmU (g15.trans h15) g12 hm0 (H.zf0 m _ W hI)

/-- From 440 (`r15` = `m`, the bytes with `Q4 m x`): the growth (`z560`, `operator new []` by `k593`, from its
return 598), or 450 (`hQ`). -/
theorem from440 (E : Ev prof F Wl L s₀ o gev gP gE fb S g0 e₂ code₂ j₂ I0 I1 I3 I2 I4 I5 P Q4 D Jd Iz)
    (H : Lh prof F Wl L s₀ o gev gP gE S g0 P Q4 Hg Gc Gr Gm Gf Go G G1 G2 G3) {m x : BitVec 32}
    (hK : KeptW Wl s₀ Y) (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = cpr_at.add 440)
    (hm : Fm S g0 Y.cpu.gpr) (h15 : Y.cpu.gpr.r15 = BitVec.setWidth 64 m) (hQ : Q4 m x W) :
    GoG prof L o gev gP gE Y t := by
  refine (c_440 prof fb).run E.c E.hfs E.hin (fun j' g' _ V' => Fr Y.cpu.gpr g' ∧ g'.r15 = Y.cpu.gpr.r15 ∧
      ((j' = 593 ∧ ∃ c : BitVec 32, V' = Vst W (aR S + 8#64) (toBytesLE c 4)) ∨ (j' = 450 ∧ V' = W))) hK hA hr
    (vc_440 (by rw [hm.1]; exact fun j hj => E.c.hws _ (E.w44 j hj))
      (by rw [hm.1]; exact fun j hj => H.w8 j (by omega))
      (fun _ c a b _ => ⟨a, b, Or.inl ⟨rfl, c, by rw [hm.1]⟩⟩) (fun _ a b _ => ⟨a, b, Or.inr ⟨rfl, rfl⟩⟩)) ?_
  rintro j' g fl V₁ ⟨gf, g15, hj⟩ U t₁ hKU hAU hrU hgU -
  subst hgU
  have hmU := Fm.fr hm gf
  have hm0 := H.hQm m x W hQ
  rcases hj with ⟨rfl, c, rfl⟩ | ⟨rfl, hV₁⟩
  · refine callK E hKU hAU hrU hmU.1 (lt_len (by decide)) (call_593 _) tgt_593 E.cA
      (H.k593 m _ (H.z560 m x W hQ c)) trivial ?_
    intro Z W' t₃ hKZ hAZ hrZ hsZ hkZ hIZ
    exact from598 E H hKZ hAZ hrZ (fm_ret hmU hsZ hkZ) (by rw [hkZ.2.2.2.2.2, g15, h15]) hm0 hIZ
  · subst V₁
    exact from450 E H hKU hAU hrU hmU (g15.trans h15) hm0 (H.hQ m x W hQ)

/-- From 431 (`r15` = `m`, the bytes with `Q4 m x`): `cmp`, the `ja` at 434 to the throw (`kth`), else 440. -/
theorem from431 (E : Ev prof F Wl L s₀ o gev gP gE fb S g0 e₂ code₂ j₂ I0 I1 I3 I2 I4 I5 P Q4 D Jd Iz)
    (H : Lh prof F Wl L s₀ o gev gP gE S g0 P Q4 Hg Gc Gr Gm Gf Go G G1 G2 G3) {m x : BitVec 32}
    (hK : KeptW Wl s₀ Y) (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = cpr_at.add 431)
    (hm : Fm S g0 Y.cpu.gpr) (h15 : Y.cpu.gpr.r15 = BitVec.setWidth 64 m) (hQ : Q4 m x W) :
    GoG prof L o gev gP gE Y t := by
  refine (c_431 prof fb).run E.c E.hfs E.hin (fun j' g' _ V' => j' = 434 ∧ V' = W ∧ Fr Y.cpu.gpr g' ∧
      g'.r15 = Y.cpu.gpr.r15) hK hA hr (vc_431 fun _ a b _ => ⟨rfl, rfl, a, b⟩) ?_
  rintro j' g fl V₁ ⟨rfl, hV₁, gf, g15⟩ U t₁ hKU hAU hrU hgU -
  subst V₁ hgU
  have hmU := Fm.fr hm gf
  obtain ⟨cT, hinT, hT⟩ := H.cT
  refine E.c.s_jcc_x hKU hAU E.hin (lt_len (by decide)) hrU (ja_434 _) hinT hT tja_434 ?_ ?_
  · intro _ Y₁ t₂ hK₁ hA₁ ⟨hr₁, hg₁⟩
    exact H.kth m x W hQ Y₁ t₂ hK₁ hA₁ (by rw [hr₁, addr_add_zero]) (by rw [hg₁]; exact hmU.1)
  · intro _ Y₁ t₂ hK₁ hA₁ ⟨hr₁, hg₁⟩
    exact from440 E H hK₁ hA₁ hr₁ (by rw [hg₁]; exact hmU) (by rw [hg₁, g15, h15]) hQ

/-- From 425 (`P425`): the `js` to the throw (`kth`), else 431. -/
theorem from425 (E : Ev prof F Wl L s₀ o gev gP gE fb S g0 e₂ code₂ j₂ I0 I1 I3 I2 I4 I5 P Q4 D Jd Iz)
    (H : Lh prof F Wl L s₀ o gev gP gE S g0 P Q4 Hg Gc Gr Gm Gf Go G G1 G2 G3) :
    AtJ prof F Wl L s₀ o gev gP gE 425 (P425 S g0 Q4) := by
  rintro Y W t hK hA hr ⟨hm, m, x, h15, -, hQ⟩
  obtain ⟨cT, hinT, hT⟩ := H.cT
  refine E.c.s_jcc_x hK hA E.hin (lt_len (by decide)) hr (js_425 _) hinT hT tjs_425 ?_ ?_
  · intro _ Y₁ t₂ hK₁ hA₁ ⟨hr₁, hg₁⟩
    exact H.kth m x W hQ Y₁ t₂ hK₁ hA₁ (by rw [hr₁, addr_add_zero]) (by rw [hg₁]; exact hm.1)
  · intro _ Y₁ t₂ hK₁ hA₁ ⟨hr₁, hg₁⟩
    exact from431 E H hK₁ hA₁ hr₁ (by rw [hg₁]; exact hm) (by rw [hg₁]; exact h15) hQ

end Runs

section Full
variable {prof : Profile} {F : Footprint} {Wl : List Rgn} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {X : State} {t : Nat} {V : Addr → Byte}

/-- `NWildcard::CCensorNode::CheckPathToRoot (include, pathParts, isFile)` from its entry to the return address:
`Cpr.cpr_ok` with the run from 425 (the growth and the copy loop) by `from425`, its hypotheses in `Lh` (the slots at
`aR S + 8`, `+ 16`, `+ 24` in what the run may store into, `pathParts._items` readable, `memcpy` and the throw's
code, the throw a continuation `kth`, the invariants of the loop). -/
theorem cpr_full {fb : Addr} {e₂ : Addr} {code₂ : List Byte} {j₂ : Nat}
    {I0 I1 I3 : (Addr → Byte) → Prop} {I2 : Gprs → (Addr → Byte) → Prop} {I4 I5 : BitVec 64 → (Addr → Byte) → Prop}
    {P : (Addr → Byte) → Prop} {Q4 : BitVec 32 → BitVec 32 → (Addr → Byte) → Prop}
    {D : BitVec 64 → Nat → (Addr → Byte) → Prop} {Jd : BitVec 64 → Nat → BitVec 64 → (Addr → Byte) → Prop}
    {Iz : (Addr → Byte) → Prop}
    {Hg Gc : BitVec 32 → (Addr → Byte) → Prop} {Gr Gm Gf : BitVec 32 → BitVec 64 → (Addr → Byte) → Prop}
    {Go : BitVec 32 → BitVec 64 → BitVec 64 → (Addr → Byte) → Prop}
    {G G1 : BitVec 32 → Nat → (Addr → Byte) → Prop} {G2 G3 : BitVec 32 → Nat → BitVec 64 → (Addr → Byte) → Prop}
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
    (H : Lh prof F Wl L s₀ o gev gP gE X.cpu.gpr.rsp X.cpu.gpr P Q4 Hg Gc Gr Gm Gf Go G G1 G2 G3)
    (kr : ∀ (W : Addr → Byte) (Z' : State) (t' : Nat), KeptW Wl s₀ Z' → Agree F Z'.proc.mm.mem W →
      Z'.cpu.rip = e₂.add j₂ → Z'.cpu.gpr.rsp = X.cpu.gpr.rsp + 8 → KS X.cpu.gpr Z'.cpu.gpr → Iz W →
      GoG prof L o gev gP gE Z' t') :
    GoG prof L o gev gP gE X t :=
  cpr_ok c hfs hin hK hA hrip hcl hs1 hs2 hs3 hs4 hs5 hs6 hw w32 w40 w44 hr8 hl hin₂ h₂ fpar fn8 hIz hz0 z80 h117 z146
    wsl z221 z425 hDa fe fp hP0 hQ0 hA0 cK cA cN cU cP cD cE k54 k112 k169 k183 k238 k290 k303 k328 (fun E => from425
    E H) kr

end Full

end FV7z.Cpr
