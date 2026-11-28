import FV7z.Lemmas.LeafRet
/-!
# The 40-byte frame of `push r14; push r13; push r12; push rbp; push rbx` (PLAN.md §M, M1)

Functions that save `r14`, `r13`, `r12`, `rbp` and `rbx` with five pushes and no `sub rsp`
(`NDir::GetFullPathAndSplit` at `0x454a50`, `FV7z/Gfs`): `S` the entry's `rsp`, the saved `r14` at `S - 8`, `r13` at
`S - 16`, `r12` at `S - 24`, `rbp` at `S - 32`, `rbx` at `S - 40`, a `call`'s return address at `S - 48`. The slots
are named as the pops read them (`S - 8 - 8 - 8 - 8 - 8`, then `+ 8` each), so the epilogue needs no address
rewriting; the pushes' forms (`S - 8`, …) meet them by `r1`–`r5`, one small `bv_omega` lemma each (never `bv_omega` in
a big context).

- `r1`–`r5`: the pops' addresses as the pushes'.
- `Fr`: the registers a piece (or a callee, from its entry's registers) keeps; `KS`: the callee-saved registers as at
  the entry.
- `StkF`, `FtsF`: the five saved registers and the return address in the bytes; the six slots readable.
- `Ap`, `Ap6`, `rdSt`: 8 bytes apart from a store; the six slots apart from it; a load of them after it.
-/
open ZellicX86 Decode FV7z
namespace FV7z.Fr40

theorem r1 (s : BitVec 64) : s - 8 - 8 - 8 - 8 - 8 + 8 = s - 8 - 8 - 8 - 8 := by bv_omega
theorem r2 (s : BitVec 64) : s - 8 - 8 - 8 - 8 - 8 + 8 + 8 = s - 8 - 8 - 8 := by bv_omega
theorem r3 (s : BitVec 64) : s - 8 - 8 - 8 - 8 - 8 + 8 + 8 + 8 = s - 8 - 8 := by bv_omega
theorem r4 (s : BitVec 64) : s - 8 - 8 - 8 - 8 - 8 + 8 + 8 + 8 + 8 = s - 8 := by bv_omega
theorem r5 (s : BitVec 64) : s - 8 - 8 - 8 - 8 - 8 + 8 + 8 + 8 + 8 + 8 = s := by bv_omega

/-- What a piece keeps: `rsp`, `rbx`, `rbp`, `r12`–`r15`. -/
abbrev Fr (g g' : Gprs) : Prop :=
  g'.rsp = g.rsp ∧ g'.rbx = g.rbx ∧ g'.rbp = g.rbp ∧ g'.r12 = g.r12 ∧ g'.r13 = g.r13 ∧ g'.r14 = g.r14 ∧
    g'.r15 = g.r15

/-- The callee-saved registers as in `g0`. -/
abbrev KS (g0 g : Gprs) : Prop :=
  g.rbx = g0.rbx ∧ g.rbp = g0.rbp ∧ g.r12 = g0.r12 ∧ g.r13 = g0.r13 ∧ g.r14 = g0.r14 ∧ g.r15 = g0.r15

/-- The saved `rbx`, `rbp`, `r12`, `r13`, `r14` of `g0` and the return address `ra` in the bytes `W`. -/
abbrev StkF (W : Addr → Byte) (S : Addr) (g0 : Gprs) (ra : Addr) : Prop :=
  rdq(W, S - 8 - 8 - 8 - 8 - 8) = g0.rbx ∧ rdq(W, S - 8 - 8 - 8 - 8 - 8 + 8) = g0.rbp ∧
    rdq(W, S - 8 - 8 - 8 - 8 - 8 + 8 + 8) = g0.r12 ∧ rdq(W, S - 8 - 8 - 8 - 8 - 8 + 8 + 8 + 8) = g0.r13 ∧
    rdq(W, S - 8 - 8 - 8 - 8 - 8 + 8 + 8 + 8 + 8) = g0.r14 ∧ rdq(W, S) = ra

/-- The six slots readable. -/
abbrev FtsF (F : Footprint) (S : Addr) : Prop :=
  (∀ i < 8, Foot F.data (Addr.add (S - 8 - 8 - 8 - 8 - 8) i)) ∧
    (∀ i < 8, Foot F.data (Addr.add (S - 8 - 8 - 8 - 8 - 8 + 8) i)) ∧
    (∀ i < 8, Foot F.data (Addr.add (S - 8 - 8 - 8 - 8 - 8 + 8 + 8) i)) ∧
    (∀ i < 8, Foot F.data (Addr.add (S - 8 - 8 - 8 - 8 - 8 + 8 + 8 + 8) i)) ∧
    (∀ i < 8, Foot F.data (Addr.add (S - 8 - 8 - 8 - 8 - 8 + 8 + 8 + 8 + 8) i)) ∧
    ∀ i < 8, Foot F.data (Addr.add S i)

/-- The 8 bytes at `x` apart from the `n` at `a`. -/
abbrev Ap (x a : Addr) (n : Nat) : Prop := ∀ c < 8, ∀ i < n, Addr.add x c ≠ Addr.add a i

/-- The six slots apart from the `n` bytes at `a`. -/
abbrev Ap6 (S a : Addr) (n : Nat) : Prop :=
  Ap (S - 8 - 8 - 8 - 8 - 8) a n ∧ Ap (S - 8 - 8 - 8 - 8 - 8 + 8) a n ∧ Ap (S - 8 - 8 - 8 - 8 - 8 + 8 + 8) a n ∧
    Ap (S - 8 - 8 - 8 - 8 - 8 + 8 + 8 + 8) a n ∧ Ap (S - 8 - 8 - 8 - 8 - 8 + 8 + 8 + 8 + 8) a n ∧ Ap S a n

/-- 8 bytes apart from a store: as before it. -/
theorem rdSt {V : Addr → Byte} {a : Addr} {bs : List Byte} {x : Addr} {n : Nat} (hn : bs.length = n)
    (h : Ap x a n) : rdq(Vst V a bs, x) = rdq(V, x) := by
  congr 1
  refine List.map_congr_left fun y hy => ?_
  obtain ⟨c, hc, rfl⟩ := mem_byteAddrs.1 hy
  exact Vst_apart _ _ _ _ fun i hi => h c hc i (hn ▸ hi)

end FV7z.Fr40
