import FV7z.Stl.Vc2
import FV7z.Nlc.Holds
/-!
# `____strtoul_l_internal`: what the function is given and asks, the ways out (PLAN.md §M, M1)

As `Ild/Holds.lean`: the caller's return is a continuation (`Kret`), the memory invariant is that the bytes kept
(`Kr`: the pushes `[S - 48, S + 8)`, and `Kk` outside the frame `[S - 88, S)`) are the pushes' (`Ag (Kr Kk S) (Vf V0
g0)`). The frame below the pushes holds `E` (at `S88 S + 8`), the cut digit (`+ 18`), the sign (`+ 20`) and
`rbp - 1` (`+ 24`); none of them is kept.

- `s88_e`, `u40`, `q40`: the frame and the pops' addresses. `rdF`: a read in the pushes.
- `Env`, `Kret`.
- `t448` (the pops and the `ret` at 462), `t432` (`EINVAL`), `t927`, `t790` (`*E = p`, `E ≠ 0`).
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
open FV7z.Stm (Km stk)
open FV7z.Mcn (fr6 rds rdo fr_e6 fr6_rd)
open FV7z.Nlc (Ag)
namespace FV7z.Stl

/-! ## Names and numbers -/

/-- The bytes kept: the pushes `[S - 48, S + 8)`, and `Kk` outside the frame `[S - 88, S)`. -/
def Kr (Kk : Addr → Prop) (S y : Addr) : Prop :=
  (S.toNat - 48 ≤ y.toNat ∧ y.toNat < S.toNat + 8) ∨ (Kk y ∧ (y.toNat < S.toNat - 88 ∨ S.toNat ≤ y.toNat))

/-- The bytes after the six pushes. -/
abbrev Vf (V0 : Addr → Byte) (g0 : Gprs) : Addr → Byte := fr6 V0 g0.rsp g0.r15 g0.r14 g0.r13 g0.r12 g0.rbp g0.rbx

theorem s88_e {S : Addr} (hS : 96 ≤ S.toNat) : (S88 S).toNat = S.toNat - 88 := by
  simp only [S88]
  bv_omega

/-- The frame's slots. -/
theorem slots {S : Addr} (hS : 96 ≤ S.toNat) : (S88 S + 8#64).toNat = S.toNat - 80 ∧
    (S88 S + 18#64).toNat = S.toNat - 70 ∧ (S88 S + 20#64).toNat = S.toNat - 68 ∧
    (S88 S + 24#64).toNat = S.toNat - 64 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [S88] <;> bv_omega

/-- The pops' addresses as numbers. -/
theorem u40 {S : Addr} (hS : 96 ≤ S.toNat) (hS8 : S.toNat + 8 ≤ 2 ^ 64) :
    (S88 S + 40#64).toNat = S.toNat - 48 ∧ (S88 S + 40#64 + 8).toNat = S.toNat - 40 ∧
    (S88 S + 40#64 + 8 + 8).toNat = S.toNat - 32 ∧ (S88 S + 40#64 + 8 + 8 + 8).toNat = S.toNat - 24 ∧
    (S88 S + 40#64 + 8 + 8 + 8 + 8).toNat = S.toNat - 16 ∧
    (S88 S + 40#64 + 8 + 8 + 8 + 8 + 8).toNat = S.toNat - 8 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [S88] <;> bv_omega

/-- The pops' addresses. -/
theorem q40 (S : Addr) :
    S88 S + 40#64 = S - 8 - 8 - 8 - 8 - 8 - 8 ∧ S88 S + 40#64 + 8 = S - 8 - 8 - 8 - 8 - 8 ∧
    S88 S + 40#64 + 8 + 8 = S - 8 - 8 - 8 - 8 ∧ S88 S + 40#64 + 8 + 8 + 8 = S - 8 - 8 - 8 ∧
    S88 S + 40#64 + 8 + 8 + 8 + 8 = S - 8 - 8 ∧ S88 S + 40#64 + 8 + 8 + 8 + 8 + 8 = S - 8 ∧
    S88 S + 40#64 + 8 + 8 + 8 + 8 + 8 + 8 = S := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [S88] <;> bv_omega

/-- The return address is not under the pushes. -/
theorem fr6_ra (V : Addr → Byte) (S : Addr) (a b c d e f : BitVec 64) (hS : 80 ≤ S.toNat)
    (hS8 : S.toNat + 8 ≤ 2 ^ 64) : rdq(fr6 V S a b c d e f, S) = rdq(V, S) := by
  have hl := S.isLt
  obtain ⟨s1, s2, s3, s4, s5, s6⟩ := fr_e6 hS
  unfold fr6
  rw [rdo, rdo, rdo, rdo, rdo, rdo] <;> omega

/-- A quadword read in the pushes `[S - 48, S + 8)`. -/
theorem rdF {Kk : Addr → Prop} {V0 V : Addr → Byte} {g0 : Gprs} (hag : Ag (Kr Kk g0.rsp) (Vf V0 g0) V) {x : Addr}
    (h1 : g0.rsp.toNat - 48 ≤ x.toNat) (h2 : x.toNat ≤ g0.rsp.toNat) (hS8 : g0.rsp.toNat + 8 ≤ 2 ^ 64) :
    rdq(V, x) = rdq(Vf V0 g0, x) := by
  apply congrArg (ofBytesLE 64)
  apply List.map_congr_left
  intro y hy
  obtain ⟨i, hi, rfl⟩ := mem_byteAddrs.1 hy
  have e := toNat_add_of_fits (a := x) (n := 8) hi (by omega)
  exact hag _ (Or.inl ⟨by omega, by omega⟩)

/-! ## What the function is given and asks -/

/-- What the function is given: `V0` the bytes and `g0` the registers at the entry (`S = rsp`, `rdi = p`,
`rsi = E`, `edx` the base, `ecx` the group flag, `r8` the locale), `fb` the `fs` base; the code, the frame
`[S - 88, S)` writable, the return address `e₂ + j₂` (in `Kk` with the pushes); no grouping; a base of 0 or 2 to 36;
`E` (if not 0) and `errno` writable and apart from the bytes kept. The string and the tables are in `Sv`. -/
structure Env (F : Footprint) (Wl : List Rgn) (L : List (Addr × List Byte)) (Kk : Addr → Prop)
    (V0 : Addr → Byte) (g0 : Gprs) (fb e₂ : Addr) (j₂ : Nat) : Prop where
  hin : CodeIn L stl_at stl
  rc : ∃ code, CodeIn L e₂ code ∧ j₂ < code.length
  s96 : 96 ≤ g0.rsp.toNat
  s8 : g0.rsp.toNat + 8 ≤ 2 ^ 64
  wf : ∀ a : Addr, g0.rsp.toNat - 88 ≤ a.toNat → a.toNat < g0.rsp.toNat → Foot Wl a
  fra : ∀ i < 8, Foot F.data (Addr.add g0.rsp i)
  hra : rdq(V0, g0.rsp) = e₂.add j₂
  kf : ∀ y : Addr, g0.rsp.toNat - 48 ≤ y.toNat → y.toNat < g0.rsp.toNat + 8 → Kk y
  hc : BitVec.setWidth 32 g0.rcx = 0#32
  b36 : (BitVec.setWidth 32 g0.rdx).toNat ≤ 36
  b1 : (BitVec.setWidth 32 g0.rdx).toNat ≠ 1
  eW : g0.rsi ≠ 0#64 → ∀ i < 8, Foot Wl (Addr.add g0.rsi i)
  eL : g0.rsi ≠ 0#64 → g0.rsi.toNat + 8 ≤ 2 ^ 64
  eK : g0.rsi ≠ 0#64 → ∀ y, Kr Kk g0.rsp y → y.toNat < g0.rsi.toNat ∨ g0.rsi.toNat + 8 ≤ y.toNat
  ef : ∀ i < 4, Foot Wl (Addr.add (fb + 18446744073709551544#64) i)
  eo : (fb + 18446744073709551544#64).toNat + 4 ≤ 2 ^ 64
  ek : ∀ y, Kr Kk g0.rsp y →
    y.toNat < (fb + 18446744073709551544#64).toNat ∨ (fb + 18446744073709551544#64).toNat + 4 ≤ y.toNat

/-- What the caller asks at the return address `ra`: bytes `W` kept as the pushes' where kept, `rsp = S + 8`, the
registers a call keeps. -/
def Kret (prof : Profile) (F : Footprint) (Wl : List Rgn) (L : List (Addr × List Byte)) (s₀ : State) (o : Oracle)
    (gev : List Event) (gP : State → Nat → List Event → Prop) (gE : Outcome → List Event → Prop)
    (Kk : Addr → Prop) (V0 : Addr → Byte) (g0 : Gprs) (ra : Addr) : Prop :=
  ∀ (Z : State) (t' : Nat) (W : Addr → Byte), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem W →
    Ag (Kr Kk g0.rsp) (Vf V0 g0) W → Z.cpu.rip = ra → Z.cpu.gpr.rsp = g0.rsp + 8 → Km g0 Z.cpu.gpr →
    GoG prof L o gev gP gE Z t'
