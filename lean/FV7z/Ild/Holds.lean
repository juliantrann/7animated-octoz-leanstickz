import FV7z.Ild.Vc
import FV7z.Nlc.Holds
/-!
# `_nl_intern_locale_data` (PLAN.md §M, M1)

glibc 2.31's `_nl_intern_locale_data (category, data, datasize)` at `0x615210` in `7zzs`, one thread (the code in
`Ild/Spec.lean`). The proof follows `Nlc/Holds.lean`: `malloc` and `free` are continuation hypotheses (`Mal`, `Fre`)
and the caller's return a continuation (`Kret`). The new block's contents are not described: the memory invariant
is only that the bytes kept (`Kr`: the frame `[S - 48, S + 8)`, and `Kk` outside `[S - 64, S)`) are the pushes'
(`Ag (Kr Kk S) (Vf V0 g0)`). The tables read are given in `Env` (the type table's entry `tA` and the jump table in
`Kk`, so they read as at the entry).

- `S56`, `Kr`, `Vf`, `lim`, `tA`: the frame after the prologue, the bytes kept, the pushes, the categories' bounds,
  the entry of `_nl_value_types[c]`.
- `be`: the `jbe`/`ja` condition as `decide (x ≤ K)`. `s56_e`, `up6`, `pq6`: the pops' addresses. `rdF`, `fr6_ra`:
  reads in the frame. `agC`: after a `call`, the bytes kept. `noK`: stores in the new block keep the bytes kept.
- `Env`, `Mal`, `Fre`, `Kret`: what the function is given and asks.
- `t264` (the pops, `ret`), `t248` (`errno = EINVAL`, `rax = 0`), `t240` (`free`, then 248): the ways out.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
open FV7z.Stm (Km stk)
open FV7z.Tun (Vst_out)
open FV7z.Mcn (fr6 rds rdo fr_e6 fr6_rd)
open FV7z.Nlc (Ag Res)
namespace FV7z.Ild

/-! ## Names -/

/-- The `rsp` after the prologue (six pushes, `sub rsp, 8`). -/
abbrev S56 (S : Addr) : Addr := S - 8 - 8 - 8 - 8 - 8 - 8 - 8#64

/-- The bytes kept: the frame `[S - 48, S + 8)`, and `Kk` outside `[S - 64, S)`. -/
def Kr (Kk : Addr → Prop) (S y : Addr) : Prop :=
  (S.toNat - 48 ≤ y.toNat ∧ y.toNat < S.toNat + 8) ∨ (Kk y ∧ (y.toNat < S.toNat - 64 ∨ S.toNat ≤ y.toNat))

/-- The bytes after the six pushes. -/
abbrev Vf (V0 : Addr → Byte) (g0 : Gprs) : Addr → Byte := fr6 V0 g0.rsp g0.r15 g0.r14 g0.r13 g0.r12 g0.rbp g0.rbx

/-- The bound of `cnt` for each category (`c = 6`, `LC_ALL`, has none). -/
def lim : List Nat := [85, 5, 158, 18, 45, 4, 0, 2, 6, 12, 4, 1, 15]

/-- The entry of `_nl_value_types[c]` (`0x7804c0 + 8c`). -/
abbrev tA (g0 : Gprs) : Addr := 7865536#64 + BitVec.signExtend 64 (BitVec.setWidth 32 g0.rdi) * 8#64

/-! ## Numbers and bytes -/

/-- The `jbe`/`ja` condition against `K`. -/
theorem be (x : Addr) (K : Nat) (hK : K < 2 ^ 64) :
    (decide (x.toNat < K) || decide (x = BitVec.ofNat 64 K)) = decide (x.toNat ≤ K) := by
  have i : x = BitVec.ofNat 64 K ↔ x.toNat = K := by
    constructor
    · intro h
      rw [h, BitVec.toNat_ofNat]
      exact Nat.mod_eq_of_lt hK
    · intro h
      apply BitVec.eq_of_toNat_eq
      rw [h, BitVec.toNat_ofNat]
      exact (Nat.mod_eq_of_lt hK).symm
  apply Bool.eq_iff_iff.2
  rw [Bool.or_eq_true, decide_eq_true_eq, decide_eq_true_eq, decide_eq_true_eq, i]
  omega

theorem s56_e {S : Addr} (hS : 80 ≤ S.toNat) : (S56 S).toNat = S.toNat - 56 := by
  obtain ⟨-, -, -, -, -, e6⟩ := fr_e6 hS
  have h : (S56 S).toNat = (S - 8 - 8 - 8 - 8 - 8 - 8).toNat - 8 := Prepare.toNat_sub8 (by rw [e6]; omega)
  rw [h, e6]
  omega

theorem s64_e {S : Addr} (hS : 80 ≤ S.toNat) : (S56 S - 8).toNat = S.toNat - 64 := by
  have e := s56_e hS
  have h : (S56 S - 8).toNat = (S56 S).toNat - 8 := Prepare.toNat_sub8 (by rw [e]; omega)
  rw [h, e]
  omega

/-- The pops' addresses as numbers. -/
theorem up6 {S : Addr} (hS : 80 ≤ S.toNat) (hS8 : S.toNat + 8 ≤ 2 ^ 64) :
    (S56 S + 8#64).toNat = S.toNat - 48 ∧ (S56 S + 8#64 + 8).toNat = S.toNat - 40 ∧
    (S56 S + 8#64 + 8 + 8).toNat = S.toNat - 32 ∧ (S56 S + 8#64 + 8 + 8 + 8).toNat = S.toNat - 24 ∧
    (S56 S + 8#64 + 8 + 8 + 8 + 8).toNat = S.toNat - 16 ∧ (S56 S + 8#64 + 8 + 8 + 8 + 8 + 8).toNat = S.toNat - 8 ∧
    (S56 S + 8#64 + 8 + 8 + 8 + 8 + 8 + 8).toNat = S.toNat := by
  have e := s56_e hS
  have e0 : (S56 S + 8#64).toNat = S.toNat - 48 := by
    rw [BitVec.toNat_add, e, show (8#64).toNat = 8 from rfl]
    omega
  have e1 := Stm.ta8 (a := S56 S + 8#64) (by omega)
  have e2 := Stm.ta8 (a := S56 S + 8#64 + 8) (by omega)
  have e3 := Stm.ta8 (a := S56 S + 8#64 + 8 + 8) (by omega)
  have e4 := Stm.ta8 (a := S56 S + 8#64 + 8 + 8 + 8) (by omega)
  have e5 := Stm.ta8 (a := S56 S + 8#64 + 8 + 8 + 8 + 8) (by omega)
  have e6 := Stm.ta8 (a := S56 S + 8#64 + 8 + 8 + 8 + 8 + 8) (by omega)
  omega

/-- The pops' addresses. -/
theorem pq6 {S : Addr} (hS : 80 ≤ S.toNat) (hS8 : S.toNat + 8 ≤ 2 ^ 64) :
    S56 S + 8#64 = S - 8 - 8 - 8 - 8 - 8 - 8 ∧ S56 S + 8#64 + 8 = S - 8 - 8 - 8 - 8 - 8 ∧
    S56 S + 8#64 + 8 + 8 = S - 8 - 8 - 8 - 8 ∧ S56 S + 8#64 + 8 + 8 + 8 = S - 8 - 8 - 8 ∧
    S56 S + 8#64 + 8 + 8 + 8 + 8 = S - 8 - 8 ∧ S56 S + 8#64 + 8 + 8 + 8 + 8 + 8 = S - 8 ∧
    S56 S + 8#64 + 8 + 8 + 8 + 8 + 8 + 8 = S := by
  obtain ⟨u0, u1, u2, u3, u4, u5, u6⟩ := up6 hS hS8
  obtain ⟨s1, s2, s3, s4, s5, s6⟩ := fr_e6 hS
  exact ⟨BitVec.eq_of_toNat_eq (by rw [u0, s6]), BitVec.eq_of_toNat_eq (by rw [u1, s5]),
    BitVec.eq_of_toNat_eq (by rw [u2, s4]), BitVec.eq_of_toNat_eq (by rw [u3, s3]),
    BitVec.eq_of_toNat_eq (by rw [u4, s2]), BitVec.eq_of_toNat_eq (by rw [u5, s1]), BitVec.eq_of_toNat_eq u6⟩

/-- The return address is not under the pushes. -/
theorem fr6_ra (V : Addr → Byte) (S : Addr) (a b c d e f : BitVec 64) (hS : 80 ≤ S.toNat)
    (hS8 : S.toNat + 8 ≤ 2 ^ 64) : rdq(fr6 V S a b c d e f, S) = rdq(V, S) := by
  have hl := S.isLt
  obtain ⟨s1, s2, s3, s4, s5, s6⟩ := fr_e6 hS
  unfold fr6
  rw [rdo, rdo, rdo, rdo, rdo, rdo] <;> omega

/-- A quadword read in the frame `[S - 48, S + 8)` where the bytes kept are the pushes'. -/
theorem rdF {Kk : Addr → Prop} {V0 V : Addr → Byte} {g0 : Gprs} (hag : Ag (Kr Kk g0.rsp) (Vf V0 g0) V) {x : Addr}
    (h1 : g0.rsp.toNat - 48 ≤ x.toNat) (h2 : x.toNat ≤ g0.rsp.toNat) (hS8 : g0.rsp.toNat + 8 ≤ 2 ^ 64) :
    rdq(V, x) = rdq(Vf V0 g0, x) := by
  apply congrArg (ofBytesLE 64)
  apply List.map_congr_left
  intro y hy
  obtain ⟨i, hi, rfl⟩ := mem_byteAddrs.1 hy
  have e := toNat_add_of_fits (a := x) (n := 8) hi (by omega)
  exact hag _ (Or.inl ⟨by omega, by omega⟩)

/-- After a `call` (its return address at `S56 S - 8`): the bytes kept, where the callee kept `Kk`. -/
theorem agC {Kk : Addr → Prop} {V0 V V' : Addr → Byte} {g0 : Gprs} {ra : Addr} (hS : 80 ≤ g0.rsp.toNat)
    (hkf : ∀ y : Addr, g0.rsp.toNat - 48 ≤ y.toNat → y.toNat < g0.rsp.toNat + 8 → Kk y)
    (hag : Ag (Kr Kk g0.rsp) (Vf V0 g0) V)
    (h : ∀ y, Kk y → V' y = Vst V (S56 g0.rsp - 8) (toBytesLE ra 8) y) :
    Ag (Kr Kk g0.rsp) (Vf V0 g0) V' := by
  intro y hy
  have hl := g0.rsp.isLt
  have e := s64_e hS
  have hk : Kk y := by
    rcases hy with ⟨h1, h2⟩ | ⟨h1, -⟩
    · exact hkf y h1 h2
    · exact h1
  rw [h y hk, Vst_out _ _ _ _ (by rw [toBytesLE_length, e]; omega)
    (by rw [toBytesLE_length, e]; rcases hy with ⟨h1, -⟩ | ⟨-, h1⟩ <;> omega)]
  exact hag y hy

/-- Stores in `[p, p + sz)`, apart from `Kk`, are apart from the bytes kept. -/
theorem noK {Kk : Addr → Prop} {S p a : Addr} {sz m : Nat}
    (hkf : ∀ y : Addr, S.toNat - 48 ≤ y.toNat → y.toNat < S.toNat + 8 → Kk y)
    (hp : ∀ y : Addr, p.toNat ≤ y.toNat → y.toNat < p.toNat + sz → ¬ Kk y)
    (h1 : p.toNat ≤ a.toNat) (h2 : a.toNat + m ≤ p.toNat + sz) :
    ∀ y, Kr Kk S y → y.toNat < a.toNat ∨ a.toNat + m ≤ y.toNat := by
  intro y hy
  have hk : Kk y := by
    rcases hy with ⟨h3, h4⟩ | ⟨h3, -⟩
    · exact hkf y h3 h4
    · exact h3
  by_cases e : y.toNat < a.toNat ∨ a.toNat + m ≤ y.toNat
  · exact e
  · exact absurd hk (hp y (by omega) (by omega))

/-! ## What the function is given and asks -/

/-- What the function is given: `V0` the bytes and `g0` the registers at the entry (`S = rsp`, `edi = c`,
`rsi = data`, `rdx = datasize`), `fb` the `fs` base; the code (and `malloc`'s, `free`'s), the frame `[S - 64, S)`
writable, the return address `e₂ + j₂`, the frame and its return address in `Kk`; `c ≤ 12`, `c ≠ 6`; the data and 4
bytes past it readable; the tables read: `_nl_category_num_items[c]`, `_nl_value_types[c]` (in `Kk`, outside the
frame) and its first `lim c + 1` types, the jump table (`ild_jt`, in `Kk`, outside the frame); `errno` writable and
apart from the bytes kept. -/
structure Env (F : Footprint) (Wl : List Rgn) (L : List (Addr × List Byte)) (Kk : Addr → Prop)
    (V0 : Addr → Byte) (g0 : Gprs) (fb e₂ : Addr) (j₂ : Nat) : Prop where
  hin : CodeIn L ild_at ild
  mc : ∃ code, CodeIn L 0x633160 code ∧ 0 < code.length
  fc : ∃ code, CodeIn L 0x633750 code ∧ 0 < code.length
  rc : ∃ code, CodeIn L e₂ code ∧ j₂ < code.length
  s80 : 80 ≤ g0.rsp.toNat
  s8 : g0.rsp.toNat + 8 ≤ 2 ^ 64
  wf : ∀ a : Addr, g0.rsp.toNat - 64 ≤ a.toNat → a.toNat < g0.rsp.toNat → Foot Wl a
  fra : ∀ i < 8, Foot F.data (Addr.add g0.rsp i)
  hra : rdq(V0, g0.rsp) = e₂.add j₂
  kf : ∀ y : Addr, g0.rsp.toNat - 48 ≤ y.toNat → y.toNat < g0.rsp.toNat + 8 → Kk y
  c12 : (BitVec.setWidth 32 g0.rdi).toNat ≤ 12
  c6 : (BitVec.setWidth 32 g0.rdi).toNat ≠ 6
  fd : ∀ i < g0.rdx.toNat + 4, Foot F.data (Addr.add g0.rsi i)
  dl : g0.rsi.toNat + g0.rdx.toNat + 4 ≤ 2 ^ 64
  fI : ∀ i < 8,
    Foot F.data (Addr.add (7270432#64 + BitVec.signExtend 64 (BitVec.setWidth 32 g0.rdi) * 8#64) i)
  fT : ∀ i < 8, Foot F.data (Addr.add (tA g0) i)
  kT : ∀ i < 8, Kk (Addr.add (tA g0) i) ∧
    ((Addr.add (tA g0) i).toNat < g0.rsp.toNat - 64 ∨ g0.rsp.toNat ≤ (Addr.add (tA g0) i).toNat)
  fY : ∀ k ≤ lim.getD (BitVec.setWidth 32 g0.rdi).toNat 0, ∀ i < 4,
    Foot F.data (Addr.add (rdq(V0, tA g0) + BitVec.ofNat 64 k * 4#64) i)
  jt : List.map V0 (byteAddrs 7268832#64 52) = ild_jt
  fJ : ∀ i < 52, Foot F.data (Addr.add 7268832#64 i)
  kJ : ∀ i < 52, Kk (Addr.add 7268832#64 i) ∧
    ((Addr.add 7268832#64 i).toNat < g0.rsp.toNat - 64 ∨ g0.rsp.toNat ≤ (Addr.add 7268832#64 i).toNat)
  ef : ∀ i < 4, Foot Wl (Addr.add (fb + 18446744073709551544#64) i)
  eo : (fb + 18446744073709551544#64).toNat + 4 ≤ 2 ^ 64
  ek : ∀ y, Kr Kk g0.rsp y →
    y.toNat < (fb + 18446744073709551544#64).toNat ∨ (fb + 18446744073709551544#64).toNat + 4 ≤ y.toNat

/-- What the function asks of `malloc` (`0x633160`): from its entry with `rsp = S56 S - 8`, the return address `ra`
there and `rdi = sz`, the run goes on to the goal if it does from every state at `ra` with `rsp = S56 S`, the
registers a call keeps, the bytes kept on `Kk`, and `rax` with `Res`. -/
def Mal (prof : Profile) (F : Footprint) (Wl : List Rgn) (L : List (Addr × List Byte)) (s₀ : State) (o : Oracle)
    (gev : List Event) (gP : State → Nat → List Event → Prop) (gE : Outcome → List Event → Prop)
    (S : Addr) (Kk : Addr → Prop) : Prop :=
  ∀ (sz : Nat) (Y : State) (t : Nat) (V : Addr → Byte) (ra : Addr), KeptW Wl s₀ Y → Agree F Y.proc.mm.mem V →
    Y.cpu.rip = 0x633160 → Y.cpu.gpr.rsp = S56 S - 8 → rdq(V, S56 S - 8) = ra →
    Y.cpu.gpr.rdi = BitVec.ofNat 64 sz →
    (∀ (Z : State) (t' : Nat) (V' : Addr → Byte), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V' →
      (∀ y, Kk y → V' y = V y) → Z.cpu.rip = ra → Z.cpu.gpr.rsp = S56 S → Km Y.cpu.gpr Z.cpu.gpr →
      Res Wl Kk sz Z.cpu.gpr.rax → GoG prof L o gev gP gE Z t') →
    GoG prof L o gev gP gE Y t

/-- What the function asks of `free` (`0x633750`), as of `malloc`, without a result. -/
def Fre (prof : Profile) (F : Footprint) (Wl : List Rgn) (L : List (Addr × List Byte)) (s₀ : State) (o : Oracle)
    (gev : List Event) (gP : State → Nat → List Event → Prop) (gE : Outcome → List Event → Prop)
    (S : Addr) (Kk : Addr → Prop) : Prop :=
  ∀ (Y : State) (t : Nat) (V : Addr → Byte) (ra : Addr), KeptW Wl s₀ Y → Agree F Y.proc.mm.mem V →
    Y.cpu.rip = 0x633750 → Y.cpu.gpr.rsp = S56 S - 8 → rdq(V, S56 S - 8) = ra →
    (∀ (Z : State) (t' : Nat) (V' : Addr → Byte), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V' →
      (∀ y, Kk y → V' y = V y) → Z.cpu.rip = ra → Z.cpu.gpr.rsp = S56 S → Km Y.cpu.gpr Z.cpu.gpr →
      GoG prof L o gev gP gE Z t') →
    GoG prof L o gev gP gE Y t

/-- What the caller asks at the return address `ra`: bytes `W` kept as the pushes' where kept, `rsp = S + 8`, the
registers a call keeps, `rax` 0 or a block `malloc` gave. -/
def Kret (prof : Profile) (F : Footprint) (Wl : List Rgn) (L : List (Addr × List Byte)) (s₀ : State) (o : Oracle)
    (gev : List Event) (gP : State → Nat → List Event → Prop) (gE : Outcome → List Event → Prop)
    (Kk : Addr → Prop) (V0 : Addr → Byte) (g0 : Gprs) (ra : Addr) : Prop :=
  ∀ (Z : State) (t' : Nat) (W : Addr → Byte), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem W →
    Ag (Kr Kk g0.rsp) (Vf V0 g0) W → Z.cpu.rip = ra → Z.cpu.gpr.rsp = g0.rsp + 8 → Km g0 Z.cpu.gpr →
    (∃ sz, Res Wl Kk sz Z.cpu.gpr.rax) → GoG prof L o gev gP gE Z t'

section
variable {prof : Profile} {F : Footprint} {Wl : List Rgn} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {Kk : Addr → Prop} {V0 : Addr → Byte} {g0 : Gprs} {fb e₂ : Addr} {j₂ : Nat}

/-! ## The ways out -/

set_option maxHeartbeats 4000000 in
/-- From 264: the pops and the `ret`. -/
theorem t264 (c : Seg prof F Wl L s₀ o) (hfs : s₀.cpu.seg.fsBase = fb) (E : Env F Wl L Kk V0 g0 fb e₂ j₂)
    {Y : State} {t : Nat} {V : Addr → Byte} (hK : KeptW Wl s₀ Y) (hA : Agree F Y.proc.mm.mem V)
    (hr : Y.cpu.rip = ild_at.add 264) (hsp : Y.cpu.gpr.rsp = S56 g0.rsp) (hag : Ag (Kr Kk g0.rsp) (Vf V0 g0) V)
    (hres : ∃ sz, Res Wl Kk sz Y.cpu.gpr.rax) (k : Kret prof F Wl L s₀ o gev gP gE Kk V0 g0 (e₂.add j₂)) :
    GoG prof L o gev gP gE Y t := by
  have hS := E.s80
  have hS8 := E.s8
  have hl := g0.rsp.isLt
  obtain ⟨s1, s2, s3, s4, s5, s6⟩ := fr_e6 hS
  obtain ⟨u0, u1, u2, u3, u4, u5, u6⟩ := up6 hS hS8
  obtain ⟨q0, q1, q2, q3, q4, q5, q6⟩ := pq6 hS hS8
  have ffr : ∀ b : Addr, g0.rsp.toNat - 48 ≤ b.toNat → b.toNat + 8 ≤ g0.rsp.toNat →
      ∀ i < 8, Foot F.data (Addr.add b i) := fun b h1 h2 i hi => c.hws _ (stk E.wf (by omega) h2 (by omega) i hi)
  obtain ⟨r6, r5, r4, r3, r2, r1⟩ := fr6_rd V0 g0.rsp g0.r15 g0.r14 g0.r13 g0.r12 g0.rbp g0.rbx hS
  have g6 : rdq(V, g0.rsp - 8 - 8 - 8 - 8 - 8 - 8) = g0.rbx :=
    (rdF (x := g0.rsp - 8 - 8 - 8 - 8 - 8 - 8) hag (by omega) (by omega) hS8).trans r6
  have g5 : rdq(V, g0.rsp - 8 - 8 - 8 - 8 - 8) = g0.rbp :=
    (rdF (x := g0.rsp - 8 - 8 - 8 - 8 - 8) hag (by omega) (by omega) hS8).trans r5
  have g4 : rdq(V, g0.rsp - 8 - 8 - 8 - 8) = g0.r12 :=
    (rdF (x := g0.rsp - 8 - 8 - 8 - 8) hag (by omega) (by omega) hS8).trans r4
  have g3 : rdq(V, g0.rsp - 8 - 8 - 8) = g0.r13 :=
    (rdF (x := g0.rsp - 8 - 8 - 8) hag (by omega) (by omega) hS8).trans r3
  have g2 : rdq(V, g0.rsp - 8 - 8) = g0.r14 := (rdF (x := g0.rsp - 8 - 8) hag (by omega) (by omega) hS8).trans r2
  have g1 : rdq(V, g0.rsp - 8) = g0.r15 := (rdF (x := g0.rsp - 8) hag (by omega) (by omega) hS8).trans r1
  have gra : rdq(V, g0.rsp) = e₂.add j₂ := (rdF (x := g0.rsp) hag (by omega) (Nat.le_refl _) hS8).trans
    ((fr6_ra V0 g0.rsp g0.r15 g0.r14 g0.r13 g0.r12 g0.rbp g0.rbx hS hS8).trans E.hra)
  obtain ⟨cR, hcR, hjR⟩ := E.rc
  refine (c_264 prof fb).run c hfs E.hin _ hK hA hr
    (vc_264 (by rw [hsp]; exact ffr _ (by omega) (by omega)) (by rw [hsp]; exact ffr _ (by omega) (by omega))
      (by rw [hsp]; exact ffr _ (by omega) (by omega)) (by rw [hsp]; exact ffr _ (by omega) (by omega))
      (by rw [hsp]; exact ffr _ (by omega) (by omega)) (by rw [hsp]; exact ffr _ (by omega) (by omega))) ?_
  rintro j' g fl V' ⟨rfl, hV, hsp', hax, hbx, hbp, h12, h13, h14, h15⟩ Z t₁ hKZ hAZ hrZ hgZ -
  subst hV
  subst hgZ
  rw [hsp, q6] at hsp'
  rw [hsp, q0, g6] at hbx
  rw [hsp, q1, g5] at hbp
  rw [hsp, q2, g4] at h12
  rw [hsp, q3, g3] at h13
  rw [hsp, q4, g2] at h14
  rw [hsp, q5, g1] at h15
  refine c.s_ret hKZ hAZ E.hin (lt_len (by decide)) hrZ (ret_278 _) (by rw [hsp']; exact E.fra) hcR hjR
    (by rw [hsp']; exact gra) ?_
  rintro W t₂ hKW hAW ⟨hrW, hgW⟩
  refine k W t₂ hKW hAW hag hrW (by rw [hgW]; show Z.cpu.gpr.rsp + 8 = _; rw [hsp'])
    ⟨(congrArg Gprs.rbx hgW).trans hbx, (congrArg Gprs.rbp hgW).trans hbp, (congrArg Gprs.r12 hgW).trans h12,
      (congrArg Gprs.r13 hgW).trans h13, (congrArg Gprs.r14 hgW).trans h14, (congrArg Gprs.r15 hgW).trans h15⟩ ?_
  rw [hgW]
  show ∃ sz, Res Wl Kk sz Z.cpu.gpr.rax
  rw [hax]
  exact hres

set_option maxHeartbeats 4000000 in
/-- From 248: `errno = EINVAL`, `rax = 0`, then 264. -/
theorem t248 (c : Seg prof F Wl L s₀ o) (hfs : s₀.cpu.seg.fsBase = fb) (E : Env F Wl L Kk V0 g0 fb e₂ j₂)
    {Y : State} {t : Nat} {V : Addr → Byte} (hK : KeptW Wl s₀ Y) (hA : Agree F Y.proc.mm.mem V)
    (hr : Y.cpu.rip = ild_at.add 248) (hsp : Y.cpu.gpr.rsp = S56 g0.rsp) (hag : Ag (Kr Kk g0.rsp) (Vf V0 g0) V)
    (k : Kret prof F Wl L s₀ o gev gP gE Kk V0 g0 (e₂.add j₂)) :
    GoG prof L o gev gP gE Y t := by
  refine (c_248 prof fb).run c hfs E.hin _ hK hA hr (vc_248 E.ef) ?_
  rintro j' g fl V' ⟨rfl, hV, hg⟩ Z t₁ hKZ hAZ hrZ hgZ -
  subst hV
  rw [hg] at hgZ
  exact t264 c hfs E hKZ hAZ hrZ (by rw [hgZ]; exact hsp)
    (hag.st (by rw [toBytesLE_length]; exact E.eo) fun y hy => by rw [toBytesLE_length]; exact E.ek y hy)
    ⟨0, by rw [hgZ]; exact Or.inl rfl⟩ k

set_option maxHeartbeats 4000000 in
/-- From 240: `rdi = rax`, the `call` of `free`, then 248. -/
theorem t240 (c : Seg prof F Wl L s₀ o) (hfs : s₀.cpu.seg.fsBase = fb) (E : Env F Wl L Kk V0 g0 fb e₂ j₂)
    (hfre : Fre prof F Wl L s₀ o gev gP gE g0.rsp Kk) {Y : State} {t : Nat} {V : Addr → Byte}
    (hK : KeptW Wl s₀ Y) (hA : Agree F Y.proc.mm.mem V) (hr : Y.cpu.rip = ild_at.add 240)
    (hsp : Y.cpu.gpr.rsp = S56 g0.rsp) (hag : Ag (Kr Kk g0.rsp) (Vf V0 g0) V)
    (k : Kret prof F Wl L s₀ o gev gP gE Kk V0 g0 (e₂.add j₂)) :
    GoG prof L o gev gP gE Y t := by
  have hS := E.s80
  have hl := g0.rsp.isLt
  have e64 := s64_e hS
  obtain ⟨cF, hcF, hF0⟩ := E.fc
  refine (c_240 prof fb).run c hfs E.hin _ hK hA hr vc_240 ?_
  rintro j' g fl V' ⟨rfl, hV, hg⟩ Z t₁ hKZ hAZ hrZ hgZ -
  subst hV
  rw [hg] at hgZ
  have hspZ : Z.cpu.gpr.rsp = S56 g0.rsp := by rw [hgZ]; exact hsp
  refine c.s_call hKZ hAZ E.hin (lt_len (by decide)) hrZ (call_243 _) hcF hF0 fr_243
    (by rw [hspZ]; exact stk E.wf (by omega) (by omega) (by omega)) ?_
  rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
  rw [hspZ] at hA₂
  have esp₂ : Y₂.cpu.gpr.rsp = S56 g0.rsp - 8 := by
    rw [hg₂]
    show Z.cpu.gpr.rsp - 8 = _
    rw [hspZ]
  refine hfre Y₂ t₂ _ _ hK₂ hA₂ hr₂ esp₂ (rds (by rw [e64]; omega)) ?_
  intro W t' V'' hKW hAW hkp hrW hspW _
  exact t248 c hfs E hKW hAW hrW hspW (agC hS E.kf hag hkp) k

end

end FV7z.Ild
