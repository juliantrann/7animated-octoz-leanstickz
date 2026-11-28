import FV7z.Cpd.Tail
import FV7z.Cpd.Loop
/-!
# `NCommandLineParser::CParser::~CParser` (PLAN.md §M, M1)

7-Zip 26.06's `CParser::~CParser (this)` at `0x5a0500` in `7zzs` (`CPP/Common/CommandLineParser.cpp`; `objdump -d`),
from its entry: `r14`, `r13`, `r12`, `rbp`, `rbx` pushed, `r12` = `this`, `b` = `_switches` (the 8 bytes at `this`).
When `b` is 0, to 170 (`FV7z/Cpd/Tail.lean`); else `N` the 8 bytes at `b - 8` (`delete []`'s count), `rbx` =
`b + 24 N`: to 157 when `N` is 0, else to the loop over the items from 48 (`FV7z/Cpd/Inner.lean`).

- `Vp`: the bytes after the pushes; `sz24 c`: `rsi` from the count `c` (`24 c`, `sz24_eq`).
- `vc_0z`, `vc_0e`, `vc_0l`: the entry's verification conditions; `cpd_ok`: the function, from its entry to the return
  address or to `0x6014f0` (the tail call).
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Cpd

/-- The bytes after the pushes of `r14`, `r13`, `r12`, `rbp`, `rbx`. -/
abbrev Vp (V : Addr → Byte) (g : Gprs) : Addr → Byte :=
  Vst (Vst (Vst (Vst (Vst V (g.rsp - 8) (toBytesLE g.r14 8)) (g.rsp - 8 - 8) (toBytesLE g.r13 8))
    (g.rsp - 8 - 8 - 8) (toBytesLE g.r12 8)) (g.rsp - 8 - 8 - 8 - 8) (toBytesLE g.rbp 8))
    (g.rsp - 8 - 8 - 8 - 8 - 8) (toBytesLE g.rbx 8)

/-- `lea rsi, [rdx + rdx * 2]; shl rsi, 3` from the count `c`. -/
abbrev sz24 (c : BitVec 64) : BitVec 64 := (c + c * 2#64) <<< 3

theorem sz24_eq {N : Nat} (hN : 24 * N < 18446744073709551616) :
    sz24 (BitVec.ofNat 64 N) = BitVec.ofNat 64 (24 * N) := by
  apply BitVec.eq_of_toNat_eq
  simp only [sz24, BitVec.toNat_shiftLeft, BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat, Nat.shiftLeft_eq,
    Nat.reducePow, Nat.reduceMod]
  omega

variable {F : Footprint} {Wl : List Rgn}

section
variable {g : Gprs} {f : Rflags} {V : Addr → Byte}

/-- From the entry with `_switches` 0: the pushes, `r12` = `this`; to 170. -/
theorem vc_0z {b : BitVec 64} (hb : rdq(Vp V g, g.rdi) = b) (hb0 : b = 0)
    (fa : ∀ i < 8, Foot F.data (Addr.add g.rdi i))
    (w1 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8) i)) (w2 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8) i))
    (w3 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8 - 8) i))
    (w4 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8 - 8 - 8) i))
    (w5 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8 - 8 - 8 - 8) i)) :
    W_0 F Wl (fun j' g' _ V' => j' = 170 ∧ V' = Vp V g ∧ Rs g g') g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [Vp] at hb fa w1 w2 w3 w4 w5 ⊢
  have e : (b == 0) = true := beq_iff_eq.2 hb0
  wpx [W_0, W_27, o0, o1, Op.shl64, Rs, hb, e, BitVec.and_self, Bool.false_eq_true, Bool.true_eq_false,
    false_implies, eq_self_iff_true, true_implies, implies_true]
  all_goals repeat' (first
    | with_reducible rfl
    | with_reducible assumption
    | exact rfl
    | exact trivial
    | (intro h; exact absurd h (by decide))
    | apply And.intro
    | intro _)

/-- From the entry with `_switches` = `b` not 0 and `rbx` = `b + sz24 c` = `b`: to 157. -/
theorem vc_0e {b c : BitVec 64} (hb : rdq(Vp V g, g.rdi) = b) (hb0 : b ≠ 0)
    (hc : rdq(Vp V g, b + 18446744073709551608#64) = c) (hs : b = b + sz24 c)
    (fa : ∀ i < 8, Foot F.data (Addr.add g.rdi i))
    (fc : ∀ i < 8, Foot F.data (Addr.add (b + 18446744073709551608#64) i))
    (w1 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8) i)) (w2 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8) i))
    (w3 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8 - 8) i))
    (w4 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8 - 8 - 8) i))
    (w5 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8 - 8 - 8 - 8) i)) :
    W_0 F Wl (fun j' g' _ V' => j' = 157 ∧ V' = Vp V g ∧ Rs g g' ∧ g'.rbx = b + sz24 c) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [Vp] at hb hc fa fc w1 w2 w3 w4 w5 ⊢
  have e : (b == 0) = false := beq_eq_false_iff_ne.2 hb0
  have e2 : decide (b = b + sz24 c) = true := decide_eq_true hs
  wpx [W_0, W_27, o0, o1, Op.shl64, Rs, hb, hc, e, e2, BitVec.and_self, Bool.false_eq_true, Bool.true_eq_false,
    false_implies, eq_self_iff_true, true_implies, implies_true, decide_eq_true_eq, decide_eq_false_iff_not]
  all_goals repeat' (first
    | with_reducible rfl
    | with_reducible assumption
    | exact rfl
    | exact trivial
    | (intro h; exact absurd hs h)
    | (intro h; exact absurd h (by decide))
    | apply And.intro
    | intro _)

/-- From the entry with `_switches` = `b` not 0 and `rbx` = `b + sz24 c` not `b`: to 48. -/
theorem vc_0l {b c : BitVec 64} (hb : rdq(Vp V g, g.rdi) = b) (hb0 : b ≠ 0)
    (hc : rdq(Vp V g, b + 18446744073709551608#64) = c) (hs : b ≠ b + sz24 c)
    (fa : ∀ i < 8, Foot F.data (Addr.add g.rdi i))
    (fc : ∀ i < 8, Foot F.data (Addr.add (b + 18446744073709551608#64) i))
    (w1 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8) i)) (w2 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8) i))
    (w3 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8 - 8) i))
    (w4 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8 - 8 - 8) i))
    (w5 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8 - 8 - 8 - 8) i)) :
    W_0 F Wl (fun j' g' _ V' => j' = 48 ∧ V' = Vp V g ∧ Rs g g' ∧ g'.rbx = b + sz24 c) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [Vp] at hb hc fa fc w1 w2 w3 w4 w5 ⊢
  have e : (b == 0) = false := beq_eq_false_iff_ne.2 hb0
  have e2 : decide (b = b + sz24 c) = false := decide_eq_false hs
  wpx [W_0, W_27, o0, o1, Op.shl64, Rs, hb, hc, e, e2, BitVec.and_self, Bool.false_eq_true, Bool.true_eq_false,
    false_implies, eq_self_iff_true, true_implies, implies_true, decide_eq_true_eq, decide_eq_false_iff_not]
  all_goals repeat' (first
    | with_reducible rfl
    | with_reducible assumption
    | exact rfl
    | exact trivial
    | (intro h; exact absurd h hs)
    | (intro h; exact absurd h (by decide))
    | apply And.intro
    | intro _)

end

/-! ## The function -/

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {X : State} {t : Nat} {V : Addr → Byte}

set_option maxHeartbeats 1000000 in
/-- `~CParser (this)` (`rdi`) from its entry, `b` = `_switches` (the 8 bytes at `this` after the pushes). When `b` is
0, `B0` (`h00`); else `N` its count (`hc`, `24 N` below `2 ^ 64`) and `O N` (`hO`), the items as in `from48` and
`operator delete [] (b - 8, …)` giving `B0` (`hDA`). From `B0` on as in `from170`: the run reaches the return address
with the registers a call keeps when `NonSwitchStrings._items` (`it`) is 0 (`kr`), else `0x6014f0` (`kt`). -/
theorem cpd_ok {b it : BitVec 64} {N : Nat} {n32 : BitVec 32} {B0 B1 : (Addr → Byte) → Prop}
    {O : Nat → (Addr → Byte) → Prop} {H : Nat → Nat → (Addr → Byte) → Prop}
    {JA : Nat → Nat → BitVec 64 → (Addr → Byte) → Prop} {nI : Nat → BitVec 32} {itI : Nat → BitVec 64}
    {I : Nat → (Addr → Byte) → Prop} {J : Nat → BitVec 64 → (Addr → Byte) → Prop}
    {e₂ : Addr} {code₂ : List Byte} {j₂ : Nat}
    (c : Seg prof F Wl L s₀ o) (hin : CodeIn L cpd_at cpd)
    (hin1 : CodeIn L 0x6014f0#64 Tiny.c6014f0) (hin2 : CodeIn L 0x6014e0#64 Tiny.c6014e0)
    (hin3 : CodeIn L 0x601500#64 Tiny.c601500)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = cpd_at)
    (w1 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8) i))
    (w2 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8 - 8) i))
    (w3 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8 - 8 - 8) i))
    (w4 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8 - 8 - 8 - 8) i))
    (w5 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8 - 8 - 8 - 8 - 8) i))
    (w6 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8 - 8 - 8 - 8 - 8 - 8) i))
    (hl : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsp i))
    (hf : Fr X.cpu.gpr (e₂.add j₂) (Vp V X.cpu.gpr))
    -- `_switches`
    (gb : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rdi i))
    (hb : rdq(Vp V X.cpu.gpr, X.cpu.gpr.rdi) = b) (h00 : b = 0 → B0 (Vp V X.cpu.gpr))
    (gc : b ≠ 0 → ∀ i < 8, Foot F.data (Addr.add (b + 18446744073709551608#64) i))
    (hc : b ≠ 0 → rdq(Vp V X.cpu.gpr, b + 18446744073709551608#64) = BitVec.ofNat 64 N)
    (hN : 24 * N < 18446744073709551616) (hO : b ≠ 0 → O N (Vp V X.cpu.gpr))
    (gn : ∀ i < N, ∀ j < 4, Foot F.data (Addr.add (ip b i + 16#64) j))
    (ga : ∀ i < N, ∀ j < 8, Foot F.data (Addr.add (ip b i + 8#64) j))
    (ge : ∀ i < N, ∀ k < (nI i).toNat, ∀ j < 8, Foot F.data (Addr.add (itI i + BitVec.ofNat 64 (8 * k)) j))
    (gp : ∀ i < N, ∀ k < (nI i).toNat, ∀ W, H i (k + 1) W → pk W (itI i) k ≠ 0 →
      ∀ j < 8, Foot F.data (Addr.add (pk W (itI i) k) j))
    (hbA : ∀ i W, O i W → rdq(W, X.cpu.gpr.rdi) = b)
    (hnA : ∀ i < N, ∀ W, O (i + 1) W → rdd(W, ip b i + 16#64) = nI i)
    (hOH : ∀ i < N, ∀ W, O (i + 1) W → H i (nI i).toNat W)
    (hItA : ∀ i < N, ∀ k W, H i k W → rdq(W, ip b i + 8#64) = itI i)
    (hP0A : ∀ i < N, ∀ k < (nI i).toNat, ∀ W, H i (k + 1) W → pk W (itI i) k = 0 → H i k W)
    (hQ0A : ∀ i < N, ∀ k < (nI i).toNat, ∀ W, H i (k + 1) W → pk W (itI i) k ≠ 0 →
      rdq(W, pk W (itI i) k) = 0 → JA i k (pk W (itI i) k) W)
    (hD1A : ∀ i < N, ∀ k < (nI i).toNat, ∀ W, H i (k + 1) W → pk W (itI i) k ≠ 0 →
      rdq(W, pk W (itI i) k) ≠ 0 →
      Call1 prof F Wl L s₀ o gev gP gE X.cpu.gpr.rsp 0x6014f0#64 (cpd_at.add 102)
        (fun g => g.rdi = rdq(W, pk W (itI i) k)) W (JA i k (pk W (itI i) k)))
    (hD2A : ∀ i < N, ∀ k < (nI i).toNat, ∀ p W, p ≠ 0 → JA i k p W →
      Call1 prof F Wl L s₀ o gev gP gE X.cpu.gpr.rsp 0x6014e0#64 (cpd_at.add 115)
        (fun g => g.rdi = p ∧ g.rsi = 16#64) W (H i k))
    (hE0 : ∀ i < N, ∀ W, H i 0 W → itI i = 0 → O i W)
    (hE1 : ∀ i < N, ∀ W, H i 0 W → itI i ≠ 0 →
      Call1 prof F Wl L s₀ o gev gP gE X.cpu.gpr.rsp 0x6014f0#64 (cpd_at.add 139) (fun g => g.rdi = itI i) W (O i))
    (hDA : ∀ W, O 0 W → Call1 prof F Wl L s₀ o gev gP gE X.cpu.gpr.rsp 0x601500#64 (cpd_at.add 170)
      (fun g => g.rdi = b + 18446744073709551608#64) W B0)
    -- from 170
    (f48 : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rdi + 48#64) i))
    (f32 : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rdi + 32#64) i))
    (fn : ∀ i < 4, Foot F.data (Addr.add (X.cpu.gpr.rdi + 16#64) i))
    (fa : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rdi + 8#64) i))
    (fe : ∀ k < n32.toNat, ∀ i < 8, Foot F.data (Addr.add (it + BitVec.ofNat 64 (8 * k)) i))
    (fp : ∀ k < n32.toNat, ∀ W, I (k + 1) W → pk W it k ≠ 0 → ∀ i < 8, Foot F.data (Addr.add (pk W it k) i))
    (hZ1 : ∀ W, B0 W → rdq(W, X.cpu.gpr.rdi + 48#64) = 0 → B1 W)
    (hC1 : ∀ W, B0 W → rdq(W, X.cpu.gpr.rdi + 48#64) ≠ 0 →
      Call1 prof F Wl L s₀ o gev gP gE X.cpu.gpr.rsp 0x6014f0#64 (cpd_at.add 185)
        (fun g => g.rdi = rdq(W, X.cpu.gpr.rdi + 48#64)) W B1)
    (hZ2 : ∀ W, B1 W → rdq(W, X.cpu.gpr.rdi + 32#64) = 0 → I n32.toNat W)
    (hC2 : ∀ W, B1 W → rdq(W, X.cpu.gpr.rdi + 32#64) ≠ 0 →
      Call1 prof F Wl L s₀ o gev gP gE X.cpu.gpr.rsp 0x6014f0#64 (cpd_at.add 200)
        (fun g => g.rdi = rdq(W, X.cpu.gpr.rdi + 32#64)) W (I n32.toNat))
    (hn : ∀ W, I n32.toNat W → rdd(W, X.cpu.gpr.rdi + 16#64) = n32)
    (hIt : ∀ k W, I k W → rdq(W, X.cpu.gpr.rdi + 8#64) = it)
    (hP0 : ∀ k < n32.toNat, ∀ W, I (k + 1) W → pk W it k = 0 → I k W)
    (hQ0 : ∀ k < n32.toNat, ∀ W, I (k + 1) W → pk W it k ≠ 0 → rdq(W, pk W it k) = 0 → J k (pk W it k) W)
    (hD1 : ∀ k < n32.toNat, ∀ W, I (k + 1) W → pk W it k ≠ 0 → rdq(W, pk W it k) ≠ 0 →
      Call1 prof F Wl L s₀ o gev gP gE X.cpu.gpr.rsp 0x6014f0#64 (cpd_at.add 247)
        (fun g => g.rdi = rdq(W, pk W it k)) W (J k (pk W it k)))
    (hD2 : ∀ k < n32.toNat, ∀ p W, p ≠ 0 → J k p W →
      Call1 prof F Wl L s₀ o gev gP gE X.cpu.gpr.rsp 0x6014e0#64 (cpd_at.add 260)
        (fun g => g.rdi = p ∧ g.rsi = 16#64) W (I k))
    (hin₂ : CodeIn L e₂ code₂) (h₂ : j₂ < code₂.length)
    (kt : ∀ (Y : State) (W : Addr → Byte) (t' : Nat), KeptW Wl s₀ Y → Agree F Y.proc.mm.mem W → I 0 W →
      Fr X.cpu.gpr (e₂.add j₂) W → Y.cpu.rip = 0x6014f0#64 → Y.cpu.gpr.rsp = X.cpu.gpr.rsp →
      Y.cpu.gpr.rdi = it → it ≠ 0 → Kp X.cpu.gpr Y.cpu.gpr → GoG prof L o gev gP gE Y t')
    (kr : ∀ (Z : State) (W : Addr → Byte) (t' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem W → I 0 W →
      Z.cpu.rip = e₂.add j₂ → Bk X.cpu.gpr Z.cpu.gpr → it = 0 → GoG prof L o gev gP gE Z t') :
    GoG prof L o gev gP gE X t := by
  have hrip' : X.cpu.rip = cpd_at.add 0 := by rw [addr_add_zero]; exact hrip
  have h170 := from170 (g₀ := X.cpu.gpr) (B0 := B0) (B1 := B1) (I := I) (J := J) c hin hin1 hin2 w1 w2 w3 w4 w5 w6
    hl f48 f32 fn fa fe fp hZ1 hC1 hZ2 hC2 hn hIt hP0 hQ0 hD1 hD2 hin₂ h₂ kt kr
  have h157 := from157 (g₀ := X.cpu.gpr) (P := O 0) c hin hin3 w6 hDA h170
  by_cases hz : b = 0
  · refine (c_0 prof).run c hin _ hK hA hrip' (vc_0z hb hz gb w1 w2 w3 w4 w5) ?_
    rintro j' g fl V₁ ⟨rfl, hV₁, hR⟩ Y t₁ hKY hAY hrY hgY -
    subst V₁
    subst hgY
    exact h170 Y _ t₁ hKY hAY hrY ⟨h00 hz, hf, hR⟩
  · have hcN := hc hz
    by_cases hN0 : N = 0
    · subst hN0
      have hs : b = b + sz24 (BitVec.ofNat 64 0) := by rw [sz24_eq hN]; exact (ip0 b).symm
      refine (c_0 prof).run c hin _ hK hA hrip' (vc_0e hb hz hcN hs gb (gc hz) w1 w2 w3 w4 w5) ?_
      rintro j' g fl V₁ ⟨rfl, hV₁, hR, hbx⟩ Y t₁ hKY hAY hrY hgY -
      subst V₁
      subst hgY
      exact h157 Y _ t₁ hKY hAY hrY ⟨hO hz, hf, hR, hbx.trans hs.symm⟩
    · have hs : b ≠ b + sz24 (BitVec.ofNat 64 N) := by rw [sz24_eq hN]; exact ip_ne b (by omega) hN
      refine (c_0 prof).run c hin _ hK hA hrip' (vc_0l hb hz hcN hs gb (gc hz) w1 w2 w3 w4 w5) ?_
      rintro j' g fl V₁ ⟨rfl, hV₁, hR, hbx⟩ Y t₁ hKY hAY hrY hgY -
      subst V₁
      subst hgY
      have e1 : N - 1 + 1 = N := by omega
      exact from48 (g₀ := X.cpu.gpr) c hin hin1 hin2 w6 hN gb (gc hz) gn ga ge gp hbA hnA hOH hItA hP0A hQ0A hD1A
        hD2A hE0 hE1 h157
        (N - 1) (by omega) Y _ t₁ hKY hAY hrY
        ⟨by rw [e1]; exact hO hz, hf, hR, by rw [e1, hbx, sz24_eq hN]⟩

end FV7z.Cpd
