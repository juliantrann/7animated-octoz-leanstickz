import FV7z.Ncs.Cuts
import FV7z.Lemmas.LeafRet
import FV7z.Tun.Inv
/-!
# `CCensorNode::NeedCheckSubDirs` (PLAN.md §M, M1)

7-Zip 26.06's `NWildcard::CCensorNode::NeedCheckSubDirs () const` at `0x452fa0` in `7zzs`
(`CPP/Common/Wildcard.cpp`; `objdump -d`): over the `SubNodes` of the node at `p` = `rdi` (`cnt`: the count, the 4
bytes at `p + 48`; `its`: the items, the 8 bytes at `p + 40`; `nd k`: the `k`-th node), the first node with
`ExcludeDirItems` (`exd k`, the byte at `nd k + 16`) set gives that byte, the first with more than one
`IncludeItems` (`inc k`, the count at `nd k + 8`; `big`, as `cmp dword [rdx + 8], 1; ja` has it) gives 1; none, 0.
The result is in `eax`; nothing is stored. Cut points: the entry, the loop's head (47) and 60; the `ret`s at 63, 73.

- `Ok k`: the `k`-th node gives nothing; `Res r`: the result `r`, as a relation; `Fp`: the bytes the loop reads.
- `Inv`, `Fin`, `Nx`: the invariant (the loop: node `i` next, the nodes before it `Ok`, `rcx` the end), the end, and
  the post of `Seg.cfg`; `vc_0`, `vc_47`, `vc_60`: the cut points' conditions.
- `ncs_ok`: from the entry to the return address with `Res` of `rax`.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
open FV7z.Tun (sw_8_32_8)
namespace FV7z.Ncs

/-- The `ret`s. -/
def pret : List Byte := [0xc3]
theorem pret_0 : ∀ feat, Dec feat pret 0 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem w_63 : pret <+: ncs.drop 63 := by decide +kernel
theorem ret_63 (feat : Features) : Dec feat ncs 63 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 63) (k := 0) (pret_0 feat) w_63 (Nat.zero_le _)
theorem w_73 : pret <+: ncs.drop 73 := by decide +kernel
theorem ret_73 (feat : Features) : Dec feat ncs 73 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 73) (k := 0) (pret_0 feat) w_73 (Nat.zero_le _)

/-- The count of `SubNodes`. -/
abbrev cnt (V : Addr → Byte) (p : Addr) : BitVec 32 := rdd(V, p + 48#64)
/-- The items of `SubNodes`. -/
abbrev its (V : Addr → Byte) (p : Addr) : Addr := rdq(V, p + 40#64)
/-- The end of the items, as `lea rcx, [rax + rdx * 8 + 8]` has it. -/
abbrev cE (V : Addr → Byte) (p : Addr) : Addr := its V p + BitVec.setWidth 64 (cnt V p - 1#32) * 8#64 + 8#64
/-- The `k`-th node. -/
abbrev nd (V : Addr → Byte) (p : Addr) (k : Nat) : Addr := rdq(V, Addr.add (its V p) (8 * k))
/-- Its `ExcludeDirItems`. -/
abbrev exd (V : Addr → Byte) (p : Addr) (k : Nat) : BitVec 8 :=
  ofBytesLE 8 (List.map V (byteAddrs (nd V p k + 16#64) 1))
/-- The count of its `IncludeItems`. -/
abbrev inc (V : Addr → Byte) (p : Addr) (k : Nat) : BitVec 32 := rdd(V, nd V p k + 8#64)

/-- More than 1: `cmp x, 1; ja` taken, as the model has it (`big_iff`). -/
def big (x : BitVec 32) : Bool := !(decide (x.toNat < 1) || decide (x = 1#32))

theorem big_iff (x : BitVec 32) : big x = true ↔ 1 < x.toNat := by
  unfold big
  by_cases a : x.toNat < 1
  · rw [decide_eq_true a]
    exact ⟨fun h => absurd h (by simp), fun h => absurd h (by omega)⟩
  · by_cases b : x = 1#32
    · subst b
      decide
    · rw [decide_eq_false a, decide_eq_false b]
      have : x.toNat ≠ 1 := fun e => b (BitVec.eq_of_toNat_eq (by simpa using e))
      exact ⟨fun _ => by omega, fun _ => rfl⟩

/-- The `k`-th node gives nothing. -/
def Ok (V : Addr → Byte) (p : Addr) (k : Nat) : Prop := exd V p k = 0 ∧ big (inc V p k) = false

/-- The result `r`: 0 if every node is `Ok`, else from the first node that is not, its `ExcludeDirItems` if set,
else 1. -/
def Res (V : Addr → Byte) (p : Addr) (r : Nat) : Prop :=
  ((∀ k < (cnt V p).toNat, Ok V p k) ∧ r = 0) ∨
  ∃ i < (cnt V p).toNat, (∀ k < i, Ok V p k) ∧
    ((exd V p i ≠ 0 ∧ r = (exd V p i).toNat) ∨ (exd V p i = 0 ∧ big (inc V p i) = true ∧ r = 1))

/-- The bytes read: the count, the items (if any), and for each node its pointer, its byte at 16 and (if that is 0)
its 4 bytes at 8. -/
def Fp (F : Footprint) (V : Addr → Byte) (p : Addr) : Prop :=
  (∀ i < 4, Foot F.data (Addr.add (p + 48#64) i)) ∧ (cnt V p ≠ 0 → ∀ i < 8, Foot F.data (Addr.add (p + 40#64) i)) ∧
  ∀ k < (cnt V p).toNat, (∀ i < 8, Foot F.data (Addr.add (Addr.add (its V p) (8 * k)) i)) ∧
    (∀ i < 1, Foot F.data (Addr.add (nd V p k + 16#64) i)) ∧
    (exd V p k = 0 → ∀ i < 4, Foot F.data (Addr.add (nd V p k + 8#64) i))

/-- At the loop's head: node `i` next, the nodes before it `Ok`. -/
def I47 (g₀ : Gprs) (V₀ : Addr → Byte) (n : Nat) (g : Gprs) : Prop :=
  ∃ i < (cnt V₀ g₀.rdi).toNat, n = (cnt V₀ g₀.rdi).toNat - i ∧ (∀ k < i, Ok V₀ g₀.rdi k) ∧
    ∃ d x, g = { g₀ with rax := Addr.add (its V₀ g₀.rdi) (8 * i), rcx := cE V₀ g₀.rdi, rdx := d, r8 := x }
/-- At 60: the result in `r8d`. -/
def I60 (g₀ : Gprs) (V₀ : Addr → Byte) (g : Gprs) : Prop :=
  ∃ a c d x, g = { g₀ with rax := a, rcx := c, rdx := d, r8 := x } ∧ x.toNat < 2 ^ 32 ∧ Res V₀ g₀.rdi x.toNat
/-- The invariant at the cut points. -/
def Inv (g₀ : Gprs) (V₀ : Addr → Byte) (ℓ n : Nat) (g : Gprs) (V : Addr → Byte) : Prop :=
  V = V₀ ∧ ((ℓ = 0 ∧ n = (cnt V₀ g₀.rdi).toNat + 1 ∧ g = g₀) ∨ (ℓ = 47 ∧ I47 g₀ V₀ n g) ∨
    (ℓ = 60 ∧ n = 0 ∧ I60 g₀ V₀ g))
/-- At a `ret`: the result in `rax`. -/
def Fin (g₀ : Gprs) (V₀ : Addr → Byte) (j : Nat) (g : Gprs) (V : Addr → Byte) : Prop :=
  V = V₀ ∧ (j = 63 ∨ j = 73) ∧ ∃ a c d x, g = { g₀ with rax := a, rcx := c, rdx := d, r8 := x } ∧
    Res V₀ g₀.rdi a.toNat
/-- At an exit: a cut point's invariant with a smaller measure, or a `ret`. -/
def Nx (g₀ : Gprs) (V₀ : Addr → Byte) (n : Nat) : Post :=
  fun j' g' _ V' => (∃ n' < n, Inv g₀ V₀ j' n' g' V') ∨ Fin g₀ V₀ j' g' V'

theorem step8 (a : Addr) (i : Nat) : Addr.add a (8 * i) + 8#64 = Addr.add a (8 * (i + 1)) := by
  apply BitVec.eq_of_toNat_eq
  simp only [Addr.add, BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

theorem tn88 (b : BitVec 8) : (BitVec.setWidth 64 (BitVec.setWidth 32 b)).toNat = b.toNat := by
  have := b.isLt
  simp only [BitVec.toNat_setWidth]
  omega

theorem tn64 (x : BitVec 64) (h : x.toNat < 2 ^ 32) : (BitVec.setWidth 64 (BitVec.setWidth 32 x)).toNat = x.toNat := by
  simp only [BitVec.toNat_setWidth]
  omega

theorem ok_succ {V : Addr → Byte} {p : Addr} {i : Nat} (hok : ∀ k < i, Ok V p k) (hb : exd V p i = 0)
    (hB : big (inc V p i) = false) : ∀ k < i + 1, Ok V p k := by
  intro k hk
  by_cases h : k < i
  · exact hok k h
  · obtain rfl : k = i := by omega
    exact ⟨hb, hB⟩

variable {g₀ : Gprs} {V₀ : Addr → Byte}

theorem e60 {n : Nat} (hn : 0 < n) {a c d x : BitVec 64} (hx : x.toNat < 2 ^ 32) (hr : Res V₀ g₀.rdi x.toNat)
    {g' : Gprs} {fl : Rflags} (hg : g' = { g₀ with rax := a, rcx := c, rdx := d, r8 := x }) :
    Nx g₀ V₀ n 60 g' fl V₀ :=
  Or.inl ⟨0, hn, rfl, Or.inr (Or.inr ⟨rfl, rfl, a, c, d, x, hg, hx, hr⟩)⟩

theorem e47 {n i : Nat} (hi : i < (cnt V₀ g₀.rdi).toNat) (hn : (cnt V₀ g₀.rdi).toNat - i < n)
    (hok : ∀ k < i, Ok V₀ g₀.rdi k) {d x : BitVec 64} {g' : Gprs} {fl : Rflags}
    (hg : g' = { g₀ with rax := Addr.add (its V₀ g₀.rdi) (8 * i), rcx := cE V₀ g₀.rdi, rdx := d, r8 := x }) :
    Nx g₀ V₀ n 47 g' fl V₀ :=
  Or.inl ⟨_, hn, rfl, Or.inr (Or.inl ⟨rfl, i, hi, rfl, hok, d, x, hg⟩)⟩

theorem e47z {n : Nat} (hi : 0 < (cnt V₀ g₀.rdi).toNat) (hn : (cnt V₀ g₀.rdi).toNat < n) {d x : BitVec 64}
    {g' : Gprs} {fl : Rflags}
    (hg : g' = { g₀ with rax := its V₀ g₀.rdi, rcx := cE V₀ g₀.rdi, rdx := d, r8 := x }) :
    Nx g₀ V₀ n 47 g' fl V₀ :=
  e47 hi (by omega) (fun k hk => absurd hk (Nat.not_lt_zero _)) (by rw [hg, Nat.mul_zero, addr_add_zero])

theorem e47s {n i : Nat} (hi : i + 1 < (cnt V₀ g₀.rdi).toNat) (hn : (cnt V₀ g₀.rdi).toNat - (i + 1) < n)
    (hok : ∀ k < i + 1, Ok V₀ g₀.rdi k) {d x : BitVec 64} {g' : Gprs} {fl : Rflags}
    (hg : g' = { g₀ with rax := Addr.add (its V₀ g₀.rdi) (8 * i) + 8#64, rcx := cE V₀ g₀.rdi, rdx := d, r8 := x }) :
    Nx g₀ V₀ n 47 g' fl V₀ :=
  e47 hi hn hok (by rw [hg, step8])

theorem eFin {n j : Nat} (hj : j = 63 ∨ j = 73) {a c d x : BitVec 64} (hr : Res V₀ g₀.rdi a.toNat)
    {g' : Gprs} {fl : Rflags} (hg : g' = { g₀ with rax := a, rcx := c, rdx := d, r8 := x }) :
    Nx g₀ V₀ n j g' fl V₀ :=
  Or.inr ⟨rfl, hj, a, c, d, x, hg, hr⟩

variable {F : Footprint} {Wl : List Rgn}

/-- The entry: no nodes, to 60 with `r8` 0; else to the loop's head with node 0 next. -/
theorem vc_0 {f : Rflags} (hF : Fp F V₀ g₀.rdi) :
    W_0 F Wl (Nx g₀ V₀ ((cnt V₀ g₀.rdi).toNat + 1)) g₀ f V₀ := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g₀
  obtain ⟨f48, f40, -⟩ := hF
  dsimp only at f48 f40 ⊢
  wpx [W_0, W_74, W_11, o0, o7, o1, BitVec.and_self, BitVec.xor_self, BitVec.setWidth_zero]
  refine ⟨f48, fun _ => ⟨fun hc _ => ?_, fun hc => ⟨f40 (by simpa using hc), ?_⟩⟩⟩
  · have h0 : (cnt V₀ rdi).toNat = 0 := by
      have e : rdd(V₀, rdi + 48#64) = 0 := by simpa using hc
      simp [cnt, e]
    exact e60 (by omega) (by decide)
      (by exact Or.inl ⟨fun k hk => absurd (show k < (cnt V₀ rdi).toNat from hk) (by omega), rfl⟩) rfl
  · have hne : rdd(V₀, rdi + 48#64) ≠ 0 := by simpa using hc
    have hpos : 0 < (cnt V₀ rdi).toNat :=
      Nat.pos_of_ne_zero fun e => hne (BitVec.eq_of_toNat_eq (by simpa using e))
    exact e47z (by exact hpos) (by dsimp only; omega) rfl

/-- The `ret` at 73: node `i` the first not `Ok`, its byte at 16 0 and its count at 8 past 1; 1. -/
theorem eFin1 {n i : Nat} (hi : i < (cnt V₀ g₀.rdi).toNat) (hok : ∀ k < i, Ok V₀ g₀.rdi k)
    (hb : exd V₀ g₀.rdi i = 0) (hB : big (inc V₀ g₀.rdi i) = true) {a c d x : BitVec 64} (ha : a.toNat = 1)
    {g' : Gprs} {fl : Rflags} (hg : g' = { g₀ with rax := a, rcx := c, rdx := d, r8 := x }) :
    Nx g₀ V₀ n 73 g' fl V₀ :=
  eFin (Or.inr rfl) (Or.inr ⟨i, hi, hok, Or.inr ⟨hb, hB, ha⟩⟩) hg

/-- At the loop's end, `rax + 8 = rcx`: node `i` the last. -/
theorem end_eq {s : Addr} {c : BitVec 32} {i : Nat} (hi : i < c.toNat)
    (h : Addr.add s (8 * i) + 8#64 = s + BitVec.setWidth 64 (c - 1#32) * 8#64 + 8#64) : i + 1 = c.toNat := by
  have := s.isLt
  have := c.isLt
  have h' := congrArg BitVec.toNat h
  simp only [Addr.add, BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_setWidth, BitVec.toNat_sub,
    BitVec.toNat_ofNat] at h'
  omega

/-- Every node `Ok` when the nodes before `i + 1` are and node `i` is the last. -/
theorem all_end {V : Addr → Byte} {p : Addr} {i : Nat} (hok : ∀ k < i + 1, Ok V p k)
    (e : i + 1 = (cnt V p).toNat) : ∀ k < (cnt V p).toNat, Ok V p k :=
  fun k hk => hok k (Nat.lt_of_lt_of_eq hk e.symm)

/-- Not at the loop's end: a node after `i`. -/
theorem end_lt {s : Addr} {c : BitVec 32} {i : Nat} (hi : i < c.toNat)
    (h : ¬ (Addr.add s (8 * i) + 8#64 = s + BitVec.setWidth 64 (c - 1#32) * 8#64 + 8#64)) : i + 1 < c.toNat := by
  refine Nat.lt_of_le_of_ne hi fun e => h (BitVec.eq_of_toNat_eq ?_)
  have := s.isLt
  have := c.isLt
  simp only [Addr.add, BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_setWidth, BitVec.toNat_sub,
    BitVec.toNat_ofNat]
  omega

/-- The state at the loop's head, node `i` next. -/
abbrev G47 (g₀ : Gprs) (V₀ : Addr → Byte) (i : Nat) (d x : BitVec 64) : Gprs :=
  { g₀ with rax := Addr.add (its V₀ g₀.rdi) (8 * i), rcx := cE V₀ g₀.rdi, rdx := d, r8 := x }

set_option maxHeartbeats 1000000 in
/-- The loop's head, node `i` with its byte at 16 set: that byte, 60. -/
theorem vc_47a {i : Nat} {d x : BitVec 64} {f : Rflags} (hF : Fp F V₀ g₀.rdi) (hi : i < (cnt V₀ g₀.rdi).toNat)
    (hok : ∀ k < i, Ok V₀ g₀.rdi k) (hb0 : ¬ exd V₀ g₀.rdi i = 0) :
    W_47 F Wl (Nx g₀ V₀ ((cnt V₀ g₀.rdi).toNat - i)) (G47 g₀ V₀ i d x) f V₀ := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g₀
  obtain ⟨-, -, fk⟩ := hF
  obtain ⟨fa, fb, -⟩ := fk i hi
  dsimp only [G47] at hi hok fa fb hb0 ⊢
  have hb := hb0
  dsimp only [exd, nd, its] at hb
  have hx : (BitVec.setWidth 64 (BitVec.setWidth 32 (exd V₀ rdi i))).toNat < 2 ^ 32 := by
    rw [tn88]
    have := (exd V₀ rdi i).isLt
    omega
  have hr : Res V₀ rdi (BitVec.setWidth 64 (BitVec.setWidth 32 (exd V₀ rdi i))).toNat :=
    Or.inr ⟨i, hi, hok, Or.inl ⟨hb0, tn88 _⟩⟩
  have hn : 0 < (cnt V₀ rdi).toNat - i := by omega
  dsimp only [cE, cnt, its] at ⊢
  wpx [W_47, W_32, W_64, W_38, o4, o2, o6, o3, Op.cmpmi, hb, BitVec.and_self, sw_8_32_8, beq_iff_eq,
    beq_eq_false_iff_ne, ne_eq, not_true_eq_false, not_false_eq_true, false_implies, Bool.true_eq_false,
    Bool.false_eq_true, implies_true]
  all_goals repeat' (first
    | with_reducible exact fa
    | with_reducible exact fb
    | apply And.intro
    | intro)
  exact e60 (by exact hn) (by exact hx) (by exact hr) rfl

set_option maxHeartbeats 1000000 in
/-- The loop's head, node `i` with its byte at 16 0 and its count at 8 past 1: 1, the `ret` at 73. -/
theorem vc_47b {i : Nat} {d x : BitVec 64} {f : Rflags} (hF : Fp F V₀ g₀.rdi) (hi : i < (cnt V₀ g₀.rdi).toNat)
    (hok : ∀ k < i, Ok V₀ g₀.rdi k) (hb0 : exd V₀ g₀.rdi i = 0) (hB0 : big (inc V₀ g₀.rdi i) = true) :
    W_47 F Wl (Nx g₀ V₀ ((cnt V₀ g₀.rdi).toNat - i)) (G47 g₀ V₀ i d x) f V₀ := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g₀
  obtain ⟨-, -, fk⟩ := hF
  obtain ⟨fa, fb, fc⟩ := fk i hi
  dsimp only [G47] at hi hok fa fb fc hb0 hB0 ⊢
  have hb := hb0
  dsimp only [exd, nd, its] at hb
  have hB := hB0
  dsimp only [inc, nd, its] at hB
  unfold big at hB
  dsimp only [cE, cnt, its] at ⊢
  wpx [W_47, W_32, W_64, W_38, o4, o2, o6, o3, Op.cmpmi, hb, hB, BitVec.and_self, sw_8_32_8,
    BitVec.setWidth_zero, beq_iff_eq, beq_eq_false_iff_ne, ne_eq, beq_self_eq_true, not_true_eq_false,
    not_false_eq_true, false_implies, Bool.true_eq_false, Bool.false_eq_true, implies_true]
  all_goals repeat' (first
    | with_reducible exact fa
    | with_reducible exact fb
    | with_reducible exact fc hb0
    | apply And.intro
    | intro)
  exact eFin1 (by exact hi) (by exact hok) (by exact hb0) (by exact hB0) (by first | decide | simp) rfl

set_option maxHeartbeats 1000000 in
/-- The loop's head, node `i` `Ok`: the next node, or 60 with `r8` 0 after the last. -/
theorem vc_47c {i : Nat} {d x : BitVec 64} {f : Rflags} (hF : Fp F V₀ g₀.rdi) (hi : i < (cnt V₀ g₀.rdi).toNat)
    (hok : ∀ k < i, Ok V₀ g₀.rdi k) (hb0 : exd V₀ g₀.rdi i = 0) (hB1 : big (inc V₀ g₀.rdi i) = false) :
    W_47 F Wl (Nx g₀ V₀ ((cnt V₀ g₀.rdi).toNat - i)) (G47 g₀ V₀ i d x) f V₀ := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g₀
  obtain ⟨-, -, fk⟩ := hF
  obtain ⟨fa, fb, fc⟩ := fk i hi
  dsimp only [G47] at hi hok fa fb fc hb0 hB1 ⊢
  have hb := hb0
  dsimp only [exd, nd, its] at hb
  have hB := hB1
  dsimp only [inc, nd, its] at hB
  unfold big at hB
  have hok' := ok_succ hok hb0 hB1
  dsimp only [cE, cnt, its] at hi hok' ⊢
  wpx [W_47, W_32, W_64, W_38, o4, o2, o6, o3, Op.cmpmi, hb, hB, BitVec.and_self, sw_8_32_8,
    BitVec.setWidth_zero, beq_iff_eq, beq_eq_false_iff_ne, ne_eq, beq_self_eq_true, not_true_eq_false,
    not_false_eq_true, false_implies, Bool.true_eq_false, Bool.false_eq_true, implies_true]
  all_goals repeat' (first
    | with_reducible exact fa
    | with_reducible exact fb
    | with_reducible exact fc hb0
    | apply And.intro
    | intro)
  all_goals rename_i hc
  all_goals first
    | exact e60 (by omega) (by first | decide | simp)
        (by exact Or.inl ⟨all_end hok' (end_eq hi (of_decide_eq_true hc)), by first | decide | simp⟩) rfl
    | exact e47s (by exact end_lt hi (of_decide_eq_false hc)) (by dsimp only [cnt]; omega) (by exact hok') rfl

/-- The loop's head, node `i`: its byte at 16 set, to 60; its count at 8 past 1, to the `ret` at 73; else the next
node, or 60 with `r8` 0 after the last. -/
theorem vc_47 {n : Nat} {g : Gprs} {f : Rflags} (hF : Fp F V₀ g₀.rdi) (h : I47 g₀ V₀ n g) :
    W_47 F Wl (Nx g₀ V₀ n) g f V₀ := by
  obtain ⟨i, hi, rfl, hok, d, x, rfl⟩ := h
  by_cases hb0 : exd V₀ g₀.rdi i = 0
  · by_cases hB0 : big (inc V₀ g₀.rdi i) = true
    · exact vc_47b hF hi hok hb0 hB0
    · exact vc_47c hF hi hok hb0 (by simpa using hB0)
  · exact vc_47a hF hi hok hb0

/-- 60: `mov eax, r8d`, to the `ret` at 63. -/
theorem vc_60 {g : Gprs} {f : Rflags} (h : I60 g₀ V₀ g) : W_60 F Wl (Nx g₀ V₀ 0) g f V₀ := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g₀
  obtain ⟨a, c, d, x, rfl, hx, hr⟩ := h
  dsimp only at hr ⊢
  wpx [W_60, o5]
  exact eFin (Or.inl rfl) (by rw [tn64 x hx]; exact hr) rfl

theorem vcAll (hF : Fp F V₀ g₀.rdi) (ℓ n : Nat) (g : Gprs) (f : Rflags) (V : Addr → Byte)
    (h : Inv g₀ V₀ ℓ n g V) : Wt ℓ F Wl (Nx g₀ V₀ n) g f V := by
  obtain ⟨rfl, ⟨rfl, rfl, rfl⟩ | ⟨rfl, h⟩ | ⟨rfl, rfl, h⟩⟩ := h
  · exact vc_0 hF
  · exact vc_47 hF h
  · exact vc_60 h

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {X : State} {t : Nat} {V : Addr → Byte}

/-- `CCensorNode::NeedCheckSubDirs ()` from its entry to the return address: `rax` the result (`Res`), `rcx`,
`rdx`, `r8` changed, nothing stored. -/
theorem ncs_ok (c : Seg prof F Wl L s₀ o) (hin : CodeIn L ncs_at ncs) (hK : KeptW Wl s₀ X)
    (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = ncs_at) (hF : Fp F V X.cpu.gpr.rdi)
    (hl : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsp i))
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (hra : rdq(V, X.cpu.gpr.rsp) = e₂.add j₂)
    (k : ∀ (Z : State) (t' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V → Z.cpu.rip = e₂.add j₂ →
      (∃ a c d x, Z.cpu.gpr = { X.cpu.gpr with rax := a, rcx := c, rdx := d, r8 := x }.set 4 (X.cpu.gpr.rsp + 8) ∧
        Res V X.cpu.gpr.rdi a.toNat) →
      GoG prof L o gev gP gE Z t') :
    GoG prof L o gev gP gE X t := by
  refine c.cfg hin (fun ℓ => spAll prof ℓ) (fun ℓ n g _ V' => Inv X.cpu.gpr V ℓ n g V')
    (fun j g _ V' => Fin X.cpu.gpr V j g V') (fun ℓ n g f V' h => vcAll hF ℓ n g f V' h) ?_
    ((cnt V X.cpu.gpr.rdi).toNat + 1) 0 hK hA (by rw [addr_add_zero]; exact hrip) ⟨rfl, Or.inl ⟨rfl, rfl, rfl⟩⟩
  rintro j g fl V' ⟨hV, hj, a, c', d, x, rfl, hr⟩ Y t' hKY hAY hrY hgY -
  subst hV
  have hsY : Y.cpu.gpr.rsp = X.cpu.gpr.rsp := by rw [hgY]
  rcases hj with rfl | rfl
  · refine c.s_ret hKY hAY hin (lt_len (by decide)) hrY (ret_63 _) (by rw [hsY]; exact hl) hin₂ h₂
      (by rw [hsY]; exact hra) ?_
    rintro Z t₂ hKZ hAZ ⟨hrZ, hgZ⟩
    exact k Z t₂ hKZ hAZ hrZ ⟨a, c', d, x, by rw [hgZ, hsY, hgY], hr⟩
  · refine c.s_ret hKY hAY hin (lt_len (by decide)) hrY (ret_73 _) (by rw [hsY]; exact hl) hin₂ h₂
      (by rw [hsY]; exact hra) ?_
    rintro Z t₂ hKZ hAZ ⟨hrZ, hgZ⟩
    exact k Z t₂ hKZ hAZ hrZ ⟨a, c', d, x, by rw [hgZ, hsY, hgY], hr⟩

end FV7z.Ncs
