import FV7z.Ctor.BlkRet
/-!
# Loops that fill a table (PLAN.md §M, constructors)

Helpers for a constructor whose loop stores into a table at a fixed address `b`: the table's bytes from `b` up to
`b + m` are in `Wl`, and the bytes outside it stay as at the entry (`Raf.Out`). Each is stated for a variable `b`, so
the kernel checks the arithmetic once and never folds the table's literal address.

- `ft_at`, `out_at`: bytes at an address `a` inside the table are in `Wl`, and a store there keeps `Raf.Out`.
- `toNat_bx`, `ft_bx`, `out_bx`: the same for the address `b + x`, `x` an index into the table.
- `toNat_m4`, `ft_b4`, `out_b4`: the same for the address `b + 4·x`, `x` the index of a word; `toNat_m2`, `ft_b2`,
  `out_b2`: of a 16-bit word, at `b + 2·x`; `toNat_m8`, `ft_b8`, `out_b8`: of a quadword, at `b + 8·x`.
- `dec32`: a loop's count one less; `inc_k`: an index below 256 one more, and the test `cmp x, 256`.
- `Kp.of`: `Kp` from the registers a call keeps, each as before; it never compares the other registers.
-/
namespace FV7z.Ctor
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn FV7z.Start

/-- `n` bytes at `a` in `Wl`, from the table's `m` bytes at `b`. -/
theorem ft_at {R : List Rgn} {b m : Nat} (h : ∀ i < m, Foot R (Addr.add (BitVec.ofNat 64 b) i))
    (hb : b + m ≤ 2 ^ 64) {a : Addr} {n : Nat} (h1 : b ≤ a.toNat) (h2 : a.toNat + n ≤ b + m) :
    ∀ i < n, Foot R (Addr.add a i) := fun i hi => by
  have e : Addr.add (BitVec.ofNat 64 b) (a.toNat - b + i) = Addr.add a i := by
    simp only [Addr.add]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  rw [← e]
  exact h _ (by omega)

/-- A store of `n` bytes at `a`, inside the table, keeps the bytes outside it. -/
theorem out_at {b m n : Nat} {V₀ V : Addr → Byte} {a : Addr} {bs : List Byte} (hO : Raf.Out b (b + m) V₀ V)
    (hn : bs.length = n) (h1 : b ≤ a.toNat) (h2 : a.toNat + n ≤ b + m) (hb : b + m ≤ 2 ^ 64) :
    Raf.Out b (b + m) V₀ (Vst V a bs) :=
  hO.trans ((Raf.Out.vst hn (by omega)).mono h1 h2)

/-- The address `x` past `b`, when it does not wrap. -/
theorem toNat_bx {b : Nat} {x : BitVec 64} (h : b + x.toNat < 2 ^ 64) :
    (BitVec.ofNat 64 b + x).toNat = b + x.toNat := by
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

/-- `n` bytes at `x` past `b` in `Wl`, from the table's `m` bytes. -/
theorem ft_bx {R : List Rgn} {b m : Nat} (h : ∀ i < m, Foot R (Addr.add (BitVec.ofNat 64 b) i))
    (hb : b + m < 2 ^ 64) {x : BitVec 64} {n : Nat} (hx : x.toNat + n ≤ m) :
    ∀ i < n, Foot R (Addr.add (BitVec.ofNat 64 b + x) i) := by
  have e : (BitVec.ofNat 64 b + x).toNat = b + x.toNat := toNat_bx (by omega)
  exact ft_at h (by omega) (by rw [e]; omega) (by rw [e]; omega)

/-- A store of `n` bytes at `x` past `b`, inside the table, keeps the bytes outside it. -/
theorem out_bx {b m n : Nat} {V₀ V : Addr → Byte} {x : BitVec 64} {bs : List Byte} (hO : Raf.Out b (b + m) V₀ V)
    (hb : b + m < 2 ^ 64) (hx : x.toNat + n ≤ m) (hn : bs.length = n) :
    Raf.Out b (b + m) V₀ (Vst V (BitVec.ofNat 64 b + x) bs) := by
  have e : (BitVec.ofNat 64 b + x).toNat = b + x.toNat := toNat_bx (by omega)
  exact out_at hO hn (by rw [e]; omega) (by rw [e]; omega) (by omega)

/-- Four times `x`, when it does not wrap. -/
theorem toNat_m4 {x : BitVec 64} (h : 4 * x.toNat < 2 ^ 64) : (x * 4#64).toNat = 4 * x.toNat := by
  simp only [BitVec.toNat_mul, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
  omega

/-- The word `x` of the table in `Wl`. -/
theorem ft_b4 {R : List Rgn} {b m : Nat} (h : ∀ i < m, Foot R (Addr.add (BitVec.ofNat 64 b) i))
    (hb : b + m < 2 ^ 64) {x : BitVec 64} (hx : 4 * x.toNat + 4 ≤ m) :
    ∀ i < 4, Foot R (Addr.add (BitVec.ofNat 64 b + x * 4#64) i) := by
  have e : (x * 4#64).toNat = 4 * x.toNat := toNat_m4 (by omega)
  exact ft_bx h hb (by rw [e]; omega)

/-- A store of the word `x` of the table keeps the bytes outside it. -/
theorem out_b4 {b m : Nat} {V₀ V : Addr → Byte} {x : BitVec 64} {bs : List Byte} (hO : Raf.Out b (b + m) V₀ V)
    (hb : b + m < 2 ^ 64) (hx : 4 * x.toNat + 4 ≤ m) (hn : bs.length = 4) :
    Raf.Out b (b + m) V₀ (Vst V (BitVec.ofNat 64 b + x * 4#64) bs) := by
  have e : (x * 4#64).toNat = 4 * x.toNat := toNat_m4 (by omega)
  exact out_bx hO hb (by rw [e]; omega) hn

/-- Two times `x`, when it does not wrap. -/
theorem toNat_m2 {x : BitVec 64} (h : 2 * x.toNat < 2 ^ 64) : (x * 2#64).toNat = 2 * x.toNat := by
  simp only [BitVec.toNat_mul, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
  omega

/-- The 16-bit word `x` of the table in `Wl`. -/
theorem ft_b2 {R : List Rgn} {b m : Nat} (h : ∀ i < m, Foot R (Addr.add (BitVec.ofNat 64 b) i))
    (hb : b + m < 2 ^ 64) {x : BitVec 64} (hx : 2 * x.toNat + 2 ≤ m) :
    ∀ i < 2, Foot R (Addr.add (BitVec.ofNat 64 b + x * 2#64) i) := by
  have e : (x * 2#64).toNat = 2 * x.toNat := toNat_m2 (by omega)
  exact ft_bx h hb (by rw [e]; omega)

/-- A store of the 16-bit word `x` of the table keeps the bytes outside it. -/
theorem out_b2 {b m : Nat} {V₀ V : Addr → Byte} {x : BitVec 64} {bs : List Byte} (hO : Raf.Out b (b + m) V₀ V)
    (hb : b + m < 2 ^ 64) (hx : 2 * x.toNat + 2 ≤ m) (hn : bs.length = 2) :
    Raf.Out b (b + m) V₀ (Vst V (BitVec.ofNat 64 b + x * 2#64) bs) := by
  have e : (x * 2#64).toNat = 2 * x.toNat := toNat_m2 (by omega)
  exact out_bx hO hb (by rw [e]; omega) hn

/-- Eight times `x`, when it does not wrap. -/
theorem toNat_m8 {x : BitVec 64} (h : 8 * x.toNat < 2 ^ 64) : (x * 8#64).toNat = 8 * x.toNat := by
  simp only [BitVec.toNat_mul, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
  omega

/-- The quadword `x` of the table in `Wl`. -/
theorem ft_b8 {R : List Rgn} {b m : Nat} (h : ∀ i < m, Foot R (Addr.add (BitVec.ofNat 64 b) i))
    (hb : b + m < 2 ^ 64) {x : BitVec 64} (hx : 8 * x.toNat + 8 ≤ m) :
    ∀ i < 8, Foot R (Addr.add (BitVec.ofNat 64 b + x * 8#64) i) := by
  have e : (x * 8#64).toNat = 8 * x.toNat := toNat_m8 (by omega)
  exact ft_bx h hb (by rw [e]; omega)

/-- A store of the quadword `x` of the table keeps the bytes outside it. -/
theorem out_b8 {b m : Nat} {V₀ V : Addr → Byte} {x : BitVec 64} {bs : List Byte} (hO : Raf.Out b (b + m) V₀ V)
    (hb : b + m < 2 ^ 64) (hx : 8 * x.toNat + 8 ≤ m) (hn : bs.length = 8) :
    Raf.Out b (b + m) V₀ (Vst V (BitVec.ofNat 64 b + x * 8#64) bs) := by
  have e : (x * 8#64).toNat = 8 * x.toNat := toNat_m8 (by omega)
  exact out_bx hO hb (by rw [e]; omega) hn

/-- An index below 256 one more, and the test `cmp x, 256`: not the end means another round. -/
theorem inc_k {x : BitVec 64} {k : Nat} (hx : x.toNat = k) (hk : k < 256) :
    (x + 1#64).toNat = k + 1 ∧ (¬ x + 1#64 = 256#64 → k + 1 < 256) := by
  subst hx
  constructor
  · bv_omega
  · intro h
    bv_omega

/-- A count from 1 to 8 one less (`sub r32, 1`), when it was not 1. -/
theorem dec32 {x : BitVec 64} (h1 : 1 ≤ x.toNat) (h8 : x.toNat ≤ 8) (hne : ¬ x.setWidth 32 = 1#32) :
    ((x.setWidth 32 - 1#32).setWidth 64).toNat + 1 = x.toNat ∧ 1 ≤ ((x.setWidth 32 - 1#32).setWidth 64).toNat := by
  bv_omega

/-- `Kp` for `g'` from `Kp` for `g`, the registers a call keeps the same in both. Give each as `rfl`: the kernel
then reduces each projection alone. -/
theorem Kp.of {g₀ g g' : Gprs} (h : Kp g₀ g) (e1 : g'.rsp = g.rsp) (e2 : g'.rbx = g.rbx) (e3 : g'.rbp = g.rbp)
    (e4 : g'.r12 = g.r12) (e5 : g'.r13 = g.r13) (e6 : g'.r14 = g.r14) (e7 : g'.r15 = g.r15) : Kp g₀ g' :=
  ⟨e1.trans h.1, e2.trans h.2.1, e3.trans h.2.2.1, e4.trans h.2.2.2.1, e5.trans h.2.2.2.2.1,
    e6.trans h.2.2.2.2.2.1, e7.trans h.2.2.2.2.2.2⟩

end FV7z.Ctor
