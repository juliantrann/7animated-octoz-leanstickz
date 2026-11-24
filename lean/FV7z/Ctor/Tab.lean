import FV7z.Ctor.Inv
import FV7z.Tun.Inv
/-!
# Arithmetic of the loops that fill tables from the image's counts (PLAN.md §M, constructors)

Facts the constructors `82` and `87` need of their registers, each stated alone so that `bv_omega` sees a small
context and the kernel checks it once.

- `xz`, `xz8`, `w1`: a register zeroed by `xor r32, r32`; the 1 of `mov r32, 1`.
- `shl1`, `nz`, `nz8_t`, `nz8_f`: the shift `1 << s`; `test r32, r32` of a count.
- `bnot_t`, `bnot_f`: the conditions `!decide p` of a `jne`.
- `addB`, `endA`, `inc64`, `inc64_ne`, `inc64_eq`, `eqk_t`, `eqk_f`, `eqk_ne`, `eqk_eq`: 64-bit indices and their
  compares with a register or a constant.
- `zw`, `addw`, `addv`, `inc32w`, `inc32_ne`, `inc32_eq`, `inc32r_ne`, `inc32r_eq`: the same in 32 bits.
- `ta`, `ea4`, `ldx`, `ldx8`, `ld0`: addresses in a table, and a byte loaded from the image's table.
- `InR_ge`: no range of a list that starts above `b` holds an address below it.
-/
namespace FV7z.Ctor
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn FV7z.Start

theorem xz (x : BitVec 64) : (BitVec.setWidth 64 (BitVec.setWidth 32 x ^^^ BitVec.setWidth 32 x)).toNat = 0 := by
  rw [BitVec.xor_self]; decide

theorem xz8 (x : BitVec 64) :
    (BitVec.setWidth 8 (BitVec.setWidth 64 (BitVec.setWidth 32 x ^^^ BitVec.setWidth 32 x))).toNat = 0 := by
  rw [BitVec.xor_self]; decide

theorem w1 : BitVec.setWidth 32 (BitVec.setWidth 64 1#32) = 1#32 := by decide

/-- The shift `1 << s` once its two registers are known. -/
theorem shl1 {x c : BitVec 64} {s : Nat} {y : BitVec 32} (hx : x.setWidth 32 = 1#32) (hc : (c.setWidth 8).toNat = s)
    (h : 1#32 <<< (s % 32) = y) : x.setWidth 32 <<< ((c.setWidth 8).toNat % 32) = y := by
  rw [hx, hc, h]

/-- `test r, r` of a count not 0 never takes the zero branch. -/
theorem nz {N : Nat} (h1 : 1 ≤ N) (h2 : N < 2 ^ 32) (h : (BitVec.ofNat 32 N &&& BitVec.ofNat 32 N == 0) = true) :
    False := by
  rw [BitVec.and_self, beq_iff_eq] at h
  bv_omega

theorem bnot_t {p : Prop} [Decidable p] (h : (!decide p) = true) : ¬ p := fun hp => by simp [hp] at h

theorem bnot_f {p : Prop} [Decidable p] (h : (!decide p) = false) : p := by
  by_cases hp : p
  · exact hp
  · simp [hp] at h

theorem addB {x y : BitVec 64} {a B : Nat} (hx : x.toNat = a) (hy : y = BitVec.ofNat 64 B) (h : B + a < 2 ^ 64) :
    (x + y).toNat = B + a := by
  subst hx hy; bv_omega

theorem endA {x y : BitVec 64} {a B N : Nat} (hx : x.toNat = a) (hy : y = BitVec.ofNat 64 B + 1#64) (h1 : 1 ≤ N)
    (hN : N < 2 ^ 32) (h : B + a + N < 2 ^ 64) :
    (x + y + BitVec.setWidth 64 (BitVec.ofNat 32 N - 1#32)).toNat = B + a + N := by
  subst hx hy; bv_omega

theorem inc64 {x : BitVec 64} {p : Nat} (hx : x.toNat = p) (h : p + 1 < 2 ^ 64) : (x + 1#64).toNat = p + 1 := by
  subst hx; bv_omega

theorem inc64_ne {x y : BitVec 64} {p q : Nat} (hx : x.toNat = p) (hy : y.toNat = q) (h : p + 1 < 2 ^ 64)
    (hb : (!decide (x + 1#64 = y)) = true) : p + 1 ≠ q := fun he => bnot_t hb (by subst hx hy; bv_omega)

theorem inc64_eq {x y : BitVec 64} {p q : Nat} (hx : x.toNat = p) (hy : y.toNat = q) (h : p + 1 < 2 ^ 64)
    (hb : (!decide (x + 1#64 = y)) = false) : p + 1 = q := by
  have e := bnot_f hb; subst hx hy; bv_omega

theorem eqk_t {x : BitVec 64} {d k : Nat} (hx : x.toNat = d) (hk : k < 2 ^ 64) (hd : d + 1 < 2 ^ 64)
    (hb : decide (x + 1#64 = BitVec.ofNat 64 k) = true) : d + 1 = k := by
  have e := of_decide_eq_true hb; subst hx; bv_omega

theorem eqk_f {x : BitVec 64} {d k : Nat} (hx : x.toNat = d) (hk : k < 2 ^ 64) (hd : d + 1 < 2 ^ 64)
    (hb : decide (x + 1#64 = BitVec.ofNat 64 k) = false) : d + 1 ≠ k := fun he =>
  of_decide_eq_false hb (by subst hx; bv_omega)

theorem zw {x : BitVec 64} {a : Nat} (hx : x.toNat = a) (h : a < 2 ^ 32) :
    (BitVec.setWidth 64 (BitVec.setWidth 32 x)).toNat = a := by
  subst hx; bv_omega

theorem addw {x : BitVec 64} {a N : Nat} (hx : x.toNat = a) (h : a + N < 2 ^ 32) :
    (BitVec.setWidth 64 (BitVec.ofNat 32 N + BitVec.setWidth 32 x)).toNat = a + N := by
  subst hx; bv_omega

theorem inc32w {x : BitVec 64} {p : Nat} (hx : x.toNat = p) (h : p + 1 < 2 ^ 32) :
    (BitVec.setWidth 64 (BitVec.setWidth 32 x + 1#32)).toNat = p + 1 := by
  subst hx; bv_omega

theorem inc32_ne {x y : BitVec 64} {p q : Nat} (hx : x.toNat = p) (hy : y.toNat = q) (h : p + 1 < 2 ^ 32)
    (hq : q < 2 ^ 32) (hb : (!decide (BitVec.setWidth 32 x + 1#32 = BitVec.setWidth 32 y)) = true) : p + 1 ≠ q :=
  fun he => bnot_t hb (by subst hx hy; bv_omega)

theorem inc32_eq {x y : BitVec 64} {p q : Nat} (hx : x.toNat = p) (hy : y.toNat = q) (h : p + 1 < 2 ^ 32)
    (hq : q < 2 ^ 32) (hb : (!decide (BitVec.setWidth 32 x + 1#32 = BitVec.setWidth 32 y)) = false) : p + 1 = q := by
  have e := bnot_f hb; subst hx hy; bv_omega

theorem ta {R k : Nat} (h : R + k < 2 ^ 64) : (Addr.add (BitVec.ofNat 64 R) k).toNat = R + k := by
  simp only [Addr.add]; bv_omega

/-- The load `[R + x + 1]` of a byte `v` of the image's table at `R`, as `movzx`'s 64 bits. -/
theorem ldx {V : Addr → Byte} {R d v : Nat} {x : BitVec 64} (hx : x.toNat = d) (hR : R + d + 1 < 2 ^ 64)
    (hv : V (Addr.add (BitVec.ofNat 64 R) (d + 1)) = BitVec.ofNat 8 v) (h : v < 256) :
    (BitVec.setWidth 64 (BitVec.setWidth 32
      (ofBytesLE 8 (List.map V (byteAddrs (BitVec.ofNat 64 R + (x + 1#64)) 1))))).toNat = v := by
  have e : BitVec.ofNat 64 R + (x + 1#64) = Addr.add (BitVec.ofNat 64 R) (d + 1) := by
    subst hx; simp only [Addr.add]; bv_omega
  rw [Tun.rd1, e, hv]
  bv_omega

/-- The same load, its low byte. -/
theorem ldx8 {V : Addr → Byte} {R d v : Nat} {x : BitVec 64} (hx : x.toNat = d) (hR : R + d + 1 < 2 ^ 64)
    (hv : V (Addr.add (BitVec.ofNat 64 R) (d + 1)) = BitVec.ofNat 8 v) (h : v < 256) :
    (BitVec.setWidth 8 (BitVec.setWidth 64 (BitVec.setWidth 32
      (ofBytesLE 8 (List.map V (byteAddrs (BitVec.ofNat 64 R + (x + 1#64)) 1)))))).toNat = v := by
  have e : BitVec.ofNat 64 R + (x + 1#64) = Addr.add (BitVec.ofNat 64 R) (d + 1) := by
    subst hx; simp only [Addr.add]; bv_omega
  rw [Tun.rd1, e, hv]
  bv_omega

/-- No range of `rs` reaches below `b`. -/
theorem InR_ge {b n : Nat} : ∀ {rs : List (Nat × Nat)}, (∀ x ∈ rs, b ≤ x.1) → n < b → ¬ InR rs n
  | [], _, _, h => h.elim
  | (lo, hi) :: rs, hb, hn, h => by
    have h0 := hb (lo, hi) (by simp)
    dsimp only at h0
    rcases h with h | h
    · omega
    · exact InR_ge (fun x hx => hb x (List.mem_cons_of_mem _ hx)) hn h

theorem nz8_t {v : Nat} (h : v < 256)
    (hb : (!(BitVec.setWidth 32 (BitVec.ofNat 8 v) &&& BitVec.setWidth 32 (BitVec.ofNat 8 v) == 0)) = true) :
    1 ≤ v := by
  rcases Nat.eq_zero_or_pos v with hv | hv
  · subst hv; exact absurd hb (by decide)
  · exact hv

theorem nz8_f {v : Nat} (h : v < 256)
    (hb : (!(BitVec.setWidth 32 (BitVec.ofNat 8 v) &&& BitVec.setWidth 32 (BitVec.ofNat 8 v) == 0)) = false) :
    v = 0 := by
  rw [BitVec.and_self] at hb
  have e : (BitVec.setWidth 32 (BitVec.ofNat 8 v) == 0) = true := by
    revert hb; cases (BitVec.setWidth 32 (BitVec.ofNat 8 v) == 0) <;> simp
  rw [beq_iff_eq] at e
  bv_omega

theorem eqk_ne {x : BitVec 64} {d k : Nat} (hx : x.toNat = d) (hk : k < 2 ^ 64) (hd : d + 1 < 2 ^ 64)
    (h : ¬ x + 1#64 = BitVec.ofNat 64 k) : d + 1 ≠ k := fun he => h (by subst hx; bv_omega)

theorem eqk_eq {x : BitVec 64} {d k : Nat} (hx : x.toNat = d) (hk : k < 2 ^ 64) (hd : d + 1 < 2 ^ 64)
    (h : x + 1#64 = BitVec.ofNat 64 k) : d + 1 = k := by
  subst hx; bv_omega

theorem addv {x : BitVec 64} {a v : Nat} (hx : x.toNat = a) (hv : v < 256) (h : a + v < 2 ^ 32) :
    (BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 8 v)) + x))).toNat =
      a + v := by
  subst hx; bv_omega

theorem inc32r_ne {x y : BitVec 64} {p q : Nat} (hx : x.toNat = p) (hy : y.toNat = q) (h : p + 1 < 2 ^ 32)
    (hq : q < 2 ^ 32) (hb : (!decide (BitVec.setWidth 32 y = BitVec.setWidth 32 x + 1#32)) = true) : p + 1 ≠ q :=
  fun he => bnot_t hb (by subst hx hy; bv_omega)

theorem inc32r_eq {x y : BitVec 64} {p q : Nat} (hx : x.toNat = p) (hy : y.toNat = q) (h : p + 1 < 2 ^ 32)
    (hq : q < 2 ^ 32) (hb : (!decide (BitVec.setWidth 32 y = BitVec.setWidth 32 x + 1#32)) = false) : p + 1 = q := by
  have e := bnot_f hb; subst hx hy; bv_omega

theorem ea4 {x : BitVec 64} {B k : Nat} (hx : x.toNat = k) (h : B + 4 * k < 2 ^ 64) :
    (BitVec.ofNat 64 B + x * 4#64).toNat = B + 4 * k := by
  subst hx; bv_omega

/-- The load `[R + x]` of a byte `v` of the image's table at `R`. -/
theorem ld0 {V : Addr → Byte} {R d v : Nat} {x : BitVec 64} (hx : x.toNat = d) (hR : R + d < 2 ^ 64)
    (hv : V (Addr.add (BitVec.ofNat 64 R) d) = BitVec.ofNat 8 v) :
    ofBytesLE 8 (List.map V (byteAddrs (BitVec.ofNat 64 R + x) 1)) = BitVec.ofNat 8 v := by
  have e : BitVec.ofNat 64 R + x = Addr.add (BitVec.ofNat 64 R) d := by
    subst hx; simp only [Addr.add]; bv_omega
  rw [Tun.rd1, e, hv]

end FV7z.Ctor
