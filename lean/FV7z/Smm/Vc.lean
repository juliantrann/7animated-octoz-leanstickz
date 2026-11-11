import FV7z.Smm.Cuts
import FV7z.Sbrk.Holds
/-!
# `sysmalloc`: the verification conditions (PLAN.md G3, `malloc`)

glibc 2.31's `sysmalloc (nb, av)` at `0x630360` in `7zzs` (`malloc/malloc.c`), on the way of the first call: the
main arena (`0x792a40`), its top the initial one (`0x792aa0`, of size 0), the heap contiguous.

- `Hi`, `rd_hi`: a read below the end of the program's data (`0x7a86c0`) through a store above it.
- `and_m4096`: `x &&& -4096`, the page below; `jle_no`: the flags of an `and` with a result above 0.
- `vc_0`: from the entry to the first `call *__morecore` (894): the size asked for is
  `(nb + mp_.top_pad + 4096 + 31) &&& -4096`.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Smm

/-- A store of `k` bytes at `a`, above the program's data. -/
def Hi (a : Addr) (k : Nat) : Prop := 8029888 ≤ a.toNat ∧ a.toNat + k ≤ 2 ^ 64

/-- A read below the end of the program's data, through a store above it. -/
theorem rd_hi {x : Addr} {n : Nat} (hx : x.toNat + n ≤ 8029888) (V : Addr → Byte) {a : Addr} {bs : List Byte}
    (ha : Hi a bs.length) : List.map (Vst V a bs) (byteAddrs x n) = List.map V (byteAddrs x n) :=
  Tun.rd_Vst V a bs x n ha.2 (by have := ha.1; omega) (.inr (by have := ha.1; omega))

theorem nat_and_m4096 (n : Nat) (h : n < 2 ^ 64) : n &&& 18446744073709547520 = n / 4096 * 4096 := by
  have hm : (18446744073709547520 : Nat) = (2 ^ 52 - 1) <<< 12 := by decide
  have hr : n / 4096 * 4096 = (n >>> 12) <<< 12 := by rw [Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
  rw [hm, hr]
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and, Nat.testBit_shiftLeft, Nat.testBit_shiftLeft, Nat.testBit_shiftRight,
    Nat.testBit_two_pow_sub_one]
  by_cases h1 : i ≥ 12
  · have e : 12 + (i - 12) = i := by omega
    rw [e]
    by_cases h2 : i < 64
    · have : i - 12 < 52 := by omega
      simp [h1, this]
    · have h3 : n.testBit i = false :=
        Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le h (Nat.pow_le_pow_right (by decide) (by omega)))
      simp [h3]
  · simp [h1]

/-- `x &&& -4096`: the start of `x`'s page. -/
theorem and_m4096 (x : BitVec 64) : (x &&& (0 - 4096#64)).toNat = x.toNat / 4096 * 4096 := by
  rw [show (0 - 4096#64 : BitVec 64) = 18446744073709547520#64 by decide, BitVec.toNat_and]
  exact nat_and_m4096 _ x.isLt

/-- After an `and` with a result above 0, `jle` is not taken. -/
theorem jle_no (f : Rflags) {R : BitVec 64} (af : Bool) (h0 : 0 < R.toNat) (h1 : R.toNat < 2 ^ 63) :
    (rfz (f.arith R false false af)).cond 14 = false := by
  have hz : (R == 0) = false := by
    apply Bool.eq_false_iff.2
    intro h
    rw [beq_iff_eq] at h
    rw [h] at h0
    exact absurd h0 (by decide)
  have hm : R.msb = false := by
    rw [BitVec.msb_eq_decide]
    exact decide_eq_false (by omega)
  rw [Sbrk.cond_14, Sbrk.rfz_of, Sbrk.arith_of, rfz_zf, rfz_sf, arith_zf, arith_sf, hz, hm]
  rfl

variable {F : Footprint} {Wl : List Rgn}

/-- A byte of the 104 below the stack pointer at the entry. -/
theorem st {sp a : Addr} (hst : ∀ i < 104, Foot Wl (Addr.add (sp - 104) i)) (hs : 104 ≤ sp.toNat)
    (h1 : sp.toNat - 104 ≤ a.toNat) (h2 : a.toNat < sp.toNat) : Foot Wl a := by
  have e : Addr.add (sp - 104) (a.toNat - (sp.toNat - 104)) = a := by
    simp only [Addr.add]
    bv_omega
  exact e ▸ hst (a.toNat - (sp.toNat - 104)) (by omega)

/-- The size `sysmalloc` asks `MORECORE` for, the top being of size 0: `nb + mp_.top_pad + MINSIZE`, to a page. -/
abbrev size (pad nb : BitVec 64) : BitVec 64 := 4096#64 + pad + 31#64 + nb &&& 0 - 4096#64

/-- The bytes at the first `call *__morecore`: the six registers pushed, and the frame's words. -/
abbrev Va (g : Gprs) (V : Addr → Byte) : Addr → Byte :=
  Vst (Vst (Vst (Vst (Vst (Vst (Vst (Vst (Vst (Vst (Vst V (g.rsp - 8) (toBytesLE g.r15 8))
    (g.rsp - 8 - 8) (toBytesLE g.r14 8)) (g.rsp - 8 - 8 - 8) (toBytesLE g.r13 8))
    (g.rsp - 8 - 8 - 8 - 8) (toBytesLE g.r12 8)) (g.rsp - 8 - 8 - 8 - 8 - 8) (toBytesLE g.rbp 8))
    (g.rsp - 8 - 8 - 8 - 8 - 8 - 8) (toBytesLE g.rbx 8))
    (g.rsp - 8 - 8 - 8 - 8 - 8 - 8 - 56#64) (toBytesLE (0#8) 1))
    (g.rsp - 8 - 8 - 8 - 8 - 8 - 8 - 56#64 + 16#64) (toBytesLE (4096#64 + g.rdi + 7#64 &&& 0 - 4096#64) 8))
    (g.rsp - 8 - 8 - 8 - 8 - 8 - 8 - 56#64) (toBytesLE (4096#64 + 18446744073709551615#64) 8))
    (g.rsp - 8 - 8 - 8 - 8 - 8 - 8 - 56#64 + 16#64) (toBytesLE (0 - 4096#64) 8))
    (g.rsp - 8 - 8 - 8 - 8 - 8 - 8 - 56#64 + 8#64) (toBytesLE (7940768#64) 8)

/-- From the entry to the first `call *__morecore`, with `av` the main arena, `nb` below `mp_.mmap_threshold` and
`2 ^ 47`, the page size 4096, the top the initial one of size 0, the arena contiguous: `rdi` is the size asked for,
`r15` is `nb + MINSIZE`, `r11` the old top's end, `r12` the old size, `r13` the old top, `rbp` is `nb`. -/
theorem vc_0 {g : Gprs} {f : Rflags} {V : Addr → Byte} {pad : BitVec 64} (hav : g.rsi = 7940672#64)
    (hsp : 8029888 + 104 ≤ g.rsp.toNat) (hst : ∀ i < 104, Foot Wl (Addr.add (g.rsp - 104) i))
    (hD : ∀ a : Addr, 7940480 ≤ a.toNat → a.toNat < 7943136 → Foot F.data a)
    (hps : rdq(V, 7943128#64) = 4096#64)
    (hthr : g.rdi.toNat < (rdq(V, 7940528#64)).toNat)
    (htop : rdq(V, 7940768#64) = 7940768#64) (hsz : rdq(V, 7940776#64) = 0#64)
    (hpad : rdq(V, 7940520#64) = pad) (hnb : g.rdi.toNat < 2 ^ 47) (hpd : pad.toNat < 2 ^ 47)
    (hfl : ofBytesLE 8 ((byteAddrs (7940676#64) 1).map V) &&& 2#8 = 0#8) :
    W_0 F Wl (fun j' g' _ V' => j' = 894 ∧
      g' = { g with rax := pad, rdx := 0 - 4096#64, rbx := 7940672#64,
                    rsp := g.rsp - 8 - 8 - 8 - 8 - 8 - 8 - 56#64, rbp := g.rdi, rsi := size pad g.rdi,
                    rdi := size pad g.rdi, r10 := 0 - 4096#64, r11 := 7940768#64, r12 := 0#64, r13 := 7940768#64,
                    r14 := size pad g.rdi, r15 := g.rdi + 32#64 } ∧
      V' = Va g V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hav hsp hthr hnb hst
  subst hav
  have a1 : Hi (rsp - 8) 8 := ⟨by bv_omega, by bv_omega⟩
  have a2 : Hi (rsp - 8 - 8) 8 := ⟨by bv_omega, by bv_omega⟩
  have a3 : Hi (rsp - 8 - 8 - 8) 8 := ⟨by bv_omega, by bv_omega⟩
  have a4 : Hi (rsp - 8 - 8 - 8 - 8) 8 := ⟨by bv_omega, by bv_omega⟩
  have a5 : Hi (rsp - 8 - 8 - 8 - 8 - 8) 8 := ⟨by bv_omega, by bv_omega⟩
  have a6 : Hi (rsp - 8 - 8 - 8 - 8 - 8 - 8) 8 := ⟨by bv_omega, by bv_omega⟩
  have a7 : Hi (rsp - 8 - 8 - 8 - 8 - 8 - 8 - 56#64) 1 := ⟨by bv_omega, by bv_omega⟩
  have a8 : Hi (rsp - 8 - 8 - 8 - 8 - 8 - 8 - 56#64) 8 := ⟨by bv_omega, by bv_omega⟩
  have a9 : Hi (rsp - 8 - 8 - 8 - 8 - 8 - 8 - 56#64 + 16#64) 8 := ⟨by bv_omega, by bv_omega⟩
  have a10 : Hi (rsp - 8 - 8 - 8 - 8 - 8 - 8 - 56#64 + 8#64) 8 := ⟨by bv_omega, by bv_omega⟩
  have q1 := @rd_hi (7943128#64) 8 (by decide)
  have q2 := @rd_hi (7940528#64) 8 (by decide)
  have q3 := @rd_hi (7940768#64) 8 (by decide)
  have q4 := @rd_hi (7940776#64) 8 (by decide)
  have q5 := @rd_hi (7940520#64) 8 (by decide)
  have q6 := @rd_hi (7940676#64) 1 (by decide)
  have e1 : (7940672#64 + 96#64 : BitVec 64) = 7940768#64 := by decide
  have e2 : (7940768#64 + 8#64 : BitVec 64) = 7940776#64 := by decide
  have e3 : (7940672#64 + 4#64 : BitVec 64) = 7940676#64 := by decide
  have z1 : (7940672#64 == (0 : BitVec 64)) = false := by decide
  have z2 : rdi + 32#64 ≠ 0#64 := by bv_omega
  have z3 : ((0#64 : BitVec 64) == 0) = true := by decide
  have z4 : ((0#8 : BitVec 8) == 0) = true := by decide
  have t1 : ¬ (rdq(V, 7940528#64)).toNat < rdi.toNat := by omega
  have t2 : rdq(V, 7940528#64) ≠ rdi := fun h => by rw [h] at hthr; omega
  have hR := and_m4096 (4096#64 + pad + 31#64 + rdi)
  have hx : (4096#64 + pad + 31#64 + rdi).toNat = 4096 + pad.toNat + 31 + rdi.toNat := by bv_omega
  have j1 := fun (f : Rflags) (af : Bool) => jle_no (R := 4096#64 + pad + 31#64 + rdi &&& 0 - 4096#64) f af
    (by omega) (by omega)
  wpx [W_0, W_33, W_49, W_53, W_79, W_104, W_140, W_153, W_824, W_866, W_881, o0, o1, o2, o3, o4, o5, o6, o7, o13,
    o14, o15, Op.lda, Op.cmpmra, Op.testmi, Op.sti, q1, q2, q3, q4, q5, q6, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10,
    toBytesLE_length, hps, t1, t2, htop, hsz, hpad, hfl, e1, e2, e3, z1, z2, z3, z4, j1, BitVec.and_self,
    BitVec.zero_and, BitVec.add_zero, BitVec.sub_zero, decide_false, decide_true, Bool.or_self, Bool.false_eq_true,
    false_imp_iff, true_imp_iff, Nat.not_lt_zero, BitVec.toNat_zero, beq_self_eq_true, Bool.not_true, Bool.not_false,
    Bool.or_false, and_true, true_and, Bool.true_eq_false]
  repeat' apply And.intro
  all_goals first
    | rfl
    | (intro i hi; exact hD _ (by simp only [Addr.add]; bv_omega) (by simp only [Addr.add]; bv_omega))
    | (intro i hi
       exact st hst (by omega) (by simp only [Addr.add]; bv_omega) (by simp only [Addr.add]; bv_omega))

end FV7z.Smm
