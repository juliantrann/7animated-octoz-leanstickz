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
- `vc_900`: from its return to 1644: `mp_.sbrk_base` and `av->system_mem` stored, the correction that aligns the
  break to 16 bytes (`corr`), both ways (the break aligned or not).
- `vc_1644`: to the second `call *__morecore` (1684), its argument what ends the heap at a page (`corr2`).
- `vc_1690`: from its return to 312: the new top and its size, `system_mem`, `max_system_mem`.
- `vc_312`: the chunk cut from the top, to the `ret` (398).
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

/-! ## After the first `MORECORE` -/

/-- A byte of the frame's 104. -/
theorem fr {sp a : Addr} (hst : ∀ i < 104, Foot Wl (Addr.add sp i)) (_hs : sp.toNat + 104 ≤ 2 ^ 64)
    (h1 : sp.toNat ≤ a.toNat) (h2 : a.toNat < sp.toNat + 104) : Foot Wl a := by
  have e : Addr.add sp (a.toNat - sp.toNat) = a := by
    simp only [Addr.add]
    bv_omega
  exact e ▸ hst (a.toNat - sp.toNat) (by omega)

/-- The break's low four bits. -/
abbrev lo4 (b : BitVec 64) : BitVec 64 := BitVec.setWidth 64 (BitVec.setWidth 32 b &&& 15#32)

/-- `front_misalign`'s correction: what aligns the break `b` to 16 bytes. -/
def corr (b : BitVec 64) : BitVec 64 :=
  if (BitVec.setWidth 32 b &&& 15#32 == 0) = true then 0#64 else 16#64 - lo4 b

/-- `rax` at 1644, where the two ways meet (it is not read). -/
def ra (b : BitVec 64) : BitVec 64 :=
  if (BitVec.setWidth 32 b &&& 15#32 == 0) = true then lo4 b else b + (16#64 - lo4 b)

/-- The bytes at 1644: `mp_.sbrk_base` is the break `b`, `av->system_mem` is `sm + size`, and in the frame the
break aligned. -/
abbrev Vb (g : Gprs) (V : Addr → Byte) (sm : BitVec 64) : Addr → Byte :=
  Vst (Vst (Vst V (7940584#64) (toBytesLE g.rax 8)) (7942856#64) (toBytesLE (sm + g.r14) 8)) (g.rsp + 8#64)
    (toBytesLE (g.rax + corr g.rax) 8)

/-- From the return of the first `MORECORE` with the break `b` in `rax`, not 0 and not the old top's end, no
`__after_morecore_hook`, `mp_.sbrk_base` 0, the old size (`r12`) 0: `sbrk_base` and `system_mem` are stored, and at
1644 `rcx` is the correction that aligns `b`, `r8` is `b`. -/
theorem vc_900 {g : Gprs} {f : Rflags} {V : Addr → Byte} {sm : BitVec 64}
    (hsp : 8029888 ≤ g.rsp.toNat) (hsp2 : g.rsp.toNat + 104 ≤ 2 ^ 64)
    (hst : ∀ i < 104, Foot Wl (Addr.add g.rsp i)) (hws : ∀ a, Foot Wl a → Foot F.data a)
    (hW : ∀ a : Addr, 7940480 ≤ a.toNat → a.toNat < 7943136 → Foot Wl a)
    (hhk : ∀ i < 8, Foot F.data (Addr.add (8013152#64) i))
    (hb0 : g.rax ≠ 0#64) (hbe : g.rax ≠ 7940768#64) (h12 : g.r12 = 0#64)
    (r1 : rdq(V, g.rsp + 8#64) = 7940768#64) (r2 : rdq(V, g.rsp + 16#64) = 0 - 4096#64)
    (hk : rdq(V, 8013152#64) = 0#64) (hsm : rdq(V, 7942856#64) = sm) (hsb : rdq(V, 7940584#64) = 0#64)
    (hfl : ofBytesLE 8 ((byteAddrs (7940676#64) 1).map V) &&& 2#8 = 0#8) :
    W_900 F Wl (fun j' g' _ V' => j' = 1644 ∧
      g' = { g with rax := ra g.rax, rcx := corr g.rax, rdi := 1#64, r8 := g.rax, r10 := 0 - 4096#64,
                    r11 := 7940768#64 } ∧
      V' = Vb g V sm) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hsp hsp2 hb0 hbe h12 r1 r2 hst
  subst h12
  have z0 : ((0#64 : BitVec 64) == 0) = true := by decide
  have z4 : ((0#8 : BitVec 8) == 0) = true := by decide
  have zb : (rax == (0 : BitVec 64)) = false := by simpa using hb0
  have zc : (!decide (7940768#64 = rax)) = true := by simpa using fun h => hbe h.symm
  have e1 : BitVec.setWidth 64 1#32 = 1#64 := by decide
  have e16 : BitVec.setWidth 64 16#32 = 16#64 := by decide
  have qf : List.map (Vst (Vst V (7940584#64) (toBytesLE rax 8)) (7942856#64) (toBytesLE (sm + r14) 8))
      (byteAddrs (7940676#64) 1) = List.map V (byteAddrs (7940676#64) 1) := by
    rw [Tun.rd_Vst _ _ _ _ _ (by simp only [toBytesLE_length]; decide) (by decide)
      (.inr (by decide)), Tun.rd_Vst _ _ _ _ _ (by simp only [toBytesLE_length]; decide) (by decide)
      (.inl (by simp only [toBytesLE_length]; decide))]
  by_cases hz : (BitVec.setWidth 32 rax &&& 15#32 == 0) = true
  · have hc : corr rax = 0#64 := by simp only [corr, hz, ↓reduceIte]
    have hr : ra rax = BitVec.setWidth 64 (BitVec.setWidth 32 rax &&& 15#32) := by
      simp only [ra, hz, ↓reduceIte]
    wpx [W_900, W_923, W_939, W_1306, W_972, W_1568, W_1581, W_1616, W_1624, W_1728, o16, o17, o18, o19, o20, o22,
      o23, o24, o29, o5, Op.lda, Op.sta, Op.testmia, r1, r2, hk, hsm, hsb, hfl, qf, z0, z4, zb, zc, e1, e16, hz, hc,
      hr, toBytesLE_length, BitVec.and_self, BitVec.zero_and, BitVec.add_zero, BitVec.sub_zero, decide_false,
      decide_true, Bool.or_self, Bool.false_eq_true, false_imp_iff, true_imp_iff, Nat.not_lt_zero,
      BitVec.toNat_zero, beq_self_eq_true, Bool.not_true, Bool.not_false, Bool.or_false, and_true, true_and,
      Bool.true_eq_false]
    repeat' apply And.intro
    all_goals first
      | (simp only [Vb, hc, BitVec.add_zero]; done)
      | rfl
      | (intro i hi; exact hhk i hi)
      | (intro i hi; refine hW _ ?_ ?_ <;> (simp only [Addr.add]; bv_omega))
      | (intro i hi; refine hws _ (hW _ ?_ ?_) <;> (simp only [Addr.add]; bv_omega))
      | (intro i hi; refine fr hst hsp2 ?_ ?_ <;> (simp only [Addr.add]; bv_omega))
      | (intro i hi; refine hws _ (fr hst hsp2 ?_ ?_) <;> (simp only [Addr.add]; bv_omega))
  · have hz' : (BitVec.setWidth 32 rax &&& 15#32 == 0) = false := Bool.eq_false_iff.2 hz
    have hc : corr rax = 16#64 - BitVec.setWidth 64 (BitVec.setWidth 32 rax &&& 15#32) := by
      simp only [corr, hz, Bool.false_eq_true, ↓reduceIte]
    have hr : ra rax = rax + (16#64 - BitVec.setWidth 64 (BitVec.setWidth 32 rax &&& 15#32)) := by
      simp only [ra, hz, Bool.false_eq_true, ↓reduceIte]
    wpx [W_900, W_923, W_939, W_1306, W_972, W_1568, W_1581, W_1616, W_1624, W_1728, o16, o17, o18, o19, o20, o22,
      o23, o24, o29, o5, Op.lda, Op.sta, Op.testmia, r1, r2, hk, hsm, hsb, hfl, qf, z0, z4, zb, zc, e1, e16, hz', hc,
      hr, toBytesLE_length, BitVec.and_self, BitVec.zero_and, BitVec.add_zero, BitVec.sub_zero, decide_false,
      decide_true, Bool.or_self, Bool.false_eq_true, false_imp_iff, true_imp_iff, Nat.not_lt_zero,
      BitVec.toNat_zero, beq_self_eq_true, Bool.not_true, Bool.not_false, Bool.or_false, and_true, true_and,
      Bool.true_eq_false]
    repeat' apply And.intro
    all_goals first
      | (simp only [Vb, hc]; done)
      | rfl
      | (intro i hi; exact hhk i hi)
      | (intro i hi; refine hW _ ?_ ?_ <;> (simp only [Addr.add]; bv_omega))
      | (intro i hi; refine hws _ (hW _ ?_ ?_) <;> (simp only [Addr.add]; bv_omega))
      | (intro i hi; refine fr hst hsp2 ?_ ?_ <;> (simp only [Addr.add]; bv_omega))
      | (intro i hi; refine hws _ (fr hst hsp2 ?_ ?_) <;> (simp only [Addr.add]; bv_omega))

/-! ## To the second `MORECORE` -/

/-- The second `MORECORE`'s argument, from the break `b`, the correction `c` that aligns it and the size `R`: what
ends the heap at a page. -/
abbrev corr2 (b c R : BitVec 64) : BitVec 64 :=
  (4096#64 + 18446744073709551615#64 + (b + (c + R)) &&& 0 - 4096#64) + (c - (b + (c + R)))

/-- It is the bytes from `b + R` to the end of the page `b + c + R` is in. -/
theorem corr2_toNat (b c R : BitVec 64) (h : b.toNat + c.toNat + R.toNat + 4095 < 2 ^ 63) :
    (corr2 b c R).toNat = (4095 + b.toNat + c.toNat + R.toNat) / 4096 * 4096 - (b.toNat + R.toNat) := by
  have hx : (4096#64 + 18446744073709551615#64 + (b + (c + R))).toNat = 4095 + b.toNat + c.toNat + R.toNat := by
    bv_omega
  have ha := and_m4096 (4096#64 + 18446744073709551615#64 + (b + (c + R)))
  rw [hx] at ha
  show ((4096#64 + 18446744073709551615#64 + (b + (c + R)) &&& 0 - 4096#64) + (c - (b + (c + R)))).toNat = _
  generalize (4096#64 + 18446744073709551615#64 + (b + (c + R)) &&& 0 - 4096#64) = A at ha ⊢
  bv_omega

/-- From 1644 to the second `call *__morecore` (1684): `rdi` and `r14` are the second correction. -/
theorem vc_1644 {g : Gprs} {f : Rflags} {V : Addr → Byte} (hf : ∀ i < 8, Foot F.data (Addr.add g.rsp i))
    (r0 : rdq(V, g.rsp) = 4096#64 + 18446744073709551615#64) (h10 : g.r10 = 0 - 4096#64)
    (hm : (corr2 g.r8 g.rcx g.r14).toNat < 2 ^ 63) :
    W_1644 F Wl (fun j' g' _ V' => j' = 1684 ∧
      g' = { g with rax := 4096#64 + 18446744073709551615#64 + (g.r8 + (g.rcx + g.r14)) &&& 0 - 4096#64,
                    rcx := g.rcx - (g.r8 + (g.rcx + g.r14)), rdx := g.r8 + (g.rcx + g.r14),
                    rsi := g.rcx + g.r14, rdi := corr2 g.r8 g.rcx g.r14, r14 := corr2 g.r8 g.rcx g.r14 } ∧
      V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at r0 h10 hm hf
  subst h10
  have hmsb : BitVec.msb ((4096#64 + 18446744073709551615#64 + (r8 + (rcx + r14)) &&& 0 - 4096#64) +
      (rcx - (r8 + (rcx + r14)))) = false := by
    rw [BitVec.msb_eq_decide]
    exact decide_eq_false (Nat.not_le.2 hm)
  wpx [W_1644, o25, r0, hmsb, toBytesLE_length, BitVec.and_self, BitVec.add_zero, Bool.false_eq_true,
    false_imp_iff, true_imp_iff, and_true, true_and]
  first
    | exact hf
    | exact ⟨hf, rfl⟩

/-! ## After the second `MORECORE` -/

/-- The bytes at 312: `av->top` is the aligned break `ab`, its size word `(snd - ab + c2) | 1`, and
`av->system_mem`, `av->max_system_mem` are `sm + c2`. -/
abbrev Vc (g : Gprs) (V : Addr → Byte) (sm ab : BitVec 64) : Addr → Byte :=
  Vst (Vst (Vst (Vst V (7940768#64) (toBytesLE ab 8)) (ab + 8#64) (toBytesLE (g.rax - ab + g.r14 ||| 1#64) 8))
    (7942856#64) (toBytesLE (sm + g.r14) 8)) (7942864#64) (toBytesLE (sm + g.r14) 8)

/-- From the return of the second `MORECORE` with the break before it in `rax`, not 0, no `__after_morecore_hook`,
the old size (`r12`) 0, `av->max_system_mem` below the new `system_mem`: the top is the aligned break `ab` of the
frame, with its size, and at 312 `r8` is the top, `rax` its size word. -/
theorem vc_1690 {g : Gprs} {f : Rflags} {V : Addr → Byte} {sm ab mx : BitVec 64}
    (hsp : 8029888 ≤ g.rsp.toNat) (hsp2 : g.rsp.toNat + 104 ≤ 2 ^ 64)
    (hst : ∀ i < 104, Foot Wl (Addr.add g.rsp i)) (hws : ∀ a, Foot Wl a → Foot F.data a)
    (hW : ∀ a : Addr, 7940480 ≤ a.toNat → a.toNat < 7943136 → Foot Wl a)
    (hhk : ∀ i < 8, Foot F.data (Addr.add (8013152#64) i))
    (hh : ∀ i < 8, Foot Wl (Addr.add (ab + 8#64) i))
    (hs0 : g.rax ≠ 0#64) (h12 : g.r12 = 0#64) (hbx : g.rbx = 7940672#64)
    (hk : rdq(V, 8013152#64) = 0#64) (hsm : rdq(V, 7942856#64) = sm) (r1 : rdq(V, g.rsp + 8#64) = ab)
    (hab : 8029888 ≤ ab.toNat) (hab2 : ab.toNat + 16 ≤ 2 ^ 64)
    (hmx : rdq(V, 7942864#64) = mx) (hlt : mx.toNat < (sm + g.r14).toNat) :
    W_1690 F Wl (fun j' g' _ V' => j' = 312 ∧
      g' = { g with rax := g.rax - ab + g.r14 ||| 1#64, rcx := sm + g.r14, rdx := 0#64, r8 := ab } ∧
      V' = Vc g V sm ab) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hsp hsp2 hs0 h12 hbx r1 hlt hst
  subst h12 hbx
  have z0 : ((0#64 : BitVec 64) == 0) = true := by decide
  have zb : (rax == (0 : BitVec 64)) = false := by simpa using hs0
  have e1 : (7940672#64 + 2192#64 : BitVec 64) = 7942864#64 := by decide
  have qm : List.map (Vst (Vst (Vst V (7940768#64) (toBytesLE ab 8)) (ab + 8#64)
      (toBytesLE (rax - ab + r14 ||| 1#64) 8)) (7942856#64) (toBytesLE (sm + r14) 8)) (byteAddrs (7942864#64) 8) =
      List.map V (byteAddrs (7942864#64) 8) := by
    rw [Tun.rd_Vst _ _ _ _ _ (by simp only [toBytesLE_length]; decide) (by decide)
      (.inl (by simp only [toBytesLE_length]; decide)),
      Tun.rd_Vst _ _ _ _ _ (by simp only [toBytesLE_length]; bv_omega) (by decide) (.inr (by bv_omega)),
      Tun.rd_Vst _ _ _ _ _ (by simp only [toBytesLE_length]; decide) (by decide)
      (.inl (by simp only [toBytesLE_length]; decide))]
  have zd : (!decide (mx.toNat < (sm + r14).toNat)) = false := by simpa using hlt
  wpx [W_1690, W_1695, W_1707, W_1450, W_296, W_305, o26, o27, o28, o21, o8, o9, Op.lda, Op.sta, Op.cmpmr,
    r1, hk, hsm, qm, hmx, zd, z0, zb, e1, toBytesLE_length,
    BitVec.and_self, BitVec.zero_and, BitVec.add_zero, BitVec.sub_zero,
    decide_false, decide_true, Bool.or_self, Bool.false_eq_true, false_imp_iff, true_imp_iff, Nat.not_lt_zero,
    BitVec.toNat_zero, beq_self_eq_true, Bool.not_true, Bool.not_false, Bool.or_false, and_true, true_and,
    Bool.true_eq_false]
  repeat' apply And.intro
  all_goals first
    | rfl
    | (intro i hi; exact hhk i hi)
    | (intro i hi; exact hh i hi)
    | (intro i hi; refine hW _ ?_ ?_ <;> (simp only [Addr.add]; bv_omega))
    | (intro i hi; refine hws _ (hW _ ?_ ?_) <;> (simp only [Addr.add]; bv_omega))
    | (intro i hi; refine hws _ (fr hst hsp2 ?_ ?_) <;> (simp only [Addr.add]; bv_omega))

/-! ## The chunk, from the top -/

/-- The bytes at the `ret`: `av->top` is the rest of the top after `nb` bytes (`rbp`), the chunk's size word is
`nb | 1`, the rest's is its size with `PREV_INUSE`. -/
abbrev Vd (g : Gprs) (V : Addr → Byte) (szw : BitVec 64) : Addr → Byte :=
  Vst (Vst (Vst V (7940768#64) (toBytesLE (g.r8 + g.rbp) 8)) (g.r8 + 16#64 + 18446744073709551608#64)
    (toBytesLE (g.rbp ||| 1#64) 8)) (g.r8 + g.rbp + 8#64)
    (toBytesLE ((szw &&& 18446744073709551608#64) - g.rbp ||| 1#64) 8)

/-- From 312 with the top in `r8`, its size not below `nb + MINSIZE` (`r15`), `av` the main arena: the chunk is the
top's first `nb` bytes (`rbp`), the top is what is left, `rax` is the chunk's memory (`top + 16`), and the frame is
given back, to the `ret` (398). The heap is below the frame. -/
theorem vc_312 {g : Gprs} {f : Rflags} {V : Addr → Byte} {szw v0 v1 v2 v3 v4 v5 : BitVec 64}
    (hsp : 8029888 ≤ g.rsp.toNat) (hsp2 : g.rsp.toNat + 104 ≤ 2 ^ 64)
    (hst : ∀ i < 104, Foot Wl (Addr.add g.rsp i)) (hws : ∀ a, Foot Wl a → Foot F.data a)
    (hW : ∀ a : Addr, 7940480 ≤ a.toNat → a.toNat < 7943136 → Foot Wl a)
    (hh : ∀ a : Addr, g.r8.toNat ≤ a.toNat → a.toNat < g.r8.toNat + g.rbp.toNat + 16 → Foot Wl a)
    (hh1 : g.r8.toNat + g.rbp.toNat + 16 ≤ g.rsp.toNat) (hh0 : 8029888 ≤ g.r8.toNat)
    (hbx : g.rbx = 7940672#64) (hszw : rdq(V, g.r8 + 8#64) = szw)
    (hle : g.r15.toNat ≤ (szw &&& 18446744073709551608#64).toNat)
    (p0 : rdq(V, g.rsp + 56#64) = v0) (p1 : rdq(V, g.rsp + 56#64 + 8) = v1)
    (p2 : rdq(V, g.rsp + 56#64 + 8 + 8) = v2) (p3 : rdq(V, g.rsp + 56#64 + 8 + 8 + 8) = v3)
    (p4 : rdq(V, g.rsp + 56#64 + 8 + 8 + 8 + 8) = v4) (p5 : rdq(V, g.rsp + 56#64 + 8 + 8 + 8 + 8 + 8) = v5) :
    W_312 F Wl (fun j' g' _ V' => j' = 398 ∧
      g' = { g with rax := g.r8 + 16#64, rcx := g.r8 + g.rbp, rbx := v0,
                    rsp := g.rsp + 56#64 + 8 + 8 + 8 + 8 + 8 + 8, rbp := v1, rsi := g.rbp ||| 4#64,
                    rdi := 7940672#64, r8 := g.r8 + 16#64, r12 := v2, r13 := v3, r14 := v4, r15 := v5 } ∧
      V' = Vd g V szw) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hsp hsp2 hbx hszw hle hst hh hh1 hh0 p0 p1 p2 p3 p4 p5
  subst hbx
  have z0 : ((7940672#64 : BitVec 64) == 7940672#64) = true := by decide
  have e96 : (7940672#64 + 96#64 : BitVec 64) = 7940768#64 := by decide
  have zc : (!(decide (r15.toNat < (szw &&& 18446744073709551608#64).toNat) ||
      decide (r15 = szw &&& 18446744073709551608#64))) = false := by
    by_cases h : r15.toNat < (szw &&& 18446744073709551608#64).toNat
    · rw [decide_eq_true h]
      rfl
    · have h' : r15 = szw &&& 18446744073709551608#64 := by bv_omega
      rw [decide_eq_true h', Bool.or_true]
      rfl
  have q : ∀ x : Addr, rsp.toNat + 56 ≤ x.toNat → x.toNat + 8 ≤ rsp.toNat + 104 →
      List.map (Vst (Vst (Vst V (7940768#64) (toBytesLE (r8 + rbp) 8)) (r8 + 16#64 + 18446744073709551608#64)
        (toBytesLE (rbp ||| 1#64) 8)) (r8 + rbp + 8#64)
        (toBytesLE ((szw &&& 18446744073709551608#64) - rbp ||| 1#64) 8)) (byteAddrs x 8) =
      List.map V (byteAddrs x 8) := by
    intro x h1 h2
    rw [Tun.rd_Vst _ _ _ _ _ (by simp only [toBytesLE_length]; bv_omega) (by omega)
        (.inl (by simp only [toBytesLE_length]; bv_omega)),
      Tun.rd_Vst _ _ _ _ _ (by simp only [toBytesLE_length]; bv_omega) (by omega)
        (.inl (by simp only [toBytesLE_length]; bv_omega)),
      Tun.rd_Vst _ _ _ _ _ (by simp only [toBytesLE_length]; decide) (by omega)
        (.inl (by simp only [toBytesLE_length]; bv_omega))]
  have q0 := q (rsp + 56#64) (by bv_omega) (by bv_omega)
  have q1 := q (rsp + 56#64 + 8) (by bv_omega) (by bv_omega)
  have q2 := q (rsp + 56#64 + 8 + 8) (by bv_omega) (by bv_omega)
  have q3 := q (rsp + 56#64 + 8 + 8 + 8) (by bv_omega) (by bv_omega)
  have q4 := q (rsp + 56#64 + 8 + 8 + 8 + 8) (by bv_omega) (by bv_omega)
  have q5 := q (rsp + 56#64 + 8 + 8 + 8 + 8 + 8) (by bv_omega) (by bv_omega)
  wpx [W_312, W_329, W_381, o10, o11, o12, Op.cmov64, hszw, z0, e96, zc, q0, q1, q2, q3, q4, q5, p0, p1, p2, p3, p4,
    p5, toBytesLE_length, BitVec.and_self, BitVec.zero_and, BitVec.add_zero, BitVec.sub_zero,
    decide_false, decide_true, Bool.or_self, Bool.false_eq_true, false_imp_iff, true_imp_iff, Nat.not_lt_zero,
    BitVec.toNat_zero, beq_self_eq_true, Bool.not_true, Bool.not_false, Bool.or_false, and_true, true_and,
    Bool.true_eq_false, ↓reduceIte]
  repeat' apply And.intro
  all_goals first
    | rfl
    | (intro i hi; refine hW _ ?_ ?_ <;> (simp only [Addr.add]; bv_omega))
    | (intro i hi; refine hh _ ?_ ?_ <;> (simp only [Addr.add]; bv_omega))
    | (intro i hi; refine hws _ (hh _ ?_ ?_) <;> (simp only [Addr.add]; bv_omega))
    | (intro i hi; refine hws _ (fr hst hsp2 ?_ ?_) <;> (simp only [Addr.add]; bv_omega))

end FV7z.Smm
