import FV7z.Im2.Head
/-! Probe: `_int_malloc`'s second call, entry to 1115, for every request `9 ≤ n ≤ 120` (`nb` 32 … 128, a fastbin
size): one `wpx` per `nb`. -/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn FV7z.Start
open FV7z.Imm (imm imm_at rd_off rd_off_self rd_below stk_f pu)
namespace FV7z.Im2
variable {F : Footprint} {Wl : List Rgn}

theorem nat_and_m16 (n : Nat) (h : n < 2 ^ 64) : n &&& 18446744073709551600 = n / 16 * 16 := by
  have hm : (18446744073709551600 : Nat) = (2 ^ 60 - 1) <<< 4 := by decide
  have hr : n / 16 * 16 = (n >>> 4) <<< 4 := by rw [Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
  rw [hm, hr]
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and, Nat.testBit_shiftLeft, Nat.testBit_shiftLeft, Nat.testBit_shiftRight,
    Nat.testBit_two_pow_sub_one]
  by_cases h1 : i ≥ 4
  · have e : 4 + (i - 4) = i := by omega
    rw [e]
    by_cases h2 : i < 64
    · have : i - 4 < 60 := by omega
      simp [h1, this]
    · have h3 : n.testBit i = false :=
        Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le h (Nat.pow_le_pow_right (by decide) (by omega)))
      simp [h3]
  · simp [h1]

/-- `x &&& -16`: `request2size`'s rounding. -/
theorem and_m16 (x : BitVec 64) : (x &&& 18446744073709551600#64).toNat = x.toNat / 16 * 16 := by
  rw [BitVec.toNat_and]
  exact nat_and_m16 _ x.isLt

/-- A request `9 ≤ n ≤ 120`: `n + 23` is above 31 and rounds to `16 k`, `2 ≤ k ≤ 8`. -/
theorem clsB {n : Addr} (h1 : 9 ≤ n.toNat) (h2 : n.toNat ≤ 120) :
    n.msb = false ∧ decide ((n + 23#64).toNat < 31) = false ∧ decide (n + 23#64 = 31#64) = false ∧
    ∃ k, 2 ≤ k ∧ k ≤ 8 ∧ n + 23#64 &&& 18446744073709551600#64 = BitVec.ofNat 64 (16 * k) := by
  have e : (n + 23#64).toNat = n.toNat + 23 := by rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  refine ⟨?_, decide_eq_false (by omega), decide_eq_false (fun h => by rw [h, BitVec.toNat_ofNat] at e; omega),
    (n.toNat + 23) / 16, by omega, by omega, BitVec.eq_of_toNat_eq ?_⟩
  · rw [BitVec.msb_eq_decide]; exact decide_eq_false (by show ¬ (2 ^ 63 ≤ n.toNat); omega)
  · rw [and_m16, e, BitVec.toNat_ofNat]; omega

/-- The bytes at offset 1115 on the second call, `nb` the size. -/
def V1n (S : Addr) (g : Gprs) (nb : Addr) (V : Addr → Byte) : Addr → Byte :=
  Vst (Vst (Vst (Vst (Vst (Vst (Vst (Vst (Vst (Vst (Vst (Vst (Vst (Vst (Vst (Vst (Vst (Vst V
    (S + 176#64) (toBytesLE g.r15 8)) (S + 168#64) (toBytesLE g.r14 8)) (S + 160#64) (toBytesLE g.r13 8))
    (S + 152#64) (toBytesLE g.r12 8)) (S + 144#64) (toBytesLE g.rbp 8)) (S + 136#64) (toBytesLE g.rbx 8))
    (S + 40#64) (toBytesLE ((nb >>> 4).setWidth 32) 4)) (S + 112#64) (toBytesLE (110#32) 4))
    (S + 64#64) (toBytesLE (nb >>> 6) 8)) (S + 80#64) (toBytesLE (nb >>> 9) 8))
    (S + 116#64) (toBytesLE ((nb >>> 9).setWidth 32 + 91#32) 4)) (S + 76#64) (toBytesLE ((nb >>> 6).setWidth 32 + 48#32) 4))
    (S + 108#64) (toBytesLE (119#32) 4)) (S + 104#64) (toBytesLE (124#32) 4)) (S + 96#64) (toBytesLE (0#64) 8))
    (S + 88#64) (toBytesLE (0#64) 8)) (S + 16#64) (toBytesLE (0#64) 8)) (S + 16#64) (toBytesLE nb 8)

/-- The registers at offset 1115 on the second call, `n` asked for, `nb` the size. -/
def G1n (S : Addr) (g : Gprs) (n nb : Addr) : Gprs :=
  ⟨nb, 7940752#64 + nb, g.rdx, 7940672#64, S, n, n, (nb >>> 9) + 91#64, 7940752#64 + nb, g.r9, g.r10, g.r11, g.r12,
    nb, nb >>> 4, (nb - 17#64) >>> 4⟩

set_option maxHeartbeats 4000000 in
theorem vc_0n {fb S n : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} (hrsp : g.rsp = S + 184#64)
    (hsi : g.rsi = n) (hdi : g.rdi = 7940672#64) (hn : 9 ≤ n.toNat) (hn' : n.toNat ≤ 120)
    (hS : S.toNat + 256 < 2 ^ 64) (hlo : 8029888 ≤ S.toNat)
    (hfb : (fb + 18446744073709551576#64).toNat + 8 ≤ S.toNat)
    (hgm : rdq(V, 8013224#64) = 128#64)
    (hfz : ∀ k < 7, rdq(V, BitVec.ofNat 64 (7940688 + 8 * k)) = 0#64)
    (hbk : ∀ i, 2 ≤ i → i ≤ 8 → rdq(V, BitVec.ofNat 64 (7940776 + 16 * i)) = BitVec.ofNat 64 (7940752 + 16 * i))
    (htc : rdq(V, fb + 18446744073709551576#64) ≠ 0#64) (htb : rdq(V, 7940592#64) = 64#64)
    (hW : ∀ a : Addr, 7940480 ≤ a.toNat → a.toNat < 7943136 → Foot F.data a)
    (hgf : ∀ i < 8, Foot F.data (Addr.add (8013224#64) i))
    (htf : ∀ i < 8, Foot F.data (Addr.add (fb + 18446744073709551576#64) i))
    (hsw : ∀ i < 184, Foot Wl (Addr.add S i)) :
    W_0 fb F Wl (fun j' g' _ V' => j' = 1115 ∧ g' = G1n S g n (n + 23#64 &&& 18446744073709551600#64) ∧
      V' = V1n S g (n + 23#64 &&& 18446744073709551600#64) V) g f V := by
  obtain ⟨m, d1, d2, k, hk1, hk2, e⟩ := clsB hn hn'
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hrsp hsi hdi ⊢
  subst hrsp hsi hdi
  rw [e]
  obtain ⟨p1, p2, p3, p4, p5, p6, p7⟩ := pu S
  have f0 : rdq(V, 7940688#64) = 0#64 := hfz 0 (by decide)
  have f1 : rdq(V, 7940696#64) = 0#64 := hfz 1 (by decide)
  have f2 : rdq(V, 7940704#64) = 0#64 := hfz 2 (by decide)
  have f3 : rdq(V, 7940712#64) = 0#64 := hfz 3 (by decide)
  have f4 : rdq(V, 7940720#64) = 0#64 := hfz 4 (by decide)
  have f5 : rdq(V, 7940728#64) = 0#64 := hfz 5 (by decide)
  have f6 : rdq(V, 7940736#64) = 0#64 := hfz 6 (by decide)
  have s2 : rdq(V, 7940808#64) = 7940784#64 := hbk 2 (by decide) (by decide)
  have s3 : rdq(V, 7940824#64) = 7940800#64 := hbk 3 (by decide) (by decide)
  have s4 : rdq(V, 7940840#64) = 7940816#64 := hbk 4 (by decide) (by decide)
  have s5 : rdq(V, 7940856#64) = 7940832#64 := hbk 5 (by decide) (by decide)
  have s6 : rdq(V, 7940872#64) = 7940848#64 := hbk 6 (by decide) (by decide)
  have s7 : rdq(V, 7940888#64) = 7940864#64 := hbk 7 (by decide) (by decide)
  have s8 : rdq(V, 7940904#64) = 7940880#64 := hbk 8 (by decide) (by decide)
  have qf0 := rd_below (S := S) (x := 7940688#64) (n := 8) (hx := by rw [BitVec.toNat_ofNat]; omega) (hS := hS)
  have qf1 := rd_below (S := S) (x := 7940696#64) (n := 8) (hx := by rw [BitVec.toNat_ofNat]; omega) (hS := hS)
  have qf2 := rd_below (S := S) (x := 7940704#64) (n := 8) (hx := by rw [BitVec.toNat_ofNat]; omega) (hS := hS)
  have qf3 := rd_below (S := S) (x := 7940712#64) (n := 8) (hx := by rw [BitVec.toNat_ofNat]; omega) (hS := hS)
  have qf4 := rd_below (S := S) (x := 7940720#64) (n := 8) (hx := by rw [BitVec.toNat_ofNat]; omega) (hS := hS)
  have qf5 := rd_below (S := S) (x := 7940728#64) (n := 8) (hx := by rw [BitVec.toNat_ofNat]; omega) (hS := hS)
  have qf6 := rd_below (S := S) (x := 7940736#64) (n := 8) (hx := by rw [BitVec.toNat_ofNat]; omega) (hS := hS)
  have qs2 := rd_below (S := S) (x := 7940808#64) (n := 8) (hx := by rw [BitVec.toNat_ofNat]; omega) (hS := hS)
  have qs3 := rd_below (S := S) (x := 7940824#64) (n := 8) (hx := by rw [BitVec.toNat_ofNat]; omega) (hS := hS)
  have qs4 := rd_below (S := S) (x := 7940840#64) (n := 8) (hx := by rw [BitVec.toNat_ofNat]; omega) (hS := hS)
  have qs5 := rd_below (S := S) (x := 7940856#64) (n := 8) (hx := by rw [BitVec.toNat_ofNat]; omega) (hS := hS)
  have qs6 := rd_below (S := S) (x := 7940872#64) (n := 8) (hx := by rw [BitVec.toNat_ofNat]; omega) (hS := hS)
  have qs7 := rd_below (S := S) (x := 7940888#64) (n := 8) (hx := by rw [BitVec.toNat_ofNat]; omega) (hS := hS)
  have qs8 := rd_below (S := S) (x := 7940904#64) (n := 8) (hx := by rw [BitVec.toNat_ofNat]; omega) (hS := hS)
  have q1 := rd_below (S := S) (x := 8013224#64) (n := 8) (hx := by rw [BitVec.toNat_ofNat]; omega) (hS := hS)
  have q3 := rd_below (S := S) (n := 8) (hx := hfb) (hS := hS)
  have q5 := rd_below (S := S) (x := 7940592#64) (n := 8) (hx := by rw [BitVec.toNat_ofNat]; omega) (hS := hS)
  have hS' : S.toNat + 256 < 18446744073709551616 := hS
  have D : ∀ (x : Addr) (n : Nat), 7940480 ≤ x.toNat → x.toNat + n ≤ 7943136 →
      ∀ i < n, Foot F.data (Addr.add x i) :=
    fun x n h1 h2 i hi => hW _ (by simp only [Addr.add]; bv_omega) (by simp only [Addr.add]; bv_omega)
  clear hfz hbk
  rcases (show k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 ∨ k = 8 by omega) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  ( simp only [Nat.reduceMul] at e
    wpx [W_0, W_9, W_304, W_320, W_960, W_563, W_848, W_86, W_984, W_1069, W_1099, o0, o1, o2, o3, o4, o5, o6, o8,
      o9, o10, o11, Op.cmpma, Op.cmpmif, Op.cmpmra, Op.shr64, p1, p2, p3, p4, p5, p6, p7, q1, q3, q5, rd_off,
      rd_off_self, hS, hS', m, d1, d2, e, hgm, htb, htc, BitVec.and_self, G1n, V1n, f0, f1, f2, f3, f4, f5, f6, s2, s3, s4, s5, s6, s7, s8, qf0, qf1, qf2, qf3, qf4, qf5, qf6, qs2, qs3, qs4, qs5, qs6, qs7, qs8,
      BitVec.reduceAdd, BitVec.reduceAnd, BitVec.reduceSetWidth, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft,
      BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceBEq, BitVec.reduceEq, BitVec.reduceToNat,
      BitVec.reduceSub, BitVec.reduceMul, BitVec.reduceLT, BitVec.reduceULT, BitVec.reduceOr, BitVec.reduceXOr,
      Nat.reduceAdd, Nat.reduceLeDiff, Nat.reduceLT, decide_false, decide_true, Bool.or_false, Bool.false_or,
      Bool.not_false, Bool.not_true, Bool.false_eq_true, false_imp_iff, true_imp_iff, Bool.or_self, Bool.true_or,
      Bool.or_true, false_implies, true_implies, and_true, true_and, reduceIte, or_true, true_or, or_false, false_or,
      ne_eq, Nat.reduceEqDiff, not_false_eq_true, ofBytesLE_toBytesLE, Bool.true_eq_false]
    repeat' first
      | apply And.intro
      | intro (_ : Rflags)
      | intro (_ : Rflags.zf _ = false)
      | intro (_ : Rflags.zf _ = true)
      | rfl
      | with_reducible exact stk_f hsw (by decide)
      | with_reducible exact hgf
      | with_reducible exact htf
      | with_reducible exact D _ _ (by decide) (by decide))

end FV7z.Im2
