import FV7z.Im2.HeadN
/-! Probe: `_int_malloc`'s second call, 1115 to 2549, for every request `9 ≤ n ≤ 120` (`nb` 32 … 128, a fastbin
size): one `wpx` per `nb`. -/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn FV7z.Start
open FV7z.Imm (imm imm_at rd_off rd_off_self rd_below stk_f pu)
namespace FV7z.Im2
variable {F : Footprint} {Wl : List Rgn}

/-- The bytes at offset 2549 on the second call. -/
abbrev V2n (S : Addr) (g : Gprs) (n nb : Addr) (V : Addr → Byte) : Addr → Byte :=
  Vst (Vst (Vst (V1n S g nb V) (S + 8#64) (toBytesLE (0#64) 8)) (S + 72#64) (toBytesLE ((nb >>> 4).setWidth 32) 4))
    (S + 32#64) (toBytesLE n 8)

/-- The registers at offset 2549 on the second call. -/
def G2n (S : Addr) (g : Gprs) (n nb : Addr) : Gprs :=
  ⟨2#64, (nb >>> 4) + 1#64, 2#64, 7940672#64, S, n, 0#64, 0#64, 7940752#64 + nb, g.r9, 7940768#64, 7940768#64,
    g.r12, nb, nb >>> 4, (nb - 17#64) >>> 4⟩

set_option maxHeartbeats 4000000 in
theorem vc_1115n {fb S n nb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (hnb : nb = 32#64 ∨ nb = 48#64 ∨ nb = 64#64 ∨ nb = 80#64 ∨ nb = 96#64 ∨ nb = 112#64 ∨ nb = 128#64)
    (hS : S.toNat + 256 < 2 ^ 64) (hlo : 8029888 ≤ S.toNat)
    (hun : rdq(V, 7940792#64) = 7940768#64)
    (hm0 : rdd(V, 7942816#64) = 0) (hm1 : rdd(V, 7942820#64) = 0) (hm2 : rdd(V, 7942824#64) = 0)
    (hm3 : rdd(V, 7942828#64) = 0)
    (hW : ∀ a : Addr, 7940480 ≤ a.toNat → a.toNat < 7943136 → Foot F.data a)
    (hsw : ∀ i < 184, Foot Wl (Addr.add S i)) (hsd : ∀ i < 184, Foot F.data (Addr.add S i)) :
    W_1115 fb F Wl (fun j' g' _ V' => j' = 2549 ∧ g' = G2n S g n nb ∧ V' = V2n S g n nb V) (G1n S g n nb) f
      (V1n S g nb V) := by
  have q1 := rd_below (S := S) (x := 7940792#64) (n := 8) (hx := by rw [BitVec.toNat_ofNat]; omega) (hS := hS)
  have q2 := rd_below (S := S) (x := 7942816#64) (n := 4) (hx := by rw [BitVec.toNat_ofNat]; omega) (hS := hS)
  have q3 := rd_below (S := S) (x := 7942820#64) (n := 4) (hx := by rw [BitVec.toNat_ofNat]; omega) (hS := hS)
  have q4 := rd_below (S := S) (x := 7942824#64) (n := 4) (hx := by rw [BitVec.toNat_ofNat]; omega) (hS := hS)
  have q5 := rd_below (S := S) (x := 7942828#64) (n := 4) (hx := by rw [BitVec.toNat_ofNat]; omega) (hS := hS)
  have hS' : S.toNat + 256 < 18446744073709551616 := hS
  have D : ∀ (x : Addr) (n : Nat), 7940480 ≤ x.toNat → x.toNat + n ≤ 7943136 →
      ∀ i < n, Foot F.data (Addr.add x i) :=
    fun x n h1 h2 i hi => hW _ (by simp only [Addr.add]; bv_omega) (by simp only [Addr.add]; bv_omega)
  rcases hnb with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  ( wpx [W_1115, W_1138, W_1968, W_2012, W_2048, W_2480, W_2488, W_2505, W_2513, W_2530, W_2535, V1n, G1n, G2n,
      o12, o13, o14, o15, o16, o17, o18, o19, o20, o21, q1, q2, q3, q4, q5, rd_off, rd_off_self, hS, hS', hun, hm0,
      hm1, hm2, hm3,
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
      | rfl
      | with_reducible exact stk_f hsw (by decide)
      | with_reducible exact stk_f hsd (by decide)
      | with_reducible exact D _ _ (by decide) (by decide))

end FV7z.Im2
