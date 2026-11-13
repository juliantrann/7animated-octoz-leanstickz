import FV7z.Im4.Cuts
import FV7z.Im2.HeadN
/-! Probe: the requests `121 ≤ n ≤ 1000` (`nb` = `16 k`, `9 ≤ k ≤ 63`, a smallbin size): `clsM`, `vc_0mP` for
`k` ∈ {9, 36, 63} (timing). -/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn FV7z.Start
open FV7z.Imm (imm imm_at rd_off rd_off_self rd_below stk_f pu)
open FV7z.Im2 (G1n V1n and_m16)
namespace FV7z.Im4
variable {F : Footprint} {Wl : List Rgn}

/-- `n + 23` above 31 and rounded to `16 k`, `9 ≤ k ≤ 63`. -/
theorem clsM {n : Addr} (h1 : 121 ≤ n.toNat) (h2 : n.toNat ≤ 1000) :
    n.msb = false ∧ decide ((n + 23#64).toNat < 31) = false ∧ decide (n + 23#64 = 31#64) = false ∧
    ∃ k, 9 ≤ k ∧ k ≤ 63 ∧ n + 23#64 &&& 18446744073709551600#64 = BitVec.ofNat 64 (16 * k) := by
  have e : (n + 23#64).toNat = n.toNat + 23 := by rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  refine ⟨?_, decide_eq_false (by omega), decide_eq_false (fun h => by rw [h, BitVec.toNat_ofNat] at e; omega),
    (n.toNat + 23) / 16, by omega, by omega, BitVec.eq_of_toNat_eq ?_⟩
  · rw [BitVec.msb_eq_decide]; exact decide_eq_false (by show ¬ (2 ^ 63 ≤ n.toNat); omega)
  · rw [and_m16, e, BitVec.toNat_ofNat]; omega

set_option maxHeartbeats 4000000 in
theorem vc_0mP {fb S n : Addr} {k : Nat} {g : Gprs} {f : Rflags} {V : Addr → Byte} (hrsp : g.rsp = S + 184#64)
    (hsi : g.rsi = n) (hdi : g.rdi = 7940672#64) (m : n.msb = false)
    (d1 : decide ((n + 23#64).toNat < 31) = false) (d2 : decide (n + 23#64 = 31#64) = false)
    (e : n + 23#64 &&& 18446744073709551600#64 = BitVec.ofNat 64 (16 * k)) (hk : k = 9 ∨ k = 36 ∨ k = 63)
    (hS : S.toNat + 256 < 2 ^ 64) (hlo : 8029888 ≤ S.toNat)
    (hfb : (fb + 18446744073709551576#64).toNat + 8 ≤ S.toNat)
    (hgm : rdq(V, 8013224#64) = 128#64)
    (hbk : ∀ i, 2 ≤ i → i ≤ 63 → rdq(V, BitVec.ofNat 64 (7940776 + 16 * i)) = BitVec.ofNat 64 (7940752 + 16 * i))
    (htc : rdq(V, fb + 18446744073709551576#64) ≠ 0#64) (htb : rdq(V, 7940592#64) = 64#64)
    (hW : ∀ a : Addr, 7940480 ≤ a.toNat → a.toNat < 7943136 → Foot F.data a)
    (hgf : ∀ i < 8, Foot F.data (Addr.add (8013224#64) i))
    (htf : ∀ i < 8, Foot F.data (Addr.add (fb + 18446744073709551576#64) i))
    (hsw : ∀ i < 184, Foot Wl (Addr.add S i)) :
    W_0 fb F Wl (fun j' g' _ V' => j' = 1115 ∧ g' = G1n S g n (BitVec.ofNat 64 (16 * k)) ∧
      V' = V1n S g (BitVec.ofNat 64 (16 * k)) V) g f V := by
  have hk1 : 9 ≤ k := by omega
  have hk2 : k ≤ 63 := by omega
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hrsp hsi hdi ⊢
  subst hrsp hsi hdi
  obtain ⟨p1, p2, p3, p4, p5, p6, p7⟩ := pu S
  have sk := hbk k (by omega) hk2
  have qk := rd_below (S := S) (x := BitVec.ofNat 64 (7940776 + 16 * k)) (n := 8)
    (hx := by rw [BitVec.toNat_ofNat]; omega) (hS := hS)
  have q1 := rd_below (S := S) (x := 8013224#64) (n := 8) (hx := by rw [BitVec.toNat_ofNat]; omega) (hS := hS)
  have q3 := rd_below (S := S) (n := 8) (hx := hfb) (hS := hS)
  have q5 := rd_below (S := S) (x := 7940592#64) (n := 8) (hx := by rw [BitVec.toNat_ofNat]; omega) (hS := hS)
  have hS' : S.toNat + 256 < 18446744073709551616 := hS
  have D : ∀ (x : Addr) (n : Nat), 7940480 ≤ x.toNat → x.toNat + n ≤ 7943136 →
      ∀ i < n, Foot F.data (Addr.add x i) :=
    fun x n h1 h2 i hi => hW _ (by simp only [Addr.add]; bv_omega) (by simp only [Addr.add]; bv_omega)
  clear hbk
  rcases hk with rfl | rfl | rfl <;>
  ( simp only [Nat.reduceMul, Nat.reduceAdd] at e sk qk ⊢
    wpx [W_0, W_9, W_304, W_320, W_340, W_848, W_86, W_984, W_1069, W_1099, o0, o1, o2, o3, o4, o5, o6, o7,
      o8, o9, Op.cmpma, Op.cmpmif, Op.cmpmra, Op.shr64, p1, p2, p3, p4, p5, p6, p7, q1, q3, q5, sk, qk, rd_off,
      rd_off_self, hS, hS', m, d1, d2, e, hgm, htb, htc, BitVec.and_self, G1n, V1n,
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
      | with_reducible exact D _ _ (by decide) (by decide)
      | (trace_state; sorry))

end FV7z.Im4
