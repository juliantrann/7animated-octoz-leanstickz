import FV7z.Im4.Cuts
import FV7z.Im2.HeadN
import FV7z.Lemmas.Ksplit
/-!
# `_int_malloc`: from the entry to offset 1115, the second call, every request `121 ≤ n ≤ 1000` (PLAN.md G3, `malloc`)

The size `nb` (`request2size`) is `16 k`, `9 ≤ k ≤ 63`: a smallbin size above the fastbins. The way is
`0 → 304 → 340 → 848 → 86` (no fastbin read), the smallbin of `nb` empty (`984`), `1069 → 1099 → 1115`; the bytes and
registers at 1115 are those of the fastbin sizes (`Im2.V1n`, `Im2.G1n`). One `wpx` per `k` (`ksplit`).

- `clsM`: `n + 23` above 31 and rounded to `16 k`, `9 ≤ k ≤ 63`.
- `vc_0m`: from the entry to 1115.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn FV7z.Start
open FV7z.Imm (imm imm_at rd_off rd_off_self rd_below stk_f pu)
open FV7z.Im2 (G1n V1n and_m16)
namespace FV7z.Im4
variable {F : Footprint} {Wl : List Rgn}

/-- A request `121 ≤ n ≤ 1000`: `n + 23` is above 31 and rounds to `16 k`, `9 ≤ k ≤ 63`. -/
theorem clsM {n : Addr} (h1 : 121 ≤ n.toNat) (h2 : n.toNat ≤ 1000) :
    n.msb = false ∧ decide ((n + 23#64).toNat < 31) = false ∧ decide (n + 23#64 = 31#64) = false ∧
    ∃ k, 9 ≤ k ∧ k ≤ 63 ∧ n + 23#64 &&& 18446744073709551600#64 = BitVec.ofNat 64 (16 * k) := by
  have e : (n + 23#64).toNat = n.toNat + 23 := by rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  refine ⟨?_, decide_eq_false (by omega), decide_eq_false (fun h => by rw [h, BitVec.toNat_ofNat] at e; omega),
    (n.toNat + 23) / 16, by omega, by omega, BitVec.eq_of_toNat_eq ?_⟩
  · rw [BitVec.msb_eq_decide]; exact decide_eq_false (by show ¬ (2 ^ 63 ≤ n.toNat); omega)
  · rw [and_m16, e, BitVec.toNat_ofNat]; omega

set_option maxHeartbeats 100000000 in
/-- `Im2.vc_0n` for the requests `121 ≤ n ≤ 1000`: the smallbin of `nb` read, empty. -/
theorem vc_0m {fb S n : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} (hrsp : g.rsp = S + 184#64)
    (hsi : g.rsi = n) (hdi : g.rdi = 7940672#64) (hn : 121 ≤ n.toNat) (hn' : n.toNat ≤ 1000)
    (hS : S.toNat + 256 < 2 ^ 64) (hlo : 8029888 ≤ S.toNat)
    (hfb : (fb + 18446744073709551576#64).toNat + 8 ≤ S.toNat)
    (hgm : rdq(V, 8013224#64) = 128#64)
    (hbk : ∀ i, 2 ≤ i → i ≤ 63 → rdq(V, BitVec.ofNat 64 (7940776 + 16 * i)) = BitVec.ofNat 64 (7940752 + 16 * i))
    (htc : rdq(V, fb + 18446744073709551576#64) ≠ 0#64) (htb : rdq(V, 7940592#64) = 64#64)
    (hW : ∀ a : Addr, 7940480 ≤ a.toNat → a.toNat < 7943136 → Foot F.data a)
    (hgf : ∀ i < 8, Foot F.data (Addr.add (8013224#64) i))
    (htf : ∀ i < 8, Foot F.data (Addr.add (fb + 18446744073709551576#64) i))
    (hsw : ∀ i < 184, Foot Wl (Addr.add S i)) :
    W_0 fb F Wl (fun j' g' _ V' => j' = 1115 ∧ g' = G1n S g n (n + 23#64 &&& 18446744073709551600#64) ∧
      V' = V1n S g (n + 23#64 &&& 18446744073709551600#64) V) g f V := by
  obtain ⟨m, d1, d2, k, hk1, hk2, e⟩ := clsM hn hn'
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hrsp hsi hdi ⊢
  subst hrsp hsi hdi
  rw [e]
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
  ksplit k from 9 using hk1 hk2 <;>
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
      | with_reducible exact D _ _ (by decide) (by decide))

end FV7z.Im4
