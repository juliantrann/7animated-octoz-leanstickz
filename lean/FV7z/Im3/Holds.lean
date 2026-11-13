import FV7z.Im3.Cuts
import FV7z.Im2.HeadN
/-!
# `_int_malloc`: from the entry to offset 1115, the second call, the requests `n ≤ 8` (PLAN.md G3, `malloc`)

`nb` is 32 (`MINSIZE`, no rounding): the way is `0 → 63 → 544 → 563`, from 563 that of `9 ≤ n ≤ 120` with
`nb` = 32 (`Im2/HeadN.lean`; the registers at 563 are those of that way, no store before). One `wpx` per `n`.

- `clsS`: `n` one of 0 … 8.
- `Cls`, `Cls.cases`, `Cls.bnd`: the requests `n ≤ 120` and their chunk sizes `nb`, a fastbin size.
- `vc_0s`: 0 → 1115, with `Im2.G1n`, `Im2.V1n`.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn FV7z.Start
open FV7z.Imm (imm imm_at rd_off rd_off_self rd_below stk_f pu)
open FV7z.Im2 (G1n V1n)
namespace FV7z.Im3
variable {F : Footprint} {Wl : List Rgn}

/-- A request `n ≤ 8`: one of nine. -/
theorem clsS {n : Addr} (h : n.toNat ≤ 8) :
    n = 0#64 ∨ n = 1#64 ∨ n = 2#64 ∨ n = 3#64 ∨ n = 4#64 ∨ n = 5#64 ∨ n = 6#64 ∨ n = 7#64 ∨ n = 8#64 := by
  bv_omega

/-- The requests `n ≤ 120` and their chunk sizes `nb` (`request2size`): `n + 23 &&& -16` from 9 on, 32 (`MINSIZE`)
below. -/
def Cls (n nb : Addr) : Prop :=
  (9 ≤ n.toNat ∧ n.toNat ≤ 120 ∧ n + 23#64 &&& 18446744073709551600#64 = nb) ∨ (n.toNat ≤ 8 ∧ nb = 32#64)

/-- `nb` is one of the seven fastbin sizes. -/
theorem Cls.cases {n nb : Addr} (h : Cls n nb) :
    nb = 32#64 ∨ nb = 48#64 ∨ nb = 64#64 ∨ nb = 80#64 ∨ nb = 96#64 ∨ nb = 112#64 ∨ nb = 128#64 := by
  rcases h with ⟨h1, h2, rfl⟩ | ⟨-, rfl⟩
  · obtain ⟨-, -, -, k₀, hk1, hk2, enb⟩ := Im2.clsB h1 h2
    rw [enb]
    rcases (show k₀ = 2 ∨ k₀ = 3 ∨ k₀ = 4 ∨ k₀ = 5 ∨ k₀ = 6 ∨ k₀ = 7 ∨ k₀ = 8 by omega) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · exact .inl rfl

theorem Cls.bnd {n nb : Addr} (h : Cls n nb) : 32 ≤ nb.toNat ∧ nb.toNat ≤ 128 := by
  rcases h.cases with h | h | h | h | h | h | h <;> subst h <;> decide

/-- `Im2.vc_0n` for the requests `n ≤ 8`: from the entry to 1115 by `0 → 63 → 544 → 563`, `nb` = 32. -/
set_option maxHeartbeats 4000000 in
theorem vc_0s {fb S n nb : Addr} (hnb : nb = 32#64) {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (hrsp : g.rsp = S + 184#64) (hsi : g.rsi = n) (hdi : g.rdi = 7940672#64) (hn : n.toNat ≤ 8)
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
    W_0 fb F Wl (fun j' g' _ V' => j' = 1115 ∧ g' = G1n S g n nb ∧ V' = V1n S g nb V) g f V := by
  subst hnb
  have hc := clsS hn
  have m : n.msb = false := by
    rw [BitVec.msb_eq_decide]; exact decide_eq_false (by show ¬ (2 ^ 63 ≤ n.toNat); omega)
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hrsp hsi hdi ⊢
  subst hrsp hdi
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
  have qf0 := rd_below (S := S) (x := 7940688#64) (n := 8)
    (hx := by rw [BitVec.toNat_ofNat]; omega) (hS := hS)
  have qf1 := rd_below (S := S) (x := 7940696#64) (n := 8)
    (hx := by rw [BitVec.toNat_ofNat]; omega) (hS := hS)
  have qf2 := rd_below (S := S) (x := 7940704#64) (n := 8)
    (hx := by rw [BitVec.toNat_ofNat]; omega) (hS := hS)
  have qf3 := rd_below (S := S) (x := 7940712#64) (n := 8)
    (hx := by rw [BitVec.toNat_ofNat]; omega) (hS := hS)
  have qf4 := rd_below (S := S) (x := 7940720#64) (n := 8)
    (hx := by rw [BitVec.toNat_ofNat]; omega) (hS := hS)
  have qf5 := rd_below (S := S) (x := 7940728#64) (n := 8)
    (hx := by rw [BitVec.toNat_ofNat]; omega) (hS := hS)
  have qf6 := rd_below (S := S) (x := 7940736#64) (n := 8)
    (hx := by rw [BitVec.toNat_ofNat]; omega) (hS := hS)
  have qs2 := rd_below (S := S) (x := 7940808#64) (n := 8)
    (hx := by rw [BitVec.toNat_ofNat]; omega) (hS := hS)
  have qs3 := rd_below (S := S) (x := 7940824#64) (n := 8)
    (hx := by rw [BitVec.toNat_ofNat]; omega) (hS := hS)
  have qs4 := rd_below (S := S) (x := 7940840#64) (n := 8)
    (hx := by rw [BitVec.toNat_ofNat]; omega) (hS := hS)
  have qs5 := rd_below (S := S) (x := 7940856#64) (n := 8)
    (hx := by rw [BitVec.toNat_ofNat]; omega) (hS := hS)
  have qs6 := rd_below (S := S) (x := 7940872#64) (n := 8)
    (hx := by rw [BitVec.toNat_ofNat]; omega) (hS := hS)
  have qs7 := rd_below (S := S) (x := 7940888#64) (n := 8)
    (hx := by rw [BitVec.toNat_ofNat]; omega) (hS := hS)
  have qs8 := rd_below (S := S) (x := 7940904#64) (n := 8)
    (hx := by rw [BitVec.toNat_ofNat]; omega) (hS := hS)
  have q1 := rd_below (S := S) (x := 8013224#64) (n := 8) (hx := by rw [BitVec.toNat_ofNat]; omega) (hS := hS)
  have q3 := rd_below (S := S) (n := 8) (hx := hfb) (hS := hS)
  have q5 := rd_below (S := S) (x := 7940592#64) (n := 8) (hx := by rw [BitVec.toNat_ofNat]; omega) (hS := hS)
  have hS' : S.toNat + 256 < 18446744073709551616 := hS
  have D : ∀ (x : Addr) (n : Nat), 7940480 ≤ x.toNat → x.toNat + n ≤ 7943136 →
      ∀ i < n, Foot F.data (Addr.add x i) :=
    fun x n h1 h2 i hi => hW _ (by simp only [Addr.add]; bv_omega) (by simp only [Addr.add]; bv_omega)
  clear hfz hbk
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  ( subst hsi
    wpx [W_0, W_9, W_46, W_55, W_544, W_563, W_848, W_86, W_984, W_1069, W_1099, o0, o1, o2, o3, o4, o5, o6, o7,
      o8, o9, o10, Op.cmpmia, Op.cmpmif, Op.cmpmra, Op.shr64, p1, p2, p3, p4, p5, p6, p7, q1, q3, q5, rd_off,
      rd_off_self, hS, hS', hgm, htb, htc, BitVec.and_self, G1n, V1n, f0, f1, f2, f3, f4, f5, f6, s2, s3,
      s4, s5, s6, s7, s8, qf0, qf1, qf2, qf3, qf4, qf5, qf6, qs2, qs3, qs4, qs5, qs6, qs7, qs8,
      BitVec.reduceAdd, BitVec.reduceAnd, BitVec.reduceSetWidth, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft,
      BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceBEq, BitVec.reduceEq, BitVec.reduceToNat,
      BitVec.reduceSub, BitVec.reduceMul, BitVec.reduceLT, BitVec.reduceULT, BitVec.reduceOr, BitVec.reduceXOr,
      m,
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

end FV7z.Im3
