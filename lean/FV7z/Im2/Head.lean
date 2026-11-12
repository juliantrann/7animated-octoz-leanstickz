import FV7z.Im2.Cuts
import FV7z.Imm.Head
/-!
# `_int_malloc`: from the entry to offset 1115, the second call (PLAN.md G3, `malloc`)

The second call comes from `malloc_hook_ini` with 50 bytes asked for (`nb` = 64, fastbin 2, smallbin 4), the
tcache made.

- `vc_0`, `im2_a`: from the entry to offset 1115: the frame, fastbin 2 and smallbin 4 empty, the tcache there and
  `tc_idx` 2 below `mp_.tcache_bins`; `G1`, `V1`: the registers and bytes there.
- `vc_1115`: from offset 1115 to 2549 (`use_top`): the unsorted bin and `binmap[0..3]` empty; `G2`, `V2`.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn FV7z.Start
open FV7z.Imm (imm imm_at rd_off rd_off_self rd_below stk_f pu)
namespace FV7z.Im2
variable {F : Footprint} {Wl : List Rgn}

/-- The bytes at offset 1115 on the second call: the six pushes and the frame stores. -/
def V1 (S : Addr) (g : Gprs) (V : Addr → Byte) : Addr → Byte :=
  Vst (Vst (Vst (Vst (Vst (Vst (Vst (Vst (Vst (Vst (Vst (Vst (Vst (Vst (Vst (Vst (Vst (Vst V
    (S + 176#64) (toBytesLE g.r15 8)) (S + 168#64) (toBytesLE g.r14 8)) (S + 160#64) (toBytesLE g.r13 8))
    (S + 152#64) (toBytesLE g.r12 8)) (S + 144#64) (toBytesLE g.rbp 8)) (S + 136#64) (toBytesLE g.rbx 8))
    (S + 40#64) (toBytesLE (4#32) 4)) (S + 112#64) (toBytesLE (110#32) 4)) (S + 64#64) (toBytesLE (1#64) 8))
    (S + 80#64) (toBytesLE (0#64) 8)) (S + 116#64) (toBytesLE (91#32) 4)) (S + 76#64) (toBytesLE (49#32) 4))
    (S + 108#64) (toBytesLE (119#32) 4)) (S + 104#64) (toBytesLE (124#32) 4)) (S + 96#64) (toBytesLE (0#64) 8))
    (S + 88#64) (toBytesLE (0#64) 8)) (S + 16#64) (toBytesLE (0#64) 8)) (S + 16#64) (toBytesLE (64#64) 8)

/-- The registers at offset 1115 on the second call. -/
abbrev G1 (S : Addr) (g : Gprs) : Gprs :=
  ⟨64#64, 7940816#64, g.rdx, 7940672#64, S, 50#64, 50#64, 91#64, 7940816#64, g.r9, g.r10, g.r11, g.r12, 64#64,
    4#64, 2#64⟩

set_option maxHeartbeats 1000000 in
theorem vc_0 {fb S : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} (hrsp : g.rsp = S + 184#64)
    (hsi : g.rsi = 50#64) (hdi : g.rdi = 7940672#64)
    (hS : S.toNat + 256 < 2 ^ 64) (hlo : 8029888 ≤ S.toNat)
    (hfb : (fb + 18446744073709551576#64).toNat + 8 ≤ S.toNat)
    (hgm : 64 ≤ (rdq(V, 8013224#64)).toNat) (hf2 : rdq(V, 7940704#64) = 0#64)
    (hsb : rdq(V, 7940840#64) = 7940816#64)
    (htc : rdq(V, fb + 18446744073709551576#64) ≠ 0#64) (htb : rdq(V, 7940592#64) = 64#64)
    (hW : ∀ a : Addr, 7940480 ≤ a.toNat → a.toNat < 7943136 → Foot F.data a)
    (hgf : ∀ i < 8, Foot F.data (Addr.add (8013224#64) i))
    (htf : ∀ i < 8, Foot F.data (Addr.add (fb + 18446744073709551576#64) i))
    (hsw : ∀ i < 184, Foot Wl (Addr.add S i)) :
    W_0 fb F Wl (fun j' g' _ V' => j' = 1115 ∧ g' = G1 S g ∧ V' = V1 S g V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hrsp hsi hdi ⊢
  subst hrsp hsi hdi
  obtain ⟨p1, p2, p3, p4, p5, p6, p7⟩ := pu S
  have q1 := rd_below (S := S) (x := 8013224#64) (n := 8) (hx := by rw [BitVec.toNat_ofNat]; omega) (hS := hS)
  have q2 := rd_below (S := S) (x := 7940704#64) (n := 8) (hx := by rw [BitVec.toNat_ofNat]; omega) (hS := hS)
  have q3 := rd_below (S := S) (n := 8) (hx := hfb) (hS := hS)
  have q4 := rd_below (S := S) (x := 7940840#64) (n := 8) (hx := by rw [BitVec.toNat_ofNat]; omega) (hS := hS)
  have q5 := rd_below (S := S) (x := 7940592#64) (n := 8) (hx := by rw [BitVec.toNat_ofNat]; omega) (hS := hS)
  have c0 : (50#64 : BitVec 64).msb = false := by decide
  have hS' : S.toNat + 256 < 18446744073709551616 := hS
  have t1 : (decide (64 < (rdq(V, 8013224#64)).toNat) || decide (64#64 = rdq(V, 8013224#64))) = true := by
    rcases Nat.lt_or_eq_of_le hgm with h | h
    · simp [h]
    · have : (64#64 : BitVec 64) = rdq(V, 8013224#64) := BitVec.eq_of_toNat_eq (by rw [← h]; rfl)
      simp [this]
  wpx [W_0, W_9, W_304, W_320, W_960, W_563, W_848, W_86, W_984, W_1069, W_1099, o0, o1, o2, o3, o4, o5, o6, o8,
    o9, o10, o11, Op.cmpma, Op.cmpmif, Op.cmpmra, Op.shr64, p1, p2, p3, p4, p5, p6, p7, q1, q2, q3, q4, q5, rd_off,
    rd_off_self, hS, hS', c0, t1, hf2, hsb, htb, htc,
    BitVec.reduceAdd, BitVec.reduceAnd, BitVec.reduceSetWidth, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft,
    BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceBEq, BitVec.reduceEq, BitVec.reduceToNat,
    BitVec.reduceSub, BitVec.reduceMul, BitVec.reduceLT, BitVec.reduceULT, BitVec.reduceOr, BitVec.reduceXOr,
    Nat.reduceAdd, Nat.reduceLeDiff, Nat.reduceLT, decide_false, decide_true, Bool.or_false, Bool.false_or,
    Bool.not_false, Bool.not_true, Bool.false_eq_true, false_imp_iff, true_imp_iff, Bool.or_self, Bool.true_or,
    Bool.or_true, false_implies, true_implies, and_true, true_and, reduceIte, or_true, true_or, or_false, false_or,
    ne_eq, Nat.reduceEqDiff, not_false_eq_true, ofBytesLE_toBytesLE, Bool.true_eq_false]
  have D : ∀ (x : Addr) (n : Nat), 7940480 ≤ x.toNat → x.toNat + n ≤ 7943136 →
      ∀ i < n, Foot F.data (Addr.add x i) :=
    fun x n h1 h2 i hi => hW _ (by simp only [Addr.add]; bv_omega) (by simp only [Addr.add]; bv_omega)
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

/-- The bytes at offset 2549 on the second call. -/
abbrev V2 (S : Addr) (g : Gprs) (V : Addr → Byte) : Addr → Byte :=
  Vst (Vst (Vst (V1 S g V) (S + 8#64) (toBytesLE (0#64) 8)) (S + 72#64) (toBytesLE (4#32) 4)) (S + 32#64)
    (toBytesLE (50#64) 8)

/-- The registers at offset 2549 on the second call. -/
abbrev G2 (S : Addr) (g : Gprs) : Gprs :=
  ⟨2#64, 5#64, 2#64, 7940672#64, S, 50#64, 0#64, 0#64, 7940816#64, g.r9, 7940768#64, 7940768#64, g.r12, 64#64,
    4#64, 2#64⟩

set_option maxHeartbeats 1000000 in
theorem vc_1115 {fb S : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (hS : S.toNat + 256 < 2 ^ 64) (hlo : 8029888 ≤ S.toNat)
    (hun : rdq(V, 7940792#64) = 7940768#64)
    (hm0 : rdd(V, 7942816#64) = 0) (hm1 : rdd(V, 7942820#64) = 0) (hm2 : rdd(V, 7942824#64) = 0)
    (hm3 : rdd(V, 7942828#64) = 0)
    (hW : ∀ a : Addr, 7940480 ≤ a.toNat → a.toNat < 7943136 → Foot F.data a)
    (hsw : ∀ i < 184, Foot Wl (Addr.add S i)) (hsd : ∀ i < 184, Foot F.data (Addr.add S i)) :
    W_1115 fb F Wl (fun j' g' _ V' => j' = 2549 ∧ g' = G2 S g ∧ V' = V2 S g V) (G1 S g) f (V1 S g V) := by
  have q1 := rd_below (S := S) (x := 7940792#64) (n := 8) (hx := by rw [BitVec.toNat_ofNat]; omega) (hS := hS)
  have q2 := rd_below (S := S) (x := 7942816#64) (n := 4) (hx := by rw [BitVec.toNat_ofNat]; omega) (hS := hS)
  have q3 := rd_below (S := S) (x := 7942820#64) (n := 4) (hx := by rw [BitVec.toNat_ofNat]; omega) (hS := hS)
  have q4 := rd_below (S := S) (x := 7942824#64) (n := 4) (hx := by rw [BitVec.toNat_ofNat]; omega) (hS := hS)
  have q5 := rd_below (S := S) (x := 7942828#64) (n := 4) (hx := by rw [BitVec.toNat_ofNat]; omega) (hS := hS)
  have hS' : S.toNat + 256 < 18446744073709551616 := hS
  wpx [W_1115, W_1138, W_1968, W_2012, W_2048, W_2480, W_2488, W_2505, W_2513, W_2530, W_2535, V1, o12, o13, o14,
    o15, o16, o17, o18, o19, o20, o21, q1, q2, q3, q4, q5, rd_off, rd_off_self, hS, hS', hun, hm0, hm1, hm2, hm3,
    BitVec.reduceAdd, BitVec.reduceAnd, BitVec.reduceSetWidth, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft,
    BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceBEq, BitVec.reduceEq, BitVec.reduceToNat,
    BitVec.reduceSub, BitVec.reduceMul, BitVec.reduceLT, BitVec.reduceULT, BitVec.reduceOr, BitVec.reduceXOr,
    Nat.reduceAdd, Nat.reduceLeDiff, Nat.reduceLT, decide_false, decide_true, Bool.or_false, Bool.false_or,
    Bool.not_false, Bool.not_true, Bool.false_eq_true, false_imp_iff, true_imp_iff, Bool.or_self, Bool.true_or,
    Bool.or_true, false_implies, true_implies, and_true, true_and, reduceIte, or_true, true_or, or_false, false_or,
    ne_eq, Nat.reduceEqDiff, not_false_eq_true, ofBytesLE_toBytesLE, Bool.true_eq_false]
  have D : ∀ (x : Addr) (n : Nat), 7940480 ≤ x.toNat → x.toNat + n ≤ 7943136 →
      ∀ i < n, Foot F.data (Addr.add x i) :=
    fun x n h1 h2 i hi => hW _ (by simp only [Addr.add]; bv_omega) (by simp only [Addr.add]; bv_omega)
  repeat' first
    | apply And.intro
    | intro (_ : Rflags)
    | rfl
    | with_reducible exact stk_f hsw (by decide)
    | with_reducible exact stk_f hsd (by decide)
    | with_reducible exact D _ _ (by decide) (by decide)

end FV7z.Im2
