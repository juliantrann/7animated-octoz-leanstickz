import FV7z.Im2.Head
/-! Probe: `Im2.vc_0` with the request `n` symbolic (class 9 ≤ n ≤ 120); show the goal after `wpx`. -/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn FV7z.Start
open FV7z.Imm (imm imm_at rd_off rd_off_self rd_below stk_f pu)
namespace FV7z.Im2
variable {F : Footprint} {Wl : List Rgn}

set_option maxHeartbeats 1000000 in
theorem vc_0n {fb S n : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} (hrsp : g.rsp = S + 184#64)
    (hsi : g.rsi = n) (hdi : g.rdi = 7940672#64) (hn : 9 ≤ n.toNat) (hn' : n.toNat ≤ 120)
    (hS : S.toNat + 256 < 2 ^ 64) (hlo : 8029888 ≤ S.toNat)
    (hfb : (fb + 18446744073709551576#64).toNat + 8 ≤ S.toNat)
    (hgm : rdq(V, 8013224#64) = 128#64)
    (hsb : rdq(V, 7940840#64) = 7940816#64)
    (htc : rdq(V, fb + 18446744073709551576#64) ≠ 0#64) (htb : rdq(V, 7940592#64) = 64#64) :
    W_0 fb F Wl (fun j' _ _ _ => j' = 1115) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hrsp hsi hdi ⊢
  subst hrsp hsi hdi
  obtain ⟨p1, p2, p3, p4, p5, p6, p7⟩ := pu S
  have q1 := rd_below (S := S) (x := 8013224#64) (n := 8) (hx := by rw [BitVec.toNat_ofNat]; omega) (hS := hS)
  have q3 := rd_below (S := S) (n := 8) (hx := hfb) (hS := hS)
  have q4 := rd_below (S := S) (x := 7940840#64) (n := 8) (hx := by rw [BitVec.toNat_ofNat]; omega) (hS := hS)
  have q5 := rd_below (S := S) (x := 7940592#64) (n := 8) (hx := by rw [BitVec.toNat_ofNat]; omega) (hS := hS)
  have hS' : S.toNat + 256 < 18446744073709551616 := hS
  wpx [W_0, W_9, W_304, W_320, W_960, W_563, W_848, W_86, W_984, W_1069, W_1099, o0, o1, o2, o3, o4, o5, o6, o8,
    o9, o10, o11, Op.cmpma, Op.cmpmif, Op.cmpmra, Op.shr64, p1, p2, p3, p4, p5, p6, p7, q1, q3, q4, q5, rd_off,
    rd_off_self, hS, hS', hgm, hsb, htb, htc,
    BitVec.reduceAdd, BitVec.reduceAnd, BitVec.reduceSetWidth, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft,
    BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceBEq, BitVec.reduceEq, BitVec.reduceToNat,
    BitVec.reduceSub, BitVec.reduceMul, BitVec.reduceLT, BitVec.reduceULT, BitVec.reduceOr, BitVec.reduceXOr,
    Nat.reduceAdd, Nat.reduceLeDiff, Nat.reduceLT, decide_false, decide_true, Bool.or_false, Bool.false_or,
    Bool.not_false, Bool.not_true, Bool.false_eq_true, false_imp_iff, true_imp_iff, Bool.or_self, Bool.true_or,
    Bool.or_true, false_implies, true_implies, and_true, true_and, reduceIte, or_true, true_or, or_false, false_or,
    ne_eq, Nat.reduceEqDiff, not_false_eq_true, ofBytesLE_toBytesLE, Bool.true_eq_false]
  trace_state
  sorry

end FV7z.Im2
