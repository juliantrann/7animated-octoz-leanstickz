import FV7z.Mhi.Holds
/-! Probe: `Mhi.vc_341` with the request `n` symbolic (9 ≤ n ≤ 4096); show the goal after `wpx`. -/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn FV7z.Start
namespace FV7z.Mhi
variable {F : Footprint} {Wl : List Rgn}

theorem vc_341n {fb n : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} (hbp : g.rbp = n)
    (hn : 9 ≤ n.toNat) (hn' : n.toNat ≤ 4096)
    (hhk : rdq(V, 7940656#64) = 0#64) (hfh : ∀ i < 8, Foot F.data (Addr.add (7940656#64) i)) :
    W_341 fb F Wl (fun j' g' _ V' => j' = 68 ∧
      g' = { g with rax := n + 23#64 &&& 18446744073709551600#64,
                    rbx := (n + 23#64 &&& 18446744073709551600#64) - 17#64 >>> 4 } ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hbp ⊢
  subst hbp
  have m : n.msb = false := by
    rw [BitVec.msb_eq_decide]; simp only [decide_eq_false_iff_not, Nat.not_le]; omega
  wpx [W_341, W_47, W_56, W_192, o16, o1, o2, o10, Op.lda, Op.shr64, m, hhk, BitVec.and_self,
    BitVec.reduceAdd, BitVec.reduceAnd, BitVec.reduceSetWidth, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft,
    BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceBEq, BitVec.reduceEq, BitVec.reduceToNat,
    BitVec.reduceSub, BitVec.reduceMul, BitVec.reduceLT, BitVec.reduceULT, BitVec.reduceOr, BitVec.reduceXOr,
    BitVec.reduceNot,
    Nat.reduceAdd, Nat.reduceLeDiff, Nat.reduceLT, decide_false, decide_true, Bool.or_false, Bool.false_or,
    Bool.not_false, Bool.not_true, Bool.false_eq_true, false_imp_iff, true_imp_iff, Bool.or_self, Bool.true_or,
    Bool.or_true, false_implies, true_implies, and_true, true_and, reduceIte, or_true, true_or, or_false, false_or,
    ne_eq, Nat.reduceEqDiff, not_false_eq_true, ofBytesLE_toBytesLE, Bool.true_eq_false, BitVec.xor_self]
  trace_state
  sorry

end FV7z.Mhi
