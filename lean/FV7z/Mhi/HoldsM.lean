import FV7z.Mhi.HoldsN
import FV7z.Lemmas.Ksplit
/-!
# `malloc_hook_ini`: the tcache and size checks for every chunk size `16 k`, `2 ≤ k ≤ 257` (PLAN.md G3, `malloc`)

The checks of `malloc_hook_ini` after the tcache index, for the fastbin, smallbin and largebin sizes up to 4112 (the
requests `n ≤ 4096`), one `wpx` per `k` (`ksplit`):

- `vc_236m`: the tcache bin `k - 2` (below `mp_.tcache_bins` = 64, `k ≤ 65`) empty, on to offset 99.
- `vc_236l`: `k - 2` not below `mp_.tcache_bins` (`66 ≤ k ≤ 257`, the requests `1033 ≤ n ≤ 4096`): straight to 99.
- `vc_130m`: the size word `nb ||| 1` of the chunk back from `_int_malloc`, on to 180.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn FV7z.Start
namespace FV7z.Mhi
variable {F : Footprint} {Wl : List Rgn}

set_option maxHeartbeats 50000000 in
theorem vc_236m {fb C : Addr} {k : Nat} {g : Gprs} {f : Rflags} {V : Addr → Byte} (hk1 : 2 ≤ k) (hk2 : k ≤ 65)
    (hbx : g.rbx = (BitVec.ofNat 64 (16 * k) + 18446744073709551599#64) >>> 4)
    (htb : rdq(V, 7940592#64) = 64#64) (htc : rdq(V, fb + 18446744073709551576#64) = C) (hC : C ≠ 0#64)
    (hn : ∀ i < 64, ofBytesLE 16 ((byteAddrs (C + BitVec.ofNat 64 (2 * i)) 2).map V) = 0#16)
    (hfb : ∀ i < 8, Foot F.data (Addr.add (7940592#64) i))
    (hft : ∀ i < 8, Foot F.data (Addr.add (fb + 18446744073709551576#64) i))
    (hfn : ∀ i < 64, ∀ j < 2, Foot F.data (Addr.add (C + BitVec.ofNat 64 (2 * i)) j)) :
    W_236 fb F Wl (fun j' g' _ V' => j' = 99 ∧
      g' = { g with rax := C,
                    rcx := C + 2#64 * ((BitVec.ofNat 64 (16 * k) + 18446744073709551599#64) >>> 4),
                    rdx := 0#64 } ∧ V' = V)
      g f V := by
  have e0 : C + BitVec.ofNat 64 0 = C := by simp
  have nk := hn (k - 2) (by omega)
  have fk := hfn (k - 2) (by omega)
  have hC' : (C == 0) = false := beq_eq_false_iff_ne.2 hC
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hbx ⊢
  subst hbx
  clear hn hfn
  ksplit k from 2 using hk1 hk2 <;>
  ( simp only [Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub] at nk fk ⊢
    try simp only [e0] at nk fk
    wpx [W_236, W_249, W_267, W_272, o12, o13, o14, o15, Op.cmpmra, Op.ldf, Op.ldzx, htb, htc, hC', nk,
      BitVec.and_self,
      BitVec.reduceAdd, BitVec.reduceAnd, BitVec.reduceSetWidth, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft,
      BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceBEq, BitVec.reduceEq, BitVec.reduceToNat,
      BitVec.reduceSub, BitVec.reduceMul, BitVec.reduceLT, BitVec.reduceULT, BitVec.reduceOr, BitVec.reduceXOr,
      BitVec.reduceNot,
      Nat.reduceAdd, Nat.reduceLeDiff, Nat.reduceLT, decide_false, decide_true, Bool.or_false, Bool.false_or,
      Bool.not_false, Bool.not_true, Bool.false_eq_true, false_imp_iff, true_imp_iff, Bool.or_self, Bool.true_or,
      Bool.or_true, false_implies, true_implies, and_true, true_and, reduceIte, or_true, true_or, or_false, false_or,
      ne_eq, Nat.reduceEqDiff, not_false_eq_true, ofBytesLE_toBytesLE, Bool.true_eq_false, BitVec.xor_self,
      BitVec.add_zero]
    first | exact ⟨hfb, hft, fk⟩)

set_option maxHeartbeats 50000000 in
theorem vc_236l {fb : Addr} {k : Nat} {g : Gprs} {f : Rflags} {V : Addr → Byte} (hk1 : 66 ≤ k) (hk2 : k ≤ 257)
    (hbx : g.rbx = (BitVec.ofNat 64 (16 * k) + 18446744073709551599#64) >>> 4)
    (htb : rdq(V, 7940592#64) = 64#64) (hfb : ∀ i < 8, Foot F.data (Addr.add (7940592#64) i)) :
    W_236 fb F Wl (fun j' g' _ V' => j' = 99 ∧ g' = g ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hbx ⊢
  subst hbx
  ksplit k from 66 using hk1 hk2 <;>
  ( simp only [Nat.reduceMul, Nat.reduceAdd]
    wpx [W_236, o12, Op.cmpmra, htb, BitVec.and_self,
      BitVec.reduceAdd, BitVec.reduceAnd, BitVec.reduceSetWidth, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft,
      BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceBEq, BitVec.reduceEq, BitVec.reduceToNat,
      BitVec.reduceSub, BitVec.reduceMul, BitVec.reduceLT, BitVec.reduceULT, BitVec.reduceOr, BitVec.reduceXOr,
      BitVec.reduceNot,
      Nat.reduceAdd, Nat.reduceLeDiff, Nat.reduceLT, decide_false, decide_true, Bool.or_false, Bool.false_or,
      Bool.not_false, Bool.not_true, Bool.false_eq_true, false_imp_iff, true_imp_iff, Bool.or_self, Bool.true_or,
      Bool.or_true, false_implies, true_implies, and_true, true_and, reduceIte, or_true, true_or, or_false, false_or,
      ne_eq, Nat.reduceEqDiff, not_false_eq_true, ofBytesLE_toBytesLE, Bool.true_eq_false]
    first | exact hfb)

set_option maxHeartbeats 50000000 in
theorem vc_130m {fb : Addr} {k : Nat} {g : Gprs} {f : Rflags} {V : Addr → Byte} (hk1 : 2 ≤ k) (hk2 : k ≤ 257)
    (hax : g.rax ≠ 0#64)
    (hsz : rdq(V, g.rax + 18446744073709551608#64) = BitVec.ofNat 64 (16 * k) ||| 1#64)
    (hfz : ∀ i < 8, Foot F.data (Addr.add (g.rax + 18446744073709551608#64) i)) :
    W_130 fb F Wl (fun j' g' _ V' => j' = 180 ∧ g' = { g with rax := BitVec.ofNat 64 (16 * k) ||| 1#64, r8 := g.rax } ∧
      V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hax hsz hfz ⊢
  have hax' : (rax == 0) = false := beq_eq_false_iff_ne.2 hax
  ksplit k from 2 using hk1 hk2 <;>
  ( simp only [Nat.reduceMul, Nat.reduceAdd] at hsz ⊢
    wpx [W_130, W_142, W_150, o6, o7, o8, hax', hsz, BitVec.and_self,
      BitVec.reduceAdd, BitVec.reduceAnd, BitVec.reduceSetWidth, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft,
      BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceBEq, BitVec.reduceEq, BitVec.reduceToNat,
      BitVec.reduceSub, BitVec.reduceMul, BitVec.reduceLT, BitVec.reduceULT, BitVec.reduceOr, BitVec.reduceXOr,
      BitVec.reduceNot,
      Nat.reduceAdd, Nat.reduceLeDiff, Nat.reduceLT, decide_false, decide_true, Bool.or_false, Bool.false_or,
      Bool.not_false, Bool.not_true, Bool.false_eq_true, false_imp_iff, true_imp_iff, Bool.or_self, Bool.true_or,
      Bool.or_true, false_implies, true_implies, and_true, true_and, reduceIte, or_true, true_or, or_false, false_or,
      ne_eq, Nat.reduceEqDiff, not_false_eq_true, ofBytesLE_toBytesLE, Bool.true_eq_false, BitVec.xor_self]
    first | exact hfz)

end FV7z.Mhi
