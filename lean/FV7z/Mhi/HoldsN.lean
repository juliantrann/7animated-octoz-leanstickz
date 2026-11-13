import FV7z.Mhi.Holds
import FV7z.Im3.Holds
/-!
# `malloc_hook_ini`: the size checks for every request `9 ≤ n ≤ 4096` (PLAN.md G3, `malloc`)

- `vc_341n`: `__malloc_hook` read back 0, `request2size` (`n + 23 &&& -16`) and the tcache index
  (`nb - 17 >>> 4`), on to offset 68; `vc_341s` for `n ≤ 8` (`nb` = 32, the index 0, one `wpx` per `n`).
- `vc_236n`, `vc_130n` (`9 ≤ n ≤ 120`, `nb` a fastbin size, one `wpx` per `nb`): the tcache bin of `nb` empty, on
  to offset 99; the size word `nb ||| 1` of the chunk back from `_int_malloc`, on to 180.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn FV7z.Start
namespace FV7z.Mhi
variable {F : Footprint} {Wl : List Rgn}

theorem vc_341n {fb n : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} (hbp : g.rbp = n)
    (hn : 9 ≤ n.toNat) (hn' : n.toNat ≤ 4096)
    (hhk : rdq(V, 7940656#64) = 0#64) (hfh : ∀ i < 8, Foot F.data (Addr.add (7940656#64) i)) :
    W_341 fb F Wl (fun j' g' _ V' => j' = 68 ∧
      g' = { g with rax := n + 23#64 &&& 18446744073709551600#64,
                    rbx := ((n + 23#64 &&& 18446744073709551600#64) + 18446744073709551599#64) >>> 4 } ∧
      V' = V) g f V := by
  have m : n.msb = false := by
    rw [BitVec.msb_eq_decide]; exact decide_eq_false (by show ¬ (2 ^ 63 ≤ n.toNat); omega)
  have e : (n + 23#64).toNat = n.toNat + 23 := by rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have d1 : decide ((n + 23#64).toNat < 31) = false := decide_eq_false (by omega)
  have d2 : decide (n + 23#64 = 31#64) = false :=
    decide_eq_false (fun h => by rw [h, BitVec.toNat_ofNat] at e; omega)
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hbp ⊢
  subst hbp
  wpx [W_341, W_47, W_56, W_192, o16, o1, o2, o10, Op.lda, Op.shr64, m, d1, d2, hhk, BitVec.and_self,
    BitVec.reduceAdd, BitVec.reduceAnd, BitVec.reduceSetWidth, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft,
    BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceBEq, BitVec.reduceEq, BitVec.reduceToNat,
    BitVec.reduceSub, BitVec.reduceMul, BitVec.reduceLT, BitVec.reduceULT, BitVec.reduceOr, BitVec.reduceXOr,
    BitVec.reduceNot,
    Nat.reduceAdd, Nat.reduceLeDiff, Nat.reduceLT, decide_false, decide_true, Bool.or_false, Bool.false_or,
    Bool.not_false, Bool.not_true, Bool.false_eq_true, false_imp_iff, true_imp_iff, Bool.or_self, Bool.true_or,
    Bool.or_true, false_implies, true_implies, and_true, true_and, reduceIte, or_true, true_or, or_false, false_or,
    ne_eq, Nat.reduceEqDiff, not_false_eq_true, ofBytesLE_toBytesLE, Bool.true_eq_false, BitVec.xor_self]
  first | exact ⟨hfh, fun _ _ => trivial⟩ | exact hfh | exact ⟨hfh, fun _ => trivial⟩

theorem vc_236n {fb C nb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (hnb : nb = 32#64 ∨ nb = 48#64 ∨ nb = 64#64 ∨ nb = 80#64 ∨ nb = 96#64 ∨ nb = 112#64 ∨ nb = 128#64)
    (hbx : g.rbx = (nb + 18446744073709551599#64) >>> 4)
    (htb : rdq(V, 7940592#64) = 64#64) (htc : rdq(V, fb + 18446744073709551576#64) = C) (hC : C ≠ 0#64)
    (hn : ∀ i < 7, ofBytesLE 16 ((byteAddrs (C + BitVec.ofNat 64 (2 * i)) 2).map V) = 0#16)
    (hfb : ∀ i < 8, Foot F.data (Addr.add (7940592#64) i))
    (hft : ∀ i < 8, Foot F.data (Addr.add (fb + 18446744073709551576#64) i))
    (hfn : ∀ i < 7, ∀ j < 2, Foot F.data (Addr.add (C + BitVec.ofNat 64 (2 * i)) j)) :
    W_236 fb F Wl (fun j' g' _ V' => j' = 99 ∧
      g' = { g with rax := C, rcx := C + 2#64 * ((nb + 18446744073709551599#64) >>> 4), rdx := 0#64 } ∧ V' = V)
      g f V := by
  have e0 : C + BitVec.ofNat 64 (2 * 0) = C := by simp
  have n0 : ofBytesLE 16 ((byteAddrs C 2).map V) = 0#16 := e0 ▸ hn 0 (by decide)
  have n1 : ofBytesLE 16 ((byteAddrs (C + 2#64) 2).map V) = 0#16 := hn 1 (by decide)
  have n2 : ofBytesLE 16 ((byteAddrs (C + 4#64) 2).map V) = 0#16 := hn 2 (by decide)
  have n3 : ofBytesLE 16 ((byteAddrs (C + 6#64) 2).map V) = 0#16 := hn 3 (by decide)
  have n4 : ofBytesLE 16 ((byteAddrs (C + 8#64) 2).map V) = 0#16 := hn 4 (by decide)
  have n5 : ofBytesLE 16 ((byteAddrs (C + 10#64) 2).map V) = 0#16 := hn 5 (by decide)
  have n6 : ofBytesLE 16 ((byteAddrs (C + 12#64) 2).map V) = 0#16 := hn 6 (by decide)
  have f0 : ∀ j < 2, Foot F.data (Addr.add C j) := e0 ▸ hfn 0 (by decide)
  have f1 : ∀ j < 2, Foot F.data (Addr.add (C + 2#64) j) := hfn 1 (by decide)
  have f2 : ∀ j < 2, Foot F.data (Addr.add (C + 4#64) j) := hfn 2 (by decide)
  have f3 : ∀ j < 2, Foot F.data (Addr.add (C + 6#64) j) := hfn 3 (by decide)
  have f4 : ∀ j < 2, Foot F.data (Addr.add (C + 8#64) j) := hfn 4 (by decide)
  have f5 : ∀ j < 2, Foot F.data (Addr.add (C + 10#64) j) := hfn 5 (by decide)
  have f6 : ∀ j < 2, Foot F.data (Addr.add (C + 12#64) j) := hfn 6 (by decide)
  have hC' : (C == 0) = false := beq_eq_false_iff_ne.2 hC
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hbx ⊢
  subst hbx
  rcases hnb with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  ( wpx [W_236, W_249, W_267, W_272, o12, o13, o14, o15, Op.cmpmra, Op.ldf, Op.ldzx, htb, htc, hC',
      n0, n1, n2, n3, n4, n5, n6,
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
    first
      | exact ⟨hfb, hft, f0⟩
      | exact ⟨hfb, hft, f1⟩
      | exact ⟨hfb, hft, f2⟩
      | exact ⟨hfb, hft, f3⟩
      | exact ⟨hfb, hft, f4⟩
      | exact ⟨hfb, hft, f5⟩
      | exact ⟨hfb, hft, f6⟩)

theorem vc_130n {fb nb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (hnb : nb = 32#64 ∨ nb = 48#64 ∨ nb = 64#64 ∨ nb = 80#64 ∨ nb = 96#64 ∨ nb = 112#64 ∨ nb = 128#64)
    (hax : g.rax ≠ 0#64)
    (hsz : rdq(V, g.rax + 18446744073709551608#64) = nb ||| 1#64)
    (hfz : ∀ i < 8, Foot F.data (Addr.add (g.rax + 18446744073709551608#64) i)) :
    W_130 fb F Wl (fun j' g' _ V' => j' = 180 ∧ g' = { g with rax := nb ||| 1#64, r8 := g.rax } ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hax hsz hfz ⊢
  have hax' : (rax == 0) = false := beq_eq_false_iff_ne.2 hax
  rcases hnb with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  ( wpx [W_130, W_142, W_150, o6, o7, o8, hax', hsz, BitVec.and_self,
      BitVec.reduceAdd, BitVec.reduceAnd, BitVec.reduceSetWidth, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft,
      BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceBEq, BitVec.reduceEq, BitVec.reduceToNat,
      BitVec.reduceSub, BitVec.reduceMul, BitVec.reduceLT, BitVec.reduceULT, BitVec.reduceOr, BitVec.reduceXOr,
      BitVec.reduceNot,
      Nat.reduceAdd, Nat.reduceLeDiff, Nat.reduceLT, decide_false, decide_true, Bool.or_false, Bool.false_or,
      Bool.not_false, Bool.not_true, Bool.false_eq_true, false_imp_iff, true_imp_iff, Bool.or_self, Bool.true_or,
      Bool.or_true, false_implies, true_implies, and_true, true_and, reduceIte, or_true, true_or, or_false, false_or,
      ne_eq, Nat.reduceEqDiff, not_false_eq_true, ofBytesLE_toBytesLE, Bool.true_eq_false, BitVec.xor_self]
    first | exact hfz)

/-- `vc_341n` for the requests `n ≤ 8`: `request2size` gives `MINSIZE` (`n + 23` below 32), the tcache index 0. -/
theorem vc_341s {fb n : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} (hbp : g.rbp = n) (hn : n.toNat ≤ 8)
    (hhk : rdq(V, 7940656#64) = 0#64) (hfh : ∀ i < 8, Foot F.data (Addr.add (7940656#64) i)) :
    W_341 fb F Wl (fun j' g' _ V' => j' = 68 ∧ g' = { g with rax := n + 23#64, rbx := 0#64 } ∧ V' = V) g f V := by
  have hc := Im3.clsS hn
  have m : n.msb = false := by
    rw [BitVec.msb_eq_decide]; exact decide_eq_false (by show ¬ (2 ^ 63 ≤ n.toNat); omega)
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hbp ⊢
  subst hbp
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  ( wpx [W_341, W_47, W_56, W_192, o16, o1, o2, o10, Op.lda, Op.shr64, hhk, BitVec.and_self,
      BitVec.reduceAdd, BitVec.reduceAnd, BitVec.reduceSetWidth, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft,
      BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceBEq, BitVec.reduceEq, BitVec.reduceToNat,
      BitVec.reduceSub, BitVec.reduceMul, BitVec.reduceLT, BitVec.reduceULT, BitVec.reduceOr, BitVec.reduceXOr,
      BitVec.reduceNot, m,
      Nat.reduceAdd, Nat.reduceLeDiff, Nat.reduceLT, decide_false, decide_true, Bool.or_false, Bool.false_or,
      Bool.not_false, Bool.not_true, Bool.false_eq_true, false_imp_iff, true_imp_iff, Bool.or_self, Bool.true_or,
      Bool.or_true, false_implies, true_implies, and_true, true_and, reduceIte, or_true, true_or, or_false, false_or,
      ne_eq, Nat.reduceEqDiff, not_false_eq_true, ofBytesLE_toBytesLE, Bool.true_eq_false, BitVec.xor_self]
    first | exact ⟨hfh, fun _ _ => trivial⟩ | exact hfh | exact ⟨hfh, fun _ => trivial⟩)

end FV7z.Mhi
