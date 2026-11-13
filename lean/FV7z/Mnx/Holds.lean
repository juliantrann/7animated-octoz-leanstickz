import FV7z.Mnx.Cuts
import FV7z.Mal.Holds
import FV7z.Lemmas.Ksplit
import FV7z.Im3.Holds
/-!
# `malloc` after the first call: the blocks (PLAN.md G3, `malloc`)

glibc 2.31's `__libc_malloc (n)` at `0x633160` once `__malloc_hook` is null and the tcache made (the first call's
`malloc_hook_ini` did both), one thread. The blocks are those `malloc_hook_ini` has inline (`Mhi.vc_341n`,
`Mhi.vc_236m`, `Mhi.vc_130m`), here from `malloc`'s own entry, with its three pushes (`Mal.Vm`):

- `vc_0n` (`9 ≤ n ≤ 4104`), `vc_0s` (`n ≤ 8`): the pushes, the hook read back 0, `request2size` and the tcache index,
  to 52.
- `vc_52m`: the tcache there, its bin `k - 2` (below `mp_.tcache_bins` = 64) empty, to 83; `vc_52l`: `k ≥ 66`, no
  bin.
- `vc_83`: one thread (`fs:0x18` 0): `_int_malloc (&main_arena, n)` set up, to its `call` (109).
- `vc_114m`: the chunk back, its size word `16 k ||| 1` (not mmapped, of the main arena), to 164.
- `vc_164r`: the three pops, `rax` the chunk, to the `ret` (171).
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn FV7z.Start
namespace FV7z.Mnx
variable {F : Footprint} {Wl : List Rgn}

/-- The hook is read after the first push (of `r12`, below the stack pointer): the bytes there are the entry's. -/
theorem hk_rd (V : Addr → Byte) (rsp r12 : Addr) (hsp : 7940664 + 8 ≤ rsp.toNat) :
    List.map (Vst V (rsp - 8) (toBytesLE r12 8)) (byteAddrs 7940656#64 8) = List.map V (byteAddrs 7940656#64 8) := by
  have e8 : (rsp - 8).toNat = rsp.toNat - 8 := by bv_omega
  have l : (toBytesLE r12 8).length = 8 := toBytesLE_length _ _
  have e0 : (7940656#64 : Addr).toNat = 7940656 := rfl
  have hR := rsp.isLt
  exact Tun.rd_Vst _ _ _ _ _ (by rw [l, e8]; omega) (by rw [e0]; omega) (.inr (by rw [e0, e8]; omega))

theorem n_msb {n : Addr} (h : n.toNat ≤ 4104) : n.msb = false := by
  rw [BitVec.msb_eq_decide]; exact decide_eq_false (by show ¬ (2 ^ 63 ≤ n.toNat); omega)

/-- From the entry to 52, `9 ≤ n ≤ 4104`: the pushes, `rbp = n`, `request2size` in `rax`, the tcache index in `rbx`. -/
theorem vc_0n {fb n : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} (hdi : g.rdi = n)
    (hn : 9 ≤ n.toNat) (hn' : n.toNat ≤ 4104)
    (hhk : rdq(V, 7940656#64) = 0#64) (hfh : ∀ i < 8, Foot F.data (Addr.add (7940656#64) i))
    (hsp : 7940664 + 8 ≤ g.rsp.toNat) (hst : ∀ i < 24, Foot Wl (Addr.add (g.rsp - 24) i)) :
    W_0 fb F Wl (fun j' g' _ V' => j' = 52 ∧
      g' = { g with rax := n + 23#64 &&& 18446744073709551600#64,
                    rbx := ((n + 23#64 &&& 18446744073709551600#64) + 18446744073709551599#64) >>> 4,
                    rbp := n, rsp := g.rsp - 8 - 8 - 8 } ∧
      V' = Mal.Vm g V) g f V := by
  have m := n_msb hn'
  have e : (n + 23#64).toNat = n.toNat + 23 := by rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have d1 : decide ((n + 23#64).toNat < 31) = false := decide_eq_false (by omega)
  have d2 : decide (n + 23#64 = 31#64) = false :=
    decide_eq_false (fun h => by rw [h, BitVec.toNat_ofNat] at e; omega)
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hdi hsp hst ⊢
  subst hdi
  obtain ⟨s1, s2, s3⟩ := Mhi.push3 hst
  have ek := hk_rd V rsp r12 hsp
  wpx [W_0, W_27, W_36, W_176, o0, o1, o2, o12, Op.lda, Op.shr64, Mal.Vm, ek, hhk, m, d1, d2, BitVec.and_self,
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
    | exact ⟨s1, hfh, s2, s3⟩
    | exact ⟨s1, hfh, s2, s3, fun _ _ => trivial⟩
    | exact ⟨s1, hfh, s2, s3, fun _ => trivial⟩

/-- `vc_0n` for `n ≤ 8`: `request2size` below 32 (`MINSIZE`), the tcache index 0. -/
theorem vc_0s {fb n : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} (hdi : g.rdi = n) (hn : n.toNat ≤ 8)
    (hhk : rdq(V, 7940656#64) = 0#64) (hfh : ∀ i < 8, Foot F.data (Addr.add (7940656#64) i))
    (hsp : 7940664 + 8 ≤ g.rsp.toNat) (hst : ∀ i < 24, Foot Wl (Addr.add (g.rsp - 24) i)) :
    W_0 fb F Wl (fun j' g' _ V' => j' = 52 ∧
      g' = { g with rax := n + 23#64, rbx := 0#64, rbp := n, rsp := g.rsp - 8 - 8 - 8 } ∧
      V' = Mal.Vm g V) g f V := by
  have hc := Im3.clsS hn
  have m := n_msb (n := n) (by omega)
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hdi hsp hst ⊢
  subst hdi
  obtain ⟨s1, s2, s3⟩ := Mhi.push3 hst
  have ek := hk_rd V rsp r12 hsp
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  ( wpx [W_0, W_27, W_36, W_176, o0, o1, o2, o12, Op.lda, Op.shr64, Mal.Vm, ek, hhk, m, BitVec.and_self,
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
      | exact ⟨s1, hfh, s2, s3⟩
      | exact ⟨s1, hfh, s2, s3, fun _ _ => trivial⟩
      | exact ⟨s1, hfh, s2, s3, fun _ => trivial⟩)

set_option maxHeartbeats 50000000 in
/-- From 52 to 83: the tcache `C` there (`fs:-0x28`), its bin `k - 2` below `mp_.tcache_bins` and empty. -/
theorem vc_52m {fb C : Addr} {k : Nat} {g : Gprs} {f : Rflags} {V : Addr → Byte} (hk1 : 2 ≤ k) (hk2 : k ≤ 65)
    (hbx : g.rbx = (BitVec.ofNat 64 (16 * k) + 18446744073709551599#64) >>> 4)
    (htb : rdq(V, 7940592#64) = 64#64) (htc : rdq(V, fb + 18446744073709551576#64) = C) (hC : C ≠ 0#64)
    (hn : ∀ i < 64, ofBytesLE 16 ((byteAddrs (C + BitVec.ofNat 64 (2 * i)) 2).map V) = 0#16)
    (hfb : ∀ i < 8, Foot F.data (Addr.add (7940592#64) i))
    (hft : ∀ i < 8, Foot F.data (Addr.add (fb + 18446744073709551576#64) i))
    (hfn : ∀ i < 64, ∀ j < 2, Foot F.data (Addr.add (C + BitVec.ofNat 64 (2 * i)) j)) :
    W_52 fb F Wl (fun j' g' _ V' => j' = 83 ∧
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
  ksplit k from 2 to 65 using hk1 hk2 <;>
  ( simp only [Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub] at nk fk ⊢
    try simp only [e0] at nk fk
    wpx [W_52, W_70, W_256, o3, o4, o13, Op.cmpma, Op.ldf, Op.ldzx, htb, htc, hC', nk, BitVec.and_self,
      BitVec.reduceAdd, BitVec.reduceAnd, BitVec.reduceSetWidth, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft,
      BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceBEq, BitVec.reduceEq, BitVec.reduceToNat,
      BitVec.reduceSub, BitVec.reduceMul, BitVec.reduceLT, BitVec.reduceULT, BitVec.reduceOr, BitVec.reduceXOr,
      BitVec.reduceNot,
      Nat.reduceAdd, Nat.reduceLeDiff, Nat.reduceLT, decide_false, decide_true, Bool.or_false, Bool.false_or,
      Bool.not_false, Bool.not_true, Bool.false_eq_true, false_imp_iff, true_imp_iff, Bool.or_self, Bool.true_or,
      Bool.or_true, false_implies, true_implies, and_true, true_and, reduceIte, or_true, true_or, or_false, false_or,
      ne_eq, Nat.reduceEqDiff, not_false_eq_true, ofBytesLE_toBytesLE, Bool.true_eq_false, BitVec.xor_self,
      BitVec.add_zero]
    first | exact ⟨hft, hfb, fk⟩ | exact ⟨hfb, hft, fk⟩)

set_option maxHeartbeats 50000000 in
/-- From 52 to 83: the tcache there, the index `k - 2` not below `mp_.tcache_bins` (`66 ≤ k ≤ 257`). -/
theorem vc_52l {fb C : Addr} {k : Nat} {g : Gprs} {f : Rflags} {V : Addr → Byte} (hk1 : 66 ≤ k) (hk2 : k ≤ 257)
    (hbx : g.rbx = (BitVec.ofNat 64 (16 * k) + 18446744073709551599#64) >>> 4)
    (htb : rdq(V, 7940592#64) = 64#64) (htc : rdq(V, fb + 18446744073709551576#64) = C) (hC : C ≠ 0#64)
    (hfb : ∀ i < 8, Foot F.data (Addr.add (7940592#64) i))
    (hft : ∀ i < 8, Foot F.data (Addr.add (fb + 18446744073709551576#64) i)) :
    W_52 fb F Wl (fun j' g' _ V' => j' = 83 ∧ g' = { g with rax := C } ∧ V' = V) g f V := by
  have hC' : (C == 0) = false := beq_eq_false_iff_ne.2 hC
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hbx ⊢
  subst hbx
  ksplit k from 66 to 257 using hk1 hk2 <;>
  ( simp only [Nat.reduceMul, Nat.reduceAdd]
    wpx [W_52, W_70, o3, o4, Op.cmpma, Op.ldf, htb, htc, hC', BitVec.and_self,
      BitVec.reduceAdd, BitVec.reduceAnd, BitVec.reduceSetWidth, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft,
      BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceBEq, BitVec.reduceEq, BitVec.reduceToNat,
      BitVec.reduceSub, BitVec.reduceMul, BitVec.reduceLT, BitVec.reduceULT, BitVec.reduceOr, BitVec.reduceXOr,
      BitVec.reduceNot,
      Nat.reduceAdd, Nat.reduceLeDiff, Nat.reduceLT, decide_false, decide_true, Bool.or_false, Bool.false_or,
      Bool.not_false, Bool.not_true, Bool.false_eq_true, false_imp_iff, true_imp_iff, Bool.or_self, Bool.true_or,
      Bool.or_true, false_implies, true_implies, and_true, true_and, reduceIte, or_true, true_or, or_false, false_or,
      ne_eq, Nat.reduceEqDiff, not_false_eq_true, ofBytesLE_toBytesLE, Bool.true_eq_false, BitVec.xor_self,
      BitVec.add_zero]
    first | exact ⟨hft, hfb⟩ | exact ⟨hfb, hft⟩)

/-- From 83 to the `call` of `_int_malloc` (109): one thread; `rsi = n` (in `rbp`), `rdi = &main_arena`. -/
theorem vc_83 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (hmt : rdd(V, fb + 24#64) = 0) (hfl : ∀ i < 4, Foot F.data ((fb + 24#64).add i)) :
    W_83 fb F Wl (fun j' g' _ V' => j' = 109 ∧ g' = { g with rax := 0, rsi := g.rbp, rdi := 7940672#64 } ∧ V' = V)
      g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_83, W_99, o5, o6, Op.ldf, hmt, beq_iff_eq, BitVec.and_self,
      BitVec.reduceAdd, BitVec.reduceAnd, BitVec.reduceSetWidth, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft,
      BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceBEq, BitVec.reduceEq, BitVec.reduceToNat,
      BitVec.reduceSub, BitVec.reduceMul, BitVec.reduceLT, BitVec.reduceULT, BitVec.reduceOr, BitVec.reduceXOr,
      BitVec.reduceNot,
      Nat.reduceAdd, Nat.reduceLeDiff, Nat.reduceLT, decide_false, decide_true, Bool.or_false, Bool.false_or,
      Bool.not_false, Bool.not_true, Bool.false_eq_true, false_imp_iff, true_imp_iff, Bool.or_self, Bool.true_or,
      Bool.or_true, false_implies, true_implies, and_true, true_and, reduceIte, or_true, true_or, or_false, false_or,
      ne_eq, Nat.reduceEqDiff, not_false_eq_true, ofBytesLE_toBytesLE, Bool.true_eq_false, BitVec.xor_self,
      BitVec.add_zero]
  first | exact hfl | exact ⟨hfl, rfl⟩ | exact ⟨hfl, fun h => absurd h (by decide)⟩
    | exact ⟨hfl, fun _ => rfl⟩

set_option maxHeartbeats 50000000 in
/-- From the return of `_int_malloc` (114) to 164: the chunk not null, its size word `16 k ||| 1`. -/
theorem vc_114m {fb : Addr} {k : Nat} {g : Gprs} {f : Rflags} {V : Addr → Byte} (hk1 : 2 ≤ k) (hk2 : k ≤ 257)
    (hax : g.rax ≠ 0#64)
    (hsz : rdq(V, g.rax + 18446744073709551608#64) = BitVec.ofNat 64 (16 * k) ||| 1#64)
    (hfz : ∀ i < 8, Foot F.data (Addr.add (g.rax + 18446744073709551608#64) i)) :
    W_114 fb F Wl (fun j' g' _ V' => j' = 164 ∧
      g' = { g with rax := BitVec.ofNat 64 (16 * k) ||| 1#64, r8 := g.rax } ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hax hsz hfz ⊢
  have hax' : (rax == 0) = false := beq_eq_false_iff_ne.2 hax
  ksplit k from 2 to 257 using hk1 hk2 <;>
  ( simp only [Nat.reduceMul, Nat.reduceAdd] at hsz ⊢
    wpx [W_114, W_126, W_134, o7, o8, o9, hax', hsz, BitVec.and_self,
      BitVec.reduceAdd, BitVec.reduceAnd, BitVec.reduceSetWidth, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft,
      BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceBEq, BitVec.reduceEq, BitVec.reduceToNat,
      BitVec.reduceSub, BitVec.reduceMul, BitVec.reduceLT, BitVec.reduceULT, BitVec.reduceOr, BitVec.reduceXOr,
      BitVec.reduceNot,
      Nat.reduceAdd, Nat.reduceLeDiff, Nat.reduceLT, decide_false, decide_true, Bool.or_false, Bool.false_or,
      Bool.not_false, Bool.not_true, Bool.false_eq_true, false_imp_iff, true_imp_iff, Bool.or_self, Bool.true_or,
      Bool.or_true, false_implies, true_implies, and_true, true_and, reduceIte, or_true, true_or, or_false, false_or,
      ne_eq, Nat.reduceEqDiff, not_false_eq_true, ofBytesLE_toBytesLE, Bool.true_eq_false, BitVec.xor_self,
      BitVec.add_zero]
    first | exact hfz)

/-- From 164 to the `ret` (171): the three pops, `rax` the chunk (`r8`). -/
theorem vc_164r {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (hst : ∀ i < 24, Foot F.data (Addr.add g.rsp i)) :
    W_164 fb F Wl (fun j' g' _ V' => j' = 171 ∧ V' = V ∧ g'.rax = g.r8 ∧ g'.rsp = g.rsp + 8 + 8 + 8 ∧
      g'.rbx = rdq(V, g.rsp) ∧ g'.rbp = rdq(V, g.rsp + 8) ∧ g'.r12 = rdq(V, g.rsp + 8 + 8) ∧
      g'.r13 = g.r13 ∧ g'.r14 = g.r14 ∧ g'.r15 = g.r15) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hst
  wpx [W_164, o11]
  refine ⟨fun i hi => hst i (by omega), fun i hi => ?_, fun i hi => ?_⟩
  · have e : Addr.add rsp (8 + i) = Addr.add (rsp + 8) i := by simp only [Addr.add]; bv_omega
    exact e ▸ hst _ (by omega)
  · have e : Addr.add rsp (16 + i) = Addr.add (rsp + 8 + 8) i := by simp only [Addr.add]; bv_omega
    exact e ▸ hst _ (by omega)

end FV7z.Mnx
