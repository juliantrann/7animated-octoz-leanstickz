import FV7z.Mhi.Hand
import FV7z.Imm.Head
/-!
# `malloc_hook_ini`: the pieces between the calls, the first `malloc` (PLAN.md G3, `malloc`)

The way of the first `malloc (50)`: `__malloc_initialized` below 0, so `ptmalloc_init`; no hook after it; 50 bytes
(`tc_idx` 2); no thread's cache yet and not shutting down, so `tcache_init`; its bin 2 empty; one thread, so
`_int_malloc (&main_arena, 50)`; the chunk neither mapped nor of another arena.

- `vc_0`: from the entry to the `call` of `ptmalloc_init` (336): the three pushes, `__malloc_hook` cleared.
- `vc_341`: from the return of `ptmalloc_init` to 68: no hook; `rbx` = `tc_idx` = 2.
- `vc_68`: from 68 to the `call` of `tcache_init` (231): no cache, not shutting down.
- `vc_236`: from the return of `tcache_init` to 99: `tc_idx` below `mp_.tcache_bins`, the cache there, its count 0.
- `vc_99`: from 99 to the `call` of `_int_malloc` (125): one thread; the arguments.
- `vc_130`: from the return of `_int_malloc` to 180: a chunk, its size word without `IS_MMAPPED` and
  `NON_MAIN_ARENA`.
- `vc_180`: from 180 to the `ret` (187): the three pops, the chunk in `rax`.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn FV7z.Start
open FV7z.Tun (rd_Vst rd_Vst_self Vst_out)
namespace FV7z.Mhi
variable {F : Footprint} {Wl : List Rgn}

/-- The three 8-byte slots of the pushes inside the 24 bytes below the stack pointer. -/
theorem push3 {R : List Rgn} {S : Addr} (h : ∀ i < 24, Foot R (Addr.add (S - 24) i)) :
    (∀ i < 8, Foot R (Addr.add (S - 8) i)) ∧ (∀ i < 8, Foot R (Addr.add (S - 8 - 8) i)) ∧
      ∀ i < 8, Foot R (Addr.add (S - 8 - 8 - 8) i) := by
  refine ⟨fun i hi => ?_, fun i hi => ?_, fun i hi => ?_⟩
  · have e : Addr.add (S - 24) (16 + i) = Addr.add (S - 8) i := by simp only [Addr.add]; bv_omega
    exact e ▸ h _ (by omega)
  · have e : Addr.add (S - 24) (8 + i) = Addr.add (S - 8 - 8) i := by simp only [Addr.add]; bv_omega
    exact e ▸ h _ (by omega)
  · have e : Addr.add (S - 24) (0 + i) = Addr.add (S - 8 - 8 - 8) i := by simp only [Addr.add]; bv_omega
    exact e ▸ h _ (by omega)

set_option maxHeartbeats 1000000 in
theorem vc_0 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (hmi : (rdd(V, 7940484#64)).msb = true)
    (hfm : ∀ i < 4, Foot F.data (Addr.add (7940484#64) i)) (hfh : ∀ i < 8, Foot Wl (Addr.add (7940656#64) i))
    (hst : ∀ i < 24, Foot Wl (Addr.add (g.rsp - 24) i)) :
    W_0 fb F Wl (fun j' g' _ V' => j' = 336 ∧
      g' = { g with rax := (rdd(V, 7940484#64)).setWidth 64, rsp := g.rsp - 8 - 8 - 8, rbp := g.rdi } ∧
      V' = Vst (Vst (Vst (Vst V (g.rsp - 8) (toBytesLE g.r12 8)) (7940656#64) (toBytesLE (0#64) 8))
        (g.rsp - 8 - 8) (toBytesLE g.rbp 8)) (g.rsp - 8 - 8 - 8) (toBytesLE g.rbx 8)) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hst ⊢
  obtain ⟨s1, s2, s3⟩ := push3 hst
  wpx [W_0, o0, Op.lda, Op.stia, BitVec.and_self, hmi]
  exact ⟨hfm, s1, hfh, s2, s3, fun h => absurd h (by decide)⟩

theorem vc_341 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} (hbp : g.rbp = 50#64)
    (hhk : rdq(V, 7940656#64) = 0#64) (hfh : ∀ i < 8, Foot F.data (Addr.add (7940656#64) i)) :
    W_341 fb F Wl (fun j' g' _ V' => j' = 68 ∧ g' = { g with rax := 64#64, rbx := 2#64 } ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hbp ⊢
  subst hbp
  have m50 : (50#64 : BitVec 64).msb = false := by decide
  wpx [W_341, W_47, W_56, W_192, o16, o1, o2, o10, Op.lda, Op.shr64, m50, hhk, BitVec.and_self,
    BitVec.reduceAdd, BitVec.reduceAnd, BitVec.reduceSetWidth, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft,
    BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceBEq, BitVec.reduceEq, BitVec.reduceToNat,
    BitVec.reduceSub, BitVec.reduceMul, BitVec.reduceLT, BitVec.reduceULT, BitVec.reduceOr, BitVec.reduceXOr,
    BitVec.reduceNot,
    Nat.reduceAdd, Nat.reduceLeDiff, Nat.reduceLT, decide_false, decide_true, Bool.or_false, Bool.false_or,
    Bool.not_false, Bool.not_true, Bool.false_eq_true, false_imp_iff, true_imp_iff, Bool.or_self, Bool.true_or,
    Bool.or_true, false_implies, true_implies, and_true, true_and, reduceIte, or_true, true_or, or_false, false_or,
    ne_eq, Nat.reduceEqDiff, not_false_eq_true, ofBytesLE_toBytesLE, Bool.true_eq_false, BitVec.xor_self]
  exact ⟨hfh, fun _ _ => trivial⟩

theorem vc_68 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (htc : rdq(V, fb + 18446744073709551576#64) = 0#64)
    (hsd : ofBytesLE 8 ((byteAddrs (fb + 18446744073709551584#64) 1).map V) = 0#8)
    (hft : ∀ i < 8, Foot F.data (Addr.add (fb + 18446744073709551576#64) i))
    (hfs : ∀ i < 1, Foot F.data (Addr.add (fb + 18446744073709551584#64) i)) :
    W_68 fb F Wl (fun j' g' _ V' => j' = 231 ∧ g' = { g with rax := 0#64 } ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_68, W_216, o3, o11, Op.ldf, Op.cmpmif, htc, hsd, BitVec.and_self,
    BitVec.reduceAdd, BitVec.reduceAnd, BitVec.reduceSetWidth, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft,
    BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceBEq, BitVec.reduceEq, BitVec.reduceToNat,
    BitVec.reduceSub, BitVec.reduceMul, BitVec.reduceLT, BitVec.reduceULT, BitVec.reduceOr, BitVec.reduceXOr,
    BitVec.reduceNot,
    Nat.reduceAdd, Nat.reduceLeDiff, Nat.reduceLT, decide_false, decide_true, Bool.or_false, Bool.false_or,
    Bool.not_false, Bool.not_true, Bool.false_eq_true, false_imp_iff, true_imp_iff, Bool.or_self, Bool.true_or,
    Bool.or_true, false_implies, true_implies, and_true, true_and, reduceIte, or_true, true_or, or_false, false_or,
    ne_eq, Nat.reduceEqDiff, not_false_eq_true, ofBytesLE_toBytesLE, Bool.true_eq_false, BitVec.xor_self]
  exact ⟨hft, hfs⟩

theorem vc_236 {fb C : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} (hbx : g.rbx = 2#64)
    (htb : rdq(V, 7940592#64) = 64#64) (htc : rdq(V, fb + 18446744073709551576#64) = C) (hC : C ≠ 0#64)
    (hn : ofBytesLE 16 ((byteAddrs (C + 4#64) 2).map V) = 0#16)
    (hfb : ∀ i < 8, Foot F.data (Addr.add (7940592#64) i))
    (hft : ∀ i < 8, Foot F.data (Addr.add (fb + 18446744073709551576#64) i))
    (hfn : ∀ i < 2, Foot F.data (Addr.add (C + 4#64) i)) :
    W_236 fb F Wl (fun j' g' _ V' => j' = 99 ∧ g' = { g with rax := C, rcx := C + 4#64, rdx := 0#64 } ∧ V' = V)
      g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hbx ⊢
  subst hbx
  have hC' : (C == 0) = false := beq_eq_false_iff_ne.2 hC
  have e4 : C + 2#64 * 2#64 = C + 4#64 := rfl
  wpx [W_236, W_249, W_267, W_272, o12, o13, o14, o15, Op.cmpmra, Op.ldf, Op.ldzx, htb, htc, hC', e4, hn, BitVec.and_self,
    BitVec.reduceAdd, BitVec.reduceAnd, BitVec.reduceSetWidth, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft,
    BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceBEq, BitVec.reduceEq, BitVec.reduceToNat,
    BitVec.reduceSub, BitVec.reduceMul, BitVec.reduceLT, BitVec.reduceULT, BitVec.reduceOr, BitVec.reduceXOr,
    BitVec.reduceNot,
    Nat.reduceAdd, Nat.reduceLeDiff, Nat.reduceLT, decide_false, decide_true, Bool.or_false, Bool.false_or,
    Bool.not_false, Bool.not_true, Bool.false_eq_true, false_imp_iff, true_imp_iff, Bool.or_self, Bool.true_or,
    Bool.or_true, false_implies, true_implies, and_true, true_and, reduceIte, or_true, true_or, or_false, false_or,
    ne_eq, Nat.reduceEqDiff, not_false_eq_true, ofBytesLE_toBytesLE, Bool.true_eq_false, BitVec.xor_self]
  exact ⟨hfb, hft, hfn⟩

theorem vc_99 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (h1 : rdd(V, fb + 24#64) = 0#32) (hf1 : ∀ i < 4, Foot F.data (Addr.add (fb + 24#64) i)) :
    W_99 fb F Wl (fun j' g' _ V' => j' = 125 ∧ g' = { g with rax := 0#64, rsi := g.rbp, rdi := 7940672#64 } ∧
      V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_99, W_115, o4, o5, Op.ldf, h1, BitVec.and_self,
    BitVec.reduceAdd, BitVec.reduceAnd, BitVec.reduceSetWidth, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft,
    BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceBEq, BitVec.reduceEq, BitVec.reduceToNat,
    BitVec.reduceSub, BitVec.reduceMul, BitVec.reduceLT, BitVec.reduceULT, BitVec.reduceOr, BitVec.reduceXOr,
    BitVec.reduceNot,
    Nat.reduceAdd, Nat.reduceLeDiff, Nat.reduceLT, decide_false, decide_true, Bool.or_false, Bool.false_or,
    Bool.not_false, Bool.not_true, Bool.false_eq_true, false_imp_iff, true_imp_iff, Bool.or_self, Bool.true_or,
    Bool.or_true, false_implies, true_implies, and_true, true_and, reduceIte, or_true, true_or, or_false, false_or,
    ne_eq, Nat.reduceEqDiff, not_false_eq_true, ofBytesLE_toBytesLE, Bool.true_eq_false, BitVec.xor_self]
  exact hf1

theorem vc_130 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} (hax : g.rax ≠ 0#64)
    (hsz : rdq(V, g.rax + 18446744073709551608#64) = 65#64)
    (hfz : ∀ i < 8, Foot F.data (Addr.add (g.rax + 18446744073709551608#64) i)) :
    W_130 fb F Wl (fun j' g' _ V' => j' = 180 ∧ g' = { g with rax := 65#64, r8 := g.rax } ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hax hsz hfz ⊢
  have hax' : (rax == 0) = false := beq_eq_false_iff_ne.2 hax
  wpx [W_130, W_142, W_150, o6, o7, o8, hax', hsz, BitVec.and_self,
    BitVec.reduceAdd, BitVec.reduceAnd, BitVec.reduceSetWidth, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft,
    BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceBEq, BitVec.reduceEq, BitVec.reduceToNat,
    BitVec.reduceSub, BitVec.reduceMul, BitVec.reduceLT, BitVec.reduceULT, BitVec.reduceOr, BitVec.reduceXOr,
    BitVec.reduceNot,
    Nat.reduceAdd, Nat.reduceLeDiff, Nat.reduceLT, decide_false, decide_true, Bool.or_false, Bool.false_or,
    Bool.not_false, Bool.not_true, Bool.false_eq_true, false_imp_iff, true_imp_iff, Bool.or_self, Bool.true_or,
    Bool.or_true, false_implies, true_implies, and_true, true_and, reduceIte, or_true, true_or, or_false, false_or,
    ne_eq, Nat.reduceEqDiff, not_false_eq_true, ofBytesLE_toBytesLE, Bool.true_eq_false, BitVec.xor_self]
  exact hfz

theorem vc_180 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (hst : ∀ i < 24, Foot F.data (Addr.add g.rsp i)) :
    W_180 fb F Wl (fun j' g' _ V' => j' = 187 ∧ V' = V ∧ g'.rax = g.r8 ∧ g'.rsp = g.rsp + 8 + 8 + 8 ∧
      g'.rbx = rdq(V, g.rsp) ∧ g'.rbp = rdq(V, g.rsp + 8) ∧ g'.r12 = rdq(V, g.rsp + 8 + 8)) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hst
  wpx [W_180, o9]
  refine ⟨fun i hi => hst i (by omega), fun i hi => ?_, fun i hi => ?_⟩
  · have e : Addr.add rsp (8 + i) = Addr.add (rsp + 8) i := by simp only [Addr.add]; bv_omega
    exact e ▸ hst _ (by omega)
  · have e : Addr.add rsp (16 + i) = Addr.add (rsp + 8 + 8) i := by simp only [Addr.add]; bv_omega
    exact e ▸ hst _ (by omega)

end FV7z.Mhi
