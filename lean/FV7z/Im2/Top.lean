import FV7z.Im2.Head
import FV7z.Imm.Tail
/-!
# `_int_malloc`: from `use_top` to the `ret`, the second call (PLAN.md G3, `malloc`)

- `vc_2549`: from `use_top` with `av` the main arena, `nb` in `r13`, the top `T` with size word `szw`: when the size
  is not above `av->system_mem` and at least `nb + MINSIZE`, and `perturb_byte` is 0, the top is split: `av->top`
  becomes `T + nb`, the chunk's size word `nb | 1`, the rest's `(size - nb) | 1`; the pieces reach the `ret` with
  `T + 16` in `rax`, the frame given back.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn FV7z.Start
open FV7z.Raf (off_ft)
open FV7z.Tun (rd_Vst rd_Vst_self Vst_out)
open FV7z.Imm (imm imm_at pops)
namespace FV7z.Im2
variable {F : Footprint} {Wl : List Rgn}

/-- The three stores of the split of the top `T` (size word `szw`) for 64 bytes: `av->top`, the chunk's size word
and the rest's. -/
abbrev Vsp (T szw : Addr) (V : Addr → Byte) : Addr → Byte :=
  Vst (Vst (Vst V (7940768#64) (toBytesLE (T + 64#64) 8)) (T + 8#64) (toBytesLE (65#64) 8)) (T + 64#64 + 8#64)
    (toBytesLE ((szw &&& 18446744073709551608#64) - 64#64 ||| 1#64) 8)

/-- A read past the split's stores. -/
theorem Vsp_rd {T szw x : Addr} {n : Nat} (V : Addr → Byte) (hT : T.toNat + 80 < 2 ^ 64) (hx : x.toNat + n ≤ 2 ^ 64)
    (h1 : x.toNat + n ≤ 7940768 ∨ 7940776 ≤ x.toNat) (h2 : x.toNat + n ≤ T.toNat + 8 ∨ T.toNat + 80 ≤ x.toNat) :
    List.map (Vsp T szw V) (byteAddrs x n) = List.map V (byteAddrs x n) := by
  have e8 : (T + 8#64).toNat = T.toNat + 8 := by rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have e72 : (T + 64#64 + 8#64).toNat = T.toNat + 72 := by
    rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat]; omega
  have l : ∀ v : Addr, (toBytesLE v 8).length = 8 := fun v => toBytesLE_length _ _
  unfold Vsp
  rw [rd_Vst _ _ _ _ _ (by rw [l, e72]; omega) hx (by rw [l, e72]; omega),
    rd_Vst _ _ _ _ _ (by rw [l, e8]; omega) hx (by rw [l, e8]; omega),
    rd_Vst _ _ _ _ _ (by rw [l]; decide) hx (by rw [l]; simp only [BitVec.toNat_ofNat]; omega)]

set_option maxHeartbeats 1000000 in
theorem vc_2549 {fb T szw sm : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} (hbx : g.rbx = 7940672#64)
    (h13 : g.r13 = 64#64) (hT : 8029888 ≤ T.toNat) (hTS : T.toNat + 80 ≤ g.rsp.toNat)
    (hsp2 : g.rsp.toNat + 256 < 2 ^ 64)
    (hW : ∀ a : Addr, 7940480 ≤ a.toNat → a.toNat < 7943136 → Foot F.data a)
    (hWl : ∀ i < 8, Foot Wl (Addr.add (7940768#64) i))
    (htf : ∀ i < 8, Foot F.data (Addr.add (T + 8#64) i))
    (htw : ∀ i < 8, Foot Wl (Addr.add (T + 8#64) i)) (hrw : ∀ i < 8, Foot Wl (Addr.add (T + 64#64 + 8#64) i))
    (hsd : ∀ i < 184, Foot F.data (Addr.add g.rsp i))
    (hpb : ∀ i < 4, Foot F.data (Addr.add (8013220#64) i)) (hp0 : rdd(V, 8013220#64) = 0)
    (htop : rdq(V, 7940768#64) = T) (hsz : rdq(V, T + 8#64) = szw) (hsm : rdq(V, 7942856#64) = sm)
    (hle : (szw &&& 18446744073709551608#64).toNat ≤ sm.toNat) (hge : 96 ≤ (szw &&& 18446744073709551608#64).toNat) :
    W_2549 fb F Wl (fun j' g' _ V' => j' = 950 ∧ V' = Vsp T szw V ∧ g'.rax = T + 16#64 ∧
      g'.rsp = g.rsp + 184#64 ∧
      g'.rbx = rdq(V, g.rsp + 136#64) ∧ g'.rbp = rdq(V, g.rsp + 144#64) ∧ g'.r12 = rdq(V, g.rsp + 152#64) ∧
      g'.r13 = rdq(V, g.rsp + 160#64) ∧ g'.r14 = rdq(V, g.rsp + 168#64) ∧ g'.r15 = rdq(V, g.rsp + 176#64))
      g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hbx h13 hTS hsp2 hsd ⊢
  subst hbx h13
  have a1 : (7940672#64 + 96#64 : Addr) = 7940768#64 := by decide
  have a2 : (7940672#64 + 2184#64 : Addr) = 7942856#64 := by decide
  obtain ⟨b1, b2, b3, b4, b5, b6⟩ := pops rsp
  have a3 : T + 16#64 + 18446744073709551608#64 = T + 8#64 := by bv_omega
  have hT' : T.toNat + 80 < 2 ^ 64 := by omega
  have r0 : rdd(Vsp T szw V, 8013220#64) = 0 :=
    (congrArg (ofBytesLE 32) (Vsp_rd V hT' (by decide) (.inr (by decide)) (.inl (by simp; omega)))).trans hp0
  have rk : ∀ d, 136 ≤ d → d ≤ 176 → rdq(Vsp T szw V, rsp + BitVec.ofNat 64 d) = rdq(V, rsp + BitVec.ofNat 64 d) :=
    fun d h1 h2 => by
      have e : (rsp + BitVec.ofNat 64 d).toNat = rsp.toNat + d := by
        rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
      exact congrArg (ofBytesLE 64) (Vsp_rd V hT' (by omega) (.inr (by omega)) (.inr (by omega)))
  have t1 : decide (sm.toNat < (szw &&& 18446744073709551608#64).toNat) = false := decide_eq_false (by omega)
  have t2 : (decide (96 < (szw &&& 18446744073709551608#64).toNat) ||
      decide (96#64 = szw &&& 18446744073709551608#64)) = true := by
    rcases Nat.lt_or_eq_of_le hge with h | h
    · rw [decide_eq_true h]; rfl
    · have : (96#64 : BitVec 64) = szw &&& 18446744073709551608#64 := BitVec.eq_of_toNat_eq (by rw [← h]; rfl)
      rw [decide_eq_true this, Bool.or_true]
  wpx [W_2549, W_2574, W_3191, W_930, o22, o23, o24, o7, Op.cmpmr, Op.lda, Op.zxr, Op.setcc, Op.shl64, a1, a2, a3,
    htop, hsz, hsm, b1, b2, b3, b4, b5, b6, t1, t2, r0, Nat.reduceSub, Nat.reduceMul, BitVec.reduceNot,
    BitVec.ofBool_false, BitVec.ofBool_true,
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
    | with_reducible exact hWl
    | with_reducible exact htf
    | with_reducible exact htw
    | with_reducible exact hrw
    | with_reducible exact hpb
    | with_reducible exact D _ _ (by decide) (by decide)
    | exact off_ft hsd _ rfl (by decide)
    | exact rk _ (by decide) (by decide)

end FV7z.Im2
