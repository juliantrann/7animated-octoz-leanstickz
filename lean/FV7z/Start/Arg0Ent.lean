import FV7z.Start.ArgEnt
/-!
# `ha0`, `hnz`, `nfit`, `nnz`, `nz` of `lif_ok` (PLAN.md G3, startup)

The pointer `argv[0]` at `argv` and the string it points to lie above `__libc_start_main`'s frame, the TLS block
and `lif_ok`'s stack, so in `lif_ok`'s bytes they are the launch bytes (`lif_hi`, `lif_rdq_hi`), where
`StackAt.arg0` gives them.

- `ent_arg0`: from the pointer at `y` and the string at `S` in the launch bytes, the same in `lif_ok`'s bytes, with
  `S ≠ 0` and no 0 in the string before its end.
-/
namespace FV7z.Start
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn

/-- `argv[0]` in `lif_ok`'s bytes: the pointer `S` at `y`, the `n` bytes of the string there without a 0, and its
0. -/
theorem ent_arg0 {K : Ctx} {W V : Addr → Byte} {b : Addr} {ver : BitVec 32} {D : Addr → Prop} {g : Gprs}
    {ra ra₀ : BitVec 64} (hM : MB K V) (hb : 0x7a9000 ≤ b.toNat) (hb' : b.toNat + 8192 ≤ 2 ^ 63)
    (hW : PtrW K W V b ver D) {y : Addr} {S n : Nat} {s : List Byte} (hy : y.toNat + 8 ≤ 2 ^ 64)
    (hbp : K.bp.toNat + 376 ≤ y.toNat) (htl : b.toNat + 8192 ≤ y.toNat) (hr : g.rsp.toNat + 8 ≤ y.toNat)
    (hr0 : 32 ≤ g.rsp.toNat) (hDy : ∀ i < 8, D (Addr.add y i)) (hS0 : 0 < S) (hSn : S + n < 2 ^ 64)
    (hbS : K.bp.toNat + 376 ≤ S) (htS : b.toNat + 8192 ≤ S) (hrS : g.rsp.toNat + 8 ≤ S)
    (hDS : ∀ k ≤ n, D (BitVec.ofNat 64 (S + k))) (hV : rdq(K.V0, y) = BitVec.ofNat 64 S)
    (hVs : ∀ k ≤ n, K.V0 (BitVec.ofNat 64 (S + k)) = (s ++ [0]).getD k 0) (hn : s.length = n)
    (hs : ∀ k < n, s.getD k 0 ≠ 0) :
    rdq(Vst (Lif.LifMem (Vst W g.rsp (toBytesLE ra₀ 8)) g) (g.rsp - 32#64) (toBytesLE ra 8), y) =
        BitVec.ofNat 64 S ∧ BitVec.ofNat 64 S ≠ 0#64 ∧ (BitVec.ofNat 64 S).toNat + n < 2 ^ 64 ∧
      (∀ k < n, Vst (Lif.LifMem (Vst W g.rsp (toBytesLE ra₀ 8)) g) (g.rsp - 32#64) (toBytesLE ra 8)
        (Addr.add (BitVec.ofNat 64 S) k) ≠ 0) ∧
      Vst (Lif.LifMem (Vst W g.rsp (toBytesLE ra₀ 8)) g) (g.rsp - 32#64) (toBytesLE ra 8)
        (Addr.add (BitVec.ofNat 64 S) n) = 0 := by
  have ht0 : (BitVec.ofNat 64 S).toNat = S := by
    rw [BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (by omega)
  have ht : ∀ k ≤ n, (BitVec.ofNat 64 (S + k)).toNat = S + k := fun k hk => by
    rw [BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (by omega)
  have e : ∀ k ≤ n, Vst (Lif.LifMem (Vst W g.rsp (toBytesLE ra₀ 8)) g) (g.rsp - 32#64) (toBytesLE ra 8)
      (BitVec.ofNat 64 (S + k)) = (s ++ [0]).getD k 0 := fun k hk => by
    have t := ht k hk
    rw [lif_hi (a := BitVec.ofNat 64 (S + k)) hM hb hb' hW (by rw [t]; omega) (by rw [t]; omega) (by rw [t]; omega)
      hr0 (hDS k hk), hVs k hk]
  refine ⟨(lif_rdq_hi hM hb hb' hW hy hbp htl hr hr0 hDy).trans hV, fun h => ?_, by rw [ht0]; exact hSn,
    fun k hk => ?_, ?_⟩
  · have := congrArg BitVec.toNat h
    rw [ht0] at this
    have h0 : S = 0 := this.trans rfl
    omega
  · rw [add_ofNat, e k (by omega), getD_in _ _ _ (by omega)]
    exact hs k hk
  · rw [add_ofNat, e n (Nat.le_refl _), ← hn, List.getD_eq_getElem?_getD,
      List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
    rfl

end FV7z.Start
