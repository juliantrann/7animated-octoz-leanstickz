import FV7z.Mnx.Pop
import FV7z.Ifr.Put
/-!
# The tcache after `tcache_get` (PLAN.md G3, `malloc`)

The three stores of `malloc`'s `tcache_get` (`Vget`, `Mnx.Pop`) on a heap with `TcSt V C bins`, the bin `ix` with
head `e`: the bins are `bpop bins ix` (bin `ix` without its head), when `e`'s `key` word `[e + 8, e + 16)` lies apart
from the tcache and from every entry's `next` word.

- `rd3`: a read apart from each of the three stores.
- `tc_get`: `TcSt V C bins` gives `TcSt (Vget …) C (bpop bins ix)`.
- `Vget_out`: a byte apart from the three stores.
- `pop_inv`: `GlB ∧ TcSt bins` before, `GlB ∧ TcSt (bpop bins ix)` after, with the bytes `GlB` reads apart from the
  tcache and from `e`'s `key`.
-/
open ZellicX86 Decode FV7z FV7z.Leaf
open FV7z.Tun (rd_Vst rd_Vst_self Vst_out)
open FV7z.Mal (GlB TcSt tcnt tent)
open FV7z.Ifr (tAdd ix2 ix8 a2 a8 toNat_C)
namespace FV7z.Mnx

/-- Bin `i` without its head, the others as they were. -/
def bpop (bins : Nat → List Addr) (i : Nat) : Nat → List Addr :=
  fun j => if j = i then (bins i).tail else bins j

/-- A read apart from each of the three stores. -/
theorem rd3 (U : Addr → Byte) (C ix e : Addr) (c : BitVec 16) (he : e.toNat + 16 ≤ 2 ^ 64)
    (hc : C.toNat + 640 ≤ 2 ^ 64) (hk : ix.toNat < 64) {x : Addr} {n : Nat} (hx : x.toNat + n ≤ 2 ^ 64)
    (h1 : x.toNat + n ≤ C.toNat + ix.toNat * 8 + 128 ∨ C.toNat + ix.toNat * 8 + 136 ≤ x.toNat)
    (h2 : x.toNat + n ≤ C.toNat + ix.toNat * 2 ∨ C.toNat + ix.toNat * 2 + 2 ≤ x.toNat)
    (h3 : x.toNat + n ≤ e.toNat + 8 ∨ e.toNat + 16 ≤ x.toNat) :
    List.map (Vget U C ix e c) (byteAddrs x n) = List.map U (byteAddrs x n) := by
  have e8' : (e + 8#64).toNat = e.toNat + 8 := tAdd e 8 (by omega)
  have e8 := ix8 hc hk
  have e2 := ix2 hc hk
  dsimp only [Vget]
  rw [rd_Vst, rd_Vst, rd_Vst]
  all_goals (try simp only [toBytesLE_length, e8', e8, e2])
  all_goals omega

/-- The tcache after `tcache_get` from bin `ix`, its head `e`: the count one less, the entry `e`'s `next`. -/
theorem tc_get {V : Addr → Byte} {C ix e : Addr} {bins : Nat → List Addr} (h : TcSt V C bins)
    (hc : C.toNat + 640 ≤ 2 ^ 64) (hk : ix.toNat < 64) (hb : (bins ix.toNat).head? = some e)
    (he : e.toNat + 16 ≤ 2 ^ 64) (eC : e.toNat + 16 ≤ C.toNat ∨ C.toNat + 640 ≤ e.toNat + 8)
    (dis : ∀ i < 64, ∀ x ∈ bins i, x.toNat + 8 ≤ 2 ^ 64 ∧ (x.toNat + 8 ≤ e.toNat + 8 ∨ e.toNat + 16 ≤ x.toNat) ∧
      (x.toNat + 8 ≤ C.toNat ∨ C.toNat + 640 ≤ x.toNat)) :
    TcSt (Vget V C ix e (ofBytesLE 16 (List.map V (byteAddrs (C + ix * 2#64) 2)))) C (bpop bins ix.toNat) := by
  have e8 := ix8 hc hk
  have e2 := ix2 hc hk
  intro j hj
  obtain ⟨h1, h2, h3⟩ := h j hj
  have ec := toNat_C (k := 2 * j) hc (by omega)
  have ee := toNat_C (k := 128 + 8 * j) hc (by omega)
  by_cases hji : j = ix.toNat
  · subst hji
    obtain ⟨rest, hr⟩ : ∃ rest, bins ix.toNat = e :: rest := by
      cases hl : bins ix.toNat with
      | nil => rw [hl] at hb; simp at hb
      | cons a t => rw [hl] at hb; simp only [List.head?_cons, Option.some.injEq] at hb; exact ⟨t, by rw [hb]⟩
    simp only [bpop, ↓reduceIte]
    refine ⟨?_, fun e' he' => ?_, fun k hk' => ?_⟩
    · -- the count
      dsimp only [tcnt]
      rw [a2 hc hk]
      dsimp only [Vget]
      rw [rd_Vst, rd_Vst_self _ _ _ (toBytesLE_length _ _) (by omega), ofBytesLE_toBytesLE (n := 2) rfl, cnt_dec]
      · dsimp only [tcnt] at h1
        rw [a2 hc hk] at h1
        rw [h1, hr, List.tail_cons, List.length_cons]
        apply BitVec.eq_of_toNat_eq
        simp only [BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
        omega
      all_goals (try simp only [toBytesLE_length, e2, tAdd e 8 (by omega)])
      all_goals omega
    · -- the head: `e`'s `next`
      rw [hr, List.tail_cons] at he'
      have hl : 1 < (bins ix.toNat).length := by
        rw [hr, List.length_cons]
        cases rest with
        | nil => simp at he'
        | cons _ _ => simp only [List.length_cons]; omega
      have hn := h3 0 hl
      have g0 : (bins ix.toNat)[0] = e := by simp only [hr, List.getElem_cons_zero]
      have g1 : (bins ix.toNat)[0 + 1] = e' := by
        cases rest with
        | nil => simp at he'
        | cons a t =>
          simp only [List.head?_cons, Option.some.injEq] at he'
          simp only [hr, List.getElem_cons_succ, List.getElem_cons_zero, he']
      rw [g0, g1] at hn
      dsimp only [tent]
      rw [a8 hc hk]
      dsimp only [Vget]
      rw [rd_Vst, rd_Vst, rd_Vst_self _ _ _ (toBytesLE_length _ _) (by omega), ofBytesLE_toBytesLE (n := 8) rfl, hn]
      all_goals (try simp only [toBytesLE_length, e2, e8, tAdd e 8 (by omega)])
      all_goals omega
    · -- the chain: the entries after the head, their words apart from the stores
      simp only [List.getElem_tail]
      have hk2 : k + 1 + 1 < (bins ix.toNat).length := by
        simp only [List.length_tail] at hk'; omega
      rw [← h3 (k + 1) hk2]
      obtain ⟨x8, d1, d2⟩ := dis _ hk _ (List.getElem_mem (by omega : k + 1 < (bins ix.toNat).length))
      exact congrArg (ofBytesLE 64) (rd3 V C ix e _ he hc hk x8 (by omega) (by omega) (by omega))
  · simp only [bpop, hji, ↓reduceIte]
    refine ⟨?_, fun e' he' => ?_, fun k hk' => ?_⟩
    · rw [← h1]
      exact congrArg (ofBytesLE 16) (rd3 V C ix e _ he hc hk (by omega) (by omega) (by omega) (by omega))
    · rw [← h2 e' he']
      exact congrArg (ofBytesLE 64) (rd3 V C ix e _ he hc hk (by omega) (by omega) (by omega) (by omega))
    · obtain ⟨x8, d1, d2⟩ := dis _ hj _ (List.getElem_mem (by omega : k < (bins j).length))
      rw [← h3 k hk']
      exact congrArg (ofBytesLE 64) (rd3 V C ix e _ he hc hk x8 (by omega) (by omega) (by omega))

/-- A byte apart from the three stores. -/
theorem Vget_out (U : Addr → Byte) (C ix e : Addr) (c : BitVec 16) (he : e.toNat + 16 ≤ 2 ^ 64)
    (hc : C.toNat + 640 ≤ 2 ^ 64) (hk : ix.toNat < 64) (a : Addr)
    (h1 : a.toNat < C.toNat ∨ C.toNat + 640 ≤ a.toNat) (h2 : a.toNat < e.toNat + 8 ∨ e.toNat + 16 ≤ a.toNat) :
    Vget U C ix e c a = U a := by
  have e8' : (e + 8#64).toNat = e.toNat + 8 := tAdd e 8 (by omega)
  have e8 := ix8 hc hk
  have e2 := ix2 hc hk
  dsimp only [Vget]
  rw [Vst_out, Vst_out, Vst_out]
  all_goals (try simp only [toBytesLE_length, e8', e8, e2])
  all_goals omega

/-- The heap after `tcache_get`: `GlB` kept, bin `ix` without its head `e`. -/
theorem pop_inv {F : Footprint} {Wl : List Rgn} {fb C ix e : Addr} {V : Addr → Byte} {bins : Nat → List Addr}
    (hg : GlB F Wl fb C V) (ht : TcSt V C bins) (hc : C.toNat + 640 ≤ 2 ^ 64) (hk : ix.toNat < 64)
    (hb : (bins ix.toNat).head? = some e) (he : e.toNat + 16 ≤ 2 ^ 64)
    (eC : e.toNat + 16 ≤ C.toNat ∨ C.toNat + 640 ≤ e.toNat + 8)
    (dis : ∀ i < 64, ∀ x ∈ bins i, x.toNat + 8 ≤ 2 ^ 64 ∧ (x.toNat + 8 ≤ e.toNat + 8 ∨ e.toNat + 16 ≤ x.toNat) ∧
      (x.toNat + 8 ≤ C.toNat ∨ C.toNat + 640 ≤ x.toNat))
    (f0 : 40 ≤ fb.toNat) (f1 : fb.toNat + 28 ≤ 2 ^ 64)
    (hG : ∀ a : Addr, Ifr.Gr fb a → (a.toNat < C.toNat ∨ C.toNat + 640 ≤ a.toNat) ∧
      (a.toNat < e.toNat + 8 ∨ e.toNat + 16 ≤ a.toNat)) :
    GlB F Wl fb C (Vget V C ix e (ofBytesLE 16 (List.map V (byteAddrs (C + ix * 2#64) 2)))) ∧
      TcSt (Vget V C ix e (ofBytesLE 16 (List.map V (byteAddrs (C + ix * 2#64) 2)))) C (bpop bins ix.toNat) :=
  ⟨Ifr.GlB.congr hg f0 f1 fun a ha => Vget_out V C ix e _ he hc hk a (hG a ha).1 (hG a ha).2,
    tc_get ht hc hk hb he eC dis⟩

end FV7z.Mnx
