import FV7z.Ctor.AtCtor
import FV7z.Ctor.BlkRet
/-!
# Constructors that store to fixed bytes (PLAN.md §M, constructors)

A constructor that calls nothing and stores to a few fixed places takes the bytes `W` to `st W`; its `spec` is
`stSpec st V wr`: over its stores `wr` the bytes are those of `st V`.

- `stSpec`, `stSpec_dep`: that spec, and that it reads only `wr`.
- `vin`: the bytes a store at a fixed address leaves do not depend on the bytes under it.
- `jg_st`: `Jg` goes from `m` to `m + 1` through `st` when `st` keeps the bytes outside `wr`, its bytes in `wr`
  depend only on the bytes of `rd`, `rd` holds bytes `Jc` keeps as `V`'s, and `wr` and `rd` are apart from the
  stores before.
-/
namespace FV7z.Ctor
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn FV7z.Start

/-- The spec of a constructor whose stores `st` leave over `wr` the bytes of `st V`. -/
def stSpec (st : (Addr → Byte) → Addr → Byte) (V : Addr → Byte) (wr : List (Nat × Nat)) : CSpec :=
  ⟨wr, fun W => ∀ a : Addr, InR wr a.toNat → W a = st V a⟩

theorem stSpec_dep (st : (Addr → Byte) → Addr → Byte) (V : Addr → Byte) (wr : List (Nat × Nat)) :
    (stSpec st V wr).Dep :=
  fun _ _ h hp a ha => (h a ha).trans (hp a ha)

/-- A store at a fixed address leaves the same bytes there whatever was under it. -/
theorem vin {W T : Addr → Byte} {x n w : Nat} {v : BitVec w} {a : Addr} (hx : x + n < 2 ^ 64)
    (h1 : x ≤ a.toNat) (h2 : a.toNat < x + n) :
    Vst W (BitVec.ofNat 64 x) (toBytesLE v n) a = Vst T (BitVec.ofNat 64 x) (toBytesLE v n) a := by
  have e : (BitVec.ofNat 64 x).toNat = x := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have ha := a.isLt
  have ea : a = Addr.add (BitVec.ofNat 64 x) (a.toNat - x) := by
    apply BitVec.eq_of_toNat_eq
    simp only [Addr.add, BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  have hj : a.toNat - x < (toBytesLE v n).length := by rw [toBytesLE_length]; omega
  have hf : (BitVec.ofNat 64 x).toNat + (toBytesLE v n).length ≤ 2 ^ 64 := by rw [toBytesLE_length, e]; omega
  rw [ea, CpuFeat.Vst_at _ W _ hj hf, CpuFeat.Vst_at _ T _ hj hf]

/-- `Jg` from `m` to `m + 1` through `st`, for `spec m = stSpec st V wr`: `st` keeps the bytes outside `wr`
(`hout`), its bytes in `wr` are `st V`'s when the bytes of `rd` are `V`'s (`hst`), `rd` lies outside the stack,
`Pre` and the tables (`hR`), and `wr` and `rd` are apart from the stores before (`hXw`, `hXr`). -/
theorem jg_st {V W : Addr → Byte} {sp m : Nat} {spec : Nat → CSpec} {G : Nat → (Addr → Byte) → Prop}
    {st : (Addr → Byte) → Addr → Byte} {wr rd : List (Nat × Nat)}
    (hm : 3 ≤ m) (hc : calls m = []) (hspec : spec m = stSpec st V wr) (hD : ∀ k, (spec k).Dep)
    (hT : ∀ x ∈ wr, ∀ y ∈ tabs, x.2 ≤ y.1 ∨ y.2 ≤ x.1)
    (hXw : ∀ k, 3 ≤ k → k < m → ∀ x ∈ (spec k).wr, ∀ y ∈ wr, x.2 ≤ y.1 ∨ y.2 ≤ x.1)
    (hXr : ∀ k, 3 ≤ k → k < m → ∀ x ∈ (spec k).wr, ∀ y ∈ rd, x.2 ≤ y.1 ∨ y.2 ≤ x.1)
    (hR : ∀ n, InR rd n → ¬ (sp - 136 ≤ n ∧ n < sp + 8) ∧ ¬ Pre n ∧ ¬ (7981024 ≤ n ∧ n < 7991300))
    (hst : ∀ W, (∀ a : Addr, InR rd a.toNat → W a = V a) → ∀ a : Addr, InR wr a.toNat → st W a = st V a)
    (hout : ∀ W (a : Addr), ¬ InR wr a.toNat → st W a = W a)
    (hG : G m W → G (m + 1) (st W)) (hJ : Jg V sp spec G m W) : Jg V sp spec G (m + 1) (st W) := by
  obtain ⟨hJc, hG'⟩ := hJ
  have hrd : ∀ a : Addr, InR rd a.toNat → W a = V a := fun a ha =>
    hJc.2.1 a (hR _ ha).1 (hR _ ha).2.1 (hR _ ha).2.2 fun k hk hkm hin => InR_sep hin (hXr k hk hkm) ha
  refine ⟨Jc_st hm hc hD ?_ (fun k hk hkm => ?_) hJc (fun a ha => hout W a ?_) ?_, hG hG'⟩
  · rw [hspec]
    exact hT
  · rw [hspec]
    exact hXw k hk hkm
  · rw [hspec] at ha
    exact ha
  · rw [hspec]
    intro a ha
    exact hst W hrd a ha

end FV7z.Ctor
