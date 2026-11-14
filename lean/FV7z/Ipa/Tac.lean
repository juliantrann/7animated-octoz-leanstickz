import FV7z.Ipa.Cuts
import FV7z.Hwc.Vc
/-!
# Tactics for the pieces of `_dl_init_paths` (PLAN.md G3, startup)

The side conditions of the addresses (`ipd`; `ifd` with the slots of the frame first made `r.toNat - c`, from
`hr0 : 96 ≤ r.toNat` in the context, so that `omega` sees no `% 2 ^ 64` of the frame), the loads through stores
(`ipeel`, `ipeelx`, `iself`), the bytes outside stores (`iout`), the goals of a piece (`icl`), regions (`ireg`).
Each peel and each byte is one `rw` with its side conditions as goals inside `repeat`/`first`, so that a failing one
stops there: a failing discharger of `simp`, like a `by` inside a `rw`, only logs its error (a131).
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Ipa

/-- The side conditions of the addresses: sums made `toNat` sums, then `omega`. -/
macro "ipd" : tactic => `(tactic| ((try simp only [FV7z.toBytesLE_length, BitVec.toNat_add, BitVec.toNat_ofNat,
  BitVec.toNat_sub, Nat.reducePow, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul]) <;> omega))

/-- A slot of the frame below `r`. -/
theorem fo {r : Addr} (K c : Nat) (hK : K + c = 2 ^ 64) (h : c ≤ r.toNat) :
    (r + BitVec.ofNat 64 K).toNat = r.toNat - c := by
  have := r.isLt
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.reducePow] at hK this ⊢
  omega

theorem f8 {r : Addr} (h : 96 ≤ r.toNat) : (r + 18446744073709551608#64).toNat = r.toNat - 8 :=
  fo _ _ (by decide) (by omega)
theorem f16 {r : Addr} (h : 96 ≤ r.toNat) : (r + 18446744073709551600#64).toNat = r.toNat - 16 :=
  fo _ _ (by decide) (by omega)
theorem f24 {r : Addr} (h : 96 ≤ r.toNat) : (r + 18446744073709551592#64).toNat = r.toNat - 24 :=
  fo _ _ (by decide) (by omega)
theorem f32 {r : Addr} (h : 96 ≤ r.toNat) : (r + 18446744073709551584#64).toNat = r.toNat - 32 :=
  fo _ _ (by decide) (by omega)
theorem f40 {r : Addr} (h : 96 ≤ r.toNat) : (r + 18446744073709551576#64).toNat = r.toNat - 40 :=
  fo _ _ (by decide) (by omega)
theorem f48 {r : Addr} (h : 96 ≤ r.toNat) : (r + 18446744073709551568#64).toNat = r.toNat - 48 :=
  fo _ _ (by decide) (by omega)
theorem f56 {r : Addr} (h : 96 ≤ r.toNat) : (r + 18446744073709551560#64).toNat = r.toNat - 56 :=
  fo _ _ (by decide) (by omega)
theorem f64 {r : Addr} (h : 96 ≤ r.toNat) : (r + 18446744073709551552#64).toNat = r.toNat - 64 :=
  fo _ _ (by decide) (by omega)
theorem f72 {r : Addr} (h : 96 ≤ r.toNat) : (r + 18446744073709551544#64).toNat = r.toNat - 72 :=
  fo _ _ (by decide) (by omega)
theorem f80 {r : Addr} (h : 96 ≤ r.toNat) : (r + 18446744073709551536#64).toNat = r.toNat - 80 :=
  fo _ _ (by decide) (by omega)
theorem f88 {r : Addr} (h : 96 ≤ r.toNat) : (r + 18446744073709551528#64).toNat = r.toNat - 88 :=
  fo _ _ (by decide) (by omega)
theorem f96 {r : Addr} (h : 96 ≤ r.toNat) : (r + 18446744073709551520#64).toNat = r.toNat - 96 :=
  fo _ _ (by decide) (by omega)

set_option hygiene false in
/-- `ipd` with the slots of the frame below `r` (`hr0 : 96 ≤ r.toNat`) first made `r.toNat - c`. -/
macro "ifd" : tactic => `(tactic| ((try simp only [FV7z.toBytesLE_length, FV7z.Ipa.f8 hr0, FV7z.Ipa.f16 hr0,
  FV7z.Ipa.f24 hr0, FV7z.Ipa.f32 hr0, FV7z.Ipa.f40 hr0, FV7z.Ipa.f48 hr0, FV7z.Ipa.f56 hr0, FV7z.Ipa.f64 hr0,
  FV7z.Ipa.f72 hr0, FV7z.Ipa.f80 hr0, FV7z.Ipa.f88 hr0, FV7z.Ipa.f96 hr0]) <;> ipd))

/-- A load through the stores apart from it, down to the store it reads (or to the memory under them). -/
macro "ipeel" : tactic =>
  `(tactic| repeat (focus (rw [FV7z.Tun.rd_Vst _ _ _ _ _ ?_ ?_ ?_]; rotate_left; iterate 3 ifd)))

/-- `ipeel` for the loads at `x` only. -/
macro "ipeelx" x:term : tactic =>
  `(tactic| repeat (focus (rw [FV7z.Tun.rd_Vst _ _ _ $x _ ?_ ?_ ?_]; rotate_left; iterate 3 ifd)))

/-- A byte outside the stores. -/
macro "iout" : tactic =>
  `(tactic| repeat (focus (rw [FV7z.Tun.Vst_out _ _ _ _ ?_ ?_]; rotate_left; iterate 2 ifd)))

/-- The load of the 8 bytes a store stored. -/
macro "iself" : tactic => `(tactic| (rw [FV7z.Tun.rd_Vst_self _ _ _ (FV7z.toBytesLE_length _ _) (by ifd),
  FV7z.ofBytesLE_toBytesLE (n := 8) rfl]; try with_reducible rfl))

/-- The goals of a piece: the flags and the conjunctions split, each closed by a hypothesis, `rfl`, or a region. -/
macro "icl" : tactic =>
  `(tactic| (all_goals (repeat' (first | intro (_ : Rflags) | intro (_ : Bool) | intro (_ : _ = _) |
    apply And.intro)); all_goals first | with_reducible assumption | with_reducible rfl | exact True.intro | skip))

/-- `n` bytes from `x` inside a region. -/
theorem rgn {p : Addr → Prop} {lo hi : Nat} (hp : ∀ a : Addr, lo ≤ a.toNat → a.toNat < hi → p a) {x : Addr}
    {n : Nat} (h1 : lo ≤ x.toNat) (h2 : x.toNat + n ≤ hi) (h3 : x.toNat + n ≤ 2 ^ 64) : ∀ i < n, p (x.add i) :=
  fun i hi' => by
    have e := toNat_add_of_fits hi' h3
    exact hp _ (by rw [e]; omega) (by rw [e]; omega)

/-- A footprint goal of a region, its bounds by `ifd`. -/
macro "ireg" h:term : tactic => `(tactic| (refine FV7z.Ipa.rgn $h ?_ ?_ ?_ <;> ifd))

end FV7z.Ipa
