import FV7z.Im2.HeadN
/-!
# `_int_malloc` from 1115 to 2549 for a smallbin size `16 k`: the statement (PLAN.md G3, `malloc`)

`P1115 k`: `Im2.vc_1115n` with `nb = 16 k`, proved for `9 ≤ k ≤ 35` (`Im4/R1115a.lean`) and `36 ≤ k ≤ 63`
(`Im4/R1115b.lean`), two files built side by side. From 1115 the way is that of the fastbin sizes: the unsorted bin
empty, the binmap's blocks from that of `k` (block 0 below 32, block 1 from 32) all 0, on to `use_top` at 2549.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn FV7z.Start
open FV7z.Im2 (G1n V1n G2n V2n)
namespace FV7z.Im4

/-- `Im2.vc_1115n` for `nb = 16 k`. -/
def P1115 (F : Footprint) (Wl : List Rgn) (k : Nat) : Prop :=
  ∀ {fb S n : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte},
    S.toNat + 256 < 2 ^ 64 → 8029888 ≤ S.toNat → rdq(V, 7940792#64) = 7940768#64 →
    rdd(V, 7942816#64) = 0 → rdd(V, 7942820#64) = 0 → rdd(V, 7942824#64) = 0 → rdd(V, 7942828#64) = 0 →
    (∀ a : Addr, 7940480 ≤ a.toNat → a.toNat < 7943136 → Foot F.data a) →
    (∀ i < 184, Foot Wl (Addr.add S i)) → (∀ i < 184, Foot F.data (Addr.add S i)) →
    Im2.W_1115 fb F Wl (fun j' g' _ V' => j' = 2549 ∧ g' = G2n S g n (BitVec.ofNat 64 (16 * k)) ∧
      V' = V2n S g n (BitVec.ofNat 64 (16 * k)) V) (G1n S g n (BitVec.ofNat 64 (16 * k))) f
      (V1n S g (BitVec.ofNat 64 (16 * k)) V)

end FV7z.Im4
