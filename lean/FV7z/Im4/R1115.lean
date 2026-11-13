import FV7z.Im4.R1115a
import FV7z.Im4.R1115b
/-!
# `_int_malloc` from 1115 to 2549 for every chunk size `16 k`, `2 ≤ k ≤ 63` (PLAN.md G3, `malloc`)

`vc_1115g`: `Im2.vc_1115n` for `k ≤ 8` (the fastbin sizes), `vc_1115a`, `vc_1115b` above.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn FV7z.Start
open FV7z.Im2 (G1n V1n G2n V2n W_1115)
namespace FV7z.Im4
variable {F : Footprint} {Wl : List Rgn}

theorem vc_1115g {fb S n nb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (hnb : ∃ k, 2 ≤ k ∧ k ≤ 63 ∧ nb = BitVec.ofNat 64 (16 * k))
    (hS : S.toNat + 256 < 2 ^ 64) (hlo : 8029888 ≤ S.toNat)
    (hun : rdq(V, 7940792#64) = 7940768#64)
    (hm0 : rdd(V, 7942816#64) = 0) (hm1 : rdd(V, 7942820#64) = 0) (hm2 : rdd(V, 7942824#64) = 0)
    (hm3 : rdd(V, 7942828#64) = 0)
    (hW : ∀ a : Addr, 7940480 ≤ a.toNat → a.toNat < 7943136 → Foot F.data a)
    (hsw : ∀ i < 184, Foot Wl (Addr.add S i)) (hsd : ∀ i < 184, Foot F.data (Addr.add S i)) :
    W_1115 fb F Wl (fun j' g' _ V' => j' = 2549 ∧ g' = G2n S g n nb ∧ V' = V2n S g n nb V) (G1n S g n nb) f
      (V1n S g nb V) := by
  obtain ⟨k, hk1, hk2, rfl⟩ := hnb
  by_cases h8 : k ≤ 8
  · refine Im2.vc_1115n ?_ hS hlo hun hm0 hm1 hm2 hm3 hW hsw hsd
    rcases (show k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 ∨ k = 8 by omega) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · by_cases h35 : k ≤ 35
    · exact vc_1115a k (by omega) h35 hS hlo hun hm0 hm1 hm2 hm3 hW hsw hsd
    · exact vc_1115b k (by omega) hk2 hS hlo hun hm0 hm1 hm2 hm3 hW hsw hsd

end FV7z.Im4
