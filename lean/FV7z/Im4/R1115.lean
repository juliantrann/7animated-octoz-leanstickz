import FV7z.Im4.R1115a
import FV7z.Im4.R1115b
/-!
# `_int_malloc` from 1115 to 2549 for every chunk size `16 k`, `2 ≤ k ≤ 63` (PLAN.md G3, `malloc`)

`vc_1115g`: `vc_1115a` (`k ≤ 32`, the fastbin sizes `k ≤ 8` with them), `vc_1115b` above.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn FV7z.Start
open FV7z.Im2 (G1n V1n V2n W_1115)
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
    W_1115 fb F Wl (fun j' g' _ V' => j' = 2549 ∧ g'.rbx = 7940672#64 ∧ g'.r13 = nb ∧ g'.rsp = S ∧
      V' = V2n S g n nb V) (G1n S g n nb) f (V1n S g nb V) := by
  obtain ⟨k, hk1, hk2, rfl⟩ := hnb
  by_cases h32 : k ≤ 32
  · exact vc_1115a k hk1 h32 hS hlo hun hm0 hm1 hm2 hm3 hW hsw hsd
  · exact vc_1115b k (by omega) hk2 hS hlo hun hm0 hm1 hm2 hm3 hW hsw hsd

end FV7z.Im4
