import FV7z.Im4.H0a
import FV7z.Im4.H0b
/-!
# `_int_malloc`: from the entry to offset 1115, the second call, every request `121 ≤ n ≤ 1000` (PLAN.md G3, `malloc`)

The size `nb` (`request2size`) is `16 k`, `9 ≤ k ≤ 63`: a smallbin size above the fastbins. The way is
`0 → 304 → 340 → 848 → 86` (no fastbin read), the smallbin of `nb` empty (`984`), `1069 → 1099 → 1115`; the bytes and
registers at 1115 are those of the fastbin sizes (`Im2.V1n`, `Im2.G1n`). One `wpx` per `k` (`ksplit`), in
`Im4/H0a.lean` and `Im4/H0b.lean` (`P0`).

- `clsM`: `n + 23` above 31 and rounded to `16 k`, `9 ≤ k ≤ 63`.
- `vc_0m`: from the entry to 1115.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn FV7z.Start
open FV7z.Imm (imm imm_at rd_off rd_off_self rd_below stk_f pu)
open FV7z.Im2 (G1n V1n and_m16)
namespace FV7z.Im4
variable {F : Footprint} {Wl : List Rgn}

/-- A request `121 ≤ n ≤ 1000`: `n + 23` is above 31 and rounds to `16 k`, `9 ≤ k ≤ 63`. -/
theorem clsM {n : Addr} (h1 : 121 ≤ n.toNat) (h2 : n.toNat ≤ 1000) :
    n.msb = false ∧ decide ((n + 23#64).toNat < 31) = false ∧ decide (n + 23#64 = 31#64) = false ∧
    ∃ k, 9 ≤ k ∧ k ≤ 63 ∧ n + 23#64 &&& 18446744073709551600#64 = BitVec.ofNat 64 (16 * k) := by
  have e : (n + 23#64).toNat = n.toNat + 23 := by rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  refine ⟨?_, decide_eq_false (by omega), decide_eq_false (fun h => by rw [h, BitVec.toNat_ofNat] at e; omega),
    (n.toNat + 23) / 16, by omega, by omega, BitVec.eq_of_toNat_eq ?_⟩
  · rw [BitVec.msb_eq_decide]; exact decide_eq_false (by show ¬ (2 ^ 63 ≤ n.toNat); omega)
  · rw [and_m16, e, BitVec.toNat_ofNat]; omega

/-- `Im2.vc_0n` for the requests `121 ≤ n ≤ 1000`: the smallbin of `nb` read, empty. -/
theorem vc_0m {fb S n : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} (hrsp : g.rsp = S + 184#64)
    (hsi : g.rsi = n) (hdi : g.rdi = 7940672#64) (hn : 121 ≤ n.toNat) (hn' : n.toNat ≤ 1000)
    (hS : S.toNat + 256 < 2 ^ 64) (hlo : 8029888 ≤ S.toNat)
    (hfb : (fb + 18446744073709551576#64).toNat + 8 ≤ S.toNat)
    (hgm : rdq(V, 8013224#64) = 128#64)
    (hbk : ∀ i, 2 ≤ i → i ≤ 63 → rdq(V, BitVec.ofNat 64 (7940776 + 16 * i)) = BitVec.ofNat 64 (7940752 + 16 * i))
    (htc : rdq(V, fb + 18446744073709551576#64) ≠ 0#64) (htb : rdq(V, 7940592#64) = 64#64)
    (hW : ∀ a : Addr, 7940480 ≤ a.toNat → a.toNat < 7943136 → Foot F.data a)
    (hgf : ∀ i < 8, Foot F.data (Addr.add (8013224#64) i))
    (htf : ∀ i < 8, Foot F.data (Addr.add (fb + 18446744073709551576#64) i))
    (hsw : ∀ i < 184, Foot Wl (Addr.add S i)) :
    W_0 fb F Wl (fun j' g' _ V' => j' = 1115 ∧ g' = G1n S g n (n + 23#64 &&& 18446744073709551600#64) ∧
      V' = V1n S g (n + 23#64 &&& 18446744073709551600#64) V) g f V := by
  obtain ⟨m, d1, d2, k, hk1, hk2, e⟩ := clsM hn hn'
  rw [e]
  by_cases h36 : k ≤ 36
  · exact vc_0a k hk1 h36 hrsp hsi hdi m d1 d2 e hS hlo hfb hgm (hbk k (by omega) hk2) htc htb hW hgf htf hsw
  · exact vc_0b k (by omega) hk2 hrsp hsi hdi m d1 d2 e hS hlo hfb hgm (hbk k (by omega) hk2) htc htb hW hgf htf hsw

end FV7z.Im4
