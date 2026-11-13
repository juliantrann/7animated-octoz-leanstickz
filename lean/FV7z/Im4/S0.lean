import FV7z.Im4.Cuts
import FV7z.Im2.HeadN
/-!
# `_int_malloc` from the entry to 1115 for a smallbin size `16 k`: the statement (PLAN.md G3, `malloc`)

`P0 k`: `vc_0m` (`Im4/Holds.lean`) with the size `16 k` (`clsM`), proved for `9 ≤ k ≤ 36` (`Im4/H0a.lean`) and
`37 ≤ k ≤ 63` (`Im4/H0b.lean`), two files built side by side (the 55 sizes in one proof ran out of memory).
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn FV7z.Start
open FV7z.Im2 (G1n V1n)
namespace FV7z.Im4

/-- From the entry to 1115 for `nb = 16 k`: the smallbin of `nb` read, empty. -/
def P0 (F : Footprint) (Wl : List Rgn) (k : Nat) : Prop :=
  ∀ {fb S n : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte},
    g.rsp = S + 184#64 → g.rsi = n → g.rdi = 7940672#64 →
    n.msb = false → decide ((n + 23#64).toNat < 31) = false → decide (n + 23#64 = 31#64) = false →
    n + 23#64 &&& 18446744073709551600#64 = BitVec.ofNat 64 (16 * k) →
    S.toNat + 256 < 2 ^ 64 → 8029888 ≤ S.toNat → (fb + 18446744073709551576#64).toNat + 8 ≤ S.toNat →
    rdq(V, 8013224#64) = 128#64 →
    rdq(V, BitVec.ofNat 64 (7940776 + 16 * k)) = BitVec.ofNat 64 (7940752 + 16 * k) →
    rdq(V, fb + 18446744073709551576#64) ≠ 0#64 → rdq(V, 7940592#64) = 64#64 →
    (∀ a : Addr, 7940480 ≤ a.toNat → a.toNat < 7943136 → Foot F.data a) →
    (∀ i < 8, Foot F.data (Addr.add (8013224#64) i)) →
    (∀ i < 8, Foot F.data (Addr.add (fb + 18446744073709551576#64) i)) →
    (∀ i < 184, Foot Wl (Addr.add S i)) →
    W_0 fb F Wl (fun j' g' _ V' => j' = 1115 ∧ g' = G1n S g n (BitVec.ofNat 64 (16 * k)) ∧
      V' = V1n S g (BitVec.ofNat 64 (16 * k)) V) g f V

end FV7z.Im4
