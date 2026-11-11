import FV7z.Ndi.Cuts
import FV7z.Sga.Holds
/-!
# `_dl_non_dynamic_init`: memory lemmas for its conditions (PLAN.md G3, startup)

The function reads and writes global variables at addresses that are numbers. `rq` moves a read past a store apart
from it (`simp (disch := decide) only [rq]`); `gf` gives the footprint of a variable from that of the data segment.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
open FV7z.Sga (vo vr vs)
namespace FV7z.Ndi

/-- Bytes through a store apart from them, both at addresses that are numbers (`simp (disch := decide)`). -/
theorem rq {V : Addr → Byte} {a x : Addr} {w n m : Nat} {v : BitVec w}
    (h : a.toNat + n ≤ 2 ^ 64 ∧ x.toNat + m ≤ 2 ^ 64 ∧ (a.toNat + n ≤ x.toNat ∨ x.toNat + m ≤ a.toNat)) :
    List.map (Vst V a (toBytesLE v n)) (byteAddrs x m) = List.map V (byteAddrs x m) :=
  vr (toBytesLE_length _ _) h.1 h.2.1 h.2.2

/-- The bytes of a region inside the data segment (`0x777000` to `0x7a9000`). -/
theorem gf {P : Addr → Prop} (h : ∀ x : Addr, 7827456 ≤ x.toNat → x.toNat < 8032256 → P x) (a : Addr) (n : Nat)
    (hd : 7827456 ≤ a.toNat ∧ a.toNat + n ≤ 8032256) : ∀ i < n, P (Addr.add a i) := fun i hi =>
  h _ (by rw [toNat_add_of_fits hi (by omega)]; omega) (by rw [toNat_add_of_fits hi (by omega)]; omega)

theorem s16 (x : BitVec 64) : x - 8 - 8 = x - 16#64 := by bv_omega
theorem s24 (x : BitVec 64) : x - 16#64 - 8 = x - 24#64 := by bv_omega
theorem s32 (x : BitVec 64) : x - 24#64 - 8 = x - 32#64 := by bv_omega
theorem s40 (x : BitVec 64) : x - 32#64 - 8 = x - 40#64 := by bv_omega
theorem s120 (x : BitVec 64) : x - 40#64 - 80#64 = x - 120#64 := by bv_omega

end FV7z.Ndi
