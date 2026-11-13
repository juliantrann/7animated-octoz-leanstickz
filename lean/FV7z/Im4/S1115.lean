import FV7z.Im2.HeadN
/-!
# `_int_malloc` from 1115 to 2549 for a smallbin size `16 k`: the statement (PLAN.md G3, `malloc`)

`P1115 k`: from 1115 to 2549 with `nb = 16 k`, proved for `2 ≤ k ≤ 32` (`Im4/R1115a.lean`) and `33 ≤ k ≤ 63`
(`Im4/R1115b.lean`), two files built side by side: the unsorted bin empty, the binmap's blocks from that of the bin
`k + 1` (block 0 below 32, block 1 to 63, block 2 at 64) all 0, on to `use_top` at 2549. At 2549 `rax`, `rdx`, `rdi`
depend on the block the scan began at (2, 2, 0 for block 0; 3, 3, 1 for block 1; 4, 3, 2 for block 2): the post names
the registers the code from 2549 reads (`rbx` the arena, `r13` the size, `rsp`), not `Im2.G2n`.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn FV7z.Start
open FV7z.Im2 (G1n V1n V2n)
namespace FV7z.Im4

/-- From 1115 to 2549 for `nb = 16 k`. -/
def P1115 (F : Footprint) (Wl : List Rgn) (k : Nat) : Prop :=
  ∀ {fb S n : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte},
    S.toNat + 256 < 2 ^ 64 → 8029888 ≤ S.toNat → rdq(V, 7940792#64) = 7940768#64 →
    rdd(V, 7942816#64) = 0 → rdd(V, 7942820#64) = 0 → rdd(V, 7942824#64) = 0 → rdd(V, 7942828#64) = 0 →
    (∀ a : Addr, 7940480 ≤ a.toNat → a.toNat < 7943136 → Foot F.data a) →
    (∀ i < 184, Foot Wl (Addr.add S i)) → (∀ i < 184, Foot F.data (Addr.add S i)) →
    Im2.W_1115 fb F Wl (fun j' g' _ V' => j' = 2549 ∧ g'.rbx = 7940672#64 ∧
      g'.r13 = BitVec.ofNat 64 (16 * k) ∧ g'.rsp = S ∧ V' = V2n S g n (BitVec.ofNat 64 (16 * k)) V)
      (G1n S g n (BitVec.ofNat 64 (16 * k))) f
      (V1n S g (BitVec.ofNat 64 (16 * k)) V)

end FV7z.Im4
