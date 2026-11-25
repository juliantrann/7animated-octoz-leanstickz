import FV7z.Lemmas.SpCallK
import FV7z.Lemmas.BlkOps20
/-!
# `idiv` and `bsr` at a cut point (PLAN.md M, ctor 103)

`Seg.s_idiv64` and `Seg.s_bsr32` as `SpAt`s: the instruction's own condition (a positive divisor after `cqo`, a source
not 0) and `Q` after it, for any flags. glibc's `init_cacheinfo` divides by thread counts and takes `bsr` of them.
-/
namespace FV7z.Fn
open ZellicX86 Decode FV7z.Leaf

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle} {F : Footprint} {Wl : List Rgn}
  {e' : Addr} {code : List Byte}

/-- The registers after `idiv` by `d`: the quotient in `rax`, the remainder in `rdx`. -/
abbrev idivG (g : Gprs) (d : BitVec 64) : Gprs :=
  (g.set 0 (BitVec.ofInt 64 (g.rax.toInt.tdiv d.toInt))).set 2 (BitVec.ofInt 64 (g.rax.toInt.tmod d.toInt))

/-- `idiv r64` after `cqo`, at a cut point: the divisor positive, `Q` after it. -/
theorem SpAt.idiv64 (c : Seg prof F Wl L s₀ o) (hin : CodeIn L e' code) {j r len : Nat} (hj : j < code.length)
    (hd : Dec prof.feat code j (FV7z.mk .idiv 64 [gr 64 r] len)) :
    SpAt prof F Wl L s₀ o e' j fun Q g _ V =>
      g.rdx = (if g.rax.msb then BitVec.allOnes 64 else 0) ∧ (g.get (regOf r)).setWidth 64 ≠ 0 ∧
      ((g.get (regOf r)).setWidth 64).msb = false ∧
      ∀ fl, Q (j + len) (idivG g ((g.get (regOf r)).setWidth 64)) fl V := by
  refine ⟨?_⟩
  rintro gev gP gE X t V Q hK hA hrip ⟨h2, hne, hpos, hW⟩ k
  refine c.s_idiv64 hK hA hin hj hrip hd h2 hne hpos ?_
  rintro Y t' hKY hAY ⟨hrY, hg⟩
  exact k _ _ _ _ (hW Y.cpu.rflags) Y t' hKY hAY hrY hg rfl

/-- `bsr r32, q32` at a cut point: the source not 0, `Q` after it. -/
theorem SpAt.bsr32 (c : Seg prof F Wl L s₀ o) (hin : CodeIn L e' code) {j r q len : Nat} (hj : j < code.length)
    (hd : Dec prof.feat code j (FV7z.mk (.bit .bsr) 32 [gr 32 r, gr 32 q] len)) :
    SpAt prof F Wl L s₀ o e' j fun Q g _ V =>
      (g.get (regOf q)).setWidth 32 ≠ 0 ∧
      ∀ fl, Q (j + len) (wr g r (BitVec.ofNat 32 (highestSetBit ((g.get (regOf q)).setWidth 32)))) fl V := by
  refine ⟨?_⟩
  rintro gev gP gE X t V Q hK hA hrip ⟨hne, hW⟩ k
  refine c.s_bsr32 hK hA hin hj hrip hd hne ?_
  rintro Y t' hKY hAY ⟨hrY, hg⟩
  exact k _ _ _ _ (hW Y.cpu.rflags) Y t' hKY hAY hrY hg rfl

end FV7z.Fn
