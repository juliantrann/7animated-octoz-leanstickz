import FV7z.Im7.S
/-!
# `_int_malloc` from the entry to 512 for a largebin request, `nb` a variable (PLAN.md G3, `malloc`)

The way `0 → 9 → 304 → 320 → 340 → 352`, then by `nb`:
- `PaA`: `nb >> 6` above 48, `nb >> 9` at most 20 (482 → 512): the index `91 + (nb >> 9)` at `rsp + 0x28`.

The flags of the comparisons with `nb` are hypotheses in the form `simp` leaves them (`decide (x.toNat < c) = b`,
`decide (x = c#64) = b`); a jump taken on `CF ∨ ZF` gets `c || z = true` for the two.
-/
set_option Elab.async false
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn FV7z.Start
open FV7z.Imm (imm imm_at rd_off rd_off_self rd_below stk_f pu)
namespace FV7z.Im7

/-- From the entry to 512, `nb >> 6` above 48 and `nb >> 9` at most 20. -/
def PaA (F : Footprint) (Wl : List Rgn) : Prop :=
  ∀ {fb S n nb : Addr} {c1 z1 : Bool} {g : Gprs} {f : Rflags} {V : Addr → Byte},
    g.rsp = S + 184#64 → g.rsi = n → g.rdi = 7940672#64 →
    n.msb = false → decide ((n + 23#64).toNat < 31) = false → decide (n + 23#64 = 31#64) = false →
    n + 23#64 &&& 18446744073709551600#64 = nb →
    decide (nb.toNat < 128) = false → decide (nb = 128#64) = false →
    decide (nb.toNat < 1023) = false → decide (nb = 1023#64) = false →
    decide (nb.toNat < 786431) = true →
    decide ((nb >>> 6).toNat < 48) = false → decide (nb >>> 6 = 48#64) = false →
    decide ((nb >>> 9).toNat < 20) = c1 → decide (nb >>> 9 = 20#64) = z1 → (c1 || z1) = true →
    S.toNat + 256 < 2 ^ 64 → 8029888 ≤ S.toNat → rdq(V, 8013224#64) = 128#64 →
    (∀ i < 8, Foot F.data (Addr.add (8013224#64) i)) →
    (∀ i < 184, Foot Wl (Addr.add S i)) → (∀ i < 184, Foot F.data (Addr.add S i)) →
    W_0 fb F Wl (fun j g₁ _ V₁ => j = 512 ∧ g₁.rbx = 7940672#64 ∧ g₁.r13 = nb ∧ g₁.rsp = S ∧
      rdd(V₁, S + 40#64) = (nb >>> 9).setWidth 32 + 91#32 ∧ Im2.Fr S g V V₁) g f V

set_option maxHeartbeats 400000000 in
set_option maxRecDepth 100000 in
theorem vcA {F : Footprint} {Wl : List Rgn} : PaA F Wl := by
  intro fb S n nb c1 z1 g f V hrsp hsi hdi m d1 d2 e c320 z320 c340 z340 c398 c476 z476 c486 z486 h486 hS hlo hgm
    hgf hsw hsd
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hrsp hsi hdi ⊢
  subst hrsp hsi hdi
  obtain ⟨p1, p2, p3, p4, p5, p6, p7⟩ := pu S
  have q1 := rd_below (S := S) (x := 8013224#64) (n := 8) (hx := by rw [BitVec.toNat_ofNat]; omega) (hS := hS)
  have hS' : S.toNat + 256 < 18446744073709551616 := hS
  lwp [W_0, W_9, W_304, W_320, W_340, W_352, W_482, o0, o1, o2, o3, o4, o5, o6,
    p1, p2, p3, p4, p5, p6, p7, q1, hS, hS', m, d1, d2, e, hgm, c320, z320, c340, z340, c398, c476, z476, c486,
    z486, h486, BitVec.xor_self]
  lc7 [p1, p2, p3, p4, p5, p6, p7, q1, hS, hS', m, d1, d2, e, hgm, c320, z320, c340, z340, c398, c476, z476, c486,
    z486, h486, BitVec.xor_self]

end FV7z.Im7
