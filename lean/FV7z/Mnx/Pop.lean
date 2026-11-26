import FV7z.Mnx.Holds
/-!
# `malloc` from a non-empty tcache bin (PLAN.md G3, `malloc`)

`__libc_malloc`'s `tcache_get` (`0x633270`, offset 272): the tcache `C` made, the bin `ix` (`rbx`, below
`mp_.tcache_bins` = 64) with a count `c ≠ 0`: the bin's entry `e` (`C + 128 + 8 ix`) taken, the entry set to `e`'s
`next` (its first word), the count `c - 1`, `e`'s `key` (`e + 8`) 0, then to 164 (the pops, `rax` the entry `r8`).
Beside `vc_52m` (the empty bin, to `_int_malloc`).

- `vc_52p`: from 52 to 164, the three stores (`Vget`).
- `sw16_32`, `cnt_dec`: the count's widths.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn FV7z.Start
namespace FV7z.Mnx
variable {F : Footprint} {Wl : List Rgn}

theorem sw16_32 (x : BitVec 16) : (x.setWidth 32).setWidth 16 = x := by
  apply BitVec.eq_of_toNat_eq
  have := x.isLt
  simp only [BitVec.toNat_setWidth, Nat.reducePow] at this ⊢
  omega

/-- The count stored back: one less. -/
theorem cnt_dec (c : BitVec 16) : (c.setWidth 32 - 1#32).setWidth 16 = c - 1#16 := by
  apply BitVec.eq_of_toNat_eq
  have := c.isLt
  simp only [BitVec.toNat_setWidth, BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod] at this ⊢
  omega

/-- The three stores of `tcache_get` for the bin `ix` of the tcache `C`, its entry `e`: the entry `e`'s `next`, the
count `c - 1` (as the code computes it), `e`'s `key` 0. -/
abbrev Vget (V : Addr → Byte) (C ix e : Addr) (c : BitVec 16) : Addr → Byte :=
  Vst (Vst (Vst V (C + ix * 8#64 + 128#64) (toBytesLE rdq(V, e) 8)) (C + ix * 2#64)
    (toBytesLE ((c.setWidth 32 - 1#32).setWidth 16) 2)) (e + 8#64) (toBytesLE 0#64 8)

/-- From 52 to 164: the tcache `C` there (`fs:-0x28`), the bin `ix` below `mp_.tcache_bins` with its count not 0:
`tcache_get`, `r8` the entry `e`. -/
theorem vc_52p {fb C ix e : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} (hbx : g.rbx = ix)
    (hk : ix.toNat < 64)
    (htb : rdq(V, 7940592#64) = 64#64) (htc : rdq(V, fb + 18446744073709551576#64) = C) (hC : C ≠ 0#64)
    (hcn : ofBytesLE 16 (List.map V (byteAddrs (C + ix * 2#64) 2)) ≠ 0)
    (he : rdq(V, C + ix * 8#64 + 128#64) = e)
    (hfb : ∀ i < 8, Foot F.data (Addr.add (7940592#64) i))
    (hft : ∀ i < 8, Foot F.data (Addr.add (fb + 18446744073709551576#64) i))
    (f1 : ∀ i < 2, Foot F.data (Addr.add (C + ix * 2#64) i))
    (f2 : ∀ i < 8, Foot F.data (Addr.add (C + ix * 8#64 + 128#64) i))
    (f3 : ∀ i < 8, Foot F.data (Addr.add e i))
    (w1 : ∀ i < 8, Foot Wl (Addr.add (C + ix * 8#64 + 128#64) i))
    (w2 : ∀ i < 2, Foot Wl (Addr.add (C + ix * 2#64) i))
    (w3 : ∀ i < 8, Foot Wl (Addr.add (e + 8#64) i)) :
    W_52 fb F Wl (fun j' g' _ V' => j' = 164 ∧ g'.rsp = g.rsp ∧ g'.rbx = g.rbx ∧ g'.rbp = g.rbp ∧
      g'.r12 = g.r12 ∧ g'.r13 = g.r13 ∧ g'.r14 = g.r14 ∧ g'.r15 = g.r15 ∧ g'.r8 = e ∧
      V' = Vget V C ix e (ofBytesLE 16 (List.map V (byteAddrs (C + ix * 2#64) 2)))) g f V := by
  have hC' : (C == 0) = false := beq_eq_false_iff_ne.2 hC
  have hz : (ofBytesLE 16 (List.map V (byteAddrs (C + ix * 2#64) 2)) == 0) = false := beq_eq_false_iff_ne.2 hcn
  have hk' : decide (ix.toNat < 64) = true := decide_eq_true hk
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hbx ⊢
  subst hbx
  wpx [W_52, W_70, W_256, W_272, o3, o4, o13, o14, Op.cmpma, Op.ldf, htb, htc, hC', he, hz, hk', sw16_32,
    BitVec.and_self, Bool.not_true, Bool.not_false, Bool.false_eq_true, Bool.true_eq_false, false_implies,
    eq_self_iff_true, implies_true]
  all_goals repeat' first
    | with_reducible assumption | with_reducible rfl | exact True.intro | apply And.intro | intro _

end FV7z.Mnx
