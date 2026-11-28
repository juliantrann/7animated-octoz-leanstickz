import FV7z.Alr.Hand
/-!
# `CArchiveLink::Release` (PLAN.md §M, M1): the start and `alr_ok`

From the entry (`S` = `rsp`, `g0` the registers, `this` = `g0.rdi`): the five pushes (`vc_0`, the bytes `P5`), the
`call` (19) of `NonOpen_ErrorInfo.ClearErrors ()` (`0x5d2b40`, `this + 0x40`; the continuation `kC`, the bytes it
returns with `C0`), `NonOpen_ArcPath.Empty ()` in line (24: the bytes `zW`, `Z1` of `vc_24`), the count `nZ` at
`this + 8`: 0 to the epilogue (`tail493`), else to the loop's head at the step `nZ - 1` (`L64`). With `C0`, `I` holds
at the count for the bytes after the stores (`hZ`).

`alr_ok`: from the entry, the run goes on to the goal, given `Ev` (`Holds`), `Eh` (`Hand`) and the start's
hypotheses.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Alr
set_option linter.unusedVariables false

open FV7z.Fr40 (KS)

/-- The bytes after `Empty ()` in line (`a` = `this`, its `_chars` at `a + 0x30`). -/
abbrev zW (W : Addr → Byte) (a : Addr) : Addr → Byte := Z1 W a (rdq(W, a + 48#64))

/-- The count at `a + 8` after `Empty ()`. -/
abbrev nZ (W : Addr → Byte) (a : Addr) : BitVec 32 := rdd(zW W a, a + 8#64)

variable {prof : Profile} {F : Footprint} {Wl : List Rgn} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop} {X : State}
  {t : Nat}

/-- `CArchiveLink::Release` from its entry. -/
theorem alr_ok {V : Addr → Byte} {e₂ : Addr} {code₂ : List Byte} {j₂ : Nat} {I D : Nat → (Addr → Byte) → Prop}
    {J : Nat → Addr → (Addr → Byte) → Prop} {H Hx : Nat → Addr → Addr → (Addr → Byte) → Prop}
    {Hi Hd : Nat → Addr → Addr → Nat → (Addr → Byte) → Prop}
    {Hj : Nat → Addr → Addr → Nat → Addr → (Addr → Byte) → Prop} {Ok : Addr → Nat → Prop}
    {C0 : (Addr → Byte) → Prop}
    (E : Ev prof F Wl L s₀ o gev gP gE X.cpu.gpr.rsp X.cpu.gpr e₂ code₂ j₂ I D J)
    (Xh : Eh prof F Wl L s₀ o gev gP gE X.cpu.gpr.rsp J H Hi Hj Hd Hx Ok)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = alr_at)
    (hs1 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8) i))
    (hs2 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8 - 8) i))
    (hs3 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8 - 8 - 8) i))
    (hs4 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8 - 8 - 8 - 8) i))
    (hs5 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8 - 8 - 8 - 8 - 8) i))
    (cC : ∃ code : List Byte, CodeIn L 0x5d2b40#64 code ∧ 0 < code.length)
    (kC : KC prof F Wl L s₀ o gev gP gE X.cpu.gpr.rsp 0x5d2b40#64 24 (P5 V X.cpu.gpr)
      (fun g => g.rdi = X.cpu.gpr.rdi + 64#64) C0)
    (f48 : ∀ W, C0 W → ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rdi + 48#64) i))
    (w56 : ∀ i < 4, Foot Wl (Addr.add (X.cpu.gpr.rdi + 56#64) i))
    (wp : ∀ W, C0 W → ∀ i < 4, Foot Wl (Addr.add (rdq(W, X.cpu.gpr.rdi + 48#64)) i))
    (hZ : ∀ W, C0 W → I (nZ W X.cpu.gpr.rdi).toNat (zW W X.cpu.gpr.rdi)) :
    GoG prof L o gev gP gE X t := by
  have hrip' : X.cpu.rip = alr_at.add 0 := by rw [addr_add_zero]; exact hrip
  refine (c_0 prof).run E.c E.hin (fun j' g' _ V' => j' = 19 ∧ V' = P5 V X.cpu.gpr ∧
      Fm X.cpu.gpr.rsp X.cpu.gpr g' ∧ g'.rdi = X.cpu.gpr.rdi + 64#64) hK hA hrip'
    (vc_0 hs1 hs2 hs3 hs4 hs5 fun _ a d _ _ _ e _ f _ => ⟨rfl, rfl, ⟨a, e, f⟩, d⟩) ?_
  rintro j' g fl V₁ ⟨rfl, hV₁, hm, gdi⟩ U t₁ hKU hAU hrU hgU -
  subst V₁ hgU
  -- `ClearErrors ()`, back at 24
  refine callK E hKU hAU hrU hm.1 (lt_len (by decide)) (call_19 _) tgt_19 cC kC gdi ?_
  intro Z W' t₂ hKZ hAZ hrZ hsZ hkZ hC
  have hmZ := fm_ret hm hsZ hkZ
  refine (c_24 prof).run E.c E.hin (fun j' g' _ V' => V' = zW W' X.cpu.gpr.rdi ∧ Fr Z.cpu.gpr g' ∧
      ((j' = 493 ∧ nZ W' X.cpu.gpr.rdi = 0) ∨
        (j' = 64 ∧ nZ W' X.cpu.gpr.rdi ≠ 0 ∧ g'.rax = BitVec.setWidth 64 (nZ W' X.cpu.gpr.rdi)))) hKZ hAZ hrZ
    (vc_24 (p := rdq(W', X.cpu.gpr.rdi + 48#64)) (n := nZ W' X.cpu.gpr.rdi) (by rw [hmZ.2.1])
      (by rw [hmZ.2.1]; exact f48 W' hC) (by rw [hmZ.2.1]; exact w56) (wp W' hC) (by rw [hmZ.2.1]; exact E.f8)
      (by rw [hmZ.2.1]) (fun h0 _ x _ => ⟨by rw [hmZ.2.1], x, Or.inl ⟨rfl, h0⟩⟩)
      (fun h0 _ x y _ => ⟨by rw [hmZ.2.1], x, Or.inr ⟨rfl, h0, y⟩⟩)) ?_
  rintro j' g fl V₁ ⟨hV₁, gf, hj⟩ U' t₃ hKU' hAU' hrU' hgU' -
  subst V₁ hgU'
  have hmU := Fm.fr hmZ gf
  rcases hj with ⟨rfl, h0⟩ | ⟨rfl, h0, gax⟩
  · -- the count 0: the epilogue
    have e0 : (nZ W' X.cpu.gpr.rdi).toNat = 0 := (congrArg BitVec.toNat h0).trans rfl
    have hI := hZ W' hC
    rw [e0] at hI
    exact tail493 E hKU' hAU' hrU' hmU hI
  · -- the loop from the step `nZ - 1`
    have hnz : (nZ W' X.cpu.gpr.rdi).toNat ≠ 0 := fun e => h0 (BitVec.eq_of_toNat_eq (e.trans rfl))
    have hlt := (nZ W' X.cpu.gpr.rdi).isLt
    simp only [Nat.reducePow] at hlt
    have e1 : (nZ W' X.cpu.gpr.rdi).toNat - 1 + 1 = (nZ W' X.cpu.gpr.rdi).toNat := by omega
    exact L64 E Xh ((nZ W' X.cpu.gpr.rdi).toNat - 1) (by omega) U' _ t₃ hKU' hAU' hrU'
      ⟨by rw [e1]; exact hZ W' hC, hmU, by rw [gax, e1, BitVec.ofNat_toNat, BitVec.setWidth_eq]⟩

end FV7z.Alr
