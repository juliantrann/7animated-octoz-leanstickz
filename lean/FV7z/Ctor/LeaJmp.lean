import FV7z.Ctor.Code
import FV7z.Ctor.Reg
/-!
# A constructor that only calls a registrar, run (PLAN.md §M, constructors)

- `lea_jmp`: `endbr64; lea rdi, [rip + d]; jmp R` at offset `j` of `sti` (its stretch and `jmp` as `Lea*.lean` gives
  them): the run gets to `R` with `rdi` the argument, the bytes and the other registers unchanged.
- `lea_reg`: then the registrar's contract (`RegSpec`): the run gets to the constructor's caller with `RegOut` of the
  bytes for the argument and the registers a call keeps.
-/
namespace FV7z.Ctor
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn

variable {prof : Profile} {F : Footprint} {Wl : List Rgn} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop} {X : State}
  {t : Nat} {V : Addr → Byte}

/-- `endbr64; lea rdi, [rip + d]; jmp R`: to `R`, `rdi` the argument `A`. -/
theorem lea_jmp {j A rel : Nat} (hb : BlkA prof sti sti_at j (j + 11) [Op.nop, Op.mov 64 7 (.i A)])
    (hd : Dec prof.feat sti (j + 11) (FV7z.mk .jmp 64 [.rel rel] 5)) (hj : j + 11 < sti.length)
    (c : Seg prof F Wl L s₀ o) (hin : CodeIn L sti_at sti) (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V)
    (hrip : X.cpu.rip = sti_at.add j) {e₂ : Addr} {code₂ : List Byte} {tgt : Nat} (hin₂ : CodeIn L e₂ code₂)
    (ht : tgt < code₂.length) (htgt : sti_at.add (j + 11 + 5) + BitVec.ofNat 64 rel = e₂.add tgt)
    (k : ∀ Y t', KeptW Wl s₀ Y → Agree F Y.proc.mm.mem V → Y.cpu.rip = e₂.add tgt →
      Y.cpu.gpr = wr X.cpu.gpr 7 (BitVec.ofNat 64 A) → GoG prof L o gev gP gE Y t') :
    GoG prof L o gev gP gE X t := by
  refine (Sp.blkA hb).run c hin (fun j' g' _ V' => j' = j + 11 ∧ g' = wr X.cpu.gpr 7 (BitVec.ofNat 64 A) ∧ V' = V)
    hK hA hrip ?_ ?_
  · intro fl _ fl' _
    exact ⟨rfl, rfl, rfl⟩
  rintro j' g fl V' ⟨rfl, rfl, rfl⟩ Y t₁ hKY hAY hrY hgY -
  refine c.s_jmp_x hKY hAY hin hj hrY hd hin₂ ht htgt ?_
  rintro Z t' hKZ hAZ ⟨hrZ, hgZ⟩
  exact k Z t' hKZ hAZ hrZ (hgZ.trans hgY)

/-- `endbr64; lea rdi, [rip + d]; jmp R` with `R` a registrar: to the caller, `RegOut` of the bytes for the argument
`A`, the registers a call keeps. -/
theorem lea_reg {j A rel : Nat} {ra cnt tab : Addr} {max : Nat} {codeR : List Byte}
    (hb : BlkA prof sti sti_at j (j + 11) [Op.nop, Op.mov 64 7 (.i A)])
    (hd : Dec prof.feat sti (j + 11) (FV7z.mk .jmp 64 [.rel rel] 5)) (hj : j + 11 < sti.length)
    (htgt : sti_at.add (j + 11 + 5) + BitVec.ofNat 64 rel = ra.add 0)
    (c : Seg prof F Wl L s₀ o) (hin : CodeIn L sti_at sti) (hinR : CodeIn L ra codeR) (hR0 : 0 < codeR.length)
    (hR : RegSpec prof F Wl L s₀ o ra cnt tab max)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = sti_at.add j)
    (hl : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsp i))
    (hap : X.cpu.gpr.rsp.toNat + 8 ≤ tab.toNat ∨ cnt.toNat + 4 ≤ X.cpu.gpr.rsp.toNat)
    {e₂ : Addr} {code₂ : List Byte} {j₂ : Nat} (hin₂ : CodeIn L e₂ code₂) (h₂ : j₂ < code₂.length)
    (hra : rdq(V, X.cpu.gpr.rsp) = e₂.add j₂)
    (k : ∀ V' Z t', KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V' → RegOut cnt tab max (BitVec.ofNat 64 A) V V' →
      Z.cpu.rip = e₂.add j₂ → Osv.Back X.cpu.gpr Z.cpu.gpr → GoG prof L o gev gP gE Z t') :
    GoG prof L o gev gP gE X t := by
  refine lea_jmp hb hd hj c hin hK hA hrip hinR hR0 htgt fun Y t₁ hKY hAY hrY hgY => ?_
  have hsp : Y.cpu.gpr.rsp = X.cpu.gpr.rsp := by rw [hgY]; rfl
  have hdi : Y.cpu.gpr.rdi = BitVec.ofNat 64 A := by rw [hgY]; exact sw_64_64 _
  refine hR hKY hAY (by rw [hrY, addr_add_zero]) (by rw [hsp]; exact hl) (by rw [hsp]; exact hap) hin₂ h₂
    (by rw [hsp]; exact hra) fun V' Z t' hKZ hAZ hO hrZ hbk => ?_
  rw [hdi] at hO
  refine k V' Z t' hKZ hAZ hO hrZ ?_
  obtain ⟨b1, b2, b3, b4, b5, b6, b7⟩ := hbk
  rw [hgY] at b1 b2 b3 b4 b5 b6 b7
  exact ⟨b1, b2, b3, b4, b5, b6, b7⟩

end FV7z.Ctor
