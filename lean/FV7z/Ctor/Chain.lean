import FV7z.Ctor.Runs
/-!
# A registrar's call in the middle of a constructor (PLAN.md §M, constructors)

Ten constructors call registrars one after the other: `sub rsp, 8; lea rdi, [rip + d₁]; call R₁; …; lea rdi,
[rip + dₖ]; add rsp, 8; jmp Rₖ`. A call in the middle, `lea rdi, [rip + d]; call R`, by the registrar's contract.

- `sub8`: `rsp - 8` as a number.
- `lea_call`: from the `lea` at offset `j` of `sti` back after the `call` (`j + 12`), the bytes `RegOut` of those with
  the return address pushed, the registers a call keeps.
- `pro`: `endbr64; sub rsp, 8`.
- `lea_add_reg`: `lea rdi, [rip + d]; add rsp, 8; jmp R`, by the registrar's contract to the constructor's caller.
-/
namespace FV7z.Ctor
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn

theorem sub8 (x : Addr) (h : 8 ≤ x.toNat) : (x - 8).toNat = x.toNat - 8 := by bv_omega

theorem rsp_sub8 (g : Gprs) : (wr g 4 (subR (gv g 64 4) (BitVec.ofNat 64 8))).rsp = g.rsp - 8 := by
  show (subR (g.rsp.setWidth 64) (BitVec.ofNat 64 8)).setWidth 64 = g.rsp - 8
  rw [sw_64_64, subR_eq, sw_64_64]
  rfl

theorem rsp_add8 (g : Gprs) : (wr g 4 (addR (gv g 64 4) (BitVec.ofNat 64 8))).rsp = g.rsp + 8 := by
  show (addR (g.rsp.setWidth 64) (BitVec.ofNat 64 8)).setWidth 64 = g.rsp + 8
  rw [sw_64_64, addR_eq, sw_64_64]
  rfl

/-- The registers a call keeps, `rsp` apart. -/
def Cs (g g' : Gprs) : Prop :=
  g'.rbx = g.rbx ∧ g'.rbp = g.rbp ∧ g'.r12 = g.r12 ∧ g'.r13 = g.r13 ∧ g'.r14 = g.r14 ∧ g'.r15 = g.r15

variable {prof : Profile} {F : Footprint} {Wl : List Rgn} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop} {X : State}
  {t : Nat} {V : Addr → Byte}

/-- `lea rdi, [rip + d]; call R` at offset `j` of `sti`, `R` the registrar `r`: back at `j + 12`, the bytes `RegOut`
of those with the return address pushed below `rsp`, the registers a call keeps. -/
theorem lea_call {j A rel r : Nat} (hb : BlkA prof sti sti_at j (j + 7) [Op.mov 64 7 (.i A)])
    (hd : Dec prof.feat sti (j + 7) (FV7z.mk .call 64 [.rel rel] 5)) (hj : j + 7 + 5 < sti.length)
    (htgt : sti_at.add (j + 7 + 5) + BitVec.ofNat 64 rel = regAt r)
    (c : Seg prof F Wl L s₀ o) (hin : CodeIn L sti_at sti)
    (hR : RegSpec prof F Wl L s₀ o (regAt r) (regCnt r) (regTab r) (regMax r))
    (hinR : CodeIn L (regAt r) (regCode r))
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = sti_at.add j)
    (hst : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8) i)) (h8 : 8 ≤ X.cpu.gpr.rsp.toNat)
    (hap : X.cpu.gpr.rsp.toNat ≤ (regTab r).toNat ∨ (regCnt r).toNat + 4 ≤ X.cpu.gpr.rsp.toNat - 8)
    (k : ∀ V' Z t', KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V' →
      RegOut (regCnt r) (regTab r) (regMax r) (BitVec.ofNat 64 A)
        (Vst V (X.cpu.gpr.rsp - 8) (toBytesLE (sti_at.add (j + 7 + 5)) 8)) V' →
      Z.cpu.rip = sti_at.add (j + 7 + 5) → Kp X.cpu.gpr Z.cpu.gpr → GoG prof L o gev gP gE Z t') :
    GoG prof L o gev gP gE X t := by
  refine (Sp.blkA hb).run c hin (fun j' g' _ V' => j' = j + 7 ∧ g' = wr X.cpu.gpr 7 (BitVec.ofNat 64 A) ∧ V' = V)
    hK hA hrip ?_ ?_
  · intro fl _ fl' _
    exact ⟨rfl, rfl, rfl⟩
  rintro j' g fl V' ⟨rfl, rfl, rfl⟩ Y t₁ hKY hAY hrY hgY -
  have hsp : Y.cpu.gpr.rsp = X.cpu.gpr.rsp := by rw [hgY]; rfl
  have hdi : Y.cpu.gpr.rdi = BitVec.ofNat 64 A := by rw [hgY]; exact sw_64_64 _
  refine c.s_call hKY hAY hin (by omega) hrY hd hinR (reg_len r) htgt (by rw [hsp]; exact hst) ?_
  rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
  rw [hsp] at hA₂ hg₂
  have e8 := sub8 _ h8
  have hsp₂ : Y₂.cpu.gpr.rsp = X.cpu.gpr.rsp - 8 := by rw [hg₂]; rfl
  have hdi₂ : Y₂.cpu.gpr.rdi = BitVec.ofNat 64 A := by rw [hg₂]; exact hdi
  have hl : ∀ i < 8, Foot F.data (Addr.add Y₂.cpu.gpr.rsp i) := fun i hi => by
    rw [hsp₂]
    exact c.hws _ (hst i hi)
  have hs8' : (X.cpu.gpr.rsp - 8).toNat + 8 ≤ 2 ^ 64 := by
    rw [e8]
    have := X.cpu.gpr.rsp.isLt
    omega
  have hs8 : Y₂.cpu.gpr.rsp.toNat + 8 ≤ 2 ^ 64 := by rw [hsp₂]; exact hs8'
  have hap₂ : Y₂.cpu.gpr.rsp.toNat + 8 ≤ (regTab r).toNat ∨
      (regCnt r).toNat + 4 ≤ Y₂.cpu.gpr.rsp.toNat := by
    rw [hsp₂, e8]
    omega
  have hra : rdq(Vst V (X.cpu.gpr.rsp - 8) (toBytesLE (sti_at.add (j + 7 + 5)) 8), Y₂.cpu.gpr.rsp) =
      sti_at.add (j + 7 + 5) := by
    rw [hsp₂, vs (toBytesLE_length _ _) hs8']
    exact ofBytesLE_toBytesLE (n := 8) rfl _
  refine hR hK₂ hA₂ hr₂ hl hs8 hap₂ hin hj hra fun V' Z t' hKZ hAZ hO hrZ hbk => ?_
  rw [hdi₂] at hO
  refine k V' Z t' hKZ hAZ hO hrZ ?_
  obtain ⟨b1, b2, b3, b4, b5, b6, b7⟩ := hbk
  rw [hsp₂] at b1
  rw [hg₂, hgY] at b2 b3 b4 b5 b6 b7
  exact ⟨b1.trans (BitVec.sub_add_cancel _ _), b2, b3, b4, b5, b6, b7⟩

/-- `endbr64; sub rsp, 8` at offset `j` of `sti`. -/
theorem pro {j : Nat} (hb : BlkA prof sti sti_at j (j + 8) [Op.nop, Op.sub 64 4 (.i 8)])
    (c : Seg prof F Wl L s₀ o) (hin : CodeIn L sti_at sti)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = sti_at.add j)
    (k : ∀ Y t', KeptW Wl s₀ Y → Agree F Y.proc.mm.mem V → Y.cpu.rip = sti_at.add (j + 8) →
      Y.cpu.gpr.rsp = X.cpu.gpr.rsp - 8 → Cs X.cpu.gpr Y.cpu.gpr → GoG prof L o gev gP gE Y t') :
    GoG prof L o gev gP gE X t := by
  refine (Sp.blkA hb).run c hin (fun j' g' _ V' => j' = j + 8 ∧
    g' = wr X.cpu.gpr 4 (subR (gv X.cpu.gpr 64 4) (BitVec.ofNat 64 8)) ∧ V' = V) hK hA hrip ?_ ?_
  · intro fl _ fl' _
    exact ⟨rfl, rfl, rfl⟩
  rintro j' g fl V' ⟨rfl, rfl, rfl⟩ Y t₁ hKY hAY hrY hgY -
  have hsp : Y.cpu.gpr.rsp = X.cpu.gpr.rsp - 8 := by rw [hgY]; exact rsp_sub8 _
  have hcs : Cs X.cpu.gpr Y.cpu.gpr := by rw [hgY]; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  exact k Y t₁ hKY hAY hrY hsp hcs

/-- `lea rdi, [rip + d]; add rsp, 8; jmp R` at offset `p` of `sti`, `R` the registrar `r`: to the return address at
`rsp + 8`, the bytes `RegOut` of those before for the argument, `rsp` past it, the registers a call keeps. -/
theorem lea_add_reg {p A rel r : Nat}
    (hb : BlkA prof sti sti_at p (p + 11) [Op.mov 64 7 (.i A), Op.add 64 4 (.i 8)])
    (hd : Dec prof.feat sti (p + 11) (FV7z.mk .jmp 64 [.rel rel] 5)) (hj : p + 11 < sti.length)
    (htgt : sti_at.add (p + 11 + 5) + BitVec.ofNat 64 rel = (regAt r).add 0)
    (c : Seg prof F Wl L s₀ o) (hin : CodeIn L sti_at sti)
    (hR : RegSpec prof F Wl L s₀ o (regAt r) (regCnt r) (regTab r) (regMax r))
    (hinR : CodeIn L (regAt r) (regCode r))
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = sti_at.add p)
    (hl : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rsp + 8) i)) (h8 : (X.cpu.gpr.rsp + 8).toNat + 8 ≤ 2 ^ 64)
    (hap : (X.cpu.gpr.rsp + 8).toNat + 8 ≤ (regTab r).toNat ∨ (regCnt r).toNat + 4 ≤ (X.cpu.gpr.rsp + 8).toNat)
    {e₂ : Addr} {code₂ : List Byte} {j₂ : Nat} (hin₂ : CodeIn L e₂ code₂) (h₂ : j₂ < code₂.length)
    (hra : rdq(V, X.cpu.gpr.rsp + 8) = e₂.add j₂)
    (k : ∀ V' Z t', KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V' →
      RegOut (regCnt r) (regTab r) (regMax r) (BitVec.ofNat 64 A) V V' → Z.cpu.rip = e₂.add j₂ →
      Z.cpu.gpr.rsp = X.cpu.gpr.rsp + 8 + 8#64 → Cs X.cpu.gpr Z.cpu.gpr → GoG prof L o gev gP gE Z t') :
    GoG prof L o gev gP gE X t := by
  refine (Sp.blkA hb).run c hin (fun j' g' _ V' => j' = p + 11 ∧
    g' = wr (wr X.cpu.gpr 7 (BitVec.ofNat 64 A)) 4
      (addR (gv (wr X.cpu.gpr 7 (BitVec.ofNat 64 A)) 64 4) (BitVec.ofNat 64 8)) ∧ V' = V) hK hA hrip ?_ ?_
  · intro fl _ fl' _
    exact ⟨rfl, rfl, rfl⟩
  rintro j' g fl V' ⟨rfl, rfl, rfl⟩ Y t₁ hKY hAY hrY hgY -
  have hsp : Y.cpu.gpr.rsp = X.cpu.gpr.rsp + 8 := by rw [hgY]; exact rsp_add8 _
  have hdi : Y.cpu.gpr.rdi = BitVec.ofNat 64 A := by rw [hgY]; exact sw_64_64 _
  have hcs : Cs X.cpu.gpr Y.cpu.gpr := by rw [hgY]; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  refine c.s_jmp_x hKY hAY hin hj hrY hd hinR (reg_len r) htgt ?_
  rintro Z t' hKZ hAZ ⟨hrZ, hgZ⟩
  have hsZ : Z.cpu.gpr.rsp = X.cpu.gpr.rsp + 8 := by rw [hgZ]; exact hsp
  have hrZ' : Z.cpu.rip = regAt r := by rw [hrZ, addr_add_zero]
  have hap' : Z.cpu.gpr.rsp.toNat + 8 ≤ (regTab r).toNat ∨ (regCnt r).toNat + 4 ≤ Z.cpu.gpr.rsp.toNat := by
    rw [hsZ]; exact hap
  have hra' : rdq(V, Z.cpu.gpr.rsp) = e₂.add j₂ := by rw [hsZ]; exact hra
  refine hR hKZ hAZ hrZ' (by rw [hsZ]; exact hl) (by rw [hsZ]; exact h8) hap' hin₂ h₂ hra'
    fun V' W t'' hKW hAW hO hrW hbk => ?_
  have hdZ : Z.cpu.gpr.rdi = BitVec.ofNat 64 A := by rw [hgZ]; exact hdi
  rw [hdZ] at hO
  obtain ⟨b1, b2, b3, b4, b5, b6, b7⟩ := hbk
  rw [hsZ] at b1
  rw [hgZ] at b2 b3 b4 b5 b6 b7
  obtain ⟨c2, c3, c4, c5, c6, c7⟩ := hcs
  exact k V' W t'' hKW hAW hO hrW b1 ⟨b2.trans c2, b3.trans c3, b4.trans c4, b5.trans c5, b6.trans c6, b7.trans c7⟩

end FV7z.Ctor
