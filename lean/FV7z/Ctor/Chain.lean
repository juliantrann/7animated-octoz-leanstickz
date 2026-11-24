import FV7z.Ctor.Runs
/-!
# A registrar's call in the middle of a constructor (PLAN.md §M, constructors)

Ten constructors call registrars one after the other: `sub rsp, 8; lea rdi, [rip + d₁]; call R₁; …; lea rdi,
[rip + dₖ]; add rsp, 8; jmp Rₖ`. A call in the middle, `lea rdi, [rip + d]; call R`, by the registrar's contract.

- `sub8`: `rsp - 8` as a number.
- `lea_call`: from the `lea` at offset `j` of `sti` back after the `call` (`j + 12`), the bytes `RegOut` of those with
  the return address pushed, the registers a call keeps.
-/
namespace FV7z.Ctor
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn

theorem sub8 (x : Addr) (h : 8 ≤ x.toNat) : (x - 8).toNat = x.toNat - 8 := by bv_omega

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

end FV7z.Ctor
