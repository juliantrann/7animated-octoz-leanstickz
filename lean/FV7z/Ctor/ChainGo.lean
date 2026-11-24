import FV7z.Ctor.Chain
import FV7z.Tun.Inv
/-!
# The constructors that call registrars one after the other (PLAN.md §M, constructors)

`sub rsp, 8; lea rdi, [rip + d₁]; call R₁; …; lea rdi, [rip + dₖ]; add rsp, 8; jmp Rₖ`, the calls as a list `cs`
of (registrar, argument).

- `ChainOut S cs V V'`: the bytes after the calls, from those before, the constructor entered with `rsp = S`: each
  call but the last with its return address pushed at `S - 16`.
- `ChainOut.out`: bytes apart from the registrars' tables and the pushed return addresses are unchanged.
- `CallsAt prof p cs`: the stretches, `call`s and `jmp` of the calls from offset `p` of `sti` on.
- `chain_go`: from the first `lea` to the constructor's caller.
- `chain_runs`: `Csu.Runs` for such a constructor.
-/
namespace FV7z.Ctor
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
open FV7z.Sga (vr)
open FV7z.Tun (Vst_out)

/-- The bytes after the registrar calls `cs` of a constructor entered with `rsp = S`. -/
def ChainOut (S : Addr) : List (Nat × Nat) → (Addr → Byte) → (Addr → Byte) → Prop
  | [], V, V' => V' = V
  | [(r, A)], V, V' => RegOut (regCnt r) (regTab r) (regMax r) (BitVec.ofNat 64 A) V V'
  | (r, A) :: c :: cs, V, V' => ∃ (ra : Addr) (V₁ : Addr → Byte),
      RegOut (regCnt r) (regTab r) (regMax r) (BitVec.ofNat 64 A) (Vst V (S - 8 - 8) (toBytesLE ra 8)) V₁ ∧
      ChainOut S (c :: cs) V₁ V'

/-- The registrars' tables with their counts lie in `[7981024, 7991300)`. -/
theorem reg_in : ∀ r, 7981024 ≤ (regTab r).toNat ∧ (regCnt r).toNat + 4 ≤ 7991300
  | 0 => by decide
  | 1 => by decide
  | _ + 2 => (by decide : 7981024 ≤ (7981024#64 : Addr).toNat ∧ (7981280#64 : Addr).toNat + 4 ≤ 7991300)

theorem sub16 (S : Addr) (h : 16 ≤ S.toNat) : (S - 8 - 8).toNat = S.toNat - 16 := by bv_omega

/-- Bytes apart from the tables and the pushed return addresses are as before. -/
theorem ChainOut.out {S : Addr} (hS : 16 ≤ S.toNat) {a : Addr} (ha1 : a.toNat < 7981024 ∨ 7991300 ≤ a.toNat)
    (ha2 : a.toNat < S.toNat - 16 ∨ S.toNat - 8 ≤ a.toNat) :
    ∀ (cs : List (Nat × Nat)) (V V' : Addr → Byte), ChainOut S cs V V' → V' a = V a
  | [], V, V', h => by rw [show V' = V from h]
  | [(r, A)], V, V', h => by
    have := reg_in r
    exact RegOut.out (show RegOut (regCnt r) (regTab r) (regMax r) _ V V' from h) (reg_lay r) (by omega)
  | (r, A) :: c :: cs, V, V', h => by
    obtain ⟨ra, V₁, h1, h2⟩ := h
    have := reg_in r
    have e := sub16 S hS
    have hs : (S - 8 - 8).toNat + (toBytesLE ra 8).length ≤ 2 ^ 64 := by
      rw [e, toBytesLE_length]
      have := S.isLt
      omega
    rw [ChainOut.out hS ha1 ha2 (c :: cs) V₁ V' h2, RegOut.out h1 (reg_lay r) (by omega),
      Vst_out V _ _ a hs (by rw [e, toBytesLE_length]; omega)]

variable {prof : Profile} {F : Footprint} {Wl : List Rgn} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}

/-- The calls `cs` from offset `p` of `sti`: a `lea rdi; call R` for each but the last, then `lea rdi; add rsp, 8;
jmp R`. -/
def CallsAt (prof : Profile) : Nat → List (Nat × Nat) → Prop
  | _, [] => False
  | p, [(r, A)] => ∃ rel, BlkA prof sti sti_at p (p + 11) [Op.mov 64 7 (.i A), Op.add 64 4 (.i 8)] ∧
      Dec prof.feat sti (p + 11) (FV7z.mk .jmp 64 [.rel rel] 5) ∧ p + 11 < sti.length ∧
      sti_at.add (p + 11 + 5) + BitVec.ofNat 64 rel = (regAt r).add 0
  | p, (r, A) :: c :: cs => ∃ rel, BlkA prof sti sti_at p (p + 7) [Op.mov 64 7 (.i A)] ∧
      Dec prof.feat sti (p + 7) (FV7z.mk .call 64 [.rel rel] 5) ∧ p + 7 + 5 < sti.length ∧
      sti_at.add (p + 7 + 5) + BitVec.ofNat 64 rel = regAt r ∧ CallsAt prof (p + 7 + 5) (c :: cs)

theorem Cs.trans {g g' g'' : Gprs} (h : Cs g g') (h' : Cs g' g'') : Cs g g'' :=
  ⟨h'.1.trans h.1, h'.2.1.trans h.2.1, h'.2.2.1.trans h.2.2.1, h'.2.2.2.1.trans h.2.2.2.1,
    h'.2.2.2.2.1.trans h.2.2.2.2.1, h'.2.2.2.2.2.trans h.2.2.2.2.2⟩

/-- From the first `lea` of the calls `cs` at offset `p`, `rsp = S - 8`, to the return address at `S`: the bytes
`ChainOut`, `rsp = S + 8`, the registers a call keeps. -/
theorem chain_go (c : Seg prof F Wl L s₀ o) (hin : CodeIn L sti_at sti)
    (hR : ∀ r, RegSpec prof F Wl L s₀ o (regAt r) (regCnt r) (regTab r) (regMax r))
    (hinR : ∀ r, CodeIn L (regAt r) (regCode r)) {S : Addr}
    (hst : ∀ i < 8, Foot Wl (Addr.add (S - 8 - 8) i)) (hlS : ∀ i < 8, Foot F.data (Addr.add S i))
    (hhi : 7991300 + 16 ≤ S.toNat) (hS8 : S.toNat + 8 ≤ 2 ^ 64)
    {e₂ : Addr} {code₂ : List Byte} {j₂ : Nat} (hin₂ : CodeIn L e₂ code₂) (h₂ : j₂ < code₂.length) :
    ∀ (cs : List (Nat × Nat)) (p : Nat) (X : State) (t : Nat) (V : Addr → Byte), CallsAt prof p cs →
    KeptW Wl s₀ X → Agree F X.proc.mm.mem V → X.cpu.rip = sti_at.add p → X.cpu.gpr.rsp = S - 8 →
    rdq(V, S) = e₂.add j₂ →
    (∀ V' Z t', KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V' → ChainOut S cs V V' → Z.cpu.rip = e₂.add j₂ →
      Z.cpu.gpr.rsp = S + 8 → Cs X.cpu.gpr Z.cpu.gpr → GoG prof L o gev gP gE Z t') →
    GoG prof L o gev gP gE X t
  | [], _, _, _, _, hC, _, _, _, _, _, _ => hC.elim
  | [(r, A)], p, X, t, V, hC, hK, hA, hrip, hsp, hra, k => by
    obtain ⟨rel, hb, hd, hj, htgt⟩ := hC
    have hS : X.cpu.gpr.rsp + 8 = S := by rw [hsp]; exact BitVec.sub_add_cancel _ _
    have := reg_in r
    have hl : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rsp + 8) i) := by rw [hS]; exact hlS
    have h8 : (X.cpu.gpr.rsp + 8).toNat + 8 ≤ 2 ^ 64 := by rw [hS]; exact hS8
    have hap : (X.cpu.gpr.rsp + 8).toNat + 8 ≤ (regTab r).toNat ∨
        (regCnt r).toNat + 4 ≤ (X.cpu.gpr.rsp + 8).toNat := by
      rw [hS]
      omega
    have hra' : rdq(V, X.cpu.gpr.rsp + 8) = e₂.add j₂ := by rw [hS]; exact hra
    refine lea_add_reg hb hd hj htgt c hin (hR r) (hinR r) hK hA hrip hl h8 hap hin₂ h₂ hra'
      fun V' Z t' hKZ hAZ hO hrZ hsZ hcZ => k V' Z t' hKZ hAZ hO hrZ ?_ hcZ
    rw [hsZ, hS]
    rfl
  | (r, A) :: c' :: cs, p, X, t, V, hC, hK, hA, hrip, hsp, hra, k => by
    obtain ⟨rel, hb, hd, hj, htgt, hC'⟩ := hC
    have := reg_in r
    have e8 : (S - 8).toNat = S.toNat - 8 := sub8 S (by omega)
    have e16 := sub16 S (by omega)
    have h8 : 8 ≤ X.cpu.gpr.rsp.toNat := by rw [hsp, e8]; omega
    have hap : X.cpu.gpr.rsp.toNat ≤ (regTab r).toNat ∨ (regCnt r).toNat + 4 ≤ X.cpu.gpr.rsp.toNat - 8 := by
      rw [hsp, e8]
      omega
    have hst' : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8) i) := by rw [hsp]; exact hst
    refine lea_call hb hd hj htgt c hin (hR r) (hinR r) hK hA hrip hst' h8 hap
      fun V₁ Y t₁ hKY hAY hO hrY hkY => ?_
    rw [hsp] at hO
    obtain ⟨k1, k2⟩ := hkY
    have hsY : Y.cpu.gpr.rsp = S - 8 := k1.trans hsp
    -- the return address at `S`: apart from the table and from the pushed one
    have hs : (S - 8 - 8).toNat + 8 ≤ 2 ^ 64 := by rw [e16]; omega
    have hra₁ : rdq(V₁, S) = e₂.add j₂ := by
      rw [← hra]
      refine congrArg (ofBytesLE 64) ((hO.rd (reg_lay r) hS8 (by omega)).trans ?_)
      exact vr (toBytesLE_length _ _) hs hS8 (by rw [e16]; omega)
    exact chain_go c hin hR hinR hst hlS hhi hS8 hin₂ h₂ (c' :: cs) (p + 7 + 5) Y t₁ V₁ hC' hKY hAY hrY hsY hra₁
      fun V' Z t' hKZ hAZ hO' hrZ hsZ hcZ =>
        k V' Z t' hKZ hAZ ⟨_, V₁, hO, hO'⟩ hrZ hsZ (Cs.trans (k2 : Cs X.cpu.gpr Y.cpu.gpr) hcZ)

/-- A constructor `endbr64; sub rsp, 8` then the calls `cs`, the `m`-th function `__libc_csu_init` calls, is a
function as `Csu.csu_ok` asks, for an invariant that `ChainOut` of its calls takes from `m` to `m + 1`, the stack of
`__libc_csu_init` above the registrars' tables and 16 bytes below its frame writable. -/
theorem chain_runs {J : Nat → (Addr → Byte) → Prop} {sp : Addr} {tg : Nat → Addr} {a₀ a₁ a₂ : BitVec 64}
    {m j : Nat} {cs : List (Nat × Nat)} (c : Seg prof F Wl L s₀ o) (hC : Csu.Env F Wl L sp tg)
    (hin : CodeIn L sti_at sti) (htg : csuTg m = sti_at.add j)
    (hpro : BlkA prof sti sti_at j (j + 8) [Op.nop, Op.sub 64 4 (.i 8)]) (hcs : CallsAt prof (j + 8) cs)
    (hR : ∀ r, RegSpec prof F Wl L s₀ o (regAt r) (regCnt r) (regTab r) (regMax r))
    (hinR : ∀ r, CodeIn L (regAt r) (regCode r))
    (hst : ∀ i < 8, Foot Wl (Addr.add (sp - 64#64 - 8 - 8) i)) (hhi : 7991300 + 80 ≤ sp.toNat)
    (hJ : ∀ V V', J m V → ChainOut (sp - 64#64) cs V V' → J (m + 1) V') :
    Csu.Runs prof F Wl L s₀ o gev gP gE J sp a₀ a₁ a₂ m (csuTg m) := by
  intro X t V j₂ hK hA hI hr hsp _ hj hra k
  have hs0 := hC.s0
  have hs8 := hC.s8
  have n := Csu.sp_n hs0
  have hlS : ∀ i < 8, Foot F.data (Addr.add (sp - 64#64) i) := fun i hi => c.hws _ (hC.st i (by omega))
  have hS8 : (sp - 64#64).toNat + 8 ≤ 2 ^ 64 := by rw [n]; omega
  refine pro hpro c hin hK hA (hr.trans htg) fun Y t₀ hKY hAY hrY hsY hcY => ?_
  rw [hsp] at hsY
  refine chain_go c hin hR hinR hst hlS (by rw [n]; omega) hS8 hC.code hj cs (j + 8) Y t₀ V hcs hKY hAY
    hrY hsY hra fun V' Z t' hKZ hAZ hO hrZ hsZ hcZ => ?_
  have hc : Cs X.cpu.gpr Z.cpu.gpr := Cs.trans hcY hcZ
  refine k Z t' V' hKZ hAZ (hJ V V' hI hO) (fun a ha => ?_) (fun a ha => ?_) hrZ ⟨by rw [hsZ, hsp]; rfl, hc⟩
  · exact ChainOut.out (by rw [n]; omega) (.inr (by omega)) (.inr (by rw [n]; omega)) cs V V' hO
  · exact ChainOut.out (by rw [n]; omega) (.inl (by omega)) (.inl (by rw [n]; omega)) cs V V' hO

end FV7z.Ctor
