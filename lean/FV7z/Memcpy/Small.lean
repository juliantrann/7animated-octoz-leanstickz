import FV7z.Memcpy.Sse2c
/-!
# `__memmove_sse2_unaligned`: the copies of 4 to 7 and of 8 to 15 bytes (PLAN.md M, the PLT contracts)

From `306` (`8 ≤ rdx < 16`) and from `323` (`4 ≤ rdx < 8`): `mov rcx, [rsi + rdx - k]`, `mov rsi, [rsi]`,
`mov [rdi + rdx - k], rcx`, `mov [rdi], rsi`, `ret`, with `k` 8 or 4 bytes (`rcx`, `rsi` as `ecx`, `esi` for 4). Both
loads come before the stores; the two stores overlap and cover the `rdx` bytes (`CopyP`, `Lemmas/CopyP.lean`).

- `wpV_ldA`, `wpV_stv`: a load into a register and a store of known bytes in `wpV`.
- `ldst`: a register loaded from `w / 8` bytes and stored as `w` bits stores them.
- `eaG_b0`, `eaG_bi`: the addresses `[b]` and `[b + i - k]`.
- `bL306`, `p306`; `bL323`, `p323`.
-/
namespace FV7z.Memcpy
open ZellicX86 Decode FV7z.Leaf FV7z.Fn FV7z.Strlen FV7z.Memset

section
variable {F : Footprint} {Wl : List Rgn}

/-- A load of `n` bytes at `a` into a register. -/
theorem wpV_ldA {n : Nat} {ea : Gprs → Addr} {h : Gprs → Rflags → List Byte → Gprs}
    {P : Gprs → Rflags → List Byte → Rflags → Prop} {ops : List VOp}
    {Q : Gprs → Rflags → XRegs → (Addr → Byte) → Prop} {g : Gprs} {f : Rflags} {x : XRegs} {V : Addr → Byte}
    {a : Addr} (he : ea g = a) (hf : ∀ i < n, Foot F.data (a.add i))
    (k : ∀ fl, P g f ((byteAddrs a n).map V) fl → wpV F Wl ops Q (h g f ((byteAddrs a n).map V)) fl x V) :
    wpV F Wl (.op (.load n ea h P) :: ops) Q g f x V := by
  subst he; exact ⟨rfl, hf, k⟩

/-- A store of the bytes `bs` at `a`. -/
theorem wpV_stv {n : Nat} {ea : Gprs → Addr} {val : Gprs → List Byte} {h : Gprs → Gprs} {ops : List VOp}
    {Q : Gprs → Rflags → XRegs → (Addr → Byte) → Prop} {g : Gprs} {f : Rflags} {x : XRegs} {V : Addr → Byte}
    {a : Addr} (bs : List Byte) (he : ea g = a) (hv : val g = bs) (hl : bs.length = n)
    (hf : ∀ i < n, Foot Wl (a.add i)) (k : wpV F Wl ops Q (h g) (rfz f) x (Vst V a bs)) :
    wpV F Wl (.op (.store n ea val h) :: ops) Q g f x V := by
  subst he; subst hv; exact ⟨rfl, hl, hf, k⟩

end

/-- A register loaded from `bs` as `w` bits and stored as `w` bits: `bs`. -/
theorem ldst {w : Nat} (bs : List Byte) (hw : w = 8 * bs.length) (h : w ≤ 64) :
    toBytesLE (((ofBytesLE w bs).setWidth 64).setWidth w) (w / 8) = bs := by
  have e : ((ofBytesLE w bs).setWidth 64).setWidth w = ofBytesLE w bs := by
    apply BitVec.eq_of_toNat_eq
    have h1 := (ofBytesLE w bs).isLt
    have h2 : 2 ^ w ≤ 2 ^ 64 := Nat.pow_le_pow_right (by decide) h
    rw [BitVec.toNat_setWidth, BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le h1 h2),
      Nat.mod_eq_of_lt h1]
  rw [e, show w / 8 = bs.length by omega]
  exact toBytesLE_ofBytesLE hw

theorem eaG_b0 {g : Gprs} {b : Nat} {a : Addr} (h : g.get (regOf b) = a) : eaG g (some b) none 1 0 = a.add 0 := by
  rw [← h]
  apply BitVec.eq_of_toNat_eq
  simp [eaG, optV, Addr.add]

theorem eaG_bi {g : Gprs} {b i : Nat} {a d : Addr} (hb : g.get (regOf b) = a) (hi : g.get (regOf i) = d) {k D : Nat}
    (hD : D + k = 2 ^ 64) (hk : k ≤ d.toNat) : eaG g (some b) (some i) 1 D = a.add (d.toNat - k) := by
  rw [← ea_back a d hD hk, ← hb, ← hi]
  apply BitVec.eq_of_toNat_eq
  simp [eaG, optV]

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle} {F : Footprint} {Wl : List Rgn}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {e : Addr} {V : Addr → Byte}

/-- The loads and stores of a copy of 8 to 15 bytes, at `306`. -/
theorem bL306 (prof : Profile) :
    BlkV prof mc2 306 322 [VOp.op (Op.ld 64 1 (some 6) (some 2) 1 18446744073709551608),
      VOp.op (Op.ld 64 6 (some 6) none 1 0),
      VOp.op (Op.st 64 (some 7) (some 2) 1 18446744073709551608 1), VOp.op (Op.st 64 (some 7) none 1 0 6)] :=
  .cons (d306 _) (OpI.ld (.inr rfl)) (by rw [mc2_length]; decide) <|
  .cons (d311 _) (OpI.ld (.inr rfl)) (by rw [mc2_length]; decide) <|
  .cons (d314 _) (OpI.st (.inr (.inr (.inr rfl)))) (by rw [mc2_length]; decide) <|
  .cons (d319 _) (OpI.st (.inr (.inr (.inr rfl)))) (by rw [mc2_length]; decide) <|
  .nil 322

/-- From `306`, `8 ≤ rdx < 16`: two loads, two stores, `ret`. -/
theorem p306 (c : Seg prof F Wl L s₀ o) (hin : CodeIn L e mc2) {X : State} {t : Nat} {g₀ : Gprs}
    {r : Addr}
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = e.add 306)
    (hkp : KpS g₀ X.cpu.gpr) (hax : X.cpu.gpr.rax = r) (hdi : X.cpu.gpr.rdi = g₀.rdi)
    (hsi : X.cpu.gpr.rsi = g₀.rsi) (hdx : X.cpu.gpr.rdx = g₀.rdx)
    (hlo : 8 ≤ g₀.rdx.toNat) (hhi : g₀.rdx.toNat < 16)
    (hsrc : ∀ i < g₀.rdx.toNat, Foot F.data (Addr.add g₀.rsi i))
    (hst : ∀ i < g₀.rdx.toNat, Foot Wl (Addr.add g₀.rdi i))
    (hd64 : g₀.rdi.toNat + g₀.rdx.toNat < 2 ^ 64)
    (hsp : g₀.rdi.toNat + g₀.rdx.toNat ≤ g₀.rsp.toNat ∨ g₀.rsp.toNat + 8 ≤ g₀.rdi.toNat)
    (hsp8 : g₀.rsp.toNat + 8 ≤ 2 ^ 64)
    (hR : RetC prof F Wl L s₀ o gev gP gE V g₀ r) : GoG prof L o gev gP gE X t := by
  have hl : ∀ a : Addr, ((byteAddrs a 8).map V).length = 8 := fun a => by rw [List.length_map, byteAddrs_len]
  refine c.s_blkV hin (bL306 prof) hK hA hrip ?_
  refine wpV_ldA (eaG_bi (a := g₀.rsi) (d := g₀.rdx) (by rw [get6, hsi]) (by rw [get2, hdx]) (k := 8) (D := 18446744073709551608)
      (by decide) (by omega))
    (fun i hi => ?_) fun fl₁ _ => ?_
  · rw [addr_add_add]
    exact hsrc _ (by omega)
  refine wpV_ldA (eaG_b0 (b := 6) (a := g₀.rsi) (by exact hsi)) (fun i hi => ?_) fun fl₂ _ => ?_
  · rw [addr_add_add]
    exact hsrc _ (by omega)
  refine wpV_stv ((byteAddrs (Addr.add g₀.rsi (g₀.rdx.toNat - 8)) 8).map V)
    (eaG_bi (a := g₀.rdi) (d := g₀.rdx) (by exact hdi) (by exact hdx) (k := 8) (D := 18446744073709551608) (by decide)
      (by omega))
    (ldst _ (by rw [hl]) (by decide)) (hl _) (fun i hi => ?_) ?_
  · rw [addr_add_add]
    exact hst _ (by omega)
  refine wpV_stv ((byteAddrs (Addr.add g₀.rsi 0) 8).map V) (eaG_b0 (b := 7) (a := g₀.rdi) (by exact hdi))
    (ldst _ (by rw [hl]) (by decide)) (hl _) (fun i hi => ?_) (wpV_nil ?_)
  · rw [addr_add_add]
    exact hst _ (by omega)
  intro Y t₁ hK₁ hA₁ hr₁ hg₁ _ _
  have hn := Nat.le_of_lt hd64
  have hC := ((CopyP.start V g₀.rdi g₀.rsi g₀.rdx.toNat).st hn (o := g₀.rdx.toNat - 8) (k := 8) (hl _)
    (by omega) CopyP.ld).st hn (o := 0) (k := 8) (hl _) (by omega) CopyP.ld
  refine ret_atC c hin (by rw [mc2_length]; decide) (d322 prof.feat) hK₁ hA₁ hr₁ (by rw [hg₁]; exact hkp)
    (by rw [hg₁]; exact hax)
    (fun i hi => hC.2 _ fun ⟨h1, h2⟩ => by rw [toNat_add_of_fits (n := 8) hi hsp8] at h1 h2; omega)
    (fun i hi => hC.1 i hi (if h : i < 8 then Or.inr ⟨by omega, by omega⟩
      else Or.inl (Or.inr ⟨by omega, by omega⟩))) hC.2 hR

/-- The loads and stores of a copy of 4 to 7 bytes, at `323`. -/
theorem bL323 (prof : Profile) :
    BlkV prof mc2 323 335 [VOp.op (Op.ld 32 1 (some 6) (some 2) 1 18446744073709551612),
      VOp.op (Op.ld 32 6 (some 6) none 1 0),
      VOp.op (Op.st 32 (some 7) (some 2) 1 18446744073709551612 1), VOp.op (Op.st 32 (some 7) none 1 0 6)] :=
  .cons (d323 _) (OpI.ld (.inl rfl)) (by rw [mc2_length]; decide) <|
  .cons (d327 _) (OpI.ld (.inl rfl)) (by rw [mc2_length]; decide) <|
  .cons (d329 _) (OpI.st (.inr (.inr (.inl rfl)))) (by rw [mc2_length]; decide) <|
  .cons (d333 _) (OpI.st (.inr (.inr (.inl rfl)))) (by rw [mc2_length]; decide) <|
  .nil 335

/-- From `323`, `4 ≤ rdx < 8`: two loads, two stores, `ret`. -/
theorem p323 (c : Seg prof F Wl L s₀ o) (hin : CodeIn L e mc2) {X : State} {t : Nat} {g₀ : Gprs}
    {r : Addr}
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = e.add 323)
    (hkp : KpS g₀ X.cpu.gpr) (hax : X.cpu.gpr.rax = r) (hdi : X.cpu.gpr.rdi = g₀.rdi)
    (hsi : X.cpu.gpr.rsi = g₀.rsi) (hdx : X.cpu.gpr.rdx = g₀.rdx)
    (hlo : 4 ≤ g₀.rdx.toNat) (hhi : g₀.rdx.toNat < 8)
    (hsrc : ∀ i < g₀.rdx.toNat, Foot F.data (Addr.add g₀.rsi i))
    (hst : ∀ i < g₀.rdx.toNat, Foot Wl (Addr.add g₀.rdi i))
    (hd64 : g₀.rdi.toNat + g₀.rdx.toNat < 2 ^ 64)
    (hsp : g₀.rdi.toNat + g₀.rdx.toNat ≤ g₀.rsp.toNat ∨ g₀.rsp.toNat + 8 ≤ g₀.rdi.toNat)
    (hsp8 : g₀.rsp.toNat + 8 ≤ 2 ^ 64)
    (hR : RetC prof F Wl L s₀ o gev gP gE V g₀ r) : GoG prof L o gev gP gE X t := by
  have hl : ∀ a : Addr, ((byteAddrs a 4).map V).length = 4 := fun a => by rw [List.length_map, byteAddrs_len]
  refine c.s_blkV hin (bL323 prof) hK hA hrip ?_
  refine wpV_ldA (eaG_bi (a := g₀.rsi) (d := g₀.rdx) (by rw [get6, hsi]) (by rw [get2, hdx]) (k := 4) (D := 18446744073709551612)
      (by decide) (by omega))
    (fun i hi => ?_) fun fl₁ _ => ?_
  · rw [addr_add_add]
    exact hsrc _ (by omega)
  refine wpV_ldA (eaG_b0 (b := 6) (a := g₀.rsi) (by exact hsi)) (fun i hi => ?_) fun fl₂ _ => ?_
  · rw [addr_add_add]
    exact hsrc _ (by omega)
  refine wpV_stv ((byteAddrs (Addr.add g₀.rsi (g₀.rdx.toNat - 4)) 4).map V)
    (eaG_bi (a := g₀.rdi) (d := g₀.rdx) (by exact hdi) (by exact hdx) (k := 4) (D := 18446744073709551612) (by decide)
      (by omega))
    (ldst _ (by rw [hl]) (by decide)) (hl _) (fun i hi => ?_) ?_
  · rw [addr_add_add]
    exact hst _ (by omega)
  refine wpV_stv ((byteAddrs (Addr.add g₀.rsi 0) 4).map V) (eaG_b0 (b := 7) (a := g₀.rdi) (by exact hdi))
    (ldst _ (by rw [hl]) (by decide)) (hl _) (fun i hi => ?_) (wpV_nil ?_)
  · rw [addr_add_add]
    exact hst _ (by omega)
  intro Y t₁ hK₁ hA₁ hr₁ hg₁ _ _
  have hn := Nat.le_of_lt hd64
  have hC := ((CopyP.start V g₀.rdi g₀.rsi g₀.rdx.toNat).st hn (o := g₀.rdx.toNat - 4) (k := 4) (hl _)
    (by omega) CopyP.ld).st hn (o := 0) (k := 4) (hl _) (by omega) CopyP.ld
  refine ret_atC c hin (by rw [mc2_length]; decide) (d335 prof.feat) hK₁ hA₁ hr₁ (by rw [hg₁]; exact hkp)
    (by rw [hg₁]; exact hax)
    (fun i hi => hC.2 _ fun ⟨h1, h2⟩ => by rw [toNat_add_of_fits (n := 8) hi hsp8] at h1 h2; omega)
    (fun i hi => hC.1 i hi (if h : i < 4 then Or.inr ⟨by omega, by omega⟩
      else Or.inl (Or.inr ⟨by omega, by omega⟩))) hC.2 hR

end FV7z.Memcpy
