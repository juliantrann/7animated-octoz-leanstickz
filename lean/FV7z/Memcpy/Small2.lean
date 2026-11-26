import FV7z.Memcpy.Small
/-!
# `__memmove_sse2_unaligned`: the copies of fewer than 4 bytes, and the choice below 16 (PLAN.md M)

From `283`, `rdx < 16`: `cmp dl, 8`, `jae 306`; `cmp dl, 4`, `jae 323`; `cmp dl, 1`, `ja 336`, `jb 305`; then one byte
(`300`: `movzx ecx, byte [rsi]`, `mov [rdi], cl`, `ret`). From `336`, `2 ≤ rdx < 4`: `movzx ecx, word [rsi + rdx - 2]`,
`movzx esi, word [rsi]`, `mov [rdi + rdx - 2], cx`, `mov [rdi], si`, `ret`. At `305`, `rdx = 0`: `ret`.

- `ldzxst`: a register loaded by `movzx` from `v / 8` bytes and stored as `v` bits stores them.
- `bL336`, `p336`; `bL300`, `p300`; `p305`; `b283`, `b288`, `b293` and `p283`, the copy of `rdx < 16` bytes.
-/
namespace FV7z.Memcpy
open ZellicX86 Decode FV7z.Leaf FV7z.Fn FV7z.Strlen FV7z.Memset

/-- A register loaded by `movzx` from `bs` as `v` bits and stored as `v` bits: `bs`. -/
theorem ldzxst {v : Nat} (bs : List Byte) (hw : v = 8 * bs.length) (h : v ≤ 32) :
    toBytesLE ((((ofBytesLE v bs).setWidth 32).setWidth 64).setWidth v) (v / 8) = bs := by
  have e : (((ofBytesLE v bs).setWidth 32).setWidth 64).setWidth v = ofBytesLE v bs := by
    apply BitVec.eq_of_toNat_eq
    have h1 := (ofBytesLE v bs).isLt
    have h2 : 2 ^ v ≤ 2 ^ 32 := Nat.pow_le_pow_right (by decide) h
    have h3 : (ofBytesLE v bs).toNat < 2 ^ 32 := Nat.lt_of_lt_of_le h1 h2
    have h4 : (ofBytesLE v bs).toNat < 2 ^ 64 := Nat.lt_of_lt_of_le h3 (by decide)
    rw [BitVec.toNat_setWidth, BitVec.toNat_setWidth, BitVec.toNat_setWidth, Nat.mod_eq_of_lt h3,
      Nat.mod_eq_of_lt h4, Nat.mod_eq_of_lt h1]
  rw [e, show v / 8 = bs.length by omega]
  exact toBytesLE_ofBytesLE hw

/-- The loads and stores of a copy of 2 or 3 bytes, at `336`. -/
theorem bL336 (prof : Profile) :
    BlkV prof mc2 336 352 [VOp.op (Op.ldzx 16 1 (some 6) (some 2) 1 18446744073709551614),
      VOp.op (Op.ldzx 16 6 (some 6) none 1 0),
      VOp.op (Op.st 16 (some 7) (some 2) 1 18446744073709551614 1), VOp.op (Op.st 16 (some 7) none 1 0 6)] :=
  .cons (d336 _) (OpI.ldzx (.inr rfl)) (by rw [mc2_length]; decide) <|
  .cons (d341 _) (OpI.ldzx (.inr rfl)) (by rw [mc2_length]; decide) <|
  .cons (d344 _) (OpI.st (.inr (.inl rfl))) (by rw [mc2_length]; decide) <|
  .cons (d349 _) (OpI.st (.inr (.inl rfl))) (by rw [mc2_length]; decide) <|
  .nil 352

/-- The load and store of a copy of 1 byte, at `300`. -/
theorem bL300 (prof : Profile) :
    BlkV prof mc2 300 305 [VOp.op (Op.ldzx 8 1 (some 6) none 1 0), VOp.op (Op.st 8 (some 7) none 1 0 1)] :=
  .cons (d300 _) (OpI.ldzx (.inl rfl)) (by rw [mc2_length]; decide) <|
  .cons (d303 _) (OpI.st (.inl rfl)) (by rw [mc2_length]; decide) <|
  .nil 305

/-- `cmp dl, 8`. -/
theorem b283 (prof : Profile) : BlkV prof mc2 283 286 [VOp.op (Op.cmp 8 2 (.i 8))] :=
  .cons (d283 _) (OpI.cmp8 (.i 8)) (by rw [mc2_length]; decide) <| .nil 286

/-- `cmp dl, 4`. -/
theorem b288 (prof : Profile) : BlkV prof mc2 288 291 [VOp.op (Op.cmp 8 2 (.i 4))] :=
  .cons (d288 _) (OpI.cmp8 (.i 4)) (by rw [mc2_length]; decide) <| .nil 291

/-- `cmp dl, 1`. -/
theorem b293 (prof : Profile) : BlkV prof mc2 293 296 [VOp.op (Op.cmp 8 2 (.i 1))] :=
  .cons (d293 _) (OpI.cmp8 (.i 1)) (by rw [mc2_length]; decide) <| .nil 296

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle} {F : Footprint} {Wl : List Rgn}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {e : Addr} {V : Addr → Byte}

/-- From `336`, `2 ≤ rdx < 4`: two loads, two stores, `ret`. -/
theorem p336 (c : Seg prof F Wl L s₀ o) (hin : CodeIn L e mc2) {X : State} {t : Nat} {g₀ : Gprs}
    {r : Addr} (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = e.add 336)
    (hkp : KpS g₀ X.cpu.gpr) (hax : X.cpu.gpr.rax = r) (hdi : X.cpu.gpr.rdi = g₀.rdi)
    (hsi : X.cpu.gpr.rsi = g₀.rsi) (hdx : X.cpu.gpr.rdx = g₀.rdx)
    (hlo : 2 ≤ g₀.rdx.toNat) (hhi : g₀.rdx.toNat < 4)
    (hsrc : ∀ i < g₀.rdx.toNat, Foot F.data (Addr.add g₀.rsi i))
    (hst : ∀ i < g₀.rdx.toNat, Foot Wl (Addr.add g₀.rdi i))
    (hd64 : g₀.rdi.toNat + g₀.rdx.toNat < 2 ^ 64)
    (hsp : g₀.rdi.toNat + g₀.rdx.toNat ≤ g₀.rsp.toNat ∨ g₀.rsp.toNat + 8 ≤ g₀.rdi.toNat)
    (hsp8 : g₀.rsp.toNat + 8 ≤ 2 ^ 64)
    (hR : RetC prof F Wl L s₀ o gev gP gE V g₀ r) : GoG prof L o gev gP gE X t := by
  have hl : ∀ a : Addr, ((byteAddrs a 2).map V).length = 2 := fun a => by rw [List.length_map, byteAddrs_len]
  refine c.s_blkV hin (bL336 prof) hK hA hrip ?_
  refine wpV_ldA (eaG_bi (a := g₀.rsi) (d := g₀.rdx) (by rw [get6, hsi]) (by rw [get2, hdx]) (k := 2)
      (D := 18446744073709551614) (by decide) (by omega))
    (fun i hi => ?_) fun fl₁ _ => ?_
  · rw [addr_add_add]
    exact hsrc _ (by omega)
  refine wpV_ldA (eaG_b0 (b := 6) (a := g₀.rsi) (by exact hsi)) (fun i hi => ?_) fun fl₂ _ => ?_
  · rw [addr_add_add]
    exact hsrc _ (by omega)
  refine wpV_stv ((byteAddrs (Addr.add g₀.rsi (g₀.rdx.toNat - 2)) 2).map V)
    (eaG_bi (a := g₀.rdi) (d := g₀.rdx) (by exact hdi) (by exact hdx) (k := 2) (D := 18446744073709551614)
      (by decide) (by omega))
    (ldzxst _ (by rw [hl]) (by decide)) (hl _) (fun i hi => ?_) ?_
  · rw [addr_add_add]
    exact hst _ (by omega)
  refine wpV_stv ((byteAddrs (Addr.add g₀.rsi 0) 2).map V) (eaG_b0 (b := 7) (a := g₀.rdi) (by exact hdi))
    (ldzxst _ (by rw [hl]) (by decide)) (hl _) (fun i hi => ?_) (wpV_nil ?_)
  · rw [addr_add_add]
    exact hst _ (by omega)
  intro Y t₁ hK₁ hA₁ hr₁ hg₁ _ _
  have hn := Nat.le_of_lt hd64
  have hC := ((CopyP.start V g₀.rdi g₀.rsi g₀.rdx.toNat).st hn (o := g₀.rdx.toNat - 2) (k := 2) (hl _)
    (by omega) CopyP.ld).st hn (o := 0) (k := 2) (hl _) (by omega) CopyP.ld
  refine ret_atC c hin (by rw [mc2_length]; decide) (d352 prof.feat) hK₁ hA₁ hr₁ (by rw [hg₁]; exact hkp)
    (by rw [hg₁]; exact hax)
    (fun i hi => hC.2 _ fun ⟨h1, h2⟩ => by rw [toNat_add_of_fits (n := 8) hi hsp8] at h1 h2; omega)
    (fun i hi => hC.1 i hi (if h : i < 2 then Or.inr ⟨by omega, by omega⟩
      else Or.inl (Or.inr ⟨by omega, by omega⟩))) hC.2 hR

/-- From `300`, `rdx = 1`: one load, one store, `ret`. -/
theorem p300 (c : Seg prof F Wl L s₀ o) (hin : CodeIn L e mc2) {X : State} {t : Nat} {g₀ : Gprs}
    {r : Addr} (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = e.add 300)
    (hkp : KpS g₀ X.cpu.gpr) (hax : X.cpu.gpr.rax = r) (hdi : X.cpu.gpr.rdi = g₀.rdi)
    (hsi : X.cpu.gpr.rsi = g₀.rsi) (_hdx : X.cpu.gpr.rdx = g₀.rdx)
    (h1 : g₀.rdx.toNat = 1)
    (hsrc : ∀ i < g₀.rdx.toNat, Foot F.data (Addr.add g₀.rsi i))
    (hst : ∀ i < g₀.rdx.toNat, Foot Wl (Addr.add g₀.rdi i))
    (hd64 : g₀.rdi.toNat + g₀.rdx.toNat < 2 ^ 64)
    (hsp : g₀.rdi.toNat + g₀.rdx.toNat ≤ g₀.rsp.toNat ∨ g₀.rsp.toNat + 8 ≤ g₀.rdi.toNat)
    (hsp8 : g₀.rsp.toNat + 8 ≤ 2 ^ 64)
    (hR : RetC prof F Wl L s₀ o gev gP gE V g₀ r) : GoG prof L o gev gP gE X t := by
  have hl : ∀ a : Addr, ((byteAddrs a 1).map V).length = 1 := fun a => by rw [List.length_map, byteAddrs_len]
  refine c.s_blkV hin (bL300 prof) hK hA hrip ?_
  refine wpV_ldA (eaG_b0 (b := 6) (a := g₀.rsi) (by rw [get6, hsi])) (fun i hi => ?_) fun fl₁ _ => ?_
  · rw [addr_add_add]
    exact hsrc _ (by omega)
  refine wpV_stv ((byteAddrs (Addr.add g₀.rsi 0) 1).map V) (eaG_b0 (b := 7) (a := g₀.rdi) (by exact hdi))
    (ldzxst _ (by rw [hl]) (by decide)) (hl _) (fun i hi => ?_) (wpV_nil ?_)
  · rw [addr_add_add]
    exact hst _ (by omega)
  intro Y t₁ hK₁ hA₁ hr₁ hg₁ _ _
  have hC := (CopyP.start V g₀.rdi g₀.rsi g₀.rdx.toNat).st (Nat.le_of_lt hd64) (o := 0) (k := 1) (hl _)
    (by omega) CopyP.ld
  refine ret_atC c hin (by rw [mc2_length]; decide) (d305 prof.feat) hK₁ hA₁ hr₁ (by rw [hg₁]; exact hkp)
    (by rw [hg₁]; exact hax)
    (fun i hi => hC.2 _ fun ⟨h1, h2⟩ => by rw [toNat_add_of_fits (n := 8) hi hsp8] at h1 h2; omega)
    (fun i hi => hC.1 i hi (Or.inr ⟨by omega, by omega⟩)) hC.2 hR

/-- At `305`, `rdx = 0`: `ret`, nothing copied. -/
theorem p305 (c : Seg prof F Wl L s₀ o) (hin : CodeIn L e mc2) {X : State} {t : Nat} {g₀ : Gprs}
    {r : Addr} (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = e.add 305)
    (hkp : KpS g₀ X.cpu.gpr) (hax : X.cpu.gpr.rax = r) (_hdi : X.cpu.gpr.rdi = g₀.rdi)
    (_hsi : X.cpu.gpr.rsi = g₀.rsi) (_hdx : X.cpu.gpr.rdx = g₀.rdx)
    (h0 : g₀.rdx.toNat = 0)
    (_hsrc : ∀ i < g₀.rdx.toNat, Foot F.data (Addr.add g₀.rsi i))
    (_hst : ∀ i < g₀.rdx.toNat, Foot Wl (Addr.add g₀.rdi i))
    (_hd64 : g₀.rdi.toNat + g₀.rdx.toNat < 2 ^ 64)
    (_hsp : g₀.rdi.toNat + g₀.rdx.toNat ≤ g₀.rsp.toNat ∨ g₀.rsp.toNat + 8 ≤ g₀.rdi.toNat)
    (_hsp8 : g₀.rsp.toNat + 8 ≤ 2 ^ 64)
    (hR : RetC prof F Wl L s₀ o gev gP gE V g₀ r) : GoG prof L o gev gP gE X t := by
  exact ret_atC c hin (by rw [mc2_length]; decide) (d305 prof.feat) hK hA hrip hkp hax (fun _ _ => rfl)
    (fun i hi => absurd hi (by omega)) (fun _ _ => rfl) hR

/-- From `283`, `rdx < 16`: by `dl`, the copy of 8 to 15, 4 to 7, 2 or 3, 1 or 0 bytes. -/
theorem p283 (c : Seg prof F Wl L s₀ o) (hin : CodeIn L e mc2) {X : State} {t : Nat} {g₀ : Gprs}
    {r : Addr} (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = e.add 283)
    (hkp : KpS g₀ X.cpu.gpr) (hax : X.cpu.gpr.rax = r) (hdi : X.cpu.gpr.rdi = g₀.rdi)
    (hsi : X.cpu.gpr.rsi = g₀.rsi) (hdx : X.cpu.gpr.rdx = g₀.rdx)
    (hhi : g₀.rdx.toNat < 16)
    (hsrc : ∀ i < g₀.rdx.toNat, Foot F.data (Addr.add g₀.rsi i))
    (hst : ∀ i < g₀.rdx.toNat, Foot Wl (Addr.add g₀.rdi i))
    (hd64 : g₀.rdi.toNat + g₀.rdx.toNat < 2 ^ 64)
    (hsp : g₀.rdi.toNat + g₀.rdx.toNat ≤ g₀.rsp.toNat ∨ g₀.rsp.toNat + 8 ≤ g₀.rdi.toNat)
    (hsp8 : g₀.rsp.toNat + 8 ≤ 2 ^ 64)
    (hR : RetC prof F Wl L s₀ o gev gP gE V g₀ r) : GoG prof L o gev gP gE X t := by
  have hd8 : (X.cpu.gpr.rdx.setWidth 8).toNat = g₀.rdx.toNat := by rw [hdx]; exact dl_toNat hhi
  -- `cmp dl, 8`, `jae 306`
  refine c.s_blkV hin (b283 prof) hK hA hrip ?_
  refine wpV_reg fun fl hP => wpV_nil ?_
  intro Y₁ t₁ hK₁ hA₁ hr₁ hg₁ hf₁ _
  simp only [gv, Src.val, get2] at hP
  have e₁ : Y₁.cpu.gpr = X.cpu.gpr := hg₁
  refine c.s_jccV hK₁ hA₁ hin (by rw [mc2_length]; decide) hr₁ (d286 prof.feat) (tgt := 306) rfl
    (by rw [mc2_length]; decide) ?_ ?_
  · intro htk Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂, _⟩
    rw [hf₁, hP, cond_3, subF_cf] at htk
    have h8 := jae_t htk
    simp only [hd8, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod] at h8
    have e₂ : Y₂.cpu.gpr = X.cpu.gpr := by rw [hg₂, e₁]
    exact p306 c hin hK₂ hA₂ hr₂ (by rw [e₂]; exact hkp) (by rw [e₂]; exact hax) (by rw [e₂]; exact hdi)
      (by rw [e₂]; exact hsi) (by rw [e₂]; exact hdx) h8 hhi hsrc hst hd64 hsp hsp8 hR
  intro hfa Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂, _⟩
  rw [hf₁, hP, cond_3, subF_cf] at hfa
  have h8 := jae_f hfa
  simp only [hd8, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod] at h8
  have e₂ : Y₂.cpu.gpr = X.cpu.gpr := by rw [hg₂, e₁]
  -- `cmp dl, 4`, `jae 323`
  refine c.s_blkV hin (b288 prof) hK₂ hA₂ hr₂ ?_
  refine wpV_reg fun fl hP => wpV_nil ?_
  intro Y₃ t₃ hK₃ hA₃ hr₃ hg₃ hf₃ _
  simp only [gv, Src.val, get2] at hP
  have e₃ : Y₃.cpu.gpr = X.cpu.gpr := by rw [hg₃, e₂]
  rw [e₂] at hP
  refine c.s_jccV hK₃ hA₃ hin (by rw [mc2_length]; decide) hr₃ (d291 prof.feat) (tgt := 323) rfl
    (by rw [mc2_length]; decide) ?_ ?_
  · intro htk Y₄ t₄ hK₄ hA₄ ⟨hr₄, hg₄, _⟩
    rw [hf₃, hP, cond_3, subF_cf] at htk
    have h4 := jae_t htk
    simp only [hd8, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod] at h4
    have e₄ : Y₄.cpu.gpr = X.cpu.gpr := by rw [hg₄, e₃]
    exact p323 c hin hK₄ hA₄ hr₄ (by rw [e₄]; exact hkp) (by rw [e₄]; exact hax) (by rw [e₄]; exact hdi)
      (by rw [e₄]; exact hsi) (by rw [e₄]; exact hdx) h4 h8 hsrc hst hd64 hsp hsp8 hR
  intro hfa Y₄ t₄ hK₄ hA₄ ⟨hr₄, hg₄, _⟩
  rw [hf₃, hP, cond_3, subF_cf] at hfa
  have h4 := jae_f hfa
  simp only [hd8, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod] at h4
  have e₄ : Y₄.cpu.gpr = X.cpu.gpr := by rw [hg₄, e₃]
  -- `cmp dl, 1`, `ja 336`, `jb 305`
  refine c.s_blkV hin (b293 prof) hK₄ hA₄ hr₄ ?_
  refine wpV_reg fun fl hP => wpV_nil ?_
  intro Y₅ t₅ hK₅ hA₅ hr₅ hg₅ hf₅ _
  simp only [gv, Src.val, get2] at hP
  have e₅ : Y₅.cpu.gpr = X.cpu.gpr := by rw [hg₅, e₄]
  rw [e₄] at hP
  refine c.s_jccF hK₅ hA₅ hin (by rw [mc2_length]; decide) hr₅ (d296 prof.feat) (tgt := 336) rfl
    (by rw [mc2_length]; decide) ?_ ?_
  · intro htk Y₆ t₆ hK₆ hA₆ ⟨hr₆, hg₆, _⟩
    rw [hf₅, hP, cond_7, subF_cf, subF_zf] at htk
    have h1 := ja_t htk
    simp only [hd8, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod] at h1
    have e₆ : Y₆.cpu.gpr = X.cpu.gpr := by rw [hg₆, e₅]
    exact p336 c hin hK₆ hA₆ hr₆ (by rw [e₆]; exact hkp) (by rw [e₆]; exact hax) (by rw [e₆]; exact hdi)
      (by rw [e₆]; exact hsi) (by rw [e₆]; exact hdx) h1 h4 hsrc hst hd64 hsp hsp8 hR
  intro hfa Y₆ t₆ hK₆ hA₆ ⟨hr₆, hg₆, _, hf₆⟩
  have hcf : Y₆.cpu.rflags.cf = decide (g₀.rdx.toNat < 1) := by
    rw [hf₆, rfz_cf, hf₅, hP, subF_cf]
    simp only [hd8, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
  rw [hf₅, hP, cond_7, subF_cf, subF_zf] at hfa
  have h1 := ja_f hfa
  simp only [hd8, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod] at h1
  have e₆ : Y₆.cpu.gpr = X.cpu.gpr := by rw [hg₆, e₅]
  refine c.s_jccV hK₆ hA₆ hin (by rw [mc2_length]; decide) hr₆ (d298 prof.feat) (tgt := 305) rfl
    (by rw [mc2_length]; decide) ?_ ?_
  · intro htk Y₇ t₇ hK₇ hA₇ ⟨hr₇, hg₇, _⟩
    rw [cond_2, hcf] at htk
    have h0 := of_decide_eq_true htk
    have e₇ : Y₇.cpu.gpr = X.cpu.gpr := by rw [hg₇, e₆]
    exact p305 c hin hK₇ hA₇ hr₇ (by rw [e₇]; exact hkp) (by rw [e₇]; exact hax) (by rw [e₇]; exact hdi)
      (by rw [e₇]; exact hsi) (by rw [e₇]; exact hdx) (by omega) hsrc hst hd64 hsp hsp8 hR
  intro hfa' Y₇ t₇ hK₇ hA₇ ⟨hr₇, hg₇, _⟩
  rw [cond_2, hcf] at hfa'
  have h0 := Nat.le_of_not_lt (of_decide_eq_false hfa')
  have e₇ : Y₇.cpu.gpr = X.cpu.gpr := by rw [hg₇, e₆]
  exact p300 c hin hK₇ hA₇ hr₇ (by rw [e₇]; exact hkp) (by rw [e₇]; exact hax) (by rw [e₇]; exact hdi)
    (by rw [e₇]; exact hsi) (by rw [e₇]; exact hdx) (by omega) hsrc hst hd64 hsp hsp8 hR

end FV7z.Memcpy
