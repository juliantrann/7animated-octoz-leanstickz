import FV7z.Strncmp.Align
/-!
# `__strncmp_sse2`: the exits of the loops (PLAN.md G3, `strncmp`)

A loop that finds a stop in its 16 bytes leaves by `6160` (`lea rax, [r9 + rcx - 16]`, the offset into `rdi`'s string
of the chunk at `rcx` of `rsi`'s, `exit6160`) or straight to `6165` (`exit6165`): `lea rdi, [rdi + rax];
lea rsi, [rsi + rcx]` point at the chunk in each string, and `test r8d, r8d; je 6192` swaps them back first when
`align` swapped them (`r8d = 0xffff`, `xchg rdi, rsi`), so that `exit6192` sees `rdi` in the first string again. The
strings are `x` (`rdi`'s) and `y` (`rsi`'s), `a` and `b` in order or swapped (`sw`); what the loops know of `x` and
`y` is what `exit6192` asks of `a` and `b`, the stop being the same either way (`Same.comm`, `nres_comm`).

- `stop_comm`: a stop of `b` and `a` is one of `a` and `b`.
- `lea_m16`: `r9 + rcx - 16` of numbers.
-/
namespace FV7z.Strncmp
open ZellicX86 Decode FV7z.Leaf FV7z.Fn FV7z.Strlen

theorem stop_comm {V : Addr → Byte} {u v : Addr}
    (h : ¬ (V u = V v ∧ V u ≠ 0)) : ¬ (V v = V u ∧ V v ≠ 0) :=
  fun ⟨he, hz⟩ => h ⟨he.symm, he ▸ hz⟩

theorem lea_m16 {k₉ kc : Nat} (h16 : 16 ≤ k₉ + kc) :
    BitVec.ofNat 64 k₉ + BitVec.ofNat 64 kc * BitVec.ofNat 64 1 + BitVec.ofNat 64 18446744073709551600 =
      BitVec.ofNat 64 (k₉ + kc - 16) := by
  have e : BitVec.ofNat 64 18446744073709551600 = -BitVec.ofNat 64 16 := by decide
  rw [e, ← BitVec.sub_eq_add_neg, BitVec.sub_eq_iff_eq_add, BitVec.ofNat_add_ofNat,
    show k₉ + kc - 16 + 16 = k₉ + kc by omega, BitVec.mul_one]
  exact BitVec.ofNat_add_ofNat _ _

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle} {F : Footprint} {Wl : List Rgn}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {e' : Addr} {V : Addr → Byte}

/-- From `6165`: `rdi + rax` and `rsi + rcx` the 16 bytes at offset `q` of the strings `x` and `y`, `a` and `b` in
order or swapped (`sw`, `r8`), `rdx` the mask of a stop at their place `p`, `r11` the `R` bytes left of `n`: what is
returned is what `strncmp` of `a`, `b`, `n` may return, and so of `P`. -/
theorem exit6165 (c : Seg prof F Wl L s₀ o) (hin : CodeIn L e' scm) {Y : State} {t : Nat} {g₀ : Gprs}
    {a b x y : Addr} {q R p n ka kc : Nat} {sw : Bool} {P : BitVec 32 → Prop}
    (hK : KeptW Wl s₀ Y) (hA : Agree F Y.proc.mm.mem V) (hrip : Y.cpu.rip = e'.add 6165) (hkp : KpN g₀ Y.cpu.gpr)
    (hax : Y.cpu.gpr.rax = BitVec.ofNat 64 ka) (hcx : Y.cpu.gpr.rcx = BitVec.ofNat 64 kc)
    (hdi : Addr.add Y.cpu.gpr.rdi ka = x.add q) (hsi : Addr.add Y.cpu.gpr.rsi kc = y.add q)
    (h8 : Y.cpu.gpr.r8 = if sw then BitVec.ofNat 64 65535 else 0)
    (hxy : sw = false ∧ x = a ∧ y = b ∨ sw = true ∧ x = b ∧ y = a)
    (h11 : Y.cpu.gpr.r11 = BitVec.ofNat 64 R) (hR64 : R < 2 ^ 64) (hn : q + R = n)
    (hnz : Y.cpu.gpr.rdx ≠ 0) (hp : lowestSetBit Y.cpu.gpr.rdx = p) (hp64 : p < 64)
    (hsame : Same V x y (q + p))
    (hstop : p < R → ¬ (V (x.add (q + p)) = V (y.add (q + p)) ∧ V (x.add (q + p)) ≠ 0))
    (hfx : p < R → Foot F.data (x.add (q + p))) (hfy : p < R → Foot F.data (y.add (q + p)))
    (hP : ∀ r, NRes V a b n r → P r) (hR : RetN prof F Wl L s₀ o gev gP gE V g₀ P) :
    GoG prof L o gev gP gE Y t := by
  -- `lea rdi, [rdi + rax]; lea rsi, [rsi + rcx]; test r8d, r8d`
  refine c.s_blkV hin (b6165 prof) hK hA hrip ?_
  refine wpV_reg fun _ _ => wpV_reg fun _ _ => wpV_reg fun fl hfl => wpV_nil ?_
  intro Y₁ t₁ hK₁ hA₁ hr₁ hg₁ hf₁ _
  have hz : Y₁.cpu.rflags.cond 4 = !sw := by
    rw [hf₁, cond4_log hfl]
    simp only [gv, Src.val, wr, set_rdi, set_rsi, get_r8n, BitVec.and_self, h8]
    cases sw <;> decide
  simp only [wr, eaG, optV, set_rdi, set_rsi, get0, get1, get6, get7, BitVec.setWidth_eq, hax, hcx] at hg₁
  have hdi₁ : Y₁.cpu.gpr.rdi = x.add q := by
    rw [← hdi, hg₁]
    simp only [Addr.add, BitVec.mul_one, BitVec.add_zero]
  have hsi₁ : Y₁.cpu.gpr.rsi = y.add q := by
    rw [← hsi, hg₁]
    simp only [Addr.add, BitVec.mul_one, BitVec.add_zero]
  have hkp₁ : KpN g₀ Y₁.cpu.gpr := by simp only [KpN, hg₁]; exact hkp
  have h11₁ : Y₁.cpu.gpr.r11 = BitVec.ofNat 64 R := by simp only [hg₁]; exact h11
  have hdx₁ : Y₁.cpu.gpr.rdx = Y.cpu.gpr.rdx := by simp only [hg₁]
  -- `je 6192`
  refine c.s_jcc (tgt := 6192) hK₁ hA₁ hin (lt_scm (by decide)) hr₁ (d6176 prof.feat) (by decide)
    (lt_scm (by decide)) ?_ ?_
  · -- in order
    intro hcc
    obtain ⟨-, rfl, rfl⟩ : sw = false ∧ x = a ∧ y = b := by
      rcases hxy with h | ⟨rfl, -⟩
      · exact h
      · rw [hz] at hcc
        exact nomatch hcc
    rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
    refine exit6192 c hin hK₂ hA₂ hr₂ (by rw [hg₂]; exact hkp₁) (by rw [hg₂]; exact hdi₁)
      (by rw [hg₂]; exact hsi₁) (by rw [hg₂]; exact h11₁) hR64 hn (by rw [hg₂, hdx₁]; exact hnz)
      (by rw [hg₂, hdx₁]; exact hp) hp64 hsame hstop hfx hfy hP hR
  · -- swapped: `xchg rdi, rsi` first
    intro hcc
    obtain ⟨-, rfl, rfl⟩ : sw = true ∧ x = b ∧ y = a := by
      rcases hxy with ⟨rfl, -⟩ | h
      · rw [hz] at hcc
        exact nomatch hcc
      · exact h
    rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
    refine c.s_blkV hin (b6178 prof) hK₂ hA₂ hr₂ ?_
    refine wpV_reg fun _ _ => wpV_reg fun _ _ => wpV_nil ?_
    intro Y₃ t₃ hK₃ hA₃ hr₃ hg₃ _ _
    simp only [wr, gv, set_rdi, set_rsi, get6, get7, BitVec.setWidth_eq] at hg₃
    refine exit6192 c hin hK₃ hA₃ hr₃ (by simp only [KpN, hg₃, hg₂]; exact hkp₁)
      (by simp only [hg₃, hg₂]; exact hsi₁) (by simp only [hg₃, hg₂]; exact hdi₁)
      (by simp only [hg₃, hg₂]; exact h11₁) hR64 hn (by simp only [hg₃, hg₂, hdx₁]; exact hnz)
      (by simp only [hg₃, hg₂, hdx₁]; exact hp) hp64 hsame.comm (fun h => stop_comm (hstop h)) hfy hfx hP hR

/-- From `6160`: `lea rax, [r9 + rcx - 16]`, then `exit6165`. -/
theorem exit6160 (c : Seg prof F Wl L s₀ o) (hin : CodeIn L e' scm) {Y : State} {t : Nat} {g₀ : Gprs}
    {a b x y : Addr} {q R p n k₉ kc : Nat} {sw : Bool} {P : BitVec 32 → Prop}
    (hK : KeptW Wl s₀ Y) (hA : Agree F Y.proc.mm.mem V) (hrip : Y.cpu.rip = e'.add 6160) (hkp : KpN g₀ Y.cpu.gpr)
    (h9 : Y.cpu.gpr.r9 = BitVec.ofNat 64 k₉) (hcx : Y.cpu.gpr.rcx = BitVec.ofNat 64 kc)
    (h16 : 16 ≤ k₉ + kc)
    (hdi : Addr.add Y.cpu.gpr.rdi (k₉ + kc - 16) = x.add q) (hsi : Addr.add Y.cpu.gpr.rsi kc = y.add q)
    (h8 : Y.cpu.gpr.r8 = if sw then BitVec.ofNat 64 65535 else 0)
    (hxy : sw = false ∧ x = a ∧ y = b ∨ sw = true ∧ x = b ∧ y = a)
    (h11 : Y.cpu.gpr.r11 = BitVec.ofNat 64 R) (hR64 : R < 2 ^ 64) (hn : q + R = n)
    (hnz : Y.cpu.gpr.rdx ≠ 0) (hp : lowestSetBit Y.cpu.gpr.rdx = p) (hp64 : p < 64)
    (hsame : Same V x y (q + p))
    (hstop : p < R → ¬ (V (x.add (q + p)) = V (y.add (q + p)) ∧ V (x.add (q + p)) ≠ 0))
    (hfx : p < R → Foot F.data (x.add (q + p))) (hfy : p < R → Foot F.data (y.add (q + p)))
    (hP : ∀ r, NRes V a b n r → P r) (hR : RetN prof F Wl L s₀ o gev gP gE V g₀ P) :
    GoG prof L o gev gP gE Y t := by
  refine c.s_blkV hin (b6160 prof) hK hA hrip ?_
  refine wpV_reg fun _ _ => wpV_nil ?_
  intro Y₁ t₁ hK₁ hA₁ hr₁ hg₁ _ _
  simp only [wr, set_rax] at hg₁
  refine exit6165 (ka := k₉ + kc - 16) (kc := kc) c hin hK₁ hA₁ hr₁ (by simp only [KpN, hg₁]; exact hkp)
    (by simp only [hg₁, eaG, optV, get1, get_r9n, BitVec.setWidth_eq, h9, hcx]; exact lea_m16 h16)
    (by simp only [hg₁]; exact hcx) (by simp only [hg₁]; exact hdi) (by simp only [hg₁]; exact hsi)
    (by simp only [hg₁]; exact h8) hxy (by simp only [hg₁]; exact h11) hR64 hn (by simp only [hg₁]; exact hnz)
    (by simp only [hg₁]; exact hp) hp64 hsame hstop hfx hfy hP hR

end FV7z.Strncmp
