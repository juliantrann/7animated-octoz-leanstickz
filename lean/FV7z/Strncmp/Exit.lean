import FV7z.Strncmp.Code
import FV7z.Strncmp.Res
import FV7z.Strlen.Run
import FV7z.CpuFeat.Inv
/-!
# `__strncmp_sse2`: the return (PLAN.md G3, `strncmp`)

Every compare of 16 bytes that finds a stop (bytes that differ or a 0) ends at `6192` with the stop's mask in `rdx`:
`bsf rdx, rdx` gives the stop's place `p` in the 16 bytes, `sub r11, rdx; jbe` returns 0 (`6212`) when the bytes
left, `r11`, end at or before it, and otherwise `movzx ecx, [rsi + rdx]; movzx eax, [rdi + rdx]; sub eax, ecx; ret`
returns the difference of the two bytes, 0 just when they are the same (`exit6192`).

- `KpN`, `RetN`, `retN_at`: the registers a call keeps, and the return with an `eax` of which `P` holds.
- `wpV_ldzx8`: `movzx r32, byte [m]` in `wpV`; `ea_ip`: the address `[b + i]`.
- `jbe_ofNat`: `sub; jbe` of two numbers; `zsub_eq_zero`: two zero-extended bytes' difference.
-/
namespace FV7z.Strncmp
open ZellicX86 Decode FV7z.Leaf FV7z.Fn FV7z.Strlen

theorem get11 (g : Gprs) : g.get (regOf 11) = g.r11 := rfl
theorem set11 (g : Gprs) (v : BitVec 64) : g.set (regOf 11) v = { g with r11 := v } := rfl

/-- The registers a call keeps, as at the call. -/
def KpN (g₀ g : Gprs) : Prop :=
  g.rsp = g₀.rsp ∧ g.rbx = g₀.rbx ∧ g.rbp = g₀.rbp ∧ g.r12 = g₀.r12 ∧ g.r13 = g₀.r13 ∧ g.r14 = g₀.r14 ∧
    g.r15 = g₀.r15

/-- What the call returns to, from registers `g₀` at the call, with an `eax` of which `P` holds. -/
def RetN (prof : Profile) (F : Footprint) (Wl : List Rgn) (L : List (Addr × List Byte)) (s₀ : State) (o : Oracle)
    (gev : List Event) (gP : State → Nat → List Event → Prop) (gE : Outcome → List Event → Prop) (V : Addr → Byte)
    (g₀ : Gprs) (P : BitVec 32 → Prop) : Prop :=
  (∀ i < 8, Foot F.data (Addr.add g₀.rsp i)) ∧ ∃ (e₂ : Addr) (code₂ : List Byte) (j₂ : Nat), CodeIn L e₂ code₂ ∧
    j₂ < code₂.length ∧ ofBytesLE 64 ((byteAddrs g₀.rsp 8).map V) = e₂.add j₂ ∧
    ∀ Z t', KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V → Z.cpu.rip = e₂.add j₂ → Z.cpu.gpr.rsp = g₀.rsp + 8 →
      P (Z.cpu.gpr.rax.setWidth 32) → Z.cpu.gpr.rbx = g₀.rbx → Z.cpu.gpr.rbp = g₀.rbp →
      Z.cpu.gpr.r12 = g₀.r12 → Z.cpu.gpr.r13 = g₀.r13 → Z.cpu.gpr.r14 = g₀.r14 → Z.cpu.gpr.r15 = g₀.r15 →
      GoG prof L o gev gP gE Z t'

section
variable {F : Footprint} {Wl : List Rgn}

/-- `movzx r32, byte [m]`, `m` the address `a`. -/
theorem wpV_ldzx8 {r : Nat} {b i : Option Nat} {sc d : Nat} {ops : List VOp}
    {Q : Gprs → Rflags → XRegs → (Addr → Byte) → Prop} {g : Gprs} {f : Rflags} {x : XRegs} {V : Addr → Byte}
    {a : Addr} (he : eaG g b i sc d = a) (hf : Foot F.data a)
    (k : wpV F Wl ops Q (wr g r ((V a).setWidth 32)) (rfz f) x V) :
    wpV F Wl (.op (Op.ldzx 8 r b i sc d) :: ops) Q g f x V := by
  refine ⟨rfl, fun j hj => ?_, fun fl hfl => ?_⟩
  · show Foot F.data ((eaG g b i sc d).add j)
    rw [he, show j = 0 by omega, addr_add_zero]
    exact hf
  · obtain rfl : fl = rfz f := hfl
    show wpV F Wl ops Q (wr g r ((ofBytesLE 8 ((byteAddrs (eaG g b i sc d) 1).map V)).setWidth 32)) (rfz f) x V
    rw [he, CpuFeat.rd1]
    exact k

end

/-- The address `[b + i]`, `i` the number `k`. -/
theorem ea_ip {g : Gprs} {b i : Nat} {a : Addr} {k : Nat} (hb : g.get (regOf b) = a)
    (hi : g.get (regOf i) = BitVec.ofNat 64 k) : eaG g (some b) (some i) 1 0 = a.add k := by
  simp only [eaG, optV, hb, hi, Addr.add]
  rw [BitVec.mul_one, BitVec.add_zero]

/-- `sub` of `p` from `R`, then `jbe`: taken just when `R ≤ p`. -/
theorem jbe_ofNat {R p : Nat} (hR : R < 2 ^ 64) (hp : p < 2 ^ 64) :
    (decide ((BitVec.ofNat 64 R).toNat < (BitVec.ofNat 64 p).toNat) ||
      decide (BitVec.ofNat 64 R = BitVec.ofNat 64 p)) = decide (R ≤ p) := by
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hR, Nat.mod_eq_of_lt hp]
  by_cases h : R < p
  · rw [decide_eq_true h, decide_eq_true (Nat.le_of_lt h)]
    rfl
  · by_cases h' : R = p
    · subst h'
      rw [decide_eq_false h, decide_eq_true rfl, decide_eq_true (Nat.le_refl _)]
      rfl
    · have hne : ¬ BitVec.ofNat 64 R = BitVec.ofNat 64 p := fun e => h' (by
        have := congrArg BitVec.toNat e
        rwa [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hR, Nat.mod_eq_of_lt hp] at this)
      rw [decide_eq_false h, decide_eq_false hne, decide_eq_false (by omega : ¬ R ≤ p)]
      rfl

/-- The difference of two bytes zero-extended: 0 just when they are the same. -/
theorem zsub_eq_zero (x y : Byte) : x.setWidth 32 - y.setWidth 32 = 0 ↔ x = y := by
  rw [sub_eq_zero_iff]
  constructor
  · intro h
    apply BitVec.eq_of_toNat_eq
    have e := congrArg BitVec.toNat h
    rw [BitVec.toNat_setWidth, BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_trans x.isLt (by decide)),
      Nat.mod_eq_of_lt (Nat.lt_trans y.isLt (by decide))] at e
    exact e
  · rintro rfl
    rfl

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle} {F : Footprint} {Wl : List Rgn}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {e' : Addr} {V : Addr → Byte}

/-- A `ret` with an `eax` of which `P` holds. -/
theorem retN_at (c : Seg prof F Wl L s₀ o) (hin : CodeIn L e' scm) {j : Nat} (hj : j < scm.length)
    (hd : Dec prof.feat scm j (FV7z.mk .ret 64 [] 1)) {Y : State} {t : Nat} {g₀ : Gprs} {P : BitVec 32 → Prop}
    (hK : KeptW Wl s₀ Y) (hA : Agree F Y.proc.mm.mem V) (hrip : Y.cpu.rip = e'.add j) (hkp : KpN g₀ Y.cpu.gpr)
    (hax : P (Y.cpu.gpr.rax.setWidth 32)) (hR : RetN prof F Wl L s₀ o gev gP gE V g₀ P) :
    GoG prof L o gev gP gE Y t := by
  obtain ⟨hl, e₂, code₂, j₂, hin₂, h₂, hra, K⟩ := hR
  obtain ⟨hsp, hbx, hbp, h12, h13, h14, h15⟩ := hkp
  refine c.s_ret hK hA hin hj hrip hd (by rw [hsp]; exact hl) hin₂ h₂ (by rw [hsp]; exact hra) ?_
  rintro Z t' hKZ hAZ ⟨hrZ, hgZ⟩
  refine K Z t' hKZ hAZ hrZ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;> rw [hgZ]
  · exact congrArg (· + (8 : BitVec 64)) hsp
  · exact hax
  · exact hbx
  · exact hbp
  · exact h12
  · exact h13
  · exact h14
  · exact h15

/-- From `6192`: `rdx` the mask of a stop at place `p` of the 16 bytes at offset `q` of the strings at `a` (in `rdi`)
and `b` (in `rsi`), `r11` the `R` bytes left of `n` (the bytes before the stop the same up to `n` only: past `n` the
mask is anything); what is returned is what `strncmp` of `a`, `b`, `n` may return, and so of `P`. -/
theorem exit6192 (c : Seg prof F Wl L s₀ o) (hin : CodeIn L e' scm) {Y : State} {t : Nat} {g₀ : Gprs}
    {a b : Addr} {q R p n : Nat} {P : BitVec 32 → Prop}
    (hK : KeptW Wl s₀ Y) (hA : Agree F Y.proc.mm.mem V) (hrip : Y.cpu.rip = e'.add 6192) (hkp : KpN g₀ Y.cpu.gpr)
    (hdi : Y.cpu.gpr.rdi = a.add q) (hsi : Y.cpu.gpr.rsi = b.add q)
    (h11 : Y.cpu.gpr.r11 = BitVec.ofNat 64 R) (hR64 : R < 2 ^ 64) (hn : q + R = n)
    (hnz : Y.cpu.gpr.rdx ≠ 0) (hp : lowestSetBit Y.cpu.gpr.rdx = p) (hp64 : p < 64)
    (hsame : Same V a b (q + min p R))
    (hstop : p < R → ¬ (V (a.add (q + p)) = V (b.add (q + p)) ∧ V (a.add (q + p)) ≠ 0))
    (hfa : p < R → Foot F.data (a.add (q + p))) (hfb : p < R → Foot F.data (b.add (q + p)))
    (hP : ∀ r, NRes V a b n r → P r) (hR : RetN prof F Wl L s₀ o gev gP gE V g₀ P) :
    GoG prof L o gev gP gE Y t := by
  -- `bsf rdx, rdx`
  have hnz' : rv Y 64 2 ≠ 0 := by
    simp only [rv, get2, BitVec.setWidth_eq]
    exact hnz
  refine c.s_bsf64 hK hA hin (lt_scm (by decide)) hrip (d6192 prof.feat) hnz' ?_
  rintro Y₁ t₁ hK₁ hA₁ ⟨hr₁, hg₁⟩
  simp only [rv, get2, BitVec.setWidth_eq, hp, set_rdx] at hg₁
  have hdx₁ : Y₁.cpu.gpr.rdx = BitVec.ofNat 64 p := by simp only [hg₁]
  have h11₁ : Y₁.cpu.gpr.r11 = BitVec.ofNat 64 R := by simp only [hg₁]; exact h11
  have hdi₁ : Y₁.cpu.gpr.rdi = a.add q := by simp only [hg₁]; exact hdi
  have hsi₁ : Y₁.cpu.gpr.rsi = b.add q := by simp only [hg₁]; exact hsi
  have hkp₁ : KpN g₀ Y₁.cpu.gpr := by simp only [KpN, hg₁]; exact hkp
  -- `sub r11, rdx`
  refine c.s_blkV hin (b6196 prof) hK₁ hA₁ hr₁ ?_
  refine wpV_reg fun fl hfl => wpV_nil ?_
  intro Y₂ t₂ hK₂ hA₂ hr₂ hg₂ hf₂ _
  have hfl : fl = subF (rfz Y₁.cpu.rflags) (gv Y₁.cpu.gpr 64 11) (Src.val 64 Y₁.cpu.gpr (.r 2)) := hfl
  have hc : Y₂.cpu.rflags.cond 6 = decide (R ≤ p) := by
    rw [hf₂, hfl, cond_6, subF_cf, subF_zf]
    simp only [Src.val, gv, get11, get2, BitVec.setWidth_eq, h11₁, hdx₁]
    exact jbe_ofNat hR64 (Nat.lt_trans hp64 (by decide))
  simp only [wr, gv, Src.val, get11, get2, BitVec.setWidth_eq, set11] at hg₂
  have hdi₂ : Y₂.cpu.gpr.rdi = a.add q := by simp only [hg₂]; exact hdi₁
  have hsi₂ : Y₂.cpu.gpr.rsi = b.add q := by simp only [hg₂]; exact hsi₁
  have hdx₂ : Y₂.cpu.gpr.rdx = BitVec.ofNat 64 p := by simp only [hg₂]; exact hdx₁
  have hkp₂ : KpN g₀ Y₂.cpu.gpr := by simp only [KpN, hg₂]; exact hkp₁
  -- `jbe 6212`
  refine c.s_jcc (tgt := 6212) hK₂ hA₂ hin (lt_scm (by decide)) hr₂ (d6199 prof.feat) (by decide)
    (lt_scm (by decide)) ?_ ?_
  · -- no stop before `n`: `xor eax, eax; ret`
    intro hcc
    have hle : R ≤ p := by
      rw [hc] at hcc
      exact of_decide_eq_true hcc
    rintro Y₃ t₃ hK₃ hA₃ ⟨hr₃, hg₃⟩
    have hkp₃ : KpN g₀ Y₃.cpu.gpr := by rw [hg₃]; exact hkp₂
    refine c.s_blkV hin (b6212 prof) hK₃ hA₃ hr₃ ?_
    refine wpV_reg fun _ _ => wpV_nil ?_
    intro Y₄ t₄ hK₄ hA₄ hr₄ hg₄ _ _
    have hkp₄ : KpN g₀ Y₄.cpu.gpr := by simp only [KpN, hg₄, wr, set_rax]; exact hkp₃
    have hax₄ : Y₄.cpu.gpr.rax.setWidth 32 = 0 := by
      simp only [hg₄, wr, gv, Src.val, set_rax, sw_64_32, BitVec.xor_self]
      all_goals rfl
    refine retN_at c hin (lt_scm (by decide)) (d6214 prof.feat) hK₄ hA₄ hr₄ hkp₄ ?_ hR
    rw [hax₄]
    exact hP 0 (nres_zero hsame (by omega))
  · -- the stop before `n`: the difference of its bytes
    intro hcc
    have hlt : p < R := by
      rw [hc] at hcc
      exact Nat.lt_of_not_le (of_decide_eq_false hcc)
    rintro Y₃ t₃ hK₃ hA₃ ⟨hr₃, hg₃⟩
    have hkp₃ : KpN g₀ Y₃.cpu.gpr := by rw [hg₃]; exact hkp₂
    have hdi₃ : Y₃.cpu.gpr.rdi = a.add q := by rw [hg₃]; exact hdi₂
    have hsi₃ : Y₃.cpu.gpr.rsi = b.add q := by rw [hg₃]; exact hsi₂
    have hdx₃ : Y₃.cpu.gpr.rdx = BitVec.ofNat 64 p := by rw [hg₃]; exact hdx₂
    refine c.s_blkV hin (b6201 prof) hK₃ hA₃ hr₃ ?_
    refine wpV_ldzx8 ((ea_ip (by rw [get6]; exact hsi₃) (by rw [get2]; exact hdx₃)).trans (addr_add_add b q p))
      (hfb hlt) <| wpV_ldzx8 ((ea_ip (by simp only [wr, set_rcx, get7]; exact hdi₃)
        (by simp only [wr, set_rcx, get2]; exact hdx₃)).trans (addr_add_add a q p)) (hfa hlt) <|
      wpV_reg fun _ _ => wpV_nil ?_
    intro Y₄ t₄ hK₄ hA₄ hr₄ hg₄ _ _
    have hkp₄ : KpN g₀ Y₄.cpu.gpr := by simp only [KpN, hg₄, wr, set_rax, set_rcx]; exact hkp₃
    have hax₄ : Y₄.cpu.gpr.rax.setWidth 32 =
        (V (a.add (q + p))).setWidth 32 - (V (b.add (q + p))).setWidth 32 := by
      simp only [hg₄, wr, gv, Src.val, set_rax, set_rcx, get0, get1, sw_64_32, subR_eq]
    refine retN_at c hin (lt_scm (by decide)) (d6211 prof.feat) hK₄ hA₄ hr₄ hkp₄ ?_ hR
    rw [hax₄]
    exact hP _ (nres_at (by omega) (by rwa [Nat.min_eq_left hlt.le] at hsame) (hstop hlt) (zsub_eq_zero _ _))

end FV7z.Strncmp
