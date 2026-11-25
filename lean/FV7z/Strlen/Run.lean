import FV7z.Strlen.Code
import FV7z.Strlen.Mask
import FV7z.Strlen.Steps
/-!
# `__strlen_sse2`, run (PLAN.md M, the PLT contracts)

The stretches of `Strlen/Code.lean` run, with what their masks say (`Strlen/Mask.lean`). `p` is `rdi` at the call and
`n` the string's length. Here the end: at `+340` `rax` is a 64-aligned `B` with `p ≤ B ≤ p + n < B + 64`, and
`xmm1`–`xmm3` are 0; the four masks of `[B, B + 64)` joined have `p + n - B` as lowest set bit, and `rax` comes back as
`B + (p + n - B) - p = n`.
-/
namespace FV7z
open ZellicX86 Decode FV7z.Leaf FV7z.Fn

section
variable {F : Footprint} {Wl : List Rgn}

theorem wpV_nil {Q : Gprs → Rflags → XRegs → (Addr → Byte) → Prop} {g : Gprs} {f : Rflags} {x : XRegs}
    {V : Addr → Byte} (h : Q g f x V) : wpV F Wl [] Q g f x V := h

theorem wpV_reg {h : Gprs → Rflags → Gprs} {P : Gprs → Rflags → Rflags → Prop} {ops : List VOp}
    {Q : Gprs → Rflags → XRegs → (Addr → Byte) → Prop} {g : Gprs} {f : Rflags} {x : XRegs} {V : Addr → Byte}
    (k : ∀ fl, P g f fl → wpV F Wl ops Q (h g f) fl x V) : wpV F Wl (.op (.reg h P) :: ops) Q g f x V :=
  ⟨rfl, k⟩

theorem wpV_v {n : Nat} {al : Bool} {ea : Gprs → Addr} {hg : Gprs → XRegs → List Byte → Gprs}
    {hx : Gprs → XRegs → List Byte → XRegs} {ops : List VOp} {Q : Gprs → Rflags → XRegs → (Addr → Byte) → Prop}
    {g : Gprs} {f : Rflags} {x : XRegs} {V : Addr → Byte}
    (h1 : ∀ i < n, Foot F.data ((ea g).add i)) (h2 : al = true → (ea g).toNat % 16 = 0)
    (k : wpV F Wl ops Q (hg g x ((byteAddrs (ea g) n).map V)) (rfz f) (hx g x ((byteAddrs (ea g) n).map V)) V) :
    wpV F Wl (.v n al ea hg hx :: ops) Q g f x V :=
  ⟨h1, h2, k⟩

theorem wpV_v0 {ea : Gprs → Addr} {hg : Gprs → XRegs → List Byte → Gprs} {hx : Gprs → XRegs → List Byte → XRegs}
    {ops : List VOp} {Q : Gprs → Rflags → XRegs → (Addr → Byte) → Prop} {g : Gprs} {f : Rflags} {x : XRegs}
    {V : Addr → Byte} (k : wpV F Wl ops Q (hg g x []) (rfz f) (hx g x []) V) :
    wpV F Wl (.v 0 false ea hg hx :: ops) Q g f x V :=
  ⟨fun _ h => absurd h (Nat.not_lt_zero _), (fun h => nomatch h), k⟩

end

namespace Strlen

/-! ## Addresses -/

theorem addr_eq {a b : Addr} {i j : Nat} (h : a.toNat + i = b.toNat + j) : a.add i = b.add j := by
  apply BitVec.eq_of_toNat_eq
  simp only [Addr.add, BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

theorem al16 {B : Addr} (hB : B.toNat % 64 = 0) {d : Nat} (hd : d % 16 = 0) :
    (B + BitVec.ofNat 64 d).toNat % 16 = 0 := by
  have := B.isLt
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

theorem add_toNat64 {B : Addr} (hB : B.toNat % 64 = 0) {k : Nat} (hk : k < 64) : (B.add k).toNat = B.toNat + k := by
  have := B.isLt
  simp only [Addr.add, BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

/-- The 64 bytes of a 64-aligned block between the string's first page and its last are to read. -/
theorem foot64 {F : Footprint} {p B : Addr} {n : Nat}
    (hft : ∀ x : Addr, p.toNat / 4096 ≤ x.toNat / 4096 → x.toNat / 4096 ≤ (p.toNat + n) / 4096 → Foot F.data x)
    (hB : B.toNat % 64 = 0) (h1 : p.toNat < B.toNat + 64) (h2 : B.toNat ≤ p.toNat + n) :
    ∀ k < 64, Foot F.data (B.add k) := by
  intro k hk
  have hk' := add_toNat64 hB hk
  apply hft <;> rw [hk'] <;> omega

/-- A load of 16 of the block's bytes. -/
theorem foot16 {F : Footprint} {B : Addr} (h : ∀ k < 64, Foot F.data (B.add k)) {d : Nat} (hd : d + 16 ≤ 64) :
    ∀ i < 16, Foot F.data ((B + BitVec.ofNat 64 d).add i) := by
  intro i hi
  have := h (d + i) (by omega)
  rw [← addr_add_add] at this
  exact this

/-- Bit `i` of the mask of the 16 bytes at `B + d`: whether byte `i + d` from `B` is 0. -/
theorem zbit (V : Addr → Byte) (B : Addr) (d i : Nat) :
    (pmsk (peqb 0 (rd16 V (B + BitVec.ofNat 64 d)))).getLsbD i =
      (decide (i < 16) && decide (V (B.add (i + d)) = 0)) := by
  rw [getLsbD_zmask']
  by_cases hi : i < 16
  · rw [lane_rd16 _ _ hi, show B + BitVec.ofNat 64 d = B.add d from rfl, addr_add_add, Nat.add_comm d i]
  · rw [decide_eq_false hi, Bool.false_and, Bool.false_and]

/-- `B + k - p` is `n` when `B + k = p + n`. -/
theorem rax_fin {B p : Addr} {k n : Nat} (h : B.toNat + k = p.toNat + n) (hn : p.toNat + n < 2 ^ 64) :
    subR (addR B (BitVec.ofNat 64 k)) p = BitVec.ofNat 64 n := by
  have h0 : (BitVec.ofBool false).setWidth 64 = (0 : BitVec 64) := by decide
  simp only [subR, addR, h0, BitVec.sub_zero]
  apply BitVec.eq_of_toNat_eq
  have := p.isLt
  have := B.isLt
  simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

/-! ## Registers by name -/

theorem get0 (g : Gprs) : g.get (regOf 0) = g.rax := rfl
theorem get1 (g : Gprs) : g.get (regOf 1) = g.rcx := rfl
theorem get2 (g : Gprs) : g.get (regOf 2) = g.rdx := rfl
theorem get6 (g : Gprs) : g.get (regOf 6) = g.rsi := rfl
theorem get7 (g : Gprs) : g.get (regOf 7) = g.rdi := rfl
theorem get8 (g : Gprs) : g.get (regOf 8) = g.r8 := rfl

/-! ## The call -/

/-- The registers a call keeps, and `rdi`, as at the call. -/
def Kp (g₀ g : Gprs) : Prop :=
  g.rdi = g₀.rdi ∧ g.rsp = g₀.rsp ∧ g.rbx = g₀.rbx ∧ g.rbp = g₀.rbp ∧ g.r12 = g₀.r12 ∧ g.r13 = g₀.r13 ∧
    g.r14 = g₀.r14 ∧ g.r15 = g₀.r15

/-- What the call returns to, from registers `g₀` at the call: `LenAt`'s continuation, its return address in code. -/
def Ret (prof : Profile) (F : Footprint) (Wl : List Rgn) (L : List (Addr × List Byte)) (s₀ : State) (o : Oracle)
    (gev : List Event) (gP : State → Nat → List Event → Prop) (gE : Outcome → List Event → Prop) (V : Addr → Byte)
    (g₀ : Gprs) (n : Nat) : Prop :=
  (∀ i < 8, Foot F.data (Addr.add g₀.rsp i)) ∧ ∃ (e₂ : Addr) (code₂ : List Byte) (j₂ : Nat), CodeIn L e₂ code₂ ∧
    j₂ < code₂.length ∧ ofBytesLE 64 ((byteAddrs g₀.rsp 8).map V) = e₂.add j₂ ∧
    ∀ Z t', KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V → Z.cpu.rip = e₂.add j₂ → Z.cpu.gpr.rsp = g₀.rsp + 8 →
      Z.cpu.gpr.rax = BitVec.ofNat 64 n → Z.cpu.gpr.rbx = g₀.rbx → Z.cpu.gpr.rbp = g₀.rbp →
      Z.cpu.gpr.r12 = g₀.r12 → Z.cpu.gpr.r13 = g₀.r13 → Z.cpu.gpr.r14 = g₀.r14 → Z.cpu.gpr.r15 = g₀.r15 →
      GoG prof L o gev gP gE Z t'

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle} {F : Footprint} {Wl : List Rgn}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {e' : Addr} {V : Addr → Byte}

/-- A `ret` with `rax` `n`. -/
theorem ret_at (c : Seg prof F Wl L s₀ o) (hin : CodeIn L e' sl2) {j : Nat} (hj : j < sl2.length)
    (hd : Dec prof.feat sl2 j (FV7z.mk .ret 64 [] 1)) {Y : State} {t : Nat} {g₀ : Gprs} {n : Nat}
    (hK : KeptW Wl s₀ Y) (hA : Agree F Y.proc.mm.mem V) (hrip : Y.cpu.rip = e'.add j) (hkp : Kp g₀ Y.cpu.gpr)
    (hax : Y.cpu.gpr.rax = BitVec.ofNat 64 n) (hR : Ret prof F Wl L s₀ o gev gP gE V g₀ n) :
    GoG prof L o gev gP gE Y t := by
  obtain ⟨hl, e₂, code₂, j₂, hin₂, h₂, hra, K⟩ := hR
  obtain ⟨_, hsp, hbx, hbp, h12, h13, h14, h15⟩ := hkp
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

/-- From `+340`: the block `B` in `rax` has the string's 0, `xmm1`–`xmm3` are 0. -/
theorem exit340 (c : Seg prof F Wl L s₀ o) (hin : CodeIn L e' sl2) {Y : State} {t : Nat} {g₀ : Gprs} {n : Nat}
    (hK : KeptW Wl s₀ Y) (hA : Agree F Y.proc.mm.mem V) (hrip : Y.cpu.rip = e'.add 340) (hkp : Kp g₀ Y.cpu.gpr)
    (hx1 : xsOf Y.cpu.vec.zmm (xmmOf 1) = 0) (hx2 : xsOf Y.cpu.vec.zmm (xmmOf 2) = 0)
    (hx3 : xsOf Y.cpu.vec.zmm (xmmOf 3) = 0)
    (hB : Y.cpu.gpr.rax.toNat % 64 = 0) (hpB : g₀.rdi.toNat ≤ Y.cpu.gpr.rax.toNat)
    (hge : Y.cpu.gpr.rax.toNat ≤ g₀.rdi.toNat + n) (hlt : g₀.rdi.toNat + n < Y.cpu.gpr.rax.toNat + 64)
    (hov : g₀.rdi.toNat + n < 2 ^ 64)
    (hnz : ∀ k < n, V (Addr.add g₀.rdi k) ≠ 0) (hz : V (Addr.add g₀.rdi n) = 0)
    (hft : ∀ x : Addr, g₀.rdi.toNat / 4096 ≤ x.toNat / 4096 → x.toNat / 4096 ≤ (g₀.rdi.toNat + n) / 4096 →
      Foot F.data x)
    (hR : Ret prof F Wl L s₀ o gev gP gE V g₀ n) : GoG prof L o gev gP gE Y t := by
  have hF := foot64 hft hB (by omega) hge
  have hal : ∀ d, d % 16 = 0 → d < 64 → true = true → (Y.cpu.gpr.rax + BitVec.ofNat 64 d).toNat % 16 = 0 :=
    fun d h1 _ _ => al16 hB h1
  refine c.s_blkV hin (b340 prof) hK hA hrip ?_
  refine wpV_v0 (wpV_v (foot16 hF (d := 0) (by omega)) (hal 0 rfl (by omega))
    (wpV_v (foot16 hF (d := 16) (by omega)) (hal 16 rfl (by omega))
    (wpV_v (foot16 hF (d := 32) (by omega)) (hal 32 rfl (by omega))
    (wpV_v (foot16 hF (d := 48) (by omega)) (hal 48 rfl (by omega))
    (wpV_v0 (wpV_v0 (wpV_v0 (wpV_v0 (wpV_reg fun _ _ => wpV_reg fun _ _ => wpV_reg fun _ _ => wpV_reg fun _ _ =>
      wpV_reg fun _ _ => wpV_reg fun _ _ => wpV_nil ?_)))))))))
  intro Y₁ t₁ hK₁ hA₁ hr₁ hg₁ _ _
  -- the registers the block leaves
  generalize hxd : xsOf Y.cpu.vec.zmm = x at hg₁ hx1 hx2 hx3
  simp (disch := decide) only [wr, gv, Src.val, eaB, set_rcx, set_rdx, set_rsi, set_r8, get0, get1, get2, get6, get8,
    xset_same, xset_ne, BitVec.setWidth_eq, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, BitVec.xor_self, hx1,
    hx2, hx3] at hg₁
  have hax₁ : Y₁.cpu.gpr.rax = Y.cpu.gpr.rax := by simp only [hg₁]
  have hkp₁ : Kp g₀ Y₁.cpu.gpr := by simp only [Kp, hg₁]; exact hkp
  -- the joined mask: its bits, its lowest set bit
  generalize hBd : Y.cpu.gpr.rax = B at hg₁ hax₁ hB hpB hge hlt hF
  have hbit : ∀ i < 64, Y₁.cpu.gpr.rdx.getLsbD i = decide (V (Addr.add B i) = 0) := by
    intro i hi
    simp only [hg₁]
    exact getLsbD_join _ _ _ _ (fun i => decide (V (Addr.add B i) = 0)) (zbit V B 0) (zbit V B 16) (zbit V B 32)
      (zbit V B 48) hi
  have hk : g₀.rdi.toNat + n - B.toNat < 64 := by omega
  have hset : Y₁.cpu.gpr.rdx.getLsbD (g₀.rdi.toNat + n - B.toNat) = true := by
    rw [hbit _ hk, addr_eq (a := B) (i := g₀.rdi.toNat + n - B.toNat) (b := g₀.rdi) (j := n) (by omega), hz]; rfl
  have hlow : lowestSetBit Y₁.cpu.gpr.rdx = g₀.rdi.toNat + n - B.toNat := by
    apply lowestSetBit_eq hk hset
    intro i hi
    rw [hbit i (by omega), addr_eq (a := B) (i := i) (b := g₀.rdi) (j := B.toNat + i - g₀.rdi.toNat) (by omega)]
    exact decide_eq_false (hnz _ (by omega))
  have hnz₁ : rv Y₁ 64 2 ≠ 0 := by
    simp only [rv, get2, BitVec.setWidth_eq]
    intro h
    rw [h, getLsbD_zero'] at hset
    exact Bool.false_ne_true hset
  -- `bsf rdx, rdx`
  refine c.s_bsf64 hK₁ hA₁ hin (by rw [sl2_length]; omega) hr₁ (d401 prof.feat) hnz₁ ?_
  rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
  simp only [rv, get2, BitVec.setWidth_eq, hlow, set_rdx] at hg₂
  have hdx₂ : Y₂.cpu.gpr.rdx = BitVec.ofNat 64 (g₀.rdi.toNat + n - B.toNat) := by simp only [hg₂]
  have hax₂ : Y₂.cpu.gpr.rax = B := by simp only [hg₂]; exact hax₁
  have hkp₂ : Kp g₀ Y₂.cpu.gpr := by simp only [Kp, hg₂]; exact hkp₁
  -- `add rax, rdx`, `sub rax, rdi`
  refine c.s_blkV hin (b405 prof) hK₂ hA₂ hr₂ ?_
  refine wpV_reg fun _ _ => wpV_reg fun _ _ => wpV_nil ?_
  intro Y₃ t₃ hK₃ hA₃ hr₃ hg₃ _ _
  simp only [wr, gv, Src.val, set_rax, get0, get2, get7, BitVec.setWidth_eq] at hg₃
  have hkp₃ : Kp g₀ Y₃.cpu.gpr := by simp only [Kp, hg₃]; exact hkp₂
  have hax₃ : Y₃.cpu.gpr.rax = subR (addR Y₂.cpu.gpr.rax Y₂.cpu.gpr.rdx) Y₂.cpu.gpr.rdi := by simp only [hg₃]
  rw [hax₂, hdx₂, hkp₂.1] at hax₃
  exact ret_at c hin (by rw [sl2_length]; omega) (d411 prof.feat) hK₃ hA₃ hr₃ hkp₃ (hax₃.trans (rax_fin (by omega) hov)) hR

end Strlen
end FV7z
