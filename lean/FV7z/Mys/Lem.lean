import FV7z.Startup.StrAt
import FV7z.Tun.Inv
import FV7z.Lemmas.FnSteps
/-!
# Pointers into strings (PLAN.md §M, M1: `MyString.o`)

The arithmetic the loops of 7-Zip's string functions need: a pointer `s + k` of a string at `s`, the index back from
it (`sub32_add`: `(int)(p - s)` at 32 bits; `sar_sub4`: `(p - s) >> 2` for `wchar_t`), a step of the pointer, the
bytes of `movzx` (`sw8b`); `Kp`, the registers a call keeps, and `ret_back`, the `ret` of a leaf that kept them.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Mys

/-- `eax = (s + m) - s` at 32 bits, zero-extended: `m`, for `m < 2 ^ 32`. -/
theorem sub32_add (s : BitVec 64) {m : Nat} (hm : m < 2 ^ 32) :
    BitVec.setWidth 64 (BitVec.setWidth 32 (s + BitVec.ofNat 64 m) - BitVec.setWidth 32 s) = BitVec.ofNat 64 m := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.reducePow]
  omega

/-- The step of a pointer: `(s + k) + d = s + (k + d)`. -/
theorem ptr_step (s : BitVec 64) (k d : Nat) :
    s + BitVec.ofNat 64 k + BitVec.ofNat 64 d = s + BitVec.ofNat 64 (k + d) := by
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]

/-- `s + k` as `Addr.add`. -/
theorem ptr_add (s : BitVec 64) (k : Nat) : s + BitVec.ofNat 64 k = s.add k := rfl

/-- `(s + 4m - s) >> 2` (arithmetic): `m`, for `4m < 2 ^ 63`. -/
theorem sar_sub4 (s : BitVec 64) {m : Nat} (hm : 4 * m < 2 ^ 63) :
    (s + BitVec.ofNat 64 (4 * m) - s).sshiftRight 2 = BitVec.ofNat 64 m := by
  rw [BitVec.add_comm s, BitVec.add_sub_cancel]
  have hmsb : (BitVec.ofNat 64 (4 * m)).msb = false := by
    rw [BitVec.msb_eq_decide]
    simp only [BitVec.toNat_ofNat, Nat.reducePow, decide_eq_false_iff_not, Nat.not_le]
    omega
  rw [BitVec.sshiftRight_eq_of_msb_false hmsb]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.reducePow, Nat.shiftRight_eq_div_pow]
  omega

/-- A byte zero-extended to 32 and 64 bits, its low byte: the byte. -/
theorem sw8b (b : BitVec 8) : BitVec.setWidth 8 (BitVec.setWidth 64 (BitVec.setWidth 32 b)) = b := by
  apply BitVec.eq_of_toNat_eq
  have h8 : b.toNat < 256 := b.isLt
  simp only [BitVec.toNat_setWidth, Nat.reducePow]
  omega

/-- A byte zero-extended to 32 bits, its low byte: the byte. -/
theorem sw8a (b : BitVec 8) : BitVec.setWidth 8 (BitVec.setWidth 32 b) = b := by
  apply BitVec.eq_of_toNat_eq
  have h8 : b.toNat < 256 := b.isLt
  simp only [BitVec.toNat_setWidth, Nat.reducePow]
  omega

/-- The low byte of `x` through 32 and 64 bits: that of `x`. -/
theorem sw8x (x : BitVec 64) : BitVec.setWidth 8 (BitVec.setWidth 64 (BitVec.setWidth 32 x)) = BitVec.setWidth 8 x := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, Nat.reducePow]
  omega

/-- 32 bits zero-extended, their low 32: the same. -/
theorem sw32 (x : BitVec 32) : BitVec.setWidth 32 (BitVec.setWidth 64 x) = x := by
  apply BitVec.eq_of_toNat_eq
  have h : x.toNat < 4294967296 := x.isLt
  simp only [BitVec.toNat_setWidth, Nat.reducePow]
  omega

/-- `eax = -1`, zero-extended. -/
theorem m1_64 : BitVec.setWidth 64 4294967295#32 = 4294967295#64 := by decide

/-- The registers a call keeps, as at `g₀`. -/
def Kp (g₀ g : Gprs) : Prop :=
  g.rsp = g₀.rsp ∧ g.rbx = g₀.rbx ∧ g.rbp = g₀.rbp ∧ g.r12 = g₀.r12 ∧ g.r13 = g₀.r13 ∧ g.r14 = g₀.r14 ∧
    g.r15 = g₀.r15

theorem Kp.refl (g : Gprs) : Kp g g := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem Kp.trans {g₁ g₂ g₃ : Gprs} (h₁ : Kp g₁ g₂) (h₂ : Kp g₂ g₃) : Kp g₁ g₃ :=
  ⟨h₂.1.trans h₁.1, h₂.2.1.trans h₁.2.1, h₂.2.2.1.trans h₁.2.2.1, h₂.2.2.2.1.trans h₁.2.2.2.1,
    h₂.2.2.2.2.1.trans h₁.2.2.2.2.1, h₂.2.2.2.2.2.1.trans h₁.2.2.2.2.2.1, h₂.2.2.2.2.2.2.trans h₁.2.2.2.2.2.2⟩

/-- `Kp` of registers equal to others. -/
theorem Kp.of_eq {g g' G : Gprs} (h : g' = G) (hk : Kp g G) : Kp g g' := h ▸ hk

/-- `Kp g g'` for `g'` equal to `g` with registers other than those a call keeps written. -/
macro "kp_w " h:term:max : term => `(Kp.of_eq $h ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩)

variable {prof : Profile} {F : Footprint} {Wl : List Rgn} {L : List (Addr × List Byte)} {s₀ : State}
  {o : Oracle} {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}

/-- The `ret` of a leaf at `jr`, the registers a call keeps as at the entry `X` (`Kp`): at the return address, those
registers as `Str.Back` has them, `rax` as at the `ret`. -/
theorem ret_back {code : List Byte} {e : Addr} {jr : Nat} (c : Seg prof F Wl L s₀ o) (hin : CodeIn L e code)
    (hj : jr < code.length) (hd : Dec prof.feat code jr (FV7z.mk .ret 64 [] 1)) {X Z : State} {t : Nat}
    {V : Addr → Byte} (hKZ : KeptW Wl s₀ Z) (hAZ : Agree F Z.proc.mm.mem V) (hrZ : Z.cpu.rip = e.add jr)
    (hkp : Kp X.cpu.gpr Z.cpu.gpr) (hl : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsp i))
    {e₂ : Addr} {code₂ : List Byte} {j₂ : Nat} (hin₂ : CodeIn L e₂ code₂) (h₂ : j₂ < code₂.length)
    (hra : rdq(V, X.cpu.gpr.rsp) = e₂.add j₂)
    (k : ∀ (Z' : State) (t' : Nat), KeptW Wl s₀ Z' → Agree F Z'.proc.mm.mem V → Z'.cpu.rip = e₂.add j₂ →
      Str.Back X.cpu.gpr Z'.cpu.gpr → Z'.cpu.gpr.rax = Z.cpu.gpr.rax → GoG prof L o gev gP gE Z' t') :
    GoG prof L o gev gP gE Z t := by
  have hsp : Z.cpu.gpr.rsp = X.cpu.gpr.rsp := hkp.1
  refine c.s_ret hKZ hAZ hin hj hrZ hd (by rw [hsp]; exact hl) hin₂ h₂ (by rw [hsp]; exact hra) ?_
  rintro Z' t' hK' hA' ⟨hr', hg'⟩
  obtain ⟨-, h2, h3, h4, h5, h6, h7⟩ := hkp
  refine k Z' t' hK' hA' hr' ?_ (by rw [hg']; rfl)
  rw [hg']
  exact ⟨by show Z.cpu.gpr.rsp + 8 = _; rw [hsp]; rfl, h2, h3, h4, h5, h6, h7⟩

end FV7z.Mys
