import FV7z.Lzma.Cuts
import FV7z.Lzma.Ctx
/-!
# The invariants at the cut points of `LzmaDec_DecodeReal_3` (PLAN.md G2, pilot)

Each is a condition on the registers and the footprint's bytes at a cut point of `Cuts.lean`, with the measure `n`
that the way to the next cut point decreases: `2^20` for each byte of the dictionary up to `limit`, and a rank within
a symbol. No flags in them, nor the code of the range decoder (`ebp`): what the function reads and stores does not
depend on it.
-/
namespace FV7z.Lzma
open ZellicX86 Decode FV7z FV7z.Leaf

/-- What holds from the prologue to the epilogue: the frame, `r10d`, the memory, `dicPos` before `limit`, and
`processedPos` in `r13d`, `e` more than the bytes written say. -/
def Bd (K : Ctx) (g : Gprs) (V : Addr → Byte) (dp e : Nat) : Prop :=
  g.rsp = K.sp ∧ g.r10 = 2048#64 ∧ Mem K V ∧ K.dp0 ≤ dp ∧ dp < K.lim ∧
  ∃ pp : BitVec 32, g.r13 = pp.setWidth 64 ∧ (K.ckd.toNat = 0 → pp.toNat + (K.lim - dp) ≤ K.ppb + e)

/-- `r8d`: twice the state, even, in `[lo, hi)`. -/
def St (r8 : BitVec 64) (lo hi : Nat) : Prop :=
  ∃ s : BitVec 32, r8 = s.setWidth 64 ∧ s.toNat % 2 = 0 ∧ lo ≤ s.toNat ∧ s.toNat < hi

theorem St.mono {r8 : BitVec 64} {lo hi lo' hi' : Nat} (h : St r8 lo hi) (hl : lo' ≤ lo) (hh : hi ≤ hi') :
    St r8 lo' hi' := by
  obtain ⟨s, e, h2, h3, h4⟩ := h
  exact ⟨s, e, h2, by omega, by omega⟩

/-- `ecx`: the position's state, times 32. -/
def Px (rcx : BitVec 64) : Prop :=
  ∃ x : BitVec 32, rcx = x.setWidth 64 ∧ x.toNat ≤ 480 ∧ x.toNat % 32 = 0

theorem px_of (a b : BitVec 32) (ha : a.toNat ≤ 15) : Px (((a &&& b) <<< 5).setWidth 64) := by
  have h : (a &&& b).toNat ≤ a.toNat := by rw [BitVec.toNat_and]; exact Nat.and_le_left
  generalize a &&& b = z at h
  exact ⟨_, rfl, by bv_omega, by bv_omega⟩

/-- At the start of a symbol, and after the normalization there: `dicPos` in `r14`, the array of probabilities in
`r11`, the slot of the first bit by `rsi` and `rcx`. -/
def SymC (K : Ctx) (g : Gprs) (V : Addr → Byte) (dp lo hi : Nat) : Prop :=
  Bd K g V dp 0 ∧ g.r14 = K.dic + BitVec.ofNat 64 dp ∧ St g.r8 lo hi ∧ g.r11 = K.P ∧ g.rsi = K.P + g.r8 ∧ Px g.rcx

/-- The start of a symbol: 1001, 3770, 2825. -/
def Sym (K : Ctx) (n : Nat) (g : Gprs) (V : Addr → Byte) (lo hi : Nat) (X : Prop) : Prop :=
  ∃ dp, SymC K g V dp lo hi ∧ RcU K 0 0 g.rax g.r15 ∧ X ∧ n = 2 ^ 20 * (K.lim - dp) + 9000

/-- The symbol's first bit: 1028, 3797, 2852. -/
def SymB (K : Ctx) (n : Nat) (g : Gprs) (V : Addr → Byte) (lo hi : Nat) (X : Prop) : Prop :=
  ∃ (dp : Nat) (R P : BitVec 32), SymC K g V dp lo hi ∧ g.rax = R.setWidth 64 ∧ RcN K 0 0 R g.r15 ∧
    g.rdx = P.setWidth 64 ∧ Pv P ∧ X ∧ n = 2 ^ 20 * (K.lim - dp) + 8900

/-- A literal, 259: the range in `eax` is the bound already, the first bit's probability in `edx` and its slot by
`rsi` and `rcx`. -/
def Lit259 (K : Ctx) (n : Nat) (g : Gprs) (V : Addr → Byte) : Prop :=
  ∃ (dp : Nat) (P so : BitVec 32), Bd K g V dp 0 ∧ g.r14 = K.dic + BitVec.ofNat 64 dp ∧ RcU K 1 0 g.rax g.r15 ∧
    g.rdx = P.setWidth 64 ∧ Pv P ∧ St g.r8 0 8 ∧ g.r11 = K.P ∧
    g.rsi = K.P + so.setWidth 64 ∧ so.toNat % 2 = 0 ∧ so.toNat < 24 ∧ Px g.rcx ∧
    g.r9.setWidth 32 = K.lpm ∧ n = 2 ^ 20 * (K.lim - dp) + 8800

/-- Within a literal: its 0x300 probabilities by `r11`. -/
def LitC (K : Ctx) (g : Gprs) (V : Addr → Byte) (dp : Nat) : Prop :=
  InPrR K g.r11 0x300 ∧ Bd K g V dp 1 ∧ g.r14 = K.dic + BitVec.ofNat 64 dp ∧ St g.r8 0 8 ∧
  g.r9.setWidth 32 = K.lpm

/-- A literal's first bit, 341. -/
def Lit341 (K : Ctx) (n : Nat) (g : Gprs) (V : Addr → Byte) : Prop :=
  ∃ (dp : Nat) (R P1 P2 : BitVec 32), g.rax = R.setWidth 64 ∧ RcN K 1 0 R g.r15 ∧ g.rcx = P1.setWidth 64 ∧ Pv P1 ∧
    g.rdx = P2.setWidth 64 ∧ Pv P2 ∧ LitC K g V dp ∧ n = 2 ^ 20 * (K.lim - dp) + 8700

/-- A literal's later bits: twice the node in `ebx`, in `[lo, 2 lo)`, its probability in `pa` and its left child's
in `pb`. -/
def LitI (K : Ctx) (n : Nat) (g : Gprs) (V : Addr → Byte) (k lo rk : Nat) (pa pb : BitVec 64) : Prop :=
  ∃ (dp : Nat) (R P1 P2 M : BitVec 32),
    g.rax = R.setWidth 64 ∧ RcN K k 0 R g.r15 ∧ pa = P1.setWidth 64 ∧ Pv P1 ∧ pb = P2.setWidth 64 ∧ Pv P2 ∧
    g.rbx = M.setWidth 64 ∧ M.toNat % 2 = 0 ∧ lo ≤ M.toNat ∧ M.toNat < 2 * lo ∧
    LitC K g V dp ∧ n = 2 ^ 20 * (K.lim - dp) + rk

/-- The frame's slot 0x68 keeps `dic + dicPos` while `r14` is used for something else. -/
def Spill (K : Ctx) (V : Addr → Byte) (dp : Nat) : Prop := rdq(V, K.sp + 104#64) = K.dic + BitVec.ofNat 64 dp

theorem Spill.st_pr {K : Ctx} {V : Addr → Byte} {dp : Nat} (hK : K.Ok) (h : Spill K V dp) {a : Addr}
    (ha : InPr K a) (v : BitVec 16) : Spill K (Vst V a (toBytesLE v 2)) dp := by
  have := hK.hsq; have := hK.hsp2
  unfold Spill
  rw [rd_fr_pr hK ha v 104 (by bv_omega) (by omega)]; exact h

/-- Within a literal after a match: its 0x300 probabilities by `r11`, `dic + dicPos` in the frame. -/
def MLitC (K : Ctx) (g : Gprs) (V : Addr → Byte) (dp : Nat) : Prop :=
  InPrR K g.r11 0x300 ∧ Bd K g V dp 1 ∧ Spill K V dp ∧ St g.r8 8 14

/-- A literal after a match, 2960: the byte to match at `r12 + r14` in the dictionary's buffer. -/
def MLit2960 (K : Ctx) (n : Nat) (g : Gprs) (V : Addr → Byte) : Prop :=
  ∃ dp o : Nat, MLitC K g V dp ∧ RcU K 1 0 g.rax g.r15 ∧ g.r12 = K.dic ∧ g.r14 = BitVec.ofNat 64 o ∧ o < K.dbs ∧
    n = 2 ^ 20 * (K.lim - dp) + 8800

/-- `offs`, twice, as the two parts `r12d` and `r14d` hold it: one of them 0, the other 0 or 0x200. -/
def Ofs (A B : BitVec 32) : Prop := (A = 0#32 ∧ B = 0#32) ∨ (A = 512#32 ∧ B = 0#32) ∨ (A = 0#32 ∧ B = 512#32)

/-- A literal after a match, its first bit, 3023: the probability in `ecx`, its slot in `rdx`. -/
def MLit3023 (K : Ctx) (n : Nat) (g : Gprs) (V : Addr → Byte) : Prop :=
  ∃ (dp : Nat) (R P1 A B : BitVec 32), g.rax = R.setWidth 64 ∧ RcN K 1 0 R g.r15 ∧ g.rcx = P1.setWidth 64 ∧ Pv P1 ∧
    InPr K g.rdx ∧ g.r12 = A.setWidth 64 ∧ g.r14 = B.setWidth 64 ∧ Ofs A B ∧ MLitC K g V dp ∧
    n = 2 ^ 20 * (K.lim - dp) + 8700

/-- A literal after a match, its later bits: twice the node in `ebx`, its probability in `ecx`, the 0x100
probabilities of this `offs` and bit to match by `rdx`. -/
def MLitI (K : Ctx) (n : Nat) (g : Gprs) (V : Addr → Byte) (k lo rk : Nat) (X : Prop) : Prop :=
  ∃ (dp : Nat) (R P1 M : BitVec 32), g.rax = R.setWidth 64 ∧ RcN K k 0 R g.r15 ∧ g.rcx = P1.setWidth 64 ∧ Pv P1 ∧
    g.rbx = M.setWidth 64 ∧ M.toNat % 2 = 0 ∧ lo ≤ M.toNat ∧ M.toNat < 2 * lo ∧ InPrR K g.rdx 0x100 ∧
    X ∧ MLitC K g V dp ∧ n = 2 ^ 20 * (K.lim - dp) + rk

/-- `r12d` and `r14d` hold `offs`. -/
def OfsR (g : Gprs) : Prop := ∃ A B : BitVec 32, g.r12 = A.setWidth 64 ∧ g.r14 = B.setWidth 64 ∧ Ofs A B

/-- The symbol's first bit was 1, 1044: the range in `edi`, the bound in `eax`, the probability in `edx`. -/
def Mat1044 (K : Ctx) (n : Nat) (g : Gprs) (V : Addr → Byte) : Prop :=
  ∃ (dp : Nat) (R P : BitVec 32), SymC K g V dp 0 24 ∧ g.rdi = R.setWidth 64 ∧ RcN K 0 0 R g.r15 ∧
    g.rax = (R >>> 11 * P).setWidth 64 ∧ g.rdx = P.setWidth 64 ∧ Pv P ∧
    (14 ≤ g.r8.toNat → g.r12 = K.dic) ∧
    n = 2 ^ 20 * (K.lim - dp) + 8800

/-- The way out, 4611: `dicPos` up to `limit`, the range before its normalization. -/
def Out4611 (K : Ctx) (n : Nat) (g : Gprs) (V : Addr → Byte) : Prop :=
  ∃ (dq k d : Nat) (pp : BitVec 32), g.rsp = K.sp ∧ Mem K V ∧ g.r14 = K.dic + BitVec.ofNat 64 dq ∧
    K.dp0 ≤ dq ∧ dq ≤ K.lim ∧ Bg k d ∧ RcU K k d g.rax g.r15 ∧ St g.r8 0 24 ∧
    g.r13 = pp.setWidth 64 ∧ (K.ckd.toNat = 0 → pp.toNat + (K.lim - dq) ≤ K.ppb) ∧ n = 200

/-- The result of `sbb $-1, ebx` on twice a node: the node's child. -/
theorem sbb_c (M : BitVec 32) (b : Bool) (hM : M.toNat < 2 ^ 31) :
    ∃ c, c ≤ 1 ∧ (M - 4294967295#32 - BitVec.setWidth 32 (BitVec.ofBool b)).toNat = M.toNat + c := by
  cases b
  · exact ⟨1, by omega, by simp; bv_omega⟩
  · exact ⟨0, by omega, by simp; bv_omega⟩

theorem Pv.ite {x y : BitVec 32} (c : Bool) (hx : Pv x) (hy : Pv y) : Pv (if c = true then x else y) := by
  cases c <;> assumption

/-- The 0x300 probabilities of a literal: from `probs + 0x280`, three times the literal's state `y`, shifted by
`lc + 1`. -/
theorem lit_base {K : Ctx} (hK : K.Ok) (y : BitVec 32) (c : Nat) (hy : y.toNat ≤ K.lpm.toNat)
    (hc : c % 32 = K.lc + 1) :
    InPrR K (K.P + 640#64 + BitVec.setWidth 64
      (BitVec.setWidth 32 (BitVec.setWidth 64 y + BitVec.setWidth 64 y * 2#64) <<< (c % 32))) 0x300 := by
  have h1 := hK.hlit; have h2 := hK.hnp32; have h3 := hK.hnp; have hP := hK.hP
  have hm : 3 * y.toNat * 2 ^ K.lc ≤ 3 * K.lpm.toNat * 2 ^ K.lc :=
    Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 3 hy)
  have h3y : 3 * y.toNat ≤ 3 * y.toNat * 2 ^ K.lc := Nat.le_mul_of_pos_right _ Nat.one_le_two_pow
  generalize 3 * K.lpm.toNat * 2 ^ K.lc = u at h1 hm
  have e1 : (BitVec.setWidth 32 (BitVec.setWidth 64 y + BitVec.setWidth 64 y * 2#64)).toNat = 3 * y.toNat := by
    bv_omega
  have e2 : (BitVec.setWidth 32 (BitVec.setWidth 64 y + BitVec.setWidth 64 y * 2#64) <<< (c % 32)).toNat =
      2 * (3 * y.toNat * 2 ^ K.lc) := by
    have e3 : 3 * y.toNat * 2 ^ (K.lc + 1) = 2 * (3 * y.toNat * 2 ^ K.lc) := by rw [Nat.pow_succ]; ac_rfl
    rw [hc, BitVec.toNat_shiftLeft, e1, Nat.shiftLeft_eq, e3, Nat.mod_eq_of_lt (by omega)]
  generalize 3 * y.toNat * 2 ^ K.lc = t at *
  generalize BitVec.setWidth 32 (BitVec.setWidth 64 y + BitVec.setWidth 64 y * 2#64) <<< (c % 32) = z at *
  exact ⟨0x7c0 + t, by bv_omega, by omega⟩

theorem and_512 (Y : BitVec 32) : Y &&& 512#32 = 0#32 ∨ Y &&& 512#32 = 512#32 := by
  have h1 : (Y &&& 512#32).toNat ≤ 512 := by rw [BitVec.toNat_and]; exact Nat.and_le_right
  have h2 : (Y &&& 512#32).toNat % 2 ^ 9 = 0 := by
    rw [BitVec.toNat_and, Nat.and_mod_two_pow]; simp
  by_cases h : (Y &&& 512#32).toNat = 0
  · left; exact BitVec.eq_of_toNat_eq h
  · right; exact BitVec.eq_of_toNat_eq (by simp only [BitVec.toNat_ofNat]; omega)

theorem ofs_and (Y X : BitVec 32) (hX : X = 0#32 ∨ X = 512#32) :
    ∃ A' B', Y &&& X = B' ∧ X ^^^ B' = A' ∧ Ofs A' B' ∧ A'.toNat + B'.toNat = X.toNat := by
  rcases hX with rfl | rfl
  · exact ⟨0#32, 0#32, by simp, by simp, .inl ⟨rfl, rfl⟩, rfl⟩
  · rcases and_512 Y with h | h
    · exact ⟨512#32, 0#32, h, by simp, .inr (.inl ⟨rfl, rfl⟩), rfl⟩
    · exact ⟨0#32, 512#32, h, by simp, .inr (.inr ⟨rfl, rfl⟩), rfl⟩

theorem Ofs.nat {A B : BitVec 32} (h : Ofs A B) : A.toNat + B.toNat ≤ 512 ∧ A.toNat % 512 = 0 ∧ B.toNat % 512 = 0 := by
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide

theorem Ofs.sel {A B : BitVec 32} (h : Ofs A B) (c : Bool) :
    (if c = true then B else A) = 0#32 ∨ (if c = true then B else A) = 512#32 := by
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> cases c <;> simp

theorem sbb_c3 (b : Bool) :
    ∃ c, c ≤ 1 ∧ (0#32 - 4294967293#32 - BitVec.setWidth 32 (BitVec.ofBool b)).toNat = 2 + c := by
  cases b
  · exact ⟨1, by omega, by decide⟩
  · exact ⟨0, by omega, by decide⟩

theorem st_mlit (s : BitVec 32) (hs2 : s.toNat % 2 = 0) (hsl : 14 ≤ s.toNat) (hsh : s.toNat < 24) :
    St (BitVec.setWidth 64 (if (!decide ((s - 6#32).toNat < 14)) = true then
      BitVec.setWidth 32 (BitVec.setWidth 64 s + 18446744073709551604#64) else s - 6#32)) 8 14 := by
  have e : BitVec.setWidth 32 (BitVec.setWidth 64 s + 18446744073709551604#64) = s - 12#32 := by bv_omega
  rw [e]
  by_cases h : (s - 6#32).toNat < 14
  · simp only [h, decide_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    exact ⟨_, rfl, by bv_omega, by bv_omega, by bv_omega⟩
  · simp only [h, decide_false, Bool.not_false, ↓reduceIte]
    exact ⟨_, rfl, by bv_omega, by bv_omega, by bv_omega⟩

theorem Spill.of_st {K : Ctx} (hK : K.Ok) (V : Addr → Byte) (dp : Nat) :
    Spill K (Vst V (K.sp + 104#64) (toBytesLE (K.dic + BitVec.ofNat 64 dp) 8)) dp := by
  have := hK.hsq; have := hK.hsp2
  unfold Spill
  rw [rd_Vst_self _ _ _ (toBytesLE_length _ _) (by bv_omega), ofBytesLE_toBytesLE (by rfl)]

theorem Spill.st_free {K : Ctx} {V : Addr → Byte} {dp : Nat} (hK : K.Ok) (h : Spill K V dp) {a : Addr} {bs : List Byte}
    (hf : (K.dic.toNat ≤ a.toNat ∧ a.toNat + bs.length ≤ K.dic.toNat + K.dbs)) : Spill K (Vst V a bs) dp := by
  have := hK.hsq; have := hK.hsp2; have := hK.hdic; have := hK.aFD
  unfold Spill
  rw [rd_Vst _ _ _ _ _ (by omega) (by bv_omega) (by bv_omega)]; exact h
/-! ## A match or a repeat -/

/-- 1088: after the bit 1 of `IsMatch`, with the probability of `IsRep`. -/
def Mat1088 (K : Ctx) (n : Nat) (g : Gprs) (V : Addr → Byte) : Prop :=
  ∃ (dp : Nat) (R P : BitVec 32), SymC K g V dp 0 24 ∧ g.rax = R.setWidth 64 ∧ RcN K 1 0 R g.r15 ∧
    g.rdx = P.setWidth 64 ∧ Pv P ∧ n = 2 ^ 20 * (K.lim - dp) + 8700

/-- A value for one of the four `reps`. -/
def RepV (K : Ctx) (r : BitVec 64) : Prop := (r.setWidth 32).toNat ≤ K.dbs

/-- A repeat: the state is the one after it, `rsi` has the one before; `r11` is at the lengths of repeats. -/
def RepC (K : Ctx) (g : Gprs) (V : Addr → Byte) (dp : Nat) : Prop :=
  Bd K g V dp 0 ∧ g.r14 = K.dic + BitVec.ofNat 64 dp ∧ St g.r8 16 24 ∧ g.r11 = K.P + 18446744073709549056#64 ∧
    (∃ so : BitVec 32, g.rsi = K.P + so.setWidth 64 ∧ so.toNat % 2 = 0 ∧ so.toNat < 24) ∧ Px g.rcx

/-- 4002, 4055, 4182, 4266: before a bit that tells which repeat. -/
def RepB (K : Ctx) (n : Nat) (g : Gprs) (V : Addr → Byte) (k rk : Nat) (X : Prop) : Prop :=
  ∃ (dp : Nat) (R P : BitVec 32), RepC K g V dp ∧ g.rax = R.setWidth 64 ∧ RcN K k 0 R g.r15 ∧
    g.rdx = P.setWidth 64 ∧ Pv P ∧ X ∧ n = 2 ^ 20 * (K.lim - dp) + rk

/-- Before the store of one byte at `dicPos` (2797), `processedPos` already counting it. -/
def CpC (K : Ctx) (g : Gprs) (V : Addr → Byte) (dq : Nat) : Prop :=
  Bd K g V dq 1 ∧ g.r14 = K.dic + BitVec.ofNat 64 dq ∧ St g.r8 14 24 ∧ g.r11 = K.P ∧ g.rsi = K.P + g.r8 ∧
    Px g.rcx ∧ g.r12 = K.dic ∧ ∃ k d, Bg k d ∧ RcU K k d g.rax g.r15

/-- 3911: a repeat of one byte, `rdi` its place in the dictionary. -/
def Rep3911 (K : Ctx) (n : Nat) (g : Gprs) (V : Addr → Byte) : Prop :=
  ∃ dq o : Nat, CpC K g V dq ∧ g.rdi = BitVec.ofNat 64 o ∧ o < K.dbs ∧ n = 2 ^ 20 * (K.lim - dq) + 8400

/-- 2797: the last byte of a copy. -/
def Cp2797 (K : Ctx) (n : Nat) (g : Gprs) (V : Addr → Byte) : Prop :=
  ∃ dq : Nat, CpC K g V dq ∧ n = 2 ^ 20 * (K.lim - dq) + 500

/-! ## The length -/

/-- The bits with a probability decoded in a symbol so far: at most 5 before the length of a repeat, 2 before a
match's. -/
def kl (s : BitVec 32) (δ : Nat) : Nat := if s.toNat < 24 then 5 + δ else 2 + δ

theorem kl_le (s : BitVec 32) {δ δ' : Nat} (h : δ ≤ δ') : kl s δ ≤ kl s δ' := by
  unfold kl; split <;> omega

theorem kl_succ (s : BitVec 32) (δ : Nat) : kl s δ + 1 = kl s (δ + 1) := by
  unfold kl; split <;> omega

theorem kl_bg (s : BitVec 32) {δ : Nat} (h : δ ≤ 10) : Bg (kl s δ) 0 := by
  unfold kl; split
  · exact .inl ⟨by omega, by omega⟩
  · exact .inl ⟨by omega, by omega⟩

/-- In the length: the state `s`, 24 more than a state after a match. -/
def LenC (K : Ctx) (g : Gprs) (V : Addr → Byte) (dp : Nat) (s : BitVec 32) : Prop :=
  Bd K g V dp 0 ∧ g.r14 = K.dic + BitVec.ofNat 64 dp ∧ g.r8 = s.setWidth 64 ∧ s.toNat % 2 = 0 ∧ 16 ≤ s.toNat ∧
    s.toNat < 48

/-- 1129: the start of a length, `r11` at the 512 probabilities of its coder. -/
def Len1129 (K : Ctx) (n : Nat) (g : Gprs) (V : Addr → Byte) : Prop :=
  ∃ (dp : Nat) (s : BitVec 32), LenC K g V dp s ∧ RcU K (kl s 0) 0 g.rax g.r15 ∧ InPrR K g.r11 512 ∧ Px g.rcx ∧
    n = 2 ^ 20 * (K.lim - dp) + 8200

/-- 1158, 1224: before the first and the second choice. -/
def LenB (K : Ctx) (n : Nat) (g : Gprs) (V : Addr → Byte) (δ sz rk : Nat) (v12 : BitVec 64) : Prop :=
  ∃ (dp : Nat) (s R P : BitVec 32), LenC K g V dp s ∧ g.rax = R.setWidth 64 ∧ RcN K (kl s δ) 0 R g.r15 ∧
    g.rdx = P.setWidth 64 ∧ Pv P ∧ InPrR K g.r11 sz ∧ Px g.rcx ∧ g.r12 = v12 ∧ n = 2 ^ 20 * (K.lim - dp) + rk

/-- What `r12` has for the low and the middle lengths. -/
def Lo12 (r12 : BitVec 64) : Prop := r12 = 5#64 ∨ r12 = 4294967293#64

/-- 1376: a low or a middle length, the choice's probability not yet stored. -/
def Len1376 (K : Ctx) (n : Nat) (g : Gprs) (V : Addr → Byte) : Prop :=
  ∃ (dp : Nat) (s P : BitVec 32), LenC K g V dp s ∧ RcU K (kl s 2) 0 g.rax g.r15 ∧ g.rdx = P.setWidth 64 ∧ Pv P ∧
    InPrR K g.r11 264 ∧ Px g.rcx ∧ Lo12 g.r12 ∧ n = 2 ^ 20 * (K.lim - dp) + 6900

/-- 1422: the first bit of the tree of 8. -/
def Len1422 (K : Ctx) (n : Nat) (g : Gprs) (V : Addr → Byte) : Prop :=
  ∃ (dp : Nat) (s R P1 P2 : BitVec 32), LenC K g V dp s ∧ g.rax = R.setWidth 64 ∧ RcN K (kl s 2) 0 R g.r15 ∧
    g.rdx = P1.setWidth 64 ∧ Pv P1 ∧ g.rcx = P2.setWidth 64 ∧ Pv P2 ∧ InPrR K g.r11 16 ∧ Lo12 g.r12 ∧
    n = 2 ^ 20 * (K.lim - dp) + 6800

/-- The tree whose last two bits 1479 to 1581 decode: of 8 with `lo` 2, of 256 with `lo` 64; `r12` is what the
last step takes from twice the tree's index for the length. -/
def LenT (lo : Nat) (r12 : BitVec 64) : Prop := (lo = 2 ∧ Lo12 r12) ∨ (lo = 64 ∧ r12 = 237#64)

/-- 1479: before the last bit but one. -/
def Len1479 (K : Ctx) (n : Nat) (g : Gprs) (V : Addr → Byte) : Prop :=
  ∃ (dp lo : Nat) (s P1 M : BitVec 32), LenC K g V dp s ∧ RcU K (kl s 8) 0 g.rax g.r15 ∧
    g.rcx = P1.setWidth 64 ∧ Pv P1 ∧ g.rbx = M.setWidth 64 ∧ lo ≤ M.toNat ∧ M.toNat < 2 * lo ∧
    InPrR K g.r11 (4 * lo) ∧ LenT lo g.r12 ∧ n = 2 ^ 20 * (K.lim - dp) + 6700

/-- 1505: the last bit but one. -/
def Len1505 (K : Ctx) (n : Nat) (g : Gprs) (V : Addr → Byte) : Prop :=
  ∃ (dp lo : Nat) (s R P1 P2 M : BitVec 32), LenC K g V dp s ∧ g.rax = R.setWidth 64 ∧ RcN K (kl s 8) 0 R g.r15 ∧
    g.rcx = P1.setWidth 64 ∧ Pv P1 ∧ g.rdx = P2.setWidth 64 ∧ Pv P2 ∧
    g.rbx = M.setWidth 64 ∧ M.toNat % 2 = 0 ∧ 2 * lo ≤ M.toNat ∧ M.toNat < 4 * lo ∧
    InPrR K g.r11 (4 * lo) ∧ LenT lo g.r12 ∧ n = 2 ^ 20 * (K.lim - dp) + 6600

/-- 1581: the last bit. -/
def Len1581 (K : Ctx) (n : Nat) (g : Gprs) (V : Addr → Byte) : Prop :=
  ∃ (dp lo : Nat) (s R P M : BitVec 32), LenC K g V dp s ∧ g.rax = R.setWidth 64 ∧ RcN K (kl s 9) 0 R g.r15 ∧
    g.rdx = P.setWidth 64 ∧ Pv P ∧ g.rbx = M.setWidth 64 ∧ M.toNat % 2 = 0 ∧ 4 * lo ≤ M.toNat ∧ M.toNat < 8 * lo ∧
    InPrR K g.r11 (4 * lo) ∧ LenT lo g.r12 ∧ n = 2 ^ 20 * (K.lim - dp) + 6500

/-- 1280: the tree of 256, before its `j`-th bit of the first six. -/
def Len1280 (K : Ctx) (n : Nat) (g : Gprs) (V : Addr → Byte) : Prop :=
  ∃ (dp j : Nat) (s P1 M : BitVec 32), LenC K g V dp s ∧ j < 6 ∧ RcU K (kl s (2 + j)) 0 g.rax g.r15 ∧
    g.rcx = P1.setWidth 64 ∧ Pv P1 ∧ g.rbx = M.setWidth 64 ∧ 2 ^ j ≤ M.toNat ∧ M.toNat < 2 * 2 ^ j ∧
    InPrR K g.r11 256 ∧ n = 2 ^ 20 * (K.lim - dp) + 7650 - 100 * j

/-- 1306: its `j`-th bit. -/
def Len1306 (K : Ctx) (n : Nat) (g : Gprs) (V : Addr → Byte) : Prop :=
  ∃ (dp j : Nat) (s R P1 P2 M : BitVec 32), LenC K g V dp s ∧ j < 6 ∧ g.rax = R.setWidth 64 ∧
    RcN K (kl s (2 + j)) 0 R g.r15 ∧ g.rcx = P1.setWidth 64 ∧ Pv P1 ∧ g.rdx = P2.setWidth 64 ∧ Pv P2 ∧
    g.rbx = M.setWidth 64 ∧ M.toNat % 2 = 0 ∧ 2 * 2 ^ j ≤ M.toNat ∧ M.toNat < 4 * 2 ^ j ∧
    InPrR K g.r11 256 ∧ n = 2 ^ 20 * (K.lim - dp) + 7600 - 100 * j

/-- 2664: the copy of a match of `L` bytes, at least one. -/
def Cp2664 (K : Ctx) (n : Nat) (g : Gprs) (V : Addr → Byte) : Prop :=
  ∃ (dp k d : Nat) (L : BitVec 32), Bd K g V dp 0 ∧ g.r14 = K.dic + BitVec.ofNat 64 dp ∧ St g.r8 14 24 ∧
    g.r11 = K.P ∧ Bg k d ∧ RcU K k d g.rax g.r15 ∧ g.rbx = L.setWidth 64 ∧ 1 ≤ L.toNat ∧ L.toNat ≤ 273 ∧
    n = 2 ^ 20 * (K.lim - dp) + 4400

/-- In the distance of a match: the length `L` in `r12`, the state 24 more than the one before the match. -/
def PosC (K : Ctx) (g : Gprs) (V : Addr → Byte) (dp : Nat) : Prop :=
  ∃ s L : BitVec 32, LenC K g V dp s ∧ 24 ≤ s.toNat ∧ g.r12 = L.setWidth 64 ∧ 2 ≤ L.toNat ∧ L.toNat ≤ 273

/-- 1695: the first bit of the distance's slot, `r11` at the 64 probabilities of the slots for the length. -/
def Pos1695 (K : Ctx) (n : Nat) (g : Gprs) (V : Addr → Byte) : Prop :=
  ∃ (dp : Nat) (R P1 P2 : BitVec 32), PosC K g V dp ∧ g.rax = R.setWidth 64 ∧ RcN K 12 0 R g.r15 ∧
    g.rcx = P1.setWidth 64 ∧ Pv P1 ∧ g.rdx = P2.setWidth 64 ∧ Pv P2 ∧ InPrR K g.r11 64 ∧
    n = 2 ^ 20 * (K.lim - dp) + 6400

/-! ## The distance -/

/-- 1778 to 2021: a bit of the tree of 64 slots, as `LitI` for a literal. -/
def PosI (K : Ctx) (n : Nat) (g : Gprs) (V : Addr → Byte) (k lo rk : Nat) (pa pb : BitVec 64) : Prop :=
  ∃ (dp : Nat) (R P1 P2 M : BitVec 32),
    g.rax = R.setWidth 64 ∧ RcN K k 0 R g.r15 ∧ pa = P1.setWidth 64 ∧ Pv P1 ∧ pb = P2.setWidth 64 ∧ Pv P2 ∧
    g.rbx = M.setWidth 64 ∧ M.toNat % 2 = 0 ∧ lo ≤ M.toNat ∧ M.toNat < 2 * lo ∧
    PosC K g V dp ∧ InPrR K g.r11 64 ∧ n = 2 ^ 20 * (K.lim - dp) + rk

/-- 2099: the slot's last bit, `rcx` with the tree's index `X` and `rbx` with twice that. -/
def Pos2099 (K : Ctx) (n : Nat) (g : Gprs) (V : Addr → Byte) : Prop :=
  ∃ (dp : Nat) (R P X : BitVec 32), g.rax = R.setWidth 64 ∧ RcN K 17 0 R g.r15 ∧ g.rdx = P.setWidth 64 ∧ Pv P ∧
    g.rcx = X.setWidth 64 ∧ g.rbx = (X + X).setWidth 64 ∧ 32 ≤ X.toNat ∧ X.toNat < 64 ∧
    PosC K g V dp ∧ InPrR K g.r11 64 ∧ n = 2 ^ 20 * (K.lim - dp) + 5900

/-- The direct bits: `r11` back at `probs`, `r9` and `rdx` ready for the four bits of `Align`. -/
def DirC (K : Ctx) (g : Gprs) (V : Addr → Byte) (dp : Nat) : Prop :=
  PosC K g V dp ∧ g.r11 = K.P ∧ g.r9 = K.P + 4#64 ∧ ∃ Pa : BitVec 32, g.rdx = Pa.setWidth 64 ∧ Pv Pa

/-- 2226: `c` direct bits to go after `d` done. -/
def Dir2226 (K : Ctx) (n : Nat) (g : Gprs) (V : Addr → Byte) : Prop :=
  ∃ (dp d : Nat) (c : BitVec 32), DirC K g V dp ∧ g.rcx = c.setWidth 64 ∧ 1 ≤ c.toNat ∧ d + c.toNat ≤ 26 ∧
    RcU K 18 d g.rax g.r15 ∧ n = 2 ^ 20 * (K.lim - dp) + 5000 + 20 * c.toNat + 10

/-- 2208: a direct bit. -/
def Dir2208 (K : Ctx) (n : Nat) (g : Gprs) (V : Addr → Byte) : Prop :=
  ∃ (dp d : Nat) (c R : BitVec 32), DirC K g V dp ∧ g.rcx = c.setWidth 64 ∧ 1 ≤ c.toNat ∧ d + c.toNat ≤ 26 ∧
    g.rax = R.setWidth 64 ∧ RcN K 18 d R g.r15 ∧ n = 2 ^ 20 * (K.lim - dp) + 5000 + 20 * c.toNat

/-- 2295 to 2546: a bit of `Align`, `X` telling where `r9` is in its tree. -/
def AlnI (K : Ctx) (n : Nat) (g : Gprs) (V : Addr → Byte) (k rk : Nat) (pa pb : BitVec 64) (X : Prop) : Prop :=
  ∃ (dp d : Nat) (R P1 P2 : BitVec 32), PosC K g V dp ∧ g.r11 = K.P ∧ g.rax = R.setWidth 64 ∧ RcN K k d R g.r15 ∧
    d ≤ 26 ∧ pa = P1.setWidth 64 ∧ Pv P1 ∧ pb = P2.setWidth 64 ∧ Pv P2 ∧ X ∧ n = 2 ^ 20 * (K.lim - dp) + rk

/-- `r9` at the `a`-th probability from `probs`, `lo ≤ a < hi`. -/
def AlnA (K : Ctx) (r9 : BitVec 64) (lo hi : Nat) : Prop :=
  ∃ a : Nat, r9 = K.P + BitVec.ofNat 64 (2 * a) ∧ lo ≤ a ∧ a < hi

/-- 4384: `c` bits of a short distance to go; `rbx` at the `q`-th probability of the array, the next one `u` or
`2 * u` further; `T` the reach of the bits to go. -/
def Spec4384 (K : Ctx) (n : Nat) (g : Gprs) (V : Addr → Byte) : Prop :=
  ∃ (dp u q T : Nat) (c : BitVec 32), PosC K g V dp ∧ g.rcx = c.setWidth 64 ∧ 1 ≤ c.toNat ∧ c.toNat ≤ 5 ∧
    g.r9 = BitVec.ofNat 64 (2 * u) ∧ 1 ≤ u ∧ u * 2 ^ c.toNat = T ∧ T ≤ 32 ∧ g.rbx.toNat = K.pbn + 2 * q ∧
    q + T ≤ 127 + 2 * u ∧ RcU K (23 - c.toNat) 0 g.rax g.r15 ∧
    n = 2 ^ 20 * (K.lim - dp) + 5000 + 20 * c.toNat + 10

/-- 4412: the bit, its probability at `r11`. -/
def Spec4412 (K : Ctx) (n : Nat) (g : Gprs) (V : Addr → Byte) : Prop :=
  ∃ (dp u q T : Nat) (c R P : BitVec 32), PosC K g V dp ∧ g.rcx = c.setWidth 64 ∧ 1 ≤ c.toNat ∧ c.toNat ≤ 5 ∧
    g.r9 = BitVec.ofNat 64 (2 * u) ∧ 1 ≤ u ∧ u * 2 ^ c.toNat = T ∧ T ≤ 32 ∧ g.rbx.toNat = K.pbn + 2 * q ∧
    q + T ≤ 127 + 3 * u ∧ InPr K g.r11 ∧ g.rax = R.setWidth 64 ∧ RcN K (23 - c.toNat) 0 R g.r15 ∧
    g.rdx = P.setWidth 64 ∧ Pv P ∧ n = 2 ^ 20 * (K.lim - dp) + 5000 + 20 * c.toNat

/-- 2594: the distance is in `rbx`, to be checked. -/
def Fin2594 (K : Ctx) (n : Nat) (g : Gprs) (V : Addr → Byte) : Prop :=
  ∃ dp k d : Nat, PosC K g V dp ∧ g.r11 = K.P ∧ Bg k d ∧ RcU K k d g.rax g.r15 ∧ n = 2 ^ 20 * (K.lim - dp) + 4500

/-! ## The copy of a match, and the way out -/

/-- 2736: `cur` bytes to copy up to the `dq`-th of the dictionary, from its `pos`-th; `r14` and `processedPos` are
past them already. -/
def Cp2736 (K : Ctx) (n : Nat) (g : Gprs) (V : Addr → Byte) : Prop :=
  ∃ dq cur pos k d : Nat, Bd K g V dq 1 ∧ g.r14 = K.dic + BitVec.ofNat 64 (dq + 1) ∧ St g.r8 14 24 ∧ g.r11 = K.P ∧
    g.r12 = K.dic ∧ g.rdi = BitVec.ofNat 64 pos ∧ g.rdx = BitVec.ofNat 64 cur ∧ 1 ≤ cur ∧ cur ≤ 273 ∧
    K.dp0 + cur ≤ dq + 1 ∧ pos + cur ≤ K.dbs ∧ Bg k d ∧ RcU K k d g.rax g.r15 ∧
    n = 2 ^ 20 * (K.lim - dq) + 4300

/-- 2748: `m` bytes to go, the first of them in `bl`, and `rdx` at `-m`; the source's end is the dictionary's
`se`-th byte. -/
def Cp2748 (K : Ctx) (n : Nat) (g : Gprs) (V : Addr → Byte) : Prop :=
  ∃ dq m se k d : Nat, Bd K g V dq 1 ∧ g.r14 = K.dic + BitVec.ofNat 64 (dq + 1) ∧ St g.r8 14 24 ∧ g.r11 = K.P ∧
    g.r12 = K.dic ∧ g.rdi = K.dic + BitVec.ofNat 64 se ∧ g.rdx = BitVec.ofNat 64 (18446744073709551616 - m) ∧
    1 ≤ m ∧ m ≤ 273 ∧ K.dp0 + m ≤ dq + 1 ∧ m ≤ se ∧ se ≤ K.dbs ∧ Bg k d ∧ RcU K k d g.rax g.r15 ∧
    n = 2 ^ 20 * (K.lim - dq) + 2000

/-- 2784: the loop of the copy, `j` bytes before the last. -/
def Cp2784 (K : Ctx) (n : Nat) (g : Gprs) (V : Addr → Byte) : Prop :=
  ∃ dq j se : Nat, CpC K g V dq ∧ g.rdi = K.dic + BitVec.ofNat 64 se ∧
    g.rdx = BitVec.ofNat 64 (18446744073709551616 - j) ∧ 1 ≤ j ∧ j ≤ 272 ∧ K.dp0 + j ≤ dq ∧ j ≤ se ∧ se ≤ K.dbs ∧
    n = 2 ^ 20 * (K.lim - dq) + 1000 + j

/-- 4505: the copy of a match whose source runs over the buffer's end: byte by byte from the `ps`-th up to the
end, with more than that to copy. -/
def Cp4505 (K : Ctx) (n : Nat) (g : Gprs) (V : Addr → Byte) : Prop :=
  ∃ dq m ps k d : Nat, Bd K g V dq 1 ∧ g.r14 = K.dic + BitVec.ofNat 64 (dq + 1) ∧ St g.r8 14 24 ∧ g.r11 = K.P ∧
    g.r12 = K.dic ∧ g.rdi = K.dic ∧ g.rsi = BitVec.ofNat 64 ps ∧ g.rcx = BitVec.ofNat 64 K.dbs ∧
    g.rdx = BitVec.ofNat 64 (18446744073709551616 - m) ∧ ps < K.dbs ∧ K.dbs < ps + m ∧ m ≤ 273 ∧
    K.dp0 + m ≤ dq + 1 ∧ Bg k d ∧ RcU K k d g.rax g.r15 ∧ n = 2 ^ 20 * (K.lim - dq) + 3000 + (K.dbs - ps)

/-- 4632, the epilogue: the result in `ebx`, 0 or 1. With 1 (an error in the data) the frame's `reps` are any, and
`remainLen` is at least 514: the callers decode no more. -/
def Out4632 (K : Ctx) (n : Nat) (g : Gprs) (V : Addr → Byte) : Prop :=
  ∃ (dq k d : Nat) (pp R : BitVec 32), g.rsp = K.sp ∧ Mem0 K V ∧ (g.rbx = 0#64 ∨ g.rbx = 1#64) ∧
    (g.rbx = 0#64 → Mem K V) ∧ (g.rbx = 1#64 → 514 ≤ (rdd(V, K.sp + 100#64)).toNat) ∧
    g.r14 = K.dic + BitVec.ofNat 64 dq ∧ K.dp0 ≤ dq ∧ dq ≤ K.lim ∧ g.rax = R.setWidth 64 ∧ RcN K k d R g.r15 ∧
    St g.r8 0 24 ∧ g.r13 = pp.setWidth 64 ∧ (K.ckd.toNat = 0 → pp.toNat + (K.lim - dq) ≤ K.ppb) ∧ n = 100

end FV7z.Lzma
