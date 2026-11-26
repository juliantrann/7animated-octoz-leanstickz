import FV7z.U16.Cnt
/-! # `Utf8_To_Utf16`: addresses, the stack pointer's forms and the frame (PLAN.md §M, M1) -/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
open FV7z.U8c (addK pret pret_0)
open FV7z.Tun (rd_Vst rd_Vst_self Vst_out)
namespace FV7z.U16
/-! ## Addresses -/

theorem adv1 (p : Addr) (k : Nat) : p + BitVec.ofNat 64 k + 1#64 = p + BitVec.ofNat 64 (k + 1) :=
  (addK p k 1).symm

theorem tO {a : Addr} {j : Nat} (h : a.toNat + j < 2 ^ 64) : (a + BitVec.ofNat 64 j).toNat = a.toNat + j := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat]
  simp only [Nat.reducePow] at h ⊢
  omega

theorem tA {a : Addr} {i : Nat} (h : a.toNat + i < 2 ^ 64) : (Addr.add a i).toNat = a.toNat + i := by
  simp only [Addr.add]
  exact tO h

/-- `s - c`, `c ≤ s`. -/
theorem ts {s : Addr} {c : Nat} (h : c ≤ s.toNat) : (s - BitVec.ofNat 64 c).toNat = s.toNat - c := by
  have hs := s.isLt
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat]
  simp only [Nat.reducePow] at hs ⊢
  omega

theorem pinj1 {p : Addr} {n k j : Nat} (hp : p.toNat + n < 2 ^ 64) (hk : k ≤ n) (hj : j ≤ n)
    (h : p + BitVec.ofNat 64 k = p + BitVec.ofNat 64 j) : k = j := by
  have := congrArg BitVec.toNat h
  rw [tO (a := p) (j := k) (by omega), tO (a := p) (j := j) (by omega)] at this
  omega

/-- `rbx + r11 * 4`. -/
theorem m4 (D : Addr) (c : Nat) : D + BitVec.ofNat 64 c * 4#64 = D + BitVec.ofNat 64 (4 * c) := by
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_mul, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
  omega

theorem ad4 (D : Addr) (j : Nat) : D + BitVec.ofNat 64 j + 4#64 = D + BitVec.ofNat 64 (j + 4) :=
  (addK D j 4).symm

/-- The six `push`es. -/
abbrev S6 (s : Addr) : Addr := s - 8 - 8 - 8 - 8 - 8 - 8

/-- The stack pointer's forms. -/
theorem k8 (s : Addr) : s - 8 = s - BitVec.ofNat 64 8 := rfl
theorem k16 (s : Addr) : s - 8 - 8 = s - BitVec.ofNat 64 16 := by bv_omega
theorem k24 (s : Addr) : s - 8 - 8 - 8 = s - BitVec.ofNat 64 24 := by bv_omega
theorem k32 (s : Addr) : s - 8 - 8 - 8 - 8 = s - BitVec.ofNat 64 32 := by bv_omega
theorem k40 (s : Addr) : s - 8 - 8 - 8 - 8 - 8 = s - BitVec.ofNat 64 40 := by bv_omega
theorem k48 (s : Addr) : S6 s = s - BitVec.ofNat 64 48 := by simp only [S6]; bv_omega
theorem k56 (s : Addr) : S6 s + 18446744073709551608#64 = s - BitVec.ofNat 64 56 := by simp only [S6]; bv_omega
theorem k60 (s : Addr) : S6 s + 18446744073709551604#64 = s - BitVec.ofNat 64 60 := by simp only [S6]; bv_omega
/-- The `pop`s. -/
theorem q40 (s : Addr) : S6 s + 8 = s - BitVec.ofNat 64 40 := by simp only [S6]; bv_omega
theorem q32 (s : Addr) : S6 s + 8 + 8 = s - BitVec.ofNat 64 32 := by simp only [S6]; bv_omega
theorem q24 (s : Addr) : S6 s + 8 + 8 + 8 = s - BitVec.ofNat 64 24 := by simp only [S6]; bv_omega
theorem q16 (s : Addr) : S6 s + 8 + 8 + 8 + 8 = s - BitVec.ofNat 64 16 := by simp only [S6]; bv_omega
theorem q8 (s : Addr) : S6 s + 8 + 8 + 8 + 8 + 8 = s - BitVec.ofNat 64 8 := by simp only [S6]; bv_omega
theorem q0 (s : Addr) : S6 s + 8 + 8 + 8 + 8 + 8 + 8 = s := by simp only [S6]; bv_omega

/-! ## The frame -/

/-- `V` is `Vb` but at the `W` bytes from `D`. -/
def Fr (Vb : Addr → Byte) (D : Addr) (W : Nat) (V : Addr → Byte) : Prop :=
  ∀ x : Addr, (x.toNat < D.toNat ∨ D.toNat + W ≤ x.toNat) → V x = Vb x

section fr
variable {Vb V : Addr → Byte} {D : Addr} {W : Nat}

theorem fr0 : Fr Vb D W Vb := fun _ _ => rfl

/-- A store of 4 bytes at the `j`-th, `j + 4 ≤ W`. -/
theorem frS (hD : D.toNat + W ≤ 2 ^ 64) (hF : Fr Vb D W V) {j : Nat} (hj : j + 4 ≤ W) (w : BitVec 32) :
    Fr Vb D W (Vst V (D + BitVec.ofNat 64 j) (toBytesLE w 4)) := by
  intro x hx
  have ht : (D + BitVec.ofNat 64 j).toNat = D.toNat + j := tO (by omega)
  rw [Vst_out V (D + BitVec.ofNat 64 j) (toBytesLE w 4) x (by rw [toBytesLE_length, ht]; omega)
    (by rw [toBytesLE_length, ht]; omega)]
  exact hF x hx

/-- A load apart from the `W` bytes. -/
theorem rdF (hF : Fr Vb D W V) {a : Addr} {m : Nat}
    (h : ∀ i < m, (Addr.add a i).toNat < D.toNat ∨ D.toNat + W ≤ (Addr.add a i).toNat) :
    List.map V (byteAddrs a m) = List.map Vb (byteAddrs a m) := by
  apply List.map_congr_left
  intro x hx
  obtain ⟨i, hi, rfl⟩ := mem_byteAddrs.1 hx
  exact hF _ (h i hi)

end fr

end FV7z.U16
