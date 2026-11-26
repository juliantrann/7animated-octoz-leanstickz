import FV7z.Lhp.Cuts
import FV7z.Lemmas.LeafRet
import FV7z.Tun.Inv
import FV7z.Raf.Holds
/-!
# `NArchive::NLzma::CHeader::Parse` (PLAN.md §M, M1)

7-Zip 26.06's `CHeader::Parse (const Byte *buf, bool isThereFilter)` at `0x49ec00` in `7zzs`
(`CPP/7zip/Archive/LzmaHandler.cpp`; `objdump -d`): `FilterID` (the byte at `this + 8`) 0, or `buf[0]` with a filter
and `buf` one on; the 5 props bytes (`this + 9`) copied in a loop, `Size` (`this + 0`) the 8 bytes after them; then
the checks, the dictionary size (`this + 10`) against `2 << i` and `3 << i` for `i` from 0 to 30 in a second loop.
Cut points: the entry, 22 (`xor eax, eax`), the copy loop's head 24 (`rax` the bytes copied), 64 (`mov eax, r8d`),
the shift loop's head 144 (`ecx` = `i`) and 152 (`mov r8d, 1`); the `ret` at 67.

- `G6`: the registers the function changes; `S1`: `rsi` after the filter byte; `Ot`: the memory as at the entry
  outside `this[0..14)`.
- `Inv`, `Fin`, `Nx`: the invariant at the cut points, the end, and the post of `Seg.cfg`; the measure goes down at
  each cut point (the loops by their counters).
- `vX42`, `vX72`, `vX94`, `vX136`: the stretches after a jump as lemmas of their own, so no `simp` sees more than
  six register effects.
- `lhp_ok`: from the entry to the return address with `Ot` of the memory and `rax`, `rcx`, `rdx`, `rsi`, `rdi`,
  `r8` some values. The values are not followed: the spec is the control flow and the stores.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Lhp
set_option linter.unusedVariables false

/-- The `ret`. -/
def pret : List Byte := [0xc3]
theorem pret_0 : ∀ feat, Dec feat pret 0 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem w_67 : pret <+: lhp.drop 67 := by decide +kernel
theorem ret_67 (feat : Features) : Dec feat lhp 67 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 67) (k := 0) (pret_0 feat) w_67 (Nat.zero_le _)

/-- The registers the function changes. -/
abbrev G6 (g₀ : Gprs) (a c d s di x : BitVec 64) : Gprs :=
  { g₀ with rax := a, rcx := c, rdx := d, rsi := s, rdi := di, r8 := x }
/-- `rsi` after the filter byte: as at the entry, or one on. -/
abbrev S1 (g₀ : Gprs) (s : Addr) : Prop := ∃ j ≤ 1, s = g₀.rsi + BitVec.ofNat 64 j
/-- The memory as at the entry outside `this[0..14)`. -/
abbrev Ot (g₀ : Gprs) (V₀ V : Addr → Byte) : Prop := Raf.Out g₀.rdi.toNat (g₀.rdi.toNat + 14) V₀ V

/-- The invariant at the cut points: the entry; 22; 24 with `k` bytes copied; 64; 144 with `ecx` = `k`; 152. -/
def Inv (g₀ : Gprs) (V₀ : Addr → Byte) (ℓ m : Nat) (g : Gprs) (V : Addr → Byte) : Prop :=
  (ℓ = 0 ∧ m = 51 ∧ g = g₀ ∧ V = V₀) ∨
  (Ot g₀ V₀ V ∧ ((ℓ = 22 ∧ m = 50 ∧ ∃ a c d s x, S1 g₀ s ∧ g = G6 g₀ a c d s g₀.rdi x) ∨
    (ℓ = 24 ∧ ∃ k < 5, m = 45 - k ∧ ∃ c d s x, S1 g₀ s ∧ g = G6 g₀ (BitVec.ofNat 64 k) c d s g₀.rdi x) ∨
    (ℓ = 64 ∧ m = 0 ∧ ∃ a c d s di x, g = G6 g₀ a c d s di x) ∨
    (ℓ = 144 ∧ ∃ k < 31, m = 33 - k ∧
      ∃ a d s di x, g = G6 g₀ a (BitVec.setWidth 64 (BitVec.ofNat 32 k)) d s di x) ∨
    (ℓ = 152 ∧ m = 1 ∧ ∃ a c d s di x, g = G6 g₀ a c d s di x)))
/-- At the `ret`. -/
def Fin (g₀ : Gprs) (V₀ : Addr → Byte) (j : Nat) (g : Gprs) (V : Addr → Byte) : Prop :=
  j = 67 ∧ Ot g₀ V₀ V ∧ ∃ a c d s di x, g = G6 g₀ a c d s di x
/-- At an exit: a cut point's invariant with a smaller measure, or the `ret`. -/
def Nx (g₀ : Gprs) (V₀ : Addr → Byte) (m : Nat) : Post :=
  fun j g _ V => (∃ m' < m, Inv g₀ V₀ j m' g V) ∨ Fin g₀ V₀ j g V

/-! ## Accesses -/

/-- Bytes `k ..< k + m` of a range of `n`. -/
theorem fA {R : List Rgn} {b : Addr} {n : Nat} (h : ∀ i < n, Foot R (Addr.add b i)) {k m : Nat}
    (hk : k + m ≤ n) : ∀ i < m, Foot R (Addr.add (b + BitVec.ofNat 64 k) i) := fun i hi => by
  rw [show Addr.add (b + BitVec.ofNat 64 k) i = Addr.add b (k + i) from addr_add_add' b k i]
  exact h (k + i) (by omega)

theorem fA2 {R : List Rgn} {b : Addr} {n : Nat} (h : ∀ i < n, Foot R (Addr.add b i)) {j k m : Nat}
    (hk : j + k + m ≤ n) : ∀ i < m, Foot R (Addr.add (b + BitVec.ofNat 64 j + BitVec.ofNat 64 k) i) :=
  fA (fA h (k := j) (m := k + m) (by omega)) (by omega)

/-- A store inside `b[0..14)`. -/
theorem oSt {V₀ V : Addr → Byte} {b : Addr} {k n : Nat} {bs : List Byte}
    (hO : Raf.Out b.toNat (b.toNat + 14) V₀ V) (hb : b.toNat + 14 ≤ 2 ^ 64) (hn : bs.length = n)
    (hk : k + n ≤ 14) (h1 : 0 < n) : Raf.Out b.toNat (b.toNat + 14) V₀ (Vst V (b + BitVec.ofNat 64 k) bs) := by
  have ht : (b + BitVec.ofNat 64 k).toNat = b.toNat + k := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have h2 := Raf.Out.vst (V := V) (a := b + BitVec.ofNat 64 k) hn (by rw [ht]; omega)
  rw [ht] at h2
  exact hO.trans (h2.mono (by omega) (by omega))

theorem oSt0 {V₀ V : Addr → Byte} {b : Addr} {n : Nat} {bs : List Byte}
    (hO : Raf.Out b.toNat (b.toNat + 14) V₀ V) (hb : b.toNat + 14 ≤ 2 ^ 64) (hn : bs.length = n)
    (hk : n ≤ 14) : Raf.Out b.toNat (b.toNat + 14) V₀ (Vst V b bs) :=
  hO.trans ((Raf.Out.vst (V := V) (a := b) hn (by omega)).mono (by omega) (by omega))

theorem oSt2 {V₀ V : Addr → Byte} {b : Addr} {j k n : Nat} {bs : List Byte}
    (hO : Raf.Out b.toNat (b.toNat + 14) V₀ V) (hb : b.toNat + 14 ≤ 2 ^ 64) (hn : bs.length = n)
    (hk : j + k + n ≤ 14) (h1 : 0 < n) :
    Raf.Out b.toNat (b.toNat + 14) V₀ (Vst V (b + BitVec.ofNat 64 j + BitVec.ofNat 64 k) bs) := by
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  exact oSt hO hb hn (by omega) h1

/-! ## The exits -/

variable {g₀ : Gprs} {V₀ : Addr → Byte} {m : Nat} {g : Gprs} {f : Rflags} {V : Addr → Byte}
  {a c d s di x : BitVec 64}

theorem e22 (hO : Ot g₀ V₀ V) (hs : S1 g₀ s) (hg : g = G6 g₀ a c d s g₀.rdi x) : Nx g₀ V₀ 51 22 g f V :=
  Or.inl ⟨50, by omega, Or.inr ⟨hO, Or.inl ⟨rfl, rfl, a, c, d, s, x, hs, hg⟩⟩⟩

theorem e24z (ha : a = BitVec.ofNat 64 0) (hO : Ot g₀ V₀ V) (hs : S1 g₀ s) (hg : g = G6 g₀ a c d s g₀.rdi x) :
    Nx g₀ V₀ 50 24 g f V :=
  Or.inl ⟨45, by omega, Or.inr ⟨hO, Or.inr (Or.inl ⟨rfl, 0, by omega, by omega, c, d, s, x, hs,
    by subst ha; exact hg⟩)⟩⟩

theorem e24s {k : Nat} (hk : k + 1 < 5) (hO : Ot g₀ V₀ V) (hs : S1 g₀ s)
    (hg : g = G6 g₀ (BitVec.ofNat 64 k + 1#64) c d s g₀.rdi x) : Nx g₀ V₀ (45 - k) 24 g f V :=
  Or.inl ⟨45 - (k + 1), by omega, Or.inr ⟨hO, Or.inr (Or.inl ⟨rfl, k + 1, hk, rfl, c, d, s, x, hs,
    by rw [BitVec.ofNat_add]; exact hg⟩)⟩⟩

theorem e64 (hO : Ot g₀ V₀ V) (hm : 0 < m) (hg : g = G6 g₀ a c d s di x) : Nx g₀ V₀ m 64 g f V :=
  Or.inl ⟨0, hm, Or.inr ⟨hO, Or.inr (Or.inr (Or.inl ⟨rfl, rfl, a, c, d, s, di, x, hg⟩))⟩⟩

theorem e144z (hc : c = BitVec.setWidth 64 (BitVec.ofNat 32 0)) (hO : Ot g₀ V₀ V) (hm : 33 < m)
    (hg : g = G6 g₀ a c d s di x) : Nx g₀ V₀ m 144 g f V :=
  Or.inl ⟨33, hm, Or.inr ⟨hO, Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, 0, by omega, by omega, a, d, s, di, x,
    by subst hc; exact hg⟩)))⟩⟩

theorem e144s {k : Nat} (hk : k + 1 < 31) (hO : Ot g₀ V₀ V)
    (hg : g = G6 g₀ a (BitVec.setWidth 64 (BitVec.ofNat 32 k + 1#32)) d s di x) : Nx g₀ V₀ (33 - k) 144 g f V :=
  Or.inl ⟨33 - (k + 1), by omega, Or.inr ⟨hO, Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, k + 1, hk, rfl, a, d, s, di,
    x, by rw [BitVec.ofNat_add]; exact hg⟩)))⟩⟩

theorem e152 (hO : Ot g₀ V₀ V) (hm : 1 < m) (hg : g = G6 g₀ a c d s di x) : Nx g₀ V₀ m 152 g f V :=
  Or.inl ⟨1, hm, Or.inr ⟨hO, Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl, a, c, d, s, di, x, hg⟩)))⟩⟩

theorem e67 (hO : Ot g₀ V₀ V) (hg : g = G6 g₀ a c d s di x) : Nx g₀ V₀ m 67 g f V :=
  Or.inr ⟨rfl, hO, a, c, d, s, di, x, hg⟩

/-! ## The stretches after the jumps -/

variable {F : Footprint} {Wl : List Rgn}

set_option maxHeartbeats 1000000 in
/-- 94: the dictionary size 1, to 64; else `ecx` 0, to the shift loop's head 144. -/
theorem vX94 (hm : 33 < m) (hO : Ot g₀ V₀ V) (hd : ∀ i < 14, Foot F.data (Addr.add g₀.rdi i)) :
    W_94 F Wl (Nx g₀ V₀ m) (G6 g₀ a c d s g₀.rdi x) f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g₀
  dsimp only [G6] at hd ⊢
  wpx [W_94, W_108, o8, o9, BitVec.xor_self]
  all_goals repeat' (first | exact fA hd (by omega) | with_reducible rfl | apply And.intro | intro _)
  all_goals first
    | exact e64 hO (by omega) rfl
    | exact e144z (by first | rfl | decide) hO hm rfl

set_option maxHeartbeats 1000000 in
/-- 72: the `Size` check, to 64 or 94. -/
theorem vX72 (hm : 33 < m) (hO : Ot g₀ V₀ V) (hd : ∀ i < 14, Foot F.data (Addr.add g₀.rdi i)) :
    W_72 F Wl (Nx g₀ V₀ m) (G6 g₀ a c d s g₀.rdi x) f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g₀
  dsimp only [G6]
  wpx [W_72, o7]
  all_goals repeat' (first | exact vX94 hm hO hd | with_reducible rfl | apply And.intro | intro _)
  all_goals first
    | exact e64 hO (by omega) rfl

set_option maxHeartbeats 1000000 in
/-- 58: `FilterID` checked, to 72 or 64. -/
theorem vX58 (hm : 33 < m) (hO : Ot g₀ V₀ V) (hd : ∀ i < 14, Foot F.data (Addr.add g₀.rdi i)) :
    W_58 F Wl (Nx g₀ V₀ m) (G6 g₀ a c d s g₀.rdi x) f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g₀
  have f8 : ∀ i < 1, Foot F.data (Addr.add (rdi + 8#64) i) := fA hd (by omega)
  dsimp only [G6]
  wpx [W_58, o5, Op.cmpmi]
  all_goals repeat' (first | exact f8 | exact vX72 hm hO hd | with_reducible rfl | apply And.intro | intro _)
  all_goals first
    | exact e64 hO (by omega) rfl

set_option maxHeartbeats 1000000 in
/-- 42: `Size` read and stored, the props byte checked, to 64 or 58. -/
theorem vX42 {j : Nat} (hj : j ≤ 1) (hm : 33 < m) (hO : Ot g₀ V₀ V) (hb : g₀.rdi.toNat + 14 ≤ 2 ^ 64)
    (hr : ∀ i < 14, Foot F.data (Addr.add g₀.rsi i)) (hd : ∀ i < 14, Foot F.data (Addr.add g₀.rdi i))
    (hw : ∀ i < 14, Foot Wl (Addr.add g₀.rdi i)) :
    W_42 F Wl (Nx g₀ V₀ m) (G6 g₀ a c d (g₀.rsi + BitVec.ofNat 64 j) g₀.rdi x) f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g₀
  have f5 : ∀ i < 8, Foot F.data (Addr.add (rsi + BitVec.ofNat 64 j + 5#64) i) := fA2 hr (by omega)
  have f9 : ∀ i < 1, Foot F.data (Addr.add (rdi + 9#64) i) := fA hd (by omega)
  have f0 : ∀ i < 8, Foot Wl (Addr.add rdi i) := fun i hi => hw i (by omega)
  dsimp only [G6]
  wpx [W_42, o4, Op.cmpmi, BitVec.xor_self]
  all_goals repeat' (first
    | exact f0
    | exact f5
    | exact f9
    | (refine vX58 hm ?_ hd; exact oSt0 hO hb (toBytesLE_length _ _) (by decide))
    | with_reducible rfl
    | apply And.intro
    | intro _)
  all_goals first
    | exact e64 (oSt0 hO hb (toBytesLE_length _ _) (by decide)) (by omega) rfl

set_option maxHeartbeats 1000000 in
/-- 136: `ecx` one on; 31, to 64 (`r8b` = the size all ones); else back to 144. -/
theorem vX136 {k : Nat} (hk : k < 31) (hO : Ot g₀ V₀ V) :
    W_136 F Wl (Nx g₀ V₀ (33 - k)) (G6 g₀ a (BitVec.setWidth 64 (BitVec.ofNat 32 k)) d s di x) f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g₀
  dsimp only [G6]
  rcases Nat.lt_or_ge k 30 with h30 | h30
  · wpx [W_136, W_160, o11, o14, Op.setcc]
    all_goals repeat' (first | with_reducible rfl | apply And.intro | intro _)
    all_goals first
      | exact e64 hO (by omega) rfl
      | exact e144s (by omega) hO rfl
  · have e30 : k = 30 := by omega
    subst e30
    wpx [W_136, W_160, o11, o14, Op.setcc, Bool.not_true, Bool.not_false, Bool.true_eq_false, Bool.false_eq_true,
      false_implies, implies_true]
    all_goals repeat' (first | with_reducible rfl | apply And.intro | intro _)
    all_goals first
      | exact e64 hO (by omega) rfl
      | (exfalso; simp_all)

/-! ## The cut points -/

set_option maxHeartbeats 1000000 in
/-- The entry: `FilterID` 0; with a filter `buf[0]` and `rsi` one on; to 22. -/
theorem vc_0 (hb : g₀.rdi.toNat + 14 ≤ 2 ^ 64) (hr : ∀ i < 14, Foot F.data (Addr.add g₀.rsi i))
    (hw : ∀ i < 14, Foot Wl (Addr.add g₀.rdi i)) : W_0 F Wl (Nx g₀ V₀ 51) g₀ f V₀ := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g₀
  dsimp only at hr hw
  have hO : Raf.Out rdi.toNat (rdi.toNat + 14) V₀ V₀ := fun _ _ => rfl
  wpx [W_0, W_12, o0, o1]
  all_goals repeat' (first
    | exact fA hw (by omega)
    | exact fun i hi => hr i (by omega)
    | with_reducible rfl
    | apply And.intro
    | intro _)
  all_goals first
    | exact e22 (oSt (oSt hO hb (toBytesLE_length _ _) (by decide) (by decide)) hb (toBytesLE_length _ _)
        (by decide) (by decide)) ⟨1, by omega, rfl⟩ rfl
    | exact e22 (oSt hO hb (toBytesLE_length _ _) (by decide) (by decide)) ⟨0, by omega, (BitVec.add_zero _).symm⟩
        rfl

/-- 22: `xor eax, eax`, to the copy loop's head with no byte copied. -/
theorem vc_22 (hO : Ot g₀ V₀ V) (hs : S1 g₀ s) : W_22 F Wl (Nx g₀ V₀ 50) (G6 g₀ a c d s g₀.rdi x) f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g₀
  dsimp only [G6]
  wpx [W_22, o2, BitVec.xor_self]
  all_goals repeat' (first | with_reducible rfl | apply And.intro | intro _)
  all_goals first
    | exact e24z (by first | rfl | decide) hO hs rfl

set_option maxHeartbeats 1000000 in
/-- The copy loop's head, `k` bytes copied: one more, back to 24 or (5 copied) on to 42. -/
theorem vc_24 {k : Nat} (hk : k < 5) (hO : Ot g₀ V₀ V) (hs : S1 g₀ s) (hb : g₀.rdi.toNat + 14 ≤ 2 ^ 64)
    (hr : ∀ i < 14, Foot F.data (Addr.add g₀.rsi i)) (hd : ∀ i < 14, Foot F.data (Addr.add g₀.rdi i))
    (hw : ∀ i < 14, Foot Wl (Addr.add g₀.rdi i)) :
    W_24 F Wl (Nx g₀ V₀ (45 - k)) (G6 g₀ (BitVec.ofNat 64 k) c d s g₀.rdi x) f V := by
  have hs' := hs
  obtain ⟨j, hj, rfl⟩ := hs'
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g₀
  dsimp only [G6] at hr hd hw ⊢
  rcases Nat.lt_or_ge k 4 with h4 | h4
  · have fl : ∀ i < 1, Foot F.data (Addr.add (rsi + BitVec.ofNat 64 j + BitVec.ofNat 64 k) i) := fA2 hr (by omega)
    have fs : ∀ i < 1, Foot Wl (Addr.add (rdi + BitVec.ofNat 64 k + 9#64) i) := fA2 hw (by omega)
    wpx [W_24, o3]
    all_goals repeat' (first
      | exact fl
      | exact fs
      | (refine vX42 hj (by omega) ?_ hb hr hd hw
         exact oSt2 hO hb (toBytesLE_length _ _) (by omega) (by decide))
      | exact fA2 hr (by omega)
      | exact fA2 hw (by omega)
      | with_reducible rfl
      | apply And.intro
      | intro _)
    all_goals first
      | exact e24s (by omega) (oSt2 hO hb (toBytesLE_length _ _) (by omega) (by decide)) hs rfl
  · have e4 : k = 4 := by omega
    subst e4
    have fl : ∀ i < 1, Foot F.data (Addr.add (rsi + BitVec.ofNat 64 j + BitVec.ofNat 64 4) i) := fA2 hr (by omega)
    have fs : ∀ i < 1, Foot Wl (Addr.add (rdi + BitVec.ofNat 64 4 + 9#64) i) := fA2 hw (by omega)
    wpx [W_24, o3, Bool.not_true, Bool.not_false, Bool.true_eq_false, Bool.false_eq_true, false_implies,
      implies_true]
    all_goals repeat' (first
      | exact fl
      | exact fs
      | (refine vX42 hj (by omega) ?_ hb hr hd hw
         exact oSt2 hO hb (toBytesLE_length _ _) (by omega) (by decide))
      | (refine vX42 hj (by omega) ?_ hb hr hd hw
         exact oSt hO hb (toBytesLE_length _ _) (by omega) (by decide))
      | exact fA2 hr (by omega)
      | exact fA2 hw (by omega)
      | exact fA hr (by omega)
      | exact fA hw (by omega)
      | with_reducible rfl
      | apply And.intro
      | intro _)
    all_goals first
      | (exfalso; simp_all)

/-- 64: `mov eax, r8d`, to the `ret` at 67. -/
theorem vc_64 (hO : Ot g₀ V₀ V) : W_64 F Wl (Nx g₀ V₀ 0) (G6 g₀ a c d s di x) f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g₀
  dsimp only [G6]
  wpx [W_64, o6]
  all_goals repeat' (first | with_reducible rfl | apply And.intro | intro _)
  all_goals first
    | exact e67 hO rfl

set_option maxHeartbeats 1000000 in
/-- The shift loop's head, `ecx` = `k`: the size `2 << k` or `3 << k`, to 152; else on to 136. -/
theorem vc_144 {k : Nat} (hk : k < 31) (hO : Ot g₀ V₀ V) :
    W_144 F Wl (Nx g₀ V₀ (33 - k)) (G6 g₀ a (BitVec.setWidth 64 (BitVec.ofNat 32 k)) d s di x) f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g₀
  dsimp only [G6]
  wpx [W_144, W_128, o12, o10]
  all_goals repeat' (first | exact vX136 hk hO | with_reducible rfl | apply And.intro | intro _)
  all_goals first
    | exact e152 hO (by omega) rfl

/-- 152: `mov r8d, 1`, to 64. -/
theorem vc_152 (hO : Ot g₀ V₀ V) : W_152 F Wl (Nx g₀ V₀ 1) (G6 g₀ a c d s di x) f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g₀
  dsimp only [G6]
  wpx [W_152, o13]
  all_goals repeat' (first | with_reducible rfl | apply And.intro | intro _)
  all_goals first
    | exact e64 hO (by omega) rfl

theorem vcAll (hb : g₀.rdi.toNat + 14 ≤ 2 ^ 64) (hr : ∀ i < 14, Foot F.data (Addr.add g₀.rsi i))
    (hd : ∀ i < 14, Foot F.data (Addr.add g₀.rdi i)) (hw : ∀ i < 14, Foot Wl (Addr.add g₀.rdi i))
    (ℓ m : Nat) (g : Gprs) (f : Rflags) (V : Addr → Byte) (h : Inv g₀ V₀ ℓ m g V) :
    Wt ℓ F Wl (Nx g₀ V₀ m) g f V := by
  rcases h with ⟨rfl, rfl, rfl, rfl⟩ | ⟨hO, ⟨rfl, rfl, a, c, d, s, x, hs, rfl⟩ |
    ⟨rfl, k, hk, rfl, c, d, s, x, hs, rfl⟩ | ⟨rfl, rfl, a, c, d, s, di, x, rfl⟩ |
    ⟨rfl, k, hk, rfl, a, d, s, di, x, rfl⟩ | ⟨rfl, rfl, a, c, d, s, di, x, rfl⟩⟩
  · exact vc_0 hb hr hw
  · exact vc_22 hO hs
  · exact vc_24 hk hO hs hb hr hd hw
  · exact vc_64 hO
  · exact vc_144 hk hO
  · exact vc_152 hO

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {X : State} {t : Nat}

/-- `CHeader::Parse (buf, isThereFilter)` from its entry, with `buf[0..14)` readable and `this[0..14)` readable and
writable: at the return address, the return address popped, the memory as it was outside `this[0..14)`, `rax`,
`rcx`, `rdx`, `rsi`, `rdi`, `r8` some values. -/
theorem lhp_ok (c : Seg prof F Wl L s₀ o) (hin : CodeIn L lhp_at lhp) (hK : KeptW Wl s₀ X)
    (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = lhp_at)
    (hr : ∀ i < 14, Foot F.data (Addr.add X.cpu.gpr.rsi i))
    (hd : ∀ i < 14, Foot F.data (Addr.add X.cpu.gpr.rdi i))
    (hw : ∀ i < 14, Foot Wl (Addr.add X.cpu.gpr.rdi i))
    (hrs : X.cpu.gpr.rsi.toNat + 14 ≤ 2 ^ 64) (hb : X.cpu.gpr.rdi.toNat + 14 ≤ 2 ^ 64)
    (hl : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsp i)) (hsp : X.cpu.gpr.rsp.toNat + 8 ≤ 2 ^ 64)
    (hsep : X.cpu.gpr.rsp.toNat + 8 ≤ X.cpu.gpr.rdi.toNat ∨ X.cpu.gpr.rdi.toNat + 14 ≤ X.cpu.gpr.rsp.toNat)
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (hra : rdq(V, X.cpu.gpr.rsp) = e₂.add j₂)
    (k : ∀ V' : Addr → Byte, Raf.Out X.cpu.gpr.rdi.toNat (X.cpu.gpr.rdi.toNat + 14) V V' →
      ∀ (Z : State) (t' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V' → Z.cpu.rip = e₂.add j₂ →
      (∃ a c d s di x, Z.cpu.gpr = (G6 X.cpu.gpr a c d s di x).set 4 (X.cpu.gpr.rsp + 8)) →
      GoG prof L o gev gP gE Z t') :
    GoG prof L o gev gP gE X t := by
  refine c.cfg hin (fun ℓ => spAll prof ℓ) (fun ℓ m g _ V' => Inv X.cpu.gpr V ℓ m g V')
    (fun j g _ V' => Fin X.cpu.gpr V j g V') (fun ℓ m g f V' h => vcAll hb hr hd hw ℓ m g f V' h) ?_
    51 0 hK hA (by rw [addr_add_zero]; exact hrip) (Or.inl ⟨rfl, rfl, rfl, rfl⟩)
  rintro j g fl V' ⟨rfl, hV, a, c', d, s, di, x, rfl⟩ Y t' hKY hAY hrY hgY -
  have hsY : Y.cpu.gpr.rsp = X.cpu.gpr.rsp := by rw [hgY]
  have hraV : rdq(V', X.cpu.gpr.rsp) = e₂.add j₂ := by
    rw [Raf.Out.rd hV hsp hsep]
    exact hra
  refine c.s_ret hKY hAY hin (lt_len (by decide)) hrY (ret_67 _) (by rw [hsY]; exact hl) hin₂ h₂
    (by rw [hsY]; exact hraV) ?_
  rintro Z t₂ hKZ hAZ ⟨hrZ, hgZ⟩
  exact k V' hV Z t₂ hKZ hAZ hrZ ⟨a, c', d, s, di, x, by rw [hgZ, hsY, hgY]⟩

end FV7z.Lhp
