import FV7z.Osv.Cuts
import FV7z.Spec.OsVersion
import FV7z.Tun.Inv
/-!
# `_dl_discover_osversion` reads the release: the loop (PLAN.md G3, startup)

From the cut point 46, where the reading of the release begins, to the two `ret`s (138, 169): the invariants at the
cut points (`Inv`) and their conditions (`vc_*`, `vcAll`), for `Seg.cfg`.

- `Par`: what the loop is given: the release's address `p` and its 65 characters in memory `V` (`ch`, the last one
  0), the registers `g` at the cut point 46.
- `Inv`: at 46 the character at `rdi` begins a number; at 80 the one at `rsi`, in `edx`, is a digit of the number
  `ecx`; at 103 it is not; at 127 `eax` is the version; at 145 the missing numbers' bits are still to make. The
  measure goes down with the characters left.
- `Fin`: at a `ret` `eax` is `osParts 3 0` of the characters, the registers the function saved are back from its
  frame, the stack pointer is at the return address.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
open FV7z.Tun (rd1)
namespace FV7z.Osv

/-! ## Arithmetic of the characters -/

theorem sx_toNat (c : Byte) : (c.signExtend 32).toNat = c.toNat ∨
    (128 ≤ c.toNat ∧ (c.signExtend 32).toNat = c.toNat + 2 ^ 32 - 256) := by
  rw [BitVec.toNat_signExtend]
  have := c.isLt
  by_cases h : c.msb
  · right
    have h2 := (BitVec.msb_eq_true_iff_two_mul_ge).1 h
    simp [h]
    omega
  · left
    simp [h]
    omega

theorem isDig_iff (c : Byte) : isDig c = true ↔ (c - 48#8).toNat ≤ 9 := by
  have := c.isLt
  simp only [isDig, decide_eq_true_eq, BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega

/-- The low byte of a character in a register is the character. -/
theorem lo_sx (c : Byte) : BitVec.setWidth 8 (BitVec.setWidth 64 (c.signExtend 32)) = c := by
  rw [BitVec.setWidth_setWidth_of_le _ (by decide)]
  apply BitVec.eq_of_toNat_eq
  have := c.isLt
  simp only [BitVec.toNat_setWidth]
  rcases sx_toNat c with h | ⟨h1, h⟩ <;> rw [h] <;> omega

/-- `lea edx, [rcx - 0x30]`, `cmp dl, 9`: the low byte is the character less `'0'`. -/
theorem lo_sub (c : Byte) : BitVec.setWidth 8 (BitVec.setWidth 32
    (BitVec.setWidth 64 (c.signExtend 32) + 18446744073709551568#64)) = c - 48#8 := by
  rw [BitVec.setWidth_setWidth_of_le _ (by decide), BitVec.setWidth_add _ _ (by decide), lo_sx]
  bv_omega

/-- A digit in a register. -/
theorem sx_dig {c : Byte} (h : isDig c = true) : c.signExtend 32 = c.setWidth 32 := by
  have h1 : c.toNat < 128 := by
    simp only [isDig, decide_eq_true_eq] at h
    omega
  exact BitVec.signExtend_eq_setWidth_of_msb_false (BitVec.msb_eq_false_iff_two_mul_lt.2 (by omega))

/-- `lea ecx, [rcx + rcx·4]`, `lea ecx, [rdx + rcx·2 - 0x30]`: ten times the number and the digit. -/
theorem dig_step {c : Byte} (h : isDig c = true) (here : BitVec 32) :
    BitVec.setWidth 32 (BitVec.setWidth 64 (c.signExtend 32) + BitVec.setWidth 64 (BitVec.setWidth 32
      (BitVec.setWidth 64 here + BitVec.setWidth 64 here * 4#64)) * 2#64 + 18446744073709551568#64) =
      here * 10 + (c.setWidth 32 - 48#32) := by
  have h1 : c.toNat < 128 := by
    simp only [isDig, decide_eq_true_eq] at h
    omega
  have e : ∀ x : BitVec 32, BitVec.setWidth 32 (BitVec.setWidth 64 x) = x := fun x => by
    rw [BitVec.setWidth_setWidth_of_le _ (by decide), BitVec.setWidth_eq]
  rw [BitVec.setWidth_add _ _ (by decide), BitVec.setWidth_add _ _ (by decide), BitVec.setWidth_mul _ _ (by decide),
    e, e, BitVec.setWidth_add _ _ (by decide), BitVec.setWidth_mul _ _ (by decide), e,
    BitVec.signExtend_eq_setWidth_of_msb_false (BitVec.msb_eq_false_iff_two_mul_lt.2 (by omega))]
  generalize BitVec.setWidth 32 c = d
  show d + (here + here * 4#32) * 2#32 + 4294967248#32 = here * 10 + (d - 48#32)
  bv_omega

/-! ## The invariants -/

/-- What the loop is given. -/
structure Par where
  /-- The release's address. -/
  p : Addr
  /-- The registers at the cut point 46. -/
  g : Gprs
  /-- Memory. -/
  V : Addr → Byte

/-- The release's `i`-th character. -/
def Par.ch (P : Par) (i : Nat) : Byte := P.V (Addr.add P.p i)

/-- The release's characters. -/
def Par.rel (P : Par) : List Byte := (List.range 65).map P.ch

theorem Par.drop (P : Par) {i : Nat} (h : i < 65) : P.rel.drop i = P.ch i :: P.rel.drop (i + 1) := by
  have hl : i < P.rel.length := by simp only [Par.rel, List.length_map, List.length_range]; exact h
  rw [List.drop_eq_getElem_cons hl]
  simp only [Par.rel, List.getElem_map, List.getElem_range]

/-- What the loop needs of memory: the release is read, its last character is 0, and so is the frame's end. -/
structure Par.Ok (P : Par) (F : Footprint) : Prop where
  fit : P.p.toNat + 65 ≤ 2 ^ 64
  rd : ∀ i < 65, Foot F.data (Addr.add P.p i)
  nul : P.ch 64 = 0
  stk : ∀ i < 24, Foot F.data (Addr.add (P.g.rsp + 464#64) i)

/-- The version `eax` has at the `ret`. -/
def Par.R (P : Par) : BitVec 32 := osParts 3 0 P.rel

/-- A register with a character, as `movsx` leaves it. -/
abbrev sx (c : Byte) : BitVec 64 := BitVec.setWidth 64 (c.signExtend 32)

/-- The registers the loop keeps. -/
def Kp (g₀ g : Gprs) : Prop := g.rsp = g₀.rsp ∧ g.r13 = g₀.r13 ∧ g.r14 = g₀.r14 ∧ g.r15 = g₀.r15

/-- The invariant at the cut points. -/
def Inv (P : Par) (ℓ n : Nat) (g : Gprs) (V : Addr → Byte) : Prop :=
  V = P.V ∧ Kp P.g g ∧
    ((ℓ = 46 ∧ ∃ i L ver, i ≤ 64 ∧ L ≤ 2 ∧ n = 3 * (66 - i) ∧ g.rdi = Addr.add P.p i ∧
        g.rax = BitVec.setWidth 64 ver ∧ g.r8 = BitVec.ofNat 64 (2 - L) ∧ osParts (L + 1) ver (P.rel.drop i) = P.R) ∨
      (ℓ = 80 ∧ ∃ j L ver here, j ≤ 64 ∧ L ≤ 2 ∧ n = 3 * (66 - j) + 1 ∧ isDig (P.ch j) = true ∧
        g.rsi = Addr.add P.p j ∧ g.rdx = sx (P.ch j) ∧ g.rcx = BitVec.setWidth 64 here ∧
        g.rax = BitVec.setWidth 64 ver ∧ g.r8 = BitVec.ofNat 64 (2 - L) ∧
        osTail (osParts L) L ver (osNum here (P.rel.drop j)).1 (osNum here (P.rel.drop j)).2 = P.R) ∨
      (ℓ = 103 ∧ ∃ j L ver here, j ≤ 64 ∧ L ≤ 2 ∧ n = 3 * (66 - j) + 2 ∧ isDig (P.ch j) = false ∧
        g.rsi = Addr.add P.p j ∧ g.rdx = sx (P.ch j) ∧ g.rcx = BitVec.setWidth 64 here ∧
        g.rax = BitVec.setWidth 64 ver ∧ g.r8 = BitVec.ofNat 64 (2 - L) ∧
        osTail (osParts L) L ver here (P.rel.drop j) = P.R) ∨
      (ℓ = 127 ∧ n = 0 ∧ g.rax = BitVec.setWidth 64 P.R) ∨
      (ℓ = 145 ∧ n = 0 ∧ ∃ parts ver, parts ≤ 2 ∧ g.r8 = BitVec.ofNat 64 parts ∧ g.rax = BitVec.setWidth 64 ver ∧
        ver <<< (8 * (3 - parts)) = P.R))

/-- At a `ret`. -/
def Fin (P : Par) (j : Nat) (g : Gprs) (V : Addr → Byte) : Prop :=
  (j = 138 ∨ j = 169) ∧ V = P.V ∧ g.rax = BitVec.setWidth 64 P.R ∧ g.rsp = P.g.rsp + 488#64 ∧
    g.rbx = rdq(P.V, P.g.rsp + 464#64) ∧ g.rbp = rdq(P.V, P.g.rsp + 472#64) ∧ g.r12 = rdq(P.V, P.g.rsp + 480#64) ∧
    g.r13 = P.g.r13 ∧ g.r14 = P.g.r14 ∧ g.r15 = P.g.r15

/-- What a condition's exits need. -/
abbrev Nx (P : Par) (n : Nat) : Post := fun j' g' _ V' => (∃ n', n' < n ∧ Inv P j' n' g' V') ∨ Fin P j' g' V'

variable {F : Footprint} {Wl : List Rgn} {P : Par}

theorem add_succ (p : Addr) (i : Nat) : Addr.add p i + 1#64 = Addr.add p (i + 1) := by
  simp only [Addr.add]
  bv_omega

theorem not_dig_nul : isDig (0 : Byte) = false := by decide

/-- A digit is not the last character. -/
theorem lt_of_dig (hP : P.Ok F) {i : Nat} (hi : i ≤ 64) (h : isDig (P.ch i) = true) : i < 64 := by
  rcases Nat.lt_or_ge i 64 with h1 | h1
  · exact h1
  · obtain rfl : i = 64 := by omega
    rw [hP.nul, not_dig_nul] at h
    exact absurd h (by decide)

theorem rd_ch (P : Par) (i : Nat) : ofBytesLE 8 (List.map P.V (byteAddrs (Addr.add P.p i) 1)) = P.ch i := rd1 _ _

theorem rd_foot (hP : P.Ok F) {i : Nat} (hi : i < 65) : ∀ k < 1, Foot F.data (Addr.add (Addr.add P.p i) k) := by
  intro k hk
  obtain rfl : k = 0 := by omega
  rw [addr_add_zero]
  exact hP.rd i hi

theorem dig_of {c : Byte} (h : (!(decide ((c - 48#8).toNat < 9) || decide (c - 48#8 = 9#8))) = false) :
    isDig c = true := by
  rw [isDig_iff]
  rw [Bool.not_eq_false', Bool.or_eq_true, decide_eq_true_eq, decide_eq_true_eq] at h
  rcases h with h | h
  · omega
  · rw [h]
    decide

theorem not_dig_of {c : Byte} (h : (!(decide ((c - 48#8).toNat < 9) || decide (c - 48#8 = 9#8))) = true) :
    isDig c = false := by
  rw [← Bool.not_eq_true, isDig_iff]
  rw [Bool.not_eq_true', Bool.or_eq_false_iff, decide_eq_false_iff_not, decide_eq_false_iff_not] at h
  intro h3
  exact h.2 (BitVec.eq_of_toNat_eq (by simp only [BitVec.toNat_ofNat]; omega))

/-- At 46: the character at `rdi` begins a number, or the reading ends. -/
theorem vc_46 (hP : P.Ok F) {n : Nat} {g : Gprs} {f : Rflags} {V : Addr → Byte} {i L : Nat} {ver : BitVec 32}
    (hV : V = P.V) (hk : Kp P.g g) (hi : i ≤ 64) (hL : L ≤ 2) (hn : n = 3 * (66 - i)) (hdi : g.rdi = Addr.add P.p i)
    (hax : g.rax = BitVec.setWidth 64 ver) (h8 : g.r8 = BitVec.ofNat 64 (2 - L))
    (hR : osParts (L + 1) ver (P.rel.drop i) = P.R) : W_46 F Wl (Nx P n) g f V := by
  subst hV
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  obtain rfl : rdi = Addr.add P.p i := hdi
  obtain rfl : rax = BitVec.setWidth 64 ver := hax
  obtain rfl : r8 = BitVec.ofNat 64 (2 - L) := h8
  rw [P.drop (by omega)] at hR
  wpx [W_46, W_57, W_77, o3, o4, o5, Op.ldsxb]
  simp only [rd_ch, lo_sub, add_succ]
  refine ⟨rd_foot hP (Nat.lt_succ_of_le hi), fun h => ?_, fun h => ?_⟩
  · -- not a digit: the missing numbers
    have hd := not_dig_of h
    refine Or.inl ⟨0, by omega, rfl, hk,
      Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl, 2 - L, ver, by omega, rfl, rfl, ?_⟩)))⟩
    rw [← hR, osParts, hd]
    show _ = ver <<< (8 * (L + 1))
    congr 2
    omega
  · have hd := dig_of h
    have h64 := lt_of_dig hP hi hd
    rw [osParts, hd] at hR
    replace hR : osTail (osParts L) L ver (osNum (BitVec.setWidth 32 (P.ch i) - 48) (List.drop (i + 1) P.rel)).1
      (osNum (BitVec.setWidth 32 (P.ch i) - 48) (List.drop (i + 1) P.rel)).2 = P.R := hR
    refine ⟨rd_foot hP (Nat.succ_lt_succ h64), fun h' => ?_, fun h' => ?_⟩
    · have hd' := not_dig_of h'
      refine Or.inl ⟨3 * (66 - (i + 1)) + 2, by omega, rfl, hk, Or.inr (Or.inr (Or.inl ⟨rfl, i + 1, L,
        ver, _, by omega, hL, rfl, hd', rfl, rfl, rfl, rfl, rfl, ?_⟩))⟩
      rw [sx_dig hd, ← hR, P.drop (i := i + 1) (Nat.succ_lt_succ h64), osNum, hd']
      rfl
    · have hd' := dig_of h'
      refine Or.inl ⟨3 * (66 - (i + 1)) + 1, by omega, rfl, hk, Or.inr (Or.inl ⟨rfl, i + 1, L,
        ver, _, by omega, hL, rfl, hd', rfl, rfl, rfl, rfl, rfl, ?_⟩)⟩
      rw [sx_dig hd]
      exact hR

/-- At 80: one more digit of the number. -/
theorem vc_80 (hP : P.Ok F) {n : Nat} {g : Gprs} {f : Rflags} {V : Addr → Byte} {j L : Nat} {ver here : BitVec 32}
    (hV : V = P.V) (hk : Kp P.g g) (hj : j ≤ 64) (hL : L ≤ 2) (hn : n = 3 * (66 - j) + 1)
    (hd : isDig (P.ch j) = true) (hsi : g.rsi = Addr.add P.p j) (hdx : g.rdx = sx (P.ch j))
    (hcx : g.rcx = BitVec.setWidth 64 here) (hax : g.rax = BitVec.setWidth 64 ver)
    (h8 : g.r8 = BitVec.ofNat 64 (2 - L))
    (hR : osTail (osParts L) L ver (osNum here (P.rel.drop j)).1 (osNum here (P.rel.drop j)).2 = P.R) :
    W_80 F Wl (Nx P n) g f V := by
  subst hV
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  obtain rfl : rsi = Addr.add P.p j := hsi
  obtain rfl : rdx = sx (P.ch j) := hdx
  obtain rfl : rcx = BitVec.setWidth 64 here := hcx
  obtain rfl : rax = BitVec.setWidth 64 ver := hax
  obtain rfl : r8 = BitVec.ofNat 64 (2 - L) := h8
  have h64 := lt_of_dig hP hj hd
  rw [P.drop (Nat.lt_succ_of_lt h64), osNum, hd] at hR
  simp only [↓reduceIte] at hR
  wpx [W_80, o6, Op.ldsxb]
  simp only [rd_ch, lo_sub, add_succ, dig_step hd here]
  refine ⟨rd_foot hP (Nat.succ_lt_succ h64), fun h => ?_, fun h => ?_⟩
  · have hd' := dig_of (c := P.ch (j + 1)) (by rw [h]; rfl)
    exact Or.inl ⟨3 * (66 - (j + 1)) + 1, by omega, rfl, hk, Or.inr (Or.inl ⟨rfl, j + 1, L, ver, _, by omega, hL,
      rfl, hd', rfl, rfl, rfl, rfl, rfl, hR⟩)⟩
  · have hd' := not_dig_of (c := P.ch (j + 1)) (by rw [h]; rfl)
    refine Or.inl ⟨3 * (66 - (j + 1)) + 2, by omega, rfl, hk, Or.inr (Or.inr (Or.inl ⟨rfl, j + 1, L, ver, _,
      by omega, hL, rfl, hd', rfl, rfl, rfl, rfl, rfl, ?_⟩))⟩
    rw [P.drop (i := j + 1) (Nat.succ_lt_succ h64), osNum, hd'] at hR
    simp only [Bool.false_eq_true, ↓reduceIte] at hR
    rw [P.drop (i := j + 1) (Nat.succ_lt_succ h64)]
    exact hR

theorem r8_iff {L : Nat} (hL : L ≤ 2) : BitVec.setWidth 32 (BitVec.ofNat 64 (2 - L)) + 1#32 = 3#32 ↔ L = 0 := by
  obtain rfl | rfl | rfl : L = 0 ∨ L = 1 ∨ L = 2 := by omega
  all_goals decide

theorem r8_new {L : Nat} (hL : L ≤ 2) :
    BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 64 (2 - L)) + 1#32) = BitVec.ofNat 64 (3 - L) := by
  obtain rfl | rfl | rfl : L = 0 ∨ L = 1 ∨ L = 2 := by omega
  all_goals decide

/-- The low byte of a character in a 32-bit register. -/
theorem lo_sx' (c : Byte) : BitVec.setWidth 8 (c.signExtend 32) = c := by
  have h := lo_sx c
  rwa [BitVec.setWidth_setWidth_of_le _ (by decide)] at h

theorem not_46_nul : (0 : Byte) ≠ 46 := by decide

/-- At 103: after a number. -/
theorem vc_103 (hP : P.Ok F) {n : Nat} {g : Gprs} {f : Rflags} {V : Addr → Byte} {j L : Nat} {ver here : BitVec 32}
    (hV : V = P.V) (hk : Kp P.g g) (hj : j ≤ 64) (hL : L ≤ 2) (hn : n = 3 * (66 - j) + 2)
    (hd : isDig (P.ch j) = false) (hsi : g.rsi = Addr.add P.p j) (hdx : g.rdx = sx (P.ch j))
    (hcx : g.rcx = BitVec.setWidth 64 here) (hax : g.rax = BitVec.setWidth 64 ver)
    (h8 : g.r8 = BitVec.ofNat 64 (2 - L))
    (hR : osTail (osParts L) L ver here (P.rel.drop j) = P.R) :
    W_103 F Wl (Nx P n) g f V := by
  subst hV
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  obtain rfl : rsi = Addr.add P.p j := hsi
  obtain rfl : rdx = sx (P.ch j) := hdx
  obtain rfl : rcx = BitVec.setWidth 64 here := hcx
  obtain rfl : rax = BitVec.setWidth 64 ver := hax
  obtain rfl : r8 = BitVec.ofNat 64 (2 - L) := h8
  rw [P.drop (Nat.lt_succ_of_le hj), osTail] at hR
  wpx [W_103, W_121, W_139, o7, o8]
  simp only [lo_sx', add_succ, r8_new hL]
  refine fun fl af => ⟨fun h1 => ?_, fun h1 => ?_⟩
  · -- not a `.`: the reading ends
    have hc : P.ch j ≠ 46 := by simpa using h1
    simp only [hc, ↓reduceIte] at hR
    refine ⟨fun h2 => ?_, fun h2 => ?_⟩
    · obtain rfl : L = 0 := (r8_iff hL).1 (of_decide_eq_true h2)
      rw [show (ver <<< 8 ||| here) <<< (8 * 0) = ver <<< 8 ||| here from BitVec.shiftLeft_zero _] at hR
      refine Or.inl ⟨0, by omega, rfl, hk, Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, ?_⟩)))⟩
      rw [← hR]
    · have hL0 : L ≠ 0 := fun e => of_decide_eq_false h2 ((r8_iff hL).2 e)
      refine Or.inl ⟨0, by omega, rfl, hk, Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl, 3 - L, _, by omega, rfl, rfl,
        ?_⟩)))⟩
      rw [← hR]
      congr 1
      omega
  · have hc : P.ch j = 46 := by simpa using h1
    simp only [hc, ↓reduceIte] at hR
    have h64 : j < 64 := by
      rcases Nat.lt_or_ge j 64 with h | h
      · exact h
      · obtain rfl : j = 64 := by omega
        rw [hP.nul] at hc
        exact absurd hc not_46_nul
    refine ⟨fun h2 => ?_, fun h2 => ?_⟩
    · have hL0 : L ≠ 0 := fun e => by
        rw [Bool.not_eq_true', decide_eq_false_iff_not] at h2
        exact h2 ((r8_iff hL).2 e)
      obtain ⟨L', rfl⟩ : ∃ L', L = L' + 1 := ⟨L - 1, by omega⟩
      exact Or.inl ⟨3 * (66 - (j + 1)), by omega, rfl, hk, Or.inl ⟨rfl, j + 1, L', _, by omega, by omega, rfl, rfl,
        rfl, congrArg (BitVec.ofNat 64) (by omega), hR⟩⟩
    · obtain rfl : L = 0 := by
        rw [Bool.not_eq_false', decide_eq_true_eq] at h2
        exact (r8_iff hL).1 h2
      refine Or.inl ⟨0, by omega, rfl, hk, Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, ?_⟩)))⟩
      rw [← hR]
      rfl

theorem stk0 (hP : P.Ok F) : ∀ i < 8, Foot F.data (Addr.add (P.g.rsp + 464#64) i) :=
  fun i hi => hP.stk i (by omega)

theorem stk8 (hP : P.Ok F) : ∀ i < 8, Foot F.data (Addr.add (P.g.rsp + 464#64 + 8) i) := by
  intro i hi
  have e : Addr.add (P.g.rsp + 464#64 + 8) i = Addr.add (P.g.rsp + 464#64) (8 + i) := by
    simp only [Addr.add]
    bv_omega
  rw [e]
  exact hP.stk (8 + i) (by omega)

theorem stk16 (hP : P.Ok F) : ∀ i < 8, Foot F.data (Addr.add (P.g.rsp + 464#64 + 8 + 8) i) := by
  intro i hi
  have e : Addr.add (P.g.rsp + 464#64 + 8 + 8) i = Addr.add (P.g.rsp + 464#64) (16 + i) := by
    simp only [Addr.add]
    bv_omega
  rw [e]
  exact hP.stk (16 + i) (by omega)

theorem sp_488 (x : BitVec 64) : x + 464#64 + 8 + 8 + 8 = x + 488#64 := by bv_omega
theorem sp_472 (x : BitVec 64) : x + 464#64 + 8 = x + 472#64 := by bv_omega
theorem sp_480 (x : BitVec 64) : x + 464#64 + 8 + 8 = x + 480#64 := by bv_omega

/-- At 127: the registers the function saved are taken from its frame. -/
theorem vc_127 (hP : P.Ok F) {g : Gprs} {f : Rflags} {V : Addr → Byte} (hV : V = P.V) (hk : Kp P.g g)
    (hax : g.rax = BitVec.setWidth 64 P.R) : W_127 F Wl (Nx P 0) g f V := by
  subst hV
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  obtain rfl : rax = BitVec.setWidth 64 P.R := hax
  obtain ⟨hsp, h13, h14, h15⟩ := hk
  obtain rfl : rsp = P.g.rsp := hsp
  wpx [W_127, o9]
  exact ⟨stk0 hP, stk8 hP, stk16 hP,
    Or.inr ⟨Or.inl rfl, rfl, rfl, sp_488 _, rfl, by rw [sp_472], by rw [sp_480], h13, h14, h15⟩⟩

theorem shl_parts {parts : Nat} (hp : parts ≤ 2) (ver : BitVec 32) :
    ver <<< ((BitVec.setWidth 8 ((3#32 - BitVec.setWidth 32 (BitVec.ofNat 64 parts)) <<< 3)).toNat % 32) =
      ver <<< (8 * (3 - parts)) := by
  obtain rfl | rfl | rfl : parts = 0 ∨ parts = 1 ∨ parts = 2 := by omega
  all_goals rfl

/-- At 145: the missing numbers' bits, and the registers the function saved are taken from its frame. -/
theorem vc_145 (hP : P.Ok F) {g : Gprs} {f : Rflags} {V : Addr → Byte} {parts : Nat} {ver : BitVec 32} (hV : V = P.V)
    (hk : Kp P.g g) (hp : parts ≤ 2) (h8 : g.r8 = BitVec.ofNat 64 parts) (hax : g.rax = BitVec.setWidth 64 ver)
    (hR : ver <<< (8 * (3 - parts)) = P.R) : W_145 F Wl (Nx P 0) g f V := by
  subst hV
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  obtain rfl : rax = BitVec.setWidth 64 ver := hax
  obtain rfl : r8 = BitVec.ofNat 64 parts := h8
  obtain ⟨hsp, h13, h14, h15⟩ := hk
  obtain rfl : rsp = P.g.rsp := hsp
  wpx [W_145, o10]
  simp only [shl_parts hp, hR]
  exact ⟨stk0 hP, stk8 hP, fun _ => ⟨stk16 hP, fun _ =>
    Or.inr ⟨Or.inr rfl, rfl, rfl, sp_488 _, rfl, by rw [sp_472], by rw [sp_480], h13, h14, h15⟩⟩⟩

/-- The conditions of the cut points from 46 on. -/
theorem vcAll (hP : P.Ok F) (ℓ n : Nat) (g : Gprs) (f : Rflags) (V : Addr → Byte) (h : Inv P ℓ n g V) :
    Wt ℓ F Wl (Nx P n) g f V := by
  obtain ⟨hV, hk, h | h | h | h | h⟩ := h
  · obtain ⟨rfl, i, L, ver, hi, hL, hn, hdi, hax, h8, hR⟩ := h
    exact vc_46 (f := f) hP hV hk hi hL hn hdi hax h8 hR
  · obtain ⟨rfl, j, L, ver, here, hj, hL, hn, hd, hsi, hdx, hcx, hax, h8, hR⟩ := h
    exact vc_80 (f := f) hP hV hk hj hL hn hd hsi hdx hcx hax h8 hR
  · obtain ⟨rfl, j, L, ver, here, hj, hL, hn, hd, hsi, hdx, hcx, hax, h8, hR⟩ := h
    exact vc_103 (f := f) hP hV hk hj hL hn hd hsi hdx hcx hax h8 hR
  · obtain ⟨rfl, rfl, hax⟩ := h
    exact vc_127 (f := f) hP hV hk hax
  · obtain ⟨rfl, rfl, parts, ver, hp, h8, hax, hR⟩ := h
    exact vc_145 (f := f) hP hV hk hp h8 hax hR

end FV7z.Osv
