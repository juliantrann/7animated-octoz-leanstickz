import FV7z.U16.Cuts
import FV7z.U8c.Holds
/-!
# `Utf8_To_Utf16`: the characters the code counts, the frame and the stack (PLAN.md §M, M1)

7-Zip 26.06's `Utf8_To_Utf16 (wchar_t *dest, size_t *destLen, const char *src, const char *srcLim, unsigned flags)`
at `0x451690` in `7zzs` (`CPP/Common/UTFConvert.cpp`; `objdump -d`; `wchar_t` is 4 bytes). The code reads the bytes
of `[src, srcLim)` once, from the first on: a byte under `0x80` is one character; a byte that cannot start a form is
one character (`0xFFFD`, or the byte plus `0xEF00` with bit 1 of `flags`); a byte `0xC2`-`0xF4` starts a form of 1 to
3 more bytes (`nc`), which the inner loop reads while they are `0x80`-`0xBF`, checking an overlong form, a surrogate
(bit 0 of `flags`) and a value past `0x10FFFF` at the first one. A form that fails is one character, the code going
on after the lead byte (bit 1) or after the bytes read; a whole form is one character, two for a value past
`0xFFFF` (a surrogate pair), or with bit 2 of `flags` and the `0xEF80` class one character for the lead byte alone.
The stores go to `dest + 4 * count` when `dest` is not 0; at the end `*destLen` gets the count and `eax` 1.

- `inn`: the inner loop from a state of it, as the code goes (`m` the bytes left after the next, `e` the bytes read,
  `d` the value so far); `fin`: the characters a lead byte's form gives and where the code goes on; `step`, `cnt`:
  one lead byte, the characters from the `k`-th byte on.
- `Fr Vb D W V`: `V` is `Vb` but at the `W` bytes from `D`; `frS`: a store of 4 bytes within them.
- `Vs0`, `Vs1`: the memory after the six `push`es and the store of `destLen` below the stack pointer, and after the
  store of `flags & 4` as well; their reads.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
open FV7z.U8c (addK pret pret_0)
open FV7z.Tun (rd_Vst rd_Vst_self Vst_out)
namespace FV7z.U16

/-- A bound on `s - c` and the bytes from it, `c` a literal. -/
macro "tsl" : tactic => `(tactic| (simp only [toBytesLE_length, BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.reducePow,
  Nat.reduceMod]; omega))

/-- The `ret`. -/
theorem w_335 : pret <+: u16.drop 335 := by decide +kernel
theorem ret_335 (feat : Features) : Dec feat u16 335 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 335) (k := 0) (pret_0 feat) w_335 (Nat.zero_le _)

/-! ## The bytes and their classes, in the code's terms -/

/-- The `k`-th byte from `p`. -/
abbrev by8 (V : Addr → Byte) (p : Addr) (k : Nat) : BitVec 8 :=
  ofBytesLE 8 (List.map V (byteAddrs (p + BitVec.ofNat 64 k) 1))

abbrev s8 (b : BitVec 8) : BitVec 8 := BitVec.setWidth 8 (BitVec.setWidth 32 b)
/-- `test al, al; js`: not under `0x80`. -/
abbrev na (b : BitVec 8) : Bool := (s8 b &&& s8 b).msb
abbrev l62 (b : BitVec 8) : BitVec 8 :=
  BitVec.setWidth 8 (BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.setWidth 32 b) + 62#64))
/-- `lea edx, [rax+0x3e]; cmp dl, 0x32; jbe`: `0xC2`-`0xF4`, a lead byte. -/
abbrev lv (b : BitVec 8) : Bool := decide ((l62 b).toNat < 50) || decide (l62 b = 50#8)
abbrev g223 (b : BitVec 8) : Bool := !(decide ((s8 b).toNat < 223) || decide (s8 b = 223#8))
abbrev g239 (b : BitVec 8) : Bool := !(decide ((s8 b).toNat < 239) || decide (s8 b = 239#8))
/-- The bytes after a lead byte. -/
def nc (b : BitVec 8) : Nat := bif g223 b then (bif g239 b then 3 else 2) else 1
/-- `-0xc0`, `-0xe0`, `-0xf0`. -/
def bse : Nat → Nat
  | 1 => 18446744073709551424
  | 2 => 18446744073709551392
  | _ => 18446744073709551376
/-- The value of a lead byte. -/
abbrev d0 (b : BitVec 8) (j : Nat) : BitVec 32 :=
  BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.setWidth 32 (s8 b)) + BitVec.ofNat 64 (bse j))

abbrev ty (y : BitVec 8) : BitVec 32 := BitVec.setWidth 32 y + 4294967168#32
/-- Not `0x80`-`0xBF`. -/
abbrev bad (y : BitVec 8) : Bool := !(decide ((ty y).toNat < 63) || decide (ty y = 63#32))
abbrev acc (d : BitVec 32) (y : BitVec 8) : BitVec 32 := d <<< 6 ||| ty y
/-- The least value above the value so far: an overlong form. -/
abbrev ovl (c d : BitVec 32) : Bool := !(decide (c.toNat < d.toNat) || decide (c = d))
/-- Not a surrogate's top bits. -/
abbrev nsg (d : BitVec 32) : Bool := !decide (d &&& 992#32 = 864#32)
abbrev l271 (d : BitVec 32) : Bool := decide (d.toNat < 271) || decide (d = 271#32)
/-- The `0xEF80` class. -/
abbrev esc (d : BitVec 32) : Bool := decide (d &&& 4294967168#32 = 61312#32)
/-- Past `0xFFFF`: a surrogate pair. -/
abbrev big (d : BitVec 32) : Bool := !(decide (d.toNat < 65535) || decide (d = 65535#32))
abbrev zr (x : BitVec 32) : Bool := x &&& x == 0

theorem nc_1 {b : BitVec 8} (h : g223 b = false) : nc b = 1 := by simp only [nc, h, cond_false]
theorem nc_2 {b : BitVec 8} (h : g223 b = true) (h' : g239 b = false) : nc b = 2 := by
  simp only [nc, h, h', cond_true, cond_false]
theorem nc_3 {b : BitVec 8} (h : g223 b = true) (h' : g239 b = true) : nc b = 3 := by
  simp only [nc, h, h', cond_true]

/-! ## The count -/

/-- How the inner loop ends: an error with the bytes read, or a value with them. -/
inductive Res where
  | err (e : Nat)
  | ok (d : BitVec 32) (e : Nat)

/-- The inner loop from a state of it: `m` the bytes left after the next, `e` read, `d` the value so far, `c` the least
value the first byte must reach, `u` bit 0 of `flags`. -/
def inn (V : Addr → Byte) (p : Addr) (n k : Nat) (u : Bool) (c : BitVec 32) (m e : Nat) (d : BitVec 32) : Res :=
  if k + 1 + e = n then .err e
  else if bad (by8 V p (k + 1 + e)) = true then .err e
  else if e = 0 ∧ ovl c (acc d (by8 V p (k + 1 + e))) = true then .err 1
  else if e = 0 ∧ m = 1 ∧ u = true ∧ nsg (acc d (by8 V p (k + 1 + e))) = false then .err 1
  else if e = 0 ∧ m = 2 ∧ l271 (acc d (by8 V p (k + 1 + e))) = false then .err 1
  else if hm : m = 0 then .ok (acc d (by8 V p (k + 1 + e))) (e + 1)
  else inn V p n k u c (m - 1) (e + 1) (acc d (by8 V p (k + 1 + e)))
termination_by m

/-- The characters a lead byte's form gives, and the byte the code goes on at (`z2`: bit 1 of `flags` clear, `z4`:
bit 2 clear). -/
def fin (k : Nat) (z2 z4 : Bool) : Res → Nat × Nat
  | .err e => (1, bif z2 then k + 1 + e else k + 1)
  | .ok d e => bif !z4 && esc d then (1, k + 1) else bif big d then (2, k + 1 + e) else (1, k + 1 + e)

theorem fin_gt (k : Nat) (z2 z4 : Bool) : ∀ r : Res, k < (fin k z2 z4 r).2
  | .err e => by cases z2 <;> simp only [fin, cond_true, cond_false] <;> omega
  | .ok d e => by
    simp only [fin]
    cases (!z4 && esc d) <;> cases big d <;> simp only [cond_true, cond_false] <;> omega

/-- One byte from the `k`-th: a lead byte's form, else one character. -/
def step (V : Addr → Byte) (p : Addr) (n : Nat) (u z2 z4 : Bool) (k : Nat) : Nat × Nat :=
  bif na (by8 V p k) && lv (by8 V p k) then
    fin k z2 z4 (inn V p n k u (128#32 >>> nc (by8 V p k)) (nc (by8 V p k) - 1) 0 (d0 (by8 V p k) (nc (by8 V p k))))
  else (1, k + 1)

section step
variable {V : Addr → Byte} {p : Addr} {n : Nat} {u z2 z4 : Bool} {k : Nat}

theorem step_gt : k < (step V p n u z2 z4 k).2 := by
  unfold step
  cases (na (by8 V p k) && lv (by8 V p k)) <;> simp only [cond_true, cond_false]
  · omega
  · exact fin_gt _ _ _ _

theorem step_a (h : na (by8 V p k) = false) : step V p n u z2 z4 k = (1, k + 1) := by
  simp only [step, h, Bool.false_and, cond_false]
theorem step_b (h : lv (by8 V p k) = false) : step V p n u z2 z4 k = (1, k + 1) := by
  simp only [step, h, Bool.and_false, cond_false]
theorem step_c (h : na (by8 V p k) = true) (h' : lv (by8 V p k) = true) : step V p n u z2 z4 k =
    fin k z2 z4 (inn V p n k u (128#32 >>> nc (by8 V p k)) (nc (by8 V p k) - 1) 0
      (d0 (by8 V p k) (nc (by8 V p k)))) := by
  simp only [step, h, h', Bool.and_self, cond_true]

end step

/-- The characters from the `k`-th byte on. -/
def cnt (V : Addr → Byte) (p : Addr) (n : Nat) (u z2 z4 : Bool) (k : Nat) : Nat :=
  if hk : k < n then (step V p n u z2 z4 k).1 + cnt V p n u z2 z4 (step V p n u z2 z4 k).2 else 0
termination_by n - k
decreasing_by
  have := step_gt (V := V) (p := p) (n := n) (u := u) (z2 := z2) (z4 := z4) (k := k)
  omega

/-- What is left from a lead byte's form on: its characters and the ones after. -/
def rem (V : Addr → Byte) (p : Addr) (n : Nat) (u z2 z4 : Bool) (k : Nat) (r : Res) : Nat :=
  (fin k z2 z4 r).1 + cnt V p n u z2 z4 (fin k z2 z4 r).2

section cnt
variable {V : Addr → Byte} {p : Addr} {n : Nat} {u z2 z4 : Bool} {k : Nat}

theorem cnt_lt (hk : k < n) :
    cnt V p n u z2 z4 k = (step V p n u z2 z4 k).1 + cnt V p n u z2 z4 (step V p n u z2 z4 k).2 := by
  rw [cnt, dif_pos hk]
theorem cnt_ge (hk : n ≤ k) : cnt V p n u z2 z4 k = 0 := by
  rw [cnt, dif_neg (by omega)]

theorem nt {b : Bool} (h : b = false) : ¬ b = true := by simp [h]

/-- The inner loop's steps. -/
theorem inn_end {c : BitVec 32} {m e : Nat} {d : BitVec 32} (h : k + 1 + e = n) :
    inn V p n k u c m e d = .err e := by
  rw [inn, if_pos h]
theorem inn_bad {c : BitVec 32} {m e : Nat} {d : BitVec 32} (h : ¬ k + 1 + e = n)
    (hb : bad (by8 V p (k + 1 + e)) = true) : inn V p n k u c m e d = .err e := by
  rw [inn, if_neg h, if_pos hb]
theorem inn_ovl {c : BitVec 32} {m : Nat} {d : BitVec 32} (h : ¬ k + 1 + 0 = n)
    (hb : bad (by8 V p (k + 1 + 0)) = false) (ho : ovl c (acc d (by8 V p (k + 1 + 0))) = true) :
    inn V p n k u c m 0 d = .err 1 := by
  rw [inn, if_neg h, if_neg (nt hb), if_pos ⟨rfl, ho⟩]
theorem inn_sur {c : BitVec 32} {d : BitVec 32} (h : ¬ k + 1 + 0 = n)
    (hb : bad (by8 V p (k + 1 + 0)) = false) (ho : ovl c (acc d (by8 V p (k + 1 + 0))) = false) (hu : u = true)
    (hs : nsg (acc d (by8 V p (k + 1 + 0))) = false) : inn V p n k u c 1 0 d = .err 1 := by
  have h3 : ¬ (0 = 0 ∧ ovl c (acc d (by8 V p (k + 1 + 0))) = true) := fun h' => nt ho h'.2
  rw [inn, if_neg h, if_neg (nt hb), if_neg h3, if_pos ⟨rfl, rfl, hu, hs⟩]
theorem inn_hi {c : BitVec 32} {d : BitVec 32} (h : ¬ k + 1 + 0 = n)
    (hb : bad (by8 V p (k + 1 + 0)) = false) (ho : ovl c (acc d (by8 V p (k + 1 + 0))) = false)
    (hl : l271 (acc d (by8 V p (k + 1 + 0))) = false) : inn V p n k u c 2 0 d = .err 1 := by
  have h3 : ¬ (0 = 0 ∧ ovl c (acc d (by8 V p (k + 1 + 0))) = true) := fun h' => nt ho h'.2
  have h4 : ¬ (0 = 0 ∧ 2 = 1 ∧ u = true ∧ nsg (acc d (by8 V p (k + 1 + 0))) = false) := fun h' => by
    have := h'.2.1; omega
  rw [inn, if_neg h, if_neg (nt hb), if_neg h3, if_neg h4, if_pos ⟨rfl, rfl, hl⟩]
/-- A byte read and kept: on with the next, or the value. -/
theorem inn_go {c : BitVec 32} {m e : Nat} {d : BitVec 32} (h : ¬ k + 1 + e = n)
    (hb : bad (by8 V p (k + 1 + e)) = false) (ho : ¬ (e = 0 ∧ ovl c (acc d (by8 V p (k + 1 + e))) = true))
    (hs : ¬ (e = 0 ∧ m = 1 ∧ u = true ∧ nsg (acc d (by8 V p (k + 1 + e))) = false))
    (hl : ¬ (e = 0 ∧ m = 2 ∧ l271 (acc d (by8 V p (k + 1 + e))) = false)) :
    inn V p n k u c m e d = if m = 0 then .ok (acc d (by8 V p (k + 1 + e))) (e + 1)
      else inn V p n k u c (m - 1) (e + 1) (acc d (by8 V p (k + 1 + e))) := by
  rw [inn, if_neg h, if_neg (nt hb), if_neg ho, if_neg hs, if_neg hl]
  by_cases hm : m = 0
  · rw [dif_pos hm, if_pos hm]
  · rw [dif_neg hm, if_neg hm]

end cnt

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

/-! ## The stack -/

/-- The memory after the six `push`es and `mov [rsp-8], rsi`. -/
def Vs0 (g : Gprs) (V : Addr → Byte) : Addr → Byte :=
  Vst (Vst (Vst (Vst (Vst (Vst (Vst V (g.rsp - 8) (toBytesLE g.r15 8)) (g.rsp - 8 - 8) (toBytesLE g.r14 8))
    (g.rsp - 8 - 8 - 8) (toBytesLE g.r13 8)) (g.rsp - 8 - 8 - 8 - 8) (toBytesLE g.r12 8))
    (g.rsp - 8 - 8 - 8 - 8 - 8) (toBytesLE g.rbp 8)) (S6 g.rsp) (toBytesLE g.rbx 8))
    (S6 g.rsp + 18446744073709551608#64) (toBytesLE g.rsi 8)

/-- And `mov [rsp-0xc], r8d` with `flags & 4`. -/
def Vs1 (g : Gprs) (V : Addr → Byte) : Addr → Byte :=
  Vst (Vs0 g V) (S6 g.rsp + 18446744073709551604#64) (toBytesLE (BitVec.setWidth 32 g.r8 &&& 4#32) 4)

/-- Past one store in a load, the bounds by `tsl`; a failing bound stops a `repeat`. -/
macro "skv" : tactic => `(tactic| focus (rw [rd_Vst _ _ _ _ _ ?_ ?_ ?_]; rotate_left; iterate 3 tsl))
/-- Past one store at a byte. -/
macro "sko" : tactic => `(tactic| focus (rw [Vst_out _ _ _ _ ?_ ?_]; rotate_left; iterate 2 tsl))

section stk
variable {g : Gprs} {V : Addr → Byte} (hs : 64 ≤ g.rsp.toNat)
include hs

/-- The memory in the forms `s - c`. -/
theorem vs0_eq : Vs0 g V =
    Vst (Vst (Vst (Vst (Vst (Vst (Vst V (g.rsp - BitVec.ofNat 64 8) (toBytesLE g.r15 8))
      (g.rsp - BitVec.ofNat 64 16) (toBytesLE g.r14 8)) (g.rsp - BitVec.ofNat 64 24) (toBytesLE g.r13 8))
      (g.rsp - BitVec.ofNat 64 32) (toBytesLE g.r12 8)) (g.rsp - BitVec.ofNat 64 40) (toBytesLE g.rbp 8))
      (g.rsp - BitVec.ofNat 64 48) (toBytesLE g.rbx 8)) (g.rsp - BitVec.ofNat 64 56) (toBytesLE g.rsi 8) := by
  rw [Vs0, k56, k48, k40, k32, k24, k16, k8]

/-- The bytes outside the 60 below the stack pointer. -/
theorem vs0_out {x : Addr} (hx : x.toNat + 60 < g.rsp.toNat ∨ g.rsp.toNat ≤ x.toNat) : Vs0 g V x = V x := by
  have hl := g.rsp.isLt
  simp only [Nat.reducePow] at hl
  rw [vs0_eq hs]
  repeat sko

theorem vs1_out {x : Addr} (hx : x.toNat + 60 < g.rsp.toNat ∨ g.rsp.toNat ≤ x.toNat) : Vs1 g V x = V x := by
  have hl := g.rsp.isLt
  simp only [Nat.reducePow] at hl
  rw [Vs1, k60]
  sko
  exact vs0_out hs hx

/-- What the six `push`es and the `destLen` store left. -/
theorem vs0_rd : rdq(Vs0 g V, g.rsp - BitVec.ofNat 64 8) = g.r15 ∧ rdq(Vs0 g V, g.rsp - BitVec.ofNat 64 16) = g.r14 ∧
    rdq(Vs0 g V, g.rsp - BitVec.ofNat 64 24) = g.r13 ∧ rdq(Vs0 g V, g.rsp - BitVec.ofNat 64 32) = g.r12 ∧
    rdq(Vs0 g V, g.rsp - BitVec.ofNat 64 40) = g.rbp ∧ rdq(Vs0 g V, g.rsp - BitVec.ofNat 64 48) = g.rbx ∧
    rdq(Vs0 g V, g.rsp - BitVec.ofNat 64 56) = g.rsi := by
  have hl := g.rsp.isLt
  simp only [Nat.reducePow] at hl
  rw [vs0_eq hs]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  · repeat skv
    rw [rd_Vst_self _ _ _ (toBytesLE_length _ _) (by tsl)]
    exact ofBytesLE_toBytesLE (w := 64) (n := 8) rfl _

/-- The `flags & 4` store is apart from the 56 bytes. -/
theorem vs1_rd {c : Nat} (hc : c = 8 ∨ c = 16 ∨ c = 24 ∨ c = 32 ∨ c = 40 ∨ c = 48 ∨ c = 56) :
    rdq(Vs1 g V, g.rsp - BitVec.ofNat 64 c) = rdq(Vs0 g V, g.rsp - BitVec.ofNat 64 c) := by
  have hl := g.rsp.isLt
  simp only [Nat.reducePow] at hl
  rw [Vs1, k60]
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> skv

/-- `flags & 4`, read back. -/
theorem vs1_fl : rdd(Vs1 g V, S6 g.rsp + 18446744073709551604#64) = BitVec.setWidth 32 g.r8 &&& 4#32 := by
  have hl := g.rsp.isLt
  simp only [Nat.reducePow] at hl
  rw [Vs1, k60, rd_Vst_self _ _ _ (toBytesLE_length _ _) (by tsl)]
  exact ofBytesLE_toBytesLE (w := 32) (n := 4) rfl _

end stk

end FV7z.U16
