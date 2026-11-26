import FV7z.U2s.Cuts
import FV7z.Tun.Inv
import FV7z.Lemmas.FnSteps
/-!
# `ConvertUInt32ToString` writes the digits and a 0 into the 11 bytes it is given (PLAN.md §M, M1)

7-Zip 26.06's `ConvertUInt32ToString (UInt32 val, char *s)` at `0x44ab70` in `7zzs` (`CPP/Common/IntToString.cpp`):
a frame of 40 bytes with the stack guard (`fs:0x28`) at `rsp - 16`; `val` (`edi`) below 10 as one digit at `s`, else
the digits from the last into the frame (`rsp - 39` on, `x / 10` by `0xcccccccd` and `shr 35`), the first at `s`, the
others copied out in reverse after it; then the 0 at `s + len` (`len` the count of digits, 1 to 10), `rax` = `s + len`.
Four pieces of the code (`U2s/Cuts.lean`): from the entry (0), the 0 and the stack guard's check (39), the first loop
(88), the second (155).

- `Hy`: what the function needs of the run: the frame and the 11 bytes at `rsi` in what it may store into, apart
  from each other, from the return address and from the stack guard's 8 bytes (`fs:0x28`).
- `Out`, `Out2`: an address apart from the bytes the code stores (the digits in the frame, the 11 at `rsi`), apart
  from the frame and the 11 bytes.
- `vc_*`: the verification conditions of the pieces; `at88`, `at155`, `at39`: one step from each cut point;
  `loop1`, `loop2`: the loops by induction.
- `u2s_ok`: from the entry to the return address: `rax` = `rsi + len` with `1 ≤ len ≤ 10`, the byte at `rsi + len`
  0, the bytes apart from the frame and `[rsi, rsi + 11)` as at the entry, the registers a call keeps as at the entry.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.U2s

/-- The `ret`. -/
def pret : List Byte := [0xc3]
theorem pret_0 : ∀ feat, Dec feat pret 0 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem w_66 : pret <+: u2s.drop 66 := by decide +kernel
theorem ret_66 (feat : Features) : Dec feat u2s 66 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 66) (k := 0) (pret_0 feat) w_66 (Nat.zero_le _)

/-! ## Arithmetic -/

/-- `x / 10` as `x · 0xcccccccd >> 35`, for `x` of 32 bits. -/
theorem mdiv (x : Nat) (hx : x < 2 ^ 32) : x * 3435973837 / 2 ^ 35 = x / 10 := by
  have hx' : x < 4294967296 := hx
  rw [show (2 : Nat) ^ 35 = 34359738368 from rfl]
  obtain ⟨r, s, hs, rfl⟩ : ∃ r s, s < 10 ∧ x = 10 * r + s :=
    ⟨x / 10, x % 10, Nat.mod_lt _ (by decide), (Nat.div_add_mod x 10).symm⟩
  have hr : (10 * r + s) / 10 = r := by omega
  rw [hr]
  apply Nat.div_eq_of_lt_le <;> omega

/-- `imul rax, r11; shr rax, 35` with `r11` = `0xcccccccd` on a zero-extended 32-bit value: the value / 10. -/
theorem bdiv (x : BitVec 32) : ((x.setWidth 64 * 3435973837#64) >>> 35).toNat = x.toNat / 10 := by
  have hx := x.isLt
  have hc : (3435973837#64).toNat = 3435973837 := by first | rfl | decide
  have e1 : (x.setWidth 64 * 3435973837#64).toNat = x.toNat * 3435973837 := by
    rw [BitVec.toNat_mul, BitVec.toNat_setWidth, hc]
    have : x.toNat % 2 ^ 64 = x.toNat := Nat.mod_eq_of_lt (by omega)
    rw [this]
    exact Nat.mod_eq_of_lt (by omega)
  rw [BitVec.toNat_ushiftRight, e1, Nat.shiftRight_eq_div_pow]
  exact mdiv _ hx

/-- `imul64_eq` with the width written `128` (as `simp` leaves `2 * 64`). -/
theorem imul64_eq128 (x y : BitVec 64) : (x.signExtend 128 * y.signExtend 128).setWidth 64 = x * y :=
  imul64_eq x y

theorem dstep (N k : Nat) : N / 10 ^ (k + 1) = N / 10 ^ k / 10 := by
  rw [Nat.div_div_eq_div_mul]
  first | rfl | rw [Nat.pow_succ] | simp [Nat.pow_succ]

/-- A 32-bit value at least 10 after `k` divisions by 10: `k ≤ 8`. -/
theorem kb {N k : Nat} (hN : N < 2 ^ 32) (h : 10 ≤ N / 10 ^ k) : k ≤ 8 := by
  apply Nat.le_of_not_lt
  intro hk
  have h1 : 10 ^ 9 ≤ 10 ^ k := Nat.pow_le_pow_right (by decide) hk
  have h2 : N / 10 ^ k ≤ N / 10 ^ 9 := Nat.div_le_div_left h1 (by decide)
  have hN' : N < 4294967296 := hN
  have h3 : N / 10 ^ 9 ≤ 4 := by
    rw [show (10 : Nat) ^ 9 = 1000000000 from rfl]
    omega
  omega

/-- `cmp r32, n; ja` not taken. -/
theorem cmp_le {x : BitVec 32} {n : Nat} (hn : n < 2 ^ 32) (h : x.toNat ≤ n) :
    (decide (x.toNat < n) || decide (x = BitVec.ofNat 32 n)) = true := by
  rcases Nat.lt_or_eq_of_le h with h | h
  · simp [h]
  · have e : x = BitVec.ofNat 32 n :=
      BitVec.eq_of_toNat_eq (by rw [h, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn])
    simp [e]

/-- `cmp r32, n; ja` taken. -/
theorem cmp_gt {x : BitVec 32} {n : Nat} (hn : n < 2 ^ 32) (h : n < x.toNat) :
    (decide (x.toNat < n) || decide (x = BitVec.ofNat 32 n)) = false := by
  have h1 : ¬ x.toNat < n := by omega
  have h2 : x ≠ BitVec.ofNat 32 n := fun e => by
    rw [e, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn] at h
    omega
  simp [h1, h2]

/-- The number, `edi`. -/
abbrev nv (g : Gprs) : Nat := (BitVec.setWidth 32 g.rdi).toNat

theorem nv_lt (g : Gprs) : nv g < 2 ^ 32 := (BitVec.setWidth 32 g.rdi).isLt

/-! ## Addresses -/

theorem t40 {s : Addr} (h : 40 ≤ s.toNat) : (s - 40#64).toNat = s.toNat - 40 := by
  have := s.isLt
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega

theorem t24 {s : Addr} (h : 40 ≤ s.toNat) : (s - 40#64 + 24#64).toNat = s.toNat - 16 := by
  have := s.isLt
  simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega

theorem tadd {a : Addr} {m : Nat} (h : a.toNat + m < 2 ^ 64) : (a + BitVec.ofNat 64 m).toNat = a.toNat + m := by
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

/-- An address `d` bytes into `n` at `a`. -/
theorem fa {a x : Addr} {d n : Nat} (hd : d < n) (hf : a.toNat + n ≤ 2 ^ 64) (hx : x.toNat = a.toNat + d) :
    x = a.add d :=
  BitVec.eq_of_toNat_eq (by rw [hx, toNat_add_of_fits hd hf])

theorem fr {P : Addr → Prop} {a x : Addr} {N d n : Nat} (h : ∀ i < N, P (Addr.add a i))
    (hx : x = a.add d) (hdn : d + n ≤ N) : ∀ i < n, P (Addr.add x i) := fun i hi => by
  rw [hx, addr_add_add']
  exact h (d + i) (by omega)

local macro "bv_eq" : tactic =>
  `(tactic| (apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]; omega))

/-! ## Bytes -/

theorem rd_congr {V V' : Addr → Byte} {a : Addr} {n : Nat} (h : ∀ i < n, V (a.add i) = V' (a.add i)) :
    (byteAddrs a n).map V = (byteAddrs a n).map V' :=
  List.map_congr_left fun x hx => by
    obtain ⟨i, hi, rfl⟩ := mem_byteAddrs.1 hx
    exact h i hi

/-- The 0 stored. -/
theorem st0 (V : Addr → Byte) (a : Addr) : Vst V a (toBytesLE (BitVec.ofNat 8 0) 1) a = 0#8 := by
  have e : toBytesLE (BitVec.ofNat 8 0) 1 = [0#8] := by first | rfl | decide | simp [toBytesLE]
  rw [e]
  first | exact if_pos rfl | simp [Vst, upd1]

/-- Apart from the bytes the code stores: the digits in the frame (`r + 1` to `r + 9`, `r` = `rsp - 40`) and the 11
bytes at `p`. -/
def Out (r p a : Addr) : Prop :=
  (a.toNat < r.toNat + 1 ∨ r.toNat + 10 ≤ a.toNat) ∧ (a.toNat < p.toNat ∨ p.toNat + 11 ≤ a.toNat)

/-- Apart from the frame (40 bytes below `s`) and the 11 bytes at `p`. -/
def Out2 (s p a : Addr) : Prop :=
  (a.toNat < s.toNat - 40 ∨ s.toNat ≤ a.toNat) ∧ (a.toNat < p.toNat ∨ p.toNat + 11 ≤ a.toNat)

/-- A byte stored among the digits or the 11 bytes. -/
theorem mi_st {V₁ V : Addr → Byte} {r p b : Addr} {bs : List Byte} (hl : bs.length = 1)
    (hm : ∀ a, Out r p a → V a = V₁ a)
    (hin : (r.toNat + 1 ≤ b.toNat ∧ b.toNat < r.toNat + 10) ∨ (p.toNat ≤ b.toNat ∧ b.toNat < p.toNat + 11)) :
    ∀ a, Out r p a → Vst V b bs a = V₁ a := fun a ha => by
  have hb := b.isLt
  have ha' := ha
  unfold Out at ha'
  rw [Tun.Vst_out V b bs a (by rw [hl]; omega) (by rw [hl]; omega)]
  exact hm a ha

/-- The registers a call keeps. -/
abbrev Kp (g h : Gprs) : Prop :=
  g.rbx = h.rbx ∧ g.rbp = h.rbp ∧ g.r12 = h.r12 ∧ g.r13 = h.r13 ∧ g.r14 = h.r14 ∧ g.r15 = h.r15

/-- The bytes after the stack guard is stored in the frame, from the bytes `V` at the entry with registers `g`. -/
def V1 (V : Addr → Byte) (g : Gprs) (fb : Addr) : Addr → Byte :=
  Vst V (g.rsp - 40#64 + 24#64) (toBytesLE rdq(V, fb + 40#64) 8)

/-- What the function needs of the run, from the registers `g₀` at the entry and the `fs` base `fb`. -/
structure Hy (F : Footprint) (Wl : List Rgn) (g₀ : Gprs) (fb : Addr) : Prop where
  h40 : 40 ≤ g₀.rsp.toNat
  hsp : g₀.rsp.toNat + 8 ≤ 2 ^ 64
  hfw : ∀ i < 40, Foot Wl (Addr.add (g₀.rsp - 40#64) i)
  hfd : ∀ i < 40, Foot F.data (Addr.add (g₀.rsp - 40#64) i)
  hpw : ∀ i < 11, Foot Wl (Addr.add g₀.rsi i)
  hpb : g₀.rsi.toNat + 11 ≤ 2 ^ 64
  hpf : g₀.rsi.toNat + 11 ≤ g₀.rsp.toNat - 40 ∨ g₀.rsp.toNat + 8 ≤ g₀.rsi.toNat
  hcl : ∀ i < 8, Foot F.data (Addr.add (fb + 40#64) i)
  hcb : (fb + 40#64).toNat + 8 ≤ 2 ^ 64
  hcd : (fb + 40#64).toNat + 8 ≤ g₀.rsp.toNat - 40 ∨ g₀.rsp.toNat ≤ (fb + 40#64).toNat
  hpc : g₀.rsi.toNat + 11 ≤ (fb + 40#64).toNat ∨ (fb + 40#64).toNat + 8 ≤ g₀.rsi.toNat

variable {F : Footprint} {Wl : List Rgn}

/-- The stack guard at the check, the bytes apart from the stores as after the guard was stored. -/
theorem can_ok {g₀ : Gprs} {fb : Addr} {V₀ V : Addr → Byte} (H : Hy F Wl g₀ fb)
    (hm : ∀ a, Out (g₀.rsp - 40#64) g₀.rsi a → V a = V1 V₀ g₀ fb a) :
    rdq(V, g₀.rsp - 40#64 + 24#64) = rdq(V, fb + 40#64) := by
  have hs := g₀.rsp.isLt
  have a40 := t40 H.h40
  have a24 := t24 H.h40
  have h40 := H.h40
  have hpf := H.hpf
  have hcb := H.hcb
  have hcd := H.hcd
  have hpc := H.hpc
  have o1 : ∀ i < 8, V (Addr.add (g₀.rsp - 40#64 + 24#64) i) =
      V1 V₀ g₀ fb (Addr.add (g₀.rsp - 40#64 + 24#64) i) := fun i hi => by
    have e := toNat_add_of_fits (a := g₀.rsp - 40#64 + 24#64) hi (by omega)
    exact hm _ (by unfold Out; omega)
  have o2 : ∀ i < 8, V (Addr.add (fb + 40#64) i) = V1 V₀ g₀ fb (Addr.add (fb + 40#64) i) := fun i hi => by
    have e := toNat_add_of_fits (a := fb + 40#64) hi hcb
    exact hm _ (by unfold Out; omega)
  rw [rd_congr o1, rd_congr o2]
  unfold V1
  rw [Tun.rd_Vst_self _ _ _ (toBytesLE_length _ _) ?c1, ofBytesLE_toBytesLE (n := 8) rfl,
    Tun.rd_Vst _ _ _ (fb + 40#64) 8 ?d1 hcb ?d3]
  all_goals (try simp only [toBytesLE_length])
  all_goals omega

/-- At the end: the bytes apart from the frame and the 11 bytes as at the entry. -/
theorem fin_mem {g₀ : Gprs} {fb : Addr} {V₀ V : Addr → Byte} (H : Hy F Wl g₀ fb)
    (hm : ∀ a, Out (g₀.rsp - 40#64) g₀.rsi a → V a = V1 V₀ g₀ fb a) :
    ∀ a, Out2 g₀.rsp g₀.rsi a → V a = V₀ a := fun a ha => by
  have hs := g₀.rsp.isLt
  have a40 := t40 H.h40
  have a24 := t24 H.h40
  have h40 := H.h40
  unfold Out2 at ha
  rw [hm a (by unfold Out; omega)]
  unfold V1
  exact Tun.Vst_out _ _ _ a (by rw [toBytesLE_length]; omega) (by rw [toBytesLE_length]; omega)

/-- The return address's bytes are apart from the frame and the 11 bytes. -/
theorem out2_ra {g₀ : Gprs} {fb : Addr} (H : Hy F Wl g₀ fb) {i : Nat} (hi : i < 8) :
    Out2 g₀.rsp g₀.rsi (Addr.add g₀.rsp i) := by
  have e := toNat_add_of_fits hi H.hsp
  have := H.hpf
  unfold Out2
  omega

/-! ## The verification conditions -/

/-- What is left of a piece's condition: footprint facts, equations, cases that cannot be, the registers and bytes
that are some values. -/
local macro "vcx" : tactic =>
  `(tactic| repeat' (first
    | rfl
    | exact trivial
    | assumption
    | (intro h; exact absurd h (by decide))
    | exact ⟨_, rfl⟩
    | exact ⟨_, _, rfl⟩
    | exact ⟨_, _, _, rfl⟩
    | exact ⟨_, rfl, toBytesLE_length _ _⟩
    | exact ⟨_, _, rfl, toBytesLE_length _ _, toBytesLE_length _ _⟩
    | exact ⟨_, _, _, rfl, (by first | rfl | decide), (by first | rfl | decide)⟩
    | refine ⟨_, _, _, _, rfl, ?_⟩
    | apply And.intro
    | intro _))

/-- From the entry, `edi` below 10: the digit at `rsi`, to the 0 (39). -/
theorem vc_0s {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (hb : (decide ((BitVec.setWidth 32 g.rdi).toNat < 9) || decide (BitVec.setWidth 32 g.rdi = 9#32)) = true)
    (hcl : ∀ i < 8, Foot F.data (Addr.add (fb + 40#64) i))
    (hfw : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 40#64 + 24#64) i)) (hw : ∀ i < 1, Foot Wl (Addr.add g.rsi i)) :
    W_0 fb F Wl (fun j' g' _ V' => j' = 39 ∧
      (∃ a d, g' = { g with rax := a, rsp := g.rsp - 40#64, r10 := g.rsi + 1#64, rdi := d }) ∧
      (∃ bs, V' = Vst (V1 V g fb) g.rsi bs ∧ bs.length = 1)) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hb hfw hw ⊢
  wpx [W_0, W_72, W_33, o0, o1, o4, Op.ldf, hb, Bool.true_eq_false, Bool.false_eq_true, false_implies,
    implies_true, Bool.not_true, Bool.not_false]
  all_goals vcx

/-- From the entry, `edi` at least 10: to the first loop (88), `ecx` 0, `r8` the frame, `r11` the multiplier. -/
theorem vc_0l {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (hb : (decide ((BitVec.setWidth 32 g.rdi).toNat < 9) || decide (BitVec.setWidth 32 g.rdi = 9#32)) = false)
    (hcl : ∀ i < 8, Foot F.data (Addr.add (fb + 40#64) i))
    (hfw : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 40#64 + 24#64) i)) :
    W_0 fb F Wl (fun j' g' _ V' => j' = 88 ∧
      (∃ a c d, g' = { g with
          rax := a, rcx := c, rsp := g.rsp - 40#64, r8 := g.rsp - 40#64, r10 := g.rsi + 1#64, r11 := d } ∧
        c = 0#64 ∧ d = 3435973837#64) ∧
      V' = V1 V g fb) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hb hfw ⊢
  wpx [W_0, W_72, W_33, o0, o1, o4, Op.ldf, hb, BitVec.xor_self, Bool.true_eq_false, Bool.false_eq_true,
    false_implies, implies_true, Bool.not_true, Bool.not_false]
  all_goals vcx

/-- The first loop, the number above 99: a digit in the frame, back to 88, `rcx` one on, `edi` / 10. -/
theorem vc_88c {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} (hr : g.r11 = 3435973837#64)
    (hb : (decide ((BitVec.setWidth 32 g.rdi).toNat < 99) || decide (BitVec.setWidth 32 g.rdi = 99#32)) = false)
    (hw : ∀ i < 1, Foot Wl (Addr.add (g.r8 + (g.rcx + 1#64)) i)) :
    W_88 fb F Wl (fun j' g' _ V' => j' = 88 ∧
      (∃ a d r di, g' = { g with rax := a, rdx := d, r9 := r, rcx := g.rcx + 1#64, rdi := di } ∧
        (BitVec.setWidth 32 di).toNat = (BitVec.setWidth 32 g.rdi).toNat / 10) ∧
      (∃ bs, V' = Vst V (g.r8 + (g.rcx + 1#64)) bs ∧ bs.length = 1)) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hr hb hw ⊢
  subst hr
  wpx [W_88, W_134, o5, o6, Op.imul64, Op.shr64, imul64_eq, hb, Bool.true_eq_false, Bool.false_eq_true,
    false_implies, implies_true, Bool.not_true, Bool.not_false]
  all_goals vcx
  all_goals (try simp only [imul64_eq128, imul64_eq])
  all_goals (simp only [BitVec.toNat_setWidth, bdiv]; omega)

/-- The first loop, the number at most 99: its last digit in the frame, the first at `rsi`, to the second loop
(155) with `rax` after the digits in the frame and `rsi` after the first. -/
theorem vc_88e {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} (hr : g.r11 = 3435973837#64)
    (hb : (decide ((BitVec.setWidth 32 g.rdi).toNat < 99) || decide (BitVec.setWidth 32 g.rdi = 99#32)) = true)
    (hw : ∀ i < 1, Foot Wl (Addr.add (g.r8 + (g.rcx + 1#64)) i)) (hw' : ∀ i < 1, Foot Wl (Addr.add g.rsi i)) :
    W_88 fb F Wl (fun j' g' _ V' => j' = 155 ∧
      (∃ d r di, g' = { g with
          rax := g.r8 + (g.rcx + 1#64), rdx := d, r9 := r, rcx := g.rcx + 1#64, rdi := di, rsi := g.r10 }) ∧
      (∃ bs bs', V' = Vst (Vst V (g.r8 + (g.rcx + 1#64)) bs) g.rsi bs' ∧ bs.length = 1 ∧ bs'.length = 1)) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hr hb hw hw' ⊢
  subst hr
  wpx [W_88, W_134, o5, o6, Op.imul64, Op.shr64, imul64_eq, hb, Bool.true_eq_false, Bool.false_eq_true,
    false_implies, implies_true, Bool.not_true, Bool.not_false]
  all_goals vcx

/-- The second loop, more digits: one copied out, the next loaded, back to 155. -/
theorem vc_155c {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} (hz : decide (g.rax - 1#64 = g.r8) = false)
    (hw : ∀ i < 1, Foot Wl (Addr.add g.rsi i)) (hd : ∀ i < 1, Foot F.data (Addr.add (g.rax - 1#64) i)) :
    W_155 fb F Wl (fun j' g' _ V' => j' = 155 ∧
      (∃ d, g' = { g with rax := g.rax - 1#64, rdx := d, rsi := g.rsi + 1#64 }) ∧
      (∃ bs, V' = Vst V g.rsi bs ∧ bs.length = 1)) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hz hw hd ⊢
  wpx [W_155, W_152, W_170, o7, o8, o9, hz, Bool.true_eq_false, Bool.false_eq_true, false_implies, implies_true,
    Bool.not_true, Bool.not_false]
  all_goals vcx

/-- The second loop, the last digit: copied out, `r10` after the digits, to the 0 (39). -/
theorem vc_155e {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} (hz : decide (g.rax - 1#64 = g.r8) = true)
    (hw : ∀ i < 1, Foot Wl (Addr.add g.rsi i)) :
    W_155 fb F Wl (fun j' g' _ V' => j' = 39 ∧
      g' = { g with rax := g.rax - 1#64, rsi := g.rsi + 1#64, r10 := g.r10 + g.rcx } ∧
      (∃ bs, V' = Vst V g.rsi bs ∧ bs.length = 1)) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hz hw ⊢
  wpx [W_155, W_152, W_170, o7, o8, o9, hz, Bool.true_eq_false, Bool.false_eq_true, false_implies, implies_true,
    Bool.not_true, Bool.not_false]
  all_goals vcx

/-- The 0 at `r10`, the stack guard checked (as stored), the frame dropped: to the `ret` (66), `rax` = `r10`. -/
theorem vc_39 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} (hw : ∀ i < 1, Foot Wl (Addr.add g.r10 i))
    (hl24 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 24#64) i))
    (hcl : ∀ i < 8, Foot F.data (Addr.add (fb + 40#64) i))
    (hc : rdq(Vst V g.r10 (toBytesLE (BitVec.ofNat 8 0) 1), g.rsp + 24#64) =
      rdq(Vst V g.r10 (toBytesLE (BitVec.ofNat 8 0) 1), fb + 40#64)) :
    W_39 fb F Wl (fun j' g' _ V' => j' = 66 ∧ g' = { g with rax := g.r10, rsp := g.rsp + 40#64 } ∧
      V' = Vst V g.r10 (toBytesLE (BitVec.ofNat 8 0) 1)) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hw hl24 hc ⊢
  wpx [W_39, W_59, o2, o3, Op.xormf, hc, BitVec.xor_self]
  all_goals vcx
  all_goals (exfalso; simp_all)

/-! ## The pieces as steps of the run -/

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}

/-- The registers at 39 with `len` bytes written at `rsi`. -/
abbrev R39 (g₀ : Gprs) (len : Nat) (g : Gprs) : Prop :=
  g.rsp = g₀.rsp - 40#64 ∧ g.r10 = g₀.rsi + BitVec.ofNat 64 len ∧ Kp g g₀

/-- The registers at 88 with `kk` digits in the frame. -/
abbrev R88 (g₀ : Gprs) (kk : Nat) (g : Gprs) : Prop :=
  g.rsp = g₀.rsp - 40#64 ∧ g.r8 = g₀.rsp - 40#64 ∧ g.rcx = BitVec.ofNat 64 kk ∧
    (BitVec.setWidth 32 g.rdi).toNat = nv g₀ / 10 ^ kk ∧ g.r11 = 3435973837#64 ∧ g.rsi = g₀.rsi ∧
    g.r10 = g₀.rsi + 1#64 ∧ Kp g g₀

/-- The registers at 155 with `cc` digits in the frame, `i` of them copied out. -/
abbrev R155 (g₀ : Gprs) (cc i : Nat) (g : Gprs) : Prop :=
  g.rsp = g₀.rsp - 40#64 ∧ g.r8 = g₀.rsp - 40#64 ∧ g.rcx = BitVec.ofNat 64 cc ∧
    g.rax = g₀.rsp - 40#64 + BitVec.ofNat 64 (cc - i) ∧ g.rsi = g₀.rsi + BitVec.ofNat 64 (i + 1) ∧
    g.r10 = g₀.rsi + 1#64 ∧ Kp g g₀

/-- From 39 to the return address. -/
theorem at39 {fb : Addr} (c : Seg prof F Wl L s₀ o) (hfs : s₀.cpu.seg.fsBase = fb) (hin : CodeIn L u2s_at u2s)
    {g₀ : Gprs} {V₀ : Addr → Byte} (H : Hy F Wl g₀ fb) (hl : ∀ i < 8, Foot F.data (Addr.add g₀.rsp i))
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (hra : rdq(V₀, g₀.rsp) = e₂.add j₂)
    (k : ∀ (Z : State) (t' : Nat) (len : Nat) (V' : Addr → Byte), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V' →
      Z.cpu.rip = e₂.add j₂ → Z.cpu.gpr.rsp = g₀.rsp + 8 → Kp Z.cpu.gpr g₀ → 1 ≤ len → len ≤ 10 →
      Z.cpu.gpr.rax = g₀.rsi + BitVec.ofNat 64 len → V' (g₀.rsi + BitVec.ofNat 64 len) = 0#8 →
      (∀ a, Out2 g₀.rsp g₀.rsi a → V' a = V₀ a) → GoG prof L o gev gP gE Z t')
    {len : Nat} (h1 : 1 ≤ len) (h10 : len ≤ 10) {X : State} {t : Nat} {V : Addr → Byte}
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = u2s_at.add 39)
    (hR : R39 g₀ len X.cpu.gpr) (hm : ∀ a, Out (g₀.rsp - 40#64) g₀.rsi a → V a = V1 V₀ g₀ fb a) :
    GoG prof L o gev gP gE X t := by
  obtain ⟨hsp, hr10, hkp⟩ := hR
  have hs := g₀.rsp.isLt
  have a40 := t40 H.h40
  have a24 := t24 H.h40
  have h40 := H.h40
  have hpb := H.hpb
  have hpf := H.hpf
  have hr10n : X.cpu.gpr.r10.toNat = g₀.rsi.toNat + len := by
    rw [hr10]
    exact tadd (by omega)
  have hm' : ∀ a, Out (g₀.rsp - 40#64) g₀.rsi a →
      Vst V X.cpu.gpr.r10 (toBytesLE (BitVec.ofNat 8 0) 1) a = V1 V₀ g₀ fb a :=
    mi_st (toBytesLE_length _ _) hm (Or.inr ⟨by omega, by omega⟩)
  have hw : ∀ i < 1, Foot Wl (Addr.add X.cpu.gpr.r10 i) :=
    fr H.hpw (fa (n := 11) (d := len) (by omega) hpb hr10n) (by omega)
  have e24 : (g₀.rsp - 40#64 + 24#64).toNat = (g₀.rsp - 40#64).toNat + 24 := by omega
  have hl24 : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rsp + 24#64) i) := by
    rw [hsp]
    exact fr H.hfd (fa (n := 40) (d := 24) (by decide) (by omega) e24) (by decide)
  have hc : rdq(Vst V X.cpu.gpr.r10 (toBytesLE (BitVec.ofNat 8 0) 1), X.cpu.gpr.rsp + 24#64) =
      rdq(Vst V X.cpu.gpr.r10 (toBytesLE (BitVec.ofNat 8 0) 1), fb + 40#64) := by
    rw [hsp]
    exact can_ok H hm'
  refine (c_39 prof fb).run c hfs hin _ hK hA hrip (vc_39 hw hl24 H.hcl hc) ?_
  rintro j' g fl V₁ ⟨rfl, rfl, rfl⟩ Y t₁ hKY hAY hrY hgY -
  have hYsp : Y.cpu.gpr.rsp = g₀.rsp := by
    rw [hgY]
    show X.cpu.gpr.rsp + 40#64 = _
    rw [hsp]
    exact BitVec.sub_add_cancel _ _
  have hfin := fin_mem H hm'
  refine c.s_ret hKY hAY hin (lt_len (by decide)) hrY (ret_66 _) (by rw [hYsp]; exact hl) hin₂ h₂ ?_ ?_
  · rw [hYsp, rd_congr (V := Vst V X.cpu.gpr.r10 (toBytesLE (BitVec.ofNat 8 0) 1)) (V' := V₀) (a := g₀.rsp)
      (n := 8) fun i hi => hfin _ (out2_ra H hi)]
    exact hra
  rintro Z t₂ hKZ hAZ ⟨hrZ, hgZ⟩
  refine k Z t₂ len _ hKZ hAZ hrZ ?_ ?_ h1 h10 ?_ ?_ hfin
  · rw [hgZ]
    show Y.cpu.gpr.rsp + 8 = _
    rw [hYsp]
  · rw [hgZ, hgY]
    exact hkp
  · rw [hgZ, hgY]
    exact hr10
  · rw [← hr10]
    exact st0 _ _

/-- One step of the first loop. -/
theorem at88 {fb : Addr} (c : Seg prof F Wl L s₀ o) (hfs : s₀.cpu.seg.fsBase = fb) (hin : CodeIn L u2s_at u2s)
    {g₀ : Gprs} {V₁ : Addr → Byte} (H : Hy F Wl g₀ fb)
    (k1 : ∀ (cc : Nat) (Z : State) (t' : Nat) (V' : Addr → Byte), 1 ≤ cc → cc ≤ 9 → KeptW Wl s₀ Z →
      Agree F Z.proc.mm.mem V' → Z.cpu.rip = u2s_at.add 155 → R155 g₀ cc 0 Z.cpu.gpr →
      (∀ a, Out (g₀.rsp - 40#64) g₀.rsi a → V' a = V₁ a) → GoG prof L o gev gP gE Z t')
    {kk : Nat} (hq : 10 ≤ nv g₀ / 10 ^ kk)
    (ih : 10 ≤ nv g₀ / 10 ^ (kk + 1) → ∀ (Z : State) (t' : Nat) (V' : Addr → Byte), KeptW Wl s₀ Z →
      Agree F Z.proc.mm.mem V' → Z.cpu.rip = u2s_at.add 88 → R88 g₀ (kk + 1) Z.cpu.gpr →
      (∀ a, Out (g₀.rsp - 40#64) g₀.rsi a → V' a = V₁ a) → GoG prof L o gev gP gE Z t')
    {X : State} {t : Nat} {V : Addr → Byte} (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V)
    (hrip : X.cpu.rip = u2s_at.add 88) (hR : R88 g₀ kk X.cpu.gpr)
    (hm : ∀ a, Out (g₀.rsp - 40#64) g₀.rsi a → V a = V₁ a) : GoG prof L o gev gP gE X t := by
  obtain ⟨hsp, hr8, hcx, hdi, hr11, hsi, hr10, hkp⟩ := hR
  have hN := nv_lt g₀
  have hk8 : kk ≤ 8 := kb hN hq
  have hs := g₀.rsp.isLt
  have a40 := t40 H.h40
  have h40 := H.h40
  have hpb := H.hpb
  have hst : (X.cpu.gpr.r8 + (X.cpu.gpr.rcx + 1#64)).toNat = (g₀.rsp - 40#64).toNat + (kk + 1) := by
    rw [hr8, hcx]
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  have hfw1 : ∀ i < 1, Foot Wl (Addr.add (X.cpu.gpr.r8 + (X.cpu.gpr.rcx + 1#64)) i) :=
    fr H.hfw (fa (n := 40) (d := kk + 1) (by omega) (by omega) hst) (by omega)
  have ercx : X.cpu.gpr.rcx + 1#64 = BitVec.ofNat 64 (kk + 1) := by
    rw [hcx]
    bv_eq
  by_cases hc : nv g₀ / 10 ^ kk ≤ 99
  · have hb := cmp_le (x := BitVec.setWidth 32 X.cpu.gpr.rdi) (n := 99) (by decide) (by omega)
    have hsin : X.cpu.gpr.rsi.toNat = g₀.rsi.toNat := by rw [hsi]
    have hsi1 : ∀ i < 1, Foot Wl (Addr.add X.cpu.gpr.rsi i) := by
      rw [hsi]
      exact fun i hi => H.hpw i (by omega)
    refine (c_88 prof fb).run c hfs hin _ hK hA hrip (vc_88e hr11 hb hfw1 hsi1) ?_
    rintro j' g fl V' ⟨rfl, ⟨d, r, di, rfl⟩, bs, bs', rfl, hl1, hl2⟩ Y t₁ hKY hAY hrY hgY -
    have erax : X.cpu.gpr.r8 + (X.cpu.gpr.rcx + 1#64) = g₀.rsp - 40#64 + BitVec.ofNat 64 (kk + 1 - 0) := by
      rw [hr8, hcx]
      bv_eq
    have ersi : X.cpu.gpr.r10 = g₀.rsi + BitVec.ofNat 64 (0 + 1) := by
      rw [hr10]
    refine k1 (kk + 1) Y t₁ _ (by omega) (by omega) hKY hAY hrY ?_
      (mi_st hl2 (mi_st hl1 hm (Or.inl ⟨by omega, by omega⟩)) (Or.inr ⟨by omega, by omega⟩))
    rw [hgY]
    exact ⟨hsp, hr8, ercx, erax, ersi, hr10, hkp⟩
  · have hgt : 99 < nv g₀ / 10 ^ kk := by omega
    have hb := cmp_gt (x := BitVec.setWidth 32 X.cpu.gpr.rdi) (n := 99) (by decide) (by omega)
    have hq' : 10 ≤ nv g₀ / 10 ^ (kk + 1) := by
      rw [dstep]
      omega
    refine (c_88 prof fb).run c hfs hin _ hK hA hrip (vc_88c hr11 hb hfw1) ?_
    rintro j' g fl V' ⟨rfl, ⟨a, d, r, di, rfl, hdi'⟩, bs, rfl, hl1⟩ Y t₁ hKY hAY hrY hgY -
    have edi : (BitVec.setWidth 32 di).toNat = nv g₀ / 10 ^ (kk + 1) := by
      rw [hdi', hdi, dstep]
    refine ih hq' Y t₁ _ hKY hAY hrY ?_ (mi_st hl1 hm (Or.inl ⟨by omega, by omega⟩))
    rw [hgY]
    exact ⟨hsp, hr8, ercx, edi, hr11, hsi, hr10, hkp⟩

/-- The first loop, from 88 with `kk` digits in the frame, `kk + m = 9`. -/
theorem loop1 {fb : Addr} (c : Seg prof F Wl L s₀ o) (hfs : s₀.cpu.seg.fsBase = fb) (hin : CodeIn L u2s_at u2s)
    {g₀ : Gprs} {V₁ : Addr → Byte} (H : Hy F Wl g₀ fb)
    (k1 : ∀ (cc : Nat) (Z : State) (t' : Nat) (V' : Addr → Byte), 1 ≤ cc → cc ≤ 9 → KeptW Wl s₀ Z →
      Agree F Z.proc.mm.mem V' → Z.cpu.rip = u2s_at.add 155 → R155 g₀ cc 0 Z.cpu.gpr →
      (∀ a, Out (g₀.rsp - 40#64) g₀.rsi a → V' a = V₁ a) → GoG prof L o gev gP gE Z t') :
    ∀ (m kk : Nat), kk + m = 9 → 10 ≤ nv g₀ / 10 ^ kk → ∀ (X : State) (t : Nat) (V : Addr → Byte),
      KeptW Wl s₀ X → Agree F X.proc.mm.mem V → X.cpu.rip = u2s_at.add 88 → R88 g₀ kk X.cpu.gpr →
      (∀ a, Out (g₀.rsp - 40#64) g₀.rsi a → V a = V₁ a) → GoG prof L o gev gP gE X t := by
  intro m
  induction m with
  | zero =>
    intro kk hkm hq
    exact absurd (kb (nv_lt g₀) hq) (by omega)
  | succ m ih =>
    intro kk hkm hq X t V hK hA hrip hR hm
    exact at88 c hfs hin H k1 hq
      (fun hq' Z t' V' hKZ hAZ hrZ hRZ hmZ => ih (kk + 1) (by omega) hq' Z t' V' hKZ hAZ hrZ hRZ hmZ)
      hK hA hrip hR hm

/-- One step of the second loop. -/
theorem at155 {fb : Addr} (c : Seg prof F Wl L s₀ o) (hfs : s₀.cpu.seg.fsBase = fb) (hin : CodeIn L u2s_at u2s)
    {g₀ : Gprs} {V₁ : Addr → Byte} (H : Hy F Wl g₀ fb) {cc : Nat} (hc9 : cc ≤ 9)
    (k2 : ∀ (Z : State) (t' : Nat) (V' : Addr → Byte), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V' →
      Z.cpu.rip = u2s_at.add 39 → R39 g₀ (cc + 1) Z.cpu.gpr →
      (∀ a, Out (g₀.rsp - 40#64) g₀.rsi a → V' a = V₁ a) → GoG prof L o gev gP gE Z t')
    {i : Nat} (hi : i < cc)
    (ih : i + 1 < cc → ∀ (Z : State) (t' : Nat) (V' : Addr → Byte), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V' →
      Z.cpu.rip = u2s_at.add 155 → R155 g₀ cc (i + 1) Z.cpu.gpr →
      (∀ a, Out (g₀.rsp - 40#64) g₀.rsi a → V' a = V₁ a) → GoG prof L o gev gP gE Z t')
    {X : State} {t : Nat} {V : Addr → Byte} (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V)
    (hrip : X.cpu.rip = u2s_at.add 155) (hR : R155 g₀ cc i X.cpu.gpr)
    (hm : ∀ a, Out (g₀.rsp - 40#64) g₀.rsi a → V a = V₁ a) : GoG prof L o gev gP gE X t := by
  obtain ⟨hsp, hr8, hcx, hax, hsi, hr10, hkp⟩ := hR
  have hs := g₀.rsp.isLt
  have a40 := t40 H.h40
  have h40 := H.h40
  have hpb := H.hpb
  have hsin : X.cpu.gpr.rsi.toNat = g₀.rsi.toNat + (i + 1) := by
    rw [hsi]
    exact tadd (by omega)
  have hw : ∀ j < 1, Foot Wl (Addr.add X.cpu.gpr.rsi j) :=
    fr H.hpw (fa (n := 11) (d := i + 1) (by omega) hpb hsin) (by omega)
  have hax1 : X.cpu.gpr.rax - 1#64 = g₀.rsp - 40#64 + BitVec.ofNat 64 (cc - (i + 1)) := by
    rw [hax]
    bv_eq
  by_cases hlast : i + 1 = cc
  · have heq : X.cpu.gpr.rax - 1#64 = X.cpu.gpr.r8 := by
      rw [hax1, hr8]
      bv_eq
    refine (c_155 prof fb).run c hfs hin _ hK hA hrip (vc_155e (decide_eq_true heq) hw) ?_
    rintro j' g fl V' ⟨rfl, rfl, bs, rfl, hl1⟩ Y t₁ hKY hAY hrY hgY -
    have e10 : X.cpu.gpr.r10 + X.cpu.gpr.rcx = g₀.rsi + BitVec.ofNat 64 (cc + 1) := by
      rw [hr10, hcx]
      bv_eq
    refine k2 Y t₁ _ hKY hAY hrY ?_ (mi_st hl1 hm (Or.inr ⟨by omega, by omega⟩))
    rw [hgY]
    exact ⟨hsp, e10, hkp⟩
  · have em : (g₀.rsp - 40#64 + BitVec.ofNat 64 (cc - (i + 1))).toNat = (g₀.rsp - 40#64).toNat + (cc - (i + 1)) :=
      tadd (by omega)
    have hne : X.cpu.gpr.rax - 1#64 ≠ X.cpu.gpr.r8 := by
      rw [hax1, hr8]
      intro h
      have := congrArg BitVec.toNat h
      omega
    have hd : ∀ j < 1, Foot F.data (Addr.add (X.cpu.gpr.rax - 1#64) j) := by
      rw [hax1]
      exact fr H.hfd (fa (n := 40) (d := cc - (i + 1)) (by omega) (by omega) em) (by omega)
    refine (c_155 prof fb).run c hfs hin _ hK hA hrip (vc_155c (decide_eq_false hne) hw hd) ?_
    rintro j' g fl V' ⟨rfl, ⟨d, rfl⟩, bs, rfl, hl1⟩ Y t₁ hKY hAY hrY hgY -
    have esi : X.cpu.gpr.rsi + 1#64 = g₀.rsi + BitVec.ofNat 64 (i + 1 + 1) := by
      rw [hsi]
      bv_eq
    refine ih (by omega) Y t₁ _ hKY hAY hrY ?_ (mi_st hl1 hm (Or.inr ⟨by omega, by omega⟩))
    rw [hgY]
    exact ⟨hsp, hr8, hcx, hax1, esi, hr10, hkp⟩

/-- The second loop, from 155 with `cc` digits in the frame, `i` copied out, `i + m + 1 = cc`. -/
theorem loop2 {fb : Addr} (c : Seg prof F Wl L s₀ o) (hfs : s₀.cpu.seg.fsBase = fb) (hin : CodeIn L u2s_at u2s)
    {g₀ : Gprs} {V₁ : Addr → Byte} (H : Hy F Wl g₀ fb) {cc : Nat} (hc9 : cc ≤ 9)
    (k2 : ∀ (Z : State) (t' : Nat) (V' : Addr → Byte), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V' →
      Z.cpu.rip = u2s_at.add 39 → R39 g₀ (cc + 1) Z.cpu.gpr →
      (∀ a, Out (g₀.rsp - 40#64) g₀.rsi a → V' a = V₁ a) → GoG prof L o gev gP gE Z t') :
    ∀ (m i : Nat), i + m + 1 = cc → ∀ (X : State) (t : Nat) (V : Addr → Byte), KeptW Wl s₀ X →
      Agree F X.proc.mm.mem V → X.cpu.rip = u2s_at.add 155 → R155 g₀ cc i X.cpu.gpr →
      (∀ a, Out (g₀.rsp - 40#64) g₀.rsi a → V a = V₁ a) → GoG prof L o gev gP gE X t := by
  intro m
  induction m with
  | zero =>
    intro i him X t V hK hA hrip hR hm
    exact at155 c hfs hin H hc9 k2 (by omega) (fun h => absurd h (by omega)) hK hA hrip hR hm
  | succ m ih =>
    intro i him X t V hK hA hrip hR hm
    exact at155 c hfs hin H hc9 k2 (by omega)
      (fun _ Z t' V' hKZ hAZ hrZ hRZ hmZ => ih (i + 1) (by omega) Z t' V' hKZ hAZ hrZ hRZ hmZ) hK hA hrip hR hm

/-! ## The function -/

variable {X : State} {t : Nat} {V : Addr → Byte}

/-- `ConvertUInt32ToString (val, s)` from its entry to the return address, with what `Hy` says of the frame (40
bytes below the stack pointer), the 11 bytes at `s` (`rsi`) and the stack guard: the run goes on with the return
address popped, the registers a call keeps as at the entry, `rax` = `s + len` with `1 ≤ len ≤ 10`, the byte at
`s + len` 0, the bytes apart from the frame and the 11 at `s` as at the entry. -/
theorem u2s_ok {fb : Addr} (c : Seg prof F Wl L s₀ o) (hfs : s₀.cpu.seg.fsBase = fb) (hin : CodeIn L u2s_at u2s)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = u2s_at) (H : Hy F Wl X.cpu.gpr fb)
    (hl : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsp i))
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (hra : rdq(V, X.cpu.gpr.rsp) = e₂.add j₂)
    (k : ∀ (Z : State) (t' : Nat) (len : Nat) (V' : Addr → Byte), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V' →
      Z.cpu.rip = e₂.add j₂ → Z.cpu.gpr.rsp = X.cpu.gpr.rsp + 8 → Kp Z.cpu.gpr X.cpu.gpr → 1 ≤ len → len ≤ 10 →
      Z.cpu.gpr.rax = X.cpu.gpr.rsi + BitVec.ofNat 64 len → V' (X.cpu.gpr.rsi + BitVec.ofNat 64 len) = 0#8 →
      (∀ a, Out2 X.cpu.gpr.rsp X.cpu.gpr.rsi a → V' a = V a) → GoG prof L o gev gP gE Z t') :
    GoG prof L o gev gP gE X t := by
  have hs := X.cpu.gpr.rsp.isLt
  have a40 := t40 H.h40
  have a24 := t24 H.h40
  have h40 := H.h40
  have hpb := H.hpb
  have e24 : (X.cpu.gpr.rsp - 40#64 + 24#64).toNat = (X.cpu.gpr.rsp - 40#64).toNat + 24 := by omega
  have hfw24 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 40#64 + 24#64) i) :=
    fr H.hfw (fa (n := 40) (d := 24) (by decide) (by omega) e24) (by decide)
  have hm1 : ∀ a, Out (X.cpu.gpr.rsp - 40#64) X.cpu.gpr.rsi a → V1 V X.cpu.gpr fb a = V1 V X.cpu.gpr fb a :=
    fun _ _ => rfl
  by_cases hsm : nv X.cpu.gpr ≤ 9
  · refine (c_0 prof fb).run c hfs hin _ hK hA (by rw [addr_add_zero]; exact hrip)
      (vc_0s (cmp_le (n := 9) (by decide) hsm) H.hcl hfw24 (fun i hi => H.hpw i (by omega))) ?_
    rintro j' g fl V₁ ⟨rfl, ⟨a, d, rfl⟩, bs, rfl, hbs⟩ Y t₁ hKY hAY hrY hgY -
    refine at39 c hfs hin H hl hin₂ h₂ hra k (len := 1) (by decide) (by decide) hKY hAY hrY ?_
      (mi_st hbs hm1 (Or.inr ⟨by omega, by omega⟩))
    rw [hgY]
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · refine (c_0 prof fb).run c hfs hin _ hK hA (by rw [addr_add_zero]; exact hrip)
      (vc_0l (cmp_gt (n := 9) (by decide) (Nat.lt_of_not_le hsm)) H.hcl hfw24) ?_
    rintro j' g fl V₁ ⟨rfl, ⟨a, c', d, rfl, hc', hd⟩, rfl⟩ Y t₁ hKY hAY hrY hgY -
    have h0 : 10 ≤ nv X.cpu.gpr / 10 ^ 0 := by
      rw [Nat.pow_zero, Nat.div_one]
      omega
    have edi : (BitVec.setWidth 32 X.cpu.gpr.rdi).toNat = nv X.cpu.gpr / 10 ^ 0 := by
      rw [Nat.pow_zero, Nat.div_one]
    refine loop1 c hfs hin H (V₁ := V1 V X.cpu.gpr fb) ?_ 9 0 (by decide) h0 Y t₁ _ hKY hAY hrY ?_ hm1
    · intro cc Z t₂ V₂ hc1 hc9 hKZ hAZ hrZ hRZ hmZ
      refine loop2 c hfs hin H hc9 ?_ (cc - 1) 0 (by omega) Z t₂ V₂ hKZ hAZ hrZ hRZ hmZ
      intro Z₂ t₃ V₃ hKZ₂ hAZ₂ hrZ₂ hR₂ hm₂
      exact at39 c hfs hin H hl hin₂ h₂ hra k (len := cc + 1) (by omega) (by omega) hKZ₂ hAZ₂ hrZ₂ hR₂ hm₂
    · rw [hgY]
      exact ⟨rfl, rfl, hc', edi, hd, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end FV7z.U2s
