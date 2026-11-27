import FV7z.C64.Cuts
import FV7z.U2s.Holds
import FV7z.Lemmas.FnFar
/-!
# `ConvertUInt64ToString` writes the digits and a 0 into the 21 bytes it is given (PLAN.md §M, M1)

7-Zip 26.06's `ConvertUInt64ToString (UInt64 val, char *s)` at `0x44ac30` in `7zzs` (`CPP/Common/IntToString.cpp`):
a frame of 40 bytes with the stack guard (`fs:0x28`) at `rsp - 16`; `val` (`rdi`) at most `0xffffffff` by a tail jump
to `ConvertUInt32ToString` (`U2s.u2s_ok`) after the stack guard's check, else the digits from the last into the frame
(`rsp - 39` on, `x / 10` by `mul` with `0xcccccccccccccccd` and `shr 3`) while the number is above 99, the first at
`s`, the others copied out in reverse after it; then the 0 at `s + len` (`len` the count of digits, 2 to 20), `rax` =
`s + len`. Five pieces of the code (`C64/Cuts.lean`): from the entry (0), the first loop (56), the second (131), the
0 and the stack guard's check (146), the check before the tail jump (176).

- `Hy`: what the function needs of the run: the frame and the 21 bytes at `rsi` in what it may store into, apart
  from each other, from the return address and from the stack guard's 8 bytes.
- `Out`, `Out2`: an address apart from the bytes the code stores (the digits in the frame, the 21 at `rsi`), apart
  from the frame and the 21 bytes.
- `vc_*`: the verification conditions of the pieces; `at56`, `at131`, `at146`: one step from each cut point;
  `loop1`, `loop2`: the loops by induction.
- `c64_ok`: from the entry to the return address: `rax` = `rsi + len` with `1 ≤ len ≤ 20`, the byte at `rsi + len`
  0, the bytes apart from the frame and `[rsi, rsi + 21)` as at the entry, the registers a call keeps as at the entry.

Status (2026-11-26): written but not built yet (no triage run). Design notes and next steps:
- Generated files from `tools/blk_gen.py` key `c64` (cuts 146 and 176 added so that the stack guard's checks get
  plain bytes `V`, as `U2s.vc_39` does). `FV7z.lean` does not import this module yet: add
  `import FV7z.C64.Holds` after the `U2s` line once it builds.
- Next step: triage `FV7z.C64.Holds` with the decls `FV7z.C64.c64_ok FV7z.C64.ddiv`; the likely spots to fix are the
  `wpx` shapes in `vc_0t`/`vc_0l` (`sw_ff` for `mov eax, 0xffffffff`, the `jbe` condition as in `hb`) and the
  quotient goal of `vc_56c` (`ddiv`'s left side may need another form of the 128-bit product).
- The contract is `U2s.u2s_ok`'s, widened to 21 bytes and `len ≤ 20`; the digits' values are not tracked.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.C64

/-- The `ret`. -/
def pret : List Byte := [0xc3]
theorem pret_0 : ∀ feat, Dec feat pret 0 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem w_172 : pret <+: c64.drop 172 := by decide +kernel
theorem ret_172 (feat : Features) : Dec feat c64 172 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 172) (k := 0) (pret_0 feat) w_172 (Nat.zero_le _)

/-- The tail jump to `ConvertUInt32ToString`. -/
def pjm : List Byte := [0xe9, 0x77, 0xfe, 0xff, 0xff]
theorem pjm_0 : ∀ feat, Dec feat pjm 0 (FV7z.mk .jmp 64 [.rel 18446744073709551223] 5) := by dec_rfl
theorem wj_196 : pjm <+: c64.drop 196 := by decide +kernel
theorem jmp_196 (feat : Features) : Dec feat c64 196 (FV7z.mk .jmp 64 [.rel 18446744073709551223] 5) :=
  Dec.shift (j := 196) (k := 0) (pjm_0 feat) wj_196 (Nat.zero_le _)

/-! ## The division by 10 -/

/-- The multiplier `0xcccccccccccccccd` and `2 ^ 67`: `x / 10` for a 64-bit `x`. -/
theorem mdiv64 (x : Nat) (hx : x < 2 ^ 64) : x * 14757395258967641293 / 2 ^ 67 = x / 10 := by
  have hx' : x < 18446744073709551616 := hx
  rw [show (2 : Nat) ^ 67 = 147573952589676412928 from rfl]
  obtain ⟨r, s, hs, rfl⟩ : ∃ r s, s < 10 ∧ x = 10 * r + s :=
    ⟨x / 10, x % 10, Nat.mod_lt _ (by decide), (Nat.div_add_mod x 10).symm⟩
  have hr : (10 * r + s) / 10 = r := by omega
  rw [hr]
  apply Nat.div_eq_of_lt_le <;> omega

/-- `mul r10; shr rdx, 3` with `r10` = `0xcccccccccccccccd`: the value / 10. -/
theorem ddiv (x : BitVec 64) :
    (((BitVec.setWidth 128 x * BitVec.setWidth 128 14757395258967641293#64).extractLsb' 64 64) >>> 3).toNat =
      x.toNat / 10 := by
  have hx := x.isLt
  have e1 : (BitVec.setWidth 128 x * BitVec.setWidth 128 14757395258967641293#64).toNat =
      x.toNat * 14757395258967641293 := by
    rw [BitVec.toNat_mul, BitVec.toNat_setWidth, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    simp only [Nat.reducePow, Nat.reduceMod]
    omega
  rw [BitVec.toNat_ushiftRight, BitVec.extractLsb'_toNat, e1, Nat.shiftRight_eq_div_pow,
    Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt (show x.toNat * 14757395258967641293 / 2 ^ 64 < 2 ^ 64 by omega),
    Nat.div_div_eq_div_mul, show (2 : Nat) ^ 64 * 2 ^ 3 = 2 ^ 67 from rfl]
  exact mdiv64 _ hx

/-- A 64-bit value at least 10 after `k` divisions by 10: `k ≤ 18`. -/
theorem kb64 {N k : Nat} (hN : N < 2 ^ 64) (h : 10 ≤ N / 10 ^ k) : k ≤ 18 := by
  apply Nat.le_of_not_lt
  intro hk
  have h1 : 10 ^ 19 ≤ 10 ^ k := Nat.pow_le_pow_right (by decide) hk
  have h2 : N / 10 ^ k ≤ N / 10 ^ 19 := Nat.div_le_div_left h1 (by decide)
  have hN' : N < 18446744073709551616 := hN
  have h3 : N / 10 ^ 19 ≤ 1 := by
    rw [show (10 : Nat) ^ 19 = 10000000000000000000 from rfl]
    omega
  omega

/-- `cmp r64, n; ja` not taken. -/
theorem cmp_le64 {x : BitVec 64} {n : Nat} (hn : n < 2 ^ 64) (h : x.toNat ≤ n) :
    (decide (x.toNat < n) || decide (x = BitVec.ofNat 64 n)) = true := by
  rcases Nat.lt_or_eq_of_le h with h | h
  · simp [h]
  · have e : x = BitVec.ofNat 64 n :=
      BitVec.eq_of_toNat_eq (by rw [h, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn])
    simp [e]

/-- `cmp r64, n; ja` taken. -/
theorem cmp_gt64 {x : BitVec 64} {n : Nat} (hn : n < 2 ^ 64) (h : n < x.toNat) :
    (decide (x.toNat < n) || decide (x = BitVec.ofNat 64 n)) = false := by
  have h1 : ¬ x.toNat < n := by omega
  have h2 : x ≠ BitVec.ofNat 64 n := fun e => by
    rw [e, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn] at h
    omega
  simp [h1, h2]

/-- `mov eax, 0xffffffff` as the 64-bit register. -/
theorem sw_ff : BitVec.setWidth 64 (4294967295#32) = 4294967295#64 := by decide

local macro "bv_eq" : tactic =>
  `(tactic| (apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]; omega))

/-! ## Bytes -/

/-- Apart from the bytes the code stores: the digits in the frame (`r + 1` to `r + 19`, `r` = `rsp - 40`) and the 21
bytes at `p`. -/
def Out (r p a : Addr) : Prop :=
  (a.toNat < r.toNat + 1 ∨ r.toNat + 20 ≤ a.toNat) ∧ (a.toNat < p.toNat ∨ p.toNat + 21 ≤ a.toNat)

/-- Apart from the frame (40 bytes below `s`) and the 21 bytes at `p`. -/
def Out2 (s p a : Addr) : Prop :=
  (a.toNat < s.toNat - 40 ∨ s.toNat ≤ a.toNat) ∧ (a.toNat < p.toNat ∨ p.toNat + 21 ≤ a.toNat)

/-- A byte stored among the digits or the 21 bytes. -/
theorem mi_st {V₁ V : Addr → Byte} {r p b : Addr} {bs : List Byte} (hl : bs.length = 1)
    (hm : ∀ a, Out r p a → V a = V₁ a)
    (hin : (r.toNat + 1 ≤ b.toNat ∧ b.toNat < r.toNat + 20) ∨ (p.toNat ≤ b.toNat ∧ b.toNat < p.toNat + 21)) :
    ∀ a, Out r p a → Vst V b bs a = V₁ a := fun a ha => by
  have hb := b.isLt
  have ha' := ha
  unfold Out at ha'
  rw [Tun.Vst_out V b bs a (by rw [hl]; omega) (by rw [hl]; omega)]
  exact hm a ha

/-- What the function needs of the run, from the registers `g₀` at the entry and the `fs` base `fb`. -/
structure Hy (F : Footprint) (Wl : List Rgn) (g₀ : Gprs) (fb : Addr) : Prop where
  h40 : 40 ≤ g₀.rsp.toNat
  hsp : g₀.rsp.toNat + 8 ≤ 2 ^ 64
  hfw : ∀ i < 40, Foot Wl (Addr.add (g₀.rsp - 40#64) i)
  hfd : ∀ i < 40, Foot F.data (Addr.add (g₀.rsp - 40#64) i)
  hpw : ∀ i < 21, Foot Wl (Addr.add g₀.rsi i)
  hpb : g₀.rsi.toNat + 21 ≤ 2 ^ 64
  hpf : g₀.rsi.toNat + 21 ≤ g₀.rsp.toNat - 40 ∨ g₀.rsp.toNat + 8 ≤ g₀.rsi.toNat
  hcl : ∀ i < 8, Foot F.data (Addr.add (fb + 40#64) i)
  hcb : (fb + 40#64).toNat + 8 ≤ 2 ^ 64
  hcd : (fb + 40#64).toNat + 8 ≤ g₀.rsp.toNat - 40 ∨ g₀.rsp.toNat ≤ (fb + 40#64).toNat
  hpc : g₀.rsi.toNat + 21 ≤ (fb + 40#64).toNat ∨ (fb + 40#64).toNat + 8 ≤ g₀.rsi.toNat

variable {F : Footprint} {Wl : List Rgn}

/-- The stack guard at the check, the bytes apart from the stores as after the guard was stored. -/
theorem can_ok {g₀ : Gprs} {fb : Addr} {V₀ V : Addr → Byte} (H : Hy F Wl g₀ fb)
    (hm : ∀ a, Out (g₀.rsp - 40#64) g₀.rsi a → V a = U2s.V1 V₀ g₀ fb a) :
    rdq(V, g₀.rsp - 40#64 + 24#64) = rdq(V, fb + 40#64) := by
  have hs := g₀.rsp.isLt
  have a40 := U2s.t40 H.h40
  have a24 := U2s.t24 H.h40
  have h40 := H.h40
  have hpf := H.hpf
  have hcb := H.hcb
  have hcd := H.hcd
  have hpc := H.hpc
  have o1 : ∀ i < 8, V (Addr.add (g₀.rsp - 40#64 + 24#64) i) =
      U2s.V1 V₀ g₀ fb (Addr.add (g₀.rsp - 40#64 + 24#64) i) := fun i hi => by
    have e := toNat_add_of_fits (a := g₀.rsp - 40#64 + 24#64) hi (by omega)
    exact hm _ (by unfold Out; omega)
  have o2 : ∀ i < 8, V (Addr.add (fb + 40#64) i) = U2s.V1 V₀ g₀ fb (Addr.add (fb + 40#64) i) := fun i hi => by
    have e := toNat_add_of_fits (a := fb + 40#64) hi hcb
    exact hm _ (by unfold Out; omega)
  rw [U2s.rd_congr o1, U2s.rd_congr o2]
  unfold U2s.V1
  rw [Tun.rd_Vst_self _ _ _ (toBytesLE_length _ _) ?c1, ofBytesLE_toBytesLE (n := 8) rfl,
    Tun.rd_Vst _ _ _ (fb + 40#64) 8 ?d1 hcb ?d3]
  all_goals (try simp only [toBytesLE_length])
  all_goals omega

/-- At the end: the bytes apart from the frame and the 21 bytes as at the entry. -/
theorem fin_mem {g₀ : Gprs} {fb : Addr} {V₀ V : Addr → Byte} (H : Hy F Wl g₀ fb)
    (hm : ∀ a, Out (g₀.rsp - 40#64) g₀.rsi a → V a = U2s.V1 V₀ g₀ fb a) :
    ∀ a, Out2 g₀.rsp g₀.rsi a → V a = V₀ a := fun a ha => by
  have hs := g₀.rsp.isLt
  have a40 := U2s.t40 H.h40
  have a24 := U2s.t24 H.h40
  have h40 := H.h40
  unfold Out2 at ha
  rw [hm a (by unfold Out; omega)]
  unfold U2s.V1
  exact Tun.Vst_out _ _ _ a (by rw [toBytesLE_length]; omega) (by rw [toBytesLE_length]; omega)

/-- The return address's bytes are apart from the frame and the 21 bytes. -/
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

/-- From the entry, `rdi` at most `0xffffffff`: to the check before the tail jump (176). -/
theorem vc_0t {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (hb : (decide (g.rdi.toNat < 4294967295) || decide (g.rdi = 4294967295#64)) = true)
    (hcl : ∀ i < 8, Foot F.data (Addr.add (fb + 40#64) i))
    (hfw : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 40#64 + 24#64) i)) :
    W_0 fb F Wl (fun j' g' _ V' => j' = 176 ∧
      (∃ a c d, g' = { g with
          rax := a, rsp := g.rsp - 40#64, r8 := c, r9 := g.rsp - 40#64, r10 := d } ∧
        c = 0#64 ∧ d = 14757395258967641293#64) ∧
      V' = U2s.V1 V g fb) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hb hfw ⊢
  wpx [W_0, W_50, o0, o1, Op.ldf, sw_ff, hb, BitVec.xor_self, Bool.true_eq_false, Bool.false_eq_true,
    false_implies, implies_true, Bool.not_true, Bool.not_false]
  all_goals vcx

/-- From the entry, `rdi` above `0xffffffff`: to the first loop (56), `r8` 0, `r9` the frame, `r10` the
multiplier. -/
theorem vc_0l {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (hb : (decide (g.rdi.toNat < 4294967295) || decide (g.rdi = 4294967295#64)) = false)
    (hcl : ∀ i < 8, Foot F.data (Addr.add (fb + 40#64) i))
    (hfw : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 40#64 + 24#64) i)) :
    W_0 fb F Wl (fun j' g' _ V' => j' = 56 ∧
      (∃ a c d, g' = { g with
          rax := a, rsp := g.rsp - 40#64, r8 := c, r9 := g.rsp - 40#64, r10 := d } ∧
        c = 0#64 ∧ d = 14757395258967641293#64) ∧
      V' = U2s.V1 V g fb) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hb hfw ⊢
  wpx [W_0, W_50, o0, o1, Op.ldf, sw_ff, hb, BitVec.xor_self, Bool.true_eq_false, Bool.false_eq_true,
    false_implies, implies_true, Bool.not_true, Bool.not_false]
  all_goals vcx

/-- The stack guard checked (as stored), the frame dropped: to the tail jump (196). -/
theorem vc_176 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (hl24 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 24#64) i))
    (hcl : ∀ i < 8, Foot F.data (Addr.add (fb + 40#64) i))
    (hc : rdq(V, g.rsp + 24#64) = rdq(V, fb + 40#64)) :
    W_176 fb F Wl (fun j' g' _ V' => j' = 196 ∧ (∃ a, g' = { g with rax := a, rsp := g.rsp + 40#64 }) ∧
      V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hl24 hc ⊢
  wpx [W_176, W_192, o8, o7, Op.xormf, hc, BitVec.xor_self]
  all_goals vcx
  all_goals (exfalso; simp_all)

/-- The first loop, the number above 99: a digit in the frame, back to 56, `r8` one on, `rdi` / 10. -/
theorem vc_56c {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} (hr : g.r10 = 14757395258967641293#64)
    (hb : (decide (g.rdi.toNat < 99) || decide (g.rdi = 99#64)) = false)
    (hw : ∀ i < 1, Foot Wl (Addr.add (g.r9 + (g.r8 + 1#64)) i)) :
    W_56 fb F Wl (fun j' g' _ V' => j' = 56 ∧
      (∃ a c d di, g' = { g with rax := a, rcx := c, rdx := d, r8 := g.r8 + 1#64, rdi := di } ∧
        di.toNat = g.rdi.toNat / 10) ∧
      (∃ bs, V' = Vst V (g.r9 + (g.r8 + 1#64)) bs ∧ bs.length = 1)) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hr hb hw ⊢
  subst hr
  wpx [W_56, W_102, o2, o3, Op.mul64, Op.mulp, Op.shr64, hb, Bool.true_eq_false, Bool.false_eq_true,
    false_implies, implies_true, Bool.not_true, Bool.not_false]
  all_goals vcx
  all_goals exact ddiv _

/-- The first loop, the number at most 99: its last digit in the frame, the first at `rsi`, to the second loop
(131) with `rdx` at the last digit in the frame, `rax` and `rsi` after the first at `rsi`. -/
theorem vc_56e {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} (hr : g.r10 = 14757395258967641293#64)
    (hb : (decide (g.rdi.toNat < 99) || decide (g.rdi = 99#64)) = true)
    (hw : ∀ i < 1, Foot Wl (Addr.add (g.r9 + (g.r8 + 1#64)) i)) (hw' : ∀ i < 1, Foot Wl (Addr.add g.rsi i)) :
    W_56 fb F Wl (fun j' g' _ V' => j' = 131 ∧
      (∃ c di, g' = { g with
          rax := g.rsi + 1#64, rcx := c, rdx := g.r9 + (g.r8 + 1#64), r8 := g.r8 + 1#64, rdi := di,
          rsi := g.rsi + 1#64 }) ∧
      (∃ bs bs', V' = Vst (Vst V (g.r9 + (g.r8 + 1#64)) bs) g.rsi bs' ∧ bs.length = 1 ∧ bs'.length = 1)) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hr hb hw hw' ⊢
  subst hr
  wpx [W_56, W_102, o2, o3, Op.mul64, Op.mulp, Op.shr64, hb, Bool.true_eq_false, Bool.false_eq_true,
    false_implies, implies_true, Bool.not_true, Bool.not_false]
  all_goals vcx

/-- The second loop, more digits: one copied out, the next loaded, back to 131. -/
theorem vc_131c {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} (hz : decide (g.rdx - 1#64 = g.r9) = false)
    (hw : ∀ i < 1, Foot Wl (Addr.add g.rsi i)) (hd : ∀ i < 1, Foot F.data (Addr.add (g.rdx - 1#64) i)) :
    W_131 fb F Wl (fun j' g' _ V' => j' = 131 ∧
      (∃ c, g' = { g with rcx := c, rdx := g.rdx - 1#64, rsi := g.rsi + 1#64 }) ∧
      (∃ bs, V' = Vst V g.rsi bs ∧ bs.length = 1)) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hz hw hd ⊢
  wpx [W_131, W_128, o5, o4, hz, Bool.true_eq_false, Bool.false_eq_true, false_implies, implies_true,
    Bool.not_true, Bool.not_false]
  all_goals vcx

/-- The second loop, the last digit: copied out, to the 0 (146). -/
theorem vc_131e {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} (hz : decide (g.rdx - 1#64 = g.r9) = true)
    (hw : ∀ i < 1, Foot Wl (Addr.add g.rsi i)) :
    W_131 fb F Wl (fun j' g' _ V' => j' = 146 ∧
      g' = { g with rdx := g.rdx - 1#64, rsi := g.rsi + 1#64 } ∧
      (∃ bs, V' = Vst V g.rsi bs ∧ bs.length = 1)) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hz hw ⊢
  wpx [W_131, W_128, o5, o4, hz, Bool.true_eq_false, Bool.false_eq_true, false_implies, implies_true,
    Bool.not_true, Bool.not_false]
  all_goals vcx

/-- The 0 at `rax + r8`, the stack guard checked (as stored), the frame dropped: to the `ret` (172), `rax` =
`rax + r8`. -/
theorem vc_146 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (hw : ∀ i < 1, Foot Wl (Addr.add (g.rax + g.r8) i))
    (hl24 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 24#64) i))
    (hcl : ∀ i < 8, Foot F.data (Addr.add (fb + 40#64) i))
    (hc : rdq(Vst V (g.rax + g.r8) (toBytesLE (BitVec.ofNat 8 0) 1), g.rsp + 24#64) =
      rdq(Vst V (g.rax + g.r8) (toBytesLE (BitVec.ofNat 8 0) 1), fb + 40#64)) :
    W_146 fb F Wl (fun j' g' _ V' => j' = 172 ∧
      (∃ s, g' = { g with rax := g.rax + g.r8, rsi := s, rsp := g.rsp + 40#64 }) ∧
      V' = Vst V (g.rax + g.r8) (toBytesLE (BitVec.ofNat 8 0) 1)) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hw hl24 hc ⊢
  wpx [W_146, W_168, o6, o7, Op.xormf, hc, BitVec.xor_self]
  all_goals vcx
  all_goals (exfalso; simp_all)

/-! ## The pieces as steps of the run -/

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}

/-- The registers at 56 with `kk` digits in the frame. -/
abbrev R56 (g₀ : Gprs) (kk : Nat) (g : Gprs) : Prop :=
  g.rsp = g₀.rsp - 40#64 ∧ g.r9 = g₀.rsp - 40#64 ∧ g.r8 = BitVec.ofNat 64 kk ∧
    g.rdi.toNat = g₀.rdi.toNat / 10 ^ kk ∧ g.r10 = 14757395258967641293#64 ∧ g.rsi = g₀.rsi ∧ U2s.Kp g g₀

/-- The registers at 131 with `cc` digits in the frame, `i` of them copied out. -/
abbrev R131 (g₀ : Gprs) (cc i : Nat) (g : Gprs) : Prop :=
  g.rsp = g₀.rsp - 40#64 ∧ g.r9 = g₀.rsp - 40#64 ∧ g.r8 = BitVec.ofNat 64 cc ∧
    g.rdx = g₀.rsp - 40#64 + BitVec.ofNat 64 (cc - i) ∧ g.rsi = g₀.rsi + BitVec.ofNat 64 (i + 1) ∧
    g.rax = g₀.rsi + 1#64 ∧ U2s.Kp g g₀

/-- The registers at 146 with `cc` digits copied out after the first. -/
abbrev R146 (g₀ : Gprs) (cc : Nat) (g : Gprs) : Prop :=
  g.rsp = g₀.rsp - 40#64 ∧ g.r8 = BitVec.ofNat 64 cc ∧ g.rax = g₀.rsi + 1#64 ∧ U2s.Kp g g₀

/-- From 146 to the return address. -/
theorem at146 {fb : Addr} (c : Seg prof F Wl L s₀ o) (hfs : s₀.cpu.seg.fsBase = fb) (hin : CodeIn L c64_at c64)
    {g₀ : Gprs} {V₀ : Addr → Byte} (H : Hy F Wl g₀ fb) (hl : ∀ i < 8, Foot F.data (Addr.add g₀.rsp i))
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (hra : rdq(V₀, g₀.rsp) = e₂.add j₂)
    (k : ∀ (Z : State) (t' : Nat) (len : Nat) (V' : Addr → Byte), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V' →
      Z.cpu.rip = e₂.add j₂ → Z.cpu.gpr.rsp = g₀.rsp + 8 → U2s.Kp Z.cpu.gpr g₀ → 1 ≤ len → len ≤ 20 →
      Z.cpu.gpr.rax = g₀.rsi + BitVec.ofNat 64 len → V' (g₀.rsi + BitVec.ofNat 64 len) = 0#8 →
      (∀ a, Out2 g₀.rsp g₀.rsi a → V' a = V₀ a) → GoG prof L o gev gP gE Z t')
    {cc : Nat} (h1 : 1 ≤ cc) (h19 : cc ≤ 19) {X : State} {t : Nat} {V : Addr → Byte}
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = c64_at.add 146)
    (hR : R146 g₀ cc X.cpu.gpr) (hm : ∀ a, Out (g₀.rsp - 40#64) g₀.rsi a → V a = U2s.V1 V₀ g₀ fb a) :
    GoG prof L o gev gP gE X t := by
  obtain ⟨hsp, hr8, hax, hkp⟩ := hR
  have hs := g₀.rsp.isLt
  have a40 := U2s.t40 H.h40
  have a24 := U2s.t24 H.h40
  have h40 := H.h40
  have hpb := H.hpb
  have hpf := H.hpf
  have ea : X.cpu.gpr.rax + X.cpu.gpr.r8 = g₀.rsi + BitVec.ofNat 64 (cc + 1) := by
    rw [hax, hr8]
    bv_eq
  have ean : (X.cpu.gpr.rax + X.cpu.gpr.r8).toNat = g₀.rsi.toNat + (cc + 1) := by
    rw [ea]
    exact U2s.tadd (by omega)
  have hm' : ∀ a, Out (g₀.rsp - 40#64) g₀.rsi a →
      Vst V (X.cpu.gpr.rax + X.cpu.gpr.r8) (toBytesLE (BitVec.ofNat 8 0) 1) a = U2s.V1 V₀ g₀ fb a :=
    mi_st (toBytesLE_length _ _) hm (Or.inr ⟨by omega, by omega⟩)
  have hw : ∀ i < 1, Foot Wl (Addr.add (X.cpu.gpr.rax + X.cpu.gpr.r8) i) :=
    U2s.fr H.hpw (U2s.fa (n := 21) (d := cc + 1) (by omega) hpb ean) (by omega)
  have e24 : (g₀.rsp - 40#64 + 24#64).toNat = (g₀.rsp - 40#64).toNat + 24 := by omega
  have hl24 : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rsp + 24#64) i) := by
    rw [hsp]
    exact U2s.fr H.hfd (U2s.fa (n := 40) (d := 24) (by decide) (by omega) e24) (by decide)
  have hc : rdq(Vst V (X.cpu.gpr.rax + X.cpu.gpr.r8) (toBytesLE (BitVec.ofNat 8 0) 1), X.cpu.gpr.rsp + 24#64) =
      rdq(Vst V (X.cpu.gpr.rax + X.cpu.gpr.r8) (toBytesLE (BitVec.ofNat 8 0) 1), fb + 40#64) := by
    rw [hsp]
    exact can_ok H hm'
  refine (c_146 prof fb).run c hfs hin _ hK hA hrip (vc_146 hw hl24 H.hcl hc) ?_
  rintro j' g fl V₁ ⟨rfl, ⟨s', rfl⟩, rfl⟩ Y t₁ hKY hAY hrY hgY -
  have hYsp : Y.cpu.gpr.rsp = g₀.rsp := by
    rw [hgY]
    show X.cpu.gpr.rsp + 40#64 = _
    rw [hsp]
    exact BitVec.sub_add_cancel _ _
  have hfin := fin_mem H hm'
  refine c.s_ret hKY hAY hin (lt_len (by decide)) hrY (ret_172 _) (by rw [hYsp]; exact hl) hin₂ h₂ ?_ ?_
  · rw [hYsp, U2s.rd_congr (V := Vst V (X.cpu.gpr.rax + X.cpu.gpr.r8) (toBytesLE (BitVec.ofNat 8 0) 1)) (V' := V₀)
      (a := g₀.rsp) (n := 8) fun i hi => hfin _ (out2_ra H hi)]
    exact hra
  rintro Z t₂ hKZ hAZ ⟨hrZ, hgZ⟩
  refine k Z t₂ (cc + 1) _ hKZ hAZ hrZ ?_ ?_ (by omega) (by omega) ?_ ?_ hfin
  · rw [hgZ]
    show Y.cpu.gpr.rsp + 8 = _
    rw [hYsp]
  · rw [hgZ, hgY]
    exact hkp
  · rw [hgZ, hgY]
    exact ea
  · rw [← ea]
    exact U2s.st0 _ _

/-- One step of the first loop. -/
theorem at56 {fb : Addr} (c : Seg prof F Wl L s₀ o) (hfs : s₀.cpu.seg.fsBase = fb) (hin : CodeIn L c64_at c64)
    {g₀ : Gprs} {V₁ : Addr → Byte} (H : Hy F Wl g₀ fb)
    (k1 : ∀ (cc : Nat) (Z : State) (t' : Nat) (V' : Addr → Byte), 1 ≤ cc → cc ≤ 19 → KeptW Wl s₀ Z →
      Agree F Z.proc.mm.mem V' → Z.cpu.rip = c64_at.add 131 → R131 g₀ cc 0 Z.cpu.gpr →
      (∀ a, Out (g₀.rsp - 40#64) g₀.rsi a → V' a = V₁ a) → GoG prof L o gev gP gE Z t')
    {kk : Nat} (hq : 10 ≤ g₀.rdi.toNat / 10 ^ kk)
    (ih : 10 ≤ g₀.rdi.toNat / 10 ^ (kk + 1) → ∀ (Z : State) (t' : Nat) (V' : Addr → Byte), KeptW Wl s₀ Z →
      Agree F Z.proc.mm.mem V' → Z.cpu.rip = c64_at.add 56 → R56 g₀ (kk + 1) Z.cpu.gpr →
      (∀ a, Out (g₀.rsp - 40#64) g₀.rsi a → V' a = V₁ a) → GoG prof L o gev gP gE Z t')
    {X : State} {t : Nat} {V : Addr → Byte} (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V)
    (hrip : X.cpu.rip = c64_at.add 56) (hR : R56 g₀ kk X.cpu.gpr)
    (hm : ∀ a, Out (g₀.rsp - 40#64) g₀.rsi a → V a = V₁ a) : GoG prof L o gev gP gE X t := by
  obtain ⟨hsp, hr9, hr8, hdi, hr10, hsi, hkp⟩ := hR
  have hN := g₀.rdi.isLt
  have hk : kk ≤ 18 := kb64 hN hq
  have hs := g₀.rsp.isLt
  have a40 := U2s.t40 H.h40
  have h40 := H.h40
  have hpb := H.hpb
  have hst : (X.cpu.gpr.r9 + (X.cpu.gpr.r8 + 1#64)).toNat = (g₀.rsp - 40#64).toNat + (kk + 1) := by
    rw [hr9, hr8]
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  have hfw1 : ∀ i < 1, Foot Wl (Addr.add (X.cpu.gpr.r9 + (X.cpu.gpr.r8 + 1#64)) i) :=
    U2s.fr H.hfw (U2s.fa (n := 40) (d := kk + 1) (by omega) (by omega) hst) (by omega)
  have er8 : X.cpu.gpr.r8 + 1#64 = BitVec.ofNat 64 (kk + 1) := by
    rw [hr8]
    bv_eq
  by_cases hc : g₀.rdi.toNat / 10 ^ kk ≤ 99
  · have hb := cmp_le64 (x := X.cpu.gpr.rdi) (n := 99) (by decide) (by omega)
    have hsin : X.cpu.gpr.rsi.toNat = g₀.rsi.toNat := by rw [hsi]
    have hsi1 : ∀ i < 1, Foot Wl (Addr.add X.cpu.gpr.rsi i) := by
      rw [hsi]
      exact fun i hi => H.hpw i (by omega)
    refine (c_56 prof fb).run c hfs hin _ hK hA hrip (vc_56e hr10 hb hfw1 hsi1) ?_
    rintro j' g fl V' ⟨rfl, ⟨c', di, rfl⟩, bs, bs', rfl, hl1, hl2⟩ Y t₁ hKY hAY hrY hgY -
    have erdx : X.cpu.gpr.r9 + (X.cpu.gpr.r8 + 1#64) = g₀.rsp - 40#64 + BitVec.ofNat 64 (kk + 1 - 0) := by
      rw [hr9, hr8]
      bv_eq
    have ersi : X.cpu.gpr.rsi + 1#64 = g₀.rsi + BitVec.ofNat 64 (0 + 1) := by
      rw [hsi]
    have erax : X.cpu.gpr.rsi + 1#64 = g₀.rsi + 1#64 := by rw [hsi]
    refine k1 (kk + 1) Y t₁ _ (by omega) (by omega) hKY hAY hrY ?_
      (mi_st hl2 (mi_st hl1 hm (Or.inl ⟨by omega, by omega⟩)) (Or.inr ⟨by omega, by omega⟩))
    rw [hgY]
    exact ⟨hsp, hr9, er8, erdx, ersi, erax, hkp⟩
  · have hgt : 99 < g₀.rdi.toNat / 10 ^ kk := by omega
    have hb := cmp_gt64 (x := X.cpu.gpr.rdi) (n := 99) (by decide) (by omega)
    have hq' : 10 ≤ g₀.rdi.toNat / 10 ^ (kk + 1) := by
      rw [U2s.dstep]
      omega
    refine (c_56 prof fb).run c hfs hin _ hK hA hrip (vc_56c hr10 hb hfw1) ?_
    rintro j' g fl V' ⟨rfl, ⟨a, c', d, di, rfl, hdi'⟩, bs, rfl, hl1⟩ Y t₁ hKY hAY hrY hgY -
    have edi : di.toNat = g₀.rdi.toNat / 10 ^ (kk + 1) := by
      rw [hdi', hdi, U2s.dstep]
    refine ih hq' Y t₁ _ hKY hAY hrY ?_ (mi_st hl1 hm (Or.inl ⟨by omega, by omega⟩))
    rw [hgY]
    exact ⟨hsp, hr9, er8, edi, hr10, hsi, hkp⟩

/-- The first loop, from 56 with `kk` digits in the frame, `kk + m = 19`. -/
theorem loop1 {fb : Addr} (c : Seg prof F Wl L s₀ o) (hfs : s₀.cpu.seg.fsBase = fb) (hin : CodeIn L c64_at c64)
    {g₀ : Gprs} {V₁ : Addr → Byte} (H : Hy F Wl g₀ fb)
    (k1 : ∀ (cc : Nat) (Z : State) (t' : Nat) (V' : Addr → Byte), 1 ≤ cc → cc ≤ 19 → KeptW Wl s₀ Z →
      Agree F Z.proc.mm.mem V' → Z.cpu.rip = c64_at.add 131 → R131 g₀ cc 0 Z.cpu.gpr →
      (∀ a, Out (g₀.rsp - 40#64) g₀.rsi a → V' a = V₁ a) → GoG prof L o gev gP gE Z t') :
    ∀ (m kk : Nat), kk + m = 19 → 10 ≤ g₀.rdi.toNat / 10 ^ kk → ∀ (X : State) (t : Nat) (V : Addr → Byte),
      KeptW Wl s₀ X → Agree F X.proc.mm.mem V → X.cpu.rip = c64_at.add 56 → R56 g₀ kk X.cpu.gpr →
      (∀ a, Out (g₀.rsp - 40#64) g₀.rsi a → V a = V₁ a) → GoG prof L o gev gP gE X t := by
  intro m
  induction m with
  | zero =>
    intro kk hkm hq
    exact absurd (kb64 g₀.rdi.isLt hq) (by omega)
  | succ m ih =>
    intro kk hkm hq X t V hK hA hrip hR hm
    exact at56 c hfs hin H k1 hq
      (fun hq' Z t' V' hKZ hAZ hrZ hRZ hmZ => ih (kk + 1) (by omega) hq' Z t' V' hKZ hAZ hrZ hRZ hmZ)
      hK hA hrip hR hm

/-- One step of the second loop. -/
theorem at131 {fb : Addr} (c : Seg prof F Wl L s₀ o) (hfs : s₀.cpu.seg.fsBase = fb) (hin : CodeIn L c64_at c64)
    {g₀ : Gprs} {V₁ : Addr → Byte} (H : Hy F Wl g₀ fb) {cc : Nat} (hc19 : cc ≤ 19)
    (k2 : ∀ (Z : State) (t' : Nat) (V' : Addr → Byte), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V' →
      Z.cpu.rip = c64_at.add 146 → R146 g₀ cc Z.cpu.gpr →
      (∀ a, Out (g₀.rsp - 40#64) g₀.rsi a → V' a = V₁ a) → GoG prof L o gev gP gE Z t')
    {i : Nat} (hi : i < cc)
    (ih : i + 1 < cc → ∀ (Z : State) (t' : Nat) (V' : Addr → Byte), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V' →
      Z.cpu.rip = c64_at.add 131 → R131 g₀ cc (i + 1) Z.cpu.gpr →
      (∀ a, Out (g₀.rsp - 40#64) g₀.rsi a → V' a = V₁ a) → GoG prof L o gev gP gE Z t')
    {X : State} {t : Nat} {V : Addr → Byte} (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V)
    (hrip : X.cpu.rip = c64_at.add 131) (hR : R131 g₀ cc i X.cpu.gpr)
    (hm : ∀ a, Out (g₀.rsp - 40#64) g₀.rsi a → V a = V₁ a) : GoG prof L o gev gP gE X t := by
  obtain ⟨hsp, hr9, hr8, hdx, hsi, hax, hkp⟩ := hR
  have hs := g₀.rsp.isLt
  have a40 := U2s.t40 H.h40
  have h40 := H.h40
  have hpb := H.hpb
  have hsin : X.cpu.gpr.rsi.toNat = g₀.rsi.toNat + (i + 1) := by
    rw [hsi]
    exact U2s.tadd (by omega)
  have hw : ∀ j < 1, Foot Wl (Addr.add X.cpu.gpr.rsi j) :=
    U2s.fr H.hpw (U2s.fa (n := 21) (d := i + 1) (by omega) hpb hsin) (by omega)
  have hdx1 : X.cpu.gpr.rdx - 1#64 = g₀.rsp - 40#64 + BitVec.ofNat 64 (cc - (i + 1)) := by
    rw [hdx]
    bv_eq
  by_cases hlast : i + 1 = cc
  · have heq : X.cpu.gpr.rdx - 1#64 = X.cpu.gpr.r9 := by
      rw [hdx1, hr9]
      bv_eq
    refine (c_131 prof fb).run c hfs hin _ hK hA hrip (vc_131e (decide_eq_true heq) hw) ?_
    rintro j' g fl V' ⟨rfl, rfl, bs, rfl, hl1⟩ Y t₁ hKY hAY hrY hgY -
    refine k2 Y t₁ _ hKY hAY hrY ?_ (mi_st hl1 hm (Or.inr ⟨by omega, by omega⟩))
    rw [hgY]
    exact ⟨hsp, hr8, hax, hkp⟩
  · have em : (g₀.rsp - 40#64 + BitVec.ofNat 64 (cc - (i + 1))).toNat = (g₀.rsp - 40#64).toNat + (cc - (i + 1)) :=
      U2s.tadd (by omega)
    have hne : X.cpu.gpr.rdx - 1#64 ≠ X.cpu.gpr.r9 := by
      rw [hdx1, hr9]
      intro h
      have := congrArg BitVec.toNat h
      omega
    have hd : ∀ j < 1, Foot F.data (Addr.add (X.cpu.gpr.rdx - 1#64) j) := by
      rw [hdx1]
      exact U2s.fr H.hfd (U2s.fa (n := 40) (d := cc - (i + 1)) (by omega) (by omega) em) (by omega)
    refine (c_131 prof fb).run c hfs hin _ hK hA hrip (vc_131c (decide_eq_false hne) hw hd) ?_
    rintro j' g fl V' ⟨rfl, ⟨c', rfl⟩, bs, rfl, hl1⟩ Y t₁ hKY hAY hrY hgY -
    have esi : X.cpu.gpr.rsi + 1#64 = g₀.rsi + BitVec.ofNat 64 (i + 1 + 1) := by
      rw [hsi]
      bv_eq
    refine ih (by omega) Y t₁ _ hKY hAY hrY ?_ (mi_st hl1 hm (Or.inr ⟨by omega, by omega⟩))
    rw [hgY]
    exact ⟨hsp, hr9, hr8, hdx1, esi, hax, hkp⟩

/-- The second loop, from 131 with `cc` digits in the frame, `i` copied out, `i + m + 1 = cc`. -/
theorem loop2 {fb : Addr} (c : Seg prof F Wl L s₀ o) (hfs : s₀.cpu.seg.fsBase = fb) (hin : CodeIn L c64_at c64)
    {g₀ : Gprs} {V₁ : Addr → Byte} (H : Hy F Wl g₀ fb) {cc : Nat} (hc19 : cc ≤ 19)
    (k2 : ∀ (Z : State) (t' : Nat) (V' : Addr → Byte), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V' →
      Z.cpu.rip = c64_at.add 146 → R146 g₀ cc Z.cpu.gpr →
      (∀ a, Out (g₀.rsp - 40#64) g₀.rsi a → V' a = V₁ a) → GoG prof L o gev gP gE Z t') :
    ∀ (m i : Nat), i + m + 1 = cc → ∀ (X : State) (t : Nat) (V : Addr → Byte), KeptW Wl s₀ X →
      Agree F X.proc.mm.mem V → X.cpu.rip = c64_at.add 131 → R131 g₀ cc i X.cpu.gpr →
      (∀ a, Out (g₀.rsp - 40#64) g₀.rsi a → V a = V₁ a) → GoG prof L o gev gP gE X t := by
  intro m
  induction m with
  | zero =>
    intro i him X t V hK hA hrip hR hm
    exact at131 c hfs hin H hc19 k2 (by omega) (fun h => absurd h (by omega)) hK hA hrip hR hm
  | succ m ih =>
    intro i him X t V hK hA hrip hR hm
    exact at131 c hfs hin H hc19 k2 (by omega)
      (fun _ Z t' V' hKZ hAZ hrZ hRZ hmZ => ih (i + 1) (by omega) Z t' V' hKZ hAZ hrZ hRZ hmZ) hK hA hrip hR hm

/-! ## The function -/

variable {X : State} {t : Nat} {V : Addr → Byte}

/-- `ConvertUInt64ToString (val, s)` from its entry to the return address, with what `Hy` says of the frame (40
bytes below the stack pointer), the 21 bytes at `s` (`rsi`) and the stack guard, and `ConvertUInt32ToString`'s code
where it lies (`hinU`, for the tail jump): the run goes on with the return address popped, the registers a call keeps
as at the entry, `rax` = `s + len` with `1 ≤ len ≤ 20`, the byte at `s + len` 0, the bytes apart from the frame and
the 21 at `s` as at the entry. -/
theorem c64_ok {fb : Addr} (c : Seg prof F Wl L s₀ o) (hfs : s₀.cpu.seg.fsBase = fb) (hin : CodeIn L c64_at c64)
    (hinU : CodeIn L U2s.u2s_at U2s.u2s)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = c64_at) (H : Hy F Wl X.cpu.gpr fb)
    (hl : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsp i))
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (hra : rdq(V, X.cpu.gpr.rsp) = e₂.add j₂)
    (k : ∀ (Z : State) (t' : Nat) (len : Nat) (V' : Addr → Byte), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V' →
      Z.cpu.rip = e₂.add j₂ → Z.cpu.gpr.rsp = X.cpu.gpr.rsp + 8 → U2s.Kp Z.cpu.gpr X.cpu.gpr → 1 ≤ len →
      len ≤ 20 → Z.cpu.gpr.rax = X.cpu.gpr.rsi + BitVec.ofNat 64 len →
      V' (X.cpu.gpr.rsi + BitVec.ofNat 64 len) = 0#8 →
      (∀ a, Out2 X.cpu.gpr.rsp X.cpu.gpr.rsi a → V' a = V a) → GoG prof L o gev gP gE Z t') :
    GoG prof L o gev gP gE X t := by
  have hs := X.cpu.gpr.rsp.isLt
  have a40 := U2s.t40 H.h40
  have a24 := U2s.t24 H.h40
  have h40 := H.h40
  have hpb := H.hpb
  have e24 : (X.cpu.gpr.rsp - 40#64 + 24#64).toNat = (X.cpu.gpr.rsp - 40#64).toNat + 24 := by omega
  have hfw24 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 40#64 + 24#64) i) :=
    U2s.fr H.hfw (U2s.fa (n := 40) (d := 24) (by decide) (by omega) e24) (by decide)
  have hm1 : ∀ a, Out (X.cpu.gpr.rsp - 40#64) X.cpu.gpr.rsi a →
      U2s.V1 V X.cpu.gpr fb a = U2s.V1 V X.cpu.gpr fb a := fun _ _ => rfl
  by_cases hsm : X.cpu.gpr.rdi.toNat ≤ 4294967295
  · -- the tail jump to `ConvertUInt32ToString`
    refine (c_0 prof fb).run c hfs hin _ hK hA (by rw [addr_add_zero]; exact hrip)
      (vc_0t (cmp_le64 (n := 4294967295) (by decide) hsm) H.hcl hfw24) ?_
    rintro j' g fl V₁ ⟨rfl, ⟨a, c', d, rfl, -, -⟩, rfl⟩ Y t₁ hKY hAY hrY hgY -
    have hYs : Y.cpu.gpr.rsp = X.cpu.gpr.rsp - 40#64 := by rw [hgY]
    have hl24 : ∀ i < 8, Foot F.data (Addr.add (Y.cpu.gpr.rsp + 24#64) i) := by
      rw [hYs]
      exact U2s.fr H.hfd (U2s.fa (n := 40) (d := 24) (by decide) (by omega) e24) (by decide)
    have hc : rdq(U2s.V1 V X.cpu.gpr fb, Y.cpu.gpr.rsp + 24#64) = rdq(U2s.V1 V X.cpu.gpr fb, fb + 40#64) := by
      rw [hYs]
      exact can_ok H hm1
    refine (c_176 prof fb).run c hfs hin _ hKY hAY hrY (vc_176 hl24 H.hcl hc) ?_
    rintro j' g fl V₂ ⟨rfl, ⟨a₂, rfl⟩, rfl⟩ Y₂ t₂ hK₂ hA₂ hr₂ hg₂ -
    have hs2 : Y₂.cpu.gpr.rsp = X.cpu.gpr.rsp := by
      rw [hg₂]
      show Y.cpu.gpr.rsp + 40#64 = _
      rw [hYs]
      exact BitVec.sub_add_cancel _ _
    have hsi2 : Y₂.cpu.gpr.rsi = X.cpu.gpr.rsi := by rw [hg₂, hgY]
    refine c.s_jmp_x hK₂ hA₂ hin (lt_len (by decide)) hr₂ (jmp_196 _) hinU (tgt := 0) (U2s.lt_len (by decide))
      (by decide) ?_
    rintro Y₃ t₃ hK₃ hA₃ ⟨hr₃, hg₃⟩
    have hs3 : Y₃.cpu.gpr.rsp = X.cpu.gpr.rsp := by rw [hg₃]; exact hs2
    have hsi3 : Y₃.cpu.gpr.rsi = X.cpu.gpr.rsi := by rw [hg₃]; exact hsi2
    have hV1 : ∀ a, Out2 X.cpu.gpr.rsp X.cpu.gpr.rsi a → U2s.V1 V X.cpu.gpr fb a = V a := fin_mem H hm1
    have hsp := H.hsp
    have hpf := H.hpf
    have hcd := H.hcd
    have hpc := H.hpc
    have hyU : U2s.Hy F Wl Y₃.cpu.gpr fb :=
      { h40 := by rw [hs3]; exact h40
        hsp := by rw [hs3]; exact hsp
        hfw := by rw [hs3]; exact H.hfw
        hfd := by rw [hs3]; exact H.hfd
        hpw := by rw [hsi3]; exact fun i hi => H.hpw i (by omega)
        hpb := by rw [hsi3]; omega
        hpf := by rw [hs3, hsi3]; omega
        hcl := H.hcl
        hcb := H.hcb
        hcd := by rw [hs3]; exact hcd
        hpc := by rw [hsi3]; omega }
    refine U2s.u2s_ok c hfs hinU hK₃ hA₃ (by rw [hr₃, addr_add_zero]) hyU (by rw [hs3]; exact hl) hin₂ h₂ ?_ ?_
    · rw [hs3, U2s.rd_congr (V := U2s.V1 V X.cpu.gpr fb) (V' := V) (a := X.cpu.gpr.rsp) (n := 8)
        fun i hi => hV1 _ (out2_ra H hi)]
      exact hra
    · intro Z t' len V' hKZ hAZ hrZ hzs hkp h1 h10 hax h0 hout
      rw [hs3] at hzs
      rw [hsi3] at hax h0
      rw [hs3, hsi3] at hout
      refine k Z t' len V' hKZ hAZ hrZ hzs ?_ h1 (by omega) hax h0 ?_
      · rw [hg₃, hg₂, hgY] at hkp
        exact hkp
      · intro x hx
        have hx' := hx
        unfold Out2 at hx'
        rw [hout x (by unfold U2s.Out2; omega)]
        exact hV1 x hx
  · -- the digits
    refine (c_0 prof fb).run c hfs hin _ hK hA (by rw [addr_add_zero]; exact hrip)
      (vc_0l (cmp_gt64 (n := 4294967295) (by decide) (by omega)) H.hcl hfw24) ?_
    rintro j' g fl V₁ ⟨rfl, ⟨a, c', d, rfl, hc', hd⟩, rfl⟩ Y t₁ hKY hAY hrY hgY -
    have h0 : 10 ≤ X.cpu.gpr.rdi.toNat / 10 ^ 0 := by
      rw [Nat.pow_zero, Nat.div_one]
      omega
    have edi : X.cpu.gpr.rdi.toNat = X.cpu.gpr.rdi.toNat / 10 ^ 0 := by
      rw [Nat.pow_zero, Nat.div_one]
    refine loop1 c hfs hin H (V₁ := U2s.V1 V X.cpu.gpr fb) ?_ 19 0 (by decide) h0 Y t₁ _ hKY hAY hrY ?_ hm1
    · intro cc Z t₂ V₂ hc1 hc19 hKZ hAZ hrZ hRZ hmZ
      refine loop2 c hfs hin H hc19 ?_ (cc - 1) 0 (by omega) Z t₂ V₂ hKZ hAZ hrZ hRZ hmZ
      intro Z₂ t₃ V₃ hKZ₂ hAZ₂ hrZ₂ hR₂ hm₂
      exact at146 c hfs hin H hl hin₂ h₂ hra k hc1 hc19 hKZ₂ hAZ₂ hrZ₂ hR₂ hm₂
    · rw [hgY]
      exact ⟨rfl, rfl, hc', edi, hd, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end FV7z.C64
