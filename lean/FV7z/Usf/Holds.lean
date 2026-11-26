import FV7z.Usf.Cuts
import FV7z.Ucn.Holds
import FV7z.Arb.Holds
/-!
# `UString::SetFrom (const wchar_t *s, unsigned len)` (PLAN.md §M, M1)

7-Zip 26.06's `UString::SetFrom (s, len)` at `0x44d790` in `7zzs` (`CPP/Common/MyString.cpp`), `this` in `rdi`,
`s` in `rsi`, `len` in `edx`: if `len > _limit` (the 4 bytes at `this + 12`; `jb` at 23), the throw stub above
`0x3ffffffe` (`ja` at 86 to `0x40140c`), else `newBuf = new wchar_t[len + 1]` (`call` at 103 to `operator new`,
`Onw.onw_at + 64`), `delete [] _chars` unless null (`call` at 120 to the thunk at `0x6014f0`), `_chars = newBuf`,
`_limit = len` (125); else `r12 = _chars` (25). Then (31) `wmemcpy (_chars, s, len)` (`call` at 44 to `Wmc.wmc_at`)
unless `len = 0`, `_chars[len] = 0`, `_len = len` (53) and the `ret` at 72. `push r14; push r13; push r12;
push rbp; push rbx`, `r13` = `s`, `rbp` = `this`, `rbx` = `r14` = `len`, `r12` = `_chars` across the calls.

The callees are hypotheses, as in `FV7z/Uau/Holds.lean`: a continuation at each entry (`kt` at the throw stub, `kn`,
`kd`; `kmA`, `km0`, `km1` for `wmemcpy` after each of the three ways to it, `Kc`), given the run from its return and
the callee's own post (`Pn`, `Pd`, `Pw`); `kr0` (for `len = 0`) and `kr1` at the return address.

- `V5`, `Sv5`: the bytes after the five pushes and the saved registers with the return address in bytes;
  `m5`, `sv5`: loads from `V5`.
- `lnd`, `tlm`: `len` and `_limit`; `g5`, `gA`, `gN`: the registers after the pushes, at 31 without
  `operator new`, at its `call`.
- `VF`: the bytes after `_chars[len] = 0; _len = len`; `Zs`: that store's 4 bytes writable and clear of `Sv5`.
- `vc_0`, `vc_31`, `vc_49`, `vc_53`, `vc_92`, `vc_108`, `vc_125`: the verification conditions of the pieces.
- `usf_ok`: from the entry, through the callees, to the return address.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Usf
open FV7z.Uau (zl VB rq_out rq_self)

/-- The `ja` to the throw stub. -/
def pja : List Byte := [0x0f, 0x87, 0x20, 0x3c, 0xfb, 0xff]
theorem pja_0 : ∀ feat, Dec feat pja 0 (FV7z.mk (.jcc 7) 64 [.rel 18446744073709239328] 6) := by dec_rfl
theorem wj_86 : pja <+: usf.drop 86 := by decide +kernel
theorem ja_86 (feat : Features) : Dec feat usf 86 (FV7z.mk (.jcc 7) 64 [.rel 18446744073709239328] 6) :=
  Dec.shift (j := 86) (k := 0) (pja_0 feat) wj_86 (Nat.zero_le _)
theorem tgt_86 : usf_at.add (86 + 6) + BitVec.ofNat 64 18446744073709239328 = (0x40140c#64).add 0 := by decide

/-- The `call`s to `wmemcpy`, `operator new` and the thunk of `operator delete []`. -/
def pcw : List Byte := [0xe8, 0x3f, 0xfb, 0x20, 0x00]
theorem pcw_0 : ∀ feat, Dec feat pcw 0 (FV7z.mk .call 64 [.rel 2161471] 5) := by dec_rfl
theorem wc_44 : pcw <+: usf.drop 44 := by decide +kernel
theorem call_44 (feat : Features) : Dec feat usf 44 (FV7z.mk .call 64 [.rel 2161471] 5) :=
  Dec.shift (j := 44) (k := 0) (pcw_0 feat) wc_44 (Nat.zero_le _)
theorem tgt_44 : usf_at.add (44 + 5) + BitVec.ofNat 64 2161471 = Wmc.wmc_at.add 0 := by decide
def pcn : List Byte := [0xe8, 0xb4, 0x51, 0x1b, 0x00]
theorem pcn_0 : ∀ feat, Dec feat pcn 0 (FV7z.mk .call 64 [.rel 1790388] 5) := by dec_rfl
theorem wc_103 : pcn <+: usf.drop 103 := by decide +kernel
theorem call_103 (feat : Features) : Dec feat usf 103 (FV7z.mk .call 64 [.rel 1790388] 5) :=
  Dec.shift (j := 103) (k := 0) (pcn_0 feat) wc_103 (Nat.zero_le _)
theorem tgt_103 : usf_at.add (103 + 5) + BitVec.ofNat 64 1790388 = Onw.onw_at.add 64 := by decide
def pcd : List Byte := [0xe8, 0xe3, 0x3c, 0x1b, 0x00]
theorem pcd_0 : ∀ feat, Dec feat pcd 0 (FV7z.mk .call 64 [.rel 1785059] 5) := by dec_rfl
theorem wc_120 : pcd <+: usf.drop 120 := by decide +kernel
theorem call_120 (feat : Features) : Dec feat usf 120 (FV7z.mk .call 64 [.rel 1785059] 5) :=
  Dec.shift (j := 120) (k := 0) (pcd_0 feat) wc_120 (Nat.zero_le _)

/-- The `ret`. -/
def pret : List Byte := [0xc3]
theorem pret_0 : ∀ feat, Dec feat pret 0 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem w_72 : pret <+: usf.drop 72 := by decide +kernel
theorem ret_72 (feat : Features) : Dec feat usf 72 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 72) (k := 0) (pret_0 feat) w_72 (Nat.zero_le _)

/-! ## Registers and bytes -/

/-- `len` and `_limit` (the bytes `V`, the entry's registers `g`). -/
abbrev lnd (g : Gprs) : BitVec 32 := BitVec.setWidth 32 g.rdx
abbrev tlm (V : Addr → Byte) (g : Gprs) : BitVec 32 := rdd(V, g.rdi + 12#64)

/-- The bytes after the pushes of `r14`, `r13`, `r12`, `rbp`, `rbx`. -/
abbrev V5 (V : Addr → Byte) (g : Gprs) : Addr → Byte :=
  Vst (Vst (Vst (Vst (Vst V (g.rsp - 8) (toBytesLE g.r14 8)) (g.rsp - 8 - 8) (toBytesLE g.r13 8))
    (g.rsp - 8 - 8 - 8) (toBytesLE g.r12 8)) (g.rsp - 8 - 8 - 8 - 8) (toBytesLE g.rbp 8))
    (g.rsp - 8 - 8 - 8 - 8 - 8) (toBytesLE g.rbx 8)

/-- The registers after the pushes: `r13` = `s`, `rbp` = `this`, `rbx` = `len`, 40 below the entry. -/
abbrev g5 (g : Gprs) : Gprs :=
  { g with r13 := g.rsi, rbp := g.rdi, rbx := zl (lnd g), rsp := g.rsp - 8 - 8 - 8 - 8 - 8 }

/-- The registers at 31 without `operator new`: `r12` = `_chars` (`q`), `r14` = `len`. -/
abbrev gA (g : Gprs) (q : BitVec 64) : Gprs := { g5 g with r12 := q, r14 := zl (lnd g) }

/-- The registers at the `call` of `operator new`: `r14` = `len`, `rdi` = `4 len + 4`. -/
abbrev gN (g : Gprs) : Gprs := { g5 g with r14 := zl (lnd g), rdi := zl (lnd g) * 4#64 + 4#64 }

/-- The bytes after `_chars[l] = 0` (`_chars` = `q`) and `_len = l` for the object at `p`. -/
abbrev VF (V : Addr → Byte) (q p : BitVec 64) (l : BitVec 32) : Addr → Byte :=
  Vst (Vst V (q + zl l * 4#64) (toBytesLE 0#32 4)) (p + 8#64) (toBytesLE l 4)

/-- The saved `rbx`, `rbp`, `r12`, `r13`, `r14` (the entry's `x`) and the return address `r` in the bytes `V`. -/
abbrev Sv5 (V : Addr → Byte) (x : Gprs) (r : Addr) : Prop :=
  rdq(V, x.rsp - 40) = x.rbx ∧ rdq(V, x.rsp - 32) = x.rbp ∧ rdq(V, x.rsp - 24) = x.r12 ∧
    rdq(V, x.rsp - 16) = x.r13 ∧ rdq(V, x.rsp - 8) = x.r14 ∧ rdq(V, x.rsp) = r

/-- The 4 bytes at `a` writable and clear of the saved registers and the return address (`x` the entry's). -/
abbrev Zs (Wl : List Rgn) (x : Gprs) (a : Addr) : Prop :=
  (∀ i < 4, Foot Wl (Addr.add a i)) ∧ a.toNat + 4 ≤ 2 ^ 64 ∧
    (a.toNat + 4 ≤ x.rsp.toNat - 40 ∨ x.rsp.toNat + 8 ≤ a.toNat)

/-- The registers at the return address from those `z` at 53 (`x` the entry's): the saved ones back. -/
abbrev gR (z x : Gprs) : Gprs :=
  { z with rbx := x.rbx, rbp := x.rbp, r12 := x.r12, r13 := x.r13, r14 := x.r14, rsp := x.rsp + 8 }

/-- The registers whose pushes at the four upper slots are those of `Uau.V0`. -/
abbrev gU (g : Gprs) : Gprs := { g with r13 := g.r14, r12 := g.r13, rbp := g.r12, rbx := g.rbp }

/-- `n` bytes apart from the pushes are those before them. -/
theorem m5 {V : Addr → Byte} {g : Gprs} (hp : 40 ≤ g.rsp.toNat) (y : Addr) (n : Nat) (hy : y.toNat + n ≤ 2 ^ 64)
    (hd : y.toNat + n ≤ g.rsp.toNat - 40 ∨ g.rsp.toNat ≤ y.toNat) :
    List.map (V5 V g) (byteAddrs y n) = List.map V (byteAddrs y n) := by
  have hlt := g.rsp.isLt
  have t1 : (g.rsp - 8).toNat = g.rsp.toNat - 8 := by rw [BitVec.toNat_sub]; simp <;> omega
  have t2 : (g.rsp - 8 - 8).toNat = g.rsp.toNat - 16 := by rw [BitVec.toNat_sub, t1]; simp <;> omega
  have t3 : (g.rsp - 8 - 8 - 8).toNat = g.rsp.toNat - 24 := by rw [BitVec.toNat_sub, t2]; simp <;> omega
  have t4 : (g.rsp - 8 - 8 - 8 - 8).toNat = g.rsp.toNat - 32 := by rw [BitVec.toNat_sub, t3]; simp <;> omega
  have t5 : (g.rsp - 8 - 8 - 8 - 8 - 8).toNat = g.rsp.toNat - 40 := by rw [BitVec.toNat_sub, t4]; simp <;> omega
  have a1 := Tun.rd_Vst (Uau.V0 V (gU g)) (g.rsp - 8 - 8 - 8 - 8 - 8) (toBytesLE g.rbx 8) y n
    (by rw [toBytesLE_length, t5]; omega) hy (by rw [toBytesLE_length, t5]; omega)
  have a2 := Uau.m0 (V := V) (g := gU g) (by show 32 ≤ g.rsp.toNat; omega) y n hy
    (by show y.toNat + n ≤ g.rsp.toNat - 32 ∨ g.rsp.toNat ≤ y.toNat; omega)
  exact a1.trans a2

/-- The saved registers and the return address in the bytes after the pushes. -/
theorem sv5 {V : Addr → Byte} {g : Gprs} {r : Addr} (hp : 40 ≤ g.rsp.toNat) (hp8 : g.rsp.toNat + 8 ≤ 2 ^ 64)
    (hr : rdq(V, g.rsp) = r) : Sv5 (V5 V g) g r := by
  have hlt := g.rsp.isLt
  obtain ⟨b1, b2, b3, b4, b5⟩ := Uau.sv0 (V := V) (g := gU g) (r := r) (by show 40 ≤ g.rsp.toNat; omega) hp8 hr
  have t1 : (g.rsp - 8).toNat = g.rsp.toNat - 8 := by rw [BitVec.toNat_sub]; simp <;> omega
  have t2 : (g.rsp - 8 - 8).toNat = g.rsp.toNat - 16 := by rw [BitVec.toNat_sub, t1]; simp <;> omega
  have t3 : (g.rsp - 8 - 8 - 8).toNat = g.rsp.toNat - 24 := by rw [BitVec.toNat_sub, t2]; simp <;> omega
  have t4 : (g.rsp - 8 - 8 - 8 - 8).toNat = g.rsp.toNat - 32 := by rw [BitVec.toNat_sub, t3]; simp <;> omega
  have t5 : (g.rsp - 8 - 8 - 8 - 8 - 8).toNat = g.rsp.toNat - 40 := by rw [BitVec.toNat_sub, t4]; simp <;> omega
  have u8 : (g.rsp - 8).toNat = g.rsp.toNat - 8 := t1
  have u16 : (g.rsp - 16).toNat = g.rsp.toNat - 16 := by rw [BitVec.toNat_sub]; simp <;> omega
  have u24 : (g.rsp - 24).toNat = g.rsp.toNat - 24 := by rw [BitVec.toNat_sub]; simp <;> omega
  have u32 : (g.rsp - 32).toNat = g.rsp.toNat - 32 := by rw [BitVec.toNat_sub]; simp <;> omega
  have f40 : g.rsp - 40 = g.rsp - 8 - 8 - 8 - 8 - 8 := by
    apply BitVec.eq_of_toNat_eq; rw [t5, BitVec.toNat_sub]; simp <;> omega
  have o : ∀ x : Addr, x.toNat + 8 ≤ 2 ^ 64 → g.rsp.toNat - 32 ≤ x.toNat →
      rdq(V5 V g, x) = rdq(Uau.V0 V (gU g), x) := fun x hx h =>
    rq_out _ (g.rsp - 8 - 8 - 8 - 8 - 8) x _ (by rw [t5]; omega) hx (by rw [t5]; omega)
  refine ⟨?_, (o (g.rsp - 32) (by rw [u32]; omega) (Nat.le_of_eq u32.symm)).trans b1,
    (o (g.rsp - 24) (by rw [u24]; omega) (by rw [u24]; omega)).trans b2,
    (o (g.rsp - 16) (by rw [u16]; omega) (by rw [u16]; omega)).trans b3,
    (o (g.rsp - 8) (by rw [u8]; omega) (by rw [u8]; omega)).trans b4, (o g.rsp hp8 (by omega)).trans b5⟩
  rw [f40]
  exact rq_self _ _ _ (by rw [t5]; omega)

/-! ## The conditions -/

variable {F : Footprint} {Wl : List Rgn}

set_option maxHeartbeats 1000000 in
/-- The pushes, `mov r13, rsi; mov rbp, rdi; mov ebx, edx; cmp [rdi + 12], edx; jb`: if `_limit < len`,
`cmp edx, 0x3ffffffe` to the `ja` at 86 (its flags: above the limit), else `mov r12, [rdi]; mov r14d, edx` to 31. -/
theorem vc_0 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} {m : BitVec 32} {q : BitVec 64}
    (hs1 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8) i)) (hs2 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8) i))
    (hs3 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8 - 8) i))
    (hs4 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8 - 8 - 8) i))
    (hs5 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8 - 8 - 8 - 8) i))
    (hm : rdd(V5 V g, g.rdi + 12#64) = m) (hq : rdq(V5 V g, g.rdi) = q)
    (f12 : ∀ i < 4, Foot F.data (Addr.add (g.rdi + 12#64) i)) (f0 : ∀ i < 8, Foot F.data (Addr.add g.rdi i))
    (h86 : m.toNat < (lnd g).toNat → ∀ fl, fl.cond 7 = decide (1073741822 < (lnd g).toNat) →
      Q 86 (g5 g) fl (V5 V g))
    (h31 : ¬ m.toNat < (lnd g).toNat → ∀ fl, Q 31 (gA g q) fl (V5 V g)) : W_0 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [V5] at hs1 hs2 hs3 hs4 hs5 hm hq f12 f0 h86 h31 ⊢
  by_cases hc : m.toNat < (BitVec.setWidth 32 rdx).toNat
  · have hb : decide (m.toNat < (BitVec.setWidth 32 rdx).toNat) = true := decide_eq_true hc
    wpx [W_0, W_80, W_25, o0, o6, o1, Op.cmpmr, hm, hq, hb, eq_self_iff_true, Bool.true_eq_false,
      Bool.false_eq_true, false_implies, implies_true]
    all_goals repeat' (first
      | exact h86 hc _ (Arb.c7 _ _)
      | (rename_i hfl; subst hfl; exact h86 hc _ (Arb.c7 _ _))
      | assumption
      | exact trivial
      | apply And.intro
      | intro _)
  · have hb : decide (m.toNat < (BitVec.setWidth 32 rdx).toNat) = false := decide_eq_false hc
    wpx [W_0, W_80, W_25, o0, o6, o1, Op.cmpmr, hm, hq, hb, eq_self_iff_true, Bool.true_eq_false,
      Bool.false_eq_true, false_implies, implies_true]
    all_goals repeat' (first | exact h31 hc _ | assumption | exact trivial | apply And.intro | intro _)

/-- `test ebx, ebx; je 53`, else `mov rdi, r12; mov rdx, r14; mov rsi, r13` to the `call` at 44. -/
theorem vc_31 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} {l : BitVec 32} (hbx : g.rbx = zl l)
    (h53 : l = 0 → ∀ fl, Q 53 g fl V)
    (h44 : l ≠ 0 → ∀ fl, Q 44 { g with rdi := g.r12, rdx := g.r14, rsi := g.r13 } fl V) :
    W_31 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hbx h53 h44 ⊢
  subst hbx
  by_cases hz : l = 0
  · have hb : (l == 0) = true := beq_iff_eq.2 hz
    wpx [W_31, W_35, o2, o3, hb, BitVec.and_self, Bool.false_eq_true, Bool.true_eq_false, false_implies,
      implies_true]
    all_goals repeat' (first | exact h53 hz _ | assumption | exact trivial | apply And.intro | intro _)
  · have hb : (l == 0) = false := beq_eq_false_iff_ne.2 hz
    wpx [W_31, W_35, o2, o3, hb, BitVec.and_self, Bool.false_eq_true, Bool.true_eq_false, false_implies,
      implies_true]
    all_goals repeat' (first | exact h44 hz _ | assumption | exact trivial | apply And.intro | intro _)

/-- Back from `wmemcpy`: `mov r12, [rbp]` to 53. -/
theorem vc_49 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} {p : Addr} (hbp : g.rbp = p)
    (f0 : ∀ i < 8, Foot F.data (Addr.add p i)) (h : ∀ fl, Q 53 { g with r12 := rdq(V, p) } fl V) :
    W_49 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hbp f0 h ⊢
  subst hbp
  wpx [W_49, o4]
  all_goals repeat' (first | exact h _ | assumption | exact trivial | apply And.intro | intro _)

set_option maxHeartbeats 1000000 in
/-- `mov dword [r12 + r14 * 4], 0; mov [rbp + 8], ebx; pop rbx; pop rbp; pop r12; pop r13; pop r14` to the `ret`
at 72. -/
theorem vc_53 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} {p q : BitVec 64} {l : BitVec 32}
    (h12 : g.r12 = q) (h14 : g.r14 = zl l) (hbp : g.rbp = p) (hbx : g.rbx = zl l)
    (w4 : ∀ i < 4, Foot Wl (Addr.add (q + zl l * 4#64) i)) (w8 : ∀ i < 4, Foot Wl (Addr.add (p + 8#64) i))
    (hl0 : ∀ i < 8, Foot F.data (Addr.add g.rsp i)) (hl1 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8) i))
    (hl2 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8 + 8) i))
    (hl3 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8 + 8 + 8) i))
    (hl4 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8 + 8 + 8 + 8) i))
    (h : ∀ fl, Q 72
      { g with
          rbx := rdq(VF V q p l, g.rsp),
          rbp := rdq(VF V q p l, g.rsp + 8),
          r12 := rdq(VF V q p l, g.rsp + 8 + 8),
          r13 := rdq(VF V q p l, g.rsp + 8 + 8 + 8),
          r14 := rdq(VF V q p l, g.rsp + 8 + 8 + 8 + 8),
          rsp := g.rsp + 8 + 8 + 8 + 8 + 8 } fl (VF V q p l)) :
    W_53 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h12 h14 hbp hbx hl0 hl1 hl2 hl3 hl4 h ⊢
  subst h12 h14 hbp hbx
  wpx [W_53, o5]
  all_goals repeat' (first | exact h _ | assumption | exact trivial | apply And.intro | intro _)

/-- `mov r14d, edx; lea rdi, [r14 * 4 + 4]` to the `call` at 103. -/
theorem vc_92 {g x : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} (hg : g = g5 x)
    (h : ∀ fl, Q 103 (gN x) fl V) : W_92 F Wl Q g f V := by
  subst hg
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := x
  dsimp only at h ⊢
  wpx [W_92, o7]
  all_goals repeat' (first | exact h _ | assumption | exact trivial | apply And.intro | intro _)

/-- Back from `operator new`: `mov rdi, [rbp]; mov r12, rax; test rdi, rdi; je 125`, else to the `call` at 120. -/
theorem vc_108 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} {p : Addr} (hbp : g.rbp = p)
    (f0 : ∀ i < 8, Foot F.data (Addr.add p i))
    (h125 : rdq(V, p) = 0 → ∀ fl, Q 125 { g with rdi := rdq(V, p), r12 := g.rax } fl V)
    (h120 : rdq(V, p) ≠ 0 → ∀ fl, Q 120 { g with rdi := rdq(V, p), r12 := g.rax } fl V) :
    W_108 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hbp f0 h125 h120 ⊢
  subst hbp
  by_cases h1 : rdq(V, rbp) = 0
  · have hb : (rdq(V, rbp) == 0) = true := beq_iff_eq.2 h1
    wpx [W_108, o8, hb, BitVec.and_self, Bool.false_eq_true, Bool.true_eq_false, false_implies, implies_true]
    all_goals repeat' (first | exact h125 h1 _ | assumption | exact trivial | apply And.intro | intro _)
  · have hb : (rdq(V, rbp) == 0) = false := beq_eq_false_iff_ne.2 h1
    wpx [W_108, o8, hb, BitVec.and_self, Bool.false_eq_true, Bool.true_eq_false, false_implies, implies_true]
    all_goals repeat' (first | exact h120 h1 _ | assumption | exact trivial | apply And.intro | intro _)

/-- `mov [rbp], r12; mov [rbp + 12], ebx` and the jump to 31. -/
theorem vc_125 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} {p q : BitVec 64} {l : BitVec 32}
    (hbp : g.rbp = p) (h12 : g.r12 = q) (hbx : g.rbx = zl l) (w0 : ∀ i < 8, Foot Wl (Addr.add p i))
    (w12 : ∀ i < 4, Foot Wl (Addr.add (p + 12#64) i)) (h : ∀ fl, Q 31 g fl (VB V p q l)) :
    W_125 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hbp h12 hbx w0 w12 h ⊢
  subst hbp h12 hbx
  wpx [W_125, o9]
  all_goals repeat' (first | exact h _ | assumption | exact trivial | apply And.intro | intro _)

/-- At `wmemcpy`'s entry from 31 with the registers `g` and the bytes `W` there (`x` the entry's registers, `r`
the return address, `l` = `len`): `rdi` = `r12`, `rdx` = `r14`, `rsi` = `r13`, `rsp` 48 below the entry's, the
return address pushed; back at `usf_at + 49` with `rsp` 40 below the entry's, `rbp` = `this`, `rbx` = `r14` = `len`,
the saved registers and the return address (`Sv5`), the 4 bytes at `_chars + 4 len` writable and clear of them
(`Zs`) and `wmemcpy`'s post `Pw`. -/
def Kc (prof : Profile) (L : List (Addr × List Byte)) (o : Oracle) (gev : List Event)
    (gP : State → Nat → List Event → Prop) (gE : Outcome → List Event → Prop) (F : Footprint) (Wl : List Rgn)
    (s₀ : State) (x : Gprs) (r : Addr) (l : BitVec 32) (Pw : State → State → (Addr → Byte) → Prop) (g : Gprs)
    (W : Addr → Byte) : Prop :=
  ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y →
    Agree F Y.proc.mm.mem (Vst W (x.rsp - 48) (toBytesLE (usf_at.add 49) 8)) →
    Y.cpu.rip = Wmc.wmc_at → Y.cpu.gpr = { g with rdi := g.r12, rdx := g.r14, rsi := g.r13 }.set 4 (x.rsp - 48) →
    (∀ (Zw : State) (V₂ : Addr → Byte) (t'' : Nat), KeptW Wl s₀ Zw → Agree F Zw.proc.mm.mem V₂ →
      Zw.cpu.rip = usf_at.add 49 → Zw.cpu.gpr.rsp = x.rsp - 40 → Zw.cpu.gpr.rbp = x.rdi →
      Zw.cpu.gpr.rbx = zl l → Zw.cpu.gpr.r14 = zl l → Sv5 V₂ x r → Zs Wl x (rdq(V₂, x.rdi) + zl l * 4#64) →
      Pw Y Zw V₂ → GoG prof L o gev gP gE Zw t'') →
    GoG prof L o gev gP gE Y t'

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {X : State} {t : Nat} {V : Addr → Byte}

/-- `UString::SetFrom (s, len)` (`this` = `rdi`, `s` = `rsi`, `len` = `edx`) from its entry. If `_limit < len`:
above `0x3ffffffe` at the throw stub with the registers `g5` (`kt`); else at `operator new`'s entry with the
registers `gN` (`kn`), back at `usf_at + 108` (`Pn`), at the thunk of `operator delete []` with `rdi` = `_chars`
unless null (`kd`), back at `usf_at + 125` (`Pd`). Then, and also without `operator new`, for `len ≠ 0` at
`wmemcpy`'s entry (`kmA`, `km0`, `km1`: `Kc`), back at `usf_at + 49` (`Pw`), at the return address with
`_chars[len] = 0`, `_len = len` and the saved registers back (`kr1`); for `len = 0` (the buffer as it is) straight
there (`kr0`, with `_chars` writable and clear of the saved registers: `hz4`). -/
theorem usf_ok {Pn : State → (Addr → Byte) → Prop} {Pd : State → State → (Addr → Byte) → Prop}
    {Pw : State → State → (Addr → Byte) → Prop}
    (c : Seg prof F Wl L s₀ o) (hin : CodeIn L usf_at usf) (hinN : CodeIn L Onw.onw_at Onw.onw)
    (hinW : CodeIn L Wmc.wmc_at Wmc.wmc) {codeD : List Byte} (hinD : CodeIn L 0x6014f0#64 codeD)
    (hD : 0 < codeD.length) {codeT : List Byte} (hinT : CodeIn L 0x40140c#64 codeT) (hT : 0 < codeT.length)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = usf_at)
    (hp : 48 ≤ X.cpu.gpr.rsp.toNat) (hp8 : X.cpu.gpr.rsp.toNat + 8 ≤ 2 ^ 64)
    (hs1 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8) i))
    (hs2 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 16) i))
    (hs3 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 24) i))
    (hs4 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 32) i))
    (hs5 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 40) i))
    (hs6 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 48) i))
    (hl : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsp i))
    (fd0 : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rdi i))
    (fd12 : ∀ i < 4, Foot F.data (Addr.add (X.cpu.gpr.rdi + 12#64) i))
    (fw0 : ∀ i < 8, Foot Wl (Addr.add X.cpu.gpr.rdi i))
    (fw8 : ∀ i < 4, Foot Wl (Addr.add (X.cpu.gpr.rdi + 8#64) i))
    (fw12 : ∀ i < 4, Foot Wl (Addr.add (X.cpu.gpr.rdi + 12#64) i))
    (hqd : X.cpu.gpr.rdi.toNat + 16 ≤ 2 ^ 64)
    (hdd : X.cpu.gpr.rdi.toNat + 16 ≤ X.cpu.gpr.rsp.toNat - 40 ∨ X.cpu.gpr.rsp.toNat ≤ X.cpu.gpr.rdi.toNat)
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (hra : rdq(V, X.cpu.gpr.rsp) = e₂.add j₂)
    (hz4 : lnd X.cpu.gpr = 0 → Zs Wl X.cpu.gpr (rdq(V, X.cpu.gpr.rdi) + zl (lnd X.cpu.gpr) * 4#64))
    (kt : ∀ (Y : State) (t' : Nat), (tlm V X.cpu.gpr).toNat < (lnd X.cpu.gpr).toNat →
      1073741822 < (lnd X.cpu.gpr).toNat → KeptW Wl s₀ Y → Agree F Y.proc.mm.mem (V5 V X.cpu.gpr) →
      Y.cpu.rip = 0x40140c#64 → Y.cpu.gpr = g5 X.cpu.gpr → GoG prof L o gev gP gE Y t')
    (kn : ∀ (Y : State) (t' : Nat), (tlm V X.cpu.gpr).toNat < (lnd X.cpu.gpr).toNat →
      ¬ 1073741822 < (lnd X.cpu.gpr).toNat → KeptW Wl s₀ Y →
      Agree F Y.proc.mm.mem (Vst (V5 V X.cpu.gpr) (X.cpu.gpr.rsp - 48) (toBytesLE (usf_at.add 108) 8)) →
      Y.cpu.rip = Onw.onw_at.add 64 → Y.cpu.gpr = (gN X.cpu.gpr).set 4 (X.cpu.gpr.rsp - 48) →
      (∀ (Zn : State) (V₁ : Addr → Byte) (t'' : Nat), KeptW Wl s₀ Zn → Agree F Zn.proc.mm.mem V₁ →
        Zn.cpu.rip = usf_at.add 108 → Zn.cpu.gpr.rsp = X.cpu.gpr.rsp - 40 → Zn.cpu.gpr.rbp = X.cpu.gpr.rdi →
        Zn.cpu.gpr.rbx = zl (lnd X.cpu.gpr) → Pn Zn V₁ → GoG prof L o gev gP gE Zn t'') →
      GoG prof L o gev gP gE Y t')
    (kd : ∀ (Zn : State) (V₁ : Addr → Byte), Pn Zn V₁ → rdq(V₁, X.cpu.gpr.rdi) ≠ 0 →
      ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y →
      Agree F Y.proc.mm.mem (Vst V₁ (X.cpu.gpr.rsp - 48) (toBytesLE (usf_at.add 125) 8)) →
      Y.cpu.rip = 0x6014f0#64 →
      Y.cpu.gpr = { Zn.cpu.gpr with rdi := rdq(V₁, X.cpu.gpr.rdi), r12 := Zn.cpu.gpr.rax }.set 4
        (X.cpu.gpr.rsp - 48) →
      (∀ (Zd : State) (V₃ : Addr → Byte) (t'' : Nat), KeptW Wl s₀ Zd → Agree F Zd.proc.mm.mem V₃ →
        Zd.cpu.rip = usf_at.add 125 → Zd.cpu.gpr.rsp = X.cpu.gpr.rsp - 40 → Zd.cpu.gpr.rbp = X.cpu.gpr.rdi →
        Zd.cpu.gpr.rbx = zl (lnd X.cpu.gpr) → Zd.cpu.gpr.r12 = Zn.cpu.gpr.rax → Pd Zn Zd V₃ →
        GoG prof L o gev gP gE Zd t'') →
      GoG prof L o gev gP gE Y t')
    (kmA : lnd X.cpu.gpr ≠ 0 → ¬ (tlm V X.cpu.gpr).toNat < (lnd X.cpu.gpr).toNat →
      Kc prof L o gev gP gE F Wl s₀ X.cpu.gpr (e₂.add j₂) (lnd X.cpu.gpr) Pw
        (gA X.cpu.gpr (rdq(V, X.cpu.gpr.rdi))) (V5 V X.cpu.gpr))
    (km0 : ∀ (Zn : State) (V₁ : Addr → Byte), Pn Zn V₁ → rdq(V₁, X.cpu.gpr.rdi) = 0 →
      Kc prof L o gev gP gE F Wl s₀ X.cpu.gpr (e₂.add j₂) (lnd X.cpu.gpr) Pw
        { Zn.cpu.gpr with rdi := rdq(V₁, X.cpu.gpr.rdi), r12 := Zn.cpu.gpr.rax }
        (VB V₁ X.cpu.gpr.rdi Zn.cpu.gpr.rax (lnd X.cpu.gpr)))
    (km1 : ∀ (Zn Zd : State) (V₃ : Addr → Byte), Pd Zn Zd V₃ →
      Kc prof L o gev gP gE F Wl s₀ X.cpu.gpr (e₂.add j₂) (lnd X.cpu.gpr) Pw Zd.cpu.gpr
        (VB V₃ X.cpu.gpr.rdi Zn.cpu.gpr.rax (lnd X.cpu.gpr)))
    (kr0 : lnd X.cpu.gpr = 0 → ∀ (Z' : State) (t' : Nat), KeptW Wl s₀ Z' →
      Agree F Z'.proc.mm.mem (VF (V5 V X.cpu.gpr) (rdq(V, X.cpu.gpr.rdi)) X.cpu.gpr.rdi (lnd X.cpu.gpr)) →
      Z'.cpu.rip = e₂.add j₂ → Z'.cpu.gpr = gR (gA X.cpu.gpr (rdq(V, X.cpu.gpr.rdi))) X.cpu.gpr →
      GoG prof L o gev gP gE Z' t')
    (kr1 : ∀ (Y Zw : State) (V₂ : Addr → Byte) (Z' : State) (t' : Nat), Pw Y Zw V₂ → KeptW Wl s₀ Z' →
      Agree F Z'.proc.mm.mem (VF V₂ (rdq(V₂, X.cpu.gpr.rdi)) X.cpu.gpr.rdi (lnd X.cpu.gpr)) →
      Z'.cpu.rip = e₂.add j₂ → Z'.cpu.gpr = gR { Zw.cpu.gpr with r12 := rdq(V₂, X.cpu.gpr.rdi) } X.cpu.gpr →
      GoG prof L o gev gP gE Z' t') :
    GoG prof L o gev gP gE X t := by
  have hlt := X.cpu.gpr.rsp.isLt
  have tn8 : (X.cpu.gpr.rsp - 8).toNat = X.cpu.gpr.rsp.toNat - 8 := by rw [BitVec.toNat_sub]; simp <;> omega
  have tn16 : (X.cpu.gpr.rsp - 16).toNat = X.cpu.gpr.rsp.toNat - 16 := by rw [BitVec.toNat_sub]; simp <;> omega
  have tn24 : (X.cpu.gpr.rsp - 24).toNat = X.cpu.gpr.rsp.toNat - 24 := by rw [BitVec.toNat_sub]; simp <;> omega
  have tn32 : (X.cpu.gpr.rsp - 32).toNat = X.cpu.gpr.rsp.toNat - 32 := by rw [BitVec.toNat_sub]; simp <;> omega
  have tn40 : (X.cpu.gpr.rsp - 40).toNat = X.cpu.gpr.rsp.toNat - 40 := by rw [BitVec.toNat_sub]; simp <;> omega
  have tn48 : (X.cpu.gpr.rsp - 48).toNat = X.cpu.gpr.rsp.toNat - 48 := by rw [BitVec.toNat_sub]; simp <;> omega
  have e16 : X.cpu.gpr.rsp - 8 - 8 = X.cpu.gpr.rsp - 16 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, tn8, tn16]
    simp <;> omega
  have e24 : X.cpu.gpr.rsp - 8 - 8 - 8 = X.cpu.gpr.rsp - 24 := by
    rw [e16]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, tn16, tn24]
    simp <;> omega
  have e32 : X.cpu.gpr.rsp - 8 - 8 - 8 - 8 = X.cpu.gpr.rsp - 32 := by
    rw [e24]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, tn24, tn32]
    simp <;> omega
  have e40 : X.cpu.gpr.rsp - 8 - 8 - 8 - 8 - 8 = X.cpu.gpr.rsp - 40 := by
    rw [e32]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, tn32, tn40]
    simp <;> omega
  have c48 : X.cpu.gpr.rsp - 40 - 8 = X.cpu.gpr.rsp - 48 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, tn40, tn48]
    simp <;> omega
  have a40 : X.cpu.gpr.rsp - 40 + 8 = X.cpu.gpr.rsp - 32 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, tn40, tn32]
    simp <;> omega
  have a32 : X.cpu.gpr.rsp - 32 + 8 = X.cpu.gpr.rsp - 24 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, tn32, tn24]
    simp <;> omega
  have a24 : X.cpu.gpr.rsp - 24 + 8 = X.cpu.gpr.rsp - 16 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, tn24, tn16]
    simp <;> omega
  have a16 : X.cpu.gpr.rsp - 16 + 8 = X.cpu.gpr.rsp - 8 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, tn16, tn8]
    simp <;> omega
  have a8 : X.cpu.gpr.rsp - 8 + 8 = X.cpu.gpr.rsp := BitVec.sub_add_cancel _ _
  have h40 : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rsp - 40) i) := fun i hi => c.hws _ (hs5 i hi)
  have h32 : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rsp - 32) i) := fun i hi => c.hws _ (hs4 i hi)
  have h24 : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rsp - 24) i) := fun i hi => c.hws _ (hs3 i hi)
  have h16 : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rsp - 16) i) := fun i hi => c.hws _ (hs2 i hi)
  have h8 : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rsp - 8) i) := fun i hi => c.hws _ (hs1 i hi)
  have td8 : (X.cpu.gpr.rdi + 8#64).toNat = X.cpu.gpr.rdi.toNat + 8 := by
    rw [BitVec.toNat_add]; simp <;> omega
  have td12 : (X.cpu.gpr.rdi + 12#64).toNat = X.cpu.gpr.rdi.toNat + 12 := by
    rw [BitVec.toNat_add]; simp <;> omega
  -- from 53 (`_chars[len] = 0; _len = len`) to the return address
  have fin : ∀ (U : State) (g : Gprs) (W : Addr → Byte) (q : BitVec 64) (t' : Nat), KeptW Wl s₀ U →
      Agree F U.proc.mm.mem W → U.cpu.rip = usf_at.add 53 → U.cpu.gpr = g → g.rsp = X.cpu.gpr.rsp - 40 →
      g.rbp = X.cpu.gpr.rdi → g.rbx = zl (lnd X.cpu.gpr) → g.r14 = zl (lnd X.cpu.gpr) → g.r12 = q →
      Sv5 W X.cpu.gpr (e₂.add j₂) → Zs Wl X.cpu.gpr (q + zl (lnd X.cpu.gpr) * 4#64) →
      (∀ (Z' : State) (t'' : Nat), KeptW Wl s₀ Z' →
        Agree F Z'.proc.mm.mem (VF W q X.cpu.gpr.rdi (lnd X.cpu.gpr)) → Z'.cpu.rip = e₂.add j₂ →
        Z'.cpu.gpr = gR g X.cpu.gpr → GoG prof L o gev gP gE Z' t'') →
      GoG prof L o gev gP gE U t' := by
    intro U g W q t' hKU hAU hrU hgU hs hbp hbx h14 h12 hsv hzs k
    subst hgU
    obtain ⟨hb1, hb2, hb3, hb4, hb5, hb6⟩ := hsv
    obtain ⟨hw4, hpb, hpd⟩ := hzs
    have r2 : ∀ y : Addr, y.toNat + 8 ≤ 2 ^ 64 → X.cpu.gpr.rsp.toNat - 40 ≤ y.toNat → y.toNat ≤ X.cpu.gpr.rsp.toNat →
        rdq(VF W q X.cpu.gpr.rdi (lnd X.cpu.gpr), y) = rdq(W, y) := by
      intro y hy h1 h2
      refine (Ucn.rq_out4 _ (X.cpu.gpr.rdi + 8#64) y _ (by rw [td8]; omega) hy (by rw [td8]; omega)).trans ?_
      exact Ucn.rq_out4 W _ y _ hpb hy (by omega)
    have q40 := (r2 (X.cpu.gpr.rsp - 40) (by rw [tn40]; omega) (Nat.le_of_eq tn40.symm)
      (by rw [tn40]; omega)).trans hb1
    have q32 := (r2 (X.cpu.gpr.rsp - 32) (by rw [tn32]; omega) (by rw [tn32]; omega) (by rw [tn32]; omega)).trans hb2
    have q24 := (r2 (X.cpu.gpr.rsp - 24) (by rw [tn24]; omega) (by rw [tn24]; omega) (by rw [tn24]; omega)).trans hb3
    have q16 := (r2 (X.cpu.gpr.rsp - 16) (by rw [tn16]; omega) (by rw [tn16]; omega) (by rw [tn16]; omega)).trans hb4
    have q8 := (r2 (X.cpu.gpr.rsp - 8) (by rw [tn8]; omega) (by rw [tn8]; omega) (by rw [tn8]; omega)).trans hb5
    have q0 := (r2 X.cpu.gpr.rsp hp8 (by omega) (Nat.le_refl _)).trans hb6
    refine (c_53 prof).run c hin (fun j' g' _ V' => j' = 72 ∧
        g' = { U.cpu.gpr with
            rbx := X.cpu.gpr.rbx, rbp := X.cpu.gpr.rbp, r12 := X.cpu.gpr.r12, r13 := X.cpu.gpr.r13,
            r14 := X.cpu.gpr.r14, rsp := X.cpu.gpr.rsp } ∧
        V' = VF W q X.cpu.gpr.rdi (lnd X.cpu.gpr)) hKU hAU hrU
      (vc_53 h12 h14 hbp hbx hw4 fw8 (by rw [hs]; exact h40) (by rw [hs, a40]; exact h32)
        (by rw [hs, a40, a32]; exact h24) (by rw [hs, a40, a32, a24]; exact h16)
        (by rw [hs, a40, a32, a24, a16]; exact h8)
        fun _ => ⟨rfl, by rw [hs, a40, a32, a24, a16, a8, q40, q32, q24, q16, q8], rfl⟩) ?_
    rintro j' g fl V₄ ⟨rfl, rfl, hV₄⟩ U' t₄ hKU' hAU' hrU' hgU' -
    subst V₄
    have hsU : U'.cpu.gpr.rsp = X.cpu.gpr.rsp := by rw [hgU']
    refine c.s_ret hKU' hAU' hin (lt_len (by decide)) hrU' (ret_72 _) (by rw [hsU]; exact hl) hin₂ h₂
      (by rw [hsU]; exact q0) ?_
    rintro Z' t₅ hKZ' hAZ' ⟨hrZ', hgZ'⟩
    refine k Z' t₅ hKZ' hAZ' hrZ' ?_
    rw [hgZ', hgU']
    try rfl
  -- from 31: for `len = 0` on to 53 (`k53`), else `wmemcpy` (`Kc`), back at 49, then 53
  have run31 : ∀ (U : State) (g : Gprs) (W : Addr → Byte) (t' : Nat), KeptW Wl s₀ U →
      Agree F U.proc.mm.mem W → U.cpu.rip = usf_at.add 31 → U.cpu.gpr = g → g.rsp = X.cpu.gpr.rsp - 40 →
      g.rbx = zl (lnd X.cpu.gpr) →
      (lnd X.cpu.gpr = 0 → ∀ (U' : State) (t'' : Nat), KeptW Wl s₀ U' → Agree F U'.proc.mm.mem W →
        U'.cpu.rip = usf_at.add 53 → U'.cpu.gpr = g → GoG prof L o gev gP gE U' t'') →
      (lnd X.cpu.gpr ≠ 0 → Kc prof L o gev gP gE F Wl s₀ X.cpu.gpr (e₂.add j₂) (lnd X.cpu.gpr) Pw g W) →
      GoG prof L o gev gP gE U t' := by
    intro U g W t' hKU hAU hrU hgU hs hbx k53 kc
    subst hgU
    refine (c_31 prof).run c hin (fun j' g' _ V' => V' = W ∧
        ((j' = 53 ∧ lnd X.cpu.gpr = 0 ∧ g' = U.cpu.gpr) ∨
         (j' = 44 ∧ lnd X.cpu.gpr ≠ 0 ∧
           g' = { U.cpu.gpr with rdi := U.cpu.gpr.r12, rdx := U.cpu.gpr.r14, rsi := U.cpu.gpr.r13 }))) hKU hAU hrU
      (vc_31 hbx (fun h0 _ => ⟨rfl, .inl ⟨rfl, h0, rfl⟩⟩) (fun h0 _ => ⟨rfl, .inr ⟨rfl, h0, rfl⟩⟩)) ?_
    rintro j' g fl V₄ ⟨hV₄, h⟩ Y t₄ hKY hAY hrY hgY -
    subst V₄
    rcases h with ⟨rfl, h0, rfl⟩ | ⟨rfl, h0, rfl⟩
    · exact k53 h0 Y t₄ hKY hAY hrY hgY
    have hsY : Y.cpu.gpr.rsp = X.cpu.gpr.rsp - 40 := by rw [hgY]; exact hs
    have hst : ∀ i < 8, Foot Wl (Addr.add (Y.cpu.gpr.rsp - 8) i) := by rw [hsY, c48]; exact hs6
    refine c.s_call_x hKY hAY hin (lt_len (by decide)) hrY (call_44 _) hinW (tgt := 0) (Wmc.lt_len (by decide))
      tgt_44 hst ?_
    rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
    rw [hsY, c48] at hA₂
    refine kc h0 Y₂ t₂ hK₂ hA₂ (by rw [hr₂, addr_add_zero]) (by rw [hg₂, hsY, c48, hgY]) ?_
    -- back from `wmemcpy`
    intro Zw V₂ t₃ hKw hAw hrw hws hwbp hwbx hw14 hsv hzs hPw
    refine (c_49 prof).run c hin (fun j' g' _ V' => j' = 53 ∧
        g' = { Zw.cpu.gpr with r12 := rdq(V₂, X.cpu.gpr.rdi) } ∧ V' = V₂) hKw hAw hrw
      (vc_49 hwbp fd0 fun _ => ⟨rfl, rfl, rfl⟩) ?_
    rintro j' g fl V₅ ⟨rfl, rfl, hV₅⟩ U₅ t₅ hK₅ hA₅ hr₅ hg₅ -
    subst V₅
    exact fin U₅ _ V₂ (rdq(V₂, X.cpu.gpr.rdi)) t₅ hK₅ hA₅ hr₅ hg₅ hws hwbp hwbx hw14 rfl hsv hzs
      fun Z' t₆ hKZ hAZ hrZ hgZ => kr1 Y₂ Zw V₂ Z' t₆ hPw hKZ hAZ hrZ hgZ
  -- from 125 (`_chars = newBuf; _limit = len`) to 31
  have run125 : ∀ (U : State) (g : Gprs) (W : Addr → Byte) (q : BitVec 64) (t' : Nat), KeptW Wl s₀ U →
      Agree F U.proc.mm.mem W → U.cpu.rip = usf_at.add 125 → U.cpu.gpr = g → g.rsp = X.cpu.gpr.rsp - 40 →
      g.rbp = X.cpu.gpr.rdi → g.rbx = zl (lnd X.cpu.gpr) → g.r12 = q → lnd X.cpu.gpr ≠ 0 →
      Kc prof L o gev gP gE F Wl s₀ X.cpu.gpr (e₂.add j₂) (lnd X.cpu.gpr) Pw g
        (VB W X.cpu.gpr.rdi q (lnd X.cpu.gpr)) →
      GoG prof L o gev gP gE U t' := by
    intro U g W q t' hKU hAU hrU hgU hs hbp hbx h12 hnz k
    subst hgU
    refine (c_125 prof).run c hin (fun j' g' _ V' => j' = 31 ∧ g' = U.cpu.gpr ∧
        V' = VB W X.cpu.gpr.rdi q (lnd X.cpu.gpr)) hKU hAU hrU
      (vc_125 hbp h12 hbx fw0 fw12 fun _ => ⟨rfl, rfl, rfl⟩) ?_
    rintro j' g fl V₄ ⟨rfl, rfl, hV₄⟩ U' t₄ hKU' hAU' hrU' hgU' -
    subst V₄
    exact run31 U' U.cpu.gpr _ t₄ hKU' hAU' hrU' hgU' hs hbx (fun h0 => absurd h0 hnz) fun _ => k
  -- the loads before any store
  have hm0 : rdd(V5 V X.cpu.gpr, X.cpu.gpr.rdi + 12#64) = tlm V X.cpu.gpr :=
    congrArg (ofBytesLE 32) (m5 (V := V) (g := X.cpu.gpr) (by omega) (X.cpu.gpr.rdi + 12#64) 4
      (by rw [td12]; omega) (by rw [td12]; omega))
  have hq0 : rdq(V5 V X.cpu.gpr, X.cpu.gpr.rdi) = rdq(V, X.cpu.gpr.rdi) :=
    congrArg (ofBytesLE 64) (m5 (V := V) (g := X.cpu.gpr) (by omega) X.cpu.gpr.rdi 8 (by omega) (by omega))
  have hrip' : X.cpu.rip = usf_at.add 0 := by rw [addr_add_zero]; exact hrip
  -- the pushes, `cmp [rdi + 12], edx`, and on to 86 or 31
  refine (c_0 prof).run c hin (fun j' g' f' V' => V' = V5 V X.cpu.gpr ∧
      ((j' = 86 ∧ (tlm V X.cpu.gpr).toNat < (lnd X.cpu.gpr).toNat ∧ g' = g5 X.cpu.gpr ∧
         f'.cond 7 = decide (1073741822 < (lnd X.cpu.gpr).toNat)) ∨
       (j' = 31 ∧ ¬ (tlm V X.cpu.gpr).toNat < (lnd X.cpu.gpr).toNat ∧
         g' = gA X.cpu.gpr (rdq(V, X.cpu.gpr.rdi))))) hK hA hrip'
    (vc_0 hs1 (by rw [e16]; exact hs2) (by rw [e24]; exact hs3) (by rw [e32]; exact hs4) (by rw [e40]; exact hs5)
      hm0 hq0 fd12 fd0 (fun hc _ h7 => ⟨rfl, .inl ⟨rfl, hc, rfl, h7⟩⟩)
      (fun hc _ => ⟨rfl, .inr ⟨rfl, hc, rfl⟩⟩)) ?_
  rintro j' g fl V₁ ⟨hV₁, h⟩ Y t₁ hKY hAY hrY hgY hfY
  subst V₁
  rcases h with ⟨rfl, hc, rfl, h7⟩ | ⟨rfl, hc, rfl⟩
  · -- `_limit < len`: the `ja` to the throw stub
    refine c.s_jcc_x hKY hAY hin (lt_len (by decide)) hrY (ja_86 _) hinT (tgt := 0) hT tgt_86 ?_ ?_
    · intro hc7
      rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
      have h7' := hc7
      rw [hfY, h7] at h7'
      exact kt Y₂ t₂ hc (of_decide_eq_true h7') hK₂ hA₂ (by rw [hr₂, addr_add_zero]) (by rw [hg₂, hgY])
    intro hc7
    have h7' := hc7
    rw [hfY, h7] at h7'
    have hl6 : ¬ 1073741822 < (lnd X.cpu.gpr).toNat := of_decide_eq_false h7'
    have hnz : lnd X.cpu.gpr ≠ 0 := fun h0 => by rw [h0] at hc; simp at hc
    rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
    -- `new wchar_t[len + 1]`
    refine (c_92 prof).run c hin (fun j' g' _ V' => j' = 103 ∧ g' = gN X.cpu.gpr ∧ V' = V5 V X.cpu.gpr) hK₂ hA₂
      hr₂ (vc_92 (hg₂.trans hgY) fun _ => ⟨rfl, rfl, rfl⟩) ?_
    rintro j' g fl V₃ ⟨rfl, rfl, hV₃⟩ Y₃ t₃ hK₃ hA₃ hr₃ hg₃ -
    subst V₃
    have hsY : Y₃.cpu.gpr.rsp = X.cpu.gpr.rsp - 40 := by rw [hg₃]; exact e40
    have hst : ∀ i < 8, Foot Wl (Addr.add (Y₃.cpu.gpr.rsp - 8) i) := by rw [hsY, c48]; exact hs6
    refine c.s_call_x hK₃ hA₃ hin (lt_len (by decide)) hr₃ (call_103 _) hinN (tgt := 64)
      (Onw.lt_len (by decide)) tgt_103 hst ?_
    rintro Y₄ t₄ hK₄ hA₄ ⟨hr₄, hg₄⟩
    rw [hsY, c48] at hA₄
    refine kn Y₄ t₄ hc hl6 hK₄ hA₄ hr₄ (by rw [hg₄, hsY, c48, hg₃]) ?_
    -- back from `operator new`
    intro Zn V₁ t₅ hKn hAn hrn hns hnbp hnbx hPn
    refine (c_108 prof).run c hin (fun j' g' _ V' => V' = V₁ ∧
        g' = { Zn.cpu.gpr with rdi := rdq(V₁, X.cpu.gpr.rdi), r12 := Zn.cpu.gpr.rax } ∧
        ((j' = 125 ∧ rdq(V₁, X.cpu.gpr.rdi) = 0) ∨ (j' = 120 ∧ rdq(V₁, X.cpu.gpr.rdi) ≠ 0))) hKn hAn hrn
      (vc_108 hnbp fd0 (fun h0 _ => ⟨rfl, rfl, .inl ⟨rfl, h0⟩⟩) (fun h0 _ => ⟨rfl, rfl, .inr ⟨rfl, h0⟩⟩)) ?_
    rintro j' g fl V₂ ⟨hV₂, rfl, h⟩ U t₆ hKU hAU hrU hgU -
    subst V₂
    rcases h with ⟨rfl, h0⟩ | ⟨rfl, h0⟩
    · -- a null `_chars`: no `delete []`
      exact run125 U _ V₁ Zn.cpu.gpr.rax t₆ hKU hAU hrU hgU hns hnbp hnbx rfl hnz (km0 Zn V₁ hPn h0)
    · -- `delete [] _chars`
      have hsU : U.cpu.gpr.rsp = X.cpu.gpr.rsp - 40 := by rw [hgU]; exact hns
      have hst5 : ∀ i < 8, Foot Wl (Addr.add (U.cpu.gpr.rsp - 8) i) := by rw [hsU, c48]; exact hs6
      refine c.s_call hKU hAU hin (lt_len (by decide)) hrU (call_120 _) hinD hD (by decide) hst5 ?_
      rintro Y₅ t₇ hK₅ hA₅ ⟨hr₅, hg₅⟩
      rw [hsU, c48] at hA₅
      refine kd Zn V₁ hPn h0 Y₅ t₇ hK₅ hA₅ hr₅ (by rw [hg₅, hsU, c48, hgU]) ?_
      intro Zd V₃ t₈ hKd hAd hrd hds hdbp hdbx hd12 hPd
      exact run125 Zd Zd.cpu.gpr V₃ Zn.cpu.gpr.rax t₈ hKd hAd hrd rfl hds hdbp hdbx hd12 hnz (km1 Zn Zd V₃ hPd)
  · -- `_limit ≥ len`: the buffer as it is
    refine run31 Y _ (V5 V X.cpu.gpr) t₁ hKY hAY hrY hgY e40 rfl ?_ fun h0 => kmA h0 hc
    intro h0 U t₂ hKU hAU hrU hgU
    exact fin U _ (V5 V X.cpu.gpr) (rdq(V, X.cpu.gpr.rdi)) t₂ hKU hAU hrU hgU e40 rfl rfl rfl rfl
      (sv5 (by omega) hp8 hra) (hz4 h0) (kr0 h0)

end FV7z.Usf
