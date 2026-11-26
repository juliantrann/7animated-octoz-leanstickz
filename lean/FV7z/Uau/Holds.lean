import FV7z.Uau.Cuts
import FV7z.Onw
import FV7z.Wmc.Code
import FV7z.Wmc.Blocks
import FV7z.Lemmas.LeafRet
import FV7z.Lemmas.Lock2
import FV7z.Lemmas.FnFar
import FV7z.Tun.Inv
/-!
# `UString::operator= (const UString &s)` (PLAN.md §M, M1)

7-Zip 26.06's `UString::operator= (const UString &s)` at `0x44d710` in `7zzs` (`CPP/Common/MyString.cpp`), `this`
in `rdi`, `&s` in `rsi`: if `&s == this` (`je` at 20) straight to the epilogue; else `len = s._len` (the 4 bytes at
`&s + 8`), and if `len > _limit` (the 4 bytes at `this + 12`; `jb` at 31) `newBuf = new wchar_t[len + 1]` (`call` at
82 to `operator new`, `Onw.onw_at + 64`), `delete [] _chars` unless null (`call` at 99 to the thunk at `0x6014f0`),
`_chars = newBuf`, `_limit = len` (104), then `_len = len` and `wmemcpy (_chars, s._chars, len + 1)` (`call` at 50
to `Wmc.wmc_at`), and `return *this` (`ret` at 68). `push r13; push r12; push rbp; push rbx; sub rsp, 8`, `r12` =
`this`, `rbx` = `&s`, `rbp` = `len`, `r13` = `_chars` (or `newBuf`) across the calls.

The callees are hypotheses, as in `FV7z/Ur2/Holds.lean`: a continuation at each entry (`kn`, `kd`; `kmA`, `km0`,
`km1` for `wmemcpy` after each of the three ways to it, `Kc`), given the run from its return and the callee's own post
(`Pn`, `Pd`, `Pw`); `kself` and `kr` at the return address.

- `V0`, `g0`: the bytes and the registers after the pushes; `m0`, `sv0`: loads from `V0`.
- `sln`, `tlm`: `s._len` and `_limit`; `gN`, `gA`: the registers at the `call` of `operator new` and at 36 without it.
- `VB`: the bytes after `_chars = newBuf; _limit = len`; `VL`: after `_len = len`; `gM`: the registers at `wmemcpy`.
- `Sv`: the saved `rbx`, `rbp`, `r12`, `r13` and the return address in the bytes; `gR`: the registers at the return.
- `vc_0`, `vc_22`, `vc_36`, `vc_55`, `vc_87`, `vc_104`: the verification conditions of the pieces.
- `uau_ok`: from the entry, through the callees, to the return address.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Uau

/-- The `call`s to `wmemcpy`, `operator new` and the thunk of `operator delete []`. -/
def pcw : List Byte := [0xe8, 0xb9, 0xfb, 0x20, 0x00]
theorem pcw_0 : ∀ feat, Dec feat pcw 0 (FV7z.mk .call 64 [.rel 2161593] 5) := by dec_rfl
theorem wc_50 : pcw <+: uau.drop 50 := by decide +kernel
theorem call_50 (feat : Features) : Dec feat uau 50 (FV7z.mk .call 64 [.rel 2161593] 5) :=
  Dec.shift (j := 50) (k := 0) (pcw_0 feat) wc_50 (Nat.zero_le _)
theorem tgt_50 : uau_at.add (50 + 5) + BitVec.ofNat 64 2161593 = Wmc.wmc_at.add 0 := by decide
def pcn : List Byte := [0xe8, 0x49, 0x52, 0x1b, 0x00]
theorem pcn_0 : ∀ feat, Dec feat pcn 0 (FV7z.mk .call 64 [.rel 1790537] 5) := by dec_rfl
theorem wc_82 : pcn <+: uau.drop 82 := by decide +kernel
theorem call_82 (feat : Features) : Dec feat uau 82 (FV7z.mk .call 64 [.rel 1790537] 5) :=
  Dec.shift (j := 82) (k := 0) (pcn_0 feat) wc_82 (Nat.zero_le _)
theorem tgt_82 : uau_at.add (82 + 5) + BitVec.ofNat 64 1790537 = Onw.onw_at.add 64 := by decide
def pcd : List Byte := [0xe8, 0x78, 0x3d, 0x1b, 0x00]
theorem pcd_0 : ∀ feat, Dec feat pcd 0 (FV7z.mk .call 64 [.rel 1785208] 5) := by dec_rfl
theorem wc_99 : pcd <+: uau.drop 99 := by decide +kernel
theorem call_99 (feat : Features) : Dec feat uau 99 (FV7z.mk .call 64 [.rel 1785208] 5) :=
  Dec.shift (j := 99) (k := 0) (pcd_0 feat) wc_99 (Nat.zero_le _)

/-- The `ret`. -/
def pret : List Byte := [0xc3]
theorem pret_0 : ∀ feat, Dec feat pret 0 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem w_68 : pret <+: uau.drop 68 := by decide +kernel
theorem ret_68 (feat : Features) : Dec feat uau 68 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 68) (k := 0) (pret_0 feat) w_68 (Nat.zero_le _)

/-- A 32-bit value zero-extended. -/
abbrev zl (x : BitVec 32) : BitVec 64 := BitVec.setWidth 64 x

/-- `s._len` and `_limit` in the bytes `V` for the entry's registers `g`. -/
abbrev sln (V : Addr → Byte) (g : Gprs) : BitVec 32 := rdd(V, g.rsi + 8#64)
abbrev tlm (V : Addr → Byte) (g : Gprs) : BitVec 32 := rdd(V, g.rdi + 12#64)

/-- The bytes after the pushes of `r13`, `r12`, `rbp`, `rbx`. -/
abbrev V0 (V : Addr → Byte) (g : Gprs) : Addr → Byte :=
  Vst (Vst (Vst (Vst V (g.rsp - 8) (toBytesLE g.r13 8)) (g.rsp - 8 - 8) (toBytesLE g.r12 8))
    (g.rsp - 8 - 8 - 8) (toBytesLE g.rbp 8)) (g.rsp - 8 - 8 - 8 - 8) (toBytesLE g.rbx 8)

/-- The registers after `sub rsp, 8`: `r12` = `this`, 40 below the entry. -/
abbrev g0 (g : Gprs) : Gprs := { g with r12 := g.rdi, rsp := g.rsp - 8 - 8 - 8 - 8 - 8#64 }

/-- The registers at the `call` of `operator new`: `rbp` = `rax` = `len`, `rbx` = `&s`, `rdi` = `4 len + 4`. -/
abbrev gN (g : Gprs) (V : Addr → Byte) : Gprs :=
  { g0 g with rbp := zl (sln V g), rbx := g.rsi, rax := zl (sln V g),
              rdi := zl (sln V g) * 4#64 + 4#64 }

/-- The registers at 36 without `operator new`: `r13` = `_chars`. -/
abbrev gA (g : Gprs) (V : Addr → Byte) : Gprs :=
  { g0 g with rbp := zl (sln V g), rbx := g.rsi, r13 := rdq(V, g.rdi) }

/-- The bytes after `_chars = q; _limit = l` for the object at `p`. -/
abbrev VB (V : Addr → Byte) (p q : BitVec 64) (l : BitVec 32) : Addr → Byte :=
  Vst (Vst V p (toBytesLE q 8)) (p + 12#64) (toBytesLE l 4)

/-- The bytes after `_len = l` for the object at `p`. -/
abbrev VL (V : Addr → Byte) (p : BitVec 64) (l : BitVec 32) : Addr → Byte := Vst V (p + 8#64) (toBytesLE l 4)

/-- The registers at the `call` of `wmemcpy` for the bytes `V` at 36 and the registers `g` there: `rsi` =
`s._chars`, `edx` = `len + 1`, `rdi` = `r13`. -/
abbrev gM (V : Addr → Byte) (g : Gprs) (p s : BitVec 64) (l : BitVec 32) : Gprs :=
  { g with rsi := rdq(VL V p l, s), rdx := BitVec.setWidth 64 (BitVec.setWidth 32 (zl l + 1#64)), rdi := g.r13 }

/-- The registers at the return address from those `z` at 55 (`x` the entry's): `rax` = `this`, the saved ones
back. -/
abbrev gR (z x : Gprs) : Gprs :=
  { z with rax := x.rdi, rbx := x.rbx, rbp := x.rbp, r12 := x.r12, r13 := x.r13, rsp := x.rsp + 8 }

/-- The saved `rbx`, `rbp`, `r12`, `r13` (the entry's `x`) and the return address `r` in the bytes `V`. -/
abbrev Sv (V : Addr → Byte) (x : Gprs) (r : Addr) : Prop :=
  rdq(V, x.rsp - 32) = x.rbx ∧ rdq(V, x.rsp - 24) = x.rbp ∧ rdq(V, x.rsp - 16) = x.r12 ∧
    rdq(V, x.rsp - 8) = x.r13 ∧ rdq(V, x.rsp) = r

/-- A quad word apart from a store of one. -/
theorem rq_out (W : Addr → Byte) (a x : Addr) (v : BitVec 64) (ha : a.toNat + 8 ≤ 2 ^ 64)
    (hx : x.toNat + 8 ≤ 2 ^ 64) (h : a.toNat + 8 ≤ x.toNat ∨ x.toNat + 8 ≤ a.toNat) :
    rdq(Vst W a (toBytesLE v 8), x) = rdq(W, x) :=
  congrArg (ofBytesLE 64)
    (Tun.rd_Vst W a _ x 8 (by rw [toBytesLE_length]; exact ha) hx (by rw [toBytesLE_length]; exact h))

/-- A quad word read back from its store. -/
theorem rq_self (W : Addr → Byte) (a : Addr) (v : BitVec 64) (ha : a.toNat + 8 ≤ 2 ^ 64) :
    rdq(Vst W a (toBytesLE v 8), a) = v := by
  rw [Tun.rd_Vst_self (n := 8) _ a _ (toBytesLE_length _ _) ha]
  exact ofBytesLE_toBytesLE rfl _

/-- `n` bytes apart from the pushes are those before them. -/
theorem m0 {V : Addr → Byte} {g : Gprs} (hp : 32 ≤ g.rsp.toNat) (y : Addr) (n : Nat) (hy : y.toNat + n ≤ 2 ^ 64)
    (hd : y.toNat + n ≤ g.rsp.toNat - 32 ∨ g.rsp.toNat ≤ y.toNat) :
    List.map (V0 V g) (byteAddrs y n) = List.map V (byteAddrs y n) := by
  have hlt := g.rsp.isLt
  have t1 : (g.rsp - 8).toNat = g.rsp.toNat - 8 := by rw [BitVec.toNat_sub]; simp <;> omega
  have t2 : (g.rsp - 8 - 8).toNat = g.rsp.toNat - 16 := by rw [BitVec.toNat_sub, t1]; simp <;> omega
  have t3 : (g.rsp - 8 - 8 - 8).toNat = g.rsp.toNat - 24 := by rw [BitVec.toNat_sub, t2]; simp <;> omega
  have t4 : (g.rsp - 8 - 8 - 8 - 8).toNat = g.rsp.toNat - 32 := by rw [BitVec.toNat_sub, t3]; simp <;> omega
  have a1 := Tun.rd_Vst (Vst (Vst (Vst V (g.rsp - 8) (toBytesLE g.r13 8)) (g.rsp - 8 - 8) (toBytesLE g.r12 8))
    (g.rsp - 8 - 8 - 8) (toBytesLE g.rbp 8)) (g.rsp - 8 - 8 - 8 - 8) (toBytesLE g.rbx 8) y n
    (by rw [toBytesLE_length, t4]; omega) hy (by rw [toBytesLE_length, t4]; omega)
  have a2 := Tun.rd_Vst (Vst (Vst V (g.rsp - 8) (toBytesLE g.r13 8)) (g.rsp - 8 - 8) (toBytesLE g.r12 8))
    (g.rsp - 8 - 8 - 8) (toBytesLE g.rbp 8) y n (by rw [toBytesLE_length, t3]; omega) hy
    (by rw [toBytesLE_length, t3]; omega)
  have a3 := Tun.rd_Vst (Vst V (g.rsp - 8) (toBytesLE g.r13 8)) (g.rsp - 8 - 8) (toBytesLE g.r12 8) y n
    (by rw [toBytesLE_length, t2]; omega) hy (by rw [toBytesLE_length, t2]; omega)
  have a4 := Tun.rd_Vst V (g.rsp - 8) (toBytesLE g.r13 8) y n (by rw [toBytesLE_length, t1]; omega) hy
    (by rw [toBytesLE_length, t1]; omega)
  exact a1.trans (a2.trans (a3.trans a4))

/-- The saved registers and the return address in the bytes after the pushes. -/
theorem sv0 {V : Addr → Byte} {g : Gprs} {r : Addr} (hp : 40 ≤ g.rsp.toNat) (hp8 : g.rsp.toNat + 8 ≤ 2 ^ 64)
    (hr : rdq(V, g.rsp) = r) : Sv (V0 V g) g r := by
  have hlt := g.rsp.isLt
  have t1 : (g.rsp - 8).toNat = g.rsp.toNat - 8 := by rw [BitVec.toNat_sub]; simp <;> omega
  have t2 : (g.rsp - 8 - 8).toNat = g.rsp.toNat - 16 := by rw [BitVec.toNat_sub, t1]; simp <;> omega
  have t3 : (g.rsp - 8 - 8 - 8).toNat = g.rsp.toNat - 24 := by rw [BitVec.toNat_sub, t2]; simp <;> omega
  have t4 : (g.rsp - 8 - 8 - 8 - 8).toNat = g.rsp.toNat - 32 := by rw [BitVec.toNat_sub, t3]; simp <;> omega
  have f16 : g.rsp - 16 = g.rsp - 8 - 8 := by
    apply BitVec.eq_of_toNat_eq; rw [t2, BitVec.toNat_sub]; simp <;> omega
  have f24 : g.rsp - 24 = g.rsp - 8 - 8 - 8 := by
    apply BitVec.eq_of_toNat_eq; rw [t3, BitVec.toNat_sub]; simp <;> omega
  have f32 : g.rsp - 32 = g.rsp - 8 - 8 - 8 - 8 := by
    apply BitVec.eq_of_toNat_eq; rw [t4, BitVec.toNat_sub]; simp <;> omega
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [f32]
    exact rq_self _ _ _ (by rw [t4]; omega)
  · rw [f24]
    exact (rq_out _ (g.rsp - 8 - 8 - 8 - 8) (g.rsp - 8 - 8 - 8) _ (by rw [t4]; omega) (by rw [t3]; omega)
      (by rw [t4, t3]; omega)).trans (rq_self _ _ _ (by rw [t3]; omega))
  · rw [f16]
    exact (rq_out _ (g.rsp - 8 - 8 - 8 - 8) (g.rsp - 8 - 8) _ (by rw [t4]; omega) (by rw [t2]; omega)
      (by rw [t4, t2]; omega)).trans <|
      (rq_out _ (g.rsp - 8 - 8 - 8) (g.rsp - 8 - 8) _ (by rw [t3]; omega) (by rw [t2]; omega)
      (by rw [t3, t2]; omega)).trans (rq_self _ _ _ (by rw [t2]; omega))
  · exact (rq_out _ (g.rsp - 8 - 8 - 8 - 8) (g.rsp - 8) _ (by rw [t4]; omega) (by rw [t1]; omega)
      (by rw [t4, t1]; omega)).trans <|
      (rq_out _ (g.rsp - 8 - 8 - 8) (g.rsp - 8) _ (by rw [t3]; omega) (by rw [t1]; omega)
      (by rw [t3, t1]; omega)).trans <|
      (rq_out _ (g.rsp - 8 - 8) (g.rsp - 8) _ (by rw [t2]; omega) (by rw [t1]; omega)
      (by rw [t2, t1]; omega)).trans (rq_self _ _ _ (by rw [t1]; omega))
  · exact (congrArg (ofBytesLE 64) (m0 (V := V) (g := g) (by omega) g.rsp 8 hp8 (.inr (Nat.le_refl _)))).trans hr

variable {F : Footprint} {Wl : List Rgn}

/-- `push r13; push r12; mov r12, rdi; push rbp; push rbx; sub rsp, 8; cmp rsi, rdi` to the `je` at 20: to 55 if
`&s == this`, else on at 22. -/
theorem vc_0 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (hs1 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8) i)) (hs2 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8) i))
    (hs3 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8 - 8) i))
    (hs4 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8 - 8 - 8) i))
    (h55 : g.rsi = g.rdi → ∀ fl, Q 55 (g0 g) fl (V0 V g))
    (h22 : g.rsi ≠ g.rdi → ∀ fl, W_22 F Wl Q (g0 g) fl (V0 V g)) : W_0 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hs1 hs2 hs3 hs4 h55 h22 ⊢
  by_cases hq : rsi = rdi
  · have hb : decide (rsi = rdi) = true := decide_eq_true hq
    wpx [W_0, o0, hb, eq_self_iff_true, Bool.true_eq_false, Bool.false_eq_true, false_implies, implies_true]
    all_goals repeat' (first | exact h55 hq _ | assumption | exact trivial | apply And.intro | intro _)
  · have hb : decide (rsi = rdi) = false := decide_eq_false hq
    wpx [W_0, o0, hb, eq_self_iff_true, Bool.true_eq_false, Bool.false_eq_true, false_implies, implies_true]
    all_goals repeat' (first | exact h22 hq _ | assumption | exact trivial | apply And.intro | intro _)

/-- `mov ebp, [rsi + 8]; mov rbx, rsi; cmp [rdi + 12], ebp` to the `jb` at 31: if `_limit < len`, `mov eax, ebp;
lea rdi, [rax * 4 + 4]` to the `call` at 82, else `mov r13, [rdi]` to 36. -/
theorem vc_22 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} {l m : BitVec 32} {q : BitVec 64}
    (hl : rdd(V, g.rsi + 8#64) = l) (hm : rdd(V, g.rdi + 12#64) = m) (hq : rdq(V, g.rdi) = q)
    (fl8 : ∀ i < 4, Foot F.data (Addr.add (g.rsi + 8#64) i))
    (fl12 : ∀ i < 4, Foot F.data (Addr.add (g.rdi + 12#64) i)) (f0 : ∀ i < 8, Foot F.data (Addr.add g.rdi i))
    (h82 : m.toNat < l.toNat →
      ∀ fl, Q 82 { g with rbp := zl l, rbx := g.rsi, rax := zl l, rdi := zl l * 4#64 + 4#64 } fl V)
    (h36 : ¬ m.toNat < l.toNat → ∀ fl, Q 36 { g with rbp := zl l, rbx := g.rsi, r13 := q } fl V) :
    W_22 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hl hm hq fl8 fl12 f0 h82 h36 ⊢
  by_cases hc : m.toNat < l.toNat
  · have hb : decide (m.toNat < l.toNat) = true := decide_eq_true hc
    wpx [W_22, W_72, W_33, o1, o5, o2, Op.cmpmr, hl, hm, hq, hb, eq_self_iff_true, Bool.true_eq_false,
      Bool.false_eq_true, false_implies, implies_true]
    all_goals repeat' (first | exact h82 hc _ | assumption | exact trivial | apply And.intro | intro _)
  · have hb : decide (m.toNat < l.toNat) = false := decide_eq_false hc
    wpx [W_22, W_72, W_33, o1, o5, o2, Op.cmpmr, hl, hm, hq, hb, eq_self_iff_true, Bool.true_eq_false,
      Bool.false_eq_true, false_implies, implies_true]
    all_goals repeat' (first | exact h36 hc _ | assumption | exact trivial | apply And.intro | intro _)

/-- `mov [r12 + 8], ebp; mov rsi, [rbx]; lea edx, [rbp + 1]; mov rdi, r13` to the `call` at 50. -/
theorem vc_36 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} {p s : BitVec 64} {l : BitVec 32}
    (h12 : g.r12 = p) (hbx : g.rbx = s) (hbp : g.rbp = zl l) (w8 : ∀ i < 4, Foot Wl (Addr.add (p + 8#64) i))
    (fs : ∀ i < 8, Foot F.data (Addr.add s i)) (h : ∀ fl, Q 50 (gM V g p s l) fl (VL V p l)) :
    W_36 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h12 hbx hbp w8 fs h ⊢
  subst h12 hbx hbp
  wpx [W_36, o3]
  all_goals repeat' (first | exact h _ | assumption | exact trivial | apply And.intro | intro _)

/-- `add rsp, 8; mov rax, r12; pop rbx; pop rbp; pop r12; pop r13` to the `ret` at 68. -/
theorem vc_55 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (hl0 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8#64) i))
    (hl1 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8#64 + 8) i))
    (hl2 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8#64 + 8 + 8) i))
    (hl3 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8#64 + 8 + 8 + 8) i))
    (h : ∀ fl, Q 68
      { g with
          rax := g.r12,
          rbx := rdq(V, g.rsp + 8#64),
          rbp := rdq(V, g.rsp + 8#64 + 8),
          r12 := rdq(V, g.rsp + 8#64 + 8 + 8),
          r13 := rdq(V, g.rsp + 8#64 + 8 + 8 + 8),
          rsp := g.rsp + 8#64 + 8 + 8 + 8 + 8 } fl V) :
    W_55 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hl0 hl1 hl2 hl3 h ⊢
  wpx [W_55, o4]
  all_goals repeat' (first | exact h _ | assumption | exact trivial | apply And.intro | intro _)

/-- Back from `operator new`: `mov rdi, [r12]; mov r13, rax; test rdi, rdi; je 104`, else to the `call` at 99. -/
theorem vc_87 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} {p : Addr} (h12 : g.r12 = p)
    (f0 : ∀ i < 8, Foot F.data (Addr.add p i))
    (h104 : rdq(V, p) = 0 → ∀ fl, Q 104 { g with rdi := rdq(V, p), r13 := g.rax } fl V)
    (h99 : rdq(V, p) ≠ 0 → ∀ fl, Q 99 { g with rdi := rdq(V, p), r13 := g.rax } fl V) :
    W_87 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h12 f0 h104 h99 ⊢
  subst h12
  by_cases h1 : rdq(V, r12) = 0
  · have hb : (rdq(V, r12) == 0) = true := beq_iff_eq.2 h1
    wpx [W_87, o6, hb, BitVec.and_self, Bool.false_eq_true, Bool.true_eq_false, false_implies, implies_true]
    all_goals repeat' (first | exact h104 h1 _ | assumption | exact trivial | apply And.intro | intro _)
  · have hb : (rdq(V, r12) == 0) = false := beq_eq_false_iff_ne.2 h1
    wpx [W_87, o6, hb, BitVec.and_self, Bool.false_eq_true, Bool.true_eq_false, false_implies, implies_true]
    all_goals repeat' (first | exact h99 h1 _ | assumption | exact trivial | apply And.intro | intro _)

/-- `mov [r12], r13; mov [r12 + 12], ebp` and the jump to 36. -/
theorem vc_104 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} {p q : BitVec 64} {l : BitVec 32}
    (h12 : g.r12 = p) (h13 : g.r13 = q) (hbp : g.rbp = zl l) (w0 : ∀ i < 8, Foot Wl (Addr.add p i))
    (w12 : ∀ i < 4, Foot Wl (Addr.add (p + 12#64) i)) (h : ∀ fl, Q 36 g fl (VB V p q l)) :
    W_104 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h12 h13 hbp w0 w12 h ⊢
  subst h12 h13 hbp
  wpx [W_104, o7]
  all_goals repeat' (first | exact h _ | assumption | exact trivial | apply And.intro | intro _)

/-- At `wmemcpy`'s entry from 36 with the registers `g` and the bytes `W` there (`x` the entry's registers, `r`
the return address, `l` = `len`): the registers `gM`, `rsp` 48 below the entry's, the bytes `VL` with the return
address pushed; back at `uau_at + 55` with `rsp` 40 below the entry's, `r12` = `this`, the saved registers and the
return address (`Sv`) and `wmemcpy`'s post `Pw`. -/
def Kc (prof : Profile) (L : List (Addr × List Byte)) (o : Oracle) (gev : List Event)
    (gP : State → Nat → List Event → Prop) (gE : Outcome → List Event → Prop) (F : Footprint) (Wl : List Rgn)
    (s₀ : State) (x : Gprs) (r : Addr) (l : BitVec 32) (Pw : State → State → (Addr → Byte) → Prop) (g : Gprs)
    (W : Addr → Byte) : Prop :=
  ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y →
    Agree F Y.proc.mm.mem (Vst (VL W x.rdi l) (x.rsp - 48) (toBytesLE (uau_at.add 55) 8)) →
    Y.cpu.rip = Wmc.wmc_at → Y.cpu.gpr = (gM W g x.rdi x.rsi l).set 4 (x.rsp - 48) →
    (∀ (Zw : State) (V₂ : Addr → Byte) (t'' : Nat), KeptW Wl s₀ Zw → Agree F Zw.proc.mm.mem V₂ →
      Zw.cpu.rip = uau_at.add 55 → Zw.cpu.gpr.rsp = x.rsp - 40 → Zw.cpu.gpr.r12 = x.rdi → Sv V₂ x r →
      Pw Y Zw V₂ → GoG prof L o gev gP gE Zw t'') →
    GoG prof L o gev gP gE Y t'

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {X : State} {t : Nat} {V : Addr → Byte}

/-- `UString::operator= (const UString &s)` (`this` = `rdi`, `&s` = `rsi`) from its entry. If `&s == this`, at the
return address with `rax` = `this` and the bytes `V0` (`kself`). Else, if `_limit < len`, at `operator new`'s entry
with the registers `gN` (`kn`); back at `uau_at + 87` (`Pn`), at the thunk of `operator delete []` with `rdi` =
`_chars` unless null (`kd`), back at `uau_at + 104` (`Pd`); then, and also without `operator new`, at `wmemcpy`'s
entry (`kmA`, `km0`, `km1`: `Kc`) and back at `uau_at + 55` (`Pw`), at the return address with the registers `gR`
(`kr`). -/
theorem uau_ok {Pn : State → (Addr → Byte) → Prop} {Pd : State → State → (Addr → Byte) → Prop}
    {Pw : State → State → (Addr → Byte) → Prop}
    (c : Seg prof F Wl L s₀ o) (hin : CodeIn L uau_at uau) (hinN : CodeIn L Onw.onw_at Onw.onw)
    (hinW : CodeIn L Wmc.wmc_at Wmc.wmc) {codeD : List Byte} (hinD : CodeIn L 0x6014f0#64 codeD)
    (hD : 0 < codeD.length)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = uau_at)
    (hp : 48 ≤ X.cpu.gpr.rsp.toNat) (hp8 : X.cpu.gpr.rsp.toNat + 8 ≤ 2 ^ 64)
    (hs1 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8) i))
    (hs2 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 16) i))
    (hs3 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 24) i))
    (hs4 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 32) i))
    (hs6 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 48) i))
    (hl : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsp i))
    (fd0 : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rdi i))
    (fd12 : ∀ i < 4, Foot F.data (Addr.add (X.cpu.gpr.rdi + 12#64) i))
    (fw0 : ∀ i < 8, Foot Wl (Addr.add X.cpu.gpr.rdi i))
    (fw8 : ∀ i < 4, Foot Wl (Addr.add (X.cpu.gpr.rdi + 8#64) i))
    (fw12 : ∀ i < 4, Foot Wl (Addr.add (X.cpu.gpr.rdi + 12#64) i))
    (fs0 : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsi i))
    (fs8 : ∀ i < 4, Foot F.data (Addr.add (X.cpu.gpr.rsi + 8#64) i))
    (hqd : X.cpu.gpr.rdi.toNat + 16 ≤ 2 ^ 64) (hqs : X.cpu.gpr.rsi.toNat + 16 ≤ 2 ^ 64)
    (hdd : X.cpu.gpr.rdi.toNat + 16 ≤ X.cpu.gpr.rsp.toNat - 32 ∨ X.cpu.gpr.rsp.toNat ≤ X.cpu.gpr.rdi.toNat)
    (hds : X.cpu.gpr.rsi.toNat + 16 ≤ X.cpu.gpr.rsp.toNat - 32 ∨ X.cpu.gpr.rsp.toNat ≤ X.cpu.gpr.rsi.toNat)
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (hra : rdq(V, X.cpu.gpr.rsp) = e₂.add j₂)
    (kself : X.cpu.gpr.rsi = X.cpu.gpr.rdi → ∀ (Z' : State) (t' : Nat), KeptW Wl s₀ Z' →
      Agree F Z'.proc.mm.mem (V0 V X.cpu.gpr) → Z'.cpu.rip = e₂.add j₂ →
      Z'.cpu.gpr = { X.cpu.gpr with rax := X.cpu.gpr.rdi, rsp := X.cpu.gpr.rsp + 8 } →
      GoG prof L o gev gP gE Z' t')
    (kn : ∀ (Y : State) (t' : Nat), X.cpu.gpr.rsi ≠ X.cpu.gpr.rdi →
      (tlm V X.cpu.gpr).toNat < (sln V X.cpu.gpr).toNat → KeptW Wl s₀ Y →
      Agree F Y.proc.mm.mem (Vst (V0 V X.cpu.gpr) (X.cpu.gpr.rsp - 48) (toBytesLE (uau_at.add 87) 8)) →
      Y.cpu.rip = Onw.onw_at.add 64 → Y.cpu.gpr = (gN X.cpu.gpr V).set 4 (X.cpu.gpr.rsp - 48) →
      (∀ (Zn : State) (V₁ : Addr → Byte) (t'' : Nat), KeptW Wl s₀ Zn → Agree F Zn.proc.mm.mem V₁ →
        Zn.cpu.rip = uau_at.add 87 → Zn.cpu.gpr.rsp = X.cpu.gpr.rsp - 40 → Zn.cpu.gpr.r12 = X.cpu.gpr.rdi →
        Zn.cpu.gpr.rbx = X.cpu.gpr.rsi → Zn.cpu.gpr.rbp = zl (sln V X.cpu.gpr) → Pn Zn V₁ →
        GoG prof L o gev gP gE Zn t'') →
      GoG prof L o gev gP gE Y t')
    (kd : ∀ (Zn : State) (V₁ : Addr → Byte), Pn Zn V₁ → rdq(V₁, X.cpu.gpr.rdi) ≠ 0 →
      ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y →
      Agree F Y.proc.mm.mem (Vst V₁ (X.cpu.gpr.rsp - 48) (toBytesLE (uau_at.add 104) 8)) →
      Y.cpu.rip = 0x6014f0#64 →
      Y.cpu.gpr = { Zn.cpu.gpr with rdi := rdq(V₁, X.cpu.gpr.rdi), r13 := Zn.cpu.gpr.rax }.set 4
        (X.cpu.gpr.rsp - 48) →
      (∀ (Zd : State) (V₃ : Addr → Byte) (t'' : Nat), KeptW Wl s₀ Zd → Agree F Zd.proc.mm.mem V₃ →
        Zd.cpu.rip = uau_at.add 104 → Zd.cpu.gpr.rsp = X.cpu.gpr.rsp - 40 → Zd.cpu.gpr.r12 = X.cpu.gpr.rdi →
        Zd.cpu.gpr.rbx = X.cpu.gpr.rsi → Zd.cpu.gpr.rbp = zl (sln V X.cpu.gpr) →
        Zd.cpu.gpr.r13 = Zn.cpu.gpr.rax → Pd Zn Zd V₃ → GoG prof L o gev gP gE Zd t'') →
      GoG prof L o gev gP gE Y t')
    (kmA : X.cpu.gpr.rsi ≠ X.cpu.gpr.rdi → ¬ (tlm V X.cpu.gpr).toNat < (sln V X.cpu.gpr).toNat →
      Kc prof L o gev gP gE F Wl s₀ X.cpu.gpr (e₂.add j₂) (sln V X.cpu.gpr) Pw (gA X.cpu.gpr V) (V0 V X.cpu.gpr))
    (km0 : ∀ (Zn : State) (V₁ : Addr → Byte), Pn Zn V₁ → rdq(V₁, X.cpu.gpr.rdi) = 0 →
      Kc prof L o gev gP gE F Wl s₀ X.cpu.gpr (e₂.add j₂) (sln V X.cpu.gpr) Pw
        { Zn.cpu.gpr with rdi := rdq(V₁, X.cpu.gpr.rdi), r13 := Zn.cpu.gpr.rax }
        (VB V₁ X.cpu.gpr.rdi Zn.cpu.gpr.rax (sln V X.cpu.gpr)))
    (km1 : ∀ (Zn Zd : State) (V₃ : Addr → Byte), Pd Zn Zd V₃ →
      Kc prof L o gev gP gE F Wl s₀ X.cpu.gpr (e₂.add j₂) (sln V X.cpu.gpr) Pw Zd.cpu.gpr
        (VB V₃ X.cpu.gpr.rdi Zn.cpu.gpr.rax (sln V X.cpu.gpr)))
    (kr : ∀ (Y Zw : State) (V₂ : Addr → Byte) (Z' : State) (t' : Nat), Pw Y Zw V₂ → KeptW Wl s₀ Z' →
      Agree F Z'.proc.mm.mem V₂ → Z'.cpu.rip = e₂.add j₂ → Z'.cpu.gpr = gR Zw.cpu.gpr X.cpu.gpr →
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
  have e40 : X.cpu.gpr.rsp - 8 - 8 - 8 - 8 - 8#64 = X.cpu.gpr.rsp - 40 := by
    rw [e32]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, tn32, tn40]
    simp <;> omega
  have c48 : X.cpu.gpr.rsp - 40 - 8 = X.cpu.gpr.rsp - 48 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, tn40, tn48]
    simp <;> omega
  have a32 : X.cpu.gpr.rsp - 40 + 8#64 = X.cpu.gpr.rsp - 32 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, tn40, tn32]
    simp <;> omega
  have a24 : X.cpu.gpr.rsp - 32 + 8 = X.cpu.gpr.rsp - 24 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, tn32, tn24]
    simp <;> omega
  have a16 : X.cpu.gpr.rsp - 24 + 8 = X.cpu.gpr.rsp - 16 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, tn24, tn16]
    simp <;> omega
  have a8 : X.cpu.gpr.rsp - 16 + 8 = X.cpu.gpr.rsp - 8 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, tn16, tn8]
    simp <;> omega
  have e8 : X.cpu.gpr.rsp - 8 + 8 = X.cpu.gpr.rsp := BitVec.sub_add_cancel _ _
  have h32 : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rsp - 32) i) := fun i hi => c.hws _ (hs4 i hi)
  have h24 : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rsp - 24) i) := fun i hi => c.hws _ (hs3 i hi)
  have h16 : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rsp - 16) i) := fun i hi => c.hws _ (hs2 i hi)
  have h8 : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rsp - 8) i) := fun i hi => c.hws _ (hs1 i hi)
  -- from 55 to the return address
  have fin : ∀ (U : State) (W : Addr → Byte) (t' : Nat), KeptW Wl s₀ U → Agree F U.proc.mm.mem W →
      U.cpu.rip = uau_at.add 55 → U.cpu.gpr.rsp = X.cpu.gpr.rsp - 40 → U.cpu.gpr.r12 = X.cpu.gpr.rdi →
      Sv W X.cpu.gpr (e₂.add j₂) →
      (∀ (Z' : State) (t'' : Nat), KeptW Wl s₀ Z' → Agree F Z'.proc.mm.mem W → Z'.cpu.rip = e₂.add j₂ →
        Z'.cpu.gpr = gR U.cpu.gpr X.cpu.gpr → GoG prof L o gev gP gE Z' t'') →
      GoG prof L o gev gP gE U t' := by
    intro U W t' hKU hAU hrU hus hu12 hsv k
    obtain ⟨hb1, hb2, hb3, hb4, hb5⟩ := hsv
    refine (c_55 prof).run c hin (fun j' g' _ V' => j' = 68 ∧
        g' = { U.cpu.gpr with
            rax := X.cpu.gpr.rdi, rbx := X.cpu.gpr.rbx, rbp := X.cpu.gpr.rbp, r12 := X.cpu.gpr.r12,
            r13 := X.cpu.gpr.r13, rsp := X.cpu.gpr.rsp } ∧ V' = W) hKU hAU hrU
      (vc_55 (by rw [hus, a32]; exact h32) (by rw [hus, a32, a24]; exact h24)
        (by rw [hus, a32, a24, a16]; exact h16) (by rw [hus, a32, a24, a16, a8]; exact h8)
        fun _ => ⟨rfl, by rw [hus, a32, a24, a16, a8, e8, hu12, hb1, hb2, hb3, hb4], rfl⟩) ?_
    rintro j' g fl V₄ ⟨rfl, rfl, hV₄⟩ U' t₄ hKU' hAU' hrU' hgU' -
    subst V₄
    have hsU : U'.cpu.gpr.rsp = X.cpu.gpr.rsp := by rw [hgU']
    refine c.s_ret hKU' hAU' hin (lt_len (by decide)) hrU' (ret_68 _) (by rw [hsU]; exact hl) hin₂ h₂
      (by rw [hsU]; exact hb5) ?_
    rintro Z' t₅ hKZ' hAZ' ⟨hrZ', hgZ'⟩
    refine k Z' t₅ hKZ' hAZ' hrZ' ?_
    rw [hgZ', hgU']
    try rfl
  -- from 36 to `wmemcpy`, and back to the return address
  have run36 : ∀ (U : State) (g : Gprs) (W : Addr → Byte) (t' : Nat), KeptW Wl s₀ U →
      Agree F U.proc.mm.mem W → U.cpu.rip = uau_at.add 36 → U.cpu.gpr = g → g.rsp = X.cpu.gpr.rsp - 40 →
      g.r12 = X.cpu.gpr.rdi → g.rbx = X.cpu.gpr.rsi → g.rbp = zl (sln V X.cpu.gpr) →
      Kc prof L o gev gP gE F Wl s₀ X.cpu.gpr (e₂.add j₂) (sln V X.cpu.gpr) Pw g W →
      GoG prof L o gev gP gE U t' := by
    intro U g W t' hKU hAU hrU hgU hs h12 hbx hbp k
    subst hgU
    refine (c_36 prof).run c hin (fun j' g' _ V' => j' = 50 ∧
        g' = gM W U.cpu.gpr X.cpu.gpr.rdi X.cpu.gpr.rsi (sln V X.cpu.gpr) ∧
        V' = VL W X.cpu.gpr.rdi (sln V X.cpu.gpr)) hKU hAU hrU
      (vc_36 h12 hbx hbp fw8 fs0 fun _ => ⟨rfl, rfl, rfl⟩) ?_
    rintro j' g fl V₄ ⟨rfl, rfl, hV₄⟩ Y t₄ hKY hAY hrY hgY -
    subst V₄
    have hsY : Y.cpu.gpr.rsp = X.cpu.gpr.rsp - 40 := by rw [hgY]; exact hs
    have hst : ∀ i < 8, Foot Wl (Addr.add (Y.cpu.gpr.rsp - 8) i) := by rw [hsY, c48]; exact hs6
    refine c.s_call_x hKY hAY hin (lt_len (by decide)) hrY (call_50 _) hinW (tgt := 0) (Wmc.lt_len (by decide))
      tgt_50 hst ?_
    rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
    rw [hsY, c48] at hA₂
    refine k Y₂ t₂ hK₂ hA₂ (by rw [hr₂, addr_add_zero]) (by rw [hg₂, hsY, c48, hgY]) ?_
    intro Zw V₂ t₃ hKw hAw hrw hws hw12 hsv hPw
    exact fin Zw V₂ t₃ hKw hAw hrw hws hw12 hsv fun Z' t₄ hKZ hAZ hrZ hgZ => kr Y₂ Zw V₂ Z' t₄ hPw hKZ hAZ hrZ hgZ
  -- from 104 (`_chars = newBuf; _limit = len`) to 36
  have run104 : ∀ (U : State) (g : Gprs) (W : Addr → Byte) (q : BitVec 64) (t' : Nat), KeptW Wl s₀ U →
      Agree F U.proc.mm.mem W → U.cpu.rip = uau_at.add 104 → U.cpu.gpr = g → g.rsp = X.cpu.gpr.rsp - 40 →
      g.r12 = X.cpu.gpr.rdi → g.rbx = X.cpu.gpr.rsi → g.rbp = zl (sln V X.cpu.gpr) → g.r13 = q →
      Kc prof L o gev gP gE F Wl s₀ X.cpu.gpr (e₂.add j₂) (sln V X.cpu.gpr) Pw g
        (VB W X.cpu.gpr.rdi q (sln V X.cpu.gpr)) →
      GoG prof L o gev gP gE U t' := by
    intro U g W q t' hKU hAU hrU hgU hs h12 hbx hbp h13 k
    subst hgU
    refine (c_104 prof).run c hin (fun j' g' _ V' => j' = 36 ∧ g' = U.cpu.gpr ∧
        V' = VB W X.cpu.gpr.rdi q (sln V X.cpu.gpr)) hKU hAU hrU
      (vc_104 h12 h13 hbp fw0 fw12 fun _ => ⟨rfl, rfl, rfl⟩) ?_
    rintro j' g fl V₄ ⟨rfl, rfl, hV₄⟩ U' t₄ hKU' hAU' hrU' hgU' -
    subst V₄
    exact run36 U' U.cpu.gpr _ t₄ hKU' hAU' hrU' hgU' hs h12 hbx hbp k
  -- the loads before any store
  have ts8 : (X.cpu.gpr.rsi + 8#64).toNat = X.cpu.gpr.rsi.toNat + 8 := by
    rw [BitVec.toNat_add]; simp <;> omega
  have td12 : (X.cpu.gpr.rdi + 12#64).toNat = X.cpu.gpr.rdi.toNat + 12 := by
    rw [BitVec.toNat_add]; simp <;> omega
  have hl0 : rdd(V0 V X.cpu.gpr, X.cpu.gpr.rsi + 8#64) = sln V X.cpu.gpr :=
    congrArg (ofBytesLE 32) (m0 (V := V) (g := X.cpu.gpr) (by omega) (X.cpu.gpr.rsi + 8#64) 4
      (by rw [ts8]; omega) (by rw [ts8]; omega))
  have hm0 : rdd(V0 V X.cpu.gpr, X.cpu.gpr.rdi + 12#64) = tlm V X.cpu.gpr :=
    congrArg (ofBytesLE 32) (m0 (V := V) (g := X.cpu.gpr) (by omega) (X.cpu.gpr.rdi + 12#64) 4
      (by rw [td12]; omega) (by rw [td12]; omega))
  have hq0 : rdq(V0 V X.cpu.gpr, X.cpu.gpr.rdi) = rdq(V, X.cpu.gpr.rdi) :=
    congrArg (ofBytesLE 64) (m0 (V := V) (g := X.cpu.gpr) (by omega) X.cpu.gpr.rdi 8 (by omega) (by omega))
  have hrip' : X.cpu.rip = uau_at.add 0 := by rw [addr_add_zero]; exact hrip
  -- the pushes, `cmp rsi, rdi`, and on to 55, 82 or 36
  refine (c_0 prof).run c hin (fun j' g' _ V' => V' = V0 V X.cpu.gpr ∧
      ((j' = 55 ∧ X.cpu.gpr.rsi = X.cpu.gpr.rdi ∧ g' = g0 X.cpu.gpr) ∨
       (j' = 82 ∧ X.cpu.gpr.rsi ≠ X.cpu.gpr.rdi ∧ (tlm V X.cpu.gpr).toNat < (sln V X.cpu.gpr).toNat ∧
         g' = gN X.cpu.gpr V) ∨
       (j' = 36 ∧ X.cpu.gpr.rsi ≠ X.cpu.gpr.rdi ∧ ¬ (tlm V X.cpu.gpr).toNat < (sln V X.cpu.gpr).toNat ∧
         g' = gA X.cpu.gpr V))) hK hA hrip'
    (vc_0 hs1 (by rw [e16]; exact hs2) (by rw [e24]; exact hs3) (by rw [e32]; exact hs4)
      (fun he _ => ⟨rfl, .inl ⟨rfl, he, rfl⟩⟩)
      (fun hne _ => vc_22 hl0 hm0 hq0 fs8 fd12 fd0 (fun hc _ => ⟨rfl, .inr (.inl ⟨rfl, hne, hc, rfl⟩)⟩)
        (fun hc _ => ⟨rfl, .inr (.inr ⟨rfl, hne, hc, rfl⟩)⟩))) ?_
  rintro j' g fl V₁ ⟨hV₁, h⟩ Y t₁ hKY hAY hrY hgY -
  subst V₁
  rcases h with ⟨rfl, he, rfl⟩ | ⟨rfl, hne, hc, rfl⟩ | ⟨rfl, hne, hc, rfl⟩
  · -- `&s == this`
    have hsY : Y.cpu.gpr.rsp = X.cpu.gpr.rsp - 40 := by rw [hgY]; exact e40
    refine fin Y (V0 V X.cpu.gpr) t₁ hKY hAY hrY hsY (by rw [hgY]) (sv0 (by omega) hp8 hra) ?_
    intro Z' t₂ hKZ hAZ hrZ hgZ
    refine kself he Z' t₂ hKZ hAZ hrZ ?_
    rw [hgZ, hgY]
    try rfl
  · -- `new wchar_t[len + 1]`
    have hsY : Y.cpu.gpr.rsp = X.cpu.gpr.rsp - 40 := by rw [hgY]; exact e40
    have hst : ∀ i < 8, Foot Wl (Addr.add (Y.cpu.gpr.rsp - 8) i) := by rw [hsY, c48]; exact hs6
    refine c.s_call_x hKY hAY hin (lt_len (by decide)) hrY (call_82 _) hinN (tgt := 64) (Onw.lt_len (by decide))
      tgt_82 hst ?_
    rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
    rw [hsY, c48] at hA₂
    refine kn Y₂ t₂ hne hc hK₂ hA₂ hr₂ (by rw [hg₂, hsY, c48, hgY]) ?_
    -- back from `operator new`
    intro Zn V₁ t₃ hKn hAn hrn hns hn12 hnb hnp hPn
    refine (c_87 prof).run c hin (fun j' g' _ V' => V' = V₁ ∧
        g' = { Zn.cpu.gpr with rdi := rdq(V₁, X.cpu.gpr.rdi), r13 := Zn.cpu.gpr.rax } ∧
        ((j' = 104 ∧ rdq(V₁, X.cpu.gpr.rdi) = 0) ∨ (j' = 99 ∧ rdq(V₁, X.cpu.gpr.rdi) ≠ 0))) hKn hAn hrn
      (vc_87 hn12 fd0 (fun h0 _ => ⟨rfl, rfl, .inl ⟨rfl, h0⟩⟩) (fun h0 _ => ⟨rfl, rfl, .inr ⟨rfl, h0⟩⟩)) ?_
    rintro j' g fl V₂ ⟨hV₂, rfl, h⟩ U t₄ hKU hAU hrU hgU -
    subst V₂
    rcases h with ⟨rfl, h0⟩ | ⟨rfl, h0⟩
    · -- a null `_chars`: no `delete []`
      exact run104 U _ V₁ Zn.cpu.gpr.rax t₄ hKU hAU hrU hgU hns hn12 hnb hnp rfl (km0 Zn V₁ hPn h0)
    · -- `delete [] _chars`
      have hsU : U.cpu.gpr.rsp = X.cpu.gpr.rsp - 40 := by rw [hgU]; exact hns
      have hst5 : ∀ i < 8, Foot Wl (Addr.add (U.cpu.gpr.rsp - 8) i) := by rw [hsU, c48]; exact hs6
      refine c.s_call hKU hAU hin (lt_len (by decide)) hrU (call_99 _) hinD hD (by decide) hst5 ?_
      rintro Y₅ t₅ hK₅ hA₅ ⟨hr₅, hg₅⟩
      rw [hsU, c48] at hA₅
      refine kd Zn V₁ hPn h0 Y₅ t₅ hK₅ hA₅ hr₅ (by rw [hg₅, hsU, c48, hgU]) ?_
      intro Zd V₃ t₆ hKd hAd hrd hds' hd12 hdb hdp hd13 hPd
      exact run104 Zd Zd.cpu.gpr V₃ Zn.cpu.gpr.rax t₆ hKd hAd hrd rfl hds' hd12 hdb hdp hd13 (km1 Zn Zd V₃ hPd)
  · -- `_limit ≥ len`: the buffer as it is
    exact run36 Y (gA X.cpu.gpr V) (V0 V X.cpu.gpr) t₁ hKY hAY hrY hgY e40 rfl rfl rfl (kmA hne hc)

end FV7z.Uau
