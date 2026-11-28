import FV7z.Uac.Loop
/-!
# `UString::operator= (const char *)` (PLAN.md §M, M1)

7-Zip's `UString::operator= (const char *s)` at `0x44d8a0` in `7zzs` (`CPP/Common/MyString.cpp`): with `this` in `rdi`
and `s` in `rsi`, six pushes and `sub rsp, 8` (`rsp` 56 below the entry's), the length loop (`FV7z/Uac/Loop.lean`);
at a length `n` above `_limit` (the 4 bytes at `this + 12`) `operator new [] (4 n + 4)` (`call` at 141 to
`0x6029b0`), at 146 `delete [] _chars` (`call` at 157 to `0x6014f0`) unless null, at 162 `_chars` = the new buffer
and `_limit` = `n`; else (73) `r14` = `_chars`; then the copy loop at 80 (each byte widened to 4, `Uca.Cw`), at 101
`_chars[n] = 0`, `_len` = `n` (at `this + 8`), `rax` = `this`, the `pop`s and the `ret` at 130.

The callees are hypotheses (`kn`, `kd`), as in `FV7z/Aac/Holds.lean`: their posts give the frame and the buffer
writable and apart (`Pn`), and `P1`, `P2`.

- `Sv6`: the saved `rbx`, `rbp`, `r12` … `r15` and the return address; `Dst`: the buffer of `4 n + 4` bytes writable
  and apart from the frame; `Pn`: the post of a callee; `W2`: the bytes after `_chars` = `p`, `_limit` = `v`; `Rg`: the
  registers from the length loop on.
- `v0_out`, `m0`, `sv0`: the bytes after the pushes; `sv2`, `svF`: the frame through the stores to the object and at
  the end.
- `vc_101` (in two pieces, `pa` and `pb`), `vc_146`, `vc_162`: the pieces between the loops and the calls.
- `uac_ok`: from the entry, through the length loop, in place (`ki`) or through `operator new []` and `operator
  delete []` (`kz`, `kr`), the copy loop, to the return with `rax` = `this`.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn FV7z.Mys
namespace FV7z.Uac
open FV7z.Uca (Cw Mf rdMf)

/-! ## The calls and the `ret` -/

def pcn : List Byte := [0xe8, 0x7e, 0x50, 0x1b, 0x00]
theorem pcn_0 : ∀ feat, Dec feat pcn 0 (FV7z.mk .call 64 [.rel 1790078] 5) := by dec_rfl
theorem wc_141 : pcn <+: uac.drop 141 := by decide +kernel
theorem call_141 (feat : Features) : Dec feat uac 141 (FV7z.mk .call 64 [.rel 1790078] 5) :=
  Dec.shift (j := 141) (k := 0) (pcn_0 feat) wc_141 (Nat.zero_le _)
def pcd : List Byte := [0xe8, 0xae, 0x3b, 0x1b, 0x00]
theorem pcd_0 : ∀ feat, Dec feat pcd 0 (FV7z.mk .call 64 [.rel 1784750] 5) := by dec_rfl
theorem wc_157 : pcd <+: uac.drop 157 := by decide +kernel
theorem call_157 (feat : Features) : Dec feat uac 157 (FV7z.mk .call 64 [.rel 1784750] 5) :=
  Dec.shift (j := 157) (k := 0) (pcd_0 feat) wc_157 (Nat.zero_le _)

def pret : List Byte := [0xc3]
theorem pret_0 : ∀ feat, Dec feat pret 0 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem w_130 : pret <+: uac.drop 130 := by decide +kernel
theorem ret_130 (feat : Features) : Dec feat uac 130 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 130) (k := 0) (pret_0 feat) w_130 (Nat.zero_le _)

/-! ## Addresses: one small `bv_omega` lemma each (never in a big context) -/

theorem e16 (s : BitVec 64) : s - 8 - 8 = s - 16 := by bv_omega
theorem e24 (s : BitVec 64) : s - 8 - 8 - 8 = s - 24 := by bv_omega
theorem e32 (s : BitVec 64) : s - 8 - 8 - 8 - 8 = s - 32 := by bv_omega
theorem e40 (s : BitVec 64) : s - 8 - 8 - 8 - 8 - 8 = s - 40 := by bv_omega
theorem e48 (s : BitVec 64) : s - 8 - 8 - 8 - 8 - 8 - 8 = s - 48 := by bv_omega
theorem e56 (s : BitVec 64) : s - 8 - 8 - 8 - 8 - 8 - 8 - 8 = s - 56 := by bv_omega
theorem e64 (s : BitVec 64) : s - 56 - 8 = s - 64 := by bv_omega
theorem q48 (s : BitVec 64) : s - 56 + 8#64 = s - 48 := by bv_omega
theorem q40 (s : BitVec 64) : s - 48 + 8 = s - 40 := by bv_omega
theorem q32 (s : BitVec 64) : s - 40 + 8 = s - 32 := by bv_omega
theorem q24 (s : BitVec 64) : s - 32 + 8 = s - 24 := by bv_omega
theorem q16 (s : BitVec 64) : s - 24 + 8 = s - 16 := by bv_omega
theorem q8 (s : BitVec 64) : s - 16 + 8 = s - 8 := by bv_omega
theorem q0 (s : BitVec 64) : s - 8 + 8 = s := by bv_omega
theorem t8 (s : BitVec 64) (h : 64 ≤ s.toNat) : (s - 8).toNat = s.toNat - 8 := by bv_omega
theorem t16 (s : BitVec 64) (h : 64 ≤ s.toNat) : (s - 16).toNat = s.toNat - 16 := by bv_omega
theorem t24 (s : BitVec 64) (h : 64 ≤ s.toNat) : (s - 24).toNat = s.toNat - 24 := by bv_omega
theorem t32 (s : BitVec 64) (h : 64 ≤ s.toNat) : (s - 32).toNat = s.toNat - 32 := by bv_omega
theorem t40 (s : BitVec 64) (h : 64 ≤ s.toNat) : (s - 40).toNat = s.toNat - 40 := by bv_omega
theorem t48 (s : BitVec 64) (h : 64 ≤ s.toNat) : (s - 48).toNat = s.toNat - 48 := by bv_omega
theorem ta8 (a : BitVec 64) (h : a.toNat + 16 ≤ 2 ^ 64) : (a + 8#64).toNat = a.toNat + 8 := by bv_omega
theorem ta12 (a : BitVec 64) (h : a.toNat + 16 ≤ 2 ^ 64) : (a + 12#64).toNat = a.toNat + 12 := by bv_omega

/-- `_len` = `n`, as 4 bytes. -/
theorem sw32 {n : Nat} (hn : n < 2 ^ 32) : BitVec.setWidth 32 (BitVec.ofNat 64 n) = BitVec.ofNat 32 n := by
  apply BitVec.eq_of_toNat_eq
  simp <;> omega

/-! ## The frame -/

/-- The saved `rbx`, `rbp`, `r12`, `r13`, `r14`, `r15` (the entry's `x`) and the return address `r` in the bytes
`V`. -/
abbrev Sv6 (V : Addr → Byte) (x : Gprs) (r : Addr) : Prop :=
  rdq(V, x.rsp - 48) = x.rbx ∧ rdq(V, x.rsp - 40) = x.rbp ∧ rdq(V, x.rsp - 32) = x.r12 ∧
    rdq(V, x.rsp - 24) = x.r13 ∧ rdq(V, x.rsp - 16) = x.r14 ∧ rdq(V, x.rsp - 8) = x.r15 ∧ rdq(V, x.rsp) = r

/-- The bytes after `_chars` = `p` and `_limit` = `v` for the object at `b`. -/
abbrev W2 (V : Addr → Byte) (b : Addr) (p : BitVec 64) (v : BitVec 32) : Addr → Byte :=
  Vst (Vst V b (toBytesLE p 8)) (b + 12#64) (toBytesLE v 4)

/-- The `4 n + 4` bytes at `d` writable and clear of the saved registers and the return address (`x` the entry's). -/
abbrev Dst (Wl : List Rgn) (x : Gprs) (n : Nat) (d : Addr) : Prop :=
  (∀ i < 4 * n + 4, Foot Wl (Addr.add d i)) ∧ d.toNat + (4 * n + 4) ≤ 2 ^ 64 ∧
    (d.toNat + (4 * n + 4) ≤ x.rsp.toNat - 48 ∨ x.rsp.toNat + 8 ≤ d.toNat)

/-- The post of a callee, for the entry's registers `x`: the frame as it was, the buffer `d` as `Dst`. -/
abbrev Pn (Wl : List Rgn) (x : Gprs) (n : Nat) (r d : Addr) (V' : Addr → Byte) : Prop :=
  Sv6 V' x r ∧ Dst Wl x n d

/-- The registers from the length loop on, for the length `n` (`x` the entry's). -/
def Rg (x : Gprs) (n : Nat) (g : Gprs) : Prop :=
  g.rsp = x.rsp - 56 ∧ g.rbp = x.rsi ∧ g.r15 = x.rdi ∧ g.rbx = BitVec.ofNat 64 n ∧
    g.r13 = BitVec.ofNat 64 (n - 1) ∧ g.r12 = BitVec.ofNat 64 (4 * n)

theorem rgE {x g : Gprs} {n : Nat} (h : Ex (gS x) n g) : Rg x n g := ⟨by rw [h.1]; exact e56 _, h.2⟩

/-- The registers whose pushes at the five upper slots are those of `Usf.V5`. -/
abbrev gW (g : Gprs) : Gprs := { g with r14 := g.r15, r13 := g.r14, r12 := g.r13, rbp := g.r12, rbx := g.rbp }

/-- A byte apart from the pushes is as before them. -/
theorem v0_out {V : Addr → Byte} {g : Gprs} (hp : 64 ≤ g.rsp.toNat) (y : Addr)
    (hy : y.toNat < g.rsp.toNat - 48 ∨ g.rsp.toNat ≤ y.toNat) : V0 V g y = V y := by
  have hlt := g.rsp.isLt
  have k8 := t8 _ hp
  have k16 := t16 _ hp
  have k24 := t24 _ hp
  have k32 := t32 _ hp
  have k40 := t40 _ hp
  have k48 := t48 _ hp
  dsimp only [V0]
  rw [e48, e40, e32, e24, e16,
    Tun.Vst_out _ (g.rsp - 48) (toBytesLE g.rbx 8) y (by rw [toBytesLE_length, k48]; omega)
      (by rw [toBytesLE_length, k48]; omega),
    Tun.Vst_out _ (g.rsp - 40) (toBytesLE g.rbp 8) y (by rw [toBytesLE_length, k40]; omega)
      (by rw [toBytesLE_length, k40]; omega),
    Tun.Vst_out _ (g.rsp - 32) (toBytesLE g.r12 8) y (by rw [toBytesLE_length, k32]; omega)
      (by rw [toBytesLE_length, k32]; omega),
    Tun.Vst_out _ (g.rsp - 24) (toBytesLE g.r13 8) y (by rw [toBytesLE_length, k24]; omega)
      (by rw [toBytesLE_length, k24]; omega),
    Tun.Vst_out _ (g.rsp - 16) (toBytesLE g.r14 8) y (by rw [toBytesLE_length, k16]; omega)
      (by rw [toBytesLE_length, k16]; omega),
    Tun.Vst_out _ (g.rsp - 8) (toBytesLE g.r15 8) y (by rw [toBytesLE_length, k8]; omega)
      (by rw [toBytesLE_length, k8]; omega)]

/-- `n` bytes apart from the pushes are those before them. -/
theorem m0 {V : Addr → Byte} {g : Gprs} (hp : 64 ≤ g.rsp.toNat) (y : Addr) (n : Nat) (hy : y.toNat + n ≤ 2 ^ 64)
    (hd : y.toNat + n ≤ g.rsp.toNat - 48 ∨ g.rsp.toNat ≤ y.toNat) :
    List.map (V0 V g) (byteAddrs y n) = List.map V (byteAddrs y n) := by
  have k : (g.rsp - 8 - 8 - 8 - 8 - 8 - 8).toNat = g.rsp.toNat - 48 := by rw [e48]; exact t48 _ hp
  have a1 := Tun.rd_Vst (Usf.V5 V (gW g)) (g.rsp - 8 - 8 - 8 - 8 - 8 - 8) (toBytesLE g.rbx 8) y n
    (by rw [toBytesLE_length, k]; omega) hy (by rw [toBytesLE_length, k]; omega)
  have a2 := Usf.m5 (V := V) (g := gW g) (by show 40 ≤ g.rsp.toNat; omega) y n hy
    (by show y.toNat + n ≤ g.rsp.toNat - 40 ∨ g.rsp.toNat ≤ y.toNat; omega)
  exact a1.trans a2

/-- The saved registers and the return address in the bytes after the pushes. -/
theorem sv0 {V : Addr → Byte} {g : Gprs} {r : Addr} (hp : 64 ≤ g.rsp.toNat) (hp8 : g.rsp.toNat + 8 ≤ 2 ^ 64)
    (hr : rdq(V, g.rsp) = r) : Sv6 (V0 V g) g r := by
  have hlt := g.rsp.isLt
  obtain ⟨b1, b2, b3, b4, b5, b6⟩ :=
    Usf.sv5 (V := V) (g := gW g) (r := r) (by show 40 ≤ g.rsp.toNat; omega) hp8 hr
  have k8 := t8 _ hp
  have k16 := t16 _ hp
  have k24 := t24 _ hp
  have k32 := t32 _ hp
  have k40 := t40 _ hp
  have k : (g.rsp - 8 - 8 - 8 - 8 - 8 - 8).toNat = g.rsp.toNat - 48 := by rw [e48]; exact t48 _ hp
  have o : ∀ x : Addr, x.toNat + 8 ≤ 2 ^ 64 → g.rsp.toNat - 40 ≤ x.toNat →
      rdq(V0 V g, x) = rdq(Usf.V5 V (gW g), x) := fun x hx h =>
    Uau.rq_out _ (g.rsp - 8 - 8 - 8 - 8 - 8 - 8) x _ (by rw [k]; omega) hx (by rw [k]; omega)
  refine ⟨?_, (o (g.rsp - 40) (by rw [k40]; omega) (by rw [k40]; omega)).trans b1,
    (o (g.rsp - 32) (by rw [k32]; omega) (by rw [k32]; omega)).trans b2,
    (o (g.rsp - 24) (by rw [k24]; omega) (by rw [k24]; omega)).trans b3,
    (o (g.rsp - 16) (by rw [k16]; omega) (by rw [k16]; omega)).trans b4,
    (o (g.rsp - 8) (by rw [k8]; omega) (by rw [k8]; omega)).trans b5, (o g.rsp hp8 (by omega)).trans b6⟩
  rw [← e48 g.rsp]
  exact Uau.rq_self _ _ _ (by rw [k]; omega)

/-- The frame through the stores of `_chars` and `_limit` to the object at `b`, apart from it. -/
theorem sv2 {M : Addr → Byte} {x : Gprs} {r b : Addr} (p : BitVec 64) (v : BitVec 32) (hp : 64 ≤ x.rsp.toNat)
    (hp8 : x.rsp.toNat + 8 ≤ 2 ^ 64) (hq : b.toNat + 16 ≤ 2 ^ 64)
    (hb : b.toNat + 16 ≤ x.rsp.toNat - 64 ∨ x.rsp.toNat + 8 ≤ b.toNat) (h : Sv6 M x r) :
    Sv6 (W2 M b p v) x r := by
  have hlt := x.rsp.isLt
  have k12 := ta12 _ hq
  have key : ∀ a : Addr, a.toNat + 8 ≤ 2 ^ 64 → x.rsp.toNat - 48 ≤ a.toNat → a.toNat ≤ x.rsp.toNat →
      rdq(W2 M b p v, a) = rdq(M, a) := fun a ha h1 h2 =>
    congrArg (ofBytesLE 64) ((Tun.rd_Vst (Vst M b (toBytesLE p 8)) (b + 12#64) (toBytesLE v 4) a 8
      (by rw [toBytesLE_length, k12]; omega) ha (by rw [toBytesLE_length, k12]; omega)).trans
      (Tun.rd_Vst M b (toBytesLE p 8) a 8 (by rw [toBytesLE_length]; omega) ha (by rw [toBytesLE_length]; omega)))
  obtain ⟨a1, a2, a3, a4, a5, a6, a7⟩ := h
  have k8 := t8 _ hp
  have k16 := t16 _ hp
  have k24 := t24 _ hp
  have k32 := t32 _ hp
  have k40 := t40 _ hp
  have k48 := t48 _ hp
  exact ⟨(key (x.rsp - 48) (by rw [k48]; omega) (by rw [k48]; omega) (by rw [k48]; omega)).trans a1,
    (key (x.rsp - 40) (by rw [k40]; omega) (by rw [k40]; omega) (by rw [k40]; omega)).trans a2,
    (key (x.rsp - 32) (by rw [k32]; omega) (by rw [k32]; omega) (by rw [k32]; omega)).trans a3,
    (key (x.rsp - 24) (by rw [k24]; omega) (by rw [k24]; omega) (by rw [k24]; omega)).trans a4,
    (key (x.rsp - 16) (by rw [k16]; omega) (by rw [k16]; omega) (by rw [k16]; omega)).trans a5,
    (key (x.rsp - 8) (by rw [k8]; omega) (by rw [k8]; omega) (by rw [k8]; omega)).trans a6,
    (key x.rsp hp8 (by omega) (Nat.le_refl _)).trans a7⟩

/-- The frame at the end: through the copy, `_chars[n] = 0` and `_len` (at `b + 8`). -/
theorem svF {M : Addr → Byte} {x : Gprs} {r s d b : Addr} {n : Nat} {v : BitVec 32} (hp : 64 ≤ x.rsp.toNat)
    (hp8 : x.rsp.toNat + 8 ≤ 2 ^ 64) (hq : b.toNat + 16 ≤ 2 ^ 64)
    (hb : b.toNat + 16 ≤ x.rsp.toNat - 64 ∨ x.rsp.toNat + 8 ≤ b.toNat) (hdw : d.toNat + (4 * n + 4) ≤ 2 ^ 64)
    (hda : d.toNat + (4 * n + 4) ≤ x.rsp.toNat - 48 ∨ x.rsp.toNat + 8 ≤ d.toNat) (h : Sv6 M x r) :
    Sv6 (Vst (Mf M s d n) (b + 8#64) (toBytesLE v 4)) x r := by
  have hlt := x.rsp.isLt
  have k8' := ta8 _ hq
  have key : ∀ a : Addr, a.toNat + 8 ≤ 2 ^ 64 → x.rsp.toNat - 48 ≤ a.toNat → a.toNat ≤ x.rsp.toNat →
      rdq(Vst (Mf M s d n) (b + 8#64) (toBytesLE v 4), a) = rdq(M, a) := fun a ha h1 h2 =>
    (congrArg (ofBytesLE 64) (Tun.rd_Vst (Mf M s d n) (b + 8#64) (toBytesLE v 4) a 8
      (by rw [toBytesLE_length, k8']; omega) ha (by rw [toBytesLE_length, k8']; omega))).trans
      (rdMf M s d n a ha hdw (by omega))
  obtain ⟨a1, a2, a3, a4, a5, a6, a7⟩ := h
  have k8 := t8 _ hp
  have k16 := t16 _ hp
  have k24 := t24 _ hp
  have k32 := t32 _ hp
  have k40 := t40 _ hp
  have k48 := t48 _ hp
  exact ⟨(key (x.rsp - 48) (by rw [k48]; omega) (by rw [k48]; omega) (by rw [k48]; omega)).trans a1,
    (key (x.rsp - 40) (by rw [k40]; omega) (by rw [k40]; omega) (by rw [k40]; omega)).trans a2,
    (key (x.rsp - 32) (by rw [k32]; omega) (by rw [k32]; omega) (by rw [k32]; omega)).trans a3,
    (key (x.rsp - 24) (by rw [k24]; omega) (by rw [k24]; omega) (by rw [k24]; omega)).trans a4,
    (key (x.rsp - 16) (by rw [k16]; omega) (by rw [k16]; omega) (by rw [k16]; omega)).trans a5,
    (key (x.rsp - 8) (by rw [k8]; omega) (by rw [k8]; omega) (by rw [k8]; omega)).trans a6,
    (key x.rsp hp8 (by omega) (Nat.le_refl _)).trans a7⟩

/-! ## The conditions -/

/-- The effects at 101 in two pieces: the stores and `add rsp, 8`; the six `pop`s. -/
def o8a : List Op :=
  [Op.sti 32 (some 14) (some 12) 1 0 0, Op.mov 64 0 (.r 15), Op.st 32 (some 15) none 1 8 3, Op.add 64 4 (.i 8)]
def o8b : List Op := [Op.pop 3, Op.pop 5, Op.pop 12, Op.pop 13, Op.pop 14, Op.pop 15]
theorem o8_eq : o8 = o8a ++ o8b := rfl

variable {F : Footprint} {Wl : List Rgn}

/-- `mov dword [r14 + r12], 0; mov rax, r15; mov [r15 + 8], ebx; add rsp, 8`. -/
theorem pa (g : Gprs) (f : Rflags) (V : Addr → Byte) (hw : ∀ i < 4, Foot Wl (Addr.add (g.r14 + g.r12) i))
    (hw8 : ∀ i < 4, Foot Wl (Addr.add (g.r15 + 8#64) i)) :
    wp F Wl o8a (fun g' _ V' => g' = { g with rax := g.r15, rsp := g.rsp + 8#64 } ∧
      V' = Vst (Vst V (g.r14 + g.r12) (toBytesLE 0#32 4)) (g.r15 + 8#64)
        (toBytesLE (BitVec.setWidth 32 g.rbx) 4)) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hw hw8 ⊢
  wpx [o8a]
  all_goals repeat' (first | exact rfl | assumption | exact trivial | apply And.intro | intro _)

/-- `pop rbx; pop rbp; pop r12; pop r13; pop r14; pop r15`. -/
theorem pb (g : Gprs) (f : Rflags) (V : Addr → Byte) (l0 : ∀ i < 8, Foot F.data (Addr.add g.rsp i))
    (l1 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8) i)) (l2 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8 + 8) i))
    (l3 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8 + 8 + 8) i))
    (l4 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8 + 8 + 8 + 8) i))
    (l5 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8 + 8 + 8 + 8 + 8) i)) :
    wp F Wl o8b (fun g' _ V' => g' = { g with
        rbx := rdq(V, g.rsp), rbp := rdq(V, g.rsp + 8),
        r12 := rdq(V, g.rsp + 8 + 8), r13 := rdq(V, g.rsp + 8 + 8 + 8), r14 := rdq(V, g.rsp + 8 + 8 + 8 + 8),
        r15 := rdq(V, g.rsp + 8 + 8 + 8 + 8 + 8), rsp := g.rsp + 8 + 8 + 8 + 8 + 8 + 8 } ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at l0 l1 l2 l3 l4 l5 ⊢
  wpx [o8b]
  all_goals repeat' (first | exact rfl | assumption | exact trivial | apply And.intro | intro _)

/-- From 101 to the `ret` at 130, the bytes after the stores `Mo`. -/
theorem vc_101 {g : Gprs} {f : Rflags} {V Mo : Addr → Byte}
    (hM : Vst (Vst V (g.r14 + g.r12) (toBytesLE 0#32 4)) (g.r15 + 8#64) (toBytesLE (BitVec.setWidth 32 g.rbx) 4) =
      Mo)
    (hw : ∀ i < 4, Foot Wl (Addr.add (g.r14 + g.r12) i)) (hw8 : ∀ i < 4, Foot Wl (Addr.add (g.r15 + 8#64) i))
    (l0 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8#64) i))
    (l1 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8#64 + 8) i))
    (l2 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8#64 + 8 + 8) i))
    (l3 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8#64 + 8 + 8 + 8) i))
    (l4 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8#64 + 8 + 8 + 8 + 8) i))
    (l5 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8#64 + 8 + 8 + 8 + 8 + 8) i)) :
    W_101 F Wl (fun j' g' _ V' => j' = 130 ∧ g' = { g with
        rax := g.r15, rbx := rdq(Mo, g.rsp + 8#64),
        rbp := rdq(Mo, g.rsp + 8#64 + 8), r12 := rdq(Mo, g.rsp + 8#64 + 8 + 8),
        r13 := rdq(Mo, g.rsp + 8#64 + 8 + 8 + 8), r14 := rdq(Mo, g.rsp + 8#64 + 8 + 8 + 8 + 8),
        r15 := rdq(Mo, g.rsp + 8#64 + 8 + 8 + 8 + 8 + 8), rsp := g.rsp + 8#64 + 8 + 8 + 8 + 8 + 8 + 8 } ∧
      V' = Mo) g f V := by
  subst hM
  unfold W_101
  rw [o8_eq]
  refine wp_append _ _ (wp_mono o8a ?_ (pa g f V hw hw8))
  rintro g₁ f₁ V₁ ⟨rfl, rfl⟩
  refine wp_mono o8b ?_ (pb { g with rax := g.r15, rsp := g.rsp + 8#64 } f₁ _ l0 l1 l2 l3 l4 l5)
  rintro g₂ f₂ V₂ ⟨rfl, rfl⟩
  exact ⟨rfl, rfl, rfl⟩

/-- Back from `operator new []`: `mov rdi, [r15]; mov r14, rax; test rdi, rdi; je 162`, else to the `call` at 157. -/
theorem vc_146 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (f0 : ∀ i < 8, Foot F.data (Addr.add g.r15 i))
    (h162 : rdq(V, g.r15) = 0 → ∀ fl, Q 162 { g with rdi := rdq(V, g.r15), r14 := g.rax } fl V)
    (h157 : rdq(V, g.r15) ≠ 0 → ∀ fl, Q 157 { g with rdi := rdq(V, g.r15), r14 := g.rax } fl V) :
    W_146 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at f0 h162 h157 ⊢
  by_cases h0 : rdq(V, r15) = 0
  · have hb : (rdq(V, r15) == 0) = true := beq_iff_eq.2 h0
    wpx [W_146, o10, hb, BitVec.and_self, Bool.false_eq_true, Bool.true_eq_false, false_implies, implies_true]
    all_goals repeat' (first | exact h162 h0 _ | assumption | exact trivial | apply And.intro | intro _)
  · have hb : (rdq(V, r15) == 0) = false := beq_eq_false_iff_ne.2 h0
    wpx [W_146, o10, hb, BitVec.and_self, Bool.false_eq_true, Bool.true_eq_false, false_implies, implies_true]
    all_goals repeat' (first | exact h157 h0 _ | assumption | exact trivial | apply And.intro | intro _)

/-- `mov [r15], r14; mov [r15 + 12], ebx`, to 73. -/
theorem vc_162 {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (hw0 : ∀ i < 8, Foot Wl (Addr.add g.r15 i)) (hw12 : ∀ i < 4, Foot Wl (Addr.add (g.r15 + 12#64) i)) :
    W_162 F Wl (fun j' g' _ V' => j' = 73 ∧ g' = g ∧ V' = W2 V g.r15 g.r14 (BitVec.setWidth 32 g.rbx)) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hw0 hw12 ⊢
  wpx [W_162, o11]
  all_goals repeat' (first | exact rfl | assumption | exact trivial | apply And.intro | intro _)

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {X : State} {t : Nat} {V : Addr → Byte}

/-- `UString::operator= (const char *s)` (`this` = `rdi`, `s` = `rsi`) from its entry, for `s` with `n` bytes not 0
and a 0, apart from the frame. With `n` = 0 or `_limit` not below `n` the bytes go in place into `_chars` (`Dst` by
`hbi`), and the run returns (`ki`). Else at `operator new []`'s entry (`kn`, for any registers as `Rg`, `rdi` =
`4 n + 4`), back at 146 with the buffer `rax` (`Pn`, `P1`); with `_chars` null on to the return (`kz`); else at
`operator delete []`'s entry (`kd`) and back at 162 (`Pn`, `P2`), then on to the return (`kr`). At the return the
registers a call keeps are as at the entry, `rax` = `this`, and the bytes are `_chars`, `_limit` as stored (`W2`), the
string copied, each byte as 4 (`Uca.Cw`), the 4 bytes 0 after it (`Uca.Mf`) and `_len` = `n`. -/
theorem uac_ok {P1 P2 : State → (Addr → Byte) → Prop} {n : Nat} (c : Seg prof F Wl L s₀ o)
    (hin : CodeIn L uac_at uac) {codeN codeD : List Byte}
    (hinN : CodeIn L 0x6029b0#64 codeN) (hN : 0 < codeN.length)
    (hinD : CodeIn L 0x6014f0#64 codeD) (hD : 0 < codeD.length)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = uac_at)
    (hp : 64 ≤ X.cpu.gpr.rsp.toNat) (hp8 : X.cpu.gpr.rsp.toNat + 8 ≤ 2 ^ 64)
    (hs1 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8) i))
    (hs2 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 16) i))
    (hs3 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 24) i))
    (hs4 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 32) i))
    (hs5 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 40) i))
    (hs6 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 48) i))
    (hs8 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 64) i))
    (hl : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsp i))
    (fw0 : ∀ i < 8, Foot Wl (Addr.add X.cpu.gpr.rdi i))
    (fw8 : ∀ i < 4, Foot Wl (Addr.add (X.cpu.gpr.rdi + 8#64) i))
    (fw12 : ∀ i < 4, Foot Wl (Addr.add (X.cpu.gpr.rdi + 12#64) i))
    (hq : X.cpu.gpr.rdi.toNat + 16 ≤ 2 ^ 64)
    (hd : X.cpu.gpr.rdi.toNat + 16 ≤ X.cpu.gpr.rsp.toNat - 64 ∨ X.cpu.gpr.rsp.toNat + 8 ≤ X.cpu.gpr.rdi.toNat)
    (hn : n < 2 ^ 32) (hnz : ∀ i < n, V (Addr.add X.cpu.gpr.rsi i) ≠ 0#8)
    (hz : V (Addr.add X.cpu.gpr.rsi n) = 0#8)
    (hf : ∀ i, i ≤ n → Foot F.data (Addr.add X.cpu.gpr.rsi i))
    (hpw : X.cpu.gpr.rsi.toNat + n + 1 ≤ 2 ^ 64)
    (hpf : X.cpu.gpr.rsi.toNat + n + 1 ≤ X.cpu.gpr.rsp.toNat - 48 ∨ X.cpu.gpr.rsp.toNat ≤ X.cpu.gpr.rsi.toNat)
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (hra : rdq(V, X.cpu.gpr.rsp) = e₂.add j₂)
    (hbi : (n = 0 ∨ ¬ rdd(V, X.cpu.gpr.rdi + 12#64).toNat < n) → Dst Wl X.cpu.gpr n rdq(V, X.cpu.gpr.rdi))
    (ki : (n = 0 ∨ ¬ rdd(V, X.cpu.gpr.rdi + 12#64).toNat < n) → ∀ (Z' : State) (t' : Nat), KeptW Wl s₀ Z' →
      Agree F Z'.proc.mm.mem (Vst (Mf (V0 V X.cpu.gpr) X.cpu.gpr.rsi rdq(V, X.cpu.gpr.rdi) n)
        (X.cpu.gpr.rdi + 8#64) (toBytesLE (BitVec.ofNat 32 n) 4)) →
      Z'.cpu.rip = e₂.add j₂ → Str.Back X.cpu.gpr Z'.cpu.gpr → Z'.cpu.gpr.rax = X.cpu.gpr.rdi →
      GoG prof L o gev gP gE Z' t')
    (kn : rdd(V, X.cpu.gpr.rdi + 12#64).toNat < n → ∀ (G : Gprs), Rg X.cpu.gpr n G →
      G.rdi = BitVec.ofNat 64 (4 * n + 4) → ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y →
      Agree F Y.proc.mm.mem (Vst (V0 V X.cpu.gpr) (X.cpu.gpr.rsp - 64) (toBytesLE (uac_at.add 146) 8)) →
      Y.cpu.rip = 0x6029b0#64 → Y.cpu.gpr = G.set 4 (X.cpu.gpr.rsp - 64) →
      (∀ (Z : State) (V' : Addr → Byte) (t'' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V' →
        Z.cpu.rip = uac_at.add 146 → Rg X.cpu.gpr n Z.cpu.gpr →
        Pn Wl X.cpu.gpr n (e₂.add j₂) Z.cpu.gpr.rax V' →
        P1 Z V' → GoG prof L o gev gP gE Z t'') →
      GoG prof L o gev gP gE Y t')
    (kz : ∀ (Z : State) (V' : Addr → Byte), P1 Z V' → rdq(V', X.cpu.gpr.rdi) = 0 → ∀ (Z' : State) (t' : Nat),
      KeptW Wl s₀ Z' →
      Agree F Z'.proc.mm.mem (Vst (Mf (W2 V' X.cpu.gpr.rdi Z.cpu.gpr.rax (BitVec.ofNat 32 n)) X.cpu.gpr.rsi
        Z.cpu.gpr.rax n) (X.cpu.gpr.rdi + 8#64) (toBytesLE (BitVec.ofNat 32 n) 4)) →
      Z'.cpu.rip = e₂.add j₂ → Str.Back X.cpu.gpr Z'.cpu.gpr → Z'.cpu.gpr.rax = X.cpu.gpr.rdi →
      GoG prof L o gev gP gE Z' t')
    (kd : ∀ (Z : State) (V' : Addr → Byte), P1 Z V' → rdq(V', X.cpu.gpr.rdi) ≠ 0 → ∀ (Y : State) (t' : Nat),
      KeptW Wl s₀ Y → Agree F Y.proc.mm.mem (Vst V' (X.cpu.gpr.rsp - 64) (toBytesLE (uac_at.add 162) 8)) →
      Y.cpu.rip = 0x6014f0#64 →
      Y.cpu.gpr = { Z.cpu.gpr with rdi := rdq(V', X.cpu.gpr.rdi), r14 := Z.cpu.gpr.rax }.set 4 (X.cpu.gpr.rsp - 64) →
      (∀ (Z₂ : State) (V'' : Addr → Byte) (t'' : Nat), KeptW Wl s₀ Z₂ → Agree F Z₂.proc.mm.mem V'' →
        Z₂.cpu.rip = uac_at.add 162 → Rg X.cpu.gpr n Z₂.cpu.gpr → Z₂.cpu.gpr.r14 = Z.cpu.gpr.rax →
        Pn Wl X.cpu.gpr n (e₂.add j₂) Z.cpu.gpr.rax V'' → P2 Z₂ V'' → GoG prof L o gev gP gE Z₂ t'') →
      GoG prof L o gev gP gE Y t')
    (kr : ∀ (Z₂ : State) (V'' : Addr → Byte), P2 Z₂ V'' → ∀ (Z' : State) (t' : Nat), KeptW Wl s₀ Z' →
      Agree F Z'.proc.mm.mem (Vst (Mf (W2 V'' X.cpu.gpr.rdi Z₂.cpu.gpr.r14 (BitVec.ofNat 32 n)) X.cpu.gpr.rsi
        Z₂.cpu.gpr.r14 n) (X.cpu.gpr.rdi + 8#64) (toBytesLE (BitVec.ofNat 32 n) 4)) →
      Z'.cpu.rip = e₂.add j₂ → Str.Back X.cpu.gpr Z'.cpu.gpr → Z'.cpu.gpr.rax = X.cpu.gpr.rdi →
      GoG prof L o gev gP gE Z' t') :
    GoG prof L o gev gP gE X t := by
  have hlt := X.cpu.gpr.rsp.isLt
  have hrip' : X.cpu.rip = uac_at.add 0 := by rw [addr_add_zero]; exact hrip
  have hpw' : X.cpu.gpr.rsi.toNat + (n + 1) ≤ 2 ^ 64 := by omega
  have tp : ∀ i, i ≤ n → (Addr.add X.cpu.gpr.rsi i).toNat = X.cpu.gpr.rsi.toNat + i :=
    fun i hi => toNat_add_of_fits (by omega) hpw'
  have k12 := ta12 _ hq
  have hV0 : ∀ i, i ≤ n → V0 V X.cpu.gpr (Addr.add X.cpu.gpr.rsi i) = V (Addr.add X.cpu.gpr.rsi i) :=
    fun i hi => v0_out hp _ (by rw [tp i hi]; omega)
  have hT0 : rdq(V0 V X.cpu.gpr, X.cpu.gpr.rdi) = rdq(V, X.cpu.gpr.rdi) := by
    rw [m0 (V := V) (g := X.cpu.gpr) hp X.cpu.gpr.rdi 8 (by omega) (by omega)]
  have hT12 : rdd(V0 V X.cpu.gpr, X.cpu.gpr.rdi + 12#64) = rdd(V, X.cpu.gpr.rdi + 12#64) := by
    rw [m0 (V := V) (g := X.cpu.gpr) hp (X.cpu.gpr.rdi + 12#64) 4 (by rw [k12]; omega) (by rw [k12]; omega)]
  have sv0' : Sv6 (V0 V X.cpu.gpr) X.cpu.gpr (e₂.add j₂) := sv0 hp hp8 hra
  -- from 101: `_chars[n] = 0`, `_len` = `n`, `rax` = `this`, the `pop`s and the `ret`
  have fin101 : ∀ (U : State) (M : Addr → Byte) (d : Addr) (t' : Nat), KeptW Wl s₀ U →
      Agree F U.proc.mm.mem (Cw M X.cpu.gpr.rsi d n) → U.cpu.rip = uac_at.add 101 →
      U.cpu.gpr.rsp = X.cpu.gpr.rsp - 56 → U.cpu.gpr.rbx = BitVec.ofNat 64 n → U.cpu.gpr.r15 = X.cpu.gpr.rdi →
      U.cpu.gpr.r14 + U.cpu.gpr.r12 = Addr.add d (4 * n) → Sv6 M X.cpu.gpr (e₂.add j₂) →
      Dst Wl X.cpu.gpr n d →
      (∀ (Z' : State) (t'' : Nat), KeptW Wl s₀ Z' →
        Agree F Z'.proc.mm.mem (Vst (Mf M X.cpu.gpr.rsi d n) (X.cpu.gpr.rdi + 8#64)
          (toBytesLE (BitVec.ofNat 32 n) 4)) →
        Z'.cpu.rip = e₂.add j₂ → Str.Back X.cpu.gpr Z'.cpu.gpr → Z'.cpu.gpr.rax = X.cpu.gpr.rdi →
        GoG prof L o gev gP gE Z' t'') →
      GoG prof L o gev gP gE U t' := by
    intro U M d t' hKU hAU hrU hus hubx hu15 h1412 hSv hDs k
    obtain ⟨hwd, hdw, hda⟩ := hDs
    have hM : Vst (Vst (Cw M X.cpu.gpr.rsi d n) (U.cpu.gpr.r14 + U.cpu.gpr.r12) (toBytesLE 0#32 4))
        (U.cpu.gpr.r15 + 8#64) (toBytesLE (BitVec.setWidth 32 U.cpu.gpr.rbx) 4) =
        Vst (Mf M X.cpu.gpr.rsi d n) (X.cpu.gpr.rdi + 8#64) (toBytesLE (BitVec.ofNat 32 n) 4) := by
      rw [h1412, hu15, hubx, sw32 hn]
    have hw4 : ∀ i < 4, Foot Wl (Addr.add (U.cpu.gpr.r14 + U.cpu.gpr.r12) i) := fun i hi => by
      rw [h1412, addr_add_add]
      exact hwd _ (by omega)
    refine (c_101 prof).run c hin _ hKU hAU hrU (vc_101 hM hw4 (by rw [hu15]; exact fw8)
      (by rw [hus, q48]; exact fun i hi => c.hws _ (hs6 i hi))
      (by rw [hus, q48, q40]; exact fun i hi => c.hws _ (hs5 i hi))
      (by rw [hus, q48, q40, q32]; exact fun i hi => c.hws _ (hs4 i hi))
      (by rw [hus, q48, q40, q32, q24]; exact fun i hi => c.hws _ (hs3 i hi))
      (by rw [hus, q48, q40, q32, q24, q16]; exact fun i hi => c.hws _ (hs2 i hi))
      (by rw [hus, q48, q40, q32, q24, q16, q8]; exact fun i hi => c.hws _ (hs1 i hi))) ?_
    rintro j' g fl V₁ ⟨rfl, rfl, rfl⟩ Z t₁ hKZ hAZ hrZ hgZ -
    rw [hus, q48, q40, q32, q24, q16, q8, q0] at hgZ
    obtain ⟨b1, b2, b3, b4, b5, b6, b7⟩ :=
      svF (s := X.cpu.gpr.rsi) (v := BitVec.ofNat 32 n) hp hp8 hq hd hdw hda hSv
    have hkp : Kp X.cpu.gpr Z.cpu.gpr := by
      refine ⟨by rw [hgZ], ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hgZ]; exact b1
      · rw [hgZ]; exact b2
      · rw [hgZ]; exact b3
      · rw [hgZ]; exact b4
      · rw [hgZ]; exact b5
      · rw [hgZ]; exact b6
    exact ret_back c hin (lt_len (by decide)) (ret_130 _) hKZ hAZ hrZ hkp hl hin₂ h₂ b7
      fun Z'' t'' hK'' hA'' hr'' hB hax'' => k Z'' t'' hK'' hA'' hr'' hB (by rw [hax'', hgZ]; exact hu15)
  have hf0 : ∀ i < 1, Foot F.data (Addr.add X.cpu.gpr.rsi i) := fun i hi => hf i (by omega)
  have hb0 : V0 V X.cpu.gpr X.cpu.gpr.rsi = V (Addr.add X.cpu.gpr.rsi 0) := by
    have := hV0 0 (Nat.zero_le _)
    rw [addr_add_zero] at this ⊢
    exact this
  rcases Nat.eq_zero_or_pos n with h0 | h0
  · -- the empty string: in place
    subst h0
    refine (c_0 prof).run c hin _ hK hA hrip'
      (vc_0z hs1 (by rw [e16]; exact hs2) (by rw [e24]; exact hs3) (by rw [e32]; exact hs4)
        (by rw [e40]; exact hs5) (by rw [e48]; exact hs6) hf0 (fun i hi => c.hws _ (fw0 i hi))
        (by rw [hb0]; exact hz)) ?_
    rintro j' g fl V₁ ⟨rfl, rfl, rfl⟩ Y t₁ hKY hAY hrY hgY -
    exact fin101 Y (V0 V X.cpu.gpr) rdq(V, X.cpu.gpr.rdi) t₁ hKY hAY hrY (by rw [hgY]; exact e56 _)
      (by rw [hgY] <;> rfl) (by rw [hgY] <;> rfl)
      (by rw [hgY]; show rdq(V0 V X.cpu.gpr, X.cpu.gpr.rdi) + 0#64 = _; rw [hT0] <;> rfl)
      sv0' (hbi (.inl rfl)) (ki (.inl rfl))
  -- from 73: `xor edx, edx; test ebx, ebx`, the copy loop, on from 101
  have fin73 : ∀ (U : State) (M : Addr → Byte) (d : Addr) (t' : Nat), KeptW Wl s₀ U →
      Agree F U.proc.mm.mem M → U.cpu.rip = uac_at.add 73 → Rg X.cpu.gpr n U.cpu.gpr → U.cpu.gpr.r14 = d →
      Sv6 M X.cpu.gpr (e₂.add j₂) →
      Dst Wl X.cpu.gpr n d →
      (∀ (Z' : State) (t'' : Nat), KeptW Wl s₀ Z' →
        Agree F Z'.proc.mm.mem (Vst (Mf M X.cpu.gpr.rsi d n) (X.cpu.gpr.rdi + 8#64)
          (toBytesLE (BitVec.ofNat 32 n) 4)) →
        Z'.cpu.rip = e₂.add j₂ → Str.Back X.cpu.gpr Z'.cpu.gpr → Z'.cpu.gpr.rax = X.cpu.gpr.rdi →
        GoG prof L o gev gP gE Z' t'') →
      GoG prof L o gev gP gE U t' := by
    intro U M d t' hKU hAU hrU hR h14 hSv hDs k
    obtain ⟨hus, hubp, hu15, hubx, hu13, hu12⟩ := hR
    refine (c_73 prof).run c hin (fun j' g' _ V' => j' = 80 ∧ g' = { U.cpu.gpr with rdx := 0#64 } ∧ V' = M)
      hKU hAU hrU (vc_73 hubx h0 hn fun _ => ⟨rfl, rfl, rfl⟩) ?_
    rintro j' g fl V₁ ⟨rfl, rfl, rfl⟩ Y t₁ hKY hAY hrY hgY -
    refine loop c hin (W := M) (s := X.cpu.gpr.rsi) (d := d) (n := n) (g₀ := Y.cpu.gpr) hn hf hDs.1
      (by rw [hgY]; exact hubp) (by rw [hgY]; exact h14) (by rw [hgY]; exact hu13) ?_ (n - 1) 0 (by omega) Y t₁
      hKY hAY hrY (by rw [hgY] <;> rfl) (Kp.refl _)
    intro Z t₂ hKZ hAZ hrZ hkp
    exact fin101 Z M d t₂ hKZ hAZ hrZ (by rw [hkp.1, hgY]; exact hus) (by rw [hkp.2.1, hgY]; exact hubx)
      (by rw [hkp.2.2.2.2.2.2, hgY]; exact hu15)
      (by rw [hkp.2.2.2.2.2.1, hkp.2.2.2.1, hgY]; show U.cpu.gpr.r14 + U.cpu.gpr.r12 = _; rw [h14, hu12] <;> rfl)
      hSv hDs k
  -- at 162 with the bytes `M`: the stores of `_chars` = `p` and `_limit`, then on from 73
  have h162 : ∀ (U : State) (M : Addr → Byte) (p : Addr) (t' : Nat), KeptW Wl s₀ U → Agree F U.proc.mm.mem M →
      U.cpu.rip = uac_at.add 162 → Rg X.cpu.gpr n U.cpu.gpr → U.cpu.gpr.r14 = p →
      Pn Wl X.cpu.gpr n (e₂.add j₂) p M →
      (∀ (Z' : State) (t'' : Nat), KeptW Wl s₀ Z' →
        Agree F Z'.proc.mm.mem (Vst (Mf (W2 M X.cpu.gpr.rdi p (BitVec.ofNat 32 n)) X.cpu.gpr.rsi p n)
          (X.cpu.gpr.rdi + 8#64) (toBytesLE (BitVec.ofNat 32 n) 4)) →
        Z'.cpu.rip = e₂.add j₂ → Str.Back X.cpu.gpr Z'.cpu.gpr → Z'.cpu.gpr.rax = X.cpu.gpr.rdi →
        GoG prof L o gev gP gE Z' t'') →
      GoG prof L o gev gP gE U t' := by
    intro U M p t' hKU hAU hrU hR h14 hP k
    have hu15 : U.cpu.gpr.r15 = X.cpu.gpr.rdi := hR.2.2.1
    have hubx : U.cpu.gpr.rbx = BitVec.ofNat 64 n := hR.2.2.2.1
    refine (c_162 prof).run c hin _ hKU hAU hrU (vc_162 (by rw [hu15]; exact fw0) (by rw [hu15]; exact fw12)) ?_
    rintro j' g fl V₁ ⟨rfl, rfl, rfl⟩ U' t₁ hKU' hAU' hrU' hgU' -
    rw [hu15, h14, hubx, sw32 hn] at hAU'
    exact fin73 U' _ p t₁ hKU' hAU' hrU' (by rw [hgU']; exact hR) (by rw [hgU']; exact h14)
      (sv2 p (BitVec.ofNat 32 n) hp hp8 hq hd hP.1) hP.2 k
  -- at 141: `operator new []`, then `delete [] _chars` unless null, on from 162
  have h141 : rdd(V, X.cpu.gpr.rdi + 12#64).toNat < n → ∀ (Y₂ : State) (t₃ : Nat), KeptW Wl s₀ Y₂ →
      Agree F Y₂.proc.mm.mem (V0 V X.cpu.gpr) → Y₂.cpu.rip = uac_at.add 141 → Rg X.cpu.gpr n Y₂.cpu.gpr →
      Y₂.cpu.gpr.rdi = BitVec.ofNat 64 (4 * n + 4) → GoG prof L o gev gP gE Y₂ t₃ := by
    intro hc Y₂ t₃ hK₂ hA₂ hr₂ hR hdi
    have hs2' : Y₂.cpu.gpr.rsp = X.cpu.gpr.rsp - 56 := hR.1
    refine c.s_call hK₂ hA₂ hin (lt_len (by decide)) hr₂ (call_141 _) hinN hN (by decide)
      (by rw [hs2', e64]; exact hs8) ?_
    rintro Y₃ t₄ hK₃ hA₃ ⟨hr₃, hg₃⟩
    rw [hs2', e64] at hA₃
    have hg₃' : Y₃.cpu.gpr = Y₂.cpu.gpr.set 4 (X.cpu.gpr.rsp - 64) := by rw [hg₃, hs2', e64]
    refine kn hc Y₂.cpu.gpr hR hdi Y₃ t₄ hK₃ hA₃ hr₃ hg₃' ?_
    -- back from `operator new []`
    intro Z V' t₅ hKZ hAZ hrZ hRZ hPn hP1
    have hz15 : Z.cpu.gpr.r15 = X.cpu.gpr.rdi := hRZ.2.2.1
    refine (c_146 prof).run c hin (fun j' g' _ V'' =>
        g' = { Z.cpu.gpr with rdi := rdq(V', X.cpu.gpr.rdi), r14 := Z.cpu.gpr.rax } ∧ V'' = V' ∧
        ((j' = 162 ∧ rdq(V', X.cpu.gpr.rdi) = 0) ∨ (j' = 157 ∧ rdq(V', X.cpu.gpr.rdi) ≠ 0))) hKZ hAZ hrZ
      (vc_146 (by rw [hz15]; exact fun i hi => c.hws _ (fw0 i hi))
        (fun h0 _ => ⟨by simp only [hz15], rfl, .inl ⟨rfl, by rw [← hz15]; exact h0⟩⟩)
        (fun h0 _ => ⟨by simp only [hz15], rfl, .inr ⟨rfl, by rw [← hz15]; exact h0⟩⟩)) ?_
    rintro j' g fl V₃ ⟨rfl, hV₃, h⟩ Y₄ t₆ hK₄ hA₄ hr₄ hg₄ -
    subst V₃
    rcases h with ⟨rfl, h0⟩ | ⟨rfl, h0⟩
    · -- `_chars` null
      exact h162 Y₄ V' Z.cpu.gpr.rax t₆ hK₄ hA₄ hr₄ (by rw [hg₄]; exact hRZ) (by rw [hg₄] <;> rfl) hPn
        (kz Z V' hP1 h0)
    · -- `operator delete [] (_chars)`
      have hs4' : Y₄.cpu.gpr.rsp = X.cpu.gpr.rsp - 56 := by rw [hg₄]; exact hRZ.1
      refine c.s_call hK₄ hA₄ hin (lt_len (by decide)) hr₄ (call_157 _) hinD hD (by decide)
        (by rw [hs4', e64]; exact hs8) ?_
      rintro Y₅ t₇ hK₅ hA₅ ⟨hr₅, hg₅⟩
      rw [hs4', e64] at hA₅
      have hg₅' : Y₅.cpu.gpr =
          { Z.cpu.gpr with rdi := rdq(V', X.cpu.gpr.rdi), r14 := Z.cpu.gpr.rax }.set 4 (X.cpu.gpr.rsp - 64) := by
        rw [hg₅, hs4', e64, hg₄]
      refine kd Z V' hP1 h0 Y₅ t₇ hK₅ hA₅ hr₅ hg₅' ?_
      intro Z₂ V'' t₈ hK₆ hA₆ hr₆ hR₂ h214 hPn₂ hP2
      exact h162 Z₂ V'' Z.cpu.gpr.rax t₈ hK₆ hA₆ hr₆ hR₂ h214 hPn₂
        fun Z' t'' hK' hA' hr' hB hax => kr Z₂ V'' hP2 Z' t'' hK' (by rw [h214]; exact hA') hr' hB hax
  -- the entry and the length loop
  refine (c_0 prof).run c hin _ hK hA hrip'
    (vc_0n hs1 (by rw [e16]; exact hs2) (by rw [e24]; exact hs3) (by rw [e32]; exact hs4)
      (by rw [e40]; exact hs5) (by rw [e48]; exact hs6) hf0 (by rw [hb0]; exact hnz 0 h0)) ?_
  rintro j' g fl V₁ ⟨rfl, rfl, rfl⟩ Y t₁ hKY hAY hrY hgY -
  refine slen c hin (W := V0 V X.cpu.gpr) (p := X.cpu.gpr.rsi) (n := n) (g₀ := gS X.cpu.gpr) hn
    (fun i hi => by rw [hV0 i (by omega)]; exact hnz i hi) (by rw [hV0 n (Nat.le_refl _)]; exact hz) hf rfl
    (fun i hi => c.hws _ (fw12 i hi)) (fun i hi => c.hws _ (fw0 i hi)) ?_ ?_ (n - 1) 0 (by omega) Y t₁ hKY hAY hrY
    (by rw [hgY] <;> rfl) (by rw [hgY]; exact ⟨rfl, rfl, rfl, rfl, rfl⟩)
  · intro hc Z t' hKZ hAZ hrZ hE _ hdi
    exact h141 (by rw [← hT12]; exact hc) Z t' hKZ hAZ hrZ (rgE hE) hdi
  · intro hc Z t' hKZ hAZ hrZ hE h14
    have hc' : ¬ rdd(V, X.cpu.gpr.rdi + 12#64).toNat < n := by rw [← hT12]; exact hc
    exact fin73 Z (V0 V X.cpu.gpr) rdq(V, X.cpu.gpr.rdi) t' hKZ hAZ hrZ (rgE hE) (by rw [h14]; exact hT0) sv0'
      (hbi (.inr hc')) (ki (.inr hc'))

end FV7z.Uac
