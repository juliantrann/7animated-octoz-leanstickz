import FV7z.Ain.Cuts
import FV7z.Lemmas.LeafRet
import FV7z.Lemmas.FnMem
import FV7z.Tun.Inv
/-!
# `AString::Insert` (PLAN.md §M, M1)

7-Zip 26.06's `AString::Insert (index, s)` at `0x44cd10` in `7zzs` (`CPP/Common/MyString.cpp`), `this` = `rdi`,
`index` = `esi`, `s` = `rdx`, `S` the entry's `rsp`: `push r12; push rbp; push rbx; sub rsp, 0x10` (`aR S`),
`r12d` = `s._len` (`[rdx + 8]`), `index` stored at `aR S + 12`; if `s._len` is 0, `add rsp, 0x10; pop rbx; pop rbp;
pop r12; ret` (33); else `rbx` = `s`, `rbp` = `this`, `InsertSpace (&index, s._len)` (`call` at 54 to `0x44c140`,
`rsi` = `aR S + 12`, `edx` = `s._len`); back at 59 `rsi` = `s._chars`, `rdi` = `_chars + index` (`index` read back
from `aR S + 12`), `edx` = `s._len`, `memcpy` (`call` at 73 to the PLT's entry `0x401070`); back at 78
`add [rbp + 8], r12d` (by hand, `Seg.s_add_mr32`: `_len += s._len`); at 82 `add rsp, 0x10; pop rbx; pop rbp;
pop r12`; the `ret` (90).

The callees are hypotheses, as in `FV7z/Adl/Holds.lean`: each a continuation at its entry (`kf1`, `kf2`), given the
run from its return; `Pc1`, `Pc2` are what they leave. `memcpy`'s return gives the saved registers and the return
address in the bytes it leaves.

- `aR`, `ln`, `V1`, `V0`, `gM`, `g59`: the frame's `rsp`; `s._len`; the bytes with the three pushes, and with
  `index` stored; the registers at the two `call`s.
- `rd_*`, `hxl`: loads from `V0` and `V1` (the saved registers, the return address, `s._len`).
- `vc_z`, `vc_nz`: the piece from the entry, one for each way; `vc_59`, `vc_82`: the pieces after the `call`s and
  after the `add`.
- `ain_ok`: with `s._len` 0, at the return address with `rbx`, `rbp`, `r12`, `rsp` restored (`kn`); else through
  both callees, the `add` and the return (`kr`).
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Ain

/-- `AString::InsertSpace`. -/
abbrev isp_at : Addr := 0x44c140

/-- The PLT's entry for `memcpy`. -/
abbrev plt_memcpy : Addr := 0x401070

/-- The `call` to `InsertSpace`. -/
def pci : List Byte := [0xe8, 0xf5, 0xf3, 0xff, 0xff]
theorem pci_0 : ∀ feat, Dec feat pci 0 (FV7z.mk .call 64 [.rel 18446744073709548533] 5) := by dec_rfl
theorem wc_54 : pci <+: ain.drop 54 := by decide +kernel
theorem call_54 (feat : Features) : Dec feat ain 54 (FV7z.mk .call 64 [.rel 18446744073709548533] 5) :=
  Dec.shift (j := 54) (k := 0) (pci_0 feat) wc_54 (Nat.zero_le _)
theorem tgt_54 : ain_at.add (54 + 5) + BitVec.ofNat 64 18446744073709548533 = isp_at := by decide

/-- The `call` to `memcpy`. -/
def pcm : List Byte := [0xe8, 0x12, 0x43, 0xfb, 0xff]
theorem pcm_0 : ∀ feat, Dec feat pcm 0 (FV7z.mk .call 64 [.rel 18446744073709241106] 5) := by dec_rfl
theorem wc_73 : pcm <+: ain.drop 73 := by decide +kernel
theorem call_73 (feat : Features) : Dec feat ain 73 (FV7z.mk .call 64 [.rel 18446744073709241106] 5) :=
  Dec.shift (j := 73) (k := 0) (pcm_0 feat) wc_73 (Nat.zero_le _)
theorem tgt_73 : ain_at.add (73 + 5) + BitVec.ofNat 64 18446744073709241106 = plt_memcpy := by decide

/-- `add dword [rbp + 8], r12d`. -/
def pad : List Byte := [0x44, 0x01, 0x65, 0x08]
theorem pad_0 : ∀ feat, Dec feat pad 0 (FV7z.mk .add 32 [.mem (mbd 5 8 32), gr 32 12] 4) := by dec_rfl
theorem wa_78 : pad <+: ain.drop 78 := by decide +kernel
theorem add_78 (feat : Features) : Dec feat ain 78 (FV7z.mk .add 32 [.mem (mbd 5 8 32), gr 32 12] 4) :=
  Dec.shift (j := 78) (k := 0) (pad_0 feat) wa_78 (Nat.zero_le _)

/-- The `ret`s. -/
def pret : List Byte := [0xc3]
theorem pret_0 : ∀ feat, Dec feat pret 0 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem w_33 : pret <+: ain.drop 33 := by decide +kernel
theorem ret_33 (feat : Features) : Dec feat ain 33 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 33) (k := 0) (pret_0 feat) w_33 (Nat.zero_le _)
theorem w_90 : pret <+: ain.drop 90 := by decide +kernel
theorem ret_90 (feat : Features) : Dec feat ain 90 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 90) (k := 0) (pret_0 feat) w_90 (Nat.zero_le _)

/-! ## The frame -/

/-- The stack pointer after `push r12; push rbp; push rbx; sub rsp, 0x10`. -/
abbrev aR (S : Addr) : Addr := S - 8 - 8 - 8 - 16#64

/-- `s._len`. -/
abbrev ln (V : Addr → Byte) (g : Gprs) : BitVec 32 := rdd(V, g.rdx + 8#64)

/-- The bytes with `r12`, `rbp`, `rbx` pushed. -/
abbrev V1 (V : Addr → Byte) (g : Gprs) : Addr → Byte :=
  Vst (Vst (Vst V (g.rsp - 8) (toBytesLE g.r12 8)) (g.rsp - 8 - 8) (toBytesLE g.rbp 8)) (g.rsp - 8 - 8 - 8)
    (toBytesLE g.rbx 8)

/-- `V1` with `index` stored at `aR S + 12`. -/
abbrev V0 (V : Addr → Byte) (g : Gprs) : Addr → Byte :=
  Vst (V1 V g) (aR g.rsp + 12#64) (toBytesLE (BitVec.setWidth 32 g.rsi) 4)

/-- The registers at the `call` of `InsertSpace`: `rbx` = `s`, `rbp` = `this`, `rsi` = `&index`, `edx` = `r12d` =
`s._len`. -/
abbrev gM (V : Addr → Byte) (g : Gprs) : Gprs :=
  { g with
      rbx := g.rdx,
      rsp := aR g.rsp,
      rbp := g.rdi,
      rsi := aR g.rsp + 12#64,
      rdx := BitVec.setWidth 64 (ln V g),
      r12 := BitVec.setWidth 64 (ln V g) }

/-- The registers at the `call` of `memcpy`: `rsi` = `s._chars`, `rdi` = `_chars + index`, `edx` = `r12d`. -/
abbrev g59 (g : Gprs) (V : Addr → Byte) : Gprs :=
  { g with
      rsi := rdq(V, g.rbx),
      rdi := BitVec.setWidth 64 rdd(V, g.rsp + 12#64) + rdq(V, g.rbp),
      rdx := BitVec.setWidth 64 (BitVec.setWidth 32 g.r12) }

theorem aE1 (s : Addr) : aR s + 16#64 = s - 8 - 8 - 8 := BitVec.sub_add_cancel _ _
theorem aE2 (s : Addr) : s - 8 - 8 - 8 + 8 = s - 8 - 8 := BitVec.sub_add_cancel _ _
theorem aE3 (s : Addr) : s - 8 - 8 + 8 = s - 8 := BitVec.sub_add_cancel _ _
theorem aE4 (s : Addr) : s - 8 + 8 = s := BitVec.sub_add_cancel _ _

theorem aT8 (s : BitVec 64) (h : 48 ≤ s.toNat) : (s - 8).toNat = s.toNat - 8 := by bv_omega
theorem aT16 (s : BitVec 64) (h : 48 ≤ s.toNat) : (s - 8 - 8).toNat = s.toNat - 16 := by bv_omega
theorem aT24 (s : BitVec 64) (h : 48 ≤ s.toNat) : (s - 8 - 8 - 8).toNat = s.toNat - 24 := by bv_omega
theorem aT28 (s : BitVec 64) (h : 48 ≤ s.toNat) : (aR s + 12#64).toNat = s.toNat - 28 := by
  show (s - 8 - 8 - 8 - 16#64 + 12#64).toNat = s.toNat - 28
  bv_omega
theorem aTr8 (x : BitVec 64) (h : x.toNat + 12 ≤ 2 ^ 64) : (x + 8#64).toNat = x.toNat + 8 := by bv_omega

/-- A load apart from a store: as before it. -/
theorem aRdA {W : Addr → Byte} {a x : Addr} {bs : List Byte} {w n : Nat} (ha : a.toNat + bs.length ≤ 2 ^ 64)
    (hx : x.toNat + n ≤ 2 ^ 64) (h : a.toNat + bs.length ≤ x.toNat ∨ x.toNat + n ≤ a.toNat) :
    ofBytesLE w ((byteAddrs x n).map (Vst W a bs)) = ofBytesLE w ((byteAddrs x n).map W) := by
  rw [Tun.rd_Vst W a bs x n ha hx h]

/-- A load of what a store of 8 bytes stored. -/
theorem aRdS {W : Addr → Byte} {a : Addr} {v : BitVec 64} (ha : a.toNat + 8 ≤ 2 ^ 64) :
    rdq(Vst W a (toBytesLE v 8), a) = v := by
  rw [Tun.rd_Vst_self W a (toBytesLE v 8) (toBytesLE_length _ _) ha, ofBytesLE_toBytesLE (w := 64) (n := 8) rfl]

/-- The saved `rbx` in `V0`. -/
theorem rd_rbx (V : Addr → Byte) (g : Gprs) (hp : 48 ≤ g.rsp.toNat) : rdq(V0 V g, g.rsp - 8 - 8 - 8) = g.rbx := by
  have hlt := g.rsp.isLt
  have t24 := aT24 g.rsp hp
  have t28 := aT28 g.rsp hp
  have a0 := aRdA (w := 64) (W := V1 V g) (a := aR g.rsp + 12#64) (bs := toBytesLE (BitVec.setWidth 32 g.rsi) 4)
    (x := g.rsp - 8 - 8 - 8) (n := 8) (by rw [toBytesLE_length, t28]; omega) (by rw [t24]; omega)
    (Or.inl (by rw [toBytesLE_length, t28, t24]; omega))
  exact a0.trans (aRdS (W := Vst (Vst V (g.rsp - 8) (toBytesLE g.r12 8)) (g.rsp - 8 - 8) (toBytesLE g.rbp 8))
    (a := g.rsp - 8 - 8 - 8) (v := g.rbx) (by rw [t24]; omega))

/-- The saved `rbp` in `V0`. -/
theorem rd_rbp (V : Addr → Byte) (g : Gprs) (hp : 48 ≤ g.rsp.toNat) : rdq(V0 V g, g.rsp - 8 - 8) = g.rbp := by
  have hlt := g.rsp.isLt
  have t16 := aT16 g.rsp hp
  have t24 := aT24 g.rsp hp
  have t28 := aT28 g.rsp hp
  have a0 := aRdA (w := 64) (W := V1 V g) (a := aR g.rsp + 12#64) (bs := toBytesLE (BitVec.setWidth 32 g.rsi) 4)
    (x := g.rsp - 8 - 8) (n := 8) (by rw [toBytesLE_length, t28]; omega) (by rw [t16]; omega)
    (Or.inl (by rw [toBytesLE_length, t28, t16]; omega))
  have a1 := aRdA (w := 64) (W := Vst (Vst V (g.rsp - 8) (toBytesLE g.r12 8)) (g.rsp - 8 - 8) (toBytesLE g.rbp 8))
    (a := g.rsp - 8 - 8 - 8) (bs := toBytesLE g.rbx 8) (x := g.rsp - 8 - 8) (n := 8)
    (by rw [toBytesLE_length, t24]; omega) (by rw [t16]; omega) (Or.inl (by rw [toBytesLE_length, t24, t16]; omega))
  exact a0.trans (a1.trans (aRdS (W := Vst V (g.rsp - 8) (toBytesLE g.r12 8)) (a := g.rsp - 8 - 8) (v := g.rbp)
    (by rw [t16]; omega)))

/-- The saved `r12` in `V0`. -/
theorem rd_r12 (V : Addr → Byte) (g : Gprs) (hp : 48 ≤ g.rsp.toNat) : rdq(V0 V g, g.rsp - 8) = g.r12 := by
  have hlt := g.rsp.isLt
  have t8 := aT8 g.rsp hp
  have t16 := aT16 g.rsp hp
  have t24 := aT24 g.rsp hp
  have t28 := aT28 g.rsp hp
  have a0 := aRdA (w := 64) (W := V1 V g) (a := aR g.rsp + 12#64) (bs := toBytesLE (BitVec.setWidth 32 g.rsi) 4)
    (x := g.rsp - 8) (n := 8) (by rw [toBytesLE_length, t28]; omega) (by rw [t8]; omega)
    (Or.inl (by rw [toBytesLE_length, t28, t8]; omega))
  have a1 := aRdA (w := 64) (W := Vst (Vst V (g.rsp - 8) (toBytesLE g.r12 8)) (g.rsp - 8 - 8) (toBytesLE g.rbp 8))
    (a := g.rsp - 8 - 8 - 8) (bs := toBytesLE g.rbx 8) (x := g.rsp - 8) (n := 8)
    (by rw [toBytesLE_length, t24]; omega) (by rw [t8]; omega) (Or.inl (by rw [toBytesLE_length, t24, t8]; omega))
  have a2 := aRdA (w := 64) (W := Vst V (g.rsp - 8) (toBytesLE g.r12 8)) (a := g.rsp - 8 - 8)
    (bs := toBytesLE g.rbp 8) (x := g.rsp - 8) (n := 8)
    (by rw [toBytesLE_length, t16]; omega) (by rw [t8]; omega) (Or.inl (by rw [toBytesLE_length, t16, t8]; omega))
  exact a0.trans (a1.trans (a2.trans (aRdS (W := V) (a := g.rsp - 8) (v := g.r12) (by rw [t8]; omega))))

/-- The return address in `V0`: as in `V`. -/
theorem rd_ra (V : Addr → Byte) (g : Gprs) (hp : 48 ≤ g.rsp.toNat) (hp8 : g.rsp.toNat + 8 ≤ 2 ^ 64) :
    rdq(V0 V g, g.rsp) = rdq(V, g.rsp) := by
  have hlt := g.rsp.isLt
  have t8 := aT8 g.rsp hp
  have t16 := aT16 g.rsp hp
  have t24 := aT24 g.rsp hp
  have t28 := aT28 g.rsp hp
  have a0 := aRdA (w := 64) (W := V1 V g) (a := aR g.rsp + 12#64) (bs := toBytesLE (BitVec.setWidth 32 g.rsi) 4)
    (x := g.rsp) (n := 8) (by rw [toBytesLE_length, t28]; omega) hp8
    (Or.inl (by rw [toBytesLE_length, t28]; omega))
  have a1 := aRdA (w := 64) (W := Vst (Vst V (g.rsp - 8) (toBytesLE g.r12 8)) (g.rsp - 8 - 8) (toBytesLE g.rbp 8))
    (a := g.rsp - 8 - 8 - 8) (bs := toBytesLE g.rbx 8) (x := g.rsp) (n := 8)
    (by rw [toBytesLE_length, t24]; omega) hp8 (Or.inl (by rw [toBytesLE_length, t24]; omega))
  have a2 := aRdA (w := 64) (W := Vst V (g.rsp - 8) (toBytesLE g.r12 8)) (a := g.rsp - 8 - 8)
    (bs := toBytesLE g.rbp 8) (x := g.rsp) (n := 8)
    (by rw [toBytesLE_length, t16]; omega) hp8 (Or.inl (by rw [toBytesLE_length, t16]; omega))
  have a3 := aRdA (w := 64) (W := V) (a := g.rsp - 8) (bs := toBytesLE g.r12 8) (x := g.rsp) (n := 8)
    (by rw [toBytesLE_length, t8]; omega) hp8 (Or.inl (by rw [toBytesLE_length, t8]; omega))
  exact a0.trans (a1.trans (a2.trans a3))

/-- `s._len` in `V1`: as in `V`, `s`'s 12 bytes apart from the pushes. -/
theorem hxl (V : Addr → Byte) (g : Gprs) (hp : 48 ≤ g.rsp.toNat) (hq1 : g.rdx.toNat + 12 ≤ 2 ^ 64)
    (hd1 : g.rdx.toNat + 12 ≤ g.rsp.toNat - 24 ∨ g.rsp.toNat ≤ g.rdx.toNat) :
    rdd(V1 V g, g.rdx + 8#64) = rdd(V, g.rdx + 8#64) := by
  have hlt := g.rsp.isLt
  have t8 := aT8 g.rsp hp
  have t16 := aT16 g.rsp hp
  have t24 := aT24 g.rsp hp
  have r8 := aTr8 g.rdx hq1
  have a1 := aRdA (w := 32) (W := Vst (Vst V (g.rsp - 8) (toBytesLE g.r12 8)) (g.rsp - 8 - 8) (toBytesLE g.rbp 8))
    (a := g.rsp - 8 - 8 - 8) (bs := toBytesLE g.rbx 8) (x := g.rdx + 8#64) (n := 4)
    (by rw [toBytesLE_length, t24]; omega) (by rw [r8]; omega) (by rw [toBytesLE_length, t24, r8]; omega)
  have a2 := aRdA (w := 32) (W := Vst V (g.rsp - 8) (toBytesLE g.r12 8)) (a := g.rsp - 8 - 8)
    (bs := toBytesLE g.rbp 8) (x := g.rdx + 8#64) (n := 4)
    (by rw [toBytesLE_length, t16]; omega) (by rw [r8]; omega) (by rw [toBytesLE_length, t16, r8]; omega)
  have a3 := aRdA (w := 32) (W := V) (a := g.rsp - 8) (bs := toBytesLE g.r12 8) (x := g.rdx + 8#64) (n := 4)
    (by rw [toBytesLE_length, t8]; omega) (by rw [r8]; omega) (by rw [toBytesLE_length, t8, r8]; omega)
  exact a1.trans (a2.trans a3)

/-! ## The pieces -/

variable {F : Footprint} {Wl : List Rgn}

/-- `s._len` 0: the entry's code, the `jne` not taken, `add rsp, 0x10; pop rbx; pop rbp; pop r12` to the `ret` at
33. -/
theorem vc_z {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} (hz : (ln V g == 0) = true)
    (hs1 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8) i)) (hs2 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8) i))
    (hs3 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8 - 8) i))
    (fl : ∀ i < 4, Foot F.data (Addr.add (g.rdx + 8#64) i))
    (hw4 : ∀ i < 4, Foot Wl (Addr.add (aR g.rsp + 12#64) i))
    (l1 : ∀ i < 8, Foot F.data (Addr.add (aR g.rsp + 16#64) i))
    (l2 : ∀ i < 8, Foot F.data (Addr.add (aR g.rsp + 16#64 + 8) i))
    (l3 : ∀ i < 8, Foot F.data (Addr.add (aR g.rsp + 16#64 + 8 + 8) i))
    (hx : rdd(V1 V g, g.rdx + 8#64) = rdd(V, g.rdx + 8#64))
    (h : ∀ fl, Q 33
      { g with
          rbx := rdq(V0 V g, aR g.rsp + 16#64),
          rbp := rdq(V0 V g, aR g.rsp + 16#64 + 8),
          rsp := aR g.rsp + 16#64 + 8 + 8 + 8,
          r12 := rdq(V0 V g, aR g.rsp + 16#64 + 8 + 8) } fl (V0 V g)) :
    W_0 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [ln, aR, V0, V1] at hz hs1 hs2 hs3 fl hw4 l1 l2 l3 hx h ⊢
  wpx [W_0, W_25, W_40, o0, o1, o2, hx, BitVec.and_self, hz, Bool.not_true, Bool.not_false,
      Bool.true_eq_false, Bool.false_eq_true, false_implies, true_implies, and_true, true_and, implies_true]
  all_goals repeat'
    first
    | exact h _
    | assumption
    | exact trivial
    | apply And.intro
    | intro _

/-- `s._len` not 0: the entry's code, the `jne` taken, up to the `call` at 54. -/
theorem vc_nz {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} (hz : (ln V g == 0) = false)
    (hs1 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8) i)) (hs2 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8) i))
    (hs3 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8 - 8) i))
    (fl : ∀ i < 4, Foot F.data (Addr.add (g.rdx + 8#64) i))
    (hw4 : ∀ i < 4, Foot Wl (Addr.add (aR g.rsp + 12#64) i))
    (hx : rdd(V1 V g, g.rdx + 8#64) = rdd(V, g.rdx + 8#64))
    (h : ∀ fl, Q 54 (gM V g) fl (V0 V g)) :
    W_0 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [gM, ln, aR, V0, V1] at hz hs1 hs2 hs3 fl hw4 hx h ⊢
  wpx [W_0, W_25, W_40, o0, o1, o2, hx, BitVec.and_self, hz, Bool.not_true, Bool.not_false,
      Bool.true_eq_false, Bool.false_eq_true, false_implies, true_implies, and_true, true_and, implies_true]
  all_goals repeat'
    first
    | exact h _
    | assumption
    | exact trivial
    | apply And.intro
    | intro _

/-- Back from `InsertSpace`: `mov rsi, [rbx]; mov edi, [rsp + 12]; mov edx, r12d; add rdi, [rbp]` to the `call`
at 73. -/
theorem vc_59 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (f1 : ∀ i < 8, Foot F.data (Addr.add g.rbx i)) (f2 : ∀ i < 4, Foot F.data (Addr.add (g.rsp + 12#64) i))
    (f3 : ∀ i < 8, Foot F.data (Addr.add g.rbp i))
    (h : ∀ fl, Q 73 (g59 g V) fl V) : W_59 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [g59] at f1 f2 f3 h ⊢
  wpx [W_59, o3]
  all_goals repeat' (first | exact h _ | assumption | exact trivial | apply And.intro | intro _)

/-- After the `add`: `add rsp, 0x10; pop rbx; pop rbp; pop r12` to the `ret` at 90. -/
theorem vc_82 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (l1 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 16#64) i))
    (l2 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 16#64 + 8) i))
    (l3 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 16#64 + 8 + 8) i))
    (h : ∀ fl, Q 90
      { g with
          rbx := rdq(V, g.rsp + 16#64),
          rbp := rdq(V, g.rsp + 16#64 + 8),
          rsp := g.rsp + 16#64 + 8 + 8 + 8,
          r12 := rdq(V, g.rsp + 16#64 + 8 + 8) } fl V) :
    W_82 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at l1 l2 l3 h ⊢
  wpx [W_82, o1]
  all_goals repeat' (first | exact h _ | assumption | exact trivial | apply And.intro | intro _)

/-! ## The function -/

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {X : State} {t : Nat} {V : Addr → Byte}

/-- `AString::Insert (index, s)` (`this` = `rdi`, `index` = `esi`, `s` = `rdx`) from its entry, `S` = `rsp`. With
`s._len` 0, at the return address with `rbx`, `rbp`, `r12`, `rsp` restored and the bytes `V0` (`kn`). Else at
`InsertSpace`'s entry with the registers `gM`, the bytes `V0` and the return address `ain_at + 59` at `aR S - 8`
(`kf1`); from its return (`rsp` = `aR S`, `rbx` = `s`, `rbp` = `this`, `r12` = `s._len`, the post `Pc1`) at
`memcpy`'s entry with the registers `g59` and the return address `ain_at + 78` (`kf2`); from its return (the same
registers, the saved ones and the return address in its bytes, the post `Pc2`) through `_len += s._len` to the
return address with `rbx`, `rbp`, `r12`, `rsp` restored (`kr`). -/
theorem ain_ok {Pc1 Pc2 : State → (Addr → Byte) → Prop} (c : Seg prof F Wl L s₀ o) (hin : CodeIn L ain_at ain)
    {codeI : List Byte} (hinI : CodeIn L isp_at codeI) (hI : 0 < codeI.length)
    {codeM : List Byte} (hinM : CodeIn L plt_memcpy codeM) (hM : 0 < codeM.length)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = ain_at)
    (hp : 48 ≤ X.cpu.gpr.rsp.toNat) (hp8 : X.cpu.gpr.rsp.toNat + 8 ≤ 2 ^ 64)
    (hs1 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8) i))
    (hs2 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8 - 8) i))
    (hs3 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8 - 8 - 8) i))
    (hw4 : ∀ i < 4, Foot Wl (Addr.add (aR X.cpu.gpr.rsp + 12#64) i))
    (hs5 : ∀ i < 8, Foot Wl (Addr.add (aR X.cpu.gpr.rsp - 8) i))
    (hl : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsp i))
    (fl : ∀ i < 4, Foot F.data (Addr.add (X.cpu.gpr.rdx + 8#64) i))
    (fb : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rdx i))
    (fc : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rdi i))
    (fw : ∀ i < 4, Foot Wl (Addr.add (X.cpu.gpr.rdi + 8#64) i))
    (hq1 : X.cpu.gpr.rdx.toNat + 12 ≤ 2 ^ 64)
    (hd1 : X.cpu.gpr.rdx.toNat + 12 ≤ X.cpu.gpr.rsp.toNat - 24 ∨ X.cpu.gpr.rsp.toNat ≤ X.cpu.gpr.rdx.toNat)
    (hq2 : X.cpu.gpr.rdi.toNat + 12 ≤ 2 ^ 64)
    (hd2 : X.cpu.gpr.rdi.toNat + 12 ≤ X.cpu.gpr.rsp.toNat - 24 ∨ X.cpu.gpr.rsp.toNat ≤ X.cpu.gpr.rdi.toNat)
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (hra : rdq(V, X.cpu.gpr.rsp) = e₂.add j₂)
    (kn : ln V X.cpu.gpr = 0 → ∀ (Z : State) (t' : Nat), KeptW Wl s₀ Z →
      Agree F Z.proc.mm.mem (V0 V X.cpu.gpr) → Z.cpu.rip = e₂.add j₂ →
      Z.cpu.gpr = { X.cpu.gpr with rsp := X.cpu.gpr.rsp + 8 } →
      GoG prof L o gev gP gE Z t')
    (kf1 : ln V X.cpu.gpr ≠ 0 → ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y →
      Agree F Y.proc.mm.mem (Vst (V0 V X.cpu.gpr) (aR X.cpu.gpr.rsp - 8) (toBytesLE (ain_at.add 59) 8)) →
      Y.cpu.rip = isp_at → Y.cpu.gpr = (gM V X.cpu.gpr).set 4 (aR X.cpu.gpr.rsp - 8) →
      (∀ (Z : State) (V' : Addr → Byte) (t'' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V' →
        Z.cpu.rip = ain_at.add 59 → Z.cpu.gpr.rsp = aR X.cpu.gpr.rsp → Z.cpu.gpr.rbx = X.cpu.gpr.rdx →
        Z.cpu.gpr.rbp = X.cpu.gpr.rdi → Z.cpu.gpr.r12 = BitVec.setWidth 64 (ln V X.cpu.gpr) → Pc1 Z V' →
        GoG prof L o gev gP gE Z t'') →
      GoG prof L o gev gP gE Y t')
    (kf2 : ∀ (Z : State) (V' : Addr → Byte), Z.cpu.gpr.rsp = aR X.cpu.gpr.rsp → Z.cpu.gpr.rbx = X.cpu.gpr.rdx →
      Z.cpu.gpr.rbp = X.cpu.gpr.rdi → Z.cpu.gpr.r12 = BitVec.setWidth 64 (ln V X.cpu.gpr) → Pc1 Z V' →
      ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y →
      Agree F Y.proc.mm.mem (Vst V' (aR X.cpu.gpr.rsp - 8) (toBytesLE (ain_at.add 78) 8)) →
      Y.cpu.rip = plt_memcpy → Y.cpu.gpr = (g59 Z.cpu.gpr V').set 4 (aR X.cpu.gpr.rsp - 8) →
      (∀ (Z₂ : State) (V₂ : Addr → Byte) (t'' : Nat), KeptW Wl s₀ Z₂ → Agree F Z₂.proc.mm.mem V₂ →
        Z₂.cpu.rip = ain_at.add 78 → Z₂.cpu.gpr.rsp = aR X.cpu.gpr.rsp → Z₂.cpu.gpr.rbp = X.cpu.gpr.rdi →
        Z₂.cpu.gpr.r12 = BitVec.setWidth 64 (ln V X.cpu.gpr) →
        rdq(V₂, X.cpu.gpr.rsp - 8 - 8 - 8) = X.cpu.gpr.rbx → rdq(V₂, X.cpu.gpr.rsp - 8 - 8) = X.cpu.gpr.rbp →
        rdq(V₂, X.cpu.gpr.rsp - 8) = X.cpu.gpr.r12 → rdq(V₂, X.cpu.gpr.rsp) = e₂.add j₂ → Pc2 Z₂ V₂ →
        GoG prof L o gev gP gE Z₂ t'') →
      GoG prof L o gev gP gE Y t')
    (kr : ∀ (Z₂ : State) (V₂ : Addr → Byte) (Z' : State) (t' : Nat), Pc2 Z₂ V₂ → KeptW Wl s₀ Z' →
      Agree F Z'.proc.mm.mem
        (Vst V₂ (X.cpu.gpr.rdi + 8#64) (toBytesLE (rdd(V₂, X.cpu.gpr.rdi + 8#64) + ln V X.cpu.gpr) 4)) →
      Z'.cpu.rip = e₂.add j₂ →
      Z'.cpu.gpr = { Z₂.cpu.gpr with
        rbx := X.cpu.gpr.rbx, rbp := X.cpu.gpr.rbp, rsp := X.cpu.gpr.rsp + 8, r12 := X.cpu.gpr.r12 } →
      GoG prof L o gev gP gE Z' t') :
    GoG prof L o gev gP gE X t := by
  have hlt := X.cpu.gpr.rsp.isLt
  have h24 : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rsp - 8 - 8 - 8) i) := fun i hi => c.hws _ (hs3 i hi)
  have h16 : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rsp - 8 - 8) i) := fun i hi => c.hws _ (hs2 i hi)
  have h8 : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rsp - 8) i) := fun i hi => c.hws _ (hs1 i hi)
  have f12 : ∀ i < 4, Foot F.data (Addr.add (aR X.cpu.gpr.rsp + 12#64) i) := fun i hi => c.hws _ (hw4 i hi)
  have hx := hxl V X.cpu.gpr hp hq1 hd1
  have hrip' : X.cpu.rip = ain_at.add 0 := by rw [addr_add_zero]; exact hrip
  by_cases h0 : ln V X.cpu.gpr = 0
  · -- `s._len` 0: to the `ret` at 33
    have hz : (ln V X.cpu.gpr == 0) = true := beq_iff_eq.2 h0
    have hra0 : rdq(V0 V X.cpu.gpr, X.cpu.gpr.rsp) = e₂.add j₂ := (rd_ra V X.cpu.gpr hp hp8).trans hra
    refine (c_0 prof).run c hin (fun j' g' _ V' => j' = 33 ∧
        g' = { X.cpu.gpr with
          rbx := X.cpu.gpr.rbx, rbp := X.cpu.gpr.rbp, rsp := X.cpu.gpr.rsp, r12 := X.cpu.gpr.r12 } ∧
        V' = V0 V X.cpu.gpr) hK hA hrip'
      (vc_z hz hs1 hs2 hs3 fl hw4 (by rw [aE1]; exact h24) (by rw [aE1, aE2]; exact h16)
        (by rw [aE1, aE2, aE3]; exact h8) hx
        fun _ => ⟨rfl, by
          rw [aE1, aE2, aE3, aE4, rd_rbx V X.cpu.gpr hp, rd_rbp V X.cpu.gpr hp, rd_r12 V X.cpu.gpr hp], rfl⟩) ?_
    rintro j' g fl₁ V₁ ⟨rfl, rfl, hV₁⟩ Y t₁ hKY hAY hrY hgY -
    subst V₁
    have hsY : Y.cpu.gpr.rsp = X.cpu.gpr.rsp := by rw [hgY]
    refine c.s_ret hKY hAY hin (lt_len (by decide)) hrY (ret_33 _) (by rw [hsY]; exact hl) hin₂ h₂
      (by rw [hsY]; exact hra0) ?_
    rintro Z t' hKZ hAZ ⟨hrZ, hgZ⟩
    refine kn h0 Z t' hKZ hAZ hrZ ?_
    rw [hgZ, hgY]
    try rfl
  · -- `s._len` not 0: to the `call` of `InsertSpace`
    have hz : (ln V X.cpu.gpr == 0) = false := beq_eq_false_iff_ne.2 h0
    refine (c_0 prof).run c hin (fun j' g' _ V' => j' = 54 ∧ g' = gM V X.cpu.gpr ∧ V' = V0 V X.cpu.gpr) hK hA hrip'
      (vc_nz hz hs1 hs2 hs3 fl hw4 hx fun _ => ⟨rfl, rfl, rfl⟩) ?_
    rintro j' g fl₁ V₁ ⟨rfl, rfl, hV₁⟩ Y t₁ hKY hAY hrY hgY -
    subst V₁
    have hsY : Y.cpu.gpr.rsp = aR X.cpu.gpr.rsp := by rw [hgY]
    refine c.s_call hKY hAY hin (lt_len (by decide)) hrY (call_54 _) hinI hI tgt_54 (by rw [hsY]; exact hs5) ?_
    rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
    rw [hsY] at hA₂
    have hg₂' : Y₂.cpu.gpr = (gM V X.cpu.gpr).set 4 (aR X.cpu.gpr.rsp - 8) := by rw [hg₂, hsY, hgY]
    refine kf1 h0 Y₂ t₂ hK₂ hA₂ hr₂ hg₂' ?_
    -- back from `InsertSpace`, at 59: to the `call` of `memcpy`
    intro Z V' t'' hKZ hAZ hrZ hzs hzb hzp hz12 hP1
    refine (c_59 prof).run c hin (fun j' g' _ V'' => j' = 73 ∧ g' = g59 Z.cpu.gpr V' ∧ V'' = V') hKZ hAZ hrZ
      (vc_59 (by rw [hzb]; exact fb) (by rw [hzs]; exact f12) (by rw [hzp]; exact fc) fun _ => ⟨rfl, rfl, rfl⟩) ?_
    rintro j' g fl₂ V₂ ⟨rfl, rfl, hV₂⟩ U t₃ hKU hAU hrU hgU -
    subst V₂
    have hsU : U.cpu.gpr.rsp = aR X.cpu.gpr.rsp := by rw [hgU]; exact hzs
    refine c.s_call hKU hAU hin (lt_len (by decide)) hrU (call_73 _) hinM hM tgt_73 (by rw [hsU]; exact hs5) ?_
    rintro U₂ t₄ hK₄ hA₄ ⟨hr₄, hg₄⟩
    rw [hsU] at hA₄
    have hg₄' : U₂.cpu.gpr = (g59 Z.cpu.gpr V').set 4 (aR X.cpu.gpr.rsp - 8) := by rw [hg₄, hsU, hgU]
    refine kf2 Z V' hzs hzb hzp hz12 hP1 U₂ t₄ hK₄ hA₄ hr₄ hg₄' ?_
    -- back from `memcpy`, at 78: the `add`
    intro Z₂ V₂ t₅ hKZ₂ hAZ₂ hrZ₂ hz2s hz2p hz2r q1 q2 q3 qr hP2
    have hea : eaD Z₂ 5 8 = X.cpu.gpr.rdi + 8#64 := by
      show Z₂.cpu.gpr.get (regOf 5) + BitVec.ofNat 64 8 = _
      rw [show Z₂.cpu.gpr.get (regOf 5) = Z₂.cpu.gpr.rbp from rfl, hz2p]
    have hrv : rv Z₂ 32 12 = ln V X.cpu.gpr := by
      show (Z₂.cpu.gpr.get (regOf 12)).setWidth 32 = _
      rw [show Z₂.cpu.gpr.get (regOf 12) = Z₂.cpu.gpr.r12 from rfl, hz2r, sw_64_32]
    refine c.s_add_mr32 hKZ₂ hAZ₂ hin (lt_len (by decide)) hrZ₂ (add_78 _) (by rw [hea]; exact fw) ?_
    rintro U₃ t₆ hKU₃ hAU₃ ⟨hrU₃, hgU₃⟩
    rw [hea, hrv] at hAU₃
    -- the bytes outside `_len`
    have t8 := aT8 X.cpu.gpr.rsp hp
    have t16 := aT16 X.cpu.gpr.rsp hp
    have t24 := aT24 X.cpu.gpr.rsp hp
    have tr := aTr8 X.cpu.gpr.rdi hq2
    have m2 : ∀ (x : Addr), x.toNat + 8 ≤ 2 ^ 64 →
        (x.toNat + 8 ≤ X.cpu.gpr.rdi.toNat + 8 ∨ X.cpu.gpr.rdi.toNat + 12 ≤ x.toNat) →
        (byteAddrs x 8).map
          (Vst V₂ (X.cpu.gpr.rdi + 8#64) (toBytesLE (rdd(V₂, X.cpu.gpr.rdi + 8#64) + ln V X.cpu.gpr) 4)) =
        (byteAddrs x 8).map V₂ := by
      intro x hx h
      exact Tun.rd_Vst V₂ (X.cpu.gpr.rdi + 8#64)
        (toBytesLE (rdd(V₂, X.cpu.gpr.rdi + 8#64) + ln V X.cpu.gpr) 4) x 8
        (by rw [toBytesLE_length, tr]; omega) hx (by rw [toBytesLE_length, tr]; omega)
    have hc1' := m2 (X.cpu.gpr.rsp - 8 - 8 - 8) (by rw [t24]; omega) (by rw [t24]; omega)
    have hc2' := m2 (X.cpu.gpr.rsp - 8 - 8) (by rw [t16]; omega) (by rw [t16]; omega)
    have hc3' := m2 (X.cpu.gpr.rsp - 8) (by rw [t8]; omega) (by rw [t8]; omega)
    have hcr' := m2 X.cpu.gpr.rsp hp8 (by omega)
    have hrU₃' : U₃.cpu.rip = ain_at.add 82 := hrU₃
    -- the epilogue at 82, then the `ret` at 90
    refine (c_82 prof).run c hin (fun j' g' _ V₃ => j' = 90 ∧
        g' = { Z₂.cpu.gpr with
          rbx := X.cpu.gpr.rbx, rbp := X.cpu.gpr.rbp, rsp := X.cpu.gpr.rsp, r12 := X.cpu.gpr.r12 } ∧
        V₃ = Vst V₂ (X.cpu.gpr.rdi + 8#64) (toBytesLE (rdd(V₂, X.cpu.gpr.rdi + 8#64) + ln V X.cpu.gpr) 4))
      hKU₃ hAU₃ hrU₃'
      (vc_82 (by rw [hgU₃, hz2s, aE1]; exact h24) (by rw [hgU₃, hz2s, aE1, aE2]; exact h16)
        (by rw [hgU₃, hz2s, aE1, aE2, aE3]; exact h8)
        fun _ => ⟨rfl, by rw [hgU₃, hz2s, aE1, aE2, aE3, aE4, hc1', hc2', hc3', q1, q2, q3], rfl⟩) ?_
    rintro j' g fl₃ V₄ ⟨rfl, rfl, hV₄⟩ U₄ t₇ hKU₄ hAU₄ hrU₄ hgU₄ -
    subst V₄
    have hsU₄ : U₄.cpu.gpr.rsp = X.cpu.gpr.rsp := by rw [hgU₄]
    refine c.s_ret hKU₄ hAU₄ hin (lt_len (by decide)) hrU₄ (ret_90 _) (by rw [hsU₄]; exact hl) hin₂ h₂
      (by rw [hsU₄, hcr']; exact qr) ?_
    rintro Z' t₈ hKZ' hAZ' ⟨hrZ', hgZ'⟩
    refine kr Z₂ V₂ Z' t₈ hP2 hKZ' hAZ' hrZ' ?_
    rw [hgZ', hgU₄]
    try rfl

end FV7z.Ain
