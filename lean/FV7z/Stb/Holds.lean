import FV7z.Stb.Cuts
import FV7z.Lemmas.LeafRet
import FV7z.Lemmas.BlkOps4
import FV7z.Tun.Inv
import FV7z.Cxa.Holds
import FV7z.Sas.Holds
/-!
# `_IO_setb` (PLAN.md §M, M1)

glibc 2.31's `_IO_setb (f, b, eb, a)` at `0x62b4a0` in `7zzs` (`libio/genops.c`): `push rbp; mov ebp, ecx; push rbx;
mov rbx, rdi; sub rsp, 24`, `rdi` = `f->_IO_buf_base` (`[f + 0x38]`), `eax` = `f->_flags` (`[f]`), `b` and `eb` kept at
`[rsp]`, `[rsp + 8]`. The old buffer not null and `_IO_USER_BUF` (bit 0) clear: `free` of it (the `call` at 80 to
`0x633750`), then the flags read again (85, `jmp` to 39). At 39: `edx` = `eax`, `movq xmm0, [rsp]`; `eax | 1` or, `a`
not 0 (`cmovne`), `edx & ~1`; `movhps xmm0, [rsp + 8]`; `movups [rbx + 0x38], xmm0` (`_IO_buf_base` = `b`,
`_IO_buf_end` = `eb`); `[rbx]` = `eax`; the registers popped, the `ret` at 74.

`free` is a hypothesis, as the callees of `FV7z/Vcl/Holds.lean` and `FV7z/Sas/Holds.lean`: a continuation at its entry
(`kf`), given the run from its return (the frame as it was, its own post `Pf`) to the return address.

- `fw a x`: the flags word stored: `x | 1` when `a` is 0, else `x & ~1`. `Vfin`: the bytes at the end (the two
  pointers, then the flags word).
- `Vp`, `G1`, `V1`: the bytes with `rbp`, `rbx` pushed, the registers and bytes at 39 or 80. `G46`: the registers
  after `or; and; test; cmovne`.
- `stb_t`: from 39 to the return address, for the frame at `r` (`b`, `eb` at `r`, `r + 8`; the saved `rbx`, `rbp`
  and the return address at `r + 24`, `r + 32`, `r + 40`).
- `stb_ok`: from the entry.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Stb

/-- The `call` of `free`. -/
def pcall : List Byte := [0xe8, 0x5b, 0x82, 0x00, 0x00]
theorem pcall_0 : ∀ feat, Dec feat pcall 0 (FV7z.mk .call 64 [.rel 33371] 5) := by dec_rfl
theorem wc_80 : pcall <+: stb.drop 80 := by decide +kernel
theorem call_80 (feat : Features) : Dec feat stb 80 (FV7z.mk .call 64 [.rel 33371] 5) :=
  Dec.shift (j := 80) (k := 0) (pcall_0 feat) wc_80 (Nat.zero_le _)

/-- The `ret`. -/
def pret : List Byte := [0xc3]
theorem pret_0 : ∀ feat, Dec feat pret 0 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem w_74 : pret <+: stb.drop 74 := by decide +kernel
theorem ret_74 (feat : Features) : Dec feat stb 74 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 74) (k := 0) (pret_0 feat) w_74 (Nat.zero_le _)

/-- The moves of `xmm0`. -/
def pmq : List Byte := [0xf3, 0x0f, 0x7e, 0x04, 0x24]
theorem pmq_0 : ∀ feat, Dec feat pmq 0 (FV7z.mk (.sse .movq) 32 [.xmm 0, .mem (mbd 4 0 64)] 5) := by dec_rfl
theorem w_41 : pmq <+: stb.drop 41 := by decide +kernel
theorem movq_41 (feat : Features) : Dec feat stb 41 (FV7z.mk (.sse .movq) 32 [.xmm 0, .mem (mbd 4 0 64)] 5) :=
  Dec.shift (j := 41) (k := 0) (pmq_0 feat) w_41 (Nat.zero_le _)
def pmh : List Byte := [0x0f, 0x16, 0x44, 0x24, 0x08]
theorem pmh_0 : ∀ feat, Dec feat pmh 0 (FV7z.mk (.sse .movhps) 32 [.xmm 0, .mem (mbd 4 8 64)] 5) := by dec_rfl
theorem w_57 : pmh <+: stb.drop 57 := by decide +kernel
theorem movhps_57 (feat : Features) :
    Dec feat stb 57 (FV7z.mk (.sse .movhps) 32 [.xmm 0, .mem (mbd 4 8 64)] 5) :=
  Dec.shift (j := 57) (k := 0) (pmh_0 feat) w_57 (Nat.zero_le _)
def pmu : List Byte := [0x0f, 0x11, 0x43, 0x38]
theorem pmu_0 : ∀ feat, Dec feat pmu 0 (FV7z.mk (.sse .movups) 32 [.mem (mbd 3 56 128), .xmm 0] 4) := by dec_rfl
theorem w_62 : pmu <+: stb.drop 62 := by decide +kernel
theorem movups_62 (feat : Features) :
    Dec feat stb 62 (FV7z.mk (.sse .movups) 32 [.mem (mbd 3 56 128), .xmm 0] 4) :=
  Dec.shift (j := 62) (k := 0) (pmu_0 feat) w_62 (Nat.zero_le _)

/-- glibc's `free` (code not proved here). -/
abbrev fre_at : Addr := 0x633750

/-! ## Offsets -/

theorem o1 (x : Addr) : x - 8 - 8 - 24#64 = x - 40 := by bv_omega
theorem o3 (x : Addr) : x - 8 - 8 = x - 16 := by bv_omega
theorem o2 (x : Addr) : x - 40 + 8#64 = x - 32 := by bv_omega
theorem a24 (x : Addr) : x - 40 + 24#64 = x - 16 := by bv_omega
theorem a32 (x : Addr) : x - 16 + 8 = x - 8 := by bv_omega
theorem a40 (x : Addr) : x - 8 + 8 = x := by bv_omega
theorem m48 (x : Addr) : x - 40 - 8 = x - 48 := by bv_omega
theorem c32 (x : Addr) : x + 24#64 + 8 = x + 32#64 := by bv_omega
theorem c40 (x : Addr) : x + 24#64 + 8 + 8 = x + 40#64 := by bv_omega
theorem c48 (x : Addr) : x + 24#64 + 8 + 8 + 8 = x + 48 := by bv_omega
theorem f48 (x : Addr) : x - 40 + 48 = x + 8 := by bv_omega
theorem n8 (x : Addr) : x - 8 = x - 48 + BitVec.ofNat 64 40 := by bv_omega
theorem n16 (x : Addr) : x - 8 - 8 = x - 48 + BitVec.ofNat 64 32 := by bv_omega
theorem n40 (x : Addr) : x - 8 - 8 - 24#64 = x - 48 + BitVec.ofNat 64 8 := by bv_omega
theorem n32 (x : Addr) : x - 8 - 8 - 24#64 + 8#64 = x - 48 + BitVec.ofNat 64 16 := by bv_omega
theorem u8 (x : Addr) (h : 8 ≤ x.toNat) : (x - 8).toNat = x.toNat - 8 := by bv_omega
theorem u16 (x : Addr) (h : 16 ≤ x.toNat) : (x - 16).toNat = x.toNat - 16 := by bv_omega
theorem u32 (x : Addr) (h : 32 ≤ x.toNat) : (x - 32).toNat = x.toNat - 32 := by bv_omega
theorem u40 (x : Addr) (h : 40 ≤ x.toNat) : (x - 40).toNat = x.toNat - 40 := by bv_omega

/-! ## The registers and bytes at the pieces' ends -/

/-- The flags word stored: `_IO_USER_BUF` set when `a` is 0, else cleared. -/
def fw (a x : BitVec 32) : BitVec 32 := if a = 0 then x ||| 1#32 else x &&& 4294967294#32

/-- The bytes at the end: `_IO_buf_base` = `b`, `_IO_buf_end` = `e`, then the flags word `y`. -/
abbrev Vfin (V : Addr → Byte) (fp b e : BitVec 64) (y : BitVec 32) : Addr → Byte :=
  Vst (Vst (Vst V (fp + 56#64) (toBytesLE b 8)) (fp + 56#64 + 8#64) (toBytesLE e 8)) fp (toBytesLE y 4)

/-- The bytes with `rbp`, `rbx` pushed. -/
abbrev Vp (V : Addr → Byte) (g : Gprs) : Addr → Byte :=
  Vst (Vst V (g.rsp - 8) (toBytesLE g.rbp 8)) (g.rsp - 8 - 8) (toBytesLE g.rbx 8)
/-- The registers at 39 or 80, `b` the old buffer, `w` the flags. -/
abbrev G1 (g : Gprs) (b : BitVec 64) (w : BitVec 32) : Gprs :=
  { g with rbp := (g.rcx.setWidth 32).setWidth 64, rbx := g.rdi, rsp := g.rsp - 8 - 8 - 24#64, rdi := b,
    rax := w.setWidth 64 }
/-- The bytes at 39 or 80: `b`, `eb` kept. -/
abbrev V1 (V : Addr → Byte) (g : Gprs) : Addr → Byte :=
  Vst (Vst (Vp V g) (g.rsp - 8 - 8 - 24#64) (toBytesLE g.rsi 8)) (g.rsp - 8 - 8 - 24#64 + 8#64) (toBytesLE g.rdx 8)
/-- The registers after `or eax, 1; and edx, ~1; test ebp, ebp; cmovne eax, edx`. -/
abbrev G46 (g : Gprs) : Gprs :=
  { g with rax := (fw (g.rbp.setWidth 32) (g.rax.setWidth 32)).setWidth 64,
    rdx := (g.rax.setWidth 32 &&& 4294967294#32).setWidth 64 }
/-- The old buffer and the flags at the entry. -/
abbrev bv (V : Addr → Byte) (g : Gprs) : BitVec 64 := rdq(V, g.rdi + 56#64)
abbrev wv (V : Addr → Byte) (g : Gprs) : BitVec 32 := ofBytesLE 32 ((byteAddrs g.rdi 4).map V)

/-- The end's stores keep the bytes of the frame. -/
theorem rd_fin {V : Addr → Byte} {fp z : Addr} (b e : BitVec 64) (y : BitVec 32) (hfp : fp.toNat + 72 ≤ 2 ^ 64)
    (hz : z.toNat + 8 ≤ 2 ^ 64) (hd : fp.toNat + 72 ≤ z.toNat ∨ z.toNat + 8 ≤ fp.toNat) :
    rdq(Vfin V fp b e y, z) = rdq(V, z) := by
  have t56 : (fp + 56#64).toNat = fp.toNat + 56 := Sas.tn_add fp 56 (by omega)
  have t64 : (fp + 56#64 + 8#64).toNat = fp.toNat + 64 := by
    rw [Sas.tn_add (fp + 56#64) 8 (by rw [t56]; omega), t56]
  dsimp only [Vfin]
  rw [Tun.rd_Vst _ fp (toBytesLE y 4) z 8 (by rw [toBytesLE_length]; omega) hz (by rw [toBytesLE_length]; omega),
    Tun.rd_Vst _ (fp + 56#64 + 8#64) (toBytesLE e 8) z 8 (by rw [toBytesLE_length, t64]; omega) hz
      (by rw [toBytesLE_length, t64]; omega),
    Tun.rd_Vst _ (fp + 56#64) (toBytesLE b 8) z 8 (by rw [toBytesLE_length, t56]; omega) hz
      (by rw [toBytesLE_length, t56]; omega)]

/-- The frame at 39 or 80 read back. -/
theorem v1_rd {V : Addr → Byte} {g : Gprs} (hp : 48 ≤ g.rsp.toNat) (hp8 : g.rsp.toNat + 8 ≤ 2 ^ 64) :
    rdq(V1 V g, g.rsp - 40) = g.rsi ∧ rdq(V1 V g, g.rsp - 40 + 8#64) = g.rdx ∧
      rdq(V1 V g, g.rsp - 40 + 24#64) = g.rbx ∧ rdq(V1 V g, g.rsp - 40 + 24#64 + 8) = g.rbp ∧
      rdq(V1 V g, g.rsp - 40 + 24#64 + 8 + 8) = rdq(V, g.rsp) := by
  have t8 := u8 g.rsp (by omega)
  have t16 := u16 g.rsp (by omega)
  have t32 := u32 g.rsp (by omega)
  have t40 := u40 g.rsp (by omega)
  dsimp only [V1, Vp]
  rw [o1, o3, o2, a24, a32, a40]
  have l8 : ∀ v : BitVec 64, (toBytesLE v 8).length = 8 := fun v => toBytesLE_length v 8
  have d : ∀ (a z : Addr) (v : BitVec 64), a.toNat + 8 ≤ 2 ^ 64 → z.toNat + 8 ≤ 2 ^ 64 →
      (a.toNat + 8 ≤ z.toNat ∨ z.toNat + 8 ≤ a.toNat) → ∀ W : Addr → Byte,
      rdq(Vst W a (toBytesLE v 8), z) = rdq(W, z) := fun a z v ha hz h W => by
    rw [Tun.rd_Vst W a (toBytesLE v 8) z 8 (by rw [l8]; exact ha) hz (by rw [l8]; exact h)]
  have s : ∀ (a : Addr) (v : BitVec 64), a.toNat + 8 ≤ 2 ^ 64 → ∀ W : Addr → Byte,
      rdq(Vst W a (toBytesLE v 8), a) = v := fun a v ha W => by
    rw [Tun.rd_Vst_self W a (toBytesLE v 8) (l8 v) ha, ofBytesLE_toBytesLE (n := 8) rfl]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [d (g.rsp - 32) (g.rsp - 40) g.rdx (by omega) (by omega) (by omega), s (g.rsp - 40) g.rsi (by omega)]
  · rw [s (g.rsp - 32) g.rdx (by omega)]
  · rw [d (g.rsp - 32) (g.rsp - 16) g.rdx (by omega) (by omega) (by omega),
      d (g.rsp - 40) (g.rsp - 16) g.rsi (by omega) (by omega) (by omega), s (g.rsp - 16) g.rbx (by omega)]
  · rw [d (g.rsp - 32) (g.rsp - 8) g.rdx (by omega) (by omega) (by omega),
      d (g.rsp - 40) (g.rsp - 8) g.rsi (by omega) (by omega) (by omega),
      d (g.rsp - 16) (g.rsp - 8) g.rbx (by omega) (by omega) (by omega), s (g.rsp - 8) g.rbp (by omega)]
  · rw [d (g.rsp - 32) g.rsp g.rdx (by omega) hp8 (by omega), d (g.rsp - 40) g.rsp g.rsi (by omega) hp8 (by omega),
      d (g.rsp - 16) g.rsp g.rbx (by omega) hp8 (by omega), d (g.rsp - 8) g.rsp g.rbp (by omega) hp8 (by omega)]

/-- The frame from `x - 40`: 40 bytes below `x` and 8 from `x`. -/
theorem fr40 {P : Addr → Prop} {x : Addr} (h1 : ∀ i < 48, P (Addr.add (x - 48) i))
    (h2 : ∀ i < 8, P (Addr.add x i)) : ∀ i < 48, P (Addr.add (x - 40) i) := fun i hi => by
  by_cases h : i < 40
  · have e : Addr.add (x - 40) i = Addr.add (x - 48) (8 + i) := by simp only [Addr.add]; bv_omega
    rw [e]; exact h1 _ (by omega)
  · have e : Addr.add (x - 40) i = Addr.add x (i - 40) := by simp only [Addr.add]; bv_omega
    rw [e]; exact h2 _ (by omega)

variable {F : Footprint} {Wl : List Rgn}

/-! ## The verification conditions -/

/-- From the entry, the old buffer null: to 39. -/
theorem vc_0a {g : Gprs} {f : Rflags} {V : Addr → Byte} {b : BitVec 64} {w : BitVec 32}
    (h1 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8) i)) (h2 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8) i))
    (l1 : ∀ i < 8, Foot F.data (Addr.add (g.rdi + 56#64) i)) (l2 : ∀ i < 4, Foot F.data (Addr.add g.rdi i))
    (s1 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8 - 24#64) i))
    (s2 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8 - 24#64 + 8#64) i))
    (hb : rdq(Vp V g, g.rdi + 56#64) = b) (hw : ofBytesLE 32 ((byteAddrs g.rdi 4).map (Vp V g)) = w)
    (hb0 : b = 0) :
    W_0 F Wl (fun j' g' _ V' => j' = 39 ∧ g' = G1 g b w ∧ V' = V1 V g) g f V := by
  subst hb0
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h1 h2 l1 l2 s1 s2 hb hw ⊢
  revert hb hw
  wpx [W_0, W_35, o0, o1, Vp, G1, V1]
  intro hb hw
  wpx [hb, hw, BitVec.and_self, beq_self_eq_true, Bool.false_eq_true, Bool.true_eq_false, eq_self_iff_true,
    false_implies, implies_true]
  all_goals repeat'
    first
    | exact rfl
    | assumption
    | exact trivial
    | (intro h; exact absurd h (by decide))
    | apply And.intro
    | intro _

/-- From the entry, the old buffer not null and `_IO_USER_BUF` set: to 39. -/
theorem vc_0b {g : Gprs} {f : Rflags} {V : Addr → Byte} {b : BitVec 64} {w : BitVec 32}
    (h1 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8) i)) (h2 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8) i))
    (l1 : ∀ i < 8, Foot F.data (Addr.add (g.rdi + 56#64) i)) (l2 : ∀ i < 4, Foot F.data (Addr.add g.rdi i))
    (s1 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8 - 24#64) i))
    (s2 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8 - 24#64 + 8#64) i))
    (hb : rdq(Vp V g, g.rdi + 56#64) = b) (hw : ofBytesLE 32 ((byteAddrs g.rdi 4).map (Vp V g)) = w)
    (hb0 : b ≠ 0) (hf : w.setWidth 8 &&& 1#8 ≠ 0) :
    W_0 F Wl (fun j' g' _ V' => j' = 39 ∧ g' = G1 g b w ∧ V' = V1 V g) g f V := by
  have hb0' : (b == 0) = false := by simp [hb0]
  have hf' : (w.setWidth 8 &&& 1#8 == 0) = false := by simp [hf]
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h1 h2 l1 l2 s1 s2 hb hw ⊢
  revert hb hw
  wpx [W_0, W_35, o0, o1, Vp, G1, V1]
  intro hb hw
  wpx [hb, hw, hb0', hf', BitVec.and_self, Bool.false_eq_true, Bool.true_eq_false, eq_self_iff_true,
    false_implies, implies_true]
  all_goals repeat'
    first
    | exact rfl
    | assumption
    | exact trivial
    | (intro h; exact absurd h (by decide))
    | apply And.intro
    | intro _

/-- From the entry, the old buffer not null and `_IO_USER_BUF` clear: to the `call` of `free` at 80. -/
theorem vc_0c {g : Gprs} {f : Rflags} {V : Addr → Byte} {b : BitVec 64} {w : BitVec 32}
    (h1 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8) i)) (h2 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8) i))
    (l1 : ∀ i < 8, Foot F.data (Addr.add (g.rdi + 56#64) i)) (l2 : ∀ i < 4, Foot F.data (Addr.add g.rdi i))
    (s1 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8 - 24#64) i))
    (s2 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8 - 24#64 + 8#64) i))
    (hb : rdq(Vp V g, g.rdi + 56#64) = b) (hw : ofBytesLE 32 ((byteAddrs g.rdi 4).map (Vp V g)) = w)
    (hb0 : b ≠ 0) (hf : w.setWidth 8 &&& 1#8 = 0) :
    W_0 F Wl (fun j' g' _ V' => j' = 80 ∧ g' = G1 g b w ∧ V' = V1 V g) g f V := by
  have hb0' : (b == 0) = false := by simp [hb0]
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h1 h2 l1 l2 s1 s2 hb hw ⊢
  revert hb hw
  wpx [W_0, W_35, o0, o1, Vp, G1, V1]
  intro hb hw
  wpx [hb, hw, hb0', hf, beq_self_eq_true, BitVec.and_self, Bool.false_eq_true, Bool.true_eq_false,
    eq_self_iff_true, false_implies, implies_true]
  all_goals repeat'
    first
    | exact rfl
    | assumption
    | exact trivial
    | (intro h; exact absurd h (by decide))
    | apply And.intro
    | intro _

/-- From 39: `mov edx, eax` to the `movq` at 41. -/
theorem vc_39 {g : Gprs} {f : Rflags} {V : Addr → Byte} :
    W_39 F Wl (fun j' g' _ V' => j' = 41 ∧ g' = { g with rdx := (g.rax.setWidth 32).setWidth 64 } ∧ V' = V)
      g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_39, o2]
  all_goals repeat' (first | exact rfl | exact trivial | apply And.intro | intro _)

/-- From 46, `edx` = `eax`: `or eax, 1; and edx, ~1; test ebp, ebp; cmovne eax, edx`. -/
theorem vc_46 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Gprs → Rflags → (Addr → Byte) → Prop}
    (hd : g.rdx = (g.rax.setWidth 32).setWidth 64) (hQ : ∀ fl, Q (G46 g) fl V) : wp F Wl o3 Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hd hQ
  subst hd
  dsimp only [G46] at hQ
  by_cases hz : rbp.setWidth 32 = 0
  · have hz' : (rbp.setWidth 32 == 0) = true := by simp [hz]
    rw [fw, if_pos hz] at hQ
    wpx [o3, hz', BitVec.and_self, Bool.not_true, Bool.false_eq_true, if_false, ↓reduceIte]
    all_goals repeat' (first | exact hQ _ | exact rfl | exact trivial | apply And.intro | intro _)
  · have hz' : (rbp.setWidth 32 == 0) = false := by simp [hz]
    rw [fw, if_neg hz] at hQ
    wpx [o3, hz', BitVec.and_self, Bool.not_false, if_true, ↓reduceIte]
    all_goals repeat' (first | exact hQ _ | exact rfl | exact trivial | apply And.intro | intro _)

/-- From 66: `mov [rbx], eax; add rsp, 24; pop rbx; pop rbp` to the `ret` at 74. -/
theorem vc_66 {g : Gprs} {f : Rflags} {V : Addr → Byte} (hw : ∀ i < 4, Foot Wl (Addr.add g.rbx i))
    (l0 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 24#64) i))
    (l1 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 24#64 + 8) i)) :
    W_66 F Wl (fun j' g' _ V' => j' = 74 ∧
      g' = { g with
        rbx := rdq(Vst V g.rbx (toBytesLE (g.rax.setWidth 32) 4), g.rsp + 24#64),
        rbp := rdq(Vst V g.rbx (toBytesLE (g.rax.setWidth 32) 4), g.rsp + 24#64 + 8),
        rsp := g.rsp + 24#64 + 8 + 8 } ∧
      V' = Vst V g.rbx (toBytesLE (g.rax.setWidth 32) 4)) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hw l0 l1 ⊢
  wpx [W_66, o4]
  all_goals repeat' (first | exact rfl | assumption | exact trivial | apply And.intro | intro _)

/-- From the return of `free` (85): `mov eax, [rbx]`, the `jmp` to 39. -/
theorem vc_85 {g : Gprs} {f : Rflags} {V : Addr → Byte} (l : ∀ i < 4, Foot F.data (Addr.add g.rbx i)) :
    W_85 F Wl (fun j' g' _ V' => j' = 39 ∧
      g' = { g with rax := (ofBytesLE 32 ((byteAddrs g.rbx 4).map V)).setWidth 64 } ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at l ⊢
  wpx [W_85, o5]
  all_goals repeat' (first | exact rfl | assumption | exact trivial | apply And.intro | intro _)

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}

/-! ## The pieces -/

/-- From 39 to the return address, for the frame at `r` and `f` at `fp`: the two pointers and the flags word stored,
`rbx`, `rbp` popped. -/
theorem stb_t (c : Seg prof F Wl L s₀ o) (hin : CodeIn L stb_at stb) {Z : State} {t : Nat} {V : Addr → Byte}
    (hK : KeptW Wl s₀ Z) (hA : Agree F Z.proc.mm.mem V) (hrip : Z.cpu.rip = stb_at.add 39)
    {r fp rf : Addr} (hr : Z.cpu.gpr.rsp = r) (hfb : Z.cpu.gpr.rbx = fp) (hrf : r + 48 = rf)
    {a x : BitVec 32} (ha : Z.cpu.gpr.rbp.setWidth 32 = a) (hx : Z.cpu.gpr.rax.setWidth 32 = x)
    (hp : r.toNat + 48 ≤ 2 ^ 64) (hl : ∀ i < 48, Foot F.data (Addr.add r i))
    (hfw : ∀ i < 72, Foot Wl (Addr.add fp i)) (hfp : fp.toNat + 72 ≤ 2 ^ 64)
    (hdj : fp.toNat + 72 ≤ r.toNat ∨ r.toNat + 48 ≤ fp.toNat)
    {bb be b3 b5 : BitVec 64} (hb0 : rdq(V, r) = bb) (hb1 : rdq(V, r + 8#64) = be) (hb3 : rdq(V, r + 24#64) = b3)
    (hb5 : rdq(V, r + 24#64 + 8) = b5)
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (hra : rdq(V, r + 24#64 + 8 + 8) = e₂.add j₂)
    (k : ∀ (Z' : State) (t' : Nat), KeptW Wl s₀ Z' → Agree F Z'.proc.mm.mem (Vfin V fp bb be (fw a x)) →
      Z'.cpu.rip = e₂.add j₂ →
      Z'.cpu.gpr = { Z.cpu.gpr with
        rax := (fw a x).setWidth 64, rdx := (x &&& 4294967294#32).setWidth 64, rbx := b3, rbp := b5, rsp := rf } →
      GoG prof L o gev gP gE Z' t') :
    GoG prof L o gev gP gE Z t := by
  subst ha hx
  have t24 : (r + 24#64).toNat = r.toNat + 24 := Sas.tn_add r 24 (by omega)
  have t32 : (r + 24#64 + 8).toNat = r.toNat + 32 := by rw [c32]; exact Sas.tn_add r 32 (by omega)
  have t40 : (r + 24#64 + 8 + 8).toNat = r.toNat + 40 := by rw [c40]; exact Sas.tn_add r 40 (by omega)
  -- `mov edx, eax`
  refine (c_39 prof).run c hin (fun j' g' _ V' => j' = 41 ∧
      g' = { Z.cpu.gpr with rdx := (Z.cpu.gpr.rax.setWidth 32).setWidth 64 } ∧ V' = V) hK hA hrip vc_39 ?_
  rintro j' g fl V₁ ⟨rfl, rfl, hV⟩ Y₁ t₁ hK₁ hA₁ hr₁ hg₁ -
  subst V₁
  have hs₁ : Y₁.cpu.gpr.rsp = r := by rw [hg₁]; exact hr
  -- `movq xmm0, [rsp]`
  have e0 : eaD Y₁ 4 0 = r := by
    show Y₁.cpu.gpr.rsp + 0#64 = r
    rw [hs₁]
    exact BitVec.add_zero r
  refine c.s_movq_ld hK₁ hA₁ hin (lt_len (by decide)) hr₁ (movq_41 _)
    (by rw [e0]; exact fun i hi => hl i (by omega)) ?_
  rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂, hx₂⟩
  rw [e0, hb0] at hx₂
  -- `or eax, 1; and edx, ~1; test ebp, ebp; cmovne eax, edx`
  refine c.s_blkA_v hin ((blk_46 prof).at stb_at) Y₂.cpu.vec hK₂ hA₂ hr₂ rfl rfl
    (vc_46 (by rw [hg₂, hg₁] <;> rfl) ?_)
  intro fl Y₃ t₃ hK₃ hA₃ hr₃ hg₃ _ hv₃
  have hs₃ : Y₃.cpu.gpr.rsp = r := by rw [hg₃, hg₂]; exact hs₁
  -- `movhps xmm0, [rsp + 8]`
  have e8 : eaD Y₃ 4 8 = r + 8#64 := by
    show Y₃.cpu.gpr.rsp + 8#64 = _
    rw [hs₃]
  refine c.s_movhps_ld hK₃ hA₃ hin (lt_len (by decide)) hr₃ (movhps_57 _)
    (by rw [e8]; exact Sas.ft hl 8 8 (by decide)) ?_
  rintro Y₄ t₄ hK₄ hA₄ ⟨hr₄, hg₄, hx₄⟩
  have hx₃ : xlo Y₃ 0 = bb.setWidth 128 := by
    show (Y₃.cpu.vec.zmm (xmmOf 0)).setWidth 128 = _
    rw [hv₃]
    exact hx₂
  rw [e8, hb1, hx₃, Cxa.lane_lo] at hx₄
  -- `movups [rbx + 0x38], xmm0`
  have e5 : Y₄.cpu.gpr = G46 { Z.cpu.gpr with rdx := (Z.cpu.gpr.rax.setWidth 32).setWidth 64 } := by
    rw [hg₄, hg₃, hg₂, hg₁]
  have hx5 : Y₄.cpu.gpr.rbx = fp := by rw [e5]; exact hfb
  have e56 : eaD Y₄ 3 56 = fp + 56#64 := by
    show Y₄.cpu.gpr.rbx + 56#64 = _
    rw [hx5]
  refine c.s_movups_st hK₄ hA₄ hin (lt_len (by decide)) hr₄ (movups_62 _)
    (by rw [e56]; exact Sas.ft hfw 56 16 (by decide)) ?_
  rintro Y₅ t₅ hK₅ hA₅ ⟨hr₅, hg₅⟩
  rw [e56, hx₄, Cxa.st16] at hA₅
  -- `mov [rbx], eax; add rsp, 24; pop rbx; pop rbp`
  have e6 : Y₅.cpu.gpr = G46 { Z.cpu.gpr with rdx := (Z.cpu.gpr.rax.setWidth 32).setWidth 64 } := by
    rw [hg₅, e5]
  have hs5 : Y₅.cpu.gpr.rsp = r := by rw [e6]; exact hr
  have hb5' : Y₅.cpu.gpr.rbx = fp := by rw [e6]; exact hfb
  have ha5 : Y₅.cpu.gpr.rax.setWidth 32 = fw (Z.cpu.gpr.rbp.setWidth 32) (Z.cpu.gpr.rax.setWidth 32) := by
    rw [e6]; exact sw_64_32 _
  refine (c_66 prof).run c hin _ hK₅ hA₅ hr₅
    (vc_66 (by rw [hb5']; exact fun i hi => hfw i (by omega)) (by rw [hs5]; exact Sas.ft hl 24 8 (by decide))
      (by rw [hs5, c32]; exact Sas.ft hl 32 8 (by decide))) ?_
  rintro j' g fl V₆ ⟨rfl, rfl, hV⟩ Y t₆ hKY hAY hrY hgY -
  subst V₆
  rw [hb5', ha5] at hAY
  have hsY : Y.cpu.gpr.rsp = r + 24#64 + 8 + 8 := by
    rw [hgY]
    show Y₅.cpu.gpr.rsp + 24#64 + 8 + 8 = _
    rw [hs5]
  have q3 : rdq(Vfin V fp bb be (fw (Z.cpu.gpr.rbp.setWidth 32) (Z.cpu.gpr.rax.setWidth 32)), r + 24#64) = b3 :=
    (rd_fin _ _ _ hfp (by rw [t24]; omega) (by rw [t24]; omega)).trans hb3
  have q5 : rdq(Vfin V fp bb be (fw (Z.cpu.gpr.rbp.setWidth 32) (Z.cpu.gpr.rax.setWidth 32)), r + 24#64 + 8) = b5 :=
    (rd_fin _ _ _ hfp (by rw [t32]; omega) (by rw [t32]; omega)).trans hb5
  have q6 : rdq(Vfin V fp bb be (fw (Z.cpu.gpr.rbp.setWidth 32) (Z.cpu.gpr.rax.setWidth 32)),
      r + 24#64 + 8 + 8) = e₂.add j₂ :=
    (rd_fin _ _ _ hfp (by rw [t40]; omega) (by rw [t40]; omega)).trans hra
  refine c.s_ret hKY hAY hin (lt_len (by decide)) hrY (ret_74 _)
    (by rw [hsY, c40]; exact Sas.ft hl 40 8 (by decide)) hin₂ h₂ (by rw [hsY]; exact q6) ?_
  rintro Z' t₇ hKZ hAZ ⟨hrZ, hgZ⟩
  refine k Z' t₇ hKZ hAZ hrZ ?_
  rw [hgZ, hsY, hgY, hb5', ha5, hs5, q3, q5, c48 r, hrf, e6]
  try rfl

/-- `_IO_setb (f, b, eb, a)` (`f` = `rdi`, `b` = `rsi`, `eb` = `rdx`, `a` = `ecx`) from its entry, `w` the flags word
`f->_flags` and `bv` the old buffer `f->_IO_buf_base`. The old buffer null or `_IO_USER_BUF` set (`k1`): at the return
address with `f->_IO_buf_base` = `b`, `f->_IO_buf_end` = `eb`, the flags `fw a w` (`_IO_USER_BUF` set when `a` is 0,
else cleared). Else at `free`'s entry with the registers `G1` (`rdi` the old buffer) and the return address into
`_IO_setb` pushed (`kf`); if `free` returns to `stb_at + 85` with the frame as it was and its post `Pf`, at the return
address as above, the flags word read again after `free` (`kr`). -/
theorem stb_ok {Pf : State → (Addr → Byte) → Prop} (c : Seg prof F Wl L s₀ o) (hin : CodeIn L stb_at stb)
    {cF : List Byte} (hinF : CodeIn L fre_at cF) (hF : 0 < cF.length)
    {X : State} {t : Nat} {V : Addr → Byte}
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = stb_at)
    (hp : 48 ≤ X.cpu.gpr.rsp.toNat) (hp8 : X.cpu.gpr.rsp.toNat + 8 ≤ 2 ^ 64)
    (hs : ∀ i < 48, Foot Wl (Addr.add (X.cpu.gpr.rsp - 48) i))
    (hl : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsp i))
    (hfw : ∀ i < 72, Foot Wl (Addr.add X.cpu.gpr.rdi i)) (hfp : X.cpu.gpr.rdi.toNat + 72 ≤ 2 ^ 64)
    (hdj : X.cpu.gpr.rdi.toNat + 72 ≤ X.cpu.gpr.rsp.toNat - 48 ∨ X.cpu.gpr.rsp.toNat + 8 ≤ X.cpu.gpr.rdi.toNat)
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (hra : rdq(V, X.cpu.gpr.rsp) = e₂.add j₂)
    (k1 : (bv V X.cpu.gpr = 0 ∨ (wv V X.cpu.gpr).setWidth 8 &&& 1#8 ≠ 0) → ∀ (Z : State) (t' : Nat),
      KeptW Wl s₀ Z →
      Agree F Z.proc.mm.mem (Vfin (V1 V X.cpu.gpr) X.cpu.gpr.rdi X.cpu.gpr.rsi X.cpu.gpr.rdx
        (fw (X.cpu.gpr.rcx.setWidth 32) (wv V X.cpu.gpr))) → Z.cpu.rip = e₂.add j₂ →
      Z.cpu.gpr = { G1 X.cpu.gpr (bv V X.cpu.gpr) (wv V X.cpu.gpr) with
        rax := (fw (X.cpu.gpr.rcx.setWidth 32) (wv V X.cpu.gpr)).setWidth 64,
        rdx := (wv V X.cpu.gpr &&& 4294967294#32).setWidth 64, rbx := X.cpu.gpr.rbx, rbp := X.cpu.gpr.rbp,
        rsp := X.cpu.gpr.rsp + 8 } →
      GoG prof L o gev gP gE Z t')
    (kf : bv V X.cpu.gpr ≠ 0 → (wv V X.cpu.gpr).setWidth 8 &&& 1#8 = 0 →
      ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y →
      Agree F Y.proc.mm.mem (Vst (V1 V X.cpu.gpr) (X.cpu.gpr.rsp - 48) (toBytesLE (stb_at.add 85) 8)) →
      Y.cpu.rip = fre_at → Y.cpu.gpr = (G1 X.cpu.gpr (bv V X.cpu.gpr) (wv V X.cpu.gpr)).set 4 (X.cpu.gpr.rsp - 48) →
      (∀ (Z : State) (V' : Addr → Byte) (t'' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V' →
        Z.cpu.rip = stb_at.add 85 → Z.cpu.gpr.rsp = X.cpu.gpr.rsp - 40 → Z.cpu.gpr.rbx = X.cpu.gpr.rdi →
        Z.cpu.gpr.rbp.setWidth 32 = X.cpu.gpr.rcx.setWidth 32 →
        rdq(V', X.cpu.gpr.rsp - 40) = X.cpu.gpr.rsi → rdq(V', X.cpu.gpr.rsp - 32) = X.cpu.gpr.rdx →
        rdq(V', X.cpu.gpr.rsp - 16) = X.cpu.gpr.rbx → rdq(V', X.cpu.gpr.rsp - 8) = X.cpu.gpr.rbp →
        rdq(V', X.cpu.gpr.rsp) = e₂.add j₂ → Pf Z V' → GoG prof L o gev gP gE Z t'') →
      GoG prof L o gev gP gE Y t')
    (kr : ∀ (Z : State) (V' : Addr → Byte), Pf Z V' → ∀ (Z' : State) (t' : Nat), KeptW Wl s₀ Z' →
      Agree F Z'.proc.mm.mem (Vfin V' X.cpu.gpr.rdi X.cpu.gpr.rsi X.cpu.gpr.rdx
        (fw (X.cpu.gpr.rcx.setWidth 32) (wv V' X.cpu.gpr))) → Z'.cpu.rip = e₂.add j₂ →
      Z'.cpu.gpr = { Z.cpu.gpr with
        rax := (fw (X.cpu.gpr.rcx.setWidth 32) (wv V' X.cpu.gpr)).setWidth 64,
        rdx := (wv V' X.cpu.gpr &&& 4294967294#32).setWidth 64, rbx := X.cpu.gpr.rbx, rbp := X.cpu.gpr.rbp,
        rsp := X.cpu.gpr.rsp + 8 } →
      GoG prof L o gev gP gE Z' t') :
    GoG prof L o gev gP gE X t := by
  have t8 := u8 X.cpu.gpr.rsp (by omega)
  have t16 : (X.cpu.gpr.rsp - 8 - 8).toNat = X.cpu.gpr.rsp.toNat - 16 := by
    rw [o3]; exact u16 _ (by omega)
  have t40 := u40 X.cpu.gpr.rsp (by omega)
  have t56 : (X.cpu.gpr.rdi + 56#64).toNat = X.cpu.gpr.rdi.toNat + 56 := Sas.tn_add _ 56 (by omega)
  have hrip' : X.cpu.rip = stb_at.add 0 := by rw [addr_add_zero]; exact hrip
  -- the bytes and the frame
  have h1 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8) i) := by rw [n8]; exact Sas.ft hs 40 8 (by decide)
  have h2 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8 - 8) i) := by rw [n16]; exact Sas.ft hs 32 8 (by decide)
  have s1 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8 - 8 - 24#64) i) := by
    rw [n40]; exact Sas.ft hs 8 8 (by decide)
  have s2 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8 - 8 - 24#64 + 8#64) i) := by
    rw [n32]; exact Sas.ft hs 16 8 (by decide)
  have l1 : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rdi + 56#64) i) := fun i hi =>
    c.hws _ (Sas.ft hfw 56 8 (by decide) i hi)
  have l2 : ∀ i < 4, Foot F.data (Addr.add X.cpu.gpr.rdi i) := fun i hi => c.hws _ (hfw i (by omega))
  have hl' : ∀ i < 48, Foot F.data (Addr.add (X.cpu.gpr.rsp - 40) i) := fr40 (fun i hi => c.hws _ (hs i hi)) hl
  have hp' : (X.cpu.gpr.rsp - 40).toNat + 48 ≤ 2 ^ 64 := by rw [t40]; omega
  have hdj' : X.cpu.gpr.rdi.toNat + 72 ≤ (X.cpu.gpr.rsp - 40).toNat ∨
      (X.cpu.gpr.rsp - 40).toNat + 48 ≤ X.cpu.gpr.rdi.toNat := by rw [t40]; omega
  -- the loads before the stores
  have l8 : ∀ v : BitVec 64, (toBytesLE v 8).length = 8 := fun v => toBytesLE_length v 8
  have hbv : rdq(Vp V X.cpu.gpr, X.cpu.gpr.rdi + 56#64) = bv V X.cpu.gpr := by
    dsimp only [Vp]
    rw [Tun.rd_Vst _ (X.cpu.gpr.rsp - 8 - 8) (toBytesLE X.cpu.gpr.rbx 8) (X.cpu.gpr.rdi + 56#64) 8
        (by rw [l8]; omega) (by rw [t56]; omega) (by rw [l8, t56]; omega),
      Tun.rd_Vst _ (X.cpu.gpr.rsp - 8) (toBytesLE X.cpu.gpr.rbp 8) (X.cpu.gpr.rdi + 56#64) 8
        (by rw [l8]; omega) (by rw [t56]; omega) (by rw [l8, t56]; omega)]
  have hwv : ofBytesLE 32 ((byteAddrs X.cpu.gpr.rdi 4).map (Vp V X.cpu.gpr)) = wv V X.cpu.gpr := by
    dsimp only [Vp]
    rw [Tun.rd_Vst _ (X.cpu.gpr.rsp - 8 - 8) (toBytesLE X.cpu.gpr.rbx 8) X.cpu.gpr.rdi 4 (by rw [l8]; omega)
        (by omega) (by rw [l8]; omega),
      Tun.rd_Vst _ (X.cpu.gpr.rsp - 8) (toBytesLE X.cpu.gpr.rbp 8) X.cpu.gpr.rdi 4 (by rw [l8]; omega)
        (by omega) (by rw [l8]; omega)]
  obtain ⟨r0, r1, r3, r5, r6⟩ := v1_rd (V := V) (g := X.cpu.gpr) hp hp8
  -- to 39: the rest
  have go39 : ∀ (Y : State) (t₁ : Nat), KeptW Wl s₀ Y → Agree F Y.proc.mm.mem (V1 V X.cpu.gpr) →
      Y.cpu.rip = stb_at.add 39 → Y.cpu.gpr = G1 X.cpu.gpr (bv V X.cpu.gpr) (wv V X.cpu.gpr) →
      (bv V X.cpu.gpr = 0 ∨ (wv V X.cpu.gpr).setWidth 8 &&& 1#8 ≠ 0) → GoG prof L o gev gP gE Y t₁ :=
    fun Y t₁ hKY hAY hrY hgY hc =>
      stb_t (r := X.cpu.gpr.rsp - 40) (fp := X.cpu.gpr.rdi) (rf := X.cpu.gpr.rsp + 8)
        (a := X.cpu.gpr.rcx.setWidth 32) (x := wv V X.cpu.gpr) (bb := X.cpu.gpr.rsi) (be := X.cpu.gpr.rdx)
        (b3 := X.cpu.gpr.rbx) (b5 := X.cpu.gpr.rbp)
        c hin hKY hAY hrY (by rw [hgY]; exact o1 _) (by rw [hgY]; try rfl) (f48 _)
        (by rw [hgY]; exact sw_64_32 _) (by rw [hgY]; exact sw_64_32 _) hp' hl' hfw hfp hdj' r0 r1 r3 r5 hin₂ h₂
        (r6.trans hra) fun Z' t' hKZ hAZ hrZ hgZ => k1 hc Z' t' hKZ hAZ hrZ (by rw [hgZ, hgY] <;> rfl)
  by_cases hb0 : bv V X.cpu.gpr = 0
  · refine (c_0 prof).run c hin _ hK hA hrip' (vc_0a h1 h2 l1 l2 s1 s2 hbv hwv hb0) ?_
    rintro j' g fl V₁ ⟨rfl, rfl, hV⟩ Y t₁ hKY hAY hrY hgY -
    subst V₁
    exact go39 Y t₁ hKY hAY hrY hgY (.inl hb0)
  by_cases hf : (wv V X.cpu.gpr).setWidth 8 &&& 1#8 = 0
  · -- through `free`
    refine (c_0 prof).run c hin _ hK hA hrip' (vc_0c h1 h2 l1 l2 s1 s2 hbv hwv hb0 hf) ?_
    rintro j' g fl V₁ ⟨rfl, rfl, hV⟩ Y t₁ hKY hAY hrY hgY -
    subst V₁
    have hsY : Y.cpu.gpr.rsp = X.cpu.gpr.rsp - 40 := by rw [hgY]; exact o1 _
    refine c.s_call hKY hAY hin (lt_len (by decide)) hrY (call_80 _) hinF hF (by decide)
      (by rw [hsY, m48]; exact fun i hi => hs i (by omega)) ?_
    rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
    rw [hsY, m48] at hA₂
    have hg₂' : Y₂.cpu.gpr = (G1 X.cpu.gpr (bv V X.cpu.gpr) (wv V X.cpu.gpr)).set 4 (X.cpu.gpr.rsp - 48) := by
      rw [hg₂, hsY, m48, hgY]
    refine kf hb0 hf Y₂ t₂ hK₂ hA₂ hr₂ hg₂' ?_
    -- back from `free`
    intro Z V' t'' hKZ hAZ hrZ hzs hzb hzp e0 e1 e3 e5 e6 hPf
    refine (c_85 prof).run c hin _ hKZ hAZ hrZ (vc_85 (by rw [hzb]; exact l2)) ?_
    rintro j' g fl V₂ ⟨rfl, rfl, hV⟩ U t₃ hKU hAU hrU hgU -
    subst V₂
    exact stb_t (r := X.cpu.gpr.rsp - 40) (fp := X.cpu.gpr.rdi) (rf := X.cpu.gpr.rsp + 8)
      (a := X.cpu.gpr.rcx.setWidth 32) (x := wv V' X.cpu.gpr) (bb := X.cpu.gpr.rsi) (be := X.cpu.gpr.rdx)
      (b3 := X.cpu.gpr.rbx) (b5 := X.cpu.gpr.rbp)
      c hin hKU hAU hrU (by rw [hgU]; exact hzs) (by rw [hgU]; exact hzb) (f48 _)
      (by rw [hgU]; exact hzp)
      (by rw [hgU]; show ((ofBytesLE 32 ((byteAddrs Z.cpu.gpr.rbx 4).map V')).setWidth 64).setWidth 32 = _
          rw [sw_64_32, hzb])
      hp' hl' hfw hfp hdj' e0 (by rw [o2]; exact e1) (by rw [a24]; exact e3) (by rw [a24, a32]; exact e5) hin₂ h₂
      (by rw [a24, a32, a40]; exact e6) fun Z' t' hKZ' hAZ' hrZ' hgZ' =>
      kr Z V' hPf Z' t' hKZ' hAZ' hrZ' (by rw [hgZ', hgU] <;> rfl)
  · refine (c_0 prof).run c hin _ hK hA hrip' (vc_0b h1 h2 l1 l2 s1 s2 hbv hwv hb0 hf) ?_
    rintro j' g fl V₁ ⟨rfl, rfl, hV⟩ Y t₁ hKY hAY hrY hgY -
    subst V₁
    exact go39 Y t₁ hKY hAY hrY hgY (.inr hf)

end FV7z.Stb
