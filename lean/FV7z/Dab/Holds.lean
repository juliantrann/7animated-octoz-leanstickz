import FV7z.Dab.Cuts
import FV7z.Lemmas.LeafRet
import FV7z.Lemmas.BlkOps4
import FV7z.Lemmas.Xmm2
import FV7z.Lemmas.CallM
import FV7z.Tun.Inv
import FV7z.Cxa.Holds
import FV7z.Sas.Holds
/-!
# `_IO_doallocbuf` (PLAN.md §M, M1)

glibc 2.31's `_IO_doallocbuf (fp)` at `0x62b500` in `7zzs` (`libio/genops.c`). `fp->_IO_buf_base` (`[fp + 0x38]`)
not null: the `ret` at 11. Else `push r12; push rbp; push rbx`, `eax` = `fp->_flags`, `rbx` = `fp`. `_IO_UNBUFFERED`
(bit 1) set and `fp->_mode` (`[fp + 0xc0]`) at most 0: the inlined `_IO_setb (fp, fp->_shortbuf, fp->_shortbuf + 1, 0)`
from 114. Else at 39 the vtable (`[fp + 0xd8]`) checked against `__libc_IO_vtables` (2088 bytes from `0x793da0`):
outside it, the `call` of `_IO_vtable_check` at 176; inside, `call qword [vtable + 0x68]` (`_IO_DOALLOCATE`) at 77.
Its result not EOF: the registers popped, the `ret` at 141. EOF: the buffer and the flags read again; the buffer not
null and `_IO_USER_BUF` (bit 0) clear, `free` of it (the `call` at 160), the flags read again (165); then at 114
`eax | 1`, `[fp]` = `eax`, `_IO_buf_base` = `fp + 0x83`, `_IO_buf_end` = `fp + 0x84` (one `movups` of `r12`, `rbp`
by `movq; movq; punpcklqdq`), the registers popped, the `ret` at 141.

The callees are hypotheses, as in `FV7z/Lfp/Holds.lean` and `FV7z/Stb/Holds.lean`: `_IO_vtable_check` a continuation
at its entry (`kc`); `_IO_DOALLOCATE` (`kd`) and `free` (`kf`) continuations at their entries, given the run from
their return (the frame as it was, their own posts `Pd`, `Pf`) to the return address.

- `Vt V fp x`: the bytes at the end: the flags word `x | 1` at `fp`, the two pointers at `fp + 0x38`.
- `G1`, `G74`, `G85`: the registers after the pushes, at the vtable's `call`, after the reads at 85.
- `dab_t`: from 114 to the return address, for the frame at `r` (the saved `rbx`, `rbp`, `r12`, the return address).
- `dab_ok`: from the entry.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Dab

/-! ## The steps outside the blocks -/

def pret : List Byte := [0xc3]
theorem pret_0 : ∀ feat, Dec feat pret 0 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem w_11 : pret <+: dab.drop 11 := by decide +kernel
theorem ret_11 (feat : Features) : Dec feat dab 11 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 11) (k := 0) (pret_0 feat) w_11 (Nat.zero_le _)
theorem w_141 : pret <+: dab.drop 141 := by decide +kernel
theorem ret_141 (feat : Features) : Dec feat dab 141 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 141) (k := 0) (pret_0 feat) w_141 (Nat.zero_le _)

/-- `call qword [rbp + 0x68]`: `_IO_DOALLOCATE`. -/
def pcm : List Byte := [0xff, 0x55, 0x68]
theorem pcm_0 : ∀ feat, Dec feat pcm 0 (FV7z.mk .call 64 [.mem (mbd 5 104 64)] 3) := by dec_rfl
theorem w_77 : pcm <+: dab.drop 77 := by decide +kernel
theorem call_77 (feat : Features) : Dec feat dab 77 (FV7z.mk .call 64 [.mem (mbd 5 104 64)] 3) :=
  Dec.shift (j := 77) (k := 0) (pcm_0 feat) w_77 (Nat.zero_le _)

/-- The `call` of `free`. -/
def pcf : List Byte := [0xe8, 0xab, 0x81, 0x00, 0x00]
theorem pcf_0 : ∀ feat, Dec feat pcf 0 (FV7z.mk .call 64 [.rel 33195] 5) := by dec_rfl
theorem w_160 : pcf <+: dab.drop 160 := by decide +kernel
theorem call_160 (feat : Features) : Dec feat dab 160 (FV7z.mk .call 64 [.rel 33195] 5) :=
  Dec.shift (j := 160) (k := 0) (pcf_0 feat) w_160 (Nat.zero_le _)

/-- The `call` of `_IO_vtable_check`. -/
def pcv : List Byte := [0xe8, 0x6b, 0xc4, 0xff, 0xff]
theorem pcv_0 : ∀ feat, Dec feat pcv 0 (FV7z.mk .call 64 [.rel 18446744073709536363] 5) := by dec_rfl
theorem w_176 : pcv <+: dab.drop 176 := by decide +kernel
theorem call_176 (feat : Features) : Dec feat dab 176 (FV7z.mk .call 64 [.rel 18446744073709536363] 5) :=
  Dec.shift (j := 176) (k := 0) (pcv_0 feat) w_176 (Nat.zero_le _)

/-- `movq xmm0, r12; movq xmm1, rbp; punpcklqdq xmm0, xmm1; movups [rbx + 0x38], xmm0`. -/
def pq0 : List Byte := [0x66, 0x49, 0x0f, 0x6e, 0xc4]
theorem pq0_0 : ∀ feat, Dec feat pq0 0 (FV7z.mk (.sse .movq) 64 [.xmm 0, gr 64 12] 5) := by dec_rfl
theorem w_117 : pq0 <+: dab.drop 117 := by decide +kernel
theorem mq_117 (feat : Features) : Dec feat dab 117 (FV7z.mk (.sse .movq) 64 [.xmm 0, gr 64 12] 5) :=
  Dec.shift (j := 117) (k := 0) (pq0_0 feat) w_117 (Nat.zero_le _)
def pq1 : List Byte := [0x66, 0x48, 0x0f, 0x6e, 0xcd]
theorem pq1_0 : ∀ feat, Dec feat pq1 0 (FV7z.mk (.sse .movq) 64 [.xmm 1, gr 64 5] 5) := by dec_rfl
theorem w_122 : pq1 <+: dab.drop 122 := by decide +kernel
theorem mq_122 (feat : Features) : Dec feat dab 122 (FV7z.mk (.sse .movq) 64 [.xmm 1, gr 64 5] 5) :=
  Dec.shift (j := 122) (k := 0) (pq1_0 feat) w_122 (Nat.zero_le _)
def ppu : List Byte := [0x66, 0x0f, 0x6c, 0xc1]
theorem ppu_0 : ∀ feat, Dec feat ppu 0 (FV7z.mk (.sse .punpcklqdq) 16 [.xmm 0, .xmm 1] 4) := by dec_rfl
theorem w_129 : ppu <+: dab.drop 129 := by decide +kernel
theorem pu_129 (feat : Features) : Dec feat dab 129 (FV7z.mk (.sse .punpcklqdq) 16 [.xmm 0, .xmm 1] 4) :=
  Dec.shift (j := 129) (k := 0) (ppu_0 feat) w_129 (Nat.zero_le _)
def pmv : List Byte := [0x0f, 0x11, 0x43, 0x38]
theorem pmv_0 : ∀ feat, Dec feat pmv 0 (FV7z.mk (.sse .movups) 32 [.mem (mbd 3 56 128), .xmm 0] 4) := by dec_rfl
theorem w_133 : pmv <+: dab.drop 133 := by decide +kernel
theorem mv_133 (feat : Features) : Dec feat dab 133 (FV7z.mk (.sse .movups) 32 [.mem (mbd 3 56 128), .xmm 0] 4) :=
  Dec.shift (j := 133) (k := 0) (pmv_0 feat) w_133 (Nat.zero_le _)

/-- glibc's `free` and `_IO_vtable_check` (code not proved here). -/
abbrev fre_at : Addr := 0x633750
abbrev vck_at : Addr := 0x627a20

/-! ## Flags and offsets -/

theorem cond_14 (f : Rflags) : f.cond 14 = (f.zf || (f.sf != f.of)) := rfl
theorem rfz_of (f : Rflags) : (rfz f).of = f.of := rfl
theorem arith_of {w : Nat} (f : Rflags) (r : BitVec w) (cf of af : Bool) : (f.arith r cf of af).of = of := rfl
theorem bnf (b : Bool) : (b != false) = b := by cases b <;> rfl

theorem q16 (x : Addr) : x - 24 + 8 + 8 = x - 8 := by bv_omega
theorem q24 (x : Addr) : x - 24 + 8 + 8 + 8 = x := by bv_omega
theorem q32 (x : Addr) : x - 24 + 8 + 8 + 8 + 8 = x + 8 := by bv_omega

/-- The frame from `x - 24`: 24 bytes below `x` and 8 from `x`. -/
theorem fr24 {P : Addr → Prop} {x : Addr} (h1 : ∀ i < 32, P (Addr.add (x - 32) i))
    (h2 : ∀ i < 8, P (Addr.add x i)) : ∀ i < 32, P (Addr.add (x - 24) i) := fun i hi => by
  by_cases h : i < 24
  · have e : Addr.add (x - 24) i = Addr.add (x - 32) (8 + i) := by simp only [Addr.add]; bv_omega
    rw [e]; exact h1 _ (by omega)
  · have e : Addr.add (x - 24) i = Addr.add x (i - 24) := by simp only [Addr.add]; bv_omega
    rw [e]; exact h2 _ (by omega)

/-! ## The registers and bytes -/

/-- The bytes at the end: the flags word `x | 1` (`_IO_USER_BUF`) at `fp`, then `_IO_buf_base` = `fp + 0x83` and
`_IO_buf_end` = `fp + 0x84` by one 16-byte store. -/
abbrev Vt (V : Addr → Byte) (fp : Addr) (x : BitVec 32) : Addr → Byte :=
  Vst (Vst V fp (toBytesLE (x ||| 1#32) 4)) (fp + 56#64) (toBytesLE ((fp + 132#64) ++ (fp + 131#64)) 16)

/-- The words the code reads at the entry: the buffer, the flags, `_mode`, the vtable. -/
abbrev bb (V : Addr → Byte) (g : Gprs) : BitVec 64 := rdq(V, g.rdi + 56#64)
abbrev wv (V : Addr → Byte) (g : Gprs) : BitVec 32 := ofBytesLE 32 ((byteAddrs g.rdi 4).map V)
abbrev md (V : Addr → Byte) (g : Gprs) : BitVec 32 := ofBytesLE 32 ((byteAddrs (g.rdi + 192#64) 4).map V)
abbrev vt (V : Addr → Byte) (g : Gprs) : BitVec 64 := rdq(V, g.rdi + 216#64)

/-- The registers after the pushes, `w` the flags. -/
abbrev G1 (g : Gprs) (w : BitVec 32) : Gprs :=
  { g with
    rax := w.setWidth 64, rbx := g.rdi, rsp := g.rsp - 8 - 8 - 8 }
/-- The registers at the vtable's `call`, `v` the vtable. -/
abbrev G74 (g : Gprs) (v : BitVec 64) : Gprs :=
  { g with
    rax := 2088#64, rcx := v - 7945632#64, rdx := 7945632#64, rbx := g.rdi, rsp := g.rsp - 8 - 8 - 8, rbp := v }
/-- The registers after the reads at 85: `b` the buffer, `w` the flags. -/
abbrev G85 (g : Gprs) (b : BitVec 64) (w : BitVec 32) : Gprs :=
  { g with
    rax := w.setWidth 64, rbp := g.rbx + 132#64, rdi := b, r12 := g.rbx + 131#64 }

/-- The end's stores keep the bytes of the frame. -/
theorem rd_t {V : Addr → Byte} {fp z : Addr} (x : BitVec 32) (hfp : fp.toNat + 72 ≤ 2 ^ 64)
    (hz : z.toNat + 8 ≤ 2 ^ 64) (hd : fp.toNat + 72 ≤ z.toNat ∨ z.toNat + 8 ≤ fp.toNat) :
    rdq(Vt V fp x, z) = rdq(V, z) := by
  have t56 : (fp + 56#64).toNat = fp.toNat + 56 := Sas.tn_add fp 56 (by omega)
  dsimp only [Vt]
  rw [Tun.rd_Vst _ (fp + 56#64) (toBytesLE ((fp + 132#64) ++ (fp + 131#64)) 16) z 8
      (by rw [toBytesLE_length, t56]; omega) hz (by rw [toBytesLE_length, t56]; omega),
    Tun.rd_Vst _ fp (toBytesLE (x ||| 1#32) 4) z 8 (by rw [toBytesLE_length]; omega) hz
      (by rw [toBytesLE_length]; omega)]

variable {F : Footprint} {Wl : List Rgn}

/-! ## The verification conditions -/

/-- From the entry, the buffer not null: to the `ret` at 11. -/
theorem vc_0r {g : Gprs} {f : Rflags} {V : Addr → Byte} {b : BitVec 64}
    (l1 : ∀ i < 8, Foot F.data (Addr.add (g.rdi + 56#64) i)) (hb : rdq(V, g.rdi + 56#64) = b)
    (hz : decide (b = 0#64) = false) :
    W_0 F Wl (fun j' g' _ V' => j' = 11 ∧ g' = g ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at l1 hb ⊢
  revert hb
  wpx [W_0, o0, Op.cmpmi]
  intro hb
  wpx [hb, hz, Bool.false_eq_true, Bool.true_eq_false, eq_self_iff_true, false_implies, implies_true]
  all_goals repeat'
    first
    | exact rfl
    | assumption
    | exact trivial
    | (intro h; exact absurd h (by decide))
    | apply And.intro
    | intro _

/-- From the entry, the buffer null and `_IO_UNBUFFERED` clear: to 39. -/
theorem vc_0a {g : Gprs} {f : Rflags} {V : Addr → Byte} {b : BitVec 64} {w : BitVec 32}
    (h1 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8) i)) (h2 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8) i))
    (h3 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8 - 8) i))
    (l1 : ∀ i < 8, Foot F.data (Addr.add (g.rdi + 56#64) i)) (l2 : ∀ i < 4, Foot F.data (Addr.add g.rdi i))
    (hb : rdq(V, g.rdi + 56#64) = b) (hz : decide (b = 0#64) = true)
    (hw : ofBytesLE 32 ((byteAddrs g.rdi 4).map (Sas.Vp V g)) = w) (hf : (w.setWidth 8 &&& 2#8 == 0) = true) :
    W_0 F Wl (fun j' g' _ V' => j' = 39 ∧ g' = { G1 g w with rdx := g.rdx } ∧ V' = Sas.Vp V g) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h1 h2 h3 l1 l2 hb hw ⊢
  revert hb hw
  wpx [W_0, W_16, o0, o1, Op.cmpmi, Sas.Vp, G1]
  intro hb hw
  wpx [hb, hz, hw, hf, BitVec.and_self, Bool.false_eq_true, Bool.true_eq_false, eq_self_iff_true,
    false_implies, implies_true]
  all_goals repeat'
    first
    | exact rfl
    | assumption
    | exact trivial
    | (intro h; exact absurd h (by decide))
    | apply And.intro
    | intro _

/-- From the entry, the buffer null, `_IO_UNBUFFERED` set and `_mode` above 0: to 39. -/
theorem vc_0b {g : Gprs} {f : Rflags} {V : Addr → Byte} {b : BitVec 64} {w m : BitVec 32}
    (h1 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8) i)) (h2 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8) i))
    (h3 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8 - 8) i))
    (l1 : ∀ i < 8, Foot F.data (Addr.add (g.rdi + 56#64) i)) (l2 : ∀ i < 4, Foot F.data (Addr.add g.rdi i))
    (l3 : ∀ i < 4, Foot F.data (Addr.add (g.rdi + 192#64) i))
    (hb : rdq(V, g.rdi + 56#64) = b) (hz : decide (b = 0#64) = true)
    (hw : ofBytesLE 32 ((byteAddrs g.rdi 4).map (Sas.Vp V g)) = w)
    (hm : ofBytesLE 32 ((byteAddrs (g.rdi + 192#64) 4).map (Sas.Vp V g)) = m)
    (hf : (w.setWidth 8 &&& 2#8 == 0) = false) (hle : ((m == 0) || m.msb) = false) :
    W_0 F Wl (fun j' g' _ V' => j' = 39 ∧ g' = { G1 g w with rdx := m.setWidth 64 } ∧ V' = Sas.Vp V g) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h1 h2 h3 l1 l2 l3 hb hw hm ⊢
  revert hb hw hm
  wpx [W_0, W_16, W_29, o0, o1, o2, Op.cmpmi, Sas.Vp, G1]
  intro hb hw hm
  wpx [hb, hz, hw, hm, hf, hle, cond_14, rfz_of, arith_of, bnf, BitVec.and_self, Bool.false_eq_true,
    Bool.true_eq_false, eq_self_iff_true, false_implies, implies_true]
  all_goals repeat'
    first
    | exact rfl
    | assumption
    | exact trivial
    | (intro h; exact absurd h (by decide))
    | apply And.intro
    | intro _

/-- From the entry, the buffer null, `_IO_UNBUFFERED` set and `_mode` at most 0: to 114, the short buffer. -/
theorem vc_0c {g : Gprs} {f : Rflags} {V : Addr → Byte} {b : BitVec 64} {w m : BitVec 32}
    (h1 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8) i)) (h2 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8) i))
    (h3 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8 - 8) i))
    (l1 : ∀ i < 8, Foot F.data (Addr.add (g.rdi + 56#64) i)) (l2 : ∀ i < 4, Foot F.data (Addr.add g.rdi i))
    (l3 : ∀ i < 4, Foot F.data (Addr.add (g.rdi + 192#64) i))
    (hb : rdq(V, g.rdi + 56#64) = b) (hz : decide (b = 0#64) = true)
    (hw : ofBytesLE 32 ((byteAddrs g.rdi 4).map (Sas.Vp V g)) = w)
    (hm : ofBytesLE 32 ((byteAddrs (g.rdi + 192#64) 4).map (Sas.Vp V g)) = m)
    (hf : (w.setWidth 8 &&& 2#8 == 0) = false) (hle : ((m == 0) || m.msb) = true) :
    W_0 F Wl (fun j' g' _ V' => j' = 114 ∧
      g' = { G1 g w with
        rdx := m.setWidth 64, rbp := g.rdi + 132#64, r12 := g.rdi + 131#64 } ∧ V' = Sas.Vp V g) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h1 h2 h3 l1 l2 l3 hb hw hm ⊢
  revert hb hw hm
  wpx [W_0, W_16, W_29, W_144, o0, o1, o2, o11, Op.cmpmi, Sas.Vp, G1]
  intro hb hw hm
  wpx [hb, hz, hw, hm, hf, hle, cond_14, rfz_of, arith_of, bnf, BitVec.and_self, Bool.false_eq_true,
    Bool.true_eq_false, eq_self_iff_true, false_implies, implies_true]
  all_goals repeat'
    first
    | exact rfl
    | assumption
    | exact trivial
    | (intro h; exact absurd h (by decide))
    | apply And.intro
    | intro _

/-- From 39, the vtable `v` inside `__libc_IO_vtables`: to 74. -/
theorem vc_39i {g : Gprs} {f : Rflags} {V : Addr → Byte} {v : BitVec 64}
    (l : ∀ i < 8, Foot F.data (Addr.add (g.rbx + 216#64) i)) (hv : rdq(V, g.rbx + 216#64) = v)
    (hr : (v - 7945632#64).toNat < 2088) :
    W_39 F Wl (fun j' g' _ V' => j' = 74 ∧
      g' = { g with
        rax := 2088#64, rcx := v - 7945632#64, rdx := 7945632#64, rbp := v } ∧ V' = V) g f V := by
  have h1 : ¬ 2088 < (v - 7945632#64).toNat := by omega
  have h2 : ¬ 2088#64 = v - 7945632#64 := fun e => by rw [← e] at hr; exact absurd hr (by decide)
  have h1' : decide (2088 < (v - 7945632#64).toNat) = false := decide_eq_false h1
  have h2' : decide (2088#64 = v - 7945632#64) = false := decide_eq_false h2
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at l hv ⊢
  revert hv
  wpx [W_39, o3]
  intro hv
  wpx [hv, h1, h2, h1', h2', BitVec.reduceSub, Bool.or_false, Bool.false_or, Bool.false_eq_true,
    Bool.true_eq_false, eq_self_iff_true, false_implies, implies_true]
  all_goals repeat'
    first
    | exact rfl
    | assumption
    | exact trivial
    | (intro h; exact absurd h (by decide))
    | apply And.intro
    | intro _

/-- From 39, the vtable `v` outside `__libc_IO_vtables`: to the `call` of `_IO_vtable_check` at 176. -/
theorem vc_39o {g : Gprs} {f : Rflags} {V : Addr → Byte} {v : BitVec 64}
    (l : ∀ i < 8, Foot F.data (Addr.add (g.rbx + 216#64) i)) (hv : rdq(V, g.rbx + 216#64) = v)
    (hr : 2088 ≤ (v - 7945632#64).toNat) :
    W_39 F Wl (fun j' g' _ V' => j' = 176 ∧
      g' = { g with
        rax := 2088#64, rcx := v - 7945632#64, rdx := 7945632#64, rbp := v } ∧ V' = V) g f V := by
  have hc : (decide (2088 < (v - 7945632#64).toNat) || decide (2088#64 = v - 7945632#64)) = true := by
    rcases Nat.lt_or_eq_of_le hr with h | h
    · rw [decide_eq_true h, Bool.true_or]
    · have e : 2088#64 = v - 7945632#64 := BitVec.eq_of_toNat_eq (by rw [← h]; rfl)
      rw [decide_eq_true e, Bool.or_true]
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at l hv ⊢
  revert hv
  wpx [W_39, o3]
  intro hv
  wpx [hv, hc, BitVec.reduceSub, Bool.false_eq_true, Bool.true_eq_false, eq_self_iff_true, false_implies,
    implies_true]
  all_goals repeat'
    first
    | exact rfl
    | assumption
    | exact trivial
    | (intro h; exact absurd h (by decide))
    | apply And.intro
    | intro _

/-- From 74: `mov rdi, rbx` to the vtable's `call` at 77. -/
theorem vc_74 {g : Gprs} {f : Rflags} {V : Addr → Byte} :
    W_74 F Wl (fun j' g' _ V' => j' = 77 ∧ g' = { g with rdi := g.rbx } ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_74, o4]
  all_goals repeat' (first | exact rfl | exact trivial | apply And.intro | intro _)

/-- From the vtable's return (80), its result not EOF: to the pops at 137. -/
theorem vc_80n {g : Gprs} {f : Rflags} {V : Addr → Byte} (hn : g.rax.setWidth 32 ≠ 4294967295#32) :
    W_80 F Wl (fun j' g' _ V' => j' = 137 ∧ g' = g ∧ V' = V) g f V := by
  have hn' : decide (g.rax.setWidth 32 = 4294967295#32) = false := decide_eq_false hn
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hn' ⊢
  wpx [W_80, o5, hn', Bool.not_false, Bool.false_eq_true, Bool.true_eq_false, eq_self_iff_true, false_implies,
    implies_true]
  all_goals repeat'
    first
    | exact rfl
    | exact trivial
    | (intro h; exact absurd h (by decide))
    | apply And.intro
    | intro _

/-- From 80, the result EOF and the buffer read again null: to 114. -/
theorem vc_80a {g : Gprs} {f : Rflags} {V : Addr → Byte} {b : BitVec 64} {w : BitVec 32}
    (he : g.rax.setWidth 32 = 4294967295#32)
    (l1 : ∀ i < 8, Foot F.data (Addr.add (g.rbx + 56#64) i)) (l2 : ∀ i < 4, Foot F.data (Addr.add g.rbx i))
    (hb : rdq(V, g.rbx + 56#64) = b) (hw : ofBytesLE 32 ((byteAddrs g.rbx 4).map V) = w)
    (hb0 : (b == 0) = true) :
    W_80 F Wl (fun j' g' _ V' => j' = 114 ∧ g' = G85 g b w ∧ V' = V) g f V := by
  have he' : decide (g.rax.setWidth 32 = 4294967295#32) = true := decide_eq_true he
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at he' l1 l2 hb hw ⊢
  revert hb hw
  wpx [W_80, W_85, o5, o6, G85]
  intro hb hw
  wpx [hb, hw, he', hb0, BitVec.and_self, Bool.not_true, Bool.false_eq_true, Bool.true_eq_false, eq_self_iff_true,
    false_implies, implies_true]
  all_goals repeat'
    first
    | exact rfl
    | assumption
    | exact trivial
    | (intro h; exact absurd h (by decide))
    | apply And.intro
    | intro _

/-- From 80, the result EOF, the buffer not null and `_IO_USER_BUF` set: to 114. -/
theorem vc_80b {g : Gprs} {f : Rflags} {V : Addr → Byte} {b : BitVec 64} {w : BitVec 32}
    (he : g.rax.setWidth 32 = 4294967295#32)
    (l1 : ∀ i < 8, Foot F.data (Addr.add (g.rbx + 56#64) i)) (l2 : ∀ i < 4, Foot F.data (Addr.add g.rbx i))
    (hb : rdq(V, g.rbx + 56#64) = b) (hw : ofBytesLE 32 ((byteAddrs g.rbx 4).map V) = w)
    (hb0 : (b == 0) = false) (hf : (w.setWidth 8 &&& 1#8 == 0) = false) :
    W_80 F Wl (fun j' g' _ V' => j' = 114 ∧ g' = G85 g b w ∧ V' = V) g f V := by
  have he' : decide (g.rax.setWidth 32 = 4294967295#32) = true := decide_eq_true he
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at he' l1 l2 hb hw ⊢
  revert hb hw
  wpx [W_80, W_85, W_110, o5, o6, o7, G85]
  intro hb hw
  wpx [hb, hw, he', hb0, hf, BitVec.and_self, Bool.not_true, Bool.false_eq_true, Bool.true_eq_false,
    eq_self_iff_true, false_implies, implies_true]
  all_goals repeat'
    first
    | exact rfl
    | assumption
    | exact trivial
    | (intro h; exact absurd h (by decide))
    | apply And.intro
    | intro _

/-- From 80, the result EOF, the buffer not null and `_IO_USER_BUF` clear: to the `call` of `free` at 160. -/
theorem vc_80c {g : Gprs} {f : Rflags} {V : Addr → Byte} {b : BitVec 64} {w : BitVec 32}
    (he : g.rax.setWidth 32 = 4294967295#32)
    (l1 : ∀ i < 8, Foot F.data (Addr.add (g.rbx + 56#64) i)) (l2 : ∀ i < 4, Foot F.data (Addr.add g.rbx i))
    (hb : rdq(V, g.rbx + 56#64) = b) (hw : ofBytesLE 32 ((byteAddrs g.rbx 4).map V) = w)
    (hb0 : (b == 0) = false) (hf : (w.setWidth 8 &&& 1#8 == 0) = true) :
    W_80 F Wl (fun j' g' _ V' => j' = 160 ∧ g' = G85 g b w ∧ V' = V) g f V := by
  have he' : decide (g.rax.setWidth 32 = 4294967295#32) = true := decide_eq_true he
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at he' l1 l2 hb hw ⊢
  revert hb hw
  wpx [W_80, W_85, W_110, o5, o6, o7, G85]
  intro hb hw
  wpx [hb, hw, he', hb0, hf, BitVec.and_self, Bool.not_true, Bool.false_eq_true, Bool.true_eq_false,
    eq_self_iff_true, false_implies, implies_true]
  all_goals repeat'
    first
    | exact rfl
    | assumption
    | exact trivial
    | (intro h; exact absurd h (by decide))
    | apply And.intro
    | intro _

/-- From 114: `or eax, 1` to the `movq` at 117. -/
theorem vc_114 {g : Gprs} {f : Rflags} {V : Addr → Byte} :
    W_114 F Wl (fun j' g' _ V' => j' = 117 ∧
      g' = { g with rax := (g.rax.setWidth 32 ||| 1#32).setWidth 64 } ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_114, o8]
  all_goals repeat' (first | exact rfl | exact trivial | apply And.intro | intro _)

/-- At 127: `mov [rbx], eax`. -/
theorem vc_127 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Gprs → Rflags → (Addr → Byte) → Prop}
    (hw : ∀ i < 4, Foot Wl (Addr.add g.rbx i))
    (hQ : ∀ fl, Q g fl (Vst V g.rbx (toBytesLE (g.rax.setWidth 32) 4))) : wp F Wl o9 Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hw hQ ⊢
  wpx [o9]
  all_goals repeat' (first | exact hQ _ | assumption | exact rfl | exact trivial | apply And.intro | intro _)

/-- From 137: `pop rbx; pop rbp; pop r12` to the `ret` at 141. -/
theorem vc_137 {g : Gprs} {f : Rflags} {V : Addr → Byte} (l0 : ∀ i < 8, Foot F.data (Addr.add g.rsp i))
    (l1 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8) i)) (l2 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8 + 8) i)) :
    W_137 F Wl (fun j' g' _ V' => j' = 141 ∧
      g' = { g with
        rbx := rdq(V, g.rsp), rbp := rdq(V, g.rsp + 8), r12 := rdq(V, g.rsp + 8 + 8),
        rsp := g.rsp + 8 + 8 + 8 } ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at l0 l1 l2 ⊢
  wpx [W_137, o10]
  all_goals repeat' (first | exact rfl | assumption | exact trivial | apply And.intro | intro _)

/-- From the return of `free` (165): `mov eax, [rbx]`, the `jmp` to 114. -/
theorem vc_165 {g : Gprs} {f : Rflags} {V : Addr → Byte} (l : ∀ i < 4, Foot F.data (Addr.add g.rbx i)) :
    W_165 F Wl (fun j' g' _ V' => j' = 114 ∧
      g' = { g with rax := (ofBytesLE 32 ((byteAddrs g.rbx 4).map V)).setWidth 64 } ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at l ⊢
  wpx [W_165, o12]
  all_goals repeat' (first | exact rfl | assumption | exact trivial | apply And.intro | intro _)

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}

/-! ## The pieces -/

/-- From 114 to the return address, for the frame at `r` and `fp` in `rbx`: the flags word `x | 1` and the two
pointers stored (`Vt`), `rbx`, `rbp`, `r12` popped. -/
theorem dab_t (c : Seg prof F Wl L s₀ o) (hin : CodeIn L dab_at dab) {Z : State} {t : Nat} {V : Addr → Byte}
    (hK : KeptW Wl s₀ Z) (hA : Agree F Z.proc.mm.mem V) (hrip : Z.cpu.rip = dab_at.add 114)
    {r fp : Addr} (hr : Z.cpu.gpr.rsp = r) (hfb : Z.cpu.gpr.rbx = fp) (hbp : Z.cpu.gpr.rbp = fp + 132#64)
    (h12 : Z.cpu.gpr.r12 = fp + 131#64) {x : BitVec 32} (hx : Z.cpu.gpr.rax.setWidth 32 = x)
    (hp : r.toNat + 32 ≤ 2 ^ 64) (hl : ∀ i < 32, Foot F.data (Addr.add r i))
    (hfw : ∀ i < 72, Foot Wl (Addr.add fp i)) (hfp : fp.toNat + 72 ≤ 2 ^ 64)
    (hdj : fp.toNat + 72 ≤ r.toNat ∨ r.toNat + 32 ≤ fp.toNat)
    {b3 b5 b12 : BitVec 64} (hb3 : rdq(V, r) = b3) (hb5 : rdq(V, r + 8) = b5) (hb12 : rdq(V, r + 8 + 8) = b12)
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (hra : rdq(V, r + 8 + 8 + 8) = e₂.add j₂)
    (k : ∀ (Z' : State) (t' : Nat), KeptW Wl s₀ Z' → Agree F Z'.proc.mm.mem (Vt V fp x) →
      Z'.cpu.rip = e₂.add j₂ →
      Z'.cpu.gpr = { Z.cpu.gpr with
        rax := (x ||| 1#32).setWidth 64, rbx := b3, rbp := b5, r12 := b12, rsp := r + 8 + 8 + 8 + 8 } →
      GoG prof L o gev gP gE Z' t') :
    GoG prof L o gev gP gE Z t := by
  subst hx
  have t8 : (r + 8).toNat = r.toNat + 8 := Sas.tn_add r 8 (by omega)
  have t16 : (r + 8 + 8).toNat = r.toNat + 16 := by rw [Sas.p16]; exact Sas.tn_add r 16 (by omega)
  have t24 : (r + 8 + 8 + 8).toNat = r.toNat + 24 := by rw [Sas.p24]; exact Sas.tn_add r 24 (by omega)
  -- `or eax, 1`
  refine (c_114 prof).run c hin (fun j' g' _ V' => j' = 117 ∧
      g' = { Z.cpu.gpr with rax := (Z.cpu.gpr.rax.setWidth 32 ||| 1#32).setWidth 64 } ∧ V' = V)
    hK hA hrip vc_114 ?_
  rintro j' g fl V₁ ⟨rfl, rfl, hV⟩ Y₁ t₁ hK₁ hA₁ hr₁ hg₁ -
  subst V₁
  -- `movq xmm0, r12; movq xmm1, rbp`
  refine c.s_movq_rx hK₁ hA₁ hin (lt_len (by decide)) hr₁ (mq_117 _) ?_
  rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂, hx₂, -⟩
  refine c.s_movq_rx hK₂ hA₂ hin (lt_len (by decide)) hr₂ (mq_122 _) ?_
  rintro Y₃ t₃ hK₃ hA₃ ⟨hr₃, hg₃, hx₃, hk₃⟩
  have e3 : Y₃.cpu.gpr = { Z.cpu.gpr with rax := (Z.cpu.gpr.rax.setWidth 32 ||| 1#32).setWidth 64 } := by
    rw [hg₃, hg₂, hg₁]
  have hb3' : Y₃.cpu.gpr.rbx = fp := by rw [e3]; exact hfb
  have ha3 : Y₃.cpu.gpr.rax.setWidth 32 = Z.cpu.gpr.rax.setWidth 32 ||| 1#32 := by rw [e3]; exact sw_64_32 _
  -- `mov [rbx], eax`
  refine c.s_blkA_v hin ((blk_127 prof).at dab_at) Y₃.cpu.vec hK₃ hA₃ hr₃ rfl rfl
    (vc_127 (by rw [hb3']; exact fun i hi => hfw i (by omega)) ?_)
  intro fl Y₄ t₄ hK₄ hA₄ hr₄ hg₄ _ hv₄
  rw [hb3', ha3] at hA₄
  -- `punpcklqdq xmm0, xmm1`
  refine c.s_punpcklqdq hK₄ hA₄ hin (lt_len (by decide)) hr₄ (pu_129 _) ?_
  rintro Y₅ t₅ hK₅ hA₅ ⟨hr₅, hg₅, hx₅, -⟩
  have hxv : xlo Y₅ 0 = (fp + 132#64) ++ (fp + 131#64) := by
    have e4 : ∀ n, xlo Y₄ n = xlo Y₃ n := fun n => by
      show (Y₄.cpu.vec.zmm (xmmOf n)).setWidth 128 = (Y₃.cpu.vec.zmm (xmmOf n)).setWidth 128
      rw [hv₄]
    have h1 : Y₂.cpu.gpr.get (regOf 5) = fp + 132#64 := by rw [hg₂, hg₁]; exact hbp
    have h2 : Y₁.cpu.gpr.get (regOf 12) = fp + 131#64 := by rw [hg₁]; exact h12
    rw [hx₅, e4, e4, hx₃, hk₃ 0 (by decide), hx₂]
    show lane 64 ((Y₂.cpu.gpr.get (regOf 5)).setWidth 64 |>.setWidth 128) 0 ++
      lane 64 ((Y₁.cpu.gpr.get (regOf 12)).setWidth 64 |>.setWidth 128) 0 = (fp + 132#64) ++ (fp + 131#64)
    rw [h1, h2, BitVec.setWidth_eq, BitVec.setWidth_eq, Cxa.lane_lo, Cxa.lane_lo]
  -- `movups [rbx + 0x38], xmm0`
  have e56 : eaD Y₅ 3 56 = fp + 56#64 := by
    show Y₅.cpu.gpr.rbx + 56#64 = _
    rw [hg₅, hg₄, hb3']
  refine c.s_movups_stv hK₅ hA₅ hin (lt_len (by decide)) hr₅ (mv_133 _)
    (by rw [e56]; exact Sas.ft hfw 56 16 (by decide)) ?_
  rintro Y₆ t₆ hK₆ hA₆ ⟨hr₆, hg₆, -⟩
  rw [e56, hxv] at hA₆
  have hA₆' : Agree F Y₆.proc.mm.mem (Vt V fp (Z.cpu.gpr.rax.setWidth 32)) := hA₆
  have e6 : Y₆.cpu.gpr = { Z.cpu.gpr with rax := (Z.cpu.gpr.rax.setWidth 32 ||| 1#32).setWidth 64 } := by
    rw [hg₆, hg₅, hg₄, e3]
  have hs6 : Y₆.cpu.gpr.rsp = r := by rw [e6]; exact hr
  -- `pop rbx; pop rbp; pop r12`
  refine (c_137 prof).run c hin _ hK₆ hA₆' hr₆
    (vc_137 (by rw [hs6]; exact fun i hi => hl i (by omega)) (by rw [hs6]; exact Sas.ft hl 8 8 (by decide))
      (by rw [hs6, Sas.p16]; exact Sas.ft hl 16 8 (by decide))) ?_
  rintro j' g fl V₇ ⟨rfl, rfl, hV⟩ Y t₇ hKY hAY hrY hgY -
  subst V₇
  have hsY : Y.cpu.gpr.rsp = r + 8 + 8 + 8 := by
    rw [hgY]
    show Y₆.cpu.gpr.rsp + 8 + 8 + 8 = _
    rw [hs6]
  have q3 : rdq(Vt V fp (Z.cpu.gpr.rax.setWidth 32), r) = b3 :=
    (rd_t _ hfp (by omega) (by omega)).trans hb3
  have q5 : rdq(Vt V fp (Z.cpu.gpr.rax.setWidth 32), r + 8) = b5 :=
    (rd_t _ hfp (by rw [t8]; omega) (by rw [t8]; omega)).trans hb5
  have q12 : rdq(Vt V fp (Z.cpu.gpr.rax.setWidth 32), r + 8 + 8) = b12 :=
    (rd_t _ hfp (by rw [t16]; omega) (by rw [t16]; omega)).trans hb12
  have q6 : rdq(Vt V fp (Z.cpu.gpr.rax.setWidth 32), r + 8 + 8 + 8) = e₂.add j₂ :=
    (rd_t _ hfp (by rw [t24]; omega) (by rw [t24]; omega)).trans hra
  -- `ret`
  refine c.s_ret hKY hAY hin (lt_len (by decide)) hrY (ret_141 _)
    (by rw [hsY, Sas.p24]; exact Sas.ft hl 24 8 (by decide)) hin₂ h₂ (by rw [hsY]; exact q6) ?_
  rintro Z' t₈ hKZ hAZ ⟨hrZ, hgZ⟩
  refine k Z' t₈ hKZ hAZ hrZ ?_
  rw [hgZ, hsY, hgY, hs6, q3, q5, q12, e6]
  try rfl

/-- `_IO_doallocbuf (fp)` (`fp` = `rdi`) from its entry, `g` the registers. `bb`, `wv`, `md`, `vt`: the buffer, the
flags, `_mode` and the vtable as at the entry.

- `k0`: the buffer not null: at the return address, nothing changed.
- `ks`: the buffer null, `_IO_UNBUFFERED` set and `_mode` at most 0: at the return address with the short buffer
  (`Vt`) and the flags `wv | 1`.
- `kc`: else, the vtable outside `__libc_IO_vtables`: at `_IO_vtable_check`'s entry, the return address (181) pushed.
- `kd`: else at the vtable's `_IO_DOALLOCATE` with `rdi` = `fp`, the return address (80) pushed; if it returns with
  the frame as it was and its post `Pd`:
  - `kr1`: its result not EOF: at the return address, the registers popped.
  - `kr2`: EOF, the buffer then null or `_IO_USER_BUF` set: at the return address with the short buffer.
  - `kf`: EOF, the buffer not null and `_IO_USER_BUF` clear: at `free`'s entry (`rdi` the buffer), the return address
    (165) pushed; if it returns with the frame as it was and its post `Pf`, at the return address with the short
    buffer, the flags read again (`kr3`). -/
theorem dab_ok {Pd Pf : State → (Addr → Byte) → Prop} (c : Seg prof F Wl L s₀ o) (hin : CodeIn L dab_at dab)
    {cC : List Byte} (hinC : CodeIn L vck_at cC) (hC : 0 < cC.length)
    {cF : List Byte} (hinF : CodeIn L fre_at cF) (hF : 0 < cF.length)
    {eD : Addr} {cD : List Byte} (hinD : CodeIn L eD cD) (hD : 0 < cD.length)
    {X : State} {t : Nat} {V : Addr → Byte} {g : Gprs} (hg : X.cpu.gpr = g)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = dab_at)
    (hp : 32 ≤ g.rsp.toNat) (hp8 : g.rsp.toNat + 8 ≤ 2 ^ 64)
    (hs : ∀ i < 32, Foot Wl (Addr.add (g.rsp - 32) i)) (hl : ∀ i < 8, Foot F.data (Addr.add g.rsp i))
    (hfw : ∀ i < 72, Foot Wl (Addr.add g.rdi i)) (hfd : ∀ i < 224, Foot F.data (Addr.add g.rdi i))
    (hfp : g.rdi.toNat + 224 ≤ 2 ^ 64) (hdj : g.rdi.toNat + 224 ≤ g.rsp.toNat - 32 ∨ g.rsp.toNat + 8 ≤ g.rdi.toNat)
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (hra : rdq(V, g.rsp) = e₂.add j₂)
    (hvd : ∀ i < 8, Foot F.data (Addr.add (vt V g + 104#64) i)) (hvp : (vt V g + 104#64).toNat + 8 ≤ 2 ^ 64)
    (hvj : (vt V g + 104#64).toNat + 8 ≤ g.rsp.toNat - 24 ∨ g.rsp.toNat ≤ (vt V g + 104#64).toNat)
    (htD : rdq(V, vt V g + 104#64) = eD)
    (k0 : bb V g ≠ 0 → ∀ (Z : State) (t' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V →
      Z.cpu.rip = e₂.add j₂ → Z.cpu.gpr = g.set 4 (g.rsp + 8) → GoG prof L o gev gP gE Z t')
    (ks : bb V g = 0 → (wv V g).setWidth 8 &&& 2#8 ≠ 0 → (md V g == 0 || (md V g).msb) = true →
      ∀ (Z : State) (t' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem (Vt (Sas.Vp V g) g.rdi (wv V g)) →
      Z.cpu.rip = e₂.add j₂ →
      Z.cpu.gpr = { g with rax := (wv V g ||| 1#32).setWidth 64, rdx := (md V g).setWidth 64, rsp := g.rsp + 8 } →
      GoG prof L o gev gP gE Z t')
    (kc : bb V g = 0 → ((wv V g).setWidth 8 &&& 2#8 = 0 ∨ (md V g == 0 || (md V g).msb) = false) →
      2088 ≤ (vt V g - 7945632#64).toNat →
      ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y →
      Agree F Y.proc.mm.mem (Vst (Sas.Vp V g) (g.rsp - 32) (toBytesLE (dab_at.add 181) 8)) →
      Y.cpu.rip = vck_at → Y.cpu.gpr = (G74 g (vt V g)).set 4 (g.rsp - 32) → GoG prof L o gev gP gE Y t')
    (kd : bb V g = 0 → ((wv V g).setWidth 8 &&& 2#8 = 0 ∨ (md V g == 0 || (md V g).msb) = false) →
      (vt V g - 7945632#64).toNat < 2088 →
      ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y →
      Agree F Y.proc.mm.mem (Vst (Sas.Vp V g) (g.rsp - 32) (toBytesLE (dab_at.add 80) 8)) →
      Y.cpu.rip = eD → Y.cpu.gpr = (G74 g (vt V g)).set 4 (g.rsp - 32) →
      (∀ (Z : State) (V' : Addr → Byte) (t'' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V' →
        Z.cpu.rip = dab_at.add 80 → Z.cpu.gpr.rsp = g.rsp - 24 → Z.cpu.gpr.rbx = g.rdi →
        rdq(V', g.rsp - 24) = g.rbx → rdq(V', g.rsp - 16) = g.rbp → rdq(V', g.rsp - 8) = g.r12 →
        rdq(V', g.rsp) = e₂.add j₂ → Pd Z V' → GoG prof L o gev gP gE Z t'') →
      GoG prof L o gev gP gE Y t')
    (kr1 : ∀ (Z : State) (V' : Addr → Byte), Pd Z V' → Z.cpu.gpr.rax.setWidth 32 ≠ 4294967295#32 →
      ∀ (Z' : State) (t' : Nat), KeptW Wl s₀ Z' → Agree F Z'.proc.mm.mem V' → Z'.cpu.rip = e₂.add j₂ →
      Z'.cpu.gpr = { Z.cpu.gpr with rbx := g.rbx, rbp := g.rbp, r12 := g.r12, rsp := g.rsp + 8 } →
      GoG prof L o gev gP gE Z' t')
    (kr2 : ∀ (Z : State) (V' : Addr → Byte), Pd Z V' → Z.cpu.gpr.rax.setWidth 32 = 4294967295#32 →
      (bb V' g = 0 ∨ (wv V' g).setWidth 8 &&& 1#8 ≠ 0) →
      ∀ (Z' : State) (t' : Nat), KeptW Wl s₀ Z' → Agree F Z'.proc.mm.mem (Vt V' g.rdi (wv V' g)) →
      Z'.cpu.rip = e₂.add j₂ →
      Z'.cpu.gpr = { G85 Z.cpu.gpr (bb V' g) (wv V' g) with
        rax := (wv V' g ||| 1#32).setWidth 64, rbx := g.rbx, rbp := g.rbp, r12 := g.r12, rsp := g.rsp + 8 } →
      GoG prof L o gev gP gE Z' t')
    (kf : ∀ (Z : State) (V' : Addr → Byte), Pd Z V' → Z.cpu.gpr.rax.setWidth 32 = 4294967295#32 →
      bb V' g ≠ 0 → (wv V' g).setWidth 8 &&& 1#8 = 0 →
      ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y →
      Agree F Y.proc.mm.mem (Vst V' (g.rsp - 32) (toBytesLE (dab_at.add 165) 8)) → Y.cpu.rip = fre_at →
      Y.cpu.gpr = (G85 Z.cpu.gpr (bb V' g) (wv V' g)).set 4 (g.rsp - 32) →
      (∀ (U : State) (V'' : Addr → Byte) (t'' : Nat), KeptW Wl s₀ U → Agree F U.proc.mm.mem V'' →
        U.cpu.rip = dab_at.add 165 → U.cpu.gpr.rsp = g.rsp - 24 → U.cpu.gpr.rbx = g.rdi →
        U.cpu.gpr.rbp = g.rdi + 132#64 → U.cpu.gpr.r12 = g.rdi + 131#64 →
        rdq(V'', g.rsp - 24) = g.rbx → rdq(V'', g.rsp - 16) = g.rbp → rdq(V'', g.rsp - 8) = g.r12 →
        rdq(V'', g.rsp) = e₂.add j₂ → Pf U V'' → GoG prof L o gev gP gE U t'') →
      GoG prof L o gev gP gE Y t')
    (kr3 : ∀ (U : State) (V'' : Addr → Byte), Pf U V'' →
      ∀ (Z' : State) (t' : Nat), KeptW Wl s₀ Z' → Agree F Z'.proc.mm.mem (Vt V'' g.rdi (wv V'' g)) →
      Z'.cpu.rip = e₂.add j₂ →
      Z'.cpu.gpr = { U.cpu.gpr with
        rax := (wv V'' g ||| 1#32).setWidth 64, rbx := g.rbx, rbp := g.rbp, r12 := g.r12, rsp := g.rsp + 8 } →
      GoG prof L o gev gP gE Z' t') :
    GoG prof L o gev gP gE X t := by
  subst hg
  have hrip' : X.cpu.rip = dab_at.add 0 := by rw [addr_add_zero]; exact hrip
  have l8 : ∀ v : BitVec 64, (toBytesLE v 8).length = 8 := fun v => toBytesLE_length v 8
  have t8 := Sas.u8 X.cpu.gpr.rsp (by omega)
  have t16 : (X.cpu.gpr.rsp - 8 - 8).toNat = X.cpu.gpr.rsp.toNat - 16 := by
    rw [Sas.s16]; exact Sas.u16 _ (by omega)
  have t24 : (X.cpu.gpr.rsp - 8 - 8 - 8).toNat = X.cpu.gpr.rsp.toNat - 24 := by
    rw [Sas.s24]; exact Sas.u24 _ (by omega)
  have u24 := Sas.u24 X.cpu.gpr.rsp (by omega)
  have t192 : (X.cpu.gpr.rdi + 192#64).toNat = X.cpu.gpr.rdi.toNat + 192 := Sas.tn_add _ 192 (by omega)
  have t216 : (X.cpu.gpr.rdi + 216#64).toNat = X.cpu.gpr.rdi.toNat + 216 := Sas.tn_add _ 216 (by omega)
  -- the bytes and the frame
  have h1 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8) i) := by rw [Sas.m8]; exact Sas.ft hs 24 8 (by decide)
  have h2 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8 - 8) i) := by
    rw [Sas.m16]; exact Sas.ft hs 16 8 (by decide)
  have h3 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8 - 8 - 8) i) := by
    rw [Sas.m24]; exact Sas.ft hs 8 8 (by decide)
  have l1 : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rdi + 56#64) i) := Sas.ft hfd 56 8 (by decide)
  have l2 : ∀ i < 4, Foot F.data (Addr.add X.cpu.gpr.rdi i) := fun i hi => hfd i (by omega)
  have l3 : ∀ i < 4, Foot F.data (Addr.add (X.cpu.gpr.rdi + 192#64) i) := Sas.ft hfd 192 4 (by decide)
  have l4 : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rdi + 216#64) i) := Sas.ft hfd 216 8 (by decide)
  have hl' : ∀ i < 32, Foot F.data (Addr.add (X.cpu.gpr.rsp - 24) i) := fr24 (fun i hi => c.hws _ (hs i hi)) hl
  have hp' : (X.cpu.gpr.rsp - 24).toNat + 32 ≤ 2 ^ 64 := by rw [u24]; omega
  have hfp72 : X.cpu.gpr.rdi.toNat + 72 ≤ 2 ^ 64 := by omega
  have hdj' : X.cpu.gpr.rdi.toNat + 72 ≤ (X.cpu.gpr.rsp - 24).toNat ∨
      (X.cpu.gpr.rsp - 24).toNat + 32 ≤ X.cpu.gpr.rdi.toNat := by rw [u24]; omega
  -- the loads after the pushes
  have rp : ∀ (z : Addr) (n : Nat), z.toNat + n ≤ 2 ^ 64 →
      (z.toNat + n ≤ X.cpu.gpr.rsp.toNat - 24 ∨ X.cpu.gpr.rsp.toNat ≤ z.toNat) →
      List.map (Sas.Vp V X.cpu.gpr) (byteAddrs z n) = List.map V (byteAddrs z n) := fun z n hz hd => by
    dsimp only [Sas.Vp]
    rw [Tun.rd_Vst _ (X.cpu.gpr.rsp - 8 - 8 - 8) (toBytesLE X.cpu.gpr.rbx 8) z n (by rw [l8, t24]; omega) hz
        (by rw [l8, t24]; omega),
      Tun.rd_Vst _ (X.cpu.gpr.rsp - 8 - 8) (toBytesLE X.cpu.gpr.rbp 8) z n (by rw [l8, t16]; omega) hz
        (by rw [l8, t16]; omega),
      Tun.rd_Vst _ (X.cpu.gpr.rsp - 8) (toBytesLE X.cpu.gpr.r12 8) z n (by rw [l8, t8]; omega) hz
        (by rw [l8, t8]; omega)]
  have hw : ofBytesLE 32 ((byteAddrs X.cpu.gpr.rdi 4).map (Sas.Vp V X.cpu.gpr)) = wv V X.cpu.gpr := by
    rw [rp X.cpu.gpr.rdi 4 (by omega) (by omega)]
  have hm : ofBytesLE 32 ((byteAddrs (X.cpu.gpr.rdi + 192#64) 4).map (Sas.Vp V X.cpu.gpr)) = md V X.cpu.gpr := by
    rw [rp (X.cpu.gpr.rdi + 192#64) 4 (by rw [t192]; omega) (by rw [t192]; omega)]
  have hv : rdq(Sas.Vp V X.cpu.gpr, X.cpu.gpr.rdi + 216#64) = vt V X.cpu.gpr := by
    rw [rp (X.cpu.gpr.rdi + 216#64) 8 (by rw [t216]; omega) (by rw [t216]; omega)]
  -- the buffer not null: the `ret` at 11
  by_cases hb0 : bb V X.cpu.gpr = 0
  rotate_left
  · refine (c_0 prof).run c hin _ hK hA hrip' (vc_0r l1 rfl (decide_eq_false hb0)) ?_
    rintro j' g₁ fl V₁ ⟨rfl, rfl, hV⟩ Y t₁ hKY hAY hrY hgY -
    subst V₁
    refine c.s_ret hKY hAY hin (lt_len (by decide)) hrY (ret_11 _) (by rw [hgY]; exact hl) hin₂ h₂
      (by rw [hgY]; exact hra) ?_
    rintro Z t₂ hKZ hAZ ⟨hrZ, hgZ⟩
    exact k0 hb0 Z t₂ hKZ hAZ hrZ (by rw [hgZ, hgY])
  -- from 39: the vtable checked and called
  have go39 : ∀ (Y : State) (t₁ : Nat) (w : BitVec 32) (dx : BitVec 64), KeptW Wl s₀ Y →
      Agree F Y.proc.mm.mem (Sas.Vp V X.cpu.gpr) → Y.cpu.rip = dab_at.add 39 →
      Y.cpu.gpr = { G1 X.cpu.gpr w with rdx := dx } →
      ((wv V X.cpu.gpr).setWidth 8 &&& 2#8 = 0 ∨ (md V X.cpu.gpr == 0 || (md V X.cpu.gpr).msb) = false) →
      GoG prof L o gev gP gE Y t₁ := by
    intro Y t₁ w dx hKY hAY hrY hgY hc
    have hyb : Y.cpu.gpr.rbx = X.cpu.gpr.rdi := by rw [hgY]
    have hv1 : rdq(Sas.Vp V X.cpu.gpr, Y.cpu.gpr.rbx + 216#64) = vt V X.cpu.gpr := by rw [hyb]; exact hv
    have l4' : ∀ i < 8, Foot F.data (Addr.add (Y.cpu.gpr.rbx + 216#64) i) := by rw [hyb]; exact l4
    by_cases hr : (vt V X.cpu.gpr - 7945632#64).toNat < 2088
    · refine (c_39 prof).run c hin _ hKY hAY hrY (vc_39i l4' hv1 hr) ?_
      rintro j' g₂ fl V₂ ⟨rfl, rfl, rfl⟩ Y₂ t₂ hK₂ hA₂ hr₂ hg₂ -
      refine (c_74 prof).run c hin _ hK₂ hA₂ hr₂ vc_74 ?_
      rintro j' g₃ fl V₃ ⟨rfl, rfl, rfl⟩ Y₃ t₃ hK₃ hA₃ hr₃ hg₃ -
      have hg3 : Y₃.cpu.gpr = G74 X.cpu.gpr (vt V X.cpu.gpr) := by
        rw [hg₃, hg₂, hgY]
        try rfl
      have hs3 : Y₃.cpu.gpr.rsp = X.cpu.gpr.rsp - 24 := by rw [hg3]; exact Sas.s24 _
      have he : eaD Y₃ 5 104 = vt V X.cpu.gpr + 104#64 := by
        show Y₃.cpu.gpr.rbp + 104#64 = _
        rw [hg3]
        try rfl
      -- `call qword [rbp + 0x68]`
      refine c.s_callM hK₃ hA₃ hin (lt_len (by decide)) hr₃ (call_77 _) (by rw [he]; exact hvd) hinD hD
        (by rw [he, rp _ 8 hvp hvj]; exact htD) (by rw [hs3, Sas.s32]; exact fun i hi => hs i (by omega)) ?_
      rintro Y₄ t₄ hK₄ hA₄ ⟨hr₄, hg₄⟩
      rw [hs3, Sas.s32] at hA₄
      refine kd hb0 hc hr Y₄ t₄ hK₄ hA₄ hr₄ (by rw [hg₄, hs3, Sas.s32, hg3]) ?_
      -- back from `_IO_DOALLOCATE`
      intro Z V' t'' hKZ hAZ hrZ hzs hzb e3 e5 e12 e6 hPd
      by_cases he1 : Z.cpu.gpr.rax.setWidth 32 = 4294967295#32
      rotate_left
      · -- not EOF: the pops and the `ret`
        refine (c_80 prof).run c hin _ hKZ hAZ hrZ (vc_80n he1) ?_
        rintro j' g₅ fl V₅ ⟨rfl, rfl, hV⟩ Y₅ t₅ hK₅ hA₅ hr₅ hg₅ -
        subst V₅
        have hs5 : Y₅.cpu.gpr.rsp = X.cpu.gpr.rsp - 24 := by rw [hg₅]; exact hzs
        refine (c_137 prof).run c hin _ hK₅ hA₅ hr₅
          (vc_137 (by rw [hs5]; exact fun i hi => hl' i (by omega)) (by rw [hs5]; exact Sas.ft hl' 8 8 (by decide))
            (by rw [hs5, Sas.p16]; exact Sas.ft hl' 16 8 (by decide))) ?_
        rintro j' g₆ fl V₆ ⟨rfl, rfl, hV⟩ Y₆ t₆ hK₆ hA₆ hr₆ hg₆ -
        subst V₆
        have hs6 : Y₆.cpu.gpr.rsp = X.cpu.gpr.rsp - 24 + 8 + 8 + 8 := by
          rw [hg₆]
          show Y₅.cpu.gpr.rsp + 8 + 8 + 8 = _
          rw [hs5]
        refine c.s_ret hK₆ hA₆ hin (lt_len (by decide)) hr₆ (ret_141 _) (by rw [hs6, q24]; exact hl) hin₂ h₂
          (by rw [hs6, q24]; exact e6) ?_
        rintro Z' t₇ hKZ' hAZ' ⟨hrZ', hgZ'⟩
        refine kr1 Z V' hPd he1 Z' t₇ hKZ' hAZ' hrZ' ?_
        rw [hgZ', hs6, hg₆, hg₅, hzs, q32, q16, Sas.a16, e3, e5, e12]
        try rfl
      -- EOF: the buffer and the flags read again
      have l1' : ∀ i < 8, Foot F.data (Addr.add (Z.cpu.gpr.rbx + 56#64) i) := by rw [hzb]; exact l1
      have l2' : ∀ i < 4, Foot F.data (Addr.add Z.cpu.gpr.rbx i) := by rw [hzb]; exact l2
      have hb' : rdq(V', Z.cpu.gpr.rbx + 56#64) = bb V' X.cpu.gpr := by rw [hzb]
      have hw' : ofBytesLE 32 ((byteAddrs Z.cpu.gpr.rbx 4).map V') = wv V' X.cpu.gpr := by rw [hzb]
      have t114 : ∀ (U : State) (t₅ : Nat), KeptW Wl s₀ U → Agree F U.proc.mm.mem V' →
          U.cpu.rip = dab_at.add 114 → U.cpu.gpr = G85 Z.cpu.gpr (bb V' X.cpu.gpr) (wv V' X.cpu.gpr) →
          (bb V' X.cpu.gpr = 0 ∨ (wv V' X.cpu.gpr).setWidth 8 &&& 1#8 ≠ 0) → GoG prof L o gev gP gE U t₅ :=
        fun U t₅ hKU hAU hrU hgU hcU =>
          dab_t (r := X.cpu.gpr.rsp - 24) (fp := X.cpu.gpr.rdi) (x := wv V' X.cpu.gpr)
            c hin hKU hAU hrU (by rw [hgU]; exact hzs) (by rw [hgU]; exact hzb)
            (by rw [hgU]; show Z.cpu.gpr.rbx + 132#64 = _; rw [hzb])
            (by rw [hgU]; show Z.cpu.gpr.rbx + 131#64 = _; rw [hzb])
            (by rw [hgU]; exact sw_64_32 _) hp' hl' hfw hfp72 hdj' e3 (by rw [Sas.a16]; exact e5)
            (by rw [q16]; exact e12) hin₂ h₂ (by rw [q24]; exact e6)
            fun Z' t' hKZ' hAZ' hrZ' hgZ' =>
              kr2 Z V' hPd he1 hcU Z' t' hKZ' hAZ' hrZ' (by rw [hgZ', hgU, q32]; try rfl)
      by_cases hb0' : bb V' X.cpu.gpr = 0
      · refine (c_80 prof).run c hin _ hKZ hAZ hrZ (vc_80a he1 l1' l2' hb' hw' (beq_iff_eq.mpr hb0')) ?_
        rintro j' g₅ fl V₅ ⟨rfl, rfl, hV⟩ U t₅ hKU hAU hrU hgU -
        subst V₅
        exact t114 U t₅ hKU hAU hrU hgU (.inl hb0')
      have hb0f : (bb V' X.cpu.gpr == 0) = false := by rw [beq_eq_false_iff_ne]; exact hb0'
      by_cases hf1 : (wv V' X.cpu.gpr).setWidth 8 &&& 1#8 = 0
      rotate_left
      · have hf1' : ((wv V' X.cpu.gpr).setWidth 8 &&& 1#8 == 0) = false := by
          rw [beq_eq_false_iff_ne]; exact hf1
        refine (c_80 prof).run c hin _ hKZ hAZ hrZ (vc_80b he1 l1' l2' hb' hw' hb0f hf1') ?_
        rintro j' g₅ fl V₅ ⟨rfl, rfl, hV⟩ U t₅ hKU hAU hrU hgU -
        subst V₅
        exact t114 U t₅ hKU hAU hrU hgU (.inr hf1)
      -- `free` of the buffer
      refine (c_80 prof).run c hin _ hKZ hAZ hrZ (vc_80c he1 l1' l2' hb' hw' hb0f (beq_iff_eq.mpr hf1)) ?_
      rintro j' g₅ fl V₅ ⟨rfl, rfl, hV⟩ Y₅ t₅ hK₅ hA₅ hr₅ hg₅ -
      subst V₅
      have hs5 : Y₅.cpu.gpr.rsp = X.cpu.gpr.rsp - 24 := by rw [hg₅]; exact hzs
      refine c.s_call hK₅ hA₅ hin (lt_len (by decide)) hr₅ (call_160 _) hinF hF (by decide)
        (by rw [hs5, Sas.s32]; exact fun i hi => hs i (by omega)) ?_
      rintro Y₆ t₆ hK₆ hA₆ ⟨hr₆, hg₆⟩
      rw [hs5, Sas.s32] at hA₆
      refine kf Z V' hPd he1 hb0' hf1 Y₆ t₆ hK₆ hA₆ hr₆ (by rw [hg₆, hs5, Sas.s32, hg₅]) ?_
      -- back from `free`
      intro U V'' t₇ hKU hAU hrU hus hub hup hu12 f3 f5 f12 f6 hPf
      refine (c_165 prof).run c hin _ hKU hAU hrU (vc_165 (by rw [hub]; exact l2)) ?_
      rintro j' g₇ fl V₇ ⟨rfl, rfl, hV⟩ W t₈ hKW hAW hrW hgW -
      subst V₇
      exact dab_t (r := X.cpu.gpr.rsp - 24) (fp := X.cpu.gpr.rdi) (x := wv V'' X.cpu.gpr)
        c hin hKW hAW hrW (by rw [hgW]; exact hus) (by rw [hgW]; exact hub) (by rw [hgW]; exact hup)
        (by rw [hgW]; exact hu12)
        (by
          rw [hgW]
          show ((ofBytesLE 32 ((byteAddrs U.cpu.gpr.rbx 4).map V'')).setWidth 64).setWidth 32 = _
          rw [sw_64_32, hub])
        hp' hl' hfw hfp72 hdj' f3 (by rw [Sas.a16]; exact f5) (by rw [q16]; exact f12) hin₂ h₂
        (by rw [q24]; exact f6)
        fun Z' t' hKZ' hAZ' hrZ' hgZ' => kr3 U V'' hPf Z' t' hKZ' hAZ' hrZ' (by rw [hgZ', hgW, q32]; try rfl)
    · -- outside `__libc_IO_vtables`: `_IO_vtable_check`
      have hr' : 2088 ≤ (vt V X.cpu.gpr - 7945632#64).toNat := by omega
      refine (c_39 prof).run c hin _ hKY hAY hrY (vc_39o l4' hv1 hr') ?_
      rintro j' g₂ fl V₂ ⟨rfl, rfl, rfl⟩ Y₂ t₂ hK₂ hA₂ hr₂ hg₂ -
      have hg2 : Y₂.cpu.gpr = G74 X.cpu.gpr (vt V X.cpu.gpr) := by
        rw [hg₂, hgY]
        try rfl
      have hs2 : Y₂.cpu.gpr.rsp = X.cpu.gpr.rsp - 24 := by rw [hg2]; exact Sas.s24 _
      refine c.s_call hK₂ hA₂ hin (lt_len (by decide)) hr₂ (call_176 _) hinC hC (by decide)
        (by rw [hs2, Sas.s32]; exact fun i hi => hs i (by omega)) ?_
      rintro Y₃ t₃ hK₃ hA₃ ⟨hr₃, hg₃⟩
      rw [hs2, Sas.s32] at hA₃
      exact kc hb0 hc hr' Y₃ t₃ hK₃ hA₃ hr₃ (by rw [hg₃, hs2, Sas.s32, hg2])
  -- the buffer null
  by_cases hf2 : (wv V X.cpu.gpr).setWidth 8 &&& 2#8 = 0
  · refine (c_0 prof).run c hin _ hK hA hrip'
      (vc_0a h1 h2 h3 l1 l2 rfl (decide_eq_true hb0) hw (beq_iff_eq.mpr hf2)) ?_
    rintro j' g₁ fl V₁ ⟨rfl, rfl, rfl⟩ Y t₁ hKY hAY hrY hgY -
    exact go39 Y t₁ _ _ hKY hAY hrY hgY (.inl hf2)
  have hf2' : ((wv V X.cpu.gpr).setWidth 8 &&& 2#8 == 0) = false := by rw [beq_eq_false_iff_ne]; exact hf2
  by_cases hle : (md V X.cpu.gpr == 0 || (md V X.cpu.gpr).msb) = true
  · -- the short buffer
    refine (c_0 prof).run c hin _ hK hA hrip'
      (vc_0c h1 h2 h3 l1 l2 l3 rfl (decide_eq_true hb0) hw hm hf2' hle) ?_
    rintro j' g₁ fl V₁ ⟨rfl, rfl, rfl⟩ Y t₁ hKY hAY hrY hgY -
    obtain ⟨r3, r5, r12, r6⟩ := Sas.vp_rd (V := V) (g := X.cpu.gpr) hp hp8
    exact dab_t (r := X.cpu.gpr.rsp - 24) (fp := X.cpu.gpr.rdi) (x := wv V X.cpu.gpr)
      c hin hKY hAY hrY (by rw [hgY]; exact Sas.s24 _) (by rw [hgY]) (by rw [hgY]) (by rw [hgY])
      (by rw [hgY]; exact sw_64_32 _) hp' hl' hfw hfp72 hdj' r3 r5 (by rw [Sas.p16]; exact r12) hin₂ h₂
      (by rw [Sas.p24]; exact r6.trans hra)
      fun Z' t' hKZ hAZ hrZ hgZ => ks hb0 hf2 hle Z' t' hKZ hAZ hrZ (by rw [hgZ, hgY, q32]; try rfl)
  · have hle' : (md V X.cpu.gpr == 0 || (md V X.cpu.gpr).msb) = false := Bool.eq_false_iff.mpr hle
    refine (c_0 prof).run c hin _ hK hA hrip'
      (vc_0b h1 h2 h3 l1 l2 l3 rfl (decide_eq_true hb0) hw hm hf2' hle') ?_
    rintro j' g₁ fl V₁ ⟨rfl, rfl, rfl⟩ Y t₁ hKY hAY hrY hgY -
    exact go39 Y t₁ _ _ hKY hAY hrY hgY (.inr hle')

end FV7z.Dab
