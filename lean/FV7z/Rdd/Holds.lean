import FV7z.Rdd.Cuts
import FV7z.Rdd.Ch
import FV7z.Gdn.Holds
import FV7z.Lemmas.Lock3
import FV7z.Sbrk.Holds
/-!
# `__readdir`: the instructions outside the blocks and the pieces between the cut points (PLAN.md §M, M1)

glibc 2.31's `__readdir (dirp)` at `0x6638a0` in `7zzs` (`sysdeps/posix/readdir.c`; `objdump -d`), one thread
(`fs:0x18` is 0): five pushes (`r14`, `r13`, `r12`, `rbp`, `rbx`, `P5`), `errno` saved in `r13d`, the `DIR`'s lock
taken by an unlocked `cmpxchg [rdi + 4], edx` (52); then the entries in the buffer (`dirp + 48`): at 109 the offset
(`rdx`) against the size (`rax`), at 80 the entry at the offset (`d_reclen` added to the offset, `d_off` to
`filepos`), `d_ino` not 0 its end; the buffer used up, `__getdents (fd, buf, allocation)` (128): a positive answer
the new size (138), 0 or an error `errno` restored (162, but an error other than `ENOENT`), the result 0; at 176 the
lock given back (`sub dword [r14 + 4], 1`, 188), the pops (193), the `ret` (204).

- `cx_52`, `call_128` (`tgt_128`), `sb_188`, `ret_204`: the instructions outside the blocks.
- `vc_0`, `vc_56`, `vc_80z`, `vc_80n`, `vc_109l`, `vc_109g`, `vc_133p`, `vc_133z`, `vc_133e`, `vc_133o`, `vc_162`,
  `vc_176`, `vc_193`: each piece from a cut point to the next, its registers and bytes after.
- `dn_ret`: `getdents64`'s answer not an error is the entries' size.

Not covered: more than one thread (`fs:0x18` not 0: 217, 253, the locked `cmpxchg` and `__lll_lock_wait`).
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn FV7z.Close
namespace FV7z.Rdd

/-- The unlocked `cmpxchg [rdi + 4], edx`. -/
def pcx : List Byte := [0x0f, 0xb1, 0x57, 0x04]
theorem pcx_0 : ∀ feat, Dec feat pcx 0 (FV7z.mk .cmpxchg 32 [.mem (mbd 7 4 32), gr 32 2] 4) := by dec_rfl
theorem w_52 : pcx <+: rdd.drop 52 := by decide +kernel
theorem cx_52 (feat : Features) : Dec feat rdd 52 (FV7z.mk .cmpxchg 32 [.mem (mbd 7 4 32), gr 32 2] 4) :=
  Dec.shift (j := 52) (k := 0) (pcx_0 feat) w_52 (Nat.zero_le _)

/-- The `call __getdents`. -/
def pcg : List Byte := [0xe8, 0xfb, 0xee, 0x03, 0x00]
theorem pcg_0 : ∀ feat, Dec feat pcg 0 (FV7z.mk .call 64 [.rel 257787] 5) := by dec_rfl
theorem wc_128 : pcg <+: rdd.drop 128 := by decide +kernel
theorem call_128 (feat : Features) : Dec feat rdd 128 (FV7z.mk .call 64 [.rel 257787] 5) :=
  Dec.shift (j := 128) (k := 0) (pcg_0 feat) wc_128 (Nat.zero_le _)
theorem tgt_128 : rdd_at.add (128 + 5) + BitVec.ofNat 64 257787 = Gdn.gdn_at := by decide

/-- `sub dword [r14 + 4], 1`. -/
def psb : List Byte := [0x41, 0x83, 0x6e, 0x04, 0x01]
theorem psb_0 : ∀ feat, Dec feat psb 0 (FV7z.mk .sub 32 [.mem (mbd 14 4 32), .imm 32 1] 5) := by dec_rfl
theorem w_188 : psb <+: rdd.drop 188 := by decide +kernel
theorem sb_188 (feat : Features) : Dec feat rdd 188 (FV7z.mk .sub 32 [.mem (mbd 14 4 32), .imm 32 1] 5) :=
  Dec.shift (j := 188) (k := 0) (psb_0 feat) w_188 (Nat.zero_le _)

/-- The `ret`. -/
def pret : List Byte := [0xc3]
theorem pret_0 : ∀ feat, Dec feat pret 0 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem w_204 : pret <+: rdd.drop 204 := by decide +kernel
theorem ret_204 (feat : Features) : Dec feat rdd 204 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 204) (k := 0) (pret_0 feat) w_204 (Nat.zero_le _)

/-! ## `getdents64`'s answer -/

/-- An `Errno` as an answer is an error. -/
theorem errRet_ce (e : Errno) : CloseErr (errRet e.val) := by
  have h0 := e.2.1
  have h1 := e.2.2
  have h : (errRet e.val).toNat = 18446744073709551616 - e.val := by
    show (BitVec.ofNat 64 0 - BitVec.ofNat 64 e.val).toNat = _
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    simp only [Nat.reducePow, Nat.zero_mod]
    omega
  unfold CloseErr
  omega

/-- `getdents64`'s answer, not an error, is the size of the entries it delivers. -/
theorem dn_ret {o : Oracle} {t : Nat} {s : State} {n : Nat} (h : ¬ CloseErr (dentsResN o t s n).ret) :
    (dentsResN o t s n).ret = BitVec.ofNat 64 ((dentsResN o t s n).es.map Dirent.reclen).sum := by
  revert h
  unfold dentsResN
  split
  · intro h
    exact absurd (errRet_ce ⟨9, by decide, by decide⟩) h
  · split
    · intro h
      exact absurd (errRet_ce ⟨20, by decide, by decide⟩) h
    · split
      · intro h
        exact absurd (errRet_ce _) h
      · intro _
        rfl

/-! ## The pieces -/

variable {F : Footprint} {Wl : List Rgn}

/-- What is left of a piece's condition: its footprint facts, equations, cases that cannot be. -/
local macro "vfin" : tactic =>
  `(tactic| repeat' (first | (with_reducible rfl) | (with_reducible assumption) | exact True.intro |
    (intro h; exact absurd h (by omega)) | contradiction | apply And.intro | assumption | rfl | intro _))

theorem s0 : BitVec.setWidth 64 0#32 = 0#64 := by decide
theorem s1 : BitVec.setWidth 64 1#32 = 1#64 := by decide
theorem s48 : BitVec.setWidth 64 48#32 = 48#64 := by decide
theorem xz (x : BitVec 32) : BitVec.setWidth 64 (x ^^^ x) = 0#64 := by simp
theorem z0 : ((0#32 : BitVec 32) == 0) = true := by decide
theorem z64 : ((0#64 : BitVec 64) == 0) = true := by decide
theorem sz : BitVec.setWidth 32 0#64 = 0#32 := by decide
theorem ffb : (false != false) = false := rfl
theorem tbf : (true != false) = true := rfl

/-- The bytes after the five pushes. -/
abbrev P5 (V : Addr → Byte) (g : Gprs) : Addr → Byte :=
  Vst (Vst (Vst (Vst (Vst V (g.rsp - 8) (toBytesLE g.r14 8)) (g.rsp - 8 - 8) (toBytesLE g.r13 8))
    (g.rsp - 8 - 8 - 8) (toBytesLE g.r12 8)) (g.rsp - 8 - 8 - 8 - 8) (toBytesLE g.rbp 8))
    (g.rsp - 8 - 8 - 8 - 8 - 8) (toBytesLE g.rbx 8)

/-- At the `cmpxchg`: `eax` 0 (`fs:0x18`), `edx` 1, `rbp` the offset of `errno` (-72), `r12` the lock, `r13`
`errno` (`e0`), `r14` the `DIR`. -/
abbrev gA (g : Gprs) (e0 : BitVec 32) : Gprs :=
  { g with
    rax := 0#64
    rdx := 1#64
    rsp := g.rsp - 8 - 8 - 8 - 8 - 8
    rbp := 18446744073709551544#64
    r12 := g.rdi + 4#64
    r13 := e0.setWidth 64
    r14 := g.rdi }

/-- From the entry to the `cmpxchg`: the pushes, `errno` saved, one thread. -/
theorem vc_0 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {e0 : BitVec 32}
    (he : rdd(P5 V g, errnoAt fb) = e0) (hmt : rdd(P5 V g, fb + 24#64) = 0#32)
    (w1 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8) i)) (w2 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8) i))
    (w3 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8 - 8) i))
    (w4 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8 - 8 - 8) i))
    (w5 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8 - 8 - 8 - 8) i))
    (fe : ∀ i < 4, Foot F.data (Addr.add (errnoAt fb) i)) (fm : ∀ i < 4, Foot F.data (Addr.add (fb + 24#64) i)) :
    W_0 fb F Wl (fun j' g' _ V' => j' = 52 ∧ g' = gA g e0 ∧ V' = P5 V g) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [P5, gA, errnoAt] at he hmt w1 w2 w3 w4 w5 fe ⊢
  wpx [W_0, W_47, o0, o1, Op.ldf, he, hmt, BitVec.and_self, z0, s0, sz, s1, Bool.not_true, Bool.false_eq_true,
    false_implies, eq_self_iff_true, true_implies, implies_true]
  all_goals vfin

/-- From after the `cmpxchg` (56) to 109: the offset (`rdx`), the size (`rax`), the buffer (`rbx`). -/
theorem vc_56 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (f24 : ∀ i < 8, Foot F.data (Addr.add (g.r14 + 24#64) i))
    (f16 : ∀ i < 8, Foot F.data (Addr.add (g.r14 + 16#64) i)) :
    W_56 fb F Wl (fun j' g' _ V' => j' = 109 ∧
      g' = { g with rdx := rdq(V, g.r14 + 24#64), rax := rdq(V, g.r14 + 16#64), rbx := g.r14 + 48#64 } ∧
      V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at f24 f16 ⊢
  wpx [W_56, o2]
  all_goals vfin

/-- `d_reclen` of the entry at `r8 + r14`, as `movzx ecx, word [r8 + 16]` loads it. -/
abbrev rcl (V : Addr → Byte) (g : Gprs) : BitVec 64 :=
  ((ofBytesLE 16 ((byteAddrs (g.r8 + g.r14 + 16#64) 2).map V)).setWidth 32).setWidth 64

/-- After 80: `r8` the entry, `rcx` its `d_off`, `rdx` the offset past it. -/
abbrev gB (V : Addr → Byte) (g : Gprs) : Gprs :=
  { g with r8 := g.r8 + g.r14, rcx := rdq(V, g.r8 + g.r14 + 8#64), rdx := g.rdx + rcl V g }

/-- After 80: the offset and `filepos` stored. -/
abbrev VB (V : Addr → Byte) (g : Gprs) : Addr → Byte :=
  Vst (Vst V (g.r14 + 24#64) (toBytesLE (g.rdx + rcl V g) 8)) (g.r14 + 32#64)
    (toBytesLE rdq(V, g.r8 + g.r14 + 8#64) 8)

/-- The entry at 80 with `d_ino` 0: to 109. -/
theorem vc_80z {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} (hz : rdq(V, g.r8 + g.r14) = 0#64)
    (f0 : ∀ i < 8, Foot F.data (Addr.add (g.r8 + g.r14) i))
    (f8 : ∀ i < 8, Foot F.data (Addr.add (g.r8 + g.r14 + 8#64) i))
    (f16 : ∀ i < 2, Foot F.data (Addr.add (g.r8 + g.r14 + 16#64) i))
    (w24 : ∀ i < 8, Foot Wl (Addr.add (g.r14 + 24#64) i)) (w32 : ∀ i < 8, Foot Wl (Addr.add (g.r14 + 32#64) i)) :
    W_80 fb F Wl (fun j' g' _ V' => j' = 109 ∧ g' = gB V g ∧ V' = VB V g) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [gB, VB, rcl] at hz f0 f8 f16 w24 w32 ⊢
  have hd : decide (rdq(V, r8 + r14) = 0#64) = true := decide_eq_true hz
  wpx [W_80, o3, Op.cmpmi, hd, Bool.not_true, Bool.false_eq_true, Bool.true_eq_false,
    false_implies, eq_self_iff_true, true_implies]
  all_goals vfin

/-- The entry at 80 with `d_ino` not 0: to 176. -/
theorem vc_80n {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} (hz : rdq(V, g.r8 + g.r14) ≠ 0#64)
    (f0 : ∀ i < 8, Foot F.data (Addr.add (g.r8 + g.r14) i))
    (f8 : ∀ i < 8, Foot F.data (Addr.add (g.r8 + g.r14 + 8#64) i))
    (f16 : ∀ i < 2, Foot F.data (Addr.add (g.r8 + g.r14 + 16#64) i))
    (w24 : ∀ i < 8, Foot Wl (Addr.add (g.r14 + 24#64) i)) (w32 : ∀ i < 8, Foot Wl (Addr.add (g.r14 + 32#64) i)) :
    W_80 fb F Wl (fun j' g' _ V' => j' = 176 ∧ g' = gB V g ∧ V' = VB V g) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [gB, VB, rcl] at hz f0 f8 f16 w24 w32 ⊢
  have hd : decide (rdq(V, r8 + r14) = 0#64) = false := decide_eq_false hz
  wpx [W_80, o3, Op.cmpmi, hd, Bool.not_false, Bool.false_eq_true, Bool.true_eq_false,
    false_implies, eq_self_iff_true, true_implies]
  all_goals vfin

/-- At 109, the offset below the size: to 80, `r8` the offset plus 48. -/
theorem vc_109l {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} (hl : g.rdx.toNat < g.rax.toNat) :
    W_109 fb F Wl (fun j' g' _ V' => j' = 80 ∧ g' = { g with r8 := g.rdx + 48#64 } ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hl ⊢
  have hd : decide (rdx.toNat < rax.toNat) = true := decide_eq_true hl
  wpx [W_109, o4, hd, Bool.false_eq_true, Bool.true_eq_false, false_implies, eq_self_iff_true, true_implies]
  all_goals vfin

/-- At the `call __getdents`: `edi` the descriptor, `rsi` the buffer, `rdx` the allocation. -/
abbrev gG (V : Addr → Byte) (g : Gprs) : Gprs :=
  { g with
    r8 := g.rdx + 48#64
    rdx := rdq(V, g.r14 + 8#64)
    rdi := BitVec.setWidth 64 rdd(V, g.r14)
    rsi := g.rbx }

/-- At 109, the buffer used up: to the `call __getdents (fd, buf, allocation)`. -/
theorem vc_109g {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} (hl : ¬ g.rdx.toNat < g.rax.toNat)
    (f8 : ∀ i < 8, Foot F.data (Addr.add (g.r14 + 8#64) i)) (f0 : ∀ i < 4, Foot F.data (Addr.add g.r14 i)) :
    W_109 fb F Wl (fun j' g' _ V' => j' = 128 ∧ g' = gG V g ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [gG] at hl f8 f0 ⊢
  have hd : decide (rdx.toNat < rax.toNat) = false := decide_eq_false hl
  wpx [W_109, W_118, o4, o5, hd, Bool.false_eq_true, Bool.true_eq_false, false_implies, eq_self_iff_true, true_implies]
  all_goals vfin

/-- `getdents64`'s answer positive: the new size stored, to 80 with the offset 0. -/
theorem vc_133p {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} (hnz : g.rax ≠ 0#64)
    (hs : g.rax.msb = false) (w16 : ∀ i < 8, Foot Wl (Addr.add (g.r14 + 16#64) i)) :
    W_133 fb F Wl (fun j' g' _ V' => j' = 80 ∧ g' = { g with rdx := 0#64, r8 := 48#64 } ∧
      V' = Vst V (g.r14 + 16#64) (toBytesLE g.rax 8)) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hnz hs w16 ⊢
  have hb0 : (rax == 0) = false := beq_false_of_ne hnz
  wpx [W_133, W_138, Sbrk.cond_14, Sbrk.rfz_of, Sbrk.arith_of, o6, o7, BitVec.and_self, hb0, hs, xz, s48,
    Bool.false_or, Bool.or_false, ffb, Bool.false_eq_true, Bool.true_eq_false, false_implies, eq_self_iff_true,
    true_implies]
  all_goals vfin

/-- `getdents64`'s answer 0: to 162. -/
theorem vc_133z {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} (hz : g.rax = 0#64) :
    W_133 fb F Wl (fun j' g' _ V' => j' = 162 ∧ g' = g ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hz ⊢
  subst hz
  wpx [W_133, W_160, Sbrk.cond_14, Sbrk.rfz_of, Sbrk.arith_of, o6, BitVec.and_self, z64, Bool.true_or,
    Bool.not_true, Bool.false_eq_true, Bool.true_eq_false, false_implies, eq_self_iff_true, true_implies]
  all_goals vfin

/-- An error, `errno` `ENOENT`: to 162, `r8` 0. -/
theorem vc_133e {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} (hs : g.rax.msb = true)
    (hbp : g.rbp = 18446744073709551544#64) (he : rdd(V, errnoAt fb) = 2#32)
    (fe : ∀ i < 4, Foot F.data (Addr.add (errnoAt fb) i)) :
    W_133 fb F Wl (fun j' g' _ V' => j' = 162 ∧ g' = { g with r8 := 0#64 } ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [errnoAt] at hs hbp he fe ⊢
  subst hbp
  have hnz : rax ≠ 0#64 := fun h => by rw [h] at hs; exact absurd hs (by decide)
  have hb0 : (rax == 0) = false := beq_false_of_ne hnz
  wpx [W_133, W_160, W_205, W_215, Sbrk.cond_14, Sbrk.rfz_of, Sbrk.arith_of, o6, o11, Op.cmpmif, BitVec.and_self,
    hb0, hs, he, xz, tbf, Bool.false_or, Bool.not_false, Bool.not_true, Bool.true_eq_false,
    not_false_eq_true, decide_true, Bool.false_eq_true, false_implies, eq_self_iff_true, true_implies]
  all_goals vfin

/-- An error, `errno` not `ENOENT`: to 176, `r8` 0. -/
theorem vc_133o {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} (hs : g.rax.msb = true)
    (hbp : g.rbp = 18446744073709551544#64) (he : rdd(V, errnoAt fb) ≠ 2#32)
    (fe : ∀ i < 4, Foot F.data (Addr.add (errnoAt fb) i)) :
    W_133 fb F Wl (fun j' g' _ V' => j' = 176 ∧ g' = { g with r8 := 0#64 } ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [errnoAt] at hs hbp he fe ⊢
  subst hbp
  have hnz : rax ≠ 0#64 := fun h => by rw [h] at hs; exact absurd hs (by decide)
  have hb0 : (rax == 0) = false := beq_false_of_ne hnz
  have hd : decide (rdd(V, fb + 18446744073709551544#64) = 2#32) = false := decide_eq_false he
  wpx [W_133, W_160, W_205, W_215, Sbrk.cond_14, Sbrk.rfz_of, Sbrk.arith_of, o6, o11, Op.cmpmif, BitVec.and_self,
    hb0, hs, hd, he, decide_false, xz, tbf, Bool.false_or, Bool.not_false, Bool.not_true, Bool.true_eq_false,
    not_false_eq_true, decide_true, Bool.false_eq_true, false_implies, eq_self_iff_true, true_implies]
  all_goals vfin
  -- the `jne` sees `2` as a literal, not `2#32`: the taken branch by `he`
  all_goals (rename_i hx; rw [Bool.not_eq_false', decide_eq_true_eq] at hx; exact absurd hx he)

/-- `errno` restored from `r13d`, `r8` 0: to 176. -/
theorem vc_162 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} (hbp : g.rbp = 18446744073709551544#64)
    (fe : ∀ i < 4, Foot Wl ((errnoAt fb).add i)) :
    W_162 fb F Wl (fun j' g' _ V' => j' = 176 ∧ g' = { g with r8 := 0#64 } ∧
      V' = Vst V (errnoAt fb) (toBytesLE (BitVec.setWidth 32 g.r13) 4)) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hbp ⊢
  subst hbp
  wpx [W_162, o8, Op.stf, xz]
  all_goals vfin

/-- One thread: to the lock given back (188), `eax` 0. -/
theorem vc_176 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} (hmt : rdd(V, fb + 24#64) = 0#32)
    (fm : ∀ i < 4, Foot F.data (Addr.add (fb + 24#64) i)) :
    W_176 fb F Wl (fun j' g' _ V' => j' = 188 ∧ g' = { g with rax := 0#64 } ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at fm ⊢
  wpx [W_176, o9, Op.ldf, hmt, BitVec.and_self, z0, s0, sz, Bool.not_true, Bool.false_eq_true, Bool.true_eq_false,
    false_implies, eq_self_iff_true, true_implies]
  all_goals vfin

/-- The pops, `rax` the result (`r8`): to the `ret`. -/
abbrev gP5 (V : Addr → Byte) (g : Gprs) : Gprs :=
  { g with
    rax := g.r8
    rbx := rdq(V, g.rsp)
    rbp := rdq(V, g.rsp + 8)
    r12 := rdq(V, g.rsp + 8 + 8)
    r13 := rdq(V, g.rsp + 8 + 8 + 8)
    r14 := rdq(V, g.rsp + 8 + 8 + 8 + 8)
    rsp := g.rsp + 8 + 8 + 8 + 8 + 8 }

theorem vc_193 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (p1 : ∀ i < 8, Foot F.data (Addr.add g.rsp i)) (p2 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8) i))
    (p3 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8 + 8) i))
    (p4 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8 + 8 + 8) i))
    (p5 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8 + 8 + 8 + 8) i)) :
    W_193 fb F Wl (fun j' g' _ V' => j' = 204 ∧ g' = gP5 V g ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [gP5] at p1 p2 p3 p4 p5 ⊢
  wpx [W_193, o10]
  all_goals vfin

/-! ## Next: `Rdd/Ok.lean`, the whole function (design notes, not yet written)

Imports `FV7z.Rdd.Holds`, `FV7z.Opd.Ok` (`Keeps`, `Keeps.trans`, `set4K`, `set4_rsp`, `rd_ret`, `ER`; `tAdd`, `tSub`,
`fa`, `frw` are in `Opd.Holds`); add `import FV7z.Rdd.Ok` to `FV7z.lean` after `FV7z.Rdd.Holds`. Below, `T` is
`S - 8 - 8 - 8 - 8 - 8` (`S` = `rsp` at the entry, `p` = `rdi`, the `DIR`).

Hypotheses to report: one thread (`fs:0x18` = 0, `hmt0 : rdd(V₀, fb + 24#64) = 0#32`, the lock 0 at the entry);
`NzIno o := ∀ t s, ∀ e ∈ (dentsRes o t s).es, e.ino ≠ 0#64` (the kernel never gives `d_ino` 0: after `getdents` the
first entry is returned, so no second `getdents`); `errno` may change (`Mut` includes `ER`).

Definitions:
- `Dir V p A w n k`: `rdd(V, p + 4#64) = w`, `rdq(V, p + 8#64).toNat = A`, `rdq(V, p + 16#64).toNat = n`, `n ≤ A`,
  `rdq(V, p + 24#64).toNat = k`.
- `Sv V S g0`: `rdq` at `T`, `S-8-8-8-8`, `S-8-8-8`, `S-8-8`, `S-8` are `g0`'s `rbx`, `rbp`, `r12`, `r13`, `r14`.
- `Mut S p fb A a` (abbrev): `a` in `[S - 48, S)`, in `[p, p + 48 + A)`, or `ER fb a`. `Fr S p fb A V₀ V`:
  `∀ a, ¬ Mut … a → V a = V₀ a`. `structure Iv`: `dir`, `sv`, `fr`.
- `RS V p n k r := (r = 0#64 ∧ Ch V p n k) ∨ ∃ k₀ < n, Ch V p n k₀ ∧ k = k₀ + rl V p k₀ ∧ r = Addr.add p (48 + k₀)`.
- `structure RdC F Wl S p fb A`: `48 ≤ S.toNat`, `S.toNat + 8 ≤ 2^64`, `sw` (48 bytes from `S - 48#64` in `Wl`),
  `sr` (8 bytes at `S` in `F.data`), `A ≤ 2147483647`, `p.toNat + 48 + A < 2^64`, `pw` (`48 + A` bytes at `p` in
  `Wl`), `fe` (`errno` in `Wl`, `(errnoAt fb).add i`), `hfe`, `fm`/`hfm` (`fb + 24#64`, 4 bytes, `F.data`), and the
  apartness of the stack `[S-48, S+8)`, the `DIR` `[p, p+48+A)`, `errno` and `fb + 24` (`dS eS mS eD mD mE`).
  Get `F.data` facts for `Wl` bytes from `c.hws`.
- `RdT gev tr := tr = gev ∨ ∃ G r, tr = gev ++ [Gdn.gdE G r]`.
- `RddK … S p fb A g0 V₀ e₂ j₂ gev := ∀ s Z tr W t', Seg s → fsBase = fb → rseq = none → KeptW Wl s Z → Agree W →
  Z.rip = e₂.add j₂ → Z.rsp = S + 8#64 → Keeps g0 Z.gpr → Fr … W → RdT gev tr →
  (∃ n k, Dir W p A 0#32 n k ∧ RS W p n k Z.rax) → GoG prof L o tr gP gE Z t'`.
- `structure At109`: `KeptW`, `Agree`, rip 109, `rsp = T`, `rbx = p + 48#64`, `rbp = -72`, `r14 = p`, `r15`,
  `rax.toNat = n`, `rdx.toNat = k`, `Iv … 1#32 n k`, `Ch W p n k`.

Lemmas, in this order. Get each memory fact by `congrArg (ofBytesLE _) (Sbrk.rd_eq (x := …) (n := …) …)`, or by
`rd_Vst` with `a`, `x` and `n` explicit. Never pass a `by` argument whose goal still has a metavariable.
- `stR`: toNat of `S-8` … `T`, `T-8` and `S - 48#64`, via `tSub`.
- `pT1`–`pT5`: `T + 8 … = S-8-8-8-8 … S`. `pT6`: `T - 8 = S - 48#64`. `pT7`: `S - 48#64 + 8 = T`. Prove each with
  `bv_omega`, as a standalone lemma.
- `ea80 p (hd : d.toNat = k) : d + 48#64 + p = Addr.add p (48 + k)`. `ea0 : 48#64 + p = Addr.add p (48 + 0)`, by
  `BitVec.add_comm`. `aa := addr_add_add'`.
- `rcl_nat (h : g.r8 + g.r14 = Addr.add p (48 + k)) : (rcl V g).toNat = rl V p k`.
- `out_of`, `nMut`, `fr_rd`.
- `Dir_eq`, `Sv_eq` (agreement on `[p+4, p+32)` and `[S-40, S)`), then `Dir_st` and `SvFr_st`.
- `Iv_lock`, `Iv_size`, `Iv_off`: stores at `p + 4/16/24#64`.
- `Ch_st`, `rl_st` (explicit `k`), `Ch_inv` (by `cases`), `RS_st`.
- `P5_out`, `P5_sv`: as `Opd.P4_out` and `Opd.Vo_reads`.
- `rd_pre` and `ino_dn`: the first entry's `d_ino` after `dnBuf`. Use `← dn_one`, unfold `direntRuns`/`vRuns` by
  `show`, then `vRuns_apart` with `direntRuns_in`. Take `e.bytes = toBytesLE e.ino 8 ++ rest` from `bytes_split`,
  then `Cxa.Vst_append`.
- `set0K`, and `gdK` (as `Opd.sysK`, with `lsErrG`).
- `ft80`: the five footprint facts of `vc_80*`.
- `post80`: after `VB`, `Iv … (k + rl W p k)`, the chain kept, `rl` kept and `(gB W g).rdx.toNat`. Generalize the
  stored values before `rw [h14]`.

Main theorems:
- `fin176`: from 176, `vc_176` (hmt from `V₀` through `Fr`), then `s_sub_mi32`. For it: `eaD Y₁ 14 4 = p + 4#64`,
  `rw [ea, hI.dir.1, (1#32 - BitVec.ofNat 32 1 = 0#32)] at hA₂`, and `Iv_lock C hI 0#32`. Then `vc_193` (slots
  from `sw` with `pT1`–`pT4`), then `s_ret` (`pT5`; the return address from `V₀` through `Fr`). End with `K`:
  `Keeps` from `Sv` and `set4K`, and `RS_st` through the lock store.
- `n80`: from 80 with `d_ino` not 0, `vc_80n` with `post80`, then `fin176` with `RS` right.
- `rdd_gd`: from 128, `s_call` (`call_128`, `tgt_128`, `Gdn.lt_len (j := 0)`), then `Gdn.gdn_ok` with
  `j₂ := 133`. Generalize the pushed memory as `W₁` once its `Iv` facts are proved.
  - `CloseErr`: `vc_133e` then `vc_162`, or `vc_133o`; then `fin176` with `RS` left and `Ch.fin`.
  - Otherwise `dn_ret`, with the sum `≤ A` from `dentsRes_sum` and `arg32`. A sum of 0: `vc_133z`, `vc_162`,
    `fin176`. A positive sum: `vc_133p` (`Iv_size`), then `n80` at `k = 0` (`ch_dn`, `ino_dn`, `NzIno`).
- `step109 (ih : ∀ k', n - k' < n - k → …)`:
  - `k < n`: `vc_109l` to 80. There, `d_ino` 0: `vc_80z` with `post80`, then `ih`. Otherwise `n80`.
  - `k = n`: `vc_109g`, then `rdd_gd`.
  `scan : ∀ m k, n - k ≤ m → …`, by `induction m` over `step109`.
- `rdd_ok`: `subst` `S` and `p`. Then `vc_0` (`e0 := rdd(P5 V₀ g, errnoAt fb)`, by `rfl`), then
  `s_cmpxchg_bd32` (`rv Y₁ 32 0 = 0#32`, `rv Y₁ 32 2 = 1#32`, `Iv_lock`), then `vc_56`, then
  `scan (n - k) k le_rfl`.
-/

end FV7z.Rdd
