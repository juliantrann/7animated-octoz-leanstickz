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

end FV7z.Rdd
