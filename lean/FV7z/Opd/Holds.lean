import FV7z.Opd.Cuts
import FV7z.Onc.Blocks
import FV7z.Fxs.Blocks
import FV7z.Mal.Blocks
import FV7z.Lemmas.FnFar
import FV7z.Lemmas.CmpImm
import FV7z.Lemmas.Frame
import FV7z.Tun.Inv
import FV7z.Sbrk.Next
/-!
# `__opendir`, the way that opens a directory (PLAN.md §M, M1)

glibc 2.31's `__opendir (name)` at `0x6635d0` in `7zzs` (`sysdeps/posix/opendir.c` with `opendir_tail` and
`__alloc_dir` inlined; `objdump -d`), `S` the stack pointer at the entry: four pushes (`r13`, `r12`, `rbp`, `rbx`,
`P4`), a frame of 168 bytes (`aQ S` = `S - 200`) with the stack guard (`fs:0x28`) at `S - 48` (`Vo`), the `struct stat`
at `aQ S`. Four pieces, each to the next call:

- `opd_open`: from the entry, `name` not empty, to `__open_nocancel (name, O_RDONLY | O_NDELAY | O_DIRECTORY |
  O_LARGEFILE | O_CLOEXEC)` (`Onc.onc_at`, call at 50, registers `aG`);
- `opd_stat`: from its return (55), the descriptor not negative, to `__fxstat (1, fd, &st)` (`Fxs.fxs_at`, call at 75,
  registers `bG`);
- `opd_alloc`: from its return (80), the answer not negative and `st.st_mode` a directory, to `malloc (bsz + 48)`
  (`Mal.mal_at`, call at 148, registers `cG`): `bsz` is `st.st_blksize` (at `rsp + 56`) bounded to 32 KiB … 1 MiB;
- `opd_ret`: from its return (153), the block not null, the `DIR`'s fields stored (`Vd`: `fd`, `lock` 0, the
  allocation size, `size`, `offset`, `filepos` 0, `errcode` 0), the stack guard checked, to the return address with
  `rax` the `DIR`.

Not covered (each a branch the pieces do not take): the empty `name` (`ENOENT`, 288), the open failing (312), `fstat`
failing or not a directory (`ENOTDIR`, 256 and 270, `__close_nocancel`), the first `malloc` failing (the second
`malloc (0x2030)`, 322 onwards), the stack guard failing (`__stack_chk_fail`, 317).
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
open FV7z.Tun (rd_Vst rd_Vst_self Vst_out)
namespace FV7z.Opd

/-- The `call __open_nocancel`. -/
def pco : List Byte := [0xe8, 0x89, 0x2a, 0x00, 0x00]
theorem pco_0 : ∀ feat, Dec feat pco 0 (FV7z.mk .call 64 [.rel 10889] 5) := by dec_rfl
theorem wc_50 : pco <+: opd.drop 50 := by decide +kernel
theorem call_50 (feat : Features) : Dec feat opd 50 (FV7z.mk .call 64 [.rel 10889] 5) :=
  Dec.shift (j := 50) (k := 0) (pco_0 feat) wc_50 (Nat.zero_le _)

/-- The `call __fxstat`. -/
def pcs : List Byte := [0xe8, 0x40, 0x1d, 0x00, 0x00]
theorem pcs_0 : ∀ feat, Dec feat pcs 0 (FV7z.mk .call 64 [.rel 7488] 5) := by dec_rfl
theorem wc_75 : pcs <+: opd.drop 75 := by decide +kernel
theorem call_75 (feat : Features) : Dec feat opd 75 (FV7z.mk .call 64 [.rel 7488] 5) :=
  Dec.shift (j := 75) (k := 0) (pcs_0 feat) wc_75 (Nat.zero_le _)

/-- The `call malloc`. -/
def pcm : List Byte := [0xe8, 0xf7, 0xfa, 0xfc, 0xff]
theorem pcm_0 : ∀ feat, Dec feat pcm 0 (FV7z.mk .call 64 [.rel 18446744073709353719] 5) := by dec_rfl
theorem wc_148 : pcm <+: opd.drop 148 := by decide +kernel
theorem call_148 (feat : Features) : Dec feat opd 148 (FV7z.mk .call 64 [.rel 18446744073709353719] 5) :=
  Dec.shift (j := 148) (k := 0) (pcm_0 feat) wc_148 (Nat.zero_le _)

/-- The `ret`. -/
def pret : List Byte := [0xc3]
theorem pret_0 : ∀ feat, Dec feat pret 0 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem w_254 : pret <+: opd.drop 254 := by decide +kernel
theorem ret_254 (feat : Features) : Dec feat opd 254 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 254) (k := 0) (pret_0 feat) w_254 (Nat.zero_le _)

/-! ## The frame -/

theorem tAdd (x : BitVec 64) (k : Nat) (hk : x.toNat + k < 2 ^ 64) : (x + BitVec.ofNat 64 k).toNat = x.toNat + k := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

theorem tSub (x : BitVec 64) (k : Nat) (hk : k ≤ x.toNat) : (x - BitVec.ofNat 64 k).toNat = x.toNat - k := by
  have := x.isLt
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega

/-- An address `d` bytes above `B`. -/
theorem fa {B x : Addr} {d : Nat} (hB : B.toNat + d < 2 ^ 64) (hx : x.toNat = B.toNat + d) : x = Addr.add B d := by
  apply BitVec.eq_of_toNat_eq
  rw [hx, toNat_add_of_fits (i := d) (n := d + 1) (by omega) (by omega)]

/-- A slot of a range. -/
theorem frw {P : Addr → Prop} {B x : Addr} {N : Nat} (h : ∀ i < N, P (Addr.add B i)) {d n : Nat}
    (hx : x = Addr.add B d) (hdn : d + n ≤ N) : ∀ i < n, P (Addr.add x i) := fun i hi => by
  rw [hx, addr_add_add']
  exact h (d + i) (by omega)

/-- The stack pointer after `sub rsp, 168`. -/
abbrev aQ (S : Addr) : Addr := S - 8 - 8 - 8 - 8 - 168#64

/-- The bytes after the four `push`es. -/
abbrev P4 (V : Addr → Byte) (g : Gprs) : Addr → Byte :=
  Vst (Vst (Vst (Vst V (g.rsp - 8) (toBytesLE g.r13 8)) (g.rsp - 8 - 8) (toBytesLE g.r12 8))
    (g.rsp - 8 - 8 - 8) (toBytesLE g.rbp 8)) (g.rsp - 8 - 8 - 8 - 8) (toBytesLE g.rbx 8)

/-- The bytes at the `call __open_nocancel`: the stack guard `cn` stored at `S - 48`. -/
abbrev Vo (g : Gprs) (cn : BitVec 64) (V : Addr → Byte) : Addr → Byte :=
  Vst (P4 V g) (aQ g.rsp + 152#64) (toBytesLE cn 8)

/-- The slots of the four pushes, the frame, the stack guard and the return address of the first call. -/
theorem stA (S : Addr) (h : 208 ≤ S.toNat) :
    (S - 8).toNat = S.toNat - 8 ∧ (S - 8 - 8).toNat = S.toNat - 16 ∧ (S - 8 - 8 - 8).toNat = S.toNat - 24 ∧
      (S - 8 - 8 - 8 - 8).toNat = S.toNat - 32 ∧ (aQ S).toNat = S.toNat - 200 ∧
      (aQ S + 152#64).toNat = S.toNat - 48 ∧ (aQ S - 8).toNat = S.toNat - 208 ∧
      (S - 208#64).toNat = S.toNat - 208 := by
  have hS := S.isLt
  have b1 : (S - 8).toNat = S.toNat - 8 := tSub S 8 (by omega)
  have b2 : (S - 8 - 8).toNat = S.toNat - 16 := (tSub (S - 8) 8 (by omega)).trans (by omega)
  have b3 : (S - 8 - 8 - 8).toNat = S.toNat - 24 := (tSub (S - 8 - 8) 8 (by omega)).trans (by omega)
  have b4 : (S - 8 - 8 - 8 - 8).toNat = S.toNat - 32 := (tSub (S - 8 - 8 - 8) 8 (by omega)).trans (by omega)
  have b5 : (aQ S).toNat = S.toNat - 200 := (tSub (S - 8 - 8 - 8 - 8) 168 (by omega)).trans (by omega)
  have b6 : (aQ S + 152#64).toNat = S.toNat - 48 := (tAdd (aQ S) 152 (by omega)).trans (by omega)
  have b7 : (aQ S - 8).toNat = S.toNat - 208 := (tSub (aQ S) 8 (by omega)).trans (by omega)
  exact ⟨b1, b2, b3, b4, b5, b6, b7, tSub S 208 h⟩

theorem P4_out (V : Addr → Byte) (g : Gprs) (h : 208 ≤ g.rsp.toNat) (a : Addr)
    (ha : a.toNat < g.rsp.toNat - 32 ∨ g.rsp.toNat ≤ a.toNat) : P4 V g a = V a := by
  obtain ⟨e1, e2, e3, e4, -⟩ := stA g.rsp h
  have := g.rsp.isLt
  dsimp only [P4]
  rw [Vst_out, Vst_out, Vst_out, Vst_out]
  all_goals (try simp only [toBytesLE_length, e1, e2, e3, e4])
  all_goals omega

theorem Vo_out (g : Gprs) (cn : BitVec 64) (V : Addr → Byte) (h : 208 ≤ g.rsp.toNat) (a : Addr)
    (ha : a.toNat < g.rsp.toNat - 48 ∨ g.rsp.toNat ≤ a.toNat) : Vo g cn V a = V a := by
  obtain ⟨-, -, -, -, -, e6, -⟩ := stA g.rsp h
  have := g.rsp.isLt
  dsimp only [Vo]
  rw [Vst_out]
  · exact P4_out V g h a (by omega)
  all_goals (try simp only [toBytesLE_length, e6])
  all_goals omega

theorem P4_rd (V : Addr → Byte) (g : Gprs) (h : 208 ≤ g.rsp.toNat) {x : Addr} {n : Nat}
    (hx : x.toNat + n ≤ 2 ^ 64) (hd : x.toNat + n ≤ g.rsp.toNat - 32 ∨ g.rsp.toNat ≤ x.toNat) :
    List.map (P4 V g) (byteAddrs x n) = List.map V (byteAddrs x n) :=
  Sbrk.rd_eq hx fun a h1 h2 => P4_out V g h a (by omega)

theorem Vo_rd (g : Gprs) (cn : BitVec 64) (V : Addr → Byte) (h : 208 ≤ g.rsp.toNat) {x : Addr} {n : Nat}
    (hx : x.toNat + n ≤ 2 ^ 64) (hd : x.toNat + n ≤ g.rsp.toNat - 48 ∨ g.rsp.toNat ≤ x.toNat) :
    List.map (Vo g cn V) (byteAddrs x n) = List.map V (byteAddrs x n) :=
  Sbrk.rd_eq hx fun a h1 h2 => Vo_out g cn V h a (by omega)

/-- The `DIR`'s fields at `p`: `fd` (the descriptor, `ebp`), `lock` 0, `allocation` (`rbx`), `size`, `offset`,
`filepos` 0, `errcode` 0. -/
abbrev Vd (V : Addr → Byte) (p bp bx : BitVec 64) : Addr → Byte :=
  Vst (Vst (Vst (Vst (Vst (Vst (Vst V p (toBytesLE (bp.setWidth 32) 4)) (p + 4#64) (toBytesLE 0#32 4))
    (p + 8#64) (toBytesLE bx 8)) (p + 16#64) (toBytesLE 0#64 8)) (p + 24#64) (toBytesLE 0#64 8))
    (p + 32#64) (toBytesLE 0#64 8)) (p + 40#64) (toBytesLE 0#32 4)

/-- A read apart from the `DIR`'s 44 bytes. -/
theorem Vd_rd (U : Addr → Byte) (p bp bx : BitVec 64) (hp : p.toNat + 44 ≤ 2 ^ 64) {x : Addr} {n : Nat}
    (hx : x.toNat + n ≤ 2 ^ 64) (h : x.toNat + n ≤ p.toNat ∨ p.toNat + 44 ≤ x.toNat) :
    List.map (Vd U p bp bx) (byteAddrs x n) = List.map U (byteAddrs x n) := by
  have e4 : (p + 4#64).toNat = p.toNat + 4 := tAdd p 4 (by omega)
  have e8 : (p + 8#64).toNat = p.toNat + 8 := tAdd p 8 (by omega)
  have e16 : (p + 16#64).toNat = p.toNat + 16 := tAdd p 16 (by omega)
  have e24 : (p + 24#64).toNat = p.toNat + 24 := tAdd p 24 (by omega)
  have e32 : (p + 32#64).toNat = p.toNat + 32 := tAdd p 32 (by omega)
  have e40 : (p + 40#64).toNat = p.toNat + 40 := tAdd p 40 (by omega)
  dsimp only [Vd]
  rw [rd_Vst, rd_Vst, rd_Vst, rd_Vst, rd_Vst, rd_Vst, rd_Vst]
  all_goals (try simp only [toBytesLE_length, e4, e8, e16, e24, e32, e40])
  all_goals omega

/-- The pops' slots after `add rsp, 168`. -/
theorem pa1 (S : Addr) : S + 168#64 + 8 = S + 176#64 := by bv_omega
theorem pa2 (S : Addr) : S + 168#64 + 8 + 8 = S + 184#64 := by bv_omega
theorem pa3 (S : Addr) : S + 168#64 + 8 + 8 + 8 = S + 192#64 := by bv_omega
theorem pa4 (S : Addr) : S + 168#64 + 8 + 8 + 8 + 8 = S + 200#64 := by bv_omega
theorem pa5 (S : Addr) : S + 168#64 + 8 + 8 + 8 + 8 + 8 = S + 208#64 := by bv_omega

/-! ## The registers -/

theorem xz (x : BitVec 32) : BitVec.setWidth 64 (x ^^^ x) = 0#64 := by simp
theorem s1 : BitVec.setWidth 64 1#32 = 1#64 := by decide
theorem s591872 : BitVec.setWidth 64 591872#32 = 591872#64 := by decide
theorem s32768 : BitVec.setWidth 64 32768#32 = 32768#64 := by decide
theorem s1048576 : BitVec.setWidth 64 1048576#32 = 1048576#64 := by decide

/-- At `__open_nocancel`'s call: `rax` 0, `esi` the flags `0x90800`, the frame made. -/
abbrev aG (g : Gprs) : Gprs := { g with rax := 0#64, rsp := aQ g.rsp, rsi := 591872#64 }

/-- At `__fxstat`'s call: `ebp` and `esi` the descriptor (`eax`), `edi` 1 (`_STAT_VER`), `rdx` the `struct stat`
(`rsp`). -/
abbrev bG (g : Gprs) : Gprs :=
  { g with
    rdx := g.rsp
    rbp := BitVec.setWidth 64 (BitVec.setWidth 32 g.rax)
    rsi := BitVec.setWidth 64 (BitVec.setWidth 32 g.rax)
    rdi := 1#64 }

/-- The buffer's size from `st_blksize` (`x`): at least 32 KiB, at most 1 MiB. -/
def bsz (x : BitVec 64) : BitVec 64 :=
  if x.toNat < 32768 then 32768#64 else if 1048576 < x.toNat then 1048576#64 else x

/-- At `malloc`'s call: `rbx` the buffer's size, `rdi` it plus 48 (the `DIR`'s header). -/
abbrev cG (V : Addr → Byte) (g : Gprs) : Gprs :=
  { g with rax := 1048576#64, rbx := bsz rdq(V, g.rsp + 56#64), rdi := bsz rdq(V, g.rsp + 56#64) + 48#64 }

/-- At the `ret`: `rax` the `DIR` (`r12`), the four registers popped. -/
abbrev dG (V : Addr → Byte) (g : Gprs) : Gprs :=
  { g with
    rax := g.r12
    rbx := rdq(V, g.rsp + 168#64)
    rbp := rdq(V, g.rsp + 168#64 + 8)
    r12 := rdq(V, g.rsp + 168#64 + 8 + 8)
    r13 := rdq(V, g.rsp + 168#64 + 8 + 8 + 8)
    rsp := g.rsp + 168#64 + 8 + 8 + 8 + 8 }

variable {F : Footprint} {Wl : List Rgn}

/-- What is left of a piece's condition: its footprint facts, equations, cases that cannot be. -/
local macro "vfin" : tactic =>
  `(tactic| repeat' (first | (with_reducible rfl) | (with_reducible assumption) | exact True.intro |
    (intro h; exact absurd h (by omega)) | apply And.intro | intro _))

/-! ## The pieces -/

/-- From the entry to the first call: the pushes, the stack guard stored, `name[0]` not 0, `esi` the flags. -/
theorem vc_0 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {cn : BitVec 64}
    (hcn : rdq(P4 V g, fb + 40#64) = cn) (hne : ofBytesLE 8 ((byteAddrs g.rdi 1).map (Vo g cn V)) ≠ 0#8)
    (w1 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8) i)) (w2 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8) i))
    (w3 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8 - 8) i))
    (w4 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8 - 8 - 8) i))
    (fc : ∀ i < 8, Foot F.data (Addr.add (fb + 40#64) i)) (wc : ∀ i < 8, Foot Wl (Addr.add (aQ g.rsp + 152#64) i))
    (fr : ∀ i < 1, Foot F.data (Addr.add g.rdi i)) :
    W_0 fb F Wl (fun j' g' _ V' => j' = 50 ∧ g' = aG g ∧ V' = Vo g cn V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [Vo, P4, aQ, aG] at hcn hne w1 w2 w3 w4 wc fr ⊢
  wpx [W_0, W_45, o0, o1, Op.ldf, Op.cmpmi, hcn, hne, xz, s591872, decide_false, Bool.false_eq_true, false_implies,
    eq_self_iff_true, true_implies, implies_true]
  all_goals vfin

/-- From the return of `__open_nocancel` to the second call, the descriptor (`eax`) not negative. -/
theorem vc_55 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} (hs : (BitVec.setWidth 32 g.rax).msb = false) :
    W_55 fb F Wl (fun j' g' _ V' => j' = 75 ∧ g' = bG g ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hs ⊢
  wpx [W_55, W_65, o2, o3, BitVec.and_self, hs, s1, Bool.false_eq_true, false_implies, eq_self_iff_true,
    true_implies]
  all_goals vfin

/-- From the return of `__fxstat` to `malloc`'s call, its answer not negative, `st_mode` a directory. -/
theorem vc_80 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} (hs : (BitVec.setWidth 32 g.rax).msb = false)
    (hm : ofBytesLE 32 ((byteAddrs (g.rsp + 24#64) 4).map V) &&& 61440#32 = 16384#32)
    (f24 : ∀ i < 4, Foot F.data (Addr.add (g.rsp + 24#64) i))
    (f56 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 56#64) i)) :
    W_80 fb F Wl (fun j' g' _ V' => j' = 148 ∧ g' = cG V g ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hs hm f24 f56 ⊢
  have hm' : decide (ofBytesLE 32 ((byteAddrs (rsp + 24#64) 4).map V) &&& 61440#32 = 16384#32) = true :=
    decide_eq_true hm
  by_cases h1 : rdq(V, rsp + 56#64).toNat < 32768
  · have d1 : decide (rdq(V, rsp + 56#64).toNat < 32768) = true := decide_eq_true h1
    have hb : bsz rdq(V, rsp + 56#64) = 32768#64 := by rw [bsz, if_pos h1]
    have d3 : decide (32768 ≤ 1048576) = true := by decide
    wpx [W_80, W_88, W_108, o4, o5, o6, Op.cmpmi, Op.cmovld64, cG, hb, BitVec.and_self, hs, hm', d1, d3, s32768,
      s1048576, be_imm (w := 64) _ 1048576 (by decide), decide_true, decide_false, Bool.not_true, Bool.not_false,
      Bool.true_or, Bool.or_true, Bool.false_or, Bool.or_false, Bool.false_eq_true, ↓reduceIte, false_implies,
      eq_self_iff_true, true_implies]
    all_goals vfin
  · have d1 : decide (rdq(V, rsp + 56#64).toNat < 32768) = false := decide_eq_false h1
    by_cases h2 : 1048576 < rdq(V, rsp + 56#64).toNat
    · have d2 : decide (rdq(V, rsp + 56#64).toNat ≤ 1048576) = false := decide_eq_false (by omega)
      have hb : bsz rdq(V, rsp + 56#64) = 1048576#64 := by rw [bsz, if_neg h1, if_pos h2]
      wpx [W_80, W_88, W_108, o4, o5, o6, Op.cmpmi, Op.cmovld64, cG, hb, BitVec.and_self, hs, hm', d1, d2, s32768,
        s1048576, be_imm (w := 64) _ 1048576 (by decide), decide_true, decide_false, Bool.not_true, Bool.not_false,
        Bool.true_or, Bool.or_true, Bool.false_or, Bool.or_false, Bool.false_eq_true, ↓reduceIte, false_implies,
        eq_self_iff_true, true_implies]
      all_goals vfin
    · have d2 : decide (rdq(V, rsp + 56#64).toNat ≤ 1048576) = true := decide_eq_true (by omega)
      have hb : bsz rdq(V, rsp + 56#64) = rdq(V, rsp + 56#64) := by rw [bsz, if_neg h1, if_neg h2]
      wpx [W_80, W_88, W_108, o4, o5, o6, Op.cmpmi, Op.cmovld64, cG, hb, BitVec.and_self, hs, hm', d1, d2, s32768,
        s1048576, be_imm (w := 64) _ 1048576 (by decide), decide_true, decide_false, Bool.not_true, Bool.not_false,
        Bool.true_or, Bool.or_true, Bool.false_or, Bool.or_false, Bool.false_eq_true, ↓reduceIte, false_implies,
        eq_self_iff_true, true_implies]
      all_goals vfin

/-- From the return of `malloc`, the block (`rax`) not null: `r12` the block. -/
theorem vc_153 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} (hnz : g.rax ≠ 0#64) :
    W_153 fb F Wl (fun j' g' _ V' => j' = 165 ∧ g' = { g with r12 := g.rax } ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hnz ⊢
  have hnz' : rax ≠ (0 : BitVec 64) := hnz
  have hb0 : (rax == 0) = false := beq_false_of_ne hnz'
  wpx [W_153, o7, BitVec.and_self, hnz, hnz', hb0, decide_false, Bool.false_eq_true, false_implies, Bool.not_false,
    eq_self_iff_true, true_implies]
  all_goals vfin

/-- The `DIR`'s fields stored at `r12`. -/
theorem vc_165 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (w0 : ∀ i < 4, Foot Wl (Addr.add g.r12 i)) (w4 : ∀ i < 4, Foot Wl (Addr.add (g.r12 + 4#64) i))
    (w8 : ∀ i < 8, Foot Wl (Addr.add (g.r12 + 8#64) i)) (w16 : ∀ i < 8, Foot Wl (Addr.add (g.r12 + 16#64) i))
    (w24 : ∀ i < 8, Foot Wl (Addr.add (g.r12 + 24#64) i)) (w32 : ∀ i < 8, Foot Wl (Addr.add (g.r12 + 32#64) i))
    (w40 : ∀ i < 4, Foot Wl (Addr.add (g.r12 + 40#64) i)) :
    W_165 fb F Wl (fun j' g' _ V' => j' = 219 ∧ g' = g ∧ V' = Vd V g.r12 g.rbp g.rbx) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [Vd] at w0 w4 w8 w16 w24 w32 w40 ⊢
  wpx [W_165, o8]
  all_goals vfin

/-- The stack guard checked, the frame dropped, the four registers popped. -/
theorem vc_219 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (hc : rdq(V, g.rsp + 152#64) = rdq(V, fb + 40#64)) (f152 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 152#64) i))
    (fc : ∀ i < 8, Foot F.data (Addr.add (fb + 40#64) i))
    (p1 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 168#64) i))
    (p2 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 168#64 + 8) i))
    (p3 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 168#64 + 8 + 8) i))
    (p4 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 168#64 + 8 + 8 + 8) i)) :
    W_219 fb F Wl (fun j' g' _ V' => j' = 254 ∧ g' = dG V g ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hc f152 p1 p2 p3 p4 ⊢
  wpx [W_219, W_238, o9, o10, Op.xormf, hc, BitVec.xor_self, decide_true, Bool.not_true, Bool.false_eq_true,
    false_implies, eq_self_iff_true, true_implies]
  all_goals vfin

/-- The registers after the `ret` from `dG`. -/
theorem dGs (V : Addr → Byte) (g : Gprs) (v : BitVec 64) :
    ((dG V g).set 4 v).rsp = v ∧ ((dG V g).set 4 v).rax = g.r12 ∧
    ((dG V g).set 4 v).rbx = rdq(V, g.rsp + 168#64) ∧ ((dG V g).set 4 v).rbp = rdq(V, g.rsp + 168#64 + 8) ∧
    ((dG V g).set 4 v).r12 = rdq(V, g.rsp + 168#64 + 8 + 8) ∧
    ((dG V g).set 4 v).r13 = rdq(V, g.rsp + 168#64 + 8 + 8 + 8) ∧
    ((dG V g).set 4 v).r14 = g.r14 ∧ ((dG V g).set 4 v).r15 = g.r15 := by
  cases g
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {X : State} {t : Nat} {V : Addr → Byte}

/-- `__opendir (name)` from its entry, `name[0]` not 0, the frame's 208 bytes below `rsp` (the pushes, 168, the
call's return address) in what the run may store into, the stack guard and `name[0]` apart from the frame: at
`__open_nocancel`'s entry with the registers `aG` (`rdi` = `name`), the stack guard and the pushes stored (`Vo`) and
the return address `opd_at + 55` below the frame. -/
theorem opd_open {fb : Addr} (c : Seg prof F Wl L s₀ o) (hfs : s₀.cpu.seg.fsBase = fb) (hin : CodeIn L opd_at opd)
    (hinO : CodeIn L Onc.onc_at Onc.onc) (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V)
    (hrip : X.cpu.rip = opd_at) (h208 : 208 ≤ X.cpu.gpr.rsp.toNat)
    (hfw : ∀ i < 208, Foot Wl (Addr.add (X.cpu.gpr.rsp - 208#64) i))
    (hcl : ∀ i < 8, Foot F.data (Addr.add (fb + 40#64) i)) (hcb : (fb + 40#64).toNat + 8 ≤ 2 ^ 64)
    (hcd : (fb + 40#64).toNat + 8 ≤ X.cpu.gpr.rsp.toNat - 208 ∨ X.cpu.gpr.rsp.toNat ≤ (fb + 40#64).toNat)
    (fr : ∀ i < 1, Foot F.data (Addr.add X.cpu.gpr.rdi i))
    (hrd : X.cpu.gpr.rdi.toNat + 1 ≤ X.cpu.gpr.rsp.toNat - 208 ∨ X.cpu.gpr.rsp.toNat ≤ X.cpu.gpr.rdi.toNat)
    (hne : ofBytesLE 8 ((byteAddrs X.cpu.gpr.rdi 1).map V) ≠ 0#8)
    (k : ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y →
      Agree F Y.proc.mm.mem (Vst (Vo X.cpu.gpr rdq(V, fb + 40#64) V) (aQ X.cpu.gpr.rsp - 8)
        (toBytesLE (opd_at.add 55) 8)) →
      Y.cpu.rip = Onc.onc_at → Y.cpu.gpr = (aG X.cpu.gpr).set 4 (aQ X.cpu.gpr.rsp - 8) →
      GoG prof L o gev gP gE Y t') :
    GoG prof L o gev gP gE X t := by
  have hlt := X.cpu.gpr.rsp.isLt
  have hdl := X.cpu.gpr.rdi.isLt
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8⟩ := stA X.cpu.gpr.rsp h208
  have hcn : rdq(P4 V X.cpu.gpr, fb + 40#64) = rdq(V, fb + 40#64) :=
    congrArg (ofBytesLE 64) (P4_rd V X.cpu.gpr h208 hcb (by omega))
  have hne' : ofBytesLE 8 ((byteAddrs X.cpu.gpr.rdi 1).map (Vo X.cpu.gpr rdq(V, fb + 40#64) V)) ≠ 0#8 := by
    rw [Vo_rd X.cpu.gpr _ V h208 (by omega) (by omega)]
    exact hne
  refine (c_0 prof fb).run c hfs hin (fun j' g' _ V' => j' = 50 ∧ g' = aG X.cpu.gpr ∧
      V' = Vo X.cpu.gpr rdq(V, fb + 40#64) V) hK hA (by rw [addr_add_zero]; exact hrip)
    (vc_0 hcn hne' (frw hfw (fa (d := 200) (by omega) (by rw [e1, e8]; omega)) (by decide))
      (frw hfw (fa (d := 192) (by omega) (by rw [e2, e8]; omega)) (by decide))
      (frw hfw (fa (d := 184) (by omega) (by rw [e3, e8]; omega)) (by decide))
      (frw hfw (fa (d := 176) (by omega) (by rw [e4, e8]; omega)) (by decide)) hcl
      (frw hfw (fa (d := 160) (by omega) (by rw [e6, e8]; omega)) (by decide)) fr) ?_
  rintro j' g fl V₁ ⟨rfl, rfl, hV⟩ Y t₁ hKY hAY hrY hgY -
  subst V₁
  have hsY : Y.cpu.gpr.rsp = aQ X.cpu.gpr.rsp := by rw [hgY]
  refine c.s_call hKY hAY hin (lt_len (by decide)) hrY (call_50 _) hinO (Onc.lt_len (j := 0) (by decide))
    (by decide) (by rw [hsY]; exact frw hfw (fa (d := 0) (by omega) (by rw [e7, e8]; omega)) (by decide)) ?_
  rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
  rw [hsY] at hA₂
  exact k Y₂ t₂ hK₂ hA₂ hr₂ (by rw [hg₂, hgY])

/-- From the return of `__open_nocancel` (55), the descriptor (`eax`) not negative: at `__fxstat`'s entry with the
registers `bG` and the return address `opd_at + 80` below `rsp`. -/
theorem opd_stat {fb : Addr} (c : Seg prof F Wl L s₀ o) (hfs : s₀.cpu.seg.fsBase = fb) (hin : CodeIn L opd_at opd)
    (hinX : CodeIn L Fxs.fxs_at Fxs.fxs) (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V)
    (hrip : X.cpu.rip = opd_at.add 55) (hs : (BitVec.setWidth 32 X.cpu.gpr.rax).msb = false)
    (hw : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8) i))
    (k : ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y →
      Agree F Y.proc.mm.mem (Vst V (X.cpu.gpr.rsp - 8) (toBytesLE (opd_at.add 80) 8)) →
      Y.cpu.rip = Fxs.fxs_at → Y.cpu.gpr = (bG X.cpu.gpr).set 4 (X.cpu.gpr.rsp - 8) →
      GoG prof L o gev gP gE Y t') :
    GoG prof L o gev gP gE X t := by
  refine (c_55 prof fb).run c hfs hin (fun j' g' _ V' => j' = 75 ∧ g' = bG X.cpu.gpr ∧ V' = V) hK hA hrip
    (vc_55 hs) ?_
  rintro j' g fl V₁ ⟨rfl, rfl, hV⟩ Y t₁ hKY hAY hrY hgY -
  subst V₁
  have hsY : Y.cpu.gpr.rsp = X.cpu.gpr.rsp := by rw [hgY]
  refine c.s_call hKY hAY hin (lt_len (by decide)) hrY (call_75 _) hinX (Fxs.lt_len (j := 0) (by decide))
    (by decide) (by rw [hsY]; exact hw) ?_
  rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
  rw [hsY] at hA₂
  exact k Y₂ t₂ hK₂ hA₂ hr₂ (by rw [hg₂, hgY])

/-- From the return of `__fxstat` (80), its answer not negative and `st_mode` (the 4 bytes at `rsp + 24`) a directory:
at `malloc`'s entry with the registers `cG` (`rdi` = `bsz (st_blksize) + 48`) and the return address `opd_at + 153`
below `rsp`. -/
theorem opd_alloc {fb : Addr} (c : Seg prof F Wl L s₀ o) (hfs : s₀.cpu.seg.fsBase = fb) (hin : CodeIn L opd_at opd)
    (hinM : CodeIn L Mal.mal_at Mal.mal) (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V)
    (hrip : X.cpu.rip = opd_at.add 80) (hs : (BitVec.setWidth 32 X.cpu.gpr.rax).msb = false)
    (hm : ofBytesLE 32 ((byteAddrs (X.cpu.gpr.rsp + 24#64) 4).map V) &&& 61440#32 = 16384#32)
    (f24 : ∀ i < 4, Foot F.data (Addr.add (X.cpu.gpr.rsp + 24#64) i))
    (f56 : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rsp + 56#64) i))
    (hw : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8) i))
    (k : ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y →
      Agree F Y.proc.mm.mem (Vst V (X.cpu.gpr.rsp - 8) (toBytesLE (opd_at.add 153) 8)) →
      Y.cpu.rip = Mal.mal_at → Y.cpu.gpr = (cG V X.cpu.gpr).set 4 (X.cpu.gpr.rsp - 8) →
      GoG prof L o gev gP gE Y t') :
    GoG prof L o gev gP gE X t := by
  refine (c_80 prof fb).run c hfs hin (fun j' g' _ V' => j' = 148 ∧ g' = cG V X.cpu.gpr ∧ V' = V) hK hA hrip
    (vc_80 hs hm f24 f56) ?_
  rintro j' g fl V₁ ⟨rfl, rfl, hV⟩ Y t₁ hKY hAY hrY hgY -
  subst V₁
  have hsY : Y.cpu.gpr.rsp = X.cpu.gpr.rsp := by rw [hgY]
  refine c.s_call hKY hAY hin (lt_len (by decide)) hrY (call_148 _) hinM (Mal.lt_len (j := 0) (by decide))
    (by decide) (by rw [hsY]; exact hw) ?_
  rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
  rw [hsY] at hA₂
  exact k Y₂ t₂ hK₂ hA₂ hr₂ (by rw [hg₂, hgY])

/-- From the return of `malloc` (153), the block `p` (`rax`) not null, its 44 bytes in what the run may store into:
at 219 with the `DIR`'s fields stored (`Vd`) and `r12` = `p`. -/
theorem opd_dir {fb : Addr} (c : Seg prof F Wl L s₀ o) (hfs : s₀.cpu.seg.fsBase = fb) (hin : CodeIn L opd_at opd)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = opd_at.add 153)
    (hnz : X.cpu.gpr.rax ≠ 0#64)
    (hdw : ∀ i < 44, Foot Wl (Addr.add X.cpu.gpr.rax i)) (hdb : X.cpu.gpr.rax.toNat + 44 ≤ 2 ^ 64)
    (k : ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y →
      Agree F Y.proc.mm.mem (Vd V X.cpu.gpr.rax X.cpu.gpr.rbp X.cpu.gpr.rbx) → Y.cpu.rip = opd_at.add 219 →
      Y.cpu.gpr = { X.cpu.gpr with r12 := X.cpu.gpr.rax } → GoG prof L o gev gP gE Y t') :
    GoG prof L o gev gP gE X t := by
  have hpl := X.cpu.gpr.rax.isLt
  have a4 : (X.cpu.gpr.rax + 4#64).toNat = X.cpu.gpr.rax.toNat + 4 := tAdd _ 4 (by omega)
  have a8 : (X.cpu.gpr.rax + 8#64).toNat = X.cpu.gpr.rax.toNat + 8 := tAdd _ 8 (by omega)
  have a16 : (X.cpu.gpr.rax + 16#64).toNat = X.cpu.gpr.rax.toNat + 16 := tAdd _ 16 (by omega)
  have a24 : (X.cpu.gpr.rax + 24#64).toNat = X.cpu.gpr.rax.toNat + 24 := tAdd _ 24 (by omega)
  have a32 : (X.cpu.gpr.rax + 32#64).toNat = X.cpu.gpr.rax.toNat + 32 := tAdd _ 32 (by omega)
  have a40 : (X.cpu.gpr.rax + 40#64).toNat = X.cpu.gpr.rax.toNat + 40 := tAdd _ 40 (by omega)
  refine (c_153 prof fb).run c hfs hin (fun j' g' _ V' => j' = 165 ∧ g' = { X.cpu.gpr with r12 := X.cpu.gpr.rax } ∧
      V' = V) hK hA hrip (vc_153 (g := X.cpu.gpr) hnz) ?_
  rintro j' g fl V₁ ⟨rfl, rfl, hV⟩ Y₁ t₁ hK₁ hA₁ hr₁ hg₁ -
  subst V₁
  have h12 : Y₁.cpu.gpr.r12 = X.cpu.gpr.rax := by rw [hg₁]
  have hbp : Y₁.cpu.gpr.rbp = X.cpu.gpr.rbp := by rw [hg₁]
  have hbx : Y₁.cpu.gpr.rbx = X.cpu.gpr.rbx := by rw [hg₁]
  refine (c_165 prof fb).run c hfs hin _ hK₁ hA₁ hr₁
    (vc_165 (g := Y₁.cpu.gpr) (by rw [h12]; exact frw hdw (fa (d := 0) (by omega) (by simp)) (by decide))
      (by rw [h12]; exact frw hdw (fa (d := 4) (by omega) a4) (by decide))
      (by rw [h12]; exact frw hdw (fa (d := 8) (by omega) a8) (by decide))
      (by rw [h12]; exact frw hdw (fa (d := 16) (by omega) a16) (by decide))
      (by rw [h12]; exact frw hdw (fa (d := 24) (by omega) a24) (by decide))
      (by rw [h12]; exact frw hdw (fa (d := 32) (by omega) a32) (by decide))
      (by rw [h12]; exact frw hdw (fa (d := 40) (by omega) a40) (by decide))) ?_
  rintro j' g fl V₂ ⟨rfl, rfl, hV⟩ Y₂ t₂ hK₂ hA₂ hr₂ hg₂ -
  subst V₂
  rw [h12, hbp, hbx] at hA₂
  exact k Y₂ t₂ hK₂ hA₂ hr₂ (hg₂.trans hg₁)

/-- From 219, the frame's 208 bytes at `rsp` in what the run may read, the stack guard at `rsp + 152` the one at
`fs:0x28`: at the return address (at `rsp + 200`) with `rax` = `r12`, `rsp` 208 above, `rbx`, `rbp`, `r12`, `r13`
popped from `rsp + 168` … `rsp + 192`. -/
theorem opd_tail {fb : Addr} (c : Seg prof F Wl L s₀ o) (hfs : s₀.cpu.seg.fsBase = fb) (hin : CodeIn L opd_at opd)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = opd_at.add 219)
    (hfd : ∀ i < 208, Foot F.data (Addr.add X.cpu.gpr.rsp i)) (hsb : X.cpu.gpr.rsp.toNat + 208 ≤ 2 ^ 64)
    (hcl : ∀ i < 8, Foot F.data (Addr.add (fb + 40#64) i))
    (hc : rdq(V, X.cpu.gpr.rsp + 152#64) = rdq(V, fb + 40#64))
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (hra : rdq(V, X.cpu.gpr.rsp + 200#64) = e₂.add j₂)
    (k : ∀ (Z : State) (t' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V → Z.cpu.rip = e₂.add j₂ →
      Z.cpu.gpr.rsp = X.cpu.gpr.rsp + 208#64 → Z.cpu.gpr.rax = X.cpu.gpr.r12 →
      Z.cpu.gpr.rbx = rdq(V, X.cpu.gpr.rsp + 168#64) → Z.cpu.gpr.rbp = rdq(V, X.cpu.gpr.rsp + 176#64) →
      Z.cpu.gpr.r12 = rdq(V, X.cpu.gpr.rsp + 184#64) → Z.cpu.gpr.r13 = rdq(V, X.cpu.gpr.rsp + 192#64) →
      Z.cpu.gpr.r14 = X.cpu.gpr.r14 → Z.cpu.gpr.r15 = X.cpu.gpr.r15 →
      GoG prof L o gev gP gE Z t') :
    GoG prof L o gev gP gE X t := by
  have q152 : (X.cpu.gpr.rsp + 152#64).toNat = X.cpu.gpr.rsp.toNat + 152 := tAdd _ 152 (by omega)
  have q168 : (X.cpu.gpr.rsp + 168#64).toNat = X.cpu.gpr.rsp.toNat + 168 := tAdd _ 168 (by omega)
  have q176 : (X.cpu.gpr.rsp + 168#64 + 8).toNat = X.cpu.gpr.rsp.toNat + 176 :=
    (tAdd (X.cpu.gpr.rsp + 168#64) 8 (by omega)).trans (by omega)
  have q184 : (X.cpu.gpr.rsp + 168#64 + 8 + 8).toNat = X.cpu.gpr.rsp.toNat + 184 :=
    (tAdd (X.cpu.gpr.rsp + 168#64 + 8) 8 (by omega)).trans (by omega)
  have q192 : (X.cpu.gpr.rsp + 168#64 + 8 + 8 + 8).toNat = X.cpu.gpr.rsp.toNat + 192 :=
    (tAdd (X.cpu.gpr.rsp + 168#64 + 8 + 8) 8 (by omega)).trans (by omega)
  have q200 : (X.cpu.gpr.rsp + 168#64 + 8 + 8 + 8 + 8).toNat = X.cpu.gpr.rsp.toNat + 200 :=
    (tAdd (X.cpu.gpr.rsp + 168#64 + 8 + 8 + 8) 8 (by omega)).trans (by omega)
  refine (c_219 prof fb).run c hfs hin _ hK hA hrip
    (vc_219 (g := X.cpu.gpr) hc (frw hfd (fa (d := 152) (by omega) q152) (by decide)) hcl
      (frw hfd (fa (d := 168) (by omega) q168) (by decide)) (frw hfd (fa (d := 176) (by omega) q176) (by decide))
      (frw hfd (fa (d := 184) (by omega) q184) (by decide))
      (frw hfd (fa (d := 192) (by omega) q192) (by decide))) ?_
  rintro j' g fl V₃ ⟨rfl, rfl, hV⟩ Y₃ t₃ hK₃ hA₃ hr₃ hg₃ -
  subst V₃
  have hs3 : Y₃.cpu.gpr.rsp = X.cpu.gpr.rsp + 168#64 + 8 + 8 + 8 + 8 := by rw [hg₃]
  refine c.s_ret hK₃ hA₃ hin (lt_len (by decide)) hr₃ (ret_254 _)
    (by rw [hs3]; exact frw hfd (fa (d := 200) (by omega) q200) (by decide)) hin₂ h₂
    (by rw [hs3, pa4]; exact hra) ?_
  rintro Z t₄ hKZ hAZ ⟨hrZ, hgZ⟩
  obtain ⟨z1, z2, z3, z4, z5, z6, z7, z8⟩ := dGs V X.cpu.gpr (Y₃.cpu.gpr.rsp + 8)
  rw [← hg₃, ← hgZ] at z1 z2 z3 z4 z5 z6 z7 z8
  exact k Z t₄ hKZ hAZ hrZ (by rw [z1, hs3, pa5]) z2 z3 (by rw [z4, pa1]) (by rw [z5, pa2]) (by rw [z6, pa3]) z7 z8

/-- From the return of `malloc` (153), the block `p` (`rax`) not null, its 44 bytes in what the run may store into
and apart from the frame's 208 bytes at `rsp` and from the stack guard, the stack guard at `rsp + 152` the one at
`fs:0x28`: at the return address (at `rsp + 200`) with the `DIR`'s fields stored (`Vd`), `rax` = `p`, `rsp` 208 above,
`rbx`, `rbp`, `r12`, `r13` popped from `rsp + 168` … `rsp + 192`. -/
theorem opd_ret {fb : Addr} (c : Seg prof F Wl L s₀ o) (hfs : s₀.cpu.seg.fsBase = fb) (hin : CodeIn L opd_at opd)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = opd_at.add 153)
    (hnz : X.cpu.gpr.rax ≠ 0#64)
    (hdw : ∀ i < 44, Foot Wl (Addr.add X.cpu.gpr.rax i)) (hdb : X.cpu.gpr.rax.toNat + 44 ≤ 2 ^ 64)
    (hfd : ∀ i < 208, Foot F.data (Addr.add X.cpu.gpr.rsp i)) (hsb : X.cpu.gpr.rsp.toNat + 208 ≤ 2 ^ 64)
    (hdd : X.cpu.gpr.rax.toNat + 44 ≤ X.cpu.gpr.rsp.toNat ∨ X.cpu.gpr.rsp.toNat + 208 ≤ X.cpu.gpr.rax.toNat)
    (hcl : ∀ i < 8, Foot F.data (Addr.add (fb + 40#64) i)) (hcb : (fb + 40#64).toNat + 8 ≤ 2 ^ 64)
    (hcd : X.cpu.gpr.rax.toNat + 44 ≤ (fb + 40#64).toNat ∨ (fb + 40#64).toNat + 8 ≤ X.cpu.gpr.rax.toNat)
    (hc : rdq(V, X.cpu.gpr.rsp + 152#64) = rdq(V, fb + 40#64))
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (hra : rdq(V, X.cpu.gpr.rsp + 200#64) = e₂.add j₂)
    (k : ∀ (Z : State) (t' : Nat), KeptW Wl s₀ Z →
      Agree F Z.proc.mm.mem (Vd V X.cpu.gpr.rax X.cpu.gpr.rbp X.cpu.gpr.rbx) → Z.cpu.rip = e₂.add j₂ →
      Z.cpu.gpr.rsp = X.cpu.gpr.rsp + 208#64 → Z.cpu.gpr.rax = X.cpu.gpr.rax →
      Z.cpu.gpr.rbx = rdq(V, X.cpu.gpr.rsp + 168#64) → Z.cpu.gpr.rbp = rdq(V, X.cpu.gpr.rsp + 176#64) →
      Z.cpu.gpr.r12 = rdq(V, X.cpu.gpr.rsp + 184#64) → Z.cpu.gpr.r13 = rdq(V, X.cpu.gpr.rsp + 192#64) →
      Z.cpu.gpr.r14 = X.cpu.gpr.r14 → Z.cpu.gpr.r15 = X.cpu.gpr.r15 →
      GoG prof L o gev gP gE Z t') :
    GoG prof L o gev gP gE X t := by
  have hlt := X.cpu.gpr.rsp.isLt
  have q152 : (X.cpu.gpr.rsp + 152#64).toNat = X.cpu.gpr.rsp.toNat + 152 := tAdd _ 152 (by omega)
  have q168 : (X.cpu.gpr.rsp + 168#64).toNat = X.cpu.gpr.rsp.toNat + 168 := tAdd _ 168 (by omega)
  have r176 : (X.cpu.gpr.rsp + 176#64).toNat = X.cpu.gpr.rsp.toNat + 176 := tAdd _ 176 (by omega)
  have r184 : (X.cpu.gpr.rsp + 184#64).toNat = X.cpu.gpr.rsp.toNat + 184 := tAdd _ 184 (by omega)
  have r192 : (X.cpu.gpr.rsp + 192#64).toNat = X.cpu.gpr.rsp.toNat + 192 := tAdd _ 192 (by omega)
  have r200 : (X.cpu.gpr.rsp + 200#64).toNat = X.cpu.gpr.rsp.toNat + 200 := tAdd _ 200 (by omega)
  -- reads apart from the `DIR`
  have vd : ∀ (x : Addr) (n : Nat), x.toNat + n ≤ 2 ^ 64 →
      x.toNat + n ≤ X.cpu.gpr.rax.toNat ∨ X.cpu.gpr.rax.toNat + 44 ≤ x.toNat →
      ofBytesLE 64 ((byteAddrs x n).map (Vd V X.cpu.gpr.rax X.cpu.gpr.rbp X.cpu.gpr.rbx)) =
        ofBytesLE 64 ((byteAddrs x n).map V) := fun x n h1 h2 =>
    congrArg (ofBytesLE 64) (Vd_rd V _ _ _ hdb h1 h2)
  refine opd_dir c hfs hin hK hA hrip hnz hdw hdb ?_
  intro Y₂ t₂ hK₂ hA₂ hr₂ hg₂
  have hs2 : Y₂.cpu.gpr.rsp = X.cpu.gpr.rsp := by rw [hg₂]
  have h12 : Y₂.cpu.gpr.r12 = X.cpu.gpr.rax := by rw [hg₂]
  have h14 : Y₂.cpu.gpr.r14 = X.cpu.gpr.r14 := by rw [hg₂]
  have h15 : Y₂.cpu.gpr.r15 = X.cpu.gpr.r15 := by rw [hg₂]
  refine opd_tail c hfs hin hK₂ hA₂ hr₂ (by rw [hs2]; exact hfd) (by rw [hs2]; exact hsb) hcl ?_ hin₂ h₂ ?_ ?_
  · rw [hs2, vd (X.cpu.gpr.rsp + 152#64) 8 (by omega) (by omega), vd (fb + 40#64) 8 hcb (by omega)]
    exact hc
  · rw [hs2, vd (X.cpu.gpr.rsp + 200#64) 8 (by omega) (by omega)]
    exact hra
  intro Z t₄ hKZ hAZ hrZ z1 z2 z3 z4 z5 z6 z7 z8
  refine k Z t₄ hKZ hAZ hrZ (by rw [z1, hs2]) (by rw [z2, h12]) ?_ ?_ ?_ ?_ (by rw [z7, h14]) (by rw [z8, h15])
  · rw [z3, hs2, vd (X.cpu.gpr.rsp + 168#64) 8 (by omega) (by omega)]
  · rw [z4, hs2, vd (X.cpu.gpr.rsp + 176#64) 8 (by omega) (by omega)]
  · rw [z5, hs2, vd (X.cpu.gpr.rsp + 184#64) 8 (by omega) (by omega)]
  · rw [z6, hs2, vd (X.cpu.gpr.rsp + 192#64) 8 (by omega) (by omega)]

end FV7z.Opd
