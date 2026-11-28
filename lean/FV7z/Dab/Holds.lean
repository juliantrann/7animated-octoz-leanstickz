import FV7z.Dab.Cuts
import FV7z.Tun.Inv
/-!
# `_IO_doallocbuf`: the pieces without a `call` (PLAN.md §M, M1)

glibc 2.31's `_IO_doallocbuf (fp)` at `0x62b500` in `7zzs` (`libio/genops.c`, `tools/blk_gen.py` "dab").

- `vc_0`: `fp->_IO_buf_base` (`[fp + 0x38]`) compared with 0: not 0 to the `ret` at 11, else to 16.
- `vc_144`: `rbp` = `fp + 0x84`, `r12` = `fp + 0x83` (`_shortbuf + 1`, `_shortbuf`), to 114.
- `vc_114`: the flags word `| 1` (`_IO_USER_BUF`) stored at `fp`, the 16 bytes at `fp + 0x38` stored (`movups`
  of `xmm0`, the register's value not followed: any 16 bytes), to 137.
- `vc_137`: the three pops, to the `ret` at 141.

Left (the exact next step): `vc_16` (pushes, `fp->_flags & _IO_UNBUFFERED`, `fp->_mode` at `fp + 0xc0`, `jle` to
144) and the run `dab_ok` of the two ways without a `call` (the buffer there: 0 .. 11; unbuffered and `_mode` not
positive: 0 → 16 → 29 → 144 → 114 → 137 → 141), as `Gtd/Holds.lean` chains its pieces. The vtable's `doallocate`
(`call [rbp + 0x68]` at 77, after the vtable section check at 39 and `_IO_vtable_check` at 176) and `free` (160)
need callee hypotheses, as `Stb/Holds.lean` takes `free`. A spec that names the two stored pointers needs the `xmm`
moves as `Seg` steps (`Seg.s_movq_ld` and its like, `Lemmas/BlkOps4.lean`) instead of `vop`.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Dab

set_option linter.unusedSimpArgs false

/-- One step of the closers of the pieces. -/
macro "ostep" : tactic => `(tactic| first
  | with_reducible rfl
  | with_reducible assumption
  | exact rfl
  | apply And.intro
  | intro _)

section Pieces
variable {F : Footprint} {Wl : List Rgn}

/-- `endbr64`, `cmp qword [rdi + 0x38], 0`: not 0 to the `ret` at 11, else to 16. -/
theorem vc_0 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (hf : ∀ i < 8, Foot F.data (Addr.add (g.rdi + 56#64) i))
    (h11 : rdq(V, g.rdi + 56#64) ≠ 0 → ∀ fl, Q 11 g fl V)
    (h16 : rdq(V, g.rdi + 56#64) = 0 → ∀ fl, W_16 F Wl Q g fl V) :
    W_0 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hf h11 h16 ⊢
  wpx [W_0, o0, Op.cmpmi, subR_eq, BitVec.sub_zero, beq_iff_eq, Bool.not_eq_eq_eq_not, Bool.not_true,
    beq_eq_false_iff_ne, ne_eq]
  refine ⟨hf, fun h => h16 (of_decide_eq_true h) _, fun h => h11 (of_decide_eq_false h) _⟩

/-- `lea rbp, [rdi + 0x84]`, `lea r12, [rdi + 0x83]`, to 114. -/
theorem vc_144 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (h114 : ∀ g', g'.rbp = g.rdi + 132#64 → g'.r12 = g.rdi + 131#64 → g'.rbx = g.rbx → g'.rsp = g.rsp →
      g'.rdi = g.rdi → g'.rax = g.rax → ∀ fl, Q 114 g' fl V) :
    W_144 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h114 ⊢
  wpx [W_144, o10]
  all_goals repeat' (first
    | refine h114 _ ?_ ?_ ?_ ?_ ?_ ?_ _
    | ostep)

/-- `or eax, 1`, the `xmm` moves, `[rbx]` = `eax`, the 16 bytes at `rbx + 0x38` any, to 137. -/
theorem vc_114 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (hw : ∀ i < 4, Foot Wl (Addr.add g.rbx i)) (hb : ∀ i < 16, Foot Wl (Addr.add (g.rbx + 56#64) i))
    (h137 : ∀ bs : List Byte, bs.length = 16 → ∀ g' fl, g'.rsp = g.rsp → g'.rbx = g.rbx →
      Q 137 g' fl (Vst (Vst V g.rbx (toBytesLE ((g.rax.setWidth 32) ||| 1#32) 4)) (g.rbx + 56#64) bs)) :
    W_114 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hw hb h137 ⊢
  wpx [W_114, o8, Op.vs]
  all_goals repeat' (first
    | refine h137 _ (by assumption) _ _ ?_ ?_
    | with_reducible exact hw
    | with_reducible exact hb
    | exact fun i hi => absurd hi (Nat.not_lt_zero _)
    | ostep)

/-- `pop rbx`, `pop rbp`, `pop r12`, to the `ret` at 141. -/
theorem vc_137 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (f1 : ∀ i < 8, Foot F.data (Addr.add g.rsp i)) (f2 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8) i))
    (f3 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8 + 8) i))
    (h141 : ∀ g', g'.rsp = g.rsp + 8 + 8 + 8 → g'.rbx = rdq(V, g.rsp) → g'.rbp = rdq(V, g.rsp + 8) →
      g'.r12 = rdq(V, g.rsp + 8 + 8) → ∀ fl, Q 141 g' fl V) :
    W_137 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at f1 f2 f3 h141 ⊢
  wpx [W_137, o9]
  all_goals repeat' (first
    | refine h141 _ ?_ ?_ ?_ ?_ _
    | with_reducible exact f1
    | with_reducible exact f2
    | with_reducible exact f3
    | ostep)

end Pieces

end FV7z.Dab
