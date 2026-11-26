import FV7z.Mck.Steps
import FV7z.Tun.Inv
/-!
# `munmap_chunk`: the straight pieces (PLAN.md §M, M1)

The pieces of `munmap_chunk (p)` (glibc 2.31, at `0x62e660`, `rdi = p`) when its checks hold: the size word `sz` at
`p + 8` with `IS_MMAPPED` (bit 1) set, `prev_size` `pv` at `p`, the page size `ps` (`GLRO (dl_pagesize)`, at
`0x7933d8`); the block `p - pv` and its length `pv + chunksize (p)` multiples of the page size and `chunk2mem (p)`'s
offset in its page a power of two or 0 (`mckc`, as the code computes it, is 0).

- `vc_0`: the checks, to the `lock dec` of `mp_.n_mmaps` (71): `rsi` the length, `r8` the block.
- `vc_78`: `rax = -rsi`, to the `lock add` of `mp_.mmapped_mem` (84).
- `vc_92`: `rdi` the block, the frame given back, to the tail call (99).
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Mck

/-- What the pieces from the entry keep: the registers a call keeps. -/
abbrev Km (g g' : Gprs) : Prop :=
  g'.rbx = g.rbx ∧ g'.rbp = g.rbp ∧ g'.r12 = g.r12 ∧ g'.r13 = g.r13 ∧ g'.r14 = g.r14 ∧ g'.r15 = g.r15

/-- The check of `munmap_chunk` as the code computes it (0 when it holds): `(block | length) & (ps - 1)`, or'ed
with `m & (m - 1)` for `m = chunk2mem (p) & (ps - 1)`. -/
abbrev mckc (p pv sz ps : Addr) : Addr :=
  (ps - 1#64 &&& (p - pv ||| pv + (sz &&& 18446744073709551608#64))) |||
    ((p + 16#64 &&& ps - 1#64) &&& (p + 16#64 &&& ps - 1#64) + 18446744073709551615#64)

set_option hygiene false in
/-- The extra lemmas of the pieces' `wp`. -/
macro "mckx" cfg:Lean.Parser.Tactic.optConfig "[" ls:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| wpx $cfg [Op.lda, BitVec.reduceAdd, BitVec.reduceAnd, BitVec.reduceBEq, BitVec.reduceSub,
      Bool.not_false, Bool.not_true, Bool.false_eq_true, false_imp_iff, true_imp_iff, false_implies, true_implies,
      and_true, true_and, Bool.true_eq_false, BitVec.add_zero, implies_true, forall_const, Km, $ls,*])

variable {F : Footprint} {Wl : List Rgn}

set_option maxHeartbeats 2000000 in
/-- The checks hold: to the `lock dec` (71), `rsi` the length, `r8` the block. -/
theorem vc_0 {fb ps sz pv : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (hps : rdq(V, 7943128#64) = ps) (hsz : rdq(V, g.rdi + 8#64) = sz) (hpv : rdq(V, g.rdi) = pv)
    (hmm : (sz.setWidth 32 &&& 2#32 == 0) = false) (hck : (mckc g.rdi pv sz ps == 0) = true)
    (f1 : ∀ i < 8, Foot F.data (Addr.add 7943128#64 i)) (f2 : ∀ i < 8, Foot F.data (Addr.add (g.rdi + 8#64) i))
    (f3 : ∀ i < 8, Foot F.data (Addr.add g.rdi i)) :
    W_0 fb F Wl (fun j' g' _ V' => j' = 71 ∧ V' = V ∧ g'.rsi = pv + (sz &&& 18446744073709551608#64) ∧
      g'.r8 = g.rdi - pv ∧ g'.rsp = g.rsp - 8#64 ∧ Km g g') g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [mckc] at hsz hpv hck f2 f3 ⊢
  mckx [W_0, W_27, o0, o1, hps, hsz, hpv, hmm, hck, f1, f2, f3]
  all_goals (and_intros <;> assumption)

/-- `rax = -rsi`, to the `lock add` (84). -/
theorem vc_78 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} :
    W_78 fb F Wl (fun j' g' _ V' => j' = 84 ∧ V' = V ∧ g' = { g with rax := 0 - g.rsi }) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  mckx [W_78, o2]

/-- `rdi` the block, the frame given back, to the tail call (99). -/
theorem vc_92 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} :
    W_92 fb F Wl (fun j' g' _ V' => j' = 99 ∧ V' = V ∧ g' = { g with rdi := g.r8, rsp := g.rsp + 8#64 }) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  mckx [W_92, o3]

end FV7z.Mck
