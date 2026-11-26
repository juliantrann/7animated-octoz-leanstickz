import FV7z.Mcn.Steps
import FV7z.Cal.Vc
import FV7z.Lemmas.CmpImm
/-!
# `malloc_consolidate`: the straight pieces (PLAN.md §M, M1)

The pieces of glibc 2.31's `malloc_consolidate (av)` (at `0x62eb00`, `rdi = av`). In the loops `r15 = av`,
`r13` the fastbin (`fb`), `rbx` the chunk `p`, `rdx` the next one (`nextp`), `rbp` the size, `r12` the chunk after
(`nextchunk`), `r14` its size; `[rsp]` keeps `nextp` across the calls of `unlink_chunk`, `[rsp + 8]` is
`unsorted_chunks (av)` (`av + 0x60`).

- `vc_0`: the six pushes, `av->have_fastchunks = false`, `r13 = &av->fastbinsY[0]`; to 37.
- `vc_37`: `ebx = 0`, to the `xchg` (39). `vc_43n`, `vc_43z`: the bin's first chunk, to 164 or (empty) to 48.
- `vc_48c`, `vc_48e`: the next bin (to 37), or after the last one, the epilogue to the `ret` (73).
- `vc_164u`, `vc_164f`: the fastbin index checked (`fbx`), `nextp`, `size`, `nextchunk`, `nextsize`; with the
  previous chunk in use, to 256; else `p` the previous chunk and `size` the sum (its size checked), `[rsp] = nextp`,
  to the `call` of `unlink_chunk` (247). `vc_252`: `nextp` back, to 256.
- `vc_256t`: `nextchunk` the top: `p` the new top, to 156. `vc_256i`, `vc_256f`: `nextchunk` in use, to the `and`
  (92); free, `size` the sum, `[rsp] = nextp`, to the `call` of `unlink_chunk` (298). `vc_303`: `nextchunk` again,
  `nextp` back, to 98.
- `vc_98s`, `vc_98l`: `p` first in the unsorted bin, `first_unsorted->bk = p`; a small chunk to 127, a large one to
  the `pxor` (119). `vc_127`, `vc_135`, `vc_144`, `vc_152`: `set_head (p, size | PREV_INUSE)`, `set_foot (p, size)`
  around the `xmm` steps.
- `vc_156z`, `vc_156n`: `nextp` null, to 48; else `p = nextp`, to 164.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Mcn

/-- The extra lemmas of the pieces' `wp`. -/
macro "mcx" cfg:Lean.Parser.Tactic.optConfig "[" ls:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| wpx $cfg [Op.lda, Op.cmpmr, Op.testmi, BitVec.and_self,
      BitVec.reduceAdd, BitVec.reduceAnd, BitVec.reduceSetWidth, BitVec.reduceBEq, BitVec.reduceBNe, BitVec.reduceEq,
      BitVec.reduceToNat, BitVec.reduceSub, BitVec.reduceOr, BitVec.reduceXOr, BitVec.reduceNot, BitVec.setWidth_zero,
      BitVec.or_zero, BitVec.and_zero, BitVec.zero_and, BitVec.zero_or,
      Nat.reduceAdd, Nat.reduceSub, Nat.reduceLeDiff, Nat.reduceLT, decide_false, decide_true, Bool.or_false,
      Bool.false_or, Bool.not_false, Bool.not_true, Bool.false_eq_true, false_imp_iff, true_imp_iff, Bool.or_self,
      Bool.true_or, Bool.or_true, false_implies, true_implies, and_true, true_and, reduceIte, or_true, true_or,
      or_false, false_or, ne_eq, Nat.reduceEqDiff, not_false_eq_true, ofBytesLE_toBytesLE, Bool.true_eq_false,
      BitVec.xor_self, BitVec.add_zero, decide_eq_true_eq, implies_true, forall_const, eq_self_iff_true,
      decide_eq_false_iff_not, $ls,*])

/-- The six pushes under `S`. -/
abbrev fr6 (V : Addr → Byte) (S : Addr) (a b c d e f : BitVec 64) : Addr → Byte :=
  Vst (Vst (Vst (Vst (Vst (Vst V (S - 8) (toBytesLE a 8)) (S - 8 - 8) (toBytesLE b 8)) (S - 8 - 8 - 8)
    (toBytesLE c 8)) (S - 8 - 8 - 8 - 8) (toBytesLE d 8)) (S - 8 - 8 - 8 - 8 - 8) (toBytesLE e 8))
    (S - 8 - 8 - 8 - 8 - 8 - 8) (toBytesLE f 8)

/-- `&fastbin (av, fastbin_index (size))` as the code computes it (`size` the size word, 32 bits of it). -/
abbrev fbx (av sz : Addr) : Addr := av + ((sz.setWidth 32 >>> 4) - 2#32).setWidth 64 * 8#64 + 16#64

variable {F : Footprint} {Wl : List Rgn}

set_option maxHeartbeats 2000000 in
/-- The six pushes, `av->have_fastchunks = false`, `[rsp + 8] = unsorted_chunks (av)`, `r13 = &fastbin (av, 0)`;
to 37. -/
theorem vc_0 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (w1 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8) i)) (w2 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8) i))
    (w3 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8 - 8) i))
    (w4 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8 - 8 - 8) i))
    (w5 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8 - 8 - 8 - 8) i))
    (w6 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8 - 8 - 8 - 8 - 8) i))
    (w7 : ∀ i < 4, Foot Wl (Addr.add (g.rdi + 8#64) i))
    (w8 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8 - 8 - 8 - 8 - 8 - 24#64 + 8#64) i)) :
    W_0 fb F Wl (fun j' g' _ V' => j' = 37 ∧
      V' = Vst (Vst (fr6 V g.rsp g.r15 g.r14 g.r13 g.r12 g.rbp g.rbx) (g.rdi + 8#64) (toBytesLE 0#32 4))
        (g.rsp - 8 - 8 - 8 - 8 - 8 - 8 - 24#64 + 8#64) (toBytesLE (g.rdi + 96#64) 8) ∧
      g'.rsp = g.rsp - 8 - 8 - 8 - 8 - 8 - 8 - 24#64 ∧ g'.r15 = g.rdi ∧ g'.r13 = g.rdi + 16#64 ∧
      g'.rbx = g.rbx ∧ g'.rbp = g.rbp ∧ g'.r12 = g.r12 ∧ g'.r14 = g.r14) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at w1 w2 w3 w4 w5 w6 w7 w8 ⊢
  mcx +contextual [W_0, o0, fr6, w1, w2, w3, w4, w5, w6, w7, w8]

/-- `ebx = 0`, to the `xchg` (39). -/
theorem vc_37 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} :
    W_37 fb F Wl (fun j' g' _ V' => j' = 39 ∧ V' = V ∧ g' = { g with rbx := 0#64 }) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  mcx +contextual [W_37, o1]

/-- A chunk in the bin: to 164. -/
theorem vc_43n {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} (hz : (g.rbx == 0) = false) :
    W_43 fb F Wl (fun j' g' _ V' => j' = 164 ∧ V' = V ∧ g' = g) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hz ⊢
  mcx +contextual [W_43, o2, hz]

/-- The bin empty: to 48. -/
theorem vc_43z {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} (hz : (g.rbx == 0) = true) :
    W_43 fb F Wl (fun j' g' _ V' => j' = 48 ∧ V' = V ∧ g' = g) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hz ⊢
  mcx +contextual [W_43, o2, hz]

/-- Not the last bin: the next one, to 37. -/
theorem vc_48c {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (hne : ¬ rdq(V, g.rsp + 8#64) = g.r13 + 8#64) (f1 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8#64) i)) :
    W_48 fb F Wl (fun j' g' _ V' => j' = 37 ∧ V' = V ∧ g' = { g with r13 := g.r13 + 8#64 }) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hne f1 ⊢
  mcx +contextual [W_48, W_59, o3, o4, hne, f1]

set_option maxHeartbeats 2000000 in
/-- After the last bin: the epilogue, to the `ret` (73). -/
theorem vc_48e {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (heq : rdq(V, g.rsp + 8#64) = g.r13 + 8#64) (f1 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8#64) i))
    (p0 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 24#64) i))
    (p1 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 24#64 + 8) i))
    (p2 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 24#64 + 8 + 8) i))
    (p3 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 24#64 + 8 + 8 + 8) i))
    (p4 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 24#64 + 8 + 8 + 8 + 8) i))
    (p5 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 24#64 + 8 + 8 + 8 + 8 + 8) i)) :
    W_48 fb F Wl (fun j' g' _ V' => j' = 73 ∧ V' = V ∧ g'.rsp = g.rsp + 24#64 + 8 + 8 + 8 + 8 + 8 + 8 ∧
      g'.rbx = rdq(V, g.rsp + 24#64) ∧ g'.rbp = rdq(V, g.rsp + 24#64 + 8) ∧
      g'.r12 = rdq(V, g.rsp + 24#64 + 8 + 8) ∧ g'.r13 = rdq(V, g.rsp + 24#64 + 8 + 8 + 8) ∧
      g'.r14 = rdq(V, g.rsp + 24#64 + 8 + 8 + 8 + 8) ∧ g'.r15 = rdq(V, g.rsp + 24#64 + 8 + 8 + 8 + 8 + 8)) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at heq f1 p0 p1 p2 p3 p4 p5 ⊢
  mcx +contextual [W_48, W_59, o3, o4, heq, f1, p0, p1, p2, p3, p4, p5]

set_option maxHeartbeats 4000000 in
/-- The chunk's checks and words, the previous chunk in use: to 256. -/
theorem vc_164u {fb sz nx ns : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (hsz : rdq(V, g.rbx + 8#64) = sz) (hfb : fbx g.r15 sz = g.r13) (hnx : rdq(V, g.rbx + 16#64) = nx)
    (hns : rdq(V, g.rbx + (sz &&& 18446744073709551608#64) + 8#64) = ns)
    (hb : (sz.setWidth 8 &&& 1#8 == 0) = false)
    (f1 : ∀ i < 8, Foot F.data (Addr.add (g.rbx + 8#64) i)) (f2 : ∀ i < 8, Foot F.data (Addr.add (g.rbx + 16#64) i))
    (f3 : ∀ i < 8, Foot F.data (Addr.add (g.rbx + (sz &&& 18446744073709551608#64) + 8#64) i)) :
    W_164 fb F Wl (fun j' g' _ V' => j' = 256 ∧ V' = V ∧ g'.rbx = g.rbx ∧ g'.rbp = sz &&& 18446744073709551608#64 ∧
      g'.rdx = nx ∧ g'.r12 = g.rbx + (sz &&& 18446744073709551608#64) ∧ g'.r14 = ns &&& 18446744073709551608#64 ∧
      g'.r13 = g.r13 ∧ g'.r15 = g.r15 ∧ g'.rsp = g.rsp) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [fbx] at hsz hfb hnx hns f1 f2 f3 ⊢
  mcx +contextual [W_164, W_190, W_218, W_240, o13, o14, o15, o16, hsz, hfb, hnx, hns, hb, f1, f2, f3]

set_option maxHeartbeats 4000000 in
/-- The chunk's checks and words, the previous chunk free: `p` the previous chunk, `size` the sum,
`[rsp] = nextp`, `rdi = p`; to the `call` of `unlink_chunk` (247). -/
theorem vc_164f {fb sz nx ns pv : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (hsz : rdq(V, g.rbx + 8#64) = sz) (hfb : fbx g.r15 sz = g.r13) (hnx : rdq(V, g.rbx + 16#64) = nx)
    (hns : rdq(V, g.rbx + (sz &&& 18446744073709551608#64) + 8#64) = ns)
    (hb : (sz.setWidth 8 &&& 1#8 == 0) = true) (hpv : rdq(V, g.rbx) = pv)
    (hck : rdq(V, g.rbx - pv + 8#64) &&& 18446744073709551608#64 = pv)
    (f1 : ∀ i < 8, Foot F.data (Addr.add (g.rbx + 8#64) i)) (f2 : ∀ i < 8, Foot F.data (Addr.add (g.rbx + 16#64) i))
    (f3 : ∀ i < 8, Foot F.data (Addr.add (g.rbx + (sz &&& 18446744073709551608#64) + 8#64) i))
    (f4 : ∀ i < 8, Foot F.data (Addr.add g.rbx i)) (f5 : ∀ i < 8, Foot F.data (Addr.add (g.rbx - pv + 8#64) i))
    (w : ∀ i < 8, Foot Wl (Addr.add g.rsp i)) :
    W_164 fb F Wl (fun j' g' _ V' => j' = 247 ∧ V' = Vst V g.rsp (toBytesLE nx 8) ∧ g'.rdi = g.rbx - pv ∧
      g'.rbx = g.rbx - pv ∧ g'.rbp = (sz &&& 18446744073709551608#64) + pv ∧ g'.rdx = nx ∧
      g'.r12 = g.rbx + (sz &&& 18446744073709551608#64) ∧ g'.r14 = ns &&& 18446744073709551608#64 ∧
      g'.r13 = g.r13 ∧ g'.r15 = g.r15 ∧ g'.rsp = g.rsp) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [fbx] at hsz hfb hnx hns hpv hck f1 f2 f3 f4 f5 w ⊢
  mcx +contextual [W_164, W_190, W_218, W_240, o13, o14, o15, o16, hsz, hfb, hnx, hns, hb, hpv, hck, f1, f2, f3, f4,
    f5, w]

/-- `nextp` back from `[rsp]`, to 256. -/
theorem vc_252 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (f1 : ∀ i < 8, Foot F.data (Addr.add g.rsp i)) :
    W_252 fb F Wl (fun j' g' _ V' => j' = 256 ∧ V' = V ∧ g' = { g with rdx := rdq(V, g.rsp) }) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at f1 ⊢
  mcx +contextual [W_252, o17, f1]

set_option maxHeartbeats 2000000 in
/-- `nextchunk` the top chunk: `set_head (p, size | PREV_INUSE)`, `av->top = p`; to 156. -/
theorem vc_256t {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (htop : rdq(V, g.r15 + 96#64) = g.r12) (f1 : ∀ i < 8, Foot F.data (Addr.add (g.r15 + 96#64) i))
    (w1 : ∀ i < 8, Foot Wl (Addr.add (g.rbx + 8#64) i)) (w2 : ∀ i < 8, Foot Wl (Addr.add (g.r15 + 96#64) i)) :
    W_256 fb F Wl (fun j' g' _ V' => j' = 156 ∧
      V' = Vst (Vst V (g.rbx + 8#64) (toBytesLE ((g.rbp + g.r14) ||| 1#64) 8)) (g.r15 + 96#64) (toBytesLE g.rbx 8) ∧
      g' = { g with rbp := (g.rbp + g.r14) ||| 1#64 }) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at htop f1 w1 w2 ⊢
  mcx +contextual [W_256, W_80, W_266, W_288, o18, o19, htop, f1, w1, w2]
  all_goals assumption

set_option maxHeartbeats 2000000 in
/-- `nextchunk` not the top chunk and in use: to the `and` (92). -/
theorem vc_256i {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (hnt : ¬ rdq(V, g.r15 + 96#64) = g.r12) (f1 : ∀ i < 8, Foot F.data (Addr.add (g.r15 + 96#64) i))
    (hb : (ofBytesLE 8 ((byteAddrs (g.r12 + g.r14 + 8#64) 1).map V) &&& 1#8 == 0) = false)
    (f2 : ∀ i < 1, Foot F.data (Addr.add (g.r12 + g.r14 + 8#64) i)) :
    W_256 fb F Wl (fun j' g' _ V' => j' = 92 ∧ V' = V ∧ g' = g) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hnt f1 hb f2 ⊢
  mcx +contextual [W_256, W_80, W_266, W_288, o5, o18, o20, hnt, f1, hb, f2]

set_option maxHeartbeats 2000000 in
/-- `nextchunk` not the top chunk and free: `size` the sum, `[rsp] = nextp`, `rdi = nextchunk`; to the `call` of
`unlink_chunk` (298). -/
theorem vc_256f {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (hnt : ¬ rdq(V, g.r15 + 96#64) = g.r12) (f1 : ∀ i < 8, Foot F.data (Addr.add (g.r15 + 96#64) i))
    (hb : (ofBytesLE 8 ((byteAddrs (g.r12 + g.r14 + 8#64) 1).map V) &&& 1#8 == 0) = true)
    (f2 : ∀ i < 1, Foot F.data (Addr.add (g.r12 + g.r14 + 8#64) i)) (w : ∀ i < 8, Foot Wl (Addr.add g.rsp i)) :
    W_256 fb F Wl (fun j' g' _ V' => j' = 298 ∧ V' = Vst V g.rsp (toBytesLE g.rdx 8) ∧
      g' = { g with rdi := g.r12, rbp := g.rbp + g.r14 }) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hnt f1 hb f2 w ⊢
  mcx +contextual [W_256, W_80, W_266, W_288, o5, o18, o20, hnt, f1, hb, f2, w]

/-- `nextchunk` again (`p + size`), `nextp` back from `[rsp]`; to 98. -/
theorem vc_303 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (f1 : ∀ i < 8, Foot F.data (Addr.add g.rsp i)) :
    W_303 fb F Wl (fun j' g' _ V' => j' = 98 ∧ V' = V ∧
      g' = { g with r12 := g.rbx + g.rbp, rdx := rdq(V, g.rsp) }) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at f1 ⊢
  mcx +contextual [W_303, o21, f1]

set_option maxHeartbeats 2000000 in
/-- `first_unsorted = unsorted_bin->fd`, `unsorted_bin->fd = p`, `first_unsorted->bk = p`; a small chunk: to 127. -/
theorem vc_98s {fb fu : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} (hfu : rdq(V, g.r15 + 112#64) = fu)
    (hs : g.rbp.toNat ≤ 1023) (f1 : ∀ i < 8, Foot F.data (Addr.add (g.r15 + 112#64) i))
    (w1 : ∀ i < 8, Foot Wl (Addr.add (g.r15 + 112#64) i)) (w2 : ∀ i < 8, Foot Wl (Addr.add (fu + 24#64) i)) :
    W_98 fb F Wl (fun j' g' _ V' => j' = 127 ∧
      V' = Vst (Vst V (g.r15 + 112#64) (toBytesLE g.rbx 8)) (fu + 24#64) (toBytesLE g.rbx 8) ∧
      g' = { g with rax := fu }) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hfu hs f1 w1 w2 ⊢
  have hb := be_imm rbp 1023 (by decide)
  have hs' := eq_true hs
  mcx +contextual [W_98, o6, hb, hs', hfu, f1, w1, w2]

set_option maxHeartbeats 2000000 in
/-- As `vc_98s`, a large chunk: to the `pxor` (119). -/
theorem vc_98l {fb fu : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} (hfu : rdq(V, g.r15 + 112#64) = fu)
    (hs : ¬ g.rbp.toNat ≤ 1023) (f1 : ∀ i < 8, Foot F.data (Addr.add (g.r15 + 112#64) i))
    (w1 : ∀ i < 8, Foot Wl (Addr.add (g.r15 + 112#64) i)) (w2 : ∀ i < 8, Foot Wl (Addr.add (fu + 24#64) i)) :
    W_98 fb F Wl (fun j' g' _ V' => j' = 119 ∧
      V' = Vst (Vst V (g.r15 + 112#64) (toBytesLE g.rbx 8)) (fu + 24#64) (toBytesLE g.rbx 8) ∧
      g' = { g with rax := fu }) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hfu hs f1 w1 w2 ⊢
  have hb := be_imm rbp 1023 (by decide)
  have hs' := eq_false hs
  mcx +contextual [W_98, o6, hb, hs', hfu, f1, w1, w2]

/-- `rsi = size`, to the `movq` (130). -/
theorem vc_127 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} :
    W_127 fb F Wl (fun j' g' _ V' => j' = 130 ∧ V' = V ∧ g' = { g with rsi := g.rbp }) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  mcx +contextual [W_127, o7]

/-- `rsi = size | PREV_INUSE`, to the `movhps` (139). -/
theorem vc_135 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} :
    W_135 fb F Wl (fun j' g' _ V' => j' = 139 ∧ V' = V ∧ g' = { g with rsi := g.rsi ||| 1#64 }) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  mcx +contextual [W_135, o8]

/-- `set_head (p, size | PREV_INUSE)`, to the `movups` (148). -/
theorem vc_144 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (w : ∀ i < 8, Foot Wl (Addr.add (g.rbx + 8#64) i)) :
    W_144 fb F Wl (fun j' g' _ V' => j' = 148 ∧ V' = Vst V (g.rbx + 8#64) (toBytesLE g.rsi 8) ∧ g' = g) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at w ⊢
  mcx +contextual [W_144, o9, w]
  all_goals assumption

/-- `set_foot (p, size)`, to 156. -/
theorem vc_152 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (w : ∀ i < 8, Foot Wl (Addr.add g.r12 i)) :
    W_152 fb F Wl (fun j' g' _ V' => j' = 156 ∧ V' = Vst V g.r12 (toBytesLE g.rbp 8) ∧ g' = g) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at w ⊢
  mcx +contextual [W_152, o10, w]
  all_goals assumption

/-- `nextp` null: to 48. -/
theorem vc_156z {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} (hz : (g.rdx == 0) = true) :
    W_156 fb F Wl (fun j' g' _ V' => j' = 48 ∧ V' = V ∧ g' = g) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hz ⊢
  mcx +contextual [W_156, W_161, o11, o12, hz]

/-- `p = nextp`, to 164. -/
theorem vc_156n {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} (hz : (g.rdx == 0) = false) :
    W_156 fb F Wl (fun j' g' _ V' => j' = 164 ∧ V' = V ∧ g' = { g with rbx := g.rdx }) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hz ⊢
  mcx +contextual [W_156, W_161, o11, o12, hz]

end FV7z.Mcn
