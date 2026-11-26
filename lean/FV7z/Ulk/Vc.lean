import FV7z.Ulk.Steps
import FV7z.Lemmas.CmpImm
/-!
# `unlink_chunk`: the straight pieces (PLAN.md §M, M1)

The pieces of `unlink_chunk (av, p)` (glibc 2.31, at `0x62ea20`, `av` dropped: `rdi = p`) when the checks hold: the
size word `sz` at `p + 8`, `fd` at `p + 16`, `bk` at `p + 24`; `ulk1`: the bytes after `fd->bk = bk`, `bk->fd = fd`.

- `vc_0s`: a small chunk (`sz` at most 0x3ff) or no `fd_nextsize`: to the epilogue (106).
- `vc_0a`: a large chunk in the `nextsize` list, `fd->fd_nextsize` set: `p` taken out of that list, to 106.
- `vc_0b`, `vc_0c`: `fd->fd_nextsize` null: `p` alone in the list (`p->fd_nextsize = p`), to the `movq` at 176;
  else to the `movq` at 117.
- `vc_135`: after the store of `fd`'s `nextsize` links, the two links to `fd`, to 106; `vc_189`: the `jmp` to 106.
- `vc_106`: the frame given back, to the `ret` (110).
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Ulk

/-- The extra lemmas of the pieces' `wp`. -/
macro "ulkx" cfg:Lean.Parser.Tactic.optConfig "[" ls:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| wpx $cfg [Op.cmpmi, BitVec.and_self, BitVec.reduceAdd, BitVec.reduceAnd, BitVec.reduceBEq,
      BitVec.reduceEq, BitVec.reduceToNat, BitVec.reduceSub, decide_false, decide_true, Bool.or_false,
      Bool.false_or, Bool.not_false, Bool.not_true, Bool.false_eq_true, false_imp_iff, true_imp_iff, false_implies,
      true_implies, and_true, true_and, reduceIte, ne_eq, not_false_eq_true, ofBytesLE_toBytesLE,
      Bool.true_eq_false, BitVec.add_zero, decide_eq_true_eq, implies_true, forall_const, eq_self_iff_true,
      beq_self_eq_true, Kp, ulk1, $ls,*])

/-- The bytes after `fd->bk = bk`, `bk->fd = fd`. -/
abbrev ulk1 (V : Addr → Byte) (fd bk : Addr) : Addr → Byte :=
  Vst (Vst V (fd + 24#64) (toBytesLE bk 8)) (bk + 16#64) (toBytesLE fd 8)

variable {F : Footprint} {Wl : List Rgn}

/-- What the pieces from the entry keep. -/
abbrev Kp (g g' : Gprs) : Prop :=
  g'.rdi = g.rdi ∧ g'.rbx = g.rbx ∧ g'.rbp = g.rbp ∧ g'.r12 = g.r12 ∧ g'.r13 = g.r13 ∧ g'.r14 = g.r14 ∧
    g'.r15 = g.r15

set_option maxHeartbeats 4000000 in
/-- A small chunk or no `fd_nextsize`: `p` out of its bin, to 106. -/
theorem vc_0s {fb sz fd bk : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (hsz : rdq(V, g.rdi + 8#64) = sz)
    (hc1 : rdq(V, g.rdi + (sz &&& 18446744073709551608#64)) = sz &&& 18446744073709551608#64)
    (hfd : rdq(V, g.rdi + 16#64) = fd) (hbk : rdq(V, g.rdi + 24#64) = bk)
    (hc2 : rdq(V, fd + 24#64) = g.rdi) (hc3 : rdq(V, bk + 16#64) = g.rdi)
    (hsm : sz.toNat ≤ 1023 ∨ rdq(ulk1 V fd bk, g.rdi + 32#64) = 0#64)
    (f1 : ∀ i < 8, Foot F.data (Addr.add (g.rdi + 8#64) i))
    (f2 : ∀ i < 8, Foot F.data (Addr.add (g.rdi + (sz &&& 18446744073709551608#64)) i))
    (f3 : ∀ i < 8, Foot F.data (Addr.add (g.rdi + 16#64) i)) (f4 : ∀ i < 8, Foot F.data (Addr.add (g.rdi + 24#64) i))
    (f5 : ∀ i < 8, Foot F.data (Addr.add (fd + 24#64) i)) (f6 : ∀ i < 8, Foot F.data (Addr.add (bk + 16#64) i))
    (w1 : ∀ i < 8, Foot Wl (Addr.add (fd + 24#64) i)) (w2 : ∀ i < 8, Foot Wl (Addr.add (bk + 16#64) i))
    (f7 : 1023 < sz.toNat → ∀ i < 8, Foot F.data (Addr.add (g.rdi + 32#64) i)) :
    W_0 fb F Wl (fun j' g' _ V' => j' = 106 ∧ V' = ulk1 V fd bk ∧ g'.rsp = g.rsp - 8#64 ∧ Kp g g') g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hsz hc1 hfd hbk hc2 hc3 hsm f1 f2 f3 f4 f5 f6 f7 ⊢
  have hb := be_imm sz 1023 (by decide)
  by_cases hs : sz.toNat ≤ 1023
  · have hs' := eq_true hs
    ulkx +contextual [W_0, W_25, W_39, W_45, o0, o1, o2, o3, hb, hs', hsz, hc1, hfd, hbk, hc2, hc3, f1, f2, f3, f4,
      f5, f6, w1, w2]
  · have hs' := eq_false hs
    have h0 := hsm.resolve_left hs
    have f7' := f7 (by omega)
    ulkx +contextual [W_0, W_25, W_39, W_45, W_62, o0, o1, o2, o3, o4, hb, hs', h0, hsz, hc1, hfd, hbk, hc2, hc3,
      f1, f2, f3, f4, f5, f6, w1, w2, f7']

/-- The checks and reads of a large chunk in the `nextsize` list, after `ulk1`. -/
structure Lg (F : Footprint) (V : Addr → Byte) (p fd bk fdn bkn : Addr) : Prop where
  fdn : rdq(ulk1 V fd bk, p + 32#64) = fdn
  fdn0 : (fdn == 0#64) = false
  c4 : rdq(ulk1 V fd bk, fdn + 40#64) = p
  bkn : rdq(ulk1 V fd bk, p + 40#64) = bkn
  c5 : rdq(ulk1 V fd bk, bkn + 32#64) = p
  g1 : ∀ i < 8, Foot F.data (Addr.add (p + 32#64) i)
  g2 : ∀ i < 8, Foot F.data (Addr.add (fdn + 40#64) i)
  g3 : ∀ i < 8, Foot F.data (Addr.add (p + 40#64) i)
  g4 : ∀ i < 8, Foot F.data (Addr.add (bkn + 32#64) i)
  g5 : ∀ i < 8, Foot F.data (Addr.add (fd + 32#64) i)

set_option maxHeartbeats 4000000 in
/-- A large chunk, `fd->fd_nextsize` set: `p` out of the `nextsize` list too, to 106. -/
theorem vc_0a {fb sz fd bk fdn bkn q : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (hsz : rdq(V, g.rdi + 8#64) = sz)
    (hc1 : rdq(V, g.rdi + (sz &&& 18446744073709551608#64)) = sz &&& 18446744073709551608#64)
    (hfd : rdq(V, g.rdi + 16#64) = fd) (hbk : rdq(V, g.rdi + 24#64) = bk)
    (hc2 : rdq(V, fd + 24#64) = g.rdi) (hc3 : rdq(V, bk + 16#64) = g.rdi) (hlg : 1023 < sz.toNat)
    (hL : Lg F V g.rdi fd bk fdn bkn) (hff : rdq(ulk1 V fd bk, fd + 32#64) ≠ 0#64)
    (hq : rdq(Vst (ulk1 V fd bk) (fdn + 40#64) (toBytesLE bkn 8), g.rdi + 40#64) = q)
    (f1 : ∀ i < 8, Foot F.data (Addr.add (g.rdi + 8#64) i))
    (f2 : ∀ i < 8, Foot F.data (Addr.add (g.rdi + (sz &&& 18446744073709551608#64)) i))
    (f3 : ∀ i < 8, Foot F.data (Addr.add (g.rdi + 16#64) i)) (f4 : ∀ i < 8, Foot F.data (Addr.add (g.rdi + 24#64) i))
    (f5 : ∀ i < 8, Foot F.data (Addr.add (fd + 24#64) i)) (f6 : ∀ i < 8, Foot F.data (Addr.add (bk + 16#64) i))
    (w1 : ∀ i < 8, Foot Wl (Addr.add (fd + 24#64) i)) (w2 : ∀ i < 8, Foot Wl (Addr.add (bk + 16#64) i))
    (w3 : ∀ i < 8, Foot Wl (Addr.add (fdn + 40#64) i)) (w4 : ∀ i < 8, Foot Wl (Addr.add (q + 32#64) i)) :
    W_0 fb F Wl (fun j' g' _ V' => j' = 106 ∧
      V' = Vst (Vst (ulk1 V fd bk) (fdn + 40#64) (toBytesLE bkn 8)) (q + 32#64) (toBytesLE fdn 8) ∧
      g'.rsp = g.rsp - 8#64 ∧ Kp g g') g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  obtain ⟨l1, l2, l3, l4, l5, g1, g2, g3, g4, g5⟩ := hL
  dsimp only at hsz hc1 hfd hbk hc2 hc3 hlg hq l1 l3 l4 l5 g1 g3 f1 f2 f3 f4 f5 f6 ⊢
  have hb := be_imm sz 1023 (by decide)
  have hs' := eq_false (show ¬ sz.toNat ≤ 1023 by omega)
  have hff' := eq_false hff
  ulkx +contextual [W_0, W_25, W_39, W_45, W_62, W_71, W_77, W_87, W_94, o0, o1, o2, o3, o4, o5, o6, o7, o8, hb,
    hs', hsz, hc1, hfd, hbk, hc2, hc3, l1, l2, l3, l4, l5, hff', hq, f1, f2, f3, f4, f5, f6, g1, g2, g3, g4, g5, w1,
    w2, w3, w4]

set_option maxHeartbeats 4000000 in
/-- A large chunk, `fd->fd_nextsize` null, `p->fd_nextsize = p`: to the `movq` at 176, `rax = fd`. -/
theorem vc_0b {fb sz fd bk fdn bkn : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (hsz : rdq(V, g.rdi + 8#64) = sz)
    (hc1 : rdq(V, g.rdi + (sz &&& 18446744073709551608#64)) = sz &&& 18446744073709551608#64)
    (hfd : rdq(V, g.rdi + 16#64) = fd) (hbk : rdq(V, g.rdi + 24#64) = bk)
    (hc2 : rdq(V, fd + 24#64) = g.rdi) (hc3 : rdq(V, bk + 16#64) = g.rdi) (hlg : 1023 < sz.toNat)
    (hL : Lg F V g.rdi fd bk fdn bkn) (hff : rdq(ulk1 V fd bk, fd + 32#64) = 0#64) (hpe : g.rdi = fdn)
    (f1 : ∀ i < 8, Foot F.data (Addr.add (g.rdi + 8#64) i))
    (f2 : ∀ i < 8, Foot F.data (Addr.add (g.rdi + (sz &&& 18446744073709551608#64)) i))
    (f3 : ∀ i < 8, Foot F.data (Addr.add (g.rdi + 16#64) i)) (f4 : ∀ i < 8, Foot F.data (Addr.add (g.rdi + 24#64) i))
    (f5 : ∀ i < 8, Foot F.data (Addr.add (fd + 24#64) i)) (f6 : ∀ i < 8, Foot F.data (Addr.add (bk + 16#64) i))
    (w1 : ∀ i < 8, Foot Wl (Addr.add (fd + 24#64) i)) (w2 : ∀ i < 8, Foot Wl (Addr.add (bk + 16#64) i)) :
    W_0 fb F Wl (fun j' g' _ V' => j' = 176 ∧ V' = ulk1 V fd bk ∧ g'.rax = fd ∧ g'.rsp = g.rsp - 8#64 ∧ Kp g g')
      g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  obtain ⟨l1, l2, l3, l4, l5, g1, g2, g3, g4, g5⟩ := hL
  dsimp only at hsz hc1 hfd hbk hc2 hc3 hlg hpe l1 l3 l4 l5 g1 g3 f1 f2 f3 f4 f5 f6 ⊢
  have hb := be_imm sz 1023 (by decide)
  have hs' := eq_false (show ¬ sz.toNat ≤ 1023 by omega)
  have hpe' := eq_true hpe
  ulkx +contextual [W_0, W_25, W_39, W_45, W_62, W_71, W_77, W_87, W_112, o0, o1, o2, o3, o4, o5, o6, o7, o10, hb,
    hs', hsz, hc1, hfd, hbk, hc2, hc3, l1, l2, l3, l4, l5, hff, hpe', f1, f2, f3, f4, f5, f6, g1, g2, g3, g4, g5,
    w1, w2]

set_option maxHeartbeats 4000000 in
/-- A large chunk, `fd->fd_nextsize` null, `p->fd_nextsize ≠ p`: to the `movq` at 117, `rax = fd`,
`rdx = fdn`, `rcx = bkn`. -/
theorem vc_0c {fb sz fd bk fdn bkn : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (hsz : rdq(V, g.rdi + 8#64) = sz)
    (hc1 : rdq(V, g.rdi + (sz &&& 18446744073709551608#64)) = sz &&& 18446744073709551608#64)
    (hfd : rdq(V, g.rdi + 16#64) = fd) (hbk : rdq(V, g.rdi + 24#64) = bk)
    (hc2 : rdq(V, fd + 24#64) = g.rdi) (hc3 : rdq(V, bk + 16#64) = g.rdi) (hlg : 1023 < sz.toNat)
    (hL : Lg F V g.rdi fd bk fdn bkn) (hff : rdq(ulk1 V fd bk, fd + 32#64) = 0#64) (hpe : g.rdi ≠ fdn)
    (f1 : ∀ i < 8, Foot F.data (Addr.add (g.rdi + 8#64) i))
    (f2 : ∀ i < 8, Foot F.data (Addr.add (g.rdi + (sz &&& 18446744073709551608#64)) i))
    (f3 : ∀ i < 8, Foot F.data (Addr.add (g.rdi + 16#64) i)) (f4 : ∀ i < 8, Foot F.data (Addr.add (g.rdi + 24#64) i))
    (f5 : ∀ i < 8, Foot F.data (Addr.add (fd + 24#64) i)) (f6 : ∀ i < 8, Foot F.data (Addr.add (bk + 16#64) i))
    (w1 : ∀ i < 8, Foot Wl (Addr.add (fd + 24#64) i)) (w2 : ∀ i < 8, Foot Wl (Addr.add (bk + 16#64) i)) :
    W_0 fb F Wl (fun j' g' _ V' => j' = 117 ∧ V' = ulk1 V fd bk ∧ g'.rax = fd ∧ g'.rdx = fdn ∧ g'.rcx = bkn ∧
      g'.rsp = g.rsp - 8#64 ∧ Kp g g') g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  obtain ⟨l1, l2, l3, l4, l5, g1, g2, g3, g4, g5⟩ := hL
  dsimp only at hsz hc1 hfd hbk hc2 hc3 hlg hpe l1 l3 l4 l5 g1 g3 f1 f2 f3 f4 f5 f6 ⊢
  have hb := be_imm sz 1023 (by decide)
  have hs' := eq_false (show ¬ sz.toNat ≤ 1023 by omega)
  have hpe' := eq_false hpe
  ulkx +contextual [W_0, W_25, W_39, W_45, W_62, W_71, W_77, W_87, W_112, o0, o1, o2, o3, o4, o5, o6, o7, o10, hb,
    hs', hsz, hc1, hfd, hbk, hc2, hc3, l1, l2, l3, l4, l5, hff, hpe', f1, f2, f3, f4, f5, f6, g1, g2, g3, g4, g5,
    w1, w2]

/-- After the store of `fd`'s `nextsize` links (`rax = fd`, `rdi = p`): `p->fd_nextsize->bk_nextsize = fd`,
`p->bk_nextsize->fd_nextsize = fd`, to 106. -/
theorem vc_135 {fb a b : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} (ha : rdq(V, g.rdi + 32#64) = a)
    (hb : rdq(Vst V (a + 40#64) (toBytesLE g.rax 8), g.rdi + 40#64) = b)
    (f1 : ∀ i < 8, Foot F.data (Addr.add (g.rdi + 32#64) i)) (f2 : ∀ i < 8, Foot F.data (Addr.add (g.rdi + 40#64) i))
    (w1 : ∀ i < 8, Foot Wl (Addr.add (a + 40#64) i)) (w2 : ∀ i < 8, Foot Wl (Addr.add (b + 32#64) i)) :
    W_135 fb F Wl (fun j' g' _ V' => j' = 106 ∧
      V' = Vst (Vst V (a + 40#64) (toBytesLE g.rax 8)) (b + 32#64) (toBytesLE g.rax 8) ∧ g' = { g with rdx := b })
      g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at ha hb f1 f2 ⊢
  ulkx +contextual [W_135, o11, ha, hb, f1, f2, w1, w2]

/-- The `jmp` at 189 to 106. -/
theorem vc_189 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} :
    W_189 fb F Wl (fun j' g' _ V' => j' = 106 ∧ V' = V ∧ g' = g) g f V := by
  unfold W_189
  exact ⟨rfl, rfl, rfl⟩

/-- The frame given back, to the `ret` (110). -/
theorem vc_106 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} :
    W_106 fb F Wl (fun j' g' _ V' => j' = 110 ∧ V' = V ∧ g' = { g with rsp := g.rsp + 8#64 }) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  ulkx [W_106, o9]

end FV7z.Ulk
