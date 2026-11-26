import FV7z.Stm.Steps
import FV7z.Cal.Vc
/-!
# `systrim`: the straight pieces (PLAN.md §M, M1)

The pieces of glibc 2.31's `systrim (pad, &main_arena)` (`systrim.isra.0.constprop.0`, at `0x62f8e0`, `rdi = pad`):
`top_size` (`ts`) the top chunk's size (`main_arena.top` at `0x792aa0`), `ps` the page size (at `0x7933d8`),
`extra = ALIGN_DOWN (ts - MINSIZE - 1 - pad, ps)` (`stmE`).

- `vc_0`: the three pushes, `ts` to `rbx`; to 75 (`return 0`: `top_area ≤ pad` or `extra` 0) or to the `call` of
  `MORECORE (0)` (51), `r12 = extra`, `rdi = 0`.
- `vc_57`: the break `current_brk` back in `rax`; to 75 when it is not the top chunk's end, else to the `call` of
  `MORECORE (-extra)` (94).
- `vc_75`: `eax = 0`, to 77; `vc_77`: the three pops, to the `ret` (81).
- `vc_100`: `__after_morecore_hook` null, to 112; `vc_112`: `rdi = 0`, to the `call` of `MORECORE (0)` (114).
- `vc_120`: the new break back in `rax`: to 75 when it is null or `released = current_brk - new_brk` is 0, else to
  the `sub` of `main_arena.system_mem` (141), `rbx = ts - released`, `rax` the top chunk.
- `vc_148`: `set_head (top, (ts - released) | PREV_INUSE)`, `eax = 1`, to 77.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
open FV7z.Tun (rd_Vst rd_Vst_self)
namespace FV7z.Stm

/-- The extra lemmas of the pieces' `wp`. -/
macro "stx" cfg:Lean.Parser.Tactic.optConfig "[" ls:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| wpx $cfg [Op.lda, BitVec.and_self,
      BitVec.reduceAdd, BitVec.reduceAnd, BitVec.reduceSetWidth, BitVec.reduceBEq, BitVec.reduceBNe, BitVec.reduceEq,
      BitVec.reduceToNat, BitVec.reduceSub, BitVec.reduceOr, BitVec.reduceXOr, BitVec.reduceNot, BitVec.setWidth_zero,
      BitVec.or_zero, BitVec.and_zero, BitVec.zero_and, BitVec.zero_or,
      Nat.reduceAdd, Nat.reduceSub, Nat.reduceLeDiff, Nat.reduceLT, decide_false, decide_true, Bool.or_false,
      Bool.false_or, Bool.not_false, Bool.not_true, Bool.false_eq_true, false_imp_iff, true_imp_iff, Bool.or_self,
      Bool.true_or, Bool.or_true, false_implies, true_implies, and_true, true_and, reduceIte, or_true, true_or,
      or_false, false_or, ne_eq, Nat.reduceEqDiff, not_false_eq_true, ofBytesLE_toBytesLE, Bool.true_eq_false,
      BitVec.xor_self, BitVec.add_zero, decide_eq_true_eq, implies_true, forall_const, $ls,*])

/-- `extra`, as the code computes it: `(ts - 33 - pad) & -ps`. -/
abbrev stmE (ts pad ps : Addr) : Addr := (0 - ps) &&& (ts + 18446744073709551583#64 - pad)

/-- The three pushes under `S`. -/
abbrev fr3 (V : Addr → Byte) (S : Addr) (a b c : BitVec 64) : Addr → Byte :=
  Vst (Vst (Vst V (S - 8) (toBytesLE a 8)) (S - 8 - 8) (toBytesLE b 8)) (S - 8 - 8 - 8) (toBytesLE c 8)

/-- Bytes outside the 24 under `S` read through the three pushes. -/
theorem fr3_rd (V : Addr → Byte) (S : Addr) (a b c : BitVec 64) {x : Addr} {n : Nat} (hS : 32 ≤ S.toNat)
    (hx : x.toNat + n ≤ 2 ^ 64) (h : x.toNat + n ≤ S.toNat - 24 ∨ S.toNat ≤ x.toNat) :
    List.map (Vst (Vst (Vst V (S - 8) (toBytesLE a 8)) (S - 8 - 8) (toBytesLE b 8)) (S - 8 - 8 - 8)
      (toBytesLE c 8)) (byteAddrs x n) = List.map V (byteAddrs x n) := by
  have hl := S.isLt
  obtain ⟨e1, e2, e3, -⟩ := Cal.fr_e hS
  rw [rd_Vst _ _ _ _ _ (by rw [toBytesLE_length, e3]; omega) hx (by rw [toBytesLE_length, e3]; omega),
    rd_Vst _ _ _ _ _ (by rw [toBytesLE_length, e2]; omega) hx (by rw [toBytesLE_length, e2]; omega),
    rd_Vst _ _ _ _ _ (by rw [toBytesLE_length, e1]; omega) hx (by rw [toBytesLE_length, e1]; omega)]

variable {F : Footprint} {Wl : List Rgn}

set_option maxHeartbeats 4000000 in
/-- From the entry: to 75, or to the `call` of `MORECORE (0)` (51) with `extra` not 0. -/
theorem vc_0 {fb T Z ps : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} (hS : 32 ≤ g.rsp.toNat)
    (hT : rdq(V, 7940768#64) = T) (hZ : rdq(V, T + 8#64) = Z) (hps : rdq(V, 7943128#64) = ps)
    (d1 : 7943136 ≤ g.rsp.toNat - 24) (d2 : (T + 8#64).toNat + 8 ≤ g.rsp.toNat - 24)
    (h1 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8) i)) (h2 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8) i))
    (h3 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8 - 8) i))
    (f1 : ∀ i < 8, Foot F.data (Addr.add 7940768#64 i)) (f2 : ∀ i < 8, Foot F.data (Addr.add (T + 8#64) i))
    (f3 : ∀ i < 8, Foot F.data (Addr.add 7943128#64 i)) :
    W_0 fb F Wl (fun j' g' _ V' => V' = fr3 V g.rsp g.r12 g.rbp g.rbx ∧ g'.rsp = g.rsp - 8 - 8 - 8 ∧
      g'.rbx = Z &&& 18446744073709551608#64 ∧ g'.r13 = g.r13 ∧ g'.r14 = g.r14 ∧ g'.r15 = g.r15 ∧
      (j' = 75 ∨ (j' = 51 ∧ g'.rdi = 0#64 ∧ g'.r12 = stmE (Z &&& 18446744073709551608#64) g.rdi ps ∧
        (stmE (Z &&& 18446744073709551608#64) g.rdi ps == 0) = false))) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hS d1 d2 h1 h2 h3 ⊢
  have k2 := fr3_rd V rsp r12 rbp rbx (x := T + 8#64) (n := 8) hS (by omega) (.inl d2)
  have k3 := fr3_rd V rsp r12 rbp rbx (x := 7943128#64) (n := 8) hS (by simp only [BitVec.toNat_ofNat]; omega)
    (.inl (by simp only [BitVec.toNat_ofNat]; omega))
  stx +contextual [W_0, W_28, W_49, o0, o1, o2, fr3, k2, k3, hT, hZ, hps, h1, h2, h3, f1, f2, f3]

set_option maxHeartbeats 2000000 in
/-- From `MORECORE (0)`'s return (57): to 75, or, the break the top chunk's end, to the `call` of
`MORECORE (-extra)` (94). -/
theorem vc_57 {fb T : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} (hT : rdq(V, 7940768#64) = T)
    (f1 : ∀ i < 8, Foot F.data (Addr.add 7940768#64 i)) :
    W_57 fb F Wl (fun j' g' _ V' => V' = V ∧ g'.rsp = g.rsp ∧ g'.rbx = g.rbx ∧ g'.r12 = g.r12 ∧ g'.r13 = g.r13 ∧
      g'.r14 = g.r14 ∧ g'.r15 = g.r15 ∧
      (j' = 75 ∨ (j' = 94 ∧ g.rax = T + g.rbx ∧ g'.rbp = g.rax ∧ g'.rdi = 0 - g.r12))) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  stx +contextual [W_57, W_88, o3, o6, hT, f1]

/-- `eax = 0`, to 77. -/
theorem vc_75 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} :
    W_75 fb F Wl (fun j' g' _ V' => j' = 77 ∧ V' = V ∧ g' = { g with rax := 0#64 }) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  stx [W_75, o4]

/-- The three pops, to the `ret` (81). -/
theorem vc_77 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (p0 : ∀ i < 8, Foot F.data (Addr.add g.rsp i)) (p1 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8) i))
    (p2 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8 + 8) i)) :
    W_77 fb F Wl (fun j' g' _ V' => j' = 81 ∧ V' = V ∧ g'.rsp = g.rsp + 8 + 8 + 8 ∧ g'.rax = g.rax ∧
      g'.rbx = rdq(V, g.rsp) ∧ g'.rbp = rdq(V, g.rsp + 8) ∧ g'.r12 = rdq(V, g.rsp + 8 + 8) ∧ g'.r13 = g.r13 ∧
      g'.r14 = g.r14 ∧ g'.r15 = g.r15) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at p0 p1 p2 ⊢
  stx +contextual [W_77, o5, p0, p1, p2]

/-- `__after_morecore_hook` null: to 112. -/
theorem vc_100 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} (hhk : rdq(V, 8013152#64) = 0#64)
    (f1 : ∀ i < 8, Foot F.data (Addr.add 8013152#64 i)) :
    W_100 fb F Wl (fun j' g' _ V' => j' = 112 ∧ V' = V ∧ g' = { g with rax := 0#64 }) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  stx [W_100, o7, hhk, f1]
  all_goals assumption

/-- `rdi = 0`, to the `call` of `MORECORE (0)` (114). -/
theorem vc_112 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} :
    W_112 fb F Wl (fun j' g' _ V' => j' = 114 ∧ V' = V ∧ g' = { g with rdi := 0#64 }) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  stx [W_112, o2]

set_option maxHeartbeats 2000000 in
/-- From `MORECORE (0)`'s return (120): to 75, or, the new break not null and `released` not 0, to the `sub` of
`main_arena.system_mem` (141). -/
theorem vc_120 {fb T : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} (hT : rdq(V, 7940768#64) = T)
    (f1 : ∀ i < 8, Foot F.data (Addr.add 7940768#64 i)) :
    W_120 fb F Wl (fun j' g' _ V' => V' = V ∧ g'.rsp = g.rsp ∧ g'.r13 = g.r13 ∧ g'.r14 = g.r14 ∧ g'.r15 = g.r15 ∧
      (j' = 75 ∨ (j' = 141 ∧ ¬ g.rbp = g.rax ∧ g'.rbp = g.rbp - g.rax ∧ g'.rax = T ∧
        g'.rbx = g.rbx - (g.rbp - g.rax) ∧ g'.r12 = g.r12))) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  stx +contextual [W_120, W_126, W_131, o8, o9, o10, decide_eq_false_iff_not, hT, f1]

/-- `set_head (top, rbx | PREV_INUSE)`, `eax = 1`, to 77. -/
theorem vc_148 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (w : ∀ i < 8, Foot Wl (Addr.add (g.rax + 8#64) i)) :
    W_148 fb F Wl (fun j' g' _ V' => j' = 77 ∧ V' = Vst V (g.rax + 8#64) (toBytesLE (g.rbx ||| 1#64) 8) ∧
      g' = { g with rax := 1#64, rbx := g.rbx ||| 1#64 }) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at w ⊢
  stx [W_148, o11, w]
  all_goals assumption

end FV7z.Stm
