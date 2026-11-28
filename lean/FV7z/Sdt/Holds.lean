import FV7z.Sdt.Cuts
import FV7z.Lemmas.LeafRet
import FV7z.Lemmas.FnFar
import FV7z.Lemmas.Fr40
import FV7z.Rst.Holds
/-!
# `CArchiveExtractCallback::SetDirsTimes` (PLAN.md §M, M1): the pieces

7-Zip 26.06's `HRESULT CArchiveExtractCallback::SetDirsTimes ()` at `0x5ad610` in `7zzs`
(`CPP/UI/Common/ArchiveExtractCallback.cpp`; `objdump -d`), `this` = `rdi` (`T`), `S` the entry's `rsp`. `_arc`
(`[T + 64]`) null returns 0 at 690 with no frame. Else (15) the six pushes (`Rst.V1`), `rbx` = `this`,
`sub rsp, 0x18` (`Rst.aR S`), the count `n` of `_extractedFolders` (`[T + 544]`) stored at `aR S + 12`: 0 to
508; else (50, by hand: `js` never taken, `n < 2^31`) `new` (69) of `8 n` bytes (`rbp` = the pairs `P`), the fill
(96–141: pair `i` = `{len (path i), i}`, `0x5ad550` at 123 writes the length), the heap sort (141–355, 528–696),
`SetDirTime` (`0x5ad590`, 388) of each folder in the sorted order (355–404), the items freed from the last
(404–485: `delete[]` of the path at 457, `operator delete` of the item at 470), `_size = 0` (485), `delete[] P`
(503), at 508 `add rsp, 0x18`, `eax` = 0, the pops and the `ret` (524).

- `Stk`, `V2`, `cnt`, `KC`: the stack, the bytes after the prologue, the count as read, a callee's contract.
- `vc_*`: the pieces' conditions; `tail508`: from 508 to the return address.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Sdt
set_option linter.unusedVariables false

open FV7z.Rst (aR e24 V1)
open FV7z.Wst (sa8)
open FV7z.Fr40 (Fr KS)

/-! ## The instructions outside the blocks -/

/-- `call new` (69), the fill's `0x5ad550` (123), `SetDirTime` (388), `delete[]` (457, 503), `delete` (470). -/
def pc1 : List Byte := [0xe8, 0x56, 0x53, 0x05, 0x00]
theorem pc1_0 : ∀ feat, Dec feat pc1 0 (FV7z.mk .call 64 [.rel 349014] 5) := by dec_rfl
theorem wc_69 : pc1 <+: sdt.drop 69 := by decide +kernel
theorem call_69 (feat : Features) : Dec feat sdt 69 (FV7z.mk .call 64 [.rel 349014] 5) :=
  Dec.shift (j := 69) (k := 0) (pc1_0 feat) wc_69 (Nat.zero_le _)
theorem tgt_69 : sdt_at.add (69 + 5) + BitVec.ofNat 64 349014 = 0x6029b0#64 := by decide

def pc2 : List Byte := [0xe8, 0xc0, 0xfe, 0xff, 0xff]
theorem pc2_0 : ∀ feat, Dec feat pc2 0 (FV7z.mk .call 64 [.rel 18446744073709551296] 5) := by dec_rfl
theorem wc_123 : pc2 <+: sdt.drop 123 := by decide +kernel
theorem call_123 (feat : Features) : Dec feat sdt 123 (FV7z.mk .call 64 [.rel 18446744073709551296] 5) :=
  Dec.shift (j := 123) (k := 0) (pc2_0 feat) wc_123 (Nat.zero_le _)
theorem tgt_123 : sdt_at.add (123 + 5) + BitVec.ofNat 64 18446744073709551296 = 0x5ad550#64 := by decide

def pc3 : List Byte := [0xe8, 0xf7, 0xfd, 0xff, 0xff]
theorem pc3_0 : ∀ feat, Dec feat pc3 0 (FV7z.mk .call 64 [.rel 18446744073709551095] 5) := by dec_rfl
theorem wc_388 : pc3 <+: sdt.drop 388 := by decide +kernel
theorem call_388 (feat : Features) : Dec feat sdt 388 (FV7z.mk .call 64 [.rel 18446744073709551095] 5) :=
  Dec.shift (j := 388) (k := 0) (pc3_0 feat) wc_388 (Nat.zero_le _)
theorem tgt_388 : sdt_at.add (388 + 5) + BitVec.ofNat 64 18446744073709551095 = 0x5ad590#64 := by decide

def pc4 : List Byte := [0xe8, 0x12, 0x3d, 0x05, 0x00]
theorem pc4_0 : ∀ feat, Dec feat pc4 0 (FV7z.mk .call 64 [.rel 343314] 5) := by dec_rfl
theorem wc_457 : pc4 <+: sdt.drop 457 := by decide +kernel
theorem call_457 (feat : Features) : Dec feat sdt 457 (FV7z.mk .call 64 [.rel 343314] 5) :=
  Dec.shift (j := 457) (k := 0) (pc4_0 feat) wc_457 (Nat.zero_le _)
theorem tgt_457 : sdt_at.add (457 + 5) + BitVec.ofNat 64 343314 = 0x6014f0#64 := by decide

def pc5 : List Byte := [0xe8, 0xf5, 0x3c, 0x05, 0x00]
theorem pc5_0 : ∀ feat, Dec feat pc5 0 (FV7z.mk .call 64 [.rel 343285] 5) := by dec_rfl
theorem wc_470 : pc5 <+: sdt.drop 470 := by decide +kernel
theorem call_470 (feat : Features) : Dec feat sdt 470 (FV7z.mk .call 64 [.rel 343285] 5) :=
  Dec.shift (j := 470) (k := 0) (pc5_0 feat) wc_470 (Nat.zero_le _)
theorem tgt_470 : sdt_at.add (470 + 5) + BitVec.ofNat 64 343285 = 0x6014e0#64 := by decide

def pc6 : List Byte := [0xe8, 0xe4, 0x3c, 0x05, 0x00]
theorem pc6_0 : ∀ feat, Dec feat pc6 0 (FV7z.mk .call 64 [.rel 343268] 5) := by dec_rfl
theorem wc_503 : pc6 <+: sdt.drop 503 := by decide +kernel
theorem call_503 (feat : Features) : Dec feat sdt 503 (FV7z.mk .call 64 [.rel 343268] 5) :=
  Dec.shift (j := 503) (k := 0) (pc6_0 feat) wc_503 (Nat.zero_le _)
theorem tgt_503 : sdt_at.add (503 + 5) + BitVec.ofNat 64 343268 = 0x6014f0#64 := by decide

/-- `js` at 50 (to `0x414756`, outside the function): never taken, the count below `2^31`. -/
def pjs : List Byte := [0x0f, 0x88, 0x0e, 0x71, 0xe6, 0xff]
theorem pjs_0 : ∀ feat, Dec feat pjs 0 (FV7z.mk (.jcc 8) 64 [.rel 18446744073707876622] 6) := by dec_rfl
theorem wj_50 : pjs <+: sdt.drop 50 := by decide +kernel
theorem js_50 (feat : Features) : Dec feat sdt 50 (FV7z.mk (.jcc 8) 64 [.rel 18446744073707876622] 6) :=
  Dec.shift (j := 50) (k := 0) (pjs_0 feat) wj_50 (Nat.zero_le _)

def pret : List Byte := [0xc3]
theorem pret_0 : ∀ feat, Dec feat pret 0 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem w_524 : pret <+: sdt.drop 524 := by decide +kernel
theorem ret_524 (feat : Features) : Dec feat sdt 524 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 524) (k := 0) (pret_0 feat) w_524 (Nat.zero_le _)
theorem w_690 : pret <+: sdt.drop 690 := by decide +kernel
theorem ret_690 (feat : Features) : Dec feat sdt 690 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 690) (k := 0) (pret_0 feat) w_690 (Nat.zero_le _)

/-! ## The frame and the bytes -/

/-- The stack: the saved `r15`, `r14`, `r13`, `r12`, `rbp`, `rbx`, the return address. -/
abbrev Stk (W : Addr → Byte) (S : Addr) (g0 : Gprs) (ra : Addr) : Prop :=
  rdq(W, S - 8) = g0.r15 ∧ rdq(W, S - 8 - 8) = g0.r14 ∧ rdq(W, S - 8 - 8 - 8) = g0.r13 ∧
    rdq(W, S - 8 - 8 - 8 - 8) = g0.r12 ∧ rdq(W, S - 8 - 8 - 8 - 8 - 8) = g0.rbp ∧
    rdq(W, S - 8 - 8 - 8 - 8 - 8 - 8) = g0.rbx ∧ rdq(W, S) = ra

/-- The count as the prologue reads it (after the pushes). -/
abbrev cnt (V : Addr → Byte) (g : Gprs) : BitVec 32 := rdd(V1 V g, g.rdi + 544#64)

/-- The bytes after the prologue: the pushes, the count at `aR S + 12`. -/
abbrev V2 (V : Addr → Byte) (g : Gprs) : Addr → Byte := Vst (V1 V g) (aR g.rsp + 12#64) (toBytesLE (cnt V g) 4)

/-! ## The pieces -/

/-- `wpx` with the flags' lemmas and the ops of the pieces here. -/
macro "sdx" "[" ls:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| wpx [not_true_eq_false, not_false_eq_true, Bool.not_true, Bool.not_false, Bool.false_eq_true,
    Bool.true_eq_false, false_implies, implies_true, ne_eq, Bool.not_eq_true', Bool.not_eq_false',
    decide_eq_true_eq, decide_eq_false_iff_not, decide_true, decide_false, BitVec.and_self, eq_self_iff_true,
    Bool.true_or, Bool.false_or, Bool.or_false, Bool.or_true, ↓reduceIte, BitVec.reduceSetWidth,
    BitVec.xor_self, BitVec.sub_self, BitVec.reduceSub, BitVec.reduceAdd, Op.cmpmi, Op.cmpmr, Op.shl64,
    Op.shr64, $ls,*])

/-- The closers after `refine h …`. -/
macro "sdc" : tactic =>
  `(tactic| first
    | with_reducible rfl
    | with_reducible assumption
    | exact toBytesLE_length _ _
    | exact trivial
    | apply And.intro
    | intro _
    | (simp only [rfz_sf, arith_sf, BitVec.and_self]; done))

variable {F : Footprint} {Wl : List Rgn}

/-- `cmp qword [rdi + 0x40], 0`: `_arc` null, `eax` = 0 and to the `ret` at 690. -/
theorem vc_0z {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (f64 : ∀ i < 8, Foot F.data (Addr.add (g.rdi + 64#64) i)) (hz : rdq(V, g.rdi + 64#64) = 0#64)
    (h : ∀ g', Fr g g' → ∀ fl, Q 690 g' fl V) :
    W_0 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [Fr] at f64 hz h ⊢
  sdx [W_0, W_688, o0, o48, hz]
  all_goals repeat' (first | refine h _ ?_ _ | sdc)

/-- `_arc` not null: the pushes, `rbx` = `this`, `sub rsp, 0x18`, the count at `rsp + 12`; 0 to 508. -/
theorem vc_0e {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (f64 : ∀ i < 8, Foot F.data (Addr.add (g.rdi + 64#64) i)) (hz : ¬ rdq(V, g.rdi + 64#64) = 0#64)
    (hs1 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8) i)) (hs2 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8) i))
    (hs3 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8 - 8) i))
    (hs4 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8 - 8 - 8) i))
    (hs5 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8 - 8 - 8 - 8) i))
    (hs6 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8 - 8 - 8 - 8 - 8) i))
    (f544 : ∀ i < 4, Foot F.data (Addr.add (g.rdi + 544#64) i))
    (w12 : ∀ i < 4, Foot Wl (Addr.add (aR g.rsp + 12#64) i)) (hc : cnt V g = 0)
    (h : ∀ g', g'.rsp = aR g.rsp → ∀ fl, Q 508 g' fl (V2 V g)) :
    W_0 F Wl Q g f V := by
  have t := beq_iff_eq.2 hc
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [cnt, V2, V1, aR] at f64 hz hs1 hs2 hs3 hs4 hs5 hs6 f544 w12 t h ⊢
  sdx [W_0, W_15, o0, o1, hz, t]
  all_goals repeat' (first | refine h _ ?_ _ | sdc)

/-- The count not 0: to the `js` at 50, `SF` its sign. -/
theorem vc_0n {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (f64 : ∀ i < 8, Foot F.data (Addr.add (g.rdi + 64#64) i)) (hz : ¬ rdq(V, g.rdi + 64#64) = 0#64)
    (hs1 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8) i)) (hs2 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8) i))
    (hs3 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8 - 8) i))
    (hs4 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8 - 8 - 8) i))
    (hs5 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8 - 8 - 8 - 8) i))
    (hs6 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8 - 8 - 8 - 8 - 8) i))
    (f544 : ∀ i < 4, Foot F.data (Addr.add (g.rdi + 544#64) i))
    (w12 : ∀ i < 4, Foot Wl (Addr.add (aR g.rsp + 12#64) i)) (hc : ¬ cnt V g = 0)
    (h : ∀ g', g'.rsp = aR g.rsp → g'.rbx = g.rdi → ∀ fl, fl.sf = (cnt V g).msb → Q 50 g' fl (V2 V g)) :
    W_0 F Wl Q g f V := by
  have t := beq_eq_false_iff_ne.2 hc
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [cnt, V2, V1, aR] at f64 hz hs1 hs2 hs3 hs4 hs5 hs6 f544 w12 t h ⊢
  sdx [W_0, W_15, o0, o1, hz, t]
  all_goals repeat' (first | refine h _ ?_ ?_ _ ?_ | sdc)

/-- `r13d` = the count from `rsp + 12`, `rdi` = `8 r13`, to the `call` of `new` (69). -/
theorem vc_56 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (f12 : ∀ i < 4, Foot F.data (Addr.add (g.rsp + 12#64) i))
    (h : ∀ g', g'.rsp = g.rsp → g'.rbx = g.rbx → g'.r13 = BitVec.setWidth 64 rdd(V, g.rsp + 12#64) →
      g'.rdi = BitVec.setWidth 64 rdd(V, g.rsp + 12#64) * 8#64 → ∀ fl, Q 69 g' fl V) :
    W_56 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at f12 h ⊢
  sdx [W_56, o2]
  all_goals repeat' (first | refine h _ ?_ ?_ ?_ ?_ _ | sdc)

/-- `rbp` = the pairs (`rax`), the count from `this`: 0 to 141. -/
theorem vc_74z {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (f544 : ∀ i < 4, Foot F.data (Addr.add (g.rbx + 544#64) i)) (hc : rdd(V, g.rbx + 544#64) = 0)
    (h : ∀ g', g'.rsp = g.rsp → g'.rbx = g.rbx → g'.rbp = g.rax → g'.r13 = g.r13 → ∀ fl, Q 141 g' fl V) :
    W_74 F Wl Q g f V := by
  have t := beq_iff_eq.2 hc
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at f544 t h ⊢
  sdx [W_74, W_87, o3, o4, t]
  all_goals repeat' (first | refine h _ ?_ ?_ ?_ ?_ _ | sdc)

/-- The count not 0: `r12d` = 0, to the fill (96). -/
theorem vc_74n {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (f544 : ∀ i < 4, Foot F.data (Addr.add (g.rbx + 544#64) i)) (hc : ¬ rdd(V, g.rbx + 544#64) = 0)
    (h : ∀ g', g'.rsp = g.rsp → g'.rbx = g.rbx → g'.rbp = g.rax → g'.r13 = g.r13 → g'.r12 = 0#64 →
      ∀ fl, Q 96 g' fl V) :
    W_74 F Wl Q g f V := by
  have t := beq_eq_false_iff_ne.2 hc
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at f544 t h ⊢
  sdx [W_74, W_87, o3, o4, t]
  all_goals repeat' (first | refine h _ ?_ ?_ ?_ ?_ ?_ _ | sdc)

/-- The fill: the item `i` (`r12d`), `rdi` = the pair `i`, its index stored, `rsi` = the item's path; to the
`call` at 123. -/
theorem vc_96 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (f536 : ∀ i < 8, Foot F.data (Addr.add (g.rbx + 536#64) i))
    (fit : ∀ i < 8, Foot F.data
      (Addr.add (rdq(V, g.rbx + 536#64) + BitVec.setWidth 64 (BitVec.setWidth 32 g.r12) * 8#64) i))
    (w4 : ∀ i < 4, Foot Wl (Addr.add (g.rbp + BitVec.setWidth 64 (BitVec.setWidth 32 g.r12) * 8#64 + 4#64) i))
    (f56 : ∀ i < 8, Foot F.data (Addr.add
      (rdq(V, rdq(V, g.rbx + 536#64) + BitVec.setWidth 64 (BitVec.setWidth 32 g.r12) * 8#64) + 56#64) i))
    (h : ∀ g', g'.rsp = g.rsp → g'.rbx = g.rbx → g'.rbp = g.rbp → g'.r12 = g.r12 → g'.r13 = g.r13 →
      g'.rdi = g.rbp + BitVec.setWidth 64 (BitVec.setWidth 32 g.r12) * 8#64 →
      g'.rsi = rdq(Vst V (g.rbp + BitVec.setWidth 64 (BitVec.setWidth 32 g.r12) * 8#64 + 4#64)
        (toBytesLE (BitVec.setWidth 32 g.r12) 4),
        rdq(V, rdq(V, g.rbx + 536#64) + BitVec.setWidth 64 (BitVec.setWidth 32 g.r12) * 8#64) + 56#64) →
      ∀ fl, Q 123 g' fl (Vst V (g.rbp + BitVec.setWidth 64 (BitVec.setWidth 32 g.r12) * 8#64 + 4#64)
        (toBytesLE (BitVec.setWidth 32 g.r12) 4))) :
    W_96 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at f536 fit w4 f56 h ⊢
  sdx [W_96, o5]
  all_goals repeat' (first | refine h _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ _ | sdc)

/-- `r12d += 1`; below the count: back to 96. -/
theorem vc_128c {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (f544 : ∀ i < 4, Foot F.data (Addr.add (g.rbx + 544#64) i))
    (hlt : (BitVec.setWidth 32 g.r12 + 1#32).toNat < rdd(V, g.rbx + 544#64).toNat)
    (h : ∀ g', g'.rsp = g.rsp → g'.rbx = g.rbx → g'.rbp = g.rbp → g'.r13 = g.r13 →
      g'.r12 = BitVec.setWidth 64 (BitVec.setWidth 32 g.r12 + 1#32) → ∀ fl, Q 96 g' fl V) :
    W_128 F Wl Q g f V := by
  have t1 : (rdd(V, g.rbx + 544#64).toNat < (BitVec.setWidth 32 g.r12 + 1#32).toNat) = False :=
    eq_false (by omega)
  have t2 : (rdd(V, g.rbx + 544#64) = BitVec.setWidth 32 g.r12 + 1#32) = False :=
    eq_false (fun e => by rw [e] at hlt; omega)
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at f544 t1 t2 h ⊢
  sdx [W_128, o6, t1, t2]
  all_goals repeat' (first | refine h _ ?_ ?_ ?_ ?_ ?_ _ | sdc)

/-- `r12d += 1`; the count reached: to 141. -/
theorem vc_128e {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (f544 : ∀ i < 4, Foot F.data (Addr.add (g.rbx + 544#64) i))
    (he : rdd(V, g.rbx + 544#64) = BitVec.setWidth 32 g.r12 + 1#32)
    (h : ∀ g', g'.rsp = g.rsp → g'.rbx = g.rbx → g'.rbp = g.rbp → g'.r13 = g.r13 → ∀ fl, Q 141 g' fl V) :
    W_128 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at f544 he h ⊢
  sdx [W_128, o6, he]
  all_goals repeat' (first | refine h _ ?_ ?_ ?_ ?_ _ | sdc)

/-- One folder: `rdi` = the item at the index `rcx`, `rsi` = its path, to the `call` of `SetDirTime` (388). -/
theorem vc_373 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (f536 : ∀ i < 8, Foot F.data (Addr.add (g.rbx + 536#64) i))
    (fit : ∀ i < 8, Foot F.data (Addr.add (rdq(V, g.rbx + 536#64) + g.rcx * 8#64) i))
    (f56 : ∀ i < 8, Foot F.data (Addr.add (rdq(V, rdq(V, g.rbx + 536#64) + g.rcx * 8#64) + 56#64) i))
    (h : ∀ g', g'.rsp = g.rsp → g'.rbx = g.rbx → g'.rbp = g.rbp → g'.r12 = g.r12 →
      g'.rdi = rdq(V, rdq(V, g.rbx + 536#64) + g.rcx * 8#64) →
      g'.rsi = rdq(V, rdq(V, rdq(V, g.rbx + 536#64) + g.rcx * 8#64) + 56#64) → ∀ fl, Q 388 g' fl V) :
    W_373 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at f536 fit f56 h ⊢
  sdx [W_373, o25]
  all_goals repeat' (first | refine h _ ?_ ?_ ?_ ?_ ?_ ?_ _ | sdc)

/-- `r12 += 1`; below the count at `rsp + 12`: `ecx` = the next index, to 373. -/
theorem vc_393c {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (f12 : ∀ i < 4, Foot F.data (Addr.add (g.rsp + 12#64) i))
    (fx : ∀ i < 4, Foot F.data (Addr.add (g.rbp + (g.r12 + 1#64) * 8#64 + 4#64) i))
    (hlt : (BitVec.setWidth 32 (g.r12 + 1#64)).toNat < rdd(V, g.rsp + 12#64).toNat)
    (h : ∀ g', g'.rsp = g.rsp → g'.rbx = g.rbx → g'.rbp = g.rbp → g'.r12 = g.r12 + 1#64 →
      g'.rcx = BitVec.setWidth 64 rdd(V, g.rbp + (g.r12 + 1#64) * 8#64 + 4#64) → ∀ fl, Q 373 g' fl V) :
    W_393 F Wl Q g f V := by
  have t1 : (rdd(V, g.rsp + 12#64).toNat < (BitVec.setWidth 32 (g.r12 + 1#64)).toNat) = False :=
    eq_false (by omega)
  have t2 : (rdd(V, g.rsp + 12#64) = BitVec.setWidth 32 (g.r12 + 1#64)) = False :=
    eq_false (fun e => by rw [e] at hlt; omega)
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at f12 fx t1 t2 h ⊢
  sdx [W_393, W_368, o26, o24, t1, t2]
  all_goals repeat' (first | refine h _ ?_ ?_ ?_ ?_ ?_ _ | sdc)

/-- The last folder done, the count from `this` 0: to 500. -/
theorem vc_393z {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (f12 : ∀ i < 4, Foot F.data (Addr.add (g.rsp + 12#64) i))
    (he : rdd(V, g.rsp + 12#64) = BitVec.setWidth 32 (g.r12 + 1#64))
    (f544 : ∀ i < 4, Foot F.data (Addr.add (g.rbx + 544#64) i)) (hc : rdd(V, g.rbx + 544#64) = 0)
    (h : ∀ g', g'.rsp = g.rsp → g'.rbx = g.rbx → g'.rbp = g.rbp → ∀ fl, Q 500 g' fl V) :
    W_393 F Wl Q g f V := by
  have t := beq_iff_eq.2 hc
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at f12 he f544 t h ⊢
  sdx [W_393, W_368, W_404, W_414, o26, o24, o27, o28, he, t]
  all_goals repeat' (first | refine h _ ?_ ?_ ?_ _ | sdc)

/-- The last folder done, the count `c` not 0: `r12` = `8 (c - 1)`, to the frees (432). -/
theorem vc_393n {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (f12 : ∀ i < 4, Foot F.data (Addr.add (g.rsp + 12#64) i))
    (he : rdd(V, g.rsp + 12#64) = BitVec.setWidth 32 (g.r12 + 1#64))
    (f544 : ∀ i < 4, Foot F.data (Addr.add (g.rbx + 544#64) i)) (hc : ¬ rdd(V, g.rbx + 544#64) = 0)
    (h : ∀ g', g'.rsp = g.rsp → g'.rbx = g.rbx → g'.rbp = g.rbp →
      g'.r12 = BitVec.setWidth 64 (BitVec.setWidth 32
        (BitVec.setWidth 64 rdd(V, g.rbx + 544#64) + 18446744073709551615#64)) <<< (3 : Nat) →
      ∀ fl, Q 432 g' fl V) :
    W_393 F Wl Q g f V := by
  have t := beq_eq_false_iff_ne.2 hc
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at f12 he f544 t h ⊢
  sdx [W_393, W_368, W_404, W_414, o26, o24, o27, o28, he, t]
  all_goals repeat' (first | refine h _ ?_ ?_ ?_ ?_ _ | sdc)

/-- The item at `r12` (bytes) null: to 475. -/
theorem vc_432z {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (f536 : ∀ i < 8, Foot F.data (Addr.add (g.rbx + 536#64) i))
    (fit : ∀ i < 8, Foot F.data (Addr.add (rdq(V, g.rbx + 536#64) + g.r12) i))
    (hz : rdq(V, rdq(V, g.rbx + 536#64) + g.r12) = 0)
    (h : ∀ g', g'.rsp = g.rsp → g'.rbx = g.rbx → g'.rbp = g.rbp → g'.r12 = g.r12 → ∀ fl, Q 475 g' fl V) :
    W_432 F Wl Q g f V := by
  have t := beq_iff_eq.2 hz
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at f536 fit t h ⊢
  sdx [W_432, W_448, o29, o30, t]
  all_goals repeat' (first | refine h _ ?_ ?_ ?_ ?_ _ | sdc)

/-- The item not null, its path null: `r13` = the item, to 462. -/
theorem vc_432a {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (f536 : ∀ i < 8, Foot F.data (Addr.add (g.rbx + 536#64) i))
    (fit : ∀ i < 8, Foot F.data (Addr.add (rdq(V, g.rbx + 536#64) + g.r12) i))
    (hz : ¬ rdq(V, rdq(V, g.rbx + 536#64) + g.r12) = 0)
    (f56 : ∀ i < 8, Foot F.data (Addr.add (rdq(V, rdq(V, g.rbx + 536#64) + g.r12) + 56#64) i))
    (hp : rdq(V, rdq(V, rdq(V, g.rbx + 536#64) + g.r12) + 56#64) = 0)
    (h : ∀ g', g'.rsp = g.rsp → g'.rbx = g.rbx → g'.rbp = g.rbp → g'.r12 = g.r12 →
      g'.r13 = rdq(V, rdq(V, g.rbx + 536#64) + g.r12) → ∀ fl, Q 462 g' fl V) :
    W_432 F Wl Q g f V := by
  have t := beq_eq_false_iff_ne.2 hz
  have t' := beq_iff_eq.2 hp
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at f536 fit f56 t t' h ⊢
  sdx [W_432, W_448, o29, o30, t, t']
  all_goals repeat' (first | refine h _ ?_ ?_ ?_ ?_ ?_ _ | sdc)

/-- The item and its path not null: `rdi` = the path, to the `call` of `delete[]` (457). -/
theorem vc_432b {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (f536 : ∀ i < 8, Foot F.data (Addr.add (g.rbx + 536#64) i))
    (fit : ∀ i < 8, Foot F.data (Addr.add (rdq(V, g.rbx + 536#64) + g.r12) i))
    (hz : ¬ rdq(V, rdq(V, g.rbx + 536#64) + g.r12) = 0)
    (f56 : ∀ i < 8, Foot F.data (Addr.add (rdq(V, rdq(V, g.rbx + 536#64) + g.r12) + 56#64) i))
    (hp : ¬ rdq(V, rdq(V, rdq(V, g.rbx + 536#64) + g.r12) + 56#64) = 0)
    (h : ∀ g', g'.rsp = g.rsp → g'.rbx = g.rbx → g'.rbp = g.rbp → g'.r12 = g.r12 →
      g'.r13 = rdq(V, rdq(V, g.rbx + 536#64) + g.r12) →
      g'.rdi = rdq(V, rdq(V, rdq(V, g.rbx + 536#64) + g.r12) + 56#64) → ∀ fl, Q 457 g' fl V) :
    W_432 F Wl Q g f V := by
  have t := beq_eq_false_iff_ne.2 hz
  have t' := beq_eq_false_iff_ne.2 hp
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at f536 fit f56 t t' h ⊢
  sdx [W_432, W_448, o29, o30, t, t']
  all_goals repeat' (first | refine h _ ?_ ?_ ?_ ?_ ?_ ?_ _ | sdc)

/-- `esi` = 72, `rdi` = the item, to the `call` of `operator delete` (470). -/
theorem vc_462 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (h : ∀ g', g'.rsp = g.rsp → g'.rbx = g.rbx → g'.rbp = g.rbp → g'.r12 = g.r12 → g'.rdi = g.r13 →
      g'.rsi = 72#64 → ∀ fl, Q 470 g' fl V) :
    W_462 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h ⊢
  sdx [W_462, o31]
  all_goals repeat' (first | refine h _ ?_ ?_ ?_ ?_ ?_ ?_ _ | sdc)

/-- `r12 -= 8`; not past the first item: back to 432. -/
theorem vc_475c {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (hn : ¬ g.r12 - 8#64 = 18446744073709551608#64)
    (h : ∀ g', g'.rsp = g.rsp → g'.rbx = g.rbx → g'.rbp = g.rbp → g'.r12 = g.r12 - 8#64 → ∀ fl, Q 432 g' fl V) :
    W_475 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hn h ⊢
  sdx [W_475, o32, hn]
  all_goals repeat' (first | refine h _ ?_ ?_ ?_ ?_ _ | sdc)

/-- Past the first item: `_size = 0`; the pairs null, to 508. -/
theorem vc_475z {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (he : g.r12 - 8#64 = 18446744073709551608#64) (w544 : ∀ i < 4, Foot Wl (Addr.add (g.rbx + 544#64) i))
    (hp : g.rbp = 0)
    (h : ∀ g', g'.rsp = g.rsp → ∀ fl, Q 508 g' fl (Vst V (g.rbx + 544#64) (toBytesLE 0#32 4))) :
    W_475 F Wl Q g f V := by
  have t := beq_iff_eq.2 hp
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at he w544 t h ⊢
  sdx [W_475, W_485, o32, o33, he, t]
  all_goals repeat' (first | refine h _ ?_ _ | sdc)

/-- Past the first item: `_size = 0`; the pairs not null, to 500. -/
theorem vc_475p {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (he : g.r12 - 8#64 = 18446744073709551608#64) (w544 : ∀ i < 4, Foot Wl (Addr.add (g.rbx + 544#64) i))
    (hp : ¬ g.rbp = 0)
    (h : ∀ g', g'.rsp = g.rsp → g'.rbp = g.rbp → ∀ fl, Q 500 g' fl (Vst V (g.rbx + 544#64) (toBytesLE 0#32 4))) :
    W_475 F Wl Q g f V := by
  have t := beq_eq_false_iff_ne.2 hp
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at he w544 t h ⊢
  sdx [W_475, W_485, o32, o33, he, t]
  all_goals repeat' (first | refine h _ ?_ ?_ _ | sdc)

/-- `rdi` = the pairs, to the `call` of `delete[]` (503). -/
theorem vc_500 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (h : ∀ g', g'.rsp = g.rsp → g'.rdi = g.rbp → ∀ fl, Q 503 g' fl V) :
    W_500 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h ⊢
  sdx [W_500, o34]
  all_goals repeat' (first | refine h _ ?_ ?_ _ | sdc)

/-- `add rsp, 0x18`, `eax` = 0, the six pops, to the `ret` (524). -/
theorem vc_508 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (p1 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 24#64) i))
    (p2 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 24#64 + 8) i))
    (p3 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 24#64 + 8 + 8) i))
    (p4 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 24#64 + 8 + 8 + 8) i))
    (p5 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 24#64 + 8 + 8 + 8 + 8) i))
    (p6 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 24#64 + 8 + 8 + 8 + 8 + 8) i))
    (h : ∀ g', g'.rsp = g.rsp + 24#64 + 8 + 8 + 8 + 8 + 8 + 8 → g'.rbx = rdq(V, g.rsp + 24#64) →
      g'.rbp = rdq(V, g.rsp + 24#64 + 8) → g'.r12 = rdq(V, g.rsp + 24#64 + 8 + 8) →
      g'.r13 = rdq(V, g.rsp + 24#64 + 8 + 8 + 8) → g'.r14 = rdq(V, g.rsp + 24#64 + 8 + 8 + 8 + 8) →
      g'.r15 = rdq(V, g.rsp + 24#64 + 8 + 8 + 8 + 8 + 8) → ∀ fl, Q 524 g' fl V) :
    W_508 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at p1 p2 p3 p4 p5 p6 h ⊢
  sdx [W_508, o35]
  all_goals repeat' (first | refine h _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ _ | sdc)

/-! ## The runs -/

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {X : State} {t : Nat} {V : Addr → Byte} {e₂ : Addr} {code₂ : List Byte} {j₂ : Nat}

/-- A callee at `tg` from a `call` returning to `sdt_at + r` (registers `G` there, bytes `W`): at its entry, and
from its return with the registers `Fr` keeps and its post `P` on the registers and the bytes, the run goes on to
the goal. -/
def KC (prof : Profile) (F : Footprint) (Wl : List Rgn) (L : List (Addr × List Byte)) (s₀ : State) (o : Oracle)
    (gev : List Event) (gP : State → Nat → List Event → Prop) (gE : Outcome → List Event → Prop)
    (tg : Addr) (r : Nat) (G : Gprs) (W : Addr → Byte) (P : Gprs → (Addr → Byte) → Prop) : Prop :=
  ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y →
    Agree F Y.proc.mm.mem (Vst W (G.rsp - 8) (toBytesLE (sdt_at.add r) 8)) →
    Y.cpu.rip = tg → Y.cpu.gpr = G.set 4 (G.rsp - 8) →
    (∀ (Z : State) (W' : Addr → Byte) (t'' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem W' →
      Z.cpu.rip = sdt_at.add r → Fr G Z.cpu.gpr → P Z.cpu.gpr W' → GoG prof L o gev gP gE Z t'') →
    GoG prof L o gev gP gE Y t'

/-- From 508 (`rsp` = `aR S`, the stack `Stk`) to the return address `e₂.add j₂`. -/
theorem tail508 {W : Addr → Byte} {S : Addr} {g0 : Gprs} {Y : State} (c : Seg prof F Wl L s₀ o)
    (hin : CodeIn L sdt_at sdt) (hK : KeptW Wl s₀ Y) (hA : Agree F Y.proc.mm.mem W)
    (hr : Y.cpu.rip = sdt_at.add 508) (hs : Y.cpu.gpr.rsp = aR S) (hst : Stk W S g0 (e₂.add j₂))
    (g1 : ∀ i < 8, Foot F.data (Addr.add (S - 8) i)) (g2 : ∀ i < 8, Foot F.data (Addr.add (S - 8 - 8) i))
    (g3 : ∀ i < 8, Foot F.data (Addr.add (S - 8 - 8 - 8) i))
    (g4 : ∀ i < 8, Foot F.data (Addr.add (S - 8 - 8 - 8 - 8) i))
    (g5 : ∀ i < 8, Foot F.data (Addr.add (S - 8 - 8 - 8 - 8 - 8) i))
    (g6 : ∀ i < 8, Foot F.data (Addr.add (S - 8 - 8 - 8 - 8 - 8 - 8) i))
    (hl : ∀ i < 8, Foot F.data (Addr.add S i)) (hin₂ : CodeIn L e₂ code₂) (h₂ : j₂ < code₂.length)
    (k : ∀ (Z' : State) (t' : Nat), KeptW Wl s₀ Z' → Agree F Z'.proc.mm.mem W → Z'.cpu.rip = e₂.add j₂ →
      Z'.cpu.gpr.rsp = S + 8 → KS g0 Z'.cpu.gpr → GoG prof L o gev gP gE Z' t') :
    GoG prof L o gev gP gE Y t := by
  obtain ⟨s1, s2, s3, s4, s5, s6, s7⟩ := hst
  have q1 : Y.cpu.gpr.rsp + 24#64 = S - 8 - 8 - 8 - 8 - 8 - 8 := by rw [hs, e24]
  have q2 : Y.cpu.gpr.rsp + 24#64 + 8 = S - 8 - 8 - 8 - 8 - 8 := by rw [q1, sa8]
  have q3 : Y.cpu.gpr.rsp + 24#64 + 8 + 8 = S - 8 - 8 - 8 - 8 := by rw [q2, sa8]
  have q4 : Y.cpu.gpr.rsp + 24#64 + 8 + 8 + 8 = S - 8 - 8 - 8 := by rw [q3, sa8]
  have q5 : Y.cpu.gpr.rsp + 24#64 + 8 + 8 + 8 + 8 = S - 8 - 8 := by rw [q4, sa8]
  have q6 : Y.cpu.gpr.rsp + 24#64 + 8 + 8 + 8 + 8 + 8 = S - 8 := by rw [q5, sa8]
  have q7 : Y.cpu.gpr.rsp + 24#64 + 8 + 8 + 8 + 8 + 8 + 8 = S := by rw [q6, sa8]
  refine (c_508 prof).run c hin (fun j' g' _ V' => j' = 524 ∧ V' = W ∧ g'.rsp = S ∧
      g'.rbx = g0.rbx ∧ g'.rbp = g0.rbp ∧ g'.r12 = g0.r12 ∧ g'.r13 = g0.r13 ∧ g'.r14 = g0.r14 ∧
      g'.r15 = g0.r15) hK hA hr
    (vc_508 (by rw [q1]; exact g6) (by rw [q2]; exact g5) (by rw [q3]; exact g4)
      (by rw [q4]; exact g3) (by rw [q5]; exact g2) (by rw [q6]; exact g1)
      fun _ a1 a2 a3 a4 a5 a6 a7 _ => ⟨rfl, rfl, a1.trans q7, a2.trans (by rw [q1]; exact s6),
        a3.trans (by rw [q2]; exact s5), a4.trans (by rw [q3]; exact s4), a5.trans (by rw [q4]; exact s3),
        a6.trans (by rw [q5]; exact s2), a7.trans (by rw [q6]; exact s1)⟩) ?_
  rintro j' g fl V₁ ⟨rfl, hV₁, gs, gb, gp, g12, g13, g14, g15⟩ U t₁ hKU hAU hrU hgU -
  subst V₁ hgU
  refine c.s_ret hKU hAU hin (lt_len (by decide)) hrU (ret_524 _) (by rw [gs]; exact hl) hin₂ h₂
    (by rw [gs]; exact s7) ?_
  rintro Z' t₂ hKZ' hAZ' ⟨hrZ', hgZ'⟩
  refine k Z' t₂ hKZ' hAZ' hrZ' ?_ ?_
  · rw [hgZ']
    show U.cpu.gpr.rsp + 8 = _
    rw [gs]
  · rw [hgZ']
    exact ⟨gb, gp, g12, g13, g14, g15⟩

end FV7z.Sdt
