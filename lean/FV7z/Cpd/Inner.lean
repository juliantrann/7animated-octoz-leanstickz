import FV7z.Cpd.Defs
/-!
# `NCommandLineParser::CParser::~CParser`, from 48 to 170 (PLAN.md §M, M1)

7-Zip 26.06's `CParser::~CParser (this)` at `0x5a0500` in `7zzs` (`CPP/Common/CommandLineParser.cpp`; `objdump -d`):
`delete [] _switches`, `_switches` = `b` an array of `N` `CSwitchResult`s of 24 bytes (`N` the 8 bytes at `b - 8`,
the item `i` at `ip b i`), each with `PostStrings` a `CObjectVector<UString>` (`_items` the 8 bytes at `ip b i + 8`,
its size the 4 bytes at `ip b i + 16`). For `i` = `N - 1` down to 0 (the loop from 48, `rbx` = `ip b (i + 1)`, `r13`
its copy): the size `n` read; for `k` = `n - 1` down to 0 (the loop from 80, `rbp` = `8k`) `p` = `_items[k]`, when
not 0 its chars freed when not 0 (`call 0x6014f0` at 97), then `p` (`operator delete (p, 16)` at 110) and `rdi` =
`_items` again (115); at 129 `_items` freed when not 0 (134); at 139 the loop goes on while `rbx` is not `b`. At 157
`operator delete [] (b - 8, 24 N + 8)` (`call 0x601500` at 165), then 170 (`FV7z/Cpd/Tail.lean`).

The callees are hypotheses on the bytes they are given and leave, as in `FV7z/Cpd/Tail.lean`: `O i` once the items
from `i` on are done (`O N` at the start, `O 0` before 157), `H i k` before the step `k` of the item `i` is done
(`H i n` once its size is read, `H i 0` at 129), `J i k p` between the two frees of that step.

- `ip b i`: the item `i` (`FV7z/Cpd/Items.lean`).
- `vc_*`: the verification conditions of the pieces; `from157` and `from48` in `FV7z/Cpd/Loop.lean`.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
open FV7z.Ocv (rbx0 rbx0_eq rb_step rb_ne rb_last)
namespace FV7z.Cpd

/-! ## The instructions outside the blocks -/

/-- The `call` of `operator delete [] (q)` at 97. -/
def qc97 : List Byte := [0xe8, 0x8a, 0x0f, 0x06, 0x00]
theorem qc97_0 : ∀ feat, Dec feat qc97 0 (FV7z.mk .call 64 [.rel 397194] 5) := by dec_rfl
theorem wc_97 : qc97 <+: cpd.drop 97 := by decide +kernel
theorem call_97 (feat : Features) : Dec feat cpd 97 (FV7z.mk .call 64 [.rel 397194] 5) :=
  Dec.shift (j := 97) (k := 0) (qc97_0 feat) wc_97 (Nat.zero_le _)
theorem tgt_97 : cpd_at.add (97 + 5) + BitVec.ofNat 64 397194 = 0x6014f0#64 := by decide

/-- The `call` of `operator delete (s, 16)` at 110. -/
def qc110 : List Byte := [0xe8, 0x6d, 0x0f, 0x06, 0x00]
theorem qc110_0 : ∀ feat, Dec feat qc110 0 (FV7z.mk .call 64 [.rel 397165] 5) := by dec_rfl
theorem wc_110 : qc110 <+: cpd.drop 110 := by decide +kernel
theorem call_110 (feat : Features) : Dec feat cpd 110 (FV7z.mk .call 64 [.rel 397165] 5) :=
  Dec.shift (j := 110) (k := 0) (qc110_0 feat) wc_110 (Nat.zero_le _)
theorem tgt_110 : cpd_at.add (110 + 5) + BitVec.ofNat 64 397165 = 0x6014e0#64 := by decide

/-- The `call` of `operator delete [] (items)` at 134. -/
def qc134 : List Byte := [0xe8, 0x65, 0x0f, 0x06, 0x00]
theorem qc134_0 : ∀ feat, Dec feat qc134 0 (FV7z.mk .call 64 [.rel 397157] 5) := by dec_rfl
theorem wc_134 : qc134 <+: cpd.drop 134 := by decide +kernel
theorem call_134 (feat : Features) : Dec feat cpd 134 (FV7z.mk .call 64 [.rel 397157] 5) :=
  Dec.shift (j := 134) (k := 0) (qc134_0 feat) wc_134 (Nat.zero_le _)
theorem tgt_134 : cpd_at.add (134 + 5) + BitVec.ofNat 64 397157 = 0x6014f0#64 := by decide

/-- The `call` of `operator delete [] (a, size)` at 165. -/
def qc165 : List Byte := [0xe8, 0x56, 0x0f, 0x06, 0x00]
theorem qc165_0 : ∀ feat, Dec feat qc165 0 (FV7z.mk .call 64 [.rel 397142] 5) := by dec_rfl
theorem wc_165 : qc165 <+: cpd.drop 165 := by decide +kernel
theorem call_165 (feat : Features) : Dec feat cpd 165 (FV7z.mk .call 64 [.rel 397142] 5) :=
  Dec.shift (j := 165) (k := 0) (qc165_0 feat) wc_165 (Nat.zero_le _)
theorem tgt_165 : cpd_at.add (165 + 5) + BitVec.ofNat 64 397142 = 0x601500#64 := by decide


/-- The closer of the pieces' conditions. -/
local macro "ocl" : tactic => `(tactic| (all_goals repeat'
    first
    | exact rfl
    | assumption
    | exact trivial
    | (intro h; exact absurd h (by decide))
    | (apply Or.inl; repeat' (first | exact rfl | assumption | apply And.intro); done)
    | (apply Or.inr; repeat' (first | exact rfl | assumption | apply And.intro); done)
    | apply And.intro
    | intro _))

variable {F : Footprint} {Wl : List Rgn}

/-! ## The pieces -/

section
variable {g : Gprs} {f : Rflags} {V : Addr → Byte}

/-- 48 with the item's size 0: `r13` = `rbx`, `rbx` -= 24, `rdi` = the item's `_items`; to 129. -/
theorem vc_48z {n32 : BitVec 32} {it : BitVec 64}
    (hn : rdd(V, g.rbx + 18446744073709551608#64) = n32) (hn0 : n32 = 0) (hit : rdq(V, g.rbx - 24#64 + 8#64) = it)
    (fn : ∀ i < 4, Foot F.data (Addr.add (g.rbx + 18446744073709551608#64) i))
    (fa : ∀ i < 8, Foot F.data (Addr.add (g.rbx - 24#64 + 8#64) i)) :
    W_48 F Wl (fun j' g' _ V' => j' = 129 ∧ g'.rsp = g.rsp ∧ g'.r12 = g.r12 ∧ g'.r15 = g.r15 ∧
      g'.rbx = g.rbx - 24#64 ∧ g'.r13 = g.rbx ∧ g'.rdi = it ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hn hit fn fa ⊢
  have e : (n32 == 0) = true := beq_iff_eq.2 hn0
  wpx [W_48, W_296, o2, o7, hn, hit, e, BitVec.and_self, Bool.false_eq_true, Bool.true_eq_false,
    false_implies, eq_self_iff_true, true_implies, implies_true]
  ocl

/-- 48 with the item's size `n32` not 0: to 80 with `rbp` = `rbx0 n32`. -/
theorem vc_48n {n32 : BitVec 32} {it : BitVec 64}
    (hn : rdd(V, g.rbx + 18446744073709551608#64) = n32) (hn0 : n32 ≠ 0) (hit : rdq(V, g.rbx - 24#64 + 8#64) = it)
    (fn : ∀ i < 4, Foot F.data (Addr.add (g.rbx + 18446744073709551608#64) i))
    (fa : ∀ i < 8, Foot F.data (Addr.add (g.rbx - 24#64 + 8#64) i)) :
    W_48 F Wl (fun j' g' _ V' => j' = 80 ∧ g'.rsp = g.rsp ∧ g'.r12 = g.r12 ∧ g'.r15 = g.r15 ∧
      g'.rbx = g.rbx - 24#64 ∧ g'.r13 = g.rbx ∧ g'.rdi = it ∧ g'.rbp = rbx0 n32 ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hn hit fn fa ⊢
  have e : (n32 == 0) = false := beq_eq_false_iff_ne.2 hn0
  wpx [W_48, W_66, o2, o3, Op.shl64, hn, hit, e, BitVec.and_self, Bool.false_eq_true, Bool.true_eq_false,
    false_implies, eq_self_iff_true, true_implies, implies_true]
  ocl

/-- 80 with `_items[k]` 0: to 119. -/
theorem vc_80z {p : BitVec 64} (hp : rdq(V, g.rdi + g.rbp) = p)
    (fp : ∀ i < 8, Foot F.data (Addr.add (g.rdi + g.rbp) i)) (hp0 : p = 0) :
    W_80 F Wl (fun j' g' _ V' => j' = 119 ∧ g' = { g with r14 := p } ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hp fp ⊢
  have e : (p == 0) = true := beq_iff_eq.2 hp0
  wpx [W_80, W_89, o4, o5, hp, e, BitVec.and_self, Bool.false_eq_true, Bool.true_eq_false, false_implies,
    eq_self_iff_true, true_implies, implies_true]
  ocl

/-- 80 with `_items[k]` = `p` not 0: `rdi` = `q` = `p->_chars`; to 102 when it is 0, else to the `call` at 97. -/
theorem vc_80n {p q : BitVec 64} (hp : rdq(V, g.rdi + g.rbp) = p)
    (fp : ∀ i < 8, Foot F.data (Addr.add (g.rdi + g.rbp) i)) (hp0 : p ≠ 0) (hq : rdq(V, p) = q)
    (fq : ∀ i < 8, Foot F.data (Addr.add p i)) :
    W_80 F Wl (fun j' g' _ V' => (q = 0 ∧ j' = 102 ∨ q ≠ 0 ∧ j' = 97) ∧ g' = { g with r14 := p, rdi := q } ∧
      V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hp fp ⊢
  have e : (p == 0) = false := beq_eq_false_iff_ne.2 hp0
  wpx [W_80, W_89, o4, o5, hp, hq, e, BitVec.and_self, beq_iff_eq, beq_eq_false_iff_ne, Bool.false_eq_true,
    Bool.true_eq_false, false_implies, eq_self_iff_true, true_implies, implies_true]
  ocl

/-- 102: `rdi` = `r14`, `esi` = 16; to the `call` at 110. -/
theorem vc_102 :
    W_102 F Wl (fun j' g' _ V' => j' = 110 ∧ g' = { g with rdi := g.r14, rsi := 16#64 } ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_102, o6, BitVec.reduceSetWidth]
  ocl

/-- 115: `rdi` = the item's `_items` again; to 119. -/
theorem vc_115 {it : BitVec 64} (hit : rdq(V, g.rbx + 8#64) = it)
    (fa : ∀ i < 8, Foot F.data (Addr.add (g.rbx + 8#64) i)) :
    W_115 F Wl (fun j' g' _ V' => j' = 119 ∧ g' = { g with rdi := it } ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hit fa ⊢
  wpx [W_115, o7, hit]
  ocl

/-- 119, the last step: `rbp` -= 8 gives `-8`; to 129. -/
theorem vc_119l (h : g.rbp - 8#64 = 18446744073709551608#64) :
    W_119 F Wl (fun j' g' _ V' => j' = 129 ∧ g' = { g with rbp := g.rbp - 8#64 } ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h ⊢
  have e := decide_eq_true h
  wpx [W_119, o8, e, Bool.not_true, Bool.not_false, Bool.false_eq_true, Bool.true_eq_false, false_implies,
    eq_self_iff_true, true_implies, implies_true]
  ocl

/-- 119, not the last step: back to 80. -/
theorem vc_119c (h : g.rbp - 8#64 ≠ 18446744073709551608#64) :
    W_119 F Wl (fun j' g' _ V' => j' = 80 ∧ g' = { g with rbp := g.rbp - 8#64 } ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h ⊢
  have e := decide_eq_false h
  wpx [W_119, o8, e, Bool.not_true, Bool.not_false, Bool.false_eq_true, Bool.true_eq_false, false_implies,
    eq_self_iff_true, true_implies, implies_true]
  ocl

/-- 129 with `rdi` 0: to 139. -/
theorem vc_129z (hz : g.rdi = 0) : W_129 F Wl (fun j' g' _ V' => j' = 139 ∧ g' = g ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hz ⊢
  have e : (rdi == 0) = true := beq_iff_eq.2 hz
  wpx [W_129, o9, e, BitVec.and_self, Bool.false_eq_true, Bool.true_eq_false, false_implies,
    eq_self_iff_true, true_implies, implies_true]
  ocl

/-- 129 with `rdi` not 0: to the `call` at 134. -/
theorem vc_129n (hz : g.rdi ≠ 0) : W_129 F Wl (fun j' g' _ V' => j' = 134 ∧ g' = g ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hz ⊢
  have e : (rdi == 0) = false := beq_eq_false_iff_ne.2 hz
  wpx [W_129, o9, e, BitVec.and_self, Bool.false_eq_true, Bool.true_eq_false, false_implies,
    eq_self_iff_true, true_implies, implies_true]
  ocl

/-- 139 with `rbx` not `b` (the 8 bytes at `this`): back to 48. -/
theorem vc_139c {b : BitVec 64} (hb : rdq(V, g.r12) = b) (hne : b ≠ g.rbx)
    (fb : ∀ i < 8, Foot F.data (Addr.add g.r12 i)) :
    W_139 F Wl (fun j' g' _ V' => j' = 48 ∧ g' = g ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hb hne fb ⊢
  have e := decide_eq_false hne
  wpx [W_139, W_145, o10, o11, Op.cmpmr, Op.shl64, hb, e, Bool.not_true, Bool.not_false, Bool.false_eq_true,
    Bool.true_eq_false, false_implies, eq_self_iff_true, true_implies, implies_true]
  ocl

/-- 139 with `rbx` = `b`: `rax` = the 8 bytes at `r13 - 32`, `rsi` = `24 rax`; to 157. -/
theorem vc_139e {b : BitVec 64} (hb : rdq(V, g.r12) = b) (heq : b = g.rbx)
    (fb : ∀ i < 8, Foot F.data (Addr.add g.r12 i))
    (f13 : ∀ i < 8, Foot F.data (Addr.add (g.r13 + 18446744073709551584#64) i)) :
    W_139 F Wl (fun j' g' _ V' => j' = 157 ∧ g'.rsp = g.rsp ∧ g'.r12 = g.r12 ∧ g'.r15 = g.r15 ∧
      g'.rbx = g.rbx ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hb heq fb f13 ⊢
  have e := decide_eq_true heq
  wpx [W_139, W_145, o10, o11, Op.cmpmr, Op.shl64, hb, e, Bool.not_true, Bool.not_false, Bool.false_eq_true,
    Bool.true_eq_false, false_implies, eq_self_iff_true, true_implies, implies_true]
  ocl

/-- 157: `rsi` += 8, `rdi` = `rbx - 8`; to the `call` at 165. -/
theorem vc_157 :
    W_157 F Wl (fun j' g' _ V' => j' = 165 ∧ g'.rsp = g.rsp ∧ g'.r12 = g.r12 ∧ g'.r15 = g.r15 ∧
      g'.rdi = g.rbx + 18446744073709551608#64 ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_157, o12]
  ocl

end

end FV7z.Cpd
