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

- `ip b i`: the item `i`; `ip0`, `ip_m24`, `ip_m8`, `ip1_m32`, `ip_ne`: its addresses.
- `vc_*`: the verification conditions of the pieces; `from157`: from 157 to 170; `from48`: from 48, for each item.
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


/-! ## The items -/

/-- The item `i` of the array at `b` (24 bytes each). -/
abbrev ip (b : Addr) (i : Nat) : Addr := b + BitVec.ofNat 64 (24 * i)

theorem ip0 (b : Addr) : ip b 0 = b := by
  show b + BitVec.ofNat 64 (24 * 0) = b
  rw [Nat.mul_zero]
  exact BitVec.add_zero b

theorem ip_m24 (b : Addr) (i : Nat) : ip b (i + 1) - 24#64 = ip b i := by
  bv_omega

theorem ip_m8 (b : Addr) (i : Nat) : ip b (i + 1) + 18446744073709551608#64 = ip b i + 16#64 := by
  bv_omega

theorem ip1_m32 (b : Addr) : ip b 1 + 18446744073709551584#64 = b + 18446744073709551608#64 := by
  bv_omega

theorem ip_ne (b : Addr) {i : Nat} (h0 : 0 < i) (h : 24 * i < 18446744073709551616) : b ≠ ip b i := by
  bv_omega

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

/-! ## From 157 and from 48 -/

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}

/-- From 157 with `rbx` = `b` and the bytes for which `P` holds: `operator delete [] (b - 8, …)` (`hDA`, at
`0x601500`) gives `B0`, then 170 (`h170`). -/
theorem from157 {g₀ : Gprs} {ra b : Addr} {P B0 : (Addr → Byte) → Prop}
    (c : Seg prof F Wl L s₀ o) (hin : CodeIn L cpd_at cpd) (hin3 : CodeIn L 0x601500#64 Tiny.c601500)
    (w6 : ∀ i < 8, Foot Wl (Addr.add (g₀.rsp - 8 - 8 - 8 - 8 - 8 - 8) i))
    (hDA : ∀ W, P W → Call1 prof F Wl L s₀ o gev gP gE g₀.rsp 0x601500#64 (cpd_at.add 170)
      (fun g => g.rdi = b + 18446744073709551608#64) W B0)
    (h170 : AtJ prof F Wl L s₀ o gev gP gE 170 fun g W => B0 W ∧ Fr g₀ ra W ∧ Rs g₀ g) :
    AtJ prof F Wl L s₀ o gev gP gE 157 fun g W => P W ∧ Fr g₀ ra W ∧ Rs g₀ g ∧ g.rbx = b := by
  rintro Y W t' hKY hAY hrY ⟨hO, hfr, hR, hbx⟩
  refine (c_157 prof).run c hin _ hKY hAY hrY vc_157 ?_
  rintro j' g fl V₁ ⟨rfl, hs, h12, h15, hdi, hV₁⟩ U t₁ hKU hAU hrU hgU -
  subst V₁
  subst hgU
  have hsU : U.cpu.gpr.rsp = g₀.rsp - 8 - 8 - 8 - 8 - 8 := hs.trans hR.1
  have h12U : U.cpu.gpr.r12 = g₀.rdi := h12.trans hR.2.1
  have h15U : U.cpu.gpr.r15 = g₀.r15 := h15.trans hR.2.2
  refine c.s_call hKU hAU hin (lt_len (by decide)) hrU (call_165 _) hin3 (by decide) tgt_165
    (by rw [hsU]; exact w6) ?_
  rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
  rw [hsU] at hA₂
  have hsY₂ : Y₂.cpu.gpr.rsp = g₀.rsp - 8 - 8 - 8 - 8 - 8 - 8 :=
    (congrArg Gprs.rsp hg₂).trans (congrArg (fun x : Addr => x - 8) hsU)
  have hdi₂ : Y₂.cpu.gpr.rdi = b + 18446744073709551608#64 :=
    (congrArg Gprs.rdi hg₂).trans (hdi.trans (by rw [hbx]))
  refine hDA W hO Y₂ t₂ hK₂ hA₂ hr₂ hsY₂ hdi₂ ?_
  rintro Z V'' t'' hKZ hAZ hB hrZ ⟨b1, b2, b3, b4, b5, b6, b7⟩ hkf
  refine h170 Z V'' t'' hKZ hAZ hrZ ⟨hB, hfr.kf hkf, ?_, ?_, ?_⟩
  · rw [b1, hsY₂, a1s]
  · exact b4.trans ((congrArg Gprs.r12 hg₂).trans h12U)
  · exact b7.trans ((congrArg Gprs.r15 hg₂).trans h15U)

/-- From 48 for each item `i` below `N` (`g₀` the registers at the entry, `this` = `g₀.rdi`, `b` the 8 bytes at
`this` whenever `O` holds): the size `nI i` (`hn`) and `_items` = `itI i` (`hIt`) of the item; the steps as in
`FV7z/Cpd/Tail.lean` (`hP0`, `hQ0`, `hD1`, `hD2`) from `H i (nI i)` (`hOH`) to `H i 0`; `_items` freed when not 0
(`hE1`, else `hE0`) gives `O i`; then 48 again for `i - 1`, or 157 after the item 0 (`h157`). -/
set_option maxHeartbeats 4000000 in
theorem from48 {g₀ : Gprs} {ra b : Addr} {N : Nat}
    {O : Nat → (Addr → Byte) → Prop} {H : Nat → Nat → (Addr → Byte) → Prop}
    {J : Nat → Nat → BitVec 64 → (Addr → Byte) → Prop} {nI : Nat → BitVec 32} {itI : Nat → BitVec 64}
    (c : Seg prof F Wl L s₀ o) (hin : CodeIn L cpd_at cpd)
    (hin1 : CodeIn L 0x6014f0#64 Tiny.c6014f0) (hin2 : CodeIn L 0x6014e0#64 Tiny.c6014e0)
    (w6 : ∀ i < 8, Foot Wl (Addr.add (g₀.rsp - 8 - 8 - 8 - 8 - 8 - 8) i))
    (hN : 24 * N < 18446744073709551616)
    (fb : ∀ i < 8, Foot F.data (Addr.add g₀.rdi i))
    (fc : ∀ i < 8, Foot F.data (Addr.add (b + 18446744073709551608#64) i))
    (fn : ∀ i < N, ∀ j < 4, Foot F.data (Addr.add (ip b i + 16#64) j))
    (fa : ∀ i < N, ∀ j < 8, Foot F.data (Addr.add (ip b i + 8#64) j))
    (fe : ∀ i < N, ∀ k < (nI i).toNat, ∀ j < 8, Foot F.data (Addr.add (itI i + BitVec.ofNat 64 (8 * k)) j))
    (fp : ∀ i < N, ∀ k < (nI i).toNat, ∀ W, H i (k + 1) W → pk W (itI i) k ≠ 0 →
      ∀ j < 8, Foot F.data (Addr.add (pk W (itI i) k) j))
    (hb : ∀ i W, O i W → rdq(W, g₀.rdi) = b)
    (hn : ∀ i < N, ∀ W, O (i + 1) W → rdd(W, ip b i + 16#64) = nI i)
    (hOH : ∀ i < N, ∀ W, O (i + 1) W → H i (nI i).toNat W)
    (hIt : ∀ i < N, ∀ k W, H i k W → rdq(W, ip b i + 8#64) = itI i)
    (hP0 : ∀ i < N, ∀ k < (nI i).toNat, ∀ W, H i (k + 1) W → pk W (itI i) k = 0 → H i k W)
    (hQ0 : ∀ i < N, ∀ k < (nI i).toNat, ∀ W, H i (k + 1) W → pk W (itI i) k ≠ 0 →
      rdq(W, pk W (itI i) k) = 0 → J i k (pk W (itI i) k) W)
    (hD1 : ∀ i < N, ∀ k < (nI i).toNat, ∀ W, H i (k + 1) W → pk W (itI i) k ≠ 0 → rdq(W, pk W (itI i) k) ≠ 0 →
      Call1 prof F Wl L s₀ o gev gP gE g₀.rsp 0x6014f0#64 (cpd_at.add 102)
        (fun g => g.rdi = rdq(W, pk W (itI i) k)) W (J i k (pk W (itI i) k)))
    (hD2 : ∀ i < N, ∀ k < (nI i).toNat, ∀ p W, p ≠ 0 → J i k p W →
      Call1 prof F Wl L s₀ o gev gP gE g₀.rsp 0x6014e0#64 (cpd_at.add 115)
        (fun g => g.rdi = p ∧ g.rsi = 16#64) W (H i k))
    (hE0 : ∀ i < N, ∀ W, H i 0 W → itI i = 0 → O i W)
    (hE1 : ∀ i < N, ∀ W, H i 0 W → itI i ≠ 0 →
      Call1 prof F Wl L s₀ o gev gP gE g₀.rsp 0x6014f0#64 (cpd_at.add 139) (fun g => g.rdi = itI i) W (O i))
    (h157 : AtJ prof F Wl L s₀ o gev gP gE 157 fun g W => O 0 W ∧ Fr g₀ ra W ∧ Rs g₀ g ∧ g.rbx = b) :
    ∀ i < N, AtJ prof F Wl L s₀ o gev gP gE 48 fun g W => O (i + 1) W ∧ Fr g₀ ra W ∧ Rs g₀ g ∧
      g.rbx = ip b (i + 1) := by
  -- 139: back to 48 for `i - 1`, or to 157 after the item 0
  have F139 : ∀ i, i < N →
      (∀ i', i = i' + 1 → AtJ prof F Wl L s₀ o gev gP gE 48 fun g W => O (i' + 1) W ∧ Fr g₀ ra W ∧
        Rs g₀ g ∧ g.rbx = ip b (i' + 1)) →
      AtJ prof F Wl L s₀ o gev gP gE 139 fun g W => O i W ∧ Fr g₀ ra W ∧ Rs g₀ g ∧ g.rbx = ip b i ∧
        g.r13 = ip b (i + 1) := by
    rintro i hi hnx Y W t' hKY hAY hrY ⟨hO, hfr, hR, hbx, h13⟩
    have h12 : Y.cpu.gpr.r12 = g₀.rdi := hR.2.1
    have hbY : rdq(W, Y.cpu.gpr.r12) = b := by rw [h12]; exact hb _ W hO
    have fbY : ∀ j < 8, Foot F.data (Addr.add Y.cpu.gpr.r12 j) := by rw [h12]; exact fb
    cases i with
    | zero =>
      have f13 : ∀ j < 8, Foot F.data (Addr.add (Y.cpu.gpr.r13 + 18446744073709551584#64) j) := by
        have e : ip b (0 + 1) + 18446744073709551584#64 = b + 18446744073709551608#64 := ip1_m32 b
        rw [h13, e]; exact fc
      have heq : b = Y.cpu.gpr.rbx := by rw [hbx]; exact (ip0 b).symm
      refine (c_139 prof).run c hin _ hKY hAY hrY (vc_139e (g := Y.cpu.gpr) (V := W) hbY heq fbY f13) ?_
      rintro j' g fl V₁ ⟨rfl, hs, h12', h15, hbx', hV₁⟩ U t₁ hKU hAU hrU hgU -
      subst V₁
      subst hgU
      exact h157 U W t₁ hKU hAU hrU ⟨hO, hfr, ⟨hs.trans hR.1, h12'.trans hR.2.1, h15.trans hR.2.2⟩,
        hbx'.trans heq.symm⟩
    | succ i =>
      have hne : b ≠ Y.cpu.gpr.rbx := by rw [hbx]; exact ip_ne b (by omega) (by omega)
      refine (c_139 prof).run c hin _ hKY hAY hrY (vc_139c (g := Y.cpu.gpr) (V := W) hbY hne fbY) ?_
      rintro j' g fl V₁ ⟨rfl, rfl, hV₁⟩ U t₁ hKU hAU hrU hgU -
      subst V₁
      exact hnx i rfl U W t₁ hKU hAU hrU ⟨hO, hfr, by rw [hgU]; exact hR, (congrArg Gprs.rbx hgU).trans hbx⟩
  -- 129: `_items` freed when not 0, to 139
  have E129 : ∀ i, i < N →
      AtJ prof F Wl L s₀ o gev gP gE 139 (fun g W => O i W ∧ Fr g₀ ra W ∧ Rs g₀ g ∧ g.rbx = ip b i ∧
        g.r13 = ip b (i + 1)) →
      AtJ prof F Wl L s₀ o gev gP gE 129 fun g W => H i 0 W ∧ Fr g₀ ra W ∧ Rs g₀ g ∧ g.rdi = itI i ∧
        g.rbx = ip b i ∧ g.r13 = ip b (i + 1) := by
    rintro i hi h139 Y W t' hKY hAY hrY ⟨hH, hfr, hR, hdi, hbx, h13⟩
    by_cases hz0 : itI i = 0
    · refine (c_129 prof).run c hin _ hKY hAY hrY (vc_129z (g := Y.cpu.gpr) (V := W) (hdi.trans hz0)) ?_
      rintro j' g fl V₁ ⟨rfl, rfl, hV₁⟩ U t₁ hKU hAU hrU hgU -
      subst V₁
      exact h139 U W t₁ hKU hAU hrU ⟨hE0 i hi W hH hz0, hfr, by rw [hgU]; exact hR, by rw [hgU]; exact hbx,
        by rw [hgU]; exact h13⟩
    · refine (c_129 prof).run c hin _ hKY hAY hrY
        (vc_129n (g := Y.cpu.gpr) (V := W) (fun h => hz0 (hdi.symm.trans h))) ?_
      rintro j' g fl V₁ ⟨rfl, rfl, hV₁⟩ U t₁ hKU hAU hrU hgU -
      subst V₁
      have hRU : Rs g₀ U.cpu.gpr := by rw [hgU]; exact hR
      have hsU : U.cpu.gpr.rsp = g₀.rsp - 8 - 8 - 8 - 8 - 8 := hRU.1
      have hbxU : U.cpu.gpr.rbx = ip b i := by rw [hgU]; exact hbx
      have h13U : U.cpu.gpr.r13 = ip b (i + 1) := by rw [hgU]; exact h13
      have hdiU : U.cpu.gpr.rdi = itI i := by rw [hgU]; exact hdi
      refine c.s_call hKU hAU hin (lt_len (by decide)) hrU (call_134 _) hin1 (by decide) tgt_134
        (by rw [hsU]; exact w6) ?_
      rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
      rw [hsU] at hA₂
      have hsY₂ : Y₂.cpu.gpr.rsp = g₀.rsp - 8 - 8 - 8 - 8 - 8 - 8 :=
        (congrArg Gprs.rsp hg₂).trans (congrArg (fun x : Addr => x - 8) hsU)
      have hdi₂ : Y₂.cpu.gpr.rdi = itI i := (congrArg Gprs.rdi hg₂).trans hdiU
      refine hE1 i hi W hH hz0 Y₂ t₂ hK₂ hA₂ hr₂ hsY₂ hdi₂ ?_
      rintro Z V'' t'' hKZ hAZ hO hrZ ⟨b1, b2, b3, b4, b5, b6, b7⟩ hkf
      refine h139 Z V'' t'' hKZ hAZ hrZ ⟨hO, hfr.kf hkf, ⟨?_, ?_, ?_⟩, ?_, ?_⟩
      · rw [b1, hsY₂, a1s]
      · exact b4.trans ((congrArg Gprs.r12 hg₂).trans hRU.2.1)
      · exact b7.trans ((congrArg Gprs.r15 hg₂).trans hRU.2.2)
      · exact b2.trans ((congrArg Gprs.rbx hg₂).trans hbxU)
      · exact b5.trans ((congrArg Gprs.r13 hg₂).trans h13U)
  -- the item `i`, from 48 to 139
  have ITEM : ∀ i, i < N →
      AtJ prof F Wl L s₀ o gev gP gE 139 (fun g W => O i W ∧ Fr g₀ ra W ∧ Rs g₀ g ∧ g.rbx = ip b i ∧
        g.r13 = ip b (i + 1)) →
      AtJ prof F Wl L s₀ o gev gP gE 48 fun g W => O (i + 1) W ∧ Fr g₀ ra W ∧ Rs g₀ g ∧
        g.rbx = ip b (i + 1) := by
    intro i hi h139
    have hnI : (nI i).toNat < 4294967296 := (nI i).isLt
    have h129 := E129 i hi h139
    -- 102: `operator delete (p, 16)`, `rdi` = `_items` again, to 119
    have A102 : ∀ k, k < (nI i).toNat → ∀ p : BitVec 64, p ≠ 0 →
        AtJ prof F Wl L s₀ o gev gP gE 119 (fun g W => H i k W ∧ Fr g₀ ra W ∧ Rs g₀ g ∧ g.rdi = itI i ∧
          g.rbp = BitVec.ofNat 64 (8 * k) ∧ g.rbx = ip b i ∧ g.r13 = ip b (i + 1)) →
        AtJ prof F Wl L s₀ o gev gP gE 102 fun g W => J i k p W ∧ Fr g₀ ra W ∧ Rs g₀ g ∧ g.r14 = p ∧
          g.rbp = BitVec.ofNat 64 (8 * k) ∧ g.rbx = ip b i ∧ g.r13 = ip b (i + 1) := by
      rintro k hk p hp h119 Y W t' hKY hAY hrY ⟨hJ, hfr, hR, hp14, hb5, hbx, h13⟩
      refine (c_102 prof).run c hin _ hKY hAY hrY vc_102 ?_
      rintro j' g fl V₁ ⟨rfl, rfl, hV₁⟩ U t₁ hKU hAU hrU hgU -
      subst V₁
      have hRU : Rs g₀ U.cpu.gpr := by rw [hgU]; exact hR
      have hsU : U.cpu.gpr.rsp = g₀.rsp - 8 - 8 - 8 - 8 - 8 := hRU.1
      have hb5U : U.cpu.gpr.rbp = BitVec.ofNat 64 (8 * k) := by rw [hgU]; exact hb5
      have hbxU : U.cpu.gpr.rbx = ip b i := by rw [hgU]; exact hbx
      have h13U : U.cpu.gpr.r13 = ip b (i + 1) := by rw [hgU]; exact h13
      refine c.s_call hKU hAU hin (lt_len (by decide)) hrU (call_110 _) hin2 (by decide) tgt_110
        (by rw [hsU]; exact w6) ?_
      rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
      rw [hsU] at hA₂
      have hsY₂ : Y₂.cpu.gpr.rsp = g₀.rsp - 8 - 8 - 8 - 8 - 8 - 8 :=
        (congrArg Gprs.rsp hg₂).trans (congrArg (fun x : Addr => x - 8) hsU)
      have hdi₂ : Y₂.cpu.gpr.rdi = p ∧ Y₂.cpu.gpr.rsi = 16#64 :=
        ⟨(congrArg Gprs.rdi hg₂).trans ((congrArg Gprs.rdi hgU).trans hp14),
          (congrArg Gprs.rsi hg₂).trans (congrArg Gprs.rsi hgU)⟩
      refine hD2 i hi k hk p W hp hJ Y₂ t₂ hK₂ hA₂ hr₂ hsY₂ hdi₂ ?_
      rintro Z V'' t'' hKZ hAZ hHk hrZ ⟨b1, b2, b3, b4, b5, b6, b7⟩ hkf
      have hsZ : Z.cpu.gpr.rsp = g₀.rsp - 8 - 8 - 8 - 8 - 8 := by rw [b1, hsY₂, a1s]
      have hbxZ : Z.cpu.gpr.rbx = ip b i := b2.trans ((congrArg Gprs.rbx hg₂).trans hbxU)
      refine (c_115 prof).run c hin _ hKZ hAZ hrZ
        (vc_115 (it := itI i) (by rw [hbxZ]; exact hIt i hi k V'' hHk) (by rw [hbxZ]; exact fa i hi)) ?_
      rintro j' g fl V₁ ⟨rfl, rfl, hV₁⟩ U₂ t₃ hKU₂ hAU₂ hrU₂ hgU₂ -
      subst V₁
      refine h119 U₂ V'' t₃ hKU₂ hAU₂ hrU₂ ⟨hHk, hfr.kf hkf, ⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
      · exact (congrArg Gprs.rsp hgU₂).trans hsZ
      · exact (congrArg Gprs.r12 hgU₂).trans (b4.trans ((congrArg Gprs.r12 hg₂).trans hRU.2.1))
      · exact (congrArg Gprs.r15 hgU₂).trans (b7.trans ((congrArg Gprs.r15 hg₂).trans hRU.2.2))
      · exact congrArg Gprs.rdi hgU₂
      · exact (congrArg Gprs.rbp hgU₂).trans (b3.trans ((congrArg Gprs.rbp hg₂).trans hb5U))
      · exact (congrArg Gprs.rbx hgU₂).trans hbxZ
      · exact (congrArg Gprs.r13 hgU₂).trans (b5.trans ((congrArg Gprs.r13 hg₂).trans h13U))
    -- 80: the step `k`, to 119
    have B80 : ∀ k, k < (nI i).toNat →
        AtJ prof F Wl L s₀ o gev gP gE 119 (fun g W => H i k W ∧ Fr g₀ ra W ∧ Rs g₀ g ∧ g.rdi = itI i ∧
          g.rbp = BitVec.ofNat 64 (8 * k) ∧ g.rbx = ip b i ∧ g.r13 = ip b (i + 1)) →
        AtJ prof F Wl L s₀ o gev gP gE 80 fun g W => H i (k + 1) W ∧ Fr g₀ ra W ∧ Rs g₀ g ∧ g.rdi = itI i ∧
          g.rbp = BitVec.ofNat 64 (8 * k) ∧ g.rbx = ip b i ∧ g.r13 = ip b (i + 1) := by
      rintro k hk h119 Y W t' hKY hAY hrY ⟨hHk, hfr, hR, hdi, hb5, hbx, h13⟩
      have hea : Y.cpu.gpr.rdi + Y.cpu.gpr.rbp = itI i + BitVec.ofNat 64 (8 * k) := by rw [hdi, hb5]
      by_cases hp0 : pk W (itI i) k = 0
      · refine (c_80 prof).run c hin _ hKY hAY hrY
          (vc_80z (p := pk W (itI i) k) (by rw [hea]) (by rw [hea]; exact fe i hi k hk) hp0) ?_
        rintro j' g fl V₁ ⟨rfl, rfl, hV₁⟩ U t₁ hKU hAU hrU hgU -
        subst V₁
        exact h119 U W t₁ hKU hAU hrU ⟨hP0 i hi k hk W hHk hp0, hfr, by rw [hgU]; exact hR,
          (congrArg Gprs.rdi hgU).trans hdi, (congrArg Gprs.rbp hgU).trans hb5, (congrArg Gprs.rbx hgU).trans hbx,
          (congrArg Gprs.r13 hgU).trans h13⟩
      · refine (c_80 prof).run c hin _ hKY hAY hrY
          (vc_80n (p := pk W (itI i) k) (q := rdq(W, pk W (itI i) k)) (by rw [hea]) (by rw [hea]; exact fe i hi k hk)
            hp0 rfl (fp i hi k hk W hHk hp0)) ?_
        rintro j' g fl V₁ ⟨hj, rfl, hV₁⟩ U t₁ hKU hAU hrU hgU -
        subst V₁
        have hRU : Rs g₀ U.cpu.gpr := by rw [hgU]; exact hR
        have hb5U : U.cpu.gpr.rbp = BitVec.ofNat 64 (8 * k) := (congrArg Gprs.rbp hgU).trans hb5
        have hbxU : U.cpu.gpr.rbx = ip b i := (congrArg Gprs.rbx hgU).trans hbx
        have h13U : U.cpu.gpr.r13 = ip b (i + 1) := (congrArg Gprs.r13 hgU).trans h13
        have hpU : U.cpu.gpr.r14 = pk W (itI i) k := congrArg Gprs.r14 hgU
        rcases hj with ⟨hq0, rfl⟩ | ⟨hq0, rfl⟩
        · exact A102 k hk _ hp0 h119 U W t₁ hKU hAU hrU
            ⟨hQ0 i hi k hk W hHk hp0 hq0, hfr, hRU, hpU, hb5U, hbxU, h13U⟩
        · -- `operator delete [] (q)`
          have hsU : U.cpu.gpr.rsp = g₀.rsp - 8 - 8 - 8 - 8 - 8 := hRU.1
          refine c.s_call hKU hAU hin (lt_len (by decide)) hrU (call_97 _) hin1 (by decide) tgt_97
            (by rw [hsU]; exact w6) ?_
          rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
          rw [hsU] at hA₂
          have hsY₂ : Y₂.cpu.gpr.rsp = g₀.rsp - 8 - 8 - 8 - 8 - 8 - 8 :=
            (congrArg Gprs.rsp hg₂).trans (congrArg (fun x : Addr => x - 8) hsU)
          have hdi₂ : Y₂.cpu.gpr.rdi = rdq(W, pk W (itI i) k) :=
            (congrArg Gprs.rdi hg₂).trans (congrArg Gprs.rdi hgU)
          refine hD1 i hi k hk W hHk hp0 hq0 Y₂ t₂ hK₂ hA₂ hr₂ hsY₂ hdi₂ ?_
          rintro Z V'' t'' hKZ hAZ hJ hrZ ⟨b1, b2, b3, b4, b5, b6, b7⟩ hkf
          refine A102 k hk _ hp0 h119 Z V'' t'' hKZ hAZ hrZ ⟨hJ, hfr.kf hkf, ⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
          · rw [b1, hsY₂, a1s]
          · exact b4.trans ((congrArg Gprs.r12 hg₂).trans hRU.2.1)
          · exact b7.trans ((congrArg Gprs.r15 hg₂).trans hRU.2.2)
          · exact b6.trans ((congrArg Gprs.r14 hg₂).trans hpU)
          · exact b3.trans ((congrArg Gprs.rbp hg₂).trans hb5U)
          · exact b2.trans ((congrArg Gprs.rbx hg₂).trans hbxU)
          · exact b5.trans ((congrArg Gprs.r13 hg₂).trans h13U)
    -- 119: `rbp` -= 8, to 129 after the step 0, else to 80
    have S119 : ∀ k, k < (nI i).toNat →
        (∀ k', k = k' + 1 → AtJ prof F Wl L s₀ o gev gP gE 80 fun g W => H i (k' + 1) W ∧ Fr g₀ ra W ∧
          Rs g₀ g ∧ g.rdi = itI i ∧ g.rbp = BitVec.ofNat 64 (8 * k') ∧ g.rbx = ip b i ∧
          g.r13 = ip b (i + 1)) →
        AtJ prof F Wl L s₀ o gev gP gE 119 fun g W => H i k W ∧ Fr g₀ ra W ∧ Rs g₀ g ∧ g.rdi = itI i ∧
          g.rbp = BitVec.ofNat 64 (8 * k) ∧ g.rbx = ip b i ∧ g.r13 = ip b (i + 1) := by
      rintro k hk hnx Y W t' hKY hAY hrY ⟨hHk, hfr, hR, hdi, hb5, hbx, h13⟩
      cases k with
      | zero =>
        refine (c_119 prof).run c hin _ hKY hAY hrY (vc_119l (by rw [hb5]; exact rb_last)) ?_
        rintro j' g fl V₁ ⟨rfl, rfl, hV₁⟩ U t₁ hKU hAU hrU hgU -
        subst V₁
        exact h129 U W t₁ hKU hAU hrU ⟨hHk, hfr, by rw [hgU]; exact hR, (congrArg Gprs.rdi hgU).trans hdi,
          (congrArg Gprs.rbx hgU).trans hbx, (congrArg Gprs.r13 hgU).trans h13⟩
      | succ k =>
        refine (c_119 prof).run c hin _ hKY hAY hrY
          (vc_119c (by rw [hb5, rb_step k (by omega)]; exact rb_ne k (by omega))) ?_
        rintro j' g fl V₁ ⟨rfl, rfl, hV₁⟩ U t₁ hKU hAU hrU hgU -
        subst V₁
        have hb5U : U.cpu.gpr.rbp = BitVec.ofNat 64 (8 * k) := by
          rw [hgU]
          show Y.cpu.gpr.rbp - 8#64 = _
          rw [hb5]
          exact rb_step k (by omega)
        exact hnx k rfl U W t₁ hKU hAU hrU ⟨hHk, hfr, by rw [hgU]; exact hR, (congrArg Gprs.rdi hgU).trans hdi,
          hb5U, (congrArg Gprs.rbx hgU).trans hbx, (congrArg Gprs.r13 hgU).trans h13⟩
    -- the steps, by induction
    have L80 : ∀ k, k < (nI i).toNat → AtJ prof F Wl L s₀ o gev gP gE 80 fun g W => H i (k + 1) W ∧
        Fr g₀ ra W ∧ Rs g₀ g ∧ g.rdi = itI i ∧ g.rbp = BitVec.ofNat 64 (8 * k) ∧ g.rbx = ip b i ∧
        g.r13 = ip b (i + 1) := by
      intro k
      induction k with
      | zero => exact fun hk => B80 0 hk (S119 0 hk fun k' e => absurd e (by omega))
      | succ k ih =>
        exact fun hk => B80 (k + 1) hk (S119 (k + 1) hk fun k' e => by
          obtain rfl : k = k' := by omega
          exact ih (by omega))
    -- 48: the item's size and `_items`
    rintro Y W t' hKY hAY hrY ⟨hO, hfr, hR, hbx⟩
    have hnY : rdd(W, Y.cpu.gpr.rbx + 18446744073709551608#64) = nI i := by
      rw [hbx, ip_m8]; exact hn i hi W hO
    have hitY : rdq(W, Y.cpu.gpr.rbx - 24#64 + 8#64) = itI i := by
      rw [hbx, ip_m24]; exact hIt i hi _ W (hOH i hi W hO)
    have fnY : ∀ j < 4, Foot F.data (Addr.add (Y.cpu.gpr.rbx + 18446744073709551608#64) j) := by
      rw [hbx, ip_m8]; exact fn i hi
    have faY : ∀ j < 8, Foot F.data (Addr.add (Y.cpu.gpr.rbx - 24#64 + 8#64) j) := by
      rw [hbx, ip_m24]; exact fa i hi
    have hbx24 : Y.cpu.gpr.rbx - 24#64 = ip b i := by rw [hbx]; exact ip_m24 b i
    by_cases hn0 : nI i = 0
    · refine (c_48 prof).run c hin _ hKY hAY hrY (vc_48z (g := Y.cpu.gpr) (V := W) hnY hn0 hitY fnY faY) ?_
      rintro j' g fl V₁ ⟨rfl, hs, h12, h15, hbx', h13', hdi, hV₁⟩ U t₁ hKU hAU hrU hgU -
      subst V₁
      subst hgU
      have e0 : (nI i).toNat = 0 := (congrArg BitVec.toNat hn0).trans rfl
      exact h129 U W t₁ hKU hAU hrU ⟨e0 ▸ hOH i hi W hO, hfr, ⟨hs.trans hR.1, h12.trans hR.2.1, h15.trans hR.2.2⟩,
        hdi, hbx'.trans hbx24, h13'.trans hbx⟩
    · refine (c_48 prof).run c hin _ hKY hAY hrY (vc_48n (g := Y.cpu.gpr) (V := W) hnY hn0 hitY fnY faY) ?_
      rintro j' g fl V₁ ⟨rfl, hs, h12, h15, hbx', h13', hdi, hb5, hV₁⟩ U t₁ hKU hAU hrU hgU -
      subst V₁
      subst hgU
      have hnz : (nI i).toNat ≠ 0 := fun e => hn0 (BitVec.eq_of_toNat_eq (e.trans rfl))
      have e1 : (nI i).toNat - 1 + 1 = (nI i).toNat := by omega
      exact L80 ((nI i).toNat - 1) (by omega) U W t₁ hKU hAU hrU
        ⟨by rw [e1]; exact hOH i hi W hO, hfr, ⟨hs.trans hR.1, h12.trans hR.2.1, h15.trans hR.2.2⟩, hdi,
          by rw [hb5, rbx0_eq hn0], hbx'.trans hbx24, h13'.trans hbx⟩
  -- the items, by induction
  intro i
  induction i with
  | zero => exact fun hi => ITEM 0 hi (F139 0 hi fun i' e => absurd e (by omega))
  | succ i ih =>
    exact fun hi => ITEM (i + 1) hi (F139 (i + 1) hi fun i' e => by
      obtain rfl : i = i' := by omega
      exact ih (by omega))

end FV7z.Cpd
