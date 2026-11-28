import FV7z.Rdf.Cuts
import FV7z.Lemmas.LeafRet
import FV7z.Lemmas.Fr40
/-!
# `NWindows::NFile::NName::ResolveDotsFolders` (PLAN.md §M, M1): the pieces

7-Zip 26.06's `ResolveDotsFolders (UString &s)` at `0x456630` in `7zzs` (`CPP/Windows/FileName.cpp`; `objdump -d`),
`s` in `rdi`, `S` the entry's `rsp`. The empty string (`s[0]` = 0) returns at 314 with no frame. Else (13) `push r12;
push rbp; push rbx` (`aR S`), `r12` = `s`, `ebp` = the index `i` (0), `rsi` = the chars (`C`), and the loop at 32
(`Lb`): `ecx` = `edx` = `i + 1`, `rbx` = `4 (i + 1)`; `s[i]` not `.` to 51 (`i += 1`, at 53 `s[i]` 0 ends the loop, to
65, else back to 32); `.` at 0 or after `/` (84) to 93: `s[i + 1]` is `.` (152, the `..` case: `s[i + 2]` `/` or 0 to
170, else 51), `/` or 0 (110: `UString::Delete` at 134 of one or two chars from `i` or `i - 1`, the chars reloaded at
139, to 53), else 51. At 170 (`..` at `i`): `i < 2` to 200 (`eax` = 0, to 65); else the backward scans from `i - 2`
(184: skip `/`; 253: up to the previous `/`) and `Delete` at 295 (`r8` the count), the chars reloaded at 300, to 53. At
65 the pops and the `ret` (69).

- `aR`, `Stk`, `V1`, `cr`, `Fm`, `Lb`, `L53`, `KC`: the frame, the bytes, the chars, the loop's registers, a callee.
- `vc_*`: the pieces' conditions; `tail65`: from 65 to the return address.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Rdf
set_option linter.unusedVariables false

open FV7z.Fr40 (Fr KS)

/-! ## The instructions outside the blocks -/

/-- The `call`s of `UString::Delete` (134, 295); the `ret`s (69, 314). -/
def pc1 : List Byte := [0xe8, 0xf5, 0x79, 0xff, 0xff]
theorem pc1_0 : ∀ feat, Dec feat pc1 0 (FV7z.mk .call 64 [.rel 18446744073709517301] 5) := by dec_rfl
theorem wc_134 : pc1 <+: rdf.drop 134 := by decide +kernel
theorem call_134 (feat : Features) : Dec feat rdf 134 (FV7z.mk .call 64 [.rel 18446744073709517301] 5) :=
  Dec.shift (j := 134) (k := 0) (pc1_0 feat) wc_134 (Nat.zero_le _)
theorem tgt_134 : rdf_at.add (134 + 5) + BitVec.ofNat 64 18446744073709517301 = 0x44e0b0#64 := by decide

def pc2 : List Byte := [0xe8, 0x54, 0x79, 0xff, 0xff]
theorem pc2_0 : ∀ feat, Dec feat pc2 0 (FV7z.mk .call 64 [.rel 18446744073709517140] 5) := by dec_rfl
theorem wc_295 : pc2 <+: rdf.drop 295 := by decide +kernel
theorem call_295 (feat : Features) : Dec feat rdf 295 (FV7z.mk .call 64 [.rel 18446744073709517140] 5) :=
  Dec.shift (j := 295) (k := 0) (pc2_0 feat) wc_295 (Nat.zero_le _)
theorem tgt_295 : rdf_at.add (295 + 5) + BitVec.ofNat 64 18446744073709517140 = 0x44e0b0#64 := by decide

def pret : List Byte := [0xc3]
theorem pret_0 : ∀ feat, Dec feat pret 0 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem w_69 : pret <+: rdf.drop 69 := by decide +kernel
theorem ret_69 (feat : Features) : Dec feat rdf 69 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 69) (k := 0) (pret_0 feat) w_69 (Nat.zero_le _)
theorem w_314 : pret <+: rdf.drop 314 := by decide +kernel
theorem ret_314 (feat : Features) : Dec feat rdf 314 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 314) (k := 0) (pret_0 feat) w_314 (Nat.zero_le _)

/-! ## The frame, the chars, the registers -/

/-- The stack pointer after the three pushes. -/
abbrev aR (S : Addr) : Addr := S - 8 - 8 - 8

theorem sa8 (x : Addr) : x - 8 + 8 = x := BitVec.sub_add_cancel _ _
theorem a8 (S : Addr) : aR S + 8 = S - 8 - 8 := BitVec.sub_add_cancel _ _

/-- The stack: the saved `r12`, `rbp`, `rbx` and the return address. -/
abbrev Stk (W : Addr → Byte) (S : Addr) (g0 : Gprs) (ra : Addr) : Prop :=
  rdq(W, S - 8) = g0.r12 ∧ rdq(W, S - 8 - 8) = g0.rbp ∧ rdq(W, S - 8 - 8 - 8) = g0.rbx ∧ rdq(W, S) = ra

/-- The bytes after the pushes. -/
abbrev V1 (V : Addr → Byte) (g : Gprs) : Addr → Byte :=
  Vst (Vst (Vst V (g.rsp - 8) (toBytesLE g.r12 8)) (g.rsp - 8 - 8) (toBytesLE g.rbp 8)) (g.rsp - 8 - 8 - 8)
    (toBytesLE g.rbx 8)

/-- The char `k` of the string at `p` (its chars' pointer at `p`). -/
abbrev cr (W : Addr → Byte) (p : Addr) (k : Nat) : BitVec 32 := rdd(W, rdq(W, p) + BitVec.ofNat 64 (4 * k))

/-- The frame: `rsp` = `A`, `r13`–`r15` as at the entry. -/
abbrev Fm (A : Addr) (g0 g : Gprs) : Prop := g.rsp = A ∧ g.r13 = g0.r13 ∧ g.r14 = g0.r14 ∧ g.r15 = g0.r15

/-- The loop's registers at 32: `r12` = `s`, `rsi` = the chars, `rbp` = `i`. -/
abbrev Lb (A p C : Addr) (i : Nat) (g0 g : Gprs) : Prop :=
  Fm A g0 g ∧ g.r12 = p ∧ g.rsi = C ∧ g.rbp = BitVec.ofNat 64 i

/-- At 53: also `rbx` = `4 i`. -/
abbrev L53 (A p C : Addr) (i : Nat) (g0 g : Gprs) : Prop := Lb A p C i g0 g ∧ g.rbx = BitVec.ofNat 64 (4 * i)

theorem frT {g g' g'' : Gprs} (h : Fr g g') (h' : Fr g' g'') : Fr g g'' :=
  ⟨h'.1.trans h.1, h'.2.1.trans h.2.1, h'.2.2.1.trans h.2.2.1, h'.2.2.2.1.trans h.2.2.2.1,
    h'.2.2.2.2.1.trans h.2.2.2.2.1, h'.2.2.2.2.2.1.trans h.2.2.2.2.2.1, h'.2.2.2.2.2.2.trans h.2.2.2.2.2.2⟩

theorem fmF {A : Addr} {g0 g g' : Gprs} (h : Fm A g0 g) (h' : Fr g g') : Fm A g0 g' :=
  ⟨h'.1.trans h.1, h'.2.2.2.2.1.trans h.2.1, h'.2.2.2.2.2.1.trans h.2.2.1, h'.2.2.2.2.2.2.trans h.2.2.2⟩

theorem fmE {A : Addr} {g0 g g' : Gprs} (h : Fm A g0 g) (a : g'.rsp = g.rsp) (b : g'.r13 = g.r13)
    (c : g'.r14 = g.r14) (d : g'.r15 = g.r15) : Fm A g0 g' :=
  ⟨a.trans h.1, b.trans h.2.1, c.trans h.2.2.1, d.trans h.2.2.2⟩

theorem lbF {A p C : Addr} {i : Nat} {g0 g g' : Gprs} (h : Lb A p C i g0 g) (h' : Fr g g') (hs : g'.rsi = C) :
    Lb A p C i g0 g' :=
  ⟨fmF h.1 h', h'.2.2.2.1.trans h.2.1, hs, h'.2.2.1.trans h.2.2.2⟩

theorem n46 {a : BitVec 32} (h : a = 46#32) : a ≠ 0 := by rw [h]; decide

theorem ltc {W : Addr → Byte} {p : Addr} {k n : Nat} (hk : k ≤ n) (hz : cr W p n = 0) (h : cr W p k ≠ 0) :
    k < n :=
  Nat.lt_of_le_of_ne hk (fun e => h (by subst e; exact hz))

theorem z4 : (0#64 : BitVec 64) = BitVec.ofNat 64 (4 * 0) := rfl

/-! ## Arithmetic -/

/-- `bv_omega`, else the `toNat` forms and `omega`. -/
macro "rdfa" : tactic => `(tactic| first
  | bv_omega
  | (simp only [BitVec.toNat_eq, BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_add, BitVec.toNat_sub,
      BitVec.toNat_mul, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.reducePow, Nat.reduceMod] <;> omega))

theorem zx {n : Nat} (h : n < 4294967296) :
    BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 64 n)) = BitVec.ofNat 64 n := by rdfa
theorem ipk (n k : Nat) (h : n + k < 4294967296) :
    BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 64 n + BitVec.ofNat 64 k)) = BitVec.ofNat 64 (n + k) := by
  rdfa
theorem im1 {n : Nat} (h1 : 1 ≤ n) (h2 : n < 4294967296) :
    BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 64 n + 18446744073709551615#64)) =
      BitVec.ofNat 64 (n - 1) := by rdfa
theorem m4 (n : Nat) : BitVec.ofNat 64 n * 4#64 = BitVec.ofNat 64 (4 * n) := by rdfa
theorem mul1 (x : BitVec 64) : x * 1#64 = x := BitVec.mul_one x
theorem sh2 (n : Nat) : BitVec.ofNat 64 n <<< (2 : Nat) = BitVec.ofNat 64 (4 * n) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  simp only [Nat.reducePow]
  omega
theorem c170c {i : Nat} (h : i < 2) :
    ¬ (BitVec.setWidth 32 (BitVec.ofNat 64 i + 18446744073709551614#64)).toNat < 2147483645 := by rdfa
theorem c170z {i : Nat} (h : i < 2) :
    ¬ BitVec.setWidth 32 (BitVec.ofNat 64 i + 18446744073709551614#64) = 2147483645#32 := by rdfa
theorem c170g {i : Nat} (h1 : 2 ≤ i) (h2 : i < 1073741824) :
    (BitVec.setWidth 32 (BitVec.ofNat 64 i + 18446744073709551614#64)).toNat < 2147483645 := by rdfa
theorem sxf {x : BitVec 32} (h : x.toNat < 2147483648) : x.signExtend 64 = x.setWidth 64 :=
  BitVec.signExtend_eq_setWidth_of_msb_false
    (BitVec.msb_eq_false_iff_two_mul_lt.2 (by simp only [Nat.reducePow]; omega))
theorem s170 {i : Nat} (h1 : 2 ≤ i) (h2 : i < 1073741824) :
    (BitVec.setWidth 32 (BitVec.ofNat 64 i + 18446744073709551614#64)).signExtend 64 = BitVec.ofNat 64 (i - 2) := by
  rw [sxf (by rdfa)]
  rdfa
theorem sxk {k : Nat} (hk : k < 1073741824) :
    (BitVec.setWidth 32 (BitVec.ofNat 64 k) - 1#32).signExtend 64 = BitVec.ofNat 64 k + 18446744073709551615#64 := by
  rcases Nat.eq_zero_or_pos k with rfl | h
  · decide
  · rw [sxf (by rdfa)]
    rdfa
theorem dk1 {k : Nat} (h1 : 1 ≤ k) (h2 : k < 1073741824) : BitVec.ofNat 64 k - 1#64 = BitVec.ofNat 64 (k - 1) := by
  rdfa
theorem ms0 {n : Nat} (h : n < 2147483648) : (BitVec.setWidth 32 (BitVec.ofNat 64 n)).msb = false :=
  BitVec.msb_eq_false_iff_two_mul_lt.2
    (by rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat]; simp only [Nat.reducePow]; omega)
theorem ms1 {k : Nat} (h : k = 0) : (BitVec.setWidth 32 (BitVec.ofNat 64 k - 1#64)).msb = true := by
  subst h
  decide
theorem am1 {m : Nat} (h1 : 1 ≤ m) (h2 : m < 4294967296) :
    BitVec.ofNat 64 m + 18446744073709551615#64 = BitVec.ofNat 64 (m - 1) := by rdfa
theorem ne32' {m : Nat} (h1 : 1 ≤ m) (h2 : m < 4294967296) :
    ¬ BitVec.setWidth 32 (BitVec.ofNat 64 (m - 1)) = 4294967295#32 := by rdfa
theorem eq32 {m : Nat} (h : m = 0) :
    BitVec.setWidth 32 (BitVec.ofNat 64 m + 18446744073709551615#64) = 4294967295#32 := by
  subst h
  decide
theorem sb32 (a b : Nat) (h1 : b ≤ a) (h2 : a < 4294967296) :
    BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 64 a) - BitVec.setWidth 32 (BitVec.ofNat 64 b)) =
      BitVec.ofNat 64 (a - b) := by rdfa
theorem tz {i : Nat} (h : i = 0) : (BitVec.setWidth 32 (BitVec.ofNat 64 i) == 0) = true := by
  subst h
  decide
theorem tnz {i : Nat} (h1 : 1 ≤ i) (h2 : i < 4294967296) : (BitVec.setWidth 32 (BitVec.ofNat 64 i) == 0) = false :=
  beq_eq_false_iff_ne.2 (by rdfa)

theorem sk0x (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 v : BitVec 64) :
    (Gprs.mk a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15).set 0 v =
      Gprs.mk v a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 := rfl

/-! ## The pieces -/

/-- `wpx` with the flags' lemmas and the ops of the pieces here. -/
macro "rdfx" "[" ls:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| wpx [not_true_eq_false, not_false_eq_true, Bool.not_true, Bool.not_false, Bool.false_eq_true,
    Bool.true_eq_false, false_implies, implies_true, ne_eq, Bool.not_eq_true', Bool.not_eq_false',
    decide_eq_true_eq, decide_eq_false_iff_not, decide_true, decide_false, BitVec.and_self, eq_self_iff_true,
    Bool.true_or, Bool.false_or, ↓reduceIte, BitVec.reduceSetWidth, BitVec.xor_self, BitVec.sub_self,
    BitVec.ofBool_true, BitVec.ofBool_false, BitVec.reduceSub, BitVec.reduceAdd, Op.cmpmi, Op.shl64, Op.cdqe,
    Op.sxr, sk0x, mul1, $ls,*])

/-- The closers after `refine h …`. -/
macro "rdfc" : tactic =>
  `(tactic| first
    | with_reducible rfl
    | with_reducible assumption
    | exact toBytesLE_length _ _
    | exact trivial
    | apply And.intro
    | intro _
    | (apply BitVec.eq_of_toNat_eq; rdfa))

variable {F : Footprint} {Wl : List Rgn}

/-- `rsi` = the chars, `eax` = `s[0]`: 0 to 314 (`eax` = 1); else the pushes, `r12` = `s`, `ebp` = 0, to 32. -/
theorem vc_0 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (fp : ∀ i < 8, Foot F.data (Addr.add g.rdi i)) (fc : ∀ i < 4, Foot F.data (Addr.add rdq(V, g.rdi) i))
    (hs1 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8) i)) (hs2 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8) i))
    (hs3 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8 - 8) i))
    (h314 : rdd(V, rdq(V, g.rdi)) = 0 → ∀ g', g'.rsp = g.rsp → KS g g' → ∀ fl, Q 314 g' fl V)
    (h32 : ¬ rdd(V, rdq(V, g.rdi)) = 0 → ∀ g', Lb (aR g.rsp) g.rdi rdq(V, g.rdi) 0 g g' →
      g'.rax = BitVec.setWidth 64 rdd(V, rdq(V, g.rdi)) → ∀ fl, Q 32 g' fl (V1 V g)) :
    W_0 F Wl Q g f V := by
  by_cases hz : rdd(V, rdq(V, g.rdi)) = 0
  · have t := beq_iff_eq.2 hz
    have k := h314 hz
    obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
    dsimp only [KS] at fp fc hs1 hs2 hs3 t k ⊢
    rdfx [W_0, W_309, W_13, o0, o5, o1, t]
    all_goals repeat' (first | refine k _ ?_ ?_ _ | rdfc)
  · have t := beq_eq_false_iff_ne.2 hz
    have k := h32 hz
    obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
    dsimp only [Lb, Fm, aR, V1] at fp fc hs1 hs2 hs3 t k ⊢
    rdfx [W_0, W_309, W_13, o0, o5, o1, t]
    all_goals repeat' (first | refine k _ ?_ ?_ _ | rdfc)

/-- The loop's head: `ecx` = `edx` = `i + 1`, `rbx` = `4 (i + 1)`; `s[i]` not `.` to 51; `.` with `i` 0 to 93;
else `s[i - 1]` not `/` to 51, `/` to 93. -/
theorem vc_32 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} {A p C : Addr} {g0 : Gprs} {i : Nat}
    {c : BitVec 32} (hL : Lb A p C i g0 g) (ha : g.rax = BitVec.setWidth 64 c) (hi : i + 1 < 4294967296)
    (f1 : 1 ≤ i → ∀ k < 4, Foot F.data (Addr.add (C + BitVec.ofNat 64 (4 * (i - 1))) k))
    (h51 : ∀ g', Lb A p C i g0 g' → g'.rdx = BitVec.ofNat 64 (i + 1) → g'.rbx = BitVec.ofNat 64 (4 * (i + 1)) →
      ∀ fl, Q 51 g' fl V)
    (h93 : ∀ g', Lb A p C i g0 g' → g'.rcx = BitVec.ofNat 64 (i + 1) → g'.rdx = BitVec.ofNat 64 (i + 1) →
      g'.rbx = BitVec.ofNat 64 (4 * (i + 1)) → ∀ fl, Q 93 g' fl V) :
    W_32 F Wl Q g f V := by
  have e1 := ipk i 1 hi
  obtain ⟨⟨hs, h13, h14, h15⟩, h12, hsi, hbp⟩ := hL
  rcases Nat.eq_zero_or_pos i with h0 | h0
  · have t := tz h0
    obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
    dsimp only [Lb, Fm] at hs h13 h14 h15 h12 hsi hbp ha h51 h93 ⊢
    subst hs h13 h14 h15 h12 hsi hbp ha
    rdfx [W_32, W_80, W_84, o2, o7, o8, e1, m4 (i + 1), t]
    all_goals repeat' (first | refine h51 _ ?_ ?_ ?_ _ | refine h93 _ ?_ ?_ ?_ ?_ _ | rdfc)
  · have t := tnz (i := i) (by omega) (by omega)
    have e2 := im1 (n := i) (by omega) (by omega)
    have f1' := f1 (by omega)
    obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
    dsimp only [Lb, Fm] at hs h13 h14 h15 h12 hsi hbp ha h51 h93 ⊢
    subst hs h13 h14 h15 h12 hsi hbp ha
    rdfx [W_32, W_80, W_84, o2, o7, o8, e1, m4 (i + 1), t, e2, m4 (i - 1)]
    all_goals repeat' (first | refine h51 _ ?_ ?_ ?_ _ | refine h93 _ ?_ ?_ ?_ ?_ _ | rdfc)

/-- `ebp` = `edx` (the next index `n`), to 53. -/
theorem vc_51 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} {A p C : Addr} {g0 : Gprs} {i n : Nat}
    (hL : Lb A p C i g0 g) (hd : g.rdx = BitVec.ofNat 64 n) (hb : g.rbx = BitVec.ofNat 64 (4 * n))
    (hn : n < 4294967296) (h : ∀ g', L53 A p C n g0 g' → ∀ fl, Q 53 g' fl V) :
    W_51 F Wl Q g f V := by
  have ez := zx hn
  obtain ⟨⟨hs, h13, h14, h15⟩, h12, hsi, -⟩ := hL
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [L53, Lb, Fm] at hs h13 h14 h15 h12 hsi hd hb h ⊢
  subst hs h13 h14 h15 h12 hsi hd hb
  rdfx [W_51, o3, ez]
  all_goals repeat' (first | refine h _ ?_ _ | rdfc)

/-- `eax` = `s[i]`: not 0 back to 32; 0 (`eax` = 1) to 65. -/
theorem vc_53 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} {A p C : Addr} {g0 : Gprs} {i : Nat}
    (hL : L53 A p C i g0 g) (fc : ∀ k < 4, Foot F.data (Addr.add (C + BitVec.ofNat 64 (4 * i)) k))
    (h65 : rdd(V, C + BitVec.ofNat 64 (4 * i)) = 0 → ∀ g', Fm A g0 g' → ∀ fl, Q 65 g' fl V)
    (h32 : ¬ rdd(V, C + BitVec.ofNat 64 (4 * i)) = 0 → ∀ g', Lb A p C i g0 g' →
      g'.rax = BitVec.setWidth 64 rdd(V, C + BitVec.ofNat 64 (4 * i)) → ∀ fl, Q 32 g' fl V) :
    W_53 F Wl Q g f V := by
  obtain ⟨⟨⟨hs, h13, h14, h15⟩, h12, hsi, hbp⟩, hbx⟩ := hL
  by_cases hz : rdd(V, C + BitVec.ofNat 64 (4 * i)) = 0
  · have t := beq_iff_eq.2 hz
    have k := h65 hz
    obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
    dsimp only [Lb, Fm] at hs h13 h14 h15 h12 hsi hbp hbx k ⊢
    subst hs h13 h14 h15 h12 hsi hbp hbx
    rdfx [W_53, W_60, o4, o5, t]
    all_goals repeat' (first | refine k _ ?_ _ | rdfc)
  · have t := beq_eq_false_iff_ne.2 hz
    have k := h32 hz
    obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
    dsimp only [Lb, Fm] at hs h13 h14 h15 h12 hsi hbp hbx k ⊢
    subst hs h13 h14 h15 h12 hsi hbp hbx
    rdfx [W_53, W_60, o4, o5, t]
    all_goals repeat' (first | refine k _ ?_ ?_ _ | rdfc)

/-- The pops, to the `ret` (69). -/
theorem vc_65 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (p1 : ∀ i < 8, Foot F.data (Addr.add g.rsp i)) (p2 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8) i))
    (p3 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8 + 8) i))
    (h : ∀ g', g'.rsp = g.rsp + 8 + 8 + 8 → g'.rbx = rdq(V, g.rsp) → g'.rbp = rdq(V, g.rsp + 8) →
      g'.r12 = rdq(V, g.rsp + 8 + 8) → g'.r13 = g.r13 → g'.r14 = g.r14 → g'.r15 = g.r15 → ∀ fl, Q 69 g' fl V) :
    W_65 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at p1 p2 p3 h ⊢
  rdfx [W_65, o6]
  all_goals repeat' (first | refine h _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ _ | rdfc)

/-- `s[i + 1]` (`c1`): `.` and `s[i + 2]` `/` or 0 to 170, else 51; `/` or 0 to 110; else 51. -/
theorem vc_93 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} {A p C : Addr} {g0 : Gprs} {i : Nat}
    (hL : Lb A p C i g0 g) (hcx : g.rcx = BitVec.ofNat 64 (i + 1)) (hdx : g.rdx = BitVec.ofNat 64 (i + 1))
    (hbx : g.rbx = BitVec.ofNat 64 (4 * (i + 1))) (hi : i + 3 < 4294967296)
    (f1 : ∀ k < 4, Foot F.data (Addr.add (C + BitVec.ofNat 64 (4 * (i + 1))) k))
    (f2 : rdd(V, C + BitVec.ofNat 64 (4 * (i + 1))) = 46#32 →
      ∀ k < 4, Foot F.data (Addr.add (C + BitVec.ofNat 64 (4 * (i + 2))) k))
    (h51 : ∀ g', Lb A p C i g0 g' → g'.rdx = BitVec.ofNat 64 (i + 1) → g'.rbx = BitVec.ofNat 64 (4 * (i + 1)) →
      ∀ fl, Q 51 g' fl V)
    (h110 : ∀ g', Lb A p C i g0 g' → g'.rax = BitVec.setWidth 64 rdd(V, C + BitVec.ofNat 64 (4 * (i + 1))) →
      ∀ fl, Q 110 g' fl V)
    (h170 : rdd(V, C + BitVec.ofNat 64 (4 * (i + 1))) = 46#32 → ∀ g', Lb A p C i g0 g' →
      g'.r8 = BitVec.ofNat 64 (i + 2) → g'.rcx = BitVec.setWidth 64 rdd(V, C + BitVec.ofNat 64 (4 * (i + 2))) →
      ∀ fl, Q 170 g' fl V) :
    W_93 F Wl Q g f V := by
  have e2 := ipk i 2 (by omega)
  obtain ⟨⟨hs, h13, h14, h15⟩, h12, hsi, hbp⟩ := hL
  by_cases h46 : rdd(V, C + BitVec.ofNat 64 (4 * (i + 1))) = 46#32
  · have d := decide_eq_true h46
    have f2' := f2 h46
    have k := h170 h46
    obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
    dsimp only [Lb, Fm] at hs h13 h14 h15 h12 hsi hbp hcx hdx hbx h51 k ⊢
    subst hs h13 h14 h15 h12 hsi hbp hcx hdx hbx
    rdfx [W_93, W_152, W_166, W_101, W_106, o9, o15, o16, o10, o11, m4 (i + 1), e2, m4 (i + 2), d]
    all_goals repeat' (first | refine h51 _ ?_ ?_ ?_ _ | refine k _ ?_ ?_ ?_ _ | rdfc)
  · have d := decide_eq_false h46
    obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
    dsimp only [Lb, Fm] at hs h13 h14 h15 h12 hsi hbp hcx hdx hbx h51 h110 ⊢
    subst hs h13 h14 h15 h12 hsi hbp hcx hdx hbx
    rdfx [W_93, W_152, W_166, W_101, W_106, o9, o15, o16, o10, o11, m4 (i + 1), e2, m4 (i + 2), d]
    all_goals repeat' (first | refine h51 _ ?_ ?_ ?_ _ | refine h110 _ ?_ ?_ _ | rdfc)

/-- `.` then `/` or 0 at `i`: `i` 0 deletes one char (`c1` 0) or two from 0; else two from `i - 1`; to 129. -/
theorem vc_110 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} {A p C : Addr} {g0 : Gprs} {i : Nat}
    {c1 : BitVec 32} (hL : Lb A p C i g0 g) (ha : g.rax = BitVec.setWidth 64 c1) (hi : i < 4294967296)
    (h129 : ∀ x n, 1 ≤ n → i + 1 ≤ x + n → x + n ≤ i + 2 → (x + n ≤ i + 1 ∨ c1 ≠ 0) → ∀ g', Lb A p C x g0 g' →
      g'.rbx = BitVec.ofNat 64 (4 * x) → g'.rdx = BitVec.ofNat 64 n → ∀ fl, Q 129 g' fl V) :
    W_110 F Wl Q g f V := by
  obtain ⟨⟨hs, h13, h14, h15⟩, h12, hsi, hbp⟩ := hL
  rcases Nat.eq_zero_or_pos i with h0 | h0
  · have t := tz h0
    have r0 : (0#64 : BitVec 64) = BitVec.ofNat 64 (4 * i) := by subst h0; rfl
    by_cases hc : c1.toNat < 1
    · have d := decide_eq_true hc
      have k := h129 i 1 (by omega) (by omega) (by omega) (Or.inl (by omega))
      obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
      dsimp only [Lb, Fm] at hs h13 h14 h15 h12 hsi hbp ha k ⊢
      subst hs h13 h14 h15 h12 hsi hbp ha
      rdfx [W_110, W_208, W_114, o7, o22, o12, t, d]
      all_goals repeat' (first | refine k _ ?_ ?_ ?_ _ | rdfc)
    · have d := decide_eq_false hc
      have k := h129 i 2 (by omega) (by omega) (by omega) (Or.inr (fun e => hc (by rw [e]; decide)))
      obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
      dsimp only [Lb, Fm] at hs h13 h14 h15 h12 hsi hbp ha k ⊢
      subst hs h13 h14 h15 h12 hsi hbp ha
      rdfx [W_110, W_208, W_114, o7, o22, o12, t, d]
      all_goals repeat' (first | refine k _ ?_ ?_ ?_ _ | rdfc)
  · have t := tnz (i := i) (by omega) hi
    have e1 := im1 (n := i) (by omega) hi
    have k := h129 (i - 1) 2 (by omega) (by omega) (by omega) (Or.inl (by omega))
    obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
    dsimp only [Lb, Fm] at hs h13 h14 h15 h12 hsi hbp ha k ⊢
    subst hs h13 h14 h15 h12 hsi hbp ha
    rdfx [W_110, W_208, W_114, o7, o22, o12, t, e1, sh2 (i - 1)]
    all_goals repeat' (first | refine k _ ?_ ?_ ?_ _ | rdfc)

/-- `esi` = the index `x`, `rdi` = `s`, to the `call` (134). -/
theorem vc_129 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} {x : Nat}
    (hbp : g.rbp = BitVec.ofNat 64 x) (hx : x < 4294967296)
    (h : ∀ g', Fr g g' → g'.rsi = BitVec.ofNat 64 x → g'.rdx = g.rdx → g'.rdi = g.r12 → ∀ fl, Q 134 g' fl V) :
    W_129 F Wl Q g f V := by
  have ez := zx hx
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [Fr] at hbp h ⊢
  subst hbp
  rdfx [W_129, o13, ez]
  all_goals repeat' (first | refine h _ ?_ ?_ ?_ ?_ _ | rdfc)

/-- Back from `Delete`: `rsi` = the chars (reloaded), to 53. -/
theorem vc_139 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (fp : ∀ i < 8, Foot F.data (Addr.add g.r12 i))
    (h : ∀ g', Fr g g' → g'.rsi = rdq(V, g.r12) → ∀ fl, Q 53 g' fl V) :
    W_139 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [Fr] at fp h ⊢
  rdfx [W_139, o14]
  all_goals repeat' (first | refine h _ ?_ ?_ _ | rdfc)

/-- The same at 300. -/
theorem vc_300 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (fp : ∀ i < 8, Foot F.data (Addr.add g.r12 i))
    (h : ∀ g', Fr g g' → g'.rsi = rdq(V, g.r12) → ∀ fl, Q 53 g' fl V) :
    W_300 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [Fr] at fp h ⊢
  rdfx [W_300, o14]
  all_goals repeat' (first | refine h _ ?_ ?_ _ | rdfc)

/-- `..` at `i`: `i < 2` to 200; else `rdx` = `i - 2`, to 184. -/
theorem vc_170 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} {i : Nat}
    (hbp : g.rbp = BitVec.ofNat 64 i) (hi : i < 1073741824)
    (h200 : i < 2 → ∀ g', Fr g g' → ∀ fl, Q 200 g' fl V)
    (h184 : 2 ≤ i → ∀ g', Fr g g' → g'.rdx = BitVec.ofNat 64 (i - 2) → g'.rsi = g.rsi → g'.rcx = g.rcx →
      g'.r8 = g.r8 → ∀ fl, Q 184 g' fl V) :
    W_170 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [Fr] at hbp h200 h184 ⊢
  subst hbp
  rcases Nat.lt_or_ge i 2 with h2 | h2
  · have a := c170c h2
    have b := c170z h2
    have k := h200 h2
    rdfx [W_170, W_181, o17, o18, a, b]
    all_goals repeat' (first | refine k _ ?_ _ | rdfc)
  · have a := c170g h2 hi
    have b := s170 h2 hi
    have k := h184 h2
    rdfx [W_170, W_181, o17, o18, a, b]
    all_goals repeat' (first | refine k _ ?_ ?_ ?_ ?_ ?_ _ | rdfc)

/-- The scan back over `/` at `k`: not `/` to 253 (`rax` = `k - 1`); `/` with `k` 0 to 200, else `k - 1` and 184. -/
theorem vc_184 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} {k : Nat}
    (hd : g.rdx = BitVec.ofNat 64 k) (hk : k < 1073741824)
    (fk : ∀ i < 4, Foot F.data (Addr.add (g.rsi + BitVec.ofNat 64 (4 * k)) i))
    (h253 : ∀ g', Fr g g' → g'.rsi = g.rsi → g'.rcx = g.rcx → g'.r8 = g.r8 →
      g'.rax = BitVec.ofNat 64 k + 18446744073709551615#64 → ∀ fl, Q 253 g' fl V)
    (h184 : 1 ≤ k → ∀ g', Fr g g' → g'.rsi = g.rsi → g'.rcx = g.rcx → g'.r8 = g.r8 →
      g'.rdx = BitVec.ofNat 64 (k - 1) → ∀ fl, Q 184 g' fl V)
    (h200 : k = 0 → ∀ g', Fr g g' → ∀ fl, Q 200 g' fl V) :
    W_184 F Wl Q g f V := by
  have ez := zx (n := k) (by omega)
  have es := sxk hk
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [Fr] at hd fk h253 h184 h200 ⊢
  subst hd
  by_cases hs : rdd(V, rsi + BitVec.ofNat 64 (4 * k)) = 47#32
  · have d := decide_eq_true hs
    rcases Nat.eq_zero_or_pos k with h0 | h0
    · have kk := h200 h0
      have mm := ms1 h0
      rdfx [W_184, W_224, W_192, o19, o23, o20, m4 k, ez, es, d, mm]
      all_goals repeat' (first | refine kk _ ?_ _ | refine h253 _ ?_ ?_ ?_ ?_ ?_ _ | rdfc)
    · have kk := h184 (by omega)
      have e1 := dk1 (k := k) (by omega) hk
      have mm := ms0 (n := k - 1) (by omega)
      rdfx [W_184, W_224, W_192, o19, o23, o20, m4 k, ez, es, d, e1, mm]
      all_goals repeat' (first | refine kk _ ?_ ?_ ?_ ?_ ?_ _ | refine h253 _ ?_ ?_ ?_ ?_ ?_ _ | rdfc)
  · have d := decide_eq_false hs
    rdfx [W_184, W_224, W_192, o19, o23, o20, m4 k, ez, es, d]
    all_goals repeat' (first | refine h253 _ ?_ ?_ ?_ ?_ ?_ _ | rdfc)

/-- `eax` = 0, to 65. -/
theorem vc_200 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (h : ∀ g', Fr g g' → ∀ fl, Q 65 g' fl V) :
    W_200 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [Fr] at h ⊢
  rdfx [W_200, o21]
  all_goals repeat' (first | refine h _ ?_ _ | rdfc)

/-- The scan back to the previous `/` (`rax` = `m - 1`, `m` 0 the start): `/` at `m - 1` to 287 (the index `m - 1`,
the count `i + 2 - (m - 1)`); else 253 at `m - 1`; the start: `s[i + 2]` (`c2`) 0 or not, to 266. -/
theorem vc_253 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} {m i : Nat} {c2 : BitVec 32}
    (hax : g.rax = BitVec.ofNat 64 m + 18446744073709551615#64) (hr8 : g.r8 = BitVec.ofNat 64 (i + 2))
    (hcx : g.rcx = BitVec.setWidth 64 c2) (hbp : g.rbp = BitVec.ofNat 64 i) (hm : m ≤ i)
    (hi : i + 3 < 4294967296)
    (fm : 1 ≤ m → ∀ k < 4, Foot F.data (Addr.add (g.rsi + BitVec.ofNat 64 (4 * (m - 1))) k))
    (h253 : 1 ≤ m → ∀ g', Fr g g' → g'.rsi = g.rsi → g'.rcx = g.rcx → g'.r8 = g.r8 →
      g'.rax = BitVec.ofNat 64 (m - 1) + 18446744073709551615#64 → ∀ fl, Q 253 g' fl V)
    (h287 : 1 ≤ m → ∀ g', g'.rsp = g.rsp → g'.r12 = g.r12 → g'.r13 = g.r13 → g'.r14 = g.r14 →
      g'.r15 = g.r15 → g'.rbp = BitVec.ofNat 64 (m - 1) → g'.rbx = BitVec.ofNat 64 (4 * (m - 1)) →
      g'.r8 = BitVec.ofNat 64 (i + 2 - (m - 1)) → ∀ fl, Q 287 g' fl V)
    (h266 : m = 0 → ∀ n, i + 2 ≤ n → n ≤ i + 3 → (n = i + 2 ∨ c2 ≠ 0) → ∀ g', Fr g g' →
      g'.r8 = BitVec.ofNat 64 n → ∀ fl, Q 266 g' fl V) :
    W_253 F Wl Q g f V := by
  rcases Nat.eq_zero_or_pos m with h0 | h0
  · have e := eq32 h0
    by_cases hc : c2 = 0
    · have t := beq_iff_eq.2 hc
      have k := h266 h0 (i + 2) (by omega) (by omega) (Or.inl rfl)
      obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
      dsimp only [Fr] at hax hr8 hcx hbp k ⊢
      subst hax hr8 hcx hbp
      rdfx [W_253, W_240, W_258, W_272, W_250, W_262, o26, o24, o16, o29, o25, o27, e, t]
      all_goals repeat' (first | refine k _ ?_ ?_ _ | rdfc)
    · have t := beq_eq_false_iff_ne.2 hc
      have k := h266 h0 (i + 3) (by omega) (by omega) (Or.inr hc)
      have e3 := ipk i 3 hi
      obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
      dsimp only [Fr] at hax hr8 hcx hbp k ⊢
      subst hax hr8 hcx hbp
      rdfx [W_253, W_240, W_258, W_272, W_250, W_262, o26, o24, o16, o29, o25, o27, e, t, e3]
      all_goals repeat' (first | refine k _ ?_ ?_ _ | rdfc)
  · have e1 := am1 (m := m) (by omega) (by omega)
    have n1 := ne32' (m := m) (by omega) (by omega)
    have f' := fm (by omega)
    have k253 := h253 (by omega)
    have k287 := h287 (by omega)
    have ez := zx (n := m - 1) (by omega)
    have es := sb32 (i + 2) (m - 1) (by omega) (by omega)
    obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
    dsimp only [Fr] at hax hr8 hcx hbp f' k253 k287 ⊢
    subst hax hr8 hcx hbp
    rdfx [W_253, W_240, W_258, W_272, W_250, W_262, o26, o24, o16, o29, o25, o27, e1, n1, m4 (m - 1), ez, es]
    all_goals repeat' (first | refine k253 _ ?_ ?_ ?_ ?_ ?_ _ | refine k287 _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ _ | rdfc)

/-- `ebx` = `ebp` = 0, to 287. -/
theorem vc_266 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (h : ∀ g', g'.rsp = g.rsp → g'.r12 = g.r12 → g'.r13 = g.r13 → g'.r14 = g.r14 → g'.r15 = g.r15 →
      g'.r8 = g.r8 → g'.rbx = 0#64 → g'.rbp = 0#64 → ∀ fl, Q 287 g' fl V) :
    W_266 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h ⊢
  rdfx [W_266, o28]
  all_goals repeat' (first | refine h _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ _ | rdfc)

/-- `esi` = the index `x`, `edx` = the count `n`, `rdi` = `s`, to the `call` (295). -/
theorem vc_287 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} {x n : Nat}
    (hbp : g.rbp = BitVec.ofNat 64 x) (hr8 : g.r8 = BitVec.ofNat 64 n) (hx : x < 4294967296)
    (hn : n < 4294967296)
    (h : ∀ g', Fr g g' → g'.rsi = BitVec.ofNat 64 x → g'.rdx = BitVec.ofNat 64 n → g'.rdi = g.r12 →
      ∀ fl, Q 295 g' fl V) :
    W_287 F Wl Q g f V := by
  have ex := zx hx
  have en := zx hn
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [Fr] at hbp hr8 h ⊢
  subst hbp hr8
  rdfx [W_287, o30, ex, en]
  all_goals repeat' (first | refine h _ ?_ ?_ ?_ ?_ _ | rdfc)

/-! ## The runs -/

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {X : State} {t : Nat} {V : Addr → Byte} {e₂ : Addr} {code₂ : List Byte} {j₂ : Nat}

/-- A callee at `tg` from a `call` returning to `rdf_at + r` (registers `G` there, bytes `W`): at its entry, and
from its return with the registers `Fr` keeps and its post `P` on the bytes, the run goes on to the goal. -/
def KC (prof : Profile) (F : Footprint) (Wl : List Rgn) (L : List (Addr × List Byte)) (s₀ : State) (o : Oracle)
    (gev : List Event) (gP : State → Nat → List Event → Prop) (gE : Outcome → List Event → Prop)
    (tg : Addr) (r : Nat) (G : Gprs) (W : Addr → Byte) (P : (Addr → Byte) → Prop) : Prop :=
  ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y →
    Agree F Y.proc.mm.mem (Vst W (G.rsp - 8) (toBytesLE (rdf_at.add r) 8)) →
    Y.cpu.rip = tg → Y.cpu.gpr = G.set 4 (G.rsp - 8) →
    (∀ (Z : State) (W' : Addr → Byte) (t'' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem W' →
      Z.cpu.rip = rdf_at.add r → Fr G Z.cpu.gpr → P W' → GoG prof L o gev gP gE Z t'') →
    GoG prof L o gev gP gE Y t'

/-- From 65 (the frame `Fm` at `aR S`, the stack `Stk`) to the return address `e₂.add j₂`. -/
theorem tail65 {W : Addr → Byte} {S : Addr} {g0 : Gprs} {Y : State} (c : Seg prof F Wl L s₀ o)
    (hin : CodeIn L rdf_at rdf) (hK : KeptW Wl s₀ Y) (hA : Agree F Y.proc.mm.mem W)
    (hr : Y.cpu.rip = rdf_at.add 65) (hm : Fm (aR S) g0 Y.cpu.gpr) (hst : Stk W S g0 (e₂.add j₂))
    (g1 : ∀ i < 8, Foot F.data (Addr.add (S - 8) i)) (g2 : ∀ i < 8, Foot F.data (Addr.add (S - 8 - 8) i))
    (g3 : ∀ i < 8, Foot F.data (Addr.add (S - 8 - 8 - 8) i))
    (hl : ∀ i < 8, Foot F.data (Addr.add S i)) (hin₂ : CodeIn L e₂ code₂) (h₂ : j₂ < code₂.length)
    (k : ∀ (Z' : State) (t' : Nat), KeptW Wl s₀ Z' → Agree F Z'.proc.mm.mem W → Z'.cpu.rip = e₂.add j₂ →
      Z'.cpu.gpr.rsp = S + 8 → KS g0 Z'.cpu.gpr → GoG prof L o gev gP gE Z' t') :
    GoG prof L o gev gP gE Y t := by
  obtain ⟨s1, s2, s3, s4⟩ := hst
  obtain ⟨hs, h13, h14, h15⟩ := hm
  have q1 : Y.cpu.gpr.rsp + 8 = S - 8 - 8 := by rw [hs, a8]
  have q2 : Y.cpu.gpr.rsp + 8 + 8 = S - 8 := by rw [q1, sa8]
  have q3 : Y.cpu.gpr.rsp + 8 + 8 + 8 = S := by rw [q2, sa8]
  refine (c_65 prof).run c hin (fun j' g' _ V' => j' = 69 ∧ V' = W ∧ g'.rsp = S ∧
      g'.rbx = g0.rbx ∧ g'.rbp = g0.rbp ∧ g'.r12 = g0.r12 ∧ g'.r13 = g0.r13 ∧ g'.r14 = g0.r14 ∧
      g'.r15 = g0.r15) hK hA hr
    (vc_65 (by rw [hs]; exact g3) (by rw [q1]; exact g2) (by rw [q2]; exact g1)
      fun _ a1 a2 a3 a4 a5 a6 a7 _ => ⟨rfl, rfl, a1.trans q3, a2.trans (by rw [hs]; exact s3),
        a3.trans (by rw [q1]; exact s2), a4.trans (by rw [q2]; exact s1), a5.trans h13, a6.trans h14,
        a7.trans h15⟩) ?_
  rintro j' g fl V₁ ⟨rfl, hV₁, gs, gb, gp, g12, g13, g14, g15⟩ U t₁ hKU hAU hrU hgU -
  subst V₁ hgU
  refine c.s_ret hKU hAU hin (lt_len (by decide)) hrU (ret_69 _) (by rw [gs]; exact hl) hin₂ h₂
    (by rw [gs]; exact s4) ?_
  rintro Z' t₂ hKZ' hAZ' ⟨hrZ', hgZ'⟩
  refine k Z' t₂ hKZ' hAZ' hrZ' ?_ ?_
  · rw [hgZ']
    show U.cpu.gpr.rsp + 8 = _
    rw [gs]
  · rw [hgZ']
    exact ⟨gb, gp, g12, g13, g14, g15⟩

end FV7z.Rdf
