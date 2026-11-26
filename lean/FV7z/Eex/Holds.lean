import FV7z.Eex.Cuts
import FV7z.Cpt.Holds
/-!
# `NWildcard::CCensor::ExtendExclude` (PLAN.md §M, M1)

7-Zip 26.06's `NWildcard::CCensor::ExtendExclude ()` at `0x4535b0` in `7zzs` (`CPP/Common/Wildcard.cpp`;
`objdump -d`): `for (i = 0; i < Pairs.Size(); i++) if (Pairs[i].Prefix.IsEmpty()) break; if (i == Pairs.Size())
return; unsigned index = i; for (i = 0; i < Pairs.Size(); i++) if (index != i)
Pairs[i].Head.ExtendExclude(Pairs[index].Head);` (`this` = `rdi`, `Pairs` its `CObjectVector<CPair>`: the items'
pointers at `[this]`, the count at `this + 8`; a pair's `Prefix._len` at `+ 8`, its `Head` at `+ 16`;
`CCensorNode::ExtendExclude` at `0x453210`, called at 106).

The frame is `FV7z.Cpt`'s (`push r13; push r12; push rbp; push rbx; sub rsp, 8`), and so are its lemmas. No pairs:
the pops and the `ret` at 131 (`vc_0z`, `vc_121`). The first loop (55, `rax` = `i`, no calls) looks for the first
pair with an empty prefix (`Emp`): found, to 68 with `ebp` = `index` (`vc_55f`); else the next pair (`vc_55n`), or,
after the last one, the pops and the `ret` at 150 (`vc_55e`). From 68 (`vc_68`) the second loop (80, `ebx` = `i`,
`r13` = `8 index`) skips `index` (`vc_80s`) and calls `CCensorNode::ExtendExclude (Pairs[i]->Head,
Pairs[index]->Head)` for every other pair (`vc_80c`); `CCensorNode::ExtendExclude` is a hypothesis (`Ext`), as in
`FV7z.Cpt`. After it (111) `i + 1` and back while below the count, which is read again (`vc_111l`), or to 121
(`vc_111e`). `lp1Head`/`lp1All` and `lp2Head`/`lp2All` are the loops, `eex_ok` the function.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Eex

/-! ## The instructions outside the blocks -/

def pc106 : List Byte := [0xe8, 0xf1, 0xfb, 0xff, 0xff]
def pret : List Byte := [0xc3]
theorem pc106_0 : ∀ feat, Dec feat pc106 0 (FV7z.mk .call 64 [.rel 18446744073709550577] 5) := by dec_rfl
theorem pret_0 : ∀ feat, Dec feat pret 0 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem wc106 : pc106 <+: eex.drop 106 := by decide +kernel
theorem w_131 : pret <+: eex.drop 131 := by decide +kernel
theorem w_150 : pret <+: eex.drop 150 := by decide +kernel
theorem call_106 (feat : Features) : Dec feat eex 106 (FV7z.mk .call 64 [.rel 18446744073709550577] 5) :=
  Dec.shift (j := 106) (k := 0) (pc106_0 feat) wc106 (Nat.zero_le _)
theorem ret_131 (feat : Features) : Dec feat eex 131 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 131) (k := 0) (pret_0 feat) w_131 (Nat.zero_le _)
theorem ret_150 (feat : Features) : Dec feat eex 150 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 150) (k := 0) (pret_0 feat) w_150 (Nat.zero_le _)

/-- `CCensorNode::ExtendExclude`. -/
abbrev ext_at : Addr := 0x453210
theorem tgt106 : eex_at.add (106 + 5) + BitVec.ofNat 64 18446744073709550577 = ext_at := by decide

/-! ## The pieces -/

/-- `esi` = the count less 1 (`lea esi, [rdi - 1]`). -/
abbrev mI (x : BitVec 32) : BitVec 64 :=
  BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.setWidth 64 x + 18446744073709551615#64))
/-- The registers at 121 with no pairs. -/
abbrev g0z (V : Addr → Byte) (g : Gprs) : Gprs :=
  { g with
    rdi := BitVec.setWidth 64 rdd(Cpt.V1 V g, g.rdi + 8#64), r12 := g.rdi, rsp := g.rsp - 8 - 8 - 8 - 8 - 8#64 }
/-- The registers at the first loop the first time. -/
abbrev g55 (V : Addr → Byte) (g : Gprs) : Gprs :=
  { g with
    rax := 0#64, rcx := rdq(Cpt.V1 V g, g.rdi), rsi := mI rdd(Cpt.V1 V g, g.rdi + 8#64),
    rdi := BitVec.setWidth 64 rdd(Cpt.V1 V g, g.rdi + 8#64), r12 := g.rdi, rsp := g.rsp - 8 - 8 - 8 - 8 - 8#64 }
/-- Found: to 68. -/
abbrev gFd (V : Addr → Byte) (g : Gprs) : Gprs :=
  { g with
    rdx := BitVec.setWidth 64 rdd(V, rdq(V, g.rcx + g.rax * 8#64) + 8#64),
    rbp := BitVec.setWidth 64 (BitVec.setWidth 32 g.rax) }
/-- The next pair. -/
abbrev gL (g : Gprs) : Gprs :=
  { g with rax := g.rax + 1#64, rdx := g.rax + 1#64, rbp := BitVec.setWidth 64 (BitVec.setWidth 32 (g.rax + 1#64)) }
/-- None found: the pops, the `ret` at 150. -/
abbrev gR (V : Addr → Byte) (g : Gprs) : Gprs :=
  { g with
    rdx := g.rax + 1#64, rbx := rdq(V, g.rsp + 8#64), rbp := rdq(V, g.rsp + 8#64 + 8),
    r12 := rdq(V, g.rsp + 8#64 + 8 + 8), r13 := rdq(V, g.rsp + 8#64 + 8 + 8 + 8), rsp := g.rsp + 8#64 + 8 + 8 + 8 + 8 }
/-- The second loop the first time. -/
abbrev g80 (g : Gprs) : Gprs := { g with rbx := 0#64, r13 := BitVec.setWidth 64 (BitVec.setWidth 32 g.rbp) <<< 3 }
/-- The registers at the `call`. -/
abbrev gC (V : Addr → Byte) (g : Gprs) : Gprs :=
  { g with
    rax := rdq(V, g.r12), rdx := BitVec.setWidth 64 (BitVec.setWidth 32 g.rbx), rcx := rdq(V, rdq(V, g.r12) + g.r13),
    rsi := rdq(V, rdq(V, g.r12) + g.r13) + 16#64,
    rdi := rdq(V, rdq(V, g.r12) + BitVec.setWidth 64 (BitVec.setWidth 32 g.rbx) * 8#64) + 16#64 }
/-- `i + 1`. -/
abbrev gI (g : Gprs) : Gprs := { g with rbx := BitVec.setWidth 64 (BitVec.setWidth 32 g.rbx + 1#32) }

variable {F : Footprint} {Wl : List Rgn}

/-- No pairs: to 121. -/
theorem vc_0z {g : Gprs} {f : Rflags} {V : Addr → Byte} (h0 : rdd(Cpt.V1 V g, g.rdi + 8#64) = 0#32)
    (hs1 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8) i)) (hs2 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8) i))
    (hs3 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8 - 8) i))
    (hs4 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8 - 8 - 8) i))
    (f8 : ∀ i < 4, Foot F.data (Addr.add (g.rdi + 8#64) i)) :
    W_0 F Wl (fun j' g' _ V' => j' = 121 ∧ g' = g0z V g ∧ V' = Cpt.V1 V g) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [g0z, Cpt.V1] at h0 f8 hs1 hs2 hs3 hs4 ⊢
  wpx [W_0, W_24, o0, o1, BitVec.and_self, beq_iff_eq, beq_eq_false_iff_ne, ne_eq, Bool.not_eq_true',
    Bool.not_eq_false', decide_eq_true_eq, decide_eq_false_iff_not, lf_xz, BitVec.xor_self, BitVec.setWidth_zero]
  all_goals repeat' (first
    | exact rfl
    | assumption
    | exact trivial
    | (intro hh; exact absurd h0 hh)
    | (intro hh; exact absurd h0 (by simpa using hh))
    | apply And.intro
    | intro _)

/-- Pairs: to the first loop with `i` = 0. -/
theorem vc_0n {g : Gprs} {f : Rflags} {V : Addr → Byte} (h : rdd(Cpt.V1 V g, g.rdi + 8#64) ≠ 0#32)
    (hs1 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8) i)) (hs2 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8) i))
    (hs3 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8 - 8) i))
    (hs4 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8 - 8 - 8) i))
    (f8 : ∀ i < 4, Foot F.data (Addr.add (g.rdi + 8#64) i)) (f0 : ∀ i < 8, Foot F.data (Addr.add g.rdi i)) :
    W_0 F Wl (fun j' g' _ V' => j' = 55 ∧ g' = g55 V g ∧ V' = Cpt.V1 V g) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [g55, mI, Cpt.V1] at h f8 f0 hs1 hs2 hs3 hs4 ⊢
  wpx [W_0, W_24, o0, o1, BitVec.and_self, beq_iff_eq, beq_eq_false_iff_ne, ne_eq, Bool.not_eq_true',
    Bool.not_eq_false', decide_eq_true_eq, decide_eq_false_iff_not, lf_xz, BitVec.xor_self, BitVec.setWidth_zero]
  all_goals repeat' (first
    | exact rfl
    | assumption
    | exact trivial
    | (intro hh; exact absurd hh h)
    | (intro hh; exact absurd (by simpa using hh) h)
    | apply And.intro
    | intro _)

/-- The first loop: the `i`-th pair's prefix is empty, to 68. -/
theorem vc_55f {g : Gprs} {f : Rflags} {V : Addr → Byte} (h : rdd(V, rdq(V, g.rcx + g.rax * 8#64) + 8#64) = 0#32)
    (f1 : ∀ i < 8, Foot F.data (Addr.add (g.rcx + g.rax * 8#64) i))
    (f2 : ∀ i < 4, Foot F.data (Addr.add (rdq(V, g.rcx + g.rax * 8#64) + 8#64) i)) :
    W_55 F Wl (fun j' g' _ V' => j' = 68 ∧ g' = gFd V g ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [gFd] at h f1 f2 ⊢
  wpx [W_55, W_40, W_52, W_136, W_140, o4, o2, o3, o10, o9, BitVec.and_self, beq_iff_eq, beq_eq_false_iff_ne,
    ne_eq, Bool.not_eq_true', Bool.not_eq_false', decide_eq_true_eq, decide_eq_false_iff_not]
  all_goals repeat' (first
    | exact rfl
    | assumption
    | exact trivial
    | (intro hh; exact absurd h hh)
    | (intro hh; exact absurd h (by simpa using hh))
    | apply And.intro
    | intro _)

/-- The first loop: not empty, not the last: the next pair. -/
theorem vc_55n {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (hl : ¬rdd(V, rdq(V, g.rcx + g.rax * 8#64) + 8#64) = 0#32) (hne : ¬g.rax = g.rsi)
    (f1 : ∀ i < 8, Foot F.data (Addr.add (g.rcx + g.rax * 8#64) i))
    (f2 : ∀ i < 4, Foot F.data (Addr.add (rdq(V, g.rcx + g.rax * 8#64) + 8#64) i)) :
    W_55 F Wl (fun j' g' _ V' => j' = 55 ∧ g' = gL g ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [gL] at hl hne f1 f2 ⊢
  wpx [W_55, W_40, W_52, W_136, W_140, o4, o2, o3, o10, o9, BitVec.and_self, beq_iff_eq, beq_eq_false_iff_ne,
    ne_eq, Bool.not_eq_true', Bool.not_eq_false', decide_eq_true_eq, decide_eq_false_iff_not]
  all_goals repeat' (first
    | exact rfl
    | assumption
    | exact trivial
    | (intro hh; exact absurd hh hne)
    | (intro hh; exact absurd hh hl)
    | (intro hh; exact absurd (by simpa using hh) hl)
    | apply And.intro
    | intro _)

/-- The first loop: not empty, the last: the pops, the `ret` at 150. -/
theorem vc_55e {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (hl : ¬rdd(V, rdq(V, g.rcx + g.rax * 8#64) + 8#64) = 0#32) (heq : g.rax = g.rsi)
    (hb : BitVec.setWidth 32 (g.rax + 1#64) = BitVec.setWidth 32 g.rdi)
    (f1 : ∀ i < 8, Foot F.data (Addr.add (g.rcx + g.rax * 8#64) i))
    (f2 : ∀ i < 4, Foot F.data (Addr.add (rdq(V, g.rcx + g.rax * 8#64) + 8#64) i))
    (p1 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8#64) i))
    (p2 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8#64 + 8) i))
    (p3 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8#64 + 8 + 8) i))
    (p4 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8#64 + 8 + 8 + 8) i)) :
    W_55 F Wl (fun j' g' _ V' => j' = 150 ∧ g' = gR V g ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [gR] at hl heq hb f1 f2 p1 p2 p3 p4 ⊢
  wpx [W_55, W_40, W_52, W_136, W_140, o4, o2, o3, o10, o9, BitVec.and_self, beq_iff_eq, beq_eq_false_iff_ne,
    ne_eq, Bool.not_eq_true', Bool.not_eq_false', decide_eq_true_eq, decide_eq_false_iff_not]
  all_goals repeat' (first
    | exact rfl
    | assumption
    | exact trivial
    | (intro hh; exact absurd heq hh)
    | (intro hh; exact absurd hb hh)
    | (intro hh; exact absurd hh hl)
    | (intro hh; exact absurd (by simpa using hh) hl)
    | (intro hh; exact absurd hb (by simpa using hh))
    | apply And.intro
    | intro _)

/-- 68: `ebx` = 0, `r13` = `8 index`, to the second loop. -/
theorem vc_68 {g : Gprs} {f : Rflags} {V : Addr → Byte} :
    W_68 F Wl (fun j' g' _ V' => j' = 80 ∧ g' = g80 g ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [g80]
  wpx [W_68, o5, Op.shl64, lf_xz, BitVec.xor_self, BitVec.setWidth_zero]
  all_goals repeat' (first
    | exact rfl
    | assumption
    | exact trivial
    | apply And.intro
    | intro _)

/-- The second loop: `i` = `index`, skipped. -/
theorem vc_80s {g : Gprs} {f : Rflags} {V : Addr → Byte} (h : BitVec.setWidth 32 g.rbx = BitVec.setWidth 32 g.rbp) :
    W_80 F Wl (fun j' g' _ V' => j' = 111 ∧ g' = g ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h ⊢
  wpx [W_80, W_84, o6, o7, BitVec.and_self, beq_iff_eq, beq_eq_false_iff_ne, ne_eq, Bool.not_eq_true',
    Bool.not_eq_false', decide_eq_true_eq, decide_eq_false_iff_not]
  all_goals repeat' (first
    | exact rfl
    | assumption
    | exact trivial
    | (intro hh; exact absurd h hh)
    | apply And.intro
    | intro _)

/-- The second loop: another pair, to the `call`. -/
theorem vc_80c {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (h : ¬BitVec.setWidth 32 g.rbx = BitVec.setWidth 32 g.rbp) (f12 : ∀ i < 8, Foot F.data (Addr.add g.r12 i))
    (fa : ∀ i < 8, Foot F.data (Addr.add (rdq(V, g.r12) + g.r13) i))
    (fb : ∀ i < 8, Foot F.data (Addr.add (rdq(V, g.r12) + BitVec.setWidth 64 (BitVec.setWidth 32 g.rbx) * 8#64) i)) :
    W_80 F Wl (fun j' g' _ V' => j' = 106 ∧ g' = gC V g ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [gC] at h f12 fa fb ⊢
  wpx [W_80, W_84, o6, o7, BitVec.and_self, beq_iff_eq, beq_eq_false_iff_ne, ne_eq, Bool.not_eq_true',
    Bool.not_eq_false', decide_eq_true_eq, decide_eq_false_iff_not]
  all_goals repeat' (first
    | exact rfl
    | assumption
    | exact trivial
    | (intro hh; exact absurd hh h)
    | apply And.intro
    | intro _)

/-- After the `call`: `i + 1` below the count, back to the second loop. -/
theorem vc_111l {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (h : (BitVec.setWidth 32 g.rbx + 1#32).toNat < rdd(V, g.r12 + 8#64).toNat)
    (f8 : ∀ i < 4, Foot F.data (Addr.add (g.r12 + 8#64) i)) :
    W_111 F Wl (fun j' g' _ V' => j' = 80 ∧ g' = gI g ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [gI] at h f8 ⊢
  wpx [W_111, o8, BitVec.and_self, beq_iff_eq, beq_eq_false_iff_ne, ne_eq, Bool.not_eq_true', Bool.not_eq_false',
    decide_eq_true_eq, decide_eq_false_iff_not]
  all_goals repeat' (first
    | exact rfl
    | assumption
    | exact trivial
    | (intro hh; exact absurd h hh)
    | apply And.intro
    | intro _)

/-- After the `call`: `i + 1` not below the count, to 121. -/
theorem vc_111e {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (h : ¬(BitVec.setWidth 32 g.rbx + 1#32).toNat < rdd(V, g.r12 + 8#64).toNat)
    (f8 : ∀ i < 4, Foot F.data (Addr.add (g.r12 + 8#64) i)) :
    W_111 F Wl (fun j' g' _ V' => j' = 121 ∧ g' = gI g ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [gI] at h f8 ⊢
  wpx [W_111, o8, BitVec.and_self, beq_iff_eq, beq_eq_false_iff_ne, ne_eq, Bool.not_eq_true', Bool.not_eq_false',
    decide_eq_true_eq, decide_eq_false_iff_not]
  all_goals repeat' (first
    | exact rfl
    | assumption
    | exact trivial
    | (intro hh; exact absurd hh h)
    | apply And.intro
    | intro _)

/-- 121: the pops, the `ret` at 131. -/
theorem vc_121 {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (p1 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8#64) i))
    (p2 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8#64 + 8) i))
    (p3 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8#64 + 8 + 8) i))
    (p4 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8#64 + 8 + 8 + 8) i)) :
    W_121 F Wl (fun j' g' _ V' => j' = 131 ∧ g' = Cpt.gF V g ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [Cpt.gF] at p1 p2 p3 p4 ⊢
  wpx [W_121, o9]
  all_goals repeat' (first
    | exact rfl
    | assumption
    | exact trivial
    | apply And.intro
    | intro _)

/-! ## Arithmetic -/

/-- The low half of `setWidth 64 x - 1`. -/
theorem lo_dec (x : BitVec 32) :
    BitVec.setWidth 32 (BitVec.setWidth 64 x + 18446744073709551615#64) = x - 1#32 := by
  bv_omega

theorem mI_eq {x : BitVec 32} {n : Nat} (hx : x.toNat = n) (hn : 0 < n) : mI x = BitVec.ofNat 64 (n - 1) := by
  have := x.isLt
  show BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.setWidth 64 x + 18446744073709551615#64)) = _
  rw [lo_dec]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
  omega

theorem ofNat_ne {i j : Nat} (hi : i < 2 ^ 64) (hj : j < 2 ^ 64) (h : i ≠ j) :
    ¬BitVec.ofNat 64 i = BitVec.ofNat 64 j := fun e => by
  have := congrArg BitVec.toNat e
  simp only [BitVec.toNat_ofNat, Nat.reducePow] at this
  omega

theorem add1 (i : Nat) : BitVec.ofNat 64 i + 1#64 = BitVec.ofNat 64 (i + 1) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
  omega

theorem lea_n {x : BitVec 32} {i n : Nat} (hx : x.toNat = n) (h : i + 1 = n) :
    BitVec.setWidth 32 (BitVec.ofNat 64 i + 1#64) = BitVec.setWidth 32 (BitVec.setWidth 64 x) := by
  have := x.isLt
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
  omega

theorem sw_iff {i j : Nat} (hi : i < 2 ^ 32) (hj : j < 2 ^ 32) :
    BitVec.setWidth 32 (BitVec.ofNat 64 i) = BitVec.setWidth 32 (BitVec.ofNat 64 j) ↔ i = j := by
  constructor
  · intro e
    have := congrArg BitVec.toNat e
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.reducePow] at this
    omega
  · rintro rfl
    rfl

theorem shl3 {k : Nat} (h : k < 2 ^ 32) :
    BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 64 k)) <<< 3 = BitVec.ofNat 64 k * 8#64 := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_mul, BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.shiftLeft_eq,
    Nat.reducePow, Nat.reduceMod]
  omega

/-! ## The data -/

/-- The number of pairs, as read. -/
abbrev nB (V₀ : Addr → Byte) (g₀ : Gprs) : BitVec 32 := rdd(V₀, g₀.rdi + 8#64)
/-- The number of pairs. -/
abbrev nP (V₀ : Addr → Byte) (g₀ : Gprs) : Nat := (nB V₀ g₀).toNat
/-- The pairs' pointers. -/
abbrev its (V₀ : Addr → Byte) (g₀ : Gprs) : Addr := rdq(V₀, g₀.rdi)
/-- The `k`-th pair's pointer's address. -/
abbrev slot (V₀ : Addr → Byte) (g₀ : Gprs) (k : Nat) : Addr := its V₀ g₀ + BitVec.ofNat 64 k * 8#64
/-- The `k`-th pair. -/
abbrev itm (V₀ : Addr → Byte) (g₀ : Gprs) (k : Nat) : Addr := rdq(V₀, slot V₀ g₀ k)
/-- The `k`-th pair's prefix is empty (`_len` = 0). -/
def Emp (V₀ : Addr → Byte) (g₀ : Gprs) (k : Nat) : Prop := rdd(V₀, itm V₀ g₀ k + 8#64) = 0#32
/-- `index`: the first pair with an empty prefix. -/
def Idx (V₀ : Addr → Byte) (g₀ : Gprs) (idx : Nat) : Prop :=
  idx < nP V₀ g₀ ∧ Emp V₀ g₀ idx ∧ ∀ k < idx, ¬Emp V₀ g₀ k

/-- The bytes `V` read as at the entry, in both loops. -/
structure Dat (V₀ : Addr → Byte) (g₀ : Gprs) (V : Addr → Byte) : Prop where
  n : rdd(V, g₀.rdi + 8#64) = rdd(V₀, g₀.rdi + 8#64)
  it : 0 < nP V₀ g₀ → rdq(V, g₀.rdi) = its V₀ g₀
  sl : ∀ k < nP V₀ g₀, rdq(V, slot V₀ g₀ k) = itm V₀ g₀ k

/-- The prefixes' lengths as at the entry: the first loop. -/
def Ln (V₀ : Addr → Byte) (g₀ : Gprs) (V : Addr → Byte) : Prop :=
  ∀ k < nP V₀ g₀, rdd(V, itm V₀ g₀ k + 8#64) = rdd(V₀, itm V₀ g₀ k + 8#64)

/-- In the loops: `Dat`, the four registers pushed and the return address `ra`. -/
structure Inv (V₀ : Addr → Byte) (g₀ : Gprs) (ra : Addr) (V : Addr → Byte) : Prop where
  d : Dat V₀ g₀ V
  r13 : rdq(V, g₀.rsp - 8#64) = g₀.r13
  r12 : rdq(V, g₀.rsp - 16#64) = g₀.r12
  rbp : rdq(V, g₀.rsp - 24#64) = g₀.rbp
  rbx : rdq(V, g₀.rsp - 32#64) = g₀.rbx
  ra : rdq(V, g₀.rsp) = ra

/-- The registers at the first loop for the `i`-th pair. -/
structure Rg1 (V₀ : Addr → Byte) (g₀ g : Gprs) (i : Nat) : Prop where
  rsp : g.rsp = g₀.rsp - 40#64
  rax : g.rax = BitVec.ofNat 64 i
  rcx : g.rcx = its V₀ g₀
  rsi : g.rsi = mI (nB V₀ g₀)
  rdi : g.rdi = BitVec.setWidth 64 (nB V₀ g₀)
  r12 : g.r12 = g₀.rdi
  r14 : g.r14 = g₀.r14
  r15 : g.r15 = g₀.r15

/-- The registers at the second loop for the `i`-th pair. -/
structure Rg2 (g₀ : Gprs) (idx : Nat) (g : Gprs) (i : Nat) : Prop where
  rsp : g.rsp = g₀.rsp - 40#64
  rbx : g.rbx = BitVec.ofNat 64 i
  rbp : g.rbp = BitVec.ofNat 64 idx
  r12 : g.r12 = g₀.rdi
  r13 : g.r13 = BitVec.ofNat 64 idx * 8#64
  r14 : g.r14 = g₀.r14
  r15 : g.r15 = g₀.r15

/-- The pushes: `Inv` with the entry's return address. -/
theorem inv1 (V₀ : Addr → Byte) (g₀ : Gprs) (hs : 48 ≤ g₀.rsp.toNat) (hs8 : g₀.rsp.toNat + 8 ≤ 2 ^ 64)
    (n8 : Cpt.RdOk F g₀.rsp (g₀.rdi + 8#64) 4) (it : 0 < nP V₀ g₀ → Cpt.RdOk F g₀.rsp g₀.rdi 8)
    (sl : ∀ k < nP V₀ g₀, Cpt.RdOk F g₀.rsp (slot V₀ g₀ k) 8) {ra : Addr} (hra : rdq(V₀, g₀.rsp) = ra) :
    Inv V₀ g₀ ra (Cpt.V1 V₀ g₀) := by
  obtain ⟨s8, s16, s24, s32⟩ := Cpt.sp_t g₀.rsp hs
  obtain ⟨e8, e16, e24, e32, -⟩ := Cpt.sp_e g₀.rsp
  have hl := g₀.rsp.isLt
  have ap : ∀ {x : Addr} {m : Nat}, Cpt.RdOk F g₀.rsp x m →
      List.map (Cpt.V1 V₀ g₀) (byteAddrs x m) = List.map V₀ (byteAddrs x m) := fun h =>
    Cpt.v1_rd V₀ g₀ hs h.fits (by have := h.apart; omega)
  refine ⟨⟨congrArg (ofBytesLE 32) (ap n8), fun h => congrArg (ofBytesLE 64) (ap (it h)),
    fun k hk => congrArg (ofBytesLE 64) (ap (sl k hk))⟩, ?_, ?_, ?_, ?_,
    (congrArg (ofBytesLE 64) (Cpt.v1_rd V₀ g₀ hs hs8 (Or.inr (Nat.le_refl _)))).trans hra⟩
  · rw [← e8]
    dsimp only [Cpt.V1]
    rw [Tun.rd_Vst _ (g₀.rsp - 8 - 8 - 8 - 8) (toBytesLE g₀.rbx 8) _ 8 (by rw [toBytesLE_length]; omega)
        (by omega) (by rw [toBytesLE_length]; omega),
      Tun.rd_Vst _ (g₀.rsp - 8 - 8 - 8) (toBytesLE g₀.rbp 8) _ 8 (by rw [toBytesLE_length]; omega)
        (by omega) (by rw [toBytesLE_length]; omega),
      Tun.rd_Vst _ (g₀.rsp - 8 - 8) (toBytesLE g₀.r12 8) _ 8 (by rw [toBytesLE_length]; omega)
        (by omega) (by rw [toBytesLE_length]; omega),
      Tun.rd_Vst_self _ _ _ (toBytesLE_length _ _) (by omega)]
    exact ofBytesLE_toBytesLE (n := 8) rfl _
  · rw [← e16]
    dsimp only [Cpt.V1]
    rw [Tun.rd_Vst _ (g₀.rsp - 8 - 8 - 8 - 8) (toBytesLE g₀.rbx 8) _ 8 (by rw [toBytesLE_length]; omega)
        (by omega) (by rw [toBytesLE_length]; omega),
      Tun.rd_Vst _ (g₀.rsp - 8 - 8 - 8) (toBytesLE g₀.rbp 8) _ 8 (by rw [toBytesLE_length]; omega)
        (by omega) (by rw [toBytesLE_length]; omega),
      Tun.rd_Vst_self _ _ _ (toBytesLE_length _ _) (by omega)]
    exact ofBytesLE_toBytesLE (n := 8) rfl _
  · rw [← e24]
    dsimp only [Cpt.V1]
    rw [Tun.rd_Vst _ (g₀.rsp - 8 - 8 - 8 - 8) (toBytesLE g₀.rbx 8) _ 8 (by rw [toBytesLE_length]; omega)
        (by omega) (by rw [toBytesLE_length]; omega),
      Tun.rd_Vst_self _ _ _ (toBytesLE_length _ _) (by omega)]
    exact ofBytesLE_toBytesLE (n := 8) rfl _
  · rw [← e32]
    dsimp only [Cpt.V1]
    rw [Tun.rd_Vst_self _ _ _ (toBytesLE_length _ _) (by omega)]
    exact ofBytesLE_toBytesLE (n := 8) rfl _

/-! ## The run -/

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ X : State} {o : Oracle} {t : Nat}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {V₀ : Addr → Byte} {g₀ : Gprs} {e₂ : Addr} {code₂ : List Byte} {j₂ : Nat}

/-- What the run needs around the function: its code and `CCensorNode::ExtendExclude`'s, the 48 bytes under the
entry's `S` it may store into, the 40 bytes from `S - 32` it reads (the registers pushed, the return address), and
the bytes of the pairs it reads (`Cpt.RdOk`). -/
structure Env (F : Footprint) (Wl : List Rgn) (L : List (Addr × List Byte)) (V₀ : Addr → Byte) (g₀ : Gprs) :
    Prop where
  code : CodeIn L eex_at eex
  ext : ∃ code, CodeIn L ext_at code ∧ 0 < code.length
  s0 : 48 ≤ g₀.rsp.toNat
  s8 : g₀.rsp.toNat + 8 ≤ 2 ^ 64
  w : ∀ i < 48, Foot Wl (Addr.add (g₀.rsp - 48#64) i)
  d : ∀ i < 40, Foot F.data (Addr.add (g₀.rsp - 32#64) i)
  n8 : Cpt.RdOk F g₀.rsp (g₀.rdi + 8#64) 4
  it : 0 < nP V₀ g₀ → Cpt.RdOk F g₀.rsp g₀.rdi 8
  sl : ∀ k < nP V₀ g₀, Cpt.RdOk F g₀.rsp (slot V₀ g₀ k) 8
  ln : ∀ k < nP V₀ g₀, Cpt.RdOk F g₀.rsp (itm V₀ g₀ k + 8#64) 4

/-- The pops' and the `ret`'s bytes. -/
theorem Env.ft (hE : Env F Wl L V₀ g₀) :
    (∀ m < 8, Foot F.data (Addr.add (g₀.rsp - 40#64 + 8#64) m)) ∧
    (∀ m < 8, Foot F.data (Addr.add (g₀.rsp - 40#64 + 8#64 + 8) m)) ∧
    (∀ m < 8, Foot F.data (Addr.add (g₀.rsp - 40#64 + 8#64 + 8 + 8) m)) ∧
    (∀ m < 8, Foot F.data (Addr.add (g₀.rsp - 40#64 + 8#64 + 8 + 8 + 8) m)) ∧
    (∀ m < 8, Foot F.data (Addr.add g₀.rsp m)) := by
  obtain ⟨-, -, -, -, a0, a8, a16, a24, a32⟩ := Cpt.sp_w g₀.rsp
  exact ⟨Cpt.off_ft hE.d 0 a0 (by decide), Cpt.off_ft hE.d 8 a8 (by decide), Cpt.off_ft hE.d 16 a16 (by decide),
    Cpt.off_ft hE.d 24 a24 (by decide), Cpt.off_ft hE.d 32 a32 (by decide)⟩

/-- The pushes' bytes. -/
theorem Env.wf (hE : Env F Wl L V₀ g₀) :
    (∀ m < 8, Foot Wl (Addr.add (g₀.rsp - 8) m)) ∧ (∀ m < 8, Foot Wl (Addr.add (g₀.rsp - 8 - 8) m)) ∧
    (∀ m < 8, Foot Wl (Addr.add (g₀.rsp - 8 - 8 - 8) m)) ∧
    (∀ m < 8, Foot Wl (Addr.add (g₀.rsp - 8 - 8 - 8 - 8) m)) := by
  obtain ⟨a40, a32, a24, a16, -⟩ := Cpt.sp_w g₀.rsp
  exact ⟨Cpt.off_ft hE.w 40 a40 (by decide), Cpt.off_ft hE.w 32 a32 (by decide),
    Cpt.off_ft hE.w 24 a24 (by decide), Cpt.off_ft hE.w 16 a16 (by decide)⟩

/-- What the function asks of `CCensorNode::ExtendExclude` (at `ext_at`) for the `i`-th pair, `i` not `index`:
from its entry with `rsp` = `S - 48`, the return address into the function there, `Inv` for the bytes `V` under it,
`rdi` the `i`-th pair's `Head` and `rsi` the `index`-th's, the run goes on to the goal if it does from every state at
the return address with `Inv`, `rsp` = `S - 40` and the registers a call keeps. -/
def Ext (prof : Profile) (F : Footprint) (Wl : List Rgn) (L : List (Addr × List Byte)) (s₀ : State) (o : Oracle)
    (gev : List Event) (gP : State → Nat → List Event → Prop) (gE : Outcome → List Event → Prop)
    (V₀ : Addr → Byte) (g₀ : Gprs) (ra : Addr) : Prop :=
  ∀ (idx i : Nat) (Y : State) (t : Nat) (V : Addr → Byte), Idx V₀ g₀ idx → i < nP V₀ g₀ → i ≠ idx →
    KeptW Wl s₀ Y → Inv V₀ g₀ ra V → Agree F Y.proc.mm.mem (Vst V (g₀.rsp - 48#64) (toBytesLE (eex_at.add 111) 8)) →
    Y.cpu.rip = ext_at → Y.cpu.gpr.rsp = g₀.rsp - 48#64 → Y.cpu.gpr.rdi = itm V₀ g₀ i + 16#64 →
    Y.cpu.gpr.rsi = itm V₀ g₀ idx + 16#64 →
    (∀ (Z : State) (t' : Nat) (V' : Addr → Byte), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V' → Inv V₀ g₀ ra V' →
      Z.cpu.rip = eex_at.add 111 → Z.cpu.gpr.rsp = g₀.rsp - 40#64 → Z.cpu.gpr.rbx = Y.cpu.gpr.rbx →
      Z.cpu.gpr.rbp = Y.cpu.gpr.rbp → Z.cpu.gpr.r12 = Y.cpu.gpr.r12 → Z.cpu.gpr.r13 = Y.cpu.gpr.r13 →
      Z.cpu.gpr.r14 = Y.cpu.gpr.r14 → Z.cpu.gpr.r15 = Y.cpu.gpr.r15 → GoG prof L o gev gP gE Z t') →
    GoG prof L o gev gP gE Y t

/-- What the caller asks at the return address `ra`: the bytes `Dat` and the registers a call keeps. -/
def Ret (prof : Profile) (F : Footprint) (Wl : List Rgn) (L : List (Addr × List Byte)) (s₀ : State) (o : Oracle)
    (gev : List Event) (gP : State → Nat → List Event → Prop) (gE : Outcome → List Event → Prop)
    (V₀ : Addr → Byte) (g₀ : Gprs) (ra : Addr) : Prop :=
  ∀ (Z : State) (t' : Nat) (V' : Addr → Byte), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V' → Dat V₀ g₀ V' →
    Z.cpu.rip = ra → Cpt.Bk g₀ Z.cpu.gpr → GoG prof L o gev gP gE Z t'

/-- From the first loop for the `i`-th pair, none of the ones before it with an empty prefix, the run goes on. -/
def At1 (prof : Profile) (F : Footprint) (Wl : List Rgn) (L : List (Addr × List Byte)) (s₀ : State) (o : Oracle)
    (gev : List Event) (gP : State → Nat → List Event → Prop) (gE : Outcome → List Event → Prop)
    (V₀ : Addr → Byte) (g₀ : Gprs) (ra : Addr) (i : Nat) : Prop :=
  ∀ (Y : State) (t : Nat) (V : Addr → Byte), KeptW Wl s₀ Y → Agree F Y.proc.mm.mem V → Inv V₀ g₀ ra V →
    Ln V₀ g₀ V → Y.cpu.rip = eex_at.add 55 → Rg1 V₀ g₀ Y.cpu.gpr i → (∀ k < i, ¬Emp V₀ g₀ k) →
    GoG prof L o gev gP gE Y t

/-- From 68 with `ebp` = `index`, the run goes on. -/
def At68 (prof : Profile) (F : Footprint) (Wl : List Rgn) (L : List (Addr × List Byte)) (s₀ : State) (o : Oracle)
    (gev : List Event) (gP : State → Nat → List Event → Prop) (gE : Outcome → List Event → Prop)
    (V₀ : Addr → Byte) (g₀ : Gprs) (ra : Addr) (idx : Nat) : Prop :=
  ∀ (Y : State) (t : Nat) (V : Addr → Byte), KeptW Wl s₀ Y → Agree F Y.proc.mm.mem V → Inv V₀ g₀ ra V →
    Y.cpu.rip = eex_at.add 68 → Y.cpu.gpr.rsp = g₀.rsp - 40#64 → Y.cpu.gpr.rbp = BitVec.ofNat 64 idx →
    Y.cpu.gpr.r12 = g₀.rdi → Y.cpu.gpr.r14 = g₀.r14 → Y.cpu.gpr.r15 = g₀.r15 → GoG prof L o gev gP gE Y t

/-- From the second loop for the `i`-th pair, the run goes on. -/
def At2 (prof : Profile) (F : Footprint) (Wl : List Rgn) (L : List (Addr × List Byte)) (s₀ : State) (o : Oracle)
    (gev : List Event) (gP : State → Nat → List Event → Prop) (gE : Outcome → List Event → Prop)
    (V₀ : Addr → Byte) (g₀ : Gprs) (ra : Addr) (idx i : Nat) : Prop :=
  ∀ (Y : State) (t : Nat) (V : Addr → Byte), KeptW Wl s₀ Y → Agree F Y.proc.mm.mem V → Inv V₀ g₀ ra V →
    Y.cpu.rip = eex_at.add 80 → Rg2 g₀ idx Y.cpu.gpr i → GoG prof L o gev gP gE Y t

/-- A `ret` (at `j`) with `rsp` = `S` and the registers a call keeps. -/
theorem fin (c : Seg prof F Wl L s₀ o) (hE : Env F Wl L V₀ g₀) (hin₂ : CodeIn L e₂ code₂)
    (h₂ : j₂ < code₂.length) (kE : Ret prof F Wl L s₀ o gev gP gE V₀ g₀ (e₂.add j₂)) {j : Nat} (hj : j < 151)
    (hd : Dec prof.feat eex j (FV7z.mk .ret 64 [] 1)) {Y : State} {V : Addr → Byte} (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem V) (hD : Dat V₀ g₀ V) (hra : rdq(V, g₀.rsp) = e₂.add j₂)
    (hr : Y.cpu.rip = eex_at.add j) (hs : Y.cpu.gpr.rsp = g₀.rsp) (hb : Y.cpu.gpr.rbx = g₀.rbx)
    (hp : Y.cpu.gpr.rbp = g₀.rbp) (h12 : Y.cpu.gpr.r12 = g₀.r12) (h13 : Y.cpu.gpr.r13 = g₀.r13)
    (h14 : Y.cpu.gpr.r14 = g₀.r14) (h15 : Y.cpu.gpr.r15 = g₀.r15) : GoG prof L o gev gP gE Y t := by
  refine c.s_ret hK hA hE.code (Eex.lt_len hj) hr hd (fun m hm => by rw [hs]; exact hE.ft.2.2.2.2 m hm) hin₂ h₂
    (by rw [hs]; exact hra) ?_
  rintro Z t' hKZ hAZ ⟨hrZ, hgZ⟩
  refine kE Z t' V hKZ hAZ hD hrZ ?_
  rw [hgZ]
  exact ⟨congrArg (· + 8) hs, hb, hp, h12, h13, h14, h15⟩

/-- The pops at 121 and the `ret` at 131, from `rsp` = `S - 40` and `Inv`. -/
theorem pop121 (c : Seg prof F Wl L s₀ o) (hE : Env F Wl L V₀ g₀) (hin₂ : CodeIn L e₂ code₂)
    (h₂ : j₂ < code₂.length) (kE : Ret prof F Wl L s₀ o gev gP gE V₀ g₀ (e₂.add j₂)) {Y : State}
    {V : Addr → Byte} (hK : KeptW Wl s₀ Y) (hA : Agree F Y.proc.mm.mem V) (hI : Inv V₀ g₀ (e₂.add j₂) V)
    (hr : Y.cpu.rip = eex_at.add 121) (hs : Y.cpu.gpr.rsp = g₀.rsp - 40#64) (h14 : Y.cpu.gpr.r14 = g₀.r14)
    (h15 : Y.cpu.gpr.r15 = g₀.r15) : GoG prof L o gev gP gE Y t := by
  obtain ⟨-, -, -, -, -, -, p0, p8, p16, p24, p32⟩ := Cpt.sp_e g₀.rsp
  obtain ⟨q0, q8, q16, q24, -⟩ := hE.ft
  refine (c_121 prof).run c hE.code (fun j' g' _ V' => j' = 131 ∧ g' = Cpt.gF V Y.cpu.gpr ∧ V' = V) hK hA hr
    (vc_121 (by rw [hs]; exact q0) (by rw [hs]; exact q8) (by rw [hs]; exact q16) (by rw [hs]; exact q24)) ?_
  rintro j' g fl V₂ ⟨rfl, rfl, hV₂⟩ Y₃ t₃ hK₃ hA₃ hr₃ hg₃ -
  subst V₂
  exact fin c hE hin₂ h₂ kE (by decide) (ret_131 _) hK₃ hA₃ hI.d hI.ra hr₃
    (by rw [hg₃]; show Y.cpu.gpr.rsp + 8#64 + 8 + 8 + 8 + 8 = _; rw [hs]; exact p32)
    (by rw [hg₃]; show rdq(V, Y.cpu.gpr.rsp + 8#64) = _; rw [hs, p0]; exact hI.rbx)
    (by rw [hg₃]; show rdq(V, Y.cpu.gpr.rsp + 8#64 + 8) = _; rw [hs, p8]; exact hI.rbp)
    (by rw [hg₃]; show rdq(V, Y.cpu.gpr.rsp + 8#64 + 8 + 8) = _; rw [hs, p16]; exact hI.r12)
    (by rw [hg₃]; show rdq(V, Y.cpu.gpr.rsp + 8#64 + 8 + 8 + 8) = _; rw [hs, p24]; exact hI.r13)
    (by rw [hg₃]; exact h14) (by rw [hg₃]; exact h15)

/-- After the `call` (111) for the `i`-th pair: the `i + 1`-th, or the pops at 121. -/
theorem aft {idx i : Nat} (c : Seg prof F Wl L s₀ o) (hE : Env F Wl L V₀ g₀) (hin₂ : CodeIn L e₂ code₂)
    (h₂ : j₂ < code₂.length) (kE : Ret prof F Wl L s₀ o gev gP gE V₀ g₀ (e₂.add j₂)) (hi : i < nP V₀ g₀)
    (kn : i + 1 < nP V₀ g₀ → At2 prof F Wl L s₀ o gev gP gE V₀ g₀ (e₂.add j₂) idx (i + 1)) {Y : State}
    {V : Addr → Byte} (hK : KeptW Wl s₀ Y) (hA : Agree F Y.proc.mm.mem V) (hI : Inv V₀ g₀ (e₂.add j₂) V)
    (hr : Y.cpu.rip = eex_at.add 111) (hR : Rg2 g₀ idx Y.cpu.gpr i) : GoG prof L o gev gP gE Y t := by
  have hn32 : nP V₀ g₀ < 2 ^ 32 := (nB V₀ g₀).isLt
  have hc : (BitVec.setWidth 32 Y.cpu.gpr.rbx + 1#32).toNat = i + 1 := by
    rw [hR.rbx]
    exact Cpt.e32 (by omega)
  have hn : rdd(V, Y.cpu.gpr.r12 + 8#64) = rdd(V₀, g₀.rdi + 8#64) := by rw [hR.r12, hI.d.n]
  have f8 : ∀ m < 4, Foot F.data (Addr.add (Y.cpu.gpr.r12 + 8#64) m) := fun m hm => by
    rw [hR.r12]
    exact hE.n8.ft m hm
  by_cases hlt : i + 1 < nP V₀ g₀
  · refine (c_111 prof).run c hE.code (fun j' g' _ V' => j' = 80 ∧ g' = gI Y.cpu.gpr ∧ V' = V) hK hA hr
      (vc_111l (by rw [hc, hn]; exact hlt) f8) ?_
    rintro j' g fl V₁ ⟨rfl, rfl, hV₁⟩ Y₁ t₁ hK₁ hA₁ hr₁ hg₁ -
    subst V₁
    have hbx : (gI Y.cpu.gpr).rbx = BitVec.ofNat 64 (i + 1) := by
      show BitVec.setWidth 64 (BitVec.setWidth 32 Y.cpu.gpr.rbx + 1#32) = _
      rw [hR.rbx]
      exact Cpt.inc32 (by omega)
    refine kn hlt Y₁ t₁ V hK₁ hA₁ hI hr₁ ?_
    rw [hg₁]
    exact ⟨hR.rsp, hbx, hR.rbp, hR.r12, hR.r13, hR.r14, hR.r15⟩
  · refine (c_111 prof).run c hE.code (fun j' g' _ V' => j' = 121 ∧ g' = gI Y.cpu.gpr ∧ V' = V) hK hA hr
      (vc_111e (by rw [hc, hn]; exact hlt) f8) ?_
    rintro j' g fl V₁ ⟨rfl, rfl, hV₁⟩ Y₁ t₁ hK₁ hA₁ hr₁ hg₁ -
    subst V₁
    exact pop121 c hE hin₂ h₂ kE hK₁ hA₁ hI hr₁ (by rw [hg₁]; exact hR.rsp) (by rw [hg₁]; exact hR.r14)
      (by rw [hg₁]; exact hR.r15)

/-- The second loop's `i`-th pair: skipped (`index`), or the `call`; then `aft`. -/
theorem lp2Head {idx i : Nat} (c : Seg prof F Wl L s₀ o) (hE : Env F Wl L V₀ g₀) (hin₂ : CodeIn L e₂ code₂)
    (h₂ : j₂ < code₂.length) (hext : Ext prof F Wl L s₀ o gev gP gE V₀ g₀ (e₂.add j₂))
    (kE : Ret prof F Wl L s₀ o gev gP gE V₀ g₀ (e₂.add j₂)) (hx : Idx V₀ g₀ idx) (hi : i < nP V₀ g₀)
    (kn : i + 1 < nP V₀ g₀ → At2 prof F Wl L s₀ o gev gP gE V₀ g₀ (e₂.add j₂) idx (i + 1)) :
    At2 prof F Wl L s₀ o gev gP gE V₀ g₀ (e₂.add j₂) idx i := by
  intro Y t V hK hA hI hr hR
  have hn32 : nP V₀ g₀ < 2 ^ 32 := (nB V₀ g₀).isLt
  have hn : 0 < nP V₀ g₀ := by omega
  have hidx : idx < nP V₀ g₀ := hx.1
  obtain ⟨-, -, -, -, -, x48, -⟩ := Cpt.sp_e g₀.rsp
  have hq : BitVec.setWidth 32 Y.cpu.gpr.rbx = BitVec.setWidth 32 Y.cpu.gpr.rbp ↔ i = idx := by
    rw [hR.rbx, hR.rbp]
    exact sw_iff (by omega) (by omega)
  by_cases he : i = idx
  · -- skipped
    refine (c_80 prof).run c hE.code (fun j' g' _ V' => j' = 111 ∧ g' = Y.cpu.gpr ∧ V' = V) hK hA hr
      (vc_80s (hq.2 he)) ?_
    rintro j' g fl V₁ ⟨rfl, rfl, hV₁⟩ Y₁ t₁ hK₁ hA₁ hr₁ hg₁ -
    subst V₁
    exact aft c hE hin₂ h₂ kE hi kn hK₁ hA₁ hI hr₁ (by rw [hg₁]; exact hR)
  have ea : rdq(V, Y.cpu.gpr.r12) + BitVec.setWidth 64 (BitVec.setWidth 32 Y.cpu.gpr.rbx) * 8#64 =
      slot V₀ g₀ i := by
    rw [hR.r12, hI.d.it hn, hR.rbx, Cpt.sw32 (i := i) (by omega)]
  have eb : rdq(V, Y.cpu.gpr.r12) + Y.cpu.gpr.r13 = slot V₀ g₀ idx := by
    rw [hR.r12, hI.d.it hn, hR.r13]
  -- to the `call`
  refine (c_80 prof).run c hE.code (fun j' g' _ V' => j' = 106 ∧ g' = gC V Y.cpu.gpr ∧ V' = V) hK hA hr
    (vc_80c (fun h => he (hq.1 h)) (fun m hm => by rw [hR.r12]; exact (hE.it hn).ft m hm)
      (fun m hm => by rw [eb]; exact (hE.sl idx hidx).ft m hm) (fun m hm => by rw [ea]; exact (hE.sl i hi).ft m hm))
    ?_
  rintro j' g fl V₁ ⟨rfl, rfl, hV₁⟩ Y₁ t₁ hK₁ hA₁ hr₁ hg₁ -
  subst V₁
  obtain ⟨codeC, hinC, hC0⟩ := hE.ext
  have hsY : Y₁.cpu.gpr.rsp = g₀.rsp - 40#64 := by rw [hg₁]; exact hR.rsp
  refine c.s_call hK₁ hA₁ hE.code (Eex.lt_len (by decide)) hr₁ (call_106 _) hinC hC0 tgt106
    (fun m hm => by rw [hsY, x48]; exact hE.w m (by omega)) ?_
  rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
  rw [hsY, x48] at hA₂
  have hg₂' : Y₂.cpu.gpr = (gC V Y.cpu.gpr).set 4 (g₀.rsp - 48#64) := by
    rw [hg₂, hg₁]
    exact congrArg (fun v => (gC V Y.cpu.gpr).set 4 v) ((congrArg (· - 8) hR.rsp).trans x48)
  -- `CCensorNode::ExtendExclude`
  refine hext idx i Y₂ t₂ V hx hi he hK₂ hI hA₂ hr₂ (by rw [hg₂']; rfl)
    (by rw [hg₂']; show rdq(V, rdq(V, Y.cpu.gpr.r12) + _ * 8#64) + 16#64 = _; rw [ea, hI.d.sl i hi])
    (by rw [hg₂']; show rdq(V, rdq(V, Y.cpu.gpr.r12) + Y.cpu.gpr.r13) + 16#64 = _; rw [eb, hI.d.sl idx hidx]) ?_
  intro Z t' V' hKZ hAZ hI' hrZ zs hzb hzp hz12 hz13 hz14 hz15
  rw [hg₂'] at hzb hzp hz12 hz13 hz14 hz15
  exact aft c hE hin₂ h₂ kE hi kn hKZ hAZ hI' hrZ ⟨zs, hzb.trans hR.rbx, hzp.trans hR.rbp, hz12.trans hR.r12,
    hz13.trans hR.r13, hz14.trans hR.r14, hz15.trans hR.r15⟩

/-- The second loop from any pair: by the number left. -/
theorem lp2All {idx : Nat} (c : Seg prof F Wl L s₀ o) (hE : Env F Wl L V₀ g₀) (hin₂ : CodeIn L e₂ code₂)
    (h₂ : j₂ < code₂.length) (hext : Ext prof F Wl L s₀ o gev gP gE V₀ g₀ (e₂.add j₂))
    (kE : Ret prof F Wl L s₀ o gev gP gE V₀ g₀ (e₂.add j₂)) (hx : Idx V₀ g₀ idx) :
    ∀ (m i : Nat), i + m + 1 = nP V₀ g₀ → At2 prof F Wl L s₀ o gev gP gE V₀ g₀ (e₂.add j₂) idx i
  | 0, _, h => lp2Head c hE hin₂ h₂ hext kE hx (by omega) fun h' => absurd h' (by omega)
  | m + 1, i, h => lp2Head c hE hin₂ h₂ hext kE hx (by omega) fun _ =>
    lp2All c hE hin₂ h₂ hext kE hx m (i + 1) (by omega)

/-- Found `index`: 68, then the second loop from the first pair. -/
theorem found {idx : Nat} (c : Seg prof F Wl L s₀ o) (hE : Env F Wl L V₀ g₀) (hin₂ : CodeIn L e₂ code₂)
    (h₂ : j₂ < code₂.length) (hext : Ext prof F Wl L s₀ o gev gP gE V₀ g₀ (e₂.add j₂))
    (kE : Ret prof F Wl L s₀ o gev gP gE V₀ g₀ (e₂.add j₂)) (hx : Idx V₀ g₀ idx) :
    At68 prof F Wl L s₀ o gev gP gE V₀ g₀ (e₂.add j₂) idx := by
  intro Y t V hK hA hI hr hs hb h12 h14 h15
  have hn32 : nP V₀ g₀ < 2 ^ 32 := (nB V₀ g₀).isLt
  have hidx : idx < nP V₀ g₀ := hx.1
  refine (c_68 prof).run c hE.code (fun j' g' _ V' => j' = 80 ∧ g' = g80 Y.cpu.gpr ∧ V' = V) hK hA hr vc_68 ?_
  rintro j' g fl V₁ ⟨rfl, rfl, hV₁⟩ Y₁ t₁ hK₁ hA₁ hr₁ hg₁ -
  subst V₁
  have h13 : (g80 Y.cpu.gpr).r13 = BitVec.ofNat 64 idx * 8#64 := by
    show BitVec.setWidth 64 (BitVec.setWidth 32 Y.cpu.gpr.rbp) <<< 3 = _
    rw [hb]
    exact shl3 (by omega)
  refine lp2All c hE hin₂ h₂ hext kE hx (nP V₀ g₀ - 1) 0 (by omega) Y₁ t₁ V hK₁ hA₁ hI hr₁ ?_
  rw [hg₁]
  exact ⟨hs, rfl, hb, h12, h13, h14, h15⟩

/-- The first loop's `i`-th pair: found (to 68), the `i + 1`-th, or the pops and the `ret` at 150. -/
theorem lp1Head {i : Nat} (c : Seg prof F Wl L s₀ o) (hE : Env F Wl L V₀ g₀) (hin₂ : CodeIn L e₂ code₂)
    (h₂ : j₂ < code₂.length) (hf : ∀ idx, Idx V₀ g₀ idx → At68 prof F Wl L s₀ o gev gP gE V₀ g₀ (e₂.add j₂) idx)
    (kE : Ret prof F Wl L s₀ o gev gP gE V₀ g₀ (e₂.add j₂)) (hi : i < nP V₀ g₀)
    (kn : i + 1 < nP V₀ g₀ → At1 prof F Wl L s₀ o gev gP gE V₀ g₀ (e₂.add j₂) (i + 1)) :
    At1 prof F Wl L s₀ o gev gP gE V₀ g₀ (e₂.add j₂) i := by
  intro Y t V hK hA hI hL hr hR hno
  have hn32 : nP V₀ g₀ < 2 ^ 32 := (nB V₀ g₀).isLt
  have hn : 0 < nP V₀ g₀ := by omega
  obtain ⟨-, -, -, -, -, -, p0, p8, p16, p24, p32⟩ := Cpt.sp_e g₀.rsp
  obtain ⟨q0, q8, q16, q24, -⟩ := hE.ft
  have ea : Y.cpu.gpr.rcx + Y.cpu.gpr.rax * 8#64 = slot V₀ g₀ i := by rw [hR.rcx, hR.rax]
  have eb : rdq(V, Y.cpu.gpr.rcx + Y.cpu.gpr.rax * 8#64) = itm V₀ g₀ i := by rw [ea, hI.d.sl i hi]
  have el : rdd(V, rdq(V, Y.cpu.gpr.rcx + Y.cpu.gpr.rax * 8#64) + 8#64) = rdd(V₀, itm V₀ g₀ i + 8#64) := by
    rw [eb, hL i hi]
  have f1 : ∀ m < 8, Foot F.data (Addr.add (Y.cpu.gpr.rcx + Y.cpu.gpr.rax * 8#64) m) := fun m hm => by
    rw [ea]
    exact (hE.sl i hi).ft m hm
  have f2 : ∀ m < 4, Foot F.data (Addr.add (rdq(V, Y.cpu.gpr.rcx + Y.cpu.gpr.rax * 8#64) + 8#64) m) :=
    fun m hm => by
      rw [eb]
      exact (hE.ln i hi).ft m hm
  by_cases hm : Emp V₀ g₀ i
  · -- found: to 68
    refine (c_55 prof).run c hE.code (fun j' g' _ V' => j' = 68 ∧ g' = gFd V Y.cpu.gpr ∧ V' = V) hK hA hr
      (vc_55f (by rw [el]; exact hm) f1 f2) ?_
    rintro j' g fl V₁ ⟨rfl, rfl, hV₁⟩ Y₁ t₁ hK₁ hA₁ hr₁ hg₁ -
    subst V₁
    have hbp : (gFd V Y.cpu.gpr).rbp = BitVec.ofNat 64 i := by
      show BitVec.setWidth 64 (BitVec.setWidth 32 Y.cpu.gpr.rax) = _
      rw [hR.rax]
      exact Cpt.sw32 (by omega)
    exact hf i ⟨hi, hm, hno⟩ Y₁ t₁ V hK₁ hA₁ hI hr₁ (by rw [hg₁]; exact hR.rsp) (by rw [hg₁]; exact hbp)
      (by rw [hg₁]; exact hR.r12) (by rw [hg₁]; exact hR.r14) (by rw [hg₁]; exact hR.r15)
  have hl : ¬rdd(V, rdq(V, Y.cpu.gpr.rcx + Y.cpu.gpr.rax * 8#64) + 8#64) = 0#32 := by
    rw [el]
    exact hm
  have hsi : Y.cpu.gpr.rsi = BitVec.ofNat 64 (nP V₀ g₀ - 1) := by
    rw [hR.rsi]
    exact mI_eq (x := nB V₀ g₀) rfl hn
  by_cases hlt : i + 1 < nP V₀ g₀
  · -- the next pair
    refine (c_55 prof).run c hE.code (fun j' g' _ V' => j' = 55 ∧ g' = gL Y.cpu.gpr ∧ V' = V) hK hA hr
      (vc_55n hl (by rw [hR.rax, hsi]; exact ofNat_ne (by omega) (by omega) (by omega)) f1 f2) ?_
    rintro j' g fl V₁ ⟨rfl, rfl, hV₁⟩ Y₁ t₁ hK₁ hA₁ hr₁ hg₁ -
    subst V₁
    have hax : (gL Y.cpu.gpr).rax = BitVec.ofNat 64 (i + 1) := by
      show Y.cpu.gpr.rax + 1#64 = _
      rw [hR.rax]
      exact add1 i
    refine kn hlt Y₁ t₁ V hK₁ hA₁ hI hL hr₁ ?_ ?_
    · rw [hg₁]
      exact ⟨hR.rsp, hax, hR.rcx, hR.rsi, hR.rdi, hR.r12, hR.r14, hR.r15⟩
    · intro k hk
      rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | rfl
      · exact hno k hk
      · exact hm
  · -- none: the pops, the `ret` at 150
    have heq : Y.cpu.gpr.rax = Y.cpu.gpr.rsi := by
      rw [hR.rax, hsi]
      exact congrArg (BitVec.ofNat 64) (by omega)
    have hb : BitVec.setWidth 32 (Y.cpu.gpr.rax + 1#64) = BitVec.setWidth 32 Y.cpu.gpr.rdi := by
      rw [hR.rax, hR.rdi]
      exact lea_n (x := nB V₀ g₀) rfl (by show i + 1 = nP V₀ g₀; omega)
    refine (c_55 prof).run c hE.code (fun j' g' _ V' => j' = 150 ∧ g' = gR V Y.cpu.gpr ∧ V' = V) hK hA hr
      (vc_55e hl heq hb f1 f2 (by rw [hR.rsp]; exact q0) (by rw [hR.rsp]; exact q8) (by rw [hR.rsp]; exact q16)
        (by rw [hR.rsp]; exact q24)) ?_
    rintro j' g fl V₁ ⟨rfl, rfl, hV₁⟩ Y₃ t₃ hK₃ hA₃ hr₃ hg₃ -
    subst V₁
    exact fin c hE hin₂ h₂ kE (by decide) (ret_150 _) hK₃ hA₃ hI.d hI.ra hr₃
      (by rw [hg₃]; show Y.cpu.gpr.rsp + 8#64 + 8 + 8 + 8 + 8 = _; rw [hR.rsp]; exact p32)
      (by rw [hg₃]; show rdq(V, Y.cpu.gpr.rsp + 8#64) = _; rw [hR.rsp, p0]; exact hI.rbx)
      (by rw [hg₃]; show rdq(V, Y.cpu.gpr.rsp + 8#64 + 8) = _; rw [hR.rsp, p8]; exact hI.rbp)
      (by rw [hg₃]; show rdq(V, Y.cpu.gpr.rsp + 8#64 + 8 + 8) = _; rw [hR.rsp, p16]; exact hI.r12)
      (by rw [hg₃]; show rdq(V, Y.cpu.gpr.rsp + 8#64 + 8 + 8 + 8) = _; rw [hR.rsp, p24]; exact hI.r13)
      (by rw [hg₃]; exact hR.r14) (by rw [hg₃]; exact hR.r15)

/-- The first loop from any pair: by the number left. -/
theorem lp1All (c : Seg prof F Wl L s₀ o) (hE : Env F Wl L V₀ g₀) (hin₂ : CodeIn L e₂ code₂)
    (h₂ : j₂ < code₂.length) (hf : ∀ idx, Idx V₀ g₀ idx → At68 prof F Wl L s₀ o gev gP gE V₀ g₀ (e₂.add j₂) idx)
    (kE : Ret prof F Wl L s₀ o gev gP gE V₀ g₀ (e₂.add j₂)) :
    ∀ (m i : Nat), i + m + 1 = nP V₀ g₀ → At1 prof F Wl L s₀ o gev gP gE V₀ g₀ (e₂.add j₂) i
  | 0, _, h => lp1Head c hE hin₂ h₂ hf kE (by omega) fun h' => absurd h' (by omega)
  | m + 1, i, h => lp1Head c hE hin₂ h₂ hf kE (by omega) fun _ => lp1All c hE hin₂ h₂ hf kE m (i + 1) (by omega)

/-- `CCensor::ExtendExclude ()` (`this` = `rdi`, the entry's bytes `V`): if `CCensorNode::ExtendExclude` runs as
`Ext` says for each pair but `index` (the first with an empty prefix, `Idx`), the run reaches the return address
with the bytes it read as they were and the registers a call keeps; with no pair with an empty prefix it calls
nothing. -/
theorem eex_ok (c : Seg prof F Wl L s₀ o) {V : Addr → Byte} (hE : Env F Wl L V X.cpu.gpr) (hK : KeptW Wl s₀ X)
    (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = eex_at) (hin₂ : CodeIn L e₂ code₂) (h₂ : j₂ < code₂.length)
    (hra : rdq(V, X.cpu.gpr.rsp) = e₂.add j₂) (hext : Ext prof F Wl L s₀ o gev gP gE V X.cpu.gpr (e₂.add j₂))
    (kE : Ret prof F Wl L s₀ o gev gP gE V X.cpu.gpr (e₂.add j₂)) :
    GoG prof L o gev gP gE X t := by
  obtain ⟨-, -, -, -, x40, -⟩ := Cpt.sp_e X.cpu.gpr.rsp
  obtain ⟨w1, w2, w3, w4⟩ := hE.wf
  have hI := inv1 V X.cpu.gpr hE.s0 hE.s8 hE.n8 hE.it hE.sl hra
  have hrd := hI.d.n
  have hL : Ln V X.cpu.gpr (Cpt.V1 V X.cpu.gpr) := fun k hk =>
    congrArg (ofBytesLE 32) (Cpt.v1_rd V X.cpu.gpr hE.s0 (hE.ln k hk).fits (by have := (hE.ln k hk).apart; omega))
  by_cases h0 : rdd(Cpt.V1 V X.cpu.gpr, X.cpu.gpr.rdi + 8#64) = 0#32
  · -- no pairs: the pops at 121
    refine (c_0 prof).run c hE.code (fun j' g' _ V' => j' = 121 ∧ g' = g0z V X.cpu.gpr ∧ V' = Cpt.V1 V X.cpu.gpr)
      hK hA (by rw [addr_add_zero]; exact hrip) (vc_0z h0 w1 w2 w3 w4 hE.n8.ft) ?_
    rintro j' g fl V₁ ⟨rfl, hg, hV₁⟩ Y t₁ hKY hAY hrY hgY -
    subst V₁
    have hR : Y.cpu.gpr.rsp = X.cpu.gpr.rsp - 40#64 ∧ Y.cpu.gpr.r14 = X.cpu.gpr.r14 ∧
        Y.cpu.gpr.r15 = X.cpu.gpr.r15 := by
      rw [hgY, hg]
      exact ⟨x40, rfl, rfl⟩
    exact pop121 c hE hin₂ h₂ kE hKY hAY hI hrY hR.1 hR.2.1 hR.2.2
  · -- the first loop from the first pair
    have hn : 0 < nP V X.cpu.gpr := by
      have : rdd(Cpt.V1 V X.cpu.gpr, X.cpu.gpr.rdi + 8#64).toNat ≠ 0 := fun h => h0 (BitVec.eq_of_toNat_eq h)
      show 0 < rdd(V, X.cpu.gpr.rdi + 8#64).toNat
      rw [← hrd]
      omega
    refine (c_0 prof).run c hE.code (fun j' g' _ V' => j' = 55 ∧ g' = g55 V X.cpu.gpr ∧ V' = Cpt.V1 V X.cpu.gpr)
      hK hA (by rw [addr_add_zero]; exact hrip) (vc_0n h0 w1 w2 w3 w4 hE.n8.ft (hE.it hn).ft) ?_
    rintro j' g fl V₁ ⟨rfl, hg, hV₁⟩ Y t₁ hKY hAY hrY hgY -
    subst V₁
    have hR : Rg1 V X.cpu.gpr Y.cpu.gpr 0 := by
      rw [hgY, hg]
      exact ⟨x40, rfl, hI.d.it hn, congrArg mI hrd, congrArg (BitVec.setWidth 64) hrd, rfl, rfl, rfl⟩
    exact lp1All c hE hin₂ h₂ (fun idx hx => found c hE hin₂ h₂ hext kE hx) kE (nP V X.cpu.gpr - 1) 0 (by omega)
      Y t₁ _ hKY hAY hI hL hrY hR (fun k hk => absurd hk (Nat.not_lt_zero k))

end FV7z.Eex
