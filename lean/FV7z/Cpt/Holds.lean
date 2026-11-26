import FV7z.Cpt.Cuts
import FV7z.Lemmas.LeafRet
import FV7z.Lemmas.SpCallK
import FV7z.Tun.Inv
/-!
# `NWildcard::CCensorNode::CheckPathCurrent` (PLAN.md §M, M1)

7-Zip 26.06's `NWildcard::CCensorNode::CheckPathCurrent (include, pathParts, isFile)` at `0x453050` in `7zzs`
(`CPP/Common/Wildcard.cpp`; `objdump -d`): `const CObjectVector<CItem> &items = include ? IncludeItems :
ExcludeItems; FOR_VECTOR (i, items) if (items[i].CheckPath (pathParts, isFile)) return true; return false;`
(`this` = `rdi`, `include` = `sil`, `pathParts` = `rdx`, `isFile` = `cl`; `CItem::CheckPath` at `0x4529d0`, called
at 74).

`push r13; push r12; push rbp; push rbx; sub rsp, 8`, `r13` the vector (`this + 40`, or `this + 56` when `include` is
0: the `cmove`), `r12` = `i` = 0, `rbp` = `pathParts`, `ebx` = `isFile` (`vc_0n`, `vc_0z`). No items: `eax` = 0, the
pops and the `ret` at 108 (`vc_96`). The loop's body (58): `rdi` the `i`-th item, `rsi` = `pathParts`, `edx` =
`isFile` (`vc_58`), the `call` (74). `CheckPath` is a hypothesis (`Chk`) for each item, as in `FV7z.Ffp`. After it
(79): `al` not 0 is the answer, the pops and the `ret` at 93 (`vc_79f`); else `i + 1` and back to 58 while below the
count (`vc_79n`), or to 96 (`vc_79e`). `lpHead` is one item, `lpAll` the items from any one by the number left,
`cpt_ok` the function (`Res`).
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Cpt

/-! ## The instructions outside the blocks -/

def pc74 : List Byte := [0xe8, 0x31, 0xf9, 0xff, 0xff]
def pret : List Byte := [0xc3]
theorem pc74_0 : ∀ feat, Dec feat pc74 0 (FV7z.mk .call 64 [.rel 18446744073709549873] 5) := by dec_rfl
theorem pret_0 : ∀ feat, Dec feat pret 0 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem wc74 : pc74 <+: cpt.drop 74 := by decide +kernel
theorem w_93 : pret <+: cpt.drop 93 := by decide +kernel
theorem w_108 : pret <+: cpt.drop 108 := by decide +kernel
theorem call_74 (feat : Features) : Dec feat cpt 74 (FV7z.mk .call 64 [.rel 18446744073709549873] 5) :=
  Dec.shift (j := 74) (k := 0) (pc74_0 feat) wc74 (Nat.zero_le _)
theorem ret_93 (feat : Features) : Dec feat cpt 93 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 93) (k := 0) (pret_0 feat) w_93 (Nat.zero_le _)
theorem ret_108 (feat : Features) : Dec feat cpt 108 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 108) (k := 0) (pret_0 feat) w_108 (Nat.zero_le _)

/-- `CItem::CheckPath`. -/
abbrev chk_at : Addr := 0x4529d0
theorem tgt74 : cpt_at.add (74 + 5) + BitVec.ofNat 64 18446744073709549873 = chk_at := by decide

/-! ## The pieces -/

/-- The four registers pushed. -/
abbrev V1 (V : Addr → Byte) (g : Gprs) : Addr → Byte :=
  Vst (Vst (Vst (Vst V (g.rsp - 8) (toBytesLE g.r13 8)) (g.rsp - 8 - 8) (toBytesLE g.r12 8)) (g.rsp - 8 - 8 - 8)
    (toBytesLE g.rbp 8)) (g.rsp - 8 - 8 - 8 - 8) (toBytesLE g.rbx 8)
/-- `isFile`, zero-extended. -/
abbrev isF (g : Gprs) : BitVec 64 := BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.setWidth 8 g.rcx))
/-- The registers after the entry's block, `v` the vector. -/
abbrev g58 (V : Addr → Byte) (g : Gprs) (v : Addr) : Gprs :=
  { g with
    rax := BitVec.setWidth 64 rdd(V1 V g, v + 8#64), rbx := isF g, rsp := g.rsp - 8 - 8 - 8 - 8 - 8#64,
    rbp := g.rdx, rdi := g.rdi + 56#64, r12 := 0#64, r13 := v }
/-- The registers at the `call`. -/
abbrev gC (V : Addr → Byte) (g : Gprs) : Gprs :=
  { g with
    rax := BitVec.setWidth 64 (BitVec.setWidth 32 g.r12), rdx := BitVec.setWidth 64 (BitVec.setWidth 32 g.rbx),
    rsi := g.rbp, rdi := rdq(V, rdq(V, g.r13) + BitVec.setWidth 64 (BitVec.setWidth 32 g.r12) * 8#64) }
/-- The pops: the `ret` at 93. -/
abbrev gF (V : Addr → Byte) (g : Gprs) : Gprs :=
  { g with
    rbx := rdq(V, g.rsp + 8#64), rbp := rdq(V, g.rsp + 8#64 + 8), r12 := rdq(V, g.rsp + 8#64 + 8 + 8),
    r13 := rdq(V, g.rsp + 8#64 + 8 + 8 + 8), rsp := g.rsp + 8#64 + 8 + 8 + 8 + 8 }
/-- `i + 1`. -/
abbrev gN (g : Gprs) : Gprs := { g with r12 := BitVec.setWidth 64 (BitVec.setWidth 32 g.r12 + 1#32) }
/-- `eax` = 0 and the pops: the `ret` at 108. -/
abbrev gX (V : Addr → Byte) (g : Gprs) : Gprs :=
  { g with
    rax := 0#64, rbx := rdq(V, g.rsp + 8#64), rbp := rdq(V, g.rsp + 8#64 + 8), r12 := rdq(V, g.rsp + 8#64 + 8 + 8),
    r13 := rdq(V, g.rsp + 8#64 + 8 + 8 + 8), rsp := g.rsp + 8#64 + 8 + 8 + 8 + 8 }

variable {F : Footprint} {Wl : List Rgn}

/-- The entry, items: to the loop's body. -/
theorem vc_0n {g : Gprs} {f : Rflags} {V : Addr → Byte} {v : Addr}
    (hv : (BitVec.setWidth 8 g.rsi = 0 ∧ v = g.rdi + 56#64) ∨ (¬BitVec.setWidth 8 g.rsi = 0 ∧ v = g.rdi + 40#64))
    (h : rdd(V1 V g, v + 8#64) ≠ 0#32)
    (hs1 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8) i)) (hs2 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8) i))
    (hs3 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8 - 8) i))
    (hs4 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8 - 8 - 8) i))
    (f8 : ∀ i < 4, Foot F.data (Addr.add (v + 8#64) i)) :
    W_0 F Wl (fun j' g' _ V' => j' = 58 ∧ g' = g58 V g v ∧ V' = V1 V g) g f V := by
  rcases hv with ⟨hs, rfl⟩ | ⟨hs, rfl⟩
  · obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
    dsimp only [g58, isF, V1] at hs h f8 hs1 hs2 hs3 hs4 ⊢
    wpx [W_0, W_46, o0, Op.cmov64, Op.zxr, hs, lf_xz, BitVec.xor_self, BitVec.setWidth_zero, BitVec.and_self,
      beq_iff_eq, beq_eq_false_iff_ne, ne_eq, beq_self_eq_true, not_true_eq_false, not_false_eq_true, false_implies,
      Bool.true_eq_false, Bool.false_eq_true, implies_true, Bool.not_eq_true', decide_eq_true_eq,
      decide_eq_false_iff_not, ↓reduceIte]
    all_goals repeat' (first
      | exact rfl
      | assumption
      | exact trivial
      | (intro hh; exact absurd hh h)
      | (intro hh; exact absurd hh (by decide))
      | apply And.intro
      | intro _)
  · obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
    dsimp only [g58, isF, V1] at hs h f8 hs1 hs2 hs3 hs4 ⊢
    wpx [W_0, W_46, o0, Op.cmov64, Op.zxr, hs, beq_eq_false_iff_ne.2 hs, lf_xz, BitVec.xor_self,
      BitVec.setWidth_zero, BitVec.and_self, beq_iff_eq, beq_eq_false_iff_ne, ne_eq, beq_self_eq_true,
      not_true_eq_false, not_false_eq_true, false_implies, Bool.true_eq_false, Bool.false_eq_true, implies_true,
      Bool.not_eq_true', decide_eq_true_eq, decide_eq_false_iff_not, ↓reduceIte]
    all_goals repeat' (first
      | exact rfl
      | assumption
      | exact trivial
      | (intro hh; exact absurd hh h)
      | (intro hh; exact absurd hh hs)
      | (intro hh; exact absurd hh (by decide))
      | apply And.intro
      | intro _)

/-- The entry, no items: to 96. -/
theorem vc_0z {g : Gprs} {f : Rflags} {V : Addr → Byte} {v : Addr}
    (hv : (BitVec.setWidth 8 g.rsi = 0 ∧ v = g.rdi + 56#64) ∨ (¬BitVec.setWidth 8 g.rsi = 0 ∧ v = g.rdi + 40#64))
    (h : rdd(V1 V g, v + 8#64) = 0#32)
    (hs1 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8) i)) (hs2 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8) i))
    (hs3 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8 - 8) i))
    (hs4 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8 - 8 - 8) i))
    (f8 : ∀ i < 4, Foot F.data (Addr.add (v + 8#64) i)) :
    W_0 F Wl (fun j' g' _ V' => j' = 96 ∧ g' = g58 V g v ∧ V' = V1 V g) g f V := by
  rcases hv with ⟨hs, rfl⟩ | ⟨hs, rfl⟩
  · obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
    dsimp only [g58, isF, V1] at hs h f8 hs1 hs2 hs3 hs4 ⊢
    wpx [W_0, W_46, o0, Op.cmov64, Op.zxr, hs, h, lf_xz, BitVec.xor_self, BitVec.setWidth_zero, BitVec.and_self,
      beq_iff_eq, beq_eq_false_iff_ne, ne_eq, beq_self_eq_true, not_true_eq_false, not_false_eq_true, false_implies,
      Bool.true_eq_false, Bool.false_eq_true, implies_true, Bool.not_eq_true', decide_eq_true_eq,
      decide_eq_false_iff_not, ↓reduceIte]
    all_goals repeat' (first
      | exact rfl
      | assumption
      | exact trivial
      | (intro hh; exact absurd h hh)
      | (intro hh; exact absurd hh (by decide))
      | apply And.intro
      | intro _)
  · obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
    dsimp only [g58, isF, V1] at hs h f8 hs1 hs2 hs3 hs4 ⊢
    wpx [W_0, W_46, o0, Op.cmov64, Op.zxr, hs, beq_eq_false_iff_ne.2 hs, h, lf_xz, BitVec.xor_self,
      BitVec.setWidth_zero, BitVec.and_self, beq_iff_eq, beq_eq_false_iff_ne, ne_eq, beq_self_eq_true,
      not_true_eq_false, not_false_eq_true, false_implies, Bool.true_eq_false, Bool.false_eq_true, implies_true,
      Bool.not_eq_true', decide_eq_true_eq, decide_eq_false_iff_not, ↓reduceIte]
    all_goals repeat' (first
      | exact rfl
      | assumption
      | exact trivial
      | (intro hh; exact absurd h hh)
      | (intro hh; exact absurd hh hs)
      | (intro hh; exact absurd hh (by decide))
      | apply And.intro
      | intro _)

/-- The loop's body to the `call`. -/
theorem vc_58 {g : Gprs} {f : Rflags} {V : Addr → Byte} (f13 : ∀ i < 8, Foot F.data (Addr.add g.r13 i))
    (fi : ∀ i < 8, Foot F.data (Addr.add (rdq(V, g.r13) + BitVec.setWidth 64 (BitVec.setWidth 32 g.r12) * 8#64) i)) :
    W_58 F Wl (fun j' g' _ V' => j' = 74 ∧ g' = gC V g ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [gC] at f13 fi ⊢
  wpx [W_58, o2]
  all_goals repeat' (first
    | exact rfl
    | assumption
    | exact trivial
    | apply And.intro
    | intro _)

/-- `CheckPath` gave `al` not 0: the pops, the `ret` at 93. -/
theorem vc_79f {g : Gprs} {f : Rflags} {V : Addr → Byte} (h : ¬BitVec.setWidth 8 g.rax = 0)
    (p1 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8#64) i))
    (p2 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8#64 + 8) i))
    (p3 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8#64 + 8 + 8) i))
    (p4 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8#64 + 8 + 8 + 8) i)) :
    W_79 F Wl (fun j' g' _ V' => j' = 93 ∧ g' = gF V g ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [gF] at h p1 p2 p3 p4 ⊢
  wpx [W_79, W_48, W_83, o3, o1, o4, Op.cmpmr, BitVec.and_self, beq_iff_eq, beq_eq_false_iff_ne, ne_eq,
    Bool.not_eq_true', Bool.or_eq_true, Bool.or_eq_false_iff, decide_eq_true_eq, decide_eq_false_iff_not]
  all_goals repeat' (first
    | exact rfl
    | assumption
    | exact trivial
    | (intro hh; exact absurd hh h)
    | apply And.intro
    | intro _)

/-- `al` 0 and `i + 1` below the count: back to the loop's body. -/
theorem vc_79n {g : Gprs} {f : Rflags} {V : Addr → Byte} (h : BitVec.setWidth 8 g.rax = 0)
    (f8 : ∀ i < 4, Foot F.data (Addr.add (g.r13 + 8#64) i))
    (hc : ¬(rdd(V, g.r13 + 8#64).toNat < (BitVec.setWidth 32 g.r12 + 1#32).toNat ∨
      rdd(V, g.r13 + 8#64) = BitVec.setWidth 32 g.r12 + 1#32)) :
    W_79 F Wl (fun j' g' _ V' => j' = 58 ∧ g' = gN g ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [gN] at h f8 hc ⊢
  wpx [W_79, W_48, W_83, o3, o1, o4, Op.cmpmr, BitVec.and_self, beq_iff_eq, beq_eq_false_iff_ne, ne_eq,
    Bool.not_eq_true', Bool.or_eq_true, Bool.or_eq_false_iff, decide_eq_true_eq, decide_eq_false_iff_not]
  all_goals repeat' (first
    | exact rfl
    | assumption
    | exact trivial
    | (intro hh; exact absurd hh hc)
    | (intro hh; exact absurd h hh)
    | apply And.intro
    | intro _)

/-- `al` 0 and `i + 1` not below the count: to 96. -/
theorem vc_79e {g : Gprs} {f : Rflags} {V : Addr → Byte} (h : BitVec.setWidth 8 g.rax = 0)
    (f8 : ∀ i < 4, Foot F.data (Addr.add (g.r13 + 8#64) i))
    (hc : rdd(V, g.r13 + 8#64).toNat < (BitVec.setWidth 32 g.r12 + 1#32).toNat ∨
      rdd(V, g.r13 + 8#64) = BitVec.setWidth 32 g.r12 + 1#32) :
    W_79 F Wl (fun j' g' _ V' => j' = 96 ∧ g' = gN g ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [gN] at h f8 hc ⊢
  wpx [W_79, W_48, W_83, o3, o1, o4, Op.cmpmr, BitVec.and_self, beq_iff_eq, beq_eq_false_iff_ne, ne_eq,
    Bool.not_eq_true', Bool.or_eq_true, Bool.or_eq_false_iff, decide_eq_true_eq, decide_eq_false_iff_not]
  all_goals repeat' (first
    | exact rfl
    | assumption
    | exact trivial
    | (intro hh; exact absurd hc (not_or.2 hh))
    | (intro hh; exact absurd h hh)
    | apply And.intro
    | intro _)

/-- None: `eax` = 0, the pops, the `ret` at 108. -/
theorem vc_96 {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (p1 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8#64) i))
    (p2 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8#64 + 8) i))
    (p3 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8#64 + 8 + 8) i))
    (p4 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8#64 + 8 + 8 + 8) i)) :
    W_96 F Wl (fun j' g' _ V' => j' = 108 ∧ g' = gX V g ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [gX] at p1 p2 p3 p4 ⊢
  wpx [W_96, o5, lf_xz, BitVec.xor_self, BitVec.setWidth_zero]
  all_goals repeat' (first
    | exact rfl
    | assumption
    | exact trivial
    | apply And.intro
    | intro _)

/-! ## Arithmetic -/

theorem sw32 {i : Nat} (h : i < 2 ^ 32) :
    BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 64 i)) = BitVec.ofNat 64 i := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.reducePow]
  omega

theorem e32 {i : Nat} (h : i + 1 < 2 ^ 32) :
    (BitVec.setWidth 32 (BitVec.ofNat 64 i) + 1#32).toNat = i + 1 := by
  simp only [BitVec.toNat_add, BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.reducePow]
  omega

theorem inc32 {i : Nat} (h : i + 1 < 2 ^ 32) :
    BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 64 i) + 1#32) = BitVec.ofNat 64 (i + 1) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, e32 h]
  simp only [BitVec.toNat_ofNat, Nat.reducePow] <;> omega

/-- `i + 1` below the count `x`: `jbe` not taken. -/
theorem cmp_lt {x : BitVec 32} {i : Nat} (h : i + 1 < x.toNat) :
    ¬(x.toNat < (BitVec.setWidth 32 (BitVec.ofNat 64 i) + 1#32).toNat ∨
      x = BitVec.setWidth 32 (BitVec.ofNat 64 i) + 1#32) := by
  have hx := x.isLt
  have e := e32 (i := i) (by omega)
  rintro (h1 | h2)
  · omega
  · have := congrArg BitVec.toNat h2
    omega

/-- `i` below the count `x` and `i + 1` not: `jbe` taken. -/
theorem cmp_ge {x : BitVec 32} {i : Nat} (hi : i < x.toNat) (h : ¬i + 1 < x.toNat) :
    x.toNat < (BitVec.setWidth 32 (BitVec.ofNat 64 i) + 1#32).toNat ∨
      x = BitVec.setWidth 32 (BitVec.ofNat 64 i) + 1#32 := by
  have hx := x.isLt
  have e := e32 (i := i) (by omega)
  exact Or.inr (BitVec.eq_of_toNat_eq (by omega))

/-! ## The frame -/

/-- The stack's addresses as numbers. -/
theorem sp_t (S : Addr) (h : 48 ≤ S.toNat) :
    (S - 8).toNat = S.toNat - 8 ∧ (S - 8 - 8).toNat = S.toNat - 16 ∧ (S - 8 - 8 - 8).toNat = S.toNat - 24 ∧
    (S - 8 - 8 - 8 - 8).toNat = S.toNat - 32 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> bv_omega

/-- The stack's addresses. -/
theorem sp_e (S : Addr) :
    S - 8 = S - 8#64 ∧ S - 8 - 8 = S - 16#64 ∧ S - 8 - 8 - 8 = S - 24#64 ∧ S - 8 - 8 - 8 - 8 = S - 32#64 ∧
    S - 8 - 8 - 8 - 8 - 8#64 = S - 40#64 ∧ S - 40#64 - 8 = S - 48#64 ∧ S - 40#64 + 8#64 = S - 32#64 ∧
    S - 40#64 + 8#64 + 8 = S - 24#64 ∧ S - 40#64 + 8#64 + 8 + 8 = S - 16#64 ∧
    S - 40#64 + 8#64 + 8 + 8 + 8 = S - 8#64 ∧ S - 40#64 + 8#64 + 8 + 8 + 8 + 8 = S := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> bv_omega

/-- The stack's addresses from the bottom of the 48 bytes under `S`, or of the 40 bytes from `S - 32`. -/
theorem sp_w (S : Addr) :
    S - 8 = S - 48#64 + BitVec.ofNat 64 40 ∧ S - 8 - 8 = S - 48#64 + BitVec.ofNat 64 32 ∧
    S - 8 - 8 - 8 = S - 48#64 + BitVec.ofNat 64 24 ∧ S - 8 - 8 - 8 - 8 = S - 48#64 + BitVec.ofNat 64 16 ∧
    S - 40#64 + 8#64 = S - 32#64 + BitVec.ofNat 64 0 ∧ S - 40#64 + 8#64 + 8 = S - 32#64 + BitVec.ofNat 64 8 ∧
    S - 40#64 + 8#64 + 8 + 8 = S - 32#64 + BitVec.ofNat 64 16 ∧
    S - 40#64 + 8#64 + 8 + 8 + 8 = S - 32#64 + BitVec.ofNat 64 24 ∧ S = S - 32#64 + BitVec.ofNat 64 32 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> bv_omega

/-- Footprint bytes from an offset `d` in a run of `m`. -/
theorem off_ft {R : List Rgn} {a : Addr} {m : Nat} (h : ∀ i < m, Foot R (Addr.add a i)) (d : Nat) {n : Nat}
    {x : Addr} (hx : x = a + BitVec.ofNat 64 d) (hd : d + n ≤ m) : ∀ i < n, Foot R (x.add i) := fun i hi => by
  subst hx
  have := h (d + i) (by omega)
  rwa [show Addr.add a (d + i) = (a + BitVec.ofNat 64 d).add i from by simp only [Addr.add]; bv_omega] at this

/-- Bytes `[a, a + m)` the function reads: in `F.data`, not wrapping, apart from the 48 bytes under `S` and the
return address at `S`. -/
structure RdOk (F : Footprint) (S a : Addr) (m : Nat) : Prop where
  ft : ∀ i < m, Foot F.data (Addr.add a i)
  fits : a.toNat + m ≤ 2 ^ 64
  apart : a.toNat + m ≤ S.toNat - 48 ∨ S.toNat + 8 ≤ a.toNat

/-- The vector of items: `ExcludeItems` (`this + 56`) when `include` is 0, else `IncludeItems` (`this + 40`). -/
abbrev vec (g₀ : Gprs) : Addr := if BitVec.setWidth 8 g₀.rsi = 0 then g₀.rdi + 56#64 else g₀.rdi + 40#64
/-- The number of items. -/
abbrev nI (V₀ : Addr → Byte) (g₀ : Gprs) : Nat := rdd(V₀, vec g₀ + 8#64).toNat
/-- The items' pointers. -/
abbrev its (V₀ : Addr → Byte) (g₀ : Gprs) : Addr := rdq(V₀, vec g₀)
/-- The `k`-th item's pointer's address. -/
abbrev slot (V₀ : Addr → Byte) (g₀ : Gprs) (k : Nat) : Addr := its V₀ g₀ + BitVec.ofNat 64 k * 8#64
/-- The `k`-th item. -/
abbrev itm (V₀ : Addr → Byte) (g₀ : Gprs) (k : Nat) : Addr := rdq(V₀, slot V₀ g₀ k)

theorem vec_hv (g : Gprs) :
    (BitVec.setWidth 8 g.rsi = 0 ∧ vec g = g.rdi + 56#64) ∨ (¬BitVec.setWidth 8 g.rsi = 0 ∧ vec g = g.rdi + 40#64) := by
  by_cases hs : BitVec.setWidth 8 g.rsi = 0
  · exact Or.inl ⟨hs, if_pos hs⟩
  · exact Or.inr ⟨hs, if_neg hs⟩

/-- The bytes `V` read as at the entry. -/
structure Dat (V₀ : Addr → Byte) (g₀ : Gprs) (V : Addr → Byte) : Prop where
  n : rdd(V, vec g₀ + 8#64) = rdd(V₀, vec g₀ + 8#64)
  it : 0 < nI V₀ g₀ → rdq(V, vec g₀) = its V₀ g₀
  sl : ∀ k < nI V₀ g₀, rdq(V, slot V₀ g₀ k) = itm V₀ g₀ k

/-- In the loop: `Dat`, the four registers pushed and the return address `ra`. -/
structure Inv (V₀ : Addr → Byte) (g₀ : Gprs) (ra : Addr) (V : Addr → Byte) : Prop where
  d : Dat V₀ g₀ V
  r13 : rdq(V, g₀.rsp - 8#64) = g₀.r13
  r12 : rdq(V, g₀.rsp - 16#64) = g₀.r12
  rbp : rdq(V, g₀.rsp - 24#64) = g₀.rbp
  rbx : rdq(V, g₀.rsp - 32#64) = g₀.rbx
  ra : rdq(V, g₀.rsp) = ra

/-- The registers at the loop's body for the `i`-th item. -/
structure Rg (g₀ g : Gprs) (i : Nat) : Prop where
  rsp : g.rsp = g₀.rsp - 40#64
  rbx : g.rbx = isF g₀
  rbp : g.rbp = g₀.rdx
  r12 : g.r12 = BitVec.ofNat 64 i
  r13 : g.r13 = vec g₀
  r14 : g.r14 = g₀.r14
  r15 : g.r15 = g₀.r15

/-- The registers a function keeps, after its `ret`. -/
def Bk (g₀ g : Gprs) : Prop :=
  g.rsp = g₀.rsp + 8 ∧ g.rbx = g₀.rbx ∧ g.rbp = g₀.rbp ∧ g.r12 = g₀.r12 ∧ g.r13 = g₀.r13 ∧ g.r14 = g₀.r14 ∧
    g.r15 = g₀.r15

/-- The result `r` of `CheckPathCurrent` with `n` items, where `Hit k` is: the `k`-th item's `CheckPath` gives
true (`al` not 0). -/
def Res (Hit : Nat → Prop) (n : Nat) (r : BitVec 64) : Prop :=
  (∃ i < n, Hit i ∧ (∀ k < i, ¬Hit k) ∧ ¬BitVec.setWidth 8 r = 0) ∨ (r = 0#64 ∧ ∀ k < n, ¬Hit k)

/-- The bytes after the pushes. -/
theorem v1_rd (V₀ : Addr → Byte) (g₀ : Gprs) (hs : 48 ≤ g₀.rsp.toNat) {x : Addr} {m : Nat}
    (hx : x.toNat + m ≤ 2 ^ 64) (h : x.toNat + m ≤ g₀.rsp.toNat - 32 ∨ g₀.rsp.toNat ≤ x.toNat) :
    List.map (V1 V₀ g₀) (byteAddrs x m) = List.map V₀ (byteAddrs x m) := by
  obtain ⟨s8, s16, s24, s32⟩ := sp_t g₀.rsp hs
  have hl := g₀.rsp.isLt
  dsimp only [V1]
  rw [Tun.rd_Vst _ (g₀.rsp - 8 - 8 - 8 - 8) (toBytesLE g₀.rbx 8) x m (by rw [toBytesLE_length]; omega) hx
      (by rw [toBytesLE_length]; omega),
    Tun.rd_Vst _ (g₀.rsp - 8 - 8 - 8) (toBytesLE g₀.rbp 8) x m (by rw [toBytesLE_length]; omega) hx
      (by rw [toBytesLE_length]; omega),
    Tun.rd_Vst _ (g₀.rsp - 8 - 8) (toBytesLE g₀.r12 8) x m (by rw [toBytesLE_length]; omega) hx
      (by rw [toBytesLE_length]; omega),
    Tun.rd_Vst V₀ (g₀.rsp - 8) (toBytesLE g₀.r13 8) x m (by rw [toBytesLE_length]; omega) hx
      (by rw [toBytesLE_length]; omega)]

/-- The pushes: `Inv` with the entry's return address. -/
theorem inv1 (V₀ : Addr → Byte) (g₀ : Gprs) (hs : 48 ≤ g₀.rsp.toNat) (hs8 : g₀.rsp.toNat + 8 ≤ 2 ^ 64)
    (n8 : RdOk F g₀.rsp (vec g₀ + 8#64) 4) (it : 0 < nI V₀ g₀ → RdOk F g₀.rsp (vec g₀) 8)
    (sl : ∀ k < nI V₀ g₀, RdOk F g₀.rsp (slot V₀ g₀ k) 8) {ra : Addr} (hra : rdq(V₀, g₀.rsp) = ra) :
    Inv V₀ g₀ ra (V1 V₀ g₀) := by
  obtain ⟨s8, s16, s24, s32⟩ := sp_t g₀.rsp hs
  obtain ⟨e8, e16, e24, e32, -⟩ := sp_e g₀.rsp
  have hl := g₀.rsp.isLt
  have ap : ∀ {x : Addr} {m : Nat}, RdOk F g₀.rsp x m →
      List.map (V1 V₀ g₀) (byteAddrs x m) = List.map V₀ (byteAddrs x m) := fun h =>
    v1_rd V₀ g₀ hs h.fits (by have := h.apart; omega)
  refine ⟨⟨congrArg (ofBytesLE 32) (ap n8), fun h => congrArg (ofBytesLE 64) (ap (it h)),
    fun k hk => congrArg (ofBytesLE 64) (ap (sl k hk))⟩, ?_, ?_, ?_, ?_,
    (congrArg (ofBytesLE 64) (v1_rd V₀ g₀ hs hs8 (Or.inr (Nat.le_refl _)))).trans hra⟩
  · rw [← e8]
    dsimp only [V1]
    rw [Tun.rd_Vst _ (g₀.rsp - 8 - 8 - 8 - 8) (toBytesLE g₀.rbx 8) _ 8 (by rw [toBytesLE_length]; omega)
        (by omega) (by rw [toBytesLE_length]; omega),
      Tun.rd_Vst _ (g₀.rsp - 8 - 8 - 8) (toBytesLE g₀.rbp 8) _ 8 (by rw [toBytesLE_length]; omega)
        (by omega) (by rw [toBytesLE_length]; omega),
      Tun.rd_Vst _ (g₀.rsp - 8 - 8) (toBytesLE g₀.r12 8) _ 8 (by rw [toBytesLE_length]; omega)
        (by omega) (by rw [toBytesLE_length]; omega),
      Tun.rd_Vst_self _ _ _ (toBytesLE_length _ _) (by omega)]
    exact ofBytesLE_toBytesLE (n := 8) rfl _
  · rw [← e16]
    dsimp only [V1]
    rw [Tun.rd_Vst _ (g₀.rsp - 8 - 8 - 8 - 8) (toBytesLE g₀.rbx 8) _ 8 (by rw [toBytesLE_length]; omega)
        (by omega) (by rw [toBytesLE_length]; omega),
      Tun.rd_Vst _ (g₀.rsp - 8 - 8 - 8) (toBytesLE g₀.rbp 8) _ 8 (by rw [toBytesLE_length]; omega)
        (by omega) (by rw [toBytesLE_length]; omega),
      Tun.rd_Vst_self _ _ _ (toBytesLE_length _ _) (by omega)]
    exact ofBytesLE_toBytesLE (n := 8) rfl _
  · rw [← e24]
    dsimp only [V1]
    rw [Tun.rd_Vst _ (g₀.rsp - 8 - 8 - 8 - 8) (toBytesLE g₀.rbx 8) _ 8 (by rw [toBytesLE_length]; omega)
        (by omega) (by rw [toBytesLE_length]; omega),
      Tun.rd_Vst_self _ _ _ (toBytesLE_length _ _) (by omega)]
    exact ofBytesLE_toBytesLE (n := 8) rfl _
  · rw [← e32]
    dsimp only [V1]
    rw [Tun.rd_Vst_self _ _ _ (toBytesLE_length _ _) (by omega)]
    exact ofBytesLE_toBytesLE (n := 8) rfl _

/-! ## The run -/

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ X : State} {o : Oracle} {t : Nat}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {V₀ : Addr → Byte} {g₀ : Gprs} {Hit : Nat → Prop} {e₂ : Addr} {code₂ : List Byte} {j₂ : Nat}

/-- What the run needs around the function: its code and `CheckPath`'s, the 48 bytes under the entry's `S` it may
store into, the 40 bytes from `S - 32` it reads (the registers pushed, the return address), and the bytes of the
vector and its items it reads (`RdOk`). -/
structure Env (F : Footprint) (Wl : List Rgn) (L : List (Addr × List Byte)) (V₀ : Addr → Byte) (g₀ : Gprs) :
    Prop where
  code : CodeIn L cpt_at cpt
  chk : ∃ code, CodeIn L chk_at code ∧ 0 < code.length
  s0 : 48 ≤ g₀.rsp.toNat
  s8 : g₀.rsp.toNat + 8 ≤ 2 ^ 64
  w : ∀ i < 48, Foot Wl (Addr.add (g₀.rsp - 48#64) i)
  d : ∀ i < 40, Foot F.data (Addr.add (g₀.rsp - 32#64) i)
  n8 : RdOk F g₀.rsp (vec g₀ + 8#64) 4
  it : 0 < nI V₀ g₀ → RdOk F g₀.rsp (vec g₀) 8
  sl : ∀ k < nI V₀ g₀, RdOk F g₀.rsp (slot V₀ g₀ k) 8

/-- The pops' and the `ret`'s bytes. -/
theorem Env.ft (hE : Env F Wl L V₀ g₀) :
    (∀ m < 8, Foot F.data (Addr.add (g₀.rsp - 40#64 + 8#64) m)) ∧
    (∀ m < 8, Foot F.data (Addr.add (g₀.rsp - 40#64 + 8#64 + 8) m)) ∧
    (∀ m < 8, Foot F.data (Addr.add (g₀.rsp - 40#64 + 8#64 + 8 + 8) m)) ∧
    (∀ m < 8, Foot F.data (Addr.add (g₀.rsp - 40#64 + 8#64 + 8 + 8 + 8) m)) ∧
    (∀ m < 8, Foot F.data (Addr.add g₀.rsp m)) := by
  obtain ⟨-, -, -, -, a0, a8, a16, a24, a32⟩ := sp_w g₀.rsp
  exact ⟨off_ft hE.d 0 a0 (by decide), off_ft hE.d 8 a8 (by decide), off_ft hE.d 16 a16 (by decide),
    off_ft hE.d 24 a24 (by decide), off_ft hE.d 32 a32 (by decide)⟩

/-- The pushes' bytes. -/
theorem Env.wf (hE : Env F Wl L V₀ g₀) :
    (∀ m < 8, Foot Wl (Addr.add (g₀.rsp - 8) m)) ∧ (∀ m < 8, Foot Wl (Addr.add (g₀.rsp - 8 - 8) m)) ∧
    (∀ m < 8, Foot Wl (Addr.add (g₀.rsp - 8 - 8 - 8) m)) ∧
    (∀ m < 8, Foot Wl (Addr.add (g₀.rsp - 8 - 8 - 8 - 8) m)) := by
  obtain ⟨a40, a32, a24, a16, -⟩ := sp_w g₀.rsp
  exact ⟨off_ft hE.w 40 a40 (by decide), off_ft hE.w 32 a32 (by decide), off_ft hE.w 24 a24 (by decide),
    off_ft hE.w 16 a16 (by decide)⟩

/-- What the function asks of `CItem::CheckPath` (at `chk_at`) for the `i`-th item: from its entry with `rsp` =
`S - 48`, the return address into the function there, `Inv` for the bytes `V` under it, `rdi` the `i`-th item,
`rsi` = `pathParts`, `edx` = `isFile`, the run goes on to the goal if it does from every state at the return address
with `Inv`, `rsp` = `S - 40`, the registers a call keeps, and `al` not 0 just when `Hit i`. -/
def Chk (prof : Profile) (F : Footprint) (Wl : List Rgn) (L : List (Addr × List Byte)) (s₀ : State) (o : Oracle)
    (gev : List Event) (gP : State → Nat → List Event → Prop) (gE : Outcome → List Event → Prop)
    (V₀ : Addr → Byte) (g₀ : Gprs) (ra : Addr) (Hit : Nat → Prop) : Prop :=
  ∀ (i : Nat) (Y : State) (t : Nat) (V : Addr → Byte), i < nI V₀ g₀ → KeptW Wl s₀ Y → Inv V₀ g₀ ra V →
    Agree F Y.proc.mm.mem (Vst V (g₀.rsp - 48#64) (toBytesLE (cpt_at.add 79) 8)) → Y.cpu.rip = chk_at →
    Y.cpu.gpr.rsp = g₀.rsp - 48#64 → Y.cpu.gpr.rdi = itm V₀ g₀ i → Y.cpu.gpr.rsi = g₀.rdx →
    Y.cpu.gpr.rdx = BitVec.setWidth 64 (BitVec.setWidth 32 (isF g₀)) →
    (∀ (Z : State) (t' : Nat) (V' : Addr → Byte), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V' → Inv V₀ g₀ ra V' →
      Z.cpu.rip = cpt_at.add 79 → Z.cpu.gpr.rsp = g₀.rsp - 40#64 → Z.cpu.gpr.rbx = Y.cpu.gpr.rbx →
      Z.cpu.gpr.rbp = Y.cpu.gpr.rbp → Z.cpu.gpr.r12 = Y.cpu.gpr.r12 → Z.cpu.gpr.r13 = Y.cpu.gpr.r13 →
      Z.cpu.gpr.r14 = Y.cpu.gpr.r14 → Z.cpu.gpr.r15 = Y.cpu.gpr.r15 →
      (¬BitVec.setWidth 8 Z.cpu.gpr.rax = 0 ↔ Hit i) → GoG prof L o gev gP gE Z t') →
    GoG prof L o gev gP gE Y t

/-- What the caller asks at the return address `ra`: the bytes `Dat`, the registers a call keeps, the result. -/
def Ret (prof : Profile) (F : Footprint) (Wl : List Rgn) (L : List (Addr × List Byte)) (s₀ : State) (o : Oracle)
    (gev : List Event) (gP : State → Nat → List Event → Prop) (gE : Outcome → List Event → Prop)
    (V₀ : Addr → Byte) (g₀ : Gprs) (ra : Addr) (Hit : Nat → Prop) : Prop :=
  ∀ (Z : State) (t' : Nat) (V' : Addr → Byte), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V' → Dat V₀ g₀ V' →
    Z.cpu.rip = ra → Bk g₀ Z.cpu.gpr → Res Hit (nI V₀ g₀) Z.cpu.gpr.rax → GoG prof L o gev gP gE Z t'

/-- From the loop's body for the `i`-th item, none of the ones before it a `Hit`, the run goes on to the goal. -/
def At (prof : Profile) (F : Footprint) (Wl : List Rgn) (L : List (Addr × List Byte)) (s₀ : State) (o : Oracle)
    (gev : List Event) (gP : State → Nat → List Event → Prop) (gE : Outcome → List Event → Prop)
    (V₀ : Addr → Byte) (g₀ : Gprs) (ra : Addr) (Hit : Nat → Prop) (i : Nat) : Prop :=
  ∀ (Y : State) (t : Nat) (V : Addr → Byte), KeptW Wl s₀ Y → Agree F Y.proc.mm.mem V → Inv V₀ g₀ ra V →
    Y.cpu.rip = cpt_at.add 58 → Rg g₀ Y.cpu.gpr i → (∀ k < i, ¬Hit k) → GoG prof L o gev gP gE Y t

/-- A `ret` (at `j`) with `rsp` = `S`, the registers a call keeps and the result. -/
theorem fin (c : Seg prof F Wl L s₀ o) (hE : Env F Wl L V₀ g₀) (hin₂ : CodeIn L e₂ code₂)
    (h₂ : j₂ < code₂.length) (kE : Ret prof F Wl L s₀ o gev gP gE V₀ g₀ (e₂.add j₂) Hit) {j : Nat} (hj : j < 110)
    (hd : Dec prof.feat cpt j (FV7z.mk .ret 64 [] 1)) {Y : State} {V : Addr → Byte} (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem V) (hD : Dat V₀ g₀ V) (hra : rdq(V, g₀.rsp) = e₂.add j₂)
    (hr : Y.cpu.rip = cpt_at.add j) (hs : Y.cpu.gpr.rsp = g₀.rsp) (hb : Y.cpu.gpr.rbx = g₀.rbx)
    (hp : Y.cpu.gpr.rbp = g₀.rbp) (h12 : Y.cpu.gpr.r12 = g₀.r12) (h13 : Y.cpu.gpr.r13 = g₀.r13)
    (h14 : Y.cpu.gpr.r14 = g₀.r14) (h15 : Y.cpu.gpr.r15 = g₀.r15) (hres : Res Hit (nI V₀ g₀) Y.cpu.gpr.rax) :
    GoG prof L o gev gP gE Y t := by
  refine c.s_ret hK hA hE.code (lt_len hj) hr hd (fun m hm => by rw [hs]; exact hE.ft.2.2.2.2 m hm) hin₂ h₂
    (by rw [hs]; exact hra) ?_
  rintro Z t' hKZ hAZ ⟨hrZ, hgZ⟩
  refine kE Z t' V hKZ hAZ hD hrZ ?_ ?_
  · rw [hgZ]
    exact ⟨congrArg (· + 8) hs, hb, hp, h12, h13, h14, h15⟩
  · rw [hgZ]
    exact hres

/-- The pops at 96 and the `ret` at 108 (`eax` = 0), from `rsp` = `S - 40` and `Inv`. -/
theorem none96 (c : Seg prof F Wl L s₀ o) (hE : Env F Wl L V₀ g₀) (hin₂ : CodeIn L e₂ code₂)
    (h₂ : j₂ < code₂.length) (kE : Ret prof F Wl L s₀ o gev gP gE V₀ g₀ (e₂.add j₂) Hit) {Y : State}
    {V : Addr → Byte} (hK : KeptW Wl s₀ Y) (hA : Agree F Y.proc.mm.mem V) (hI : Inv V₀ g₀ (e₂.add j₂) V)
    (hr : Y.cpu.rip = cpt_at.add 96) (hs : Y.cpu.gpr.rsp = g₀.rsp - 40#64) (h14 : Y.cpu.gpr.r14 = g₀.r14)
    (h15 : Y.cpu.gpr.r15 = g₀.r15) (hno : ∀ k < nI V₀ g₀, ¬Hit k) : GoG prof L o gev gP gE Y t := by
  obtain ⟨-, -, -, -, -, -, p0, p8, p16, p24, p32⟩ := sp_e g₀.rsp
  obtain ⟨q0, q8, q16, q24, -⟩ := hE.ft
  refine (c_96 prof).run c hE.code (fun j' g' _ V' => j' = 108 ∧ g' = gX V Y.cpu.gpr ∧ V' = V) hK hA hr
    (vc_96 (by rw [hs]; exact q0) (by rw [hs]; exact q8) (by rw [hs]; exact q16) (by rw [hs]; exact q24)) ?_
  rintro j' g fl V₂ ⟨rfl, rfl, hV₂⟩ Y₃ t₃ hK₃ hA₃ hr₃ hg₃ -
  subst V₂
  exact fin c hE hin₂ h₂ kE (by decide) (ret_108 _) hK₃ hA₃ hI.d hI.ra hr₃
    (by rw [hg₃]; show Y.cpu.gpr.rsp + 8#64 + 8 + 8 + 8 + 8 = _; rw [hs]; exact p32)
    (by rw [hg₃]; show rdq(V, Y.cpu.gpr.rsp + 8#64) = _; rw [hs, p0]; exact hI.rbx)
    (by rw [hg₃]; show rdq(V, Y.cpu.gpr.rsp + 8#64 + 8) = _; rw [hs, p8]; exact hI.rbp)
    (by rw [hg₃]; show rdq(V, Y.cpu.gpr.rsp + 8#64 + 8 + 8) = _; rw [hs, p16]; exact hI.r12)
    (by rw [hg₃]; show rdq(V, Y.cpu.gpr.rsp + 8#64 + 8 + 8 + 8) = _; rw [hs, p24]; exact hI.r13)
    (by rw [hg₃]; exact h14) (by rw [hg₃]; exact h15) (Or.inr ⟨by rw [hg₃], hno⟩)

/-- The `i`-th item: the `call`, then the `ret` at 93 (`Hit i`), the `i + 1`-th item, or the pops at 96. -/
theorem lpHead {i : Nat} (c : Seg prof F Wl L s₀ o) (hE : Env F Wl L V₀ g₀) (hin₂ : CodeIn L e₂ code₂)
    (h₂ : j₂ < code₂.length) (hchk : Chk prof F Wl L s₀ o gev gP gE V₀ g₀ (e₂.add j₂) Hit)
    (kE : Ret prof F Wl L s₀ o gev gP gE V₀ g₀ (e₂.add j₂) Hit) (hi : i < nI V₀ g₀)
    (kn : i + 1 < nI V₀ g₀ → At prof F Wl L s₀ o gev gP gE V₀ g₀ (e₂.add j₂) Hit (i + 1)) :
    At prof F Wl L s₀ o gev gP gE V₀ g₀ (e₂.add j₂) Hit i := by
  intro Y t V hK hA hI hr hR hno
  have hn32 : nI V₀ g₀ < 2 ^ 32 := (rdd(V₀, vec g₀ + 8#64)).isLt
  have hn : 0 < nI V₀ g₀ := by omega
  obtain ⟨-, -, -, -, -, x48, p0, p8, p16, p24, p32⟩ := sp_e g₀.rsp
  obtain ⟨q0, q8, q16, q24, -⟩ := hE.ft
  have hsw : BitVec.setWidth 64 (BitVec.setWidth 32 Y.cpu.gpr.r12) = BitVec.ofNat 64 i := by
    rw [hR.r12]
    exact sw32 (by omega)
  have ea : rdq(V, Y.cpu.gpr.r13) + BitVec.setWidth 64 (BitVec.setWidth 32 Y.cpu.gpr.r12) * 8#64 =
      slot V₀ g₀ i := by
    rw [hsw, hR.r13, hI.d.it hn]
  -- to the `call`
  refine (c_58 prof).run c hE.code (fun j' g' _ V' => j' = 74 ∧ g' = gC V Y.cpu.gpr ∧ V' = V) hK hA hr
    (vc_58 (fun m hm => by rw [hR.r13]; exact (hE.it hn).ft m hm)
      (fun m hm => by rw [ea]; exact (hE.sl i hi).ft m hm)) ?_
  rintro j' g fl V₁ ⟨rfl, rfl, hV₁⟩ Y₁ t₁ hK₁ hA₁ hr₁ hg₁ -
  subst V₁
  obtain ⟨codeC, hinC, hC0⟩ := hE.chk
  have hsY : Y₁.cpu.gpr.rsp = g₀.rsp - 40#64 := by rw [hg₁]; exact hR.rsp
  refine c.s_call hK₁ hA₁ hE.code (lt_len (by decide)) hr₁ (call_74 _) hinC hC0 tgt74
    (fun m hm => by rw [hsY, x48]; exact hE.w m (by omega)) ?_
  rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
  rw [hsY, x48] at hA₂
  have hg₂' : Y₂.cpu.gpr = (gC V Y.cpu.gpr).set 4 (g₀.rsp - 48#64) := by
    rw [hg₂, hg₁]
    exact congrArg (fun v => (gC V Y.cpu.gpr).set 4 v) ((congrArg (· - 8) hR.rsp).trans x48)
  -- `CheckPath`
  refine hchk i Y₂ t₂ V hi hK₂ hI hA₂ hr₂ (by rw [hg₂']; rfl)
    (by rw [hg₂']; show rdq(V, rdq(V, Y.cpu.gpr.r13) + _ * 8#64) = _; rw [ea, hI.d.sl i hi])
    (by rw [hg₂']; exact hR.rbp)
    (by rw [hg₂']; show BitVec.setWidth 64 (BitVec.setWidth 32 Y.cpu.gpr.rbx) = _; rw [hR.rbx]) ?_
  intro Z t' V' hKZ hAZ hI' hrZ zs hzb hzp hz12 hz13 hz14 hz15 hhit
  rw [hg₂'] at hzb hzp hz12 hz13 hz14 hz15
  have zb : Z.cpu.gpr.rbx = isF g₀ := hzb.trans hR.rbx
  have zp : Z.cpu.gpr.rbp = g₀.rdx := hzp.trans hR.rbp
  have z12 : Z.cpu.gpr.r12 = BitVec.ofNat 64 i := hz12.trans hR.r12
  have z13 : Z.cpu.gpr.r13 = vec g₀ := hz13.trans hR.r13
  have z14 : Z.cpu.gpr.r14 = g₀.r14 := hz14.trans hR.r14
  have z15 : Z.cpu.gpr.r15 = g₀.r15 := hz15.trans hR.r15
  by_cases hH : Hit i
  · -- the `ret` at 93 with `al` not 0
    have hal := hhit.2 hH
    refine (c_79 prof).run c hE.code (fun j' g' _ V'' => j' = 93 ∧ g' = gF V' Z.cpu.gpr ∧ V'' = V') hKZ hAZ hrZ
      (vc_79f hal (by rw [zs]; exact q0) (by rw [zs]; exact q8) (by rw [zs]; exact q16) (by rw [zs]; exact q24)) ?_
    rintro j' g fl V₂ ⟨rfl, rfl, hV₂⟩ Y₃ t₃ hK₃ hA₃ hr₃ hg₃ -
    subst V₂
    exact fin c hE hin₂ h₂ kE (by decide) (ret_93 _) hK₃ hA₃ hI'.d hI'.ra hr₃
      (by rw [hg₃]; show Z.cpu.gpr.rsp + 8#64 + 8 + 8 + 8 + 8 = _; rw [zs]; exact p32)
      (by rw [hg₃]; show rdq(V', Z.cpu.gpr.rsp + 8#64) = _; rw [zs, p0]; exact hI'.rbx)
      (by rw [hg₃]; show rdq(V', Z.cpu.gpr.rsp + 8#64 + 8) = _; rw [zs, p8]; exact hI'.rbp)
      (by rw [hg₃]; show rdq(V', Z.cpu.gpr.rsp + 8#64 + 8 + 8) = _; rw [zs, p16]; exact hI'.r12)
      (by rw [hg₃]; show rdq(V', Z.cpu.gpr.rsp + 8#64 + 8 + 8 + 8) = _; rw [zs, p24]; exact hI'.r13)
      (by rw [hg₃]; exact z14) (by rw [hg₃]; exact z15)
      (Or.inl ⟨i, hi, hH, hno, by rw [hg₃]; exact hal⟩)
  have hz : BitVec.setWidth 8 Z.cpu.gpr.rax = 0 := Classical.byContradiction fun h => hH (hhit.1 h)
  by_cases hlt : i + 1 < nI V₀ g₀
  · -- the next item
    refine (c_79 prof).run c hE.code (fun j' g' _ V'' => j' = 58 ∧ g' = gN Z.cpu.gpr ∧ V'' = V') hKZ hAZ hrZ
      (vc_79n hz (by rw [z13]; exact hE.n8.ft) (by rw [z13, z12, hI'.d.n]; exact cmp_lt hlt)) ?_
    rintro j' g fl V₂ ⟨rfl, rfl, hV₂⟩ Y₃ t₃ hK₃ hA₃ hr₃ hg₃ -
    subst V₂
    have h12 : (gN Z.cpu.gpr).r12 = BitVec.ofNat 64 (i + 1) := by
      show BitVec.setWidth 64 (BitVec.setWidth 32 Z.cpu.gpr.r12 + 1#32) = _
      rw [z12]
      exact inc32 (by omega)
    refine kn hlt Y₃ t₃ V' hK₃ hA₃ hI' hr₃ ?_ ?_
    · rw [hg₃]
      exact ⟨zs, zb, zp, h12, z13, z14, z15⟩
    · intro k hk
      rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | rfl
      · exact hno k hk
      · exact hH
  · -- none: the pops at 96
    refine (c_79 prof).run c hE.code (fun j' g' _ V'' => j' = 96 ∧ g' = gN Z.cpu.gpr ∧ V'' = V') hKZ hAZ hrZ
      (vc_79e hz (by rw [z13]; exact hE.n8.ft) (by rw [z13, z12, hI'.d.n]; exact cmp_ge hi hlt)) ?_
    rintro j' g fl V₂ ⟨rfl, rfl, hV₂⟩ Y₃ t₃ hK₃ hA₃ hr₃ hg₃ -
    subst V₂
    refine none96 c hE hin₂ h₂ kE hK₃ hA₃ hI' hr₃ (by rw [hg₃]; exact zs) (by rw [hg₃]; exact z14)
      (by rw [hg₃]; exact z15) fun k hk => ?_
    rcases Nat.lt_succ_iff_lt_or_eq.1 (show k < i + 1 by omega) with hk | rfl
    · exact hno k hk
    · exact hH

/-- The items from any one: by the number left. -/
theorem lpAll (c : Seg prof F Wl L s₀ o) (hE : Env F Wl L V₀ g₀) (hin₂ : CodeIn L e₂ code₂)
    (h₂ : j₂ < code₂.length) (hchk : Chk prof F Wl L s₀ o gev gP gE V₀ g₀ (e₂.add j₂) Hit)
    (kE : Ret prof F Wl L s₀ o gev gP gE V₀ g₀ (e₂.add j₂) Hit) :
    ∀ (m i : Nat), i + m + 1 = nI V₀ g₀ → At prof F Wl L s₀ o gev gP gE V₀ g₀ (e₂.add j₂) Hit i
  | 0, _, h => lpHead c hE hin₂ h₂ hchk kE (by omega) fun h' => absurd h' (by omega)
  | m + 1, i, h => lpHead c hE hin₂ h₂ hchk kE (by omega) fun _ => lpAll c hE hin₂ h₂ hchk kE m (i + 1) (by omega)

/-- `CCensorNode::CheckPathCurrent (include, pathParts, isFile)` (the entry's bytes `V`): if `CheckPath` runs for
each item of the vector `vec` as `Chk` says (`al` not 0 just when `Hit i`), the run reaches the return address with
the bytes it read as they were, the registers a call keeps, and in `rax` what the first `Hit` gave (`al` not 0), or
0 if there is none (`Res`). -/
theorem cpt_ok (c : Seg prof F Wl L s₀ o) {V : Addr → Byte} (hE : Env F Wl L V X.cpu.gpr) (hK : KeptW Wl s₀ X)
    (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = cpt_at) (hin₂ : CodeIn L e₂ code₂) (h₂ : j₂ < code₂.length)
    (hra : rdq(V, X.cpu.gpr.rsp) = e₂.add j₂)
    (hchk : Chk prof F Wl L s₀ o gev gP gE V X.cpu.gpr (e₂.add j₂) Hit)
    (kE : Ret prof F Wl L s₀ o gev gP gE V X.cpu.gpr (e₂.add j₂) Hit) :
    GoG prof L o gev gP gE X t := by
  obtain ⟨-, -, -, -, x40, -⟩ := sp_e X.cpu.gpr.rsp
  obtain ⟨w1, w2, w3, w4⟩ := hE.wf
  have hI := inv1 V X.cpu.gpr hE.s0 hE.s8 hE.n8 hE.it hE.sl hra
  have hrd := hI.d.n
  have hR : ∀ g : Gprs, g = g58 V X.cpu.gpr (vec X.cpu.gpr) → Rg X.cpu.gpr g 0 := fun g hg => by
    subst hg
    exact ⟨x40, rfl, rfl, rfl, rfl, rfl, rfl⟩
  by_cases h0 : rdd(V1 V X.cpu.gpr, vec X.cpu.gpr + 8#64) = 0#32
  · -- no items: the pops at 96
    refine (c_0 prof).run c hE.code (fun j' g' _ V' => j' = 96 ∧ g' = g58 V X.cpu.gpr (vec X.cpu.gpr) ∧
        V' = V1 V X.cpu.gpr) hK hA (by rw [addr_add_zero]; exact hrip)
      (vc_0z (vec_hv _) h0 w1 w2 w3 w4 hE.n8.ft) ?_
    rintro j' g fl V₁ ⟨rfl, hg, hV₁⟩ Y t₁ hKY hAY hrY hgY -
    subst V₁
    have hRY := hR _ (hgY.trans hg)
    have hn0 : nI V X.cpu.gpr = 0 := by
      show rdd(V, vec X.cpu.gpr + 8#64).toNat = 0
      rw [← hrd, h0]
      rfl
    exact none96 c hE hin₂ h₂ kE hKY hAY hI hrY hRY.rsp hRY.r14 hRY.r15 fun k hk => absurd hk (by omega)
  · -- the loop from the first item
    refine (c_0 prof).run c hE.code (fun j' g' _ V' => j' = 58 ∧ g' = g58 V X.cpu.gpr (vec X.cpu.gpr) ∧
        V' = V1 V X.cpu.gpr) hK hA (by rw [addr_add_zero]; exact hrip)
      (vc_0n (vec_hv _) h0 w1 w2 w3 w4 hE.n8.ft) ?_
    rintro j' g fl V₁ ⟨rfl, hg, hV₁⟩ Y t₁ hKY hAY hrY hgY -
    subst V₁
    have hn : 0 < nI V X.cpu.gpr := by
      have : rdd(V1 V X.cpu.gpr, vec X.cpu.gpr + 8#64).toNat ≠ 0 := fun h => h0 (BitVec.eq_of_toNat_eq h)
      show 0 < rdd(V, vec X.cpu.gpr + 8#64).toNat
      rw [← hrd]
      omega
    exact lpAll c hE hin₂ h₂ hchk kE (nI V X.cpu.gpr - 1) 0 (by omega) Y t₁ _ hKY hAY hI hrY
      (hR _ (hgY.trans hg)) (fun k hk => absurd hk (Nat.not_lt_zero k))

end FV7z.Cpt
