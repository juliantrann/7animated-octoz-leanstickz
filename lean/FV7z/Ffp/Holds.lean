import FV7z.Ffp.Cuts
import FV7z.Lemmas.LeafRet
import FV7z.Lemmas.SpCallK
import FV7z.Tun.Inv
/-!
# `NWildcard::CCensor::FindPairForPrefix` (PLAN.md §M, M1)

7-Zip 26.06's `NWildcard::CCensor::FindPairForPrefix (prefix)` at `0x453550` in `7zzs` (`CPP/Common/Wildcard.cpp`;
`objdump -d`): `for (i = 0; i < Pairs.Size(); i++) if (CompareFileNames (Pairs[i].Prefix, prefix) == 0) return i;
return -1;` (`this` = `rdi`, `prefix` = `rsi`; `CompareFileNames` at `0x4522b0`, called at 57).

No pairs: `eax` = -1 and the `ret` at 95 (`vc_0z`). Else `push r12; push rbp; push rbx`, `rbx` = `i` = 0 (`vc_0n`),
and the loop's head (40): the pair's prefix's characters in `rdi`, those of `prefix` in `rsi` (`vc_40`), the `call`
(57). `CompareFileNames` is a hypothesis (`Cmp`) for each pair, as the functions of `FV7z.Csu`'s `Runs`. After it
(62): 0 gives `eax` = `i`, the pops and the `ret` at 72 (`vc_62z`); else `i + 1` and back to 40 while below the
count (`vc_62n`), or `eax` = -1, the pops and the `ret` at 89 (`vc_62e`). `lpHead` is one pair, `lpAll` the pairs
from any one by the number left, `ffp_ok` the function (`Res`: the first `i` with `Same i`, or -1).
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Ffp

/-! ## The instructions outside the blocks -/

def pc57 : List Byte := [0xe8, 0x22, 0xed, 0xff, 0xff]
def pret : List Byte := [0xc3]
theorem pc57_0 : ∀ feat, Dec feat pc57 0 (FV7z.mk .call 64 [.rel 18446744073709546786] 5) := by dec_rfl
theorem pret_0 : ∀ feat, Dec feat pret 0 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem wc57 : pc57 <+: ffp.drop 57 := by decide +kernel
theorem w_72 : pret <+: ffp.drop 72 := by decide +kernel
theorem w_89 : pret <+: ffp.drop 89 := by decide +kernel
theorem w_95 : pret <+: ffp.drop 95 := by decide +kernel
theorem call_57 (feat : Features) : Dec feat ffp 57 (FV7z.mk .call 64 [.rel 18446744073709546786] 5) :=
  Dec.shift (j := 57) (k := 0) (pc57_0 feat) wc57 (Nat.zero_le _)
theorem ret_72 (feat : Features) : Dec feat ffp 72 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 72) (k := 0) (pret_0 feat) w_72 (Nat.zero_le _)
theorem ret_89 (feat : Features) : Dec feat ffp 89 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 89) (k := 0) (pret_0 feat) w_89 (Nat.zero_le _)
theorem ret_95 (feat : Features) : Dec feat ffp 95 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 95) (k := 0) (pret_0 feat) w_95 (Nat.zero_le _)

/-- `CompareFileNames`. -/
abbrev cfn_at : Addr := 0x4522b0
theorem tgt57 : ffp_at.add (57 + 5) + BitVec.ofNat 64 18446744073709546786 = cfn_at := by decide

/-! ## The pieces -/

/-- The registers at the loop's head the first time. -/
abbrev g40 (V : Addr → Byte) (g : Gprs) : Gprs :=
  { g with
    rax := BitVec.setWidth 64 rdd(V, g.rdi + 8#64), rbx := 0#64, rsp := g.rsp - 8 - 8 - 8, rbp := g.rdi,
    r12 := g.rsi }
/-- The three registers pushed. -/
abbrev V1 (V : Addr → Byte) (g : Gprs) : Addr → Byte :=
  Vst (Vst (Vst V (g.rsp - 8) (toBytesLE g.r12 8)) (g.rsp - 8 - 8) (toBytesLE g.rbp 8)) (g.rsp - 8 - 8 - 8)
    (toBytesLE g.rbx 8)
/-- The pair's address read at 50. -/
abbrev ia (V : Addr → Byte) (g : Gprs) : Addr :=
  rdq(V, rdq(V, g.rbp) + BitVec.setWidth 64 (BitVec.setWidth 32 g.rbx) * 8#64)
/-- The registers at the `call`. -/
abbrev gC (V : Addr → Byte) (g : Gprs) : Gprs :=
  { g with rax := ia V g, rdx := rdq(V, g.rbp), rsi := rdq(V, g.r12), rdi := rdq(V, ia V g) }

variable {F : Footprint} {Wl : List Rgn}

/-- No pairs: `eax` = -1, the `ret` at 95. -/
theorem vc_0z {g : Gprs} {f : Rflags} {V : Addr → Byte} (h : rdd(V, g.rdi + 8#64) = 0#32)
    (f8 : ∀ i < 4, Foot F.data (Addr.add (g.rdi + 8#64) i)) :
    W_0 F Wl (fun j' g' _ V' => j' = 95 ∧ g' = { g with rax := BitVec.setWidth 64 4294967295#32 } ∧ V' = V)
      g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h f8 ⊢
  wpx [W_0, W_90, W_11, o0, o7, o1, h, BitVec.and_self, beq_iff_eq, beq_eq_false_iff_ne, ne_eq, beq_self_eq_true,
    not_true_eq_false, not_false_eq_true, false_implies, Bool.true_eq_false, Bool.false_eq_true, implies_true]
  all_goals repeat' (first
    | exact rfl
    | assumption
    | exact trivial
    | (intro hh; exact absurd hh (by decide))
    | apply And.intro
    | intro _)

/-- Pairs: the pushes, `i` = 0, to the loop's head. -/
theorem vc_0n {g : Gprs} {f : Rflags} {V : Addr → Byte} (h : rdd(V, g.rdi + 8#64) ≠ 0#32)
    (f8 : ∀ i < 4, Foot F.data (Addr.add (g.rdi + 8#64) i))
    (hs1 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8) i)) (hs2 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8) i))
    (hs3 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8 - 8) i)) :
    W_0 F Wl (fun j' g' _ V' => j' = 40 ∧ g' = g40 V g ∧ V' = V1 V g) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [g40, V1] at h f8 hs1 hs2 hs3 ⊢
  wpx [W_0, W_90, W_11, o0, o7, o1, lf_xz, BitVec.xor_self, BitVec.setWidth_zero, BitVec.and_self, beq_iff_eq,
    beq_eq_false_iff_ne, ne_eq, beq_self_eq_true, not_true_eq_false, not_false_eq_true, false_implies,
    Bool.true_eq_false, Bool.false_eq_true, implies_true]
  all_goals repeat' (first
    | exact rfl
    | assumption
    | exact trivial
    | (intro hh; exact absurd hh h)
    | (intro hh; exact absurd hh (by decide))
    | apply And.intro
    | intro _)

/-- The loop's head to the `call`. -/
theorem vc_40 {g : Gprs} {f : Rflags} {V : Addr → Byte} (f0 : ∀ i < 8, Foot F.data (Addr.add g.rbp i))
    (f12 : ∀ i < 8, Foot F.data (Addr.add g.r12 i))
    (fi : ∀ i < 8, Foot F.data (Addr.add (rdq(V, g.rbp) + BitVec.setWidth 64 (BitVec.setWidth 32 g.rbx) * 8#64) i))
    (fp : ∀ i < 8, Foot F.data (Addr.add (ia V g) i)) :
    W_40 F Wl (fun j' g' _ V' => j' = 57 ∧ g' = gC V g ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [gC, ia] at f0 f12 fi fp ⊢
  wpx [W_40, o3]
  all_goals repeat' (first
    | exact rfl
    | assumption
    | exact trivial
    | apply And.intro
    | intro _)

/-- `eax` = `i` and the pops: the `ret` at 72. -/
abbrev gZ (V : Addr → Byte) (g : Gprs) : Gprs :=
  { g with
    rax := BitVec.setWidth 64 (BitVec.setWidth 32 g.rbx), rbx := rdq(V, g.rsp), rbp := rdq(V, g.rsp + 8),
    r12 := rdq(V, g.rsp + 8 + 8), rsp := g.rsp + 8 + 8 + 8 }
/-- `i + 1`, back to the loop's head. -/
abbrev gN (g : Gprs) : Gprs := { g with rbx := BitVec.setWidth 64 (BitVec.setWidth 32 g.rbx + 1#32) }
/-- `eax` = -1 and the pops: the `ret` at 89. -/
abbrev gX (V : Addr → Byte) (g : Gprs) : Gprs :=
  { g with
    rax := BitVec.setWidth 64 4294967295#32, rbx := rdq(V, g.rsp), rbp := rdq(V, g.rsp + 8),
    r12 := rdq(V, g.rsp + 8 + 8), rsp := g.rsp + 8 + 8 + 8 }

/-- `CompareFileNames` gave 0: the pops, the `ret` at 72. -/
theorem vc_62z {g : Gprs} {f : Rflags} {V : Addr → Byte} (h : BitVec.setWidth 32 g.rax = 0)
    (p1 : ∀ i < 8, Foot F.data (Addr.add g.rsp i)) (p2 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8) i))
    (p3 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8 + 8) i)) :
    W_62 F Wl (fun j' g' _ V' => j' = 72 ∧ g' = gZ V g ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [gZ] at h p1 p2 p3 ⊢
  wpx [W_62, W_32, W_66, W_80, o4, o2, o5, o6, Op.cmpmr, BitVec.and_self, beq_iff_eq, beq_eq_false_iff_ne, ne_eq,
    Bool.not_eq_true', Bool.or_eq_true, Bool.or_eq_false_iff, decide_eq_true_eq, decide_eq_false_iff_not]
  all_goals repeat' (first
    | exact rfl
    | assumption
    | exact trivial
    | (intro hh; exact absurd h hh)
    | apply And.intro
    | intro _)

/-- Not 0 and `i + 1` below the count: back to the loop's head. -/
theorem vc_62n {g : Gprs} {f : Rflags} {V : Addr → Byte} (h : ¬BitVec.setWidth 32 g.rax = 0)
    (f8 : ∀ i < 4, Foot F.data (Addr.add (g.rbp + 8#64) i))
    (hc : ¬(rdd(V, g.rbp + 8#64).toNat < (BitVec.setWidth 32 g.rbx + 1#32).toNat ∨
      rdd(V, g.rbp + 8#64) = BitVec.setWidth 32 g.rbx + 1#32)) :
    W_62 F Wl (fun j' g' _ V' => j' = 40 ∧ g' = gN g ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [gN] at h f8 hc ⊢
  wpx [W_62, W_32, W_66, W_80, o4, o2, o5, o6, Op.cmpmr, BitVec.and_self, beq_iff_eq, beq_eq_false_iff_ne, ne_eq,
    Bool.not_eq_true', Bool.or_eq_true, Bool.or_eq_false_iff, decide_eq_true_eq, decide_eq_false_iff_not]
  all_goals repeat' (first
    | exact rfl
    | assumption
    | exact trivial
    | (intro hh; exact absurd hh hc)
    | (intro hh; exact absurd (show BitVec.setWidth 32 rax = 0 by simpa using hh) h)
    | apply And.intro
    | intro _)

/-- Not 0 and `i + 1` not below the count: the pops, the `ret` at 89. -/
theorem vc_62e {g : Gprs} {f : Rflags} {V : Addr → Byte} (h : ¬BitVec.setWidth 32 g.rax = 0)
    (f8 : ∀ i < 4, Foot F.data (Addr.add (g.rbp + 8#64) i))
    (hc : rdd(V, g.rbp + 8#64).toNat < (BitVec.setWidth 32 g.rbx + 1#32).toNat ∨
      rdd(V, g.rbp + 8#64) = BitVec.setWidth 32 g.rbx + 1#32)
    (p1 : ∀ i < 8, Foot F.data (Addr.add g.rsp i)) (p2 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8) i))
    (p3 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8 + 8) i)) :
    W_62 F Wl (fun j' g' _ V' => j' = 89 ∧ g' = gX V g ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [gX] at h f8 hc p1 p2 p3 ⊢
  wpx [W_62, W_32, W_66, W_80, o4, o2, o5, o6, Op.cmpmr, BitVec.and_self, beq_iff_eq, beq_eq_false_iff_ne, ne_eq,
    Bool.not_eq_true', Bool.or_eq_true, Bool.or_eq_false_iff, decide_eq_true_eq, decide_eq_false_iff_not]
  all_goals repeat' (first
    | exact rfl
    | assumption
    | exact trivial
    | (intro hh; exact absurd hc (not_or.2 hh))
    | (intro hh; exact absurd (show BitVec.setWidth 32 rax = 0 by simpa using hh) h)
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

/-- The stack's addresses. -/
theorem sp_c (S : Addr) (h : 32 ≤ S.toNat) :
    (S - 8).toNat = S.toNat - 8 ∧ (S - 8 - 8).toNat = S.toNat - 16 ∧ (S - 8 - 8 - 8).toNat = S.toNat - 24 ∧
    (S - 8#64).toNat = S.toNat - 8 ∧ (S - 16#64).toNat = S.toNat - 16 ∧ (S - 24#64).toNat = S.toNat - 24 ∧
    S - 8 - 8 = S - 16#64 ∧ S - 8 - 8 - 8 = S - 24#64 ∧ S - 24#64 - 8 = S - 32#64 ∧ S - 8 = S - 8#64 ∧
    S - 24#64 + 8 = S - 16#64 ∧ S - 24#64 + 8 + 8 = S - 8#64 ∧ S - 24#64 + 8 + 8 + 8 = S := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> bv_omega

/-- The stack's addresses from the bottom of the 32 bytes under `S`, or of the 32 bytes from `S - 24`. -/
theorem sp_w (S : Addr) :
    S - 8 = S - 32#64 + BitVec.ofNat 64 24 ∧ S - 8 - 8 = S - 32#64 + BitVec.ofNat 64 16 ∧
    S - 8 - 8 - 8 = S - 32#64 + BitVec.ofNat 64 8 ∧ S - 24#64 = S - 24#64 + BitVec.ofNat 64 0 ∧
    S - 24#64 + 8 = S - 24#64 + BitVec.ofNat 64 8 ∧ S - 24#64 + 8 + 8 = S - 24#64 + BitVec.ofNat 64 16 ∧
    S = S - 24#64 + BitVec.ofNat 64 24 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> bv_omega

/-- Footprint bytes from an offset `d` in a run of `m`. -/
theorem off_ft {R : List Rgn} {a : Addr} {m : Nat} (h : ∀ i < m, Foot R (Addr.add a i)) (d : Nat) {n : Nat}
    {x : Addr} (hx : x = a + BitVec.ofNat 64 d) (hd : d + n ≤ m) : ∀ i < n, Foot R (x.add i) := fun i hi => by
  subst hx
  have := h (d + i) (by omega)
  rwa [show Addr.add a (d + i) = (a + BitVec.ofNat 64 d).add i from by simp only [Addr.add]; bv_omega] at this

/-- Bytes `[a, a + m)` the function reads: in `F.data`, not wrapping, apart from the 32 bytes under `S` and the
return address at `S`. -/
structure RdOk (F : Footprint) (S a : Addr) (m : Nat) : Prop where
  ft : ∀ i < m, Foot F.data (Addr.add a i)
  fits : a.toNat + m ≤ 2 ^ 64
  apart : a.toNat + m ≤ S.toNat - 32 ∨ S.toNat + 8 ≤ a.toNat

/-- The number of pairs, at `this + 8` (the entry's registers `g₀`, bytes `V₀`). -/
abbrev nP (V₀ : Addr → Byte) (g₀ : Gprs) : Nat := rdd(V₀, g₀.rdi + 8#64).toNat
/-- The pairs' pointers. -/
abbrev its (V₀ : Addr → Byte) (g₀ : Gprs) : Addr := rdq(V₀, g₀.rdi)
/-- The `k`-th pair's pointer's address. -/
abbrev slot (V₀ : Addr → Byte) (g₀ : Gprs) (k : Nat) : Addr := its V₀ g₀ + BitVec.ofNat 64 k * 8#64
/-- The `k`-th pair. -/
abbrev itm (V₀ : Addr → Byte) (g₀ : Gprs) (k : Nat) : Addr := rdq(V₀, slot V₀ g₀ k)
/-- The `k`-th pair's prefix's characters. -/
abbrev nm (V₀ : Addr → Byte) (g₀ : Gprs) (k : Nat) : Addr := rdq(V₀, itm V₀ g₀ k)
/-- The characters of `prefix`. -/
abbrev pfx (V₀ : Addr → Byte) (g₀ : Gprs) : Addr := rdq(V₀, g₀.rsi)

/-- The bytes `V` read as at the entry. -/
structure Dat (V₀ : Addr → Byte) (g₀ : Gprs) (V : Addr → Byte) : Prop where
  n : rdd(V, g₀.rdi + 8#64) = rdd(V₀, g₀.rdi + 8#64)
  it : 0 < nP V₀ g₀ → rdq(V, g₀.rdi) = its V₀ g₀
  pf : 0 < nP V₀ g₀ → rdq(V, g₀.rsi) = pfx V₀ g₀
  sl : ∀ k < nP V₀ g₀, rdq(V, slot V₀ g₀ k) = itm V₀ g₀ k
  nm : ∀ k < nP V₀ g₀, rdq(V, itm V₀ g₀ k) = nm V₀ g₀ k

/-- In the loop: `Dat`, the three registers pushed and the return address `ra`. -/
structure Inv (V₀ : Addr → Byte) (g₀ : Gprs) (ra : Addr) (V : Addr → Byte) : Prop where
  d : Dat V₀ g₀ V
  r12 : rdq(V, g₀.rsp - 8#64) = g₀.r12
  rbp : rdq(V, g₀.rsp - 16#64) = g₀.rbp
  rbx : rdq(V, g₀.rsp - 24#64) = g₀.rbx
  ra : rdq(V, g₀.rsp) = ra

/-- The registers at the loop's head for the `i`-th pair. -/
structure Rg (g₀ g : Gprs) (i : Nat) : Prop where
  rsp : g.rsp = g₀.rsp - 24#64
  rbx : g.rbx = BitVec.ofNat 64 i
  rbp : g.rbp = g₀.rdi
  r12 : g.r12 = g₀.rsi
  r13 : g.r13 = g₀.r13
  r14 : g.r14 = g₀.r14
  r15 : g.r15 = g₀.r15

/-- The registers a function keeps, after its `ret`. -/
def Bk (g₀ g : Gprs) : Prop :=
  g.rsp = g₀.rsp + 8 ∧ g.rbx = g₀.rbx ∧ g.rbp = g₀.rbp ∧ g.r12 = g₀.r12 ∧ g.r13 = g₀.r13 ∧ g.r14 = g₀.r14 ∧
    g.r15 = g₀.r15

/-- The result `r` of `FindPairForPrefix` with `n` pairs, where `Same k` is: the `k`-th pair's prefix is
`prefix` (`CompareFileNames` gives 0). -/
def Res (Same : Nat → Prop) (n : Nat) (r : BitVec 64) : Prop :=
  (∃ i < n, r = BitVec.ofNat 64 i ∧ Same i ∧ ∀ k < i, ¬Same k) ∨
    (r = BitVec.setWidth 64 4294967295#32 ∧ ∀ k < n, ¬Same k)

/-- The bytes after the pushes. -/
theorem v1_rd (V₀ : Addr → Byte) (g₀ : Gprs) (hs : 32 ≤ g₀.rsp.toNat) {x : Addr} {m : Nat}
    (hx : x.toNat + m ≤ 2 ^ 64) (h : x.toNat + m ≤ g₀.rsp.toNat - 24 ∨ g₀.rsp.toNat ≤ x.toNat) :
    List.map (V1 V₀ g₀) (byteAddrs x m) = List.map V₀ (byteAddrs x m) := by
  obtain ⟨s8, s16, s24, -⟩ := sp_c g₀.rsp hs
  have hl := g₀.rsp.isLt
  dsimp only [V1]
  rw [Tun.rd_Vst (Vst (Vst V₀ (g₀.rsp - 8) (toBytesLE g₀.r12 8)) (g₀.rsp - 8 - 8) (toBytesLE g₀.rbp 8))
      (g₀.rsp - 8 - 8 - 8) (toBytesLE g₀.rbx 8) x m (by rw [toBytesLE_length]; omega) hx
      (by rw [toBytesLE_length]; omega),
    Tun.rd_Vst (Vst V₀ (g₀.rsp - 8) (toBytesLE g₀.r12 8)) (g₀.rsp - 8 - 8) (toBytesLE g₀.rbp 8) x m
      (by rw [toBytesLE_length]; omega) hx (by rw [toBytesLE_length]; omega),
    Tun.rd_Vst V₀ (g₀.rsp - 8) (toBytesLE g₀.r12 8) x m (by rw [toBytesLE_length]; omega) hx
      (by rw [toBytesLE_length]; omega)]

/-- The pushes: `Inv` with the entry's return address. -/
theorem inv1 (V₀ : Addr → Byte) (g₀ : Gprs) (hs : 32 ≤ g₀.rsp.toNat) (hs8 : g₀.rsp.toNat + 8 ≤ 2 ^ 64)
    (n8 : RdOk F g₀.rsp (g₀.rdi + 8#64) 4) (it : 0 < nP V₀ g₀ → RdOk F g₀.rsp g₀.rdi 8)
    (pf : 0 < nP V₀ g₀ → RdOk F g₀.rsp g₀.rsi 8) (sl : ∀ k < nP V₀ g₀, RdOk F g₀.rsp (slot V₀ g₀ k) 8)
    (nm' : ∀ k < nP V₀ g₀, RdOk F g₀.rsp (itm V₀ g₀ k) 8) {ra : Addr} (hra : rdq(V₀, g₀.rsp) = ra) :
    Inv V₀ g₀ ra (V1 V₀ g₀) := by
  obtain ⟨s8, s16, s24, t8, t16, t24, e16, e24, -, e8, -⟩ := sp_c g₀.rsp hs
  have hl := g₀.rsp.isLt
  have ap : ∀ {x : Addr} {m : Nat}, RdOk F g₀.rsp x m →
      List.map (V1 V₀ g₀) (byteAddrs x m) = List.map V₀ (byteAddrs x m) := fun h =>
    v1_rd V₀ g₀ hs h.fits (by have := h.apart; omega)
  refine ⟨⟨congrArg (ofBytesLE 32) (ap n8), fun h => congrArg (ofBytesLE 64) (ap (it h)),
    fun h => congrArg (ofBytesLE 64) (ap (pf h)), fun k hk => congrArg (ofBytesLE 64) (ap (sl k hk)),
    fun k hk => congrArg (ofBytesLE 64) (ap (nm' k hk))⟩, ?_, ?_, ?_,
    (congrArg (ofBytesLE 64) (v1_rd V₀ g₀ hs hs8 (Or.inr (Nat.le_refl _)))).trans hra⟩
  · rw [← e8]
    dsimp only [V1]
    rw [Tun.rd_Vst _ (g₀.rsp - 8 - 8 - 8) (toBytesLE g₀.rbx 8) _ 8 (by rw [toBytesLE_length]; omega)
        (by omega) (by rw [toBytesLE_length]; omega),
      Tun.rd_Vst _ (g₀.rsp - 8 - 8) (toBytesLE g₀.rbp 8) _ 8 (by rw [toBytesLE_length]; omega)
        (by omega) (by rw [toBytesLE_length]; omega),
      Tun.rd_Vst_self _ _ _ (toBytesLE_length _ _) (by omega)]
    exact ofBytesLE_toBytesLE (n := 8) rfl _
  · rw [← e16]
    dsimp only [V1]
    rw [Tun.rd_Vst _ (g₀.rsp - 8 - 8 - 8) (toBytesLE g₀.rbx 8) _ 8 (by rw [toBytesLE_length]; omega)
        (by omega) (by rw [toBytesLE_length]; omega),
      Tun.rd_Vst_self _ _ _ (toBytesLE_length _ _) (by omega)]
    exact ofBytesLE_toBytesLE (n := 8) rfl _
  · rw [← e24]
    dsimp only [V1]
    rw [Tun.rd_Vst_self _ _ _ (toBytesLE_length _ _) (by omega)]
    exact ofBytesLE_toBytesLE (n := 8) rfl _

/-! ## The run -/

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ X : State} {o : Oracle} {t : Nat}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {V₀ : Addr → Byte} {g₀ : Gprs} {Same : Nat → Prop} {e₂ : Addr} {code₂ : List Byte} {j₂ : Nat}

/-- What the run needs around the function: its code and `CompareFileNames`'s, the 32 bytes under the entry's `S`
it may store into, the 32 bytes from `S - 24` it reads (the registers pushed, the return address), and the bytes of
the pairs and of `prefix` it reads (`RdOk`). -/
structure Env (F : Footprint) (Wl : List Rgn) (L : List (Addr × List Byte)) (V₀ : Addr → Byte) (g₀ : Gprs) :
    Prop where
  code : CodeIn L ffp_at ffp
  cfn : ∃ code, CodeIn L cfn_at code ∧ 0 < code.length
  s0 : 32 ≤ g₀.rsp.toNat
  s8 : g₀.rsp.toNat + 8 ≤ 2 ^ 64
  w : ∀ i < 32, Foot Wl (Addr.add (g₀.rsp - 32#64) i)
  d : ∀ i < 32, Foot F.data (Addr.add (g₀.rsp - 24#64) i)
  n8 : RdOk F g₀.rsp (g₀.rdi + 8#64) 4
  it : 0 < nP V₀ g₀ → RdOk F g₀.rsp g₀.rdi 8
  pf : 0 < nP V₀ g₀ → RdOk F g₀.rsp g₀.rsi 8
  sl : ∀ k < nP V₀ g₀, RdOk F g₀.rsp (slot V₀ g₀ k) 8
  nm : ∀ k < nP V₀ g₀, RdOk F g₀.rsp (itm V₀ g₀ k) 8

/-- The pops' and the `ret`'s bytes. -/
theorem Env.ft (hE : Env F Wl L V₀ g₀) :
    (∀ m < 8, Foot F.data (Addr.add (g₀.rsp - 24#64) m)) ∧
    (∀ m < 8, Foot F.data (Addr.add (g₀.rsp - 24#64 + 8) m)) ∧
    (∀ m < 8, Foot F.data (Addr.add (g₀.rsp - 24#64 + 8 + 8) m)) ∧ (∀ m < 8, Foot F.data (Addr.add g₀.rsp m)) := by
  obtain ⟨-, -, -, a0, a8, a16, a24⟩ := sp_w g₀.rsp
  exact ⟨off_ft hE.d 0 a0 (by decide), off_ft hE.d 8 a8 (by decide), off_ft hE.d 16 a16 (by decide),
    off_ft hE.d 24 a24 (by decide)⟩

/-- The pushes' bytes. -/
theorem Env.wf (hE : Env F Wl L V₀ g₀) :
    (∀ m < 8, Foot Wl (Addr.add (g₀.rsp - 8) m)) ∧ (∀ m < 8, Foot Wl (Addr.add (g₀.rsp - 8 - 8) m)) ∧
    (∀ m < 8, Foot Wl (Addr.add (g₀.rsp - 8 - 8 - 8) m)) := by
  obtain ⟨a24, a16, a8, -⟩ := sp_w g₀.rsp
  exact ⟨off_ft hE.w 24 a24 (by decide), off_ft hE.w 16 a16 (by decide), off_ft hE.w 8 a8 (by decide)⟩

/-- What the function asks of `CompareFileNames` (at `cfn_at`) for the `i`-th pair: from its entry with `rsp` =
`S - 32`, the return address into the function there, `Inv` for the bytes `V` under it, `rdi` the `i`-th pair's
prefix's characters and `rsi` those of `prefix`, the run goes on to the goal if it does from every state at the
return address with `Inv`, `rsp` = `S - 24`, the registers a call keeps, and `eax` = 0 just when `Same i`. -/
def Cmp (prof : Profile) (F : Footprint) (Wl : List Rgn) (L : List (Addr × List Byte)) (s₀ : State) (o : Oracle)
    (gev : List Event) (gP : State → Nat → List Event → Prop) (gE : Outcome → List Event → Prop)
    (V₀ : Addr → Byte) (g₀ : Gprs) (ra : Addr) (Same : Nat → Prop) : Prop :=
  ∀ (i : Nat) (Y : State) (t : Nat) (V : Addr → Byte), i < nP V₀ g₀ → KeptW Wl s₀ Y → Inv V₀ g₀ ra V →
    Agree F Y.proc.mm.mem (Vst V (g₀.rsp - 32#64) (toBytesLE (ffp_at.add 62) 8)) → Y.cpu.rip = cfn_at →
    Y.cpu.gpr.rsp = g₀.rsp - 32#64 → Y.cpu.gpr.rdi = nm V₀ g₀ i → Y.cpu.gpr.rsi = pfx V₀ g₀ →
    (∀ (Z : State) (t' : Nat) (V' : Addr → Byte), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V' → Inv V₀ g₀ ra V' →
      Z.cpu.rip = ffp_at.add 62 → Z.cpu.gpr.rsp = g₀.rsp - 24#64 → Z.cpu.gpr.rbx = Y.cpu.gpr.rbx →
      Z.cpu.gpr.rbp = Y.cpu.gpr.rbp → Z.cpu.gpr.r12 = Y.cpu.gpr.r12 → Z.cpu.gpr.r13 = Y.cpu.gpr.r13 →
      Z.cpu.gpr.r14 = Y.cpu.gpr.r14 → Z.cpu.gpr.r15 = Y.cpu.gpr.r15 →
      (BitVec.setWidth 32 Z.cpu.gpr.rax = 0 ↔ Same i) → GoG prof L o gev gP gE Z t') →
    GoG prof L o gev gP gE Y t

/-- What the caller asks at the return address `ra`: the bytes `Dat`, the registers a call keeps, the result. -/
def Ret (prof : Profile) (F : Footprint) (Wl : List Rgn) (L : List (Addr × List Byte)) (s₀ : State) (o : Oracle)
    (gev : List Event) (gP : State → Nat → List Event → Prop) (gE : Outcome → List Event → Prop)
    (V₀ : Addr → Byte) (g₀ : Gprs) (ra : Addr) (Same : Nat → Prop) : Prop :=
  ∀ (Z : State) (t' : Nat) (V' : Addr → Byte), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V' → Dat V₀ g₀ V' →
    Z.cpu.rip = ra → Bk g₀ Z.cpu.gpr → Res Same (nP V₀ g₀) Z.cpu.gpr.rax → GoG prof L o gev gP gE Z t'

/-- From the loop's head for the `i`-th pair, none of the ones before it `Same`, the run goes on to the goal. -/
def At (prof : Profile) (F : Footprint) (Wl : List Rgn) (L : List (Addr × List Byte)) (s₀ : State) (o : Oracle)
    (gev : List Event) (gP : State → Nat → List Event → Prop) (gE : Outcome → List Event → Prop)
    (V₀ : Addr → Byte) (g₀ : Gprs) (ra : Addr) (Same : Nat → Prop) (i : Nat) : Prop :=
  ∀ (Y : State) (t : Nat) (V : Addr → Byte), KeptW Wl s₀ Y → Agree F Y.proc.mm.mem V → Inv V₀ g₀ ra V →
    Y.cpu.rip = ffp_at.add 40 → Rg g₀ Y.cpu.gpr i → (∀ k < i, ¬Same k) → GoG prof L o gev gP gE Y t

/-- A `ret` (at `j`) with `rsp` = `S`, the registers a call keeps and the result. -/
theorem fin (c : Seg prof F Wl L s₀ o) (hE : Env F Wl L V₀ g₀) (hin₂ : CodeIn L e₂ code₂)
    (h₂ : j₂ < code₂.length) (kE : Ret prof F Wl L s₀ o gev gP gE V₀ g₀ (e₂.add j₂) Same) {j : Nat} (hj : j < 96)
    (hd : Dec prof.feat ffp j (FV7z.mk .ret 64 [] 1)) {Y : State} {V : Addr → Byte} (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem V) (hD : Dat V₀ g₀ V) (hra : rdq(V, g₀.rsp) = e₂.add j₂)
    (hr : Y.cpu.rip = ffp_at.add j) (hs : Y.cpu.gpr.rsp = g₀.rsp) (hb : Y.cpu.gpr.rbx = g₀.rbx)
    (hp : Y.cpu.gpr.rbp = g₀.rbp) (h12 : Y.cpu.gpr.r12 = g₀.r12) (h13 : Y.cpu.gpr.r13 = g₀.r13)
    (h14 : Y.cpu.gpr.r14 = g₀.r14) (h15 : Y.cpu.gpr.r15 = g₀.r15) (hres : Res Same (nP V₀ g₀) Y.cpu.gpr.rax) :
    GoG prof L o gev gP gE Y t := by
  refine c.s_ret hK hA hE.code (lt_len hj) hr hd (fun m hm => by rw [hs]; exact hE.ft.2.2.2 m hm) hin₂ h₂
    (by rw [hs]; exact hra) ?_
  rintro Z t' hKZ hAZ ⟨hrZ, hgZ⟩
  refine kE Z t' V hKZ hAZ hD hrZ ?_ ?_
  · rw [hgZ]
    exact ⟨congrArg (· + 8) hs, hb, hp, h12, h13, h14, h15⟩
  · rw [hgZ]
    exact hres

/-- The `i`-th pair: the `call`, then the `ret` at 72 (`Same i`), the `i + 1`-th pair, or the `ret` at 89. -/
theorem lpHead {i : Nat} (c : Seg prof F Wl L s₀ o) (hE : Env F Wl L V₀ g₀) (hin₂ : CodeIn L e₂ code₂)
    (h₂ : j₂ < code₂.length) (hcmp : Cmp prof F Wl L s₀ o gev gP gE V₀ g₀ (e₂.add j₂) Same)
    (kE : Ret prof F Wl L s₀ o gev gP gE V₀ g₀ (e₂.add j₂) Same) (hi : i < nP V₀ g₀)
    (kn : i + 1 < nP V₀ g₀ → At prof F Wl L s₀ o gev gP gE V₀ g₀ (e₂.add j₂) Same (i + 1)) :
    At prof F Wl L s₀ o gev gP gE V₀ g₀ (e₂.add j₂) Same i := by
  intro Y t V hK hA hI hr hR hno
  have hn32 : nP V₀ g₀ < 2 ^ 32 := (rdd(V₀, g₀.rdi + 8#64)).isLt
  have hn : 0 < nP V₀ g₀ := by omega
  obtain ⟨-, -, -, -, -, -, -, -, x32, -, p16, p8, p0⟩ := sp_c g₀.rsp hE.s0
  obtain ⟨q0, q8, q16, -⟩ := hE.ft
  have hsw : BitVec.setWidth 64 (BitVec.setWidth 32 Y.cpu.gpr.rbx) = BitVec.ofNat 64 i := by
    rw [hR.rbx]
    exact sw32 (by omega)
  have ea : rdq(V, Y.cpu.gpr.rbp) + BitVec.setWidth 64 (BitVec.setWidth 32 Y.cpu.gpr.rbx) * 8#64 =
      slot V₀ g₀ i := by
    rw [hsw, hR.rbp, hI.d.it hn]
  have eia : ia V Y.cpu.gpr = itm V₀ g₀ i := by
    show rdq(V, rdq(V, Y.cpu.gpr.rbp) + BitVec.setWidth 64 (BitVec.setWidth 32 Y.cpu.gpr.rbx) * 8#64) = _
    rw [ea, hI.d.sl i hi]
  -- to the `call`
  refine (c_40 prof).run c hE.code (fun j' g' _ V' => j' = 57 ∧ g' = gC V Y.cpu.gpr ∧ V' = V) hK hA hr
    (vc_40 (fun m hm => by rw [hR.rbp]; exact (hE.it hn).ft m hm) (fun m hm => by rw [hR.r12]; exact (hE.pf hn).ft m hm)
      (fun m hm => by rw [ea]; exact (hE.sl i hi).ft m hm) (fun m hm => by rw [eia]; exact (hE.nm i hi).ft m hm)) ?_
  rintro j' g fl V₁ ⟨rfl, rfl, hV₁⟩ Y₁ t₁ hK₁ hA₁ hr₁ hg₁ -
  subst V₁
  obtain ⟨codeC, hinC, hC0⟩ := hE.cfn
  have hsY : Y₁.cpu.gpr.rsp = g₀.rsp - 24#64 := by rw [hg₁]; exact hR.rsp
  refine c.s_call hK₁ hA₁ hE.code (lt_len (by decide)) hr₁ (call_57 _) hinC hC0 tgt57
    (fun m hm => by rw [hsY, x32]; exact hE.w m (by omega)) ?_
  rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
  rw [hsY, x32] at hA₂
  have hg₂' : Y₂.cpu.gpr = (gC V Y.cpu.gpr).set 4 (g₀.rsp - 32#64) := by
    rw [hg₂, hg₁]
    exact congrArg (fun v => (gC V Y.cpu.gpr).set 4 v) ((congrArg (· - 8) hR.rsp).trans x32)
  -- `CompareFileNames`
  refine hcmp i Y₂ t₂ V hi hK₂ hI hA₂ hr₂ (by rw [hg₂']; rfl)
    (by rw [hg₂']; show rdq(V, ia V Y.cpu.gpr) = _; rw [eia, hI.d.nm i hi])
    (by rw [hg₂']; show rdq(V, Y.cpu.gpr.r12) = _; rw [hR.r12, hI.d.pf hn]) ?_
  intro Z t' V' hKZ hAZ hI' hrZ zs hzb hzp hz12 hz13 hz14 hz15 hsame
  rw [hg₂'] at hzb hzp hz12 hz13 hz14 hz15
  have zb : Z.cpu.gpr.rbx = BitVec.ofNat 64 i := hzb.trans hR.rbx
  have zp : Z.cpu.gpr.rbp = g₀.rdi := hzp.trans hR.rbp
  have z12 : Z.cpu.gpr.r12 = g₀.rsi := hz12.trans hR.r12
  have z13 : Z.cpu.gpr.r13 = g₀.r13 := hz13.trans hR.r13
  have z14 : Z.cpu.gpr.r14 = g₀.r14 := hz14.trans hR.r14
  have z15 : Z.cpu.gpr.r15 = g₀.r15 := hz15.trans hR.r15
  by_cases hS : Same i
  · -- found: the `ret` at 72
    refine (c_62 prof).run c hE.code (fun j' g' _ V'' => j' = 72 ∧ g' = gZ V' Z.cpu.gpr ∧ V'' = V') hKZ hAZ hrZ
      (vc_62z (hsame.2 hS) (by rw [zs]; exact q0) (by rw [zs]; exact q8) (by rw [zs]; exact q16)) ?_
    rintro j' g fl V₂ ⟨rfl, rfl, hV₂⟩ Y₃ t₃ hK₃ hA₃ hr₃ hg₃ -
    subst V₂
    have hrx : (gZ V' Z.cpu.gpr).rax = BitVec.ofNat 64 i := by
      show BitVec.setWidth 64 (BitVec.setWidth 32 Z.cpu.gpr.rbx) = _
      rw [zb]
      exact sw32 (by omega)
    exact fin c hE hin₂ h₂ kE (by decide) (ret_72 _) hK₃ hA₃ hI'.d hI'.ra hr₃
      (by rw [hg₃]; show Z.cpu.gpr.rsp + 8 + 8 + 8 = _; rw [zs]; exact p0)
      (by rw [hg₃]; show rdq(V', Z.cpu.gpr.rsp) = _; rw [zs]; exact hI'.rbx)
      (by rw [hg₃]; show rdq(V', Z.cpu.gpr.rsp + 8) = _; rw [zs, p16]; exact hI'.rbp)
      (by rw [hg₃]; show rdq(V', Z.cpu.gpr.rsp + 8 + 8) = _; rw [zs, p8]; exact hI'.r12)
      (by rw [hg₃]; exact z13) (by rw [hg₃]; exact z14) (by rw [hg₃]; exact z15)
      (Or.inl ⟨i, hi, by rw [hg₃]; exact hrx, hS, hno⟩)
  have hz : ¬BitVec.setWidth 32 Z.cpu.gpr.rax = 0 := fun h => hS (hsame.1 h)
  by_cases hlt : i + 1 < nP V₀ g₀
  · -- the next pair
    refine (c_62 prof).run c hE.code (fun j' g' _ V'' => j' = 40 ∧ g' = gN Z.cpu.gpr ∧ V'' = V') hKZ hAZ hrZ
      (vc_62n hz (by rw [zp]; exact hE.n8.ft) (by rw [zp, zb, hI'.d.n]; exact cmp_lt hlt)) ?_
    rintro j' g fl V₂ ⟨rfl, rfl, hV₂⟩ Y₃ t₃ hK₃ hA₃ hr₃ hg₃ -
    subst V₂
    have hbx : (gN Z.cpu.gpr).rbx = BitVec.ofNat 64 (i + 1) := by
      show BitVec.setWidth 64 (BitVec.setWidth 32 Z.cpu.gpr.rbx + 1#32) = _
      rw [zb]
      exact inc32 (by omega)
    refine kn hlt Y₃ t₃ V' hK₃ hA₃ hI' hr₃ ?_ ?_
    · rw [hg₃]
      exact ⟨zs, hbx, zp, z12, z13, z14, z15⟩
    · intro k hk
      rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | rfl
      · exact hno k hk
      · exact hS
  · -- none: the `ret` at 89
    refine (c_62 prof).run c hE.code (fun j' g' _ V'' => j' = 89 ∧ g' = gX V' Z.cpu.gpr ∧ V'' = V') hKZ hAZ hrZ
      (vc_62e hz (by rw [zp]; exact hE.n8.ft) (by rw [zp, zb, hI'.d.n]; exact cmp_ge hi hlt) (by rw [zs]; exact q0)
        (by rw [zs]; exact q8) (by rw [zs]; exact q16)) ?_
    rintro j' g fl V₂ ⟨rfl, rfl, hV₂⟩ Y₃ t₃ hK₃ hA₃ hr₃ hg₃ -
    subst V₂
    exact fin c hE hin₂ h₂ kE (by decide) (ret_89 _) hK₃ hA₃ hI'.d hI'.ra hr₃
      (by rw [hg₃]; show Z.cpu.gpr.rsp + 8 + 8 + 8 = _; rw [zs]; exact p0)
      (by rw [hg₃]; show rdq(V', Z.cpu.gpr.rsp) = _; rw [zs]; exact hI'.rbx)
      (by rw [hg₃]; show rdq(V', Z.cpu.gpr.rsp + 8) = _; rw [zs, p16]; exact hI'.rbp)
      (by rw [hg₃]; show rdq(V', Z.cpu.gpr.rsp + 8 + 8) = _; rw [zs, p8]; exact hI'.r12)
      (by rw [hg₃]; exact z13) (by rw [hg₃]; exact z14) (by rw [hg₃]; exact z15)
      (Or.inr ⟨by rw [hg₃], fun k hk => by
        rcases Nat.lt_succ_iff_lt_or_eq.1 (show k < i + 1 by omega) with hk | rfl
        · exact hno k hk
        · exact hS⟩)

/-- The pairs from any one: by the number left. -/
theorem lpAll (c : Seg prof F Wl L s₀ o) (hE : Env F Wl L V₀ g₀) (hin₂ : CodeIn L e₂ code₂)
    (h₂ : j₂ < code₂.length) (hcmp : Cmp prof F Wl L s₀ o gev gP gE V₀ g₀ (e₂.add j₂) Same)
    (kE : Ret prof F Wl L s₀ o gev gP gE V₀ g₀ (e₂.add j₂) Same) :
    ∀ (m i : Nat), i + m + 1 = nP V₀ g₀ → At prof F Wl L s₀ o gev gP gE V₀ g₀ (e₂.add j₂) Same i
  | 0, _, h => lpHead c hE hin₂ h₂ hcmp kE (by omega) fun h' => absurd h' (by omega)
  | m + 1, i, h => lpHead c hE hin₂ h₂ hcmp kE (by omega) fun _ => lpAll c hE hin₂ h₂ hcmp kE m (i + 1) (by omega)

/-- `CCensor::FindPairForPrefix (prefix)` (`this` = `rdi`, `&prefix` = `rsi`, the entry's bytes `V`): if
`CompareFileNames` runs for each pair as `Cmp` says (`eax` = 0 just when `Same i`), the run reaches the return
address with the bytes it read as they were, the registers a call keeps, and in `rax` the first `i` with `Same i`,
or -1 (`eax`) if there is none (`Res`). -/
theorem ffp_ok (c : Seg prof F Wl L s₀ o) {V : Addr → Byte} (hE : Env F Wl L V X.cpu.gpr) (hK : KeptW Wl s₀ X)
    (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = ffp_at) (hin₂ : CodeIn L e₂ code₂) (h₂ : j₂ < code₂.length)
    (hra : rdq(V, X.cpu.gpr.rsp) = e₂.add j₂)
    (hcmp : Cmp prof F Wl L s₀ o gev gP gE V X.cpu.gpr (e₂.add j₂) Same)
    (kE : Ret prof F Wl L s₀ o gev gP gE V X.cpu.gpr (e₂.add j₂) Same) :
    GoG prof L o gev gP gE X t := by
  obtain ⟨-, -, -, -, -, -, -, x24, -⟩ := sp_c X.cpu.gpr.rsp hE.s0
  by_cases h0 : rdd(V, X.cpu.gpr.rdi + 8#64) = 0#32
  · -- no pairs: the `ret` at 95
    refine (c_0 prof).run c hE.code (fun j' g' _ V' => j' = 95 ∧
        g' = { X.cpu.gpr with rax := BitVec.setWidth 64 4294967295#32 } ∧ V' = V) hK hA
      (by rw [addr_add_zero]; exact hrip) (vc_0z h0 hE.n8.ft) ?_
    rintro j' g fl V₁ ⟨rfl, rfl, hV₁⟩ Y t₁ hKY hAY hrY hgY -
    subst V₁
    have hn0 : nP V X.cpu.gpr = 0 := by
      show rdd(V, X.cpu.gpr.rdi + 8#64).toNat = 0
      rw [h0]
      rfl
    exact fin c hE hin₂ h₂ kE (by decide) (ret_95 _) hKY hAY
      ⟨rfl, fun _ => rfl, fun _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩ hra hrY (by rw [hgY]) (by rw [hgY])
      (by rw [hgY]) (by rw [hgY]) (by rw [hgY]) (by rw [hgY]) (by rw [hgY])
      (Or.inr ⟨by rw [hgY], fun k hk => absurd hk (by omega)⟩)
  · -- the pushes, then the loop from the first pair
    obtain ⟨w1, w2, w3⟩ := hE.wf
    refine (c_0 prof).run c hE.code (fun j' g' _ V' => j' = 40 ∧ g' = g40 V X.cpu.gpr ∧ V' = V1 V X.cpu.gpr) hK hA
      (by rw [addr_add_zero]; exact hrip) (vc_0n h0 hE.n8.ft w1 w2 w3) ?_
    rintro j' g fl V₁ ⟨rfl, rfl, hV₁⟩ Y t₁ hKY hAY hrY hgY -
    subst V₁
    have hn : 0 < nP V X.cpu.gpr := by
      have : rdd(V, X.cpu.gpr.rdi + 8#64).toNat ≠ 0 := fun h => h0 (BitVec.eq_of_toNat_eq h)
      show 0 < rdd(V, X.cpu.gpr.rdi + 8#64).toNat
      omega
    exact lpAll c hE hin₂ h₂ hcmp kE (nP V X.cpu.gpr - 1) 0 (by omega) Y t₁ _ hKY hAY
      (inv1 V X.cpu.gpr hE.s0 hE.s8 hE.n8 hE.it hE.pf hE.sl hE.nm hra) hrY
      ⟨by rw [hgY]; exact x24, by rw [hgY], by rw [hgY], by rw [hgY], by rw [hgY], by rw [hgY], by rw [hgY]⟩
      (fun k hk => absurd hk (Nat.not_lt_zero k))

end FV7z.Ffp
