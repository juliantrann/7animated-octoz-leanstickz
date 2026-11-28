import FV7z.Fnd.Cuts
import FV7z.Fdn.Blocks
import FV7z.Aac.Blocks
import FV7z.Ffp.Holds
import FV7z.Lemmas.LeafRet
import FV7z.Lemmas.FnFar
import FV7z.Lemmas.Lock2
import FV7z.Tun.Inv
/-!
# `CFileInfo::Find` (PLAN.md §M, M1)

7-Zip 26.06's `NWindows::NFile::NFind::CFileInfo::Find (CFSTR path, bool followLink)` at `0x455b80` in `7zzs`
(`CPP/Windows/FileFind.cpp`), `this` in `rdi`, `path` in `rsi`, `followLink` in `dl`: `push r12; movzx edx, dl;
push rbp; mov rbp, rsi; push rbx; mov rbx, rdi`, the `call` (17) of `Find_DontFill_Base (path, followLink)`
(`Fdn.fdn_at`); `mov r12d, eax; test al, al; je 122`. Then the name: the bytes of `path` from `rbp`, `rax` one
ahead, `rcx` the byte before it; a '/' with a byte after it moves `rbp` to that byte (the loop at 58, through 48, 52,
66, 70), the first 0 ends it (80): `lea rdi, [rbx + 0x68]; mov rsi, rbp`, the `call` (87) of
`AString::operator= (const char *)` (`Aac.aac_at`) on `Name`; at 92 a '/' at the end of `Name` (non-empty) is cut off
(`Trm`). At 122 `mov eax, r12d`, the pops and the `ret` (129).

The callees are hypotheses, as in `FV7z/Mgt/Holds.lean` and `FV7z/Ndp/Holds.lean`: `Find_DontFill_Base` a
continuation at its entry (`k1`), given the run from its return (`rsp` 24 below the entry's, `rbx` = `this`, `rbp` =
`path`, the saved registers and the return address as they were (`StkF`), the path a string of `n` bytes (`Pth`) and
its own post `P1`); `AString::operator=` likewise (`k2`, `KAac`: the name at `path + nl … (n - 1)`; from its return the
footprints of the cut (`TlF`), the stack as it was in its bytes and in those after the cut, and its post `P2`).

- `bt`, `nl`, `Pth`: the path's bytes; where the name starts (after the last '/' a byte follows); the string.
- `Fr`, `Fm`, `KS`: registers kept by a piece; the frame from 22 on; the callee-saved registers as they were.
- `Trm`, `TlF`: the bytes after the cut at 112, and the footprints of the reads and stores from 92.
- `vc_0`, `vc_22`, `vc_52`, `vc_58`, `vc_80`, `vc_92`, `vc_122`: the pieces' verification conditions.
- `tail122`: from 122 to the return address; `from80`: from 80 through `operator=`; `lpHead`, `lpAll`: the loop at 58,
  by the number of bytes left; `fnd_ok`: the function.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Fnd
set_option linter.unusedVariables false

/-! ## The instructions outside the blocks -/

/-- The `call` of `Find_DontFill_Base`. -/
def pc1 : List Byte := [0xe8, 0x6a, 0xff, 0xff, 0xff]
theorem pc1_0 : ∀ feat, Dec feat pc1 0 (FV7z.mk .call 64 [.rel 18446744073709551466] 5) := by dec_rfl
theorem wc_17 : pc1 <+: fnd.drop 17 := by decide +kernel
theorem call_17 (feat : Features) : Dec feat fnd 17 (FV7z.mk .call 64 [.rel 18446744073709551466] 5) :=
  Dec.shift (j := 17) (k := 0) (pc1_0 feat) wc_17 (Nat.zero_le _)
theorem tgt_17 : fnd_at.add (17 + 5) + BitVec.ofNat 64 18446744073709551466 = Fdn.fdn_at.add 0 := by decide

/-- The `call` of `AString::operator= (const char *)`. -/
def pc2 : List Byte := [0xe8, 0xe4, 0x68, 0xff, 0xff]
theorem pc2_0 : ∀ feat, Dec feat pc2 0 (FV7z.mk .call 64 [.rel 18446744073709512932] 5) := by dec_rfl
theorem wc_87 : pc2 <+: fnd.drop 87 := by decide +kernel
theorem call_87 (feat : Features) : Dec feat fnd 87 (FV7z.mk .call 64 [.rel 18446744073709512932] 5) :=
  Dec.shift (j := 87) (k := 0) (pc2_0 feat) wc_87 (Nat.zero_le _)
theorem tgt_87 : fnd_at.add (87 + 5) + BitVec.ofNat 64 18446744073709512932 = Aac.aac_at.add 0 := by decide

/-- The `ret`. -/
def pret : List Byte := [0xc3]
theorem pret_0 : ∀ feat, Dec feat pret 0 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem w_129 : pret <+: fnd.drop 129 := by decide +kernel
theorem ret_129 (feat : Features) : Dec feat fnd 129 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 129) (k := 0) (pret_0 feat) w_129 (Nat.zero_le _)

/-! ## Arithmetic -/

theorem a0 (p : Addr) : p + BitVec.ofNat 64 0 = p := by bv_omega
theorem inc1 (p : Addr) (k : Nat) : p + BitVec.ofNat 64 k + 1#64 = p + BitVec.ofNat 64 (k + 1) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.reducePow]
  omega
theorem q1 (S : Addr) : S - 8 - 8 - 8 + 8 = S - 8 - 8 := by bv_omega
theorem q2 (S : Addr) : S - 8 - 8 - 8 + 8 + 8 = S - 8 := by bv_omega
theorem q3 (S : Addr) : S - 8 - 8 - 8 + 8 + 8 + 8 = S := by bv_omega

/-! ## The path and the name -/

/-- The `j`-th byte of the path at `p`. -/
abbrev bt (V : Addr → Byte) (p : Addr) (j : Nat) : Byte := V (p + BitVec.ofNat 64 j)

/-- Where the name starts, from the first `k + 1` bytes: after the last '/' among the first `k` (a byte follows it),
else 0. -/
def nl (V : Addr → Byte) (p : Addr) : Nat → Nat
  | 0 => 0
  | k + 1 => if bt V p k = 47#8 then k + 1 else nl V p k

theorem nl_zero (V : Addr → Byte) (p : Addr) : nl V p 0 = 0 := rfl
theorem nl_succ (V : Addr → Byte) (p : Addr) (k : Nat) :
    nl V p (k + 1) = if bt V p k = 47#8 then k + 1 else nl V p k := rfl

/-- The path: `n` bytes not 0, then a 0, all of them readable. -/
structure Pth (F : Footprint) (V : Addr → Byte) (p : Addr) (n : Nat) : Prop where
  z : bt V p n = 0
  nz : ∀ j < n, ¬bt V p j = 0
  ft : ∀ j ≤ n, ∀ i < 1, Foot F.data (Addr.add (p + BitVec.ofNat 64 j) i)

/-! ## Registers -/

/-- What a piece keeps: `rsp`, `rbx`, `r13`–`r15`. -/
abbrev Fr (g g' : Gprs) : Prop :=
  g'.rsp = g.rsp ∧ g'.rbx = g.rbx ∧ g'.r13 = g.r13 ∧ g'.r14 = g.r14 ∧ g'.r15 = g.r15

/-- The frame from 22 on: the three pushes, `rbx` = `this`, `r13`–`r15` as at the entry (`S`, `g0`). -/
abbrev Fm (S : Addr) (g0 g : Gprs) : Prop :=
  g.rsp = S - 8 - 8 - 8 ∧ g.rbx = g0.rdi ∧ g.r13 = g0.r13 ∧ g.r14 = g0.r14 ∧ g.r15 = g0.r15

theorem Fm.fr {S : Addr} {g0 g g' : Gprs} (h : Fm S g0 g) (h' : Fr g g') : Fm S g0 g' :=
  ⟨h'.1.trans h.1, h'.2.1.trans h.2.1, h'.2.2.1.trans h.2.2.1, h'.2.2.2.1.trans h.2.2.2.1,
    h'.2.2.2.2.trans h.2.2.2.2⟩

/-- The callee-saved registers as they were. -/
abbrev KS (g g' : Gprs) : Prop :=
  g'.rbx = g.rbx ∧ g'.rbp = g.rbp ∧ g'.r12 = g.r12 ∧ g'.r13 = g.r13 ∧ g'.r14 = g.r14 ∧ g'.r15 = g.r15

/-- The saved `rbx`, `rbp`, `r12` and the return address `ra` in the bytes `W`. -/
abbrev StkF (W : Addr → Byte) (S : Addr) (g0 : Gprs) (ra : Addr) : Prop :=
  rdq(W, S - 8 - 8 - 8) = g0.rbx ∧ rdq(W, S - 8 - 8 - 8 + 8) = g0.rbp ∧ rdq(W, S - 8 - 8 - 8 + 8 + 8) = g0.r12 ∧
    rdq(W, S) = ra

/-- The frame's bytes readable. -/
abbrev FtsF (F : Footprint) (S : Addr) : Prop :=
  (∀ i < 8, Foot F.data (Addr.add (S - 8 - 8 - 8) i)) ∧ (∀ i < 8, Foot F.data (Addr.add (S - 8 - 8 - 8 + 8) i)) ∧
    (∀ i < 8, Foot F.data (Addr.add (S - 8 - 8 - 8 + 8 + 8) i)) ∧ ∀ i < 8, Foot F.data (Addr.add S i)

/-- The bytes after the cut at 112 (`b` = `this`): `Name._len` one less, a 0 where the '/' was. -/
abbrev Trm (V : Addr → Byte) (b : Addr) : Addr → Byte :=
  Vst (Vst V (b + 112#64) (toBytesLE (rdd(V, b + 112#64) - 1#32) 4))
    (rdq(V, b + 104#64) + BitVec.setWidth 64 (rdd(V, b + 112#64) - 1#32)) (toBytesLE 0#8 1)

/-- The footprints from 92 (`b` = `this`): `Name._len`; if not 0, `Name._chars` and its last byte; if that is '/',
the stores. -/
structure TlF (F : Footprint) (Wl : List Rgn) (V : Addr → Byte) (b : Addr) : Prop where
  n4 : ∀ i < 4, Foot F.data (Addr.add (b + 112#64) i)
  c8 : ¬rdd(V, b + 112#64) = 0 → ∀ i < 8, Foot F.data (Addr.add (b + 104#64) i)
  l1 : ¬rdd(V, b + 112#64) = 0 → ∀ i < 1,
    Foot F.data (Addr.add (rdq(V, b + 104#64) + BitVec.setWidth 64 rdd(V, b + 112#64) + 18446744073709551615#64) i)
  w4 : ¬rdd(V, b + 112#64) = 0 →
    V (rdq(V, b + 104#64) + BitVec.setWidth 64 rdd(V, b + 112#64) + 18446744073709551615#64) = 47#8 →
    ∀ i < 4, Foot Wl (Addr.add (b + 112#64) i)
  w1 : ¬rdd(V, b + 112#64) = 0 →
    V (rdq(V, b + 104#64) + BitVec.setWidth 64 rdd(V, b + 112#64) + 18446744073709551615#64) = 47#8 →
    ∀ i < 1, Foot Wl (Addr.add (rdq(V, b + 104#64) + BitVec.setWidth 64 (rdd(V, b + 112#64) - 1#32)) i)

/-! ## The pieces -/

variable {F : Footprint} {Wl : List Rgn}

/-- The pushes, `edx` = `dl`, `rbp` = `path`, `rbx` = `this`, to the first `call`. -/
theorem vc_0 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (hs1 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8) i)) (hs2 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8) i))
    (hs3 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8 - 8) i))
    (h : ∀ g', g'.rsp = g.rsp - 8 - 8 - 8 → g'.rdi = g.rdi → g'.rsi = g.rsi →
      g'.rdx = BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.setWidth 8 g.rdx)) → g'.rbx = g.rdi →
      g'.rbp = g.rsi → g'.r12 = g.r12 → g'.r13 = g.r13 → g'.r14 = g.r14 → g'.r15 = g.r15 →
      ∀ fl, Q 17 g' fl (Ffp.V1 V g)) :
    W_0 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [Ffp.V1] at hs1 hs2 hs3 h ⊢
  wpx [W_0, o0, Op.zxr]
  all_goals repeat' (first
    | refine h _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ _
    | with_reducible rfl
    | with_reducible exact hs1
    | with_reducible exact hs2
    | with_reducible exact hs3
    | apply And.intro
    | intro _)

/-- Back from `Find_DontFill_Base` at 22: `r12d` = `eax`; `al` = 0 to 122; else the first byte of the path: 0 to 80,
else to the loop at 58 with `rax` one ahead. -/
theorem vc_22 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (fb : ∀ i < 1, Foot F.data (Addr.add g.rbp i))
    (h122 : BitVec.setWidth 8 g.rax = 0 → ∀ g', g'.r12 = BitVec.setWidth 64 (BitVec.setWidth 32 g.rax) →
      Fr g g' → ∀ fl, Q 122 g' fl V)
    (h80 : ¬BitVec.setWidth 8 g.rax = 0 → V g.rbp = 0 → ∀ g', g'.rbp = g.rbp →
      g'.r12 = BitVec.setWidth 64 (BitVec.setWidth 32 g.rax) → Fr g g' → ∀ fl, Q 80 g' fl V)
    (h58 : ¬BitVec.setWidth 8 g.rax = 0 → ¬V g.rbp = 0 → ∀ g', g'.rax = g.rbp + 1#64 →
      g'.rcx = BitVec.setWidth 64 (BitVec.setWidth 32 (V g.rbp)) → g'.rbp = g.rbp →
      g'.r12 = BitVec.setWidth 64 (BitVec.setWidth 32 g.rax) → Fr g g' → ∀ fl, Q 58 g' fl V) :
    W_22 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at fb h122 h80 h58 ⊢
  wpx [W_22, W_29, W_41, o1, o2, Tun.rd1, Tun.sw_8_32_8, BitVec.and_self, beq_iff_eq, beq_eq_false_iff_ne, ne_eq,
    Bool.not_eq_true', Bool.not_eq_false', decide_eq_true_eq, decide_eq_false_iff_not]
  all_goals repeat' (first
    | refine h122 (by assumption) _ ?_ ?_ _
    | refine h80 (by assumption) (by assumption) _ ?_ ?_ ?_ _
    | refine h58 (by assumption) (by assumption) _ ?_ ?_ ?_ ?_ ?_ _
    | with_reducible rfl
    | with_reducible exact fb
    | apply And.intro
    | intro _)

/-- `add rax, 1; mov ecx, edx` back to 58. -/
theorem vc_52 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (h : ∀ g', g'.rax = g.rax + 1#64 → g'.rcx = BitVec.setWidth 64 (BitVec.setWidth 32 g.rdx) → g'.rbp = g.rbp →
      g'.r12 = g.r12 → Fr g g' → ∀ fl, Q 58 g' fl V) :
    W_52 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h ⊢
  wpx [W_52, o4]
  all_goals repeat' (first
    | refine h _ ?_ ?_ ?_ ?_ ?_ _
    | with_reducible rfl
    | apply And.intro
    | intro _)

/-- The loop at 58 (`cl` = `c`, the byte before `rax`): the byte at `rax` 0 to 80; else to 52, `rbp` = `rax` if `c`
is '/'. -/
theorem vc_58 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} {c : Byte}
    (hx : g.rcx = BitVec.setWidth 64 (BitVec.setWidth 32 c)) (fb : ∀ i < 1, Foot F.data (Addr.add g.rax i))
    (h80 : V g.rax = 0 → ∀ g', g'.rbp = g.rbp → g'.r12 = g.r12 → Fr g g' → ∀ fl, Q 80 g' fl V)
    (h52n : ¬c = 47#8 → ¬V g.rax = 0 → ∀ g', g'.rax = g.rax →
      g'.rdx = BitVec.setWidth 64 (BitVec.setWidth 32 (V g.rax)) → g'.rbp = g.rbp → g'.r12 = g.r12 → Fr g g' →
      ∀ fl, Q 52 g' fl V)
    (h52s : c = 47#8 → ¬V g.rax = 0 → ∀ g', g'.rax = g.rax →
      g'.rdx = BitVec.setWidth 64 (BitVec.setWidth 32 (V g.rax)) → g'.rbp = g.rax → g'.r12 = g.r12 → Fr g g' →
      ∀ fl, Q 52 g' fl V) :
    W_58 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hx fb h80 h52n h52s ⊢
  subst hx
  wpx [W_58, W_48, W_66, W_70, o5, o3, o6, Tun.rd1, Tun.sw_8_32_8, BitVec.and_self, beq_iff_eq,
    beq_eq_false_iff_ne, ne_eq, Bool.not_eq_true', Bool.not_eq_false', decide_eq_true_eq, decide_eq_false_iff_not]
  all_goals repeat' (first
    | refine h80 (by assumption) _ ?_ ?_ ?_ _
    | refine h52n (by assumption) (by assumption) _ ?_ ?_ ?_ ?_ ?_ _
    | refine h52s (by assumption) (by assumption) _ ?_ ?_ ?_ ?_ ?_ _
    | with_reducible rfl
    | with_reducible exact fb
    | apply And.intro
    | intro _)

/-- `lea rdi, [rbx + 0x68]; mov rsi, rbp` to the second `call`. -/
theorem vc_80 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (h : ∀ g', g'.rdi = g.rbx + 104#64 → g'.rsi = g.rbp → g'.r12 = g.r12 → Fr g g' → ∀ fl, Q 87 g' fl V) :
    W_80 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h ⊢
  wpx [W_80, o7]
  all_goals repeat' (first
    | refine h _ ?_ ?_ ?_ ?_ _
    | with_reducible rfl
    | apply And.intro
    | intro _)

/-- Back from `operator=` at 92: to 122 with the bytes as they were, or after the cut (`Trm`). -/
theorem vc_92 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} (hT : TlF F Wl V g.rbx)
    (hn : ∀ g', g'.r12 = g.r12 → Fr g g' → ∀ fl, Q 122 g' fl V)
    (ht : ∀ g', g'.r12 = g.r12 → Fr g g' → ∀ fl, Q 122 g' fl (Trm V g.rbx)) :
    W_92 F Wl Q g f V := by
  obtain ⟨n4, c8, l1, w4, w1⟩ := hT
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at n4 c8 l1 w4 w1 hn ht ⊢
  wpx [W_92, W_99, W_112, o8, o9, o10, Op.cmpmi, Tun.rd1, BitVec.and_self, beq_iff_eq, beq_eq_false_iff_ne, ne_eq,
    Bool.not_eq_true', Bool.not_eq_false', decide_eq_true_eq, decide_eq_false_iff_not]
  all_goals repeat' (first
    | refine ht _ ?_ ?_ _
    | refine hn _ ?_ ?_ _
    | with_reducible rfl
    | with_reducible exact n4
    | with_reducible exact c8 (by assumption)
    | with_reducible exact l1 (by assumption)
    | with_reducible exact w4 (by assumption) (by assumption)
    | with_reducible exact w1 (by assumption) (by assumption)
    | apply And.intro
    | intro _)

/-- The registers at the `ret`. -/
abbrev g122 (V : Addr → Byte) (g : Gprs) : Gprs :=
  { g with
    rax := BitVec.setWidth 64 (BitVec.setWidth 32 g.r12), rbx := rdq(V, g.rsp), rbp := rdq(V, g.rsp + 8),
    r12 := rdq(V, g.rsp + 8 + 8), rsp := g.rsp + 8 + 8 + 8 }

/-- `mov eax, r12d` and the pops to the `ret`. -/
theorem vc_122 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (p1 : ∀ i < 8, Foot F.data (Addr.add g.rsp i)) (p2 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8) i))
    (p3 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8 + 8) i)) (h : ∀ fl, Q 129 (g122 V g) fl V) :
    W_122 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [g122] at p1 p2 p3 h ⊢
  wpx [W_122, o11]
  all_goals repeat' (first
    | exact h _
    | with_reducible exact p1
    | with_reducible exact p2
    | with_reducible exact p3
    | apply And.intro
    | intro _)

/-! ## The runs -/

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {X : State} {t : Nat} {V : Addr → Byte} {e₂ : Addr} {code₂ : List Byte} {j₂ : Nat}

/-- From 122 (`r12` = `r`, the bytes `W`) to the return address `e₂.add j₂`, with `eax` = `r32`. -/
theorem tail122 {W : Addr → Byte} {S : Addr} {g0 : Gprs} {r : BitVec 64} {Y : State} (c : Seg prof F Wl L s₀ o)
    (hin : CodeIn L fnd_at fnd) (hK : KeptW Wl s₀ Y) (hA : Agree F Y.proc.mm.mem W)
    (hr : Y.cpu.rip = fnd_at.add 122) (hm : Fm S g0 Y.cpu.gpr) (h12 : Y.cpu.gpr.r12 = r)
    (hst : StkF W S g0 (e₂.add j₂)) (ft : FtsF F S) (hin₂ : CodeIn L e₂ code₂) (h₂ : j₂ < code₂.length)
    (k : ∀ (Z' : State) (t' : Nat), KeptW Wl s₀ Z' → Agree F Z'.proc.mm.mem W → Z'.cpu.rip = e₂.add j₂ →
      Z'.cpu.gpr.rsp = S + 8 → KS g0 Z'.cpu.gpr → Z'.cpu.gpr.rax = BitVec.setWidth 64 (BitVec.setWidth 32 r) →
      GoG prof L o gev gP gE Z' t') :
    GoG prof L o gev gP gE Y t := by
  obtain ⟨ms, mb, m13, m14, m15⟩ := hm
  obtain ⟨s1, s2, s3, s4⟩ := hst
  obtain ⟨f3, f2, f1, f0⟩ := ft
  refine (c_122 prof).run c hin (fun j' g' _ V' => j' = 129 ∧ g' = g122 W Y.cpu.gpr ∧ V' = W) hK hA hr
    (vc_122 (by rw [ms]; exact f3) (by rw [ms]; exact f2) (by rw [ms]; exact f1) fun _ => ⟨rfl, rfl, rfl⟩) ?_
  rintro j' g fl V₁ ⟨rfl, rfl, hV₁⟩ U t₁ hKU hAU hrU hgU -
  subst V₁
  have hsU : U.cpu.gpr.rsp = S := by
    rw [hgU]
    show Y.cpu.gpr.rsp + 8 + 8 + 8 = S
    rw [ms, q3]
  have e1 : rdq(W, Y.cpu.gpr.rsp) = g0.rbx := by rw [ms]; exact s1
  have e2 : rdq(W, Y.cpu.gpr.rsp + 8) = g0.rbp := by rw [ms]; exact s2
  have e3 : rdq(W, Y.cpu.gpr.rsp + 8 + 8) = g0.r12 := by rw [ms]; exact s3
  refine c.s_ret hKU hAU hin (lt_len (by decide)) hrU (ret_129 _) (by rw [hsU]; exact f0) hin₂ h₂
    (by rw [hsU]; exact s4) ?_
  rintro Z' t₂ hKZ' hAZ' ⟨hrZ', hgZ'⟩
  refine k Z' t₂ hKZ' hAZ' hrZ' ?_ ?_ ?_
  · rw [hgZ']
    show U.cpu.gpr.rsp + 8 = _
    rw [hsU]
  · rw [hgZ', hgU]
    exact ⟨e1, e2, e3, m13, m14, m15⟩
  · rw [hgZ', hgU]
    show BitVec.setWidth 64 (BitVec.setWidth 32 Y.cpu.gpr.r12) = _
    rw [h12]

/-- `AString::operator=` from the `call` at 87 (the bytes `V'`, `rsi` = `a`, `r12` = `r`): at its entry, and from
its return with the frame, `r12`, the footprints from 92, the stack in its bytes and in those after the cut, and
`P2`, the run goes on to the goal. -/
def KAac (prof : Profile) (F : Footprint) (Wl : List Rgn) (L : List (Addr × List Byte)) (s₀ : State) (o : Oracle)
    (gev : List Event) (gP : State → Nat → List Event → Prop) (gE : Outcome → List Event → Prop)
    (P2 : State → (Addr → Byte) → Prop) (S : Addr) (g0 : Gprs) (ra : Addr) (V' : Addr → Byte) (a : Addr)
    (r : BitVec 64) : Prop :=
  ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y →
    Agree F Y.proc.mm.mem (Vst V' (S - 8 - 8 - 8 - 8) (toBytesLE (fnd_at.add 92) 8)) →
    Y.cpu.rip = Aac.aac_at → Y.cpu.gpr.rsp = S - 8 - 8 - 8 - 8 → Y.cpu.gpr.rdi = g0.rdi + 104#64 →
    Y.cpu.gpr.rsi = a → Y.cpu.gpr.rbx = g0.rdi → Y.cpu.gpr.r12 = r → Y.cpu.gpr.r13 = g0.r13 →
    Y.cpu.gpr.r14 = g0.r14 → Y.cpu.gpr.r15 = g0.r15 →
    (∀ (Z₂ : State) (V₂ : Addr → Byte) (t'' : Nat), KeptW Wl s₀ Z₂ → Agree F Z₂.proc.mm.mem V₂ →
      Z₂.cpu.rip = fnd_at.add 92 → Fm S g0 Z₂.cpu.gpr → Z₂.cpu.gpr.r12 = r → TlF F Wl V₂ g0.rdi →
      StkF V₂ S g0 ra → StkF (Trm V₂ g0.rdi) S g0 ra → P2 Z₂ V₂ → GoG prof L o gev gP gE Z₂ t'') →
    GoG prof L o gev gP gE Y t'

/-- From 80 (`rbp` = `a`): the run goes on to the goal. -/
def ExL (prof : Profile) (F : Footprint) (Wl : List Rgn) (L : List (Addr × List Byte)) (s₀ : State) (o : Oracle)
    (gev : List Event) (gP : State → Nat → List Event → Prop) (gE : Outcome → List Event → Prop)
    (V : Addr → Byte) (S : Addr) (g0 : Gprs) (r : BitVec 64) (a : Addr) : Prop :=
  ∀ (Y : State) (t : Nat), KeptW Wl s₀ Y → Agree F Y.proc.mm.mem V → Y.cpu.rip = fnd_at.add 80 →
    Fm S g0 Y.cpu.gpr → Y.cpu.gpr.r12 = r → Y.cpu.gpr.rbp = a → GoG prof L o gev gP gE Y t

/-- At 58 with `j + 1` bytes of the path at `p` behind `rax`: the run goes on to the goal. -/
def AtL (prof : Profile) (F : Footprint) (Wl : List Rgn) (L : List (Addr × List Byte)) (s₀ : State) (o : Oracle)
    (gev : List Event) (gP : State → Nat → List Event → Prop) (gE : Outcome → List Event → Prop)
    (V : Addr → Byte) (S : Addr) (g0 : Gprs) (r : BitVec 64) (p : Addr) (j : Nat) : Prop :=
  ∀ (Y : State) (t : Nat), KeptW Wl s₀ Y → Agree F Y.proc.mm.mem V → Y.cpu.rip = fnd_at.add 58 →
    Fm S g0 Y.cpu.gpr → Y.cpu.gpr.r12 = r → Y.cpu.gpr.rax = p + BitVec.ofNat 64 (j + 1) →
    Y.cpu.gpr.rcx = BitVec.setWidth 64 (BitVec.setWidth 32 (bt V p j)) →
    Y.cpu.gpr.rbp = p + BitVec.ofNat 64 (nl V p j) → GoG prof L o gev gP gE Y t

/-- From 80: `rdi` = `&Name`, `rsi` = `rbp`, the `call` of `operator=`; from its return the cut or not, then 122. -/
theorem from80 {V' : Addr → Byte} {S : Addr} {g0 : Gprs} {r : BitVec 64} {a : Addr}
    {P2 : State → (Addr → Byte) → Prop} (c : Seg prof F Wl L s₀ o) (hin : CodeIn L fnd_at fnd)
    (hinA : CodeIn L Aac.aac_at Aac.aac) (hs4 : ∀ i < 8, Foot Wl (Addr.add (S - 8 - 8 - 8 - 8) i))
    (ft : FtsF F S) (hin₂ : CodeIn L e₂ code₂) (h₂ : j₂ < code₂.length)
    (k2 : KAac prof F Wl L s₀ o gev gP gE P2 S g0 (e₂.add j₂) V' a r)
    (kr : ∀ (W : Addr → Byte) (Z' : State) (t' : Nat), KeptW Wl s₀ Z' → Agree F Z'.proc.mm.mem W →
      Z'.cpu.rip = e₂.add j₂ → Z'.cpu.gpr.rsp = S + 8 → KS g0 Z'.cpu.gpr →
      Z'.cpu.gpr.rax = BitVec.setWidth 64 (BitVec.setWidth 32 r) →
      (∃ (Z₂ : State) (V₂ : Addr → Byte), P2 Z₂ V₂ ∧ (W = V₂ ∨ W = Trm V₂ g0.rdi)) →
      GoG prof L o gev gP gE Z' t') :
    ExL prof F Wl L s₀ o gev gP gE V' S g0 r a := by
  intro Y t hK hA hr hm h12 hbp
  refine (c_80 prof).run c hin (fun j' g' _ V'' => j' = 87 ∧ V'' = V' ∧ g'.rdi = Y.cpu.gpr.rbx + 104#64 ∧
      g'.rsi = Y.cpu.gpr.rbp ∧ g'.r12 = Y.cpu.gpr.r12 ∧ Fr Y.cpu.gpr g') hK hA hr
    (vc_80 fun _ a b d e _ => ⟨rfl, rfl, a, b, d, e⟩) ?_
  rintro j' g fl V₁ ⟨rfl, hV₁, gdi, gsi, g12, gf⟩ U t₁ hKU hAU hrU hgU -
  subst V₁ hgU
  have hmU := Fm.fr hm gf
  have hU : U.cpu.gpr.rsp - 8 = S - 8 - 8 - 8 - 8 := by rw [hmU.1]
  refine c.s_call_x hKU hAU hin (lt_len (by decide)) hrU (call_87 _) hinA (tgt := 0) (Aac.lt_len (by decide))
    tgt_87 (by rw [hU]; exact hs4) ?_
  rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
  rw [hU] at hA₂
  refine k2 Y₂ t₂ hK₂ hA₂ (by rw [hr₂, addr_add_zero]) (by rw [hg₂]; exact hU)
    (by rw [hg₂]; show U.cpu.gpr.rdi = _; rw [gdi, hm.2.1]) (by rw [hg₂]; show U.cpu.gpr.rsi = _; rw [gsi, hbp])
    (by rw [hg₂]; exact hmU.2.1) (by rw [hg₂]; show U.cpu.gpr.r12 = _; rw [g12, h12])
    (by rw [hg₂]; exact hmU.2.2.1) (by rw [hg₂]; exact hmU.2.2.2.1) (by rw [hg₂]; exact hmU.2.2.2.2) ?_
  intro Z₂ V₂ t₃ hKZ hAZ hrZ hmZ hz12 hT st1 st2 hP2
  refine (c_92 prof).run c hin (fun j' g' _ V'' => j' = 122 ∧ (V'' = V₂ ∨ V'' = Trm V₂ g0.rdi) ∧
      g'.r12 = Z₂.cpu.gpr.r12 ∧ Fr Z₂.cpu.gpr g') hKZ hAZ hrZ
    (vc_92 (by rw [hmZ.2.1]; exact hT) (fun _ a b _ => ⟨rfl, Or.inl rfl, a, b⟩)
      (fun _ a b _ => ⟨rfl, Or.inr (by rw [hmZ.2.1]), a, b⟩)) ?_
  rintro j' g fl V₃ ⟨rfl, hV₃, g12', gf'⟩ U₃ t₄ hK₄ hA₄ hr₄ hg₄ -
  subst hg₄
  have hst : StkF V₃ S g0 (e₂.add j₂) := by
    rcases hV₃ with rfl | rfl
    · exact st1
    · exact st2
  exact tail122 c hin hK₄ hA₄ hr₄ (Fm.fr hmZ gf') (g12'.trans hz12) hst ft hin₂ h₂
    fun Z' t₅ a b d e f g => kr V₃ Z' t₅ a b d e f g ⟨Z₂, V₂, hP2, hV₃⟩

/-- One byte of the loop: the end of the path (to 80), or the next byte (`kn`). -/
theorem lpHead {V : Addr → Byte} {S p : Addr} {g0 : Gprs} {r : BitVec 64} {n j : Nat} (c : Seg prof F Wl L s₀ o)
    (hin : CodeIn L fnd_at fnd) (hS : Pth F V p n) (hj : j + 1 ≤ n)
    (kx : ExL prof F Wl L s₀ o gev gP gE V S g0 r (p + BitVec.ofNat 64 (nl V p (n - 1))))
    (kn : j + 2 ≤ n → AtL prof F Wl L s₀ o gev gP gE V S g0 r p (j + 1)) :
    AtL prof F Wl L s₀ o gev gP gE V S g0 r p j := by
  intro Y t hK hA hr hm h12 hax hcx hbp
  have fb : ∀ i < 1, Foot F.data (Addr.add Y.cpu.gpr.rax i) := by rw [hax]; exact hS.ft (j + 1) hj
  have eb : V Y.cpu.gpr.rax = bt V p (j + 1) := by rw [hax]
  refine (c_58 prof).run c hin (fun j' g' _ V' => V' = V ∧ g'.r12 = Y.cpu.gpr.r12 ∧ Fr Y.cpu.gpr g' ∧
      ((j' = 80 ∧ bt V p (j + 1) = 0 ∧ g'.rbp = Y.cpu.gpr.rbp) ∨
        (j' = 52 ∧ ¬bt V p (j + 1) = 0 ∧ g'.rax = Y.cpu.gpr.rax ∧
          g'.rdx = BitVec.setWidth 64 (BitVec.setWidth 32 (bt V p (j + 1))) ∧
          g'.rbp = p + BitVec.ofNat 64 (nl V p (j + 1))))) hK hA hr
    (vc_58 hcx fb (fun hz _ hb h2 hf _ => ⟨rfl, h2, hf, Or.inl ⟨rfl, by rw [← eb]; exact hz, hb⟩⟩)
      (fun hc hz _ ha hd hb h2 hf _ => ⟨rfl, h2, hf, Or.inr ⟨rfl, by rw [← eb]; exact hz, ha,
        by rw [← eb]; exact hd, by rw [hb, hbp, nl_succ, if_neg hc]⟩⟩)
      (fun hc hz _ ha hd hb h2 hf _ => ⟨rfl, h2, hf, Or.inr ⟨rfl, by rw [← eb]; exact hz, ha,
        by rw [← eb]; exact hd, by rw [hb, hax, nl_succ, if_pos hc]⟩⟩)) ?_
  rintro j' g fl V₁ ⟨hV₁, g12, gf, hpost⟩ U t₁ hKU hAU hrU hgU -
  subst V₁ hgU
  have hmU := Fm.fr hm gf
  rcases hpost with ⟨rfl, hz, hb⟩ | ⟨rfl, hz, ha, hd, hb⟩
  · -- the 0 at the end: `j + 1` = `n`
    have hn : j + 1 = n := by
      rcases Nat.lt_or_ge (j + 1) n with h | h
      · exact absurd hz (hS.nz _ h)
      · omega
    refine kx U t₁ hKU hAU hrU hmU (g12.trans h12) ?_
    rw [hb, hbp, ← hn, Nat.add_sub_cancel]
  · -- the next byte, through 52
    have hlt : j + 2 ≤ n := by
      rcases Nat.lt_or_ge (j + 1) n with h | h
      · omega
      · have e : j + 1 = n := by omega
        have := hS.z
        rw [← e] at this
        exact absurd this hz
    refine (c_52 prof).run c hin (fun j' g' _ V' => j' = 58 ∧ V' = V ∧ g'.rax = U.cpu.gpr.rax + 1#64 ∧
        g'.rcx = BitVec.setWidth 64 (BitVec.setWidth 32 U.cpu.gpr.rdx) ∧ g'.rbp = U.cpu.gpr.rbp ∧
        g'.r12 = U.cpu.gpr.r12 ∧ Fr U.cpu.gpr g') hKU hAU hrU
      (vc_52 fun _ a b d e f _ => ⟨rfl, rfl, a, b, d, e, f⟩) ?_
    rintro j' g fl V₂ ⟨rfl, hV₂, ga, gc, gb, g12', gf'⟩ U₂ t₂ hK₂ hA₂ hr₂ hg₂ -
    subst V₂ hg₂
    refine kn hlt U₂ t₂ hK₂ hA₂ hr₂ (Fm.fr hmU gf') (g12'.trans (g12.trans h12)) ?_ ?_ ?_
    · rw [ga, ha, hax]
      exact inc1 p (j + 1)
    · rw [gc, hd, sw_64_32]
    · rw [gb, hb]

/-- The loop from any byte: by the number left. -/
theorem lpAll {V : Addr → Byte} {S p : Addr} {g0 : Gprs} {r : BitVec 64} {n : Nat} (c : Seg prof F Wl L s₀ o)
    (hin : CodeIn L fnd_at fnd) (hS : Pth F V p n)
    (kx : ExL prof F Wl L s₀ o gev gP gE V S g0 r (p + BitVec.ofNat 64 (nl V p (n - 1)))) :
    ∀ (m j : Nat), j + 1 + m = n → AtL prof F Wl L s₀ o gev gP gE V S g0 r p j
  | 0, _, h => lpHead c hin hS (by omega) kx fun h' => absurd h' (by omega)
  | m + 1, j, h => lpHead c hin hS (by omega) kx fun _ => lpAll c hin hS kx m (j + 1) (by omega)

/-- `CFileInfo::Find (path, followLink)` (`this` = `rdi`, `path` = `rsi`) from its entry. `Find_DontFill_Base` at its
entry with `rsp` 32 below the entry's, the three registers pushed and the return address (`k1`); from its return
(`P1`, the path still `n` bytes) `al` = 0 goes to the return address with the bytes it left; else the name (after the
last '/' a byte follows) to `AString::operator=` on `Name` (`k2`); from its return (`P2`) the cut of a '/' at the end
or not, then the return address. There (`kr`): `rsp` 8 above the entry's, the callee-saved registers as they were,
`eax` = `Find_DontFill_Base`'s `eax`. -/
theorem fnd_ok {P1 P2 : State → (Addr → Byte) → Prop} {n : Nat} (c : Seg prof F Wl L s₀ o)
    (hin : CodeIn L fnd_at fnd) (hinF : CodeIn L Fdn.fdn_at Fdn.fdn) (hinA : CodeIn L Aac.aac_at Aac.aac)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = fnd_at)
    (hs1 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8) i))
    (hs2 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8 - 8) i))
    (hs3 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8 - 8 - 8) i))
    (hs4 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8 - 8 - 8 - 8) i))
    (hl : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsp i))
    (hin₂ : CodeIn L e₂ code₂) (h₂ : j₂ < code₂.length)
    (k1 : ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y →
      Agree F Y.proc.mm.mem
        (Vst (Ffp.V1 V X.cpu.gpr) (X.cpu.gpr.rsp - 8 - 8 - 8 - 8) (toBytesLE (fnd_at.add 22) 8)) →
      Y.cpu.rip = Fdn.fdn_at → Y.cpu.gpr.rsp = X.cpu.gpr.rsp - 8 - 8 - 8 - 8 → Y.cpu.gpr.rdi = X.cpu.gpr.rdi →
      Y.cpu.gpr.rsi = X.cpu.gpr.rsi →
      Y.cpu.gpr.rdx = BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.setWidth 8 X.cpu.gpr.rdx)) →
      Y.cpu.gpr.rbx = X.cpu.gpr.rdi → Y.cpu.gpr.rbp = X.cpu.gpr.rsi → Y.cpu.gpr.r12 = X.cpu.gpr.r12 →
      Y.cpu.gpr.r13 = X.cpu.gpr.r13 → Y.cpu.gpr.r14 = X.cpu.gpr.r14 → Y.cpu.gpr.r15 = X.cpu.gpr.r15 →
      (∀ (Z : State) (V' : Addr → Byte) (t'' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V' →
        Z.cpu.rip = fnd_at.add 22 → Fm X.cpu.gpr.rsp X.cpu.gpr Z.cpu.gpr → Z.cpu.gpr.rbp = X.cpu.gpr.rsi →
        StkF V' X.cpu.gpr.rsp X.cpu.gpr (e₂.add j₂) → Pth F V' X.cpu.gpr.rsi n → P1 Z V' →
        GoG prof L o gev gP gE Z t'') →
      GoG prof L o gev gP gE Y t')
    (k2 : ∀ (Z : State) (V' : Addr → Byte), P1 Z V' → ¬BitVec.setWidth 8 Z.cpu.gpr.rax = 0 →
      KAac prof F Wl L s₀ o gev gP gE P2 X.cpu.gpr.rsp X.cpu.gpr (e₂.add j₂) V'
        (X.cpu.gpr.rsi + BitVec.ofNat 64 (nl V' X.cpu.gpr.rsi (n - 1)))
        (BitVec.setWidth 64 (BitVec.setWidth 32 Z.cpu.gpr.rax)))
    (kr : ∀ (W : Addr → Byte) (Z' : State) (t' : Nat), KeptW Wl s₀ Z' → Agree F Z'.proc.mm.mem W →
      Z'.cpu.rip = e₂.add j₂ → Z'.cpu.gpr.rsp = X.cpu.gpr.rsp + 8 → KS X.cpu.gpr Z'.cpu.gpr →
      (∃ (Z : State) (V' : Addr → Byte), P1 Z V' ∧
        Z'.cpu.gpr.rax = BitVec.setWidth 64 (BitVec.setWidth 32 Z.cpu.gpr.rax) ∧
        ((BitVec.setWidth 8 Z.cpu.gpr.rax = 0 ∧ W = V') ∨
          ∃ (Z₂ : State) (V₂ : Addr → Byte), P2 Z₂ V₂ ∧ (W = V₂ ∨ W = Trm V₂ X.cpu.gpr.rdi))) →
      GoG prof L o gev gP gE Z' t') :
    GoG prof L o gev gP gE X t := by
  have ft : FtsF F X.cpu.gpr.rsp :=
    ⟨fun i hi => c.hws _ (hs3 i hi), by rw [q1]; exact fun i hi => c.hws _ (hs2 i hi),
      by rw [q2]; exact fun i hi => c.hws _ (hs1 i hi), hl⟩
  -- the prologue, to the first `call`
  refine (c_0 prof).run c hin (fun j' g' _ V' => j' = 17 ∧ V' = Ffp.V1 V X.cpu.gpr ∧
      g'.rsp = X.cpu.gpr.rsp - 8 - 8 - 8 ∧ g'.rdi = X.cpu.gpr.rdi ∧ g'.rsi = X.cpu.gpr.rsi ∧
      g'.rdx = BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.setWidth 8 X.cpu.gpr.rdx)) ∧
      g'.rbx = X.cpu.gpr.rdi ∧ g'.rbp = X.cpu.gpr.rsi ∧ g'.r12 = X.cpu.gpr.r12 ∧ g'.r13 = X.cpu.gpr.r13 ∧
      g'.r14 = X.cpu.gpr.r14 ∧ g'.r15 = X.cpu.gpr.r15) hK hA (by rw [addr_add_zero]; exact hrip)
    (vc_0 hs1 hs2 hs3 fun _ a b d e f g h i j k _ => ⟨rfl, rfl, a, b, d, e, f, g, h, i, j, k⟩) ?_
  rintro j' g fl V₁ ⟨rfl, rfl, gs, gdi, gsi, gdx, gbx, gbp, g12, g13, g14, g15⟩ Y t₁ hKY hAY hrY hgY -
  subst hgY
  have hY : Y.cpu.gpr.rsp - 8 = X.cpu.gpr.rsp - 8 - 8 - 8 - 8 := by rw [gs]
  refine c.s_call_x hKY hAY hin (lt_len (by decide)) hrY (call_17 _) hinF (tgt := 0) (Fdn.lt_len (by decide))
    tgt_17 (by rw [hY]; exact hs4) ?_
  rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
  rw [hY] at hA₂
  refine k1 Y₂ t₂ hK₂ hA₂ (by rw [hr₂, addr_add_zero]) (by rw [hg₂]; exact hY) (by rw [hg₂]; exact gdi)
    (by rw [hg₂]; exact gsi) (by rw [hg₂]; exact gdx) (by rw [hg₂]; exact gbx) (by rw [hg₂]; exact gbp)
    (by rw [hg₂]; exact g12) (by rw [hg₂]; exact g13) (by rw [hg₂]; exact g14) (by rw [hg₂]; exact g15) ?_
  -- back from `Find_DontFill_Base`, at 22
  intro Z V' t₃ hKZ hAZ hrZ hmZ zbp hst hS hP1
  have fb : ∀ i < 1, Foot F.data (Addr.add Z.cpu.gpr.rbp i) := by
    have h0 := hS.ft 0 (Nat.zero_le _)
    rw [a0] at h0
    rw [zbp]
    exact h0
  have eb : V' Z.cpu.gpr.rbp = bt V' X.cpu.gpr.rsi 0 := by
    show V' Z.cpu.gpr.rbp = V' (X.cpu.gpr.rsi + BitVec.ofNat 64 0)
    rw [zbp, a0]
  have kE : ∀ W Z' t', KeptW Wl s₀ Z' → Agree F Z'.proc.mm.mem W → Z'.cpu.rip = e₂.add j₂ →
      Z'.cpu.gpr.rsp = X.cpu.gpr.rsp + 8 → KS X.cpu.gpr Z'.cpu.gpr →
      Z'.cpu.gpr.rax = BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.setWidth 32 Z.cpu.gpr.rax))) →
      (∃ (Z₂ : State) (V₂ : Addr → Byte), P2 Z₂ V₂ ∧ (W = V₂ ∨ W = Trm V₂ X.cpu.gpr.rdi)) →
      GoG prof L o gev gP gE Z' t' :=
    fun W Z' t' a b d e f g hw => kr W Z' t' a b d e f ⟨Z, V', hP1, by rw [g, sw_64_32], Or.inr hw⟩
  refine (c_22 prof).run c hin (fun j' g' _ V'' => V'' = V' ∧
      g'.r12 = BitVec.setWidth 64 (BitVec.setWidth 32 Z.cpu.gpr.rax) ∧ Fr Z.cpu.gpr g' ∧
      ((j' = 122 ∧ BitVec.setWidth 8 Z.cpu.gpr.rax = 0) ∨
        (j' = 80 ∧ ¬BitVec.setWidth 8 Z.cpu.gpr.rax = 0 ∧ bt V' X.cpu.gpr.rsi 0 = 0 ∧ g'.rbp = Z.cpu.gpr.rbp) ∨
        (j' = 58 ∧ ¬BitVec.setWidth 8 Z.cpu.gpr.rax = 0 ∧ ¬bt V' X.cpu.gpr.rsi 0 = 0 ∧
          g'.rax = Z.cpu.gpr.rbp + 1#64 ∧ g'.rcx = BitVec.setWidth 64 (BitVec.setWidth 32 (bt V' X.cpu.gpr.rsi 0)) ∧
          g'.rbp = Z.cpu.gpr.rbp))) hKZ hAZ hrZ
    (vc_22 fb (fun h0 _ a b _ => ⟨rfl, a, b, Or.inl ⟨rfl, h0⟩⟩)
      (fun h0 hz _ a b d _ => ⟨rfl, b, d, Or.inr (Or.inl ⟨rfl, h0, by rw [← eb]; exact hz, a⟩)⟩)
      (fun h0 hz _ a d e b f _ => ⟨rfl, b, f, Or.inr (Or.inr ⟨rfl, h0, by rw [← eb]; exact hz, a,
        by rw [← eb]; exact d, e⟩)⟩)) ?_
  rintro j' g fl V₂ ⟨hV₂, g12, gf, hpost⟩ U t₄ hKU hAU hrU hgU -
  subst V₂ hgU
  have hmU := Fm.fr hmZ gf
  rcases hpost with ⟨rfl, h0⟩ | ⟨rfl, h0, hz, hb⟩ | ⟨rfl, h0, hz, ha, hc, hb⟩
  · -- `al` = 0: `eax` back, the pops and the `ret`
    exact tail122 c hin hKU hAU hrU hmU g12 hst ft hin₂ h₂ fun Z' t₅ a b d e f g =>
      kr V' Z' t₅ a b d e f ⟨Z, V', hP1, by rw [g, sw_64_32], Or.inl ⟨h0, rfl⟩⟩
  · -- the path empty: the name at `path`
    have hn : n = 0 := by
      rcases Nat.eq_zero_or_pos n with h | h
      · exact h
      · exact absurd hz (hS.nz 0 h)
    refine from80 c hin hinA hs4 ft hin₂ h₂ (k2 Z V' hP1 h0) kE U t₄ hKU hAU hrU hmU g12 ?_
    rw [hb, zbp, hn, Nat.zero_sub, nl_zero, a0]
  · -- the loop from the second byte
    have hn : 1 ≤ n := by
      rcases Nat.eq_zero_or_pos n with h | h
      · have := hS.z
        rw [h] at this
        exact absurd this hz
      · exact h
    refine lpAll c hin hS (from80 c hin hinA hs4 ft hin₂ h₂ (k2 Z V' hP1 h0) kE) (n - 1) 0 (by omega) U t₄ hKU hAU
      hrU hmU g12 ?_ hc ?_
    · rw [ha, zbp]
      try rfl
    · rw [hb, zbp]
      exact (a0 _).symm

end FV7z.Fnd
