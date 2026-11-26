import FV7z.Ocv.Cuts
import FV7z.Tiny.Tj
import FV7z.Lemmas.LeafRet
import FV7z.Tun.Inv
/-!
# `CObjectVector<CRecordVector<unsigned>>::~CObjectVector` (PLAN.md §M, M1)

7-Zip 26.06's `CObjectVector<CRecordVector<unsigned>>::~CObjectVector (this)` at `0x454600` in `7zzs`
(`CPP/Common/MyVector.h`), `S` the stack pointer at the entry: `r12`, `rbp`, `rbx` pushed, `r12` = `this`, `eax` =
`_v._size` (the 4 bytes at `this + 8`), `rdi` = `_v._items` (`it`, the 8 bytes at `this`). When the size `n` is not 0,
`rbx` = `8 (n - 1)` and the loop from 32 runs for `k` = `n - 1` down to 0: `p` = `_items[k]` (the 8 bytes at
`it + 8k`); when `p` is not 0, `q` = `p->_items` (the 8 bytes at `p`) is freed when not 0 (`call 0x6014f0` at 50,
`operator delete (q)`), then `p` (`call 0x6014e0` at 63, `operator delete (p, 16)`), and `rdi` = `_items` again (68);
then `rbx` -= 8 (72). At 82 the registers are popped; when `it` is 0, `ret` (100), else `jmp 0x6014f0` (91,
`operator delete (it)` as a tail call).

The callees are hypotheses on the bytes they are given and leave (`I`, `J`, chosen by the caller): `I k` before the
`k`-th step's frees are done (`I n` at the start, `I 0` at the end), `J k p` between the two frees of the `k`-th step.
`Call1 S f ra A V P`: from `f` with `rsp` = `S - 32`, the return address `ra` at `S - 32`, the arguments `A` and the
bytes `V`, the run goes on to the goal if it does from every state at `ra` with bytes `V'`, `P V'`, the registers a
call keeps (`Bk`) and the saved registers and the return address as in `V` (`Kf`).

- `Fr`: the saved registers and the return address in the bytes; `Rs`: the registers the loop keeps; `pk V it k`:
  `_items[k]`; `rbx0 n`: `rbx` at 32 the first time; `pops3`: the registers after the pops.
- `vc_*`: the verification conditions of the pieces; `ocv_ok`: from the entry to the return address (`kr`) or to
  `0x6014f0` (`kt`).

The reads at the entry are stated on the bytes after the pushes (`hn`, `hf`, `hI`).
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Ocv

/-! ## The instructions outside the blocks -/

/-- The `call` to `0x6014f0` at 50. -/
def qc50 : List Byte := [0xe8, 0xb9, 0xce, 0x1a, 0x00]
theorem qc50_0 : ∀ feat, Dec feat qc50 0 (FV7z.mk .call 64 [.rel 1756857] 5) := by dec_rfl
theorem wc_50 : qc50 <+: ocv.drop 50 := by decide +kernel
theorem call_50 (feat : Features) : Dec feat ocv 50 (FV7z.mk .call 64 [.rel 1756857] 5) :=
  Dec.shift (j := 50) (k := 0) (qc50_0 feat) wc_50 (Nat.zero_le _)
theorem tgt_50 : ocv_at.add (50 + 5) + BitVec.ofNat 64 1756857 = 0x6014f0#64 := by decide

/-- The `call` to `0x6014e0` at 63. -/
def qc63 : List Byte := [0xe8, 0x9c, 0xce, 0x1a, 0x00]
theorem qc63_0 : ∀ feat, Dec feat qc63 0 (FV7z.mk .call 64 [.rel 1756828] 5) := by dec_rfl
theorem wc_63 : qc63 <+: ocv.drop 63 := by decide +kernel
theorem call_63 (feat : Features) : Dec feat ocv 63 (FV7z.mk .call 64 [.rel 1756828] 5) :=
  Dec.shift (j := 63) (k := 0) (qc63_0 feat) wc_63 (Nat.zero_le _)
theorem tgt_63 : ocv_at.add (63 + 5) + BitVec.ofNat 64 1756828 = 0x6014e0#64 := by decide

/-- The `jmp` to `0x6014f0` at 91. -/
def qjm : List Byte := [0xe9, 0x90, 0xce, 0x1a, 0x00]
theorem qjm_0 : ∀ feat, Dec feat qjm 0 (FV7z.mk .jmp 64 [.rel 1756816] 5) := by dec_rfl
theorem wx_91 : qjm <+: ocv.drop 91 := by decide +kernel
theorem jmp_91 (feat : Features) : Dec feat ocv 91 (FV7z.mk .jmp 64 [.rel 1756816] 5) :=
  Dec.shift (j := 91) (k := 0) (qjm_0 feat) wx_91 (Nat.zero_le _)

/-- The `ret`. -/
def qret : List Byte := [0xc3]
theorem qret_0 : ∀ feat, Dec feat qret 0 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem wr_100 : qret <+: ocv.drop 100 := by decide +kernel
theorem ret_100 (feat : Features) : Dec feat ocv 100 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 100) (k := 0) (qret_0 feat) wr_100 (Nat.zero_le _)

/-! ## The frame and the loop's registers -/

/-- The bytes after the pushes of `r12`, `rbp`, `rbx`. -/
abbrev Vp (V : Addr → Byte) (g : Gprs) : Addr → Byte :=
  Vst (Vst (Vst V (g.rsp - 8) (toBytesLE g.r12 8)) (g.rsp - 8 - 8) (toBytesLE g.rbp 8)) (g.rsp - 8 - 8 - 8)
    (toBytesLE g.rbx 8)

/-- The saved registers of `g₀` and the return address `ra` in the bytes `V`. -/
def Fr (g₀ : Gprs) (ra : Addr) (V : Addr → Byte) : Prop :=
  rdq(V, g₀.rsp - 8) = g₀.r12 ∧ rdq(V, g₀.rsp - 8 - 8) = g₀.rbp ∧ rdq(V, g₀.rsp - 8 - 8 - 8) = g₀.rbx ∧
    rdq(V, g₀.rsp) = ra

/-- The 32 bytes from `S - 24` as in `V`. -/
def Kf (S : Addr) (V V' : Addr → Byte) : Prop :=
  rdq(V', S - 8) = rdq(V, S - 8) ∧ rdq(V', S - 8 - 8) = rdq(V, S - 8 - 8) ∧
    rdq(V', S - 8 - 8 - 8) = rdq(V, S - 8 - 8 - 8) ∧ rdq(V', S) = rdq(V, S)

theorem Fr.kf {g₀ : Gprs} {ra : Addr} {V V' : Addr → Byte} (h : Fr g₀ ra V) (k : Kf g₀.rsp V V') : Fr g₀ ra V' :=
  ⟨k.1.trans h.1, k.2.1.trans h.2.1, k.2.2.1.trans h.2.2.1, k.2.2.2.trans h.2.2.2⟩

/-- The registers a function keeps. -/
def Kp (g₀ g : Gprs) : Prop :=
  g.rbx = g₀.rbx ∧ g.rbp = g₀.rbp ∧ g.r12 = g₀.r12 ∧ g.r13 = g₀.r13 ∧ g.r14 = g₀.r14 ∧ g.r15 = g₀.r15

/-- The registers after a `ret`, from those at the entry. -/
def Bk (g₀ g : Gprs) : Prop := g.rsp = g₀.rsp + 8 ∧ Kp g₀ g

/-- The registers the loop keeps: `rsp` below the pushes, `r12` = `this`, `r13`–`r15`. -/
def Rs (g₀ g : Gprs) : Prop :=
  g.rsp = g₀.rsp - 8 - 8 - 8 ∧ g.r12 = g₀.rdi ∧ g.r13 = g₀.r13 ∧ g.r14 = g₀.r14 ∧ g.r15 = g₀.r15

/-- `_items[k]`. -/
abbrev pk (V : Addr → Byte) (it : BitVec 64) (k : Nat) : BitVec 64 := rdq(V, it + BitVec.ofNat 64 (8 * k))

/-- `rbx` at 32 the first time: `lea ebx, [rax - 1]; shl rbx, 3`. -/
def rbx0 (n : BitVec 32) : BitVec 64 :=
  BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.setWidth 64 n + 18446744073709551615#64)) <<< 3

/-- The registers after `pop rbx; pop rbp; pop r12`. -/
abbrev pops3 (V : Addr → Byte) (g : Gprs) : Gprs :=
  { g with
      rbx := rdq(V, g.rsp),
      rbp := rdq(V, g.rsp + 8),
      rsp := g.rsp + 8 + 8 + 8,
      r12 := rdq(V, g.rsp + 8 + 8) }

theorem rbx0_eq {n : BitVec 32} (h : n ≠ 0) : rbx0 n = BitVec.ofNat 64 (8 * (n.toNat - 1)) := by
  have h1 : n.toNat ≠ 0 := fun e => h (BitVec.eq_of_toNat_eq e)
  have h2 : n.toNat < 4294967296 := n.isLt
  apply BitVec.eq_of_toNat_eq
  simp only [rbx0, BitVec.toNat_shiftLeft, BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_ofNat,
    Nat.shiftLeft_eq, Nat.reducePow, Nat.reduceMod]
  omega

theorem rb_step (k : Nat) (hk : k < 4294967296) :
    BitVec.ofNat 64 (8 * (k + 1)) - 8#64 = BitVec.ofNat 64 (8 * k) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
  omega

theorem rb_ne (k : Nat) (hk : k < 4294967296) : BitVec.ofNat 64 (8 * k) ≠ 18446744073709551608#64 := by
  intro h
  have h' := congrArg BitVec.toNat h
  simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod] at h'
  omega

theorem rb_last : BitVec.ofNat 64 (8 * 0) - 8#64 = 18446744073709551608#64 := by decide

theorem a3s (x : Addr) : x - 8 - 8 - 8 + 8 = x - 8 - 8 := BitVec.sub_add_cancel _ _
theorem a2s (x : Addr) : x - 8 - 8 + 8 = x - 8 := BitVec.sub_add_cancel _ _
theorem a1s (x : Addr) : x - 8 + 8 = x := BitVec.sub_add_cancel _ _

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

/-- From the entry: the pushes, `r12` = `this`, the size `n32` and `it` read; to 82 when the size is 0, else to 32
with `rbx` = `rbx0 n32`. -/
theorem vc_0 {n32 : BitVec 32} {it : BitVec 64}
    (hn : rdd(Vp V g, g.rdi + 8#64) = n32) (hit : rdq(Vp V g, g.rdi) = it)
    (fn : ∀ i < 4, Foot F.data (Addr.add (g.rdi + 8#64) i)) (fa : ∀ i < 8, Foot F.data (Addr.add g.rdi i))
    (w1 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8) i)) (w2 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8) i))
    (w3 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8 - 8) i)) :
    W_0 F Wl (fun j' g' _ V' => V' = Vp V g ∧ Rs g g' ∧ g'.rdi = it ∧
      (n32 = 0 ∧ j' = 82 ∨ n32 ≠ 0 ∧ j' = 32 ∧ g'.rbx = rbx0 n32)) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [Vp] at hn hit fn fa w1 w2 w3 ⊢
  wpx [W_0, W_21, o0, o1, Op.shl64, Rs, hn, hit, BitVec.and_self, beq_iff_eq, beq_eq_false_iff_ne]
  ocl

/-- 32 with `_items[k]` 0: to 72. -/
theorem vc_32z {p : BitVec 64} (hp : rdq(V, g.rdi + g.rbx) = p)
    (fp : ∀ i < 8, Foot F.data (Addr.add (g.rdi + g.rbx) i)) (hp0 : p = 0) :
    W_32 F Wl (fun j' g' _ V' => j' = 72 ∧ g' = { g with rbp := p } ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hp fp ⊢
  have e : (p == 0) = true := beq_iff_eq.2 hp0
  wpx [W_32, W_41, o2, o3, hp, e, BitVec.and_self, Bool.false_eq_true, Bool.true_eq_false, false_implies,
    eq_self_iff_true, true_implies, implies_true]
  ocl

/-- 32 with `_items[k]` = `p` not 0: `rdi` = `q` = `p->_items`; to 55 when it is 0, else to the `call` at 50. -/
theorem vc_32n {p q : BitVec 64} (hp : rdq(V, g.rdi + g.rbx) = p)
    (fp : ∀ i < 8, Foot F.data (Addr.add (g.rdi + g.rbx) i)) (hp0 : p ≠ 0) (hq : rdq(V, p) = q)
    (fq : ∀ i < 8, Foot F.data (Addr.add p i)) :
    W_32 F Wl (fun j' g' _ V' => (q = 0 ∧ j' = 55 ∨ q ≠ 0 ∧ j' = 50) ∧ g' = { g with rbp := p, rdi := q } ∧
      V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hp fp ⊢
  have e : (p == 0) = false := beq_eq_false_iff_ne.2 hp0
  wpx [W_32, W_41, o2, o3, hp, hq, e, BitVec.and_self, beq_iff_eq, beq_eq_false_iff_ne, Bool.false_eq_true,
    Bool.true_eq_false, false_implies, eq_self_iff_true, true_implies, implies_true]
  ocl

/-- 55: `rdi` = `rbp`, `esi` = 16; to the `call` at 63. -/
theorem vc_55 :
    W_55 F Wl (fun j' g' _ V' => j' = 63 ∧ g' = { g with rdi := g.rbp, rsi := 16#64 } ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_55, o4, BitVec.reduceSetWidth]
  ocl

/-- 68: `rdi` = `_items` again; to 72. -/
theorem vc_68 {it : BitVec 64} (hit : rdq(V, g.r12) = it) (fa : ∀ i < 8, Foot F.data (Addr.add g.r12 i)) :
    W_68 F Wl (fun j' g' _ V' => j' = 72 ∧ g' = { g with rdi := it } ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hit fa ⊢
  wpx [W_68, o5, hit]
  ocl

/-- 72, the last step: `rbx` -= 8 gives `-8`; to 82. -/
theorem vc_72l (h : g.rbx - 8#64 = 18446744073709551608#64) :
    W_72 F Wl (fun j' g' _ V' => j' = 82 ∧ g' = { g with rbx := g.rbx - 8#64 } ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h ⊢
  have e := decide_eq_true h
  wpx [W_72, o6, e, Bool.not_true, Bool.not_false, Bool.false_eq_true, Bool.true_eq_false, false_implies,
    eq_self_iff_true, true_implies, implies_true]
  ocl

/-- 72, not the last step: back to 32. -/
theorem vc_72c (h : g.rbx - 8#64 ≠ 18446744073709551608#64) :
    W_72 F Wl (fun j' g' _ V' => j' = 32 ∧ g' = { g with rbx := g.rbx - 8#64 } ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h ⊢
  have e := decide_eq_false h
  wpx [W_72, o6, e, Bool.not_true, Bool.not_false, Bool.false_eq_true, Bool.true_eq_false, false_implies,
    eq_self_iff_true, true_implies, implies_true]
  ocl

/-- 82 with `rdi` 0: the pops, to the `ret` at 100. -/
theorem vc_82z {Q : Post} (hz : g.rdi = 0) (l3 : ∀ i < 8, Foot F.data (Addr.add g.rsp i))
    (l2 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8) i)) (l1 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8 + 8) i))
    (h : ∀ fl, Q 100 (pops3 V g) fl V) : W_82 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [pops3] at hz l3 l2 l1 h ⊢
  have e : (rdi == 0) = true := beq_iff_eq.2 hz
  wpx [W_82, W_96, W_87, o7, o8, e, BitVec.and_self, Bool.false_eq_true, Bool.true_eq_false, false_implies,
    eq_self_iff_true, true_implies]
  all_goals repeat' (first | exact h _ | assumption | exact trivial | apply And.intro | intro _)

/-- 82 with `rdi` not 0: the pops, to the `jmp` at 91. -/
theorem vc_82n {Q : Post} (hz : g.rdi ≠ 0) (l3 : ∀ i < 8, Foot F.data (Addr.add g.rsp i))
    (l2 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8) i)) (l1 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8 + 8) i))
    (h : ∀ fl, Q 91 (pops3 V g) fl V) : W_82 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [pops3] at hz l3 l2 l1 h ⊢
  have e : (rdi == 0) = false := beq_eq_false_iff_ne.2 hz
  wpx [W_82, W_96, W_87, o7, o8, e, BitVec.and_self, Bool.false_eq_true, Bool.true_eq_false, false_implies,
    eq_self_iff_true, true_implies]
  all_goals repeat' (first | exact h _ | assumption | exact trivial | apply And.intro | intro _)

end

/-! ## The function -/

/-- What the code asks of a function it calls at `f` with the return address `ra` (pushed at `S - 32`), the
arguments `A` and the bytes `V`: the run goes on to the goal if it does from every state at `ra` with bytes `V'`
for which `P` holds, the registers a call keeps and the 32 bytes from `S - 24` as in `V`. -/
def Call1 (prof : Profile) (F : Footprint) (Wl : List Rgn) (L : List (Addr × List Byte)) (s₀ : State) (o : Oracle)
    (gev : List Event) (gP : State → Nat → List Event → Prop) (gE : Outcome → List Event → Prop)
    (S f ra : Addr) (A : Gprs → Prop) (V : Addr → Byte) (P : (Addr → Byte) → Prop) : Prop :=
  ∀ (Y : State) (t : Nat), KeptW Wl s₀ Y → Agree F Y.proc.mm.mem (Vst V (S - 8 - 8 - 8 - 8) (toBytesLE ra 8)) →
    Y.cpu.rip = f → Y.cpu.gpr.rsp = S - 8 - 8 - 8 - 8 → A Y.cpu.gpr →
    (∀ (Z : State) (V' : Addr → Byte) (t' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V' → P V' →
      Z.cpu.rip = ra → Bk Y.cpu.gpr Z.cpu.gpr → Kf S V V' → GoG prof L o gev gP gE Z t') →
    GoG prof L o gev gP gE Y t

/-- From offset `j` with registers and bytes for which `P` holds, the run goes on to the goal. -/
def AtJ (prof : Profile) (F : Footprint) (Wl : List Rgn) (L : List (Addr × List Byte)) (s₀ : State) (o : Oracle)
    (gev : List Event) (gP : State → Nat → List Event → Prop) (gE : Outcome → List Event → Prop) (j : Nat)
    (P : Gprs → (Addr → Byte) → Prop) : Prop :=
  ∀ (Y : State) (V : Addr → Byte) (t : Nat), KeptW Wl s₀ Y → Agree F Y.proc.mm.mem V →
    Y.cpu.rip = ocv_at.add j → P Y.cpu.gpr V → GoG prof L o gev gP gE Y t

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {X : State} {t : Nat} {V : Addr → Byte}

/-- `~CObjectVector (this)` (`rdi`) from its entry, the size `n32` (the 4 bytes at `this + 8`, as read) and the
items `it` (the 8 bytes at `this` whenever `I` holds). The step `k` (from `n - 1` down to 0) starts with `I (k + 1)`
and ends with `I k`: when `_items[k]` (`pk`) is 0 at once (`hP0`); else through `J k p` after `operator delete (q)`
(`hD1`, at `0x6014f0`) or at once when `q` is 0 (`hQ0`), and `operator delete (p, 16)` (`hD2`, at `0x6014e0`). With
`I 0` the run reaches the return address with the registers a call keeps when `it` is 0 (`kr`), else `0x6014f0` with
`rsp` as at the entry, `rdi` = `it`, the saved registers back and the return address in place (`kt`). -/
theorem ocv_ok {n32 : BitVec 32} {it : BitVec 64} {I : Nat → (Addr → Byte) → Prop}
    {J : Nat → BitVec 64 → (Addr → Byte) → Prop} {e₂ : Addr} {code₂ : List Byte} {j₂ : Nat}
    (c : Seg prof F Wl L s₀ o) (hin : CodeIn L ocv_at ocv)
    (hin1 : CodeIn L 0x6014f0#64 Tiny.c6014f0) (hin2 : CodeIn L 0x6014e0#64 Tiny.c6014e0)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = ocv_at)
    (w1 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8) i))
    (w2 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8 - 8) i))
    (w3 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8 - 8 - 8) i))
    (w4 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8 - 8 - 8 - 8) i))
    (hl : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsp i))
    (fn : ∀ i < 4, Foot F.data (Addr.add (X.cpu.gpr.rdi + 8#64) i))
    (fa : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rdi i))
    (fe : ∀ k < n32.toNat, ∀ i < 8, Foot F.data (Addr.add (it + BitVec.ofNat 64 (8 * k)) i))
    (fp : ∀ k < n32.toNat, ∀ W, I (k + 1) W → pk W it k ≠ 0 → ∀ i < 8, Foot F.data (Addr.add (pk W it k) i))
    (hn : rdd(Vp V X.cpu.gpr, X.cpu.gpr.rdi + 8#64) = n32)
    (hI : I n32.toNat (Vp V X.cpu.gpr)) (hf : Fr X.cpu.gpr (e₂.add j₂) (Vp V X.cpu.gpr))
    (hIt : ∀ k W, I k W → rdq(W, X.cpu.gpr.rdi) = it)
    (hP0 : ∀ k < n32.toNat, ∀ W, I (k + 1) W → pk W it k = 0 → I k W)
    (hQ0 : ∀ k < n32.toNat, ∀ W, I (k + 1) W → pk W it k ≠ 0 → rdq(W, pk W it k) = 0 → J k (pk W it k) W)
    (hD1 : ∀ k < n32.toNat, ∀ W, I (k + 1) W → pk W it k ≠ 0 → rdq(W, pk W it k) ≠ 0 →
      Call1 prof F Wl L s₀ o gev gP gE X.cpu.gpr.rsp 0x6014f0#64 (ocv_at.add 55)
        (fun g => g.rdi = rdq(W, pk W it k)) W (J k (pk W it k)))
    (hD2 : ∀ k < n32.toNat, ∀ p W, p ≠ 0 → J k p W →
      Call1 prof F Wl L s₀ o gev gP gE X.cpu.gpr.rsp 0x6014e0#64 (ocv_at.add 68)
        (fun g => g.rdi = p ∧ g.rsi = 16#64) W (I k))
    (hin₂ : CodeIn L e₂ code₂) (h₂ : j₂ < code₂.length)
    (kt : ∀ (Y : State) (W : Addr → Byte) (t' : Nat), KeptW Wl s₀ Y → Agree F Y.proc.mm.mem W → I 0 W →
      Fr X.cpu.gpr (e₂.add j₂) W → Y.cpu.rip = 0x6014f0#64 → Y.cpu.gpr.rsp = X.cpu.gpr.rsp →
      Y.cpu.gpr.rdi = it → it ≠ 0 → Kp X.cpu.gpr Y.cpu.gpr → GoG prof L o gev gP gE Y t')
    (kr : ∀ (Z : State) (W : Addr → Byte) (t' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem W → I 0 W →
      Z.cpu.rip = e₂.add j₂ → Bk X.cpu.gpr Z.cpu.gpr → it = 0 → GoG prof L o gev gP gE Z t') :
    GoG prof L o gev gP gE X t := by
  have hn32 : n32.toNat < 4294967296 := n32.isLt
  -- the end, from 82
  have F82 : AtJ prof F Wl L s₀ o gev gP gE 82 fun g W => I 0 W ∧ Fr X.cpu.gpr (e₂.add j₂) W ∧
      Rs X.cpu.gpr g ∧ g.rdi = it := by
    rintro Y W t' hKY hAY hrY ⟨hI0, hfr, ⟨hs, h12, h13, h14, h15⟩, hdi⟩
    have l3 : ∀ i < 8, Foot F.data (Addr.add Y.cpu.gpr.rsp i) := by
      rw [hs]; exact fun i hi => c.hws _ (w3 i hi)
    have l2 : ∀ i < 8, Foot F.data (Addr.add (Y.cpu.gpr.rsp + 8) i) := by
      rw [hs, a3s]; exact fun i hi => c.hws _ (w2 i hi)
    have l1 : ∀ i < 8, Foot F.data (Addr.add (Y.cpu.gpr.rsp + 8 + 8) i) := by
      rw [hs, a3s, a2s]; exact fun i hi => c.hws _ (w1 i hi)
    have hsP : (pops3 W Y.cpu.gpr).rsp = X.cpu.gpr.rsp := by
      show Y.cpu.gpr.rsp + 8 + 8 + 8 = _
      rw [hs, a3s, a2s, a1s]
    have hkP : Kp X.cpu.gpr (pops3 W Y.cpu.gpr) := by
      refine ⟨?_, ?_, ?_, h13, h14, h15⟩
      · show rdq(W, Y.cpu.gpr.rsp) = _
        rw [hs]; exact hfr.2.2.1
      · show rdq(W, Y.cpu.gpr.rsp + 8) = _
        rw [hs, a3s]; exact hfr.2.1
      · show rdq(W, Y.cpu.gpr.rsp + 8 + 8) = _
        rw [hs, a3s, a2s]; exact hfr.1
    by_cases hz0 : it = 0
    · refine (c_82 prof).run c hin (fun j' g' _ V₁ => j' = 100 ∧ g' = pops3 W Y.cpu.gpr ∧ V₁ = W) hKY hAY hrY
        (vc_82z (hdi.trans hz0) l3 l2 l1 fun _ => ⟨rfl, rfl, rfl⟩) ?_
      rintro j' g fl V₁ ⟨rfl, rfl, hV₁⟩ U t₁ hKU hAU hrU hgU -
      subst V₁
      have hsU : U.cpu.gpr.rsp = X.cpu.gpr.rsp := (congrArg Gprs.rsp hgU).trans hsP
      refine c.s_ret hKU hAU hin (lt_len (by decide)) hrU (ret_100 _) (by rw [hsU]; exact hl) hin₂ h₂
        (by rw [hsU]; exact hfr.2.2.2) ?_
      rintro Z t₂ hKZ hAZ ⟨hrZ, hgZ⟩
      refine kr Z W t₂ hKZ hAZ hI0 hrZ ⟨?_, ?_⟩ hz0
      · rw [hgZ]
        show U.cpu.gpr.rsp + 8 = _
        rw [hsU]
      · rw [hgZ, hgU]
        exact hkP
    · refine (c_82 prof).run c hin (fun j' g' _ V₁ => j' = 91 ∧ g' = pops3 W Y.cpu.gpr ∧ V₁ = W) hKY hAY hrY
        (vc_82n (fun h => hz0 (hdi.symm.trans h)) l3 l2 l1 fun _ => ⟨rfl, rfl, rfl⟩) ?_
      rintro j' g fl V₁ ⟨rfl, rfl, hV₁⟩ U t₁ hKU hAU hrU hgU -
      subst V₁
      refine c.s_jmp_x hKU hAU hin (lt_len (by decide)) hrU (jmp_91 _) (tgt := 0) hin1 (by decide) (by decide) ?_
      rintro Z t₂ hKZ hAZ ⟨hrZ, hgZ⟩
      refine kt Z W t₂ hKZ hAZ hI0 hfr (by rw [hrZ, addr_add_zero]) ?_ ?_ hz0 ?_
      · rw [hgZ, hgU]
        exact hsP
      · rw [hgZ, hgU]
        exact hdi
      · rw [hgZ, hgU]
        exact hkP
  -- 72: `rbx` -= 8, to 82 after the step 0, else to 32
  have S72 : ∀ k, k < n32.toNat →
      (∀ k', k = k' + 1 → AtJ prof F Wl L s₀ o gev gP gE 32 fun g W => I (k' + 1) W ∧
        Fr X.cpu.gpr (e₂.add j₂) W ∧ Rs X.cpu.gpr g ∧ g.rdi = it ∧ g.rbx = BitVec.ofNat 64 (8 * k')) →
      AtJ prof F Wl L s₀ o gev gP gE 72 fun g W => I k W ∧ Fr X.cpu.gpr (e₂.add j₂) W ∧ Rs X.cpu.gpr g ∧
        g.rdi = it ∧ g.rbx = BitVec.ofNat 64 (8 * k) := by
    rintro k hk hnx Y W t' hKY hAY hrY ⟨hIk, hfr, hR, hdi, hb⟩
    cases k with
    | zero =>
      refine (c_72 prof).run c hin _ hKY hAY hrY (vc_72l (by rw [hb]; exact rb_last)) ?_
      rintro j' g fl V₁ ⟨rfl, rfl, hV₁⟩ U t₁ hKU hAU hrU hgU -
      subst V₁
      exact F82 U W t₁ hKU hAU hrU ⟨hIk, hfr, by rw [hgU]; exact hR, (congrArg Gprs.rdi hgU).trans hdi⟩
    | succ k =>
      refine (c_72 prof).run c hin _ hKY hAY hrY
        (vc_72c (by rw [hb, rb_step k (by omega)]; exact rb_ne k (by omega))) ?_
      rintro j' g fl V₁ ⟨rfl, rfl, hV₁⟩ U t₁ hKU hAU hrU hgU -
      subst V₁
      have hbU : U.cpu.gpr.rbx = BitVec.ofNat 64 (8 * k) := by
        rw [hgU]
        show Y.cpu.gpr.rbx - 8#64 = _
        rw [hb]
        exact rb_step k (by omega)
      exact hnx k rfl U W t₁ hKU hAU hrU ⟨hIk, hfr, by rw [hgU]; exact hR, (congrArg Gprs.rdi hgU).trans hdi, hbU⟩
  -- 55: `operator delete (p, 16)`, `rdi` = `_items` again, to 72
  have A55 : ∀ k, k < n32.toNat → ∀ p : BitVec 64, p ≠ 0 →
      AtJ prof F Wl L s₀ o gev gP gE 72 (fun g W => I k W ∧ Fr X.cpu.gpr (e₂.add j₂) W ∧ Rs X.cpu.gpr g ∧
        g.rdi = it ∧ g.rbx = BitVec.ofNat 64 (8 * k)) →
      AtJ prof F Wl L s₀ o gev gP gE 55 fun g W => J k p W ∧ Fr X.cpu.gpr (e₂.add j₂) W ∧ Rs X.cpu.gpr g ∧
        g.rbp = p ∧ g.rbx = BitVec.ofNat 64 (8 * k) := by
    rintro k hk p hp h72 Y W t' hKY hAY hrY ⟨hJ, hfr, hR, hbp, hb⟩
    refine (c_55 prof).run c hin _ hKY hAY hrY vc_55 ?_
    rintro j' g fl V₁ ⟨rfl, rfl, hV₁⟩ U t₁ hKU hAU hrU hgU -
    subst V₁
    have hRU : Rs X.cpu.gpr U.cpu.gpr := by rw [hgU]; exact hR
    have hbU : U.cpu.gpr.rbx = BitVec.ofNat 64 (8 * k) := (congrArg Gprs.rbx hgU).trans hb
    have hsU : U.cpu.gpr.rsp = X.cpu.gpr.rsp - 8 - 8 - 8 := hRU.1
    refine c.s_call hKU hAU hin (lt_len (by decide)) hrU (call_63 _) hin2 (by decide) tgt_63
      (by rw [hsU]; exact w4) ?_
    rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
    rw [hsU] at hA₂
    have hsY₂ : Y₂.cpu.gpr.rsp = X.cpu.gpr.rsp - 8 - 8 - 8 - 8 :=
      (congrArg Gprs.rsp hg₂).trans (congrArg (fun x : Addr => x - 8) hsU)
    have hdi₂ : Y₂.cpu.gpr.rdi = p ∧ Y₂.cpu.gpr.rsi = 16#64 :=
      ⟨(congrArg Gprs.rdi hg₂).trans ((congrArg Gprs.rdi hgU).trans hbp),
        (congrArg Gprs.rsi hg₂).trans (congrArg Gprs.rsi hgU)⟩
    refine hD2 k hk p W hp hJ Y₂ t₂ hK₂ hA₂ hr₂ hsY₂ hdi₂ ?_
    rintro Z V'' t'' hKZ hAZ hIk hrZ ⟨b1, b2, b3, b4, b5, b6, b7⟩ hkf
    have hsZ : Z.cpu.gpr.rsp = X.cpu.gpr.rsp - 8 - 8 - 8 := by rw [b1, hsY₂, a1s]
    have h12Z : Z.cpu.gpr.r12 = X.cpu.gpr.rdi := b4.trans ((congrArg Gprs.r12 hg₂).trans hRU.2.1)
    refine (c_68 prof).run c hin _ hKZ hAZ hrZ
      (vc_68 (it := it) (by rw [h12Z]; exact hIt k V'' hIk) (by rw [h12Z]; exact fa)) ?_
    rintro j' g fl V₁ ⟨rfl, rfl, hV₁⟩ U₂ t₃ hKU₂ hAU₂ hrU₂ hgU₂ -
    subst V₁
    refine h72 U₂ V'' t₃ hKU₂ hAU₂ hrU₂ ⟨hIk, hfr.kf hkf, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
    · exact (congrArg Gprs.rsp hgU₂).trans hsZ
    · exact (congrArg Gprs.r12 hgU₂).trans h12Z
    · exact (congrArg Gprs.r13 hgU₂).trans (b5.trans ((congrArg Gprs.r13 hg₂).trans hRU.2.2.1))
    · exact (congrArg Gprs.r14 hgU₂).trans (b6.trans ((congrArg Gprs.r14 hg₂).trans hRU.2.2.2.1))
    · exact (congrArg Gprs.r15 hgU₂).trans (b7.trans ((congrArg Gprs.r15 hg₂).trans hRU.2.2.2.2))
    · exact congrArg Gprs.rdi hgU₂
    · exact (congrArg Gprs.rbx hgU₂).trans (b2.trans ((congrArg Gprs.rbx hg₂).trans hbU))
  -- 32: the step `k`, to 72
  have B32 : ∀ k, k < n32.toNat →
      AtJ prof F Wl L s₀ o gev gP gE 72 (fun g W => I k W ∧ Fr X.cpu.gpr (e₂.add j₂) W ∧ Rs X.cpu.gpr g ∧
        g.rdi = it ∧ g.rbx = BitVec.ofNat 64 (8 * k)) →
      AtJ prof F Wl L s₀ o gev gP gE 32 fun g W => I (k + 1) W ∧ Fr X.cpu.gpr (e₂.add j₂) W ∧ Rs X.cpu.gpr g ∧
        g.rdi = it ∧ g.rbx = BitVec.ofNat 64 (8 * k) := by
    rintro k hk h72 Y W t' hKY hAY hrY ⟨hIk, hfr, hR, hdi, hb⟩
    have hea : Y.cpu.gpr.rdi + Y.cpu.gpr.rbx = it + BitVec.ofNat 64 (8 * k) := by rw [hdi, hb]
    by_cases hp0 : pk W it k = 0
    · refine (c_32 prof).run c hin _ hKY hAY hrY
        (vc_32z (p := pk W it k) (by rw [hea]) (by rw [hea]; exact fe k hk) hp0) ?_
      rintro j' g fl V₁ ⟨rfl, rfl, hV₁⟩ U t₁ hKU hAU hrU hgU -
      subst V₁
      exact h72 U W t₁ hKU hAU hrU ⟨hP0 k hk W hIk hp0, hfr, by rw [hgU]; exact hR,
        (congrArg Gprs.rdi hgU).trans hdi, (congrArg Gprs.rbx hgU).trans hb⟩
    · refine (c_32 prof).run c hin _ hKY hAY hrY
        (vc_32n (p := pk W it k) (q := rdq(W, pk W it k)) (by rw [hea]) (by rw [hea]; exact fe k hk) hp0 rfl
          (fp k hk W hIk hp0)) ?_
      rintro j' g fl V₁ ⟨hj, rfl, hV₁⟩ U t₁ hKU hAU hrU hgU -
      subst V₁
      have hRU : Rs X.cpu.gpr U.cpu.gpr := by rw [hgU]; exact hR
      have hbU : U.cpu.gpr.rbx = BitVec.ofNat 64 (8 * k) := (congrArg Gprs.rbx hgU).trans hb
      have hpU : U.cpu.gpr.rbp = pk W it k := congrArg Gprs.rbp hgU
      rcases hj with ⟨hq0, rfl⟩ | ⟨hq0, rfl⟩
      · exact A55 k hk _ hp0 h72 U W t₁ hKU hAU hrU ⟨hQ0 k hk W hIk hp0 hq0, hfr, hRU, hpU, hbU⟩
      · -- `operator delete (q)`
        have hsU : U.cpu.gpr.rsp = X.cpu.gpr.rsp - 8 - 8 - 8 := hRU.1
        refine c.s_call hKU hAU hin (lt_len (by decide)) hrU (call_50 _) hin1 (by decide) tgt_50
          (by rw [hsU]; exact w4) ?_
        rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
        rw [hsU] at hA₂
        have hsY₂ : Y₂.cpu.gpr.rsp = X.cpu.gpr.rsp - 8 - 8 - 8 - 8 :=
          (congrArg Gprs.rsp hg₂).trans (congrArg (fun x : Addr => x - 8) hsU)
        have hdi₂ : Y₂.cpu.gpr.rdi = rdq(W, pk W it k) := (congrArg Gprs.rdi hg₂).trans (congrArg Gprs.rdi hgU)
        refine hD1 k hk W hIk hp0 hq0 Y₂ t₂ hK₂ hA₂ hr₂ hsY₂ hdi₂ ?_
        rintro Z V'' t'' hKZ hAZ hJ hrZ ⟨b1, b2, b3, b4, b5, b6, b7⟩ hkf
        refine A55 k hk _ hp0 h72 Z V'' t'' hKZ hAZ hrZ ⟨hJ, hfr.kf hkf, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
        · rw [b1, hsY₂, a1s]
        · exact b4.trans ((congrArg Gprs.r12 hg₂).trans hRU.2.1)
        · exact b5.trans ((congrArg Gprs.r13 hg₂).trans hRU.2.2.1)
        · exact b6.trans ((congrArg Gprs.r14 hg₂).trans hRU.2.2.2.1)
        · exact b7.trans ((congrArg Gprs.r15 hg₂).trans hRU.2.2.2.2)
        · exact b3.trans ((congrArg Gprs.rbp hg₂).trans hpU)
        · exact b2.trans ((congrArg Gprs.rbx hg₂).trans hbU)
  -- the loop, by induction on the step
  have L32 : ∀ k, k < n32.toNat → AtJ prof F Wl L s₀ o gev gP gE 32 fun g W => I (k + 1) W ∧
      Fr X.cpu.gpr (e₂.add j₂) W ∧ Rs X.cpu.gpr g ∧ g.rdi = it ∧ g.rbx = BitVec.ofNat 64 (8 * k) := by
    intro k
    induction k with
    | zero => exact fun hk => B32 0 hk (S72 0 hk fun k' e => absurd e (by omega))
    | succ k ih =>
      exact fun hk => B32 (k + 1) hk (S72 (k + 1) hk fun k' e => by
        obtain rfl : k = k' := by omega
        exact ih (by omega))
  -- the entry
  have hrip' : X.cpu.rip = ocv_at.add 0 := by rw [addr_add_zero]; exact hrip
  refine (c_0 prof).run c hin _ hK hA hrip' (vc_0 hn (hIt _ _ hI) fn fa w1 w2 w3) ?_
  rintro j' g fl V₁ ⟨hV₁, hR, hdi, hj⟩ Y t₁ hKY hAY hrY hgY -
  subst V₁
  subst hgY
  rcases hj with ⟨hn0, rfl⟩ | ⟨hn0, rfl, hb⟩
  · have e0 : n32.toNat = 0 := congrArg BitVec.toNat hn0
    exact F82 Y _ t₁ hKY hAY hrY ⟨e0 ▸ hI, hf, hR, hdi⟩
  · have hnz : n32.toNat ≠ 0 := fun e => hn0 (BitVec.eq_of_toNat_eq e)
    have e1 : n32.toNat - 1 + 1 = n32.toNat := by omega
    exact L32 (n32.toNat - 1) (by omega) Y _ t₁ hKY hAY hrY
      ⟨by rw [e1]; exact hI, hf, hR, hdi, by rw [hb, rbx0_eq hn0]⟩

end FV7z.Ocv
