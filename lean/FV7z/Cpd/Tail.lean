import FV7z.Cpd.Defs
/-!
# `NCommandLineParser::CParser::~CParser`, from 170 (PLAN.md §M, M1)

7-Zip 26.06's `CParser::~CParser (this)` at `0x5a0500` in `7zzs` (`CPP/Common/CommandLineParser.cpp`; `objdump -d`),
`S` the stack pointer at the entry: `r14`, `r13`, `r12`, `rbp`, `rbx` pushed, `r12` = `this`. From 170 (after
`delete [] _switches`, `FV7z/Cpd/Holds.lean`): the 8 bytes at `this + 48` freed when not 0 (`call 0x6014f0` at 180),
then those at `this + 32` (195); at 200 `NonSwitchStrings` (a `CObjectVector<UString>` at `this + 8`: `_items` the 8
bytes at `this + 8`, the size `n` the 4 bytes at `this + 16`) as `FV7z/Ocv/Holds.lean`: for `k` = `n - 1` down to 0
(the loop from 224, `rbx` = `8k`) `p` = `_items[k]`; when `p` is not 0 its chars (the 8 bytes at `p`) freed when not
0 (242), then `p` (`operator delete (p, 16)`, 255) and `rdi` = `_items` again (260). At 275 the registers are
popped; when `_items` is 0, `ret` (320), else `jmp 0x6014f0` (288, `operator delete [] (_items)` as a tail call).

The callees are hypotheses on the bytes they are given and leave (as in `FV7z/Ocv/Holds.lean`): `B0` at 170, `B1`
after the first free, `I k` before the `k`-th step's frees are done (`I n` at 200, `I 0` at the end), `J k p` between
the two frees of the `k`-th step. `Call1 S f ra A V P`: from `f` with `rsp` = `S - 48`, the return address `ra` at
`S - 48`, the arguments `A` and the bytes `V`, the run goes on to the goal if it does from every state at `ra` with
bytes `V'`, `P V'`, the registers a call keeps (`Bk`) and the saved registers and the return address as in `V` (`Kf`).

- `Fr`: the saved registers and the return address in the bytes; `Rs`: the registers kept from 170 on (`rsp` below
  the pushes, `r12` = `this`, `r15`); `pk V it k`: `_items[k]`; `pops5`: the registers after the pops.
- `vc_*`: the verification conditions of the pieces; `from170`: from 170 to the return address (`kr`) or to
  `0x6014f0` (`kt`).
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
open FV7z.Ocv (rbx0 rbx0_eq rb_step rb_ne rb_last)
namespace FV7z.Cpd

/-! ## The instructions outside the blocks -/

/-- The `call` of `operator delete []` at 180. -/
def qc180 : List Byte := [0xe8, 0x37, 0x0f, 0x06, 0x00]
theorem qc180_0 : ∀ feat, Dec feat qc180 0 (FV7z.mk .call 64 [.rel 397111] 5) := by dec_rfl
theorem wc_180 : qc180 <+: cpd.drop 180 := by decide +kernel
theorem call_180 (feat : Features) : Dec feat cpd 180 (FV7z.mk .call 64 [.rel 397111] 5) :=
  Dec.shift (j := 180) (k := 0) (qc180_0 feat) wc_180 (Nat.zero_le _)
theorem tgt_180 : cpd_at.add (180 + 5) + BitVec.ofNat 64 397111 = 0x6014f0#64 := by decide

/-- The `call` of `operator delete []` at 195. -/
def qc195 : List Byte := [0xe8, 0x28, 0x0f, 0x06, 0x00]
theorem qc195_0 : ∀ feat, Dec feat qc195 0 (FV7z.mk .call 64 [.rel 397096] 5) := by dec_rfl
theorem wc_195 : qc195 <+: cpd.drop 195 := by decide +kernel
theorem call_195 (feat : Features) : Dec feat cpd 195 (FV7z.mk .call 64 [.rel 397096] 5) :=
  Dec.shift (j := 195) (k := 0) (qc195_0 feat) wc_195 (Nat.zero_le _)
theorem tgt_195 : cpd_at.add (195 + 5) + BitVec.ofNat 64 397096 = 0x6014f0#64 := by decide

/-- The `call` of `operator delete [] (q)` at 242. -/
def qc242 : List Byte := [0xe8, 0xf9, 0x0e, 0x06, 0x00]
theorem qc242_0 : ∀ feat, Dec feat qc242 0 (FV7z.mk .call 64 [.rel 397049] 5) := by dec_rfl
theorem wc_242 : qc242 <+: cpd.drop 242 := by decide +kernel
theorem call_242 (feat : Features) : Dec feat cpd 242 (FV7z.mk .call 64 [.rel 397049] 5) :=
  Dec.shift (j := 242) (k := 0) (qc242_0 feat) wc_242 (Nat.zero_le _)
theorem tgt_242 : cpd_at.add (242 + 5) + BitVec.ofNat 64 397049 = 0x6014f0#64 := by decide

/-- The `call` of `operator delete (p, 16)` at 255. -/
def qc255 : List Byte := [0xe8, 0xdc, 0x0e, 0x06, 0x00]
theorem qc255_0 : ∀ feat, Dec feat qc255 0 (FV7z.mk .call 64 [.rel 397020] 5) := by dec_rfl
theorem wc_255 : qc255 <+: cpd.drop 255 := by decide +kernel
theorem call_255 (feat : Features) : Dec feat cpd 255 (FV7z.mk .call 64 [.rel 397020] 5) :=
  Dec.shift (j := 255) (k := 0) (qc255_0 feat) wc_255 (Nat.zero_le _)
theorem tgt_255 : cpd_at.add (255 + 5) + BitVec.ofNat 64 397020 = 0x6014e0#64 := by decide

/-- The `jmp` to `0x6014f0` at 288. -/
def qjm : List Byte := [0xe9, 0xcb, 0x0e, 0x06, 0x00]
theorem qjm_0 : ∀ feat, Dec feat qjm 0 (FV7z.mk .jmp 64 [.rel 397003] 5) := by dec_rfl
theorem wx_288 : qjm <+: cpd.drop 288 := by decide +kernel
theorem jmp_288 (feat : Features) : Dec feat cpd 288 (FV7z.mk .jmp 64 [.rel 397003] 5) :=
  Dec.shift (j := 288) (k := 0) (qjm_0 feat) wx_288 (Nat.zero_le _)

/-- The `ret`. -/
def qret : List Byte := [0xc3]
theorem qret_0 : ∀ feat, Dec feat qret 0 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem wr_320 : qret <+: cpd.drop 320 := by decide +kernel
theorem ret_320 (feat : Features) : Dec feat cpd 320 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 320) (k := 0) (qret_0 feat) wr_320 (Nat.zero_le _)


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

/-- 170: `rdi` = the 8 bytes at `this + 48`; to 185 when 0, else to the `call` at 180. -/
theorem vc_170 {q : BitVec 64} (hq : rdq(V, g.r12 + 48#64) = q)
    (fq : ∀ i < 8, Foot F.data (Addr.add (g.r12 + 48#64) i)) :
    W_170 F Wl (fun j' g' _ V' => (q = 0 ∧ j' = 185 ∨ q ≠ 0 ∧ j' = 180) ∧ g' = { g with rdi := q } ∧ V' = V)
      g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hq fq ⊢
  wpx [W_170, o13, hq, BitVec.and_self, beq_iff_eq, beq_eq_false_iff_ne, Bool.false_eq_true,
    Bool.true_eq_false, false_implies, eq_self_iff_true, true_implies, implies_true]
  ocl

/-- 185: `rdi` = the 8 bytes at `this + 32`; to 200 when 0, else to the `call` at 195. -/
theorem vc_185 {q : BitVec 64} (hq : rdq(V, g.r12 + 32#64) = q)
    (fq : ∀ i < 8, Foot F.data (Addr.add (g.r12 + 32#64) i)) :
    W_185 F Wl (fun j' g' _ V' => (q = 0 ∧ j' = 200 ∨ q ≠ 0 ∧ j' = 195) ∧ g' = { g with rdi := q } ∧ V' = V)
      g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hq fq ⊢
  wpx [W_185, o14, hq, BitVec.and_self, beq_iff_eq, beq_eq_false_iff_ne, Bool.false_eq_true,
    Bool.true_eq_false, false_implies, eq_self_iff_true, true_implies, implies_true]
  ocl

/-- 200 with the size 0: `eax` = the size, `rdi` = `_items`; to 275. -/
theorem vc_200z {n32 : BitVec 32} {it : BitVec 64}
    (hn : rdd(V, g.r12 + 16#64) = n32) (hit : rdq(V, g.r12 + 8#64) = it) (hn0 : n32 = 0)
    (fn : ∀ i < 4, Foot F.data (Addr.add (g.r12 + 16#64) i)) (fa : ∀ i < 8, Foot F.data (Addr.add (g.r12 + 8#64) i)) :
    W_200 F Wl (fun j' g' _ V' => j' = 275 ∧ g'.rsp = g.rsp ∧ g'.r12 = g.r12 ∧ g'.r15 = g.r15 ∧ g'.rdi = it ∧
      V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hn hit fn fa ⊢
  have e : (n32 == 0) = true := beq_iff_eq.2 hn0
  wpx [W_200, W_214, o15, o16, Op.shl64, hn, hit, e, BitVec.and_self, Bool.false_eq_true, Bool.true_eq_false,
    false_implies, eq_self_iff_true, true_implies, implies_true]
  ocl

/-- 200 with the size `n32` not 0: to 224 with `rbx` = `rbx0 n32`. -/
theorem vc_200n {n32 : BitVec 32} {it : BitVec 64}
    (hn : rdd(V, g.r12 + 16#64) = n32) (hit : rdq(V, g.r12 + 8#64) = it) (hn0 : n32 ≠ 0)
    (fn : ∀ i < 4, Foot F.data (Addr.add (g.r12 + 16#64) i)) (fa : ∀ i < 8, Foot F.data (Addr.add (g.r12 + 8#64) i)) :
    W_200 F Wl (fun j' g' _ V' => j' = 224 ∧ g'.rsp = g.rsp ∧ g'.r12 = g.r12 ∧ g'.r15 = g.r15 ∧ g'.rdi = it ∧
      g'.rbx = rbx0 n32 ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hn hit fn fa ⊢
  have e : (n32 == 0) = false := beq_eq_false_iff_ne.2 hn0
  wpx [W_200, W_214, o15, o16, Op.shl64, hn, hit, e, BitVec.and_self, Bool.false_eq_true, Bool.true_eq_false,
    false_implies, eq_self_iff_true, true_implies, implies_true]
  ocl

/-- 224 with `_items[k]` 0: to 265. -/
theorem vc_224z {p : BitVec 64} (hp : rdq(V, g.rdi + g.rbx) = p)
    (fp : ∀ i < 8, Foot F.data (Addr.add (g.rdi + g.rbx) i)) (hp0 : p = 0) :
    W_224 F Wl (fun j' g' _ V' => j' = 265 ∧ g' = { g with rbp := p } ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hp fp ⊢
  have e : (p == 0) = true := beq_iff_eq.2 hp0
  wpx [W_224, W_233, o17, o18, hp, e, BitVec.and_self, Bool.false_eq_true, Bool.true_eq_false, false_implies,
    eq_self_iff_true, true_implies, implies_true]
  ocl

/-- 224 with `_items[k]` = `p` not 0: `rdi` = `q` = `p->_chars`; to 247 when it is 0, else to the `call` at 242. -/
theorem vc_224n {p q : BitVec 64} (hp : rdq(V, g.rdi + g.rbx) = p)
    (fp : ∀ i < 8, Foot F.data (Addr.add (g.rdi + g.rbx) i)) (hp0 : p ≠ 0) (hq : rdq(V, p) = q)
    (fq : ∀ i < 8, Foot F.data (Addr.add p i)) :
    W_224 F Wl (fun j' g' _ V' => (q = 0 ∧ j' = 247 ∨ q ≠ 0 ∧ j' = 242) ∧ g' = { g with rbp := p, rdi := q } ∧
      V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hp fp ⊢
  have e : (p == 0) = false := beq_eq_false_iff_ne.2 hp0
  wpx [W_224, W_233, o17, o18, hp, hq, e, BitVec.and_self, beq_iff_eq, beq_eq_false_iff_ne, Bool.false_eq_true,
    Bool.true_eq_false, false_implies, eq_self_iff_true, true_implies, implies_true]
  ocl

/-- 247: `rdi` = `rbp`, `esi` = 16; to the `call` at 255. -/
theorem vc_247 :
    W_247 F Wl (fun j' g' _ V' => j' = 255 ∧ g' = { g with rdi := g.rbp, rsi := 16#64 } ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_247, o19, BitVec.reduceSetWidth]
  ocl

/-- 260: `rdi` = `_items` again; to 265. -/
theorem vc_260 {it : BitVec 64} (hit : rdq(V, g.r12 + 8#64) = it)
    (fa : ∀ i < 8, Foot F.data (Addr.add (g.r12 + 8#64) i)) :
    W_260 F Wl (fun j' g' _ V' => j' = 265 ∧ g' = { g with rdi := it } ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hit fa ⊢
  wpx [W_260, o20, hit]
  ocl

/-- 265, the last step: `rbx` -= 8 gives `-8`; to 275. -/
theorem vc_265l (h : g.rbx - 8#64 = 18446744073709551608#64) :
    W_265 F Wl (fun j' g' _ V' => j' = 275 ∧ g' = { g with rbx := g.rbx - 8#64 } ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h ⊢
  have e := decide_eq_true h
  wpx [W_265, o21, e, Bool.not_true, Bool.not_false, Bool.false_eq_true, Bool.true_eq_false, false_implies,
    eq_self_iff_true, true_implies, implies_true]
  ocl

/-- 265, not the last step: back to 224. -/
theorem vc_265c (h : g.rbx - 8#64 ≠ 18446744073709551608#64) :
    W_265 F Wl (fun j' g' _ V' => j' = 224 ∧ g' = { g with rbx := g.rbx - 8#64 } ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h ⊢
  have e := decide_eq_false h
  wpx [W_265, o21, e, Bool.not_true, Bool.not_false, Bool.false_eq_true, Bool.true_eq_false, false_implies,
    eq_self_iff_true, true_implies, implies_true]
  ocl

/-- 275 with `rdi` 0: the pops, to the `ret` at 320. -/
theorem vc_275z {Q : Post} (hz : g.rdi = 0) (l5 : ∀ i < 8, Foot F.data (Addr.add g.rsp i))
    (l4 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8) i)) (l3 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8 + 8) i))
    (l2 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8 + 8 + 8) i))
    (l1 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8 + 8 + 8 + 8) i))
    (h : ∀ fl, Q 320 (pops5 V g) fl V) : W_275 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [pops5] at hz l5 l4 l3 l2 l1 h ⊢
  have e : (rdi == 0) = true := beq_iff_eq.2 hz
  wpx [W_275, W_312, W_280, o9, o22, e, BitVec.and_self, Bool.false_eq_true, Bool.true_eq_false, false_implies,
    eq_self_iff_true, true_implies]
  all_goals repeat' (first | exact h _ | assumption | exact trivial | apply And.intro | intro _)

/-- 275 with `rdi` not 0: the pops, to the `jmp` at 288. -/
theorem vc_275n {Q : Post} (hz : g.rdi ≠ 0) (l5 : ∀ i < 8, Foot F.data (Addr.add g.rsp i))
    (l4 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8) i)) (l3 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8 + 8) i))
    (l2 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8 + 8 + 8) i))
    (l1 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8 + 8 + 8 + 8) i))
    (h : ∀ fl, Q 288 (pops5 V g) fl V) : W_275 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [pops5] at hz l5 l4 l3 l2 l1 h ⊢
  have e : (rdi == 0) = false := beq_eq_false_iff_ne.2 hz
  wpx [W_275, W_312, W_280, o9, o22, e, BitVec.and_self, Bool.false_eq_true, Bool.true_eq_false, false_implies,
    eq_self_iff_true, true_implies]
  all_goals repeat' (first | exact h _ | assumption | exact trivial | apply And.intro | intro _)

end

/-! ## From 170 -/


variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}

/-- From 170 (`g₀` the registers at the entry, `this` = `g₀.rdi`): `B0` at 170; the 8 bytes at `this + 48` freed
when not 0 (`hC1`, else `hZ1`), giving `B1`; those at `this + 32` (`hC2`, else `hZ2`), giving `I n` with `n` = `n32`
the 4 bytes at `this + 16` (`hn`) and `it` the 8 bytes at `this + 8` whenever `I` holds (`hIt`); the steps as in
`FV7z/Ocv/Holds.lean` (`hP0`, `hQ0`, `hD1`, `hD2`); with `I 0` the run reaches the return address with the registers
a call keeps when `it` is 0 (`kr`), else `0x6014f0` with `rsp` as at the entry, `rdi` = `it`, the saved registers
back and the return address in place (`kt`). -/
theorem from170 {g₀ : Gprs} {n32 : BitVec 32} {it : BitVec 64} {B0 B1 : (Addr → Byte) → Prop}
    {I : Nat → (Addr → Byte) → Prop} {J : Nat → BitVec 64 → (Addr → Byte) → Prop} {e₂ : Addr} {code₂ : List Byte}
    {j₂ : Nat} (c : Seg prof F Wl L s₀ o) (hin : CodeIn L cpd_at cpd)
    (hin1 : CodeIn L 0x6014f0#64 Tiny.c6014f0) (hin2 : CodeIn L 0x6014e0#64 Tiny.c6014e0)
    (w1 : ∀ i < 8, Foot Wl (Addr.add (g₀.rsp - 8) i))
    (w2 : ∀ i < 8, Foot Wl (Addr.add (g₀.rsp - 8 - 8) i))
    (w3 : ∀ i < 8, Foot Wl (Addr.add (g₀.rsp - 8 - 8 - 8) i))
    (w4 : ∀ i < 8, Foot Wl (Addr.add (g₀.rsp - 8 - 8 - 8 - 8) i))
    (w5 : ∀ i < 8, Foot Wl (Addr.add (g₀.rsp - 8 - 8 - 8 - 8 - 8) i))
    (w6 : ∀ i < 8, Foot Wl (Addr.add (g₀.rsp - 8 - 8 - 8 - 8 - 8 - 8) i))
    (hl : ∀ i < 8, Foot F.data (Addr.add g₀.rsp i))
    (f48 : ∀ i < 8, Foot F.data (Addr.add (g₀.rdi + 48#64) i))
    (f32 : ∀ i < 8, Foot F.data (Addr.add (g₀.rdi + 32#64) i))
    (fn : ∀ i < 4, Foot F.data (Addr.add (g₀.rdi + 16#64) i))
    (fa : ∀ i < 8, Foot F.data (Addr.add (g₀.rdi + 8#64) i))
    (fe : ∀ k < n32.toNat, ∀ i < 8, Foot F.data (Addr.add (it + BitVec.ofNat 64 (8 * k)) i))
    (fp : ∀ k < n32.toNat, ∀ W, I (k + 1) W → pk W it k ≠ 0 → ∀ i < 8, Foot F.data (Addr.add (pk W it k) i))
    (hZ1 : ∀ W, B0 W → rdq(W, g₀.rdi + 48#64) = 0 → B1 W)
    (hC1 : ∀ W, B0 W → rdq(W, g₀.rdi + 48#64) ≠ 0 →
      Call1 prof F Wl L s₀ o gev gP gE g₀.rsp 0x6014f0#64 (cpd_at.add 185)
        (fun g => g.rdi = rdq(W, g₀.rdi + 48#64)) W B1)
    (hZ2 : ∀ W, B1 W → rdq(W, g₀.rdi + 32#64) = 0 → I n32.toNat W)
    (hC2 : ∀ W, B1 W → rdq(W, g₀.rdi + 32#64) ≠ 0 →
      Call1 prof F Wl L s₀ o gev gP gE g₀.rsp 0x6014f0#64 (cpd_at.add 200)
        (fun g => g.rdi = rdq(W, g₀.rdi + 32#64)) W (I n32.toNat))
    (hn : ∀ W, I n32.toNat W → rdd(W, g₀.rdi + 16#64) = n32)
    (hIt : ∀ k W, I k W → rdq(W, g₀.rdi + 8#64) = it)
    (hP0 : ∀ k < n32.toNat, ∀ W, I (k + 1) W → pk W it k = 0 → I k W)
    (hQ0 : ∀ k < n32.toNat, ∀ W, I (k + 1) W → pk W it k ≠ 0 → rdq(W, pk W it k) = 0 → J k (pk W it k) W)
    (hD1 : ∀ k < n32.toNat, ∀ W, I (k + 1) W → pk W it k ≠ 0 → rdq(W, pk W it k) ≠ 0 →
      Call1 prof F Wl L s₀ o gev gP gE g₀.rsp 0x6014f0#64 (cpd_at.add 247)
        (fun g => g.rdi = rdq(W, pk W it k)) W (J k (pk W it k)))
    (hD2 : ∀ k < n32.toNat, ∀ p W, p ≠ 0 → J k p W →
      Call1 prof F Wl L s₀ o gev gP gE g₀.rsp 0x6014e0#64 (cpd_at.add 260)
        (fun g => g.rdi = p ∧ g.rsi = 16#64) W (I k))
    (hin₂ : CodeIn L e₂ code₂) (h₂ : j₂ < code₂.length)
    (kt : ∀ (Y : State) (W : Addr → Byte) (t' : Nat), KeptW Wl s₀ Y → Agree F Y.proc.mm.mem W → I 0 W →
      Fr g₀ (e₂.add j₂) W → Y.cpu.rip = 0x6014f0#64 → Y.cpu.gpr.rsp = g₀.rsp →
      Y.cpu.gpr.rdi = it → it ≠ 0 → Kp g₀ Y.cpu.gpr → GoG prof L o gev gP gE Y t')
    (kr : ∀ (Z : State) (W : Addr → Byte) (t' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem W → I 0 W →
      Z.cpu.rip = e₂.add j₂ → Bk g₀ Z.cpu.gpr → it = 0 → GoG prof L o gev gP gE Z t') :
    AtJ prof F Wl L s₀ o gev gP gE 170 fun g W => B0 W ∧ Fr g₀ (e₂.add j₂) W ∧ Rs g₀ g := by
  have hn32 : n32.toNat < 4294967296 := n32.isLt
  -- the end, from 275
  have F275 : AtJ prof F Wl L s₀ o gev gP gE 275 fun g W => I 0 W ∧ Fr g₀ (e₂.add j₂) W ∧
      Rs g₀ g ∧ g.rdi = it := by
    rintro Y W t' hKY hAY hrY ⟨hI0, hfr, ⟨hs, h12, h15⟩, hdi⟩
    have l5 : ∀ i < 8, Foot F.data (Addr.add Y.cpu.gpr.rsp i) := by
      rw [hs]; exact fun i hi => c.hws _ (w5 i hi)
    have l4 : ∀ i < 8, Foot F.data (Addr.add (Y.cpu.gpr.rsp + 8) i) := by
      rw [hs, a5s]; exact fun i hi => c.hws _ (w4 i hi)
    have l3 : ∀ i < 8, Foot F.data (Addr.add (Y.cpu.gpr.rsp + 8 + 8) i) := by
      rw [hs, a5s, a4s]; exact fun i hi => c.hws _ (w3 i hi)
    have l2 : ∀ i < 8, Foot F.data (Addr.add (Y.cpu.gpr.rsp + 8 + 8 + 8) i) := by
      rw [hs, a5s, a4s, a3s]; exact fun i hi => c.hws _ (w2 i hi)
    have l1 : ∀ i < 8, Foot F.data (Addr.add (Y.cpu.gpr.rsp + 8 + 8 + 8 + 8) i) := by
      rw [hs, a5s, a4s, a3s, a2s]; exact fun i hi => c.hws _ (w1 i hi)
    have hsP : (pops5 W Y.cpu.gpr).rsp = g₀.rsp := by
      show Y.cpu.gpr.rsp + 8 + 8 + 8 + 8 + 8 = _
      rw [hs, a5s, a4s, a3s, a2s, a1s]
    have hkP : Kp g₀ (pops5 W Y.cpu.gpr) := by
      refine ⟨?_, ?_, ?_, ?_, ?_, h15⟩
      · show rdq(W, Y.cpu.gpr.rsp) = _
        rw [hs]; exact hfr.2.2.2.2.1
      · show rdq(W, Y.cpu.gpr.rsp + 8) = _
        rw [hs, a5s]; exact hfr.2.2.2.1
      · show rdq(W, Y.cpu.gpr.rsp + 8 + 8) = _
        rw [hs, a5s, a4s]; exact hfr.2.2.1
      · show rdq(W, Y.cpu.gpr.rsp + 8 + 8 + 8) = _
        rw [hs, a5s, a4s, a3s]; exact hfr.2.1
      · show rdq(W, Y.cpu.gpr.rsp + 8 + 8 + 8 + 8) = _
        rw [hs, a5s, a4s, a3s, a2s]; exact hfr.1
    by_cases hz0 : it = 0
    · refine (c_275 prof).run c hin (fun j' g' _ V₁ => j' = 320 ∧ g' = pops5 W Y.cpu.gpr ∧ V₁ = W) hKY hAY hrY
        (vc_275z (g := Y.cpu.gpr) (V := W) (hdi.trans hz0) l5 l4 l3 l2 l1 fun _ => ⟨rfl, rfl, rfl⟩) ?_
      rintro j' g fl V₁ ⟨rfl, rfl, hV₁⟩ U t₁ hKU hAU hrU hgU -
      subst V₁
      have hsU : U.cpu.gpr.rsp = g₀.rsp := (congrArg Gprs.rsp hgU).trans hsP
      refine c.s_ret hKU hAU hin (lt_len (by decide)) hrU (ret_320 _) (by rw [hsU]; exact hl) hin₂ h₂
        (by rw [hsU]; exact hfr.2.2.2.2.2) ?_
      rintro Z t₂ hKZ hAZ ⟨hrZ, hgZ⟩
      refine kr Z W t₂ hKZ hAZ hI0 hrZ ⟨?_, ?_⟩ hz0
      · rw [hgZ]
        show U.cpu.gpr.rsp + 8 = _
        rw [hsU]
      · rw [hgZ, hgU]
        exact hkP
    · refine (c_275 prof).run c hin (fun j' g' _ V₁ => j' = 288 ∧ g' = pops5 W Y.cpu.gpr ∧ V₁ = W) hKY hAY hrY
        (vc_275n (g := Y.cpu.gpr) (V := W) (fun h => hz0 (hdi.symm.trans h)) l5 l4 l3 l2 l1 fun _ => ⟨rfl, rfl, rfl⟩) ?_
      rintro j' g fl V₁ ⟨rfl, rfl, hV₁⟩ U t₁ hKU hAU hrU hgU -
      subst V₁
      refine c.s_jmp_x hKU hAU hin (lt_len (by decide)) hrU (jmp_288 _) (tgt := 0) hin1 (by decide) (by decide) ?_
      rintro Z t₂ hKZ hAZ ⟨hrZ, hgZ⟩
      refine kt Z W t₂ hKZ hAZ hI0 hfr (by rw [hrZ, addr_add_zero]) ?_ ?_ hz0 ?_
      · rw [hgZ, hgU]
        exact hsP
      · rw [hgZ, hgU]
        exact hdi
      · rw [hgZ, hgU]
        exact hkP
  -- 265: `rbx` -= 8, to 275 after the step 0, else to 224
  have S265 : ∀ k, k < n32.toNat →
      (∀ k', k = k' + 1 → AtJ prof F Wl L s₀ o gev gP gE 224 fun g W => I (k' + 1) W ∧
        Fr g₀ (e₂.add j₂) W ∧ Rs g₀ g ∧ g.rdi = it ∧ g.rbx = BitVec.ofNat 64 (8 * k')) →
      AtJ prof F Wl L s₀ o gev gP gE 265 fun g W => I k W ∧ Fr g₀ (e₂.add j₂) W ∧ Rs g₀ g ∧
        g.rdi = it ∧ g.rbx = BitVec.ofNat 64 (8 * k) := by
    rintro k hk hnx Y W t' hKY hAY hrY ⟨hIk, hfr, hR, hdi, hb⟩
    cases k with
    | zero =>
      refine (c_265 prof).run c hin _ hKY hAY hrY (vc_265l (by rw [hb]; exact rb_last)) ?_
      rintro j' g fl V₁ ⟨rfl, rfl, hV₁⟩ U t₁ hKU hAU hrU hgU -
      subst V₁
      exact F275 U W t₁ hKU hAU hrU ⟨hIk, hfr, by rw [hgU]; exact hR, (congrArg Gprs.rdi hgU).trans hdi⟩
    | succ k =>
      refine (c_265 prof).run c hin _ hKY hAY hrY
        (vc_265c (by rw [hb, rb_step k (by omega)]; exact rb_ne k (by omega))) ?_
      rintro j' g fl V₁ ⟨rfl, rfl, hV₁⟩ U t₁ hKU hAU hrU hgU -
      subst V₁
      have hbU : U.cpu.gpr.rbx = BitVec.ofNat 64 (8 * k) := by
        rw [hgU]
        show Y.cpu.gpr.rbx - 8#64 = _
        rw [hb]
        exact rb_step k (by omega)
      exact hnx k rfl U W t₁ hKU hAU hrU ⟨hIk, hfr, by rw [hgU]; exact hR, (congrArg Gprs.rdi hgU).trans hdi, hbU⟩
  -- 247: `operator delete (p, 16)`, `rdi` = `_items` again, to 265
  have A247 : ∀ k, k < n32.toNat → ∀ p : BitVec 64, p ≠ 0 →
      AtJ prof F Wl L s₀ o gev gP gE 265 (fun g W => I k W ∧ Fr g₀ (e₂.add j₂) W ∧ Rs g₀ g ∧
        g.rdi = it ∧ g.rbx = BitVec.ofNat 64 (8 * k)) →
      AtJ prof F Wl L s₀ o gev gP gE 247 fun g W => J k p W ∧ Fr g₀ (e₂.add j₂) W ∧ Rs g₀ g ∧
        g.rbp = p ∧ g.rbx = BitVec.ofNat 64 (8 * k) := by
    rintro k hk p hp h265 Y W t' hKY hAY hrY ⟨hJ, hfr, hR, hbp, hb⟩
    refine (c_247 prof).run c hin _ hKY hAY hrY vc_247 ?_
    rintro j' g fl V₁ ⟨rfl, rfl, hV₁⟩ U t₁ hKU hAU hrU hgU -
    subst V₁
    have hRU : Rs g₀ U.cpu.gpr := by rw [hgU]; exact hR
    have hbU : U.cpu.gpr.rbx = BitVec.ofNat 64 (8 * k) := (congrArg Gprs.rbx hgU).trans hb
    have hsU : U.cpu.gpr.rsp = g₀.rsp - 8 - 8 - 8 - 8 - 8 := hRU.1
    refine c.s_call hKU hAU hin (lt_len (by decide)) hrU (call_255 _) hin2 (by decide) tgt_255
      (by rw [hsU]; exact w6) ?_
    rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
    rw [hsU] at hA₂
    have hsY₂ : Y₂.cpu.gpr.rsp = g₀.rsp - 8 - 8 - 8 - 8 - 8 - 8 :=
      (congrArg Gprs.rsp hg₂).trans (congrArg (fun x : Addr => x - 8) hsU)
    have hdi₂ : Y₂.cpu.gpr.rdi = p ∧ Y₂.cpu.gpr.rsi = 16#64 :=
      ⟨(congrArg Gprs.rdi hg₂).trans ((congrArg Gprs.rdi hgU).trans hbp),
        (congrArg Gprs.rsi hg₂).trans (congrArg Gprs.rsi hgU)⟩
    refine hD2 k hk p W hp hJ Y₂ t₂ hK₂ hA₂ hr₂ hsY₂ hdi₂ ?_
    rintro Z V'' t'' hKZ hAZ hIk hrZ ⟨b1, b2, b3, b4, b5, b6, b7⟩ hkf
    have hsZ : Z.cpu.gpr.rsp = g₀.rsp - 8 - 8 - 8 - 8 - 8 := by rw [b1, hsY₂, a1s]
    have h12Z : Z.cpu.gpr.r12 = g₀.rdi := b4.trans ((congrArg Gprs.r12 hg₂).trans hRU.2.1)
    refine (c_260 prof).run c hin _ hKZ hAZ hrZ
      (vc_260 (it := it) (by rw [h12Z]; exact hIt k V'' hIk) (by rw [h12Z]; exact fa)) ?_
    rintro j' g fl V₁ ⟨rfl, rfl, hV₁⟩ U₂ t₃ hKU₂ hAU₂ hrU₂ hgU₂ -
    subst V₁
    refine h265 U₂ V'' t₃ hKU₂ hAU₂ hrU₂ ⟨hIk, hfr.kf hkf, ⟨?_, ?_, ?_⟩, ?_, ?_⟩
    · exact (congrArg Gprs.rsp hgU₂).trans hsZ
    · exact (congrArg Gprs.r12 hgU₂).trans h12Z
    · exact (congrArg Gprs.r15 hgU₂).trans (b7.trans ((congrArg Gprs.r15 hg₂).trans hRU.2.2))
    · exact congrArg Gprs.rdi hgU₂
    · exact (congrArg Gprs.rbx hgU₂).trans (b2.trans ((congrArg Gprs.rbx hg₂).trans hbU))
  -- 224: the step `k`, to 265
  have B224 : ∀ k, k < n32.toNat →
      AtJ prof F Wl L s₀ o gev gP gE 265 (fun g W => I k W ∧ Fr g₀ (e₂.add j₂) W ∧ Rs g₀ g ∧
        g.rdi = it ∧ g.rbx = BitVec.ofNat 64 (8 * k)) →
      AtJ prof F Wl L s₀ o gev gP gE 224 fun g W => I (k + 1) W ∧ Fr g₀ (e₂.add j₂) W ∧ Rs g₀ g ∧
        g.rdi = it ∧ g.rbx = BitVec.ofNat 64 (8 * k) := by
    rintro k hk h265 Y W t' hKY hAY hrY ⟨hIk, hfr, hR, hdi, hb⟩
    have hea : Y.cpu.gpr.rdi + Y.cpu.gpr.rbx = it + BitVec.ofNat 64 (8 * k) := by rw [hdi, hb]
    by_cases hp0 : pk W it k = 0
    · refine (c_224 prof).run c hin _ hKY hAY hrY
        (vc_224z (p := pk W it k) (by rw [hea]) (by rw [hea]; exact fe k hk) hp0) ?_
      rintro j' g fl V₁ ⟨rfl, rfl, hV₁⟩ U t₁ hKU hAU hrU hgU -
      subst V₁
      exact h265 U W t₁ hKU hAU hrU ⟨hP0 k hk W hIk hp0, hfr, by rw [hgU]; exact hR,
        (congrArg Gprs.rdi hgU).trans hdi, (congrArg Gprs.rbx hgU).trans hb⟩
    · refine (c_224 prof).run c hin _ hKY hAY hrY
        (vc_224n (p := pk W it k) (q := rdq(W, pk W it k)) (by rw [hea]) (by rw [hea]; exact fe k hk) hp0 rfl
          (fp k hk W hIk hp0)) ?_
      rintro j' g fl V₁ ⟨hj, rfl, hV₁⟩ U t₁ hKU hAU hrU hgU -
      subst V₁
      have hRU : Rs g₀ U.cpu.gpr := by rw [hgU]; exact hR
      have hbU : U.cpu.gpr.rbx = BitVec.ofNat 64 (8 * k) := (congrArg Gprs.rbx hgU).trans hb
      have hpU : U.cpu.gpr.rbp = pk W it k := congrArg Gprs.rbp hgU
      rcases hj with ⟨hq0, rfl⟩ | ⟨hq0, rfl⟩
      · exact A247 k hk _ hp0 h265 U W t₁ hKU hAU hrU ⟨hQ0 k hk W hIk hp0 hq0, hfr, hRU, hpU, hbU⟩
      · -- `operator delete (q)`
        have hsU : U.cpu.gpr.rsp = g₀.rsp - 8 - 8 - 8 - 8 - 8 := hRU.1
        refine c.s_call hKU hAU hin (lt_len (by decide)) hrU (call_242 _) hin1 (by decide) tgt_242
          (by rw [hsU]; exact w6) ?_
        rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
        rw [hsU] at hA₂
        have hsY₂ : Y₂.cpu.gpr.rsp = g₀.rsp - 8 - 8 - 8 - 8 - 8 - 8 :=
          (congrArg Gprs.rsp hg₂).trans (congrArg (fun x : Addr => x - 8) hsU)
        have hdi₂ : Y₂.cpu.gpr.rdi = rdq(W, pk W it k) := (congrArg Gprs.rdi hg₂).trans (congrArg Gprs.rdi hgU)
        refine hD1 k hk W hIk hp0 hq0 Y₂ t₂ hK₂ hA₂ hr₂ hsY₂ hdi₂ ?_
        rintro Z V'' t'' hKZ hAZ hJ hrZ ⟨b1, b2, b3, b4, b5, b6, b7⟩ hkf
        refine A247 k hk _ hp0 h265 Z V'' t'' hKZ hAZ hrZ ⟨hJ, hfr.kf hkf, ⟨?_, ?_, ?_⟩, ?_, ?_⟩
        · rw [b1, hsY₂, a1s]
        · exact b4.trans ((congrArg Gprs.r12 hg₂).trans hRU.2.1)
        · exact b7.trans ((congrArg Gprs.r15 hg₂).trans hRU.2.2)
        · exact b3.trans ((congrArg Gprs.rbp hg₂).trans hpU)
        · exact b2.trans ((congrArg Gprs.rbx hg₂).trans hbU)
  -- the loop, by induction on the step
  have L224 : ∀ k, k < n32.toNat → AtJ prof F Wl L s₀ o gev gP gE 224 fun g W => I (k + 1) W ∧
      Fr g₀ (e₂.add j₂) W ∧ Rs g₀ g ∧ g.rdi = it ∧ g.rbx = BitVec.ofNat 64 (8 * k) := by
    intro k
    induction k with
    | zero => exact fun hk => B224 0 hk (S265 0 hk fun k' e => absurd e (by omega))
    | succ k ih =>
      exact fun hk => B224 (k + 1) hk (S265 (k + 1) hk fun k' e => by
        obtain rfl : k = k' := by omega
        exact ih (by omega))
  -- 200: the size and `_items`
  have E200 : AtJ prof F Wl L s₀ o gev gP gE 200 fun g W => I n32.toNat W ∧ Fr g₀ (e₂.add j₂) W ∧ Rs g₀ g := by
    rintro Y W t' hKY hAY hrY ⟨hI, hfr, hR⟩
    have h12 : Y.cpu.gpr.r12 = g₀.rdi := hR.2.1
    have hnY : rdd(W, Y.cpu.gpr.r12 + 16#64) = n32 := by rw [h12]; exact hn W hI
    have hitY : rdq(W, Y.cpu.gpr.r12 + 8#64) = it := by rw [h12]; exact hIt _ W hI
    have fnY : ∀ i < 4, Foot F.data (Addr.add (Y.cpu.gpr.r12 + 16#64) i) := by rw [h12]; exact fn
    have faY : ∀ i < 8, Foot F.data (Addr.add (Y.cpu.gpr.r12 + 8#64) i) := by rw [h12]; exact fa
    by_cases hn0 : n32 = 0
    · refine (c_200 prof).run c hin _ hKY hAY hrY (vc_200z hnY hitY hn0 fnY faY) ?_
      rintro j' g fl V₁ ⟨rfl, hs, h12', h15, hdi, hV₁⟩ U t₁ hKU hAU hrU hgU -
      subst V₁
      subst hgU
      have e0 : n32.toNat = 0 := (congrArg BitVec.toNat hn0).trans rfl
      exact F275 U W t₁ hKU hAU hrU ⟨e0 ▸ hI, hfr, ⟨hs.trans hR.1, h12'.trans h12, h15.trans hR.2.2⟩, hdi⟩
    · refine (c_200 prof).run c hin _ hKY hAY hrY (vc_200n hnY hitY hn0 fnY faY) ?_
      rintro j' g fl V₁ ⟨rfl, hs, h12', h15, hdi, hb, hV₁⟩ U t₁ hKU hAU hrU hgU -
      subst V₁
      subst hgU
      have hnz : n32.toNat ≠ 0 := fun e => hn0 (BitVec.eq_of_toNat_eq (e.trans rfl))
      have e1 : n32.toNat - 1 + 1 = n32.toNat := by omega
      exact L224 (n32.toNat - 1) (by omega) U W t₁ hKU hAU hrU
        ⟨by rw [e1]; exact hI, hfr, ⟨hs.trans hR.1, h12'.trans h12, h15.trans hR.2.2⟩, hdi, by rw [hb, rbx0_eq hn0]⟩
  -- 185: the 8 bytes at `this + 32`
  have E185 : AtJ prof F Wl L s₀ o gev gP gE 185 fun g W => B1 W ∧ Fr g₀ (e₂.add j₂) W ∧ Rs g₀ g := by
    rintro Y W t' hKY hAY hrY ⟨hB, hfr, hR⟩
    have h12 : Y.cpu.gpr.r12 = g₀.rdi := hR.2.1
    refine (c_185 prof).run c hin _ hKY hAY hrY
      (vc_185 (q := rdq(W, g₀.rdi + 32#64)) (by rw [h12]) (by rw [h12]; exact f32)) ?_
    rintro j' g fl V₁ ⟨hj, rfl, hV₁⟩ U t₁ hKU hAU hrU hgU -
    subst V₁
    have hRU : Rs g₀ U.cpu.gpr := by rw [hgU]; exact hR
    rcases hj with ⟨hq0, rfl⟩ | ⟨hq0, rfl⟩
    · exact E200 U W t₁ hKU hAU hrU ⟨hZ2 W hB hq0, hfr, hRU⟩
    · have hsU : U.cpu.gpr.rsp = g₀.rsp - 8 - 8 - 8 - 8 - 8 := hRU.1
      refine c.s_call hKU hAU hin (lt_len (by decide)) hrU (call_195 _) hin1 (by decide) tgt_195
        (by rw [hsU]; exact w6) ?_
      rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
      rw [hsU] at hA₂
      have hsY₂ : Y₂.cpu.gpr.rsp = g₀.rsp - 8 - 8 - 8 - 8 - 8 - 8 :=
        (congrArg Gprs.rsp hg₂).trans (congrArg (fun x : Addr => x - 8) hsU)
      have hdi₂ : Y₂.cpu.gpr.rdi = rdq(W, g₀.rdi + 32#64) := (congrArg Gprs.rdi hg₂).trans (congrArg Gprs.rdi hgU)
      refine hC2 W hB hq0 Y₂ t₂ hK₂ hA₂ hr₂ hsY₂ hdi₂ ?_
      rintro Z V'' t'' hKZ hAZ hI hrZ ⟨b1, b2, b3, b4, b5, b6, b7⟩ hkf
      refine E200 Z V'' t'' hKZ hAZ hrZ ⟨hI, hfr.kf hkf, ?_, ?_, ?_⟩
      · rw [b1, hsY₂, a1s]
      · exact b4.trans ((congrArg Gprs.r12 hg₂).trans hRU.2.1)
      · exact b7.trans ((congrArg Gprs.r15 hg₂).trans hRU.2.2)
  -- 170: the 8 bytes at `this + 48`
  rintro Y W t' hKY hAY hrY ⟨hB, hfr, hR⟩
  have h12 : Y.cpu.gpr.r12 = g₀.rdi := hR.2.1
  refine (c_170 prof).run c hin _ hKY hAY hrY
    (vc_170 (q := rdq(W, g₀.rdi + 48#64)) (by rw [h12]) (by rw [h12]; exact f48)) ?_
  rintro j' g fl V₁ ⟨hj, rfl, hV₁⟩ U t₁ hKU hAU hrU hgU -
  subst V₁
  have hRU : Rs g₀ U.cpu.gpr := by rw [hgU]; exact hR
  rcases hj with ⟨hq0, rfl⟩ | ⟨hq0, rfl⟩
  · exact E185 U W t₁ hKU hAU hrU ⟨hZ1 W hB hq0, hfr, hRU⟩
  · have hsU : U.cpu.gpr.rsp = g₀.rsp - 8 - 8 - 8 - 8 - 8 := hRU.1
    refine c.s_call hKU hAU hin (lt_len (by decide)) hrU (call_180 _) hin1 (by decide) tgt_180
      (by rw [hsU]; exact w6) ?_
    rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
    rw [hsU] at hA₂
    have hsY₂ : Y₂.cpu.gpr.rsp = g₀.rsp - 8 - 8 - 8 - 8 - 8 - 8 :=
      (congrArg Gprs.rsp hg₂).trans (congrArg (fun x : Addr => x - 8) hsU)
    have hdi₂ : Y₂.cpu.gpr.rdi = rdq(W, g₀.rdi + 48#64) := (congrArg Gprs.rdi hg₂).trans (congrArg Gprs.rdi hgU)
    refine hC1 W hB hq0 Y₂ t₂ hK₂ hA₂ hr₂ hsY₂ hdi₂ ?_
    rintro Z V'' t'' hKZ hAZ hB1 hrZ ⟨b1, b2, b3, b4, b5, b6, b7⟩ hkf
    refine E185 Z V'' t'' hKZ hAZ hrZ ⟨hB1, hfr.kf hkf, ?_, ?_, ?_⟩
    · rw [b1, hsY₂, a1s]
    · exact b4.trans ((congrArg Gprs.r12 hg₂).trans hRU.2.1)
    · exact b7.trans ((congrArg Gprs.r15 hg₂).trans hRU.2.2)

end FV7z.Cpd
