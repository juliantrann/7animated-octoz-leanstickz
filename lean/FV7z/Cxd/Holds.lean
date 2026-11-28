import FV7z.Cxd.Cuts
import FV7z.Tiny.Tj
import FV7z.Lemmas.LeafRet
import FV7z.Tun.Inv
import FV7z.Ocv.Holds
/-!
# `CObjectVector<CXmlProp>::~CObjectVector` (PLAN.md §M, M1)

7-Zip 26.06's `CObjectVector<CXmlProp>::~CObjectVector (this)` at `0x5f63c0` in `7zzs` (`CPP/Common/MyVector.h`,
from `ApfsHandler.o`; `objdump -d`), `S` the stack pointer at the entry: `r12`, `rbp`, `rbx` pushed, `r12` = `this`,
`eax` = `_v._size` (the 4 bytes at `this + 8`), `rdi` = `_v._items` (`it`, the 8 bytes at `this`). When the size `n`
is not 0, `rbx` = `8 (n - 1)` and the loop from 32 runs for `k` = `n - 1` down to 0: `p` = `_items[k]` (the 8 bytes
at `it + 8k`); when `p` is not 0 (a `CXmlProp`: two `AString`s, `Name` at `p` and `Value` at `p + 16`), `Value`'s
chars (the 8 bytes at `p + 16`) are freed when not 0 (`call 0x6014f0` at 50, `operator delete [] (q)`), then
`Name`'s (the 8 bytes at `p`, `call 0x6014f0` at 64), then `p` (`call 0x6014e0` at 77, `operator delete (p, 32)`),
and `rdi` = `_items` again (82); then `rbx` -= 8 (86). At 96 the registers are popped; when `it` is 0, `ret` (116),
else `jmp 0x6014f0` (105, `operator delete [] (it)` as a tail call).

The proof follows `FV7z.Ocv` (the same template with one string per item). The callees are hypotheses on the bytes
they are given and leave (`I`, `J`, `K`, chosen by the caller): `I k` before the `k`-th step's frees are done (`I n`
at the start, `I 0` at the end), `J k p` after `Value`'s chars, `K k p` after `Name`'s. `Call1 S f ra A V P`: from
`f` with `rsp` = `S - 32`, the return address `ra` at `S - 32`, the arguments `A` and the bytes `V`, the run goes on
to the goal if it does from every state at `ra` with bytes `V'`, `P V'`, the registers a call keeps (`Bk`) and the
saved registers and the return address as in `V` (`Kf`).

- `Fr`: the saved registers and the return address in the bytes; `Rs`: the registers the loop keeps; `pk V it k`:
  `_items[k]`; `pops3`: the registers after the pops.
- `vc_*`: the verification conditions of the pieces; `cxd_ok`: from the entry to the return address (`kr`) or to
  `0x6014f0` (`kt`).
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Cxd

/-! ## The instructions outside the blocks -/

/-- The `call` to `0x6014f0` at 50. -/
def qc50 : List Byte := [0xe8, 0xf9, 0xb0, 0x00, 0x00]
theorem qc50_0 : ∀ feat, Dec feat qc50 0 (FV7z.mk .call 64 [.rel 45305] 5) := by dec_rfl
theorem wc_50 : qc50 <+: cxd.drop 50 := by decide +kernel
theorem call_50 (feat : Features) : Dec feat cxd 50 (FV7z.mk .call 64 [.rel 45305] 5) :=
  Dec.shift (j := 50) (k := 0) (qc50_0 feat) wc_50 (Nat.zero_le _)
theorem tgt_50 : cxd_at.add (50 + 5) + BitVec.ofNat 64 45305 = 0x6014f0#64 := by decide

/-- The `call` to `0x6014f0` at 64. -/
def qc64 : List Byte := [0xe8, 0xeb, 0xb0, 0x00, 0x00]
theorem qc64_0 : ∀ feat, Dec feat qc64 0 (FV7z.mk .call 64 [.rel 45291] 5) := by dec_rfl
theorem wc_64 : qc64 <+: cxd.drop 64 := by decide +kernel
theorem call_64 (feat : Features) : Dec feat cxd 64 (FV7z.mk .call 64 [.rel 45291] 5) :=
  Dec.shift (j := 64) (k := 0) (qc64_0 feat) wc_64 (Nat.zero_le _)
theorem tgt_64 : cxd_at.add (64 + 5) + BitVec.ofNat 64 45291 = 0x6014f0#64 := by decide

/-- The `call` to `0x6014e0` at 77. -/
def qc77 : List Byte := [0xe8, 0xce, 0xb0, 0x00, 0x00]
theorem qc77_0 : ∀ feat, Dec feat qc77 0 (FV7z.mk .call 64 [.rel 45262] 5) := by dec_rfl
theorem wc_77 : qc77 <+: cxd.drop 77 := by decide +kernel
theorem call_77 (feat : Features) : Dec feat cxd 77 (FV7z.mk .call 64 [.rel 45262] 5) :=
  Dec.shift (j := 77) (k := 0) (qc77_0 feat) wc_77 (Nat.zero_le _)
theorem tgt_77 : cxd_at.add (77 + 5) + BitVec.ofNat 64 45262 = 0x6014e0#64 := by decide

/-- The `jmp` to `0x6014f0` at 105. -/
def qjm : List Byte := [0xe9, 0xc2, 0xb0, 0x00, 0x00]
theorem qjm_0 : ∀ feat, Dec feat qjm 0 (FV7z.mk .jmp 64 [.rel 45250] 5) := by dec_rfl
theorem wx_105 : qjm <+: cxd.drop 105 := by decide +kernel
theorem jmp_105 (feat : Features) : Dec feat cxd 105 (FV7z.mk .jmp 64 [.rel 45250] 5) :=
  Dec.shift (j := 105) (k := 0) (qjm_0 feat) wx_105 (Nat.zero_le _)

/-- The `ret`. -/
def qret : List Byte := [0xc3]
theorem qret_0 : ∀ feat, Dec feat qret 0 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem wr_116 : qret <+: cxd.drop 116 := by decide +kernel
theorem ret_116 (feat : Features) : Dec feat cxd 116 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 116) (k := 0) (qret_0 feat) wr_116 (Nat.zero_le _)

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

/-- The registers after `pop rbx; pop rbp; pop r12`. -/
abbrev pops3 (V : Addr → Byte) (g : Gprs) : Gprs :=
  { g with
      rbx := rdq(V, g.rsp),
      rbp := rdq(V, g.rsp + 8),
      rsp := g.rsp + 8 + 8 + 8,
      r12 := rdq(V, g.rsp + 8 + 8) }

theorem a3s (x : Addr) : x - 8 - 8 - 8 + 8 = x - 8 - 8 := BitVec.sub_add_cancel _ _
theorem a2s (x : Addr) : x - 8 - 8 + 8 = x - 8 := BitVec.sub_add_cancel _ _
theorem a1s (x : Addr) : x - 8 + 8 = x := BitVec.sub_add_cancel _ _

/-- The closer of the pieces' conditions. -/
local macro "ccl" : tactic => `(tactic| (all_goals repeat'
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

/-- From the entry with the size 0: the pushes, `r12` = `this`, `it` read; to 96. -/
theorem vc_0z {n32 : BitVec 32} {it : BitVec 64}
    (hn : rdd(Vp V g, g.rdi + 8#64) = n32) (hit : rdq(Vp V g, g.rdi) = it) (hn0 : n32 = 0)
    (fn : ∀ i < 4, Foot F.data (Addr.add (g.rdi + 8#64) i)) (fa : ∀ i < 8, Foot F.data (Addr.add g.rdi i))
    (w1 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8) i)) (w2 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8) i))
    (w3 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8 - 8) i)) :
    W_0 F Wl (fun j' g' _ V' => V' = Vp V g ∧ Rs g g' ∧ g'.rdi = it ∧ j' = 96) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [Vp] at hn hit fn fa w1 w2 w3 ⊢
  have e : (n32 == 0) = true := beq_iff_eq.2 hn0
  wpx [W_0, W_21, o0, o1, Op.shl64, Rs, hn, hit, e, BitVec.and_self, Bool.false_eq_true, Bool.true_eq_false,
    false_implies, eq_self_iff_true, true_implies, implies_true]
  ccl

/-- From the entry with the size `n32` not 0: the pushes, `r12` = `this`, `it` read; to 32 with `rbx` =
`Ocv.rbx0 n32`. -/
theorem vc_0n {n32 : BitVec 32} {it : BitVec 64}
    (hn : rdd(Vp V g, g.rdi + 8#64) = n32) (hit : rdq(Vp V g, g.rdi) = it) (hn0 : n32 ≠ 0)
    (fn : ∀ i < 4, Foot F.data (Addr.add (g.rdi + 8#64) i)) (fa : ∀ i < 8, Foot F.data (Addr.add g.rdi i))
    (w1 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8) i)) (w2 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8) i))
    (w3 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8 - 8) i)) :
    W_0 F Wl (fun j' g' _ V' => V' = Vp V g ∧ Rs g g' ∧ g'.rdi = it ∧ j' = 32 ∧ g'.rbx = Ocv.rbx0 n32) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [Vp] at hn hit fn fa w1 w2 w3 ⊢
  have e : (n32 == 0) = false := beq_eq_false_iff_ne.2 hn0
  wpx [W_0, W_21, o0, o1, Op.shl64, Rs, hn, hit, e, BitVec.and_self, Bool.false_eq_true, Bool.true_eq_false,
    false_implies, eq_self_iff_true, true_implies, implies_true]
  ccl

/-- 32 with `_items[k]` 0: to 86. -/
theorem vc_32z {p : BitVec 64} (hp : rdq(V, g.rdi + g.rbx) = p)
    (fp : ∀ i < 8, Foot F.data (Addr.add (g.rdi + g.rbx) i)) (hp0 : p = 0) :
    W_32 F Wl (fun j' g' _ V' => j' = 86 ∧ g' = { g with rbp := p } ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hp fp ⊢
  have e : (p == 0) = true := beq_iff_eq.2 hp0
  wpx [W_32, W_41, o2, o3, hp, e, BitVec.and_self, Bool.false_eq_true, Bool.true_eq_false, false_implies,
    eq_self_iff_true, true_implies, implies_true]
  ccl

/-- 32 with `_items[k]` = `p` not 0: `rdi` = `q` = `p->Value._chars`; to 55 when it is 0, else to the `call` at
50. -/
theorem vc_32n {p q : BitVec 64} (hp : rdq(V, g.rdi + g.rbx) = p)
    (fp : ∀ i < 8, Foot F.data (Addr.add (g.rdi + g.rbx) i)) (hp0 : p ≠ 0) (hq : rdq(V, p + 16#64) = q)
    (fq : ∀ i < 8, Foot F.data (Addr.add (p + 16#64) i)) :
    W_32 F Wl (fun j' g' _ V' => (q = 0 ∧ j' = 55 ∨ q ≠ 0 ∧ j' = 50) ∧ g' = { g with rbp := p, rdi := q } ∧
      V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hp fp ⊢
  have e : (p == 0) = false := beq_eq_false_iff_ne.2 hp0
  wpx [W_32, W_41, o2, o3, hp, hq, e, BitVec.and_self, beq_iff_eq, beq_eq_false_iff_ne, Bool.false_eq_true,
    Bool.true_eq_false, false_implies, eq_self_iff_true, true_implies, implies_true]
  ccl

/-- 55: `rdi` = `q` = `p->Name._chars` (`p` = `rbp`); to 69 when it is 0, else to the `call` at 64. -/
theorem vc_55 {q : BitVec 64} (hq : rdq(V, g.rbp) = q) (fq : ∀ i < 8, Foot F.data (Addr.add g.rbp i)) :
    W_55 F Wl (fun j' g' _ V' => (q = 0 ∧ j' = 69 ∨ q ≠ 0 ∧ j' = 64) ∧ g' = { g with rdi := q } ∧ V' = V)
      g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hq fq ⊢
  wpx [W_55, o4, hq, BitVec.and_self, beq_iff_eq, beq_eq_false_iff_ne, Bool.false_eq_true,
    Bool.true_eq_false, false_implies, eq_self_iff_true, true_implies, implies_true]
  ccl

/-- 69: `rdi` = `rbp`, `esi` = 32; to the `call` at 77. -/
theorem vc_69 :
    W_69 F Wl (fun j' g' _ V' => j' = 77 ∧ g' = { g with rdi := g.rbp, rsi := 32#64 } ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_69, o5, BitVec.reduceSetWidth]
  ccl

/-- 82: `rdi` = `_items` again; to 86. -/
theorem vc_82 {it : BitVec 64} (hit : rdq(V, g.r12) = it) (fa : ∀ i < 8, Foot F.data (Addr.add g.r12 i)) :
    W_82 F Wl (fun j' g' _ V' => j' = 86 ∧ g' = { g with rdi := it } ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hit fa ⊢
  wpx [W_82, o6, hit]
  ccl

/-- 86, the last step: `rbx` -= 8 gives `-8`; to 96. -/
theorem vc_86l (h : g.rbx - 8#64 = 18446744073709551608#64) :
    W_86 F Wl (fun j' g' _ V' => j' = 96 ∧ g' = { g with rbx := g.rbx - 8#64 } ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h ⊢
  have e := decide_eq_true h
  wpx [W_86, o7, e, Bool.not_true, Bool.not_false, Bool.false_eq_true, Bool.true_eq_false, false_implies,
    eq_self_iff_true, true_implies, implies_true]
  ccl

/-- 86, not the last step: back to 32. -/
theorem vc_86c (h : g.rbx - 8#64 ≠ 18446744073709551608#64) :
    W_86 F Wl (fun j' g' _ V' => j' = 32 ∧ g' = { g with rbx := g.rbx - 8#64 } ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h ⊢
  have e := decide_eq_false h
  wpx [W_86, o7, e, Bool.not_true, Bool.not_false, Bool.false_eq_true, Bool.true_eq_false, false_implies,
    eq_self_iff_true, true_implies, implies_true]
  ccl

/-- 96 with `rdi` 0: the pops, to the `ret` at 116. -/
theorem vc_96z {Q : Post} (hz : g.rdi = 0) (l3 : ∀ i < 8, Foot F.data (Addr.add g.rsp i))
    (l2 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8) i)) (l1 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8 + 8) i))
    (h : ∀ fl, Q 116 (pops3 V g) fl V) : W_96 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [pops3] at hz l3 l2 l1 h ⊢
  have e : (rdi == 0) = true := beq_iff_eq.2 hz
  wpx [W_96, W_112, W_101, o8, o9, e, BitVec.and_self, Bool.false_eq_true, Bool.true_eq_false, false_implies,
    eq_self_iff_true, true_implies]
  all_goals repeat' (first | exact h _ | assumption | exact trivial | apply And.intro | intro _)

/-- 96 with `rdi` not 0: the pops, to the `jmp` at 105. -/
theorem vc_96n {Q : Post} (hz : g.rdi ≠ 0) (l3 : ∀ i < 8, Foot F.data (Addr.add g.rsp i))
    (l2 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8) i)) (l1 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8 + 8) i))
    (h : ∀ fl, Q 105 (pops3 V g) fl V) : W_96 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [pops3] at hz l3 l2 l1 h ⊢
  have e : (rdi == 0) = false := beq_eq_false_iff_ne.2 hz
  wpx [W_96, W_112, W_101, o8, o9, e, BitVec.and_self, Bool.false_eq_true, Bool.true_eq_false, false_implies,
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
    Y.cpu.rip = cxd_at.add j → P Y.cpu.gpr V → GoG prof L o gev gP gE Y t

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {X : State} {t : Nat} {V : Addr → Byte}

/-- `~CObjectVector (this)` (`rdi`) from its entry, the size `n32` (the 4 bytes at `this + 8`, as read) and the
items `it` (the 8 bytes at `this` whenever `I` holds). The step `k` (from `n - 1` down to 0) starts with `I (k + 1)`
and ends with `I k`: when `_items[k]` (`pk`) is 0 at once (`hP0`); else through `J k p` after `operator delete []`
of `Value`'s chars (`hD1`, at `0x6014f0`, or at once when they are NULL: `hQ0`), `K k p` after `Name`'s (`hD2`, or
`hR0`), and `operator delete (p, 32)` (`hD3`, at `0x6014e0`). With `I 0` the run reaches the return address with
the registers a call keeps when `it` is 0 (`kr`), else `0x6014f0` with `rsp` as at the entry, `rdi` = `it`, the
saved registers back and the return address in place (`kt`). -/
theorem cxd_ok {n32 : BitVec 32} {it : BitVec 64} {I : Nat → (Addr → Byte) → Prop}
    {J K : Nat → BitVec 64 → (Addr → Byte) → Prop} {e₂ : Addr} {code₂ : List Byte} {j₂ : Nat}
    (c : Seg prof F Wl L s₀ o) (hin : CodeIn L cxd_at cxd)
    (hin1 : CodeIn L 0x6014f0#64 Tiny.c6014f0) (hin2 : CodeIn L 0x6014e0#64 Tiny.c6014e0)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = cxd_at)
    (w1 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8) i))
    (w2 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8 - 8) i))
    (w3 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8 - 8 - 8) i))
    (w4 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8 - 8 - 8 - 8) i))
    (hl : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsp i))
    (fn : ∀ i < 4, Foot F.data (Addr.add (X.cpu.gpr.rdi + 8#64) i))
    (fa : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rdi i))
    (fe : ∀ k < n32.toNat, ∀ i < 8, Foot F.data (Addr.add (it + BitVec.ofNat 64 (8 * k)) i))
    (fp : ∀ k < n32.toNat, ∀ W, I (k + 1) W → pk W it k ≠ 0 → ∀ i < 8, Foot F.data (Addr.add (pk W it k) i))
    (fp16 : ∀ k < n32.toNat, ∀ W, I (k + 1) W → pk W it k ≠ 0 →
      ∀ i < 8, Foot F.data (Addr.add (pk W it k + 16#64) i))
    (hn : rdd(Vp V X.cpu.gpr, X.cpu.gpr.rdi + 8#64) = n32)
    (hI : I n32.toNat (Vp V X.cpu.gpr)) (hf : Fr X.cpu.gpr (e₂.add j₂) (Vp V X.cpu.gpr))
    (hIt : ∀ k W, I k W → rdq(W, X.cpu.gpr.rdi) = it)
    (hP0 : ∀ k < n32.toNat, ∀ W, I (k + 1) W → pk W it k = 0 → I k W)
    (hQ0 : ∀ k < n32.toNat, ∀ W, I (k + 1) W → pk W it k ≠ 0 → rdq(W, pk W it k + 16#64) = 0 →
      J k (pk W it k) W)
    (hD1 : ∀ k < n32.toNat, ∀ W, I (k + 1) W → pk W it k ≠ 0 → rdq(W, pk W it k + 16#64) ≠ 0 →
      Call1 prof F Wl L s₀ o gev gP gE X.cpu.gpr.rsp 0x6014f0#64 (cxd_at.add 55)
        (fun g => g.rdi = rdq(W, pk W it k + 16#64)) W (J k (pk W it k)))
    (hR0 : ∀ k < n32.toNat, ∀ p W, p ≠ 0 → J k p W → rdq(W, p) = 0 → K k p W)
    (hD2 : ∀ k < n32.toNat, ∀ p W, p ≠ 0 → J k p W → rdq(W, p) ≠ 0 →
      Call1 prof F Wl L s₀ o gev gP gE X.cpu.gpr.rsp 0x6014f0#64 (cxd_at.add 69)
        (fun g => g.rdi = rdq(W, p)) W (K k p))
    (hD3 : ∀ k < n32.toNat, ∀ p W, p ≠ 0 → K k p W →
      Call1 prof F Wl L s₀ o gev gP gE X.cpu.gpr.rsp 0x6014e0#64 (cxd_at.add 82)
        (fun g => g.rdi = p ∧ g.rsi = 32#64) W (I k))
    (hin₂ : CodeIn L e₂ code₂) (h₂ : j₂ < code₂.length)
    (kt : ∀ (Y : State) (W : Addr → Byte) (t' : Nat), KeptW Wl s₀ Y → Agree F Y.proc.mm.mem W → I 0 W →
      Fr X.cpu.gpr (e₂.add j₂) W → Y.cpu.rip = 0x6014f0#64 → Y.cpu.gpr.rsp = X.cpu.gpr.rsp →
      Y.cpu.gpr.rdi = it → it ≠ 0 → Kp X.cpu.gpr Y.cpu.gpr → GoG prof L o gev gP gE Y t')
    (kr : ∀ (Z : State) (W : Addr → Byte) (t' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem W → I 0 W →
      Z.cpu.rip = e₂.add j₂ → Bk X.cpu.gpr Z.cpu.gpr → it = 0 → GoG prof L o gev gP gE Z t') :
    GoG prof L o gev gP gE X t := by
  have hn32 : n32.toNat < 4294967296 := n32.isLt
  -- the end, from 96
  have F96 : AtJ prof F Wl L s₀ o gev gP gE 96 fun g W => I 0 W ∧ Fr X.cpu.gpr (e₂.add j₂) W ∧
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
    · refine (c_96 prof).run c hin (fun j' g' _ V₁ => j' = 116 ∧ g' = pops3 W Y.cpu.gpr ∧ V₁ = W) hKY hAY hrY
        (vc_96z (hdi.trans hz0) l3 l2 l1 fun _ => ⟨rfl, rfl, rfl⟩) ?_
      rintro j' g fl V₁ ⟨rfl, rfl, hV₁⟩ U t₁ hKU hAU hrU hgU -
      subst V₁
      have hsU : U.cpu.gpr.rsp = X.cpu.gpr.rsp := (congrArg Gprs.rsp hgU).trans hsP
      refine c.s_ret hKU hAU hin (lt_len (by decide)) hrU (ret_116 _) (by rw [hsU]; exact hl) hin₂ h₂
        (by rw [hsU]; exact hfr.2.2.2) ?_
      rintro Z t₂ hKZ hAZ ⟨hrZ, hgZ⟩
      refine kr Z W t₂ hKZ hAZ hI0 hrZ ⟨?_, ?_⟩ hz0
      · rw [hgZ]
        show U.cpu.gpr.rsp + 8 = _
        rw [hsU]
      · rw [hgZ, hgU]
        exact hkP
    · refine (c_96 prof).run c hin (fun j' g' _ V₁ => j' = 105 ∧ g' = pops3 W Y.cpu.gpr ∧ V₁ = W) hKY hAY hrY
        (vc_96n (fun h => hz0 (hdi.symm.trans h)) l3 l2 l1 fun _ => ⟨rfl, rfl, rfl⟩) ?_
      rintro j' g fl V₁ ⟨rfl, rfl, hV₁⟩ U t₁ hKU hAU hrU hgU -
      subst V₁
      refine c.s_jmp_x hKU hAU hin (lt_len (by decide)) hrU (jmp_105 _) (tgt := 0) hin1 (by decide) (by decide) ?_
      rintro Z t₂ hKZ hAZ ⟨hrZ, hgZ⟩
      refine kt Z W t₂ hKZ hAZ hI0 hfr (by rw [hrZ, addr_add_zero]) ?_ ?_ hz0 ?_
      · rw [hgZ, hgU]
        exact hsP
      · rw [hgZ, hgU]
        exact hdi
      · rw [hgZ, hgU]
        exact hkP
  -- 86: `rbx` -= 8, to 96 after the step 0, else to 32
  have S86 : ∀ k, k < n32.toNat →
      (∀ k', k = k' + 1 → AtJ prof F Wl L s₀ o gev gP gE 32 fun g W => I (k' + 1) W ∧
        Fr X.cpu.gpr (e₂.add j₂) W ∧ Rs X.cpu.gpr g ∧ g.rdi = it ∧ g.rbx = BitVec.ofNat 64 (8 * k')) →
      AtJ prof F Wl L s₀ o gev gP gE 86 fun g W => I k W ∧ Fr X.cpu.gpr (e₂.add j₂) W ∧ Rs X.cpu.gpr g ∧
        g.rdi = it ∧ g.rbx = BitVec.ofNat 64 (8 * k) := by
    rintro k hk hnx Y W t' hKY hAY hrY ⟨hIk, hfr, hR, hdi, hb⟩
    cases k with
    | zero =>
      refine (c_86 prof).run c hin _ hKY hAY hrY (vc_86l (by rw [hb]; exact Ocv.rb_last)) ?_
      rintro j' g fl V₁ ⟨rfl, rfl, hV₁⟩ U t₁ hKU hAU hrU hgU -
      subst V₁
      exact F96 U W t₁ hKU hAU hrU ⟨hIk, hfr, by rw [hgU]; exact hR, (congrArg Gprs.rdi hgU).trans hdi⟩
    | succ k =>
      refine (c_86 prof).run c hin _ hKY hAY hrY
        (vc_86c (by rw [hb, Ocv.rb_step k (by omega)]; exact Ocv.rb_ne k (by omega))) ?_
      rintro j' g fl V₁ ⟨rfl, rfl, hV₁⟩ U t₁ hKU hAU hrU hgU -
      subst V₁
      have hbU : U.cpu.gpr.rbx = BitVec.ofNat 64 (8 * k) := by
        rw [hgU]
        show Y.cpu.gpr.rbx - 8#64 = _
        rw [hb]
        exact Ocv.rb_step k (by omega)
      exact hnx k rfl U W t₁ hKU hAU hrU ⟨hIk, hfr, by rw [hgU]; exact hR, (congrArg Gprs.rdi hgU).trans hdi, hbU⟩
  -- 69: `operator delete (p, 32)`, `rdi` = `_items` again, to 86
  have A69 : ∀ k, k < n32.toNat → ∀ p : BitVec 64, p ≠ 0 →
      AtJ prof F Wl L s₀ o gev gP gE 86 (fun g W => I k W ∧ Fr X.cpu.gpr (e₂.add j₂) W ∧ Rs X.cpu.gpr g ∧
        g.rdi = it ∧ g.rbx = BitVec.ofNat 64 (8 * k)) →
      AtJ prof F Wl L s₀ o gev gP gE 69 fun g W => K k p W ∧ Fr X.cpu.gpr (e₂.add j₂) W ∧ Rs X.cpu.gpr g ∧
        g.rbp = p ∧ g.rbx = BitVec.ofNat 64 (8 * k) := by
    rintro k hk p hp h86 Y W t' hKY hAY hrY ⟨hJ, hfr, hR, hbp, hb⟩
    refine (c_69 prof).run c hin _ hKY hAY hrY vc_69 ?_
    rintro j' g fl V₁ ⟨rfl, rfl, hV₁⟩ U t₁ hKU hAU hrU hgU -
    subst V₁
    have hRU : Rs X.cpu.gpr U.cpu.gpr := by rw [hgU]; exact hR
    have hbU : U.cpu.gpr.rbx = BitVec.ofNat 64 (8 * k) := (congrArg Gprs.rbx hgU).trans hb
    have hsU : U.cpu.gpr.rsp = X.cpu.gpr.rsp - 8 - 8 - 8 := hRU.1
    refine c.s_call hKU hAU hin (lt_len (by decide)) hrU (call_77 _) hin2 (by decide) tgt_77
      (by rw [hsU]; exact w4) ?_
    rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
    rw [hsU] at hA₂
    have hsY₂ : Y₂.cpu.gpr.rsp = X.cpu.gpr.rsp - 8 - 8 - 8 - 8 :=
      (congrArg Gprs.rsp hg₂).trans (congrArg (fun x : Addr => x - 8) hsU)
    have hdi₂ : Y₂.cpu.gpr.rdi = p ∧ Y₂.cpu.gpr.rsi = 32#64 :=
      ⟨(congrArg Gprs.rdi hg₂).trans ((congrArg Gprs.rdi hgU).trans hbp),
        (congrArg Gprs.rsi hg₂).trans (congrArg Gprs.rsi hgU)⟩
    refine hD3 k hk p W hp hJ Y₂ t₂ hK₂ hA₂ hr₂ hsY₂ hdi₂ ?_
    rintro Z V'' t'' hKZ hAZ hIk hrZ ⟨b1, b2, b3, b4, b5, b6, b7⟩ hkf
    have hsZ : Z.cpu.gpr.rsp = X.cpu.gpr.rsp - 8 - 8 - 8 := by rw [b1, hsY₂, a1s]
    have h12Z : Z.cpu.gpr.r12 = X.cpu.gpr.rdi := b4.trans ((congrArg Gprs.r12 hg₂).trans hRU.2.1)
    refine (c_82 prof).run c hin _ hKZ hAZ hrZ
      (vc_82 (it := it) (by rw [h12Z]; exact hIt k V'' hIk) (by rw [h12Z]; exact fa)) ?_
    rintro j' g fl V₁ ⟨rfl, rfl, hV₁⟩ U₂ t₃ hKU₂ hAU₂ hrU₂ hgU₂ -
    subst V₁
    refine h86 U₂ V'' t₃ hKU₂ hAU₂ hrU₂ ⟨hIk, hfr.kf hkf, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
    · exact (congrArg Gprs.rsp hgU₂).trans hsZ
    · exact (congrArg Gprs.r12 hgU₂).trans h12Z
    · exact (congrArg Gprs.r13 hgU₂).trans (b5.trans ((congrArg Gprs.r13 hg₂).trans hRU.2.2.1))
    · exact (congrArg Gprs.r14 hgU₂).trans (b6.trans ((congrArg Gprs.r14 hg₂).trans hRU.2.2.2.1))
    · exact (congrArg Gprs.r15 hgU₂).trans (b7.trans ((congrArg Gprs.r15 hg₂).trans hRU.2.2.2.2))
    · exact congrArg Gprs.rdi hgU₂
    · exact (congrArg Gprs.rbx hgU₂).trans (b2.trans ((congrArg Gprs.rbx hg₂).trans hbU))
  -- 55: `Name`'s chars freed unless NULL, to 69
  have A55 : ∀ k, k < n32.toNat → ∀ p : BitVec 64, p ≠ 0 → (∀ i < 8, Foot F.data (Addr.add p i)) →
      AtJ prof F Wl L s₀ o gev gP gE 86 (fun g W => I k W ∧ Fr X.cpu.gpr (e₂.add j₂) W ∧ Rs X.cpu.gpr g ∧
        g.rdi = it ∧ g.rbx = BitVec.ofNat 64 (8 * k)) →
      AtJ prof F Wl L s₀ o gev gP gE 55 fun g W => J k p W ∧ Fr X.cpu.gpr (e₂.add j₂) W ∧ Rs X.cpu.gpr g ∧
        g.rbp = p ∧ g.rbx = BitVec.ofNat 64 (8 * k) := by
    rintro k hk p hp fpp h86 Y W t' hKY hAY hrY ⟨hJ, hfr, hR, hbp, hb⟩
    refine (c_55 prof).run c hin _ hKY hAY hrY
      (vc_55 (q := rdq(W, p)) (by rw [hbp]) (by rw [hbp]; exact fpp)) ?_
    rintro j' g fl V₁ ⟨hj, rfl, hV₁⟩ U t₁ hKU hAU hrU hgU -
    subst V₁
    have hRU : Rs X.cpu.gpr U.cpu.gpr := by rw [hgU]; exact hR
    have hbU : U.cpu.gpr.rbx = BitVec.ofNat 64 (8 * k) := (congrArg Gprs.rbx hgU).trans hb
    have hpU : U.cpu.gpr.rbp = p := (congrArg Gprs.rbp hgU).trans hbp
    rcases hj with ⟨hq0, rfl⟩ | ⟨hq0, rfl⟩
    · exact A69 k hk p hp h86 U W t₁ hKU hAU hrU ⟨hR0 k hk p W hp hJ hq0, hfr, hRU, hpU, hbU⟩
    · -- `operator delete [] (Name._chars)`
      have hsU : U.cpu.gpr.rsp = X.cpu.gpr.rsp - 8 - 8 - 8 := hRU.1
      refine c.s_call hKU hAU hin (lt_len (by decide)) hrU (call_64 _) hin1 (by decide) tgt_64
        (by rw [hsU]; exact w4) ?_
      rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
      rw [hsU] at hA₂
      have hsY₂ : Y₂.cpu.gpr.rsp = X.cpu.gpr.rsp - 8 - 8 - 8 - 8 :=
        (congrArg Gprs.rsp hg₂).trans (congrArg (fun x : Addr => x - 8) hsU)
      have hdi₂ : Y₂.cpu.gpr.rdi = rdq(W, p) := (congrArg Gprs.rdi hg₂).trans (congrArg Gprs.rdi hgU)
      refine hD2 k hk p W hp hJ hq0 Y₂ t₂ hK₂ hA₂ hr₂ hsY₂ hdi₂ ?_
      rintro Z V'' t'' hKZ hAZ hKk hrZ ⟨b1, b2, b3, b4, b5, b6, b7⟩ hkf
      refine A69 k hk p hp h86 Z V'' t'' hKZ hAZ hrZ ⟨hKk, hfr.kf hkf, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
      · rw [b1, hsY₂, a1s]
      · exact b4.trans ((congrArg Gprs.r12 hg₂).trans hRU.2.1)
      · exact b5.trans ((congrArg Gprs.r13 hg₂).trans hRU.2.2.1)
      · exact b6.trans ((congrArg Gprs.r14 hg₂).trans hRU.2.2.2.1)
      · exact b7.trans ((congrArg Gprs.r15 hg₂).trans hRU.2.2.2.2)
      · exact b3.trans ((congrArg Gprs.rbp hg₂).trans hpU)
      · exact b2.trans ((congrArg Gprs.rbx hg₂).trans hbU)
  -- 32: the step `k`, to 86
  have B32 : ∀ k, k < n32.toNat →
      AtJ prof F Wl L s₀ o gev gP gE 86 (fun g W => I k W ∧ Fr X.cpu.gpr (e₂.add j₂) W ∧ Rs X.cpu.gpr g ∧
        g.rdi = it ∧ g.rbx = BitVec.ofNat 64 (8 * k)) →
      AtJ prof F Wl L s₀ o gev gP gE 32 fun g W => I (k + 1) W ∧ Fr X.cpu.gpr (e₂.add j₂) W ∧ Rs X.cpu.gpr g ∧
        g.rdi = it ∧ g.rbx = BitVec.ofNat 64 (8 * k) := by
    rintro k hk h86 Y W t' hKY hAY hrY ⟨hIk, hfr, hR, hdi, hb⟩
    have hea : Y.cpu.gpr.rdi + Y.cpu.gpr.rbx = it + BitVec.ofNat 64 (8 * k) := by rw [hdi, hb]
    by_cases hp0 : pk W it k = 0
    · refine (c_32 prof).run c hin _ hKY hAY hrY
        (vc_32z (p := pk W it k) (by rw [hea]) (by rw [hea]; exact fe k hk) hp0) ?_
      rintro j' g fl V₁ ⟨rfl, rfl, hV₁⟩ U t₁ hKU hAU hrU hgU -
      subst V₁
      exact h86 U W t₁ hKU hAU hrU ⟨hP0 k hk W hIk hp0, hfr, by rw [hgU]; exact hR,
        (congrArg Gprs.rdi hgU).trans hdi, (congrArg Gprs.rbx hgU).trans hb⟩
    · have fpp := fp k hk W hIk hp0
      refine (c_32 prof).run c hin _ hKY hAY hrY
        (vc_32n (p := pk W it k) (q := rdq(W, pk W it k + 16#64)) (by rw [hea]) (by rw [hea]; exact fe k hk) hp0
          rfl (fp16 k hk W hIk hp0)) ?_
      rintro j' g fl V₁ ⟨hj, rfl, hV₁⟩ U t₁ hKU hAU hrU hgU -
      subst V₁
      have hRU : Rs X.cpu.gpr U.cpu.gpr := by rw [hgU]; exact hR
      have hbU : U.cpu.gpr.rbx = BitVec.ofNat 64 (8 * k) := (congrArg Gprs.rbx hgU).trans hb
      have hpU : U.cpu.gpr.rbp = pk W it k := congrArg Gprs.rbp hgU
      rcases hj with ⟨hq0, rfl⟩ | ⟨hq0, rfl⟩
      · exact A55 k hk _ hp0 fpp h86 U W t₁ hKU hAU hrU ⟨hQ0 k hk W hIk hp0 hq0, hfr, hRU, hpU, hbU⟩
      · -- `operator delete [] (Value._chars)`
        have hsU : U.cpu.gpr.rsp = X.cpu.gpr.rsp - 8 - 8 - 8 := hRU.1
        refine c.s_call hKU hAU hin (lt_len (by decide)) hrU (call_50 _) hin1 (by decide) tgt_50
          (by rw [hsU]; exact w4) ?_
        rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
        rw [hsU] at hA₂
        have hsY₂ : Y₂.cpu.gpr.rsp = X.cpu.gpr.rsp - 8 - 8 - 8 - 8 :=
          (congrArg Gprs.rsp hg₂).trans (congrArg (fun x : Addr => x - 8) hsU)
        have hdi₂ : Y₂.cpu.gpr.rdi = rdq(W, pk W it k + 16#64) :=
          (congrArg Gprs.rdi hg₂).trans (congrArg Gprs.rdi hgU)
        refine hD1 k hk W hIk hp0 hq0 Y₂ t₂ hK₂ hA₂ hr₂ hsY₂ hdi₂ ?_
        rintro Z V'' t'' hKZ hAZ hJ hrZ ⟨b1, b2, b3, b4, b5, b6, b7⟩ hkf
        refine A55 k hk _ hp0 fpp h86 Z V'' t'' hKZ hAZ hrZ ⟨hJ, hfr.kf hkf, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
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
    | zero => exact fun hk => B32 0 hk (S86 0 hk fun k' e => absurd e (by omega))
    | succ k ih =>
      exact fun hk => B32 (k + 1) hk (S86 (k + 1) hk fun k' e => by
        obtain rfl : k = k' := by omega
        exact ih (by omega))
  -- the entry
  have hrip' : X.cpu.rip = cxd_at.add 0 := by rw [addr_add_zero]; exact hrip
  by_cases hn0 : n32 = 0
  · refine (c_0 prof).run c hin _ hK hA hrip' (vc_0z hn (hIt _ _ hI) hn0 fn fa w1 w2 w3) ?_
    rintro j' g fl V₁ ⟨hV₁, hR, hdi, rfl⟩ Y t₁ hKY hAY hrY hgY -
    subst V₁
    subst hgY
    have e0 : n32.toNat = 0 := (congrArg BitVec.toNat hn0).trans rfl
    exact F96 Y _ t₁ hKY hAY hrY ⟨e0 ▸ hI, hf, hR, hdi⟩
  · refine (c_0 prof).run c hin _ hK hA hrip' (vc_0n hn (hIt _ _ hI) hn0 fn fa w1 w2 w3) ?_
    rintro j' g fl V₁ ⟨hV₁, hR, hdi, rfl, hb⟩ Y t₁ hKY hAY hrY hgY -
    subst V₁
    subst hgY
    have hnz : n32.toNat ≠ 0 := fun e => hn0 (BitVec.eq_of_toNat_eq (e.trans rfl))
    have e1 : n32.toNat - 1 + 1 = n32.toNat := by omega
    exact L32 (n32.toNat - 1) (by omega) Y _ t₁ hKY hAY hrY
      ⟨by rw [e1]; exact hI, hf, hR, hdi, by rw [hb, Ocv.rbx0_eq hn0]⟩

end FV7z.Cxd
