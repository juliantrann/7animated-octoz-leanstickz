import FV7z.Msi.Cuts
import FV7z.Ocv.Holds
import FV7z.Lemmas.CallM
/-!
# `CMultiStreams::Init` (PLAN.md §M, M1)

7-Zip 26.06's `CMultiStreams::Init (this)` at `0x5b3260` in `7zzs` (`CPP/7zip/Archive/Common/MultiStream.cpp`;
`objdump -d`), `S` the stack pointer at the entry: `r12`, `rbp`, `rbx` pushed, `eax` = `Streams.Size ()` (`n`, the
4 bytes at `this + 8`), `rbx` = `this`, the 8 bytes at `this + 16` set to -1 and the 4 bytes at `this + 24` to 0.
When `n` is not 0, `rbp` = `8 (n - 1)` and the loop from 48 runs for `k` = `n - 1` down to 0: `p` = `_items[k]`
(`_items` = `it`, the 8 bytes at `this`, read again each time; `p` the 8 bytes at `it + 8k`); when `p` is not 0,
`q` = the 8 bytes at `p + 16` is freed when not 0 (`call 0x6014f0` at 70, `operator delete (q)`), the stream `s` (the
8 bytes at `p`) is released when not 0 (`call qword [rax + 16]` at 87, through its vtable, `Seg.s_callM`), then `p`
is deleted (`call 0x6014e0` at 98, `operator delete (p, 48)`); then `rbp` -= 8 (103). At 113 the 4 bytes at
`this + 8` are set to 0, the registers popped and `ret` (124).

The callees are hypotheses on the bytes they are given and leave (`I`, `J1`, `J2`, chosen by the caller), as in
`FV7z.Ocv`: `I k` before the `k`-th step's calls (`I n` at the start, `I 0` at the end), `J1 k p` after the free of
`q`, `J2 k p` after the release of `s`. `Call1`, `Fr`, `Kf`, `Kp`, `Bk`, `pk`, `pops3`, `rbx0` are `FV7z.Ocv`'s.

- `Rs`: the registers the loop keeps (`rbx` = `this`); `V0`: the bytes after the pushes and the two stores; `Vz`:
  the bytes after the store at 113.
- `vc_*`: the verification conditions of the pieces; `msi_ok`: from the entry to the return address (`kr`).

The reads at the entry are stated on the bytes after the pushes (`hn`) and after the stores (`hI`, `hf`). The
store at 113 is taken to leave the frame as it is (`hF8`).
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
open FV7z.Ocv (Vp Fr Kf Kp Bk Call1 pk rbx0 rbx0_eq rb_step rb_ne rb_last a3s a2s a1s pops3)
namespace FV7z.Msi

/-! ## The instructions outside the blocks -/

/-- The `call` to `0x6014f0` at 70. -/
def qc70 : List Byte := [0xe8, 0x45, 0xe2, 0x04, 0x00]
theorem qc70_0 : ∀ feat, Dec feat qc70 0 (FV7z.mk .call 64 [.rel 320069] 5) := by dec_rfl
theorem wc_70 : qc70 <+: msi.drop 70 := by decide +kernel
theorem call_70 (feat : Features) : Dec feat msi 70 (FV7z.mk .call 64 [.rel 320069] 5) :=
  Dec.shift (j := 70) (k := 0) (qc70_0 feat) wc_70 (Nat.zero_le _)
theorem tgt_70 : msi_at.add (70 + 5) + BitVec.ofNat 64 320069 = 0x6014f0#64 := by decide

/-- The `call` through the vtable at 87. -/
def qc87 : List Byte := [0xff, 0x50, 0x10]
theorem qc87_0 : ∀ feat, Dec feat qc87 0 (FV7z.mk .call 64 [.mem (mbd 0 16 64)] 3) := by dec_rfl
theorem wc_87 : qc87 <+: msi.drop 87 := by decide +kernel
theorem call_87 (feat : Features) : Dec feat msi 87 (FV7z.mk .call 64 [.mem (mbd 0 16 64)] 3) :=
  Dec.shift (j := 87) (k := 0) (qc87_0 feat) wc_87 (Nat.zero_le _)

/-- The `call` to `0x6014e0` at 98. -/
def qc98 : List Byte := [0xe8, 0x19, 0xe2, 0x04, 0x00]
theorem qc98_0 : ∀ feat, Dec feat qc98 0 (FV7z.mk .call 64 [.rel 320025] 5) := by dec_rfl
theorem wc_98 : qc98 <+: msi.drop 98 := by decide +kernel
theorem call_98 (feat : Features) : Dec feat msi 98 (FV7z.mk .call 64 [.rel 320025] 5) :=
  Dec.shift (j := 98) (k := 0) (qc98_0 feat) wc_98 (Nat.zero_le _)
theorem tgt_98 : msi_at.add (98 + 5) + BitVec.ofNat 64 320025 = 0x6014e0#64 := by decide

/-- The `ret`. -/
def qret : List Byte := [0xc3]
theorem qret_0 : ∀ feat, Dec feat qret 0 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem wr_124 : qret <+: msi.drop 124 := by decide +kernel
theorem ret_124 (feat : Features) : Dec feat msi 124 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 124) (k := 0) (qret_0 feat) wr_124 (Nat.zero_le _)

/-! ## The bytes and the loop's registers -/

/-- The bytes after the pushes, `this->_pos` (at 16) = -1 and `this->_streamIndex` (at 24) = 0. -/
abbrev V0 (V : Addr → Byte) (g : Gprs) : Addr → Byte :=
  Vst (Vst (Vp V g) (g.rdi + 16#64) (toBytesLE 18446744073709551615#64 8)) (g.rdi + 24#64) (toBytesLE 0#32 4)

/-- The bytes after `Streams.Size ()` = 0 (the 4 bytes at `b + 8`). -/
abbrev Vz (V : Addr → Byte) (b : Addr) : Addr → Byte := Vst V (b + 8#64) (toBytesLE 0#32 4)

/-- The registers the loop keeps: `rsp` below the pushes, `rbx` = `this`, `r13`–`r15`. -/
def Rs (g₀ g : Gprs) : Prop :=
  g.rsp = g₀.rsp - 8 - 8 - 8 ∧ g.rbx = g₀.rdi ∧ g.r13 = g₀.r13 ∧ g.r14 = g₀.r14 ∧ g.r15 = g₀.r15

/-- The closer of the pieces' conditions. -/
local macro "mcl" : tactic => `(tactic| (all_goals repeat'
    first
    | exact rfl
    | assumption
    | exact trivial
    | (intro h; exact absurd h (by decide))
    | apply And.intro
    | intro _))

variable {F : Footprint} {Wl : List Rgn}

/-! ## The pieces -/

section
variable {g : Gprs} {f : Rflags} {V : Addr → Byte}

/-- From the entry with the size 0: the pushes, `rbx` = `this`, the stores; to 113. -/
theorem vc_0z {n32 : BitVec 32} (hn : rdd(Vp V g, g.rdi + 8#64) = n32) (hn0 : n32 = 0)
    (fn : ∀ i < 4, Foot F.data (Addr.add (g.rdi + 8#64) i))
    (w1 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8) i)) (w2 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8) i))
    (w3 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8 - 8) i))
    (w16 : ∀ i < 8, Foot Wl (Addr.add (g.rdi + 16#64) i)) (w24 : ∀ i < 4, Foot Wl (Addr.add (g.rdi + 24#64) i)) :
    W_0 F Wl (fun j' g' _ V' => V' = V0 V g ∧ Rs g g' ∧ j' = 113) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [V0, Vp] at hn fn w1 w2 w3 w16 w24 ⊢
  have e : (n32 == 0) = true := beq_iff_eq.2 hn0
  wpx [W_0, W_33, o0, o1, Op.shl64, Rs, hn, e, BitVec.and_self, Bool.false_eq_true, Bool.true_eq_false,
    false_implies, eq_self_iff_true, true_implies, implies_true]
  mcl

/-- From the entry with the size `n32` not 0: the pushes, `rbx` = `this`, the stores; to 48 with `rbp` =
`rbx0 n32`. -/
theorem vc_0n {n32 : BitVec 32} (hn : rdd(Vp V g, g.rdi + 8#64) = n32) (hn0 : n32 ≠ 0)
    (fn : ∀ i < 4, Foot F.data (Addr.add (g.rdi + 8#64) i))
    (w1 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8) i)) (w2 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8) i))
    (w3 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8 - 8) i))
    (w16 : ∀ i < 8, Foot Wl (Addr.add (g.rdi + 16#64) i)) (w24 : ∀ i < 4, Foot Wl (Addr.add (g.rdi + 24#64) i)) :
    W_0 F Wl (fun j' g' _ V' => V' = V0 V g ∧ Rs g g' ∧ j' = 48 ∧ g'.rbp = rbx0 n32) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [V0, Vp] at hn fn w1 w2 w3 w16 w24 ⊢
  have e : (n32 == 0) = false := beq_eq_false_iff_ne.2 hn0
  wpx [W_0, W_33, o0, o1, Op.shl64, Rs, hn, e, BitVec.and_self, Bool.false_eq_true, Bool.true_eq_false,
    false_implies, eq_self_iff_true, true_implies, implies_true]
  mcl

/-- 48 with `_items[k]` 0: to 103. -/
theorem vc_48z {it p : BitVec 64} (hit : rdq(V, g.rbx) = it) (fa : ∀ i < 8, Foot F.data (Addr.add g.rbx i))
    (hp : rdq(V, it + g.rbp) = p) (fp : ∀ i < 8, Foot F.data (Addr.add (it + g.rbp) i)) (hp0 : p = 0) :
    W_48 F Wl (fun j' g' _ V' => j' = 103 ∧ g' = { g with rax := it, r12 := p } ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hit fa hp fp ⊢
  have e : (p == 0) = true := beq_iff_eq.2 hp0
  wpx [W_48, W_60, o2, o3, hit, hp, e, BitVec.and_self, Bool.false_eq_true, Bool.true_eq_false, false_implies,
    eq_self_iff_true, true_implies, implies_true]
  mcl

/-- 48 with `_items[k]` = `p` not 0 and `q` (the 8 bytes at `p + 16`) 0: to 75. -/
theorem vc_48a {it p q : BitVec 64} (hit : rdq(V, g.rbx) = it) (fa : ∀ i < 8, Foot F.data (Addr.add g.rbx i))
    (hp : rdq(V, it + g.rbp) = p) (fp : ∀ i < 8, Foot F.data (Addr.add (it + g.rbp) i)) (hp0 : p ≠ 0)
    (hq : rdq(V, p + 16#64) = q) (fq : ∀ i < 8, Foot F.data (Addr.add (p + 16#64) i)) (hq0 : q = 0) :
    W_48 F Wl (fun j' g' _ V' => j' = 75 ∧ g' = { g with rax := it, r12 := p, rdi := q } ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hit fa hp fp hq fq ⊢
  have e : (p == 0) = false := beq_eq_false_iff_ne.2 hp0
  have e2 : (q == 0) = true := beq_iff_eq.2 hq0
  wpx [W_48, W_60, o2, o3, hit, hp, hq, e, e2, BitVec.and_self, Bool.false_eq_true, Bool.true_eq_false,
    false_implies, eq_self_iff_true, true_implies, implies_true]
  mcl

/-- 48 with `p` not 0 and `q` not 0: to the `call` at 70. -/
theorem vc_48b {it p q : BitVec 64} (hit : rdq(V, g.rbx) = it) (fa : ∀ i < 8, Foot F.data (Addr.add g.rbx i))
    (hp : rdq(V, it + g.rbp) = p) (fp : ∀ i < 8, Foot F.data (Addr.add (it + g.rbp) i)) (hp0 : p ≠ 0)
    (hq : rdq(V, p + 16#64) = q) (fq : ∀ i < 8, Foot F.data (Addr.add (p + 16#64) i)) (hq0 : q ≠ 0) :
    W_48 F Wl (fun j' g' _ V' => j' = 70 ∧ g' = { g with rax := it, r12 := p, rdi := q } ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hit fa hp fp hq fq ⊢
  have e : (p == 0) = false := beq_eq_false_iff_ne.2 hp0
  have e2 : (q == 0) = false := beq_eq_false_iff_ne.2 hq0
  wpx [W_48, W_60, o2, o3, hit, hp, hq, e, e2, BitVec.and_self, Bool.false_eq_true, Bool.true_eq_false,
    false_implies, eq_self_iff_true, true_implies, implies_true]
  mcl

/-- 75 with the stream `s` (the 8 bytes at `r12`) 0: to 90. -/
theorem vc_75z {s : BitVec 64} (hs : rdq(V, g.r12) = s) (fs : ∀ i < 8, Foot F.data (Addr.add g.r12 i))
    (hs0 : s = 0) :
    W_75 F Wl (fun j' g' _ V' => j' = 90 ∧ g' = { g with rdi := s } ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hs fs ⊢
  have e : (s == 0) = true := beq_iff_eq.2 hs0
  wpx [W_75, W_84, o4, o5, hs, e, BitVec.and_self, Bool.false_eq_true, Bool.true_eq_false, false_implies,
    eq_self_iff_true, true_implies, implies_true]
  mcl

/-- 75 with `s` not 0: `rax` = its vtable `vt`; to the `call` at 87. -/
theorem vc_75n {s vt : BitVec 64} (hs : rdq(V, g.r12) = s) (fs : ∀ i < 8, Foot F.data (Addr.add g.r12 i))
    (hs0 : s ≠ 0) (hv : rdq(V, s) = vt) (fv : ∀ i < 8, Foot F.data (Addr.add s i)) :
    W_75 F Wl (fun j' g' _ V' => j' = 87 ∧ g' = { g with rdi := s, rax := vt } ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hs fs ⊢
  have e : (s == 0) = false := beq_eq_false_iff_ne.2 hs0
  wpx [W_75, W_84, o4, o5, hs, hv, e, BitVec.and_self, Bool.false_eq_true, Bool.true_eq_false, false_implies,
    eq_self_iff_true, true_implies, implies_true]
  mcl

/-- 90: `esi` = 48, `rdi` = `r12`; to the `call` at 98. -/
theorem vc_90 :
    W_90 F Wl (fun j' g' _ V' => j' = 98 ∧ g' = { g with rsi := 48#64, rdi := g.r12 } ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_90, o6, BitVec.reduceSetWidth]
  mcl

/-- 103, the last step: `rbp` -= 8 gives `-8`; to 113. -/
theorem vc_103l (h : g.rbp - 8#64 = 18446744073709551608#64) :
    W_103 F Wl (fun j' g' _ V' => j' = 113 ∧ g' = { g with rbp := g.rbp - 8#64 } ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h ⊢
  have e := decide_eq_true h
  wpx [W_103, o7, e, Bool.not_true, Bool.not_false, Bool.false_eq_true, Bool.true_eq_false, false_implies,
    eq_self_iff_true, true_implies, implies_true]
  mcl

/-- 103, not the last step: back to 48. -/
theorem vc_103c (h : g.rbp - 8#64 ≠ 18446744073709551608#64) :
    W_103 F Wl (fun j' g' _ V' => j' = 48 ∧ g' = { g with rbp := g.rbp - 8#64 } ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h ⊢
  have e := decide_eq_false h
  wpx [W_103, o7, e, Bool.not_true, Bool.not_false, Bool.false_eq_true, Bool.true_eq_false, false_implies,
    eq_self_iff_true, true_implies, implies_true]
  mcl

/-- 113: the size 0, the pops, to the `ret` at 124. -/
theorem vc_113 {Q : Post} {b : Addr} (hb : g.rbx = b) (w8 : ∀ i < 4, Foot Wl (Addr.add (b + 8#64) i))
    (l3 : ∀ i < 8, Foot F.data (Addr.add g.rsp i)) (l2 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8) i))
    (l1 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8 + 8) i))
    (h : ∀ fl, Q 124 (pops3 (Vz V b) g) fl (Vz V b)) : W_113 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hb
  subst hb
  dsimp only [pops3, Vz] at w8 l3 l2 l1 h ⊢
  wpx [W_113, o8]
  all_goals repeat' (first | exact h _ | assumption | exact trivial | apply And.intro | intro _)

end

/-! ## The function -/

/-- From offset `j` with registers and bytes for which `P` holds, the run goes on to the goal. -/
def AtJ (prof : Profile) (F : Footprint) (Wl : List Rgn) (L : List (Addr × List Byte)) (s₀ : State) (o : Oracle)
    (gev : List Event) (gP : State → Nat → List Event → Prop) (gE : Outcome → List Event → Prop) (j : Nat)
    (P : Gprs → (Addr → Byte) → Prop) : Prop :=
  ∀ (Y : State) (V : Addr → Byte) (t : Nat), KeptW Wl s₀ Y → Agree F Y.proc.mm.mem V →
    Y.cpu.rip = msi_at.add j → P Y.cpu.gpr V → GoG prof L o gev gP gE Y t

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {X : State} {t : Nat} {V : Addr → Byte}

/-- `CMultiStreams::Init (this)` (`rdi`) from its entry, the size `n32` (the 4 bytes at `this + 8`, as read) and the
items `it` (the 8 bytes at `this` whenever `I` holds). The step `k` (from `n - 1` down to 0) starts with `I (k + 1)`
and ends with `I k`: at once when `_items[k]` (`pk`) is 0 (`hP0`); else `J1 k p` after `operator delete (q)` (`hD1`,
at `0x6014f0`), or at once when `q` is 0 (`hQ0`); `J2 k p` after the stream's `Release` (`hDv`, at the address in
its vtable's entry at 16, with its code `hcv`), or at once when the stream is 0 (`hS0`); `I k` after
`operator delete (p, 48)` (`hD2`, at `0x6014e0`). With `I 0` the run reaches the return address with the size set
to 0 and the registers a call keeps (`kr`). -/
theorem msi_ok {n32 : BitVec 32} {it : BitVec 64} {I : Nat → (Addr → Byte) → Prop}
    {J1 J2 : Nat → BitVec 64 → (Addr → Byte) → Prop} {e₂ : Addr} {code₂ : List Byte} {j₂ : Nat}
    (c : Seg prof F Wl L s₀ o) (hin : CodeIn L msi_at msi)
    (hin1 : CodeIn L 0x6014f0#64 Tiny.c6014f0) (hin2 : CodeIn L 0x6014e0#64 Tiny.c6014e0)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = msi_at)
    (w1 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8) i))
    (w2 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8 - 8) i))
    (w3 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8 - 8 - 8) i))
    (w4 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8 - 8 - 8 - 8) i))
    (hl : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsp i))
    (fn : ∀ i < 4, Foot F.data (Addr.add (X.cpu.gpr.rdi + 8#64) i))
    (fa : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rdi i))
    (w8 : ∀ i < 4, Foot Wl (Addr.add (X.cpu.gpr.rdi + 8#64) i))
    (w16 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rdi + 16#64) i))
    (w24 : ∀ i < 4, Foot Wl (Addr.add (X.cpu.gpr.rdi + 24#64) i))
    (fe : ∀ k < n32.toNat, ∀ i < 8, Foot F.data (Addr.add (it + BitVec.ofNat 64 (8 * k)) i))
    (fq : ∀ k < n32.toNat, ∀ W, I (k + 1) W → pk W it k ≠ 0 →
      ∀ i < 8, Foot F.data (Addr.add (pk W it k + 16#64) i))
    (fp : ∀ k < n32.toNat, ∀ p W, p ≠ 0 → J1 k p W → ∀ i < 8, Foot F.data (Addr.add p i))
    (fs : ∀ k < n32.toNat, ∀ p W, p ≠ 0 → J1 k p W → rdq(W, p) ≠ 0 →
      ∀ i < 8, Foot F.data (Addr.add (rdq(W, p)) i))
    (fv : ∀ k < n32.toNat, ∀ p W, p ≠ 0 → J1 k p W → rdq(W, p) ≠ 0 →
      ∀ i < 8, Foot F.data (Addr.add (rdq(W, rdq(W, p)) + 16#64) i))
    (hn : rdd(Vp V X.cpu.gpr, X.cpu.gpr.rdi + 8#64) = n32)
    (hI : I n32.toNat (V0 V X.cpu.gpr)) (hf : Fr X.cpu.gpr (e₂.add j₂) (V0 V X.cpu.gpr))
    (hIt : ∀ k W, I k W → rdq(W, X.cpu.gpr.rdi) = it)
    (hP0 : ∀ k < n32.toNat, ∀ W, I (k + 1) W → pk W it k = 0 → I k W)
    (hQ0 : ∀ k < n32.toNat, ∀ W, I (k + 1) W → pk W it k ≠ 0 → rdq(W, pk W it k + 16#64) = 0 →
      J1 k (pk W it k) W)
    (hD1 : ∀ k < n32.toNat, ∀ W, I (k + 1) W → pk W it k ≠ 0 → rdq(W, pk W it k + 16#64) ≠ 0 →
      Call1 prof F Wl L s₀ o gev gP gE X.cpu.gpr.rsp 0x6014f0#64 (msi_at.add 75)
        (fun g => g.rdi = rdq(W, pk W it k + 16#64)) W (J1 k (pk W it k)))
    (hS0 : ∀ k < n32.toNat, ∀ p W, p ≠ 0 → J1 k p W → rdq(W, p) = 0 → J2 k p W)
    (hcv : ∀ k < n32.toNat, ∀ p W, p ≠ 0 → J1 k p W → rdq(W, p) ≠ 0 →
      ∃ codeF : List Byte, CodeIn L (rdq(W, rdq(W, rdq(W, p)) + 16#64)) codeF ∧ 0 < codeF.length)
    (hDv : ∀ k < n32.toNat, ∀ p W, p ≠ 0 → J1 k p W → rdq(W, p) ≠ 0 →
      Call1 prof F Wl L s₀ o gev gP gE X.cpu.gpr.rsp (rdq(W, rdq(W, rdq(W, p)) + 16#64)) (msi_at.add 90)
        (fun g => g.rdi = rdq(W, p)) W (J2 k p))
    (hD2 : ∀ k < n32.toNat, ∀ p W, p ≠ 0 → J2 k p W →
      Call1 prof F Wl L s₀ o gev gP gE X.cpu.gpr.rsp 0x6014e0#64 (msi_at.add 103)
        (fun g => g.rdi = p ∧ g.rsi = 48#64) W (I k))
    (hF8 : ∀ W, Fr X.cpu.gpr (e₂.add j₂) W → Fr X.cpu.gpr (e₂.add j₂) (Vz W X.cpu.gpr.rdi))
    (hin₂ : CodeIn L e₂ code₂) (h₂ : j₂ < code₂.length)
    (kr : ∀ (Z : State) (W : Addr → Byte) (t' : Nat), KeptW Wl s₀ Z →
      Agree F Z.proc.mm.mem (Vz W X.cpu.gpr.rdi) → I 0 W → Z.cpu.rip = e₂.add j₂ → Bk X.cpu.gpr Z.cpu.gpr →
      GoG prof L o gev gP gE Z t') :
    GoG prof L o gev gP gE X t := by
  have hn32 : n32.toNat < 4294967296 := n32.isLt
  -- the end, from 113
  have F113 : AtJ prof F Wl L s₀ o gev gP gE 113 fun g W => I 0 W ∧ Fr X.cpu.gpr (e₂.add j₂) W ∧
      Rs X.cpu.gpr g := by
    rintro Y W t' hKY hAY hrY ⟨hI0, hfr, ⟨hs, hbx, h13, h14, h15⟩⟩
    have hfr8 := hF8 W hfr
    have l3 : ∀ i < 8, Foot F.data (Addr.add Y.cpu.gpr.rsp i) := by
      rw [hs]; exact fun i hi => c.hws _ (w3 i hi)
    have l2 : ∀ i < 8, Foot F.data (Addr.add (Y.cpu.gpr.rsp + 8) i) := by
      rw [hs, a3s]; exact fun i hi => c.hws _ (w2 i hi)
    have l1 : ∀ i < 8, Foot F.data (Addr.add (Y.cpu.gpr.rsp + 8 + 8) i) := by
      rw [hs, a3s, a2s]; exact fun i hi => c.hws _ (w1 i hi)
    have hsP : (pops3 (Vz W X.cpu.gpr.rdi) Y.cpu.gpr).rsp = X.cpu.gpr.rsp := by
      show Y.cpu.gpr.rsp + 8 + 8 + 8 = _
      rw [hs, a3s, a2s, a1s]
    have hkP : Kp X.cpu.gpr (pops3 (Vz W X.cpu.gpr.rdi) Y.cpu.gpr) := by
      refine ⟨?_, ?_, ?_, h13, h14, h15⟩
      · show rdq(Vz W X.cpu.gpr.rdi, Y.cpu.gpr.rsp) = _
        rw [hs]; exact hfr8.2.2.1
      · show rdq(Vz W X.cpu.gpr.rdi, Y.cpu.gpr.rsp + 8) = _
        rw [hs, a3s]; exact hfr8.2.1
      · show rdq(Vz W X.cpu.gpr.rdi, Y.cpu.gpr.rsp + 8 + 8) = _
        rw [hs, a3s, a2s]; exact hfr8.1
    refine (c_113 prof).run c hin (fun j' g' _ V₁ => j' = 124 ∧ g' = pops3 (Vz W X.cpu.gpr.rdi) Y.cpu.gpr ∧
        V₁ = Vz W X.cpu.gpr.rdi) hKY hAY hrY (vc_113 hbx w8 l3 l2 l1 fun _ => ⟨rfl, rfl, rfl⟩) ?_
    rintro j' g fl V₁ ⟨rfl, rfl, hV₁⟩ U t₁ hKU hAU hrU hgU -
    subst V₁
    have hsU : U.cpu.gpr.rsp = X.cpu.gpr.rsp := (congrArg Gprs.rsp hgU).trans hsP
    refine c.s_ret hKU hAU hin (lt_len (by decide)) hrU (ret_124 _) (by rw [hsU]; exact hl) hin₂ h₂
      (by rw [hsU]; exact hfr8.2.2.2) ?_
    rintro Z t₂ hKZ hAZ ⟨hrZ, hgZ⟩
    refine kr Z W t₂ hKZ hAZ hI0 hrZ ⟨?_, ?_⟩
    · rw [hgZ]
      show U.cpu.gpr.rsp + 8 = _
      rw [hsU]
    · rw [hgZ, hgU]
      exact hkP
  -- 103: `rbp` -= 8, to 113 after the step 0, else to 48
  have S103 : ∀ k, k < n32.toNat →
      (∀ k', k = k' + 1 → AtJ prof F Wl L s₀ o gev gP gE 48 fun g W => I (k' + 1) W ∧
        Fr X.cpu.gpr (e₂.add j₂) W ∧ Rs X.cpu.gpr g ∧ g.rbp = BitVec.ofNat 64 (8 * k')) →
      AtJ prof F Wl L s₀ o gev gP gE 103 fun g W => I k W ∧ Fr X.cpu.gpr (e₂.add j₂) W ∧ Rs X.cpu.gpr g ∧
        g.rbp = BitVec.ofNat 64 (8 * k) := by
    rintro k hk hnx Y W t' hKY hAY hrY ⟨hIk, hfr, hR, hb⟩
    cases k with
    | zero =>
      refine (c_103 prof).run c hin _ hKY hAY hrY (vc_103l (by rw [hb]; exact rb_last)) ?_
      rintro j' g fl V₁ ⟨rfl, rfl, hV₁⟩ U t₁ hKU hAU hrU hgU -
      subst V₁
      exact F113 U W t₁ hKU hAU hrU ⟨hIk, hfr, by rw [hgU]; exact hR⟩
    | succ k =>
      refine (c_103 prof).run c hin _ hKY hAY hrY
        (vc_103c (by rw [hb, rb_step k (by omega)]; exact rb_ne k (by omega))) ?_
      rintro j' g fl V₁ ⟨rfl, rfl, hV₁⟩ U t₁ hKU hAU hrU hgU -
      subst V₁
      have hbU : U.cpu.gpr.rbp = BitVec.ofNat 64 (8 * k) := by
        rw [hgU]
        show Y.cpu.gpr.rbp - 8#64 = _
        rw [hb]
        exact rb_step k (by omega)
      exact hnx k rfl U W t₁ hKU hAU hrU ⟨hIk, hfr, by rw [hgU]; exact hR, hbU⟩
  -- 90: `operator delete (p, 48)`, to 103
  have A90 : ∀ k, k < n32.toNat → ∀ p : BitVec 64, p ≠ 0 →
      AtJ prof F Wl L s₀ o gev gP gE 103 (fun g W => I k W ∧ Fr X.cpu.gpr (e₂.add j₂) W ∧ Rs X.cpu.gpr g ∧
        g.rbp = BitVec.ofNat 64 (8 * k)) →
      AtJ prof F Wl L s₀ o gev gP gE 90 fun g W => J2 k p W ∧ Fr X.cpu.gpr (e₂.add j₂) W ∧ Rs X.cpu.gpr g ∧
        g.r12 = p ∧ g.rbp = BitVec.ofNat 64 (8 * k) := by
    rintro k hk p hp h103 Y W t' hKY hAY hrY ⟨hJ, hfr, hR, h12, hb⟩
    refine (c_90 prof).run c hin _ hKY hAY hrY vc_90 ?_
    rintro j' g fl V₁ ⟨rfl, rfl, hV₁⟩ U t₁ hKU hAU hrU hgU -
    subst V₁
    have hRU : Rs X.cpu.gpr U.cpu.gpr := by rw [hgU]; exact hR
    have hbU : U.cpu.gpr.rbp = BitVec.ofNat 64 (8 * k) := (congrArg Gprs.rbp hgU).trans hb
    have hsU : U.cpu.gpr.rsp = X.cpu.gpr.rsp - 8 - 8 - 8 := hRU.1
    refine c.s_call hKU hAU hin (lt_len (by decide)) hrU (call_98 _) hin2 (by decide) tgt_98
      (by rw [hsU]; exact w4) ?_
    rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
    rw [hsU] at hA₂
    have hsY₂ : Y₂.cpu.gpr.rsp = X.cpu.gpr.rsp - 8 - 8 - 8 - 8 :=
      (congrArg Gprs.rsp hg₂).trans (congrArg (fun x : Addr => x - 8) hsU)
    have hdi₂ : Y₂.cpu.gpr.rdi = p ∧ Y₂.cpu.gpr.rsi = 48#64 :=
      ⟨(congrArg Gprs.rdi hg₂).trans ((congrArg Gprs.rdi hgU).trans h12),
        (congrArg Gprs.rsi hg₂).trans (congrArg Gprs.rsi hgU)⟩
    refine hD2 k hk p W hp hJ Y₂ t₂ hK₂ hA₂ hr₂ hsY₂ hdi₂ ?_
    rintro Z V'' t'' hKZ hAZ hIk hrZ ⟨b1, b2, b3, b4, b5, b6, b7⟩ hkf
    refine h103 Z V'' t'' hKZ hAZ hrZ ⟨hIk, hfr.kf hkf, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    · rw [b1, hsY₂, a1s]
    · exact b2.trans ((congrArg Gprs.rbx hg₂).trans hRU.2.1)
    · exact b5.trans ((congrArg Gprs.r13 hg₂).trans hRU.2.2.1)
    · exact b6.trans ((congrArg Gprs.r14 hg₂).trans hRU.2.2.2.1)
    · exact b7.trans ((congrArg Gprs.r15 hg₂).trans hRU.2.2.2.2)
    · exact b3.trans ((congrArg Gprs.rbp hg₂).trans hbU)
  -- 75: the stream's `Release` when it is set, to 90
  have A75 : ∀ k, k < n32.toNat → ∀ p : BitVec 64, p ≠ 0 →
      AtJ prof F Wl L s₀ o gev gP gE 90 (fun g W => J2 k p W ∧ Fr X.cpu.gpr (e₂.add j₂) W ∧ Rs X.cpu.gpr g ∧
        g.r12 = p ∧ g.rbp = BitVec.ofNat 64 (8 * k)) →
      AtJ prof F Wl L s₀ o gev gP gE 75 fun g W => J1 k p W ∧ Fr X.cpu.gpr (e₂.add j₂) W ∧ Rs X.cpu.gpr g ∧
        g.r12 = p ∧ g.rbp = BitVec.ofNat 64 (8 * k) := by
    rintro k hk p hp h90 Y W t' hKY hAY hrY ⟨hJ, hfr, hR, h12, hb⟩
    have fpY : ∀ i < 8, Foot F.data (Addr.add Y.cpu.gpr.r12 i) := by rw [h12]; exact fp k hk p W hp hJ
    by_cases hs0 : rdq(W, p) = 0
    · refine (c_75 prof).run c hin _ hKY hAY hrY (vc_75z (s := rdq(W, p)) (by rw [h12]) fpY hs0) ?_
      rintro j' g fl V₁ ⟨rfl, rfl, hV₁⟩ U t₁ hKU hAU hrU hgU -
      subst V₁
      exact h90 U W t₁ hKU hAU hrU ⟨hS0 k hk p W hp hJ hs0, hfr, by rw [hgU]; exact hR,
        (congrArg Gprs.r12 hgU).trans h12, (congrArg Gprs.rbp hgU).trans hb⟩
    · refine (c_75 prof).run c hin _ hKY hAY hrY
        (vc_75n (s := rdq(W, p)) (vt := rdq(W, rdq(W, p))) (by rw [h12]) fpY hs0 rfl
          (fs k hk p W hp hJ hs0)) ?_
      rintro j' g fl V₁ ⟨rfl, rfl, hV₁⟩ U t₁ hKU hAU hrU hgU -
      subst V₁
      have hRU : Rs X.cpu.gpr U.cpu.gpr := by rw [hgU]; exact hR
      have hsU : U.cpu.gpr.rsp = X.cpu.gpr.rsp - 8 - 8 - 8 := hRU.1
      have h12U : U.cpu.gpr.r12 = p := (congrArg Gprs.r12 hgU).trans h12
      have hbU : U.cpu.gpr.rbp = BitVec.ofNat 64 (8 * k) := (congrArg Gprs.rbp hgU).trans hb
      have he : eaD U 0 16 = rdq(W, rdq(W, p)) + 16#64 := by
        show U.cpu.gpr.get (regOf 0) + BitVec.ofNat 64 16 = _
        rw [hgU]
        rfl
      obtain ⟨codeF, hinF, hF0⟩ := hcv k hk p W hp hJ hs0
      refine c.s_callM hKU hAU hin (lt_len (by decide)) hrU (call_87 _) (by rw [he]; exact fv k hk p W hp hJ hs0)
        hinF hF0 (by rw [he]) (by rw [hsU]; exact w4) ?_
      rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
      rw [hsU] at hA₂
      have hsY₂ : Y₂.cpu.gpr.rsp = X.cpu.gpr.rsp - 8 - 8 - 8 - 8 :=
        (congrArg Gprs.rsp hg₂).trans (congrArg (fun x : Addr => x - 8) hsU)
      have hdi₂ : Y₂.cpu.gpr.rdi = rdq(W, p) := (congrArg Gprs.rdi hg₂).trans (congrArg Gprs.rdi hgU)
      refine hDv k hk p W hp hJ hs0 Y₂ t₂ hK₂ hA₂ hr₂ hsY₂ hdi₂ ?_
      rintro Z V'' t'' hKZ hAZ hJ2 hrZ ⟨b1, b2, b3, b4, b5, b6, b7⟩ hkf
      refine h90 Z V'' t'' hKZ hAZ hrZ ⟨hJ2, hfr.kf hkf, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
      · rw [b1, hsY₂, a1s]
      · exact b2.trans ((congrArg Gprs.rbx hg₂).trans hRU.2.1)
      · exact b5.trans ((congrArg Gprs.r13 hg₂).trans hRU.2.2.1)
      · exact b6.trans ((congrArg Gprs.r14 hg₂).trans hRU.2.2.2.1)
      · exact b7.trans ((congrArg Gprs.r15 hg₂).trans hRU.2.2.2.2)
      · exact b4.trans ((congrArg Gprs.r12 hg₂).trans h12U)
      · exact b3.trans ((congrArg Gprs.rbp hg₂).trans hbU)
  -- 48: the step `k`, to 103
  have B48 : ∀ k, k < n32.toNat →
      AtJ prof F Wl L s₀ o gev gP gE 103 (fun g W => I k W ∧ Fr X.cpu.gpr (e₂.add j₂) W ∧ Rs X.cpu.gpr g ∧
        g.rbp = BitVec.ofNat 64 (8 * k)) →
      AtJ prof F Wl L s₀ o gev gP gE 48 fun g W => I (k + 1) W ∧ Fr X.cpu.gpr (e₂.add j₂) W ∧ Rs X.cpu.gpr g ∧
        g.rbp = BitVec.ofNat 64 (8 * k) := by
    rintro k hk h103 Y W t' hKY hAY hrY ⟨hIk, hfr, hR, hb⟩
    have hit : rdq(W, Y.cpu.gpr.rbx) = it := by rw [hR.2.1]; exact hIt _ W hIk
    have faY : ∀ i < 8, Foot F.data (Addr.add Y.cpu.gpr.rbx i) := by rw [hR.2.1]; exact fa
    have hea : it + Y.cpu.gpr.rbp = it + BitVec.ofNat 64 (8 * k) := by rw [hb]
    by_cases hp0 : pk W it k = 0
    · refine (c_48 prof).run c hin _ hKY hAY hrY
        (vc_48z (p := pk W it k) hit faY (by rw [hea]) (by rw [hea]; exact fe k hk) hp0) ?_
      rintro j' g fl V₁ ⟨rfl, rfl, hV₁⟩ U t₁ hKU hAU hrU hgU -
      subst V₁
      exact h103 U W t₁ hKU hAU hrU ⟨hP0 k hk W hIk hp0, hfr, by rw [hgU]; exact hR,
        (congrArg Gprs.rbp hgU).trans hb⟩
    · have hq := fq k hk W hIk hp0
      by_cases hq0 : rdq(W, pk W it k + 16#64) = 0
      · refine (c_48 prof).run c hin _ hKY hAY hrY
          (vc_48a (p := pk W it k) (q := rdq(W, pk W it k + 16#64)) hit faY (by rw [hea])
            (by rw [hea]; exact fe k hk) hp0 rfl hq hq0) ?_
        rintro j' g fl V₁ ⟨rfl, rfl, hV₁⟩ U t₁ hKU hAU hrU hgU -
        subst V₁
        exact A75 k hk _ hp0 (A90 k hk _ hp0 h103) U W t₁ hKU hAU hrU
          ⟨hQ0 k hk W hIk hp0 hq0, hfr, by rw [hgU]; exact hR, congrArg Gprs.r12 hgU,
            (congrArg Gprs.rbp hgU).trans hb⟩
      · refine (c_48 prof).run c hin _ hKY hAY hrY
          (vc_48b (p := pk W it k) (q := rdq(W, pk W it k + 16#64)) hit faY (by rw [hea])
            (by rw [hea]; exact fe k hk) hp0 rfl hq hq0) ?_
        rintro j' g fl V₁ ⟨rfl, rfl, hV₁⟩ U t₁ hKU hAU hrU hgU -
        subst V₁
        have hRU : Rs X.cpu.gpr U.cpu.gpr := by rw [hgU]; exact hR
        have hsU : U.cpu.gpr.rsp = X.cpu.gpr.rsp - 8 - 8 - 8 := hRU.1
        have hpU : U.cpu.gpr.r12 = pk W it k := congrArg Gprs.r12 hgU
        have hbU : U.cpu.gpr.rbp = BitVec.ofNat 64 (8 * k) := (congrArg Gprs.rbp hgU).trans hb
        -- `operator delete (q)`
        refine c.s_call hKU hAU hin (lt_len (by decide)) hrU (call_70 _) hin1 (by decide) tgt_70
          (by rw [hsU]; exact w4) ?_
        rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
        rw [hsU] at hA₂
        have hsY₂ : Y₂.cpu.gpr.rsp = X.cpu.gpr.rsp - 8 - 8 - 8 - 8 :=
          (congrArg Gprs.rsp hg₂).trans (congrArg (fun x : Addr => x - 8) hsU)
        have hdi₂ : Y₂.cpu.gpr.rdi = rdq(W, pk W it k + 16#64) :=
          (congrArg Gprs.rdi hg₂).trans (congrArg Gprs.rdi hgU)
        refine hD1 k hk W hIk hp0 hq0 Y₂ t₂ hK₂ hA₂ hr₂ hsY₂ hdi₂ ?_
        rintro Z V'' t'' hKZ hAZ hJ hrZ ⟨b1, b2, b3, b4, b5, b6, b7⟩ hkf
        refine A75 k hk _ hp0 (A90 k hk _ hp0 h103) Z V'' t'' hKZ hAZ hrZ
          ⟨hJ, hfr.kf hkf, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
        · rw [b1, hsY₂, a1s]
        · exact b2.trans ((congrArg Gprs.rbx hg₂).trans hRU.2.1)
        · exact b5.trans ((congrArg Gprs.r13 hg₂).trans hRU.2.2.1)
        · exact b6.trans ((congrArg Gprs.r14 hg₂).trans hRU.2.2.2.1)
        · exact b7.trans ((congrArg Gprs.r15 hg₂).trans hRU.2.2.2.2)
        · exact b4.trans ((congrArg Gprs.r12 hg₂).trans hpU)
        · exact b3.trans ((congrArg Gprs.rbp hg₂).trans hbU)
  -- the loop, by induction on the step
  have L48 : ∀ k, k < n32.toNat → AtJ prof F Wl L s₀ o gev gP gE 48 fun g W => I (k + 1) W ∧
      Fr X.cpu.gpr (e₂.add j₂) W ∧ Rs X.cpu.gpr g ∧ g.rbp = BitVec.ofNat 64 (8 * k) := by
    intro k
    induction k with
    | zero => exact fun hk => B48 0 hk (S103 0 hk fun k' e => absurd e (by omega))
    | succ k ih =>
      exact fun hk => B48 (k + 1) hk (S103 (k + 1) hk fun k' e => by
        obtain rfl : k = k' := by omega
        exact ih (by omega))
  -- the entry
  have hrip' : X.cpu.rip = msi_at.add 0 := by rw [addr_add_zero]; exact hrip
  by_cases hn0 : n32 = 0
  · refine (c_0 prof).run c hin _ hK hA hrip' (vc_0z hn hn0 fn w1 w2 w3 w16 w24) ?_
    rintro j' g fl V₁ ⟨hV₁, hR, rfl⟩ Y t₁ hKY hAY hrY hgY -
    subst V₁
    subst hgY
    have e0 : n32.toNat = 0 := (congrArg BitVec.toNat hn0).trans rfl
    exact F113 Y _ t₁ hKY hAY hrY ⟨e0 ▸ hI, hf, hR⟩
  · refine (c_0 prof).run c hin _ hK hA hrip' (vc_0n hn hn0 fn w1 w2 w3 w16 w24) ?_
    rintro j' g fl V₁ ⟨hV₁, hR, rfl, hb⟩ Y t₁ hKY hAY hrY hgY -
    subst V₁
    subst hgY
    have hnz : n32.toNat ≠ 0 := fun e => hn0 (BitVec.eq_of_toNat_eq (e.trans rfl))
    have e1 : n32.toNat - 1 + 1 = n32.toNat := by omega
    exact L48 (n32.toNat - 1) (by omega) Y _ t₁ hKY hAY hrY
      ⟨by rw [e1]; exact hI, hf, hR, by rw [hb, rbx0_eq hn0]⟩

end FV7z.Msi
