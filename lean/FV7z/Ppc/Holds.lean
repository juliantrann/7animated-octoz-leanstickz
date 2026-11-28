import FV7z.Ppc.Cuts
import FV7z.Api.Holds
import FV7z.Tun.Inv
/-!
# `CPercentPrinter::CPercentPrinter (unsigned)` (0x5f4f80): from the entry to the return (PLAN.md §M, M1)

7-Zip 26.06's `CPercentPrinter::CPercentPrinter (unsigned tickStep)` (`CPP/7zip/UI/Console/PercentPrinter.h`;
`objdump -d`) at `0x5f4f80` in `7zzs`: `this` = `rdi` (`rbp`), `tickStep` = `esi` (`ebx`). Three pushes (`r12`, `rbp`,
`rbx`, `aR S`), no stack guard. The stores of the fields (`this + 0`, `8`, `16`: 0, -1, 0 at the entry; `this + 64`
.. `80` and `this + 144` .. `168` later) and the `call`s of the members' constructors, `AString::AString ()` at
`0x44c360` (`this + 24`, `80`, `96`, `112`, `168`, `200`) and `UString::UString ()` at `0x44d3e0` (`this + 40`, `128`,
`184`), their code a hypothesis (`Ev.kA`, `Ev.kU`: the runs from their entries with `rdi` = the member to their
returns); then the pops and the `ret` (193). The landing pads after the `ret` (194..) are not on these runs.

- `call_*`, `tgt_*`, `ret_193`: the instructions outside the blocks.
- `aR`, `V0`, `M0`, `q1`..`q3`, `Fm`, `fm_ks`, `Stk`, `KC`, `Ev`: the frame, the bytes after the pushes and the
  entry's stores, the pops' addresses, the frame's registers (`rsp` = `aR S`, `rbp` = `this`, `r12`..`r15` as at the
  entry), the stack, the callee as a continuation, the hypotheses of the runs.
- `vc_*`: the pieces.
- `ppc_ok`: from the entry (`S` = the entry's `rsp`, `g0` = its registers, `I` of the bytes after the pushes and the
  entry's stores, `M0`; `I` kept by the later stores into `this + 64` .. `this + 168`, `Ev.iS`) to the return
  (`Ev.kr`: `rsp` 8 up, the callee-saved registers as at the entry) or a callee's goal.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
open FV7z.Api (KS)
namespace FV7z.Ppc
set_option linter.unusedVariables false

/-! ## The instructions outside the blocks -/

/-- `AString::AString ()`'s entry. -/
abbrev astr_ent : Addr := 0x44c360

/-- `UString::UString ()`'s entry. -/
abbrev ustr_ent : Addr := 0x44d3e0

/-- The `call` of `AString::AString ()` (41). -/
def pc41 : List Byte := [0xe8, 0xb2, 0x73, 0xe5, 0xff]
theorem pc41_0 : ∀ feat, Dec feat pc41 0 (FV7z.mk .call 64 [.rel 18446744073707811762] 5) := by dec_rfl
theorem wc_41 : pc41 <+: ppc.drop 41 := by decide +kernel
theorem call_41 (feat : Features) : Dec feat ppc 41 (FV7z.mk .call 64 [.rel 18446744073707811762] 5) :=
  Dec.shift (j := 41) (k := 0) (pc41_0 feat) wc_41 (Nat.zero_le _)
theorem tgt_41 : ppc_at.add (41 + 5) + BitVec.ofNat 64 18446744073707811762 = astr_ent := by decide

/-- The `call` of `UString::UString ()` (50). -/
def pc50 : List Byte := [0xe8, 0x29, 0x84, 0xe5, 0xff]
theorem pc50_0 : ∀ feat, Dec feat pc50 0 (FV7z.mk .call 64 [.rel 18446744073707815977] 5) := by dec_rfl
theorem wc_50 : pc50 <+: ppc.drop 50 := by decide +kernel
theorem call_50 (feat : Features) : Dec feat ppc 50 (FV7z.mk .call 64 [.rel 18446744073707815977] 5) :=
  Dec.shift (j := 50) (k := 0) (pc50_0 feat) wc_50 (Nat.zero_le _)
theorem tgt_50 : ppc_at.add (50 + 5) + BitVec.ofNat 64 18446744073707815977 = ustr_ent := by decide

/-- The `call` of `AString::AString ()` (85). -/
def pc85 : List Byte := [0xe8, 0x86, 0x73, 0xe5, 0xff]
theorem pc85_0 : ∀ feat, Dec feat pc85 0 (FV7z.mk .call 64 [.rel 18446744073707811718] 5) := by dec_rfl
theorem wc_85 : pc85 <+: ppc.drop 85 := by decide +kernel
theorem call_85 (feat : Features) : Dec feat ppc 85 (FV7z.mk .call 64 [.rel 18446744073707811718] 5) :=
  Dec.shift (j := 85) (k := 0) (pc85_0 feat) wc_85 (Nat.zero_le _)
theorem tgt_85 : ppc_at.add (85 + 5) + BitVec.ofNat 64 18446744073707811718 = astr_ent := by decide

/-- The `call` of `AString::AString ()` (94). -/
def pc94 : List Byte := [0xe8, 0x7d, 0x73, 0xe5, 0xff]
theorem pc94_0 : ∀ feat, Dec feat pc94 0 (FV7z.mk .call 64 [.rel 18446744073707811709] 5) := by dec_rfl
theorem wc_94 : pc94 <+: ppc.drop 94 := by decide +kernel
theorem call_94 (feat : Features) : Dec feat ppc 94 (FV7z.mk .call 64 [.rel 18446744073707811709] 5) :=
  Dec.shift (j := 94) (k := 0) (pc94_0 feat) wc_94 (Nat.zero_le _)
theorem tgt_94 : ppc_at.add (94 + 5) + BitVec.ofNat 64 18446744073707811709 = astr_ent := by decide

/-- The `call` of `AString::AString ()` (103). -/
def pc103 : List Byte := [0xe8, 0x74, 0x73, 0xe5, 0xff]
theorem pc103_0 : ∀ feat, Dec feat pc103 0 (FV7z.mk .call 64 [.rel 18446744073707811700] 5) := by dec_rfl
theorem wc_103 : pc103 <+: ppc.drop 103 := by decide +kernel
theorem call_103 (feat : Features) : Dec feat ppc 103 (FV7z.mk .call 64 [.rel 18446744073707811700] 5) :=
  Dec.shift (j := 103) (k := 0) (pc103_0 feat) wc_103 (Nat.zero_le _)
theorem tgt_103 : ppc_at.add (103 + 5) + BitVec.ofNat 64 18446744073707811700 = astr_ent := by decide

/-- The `call` of `UString::UString ()` (115). -/
def pc115 : List Byte := [0xe8, 0xe8, 0x83, 0xe5, 0xff]
theorem pc115_0 : ∀ feat, Dec feat pc115 0 (FV7z.mk .call 64 [.rel 18446744073707815912] 5) := by dec_rfl
theorem wc_115 : pc115 <+: ppc.drop 115 := by decide +kernel
theorem call_115 (feat : Features) : Dec feat ppc 115 (FV7z.mk .call 64 [.rel 18446744073707815912] 5) :=
  Dec.shift (j := 115) (k := 0) (pc115_0 feat) wc_115 (Nat.zero_le _)
theorem tgt_115 : ppc_at.add (115 + 5) + BitVec.ofNat 64 18446744073707815912 = ustr_ent := by decide

/-- The `call` of `AString::AString ()` (160). -/
def pc160 : List Byte := [0xe8, 0x3b, 0x73, 0xe5, 0xff]
theorem pc160_0 : ∀ feat, Dec feat pc160 0 (FV7z.mk .call 64 [.rel 18446744073707811643] 5) := by dec_rfl
theorem wc_160 : pc160 <+: ppc.drop 160 := by decide +kernel
theorem call_160 (feat : Features) : Dec feat ppc 160 (FV7z.mk .call 64 [.rel 18446744073707811643] 5) :=
  Dec.shift (j := 160) (k := 0) (pc160_0 feat) wc_160 (Nat.zero_le _)
theorem tgt_160 : ppc_at.add (160 + 5) + BitVec.ofNat 64 18446744073707811643 = astr_ent := by decide

/-- The `call` of `UString::UString ()` (172). -/
def pc172 : List Byte := [0xe8, 0xaf, 0x83, 0xe5, 0xff]
theorem pc172_0 : ∀ feat, Dec feat pc172 0 (FV7z.mk .call 64 [.rel 18446744073707815855] 5) := by dec_rfl
theorem wc_172 : pc172 <+: ppc.drop 172 := by decide +kernel
theorem call_172 (feat : Features) : Dec feat ppc 172 (FV7z.mk .call 64 [.rel 18446744073707815855] 5) :=
  Dec.shift (j := 172) (k := 0) (pc172_0 feat) wc_172 (Nat.zero_le _)
theorem tgt_172 : ppc_at.add (172 + 5) + BitVec.ofNat 64 18446744073707815855 = ustr_ent := by decide

/-- The `call` of `AString::AString ()` (184). -/
def pc184 : List Byte := [0xe8, 0x23, 0x73, 0xe5, 0xff]
theorem pc184_0 : ∀ feat, Dec feat pc184 0 (FV7z.mk .call 64 [.rel 18446744073707811619] 5) := by dec_rfl
theorem wc_184 : pc184 <+: ppc.drop 184 := by decide +kernel
theorem call_184 (feat : Features) : Dec feat ppc 184 (FV7z.mk .call 64 [.rel 18446744073707811619] 5) :=
  Dec.shift (j := 184) (k := 0) (pc184_0 feat) wc_184 (Nat.zero_le _)
theorem tgt_184 : ppc_at.add (184 + 5) + BitVec.ofNat 64 18446744073707811619 = astr_ent := by decide

/-- The `ret` (193). -/
def pret : List Byte := [0xc3]
theorem pret_0 : ∀ feat, Dec feat pret 0 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem w_193 : pret <+: ppc.drop 193 := by decide +kernel
theorem ret_193 (feat : Features) : Dec feat ppc 193 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 193) (k := 0) (pret_0 feat) w_193 (Nat.zero_le _)

/-! ## The frame -/

/-- The stack pointer after the three pushes. -/
abbrev aR (S : Addr) : Addr := S - 8 - 8 - 8

/-- The bytes after the three pushes (`r12`, `rbp`, `rbx`). -/
abbrev V0 (V : Addr → Byte) (g : Gprs) : Addr → Byte :=
  Vst (Vst (Vst V (g.rsp - 8) (toBytesLE g.r12 8)) (g.rsp - 8 - 8) (toBytesLE g.rbp 8)) (g.rsp - 8 - 8 - 8)
    (toBytesLE g.rbx 8)

/-- The bytes after the pushes and the entry's stores (`this + 0`, `8`, `16`: 0, -1, 0). -/
abbrev M0 (V : Addr → Byte) (g : Gprs) : Addr → Byte :=
  Vst (Vst (Vst (V0 V g) g.rdi (toBytesLE (0#64) 8)) (g.rdi + 8#64) (toBytesLE (18446744073709551615#64) 8))
    (g.rdi + 16#64) (toBytesLE (0#64) 8)

theorem q1 (S : Addr) : aR S + 8 = S - 8 - 8 := BitVec.sub_add_cancel _ _
theorem q2 (S : Addr) : aR S + 8 + 8 = S - 8 := by rw [q1, BitVec.sub_add_cancel]
theorem q3 (S : Addr) : aR S + 8 + 8 + 8 = S := by rw [q2, BitVec.sub_add_cancel]

/-- The frame from the prologue on: `rsp` = `aR S`, `rbp` = `this`, `r12`..`r15` as at the entry. -/
abbrev Fm (S : Addr) (g0 g : Gprs) : Prop :=
  g.rsp = aR S ∧ g.rbp = g0.rdi ∧ g.r12 = g0.r12 ∧ g.r13 = g0.r13 ∧ g.r14 = g0.r14 ∧ g.r15 = g0.r15

/-- Through a piece or a callee: `rsp` = `aR S`, the callee-saved registers kept. -/
theorem fm_ks {S : Addr} {g0 g g' : Gprs} (h : Fm S g0 g) (hs : g'.rsp = aR S) (hk : KS g g') : Fm S g0 g' :=
  ⟨hs, hk.2.1.trans h.2.1, hk.2.2.1.trans h.2.2.1, hk.2.2.2.1.trans h.2.2.2.1, hk.2.2.2.2.1.trans h.2.2.2.2.1,
    hk.2.2.2.2.2.trans h.2.2.2.2.2⟩

/-- The stack: the three saved registers. -/
abbrev Stk (W : Addr → Byte) (S : Addr) (g0 : Gprs) : Prop :=
  rdq(W, S - 8) = g0.r12 ∧ rdq(W, S - 8 - 8) = g0.rbp ∧ rdq(W, S - 8 - 8 - 8) = g0.rbx

/-- The callee from the `call` before `j` (entry `ent`, the bytes `W`, the registers `A`): at its entry, and from its
return at `j` with `rsp` = `aR S`, the callee-saved registers as at its entry, `B` and the invariant `J`, the run
goes on to the goal. -/
def KC (prof : Profile) (F : Footprint) (Wl : List Rgn) (L : List (Addr × List Byte)) (s₀ : State) (o : Oracle)
    (gev : List Event) (gP : State → Nat → List Event → Prop) (gE : Outcome → List Event → Prop)
    (S : Addr) (J : (Addr → Byte) → Prop) (ent : Addr) (j : Nat) (W : Addr → Byte) (A B : Gprs → Prop) : Prop :=
  ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y →
    Agree F Y.proc.mm.mem (Vst W (aR S - 8) (toBytesLE (ppc_at.add j) 8)) →
    Y.cpu.rip = ent → Y.cpu.gpr.rsp = aR S - 8 → A Y.cpu.gpr →
    (∀ (Z : State) (W' : Addr → Byte) (t'' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem W' →
      Z.cpu.rip = ppc_at.add j → Z.cpu.gpr.rsp = aR S → KS Y.cpu.gpr Z.cpu.gpr → B Z.cpu.gpr → J W' →
      GoG prof L o gev gP gE Z t'') →
    GoG prof L o gev gP gE Y t'

/-! ## The hypotheses of the runs -/

/-- The hypotheses of the runs (`S`, `g0` the entry's stack pointer and registers, `e₂.add j₂` the return address,
`I` the invariant of the bytes): the saved registers and the return address under `I`, their slots readable, the
`call`s' slot; `this + 64` .. `this + 168` in what the run may store into (`sw`) and `I` kept by stores there
(`iS`); the callees (`kA`, `kU`: with `rdi` = `this + d`), keeping `I`; the return (`kr`) as the goal. -/
structure Ev (prof : Profile) (F : Footprint) (Wl : List Rgn) (L : List (Addr × List Byte)) (s₀ : State)
    (o : Oracle) (gev : List Event) (gP : State → Nat → List Event → Prop) (gE : Outcome → List Event → Prop)
    (S : Addr) (g0 : Gprs) (e₂ : Addr) (code₂ : List Byte) (j₂ : Nat) (I : (Addr → Byte) → Prop) : Prop where
  c : Seg prof F Wl L s₀ o
  hin : CodeIn L ppc_at ppc
  hin₂ : CodeIn L e₂ code₂
  h₂ : j₂ < code₂.length
  hI : ∀ W, I W → Stk W S g0
  hR : ∀ W, I W → rdq(W, S) = e₂.add j₂
  hl : ∀ i < 8, Foot F.data (Addr.add S i)
  fb1 : ∀ i < 8, Foot F.data (Addr.add (S - 8) i)
  fb2 : ∀ i < 8, Foot F.data (Addr.add (S - 8 - 8) i)
  fb3 : ∀ i < 8, Foot F.data (Addr.add (S - 8 - 8 - 8) i)
  hr8 : ∀ i < 8, Foot Wl (Addr.add (aR S - 8) i)
  sw : ∀ k i, 64 ≤ k → k + i < 168 → Foot Wl (Addr.add (g0.rdi + BitVec.ofNat 64 k) i)
  iS : ∀ (W : Addr → Byte) (k w n : Nat) (x : BitVec w), I W → 64 ≤ k → k + n ≤ 168 →
    I (Vst W (g0.rdi + BitVec.ofNat 64 k) (toBytesLE x n))
  cA : ∃ code : List Byte, CodeIn L astr_ent code ∧ 0 < code.length
  cU : ∃ code : List Byte, CodeIn L ustr_ent code ∧ 0 < code.length
  kA : ∀ j W (d : Addr), I W → KC prof F Wl L s₀ o gev gP gE S I astr_ent j W (fun g => g.rdi = g0.rdi + d)
    (fun _ => True)
  kU : ∀ j W (d : Addr), I W → KC prof F Wl L s₀ o gev gP gE S I ustr_ent j W (fun g => g.rdi = g0.rdi + d)
    (fun _ => True)
  kr : ∀ (W : Addr → Byte) (Z' : State) (t' : Nat), KeptW Wl s₀ Z' → Agree F Z'.proc.mm.mem W →
    Z'.cpu.rip = e₂.add j₂ → Z'.cpu.gpr.rsp = S + 8 → KS g0 Z'.cpu.gpr → I W → GoG prof L o gev gP gE Z' t'

/-! ## The pieces -/

/-- One step of the closers of the pieces. -/
macro "ostep" : tactic => `(tactic| first
  | with_reducible rfl
  | with_reducible assumption
  | exact rfl
  | apply And.intro
  | intro _)

section Pieces
variable {F : Footprint} {Wl : List Rgn}

/-- `endbr64`, the three pushes, `rbp` = `this`, `rdi` = `this + 24`, `ebx` = `tickStep`, the stores of 0, -1, 0
into `this + 0`, `8`, `16`, to the `call` of `AString::AString ()` at 41. -/
theorem vc_0 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (hs1 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8) i)) (hs2 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8) i))
    (hs3 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8 - 8) i))
    (hw0 : ∀ i < 8, Foot Wl (Addr.add g.rdi i)) (hw8 : ∀ i < 8, Foot Wl (Addr.add (g.rdi + 8#64) i))
    (hw16 : ∀ i < 8, Foot Wl (Addr.add (g.rdi + 16#64) i))
    (h : ∀ g', g'.rsp = aR g.rsp → g'.rbp = g.rdi → g'.rdi = g.rdi + 24#64 → g'.r12 = g.r12 →
      g'.r13 = g.r13 → g'.r14 = g.r14 → g'.r15 = g.r15 → ∀ fl, Q 41 g' fl (M0 V g)) :
    W_0 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [aR, V0, M0] at hs1 hs2 hs3 hw0 hw8 hw16 h ⊢
  wpx [W_0, o0, BitVec.add_assoc, BitVec.reduceAdd]
  all_goals repeat' (first
    | refine h _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ _
    | with_reducible exact hs1
    | with_reducible exact hs2
    | with_reducible exact hs3
    | exact hw0
    | exact hw8
    | exact hw16
    | ostep)

/-- `rdi` = `this + 40`, to the `call` of `UString::UString ()` at 50. -/
theorem vc_46 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (h : ∀ g', g'.rsp = g.rsp → KS g g' → g'.rdi = g.rbp + 40#64 → ∀ fl, Q 50 g' fl V) :
    W_46 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h ⊢
  wpx [W_46, o1]
  all_goals repeat' (first
    | refine h _ ?_ ?_ ?_ _
    | ostep)

/-- The stores into `this` (`this + 64` .. `this + 168`, `P` kept by them), `rdi` = `this + 80`, to the `call` of
`AString::AString ()` at 85. -/
theorem vc_55 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} {P : (Addr → Byte) → Prop}
    (hw : ∀ k i, 64 ≤ k → k + i < 168 → Foot Wl (Addr.add (g.rbp + BitVec.ofNat 64 k) i))
    (hS : ∀ (V' : Addr → Byte) (k w n : Nat) (x : BitVec w), P V' → 64 ≤ k → k + n ≤ 168 →
      P (Vst V' (g.rbp + BitVec.ofNat 64 k) (toBytesLE x n)))
    (hP : P V)
    (h : ∀ g' V', P V' → g'.rsp = g.rsp → KS g g' → g'.rdi = g.rbp + 80#64 → ∀ fl, Q 85 g' fl V') :
    W_55 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hw hS h ⊢
  wpx [W_55, o2]
  all_goals repeat' (first
    | refine h _ _ ?_ ?_ ?_ ?_ _
    | exact hP
    | (apply hS <;> try decide)
    | exact fun i hi => hw _ i (by decide) (by omega)
    | ostep)

/-- `rdi` = `this + 96`, to the `call` of `AString::AString ()` at 94. -/
theorem vc_90 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (h : ∀ g', g'.rsp = g.rsp → KS g g' → g'.rdi = g.rbp + 96#64 → ∀ fl, Q 94 g' fl V) :
    W_90 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h ⊢
  wpx [W_90, o3]
  all_goals repeat' (first
    | refine h _ ?_ ?_ ?_ _
    | ostep)

/-- `rdi` = `this + 112`, to the `call` of `AString::AString ()` at 103. -/
theorem vc_99 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (h : ∀ g', g'.rsp = g.rsp → KS g g' → g'.rdi = g.rbp + 112#64 → ∀ fl, Q 103 g' fl V) :
    W_99 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h ⊢
  wpx [W_99, o4]
  all_goals repeat' (first
    | refine h _ ?_ ?_ ?_ _
    | ostep)

/-- `rdi` = `this + 128`, to the `call` of `UString::UString ()` at 115. -/
theorem vc_108 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (h : ∀ g', g'.rsp = g.rsp → KS g g' → g'.rdi = g.rbp + 128#64 → ∀ fl, Q 115 g' fl V) :
    W_108 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h ⊢
  wpx [W_108, o5]
  all_goals repeat' (first
    | refine h _ ?_ ?_ ?_ _
    | ostep)

/-- The stores into `this` (`this + 64` .. `this + 168`, `P` kept by them), `rdi` = `this + 168`, to the `call` of
`AString::AString ()` at 160. -/
theorem vc_120 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} {P : (Addr → Byte) → Prop}
    (hw : ∀ k i, 64 ≤ k → k + i < 168 → Foot Wl (Addr.add (g.rbp + BitVec.ofNat 64 k) i))
    (hS : ∀ (V' : Addr → Byte) (k w n : Nat) (x : BitVec w), P V' → 64 ≤ k → k + n ≤ 168 →
      P (Vst V' (g.rbp + BitVec.ofNat 64 k) (toBytesLE x n)))
    (hP : P V)
    (h : ∀ g' V', P V' → g'.rsp = g.rsp → KS g g' → g'.rdi = g.rbp + 168#64 → ∀ fl, Q 160 g' fl V') :
    W_120 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hw hS h ⊢
  wpx [W_120, o6]
  all_goals repeat' (first
    | refine h _ _ ?_ ?_ ?_ ?_ _
    | exact hP
    | (apply hS <;> try decide)
    | exact fun i hi => hw _ i (by decide) (by omega)
    | ostep)

/-- `rdi` = `this + 184`, to the `call` of `UString::UString ()` at 172. -/
theorem vc_165 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (h : ∀ g', g'.rsp = g.rsp → KS g g' → g'.rdi = g.rbp + 184#64 → ∀ fl, Q 172 g' fl V) :
    W_165 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h ⊢
  wpx [W_165, o7]
  all_goals repeat' (first
    | refine h _ ?_ ?_ ?_ _
    | ostep)

/-- `rdi` = `this + 200`, to the `call` of `AString::AString ()` at 184. -/
theorem vc_177 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (h : ∀ g', g'.rsp = g.rsp → KS g g' → g'.rdi = g.rbp + 200#64 → ∀ fl, Q 184 g' fl V) :
    W_177 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h ⊢
  wpx [W_177, o8]
  all_goals repeat' (first
    | refine h _ ?_ ?_ ?_ _
    | ostep)

/-- The three pops, to the `ret` at 193. -/
theorem vc_189 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (f1 : ∀ i < 8, Foot F.data (Addr.add g.rsp i)) (f2 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8) i))
    (f3 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8 + 8) i))
    (h : ∀ g', g'.rsp = g.rsp + 8 + 8 + 8 → g'.rbx = rdq(V, g.rsp) → g'.rbp = rdq(V, g.rsp + 8) →
      g'.r12 = rdq(V, g.rsp + 8 + 8) → g'.r13 = g.r13 → g'.r14 = g.r14 → g'.r15 = g.r15 →
      ∀ fl, Q 193 g' fl V) :
    W_189 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at f1 f2 f3 h ⊢
  wpx [W_189, o9]
  all_goals repeat' (first
    | refine h _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ _
    | with_reducible exact f1
    | with_reducible exact f2
    | with_reducible exact f3
    | ostep)

end Pieces

/-! ## The runs -/

section Runs
variable {prof : Profile} {F : Footprint} {Wl : List Rgn} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {S : Addr} {g0 : Gprs} {e₂ : Addr} {code₂ : List Byte} {j₂ : Nat} {I : (Addr → Byte) → Prop}
  {X Y : State} {t : Nat} {V W : Addr → Byte}

/-- From 189: the pops, the `ret`, to `kr`. -/
theorem from189 (E : Ev prof F Wl L s₀ o gev gP gE S g0 e₂ code₂ j₂ I) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = ppc_at.add 189) (hm : Fm S g0 Y.cpu.gpr) (hIW : I W) :
    GoG prof L o gev gP gE Y t := by
  obtain ⟨s1, s2, s3⟩ := E.hI W hIW
  have s0 := E.hR W hIW
  have ms := hm.1
  have e1 : rdq(W, Y.cpu.gpr.rsp) = g0.rbx := by rw [ms]; exact s3
  have e2 : rdq(W, Y.cpu.gpr.rsp + 8) = g0.rbp := by rw [ms, q1]; exact s2
  have e3 : rdq(W, Y.cpu.gpr.rsp + 8 + 8) = g0.r12 := by rw [ms, q2]; exact s1
  refine (c_189 prof).run E.c E.hin (fun j' g' _ V' => j' = 193 ∧ V' = W ∧
      g'.rsp = Y.cpu.gpr.rsp + 8 + 8 + 8 ∧ g'.rbx = rdq(W, Y.cpu.gpr.rsp) ∧ g'.rbp = rdq(W, Y.cpu.gpr.rsp + 8) ∧
      g'.r12 = rdq(W, Y.cpu.gpr.rsp + 8 + 8) ∧ g'.r13 = Y.cpu.gpr.r13 ∧ g'.r14 = Y.cpu.gpr.r14 ∧
      g'.r15 = Y.cpu.gpr.r15) hK hA hr
    (vc_189 (by rw [ms]; exact E.fb3) (by rw [ms, q1]; exact E.fb2) (by rw [ms, q2]; exact E.fb1)
      fun _ a b c d e m n _ => ⟨rfl, rfl, a, b, c, d, e, m, n⟩) ?_
  rintro j' g fl V₁ ⟨rfl, hV₁, gs, gb, gp, g12, g13, g14, g15⟩ U t₁ hKU hAU hrU hgU -
  subst V₁ hgU
  have hsU : U.cpu.gpr.rsp = S := by rw [gs, ms]; exact q3 S
  have hk : KS g0 U.cpu.gpr :=
    ⟨gb.trans e1, gp.trans e2, g12.trans e3, g13.trans hm.2.2.2.1, g14.trans hm.2.2.2.2.1, g15.trans hm.2.2.2.2.2⟩
  refine E.c.s_ret hKU hAU E.hin (lt_len (by decide)) hrU (ret_193 _) (by rw [hsU]; exact E.hl) E.hin₂ E.h₂
    (by rw [hsU]; exact s0) ?_
  rintro Z' t₂ hKZ' hAZ' ⟨hrZ', hgZ'⟩
  refine E.kr W Z' t₂ hKZ' hAZ' hrZ' ?_ ?_ hIW
  · rw [hgZ']
    show U.cpu.gpr.rsp + 8 = _
    rw [hsU]
  · rw [hgZ']
    exact hk

/-- From 177: `rdi` = `this + 200`, the `call` of `AString::AString ()` at 184, then from 189. -/
theorem from177 (E : Ev prof F Wl L s₀ o gev gP gE S g0 e₂ code₂ j₂ I) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = ppc_at.add 177) (hm : Fm S g0 Y.cpu.gpr) (hIW : I W) :
    GoG prof L o gev gP gE Y t := by
  have hrb := hm.2.1
  refine (c_177 prof).run E.c E.hin (fun j' g' _ V' => j' = 184 ∧ V' = W ∧ Fm S g0 g' ∧
      g'.rdi = g0.rdi + 200#64) hK hA hr
    (vc_177 fun _ a k p _ => ⟨rfl, rfl, fm_ks hm (a.trans hm.1) k, by rw [p, hrb]⟩) ?_
  rintro j' g fl V₁ ⟨rfl, hV₁, hmU, hdi⟩ U t₁ hKU hAU hrU hgU -
  subst V₁ hgU
  obtain ⟨cc, hinc, hcc⟩ := E.cA
  have hU : U.cpu.gpr.rsp - 8 = aR S - 8 := by rw [hmU.1]
  refine E.c.s_call hKU hAU E.hin (lt_len (by decide)) hrU (call_184 _) hinc hcc tgt_184
    (by rw [hU]; exact E.hr8) ?_
  rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
  rw [hU] at hA₂
  refine E.kA _ _ (200#64) hIW Y₂ t₂ hK₂ hA₂ hr₂ (by rw [hg₂]; exact hU) (by rw [hg₂]; exact hdi) ?_
  intro Z W' t₃ hKZ hAZ hrZ hsZ hkZ _ hIZ
  rw [hg₂] at hkZ
  exact from189 E hKZ hAZ hrZ (fm_ks hmU hsZ hkZ) hIZ

/-- From 165: `rdi` = `this + 184`, the `call` of `UString::UString ()` at 172, then from 177. -/
theorem from165 (E : Ev prof F Wl L s₀ o gev gP gE S g0 e₂ code₂ j₂ I) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = ppc_at.add 165) (hm : Fm S g0 Y.cpu.gpr) (hIW : I W) :
    GoG prof L o gev gP gE Y t := by
  have hrb := hm.2.1
  refine (c_165 prof).run E.c E.hin (fun j' g' _ V' => j' = 172 ∧ V' = W ∧ Fm S g0 g' ∧
      g'.rdi = g0.rdi + 184#64) hK hA hr
    (vc_165 fun _ a k p _ => ⟨rfl, rfl, fm_ks hm (a.trans hm.1) k, by rw [p, hrb]⟩) ?_
  rintro j' g fl V₁ ⟨rfl, hV₁, hmU, hdi⟩ U t₁ hKU hAU hrU hgU -
  subst V₁ hgU
  obtain ⟨cc, hinc, hcc⟩ := E.cU
  have hU : U.cpu.gpr.rsp - 8 = aR S - 8 := by rw [hmU.1]
  refine E.c.s_call hKU hAU E.hin (lt_len (by decide)) hrU (call_172 _) hinc hcc tgt_172
    (by rw [hU]; exact E.hr8) ?_
  rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
  rw [hU] at hA₂
  refine E.kU _ _ (184#64) hIW Y₂ t₂ hK₂ hA₂ hr₂ (by rw [hg₂]; exact hU) (by rw [hg₂]; exact hdi) ?_
  intro Z W' t₃ hKZ hAZ hrZ hsZ hkZ _ hIZ
  rw [hg₂] at hkZ
  exact from177 E hKZ hAZ hrZ (fm_ks hmU hsZ hkZ) hIZ

/-- From 120: the stores, `rdi` = `this + 168`, the `call` of `AString::AString ()` at 160, then from 165. -/
theorem from120 (E : Ev prof F Wl L s₀ o gev gP gE S g0 e₂ code₂ j₂ I) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = ppc_at.add 120) (hm : Fm S g0 Y.cpu.gpr) (hIW : I W) :
    GoG prof L o gev gP gE Y t := by
  have hrb := hm.2.1
  refine (c_120 prof).run E.c E.hin (fun j' g' _ V' => j' = 160 ∧ I V' ∧ Fm S g0 g' ∧
      g'.rdi = g0.rdi + 168#64) hK hA hr
    (vc_120 (P := I) (by rw [hrb]; exact E.sw) (by rw [hrb]; exact E.iS) hIW
      fun _ V' hV a k p _ => ⟨rfl, hV, fm_ks hm (a.trans hm.1) k, by rw [p, hrb]⟩) ?_
  rintro j' g fl V₁ ⟨rfl, hV₁, hmU, hdi⟩ U t₁ hKU hAU hrU hgU -
  subst hgU
  obtain ⟨cc, hinc, hcc⟩ := E.cA
  have hU : U.cpu.gpr.rsp - 8 = aR S - 8 := by rw [hmU.1]
  refine E.c.s_call hKU hAU E.hin (lt_len (by decide)) hrU (call_160 _) hinc hcc tgt_160
    (by rw [hU]; exact E.hr8) ?_
  rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
  rw [hU] at hA₂
  refine E.kA _ _ (168#64) hV₁ Y₂ t₂ hK₂ hA₂ hr₂ (by rw [hg₂]; exact hU) (by rw [hg₂]; exact hdi) ?_
  intro Z W' t₃ hKZ hAZ hrZ hsZ hkZ _ hIZ
  rw [hg₂] at hkZ
  exact from165 E hKZ hAZ hrZ (fm_ks hmU hsZ hkZ) hIZ

/-- From 108: `rdi` = `this + 128`, the `call` of `UString::UString ()` at 115, then from 120. -/
theorem from108 (E : Ev prof F Wl L s₀ o gev gP gE S g0 e₂ code₂ j₂ I) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = ppc_at.add 108) (hm : Fm S g0 Y.cpu.gpr) (hIW : I W) :
    GoG prof L o gev gP gE Y t := by
  have hrb := hm.2.1
  refine (c_108 prof).run E.c E.hin (fun j' g' _ V' => j' = 115 ∧ V' = W ∧ Fm S g0 g' ∧
      g'.rdi = g0.rdi + 128#64) hK hA hr
    (vc_108 fun _ a k p _ => ⟨rfl, rfl, fm_ks hm (a.trans hm.1) k, by rw [p, hrb]⟩) ?_
  rintro j' g fl V₁ ⟨rfl, hV₁, hmU, hdi⟩ U t₁ hKU hAU hrU hgU -
  subst V₁ hgU
  obtain ⟨cc, hinc, hcc⟩ := E.cU
  have hU : U.cpu.gpr.rsp - 8 = aR S - 8 := by rw [hmU.1]
  refine E.c.s_call hKU hAU E.hin (lt_len (by decide)) hrU (call_115 _) hinc hcc tgt_115
    (by rw [hU]; exact E.hr8) ?_
  rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
  rw [hU] at hA₂
  refine E.kU _ _ (128#64) hIW Y₂ t₂ hK₂ hA₂ hr₂ (by rw [hg₂]; exact hU) (by rw [hg₂]; exact hdi) ?_
  intro Z W' t₃ hKZ hAZ hrZ hsZ hkZ _ hIZ
  rw [hg₂] at hkZ
  exact from120 E hKZ hAZ hrZ (fm_ks hmU hsZ hkZ) hIZ

/-- From 99: `rdi` = `this + 112`, the `call` of `AString::AString ()` at 103, then from 108. -/
theorem from99 (E : Ev prof F Wl L s₀ o gev gP gE S g0 e₂ code₂ j₂ I) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = ppc_at.add 99) (hm : Fm S g0 Y.cpu.gpr) (hIW : I W) :
    GoG prof L o gev gP gE Y t := by
  have hrb := hm.2.1
  refine (c_99 prof).run E.c E.hin (fun j' g' _ V' => j' = 103 ∧ V' = W ∧ Fm S g0 g' ∧
      g'.rdi = g0.rdi + 112#64) hK hA hr
    (vc_99 fun _ a k p _ => ⟨rfl, rfl, fm_ks hm (a.trans hm.1) k, by rw [p, hrb]⟩) ?_
  rintro j' g fl V₁ ⟨rfl, hV₁, hmU, hdi⟩ U t₁ hKU hAU hrU hgU -
  subst V₁ hgU
  obtain ⟨cc, hinc, hcc⟩ := E.cA
  have hU : U.cpu.gpr.rsp - 8 = aR S - 8 := by rw [hmU.1]
  refine E.c.s_call hKU hAU E.hin (lt_len (by decide)) hrU (call_103 _) hinc hcc tgt_103
    (by rw [hU]; exact E.hr8) ?_
  rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
  rw [hU] at hA₂
  refine E.kA _ _ (112#64) hIW Y₂ t₂ hK₂ hA₂ hr₂ (by rw [hg₂]; exact hU) (by rw [hg₂]; exact hdi) ?_
  intro Z W' t₃ hKZ hAZ hrZ hsZ hkZ _ hIZ
  rw [hg₂] at hkZ
  exact from108 E hKZ hAZ hrZ (fm_ks hmU hsZ hkZ) hIZ

/-- From 90: `rdi` = `this + 96`, the `call` of `AString::AString ()` at 94, then from 99. -/
theorem from90 (E : Ev prof F Wl L s₀ o gev gP gE S g0 e₂ code₂ j₂ I) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = ppc_at.add 90) (hm : Fm S g0 Y.cpu.gpr) (hIW : I W) :
    GoG prof L o gev gP gE Y t := by
  have hrb := hm.2.1
  refine (c_90 prof).run E.c E.hin (fun j' g' _ V' => j' = 94 ∧ V' = W ∧ Fm S g0 g' ∧
      g'.rdi = g0.rdi + 96#64) hK hA hr
    (vc_90 fun _ a k p _ => ⟨rfl, rfl, fm_ks hm (a.trans hm.1) k, by rw [p, hrb]⟩) ?_
  rintro j' g fl V₁ ⟨rfl, hV₁, hmU, hdi⟩ U t₁ hKU hAU hrU hgU -
  subst V₁ hgU
  obtain ⟨cc, hinc, hcc⟩ := E.cA
  have hU : U.cpu.gpr.rsp - 8 = aR S - 8 := by rw [hmU.1]
  refine E.c.s_call hKU hAU E.hin (lt_len (by decide)) hrU (call_94 _) hinc hcc tgt_94
    (by rw [hU]; exact E.hr8) ?_
  rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
  rw [hU] at hA₂
  refine E.kA _ _ (96#64) hIW Y₂ t₂ hK₂ hA₂ hr₂ (by rw [hg₂]; exact hU) (by rw [hg₂]; exact hdi) ?_
  intro Z W' t₃ hKZ hAZ hrZ hsZ hkZ _ hIZ
  rw [hg₂] at hkZ
  exact from99 E hKZ hAZ hrZ (fm_ks hmU hsZ hkZ) hIZ

/-- From 55: the stores, `rdi` = `this + 80`, the `call` of `AString::AString ()` at 85, then from 90. -/
theorem from55 (E : Ev prof F Wl L s₀ o gev gP gE S g0 e₂ code₂ j₂ I) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = ppc_at.add 55) (hm : Fm S g0 Y.cpu.gpr) (hIW : I W) :
    GoG prof L o gev gP gE Y t := by
  have hrb := hm.2.1
  refine (c_55 prof).run E.c E.hin (fun j' g' _ V' => j' = 85 ∧ I V' ∧ Fm S g0 g' ∧
      g'.rdi = g0.rdi + 80#64) hK hA hr
    (vc_55 (P := I) (by rw [hrb]; exact E.sw) (by rw [hrb]; exact E.iS) hIW
      fun _ V' hV a k p _ => ⟨rfl, hV, fm_ks hm (a.trans hm.1) k, by rw [p, hrb]⟩) ?_
  rintro j' g fl V₁ ⟨rfl, hV₁, hmU, hdi⟩ U t₁ hKU hAU hrU hgU -
  subst hgU
  obtain ⟨cc, hinc, hcc⟩ := E.cA
  have hU : U.cpu.gpr.rsp - 8 = aR S - 8 := by rw [hmU.1]
  refine E.c.s_call hKU hAU E.hin (lt_len (by decide)) hrU (call_85 _) hinc hcc tgt_85
    (by rw [hU]; exact E.hr8) ?_
  rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
  rw [hU] at hA₂
  refine E.kA _ _ (80#64) hV₁ Y₂ t₂ hK₂ hA₂ hr₂ (by rw [hg₂]; exact hU) (by rw [hg₂]; exact hdi) ?_
  intro Z W' t₃ hKZ hAZ hrZ hsZ hkZ _ hIZ
  rw [hg₂] at hkZ
  exact from90 E hKZ hAZ hrZ (fm_ks hmU hsZ hkZ) hIZ

/-- From 46: `rdi` = `this + 40`, the `call` of `UString::UString ()` at 50, then from 55. -/
theorem from46 (E : Ev prof F Wl L s₀ o gev gP gE S g0 e₂ code₂ j₂ I) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = ppc_at.add 46) (hm : Fm S g0 Y.cpu.gpr) (hIW : I W) :
    GoG prof L o gev gP gE Y t := by
  have hrb := hm.2.1
  refine (c_46 prof).run E.c E.hin (fun j' g' _ V' => j' = 50 ∧ V' = W ∧ Fm S g0 g' ∧
      g'.rdi = g0.rdi + 40#64) hK hA hr
    (vc_46 fun _ a k p _ => ⟨rfl, rfl, fm_ks hm (a.trans hm.1) k, by rw [p, hrb]⟩) ?_
  rintro j' g fl V₁ ⟨rfl, hV₁, hmU, hdi⟩ U t₁ hKU hAU hrU hgU -
  subst V₁ hgU
  obtain ⟨cc, hinc, hcc⟩ := E.cU
  have hU : U.cpu.gpr.rsp - 8 = aR S - 8 := by rw [hmU.1]
  refine E.c.s_call hKU hAU E.hin (lt_len (by decide)) hrU (call_50 _) hinc hcc tgt_50
    (by rw [hU]; exact E.hr8) ?_
  rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
  rw [hU] at hA₂
  refine E.kU _ _ (40#64) hIW Y₂ t₂ hK₂ hA₂ hr₂ (by rw [hg₂]; exact hU) (by rw [hg₂]; exact hdi) ?_
  intro Z W' t₃ hKZ hAZ hrZ hsZ hkZ _ hIZ
  rw [hg₂] at hkZ
  exact from55 E hKZ hAZ hrZ (fm_ks hmU hsZ hkZ) hIZ

/-- `CPercentPrinter::CPercentPrinter (this, tickStep)` from its entry (`X`'s registers, `S` = their `rsp`; the
pushes' slots and `this + 0` .. `this + 24` in what the run may store into, `I` of the bytes after the pushes and
the entry's stores). -/
theorem ppc_ok (E : Ev prof F Wl L s₀ o gev gP gE X.cpu.gpr.rsp X.cpu.gpr e₂ code₂ j₂ I)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = ppc_at)
    (hs1 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8) i))
    (hs2 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8 - 8) i))
    (hs3 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8 - 8 - 8) i))
    (hw0 : ∀ i < 8, Foot Wl (Addr.add X.cpu.gpr.rdi i)) (hw8 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rdi + 8#64) i))
    (hw16 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rdi + 16#64) i)) (hI0 : I (M0 V X.cpu.gpr)) :
    GoG prof L o gev gP gE X t := by
  refine (c_0 prof).run E.c E.hin (fun j' g' _ V' => j' = 41 ∧ V' = M0 V X.cpu.gpr ∧
      Fm X.cpu.gpr.rsp X.cpu.gpr g' ∧ g'.rdi = X.cpu.gpr.rdi + 24#64) hK hA (by rw [addr_add_zero]; exact hrip)
    (vc_0 hs1 hs2 hs3 hw0 hw8 hw16 fun _ a b d c e m n _ => ⟨rfl, rfl, ⟨a, b, c, e, m, n⟩, d⟩) ?_
  rintro j' g fl V₁ ⟨rfl, hV₁, hmU, hdi⟩ U t₁ hKU hAU hrU hgU -
  subst V₁ hgU
  obtain ⟨cc, hinc, hcc⟩ := E.cA
  have hU : U.cpu.gpr.rsp - 8 = aR X.cpu.gpr.rsp - 8 := by rw [hmU.1]
  refine E.c.s_call hKU hAU E.hin (lt_len (by decide)) hrU (call_41 _) hinc hcc tgt_41 (by rw [hU]; exact E.hr8) ?_
  rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
  rw [hU] at hA₂
  refine E.kA _ _ (24#64) hI0 Y₂ t₂ hK₂ hA₂ hr₂ (by rw [hg₂]; exact hU) (by rw [hg₂]; exact hdi) ?_
  intro Z W' t₃ hKZ hAZ hrZ hsZ hkZ _ hIZ
  rw [hg₂] at hkZ
  exact from46 E hKZ hAZ hrZ (fm_ks hmU hsZ hkZ) hIZ

end Runs

end FV7z.Ppc
