import FV7z.Pst.Cuts
import FV7z.Api.Holds
import FV7z.Tun.Inv
/-!
# `PrintString (adj, width, s)` (0x5ebf50): from the entry to the return or the tail jump (PLAN.md §M, M1)

7-Zip 26.06's `PrintString (EAdjustment adj, unsigned width, const char *s)` (`CPP/7zip/UI/Console/List.cpp`;
`objdump -d`) at `0x5ebf50` in `7zzs`: `adj` = `edi` (`r12d`), `width` = `esi` (`ebx`), `s` = `rdx` (`rbp`). Four
pushes (`r13`, `r12`, `rbp`, `rbx`) and 8 bytes of frame (`aR S`), no stack guard. The `call` (24) of `strlen (s)` at
`0x401108`; then, by `adj` and the length, the number of spaces before (`PrintSpaces` at `0x5ebdd0`, its `call` at
133) and after; the `call` (63) of `fputs (s, g_StdOut._stream)` at `0x624cc0` (`mov rax, 0x79ed70`, `rsi` = the
`FILE *` there); then the epilogue and either the `ret` (87) or, with spaces after, the tail jump (109) to
`PrintSpaces`. The callees' code is a hypothesis (`Ev.kL`, `Ev.kF`, `Ev.kP`: the runs from their entries to their
returns). The landing pad after the tail jump (156) is not on these runs.

- `call_24`, `call_63`, `call_133`, `tgt_*`, `ret_87`, `jmp_109`: the instructions outside the blocks.
- `aR`, `V0`, `q1`..`q5`, `Fm`, `Stk`, `KC`, `Ev`: the frame, the bytes after the pushes, the pops' addresses, the
  frame's registers at the cut points (`rsp` = `aR S`, `rbp` = `s`, `r14`, `r15` as at the entry), the stack, the
  callee as a continuation, the hypotheses of the runs.
- `vc_0`, `vc_29`, `vc_50`, `vc_68`, `vc_128`, `vc_138`: the pieces.
- `pst_ok`: from the entry (`S` = the entry's `rsp`, `g0` = its registers, `I` of the bytes after the pushes, `V0`)
  to the return (`Ev.kr`: `rsp` 8 up, the callee-saved registers as at the entry), to `PrintSpaces`' entry by the
  tail jump (`Ev.kj`: `rsp` = `S`, the callee-saved registers as at the entry), or a callee's goal.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
open FV7z.Api (KS)
namespace FV7z.Pst
set_option linter.unusedVariables false

/-! ## The instructions outside the blocks -/

/-- `strlen`'s entry (its PLT slot). -/
abbrev strlen_ent : Addr := 0x401108

/-- `PrintSpaces`' entry (`FV7z.Psp.psp_at`). -/
abbrev psp_ent : Addr := 0x5ebdd0

/-- The `call` of `strlen` (24). -/
def pc24 : List Byte := [0xe8, 0x9b, 0x51, 0xe1, 0xff]
theorem pc24_0 : ∀ feat, Dec feat pc24 0 (FV7z.mk .call 64 [.rel 18446744073707540891] 5) := by dec_rfl
theorem wc_24 : pc24 <+: pst.drop 24 := by decide +kernel
theorem call_24 (feat : Features) : Dec feat pst 24 (FV7z.mk .call 64 [.rel 18446744073707540891] 5) :=
  Dec.shift (j := 24) (k := 0) (pc24_0 feat) wc_24 (Nat.zero_le _)
theorem tgt_24 : pst_at.add (24 + 5) + BitVec.ofNat 64 18446744073707540891 = strlen_ent := by decide

/-- The `call` of `fputs` (63). -/
def pc63 : List Byte := [0xe8, 0x2c, 0x8d, 0x03, 0x00]
theorem pc63_0 : ∀ feat, Dec feat pc63 0 (FV7z.mk .call 64 [.rel 232748] 5) := by dec_rfl
theorem wc_63 : pc63 <+: pst.drop 63 := by decide +kernel
theorem call_63 (feat : Features) : Dec feat pst 63 (FV7z.mk .call 64 [.rel 232748] 5) :=
  Dec.shift (j := 63) (k := 0) (pc63_0 feat) wc_63 (Nat.zero_le _)
theorem tgt_63 : pst_at.add (63 + 5) + BitVec.ofNat 64 232748 = 0x624cc0#64 := by decide

/-- The `call` of `PrintSpaces` (133). -/
def pc133 : List Byte := [0xe8, 0xf6, 0xfd, 0xff, 0xff]
theorem pc133_0 : ∀ feat, Dec feat pc133 0 (FV7z.mk .call 64 [.rel 18446744073709551094] 5) := by dec_rfl
theorem wc_133 : pc133 <+: pst.drop 133 := by decide +kernel
theorem call_133 (feat : Features) : Dec feat pst 133 (FV7z.mk .call 64 [.rel 18446744073709551094] 5) :=
  Dec.shift (j := 133) (k := 0) (pc133_0 feat) wc_133 (Nat.zero_le _)
theorem tgt_133 : pst_at.add (133 + 5) + BitVec.ofNat 64 18446744073709551094 = psp_ent := by decide

/-- The tail jump to `PrintSpaces` (109). -/
def pjm : List Byte := [0xe9, 0x0e, 0xfe, 0xff, 0xff]
theorem pjm_0 : ∀ feat, Dec feat pjm 0 (FV7z.mk .jmp 64 [.rel 18446744073709551118] 5) := by dec_rfl
theorem wj_109 : pjm <+: pst.drop 109 := by decide +kernel
theorem jmp_109 (feat : Features) : Dec feat pst 109 (FV7z.mk .jmp 64 [.rel 18446744073709551118] 5) :=
  Dec.shift (j := 109) (k := 0) (pjm_0 feat) wj_109 (Nat.zero_le _)

/-- The `ret` (87). -/
def pret : List Byte := [0xc3]
theorem pret_0 : ∀ feat, Dec feat pret 0 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem w_87 : pret <+: pst.drop 87 := by decide +kernel
theorem ret_87 (feat : Features) : Dec feat pst 87 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 87) (k := 0) (pret_0 feat) w_87 (Nat.zero_le _)

/-! ## The frame -/

/-- The stack pointer after the four pushes and `sub rsp, 8`. -/
abbrev aR (S : Addr) : Addr := S - 8 - 8 - 8 - 8 - 8#64

/-- The bytes after the four pushes (`r13`, `r12`, `rbp`, `rbx`). -/
abbrev V0 (V : Addr → Byte) (g : Gprs) : Addr → Byte :=
  Vst (Vst (Vst (Vst V (g.rsp - 8) (toBytesLE g.r13 8)) (g.rsp - 8 - 8) (toBytesLE g.r12 8))
    (g.rsp - 8 - 8 - 8) (toBytesLE g.rbp 8)) (g.rsp - 8 - 8 - 8 - 8) (toBytesLE g.rbx 8)

theorem q1 (S : Addr) : aR S + 8#64 = S - 8 - 8 - 8 - 8 := BitVec.sub_add_cancel _ _
theorem q2 (S : Addr) : aR S + 8#64 + 8 = S - 8 - 8 - 8 := by rw [q1, BitVec.sub_add_cancel]
theorem q3 (S : Addr) : aR S + 8#64 + 8 + 8 = S - 8 - 8 := by rw [q2, BitVec.sub_add_cancel]
theorem q4 (S : Addr) : aR S + 8#64 + 8 + 8 + 8 = S - 8 := by rw [q3, BitVec.sub_add_cancel]
theorem q5 (S : Addr) : aR S + 8#64 + 8 + 8 + 8 + 8 = S := by rw [q4, BitVec.sub_add_cancel]

/-- The frame at the cut points: `rsp` = `aR S`, `rbp` = `s`, `r14`, `r15` as at the entry (`rbx`, `r12`, `r13`
hold the width, `adj` and the spaces after; their entry values are on the stack, `Stk`). -/
abbrev Fm (S : Addr) (g0 g : Gprs) : Prop :=
  g.rsp = aR S ∧ g.rbp = g0.rdx ∧ g.r14 = g0.r14 ∧ g.r15 = g0.r15

/-- Through a piece that keeps `rsp`, `rbp`, `r14`, `r15`. -/
theorem fm_of {S : Addr} {g0 g g' : Gprs} (h : Fm S g0 g) (a : g'.rsp = g.rsp) (b : g'.rbp = g.rbp)
    (c : g'.r14 = g.r14) (d : g'.r15 = g.r15) : Fm S g0 g' :=
  ⟨a.trans h.1, b.trans h.2.1, c.trans h.2.2.1, d.trans h.2.2.2⟩

/-- Back from a callee: `rsp` as before the `call`, the callee-saved registers kept. -/
theorem fm_ret {S : Addr} {g0 g g' : Gprs} (h : Fm S g0 g) (hs : g'.rsp = aR S) (hk : KS g g') : Fm S g0 g' :=
  ⟨hs, hk.2.1.trans h.2.1, hk.2.2.2.2.1.trans h.2.2.1, hk.2.2.2.2.2.trans h.2.2.2⟩

/-- The stack: the four saved registers. -/
abbrev Stk (W : Addr → Byte) (S : Addr) (g0 : Gprs) : Prop :=
  rdq(W, S - 8) = g0.r13 ∧ rdq(W, S - 8 - 8) = g0.r12 ∧ rdq(W, S - 8 - 8 - 8) = g0.rbp ∧
    rdq(W, S - 8 - 8 - 8 - 8) = g0.rbx

/-- The callee from the `call` before `j` (entry `ent`, the bytes `W`, the registers `A`): at its entry, and from its
return at `j` with `rsp` = `aR S`, the callee-saved registers as at its entry, `B` and the invariant `J`, the run
goes on to the goal. -/
def KC (prof : Profile) (F : Footprint) (Wl : List Rgn) (L : List (Addr × List Byte)) (s₀ : State) (o : Oracle)
    (gev : List Event) (gP : State → Nat → List Event → Prop) (gE : Outcome → List Event → Prop)
    (S : Addr) (J : (Addr → Byte) → Prop) (ent : Addr) (j : Nat) (W : Addr → Byte) (A B : Gprs → Prop) : Prop :=
  ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y →
    Agree F Y.proc.mm.mem (Vst W (aR S - 8) (toBytesLE (pst_at.add j) 8)) →
    Y.cpu.rip = ent → Y.cpu.gpr.rsp = aR S - 8 → A Y.cpu.gpr →
    (∀ (Z : State) (W' : Addr → Byte) (t'' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem W' →
      Z.cpu.rip = pst_at.add j → Z.cpu.gpr.rsp = aR S → KS Y.cpu.gpr Z.cpu.gpr → B Z.cpu.gpr → J W' →
      GoG prof L o gev gP gE Z t'') →
    GoG prof L o gev gP gE Y t'

/-! ## The hypotheses of the runs -/

/-- The hypotheses of the runs (`S`, `g0` the entry's stack pointer and registers, `e₂.add j₂` the return address,
`I` the invariant of the bytes): the saved registers and the return address under `I`, their slots readable, the
`call`s' slot, the `FILE *` at `0x79ed70` readable; the callees (`kL`: `strlen` with `rdi` = `s`; `kF`: `fputs`
with `rdi` = `s`, `rsi` = the `FILE *`; `kP`: `PrintSpaces`), keeping `I`; the return (`kr`) and the tail jump
(`kj`) as the goals. -/
structure Ev (prof : Profile) (F : Footprint) (Wl : List Rgn) (L : List (Addr × List Byte)) (s₀ : State)
    (o : Oracle) (gev : List Event) (gP : State → Nat → List Event → Prop) (gE : Outcome → List Event → Prop)
    (S : Addr) (g0 : Gprs) (e₂ : Addr) (code₂ : List Byte) (j₂ : Nat) (I : (Addr → Byte) → Prop) : Prop where
  c : Seg prof F Wl L s₀ o
  hin : CodeIn L pst_at pst
  hin₂ : CodeIn L e₂ code₂
  h₂ : j₂ < code₂.length
  hI : ∀ W, I W → Stk W S g0
  hR : ∀ W, I W → rdq(W, S) = e₂.add j₂
  hl : ∀ i < 8, Foot F.data (Addr.add S i)
  fb1 : ∀ i < 8, Foot F.data (Addr.add (S - 8) i)
  fb2 : ∀ i < 8, Foot F.data (Addr.add (S - 8 - 8) i)
  fb3 : ∀ i < 8, Foot F.data (Addr.add (S - 8 - 8 - 8) i)
  fb4 : ∀ i < 8, Foot F.data (Addr.add (S - 8 - 8 - 8 - 8) i)
  hr8 : ∀ i < 8, Foot Wl (Addr.add (aR S - 8) i)
  fso : ∀ i < 8, Foot F.data (Addr.add (0x79ed70#64) i)
  cL : ∃ code : List Byte, CodeIn L strlen_ent code ∧ 0 < code.length
  cF : ∃ code : List Byte, CodeIn L 0x624cc0#64 code ∧ 0 < code.length
  cP : ∃ code : List Byte, CodeIn L psp_ent code ∧ 0 < code.length
  kL : ∀ j W, I W → KC prof F Wl L s₀ o gev gP gE S I strlen_ent j W (fun g => g.rdi = g0.rdx) (fun _ => True)
  kF : ∀ j W, I W → KC prof F Wl L s₀ o gev gP gE S I 0x624cc0#64 j W
    (fun g => g.rdi = g0.rdx ∧ g.rsi = rdq(W, 0x79ed70#64)) (fun _ => True)
  kP : ∀ j W, I W → KC prof F Wl L s₀ o gev gP gE S I psp_ent j W (fun _ => True) (fun _ => True)
  kr : ∀ (W : Addr → Byte) (Z' : State) (t' : Nat), KeptW Wl s₀ Z' → Agree F Z'.proc.mm.mem W →
    Z'.cpu.rip = e₂.add j₂ → Z'.cpu.gpr.rsp = S + 8 → KS g0 Z'.cpu.gpr → I W → GoG prof L o gev gP gE Z' t'
  kj : ∀ (W : Addr → Byte) (Y : State) (t' : Nat), KeptW Wl s₀ Y → Agree F Y.proc.mm.mem W →
    Y.cpu.rip = psp_ent → Y.cpu.gpr.rsp = S → KS g0 Y.cpu.gpr → I W → GoG prof L o gev gP gE Y t'

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

/-- The four pushes, `r13d` = 0, `r12d` = `adj`, `rdi` = `rbp` = `s`, `ebx` = `width`, `sub rsp, 8`, to the `call`
of `strlen` at 24. -/
theorem vc_0 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (hs1 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8) i)) (hs2 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8) i))
    (hs3 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8 - 8) i))
    (hs4 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8 - 8 - 8) i))
    (h : ∀ g', g'.rsp = aR g.rsp → g'.rbp = g.rdx → g'.rdi = g.rdx → g'.r14 = g.r14 → g'.r15 = g.r15 →
      ∀ fl, Q 24 g' fl (V0 V g)) :
    W_0 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [aR, V0] at hs1 hs2 hs3 hs4 h ⊢
  wpx [W_0, o0]
  all_goals repeat' (first
    | refine h _ ?_ ?_ ?_ ?_ ?_ _
    | with_reducible exact hs1
    | with_reducible exact hs2
    | with_reducible exact hs3
    | with_reducible exact hs4
    | ostep)

/-- Back from `strlen`: the length against `width`, `adj`, the spaces before and after: to 50 (no spaces before) or
to 128 (the test of the spaces before). -/
theorem vc_29 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (h50 : ∀ g', g'.rsp = g.rsp → g'.rbp = g.rbp → g'.r14 = g.r14 → g'.r15 = g.r15 → ∀ fl, Q 50 g' fl V)
    (h128 : ∀ g', g'.rsp = g.rsp → g'.rbp = g.rbp → g'.r14 = g.r14 → g'.r15 = g.r15 → ∀ fl, Q 128 g' fl V) :
    W_29 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h50 h128 ⊢
  wpx [W_29, W_33, W_44, W_120, W_144, o1, o2, o3, o8, o10]
  all_goals repeat' (first
    | refine h50 _ ?_ ?_ ?_ ?_ _
    | refine h128 _ ?_ ?_ ?_ ?_ _
    | ostep)

/-- `rax` = `0x79ed70`, `rdi` = `s`, `rsi` = the `FILE *` at `rax`, to the `call` of `fputs` at 63. -/
theorem vc_50 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (hso : ∀ i < 8, Foot F.data (Addr.add (0x79ed70#64) i))
    (h : ∀ g', g'.rsp = g.rsp → g'.rbp = g.rbp → g'.r14 = g.r14 → g'.r15 = g.r15 → g'.rdi = g.rbp →
      g'.rsi = rdq(V, 0x79ed70#64) → ∀ fl, Q 63 g' fl V) :
    W_50 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h ⊢
  wpx [W_50, o4]
  all_goals repeat' (first
    | refine h _ ?_ ?_ ?_ ?_ ?_ ?_ _
    | exact hso
    | ostep)

/-- Back from `fputs`: the test of the spaces after; `add rsp, 8`, (`edi` = the spaces after,) the four pops, to the
`ret` at 87 or the tail jump at 109. -/
theorem vc_68 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (f1 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8#64) i))
    (f2 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8#64 + 8) i))
    (f3 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8#64 + 8 + 8) i))
    (f4 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8#64 + 8 + 8 + 8) i))
    (h87 : ∀ g', g'.rsp = g.rsp + 8#64 + 8 + 8 + 8 + 8 → g'.rbx = rdq(V, g.rsp + 8#64) →
      g'.rbp = rdq(V, g.rsp + 8#64 + 8) → g'.r12 = rdq(V, g.rsp + 8#64 + 8 + 8) →
      g'.r13 = rdq(V, g.rsp + 8#64 + 8 + 8 + 8) → g'.r14 = g.r14 → g'.r15 = g.r15 → ∀ fl, Q 87 g' fl V)
    (h109 : ∀ g', g'.rsp = g.rsp + 8#64 + 8 + 8 + 8 + 8 → g'.rbx = rdq(V, g.rsp + 8#64) →
      g'.rbp = rdq(V, g.rsp + 8#64 + 8) → g'.r12 = rdq(V, g.rsp + 8#64 + 8 + 8) →
      g'.r13 = rdq(V, g.rsp + 8#64 + 8 + 8 + 8) → g'.r14 = g.r14 → g'.r15 = g.r15 → ∀ fl, Q 109 g' fl V) :
    W_68 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at f1 f2 f3 f4 h87 h109 ⊢
  wpx [W_68, W_77, W_96, o5, o6, o7]
  all_goals repeat' (first
    | refine h87 _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ _
    | refine h109 _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ _
    | with_reducible exact f1
    | with_reducible exact f2
    | with_reducible exact f3
    | with_reducible exact f4
    | ostep)

/-- The test of the spaces before: to 50, or to the `call` of `PrintSpaces` at 133. -/
theorem vc_128 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (h50 : ∀ g', g'.rsp = g.rsp → g'.rbp = g.rbp → g'.r14 = g.r14 → g'.r15 = g.r15 → ∀ fl, Q 50 g' fl V)
    (h133 : ∀ g', g'.rsp = g.rsp → g'.rbp = g.rbp → g'.r14 = g.r14 → g'.r15 = g.r15 → ∀ fl, Q 133 g' fl V) :
    W_128 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h50 h133 ⊢
  wpx [W_128, o9]
  all_goals repeat' (first
    | refine h50 _ ?_ ?_ ?_ ?_ _
    | refine h133 _ ?_ ?_ ?_ ?_ _
    | ostep)

/-- Back from `PrintSpaces`: the jump to 50. -/
theorem vc_138 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} (h : ∀ fl, Q 50 g fl V) :
    W_138 F Wl Q g f V :=
  h _

end Pieces

/-! ## The runs -/

section Runs
variable {prof : Profile} {F : Footprint} {Wl : List Rgn} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {S : Addr} {g0 : Gprs} {e₂ : Addr} {code₂ : List Byte} {j₂ : Nat} {I : (Addr → Byte) → Prop}
  {X Y : State} {t : Nat} {V W : Addr → Byte}

/-- From 68 (back from `fputs`): the epilogue, to the `ret` (`kr`) or the tail jump (`kj`). -/
theorem from68 (E : Ev prof F Wl L s₀ o gev gP gE S g0 e₂ code₂ j₂ I) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = pst_at.add 68) (hm : Fm S g0 Y.cpu.gpr) (hIW : I W) :
    GoG prof L o gev gP gE Y t := by
  obtain ⟨s1, s2, s3, s4⟩ := E.hI W hIW
  have s0 := E.hR W hIW
  have ms := hm.1
  have e1 : rdq(W, Y.cpu.gpr.rsp + 8#64) = g0.rbx := by rw [ms, q1]; exact s4
  have e2 : rdq(W, Y.cpu.gpr.rsp + 8#64 + 8) = g0.rbp := by rw [ms, q2]; exact s3
  have e3 : rdq(W, Y.cpu.gpr.rsp + 8#64 + 8 + 8) = g0.r12 := by rw [ms, q3]; exact s2
  have e4 : rdq(W, Y.cpu.gpr.rsp + 8#64 + 8 + 8 + 8) = g0.r13 := by rw [ms, q4]; exact s1
  refine (c_68 prof).run E.c E.hin (fun j' g' _ V' => (j' = 87 ∨ j' = 109) ∧ V' = W ∧
      g'.rsp = Y.cpu.gpr.rsp + 8#64 + 8 + 8 + 8 + 8 ∧ g'.rbx = rdq(W, Y.cpu.gpr.rsp + 8#64) ∧
      g'.rbp = rdq(W, Y.cpu.gpr.rsp + 8#64 + 8) ∧ g'.r12 = rdq(W, Y.cpu.gpr.rsp + 8#64 + 8 + 8) ∧
      g'.r13 = rdq(W, Y.cpu.gpr.rsp + 8#64 + 8 + 8 + 8) ∧ g'.r14 = Y.cpu.gpr.r14 ∧ g'.r15 = Y.cpu.gpr.r15)
    hK hA hr
    (vc_68 (by rw [ms, q1]; exact E.fb4) (by rw [ms, q2]; exact E.fb3) (by rw [ms, q3]; exact E.fb2)
      (by rw [ms, q4]; exact E.fb1) (fun _ a b c d e m n _ => ⟨Or.inl rfl, rfl, a, b, c, d, e, m, n⟩)
      fun _ a b c d e m n _ => ⟨Or.inr rfl, rfl, a, b, c, d, e, m, n⟩) ?_
  rintro j' g fl V₁ ⟨hj, hV₁, gs, gb, gp, g12, g13, g14, g15⟩ U t₁ hKU hAU hrU hgU -
  subst V₁ hgU
  have hsU : U.cpu.gpr.rsp = S := by rw [gs, ms]; exact q5 S
  have hk : KS g0 U.cpu.gpr :=
    ⟨gb.trans e1, gp.trans e2, g12.trans e3, g13.trans e4, g14.trans hm.2.2.1, g15.trans hm.2.2.2⟩
  rcases hj with rfl | rfl
  · refine E.c.s_ret hKU hAU E.hin (lt_len (by decide)) hrU (ret_87 _) (by rw [hsU]; exact E.hl) E.hin₂ E.h₂
      (by rw [hsU]; exact s0) ?_
    rintro Z' t₂ hKZ' hAZ' ⟨hrZ', hgZ'⟩
    refine E.kr W Z' t₂ hKZ' hAZ' hrZ' ?_ ?_ hIW
    · rw [hgZ']
      show U.cpu.gpr.rsp + 8 = _
      rw [hsU]
    · rw [hgZ']
      exact hk
  · obtain ⟨cT, hinT, hT⟩ := E.cP
    refine E.c.s_jmp_x hKU hAU E.hin (lt_len (by decide)) hrU (jmp_109 _) hinT hT (by decide) ?_
    rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
    refine E.kj W Y₂ t₂ hK₂ hA₂ (by rw [hr₂, addr_add_zero]) (by rw [hg₂]; exact hsU) ?_ hIW
    rw [hg₂]
    exact hk

/-- From 50: the arguments of `fputs`, its `call` at 63, then from 68. -/
theorem from50 (E : Ev prof F Wl L s₀ o gev gP gE S g0 e₂ code₂ j₂ I) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = pst_at.add 50) (hm : Fm S g0 Y.cpu.gpr) (hIW : I W) :
    GoG prof L o gev gP gE Y t := by
  refine (c_50 prof).run E.c E.hin (fun j' g' _ V' => j' = 63 ∧ V' = W ∧ Fm S g0 g' ∧ g'.rdi = g0.rdx ∧
      g'.rsi = rdq(W, 0x79ed70#64)) hK hA hr
    (vc_50 E.fso fun _ a b c d e s _ => ⟨rfl, rfl, fm_of hm a b c d, e.trans hm.2.1, s⟩) ?_
  rintro j' g fl V₁ ⟨rfl, hV₁, hmU, hdi, hsi⟩ U t₁ hKU hAU hrU hgU -
  subst V₁ hgU
  obtain ⟨cc, hinc, hcc⟩ := E.cF
  have hU : U.cpu.gpr.rsp - 8 = aR S - 8 := by rw [hmU.1]
  refine E.c.s_call hKU hAU E.hin (lt_len (by decide)) hrU (call_63 _) hinc hcc tgt_63 (by rw [hU]; exact E.hr8) ?_
  rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
  rw [hU] at hA₂
  refine E.kF _ _ hIW Y₂ t₂ hK₂ hA₂ hr₂ (by rw [hg₂]; exact hU) (by rw [hg₂]; exact ⟨hdi, hsi⟩) ?_
  intro Z W' t₃ hKZ hAZ hrZ hsZ hkZ _ hIZ
  rw [hg₂] at hkZ
  exact from68 E hKZ hAZ hrZ (fm_ret hmU hsZ hkZ) hIZ

/-- From 138 (back from `PrintSpaces`): the jump, to 50. -/
theorem from138 (E : Ev prof F Wl L s₀ o gev gP gE S g0 e₂ code₂ j₂ I) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = pst_at.add 138) (hm : Fm S g0 Y.cpu.gpr) (hIW : I W) :
    GoG prof L o gev gP gE Y t := by
  refine (c_138 prof).run E.c E.hin (fun j' g' _ V' => j' = 50 ∧ V' = W ∧ g' = Y.cpu.gpr) hK hA hr
    (vc_138 fun _ => ⟨rfl, rfl, rfl⟩) ?_
  rintro j' g fl V₁ ⟨rfl, hV₁, hg⟩ U t₁ hKU hAU hrU hgU -
  subst V₁ hgU
  exact from50 E hKU hAU hrU (by rw [hg]; exact hm) hIW

/-- From 128: to 50, or the `call` of `PrintSpaces` at 133, then from 138. -/
theorem from128 (E : Ev prof F Wl L s₀ o gev gP gE S g0 e₂ code₂ j₂ I) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = pst_at.add 128) (hm : Fm S g0 Y.cpu.gpr) (hIW : I W) :
    GoG prof L o gev gP gE Y t := by
  refine (c_128 prof).run E.c E.hin (fun j' g' _ V' => (j' = 50 ∨ j' = 133) ∧ V' = W ∧ Fm S g0 g') hK hA hr
    (vc_128 (fun _ a b c d _ => ⟨Or.inl rfl, rfl, fm_of hm a b c d⟩)
      fun _ a b c d _ => ⟨Or.inr rfl, rfl, fm_of hm a b c d⟩) ?_
  rintro j' g fl V₁ ⟨hj, hV₁, hmU⟩ U t₁ hKU hAU hrU hgU -
  subst V₁ hgU
  rcases hj with rfl | rfl
  · exact from50 E hKU hAU hrU hmU hIW
  · obtain ⟨cc, hinc, hcc⟩ := E.cP
    have hU : U.cpu.gpr.rsp - 8 = aR S - 8 := by rw [hmU.1]
    refine E.c.s_call hKU hAU E.hin (lt_len (by decide)) hrU (call_133 _) hinc hcc tgt_133
      (by rw [hU]; exact E.hr8) ?_
    rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
    rw [hU] at hA₂
    refine E.kP _ _ hIW Y₂ t₂ hK₂ hA₂ hr₂ (by rw [hg₂]; exact hU) trivial ?_
    intro Z W' t₃ hKZ hAZ hrZ hsZ hkZ _ hIZ
    rw [hg₂] at hkZ
    exact from138 E hKZ hAZ hrZ (fm_ret hmU hsZ hkZ) hIZ

/-- From 29 (back from `strlen`): to 50 or 128. -/
theorem from29 (E : Ev prof F Wl L s₀ o gev gP gE S g0 e₂ code₂ j₂ I) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = pst_at.add 29) (hm : Fm S g0 Y.cpu.gpr) (hIW : I W) :
    GoG prof L o gev gP gE Y t := by
  refine (c_29 prof).run E.c E.hin (fun j' g' _ V' => (j' = 50 ∨ j' = 128) ∧ V' = W ∧ Fm S g0 g') hK hA hr
    (vc_29 (fun _ a b c d _ => ⟨Or.inl rfl, rfl, fm_of hm a b c d⟩)
      fun _ a b c d _ => ⟨Or.inr rfl, rfl, fm_of hm a b c d⟩) ?_
  rintro j' g fl V₁ ⟨hj, hV₁, hmU⟩ U t₁ hKU hAU hrU hgU -
  subst V₁ hgU
  rcases hj with rfl | rfl
  · exact from50 E hKU hAU hrU hmU hIW
  · exact from128 E hKU hAU hrU hmU hIW

/-- `PrintString (adj, width, s)` from its entry (`X`'s registers, `S` = their `rsp`; the pushes' slots in what the
run may store into, `I` of the bytes after the pushes). -/
theorem pst_ok (E : Ev prof F Wl L s₀ o gev gP gE X.cpu.gpr.rsp X.cpu.gpr e₂ code₂ j₂ I)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = pst_at)
    (hs1 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8) i))
    (hs2 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8 - 8) i))
    (hs3 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8 - 8 - 8) i))
    (hs4 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8 - 8 - 8 - 8) i)) (hI0 : I (V0 V X.cpu.gpr)) :
    GoG prof L o gev gP gE X t := by
  refine (c_0 prof).run E.c E.hin (fun j' g' _ V' => j' = 24 ∧ V' = V0 V X.cpu.gpr ∧
      Fm X.cpu.gpr.rsp X.cpu.gpr g' ∧ g'.rdi = X.cpu.gpr.rdx) hK hA (by rw [addr_add_zero]; exact hrip)
    (vc_0 hs1 hs2 hs3 hs4 fun _ a b d c e _ => ⟨rfl, rfl, ⟨a, b, c, e⟩, d⟩) ?_
  rintro j' g fl V₁ ⟨rfl, hV₁, hmY, hdi⟩ Y t₁ hKY hAY hrY hgY -
  subst V₁ hgY
  obtain ⟨cc, hinc, hcc⟩ := E.cL
  have hU : Y.cpu.gpr.rsp - 8 = aR X.cpu.gpr.rsp - 8 := by rw [hmY.1]
  refine E.c.s_call hKY hAY E.hin (lt_len (by decide)) hrY (call_24 _) hinc hcc tgt_24 (by rw [hU]; exact E.hr8) ?_
  rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
  rw [hU] at hA₂
  refine E.kL _ _ hI0 Y₂ t₂ hK₂ hA₂ hr₂ (by rw [hg₂]; exact hU) (by rw [hg₂]; exact hdi) ?_
  intro Z W' t₃ hKZ hAZ hrZ hsZ hkZ _ hIZ
  rw [hg₂] at hkZ
  exact from29 E hKZ hAZ hrZ (fm_ret hmY hsZ hkZ) hIZ

end Runs

end FV7z.Pst
