import FV7z.Ppd.Cuts
import FV7z.Api.Holds
import FV7z.Tun.Inv
/-!
# `CPercentPrinter::~CPercentPrinter ()` (0x5f68a0): from the entry to the return or the tail jump (PLAN.md §M, M1)

7-Zip 26.06's `CPercentPrinter::~CPercentPrinter ()` (`CPP/7zip/UI/Console/PercentPrinter.h`; `objdump -d`) at
`0x5f68a0` in `7zzs`: `this` = `rdi` (`rbx`). One push (`rbx`, `aR S`), no stack guard. The `call` (10) of
`ClosePrint (false)` at `0x5f67c0` (`FV7z.Ocf`'s callee; its code a hypothesis, `Ev.kC`), then the members' buffers
freed from the last to the first: for each of the pointers at `this + 200`, `184`, `168`, `128`, `112`, `96`, `80`,
`40`, when it is not 0, the `call` of `operator delete []` at `0x6014f0` (its code a hypothesis, `Ev.kD`: the run
from its entry with `rdi` = the pointer to its return); the last (`this + 24`) by a tail jump (149) after the pop, or,
when it is 0, the pop and the `ret` (161). The padding after the tail jump (154) is not on these runs.

- `call_*`, `tgt_*`, `jmp_149`, `ret_161`: the instructions outside the blocks.
- `aR`, `V0`, `q1`, `Fm`, `fm_ks`, `Stk`, `KC`, `Ev`: the frame, the bytes after the push, the pop's address, the
  frame's registers (`rsp` = `aR S`, `rbx` = `this`, `rbp`, `r12`..`r15` as at the entry), the stack, the callee
  as a continuation, the hypotheses of the runs.
- `vc_*`: the pieces.
- `ppd_ok`: from the entry (`S` = the entry's `rsp`, `g0` = its registers, `I` of the bytes after the push, `V0`) to
  the return (`Ev.kr`: `rsp` 8 up, the callee-saved registers as at the entry), to `operator delete []`'s entry by
  the tail jump (`Ev.kj`: `rsp` = `S`, the callee-saved registers as at the entry, `rdi` = the pointer at
  `this + 24`), or a callee's goal.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
open FV7z.Api (KS)
namespace FV7z.Ppd
set_option linter.unusedVariables false

/-! ## The instructions outside the blocks -/

/-- `CPercentPrinter::ClosePrint`'s entry (`FV7z.Ocf`'s callee). -/
abbrev clp_ent : Addr := 0x5f67c0

/-- `operator delete []`'s entry. -/
abbrev del_ent : Addr := 0x6014f0
/-- The `call` of `ClosePrint` (10). -/
def pc10 : List Byte := [0xe8, 0x11, 0xff, 0xff, 0xff]
theorem pc10_0 : ∀ feat, Dec feat pc10 0 (FV7z.mk .call 64 [.rel 18446744073709551377] 5) := by dec_rfl
theorem wc_10 : pc10 <+: ppd.drop 10 := by decide +kernel
theorem call_10 (feat : Features) : Dec feat ppd 10 (FV7z.mk .call 64 [.rel 18446744073709551377] 5) :=
  Dec.shift (j := 10) (k := 0) (pc10_0 feat) wc_10 (Nat.zero_le _)
theorem tgt_10 : ppd_at.add (10 + 5) + BitVec.ofNat 64 18446744073709551377 = clp_ent := by decide
/-- The `call` of `operator delete []` (27). -/
def pc27 : List Byte := [0xe8, 0x30, 0xac, 0x00, 0x00]
theorem pc27_0 : ∀ feat, Dec feat pc27 0 (FV7z.mk .call 64 [.rel 44080] 5) := by dec_rfl
theorem wc_27 : pc27 <+: ppd.drop 27 := by decide +kernel
theorem call_27 (feat : Features) : Dec feat ppd 27 (FV7z.mk .call 64 [.rel 44080] 5) :=
  Dec.shift (j := 27) (k := 0) (pc27_0 feat) wc_27 (Nat.zero_le _)
theorem tgt_27 : ppd_at.add (27 + 5) + BitVec.ofNat 64 44080 = del_ent := by decide
/-- The `call` of `operator delete []` (44). -/
def pc44 : List Byte := [0xe8, 0x1f, 0xac, 0x00, 0x00]
theorem pc44_0 : ∀ feat, Dec feat pc44 0 (FV7z.mk .call 64 [.rel 44063] 5) := by dec_rfl
theorem wc_44 : pc44 <+: ppd.drop 44 := by decide +kernel
theorem call_44 (feat : Features) : Dec feat ppd 44 (FV7z.mk .call 64 [.rel 44063] 5) :=
  Dec.shift (j := 44) (k := 0) (pc44_0 feat) wc_44 (Nat.zero_le _)
theorem tgt_44 : ppd_at.add (44 + 5) + BitVec.ofNat 64 44063 = del_ent := by decide
/-- The `call` of `operator delete []` (61). -/
def pc61 : List Byte := [0xe8, 0x0e, 0xac, 0x00, 0x00]
theorem pc61_0 : ∀ feat, Dec feat pc61 0 (FV7z.mk .call 64 [.rel 44046] 5) := by dec_rfl
theorem wc_61 : pc61 <+: ppd.drop 61 := by decide +kernel
theorem call_61 (feat : Features) : Dec feat ppd 61 (FV7z.mk .call 64 [.rel 44046] 5) :=
  Dec.shift (j := 61) (k := 0) (pc61_0 feat) wc_61 (Nat.zero_le _)
theorem tgt_61 : ppd_at.add (61 + 5) + BitVec.ofNat 64 44046 = del_ent := by decide
/-- The `call` of `operator delete []` (78). -/
def pc78 : List Byte := [0xe8, 0xfd, 0xab, 0x00, 0x00]
theorem pc78_0 : ∀ feat, Dec feat pc78 0 (FV7z.mk .call 64 [.rel 44029] 5) := by dec_rfl
theorem wc_78 : pc78 <+: ppd.drop 78 := by decide +kernel
theorem call_78 (feat : Features) : Dec feat ppd 78 (FV7z.mk .call 64 [.rel 44029] 5) :=
  Dec.shift (j := 78) (k := 0) (pc78_0 feat) wc_78 (Nat.zero_le _)
theorem tgt_78 : ppd_at.add (78 + 5) + BitVec.ofNat 64 44029 = del_ent := by decide
/-- The `call` of `operator delete []` (92). -/
def pc92 : List Byte := [0xe8, 0xef, 0xab, 0x00, 0x00]
theorem pc92_0 : ∀ feat, Dec feat pc92 0 (FV7z.mk .call 64 [.rel 44015] 5) := by dec_rfl
theorem wc_92 : pc92 <+: ppd.drop 92 := by decide +kernel
theorem call_92 (feat : Features) : Dec feat ppd 92 (FV7z.mk .call 64 [.rel 44015] 5) :=
  Dec.shift (j := 92) (k := 0) (pc92_0 feat) wc_92 (Nat.zero_le _)
theorem tgt_92 : ppd_at.add (92 + 5) + BitVec.ofNat 64 44015 = del_ent := by decide
/-- The `call` of `operator delete []` (106). -/
def pc106 : List Byte := [0xe8, 0xe1, 0xab, 0x00, 0x00]
theorem pc106_0 : ∀ feat, Dec feat pc106 0 (FV7z.mk .call 64 [.rel 44001] 5) := by dec_rfl
theorem wc_106 : pc106 <+: ppd.drop 106 := by decide +kernel
theorem call_106 (feat : Features) : Dec feat ppd 106 (FV7z.mk .call 64 [.rel 44001] 5) :=
  Dec.shift (j := 106) (k := 0) (pc106_0 feat) wc_106 (Nat.zero_le _)
theorem tgt_106 : ppd_at.add (106 + 5) + BitVec.ofNat 64 44001 = del_ent := by decide
/-- The `call` of `operator delete []` (120). -/
def pc120 : List Byte := [0xe8, 0xd3, 0xab, 0x00, 0x00]
theorem pc120_0 : ∀ feat, Dec feat pc120 0 (FV7z.mk .call 64 [.rel 43987] 5) := by dec_rfl
theorem wc_120 : pc120 <+: ppd.drop 120 := by decide +kernel
theorem call_120 (feat : Features) : Dec feat ppd 120 (FV7z.mk .call 64 [.rel 43987] 5) :=
  Dec.shift (j := 120) (k := 0) (pc120_0 feat) wc_120 (Nat.zero_le _)
theorem tgt_120 : ppd_at.add (120 + 5) + BitVec.ofNat 64 43987 = del_ent := by decide
/-- The `call` of `operator delete []` (134). -/
def pc134 : List Byte := [0xe8, 0xc5, 0xab, 0x00, 0x00]
theorem pc134_0 : ∀ feat, Dec feat pc134 0 (FV7z.mk .call 64 [.rel 43973] 5) := by dec_rfl
theorem wc_134 : pc134 <+: ppd.drop 134 := by decide +kernel
theorem call_134 (feat : Features) : Dec feat ppd 134 (FV7z.mk .call 64 [.rel 43973] 5) :=
  Dec.shift (j := 134) (k := 0) (pc134_0 feat) wc_134 (Nat.zero_le _)
theorem tgt_134 : ppd_at.add (134 + 5) + BitVec.ofNat 64 43973 = del_ent := by decide
/-- The tail jump to `operator delete []` (149). -/
def pjm : List Byte := [0xe9, 0xb6, 0xab, 0x00, 0x00]
theorem pjm_0 : ∀ feat, Dec feat pjm 0 (FV7z.mk .jmp 64 [.rel 43958] 5) := by dec_rfl
theorem wj_149 : pjm <+: ppd.drop 149 := by decide +kernel
theorem jmp_149 (feat : Features) : Dec feat ppd 149 (FV7z.mk .jmp 64 [.rel 43958] 5) :=
  Dec.shift (j := 149) (k := 0) (pjm_0 feat) wj_149 (Nat.zero_le _)

/-- The `ret` (161). -/
def pret : List Byte := [0xc3]
theorem pret_0 : ∀ feat, Dec feat pret 0 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem w_161 : pret <+: ppd.drop 161 := by decide +kernel
theorem ret_161 (feat : Features) : Dec feat ppd 161 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 161) (k := 0) (pret_0 feat) w_161 (Nat.zero_le _)

/-! ## The frame -/

/-- The stack pointer after the push. -/
abbrev aR (S : Addr) : Addr := S - 8

/-- The bytes after the push (`rbx`). -/
abbrev V0 (V : Addr → Byte) (g : Gprs) : Addr → Byte := Vst V (g.rsp - 8) (toBytesLE g.rbx 8)

theorem q1 (S : Addr) : aR S + 8 = S := BitVec.sub_add_cancel _ _

/-- The frame from the prologue on: `rsp` = `aR S`, `rbx` = `this`, `rbp`, `r12`..`r15` as at the entry. -/
abbrev Fm (S : Addr) (g0 g : Gprs) : Prop :=
  g.rsp = aR S ∧ g.rbx = g0.rdi ∧ g.rbp = g0.rbp ∧ g.r12 = g0.r12 ∧ g.r13 = g0.r13 ∧ g.r14 = g0.r14 ∧
    g.r15 = g0.r15

/-- Through a piece or a callee: `rsp` = `aR S`, the callee-saved registers kept. -/
theorem fm_ks {S : Addr} {g0 g g' : Gprs} (h : Fm S g0 g) (hs : g'.rsp = aR S) (hk : KS g g') : Fm S g0 g' :=
  ⟨hs, hk.1.trans h.2.1, hk.2.1.trans h.2.2.1, hk.2.2.1.trans h.2.2.2.1, hk.2.2.2.1.trans h.2.2.2.2.1,
    hk.2.2.2.2.1.trans h.2.2.2.2.2.1, hk.2.2.2.2.2.trans h.2.2.2.2.2.2⟩

/-- The stack: the saved `rbx`. -/
abbrev Stk (W : Addr → Byte) (S : Addr) (g0 : Gprs) : Prop := rdq(W, S - 8) = g0.rbx

/-- The callee from the `call` before `j` (entry `ent`, the bytes `W`, the registers `A`): at its entry, and from its
return at `j` with `rsp` = `aR S`, the callee-saved registers as at its entry, `B` and the invariant `J`, the run
goes on to the goal. -/
def KC (prof : Profile) (F : Footprint) (Wl : List Rgn) (L : List (Addr × List Byte)) (s₀ : State) (o : Oracle)
    (gev : List Event) (gP : State → Nat → List Event → Prop) (gE : Outcome → List Event → Prop)
    (S : Addr) (J : (Addr → Byte) → Prop) (ent : Addr) (j : Nat) (W : Addr → Byte) (A B : Gprs → Prop) : Prop :=
  ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y →
    Agree F Y.proc.mm.mem (Vst W (aR S - 8) (toBytesLE (ppd_at.add j) 8)) →
    Y.cpu.rip = ent → Y.cpu.gpr.rsp = aR S - 8 → A Y.cpu.gpr →
    (∀ (Z : State) (W' : Addr → Byte) (t'' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem W' →
      Z.cpu.rip = ppd_at.add j → Z.cpu.gpr.rsp = aR S → KS Y.cpu.gpr Z.cpu.gpr → B Z.cpu.gpr → J W' →
      GoG prof L o gev gP gE Z t'') →
    GoG prof L o gev gP gE Y t'

/-! ## The hypotheses of the runs -/

/-- The hypotheses of the runs (`S`, `g0` the entry's stack pointer and registers, `e₂.add j₂` the return address,
`I` the invariant of the bytes): the saved `rbx` and the return address under `I`, their slots readable, the
`call`s' slot, the nine pointers of `this` readable (`f*`); the callees (`kC`: `ClosePrint` with `rdi` = `this`;
`kD`: `operator delete []` with `rdi` = the pointer at `this + d`), keeping `I`; the return (`kr`) and the tail jump
(`kj`) as the goals. -/
structure Ev (prof : Profile) (F : Footprint) (Wl : List Rgn) (L : List (Addr × List Byte)) (s₀ : State)
    (o : Oracle) (gev : List Event) (gP : State → Nat → List Event → Prop) (gE : Outcome → List Event → Prop)
    (S : Addr) (g0 : Gprs) (e₂ : Addr) (code₂ : List Byte) (j₂ : Nat) (I : (Addr → Byte) → Prop) : Prop where
  c : Seg prof F Wl L s₀ o
  hin : CodeIn L ppd_at ppd
  hin₂ : CodeIn L e₂ code₂
  h₂ : j₂ < code₂.length
  hI : ∀ W, I W → Stk W S g0
  hR : ∀ W, I W → rdq(W, S) = e₂.add j₂
  hl : ∀ i < 8, Foot F.data (Addr.add S i)
  fb1 : ∀ i < 8, Foot F.data (Addr.add (S - 8) i)
  hr8 : ∀ i < 8, Foot Wl (Addr.add (aR S - 8) i)
  f200 : ∀ i < 8, Foot F.data (Addr.add (g0.rdi + 200#64) i)
  f184 : ∀ i < 8, Foot F.data (Addr.add (g0.rdi + 184#64) i)
  f168 : ∀ i < 8, Foot F.data (Addr.add (g0.rdi + 168#64) i)
  f128 : ∀ i < 8, Foot F.data (Addr.add (g0.rdi + 128#64) i)
  f112 : ∀ i < 8, Foot F.data (Addr.add (g0.rdi + 112#64) i)
  f96 : ∀ i < 8, Foot F.data (Addr.add (g0.rdi + 96#64) i)
  f80 : ∀ i < 8, Foot F.data (Addr.add (g0.rdi + 80#64) i)
  f40 : ∀ i < 8, Foot F.data (Addr.add (g0.rdi + 40#64) i)
  f24 : ∀ i < 8, Foot F.data (Addr.add (g0.rdi + 24#64) i)
  cC : ∃ code : List Byte, CodeIn L clp_ent code ∧ 0 < code.length
  cD : ∃ code : List Byte, CodeIn L del_ent code ∧ 0 < code.length
  kC : ∀ j W, I W → KC prof F Wl L s₀ o gev gP gE S I clp_ent j W (fun g => g.rdi = g0.rdi) (fun _ => True)
  kD : ∀ j W (d : Addr), I W → KC prof F Wl L s₀ o gev gP gE S I del_ent j W (fun g => g.rdi = rdq(W, g0.rdi + d))
    (fun _ => True)
  kr : ∀ (W : Addr → Byte) (Z' : State) (t' : Nat), KeptW Wl s₀ Z' → Agree F Z'.proc.mm.mem W →
    Z'.cpu.rip = e₂.add j₂ → Z'.cpu.gpr.rsp = S + 8 → KS g0 Z'.cpu.gpr → I W → GoG prof L o gev gP gE Z' t'
  kj : ∀ (W : Addr → Byte) (Y : State) (t' : Nat), KeptW Wl s₀ Y → Agree F Y.proc.mm.mem W →
    Y.cpu.rip = del_ent → Y.cpu.gpr.rsp = S → KS g0 Y.cpu.gpr → Y.cpu.gpr.rdi = rdq(W, g0.rdi + 24#64) → I W →
    GoG prof L o gev gP gE Y t'

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

/-- `endbr64`, the push, `esi` = 0, `rbx` = `this`, to the `call` of `ClosePrint` at 10. -/
theorem vc_0 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (hs1 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8) i))
    (h : ∀ g', g'.rsp = aR g.rsp → g'.rbx = g.rdi → g'.rdi = g.rdi → g'.rbp = g.rbp → g'.r12 = g.r12 →
      g'.r13 = g.r13 → g'.r14 = g.r14 → g'.r15 = g.r15 → ∀ fl, Q 10 g' fl (V0 V g)) :
    W_0 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [aR, V0] at hs1 h ⊢
  wpx [W_0, o0]
  all_goals repeat' (first
    | refine h _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ _
    | with_reducible exact hs1
    | ostep)

/-- `rdi` = the pointer at `this + 200`: to 32 when it is 0, else to the `call` of `operator delete []` at 27. -/
theorem vc_15 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (hf : ∀ i < 8, Foot F.data (Addr.add (g.rbx + 200#64) i))
    (hn : ∀ g', g'.rsp = g.rsp → KS g g' → ∀ fl, Q 32 g' fl V)
    (hc : ∀ g', g'.rsp = g.rsp → KS g g' → g'.rdi = rdq(V, g.rbx + 200#64) → ∀ fl, Q 27 g' fl V) :
    W_15 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hf hn hc ⊢
  wpx [W_15, o1]
  all_goals repeat' (first
    | refine hn _ ?_ ?_ _
    | refine hc _ ?_ ?_ ?_ _
    | exact hf
    | ostep)

/-- `rdi` = the pointer at `this + 184`: to 49 when it is 0, else to the `call` of `operator delete []` at 44. -/
theorem vc_32 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (hf : ∀ i < 8, Foot F.data (Addr.add (g.rbx + 184#64) i))
    (hn : ∀ g', g'.rsp = g.rsp → KS g g' → ∀ fl, Q 49 g' fl V)
    (hc : ∀ g', g'.rsp = g.rsp → KS g g' → g'.rdi = rdq(V, g.rbx + 184#64) → ∀ fl, Q 44 g' fl V) :
    W_32 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hf hn hc ⊢
  wpx [W_32, o2]
  all_goals repeat' (first
    | refine hn _ ?_ ?_ _
    | refine hc _ ?_ ?_ ?_ _
    | exact hf
    | ostep)

/-- `rdi` = the pointer at `this + 168`: to 66 when it is 0, else to the `call` of `operator delete []` at 61. -/
theorem vc_49 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (hf : ∀ i < 8, Foot F.data (Addr.add (g.rbx + 168#64) i))
    (hn : ∀ g', g'.rsp = g.rsp → KS g g' → ∀ fl, Q 66 g' fl V)
    (hc : ∀ g', g'.rsp = g.rsp → KS g g' → g'.rdi = rdq(V, g.rbx + 168#64) → ∀ fl, Q 61 g' fl V) :
    W_49 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hf hn hc ⊢
  wpx [W_49, o3]
  all_goals repeat' (first
    | refine hn _ ?_ ?_ _
    | refine hc _ ?_ ?_ ?_ _
    | exact hf
    | ostep)

/-- `rdi` = the pointer at `this + 128`: to 83 when it is 0, else to the `call` of `operator delete []` at 78. -/
theorem vc_66 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (hf : ∀ i < 8, Foot F.data (Addr.add (g.rbx + 128#64) i))
    (hn : ∀ g', g'.rsp = g.rsp → KS g g' → ∀ fl, Q 83 g' fl V)
    (hc : ∀ g', g'.rsp = g.rsp → KS g g' → g'.rdi = rdq(V, g.rbx + 128#64) → ∀ fl, Q 78 g' fl V) :
    W_66 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hf hn hc ⊢
  wpx [W_66, o4]
  all_goals repeat' (first
    | refine hn _ ?_ ?_ _
    | refine hc _ ?_ ?_ ?_ _
    | exact hf
    | ostep)

/-- `rdi` = the pointer at `this + 112`: to 97 when it is 0, else to the `call` of `operator delete []` at 92. -/
theorem vc_83 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (hf : ∀ i < 8, Foot F.data (Addr.add (g.rbx + 112#64) i))
    (hn : ∀ g', g'.rsp = g.rsp → KS g g' → ∀ fl, Q 97 g' fl V)
    (hc : ∀ g', g'.rsp = g.rsp → KS g g' → g'.rdi = rdq(V, g.rbx + 112#64) → ∀ fl, Q 92 g' fl V) :
    W_83 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hf hn hc ⊢
  wpx [W_83, o5]
  all_goals repeat' (first
    | refine hn _ ?_ ?_ _
    | refine hc _ ?_ ?_ ?_ _
    | exact hf
    | ostep)

/-- `rdi` = the pointer at `this + 96`: to 111 when it is 0, else to the `call` of `operator delete []` at 106. -/
theorem vc_97 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (hf : ∀ i < 8, Foot F.data (Addr.add (g.rbx + 96#64) i))
    (hn : ∀ g', g'.rsp = g.rsp → KS g g' → ∀ fl, Q 111 g' fl V)
    (hc : ∀ g', g'.rsp = g.rsp → KS g g' → g'.rdi = rdq(V, g.rbx + 96#64) → ∀ fl, Q 106 g' fl V) :
    W_97 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hf hn hc ⊢
  wpx [W_97, o6]
  all_goals repeat' (first
    | refine hn _ ?_ ?_ _
    | refine hc _ ?_ ?_ ?_ _
    | exact hf
    | ostep)

/-- `rdi` = the pointer at `this + 80`: to 125 when it is 0, else to the `call` of `operator delete []` at 120. -/
theorem vc_111 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (hf : ∀ i < 8, Foot F.data (Addr.add (g.rbx + 80#64) i))
    (hn : ∀ g', g'.rsp = g.rsp → KS g g' → ∀ fl, Q 125 g' fl V)
    (hc : ∀ g', g'.rsp = g.rsp → KS g g' → g'.rdi = rdq(V, g.rbx + 80#64) → ∀ fl, Q 120 g' fl V) :
    W_111 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hf hn hc ⊢
  wpx [W_111, o7]
  all_goals repeat' (first
    | refine hn _ ?_ ?_ _
    | refine hc _ ?_ ?_ ?_ _
    | exact hf
    | ostep)

/-- `rdi` = the pointer at `this + 40`: to 139 when it is 0, else to the `call` of `operator delete []` at 134. -/
theorem vc_125 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (hf : ∀ i < 8, Foot F.data (Addr.add (g.rbx + 40#64) i))
    (hn : ∀ g', g'.rsp = g.rsp → KS g g' → ∀ fl, Q 139 g' fl V)
    (hc : ∀ g', g'.rsp = g.rsp → KS g g' → g'.rdi = rdq(V, g.rbx + 40#64) → ∀ fl, Q 134 g' fl V) :
    W_125 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hf hn hc ⊢
  wpx [W_125, o8]
  all_goals repeat' (first
    | refine hn _ ?_ ?_ _
    | refine hc _ ?_ ?_ ?_ _
    | exact hf
    | ostep)

/-- `rdi` = the pointer at `this + 24`, the pop: to the `ret` at 161 when it is 0, else to the tail jump at 149. -/
theorem vc_139 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (hf : ∀ i < 8, Foot F.data (Addr.add (g.rbx + 24#64) i)) (hp : ∀ i < 8, Foot F.data (Addr.add g.rsp i))
    (hr : ∀ g', g'.rsp = g.rsp + 8 → g'.rbx = rdq(V, g.rsp) → g'.rbp = g.rbp → g'.r12 = g.r12 →
      g'.r13 = g.r13 → g'.r14 = g.r14 → g'.r15 = g.r15 → ∀ fl, Q 161 g' fl V)
    (hj : ∀ g', g'.rsp = g.rsp + 8 → g'.rbx = rdq(V, g.rsp) → g'.rbp = g.rbp → g'.r12 = g.r12 →
      g'.r13 = g.r13 → g'.r14 = g.r14 → g'.r15 = g.r15 → g'.rdi = rdq(V, g.rbx + 24#64) →
      ∀ fl, Q 149 g' fl V) :
    W_139 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hf hp hr hj ⊢
  wpx [W_139, W_148, W_160, o9, o10]
  all_goals repeat' (first
    | refine hr _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ _
    | refine hj _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ _
    | exact hf
    | exact hp
    | ostep)

end Pieces

/-! ## The runs -/

section Runs
variable {prof : Profile} {F : Footprint} {Wl : List Rgn} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {S : Addr} {g0 : Gprs} {e₂ : Addr} {code₂ : List Byte} {j₂ : Nat} {I : (Addr → Byte) → Prop}
  {X Y : State} {t : Nat} {V W : Addr → Byte}

/-- From 139: the last pointer, the pop, to the `ret` (`kr`) or the tail jump (`kj`). -/
theorem from139 (E : Ev prof F Wl L s₀ o gev gP gE S g0 e₂ code₂ j₂ I) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = ppd_at.add 139) (hm : Fm S g0 Y.cpu.gpr) (hIW : I W) :
    GoG prof L o gev gP gE Y t := by
  have s1 := E.hI W hIW
  have s0 := E.hR W hIW
  have ms := hm.1
  have hrb := hm.2.1
  have e1 : rdq(W, Y.cpu.gpr.rsp) = g0.rbx := by rw [ms]; exact s1
  refine (c_139 prof).run E.c E.hin (fun j' g' _ V' => (j' = 161 ∨ j' = 149) ∧ V' = W ∧
      g'.rsp = Y.cpu.gpr.rsp + 8 ∧ g'.rbx = rdq(W, Y.cpu.gpr.rsp) ∧ g'.rbp = Y.cpu.gpr.rbp ∧
      g'.r12 = Y.cpu.gpr.r12 ∧ g'.r13 = Y.cpu.gpr.r13 ∧ g'.r14 = Y.cpu.gpr.r14 ∧ g'.r15 = Y.cpu.gpr.r15 ∧
      (j' = 149 → g'.rdi = rdq(W, g0.rdi + 24#64))) hK hA hr
    (vc_139 (by rw [hrb]; exact E.f24) (by rw [ms]; exact E.fb1)
      (fun _ a b c d e m n _ => ⟨Or.inl rfl, rfl, a, b, c, d, e, m, n, fun h => absurd h (by decide)⟩)
      fun _ a b c d e m n p _ => ⟨Or.inr rfl, rfl, a, b, c, d, e, m, n, fun _ => by rw [p, hrb]⟩) ?_
  rintro j' g fl V₁ ⟨hj, hV₁, gs, gb, gp, g12, g13, g14, g15, gdi⟩ U t₁ hKU hAU hrU hgU -
  subst V₁ hgU
  have hsU : U.cpu.gpr.rsp = S := by rw [gs, ms]; exact q1 S
  have hk : KS g0 U.cpu.gpr :=
    ⟨gb.trans e1, gp.trans hm.2.2.1, g12.trans hm.2.2.2.1, g13.trans hm.2.2.2.2.1, g14.trans hm.2.2.2.2.2.1,
      g15.trans hm.2.2.2.2.2.2⟩
  rcases hj with rfl | rfl
  · refine E.c.s_ret hKU hAU E.hin (lt_len (by decide)) hrU (ret_161 _) (by rw [hsU]; exact E.hl) E.hin₂ E.h₂
      (by rw [hsU]; exact s0) ?_
    rintro Z' t₂ hKZ' hAZ' ⟨hrZ', hgZ'⟩
    refine E.kr W Z' t₂ hKZ' hAZ' hrZ' ?_ ?_ hIW
    · rw [hgZ']
      show U.cpu.gpr.rsp + 8 = _
      rw [hsU]
    · rw [hgZ']
      exact hk
  · obtain ⟨cT, hinT, hT⟩ := E.cD
    refine E.c.s_jmp_x hKU hAU E.hin (lt_len (by decide)) hrU (jmp_149 _) hinT hT (by decide) ?_
    rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
    refine E.kj W Y₂ t₂ hK₂ hA₂ (by rw [hr₂, addr_add_zero]) (by rw [hg₂]; exact hsU) ?_ ?_ hIW
    · rw [hg₂]
      exact hk
    · rw [hg₂]
      exact gdi rfl

/-- From 125: the pointer at `this + 40`, to 139, or its `call` of `operator delete []` at 134, then from 139. -/
theorem from125 (E : Ev prof F Wl L s₀ o gev gP gE S g0 e₂ code₂ j₂ I) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = ppd_at.add 125) (hm : Fm S g0 Y.cpu.gpr) (hIW : I W) :
    GoG prof L o gev gP gE Y t := by
  have hrb := hm.2.1
  refine (c_125 prof).run E.c E.hin (fun j' g' _ V' => (j' = 139 ∨ j' = 134) ∧ V' = W ∧ Fm S g0 g' ∧
      (j' = 134 → g'.rdi = rdq(W, g0.rdi + 40#64))) hK hA hr
    (vc_125 (by rw [hrb]; exact E.f40)
      (fun _ a k _ => ⟨Or.inl rfl, rfl, fm_ks hm (a.trans hm.1) k, fun h => absurd h (by decide)⟩)
      fun _ a k p _ => ⟨Or.inr rfl, rfl, fm_ks hm (a.trans hm.1) k, fun _ => by rw [p, hrb]⟩) ?_
  rintro j' g fl V₁ ⟨hj, hV₁, hmU, hdi⟩ U t₁ hKU hAU hrU hgU -
  subst V₁ hgU
  rcases hj with rfl | rfl
  · exact from139 E hKU hAU hrU hmU hIW
  · obtain ⟨cc, hinc, hcc⟩ := E.cD
    have hU : U.cpu.gpr.rsp - 8 = aR S - 8 := by rw [hmU.1]
    refine E.c.s_call hKU hAU E.hin (lt_len (by decide)) hrU (call_134 _) hinc hcc tgt_134
      (by rw [hU]; exact E.hr8) ?_
    rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
    rw [hU] at hA₂
    refine E.kD _ _ (40#64) hIW Y₂ t₂ hK₂ hA₂ hr₂ (by rw [hg₂]; exact hU) (by rw [hg₂]; exact hdi rfl) ?_
    intro Z W' t₃ hKZ hAZ hrZ hsZ hkZ _ hIZ
    rw [hg₂] at hkZ
    exact from139 E hKZ hAZ hrZ (fm_ks hmU hsZ hkZ) hIZ

/-- From 111: the pointer at `this + 80`, to 125, or its `call` of `operator delete []` at 120, then from 125. -/
theorem from111 (E : Ev prof F Wl L s₀ o gev gP gE S g0 e₂ code₂ j₂ I) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = ppd_at.add 111) (hm : Fm S g0 Y.cpu.gpr) (hIW : I W) :
    GoG prof L o gev gP gE Y t := by
  have hrb := hm.2.1
  refine (c_111 prof).run E.c E.hin (fun j' g' _ V' => (j' = 125 ∨ j' = 120) ∧ V' = W ∧ Fm S g0 g' ∧
      (j' = 120 → g'.rdi = rdq(W, g0.rdi + 80#64))) hK hA hr
    (vc_111 (by rw [hrb]; exact E.f80)
      (fun _ a k _ => ⟨Or.inl rfl, rfl, fm_ks hm (a.trans hm.1) k, fun h => absurd h (by decide)⟩)
      fun _ a k p _ => ⟨Or.inr rfl, rfl, fm_ks hm (a.trans hm.1) k, fun _ => by rw [p, hrb]⟩) ?_
  rintro j' g fl V₁ ⟨hj, hV₁, hmU, hdi⟩ U t₁ hKU hAU hrU hgU -
  subst V₁ hgU
  rcases hj with rfl | rfl
  · exact from125 E hKU hAU hrU hmU hIW
  · obtain ⟨cc, hinc, hcc⟩ := E.cD
    have hU : U.cpu.gpr.rsp - 8 = aR S - 8 := by rw [hmU.1]
    refine E.c.s_call hKU hAU E.hin (lt_len (by decide)) hrU (call_120 _) hinc hcc tgt_120
      (by rw [hU]; exact E.hr8) ?_
    rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
    rw [hU] at hA₂
    refine E.kD _ _ (80#64) hIW Y₂ t₂ hK₂ hA₂ hr₂ (by rw [hg₂]; exact hU) (by rw [hg₂]; exact hdi rfl) ?_
    intro Z W' t₃ hKZ hAZ hrZ hsZ hkZ _ hIZ
    rw [hg₂] at hkZ
    exact from125 E hKZ hAZ hrZ (fm_ks hmU hsZ hkZ) hIZ

/-- From 97: the pointer at `this + 96`, to 111, or its `call` of `operator delete []` at 106, then from 111. -/
theorem from97 (E : Ev prof F Wl L s₀ o gev gP gE S g0 e₂ code₂ j₂ I) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = ppd_at.add 97) (hm : Fm S g0 Y.cpu.gpr) (hIW : I W) :
    GoG prof L o gev gP gE Y t := by
  have hrb := hm.2.1
  refine (c_97 prof).run E.c E.hin (fun j' g' _ V' => (j' = 111 ∨ j' = 106) ∧ V' = W ∧ Fm S g0 g' ∧
      (j' = 106 → g'.rdi = rdq(W, g0.rdi + 96#64))) hK hA hr
    (vc_97 (by rw [hrb]; exact E.f96)
      (fun _ a k _ => ⟨Or.inl rfl, rfl, fm_ks hm (a.trans hm.1) k, fun h => absurd h (by decide)⟩)
      fun _ a k p _ => ⟨Or.inr rfl, rfl, fm_ks hm (a.trans hm.1) k, fun _ => by rw [p, hrb]⟩) ?_
  rintro j' g fl V₁ ⟨hj, hV₁, hmU, hdi⟩ U t₁ hKU hAU hrU hgU -
  subst V₁ hgU
  rcases hj with rfl | rfl
  · exact from111 E hKU hAU hrU hmU hIW
  · obtain ⟨cc, hinc, hcc⟩ := E.cD
    have hU : U.cpu.gpr.rsp - 8 = aR S - 8 := by rw [hmU.1]
    refine E.c.s_call hKU hAU E.hin (lt_len (by decide)) hrU (call_106 _) hinc hcc tgt_106
      (by rw [hU]; exact E.hr8) ?_
    rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
    rw [hU] at hA₂
    refine E.kD _ _ (96#64) hIW Y₂ t₂ hK₂ hA₂ hr₂ (by rw [hg₂]; exact hU) (by rw [hg₂]; exact hdi rfl) ?_
    intro Z W' t₃ hKZ hAZ hrZ hsZ hkZ _ hIZ
    rw [hg₂] at hkZ
    exact from111 E hKZ hAZ hrZ (fm_ks hmU hsZ hkZ) hIZ

/-- From 83: the pointer at `this + 112`, to 97, or its `call` of `operator delete []` at 92, then from 97. -/
theorem from83 (E : Ev prof F Wl L s₀ o gev gP gE S g0 e₂ code₂ j₂ I) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = ppd_at.add 83) (hm : Fm S g0 Y.cpu.gpr) (hIW : I W) :
    GoG prof L o gev gP gE Y t := by
  have hrb := hm.2.1
  refine (c_83 prof).run E.c E.hin (fun j' g' _ V' => (j' = 97 ∨ j' = 92) ∧ V' = W ∧ Fm S g0 g' ∧
      (j' = 92 → g'.rdi = rdq(W, g0.rdi + 112#64))) hK hA hr
    (vc_83 (by rw [hrb]; exact E.f112)
      (fun _ a k _ => ⟨Or.inl rfl, rfl, fm_ks hm (a.trans hm.1) k, fun h => absurd h (by decide)⟩)
      fun _ a k p _ => ⟨Or.inr rfl, rfl, fm_ks hm (a.trans hm.1) k, fun _ => by rw [p, hrb]⟩) ?_
  rintro j' g fl V₁ ⟨hj, hV₁, hmU, hdi⟩ U t₁ hKU hAU hrU hgU -
  subst V₁ hgU
  rcases hj with rfl | rfl
  · exact from97 E hKU hAU hrU hmU hIW
  · obtain ⟨cc, hinc, hcc⟩ := E.cD
    have hU : U.cpu.gpr.rsp - 8 = aR S - 8 := by rw [hmU.1]
    refine E.c.s_call hKU hAU E.hin (lt_len (by decide)) hrU (call_92 _) hinc hcc tgt_92
      (by rw [hU]; exact E.hr8) ?_
    rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
    rw [hU] at hA₂
    refine E.kD _ _ (112#64) hIW Y₂ t₂ hK₂ hA₂ hr₂ (by rw [hg₂]; exact hU) (by rw [hg₂]; exact hdi rfl) ?_
    intro Z W' t₃ hKZ hAZ hrZ hsZ hkZ _ hIZ
    rw [hg₂] at hkZ
    exact from97 E hKZ hAZ hrZ (fm_ks hmU hsZ hkZ) hIZ

/-- From 66: the pointer at `this + 128`, to 83, or its `call` of `operator delete []` at 78, then from 83. -/
theorem from66 (E : Ev prof F Wl L s₀ o gev gP gE S g0 e₂ code₂ j₂ I) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = ppd_at.add 66) (hm : Fm S g0 Y.cpu.gpr) (hIW : I W) :
    GoG prof L o gev gP gE Y t := by
  have hrb := hm.2.1
  refine (c_66 prof).run E.c E.hin (fun j' g' _ V' => (j' = 83 ∨ j' = 78) ∧ V' = W ∧ Fm S g0 g' ∧
      (j' = 78 → g'.rdi = rdq(W, g0.rdi + 128#64))) hK hA hr
    (vc_66 (by rw [hrb]; exact E.f128)
      (fun _ a k _ => ⟨Or.inl rfl, rfl, fm_ks hm (a.trans hm.1) k, fun h => absurd h (by decide)⟩)
      fun _ a k p _ => ⟨Or.inr rfl, rfl, fm_ks hm (a.trans hm.1) k, fun _ => by rw [p, hrb]⟩) ?_
  rintro j' g fl V₁ ⟨hj, hV₁, hmU, hdi⟩ U t₁ hKU hAU hrU hgU -
  subst V₁ hgU
  rcases hj with rfl | rfl
  · exact from83 E hKU hAU hrU hmU hIW
  · obtain ⟨cc, hinc, hcc⟩ := E.cD
    have hU : U.cpu.gpr.rsp - 8 = aR S - 8 := by rw [hmU.1]
    refine E.c.s_call hKU hAU E.hin (lt_len (by decide)) hrU (call_78 _) hinc hcc tgt_78
      (by rw [hU]; exact E.hr8) ?_
    rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
    rw [hU] at hA₂
    refine E.kD _ _ (128#64) hIW Y₂ t₂ hK₂ hA₂ hr₂ (by rw [hg₂]; exact hU) (by rw [hg₂]; exact hdi rfl) ?_
    intro Z W' t₃ hKZ hAZ hrZ hsZ hkZ _ hIZ
    rw [hg₂] at hkZ
    exact from83 E hKZ hAZ hrZ (fm_ks hmU hsZ hkZ) hIZ

/-- From 49: the pointer at `this + 168`, to 66, or its `call` of `operator delete []` at 61, then from 66. -/
theorem from49 (E : Ev prof F Wl L s₀ o gev gP gE S g0 e₂ code₂ j₂ I) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = ppd_at.add 49) (hm : Fm S g0 Y.cpu.gpr) (hIW : I W) :
    GoG prof L o gev gP gE Y t := by
  have hrb := hm.2.1
  refine (c_49 prof).run E.c E.hin (fun j' g' _ V' => (j' = 66 ∨ j' = 61) ∧ V' = W ∧ Fm S g0 g' ∧
      (j' = 61 → g'.rdi = rdq(W, g0.rdi + 168#64))) hK hA hr
    (vc_49 (by rw [hrb]; exact E.f168)
      (fun _ a k _ => ⟨Or.inl rfl, rfl, fm_ks hm (a.trans hm.1) k, fun h => absurd h (by decide)⟩)
      fun _ a k p _ => ⟨Or.inr rfl, rfl, fm_ks hm (a.trans hm.1) k, fun _ => by rw [p, hrb]⟩) ?_
  rintro j' g fl V₁ ⟨hj, hV₁, hmU, hdi⟩ U t₁ hKU hAU hrU hgU -
  subst V₁ hgU
  rcases hj with rfl | rfl
  · exact from66 E hKU hAU hrU hmU hIW
  · obtain ⟨cc, hinc, hcc⟩ := E.cD
    have hU : U.cpu.gpr.rsp - 8 = aR S - 8 := by rw [hmU.1]
    refine E.c.s_call hKU hAU E.hin (lt_len (by decide)) hrU (call_61 _) hinc hcc tgt_61
      (by rw [hU]; exact E.hr8) ?_
    rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
    rw [hU] at hA₂
    refine E.kD _ _ (168#64) hIW Y₂ t₂ hK₂ hA₂ hr₂ (by rw [hg₂]; exact hU) (by rw [hg₂]; exact hdi rfl) ?_
    intro Z W' t₃ hKZ hAZ hrZ hsZ hkZ _ hIZ
    rw [hg₂] at hkZ
    exact from66 E hKZ hAZ hrZ (fm_ks hmU hsZ hkZ) hIZ

/-- From 32: the pointer at `this + 184`, to 49, or its `call` of `operator delete []` at 44, then from 49. -/
theorem from32 (E : Ev prof F Wl L s₀ o gev gP gE S g0 e₂ code₂ j₂ I) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = ppd_at.add 32) (hm : Fm S g0 Y.cpu.gpr) (hIW : I W) :
    GoG prof L o gev gP gE Y t := by
  have hrb := hm.2.1
  refine (c_32 prof).run E.c E.hin (fun j' g' _ V' => (j' = 49 ∨ j' = 44) ∧ V' = W ∧ Fm S g0 g' ∧
      (j' = 44 → g'.rdi = rdq(W, g0.rdi + 184#64))) hK hA hr
    (vc_32 (by rw [hrb]; exact E.f184)
      (fun _ a k _ => ⟨Or.inl rfl, rfl, fm_ks hm (a.trans hm.1) k, fun h => absurd h (by decide)⟩)
      fun _ a k p _ => ⟨Or.inr rfl, rfl, fm_ks hm (a.trans hm.1) k, fun _ => by rw [p, hrb]⟩) ?_
  rintro j' g fl V₁ ⟨hj, hV₁, hmU, hdi⟩ U t₁ hKU hAU hrU hgU -
  subst V₁ hgU
  rcases hj with rfl | rfl
  · exact from49 E hKU hAU hrU hmU hIW
  · obtain ⟨cc, hinc, hcc⟩ := E.cD
    have hU : U.cpu.gpr.rsp - 8 = aR S - 8 := by rw [hmU.1]
    refine E.c.s_call hKU hAU E.hin (lt_len (by decide)) hrU (call_44 _) hinc hcc tgt_44
      (by rw [hU]; exact E.hr8) ?_
    rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
    rw [hU] at hA₂
    refine E.kD _ _ (184#64) hIW Y₂ t₂ hK₂ hA₂ hr₂ (by rw [hg₂]; exact hU) (by rw [hg₂]; exact hdi rfl) ?_
    intro Z W' t₃ hKZ hAZ hrZ hsZ hkZ _ hIZ
    rw [hg₂] at hkZ
    exact from49 E hKZ hAZ hrZ (fm_ks hmU hsZ hkZ) hIZ

/-- From 15: the pointer at `this + 200`, to 32, or its `call` of `operator delete []` at 27, then from 32. -/
theorem from15 (E : Ev prof F Wl L s₀ o gev gP gE S g0 e₂ code₂ j₂ I) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = ppd_at.add 15) (hm : Fm S g0 Y.cpu.gpr) (hIW : I W) :
    GoG prof L o gev gP gE Y t := by
  have hrb := hm.2.1
  refine (c_15 prof).run E.c E.hin (fun j' g' _ V' => (j' = 32 ∨ j' = 27) ∧ V' = W ∧ Fm S g0 g' ∧
      (j' = 27 → g'.rdi = rdq(W, g0.rdi + 200#64))) hK hA hr
    (vc_15 (by rw [hrb]; exact E.f200)
      (fun _ a k _ => ⟨Or.inl rfl, rfl, fm_ks hm (a.trans hm.1) k, fun h => absurd h (by decide)⟩)
      fun _ a k p _ => ⟨Or.inr rfl, rfl, fm_ks hm (a.trans hm.1) k, fun _ => by rw [p, hrb]⟩) ?_
  rintro j' g fl V₁ ⟨hj, hV₁, hmU, hdi⟩ U t₁ hKU hAU hrU hgU -
  subst V₁ hgU
  rcases hj with rfl | rfl
  · exact from32 E hKU hAU hrU hmU hIW
  · obtain ⟨cc, hinc, hcc⟩ := E.cD
    have hU : U.cpu.gpr.rsp - 8 = aR S - 8 := by rw [hmU.1]
    refine E.c.s_call hKU hAU E.hin (lt_len (by decide)) hrU (call_27 _) hinc hcc tgt_27
      (by rw [hU]; exact E.hr8) ?_
    rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
    rw [hU] at hA₂
    refine E.kD _ _ (200#64) hIW Y₂ t₂ hK₂ hA₂ hr₂ (by rw [hg₂]; exact hU) (by rw [hg₂]; exact hdi rfl) ?_
    intro Z W' t₃ hKZ hAZ hrZ hsZ hkZ _ hIZ
    rw [hg₂] at hkZ
    exact from32 E hKZ hAZ hrZ (fm_ks hmU hsZ hkZ) hIZ

/-- `CPercentPrinter::~CPercentPrinter ()` from its entry (`X`'s registers, `S` = their `rsp`; the push's slot in
what the run may store into, `I` of the bytes after the push). -/
theorem ppd_ok (E : Ev prof F Wl L s₀ o gev gP gE X.cpu.gpr.rsp X.cpu.gpr e₂ code₂ j₂ I)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = ppd_at)
    (hs1 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8) i)) (hI0 : I (V0 V X.cpu.gpr)) :
    GoG prof L o gev gP gE X t := by
  refine (c_0 prof).run E.c E.hin (fun j' g' _ V' => j' = 10 ∧ V' = V0 V X.cpu.gpr ∧
      Fm X.cpu.gpr.rsp X.cpu.gpr g' ∧ g'.rdi = X.cpu.gpr.rdi) hK hA (by rw [addr_add_zero]; exact hrip)
    (vc_0 hs1 fun _ a b d p c e m n _ => ⟨rfl, rfl, ⟨a, b, p, c, e, m, n⟩, d⟩) ?_
  rintro j' g fl V₁ ⟨rfl, hV₁, hmY, hdi⟩ Y t₁ hKY hAY hrY hgY -
  subst V₁ hgY
  obtain ⟨cc, hinc, hcc⟩ := E.cC
  have hU : Y.cpu.gpr.rsp - 8 = aR X.cpu.gpr.rsp - 8 := by rw [hmY.1]
  refine E.c.s_call hKY hAY E.hin (lt_len (by decide)) hrY (call_10 _) hinc hcc tgt_10 (by rw [hU]; exact E.hr8) ?_
  rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
  rw [hU] at hA₂
  refine E.kC _ _ hI0 Y₂ t₂ hK₂ hA₂ hr₂ (by rw [hg₂]; exact hU) (by rw [hg₂]; exact hdi) ?_
  intro Z W' t₃ hKZ hAZ hrZ hsZ hkZ _ hIZ
  rw [hg₂] at hkZ
  exact from15 E hKZ hAZ hrZ (fm_ks hmY hsZ hkZ) hIZ

end Runs

end FV7z.Ppd
