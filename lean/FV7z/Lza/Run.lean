import FV7z.Lza.Holds
import FV7z.Cpt.Holds
import FV7z.Lemmas.CallM
/-!
# `LzmaDec_Allocate` (PLAN.md §M, M1): the run through the callees

7-Zip 26.06's `LzmaDec_Allocate (p, props, propsSize, alloc)` at `0x42bf80` in `7zzs` (`C/LzmaDec.c`; `objdump -d`),
from its entry to its return address, `S` the stack pointer and `g0` the registers at the entry, the callees as
continuations (`KC`, as in `FV7z/Smd/Holds.lean`): `LzmaProps_Decode` (39), `LzmaDec_AllocateProbs2` (103),
`alloc->Free` (207, `call [r13 + 8]`), `alloc->Alloc` (225, `call [r13]`), `LzmaDec_FreeProbs` (284).

The bytes are tracked by an invariant `I` the caller chooses: every callee returns with it, the stores into `p`
(`p->dic`, `p->dicBufSize`, `p->prop`) keep it (`hsep`), and it gives the saved registers, the return address and the
stack guard (`Stk`) and the code at `alloc->Free` and `alloc->Alloc`. `dicBufSize` (in `rbx`) is not named: the run
holds for every value.

- `Fm`, `Fr`, `Kf`, `KS`, `Stk`, `KC`, `Ev`: the frame, what a piece keeps, what a callee is given, the callee-saved
  registers, the stack, the callees, the hypotheses of the runs.
- `vc_44`, `vc_51`, `vc_108`, `vc_173`, `vc_229`, `vc_289`: the pieces with branches.
- `tail51`, `from238`, `from229`, `from211`, `from204`, `from173`, `from108`, `from44`: the runs from the cut points.
- `lza_ok`: from the entry to the return address.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Lza
set_option linter.unusedVariables false

/-! ## The instructions outside the blocks -/

/-- The `call` of `LzmaProps_Decode`. -/
def pc1 : List Byte := [0xe8, 0xf4, 0xfe, 0xff, 0xff]
theorem pc1_0 : ∀ feat, Dec feat pc1 0 (FV7z.mk .call 64 [.rel 18446744073709551348] 5) := by dec_rfl
theorem wc_39 : pc1 <+: lza.drop 39 := by decide +kernel
theorem call_39 (feat : Features) : Dec feat lza 39 (FV7z.mk .call 64 [.rel 18446744073709551348] 5) :=
  Dec.shift (j := 39) (k := 0) (pc1_0 feat) wc_39 (Nat.zero_le _)
theorem tgt_39 : lza_at.add (39 + 5) + BitVec.ofNat 64 18446744073709551348 = 0x42bea0#64 := by decide

/-- The `call` of `LzmaDec_AllocateProbs2`. -/
def pc2 : List Byte := [0xe8, 0x14, 0xfe, 0xff, 0xff]
theorem pc2_0 : ∀ feat, Dec feat pc2 0 (FV7z.mk .call 64 [.rel 18446744073709551124] 5) := by dec_rfl
theorem wc_103 : pc2 <+: lza.drop 103 := by decide +kernel
theorem call_103 (feat : Features) : Dec feat lza 103 (FV7z.mk .call 64 [.rel 18446744073709551124] 5) :=
  Dec.shift (j := 103) (k := 0) (pc2_0 feat) wc_103 (Nat.zero_le _)
theorem tgt_103 : lza_at.add (103 + 5) + BitVec.ofNat 64 18446744073709551124 = 0x42be00#64 := by decide

/-- The `call` of `alloc->Free`. -/
def pc3 : List Byte := [0x41, 0xff, 0x55, 0x08]
theorem pc3_0 : ∀ feat, Dec feat pc3 0 (FV7z.mk .call 64 [.mem (mbd 13 8 64)] 4) := by dec_rfl
theorem wc_207 : pc3 <+: lza.drop 207 := by decide +kernel
theorem call_207 (feat : Features) : Dec feat lza 207 (FV7z.mk .call 64 [.mem (mbd 13 8 64)] 4) :=
  Dec.shift (j := 207) (k := 0) (pc3_0 feat) wc_207 (Nat.zero_le _)

/-- The `call` of `alloc->Alloc`. -/
def pc4 : List Byte := [0x41, 0xff, 0x55, 0x00]
theorem pc4_0 : ∀ feat, Dec feat pc4 0 (FV7z.mk .call 64 [.mem (mbd 13 0 64)] 4) := by dec_rfl
theorem wc_225 : pc4 <+: lza.drop 225 := by decide +kernel
theorem call_225 (feat : Features) : Dec feat lza 225 (FV7z.mk .call 64 [.mem (mbd 13 0 64)] 4) :=
  Dec.shift (j := 225) (k := 0) (pc4_0 feat) wc_225 (Nat.zero_le _)

/-- The `call` of `LzmaDec_FreeProbs`. -/
def pc5 : List Byte := [0xe8, 0x3f, 0xfd, 0xff, 0xff]
theorem pc5_0 : ∀ feat, Dec feat pc5 0 (FV7z.mk .call 64 [.rel 18446744073709550911] 5) := by dec_rfl
theorem wc_284 : pc5 <+: lza.drop 284 := by decide +kernel
theorem call_284 (feat : Features) : Dec feat lza 284 (FV7z.mk .call 64 [.rel 18446744073709550911] 5) :=
  Dec.shift (j := 284) (k := 0) (pc5_0 feat) wc_284 (Nat.zero_le _)
theorem tgt_284 : lza_at.add (284 + 5) + BitVec.ofNat 64 18446744073709550911 = 0x42bde0#64 := by decide

/-- The `ret`. -/
def pret : List Byte := [0xc3]
theorem pret_0 : ∀ feat, Dec feat pret 0 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem w_84 : pret <+: lza.drop 84 := by decide +kernel
theorem ret_84 (feat : Features) : Dec feat lza 84 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 84) (k := 0) (pret_0 feat) w_84 (Nat.zero_le _)

/-! ## The frame -/

theorem q1 (S : Addr) : aR S + 24#64 = S - 8 - 8 - 8 - 8 := by
  show S - 8 - 8 - 8 - 8 - 24#64 + 24#64 = _; bv_omega
theorem q2 (S : Addr) : aR S + 24#64 + 8 = S - 8 - 8 - 8 := by
  show S - 8 - 8 - 8 - 8 - 24#64 + 24#64 + 8 = _; bv_omega
theorem q3 (S : Addr) : aR S + 24#64 + 8 + 8 = S - 8 - 8 := by
  show S - 8 - 8 - 8 - 8 - 24#64 + 24#64 + 8 + 8 = _; bv_omega
theorem q4 (S : Addr) : aR S + 24#64 + 8 + 8 + 8 = S - 8 := by
  show S - 8 - 8 - 8 - 8 - 24#64 + 24#64 + 8 + 8 + 8 = _; bv_omega
theorem q5 (S : Addr) : aR S + 24#64 + 8 + 8 + 8 + 8 = S := by
  show S - 8 - 8 - 8 - 8 - 24#64 + 24#64 + 8 + 8 + 8 + 8 = _; bv_omega

/-- The frame from 39 on: `rsp` = `aR S`, `rbp` = `p`, `r13` = `alloc`, `r14`, `r15` as at the entry (`g0`). -/
abbrev Fm (S : Addr) (g0 g : Gprs) : Prop :=
  g.rsp = aR S ∧ g.rbp = g0.rdi ∧ g.r13 = g0.rcx ∧ g.r14 = g0.r14 ∧ g.r15 = g0.r15

/-- What a piece keeps: `rsp`, `rbp`, `r13`–`r15`. -/
abbrev Fr (g g' : Gprs) : Prop :=
  g'.rsp = g.rsp ∧ g'.rbp = g.rbp ∧ g'.r13 = g.r13 ∧ g'.r14 = g.r14 ∧ g'.r15 = g.r15

/-- `Fm` but `rsp`: what a callee is given. -/
abbrev Kf (g0 g : Gprs) : Prop :=
  g.rbp = g0.rdi ∧ g.r13 = g0.rcx ∧ g.r14 = g0.r14 ∧ g.r15 = g0.r15

/-- The callee-saved registers as at the entry. -/
abbrev KS (g0 g : Gprs) : Prop :=
  g.rbx = g0.rbx ∧ g.rbp = g0.rbp ∧ g.r12 = g0.r12 ∧ g.r13 = g0.r13 ∧ g.r14 = g0.r14 ∧ g.r15 = g0.r15

theorem Fm.fr {S : Addr} {g0 g g' : Gprs} (h : Fm S g0 g) (h' : Fr g g') : Fm S g0 g' :=
  ⟨h'.1.trans h.1, h'.2.1.trans h.2.1, h'.2.2.1.trans h.2.2.1, h'.2.2.2.1.trans h.2.2.2.1,
    h'.2.2.2.2.trans h.2.2.2.2⟩

theorem kf_set {S : Addr} {g0 g : Gprs} {x : Addr} (h : Fm S g0 g) : Kf g0 (g.set 4 x) :=
  ⟨h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩

/-- The stack (`fb` the `fs` base, `ra` the return address): the four saved registers, the return address, the
stack guard as at `fs:0x28`. -/
abbrev Stk (fb : Addr) (W : Addr → Byte) (S : Addr) (g0 : Gprs) (ra : Addr) : Prop :=
  rdq(W, S - 8 - 8 - 8 - 8) = g0.rbx ∧ rdq(W, S - 8 - 8 - 8) = g0.rbp ∧ rdq(W, S - 8 - 8) = g0.r12 ∧
    rdq(W, S - 8) = g0.r13 ∧ rdq(W, S) = ra ∧ rdq(W, aR S + 8#64) = rdq(W, fb + 40#64)

/-- The bytes at the first `call`: the pushes, the stack guard stored. -/
abbrev V0 (fb : Addr) (V : Addr → Byte) (g : Gprs) : Addr → Byte :=
  Vst (P4 V g) (aR g.rsp + 8#64) (toBytesLE rdq(P4 V g, fb + 40#64) 8)

/-- A callee from the `call` before `j` (entry `ent`, the bytes `W`, the registers `A`): at its entry, and from its
return at `j` with the frame and the invariant `I`, the run goes on to the goal. -/
def KC (prof : Profile) (F : Footprint) (Wl : List Rgn) (L : List (Addr × List Byte)) (s₀ : State) (o : Oracle)
    (gev : List Event) (gP : State → Nat → List Event → Prop) (gE : Outcome → List Event → Prop)
    (S : Addr) (g0 : Gprs) (I : (Addr → Byte) → Prop) (ent : Addr) (j : Nat) (W : Addr → Byte)
    (A : Gprs → Prop) : Prop :=
  ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y →
    Agree F Y.proc.mm.mem (Vst W (aR S - 8) (toBytesLE (lza_at.add j) 8)) →
    Y.cpu.rip = ent → Y.cpu.gpr.rsp = aR S - 8 → A Y.cpu.gpr →
    (∀ (Z : State) (W' : Addr → Byte) (t'' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem W' →
      Z.cpu.rip = lza_at.add j → Fm S g0 Z.cpu.gpr → I W' → GoG prof L o gev gP gE Z t'') →
    GoG prof L o gev gP gE Y t'

/-- The hypotheses of the runs from the cut points after the first `call` (`S`, `g0` the entry's stack pointer and
registers, `e₂.add j₂` the return address, `I` the invariant of the bytes). -/
structure Ev (prof : Profile) (F : Footprint) (Wl : List Rgn) (L : List (Addr × List Byte)) (s₀ : State)
    (o : Oracle) (gev : List Event) (gP : State → Nat → List Event → Prop) (gE : Outcome → List Event → Prop)
    (fb S : Addr) (g0 : Gprs) (e₂ : Addr) (code₂ : List Byte) (j₂ : Nat) (I : (Addr → Byte) → Prop) : Prop where
  c : Seg prof F Wl L s₀ o
  hfs : s₀.cpu.seg.fsBase = fb
  hin : CodeIn L lza_at lza
  hin₂ : CodeIn L e₂ code₂
  h₂ : j₂ < code₂.length
  hI : ∀ W, I W → Stk fb W S g0 (e₂.add j₂)
  hsep : ∀ (W : Addr → Byte) (a v : BitVec 64), (a = g0.rdi ∨ a = g0.rdi + 24#64 ∨ a = g0.rdi + 32#64) → I W →
    I (Vst W a (toBytesLE v 8))
  hcl : ∀ i < 8, Foot F.data (Addr.add (fb + 40#64) i)
  fg : ∀ i < 8, Foot F.data (Addr.add (aR S + 8#64) i)
  f0 : ∀ i < 8, Foot F.data (Addr.add (aR S) i)
  f1 : ∀ i < 1, Foot F.data (Addr.add (aR S + 1#64) i)
  f4 : ∀ i < 4, Foot F.data (Addr.add (aR S + 4#64) i)
  fb32 : ∀ i < 8, Foot F.data (Addr.add (S - 8 - 8 - 8 - 8) i)
  fb24 : ∀ i < 8, Foot F.data (Addr.add (S - 8 - 8 - 8) i)
  fb16 : ∀ i < 8, Foot F.data (Addr.add (S - 8 - 8) i)
  fb8 : ∀ i < 8, Foot F.data (Addr.add (S - 8) i)
  hl : ∀ i < 8, Foot F.data (Addr.add S i)
  hr8 : ∀ i < 8, Foot Wl (Addr.add (aR S - 8) i)
  w0 : ∀ i < 8, Foot Wl (Addr.add g0.rdi i)
  w24 : ∀ i < 8, Foot Wl (Addr.add (g0.rdi + 24#64) i)
  w32 : ∀ i < 8, Foot Wl (Addr.add (g0.rdi + 32#64) i)
  fF : ∀ i < 8, Foot F.data (Addr.add (g0.rcx + 8#64) i)
  fA : ∀ i < 8, Foot F.data (Addr.add g0.rcx i)
  hcF : ∀ W, I W → ∃ code : List Byte, CodeIn L rdq(W, g0.rcx + 8#64) code ∧ 0 < code.length
  hcA : ∀ W, I W → ∃ code : List Byte, CodeIn L rdq(W, g0.rcx) code ∧ 0 < code.length
  hcAp : ∃ code : List Byte, CodeIn L 0x42be00#64 code ∧ 0 < code.length
  hcP : ∃ code : List Byte, CodeIn L 0x42bde0#64 code ∧ 0 < code.length
  kAp : ∀ W, I W → KC prof F Wl L s₀ o gev gP gE S g0 I 0x42be00#64 108 W
    (fun g => Kf g0 g ∧ g.rdi = g0.rdi ∧ g.rcx = g0.rcx)
  kF : ∀ W, I W → KC prof F Wl L s₀ o gev gP gE S g0 I rdq(W, g0.rcx + 8#64) 211 W
    (fun g => Kf g0 g ∧ g.rdi = g0.rcx)
  kA : ∀ W, I W → KC prof F Wl L s₀ o gev gP gE S g0 I rdq(W, g0.rcx) 229 W
    (fun g => Kf g0 g ∧ g.rdi = g0.rcx)
  kP : ∀ W, I W → KC prof F Wl L s₀ o gev gP gE S g0 I 0x42bde0#64 289 W
    (fun g => Kf g0 g ∧ g.rdi = g0.rdi ∧ g.rsi = g0.rcx)
  kr : ∀ (W : Addr → Byte) (Z' : State) (t' : Nat), KeptW Wl s₀ Z' → Agree F Z'.proc.mm.mem W →
    Z'.cpu.rip = e₂.add j₂ → Z'.cpu.gpr.rsp = S + 8 → KS g0 Z'.cpu.gpr → I W → GoG prof L o gev gP gE Z' t'

/-! ## The pieces with branches -/

section Pieces
variable {F : Footprint} {Wl : List Rgn}

/-- `mov r12d, eax; test eax, eax`: to the guard's check (51), or `edx`, `esi` = `propNew.lp`, `propNew.lc`, `rcx` =
`r13`, `rdi` = `rbp` to the `call` of `LzmaDec_AllocateProbs2` (103). -/
theorem vc_44 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (f0 : ∀ i < 1, Foot F.data (Addr.add g.rsp i)) (f1 : ∀ i < 1, Foot F.data (Addr.add (g.rsp + 1#64) i))
    (h103 : ∀ g', g'.rdi = g.rbp → g'.rcx = g.r13 → Fr g g' → ∀ fl, Q 103 g' fl V)
    (h51 : ∀ g', Fr g g' → ∀ fl, Q 51 g' fl V) :
    W_44 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at f0 f1 h103 h51 ⊢
  wpx [W_44, W_88, o1, o4]
  all_goals repeat' (first
    | refine h103 _ ?_ ?_ ?_ _
    | refine h51 _ ?_ _
    | with_reducible rfl
    | with_reducible exact f0
    | with_reducible exact f1
    | apply And.intro
    | intro _)

/-- The stack guard checked (as at `fs:0x28`: `jne` not taken), `add rsp, 0x18; mov eax, r12d`, the four pops, to
the `ret`. -/
theorem vc_51 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (hc : rdq(V, g.rsp + 8#64) = rdq(V, fb + 40#64)) (f8 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8#64) i))
    (fcl : ∀ i < 8, Foot F.data (Addr.add (fb + 40#64) i))
    (f1 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 24#64) i))
    (f2 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 24#64 + 8) i))
    (f3 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 24#64 + 8 + 8) i))
    (f4 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 24#64 + 8 + 8 + 8) i))
    (h : ∀ g', g'.rsp = g.rsp + 24#64 + 8 + 8 + 8 + 8 → g'.rbx = rdq(V, g.rsp + 24#64) →
      g'.rbp = rdq(V, g.rsp + 24#64 + 8) → g'.r12 = rdq(V, g.rsp + 24#64 + 8 + 8) →
      g'.r13 = rdq(V, g.rsp + 24#64 + 8 + 8 + 8) → g'.r14 = g.r14 → g'.r15 = g.r15 → ∀ fl, Q 84 g' fl V) :
    W_51 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hc f8 f1 f2 f3 f4 h ⊢
  have z0 : ((0#64 : BitVec 64) == 0) = true := by decide
  wpx [W_51, W_71, o2, o3, Op.xormf, hc, BitVec.xor_self, z0, decide_true, Bool.not_true, Bool.false_eq_true,
    false_implies, eq_self_iff_true, true_implies]
  all_goals repeat' (first
    | refine h _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ _
    | with_reducible rfl
    | with_reducible exact f8
    | with_reducible exact fcl
    | with_reducible exact f1
    | with_reducible exact f2
    | with_reducible exact f3
    | with_reducible exact f4
    | apply And.intro
    | intro _)

/-- `mov r12d, eax; test eax, eax`: to the guard's check (51), or `dicBufSize` into `rbx` (108..172), to 173. -/
theorem vc_108 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (f4 : ∀ i < 4, Foot F.data (Addr.add (g.rsp + 4#64) i))
    (h51 : ∀ g', Fr g g' → ∀ fl, Q 51 g' fl V) (h173 : ∀ g', Fr g g' → ∀ fl, Q 173 g' fl V) :
    W_108 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at f4 h51 h173 ⊢
  wpx [W_108, W_115, W_256, W_130, o1, o5, o13, o6]
  all_goals repeat' (first
    | refine h51 _ ?_ _
    | refine h173 _ ?_ _
    | with_reducible rfl
    | with_reducible exact f4
    | apply And.intro
    | intro _)

/-- An `rbp`-based address with no index, as `wpx` leaves it in a footprint goal. -/
theorem eaG_r5 {g : Gprs} (d : Nat) : eaG g (some 5) none 1 d = g.rbp + BitVec.ofNat 64 d := by
  show g.get (regOf 5) + 0 * BitVec.ofNat 64 1 + BitVec.ofNat 64 d = _
  rw [z_mul64, add_z64]; rfl

/-- The rounding's end, `rsi` = `p->dic`: to `alloc->Free` (204), or (`p->dic` set with `p->dicBufSize` = `rbx`)
to 238. -/
theorem vc_173 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (f24 : ∀ i < 8, Foot F.data (Addr.add (g.rbp + 24#64) i))
    (f32 : ∀ i < 8, Foot F.data (Addr.add (g.rbp + 32#64) i))
    (h204 : ∀ g', Fr g g' → ∀ fl, Q 204 g' fl V) (h238 : ∀ g', Fr g g' → ∀ fl, Q 238 g' fl V) :
    W_173 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at f24 f32 h204 h238 ⊢
  -- the `cmovae`'s condition, so that the registers after it are a structure, not an `if`
  by_cases hc : rax.toNat < (rdx + rax &&& rbx).toNat
  all_goals wpx [W_173, W_198, o7, o8, hc, decide_true, decide_false, Bool.not_true, Bool.not_false,
    Bool.false_eq_true, eq_self_iff_true, ↓reduceIte]
  all_goals repeat' (first
    | refine h204 _ ?_ _
    | refine h238 _ ?_ _
    | with_reducible rfl
    | with_reducible exact f24
    | with_reducible exact f32
    | (simp only [eaG_r5]; exact f32 _ (by assumption))
    | apply And.intro
    | intro _)

/-- `p->dic = rax; test rax, rax`: to 238, or `rsi` = `alloc`, `rdi` = `p` to `LzmaDec_FreeProbs` (284). -/
theorem vc_229 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (w24 : ∀ i < 8, Foot Wl (Addr.add (g.rbp + 24#64) i))
    (h284 : ∀ g', g'.rsi = g.r13 → g'.rdi = g.rbp → Fr g g' → ∀ fl,
      Q 284 g' fl (Vst V (g.rbp + 24#64) (toBytesLE g.rax 8)))
    (h238 : ∀ g', Fr g g' → ∀ fl, Q 238 g' fl (Vst V (g.rbp + 24#64) (toBytesLE g.rax 8))) :
    W_229 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at w24 h284 h238 ⊢
  wpx [W_229, W_272, o11, o14]
  all_goals repeat' (first
    | refine h284 _ ?_ ?_ ?_ _
    | refine h238 _ ?_ _
    | with_reducible rfl
    | with_reducible exact w24
    | apply And.intro
    | intro _)

/-- `jmp` to the guard's check. -/
theorem vc_289 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} (h : ∀ fl, Q 51 g fl V) :
    W_289 fb F Wl Q g f V := h _

end Pieces

/-! ## The runs -/

section Runs
variable {prof : Profile} {F : Footprint} {Wl : List Rgn} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {fb S : Addr} {g0 : Gprs} {e₂ : Addr} {code₂ : List Byte} {j₂ : Nat} {I : (Addr → Byte) → Prop}
  {Y : State} {t : Nat} {W : Addr → Byte}

/-- From 51 (the frame, the bytes `W` with `I`): the guard's check, the epilogue, the `ret`, to `kr`. -/
theorem tail51 (E : Ev prof F Wl L s₀ o gev gP gE fb S g0 e₂ code₂ j₂ I) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = lza_at.add 51) (hm : Fm S g0 Y.cpu.gpr) (hIW : I W) :
    GoG prof L o gev gP gE Y t := by
  obtain ⟨ms, mp, m13, m14, m15⟩ := hm
  obtain ⟨s1, s2, s3, s4, s5, s6⟩ := E.hI W hIW
  have e1 : rdq(W, Y.cpu.gpr.rsp + 24#64) = g0.rbx := by rw [ms, q1]; exact s1
  have e2 : rdq(W, Y.cpu.gpr.rsp + 24#64 + 8) = g0.rbp := by rw [ms, q2]; exact s2
  have e3 : rdq(W, Y.cpu.gpr.rsp + 24#64 + 8 + 8) = g0.r12 := by rw [ms, q3]; exact s3
  have e4 : rdq(W, Y.cpu.gpr.rsp + 24#64 + 8 + 8 + 8) = g0.r13 := by rw [ms, q4]; exact s4
  refine (c_51 prof fb).run E.c E.hfs E.hin (fun j' g' _ V' => j' = 84 ∧ V' = W ∧
      g'.rsp = Y.cpu.gpr.rsp + 24#64 + 8 + 8 + 8 + 8 ∧ g'.rbx = rdq(W, Y.cpu.gpr.rsp + 24#64) ∧
      g'.rbp = rdq(W, Y.cpu.gpr.rsp + 24#64 + 8) ∧ g'.r12 = rdq(W, Y.cpu.gpr.rsp + 24#64 + 8 + 8) ∧
      g'.r13 = rdq(W, Y.cpu.gpr.rsp + 24#64 + 8 + 8 + 8) ∧ g'.r14 = Y.cpu.gpr.r14 ∧ g'.r15 = Y.cpu.gpr.r15)
    hK hA hr
    (vc_51 (by rw [ms]; exact s6) (by rw [ms]; exact E.fg) E.hcl (by rw [ms, q1]; exact E.fb32)
      (by rw [ms, q2]; exact E.fb24) (by rw [ms, q3]; exact E.fb16) (by rw [ms, q4]; exact E.fb8)
      fun _ a b d e f g h _ => ⟨rfl, rfl, a, b, d, e, f, g, h⟩) ?_
  rintro j' g fl V₁ ⟨rfl, hV₁, gs, gx, gp, g12, g13, g14, g15⟩ U t₁ hKU hAU hrU hgU -
  subst V₁ hgU
  have hsU : U.cpu.gpr.rsp = S := by rw [gs, ms]; exact q5 S
  refine E.c.s_ret hKU hAU E.hin (lt_len (by decide)) hrU (ret_84 _) (by rw [hsU]; exact E.hl) E.hin₂ E.h₂
    (by rw [hsU]; exact s5) ?_
  rintro Z' t₂ hKZ' hAZ' ⟨hrZ', hgZ'⟩
  refine E.kr W Z' t₂ hKZ' hAZ' hrZ' ?_ ?_ hIW
  · rw [hgZ']
    show U.cpu.gpr.rsp + 8 = _
    rw [hsU]
  · rw [hgZ']
    exact ⟨gx.trans e1, gp.trans e2, g12.trans e3, g13.trans e4, g14.trans m14, g15.trans m15⟩

/-- From 238: `p->dicBufSize`, `p->prop` stored, to 51. -/
theorem from238 (E : Ev prof F Wl L s₀ o gev gP gE fb S g0 e₂ code₂ j₂ I) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = lza_at.add 238) (hm : Fm S g0 Y.cpu.gpr) (hIW : I W) :
    GoG prof L o gev gP gE Y t := by
  refine (c_238 prof fb).run E.c E.hfs E.hin (fun j' g' _ V' => j' = 51 ∧ Fr Y.cpu.gpr g' ∧
      V' = Vst (Vst W (Y.cpu.gpr.rbp + 32#64) (toBytesLE Y.cpu.gpr.rbx 8)) Y.cpu.gpr.rbp
        (toBytesLE rdq(W, Y.cpu.gpr.rsp) 8)) hK hA hr
    (vc_238 (by rw [hm.1]; exact E.f0) (by rw [hm.2.1]; exact E.w32) (by rw [hm.2.1]; exact E.w0)
      fun _ => ⟨rfl, ⟨rfl, rfl, rfl, rfl, rfl⟩, rfl⟩) ?_
  rintro j' g fl V₁ ⟨rfl, gf, rfl⟩ U t₁ hKU hAU hrU hgU -
  subst hgU
  exact tail51 E hKU hAU hrU (Fm.fr hm gf)
    (E.hsep _ _ _ (Or.inl hm.2.1) (E.hsep _ _ _ (Or.inr (Or.inr (by rw [hm.2.1]))) hIW))

/-- From 229 (back from `alloc->Alloc`): `p->dic` stored, to 238, or `LzmaDec_FreeProbs` (`kP`) and from its return
(289) to 51. -/
theorem from229 (E : Ev prof F Wl L s₀ o gev gP gE fb S g0 e₂ code₂ j₂ I) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = lza_at.add 229) (hm : Fm S g0 Y.cpu.gpr) (hIW : I W) :
    GoG prof L o gev gP gE Y t := by
  refine (c_229 prof fb).run E.c E.hfs E.hin (fun j' g' _ V' =>
      V' = Vst W (Y.cpu.gpr.rbp + 24#64) (toBytesLE Y.cpu.gpr.rax 8) ∧ Fr Y.cpu.gpr g' ∧
      (j' = 238 ∨ (j' = 284 ∧ g'.rsi = Y.cpu.gpr.r13 ∧ g'.rdi = Y.cpu.gpr.rbp))) hK hA hr
    (vc_229 (by rw [hm.2.1]; exact E.w24) (fun _ a b d _ => ⟨rfl, d, Or.inr ⟨rfl, a, b⟩⟩)
      (fun _ a _ => ⟨rfl, a, Or.inl rfl⟩)) ?_
  rintro j' g fl V₁ ⟨rfl, gf, hpost⟩ U t₁ hKU hAU hrU hgU -
  subst hgU
  have hmU := Fm.fr hm gf
  have hI1 : I (Vst W (Y.cpu.gpr.rbp + 24#64) (toBytesLE Y.cpu.gpr.rax 8)) :=
    E.hsep _ _ _ (Or.inr (Or.inl (by rw [hm.2.1]))) hIW
  rcases hpost with rfl | ⟨rfl, gsi, gdi⟩
  · exact from238 E hKU hAU hrU hmU hI1
  · have hU : U.cpu.gpr.rsp - 8 = aR S - 8 := by rw [hmU.1]
    obtain ⟨cP, hinP, hP⟩ := E.hcP
    refine E.c.s_call hKU hAU E.hin (lt_len (by decide)) hrU (call_284 _) hinP hP tgt_284
      (by rw [hU]; exact E.hr8) ?_
    rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
    rw [hU] at hA₂
    refine E.kP _ hI1 Y₂ t₂ hK₂ hA₂ hr₂ (by rw [hg₂]; exact hU)
      ⟨by rw [hg₂]; exact kf_set hmU, by rw [hg₂]; show U.cpu.gpr.rdi = _; rw [gdi, hm.2.1],
        by rw [hg₂]; show U.cpu.gpr.rsi = _; rw [gsi, hm.2.2.1]⟩ ?_
    intro Z W' t₃ hKZ hAZ hrZ hmZ hIZ
    refine (c_289 prof fb).run E.c E.hfs E.hin (fun j' g' _ V' => j' = 51 ∧ g' = Z.cpu.gpr ∧ V' = W')
      hKZ hAZ hrZ (vc_289 fun _ => ⟨rfl, rfl, rfl⟩) ?_
    rintro j' g fl V₁ ⟨rfl, rfl, rfl⟩ U' t₄ hKU' hAU' hrU' hgU' -
    exact tail51 E hKU' hAU' hrU' (by rw [hgU']; exact hmZ) hIZ

/-- From 211 (back from `alloc->Free`): `p->dic` = 0, `alloc->Alloc` (`kA`), from its return 229. -/
theorem from211 (E : Ev prof F Wl L s₀ o gev gP gE fb S g0 e₂ code₂ j₂ I) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = lza_at.add 211) (hm : Fm S g0 Y.cpu.gpr) (hIW : I W) :
    GoG prof L o gev gP gE Y t := by
  refine (c_211 prof fb).run E.c E.hfs E.hin (fun j' g' _ V' => j' = 225 ∧
      g' = { Y.cpu.gpr with rsi := Y.cpu.gpr.rbx, rdi := Y.cpu.gpr.r13 } ∧
      V' = Vst W (Y.cpu.gpr.rbp + 24#64) (toBytesLE 0#64 8)) hK hA hr
    (vc_211 (by rw [hm.2.1]; exact E.w24) fun _ => ⟨rfl, rfl, rfl⟩) ?_
  rintro j' g fl V₁ ⟨rfl, rfl, rfl⟩ U t₁ hKU hAU hrU hgU -
  have hI1 : I (Vst W (Y.cpu.gpr.rbp + 24#64) (toBytesLE 0#64 8)) :=
    E.hsep _ _ _ (Or.inr (Or.inl (by rw [hm.2.1]))) hIW
  have hmU : Fm S g0 U.cpu.gpr := by
    rw [hgU]; exact ⟨hm.1, hm.2.1, hm.2.2.1, hm.2.2.2.1, hm.2.2.2.2⟩
  have hU : U.cpu.gpr.rsp - 8 = aR S - 8 := by rw [hmU.1]
  have he : eaD U 13 0 = g0.rcx := by
    show U.cpu.gpr.get (regOf 13) + BitVec.ofNat 64 0 = _
    rw [hgU]
    show Y.cpu.gpr.r13 + 0#64 = _
    rw [hm.2.2.1]
    exact BitVec.add_zero _
  obtain ⟨cA, hinA, hAc⟩ := E.hcA _ hI1
  refine E.c.s_callM hKU hAU E.hin (lt_len (by decide)) hrU (call_225 _) (by rw [he]; exact E.fA) hinA hAc
    (by rw [he]) (by rw [hU]; exact E.hr8) ?_
  rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
  rw [hU] at hA₂
  refine E.kA _ hI1 Y₂ t₂ hK₂ hA₂ hr₂ (by rw [hg₂]; exact hU)
    ⟨by rw [hg₂]; exact kf_set hmU, by rw [hg₂]; show U.cpu.gpr.rdi = _; rw [hgU]; exact hm.2.2.1⟩ ?_
  intro Z W' t₃ hKZ hAZ hrZ hmZ hIZ
  exact from229 E hKZ hAZ hrZ hmZ hIZ

/-- From 204: `alloc->Free` (`kF`), from its return 211. -/
theorem from204 (E : Ev prof F Wl L s₀ o gev gP gE fb S g0 e₂ code₂ j₂ I) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = lza_at.add 204) (hm : Fm S g0 Y.cpu.gpr) (hIW : I W) :
    GoG prof L o gev gP gE Y t := by
  refine (c_204 prof fb).run E.c E.hfs E.hin (fun j' g' _ V' => j' = 207 ∧
      g' = { Y.cpu.gpr with rdi := Y.cpu.gpr.r13 } ∧ V' = W) hK hA hr (vc_204 fun _ => ⟨rfl, rfl, rfl⟩) ?_
  rintro j' g fl V₁ ⟨rfl, rfl, hV₁⟩ U t₁ hKU hAU hrU hgU -
  subst V₁
  have hmU : Fm S g0 U.cpu.gpr := by
    rw [hgU]; exact ⟨hm.1, hm.2.1, hm.2.2.1, hm.2.2.2.1, hm.2.2.2.2⟩
  have hU : U.cpu.gpr.rsp - 8 = aR S - 8 := by rw [hmU.1]
  have he : eaD U 13 8 = g0.rcx + 8#64 := by
    show U.cpu.gpr.get (regOf 13) + BitVec.ofNat 64 8 = _
    rw [hgU]
    show Y.cpu.gpr.r13 + 8#64 = _
    rw [hm.2.2.1]
  obtain ⟨cF, hinF, hFc⟩ := E.hcF _ hIW
  refine E.c.s_callM hKU hAU E.hin (lt_len (by decide)) hrU (call_207 _) (by rw [he]; exact E.fF) hinF hFc
    (by rw [he]) (by rw [hU]; exact E.hr8) ?_
  rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
  rw [hU] at hA₂
  refine E.kF _ hIW Y₂ t₂ hK₂ hA₂ hr₂ (by rw [hg₂]; exact hU)
    ⟨by rw [hg₂]; exact kf_set hmU, by rw [hg₂]; show U.cpu.gpr.rdi = _; rw [hgU]; exact hm.2.2.1⟩ ?_
  intro Z W' t₃ hKZ hAZ hrZ hmZ hIZ
  exact from211 E hKZ hAZ hrZ hmZ hIZ

/-- From 173: to `alloc->Free` (204) or to 238. -/
theorem from173 (E : Ev prof F Wl L s₀ o gev gP gE fb S g0 e₂ code₂ j₂ I) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = lza_at.add 173) (hm : Fm S g0 Y.cpu.gpr) (hIW : I W) :
    GoG prof L o gev gP gE Y t := by
  refine (c_173 prof fb).run E.c E.hfs E.hin (fun j' g' _ V' => V' = W ∧ Fr Y.cpu.gpr g' ∧
      (j' = 204 ∨ j' = 238)) hK hA hr
    (vc_173 (by rw [hm.2.1]; exact fun i hi => E.c.hws _ (E.w24 i hi))
      (by rw [hm.2.1]; exact fun i hi => E.c.hws _ (E.w32 i hi))
      (fun _ a _ => ⟨rfl, a, Or.inl rfl⟩) (fun _ a _ => ⟨rfl, a, Or.inr rfl⟩)) ?_
  rintro j' g fl V₁ ⟨hV₁, gf, hj⟩ U t₁ hKU hAU hrU hgU -
  subst V₁ hgU
  rcases hj with rfl | rfl
  · exact from204 E hKU hAU hrU (Fm.fr hm gf) hIW
  · exact from238 E hKU hAU hrU (Fm.fr hm gf) hIW

/-- From 108 (back from `LzmaDec_AllocateProbs2`): to 51, or `dicBufSize` and 173. -/
theorem from108 (E : Ev prof F Wl L s₀ o gev gP gE fb S g0 e₂ code₂ j₂ I) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = lza_at.add 108) (hm : Fm S g0 Y.cpu.gpr) (hIW : I W) :
    GoG prof L o gev gP gE Y t := by
  refine (c_108 prof fb).run E.c E.hfs E.hin (fun j' g' _ V' => V' = W ∧ Fr Y.cpu.gpr g' ∧
      (j' = 51 ∨ j' = 173)) hK hA hr
    (vc_108 (by rw [hm.1]; exact E.f4) (fun _ a _ => ⟨rfl, a, Or.inl rfl⟩) (fun _ a _ => ⟨rfl, a, Or.inr rfl⟩)) ?_
  rintro j' g fl V₁ ⟨hV₁, gf, hj⟩ U t₁ hKU hAU hrU hgU -
  subst V₁ hgU
  rcases hj with rfl | rfl
  · exact tail51 E hKU hAU hrU (Fm.fr hm gf) hIW
  · exact from173 E hKU hAU hrU (Fm.fr hm gf) hIW

/-- From 44 (back from `LzmaProps_Decode`): to 51, or `LzmaDec_AllocateProbs2` (`kAp`) and from its return 108. -/
theorem from44 (E : Ev prof F Wl L s₀ o gev gP gE fb S g0 e₂ code₂ j₂ I) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = lza_at.add 44) (hm : Fm S g0 Y.cpu.gpr) (hIW : I W) :
    GoG prof L o gev gP gE Y t := by
  refine (c_44 prof fb).run E.c E.hfs E.hin (fun j' g' _ V' => V' = W ∧ Fr Y.cpu.gpr g' ∧
      (j' = 51 ∨ (j' = 103 ∧ g'.rdi = Y.cpu.gpr.rbp ∧ g'.rcx = Y.cpu.gpr.r13))) hK hA hr
    (vc_44 (by rw [hm.1]; exact fun i hi => E.f0 i (Nat.lt_of_lt_of_le hi (by decide)))
      (by rw [hm.1]; exact E.f1) (fun _ a b d _ => ⟨rfl, d, Or.inr ⟨rfl, a, b⟩⟩)
      (fun _ a _ => ⟨rfl, a, Or.inl rfl⟩)) ?_
  rintro j' g fl V₁ ⟨hV₁, gf, hpost⟩ U t₁ hKU hAU hrU hgU -
  subst V₁ hgU
  have hmU := Fm.fr hm gf
  rcases hpost with rfl | ⟨rfl, gdi, gcx⟩
  · exact tail51 E hKU hAU hrU hmU hIW
  · have hU : U.cpu.gpr.rsp - 8 = aR S - 8 := by rw [hmU.1]
    obtain ⟨cL, hinL, hLc⟩ := E.hcAp
    refine E.c.s_call hKU hAU E.hin (lt_len (by decide)) hrU (call_103 _) hinL hLc tgt_103
      (by rw [hU]; exact E.hr8) ?_
    rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
    rw [hU] at hA₂
    refine E.kAp _ hIW Y₂ t₂ hK₂ hA₂ hr₂ (by rw [hg₂]; exact hU)
      ⟨by rw [hg₂]; exact kf_set hmU, by rw [hg₂]; show U.cpu.gpr.rdi = _; rw [gdi, hm.2.1],
        by rw [hg₂]; show U.cpu.gpr.rcx = _; rw [gcx, hm.2.2.1]⟩ ?_
    intro Z W' t₃ hKZ hAZ hrZ hmZ hIZ
    exact from108 E hKZ hAZ hrZ hmZ hIZ

end Runs

variable {prof : Profile} {F : Footprint} {Wl : List Rgn} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {X : State} {t : Nat} {V : Addr → Byte}

/-- `LzmaDec_Allocate (p, props, propsSize, alloc)` (`p` = `rdi`, `alloc` = `rcx`) from its entry, `fb` the `fs`
base, `I` an invariant of the bytes: the pushes' slots, the guard's slot, `propNew` and the calls' return address
slot in what the run may store into, the return address and the guard at `fs:0x28` readable; `p->prop`, `p->dic`,
`p->dicBufSize` in what the run may store into, `alloc->Alloc` and `alloc->Free` readable. `I` gives the stack
(`hI`) and the code at `alloc->Free` and `alloc->Alloc` (`hcF`, `hcA`), and the stores into `p` keep it (`hsep`).
The callees: `LzmaProps_Decode (&propNew, props, propsSize)` (`k1`), `LzmaDec_AllocateProbs2 (p, &propNew, alloc)`
(`kAp`), `alloc->Free (alloc, p->dic)` (`kF`), `alloc->Alloc (alloc, dicBufSize)` (`kA`), `LzmaDec_FreeProbs (p,
alloc)` (`kP`), each from its return with the frame and `I`. At the return address (`kr`): `rsp` 8 above the entry's,
the callee-saved registers as they were, bytes with `I`. -/
theorem lza_ok {fb : Addr} {I : (Addr → Byte) → Prop} {e₂ : Addr} {code₂ : List Byte} {j₂ : Nat}
    (c : Seg prof F Wl L s₀ o) (hfs : s₀.cpu.seg.fsBase = fb) (hin : CodeIn L lza_at lza)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = lza_at)
    (hcl : ∀ i < 8, Foot F.data (Addr.add (fb + 40#64) i))
    (hs1 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8) i))
    (hs2 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8 - 8) i))
    (hs3 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8 - 8 - 8) i))
    (hs4 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8 - 8 - 8 - 8) i))
    (hw : ∀ i < 8, Foot Wl (Addr.add (aR X.cpu.gpr.rsp + 8#64) i))
    (hw0 : ∀ i < 8, Foot Wl (Addr.add (aR X.cpu.gpr.rsp) i))
    (hr8 : ∀ i < 8, Foot Wl (Addr.add (aR X.cpu.gpr.rsp - 8) i))
    (hl : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsp i))
    (hin₂ : CodeIn L e₂ code₂) (h₂ : j₂ < code₂.length)
    (w0 : ∀ i < 8, Foot Wl (Addr.add X.cpu.gpr.rdi i))
    (w24 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rdi + 24#64) i))
    (w32 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rdi + 32#64) i))
    (fF : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rcx + 8#64) i))
    (fA : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rcx i))
    (hI : ∀ W, I W → Stk fb W X.cpu.gpr.rsp X.cpu.gpr (e₂.add j₂))
    (hsep : ∀ (W : Addr → Byte) (a v : BitVec 64),
      (a = X.cpu.gpr.rdi ∨ a = X.cpu.gpr.rdi + 24#64 ∨ a = X.cpu.gpr.rdi + 32#64) → I W →
      I (Vst W a (toBytesLE v 8)))
    (hcF : ∀ W, I W → ∃ code : List Byte, CodeIn L rdq(W, X.cpu.gpr.rcx + 8#64) code ∧ 0 < code.length)
    (hcA : ∀ W, I W → ∃ code : List Byte, CodeIn L rdq(W, X.cpu.gpr.rcx) code ∧ 0 < code.length)
    (hcPd : ∃ code : List Byte, CodeIn L 0x42bea0#64 code ∧ 0 < code.length)
    (hcAp : ∃ code : List Byte, CodeIn L 0x42be00#64 code ∧ 0 < code.length)
    (hcP : ∃ code : List Byte, CodeIn L 0x42bde0#64 code ∧ 0 < code.length)
    (k1 : KC prof F Wl L s₀ o gev gP gE X.cpu.gpr.rsp X.cpu.gpr I 0x42bea0#64 44 (V0 fb V X.cpu.gpr)
      (fun g => Kf X.cpu.gpr g ∧ g.rdi = aR X.cpu.gpr.rsp))
    (kAp : ∀ W, I W → KC prof F Wl L s₀ o gev gP gE X.cpu.gpr.rsp X.cpu.gpr I 0x42be00#64 108 W
      (fun g => Kf X.cpu.gpr g ∧ g.rdi = X.cpu.gpr.rdi ∧ g.rcx = X.cpu.gpr.rcx))
    (kF : ∀ W, I W → KC prof F Wl L s₀ o gev gP gE X.cpu.gpr.rsp X.cpu.gpr I rdq(W, X.cpu.gpr.rcx + 8#64) 211 W
      (fun g => Kf X.cpu.gpr g ∧ g.rdi = X.cpu.gpr.rcx))
    (kA : ∀ W, I W → KC prof F Wl L s₀ o gev gP gE X.cpu.gpr.rsp X.cpu.gpr I rdq(W, X.cpu.gpr.rcx) 229 W
      (fun g => Kf X.cpu.gpr g ∧ g.rdi = X.cpu.gpr.rcx))
    (kP : ∀ W, I W → KC prof F Wl L s₀ o gev gP gE X.cpu.gpr.rsp X.cpu.gpr I 0x42bde0#64 289 W
      (fun g => Kf X.cpu.gpr g ∧ g.rdi = X.cpu.gpr.rdi ∧ g.rsi = X.cpu.gpr.rcx))
    (kr : ∀ (W : Addr → Byte) (Z' : State) (t' : Nat), KeptW Wl s₀ Z' → Agree F Z'.proc.mm.mem W →
      Z'.cpu.rip = e₂.add j₂ → Z'.cpu.gpr.rsp = X.cpu.gpr.rsp + 8 → KS X.cpu.gpr Z'.cpu.gpr → I W →
      GoG prof L o gev gP gE Z' t') :
    GoG prof L o gev gP gE X t := by
  have f0 : ∀ i < 8, Foot F.data (Addr.add (aR X.cpu.gpr.rsp) i) := fun i hi => c.hws _ (hw0 i hi)
  have E : Ev prof F Wl L s₀ o gev gP gE fb X.cpu.gpr.rsp X.cpu.gpr e₂ code₂ j₂ I :=
    { c := c, hfs := hfs, hin := hin, hin₂ := hin₂, h₂ := h₂, hI := hI, hsep := hsep, hcl := hcl,
      fg := fun i hi => c.hws _ (hw i hi), f0 := f0,
      f1 := Cpt.off_ft f0 1 rfl (by decide), f4 := Cpt.off_ft f0 4 rfl (by decide),
      fb32 := fun i hi => c.hws _ (hs4 i hi), fb24 := fun i hi => c.hws _ (hs3 i hi),
      fb16 := fun i hi => c.hws _ (hs2 i hi), fb8 := fun i hi => c.hws _ (hs1 i hi),
      hl := hl, hr8 := hr8, w0 := w0, w24 := w24, w32 := w32, fF := fF, fA := fA, hcF := hcF, hcA := hcA,
      hcAp := hcAp, hcP := hcP, kAp := kAp, kF := kF, kA := kA, kP := kP, kr := kr }
  -- the prologue, to the first `call`
  refine (c_0 prof fb).run c hfs hin (fun j' g' _ V' => j' = 39 ∧ V' = V0 fb V X.cpu.gpr ∧
      g'.rsp = aR X.cpu.gpr.rsp ∧ g'.rdi = aR X.cpu.gpr.rsp ∧ g'.rbp = X.cpu.gpr.rdi ∧ g'.r13 = X.cpu.gpr.rcx ∧
      g'.r14 = X.cpu.gpr.r14 ∧ g'.r15 = X.cpu.gpr.r15) hK hA (by rw [addr_add_zero]; exact hrip)
    (vc_0 rfl hs1 hs2 hs3 hs4 hcl hw fun _ a b d e _ _ f g _ => ⟨rfl, rfl, a, b, d, e, f, g⟩) ?_
  rintro j' g fl V₁ ⟨rfl, hV₁, gs, gdi, gp, g13, g14, g15⟩ Y t₁ hKY hAY hrY hgY -
  subst V₁ hgY
  have hY : Y.cpu.gpr.rsp - 8 = aR X.cpu.gpr.rsp - 8 := by rw [gs]
  obtain ⟨cD, hinD, hD⟩ := hcPd
  refine c.s_call hKY hAY hin (lt_len (by decide)) hrY (call_39 _) hinD hD tgt_39 (by rw [hY]; exact hr8) ?_
  rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
  rw [hY] at hA₂
  refine k1 Y₂ t₂ hK₂ hA₂ hr₂ (by rw [hg₂]; exact hY)
    ⟨by rw [hg₂]; exact ⟨gp, g13, g14, g15⟩, by rw [hg₂]; exact gdi⟩ ?_
  -- back from `LzmaProps_Decode`, at 44
  intro Z W t₃ hKZ hAZ hrZ hmZ hIZ
  exact from44 E hKZ hAZ hrZ hmZ hIZ

end FV7z.Lza
