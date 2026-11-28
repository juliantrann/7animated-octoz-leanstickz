import FV7z.Anc.Cuts
import FV7z.Dnw.Blocks1
import FV7z.Api.Blocks1
import FV7z.Lemmas.LeafRet
/-!
# `AddNameToCensor` (PLAN.md §M, M1)

7-Zip 26.06's `AddNameToCensor (NWildcard::CCensor &censor, const CNameOption &nop, const UString &name)` (static)
at `0x5a66e0` in `7zzs` (`CPP/7zip/UI/Common/ArchiveCommandLine.cpp`; `objdump -d`), `S` the stack pointer at the
entry: `push r12; mov r12, rdx; push rbp; mov rbp, rdi; push rbx; mov rbx, rsi; sub rsp, 0x10`, `edx` = the
wildcard mode (`[rsi + 4]`), the stack guard (`fs:0x28`) stored at `aR S + 8`; mode 0: `eax` = 1, mode 1: the `call`
(55) of `DoesNameContainWildcard (name)` (`Dnw.dnw_at`), else `eax` = 0 (to 60); the `CCensorPathProps` at
`aR S + 5` (`al`, then the two bytes at `nop + 1`), the `call` (87) of `censor.AddPreItem (nop.Include, name,
props)` (`Api.api_at`); the stack guard checked (92), `add rsp, 0x10; pop rbx; pop rbp; pop r12; ret` (116).

The callees are hypotheses, as in `FV7z/Smd/Holds.lean` (`KC`). The bytes stored at 60 (the props) are not
tracked: `AddPreItem` is a continuation for any bytes at its entry (`k2`), from its return the stack as it was
(`Stk`: the saved registers, the return address, the guard), so `jne 117` is not taken. Not covered:
`__stack_chk_fail` (117).

- `aR`, `Sv`, `V0`, `Fr`, `Fm`, `Kf`, `KS`, `Stk`, `KC`: the frame, bytes, kept registers, the stack, contracts.
- `vc_0`, `vc_60`, `vc_92`: the pieces' verification conditions.
- `tail92`, `from60`: the runs from those offsets; `anc_ok`: the function.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Anc
set_option linter.unusedVariables false

/-! ## The instructions outside the blocks -/

/-- The `call` of `DoesNameContainWildcard`. -/
def pc1 : List Byte := [0xe8, 0x24, 0xc2, 0xea, 0xff]
theorem pc1_0 : ∀ feat, Dec feat pc1 0 (FV7z.mk .call 64 [.rel 18446744073708159524] 5) := by intro feat f; rfl
theorem wc_55 : pc1 <+: anc.drop 55 := by decide +kernel
theorem call_55 (feat : Features) : Dec feat anc 55 (FV7z.mk .call 64 [.rel 18446744073708159524] 5) :=
  Dec.shift (j := 55) (k := 0) (pc1_0 feat) wc_55 (Nat.zero_le _)
theorem tgt_55 : anc_at.add (55 + 5) + BitVec.ofNat 64 18446744073708159524 = Dnw.dnw_at := by decide

/-- The `call` of `CCensor::AddPreItem`. -/
def pc2 : List Byte := [0xe8, 0x14, 0xcf, 0xea, 0xff]
theorem pc2_0 : ∀ feat, Dec feat pc2 0 (FV7z.mk .call 64 [.rel 18446744073708162836] 5) := by intro feat f; rfl
theorem wc_87 : pc2 <+: anc.drop 87 := by decide +kernel
theorem call_87 (feat : Features) : Dec feat anc 87 (FV7z.mk .call 64 [.rel 18446744073708162836] 5) :=
  Dec.shift (j := 87) (k := 0) (pc2_0 feat) wc_87 (Nat.zero_le _)
theorem tgt_87 : anc_at.add (87 + 5) + BitVec.ofNat 64 18446744073708162836 = Api.api_at := by decide

/-- The `ret`. -/
def pret : List Byte := [0xc3]
theorem pret_0 : ∀ feat, Dec feat pret 0 (FV7z.mk .ret 64 [] 1) := by intro feat f; rfl
theorem w_116 : pret <+: anc.drop 116 := by decide +kernel
theorem ret_116 (feat : Features) : Dec feat anc 116 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 116) (k := 0) (pret_0 feat) w_116 (Nat.zero_le _)

/-! ## The frame -/

/-- The stack pointer after the three `push`es and `sub rsp, 0x10`. -/
abbrev aR (S : Addr) : Addr := S - 8 - 8 - 8 - 16#64

theorem e16 (S : Addr) : aR S + 16#64 = S - 8 - 8 - 8 := by show S - 8 - 8 - 8 - 16#64 + 16#64 = _; bv_omega
theorem e24 (S : Addr) : aR S + 16#64 + 8 = S - 8 - 8 := by show S - 8 - 8 - 8 - 16#64 + 16#64 + 8 = _; bv_omega
theorem e32 (S : Addr) : aR S + 16#64 + 8 + 8 = S - 8 := by
  show S - 8 - 8 - 8 - 16#64 + 16#64 + 8 + 8 = _
  bv_omega
theorem e40 (S : Addr) : aR S + 16#64 + 8 + 8 + 8 = S := by
  show S - 8 - 8 - 8 - 16#64 + 16#64 + 8 + 8 + 8 = _
  bv_omega

/-- The bytes after the three `push`es: `r12`, `rbp`, `rbx` below the stack pointer. -/
abbrev Sv (V : Addr → Byte) (g : Gprs) : Addr → Byte :=
  Vst (Vst (Vst V (g.rsp - 8) (toBytesLE g.r12 8)) (g.rsp - 8 - 8) (toBytesLE g.rbp 8)) (g.rsp - 8 - 8 - 8)
    (toBytesLE g.rbx 8)

/-- The bytes from 43 on: the three registers pushed, the stack guard stored. -/
abbrev V0 (fb : Addr) (V : Addr → Byte) (g : Gprs) : Addr → Byte :=
  Vst (Sv V g) (aR g.rsp + 8#64) (toBytesLE rdq(Sv V g, fb + 40#64) 8)

/-- What a piece keeps: `rsp`, `rbp`, `rbx`, `r12`–`r15`. -/
abbrev Fr (g g' : Gprs) : Prop :=
  g'.rsp = g.rsp ∧ g'.rbp = g.rbp ∧ g'.rbx = g.rbx ∧ g'.r12 = g.r12 ∧ g'.r13 = g.r13 ∧ g'.r14 = g.r14 ∧
    g'.r15 = g.r15

/-- The frame from 43 on: `rsp` = `aR S`, `rbp` = `censor`, `rbx` = `nop`, `r12` = `name`, `r13`–`r15` as at the
entry (`g0`). -/
abbrev Fm (S : Addr) (g0 g : Gprs) : Prop :=
  g.rsp = aR S ∧ g.rbp = g0.rdi ∧ g.rbx = g0.rsi ∧ g.r12 = g0.rdx ∧ g.r13 = g0.r13 ∧ g.r14 = g0.r14 ∧
    g.r15 = g0.r15

/-- `Fm` but `rsp`: what a callee is given. -/
abbrev Kf (g0 g : Gprs) : Prop :=
  g.rbp = g0.rdi ∧ g.rbx = g0.rsi ∧ g.r12 = g0.rdx ∧ g.r13 = g0.r13 ∧ g.r14 = g0.r14 ∧ g.r15 = g0.r15

/-- The callee-saved registers as at the entry. -/
abbrev KS (g0 g : Gprs) : Prop :=
  g.rbx = g0.rbx ∧ g.rbp = g0.rbp ∧ g.r12 = g0.r12 ∧ g.r13 = g0.r13 ∧ g.r14 = g0.r14 ∧ g.r15 = g0.r15

theorem Fm.fr {S : Addr} {g0 g g' : Gprs} (h : Fm S g0 g) (h' : Fr g g') : Fm S g0 g' :=
  ⟨h'.1.trans h.1, h'.2.1.trans h.2.1, h'.2.2.1.trans h.2.2.1, h'.2.2.2.1.trans h.2.2.2.1,
    h'.2.2.2.2.1.trans h.2.2.2.2.1, h'.2.2.2.2.2.1.trans h.2.2.2.2.2.1, h'.2.2.2.2.2.2.trans h.2.2.2.2.2.2⟩

theorem kf_set {S : Addr} {g0 g : Gprs} {x : Addr} (h : Fm S g0 g) : Kf g0 (g.set 4 x) :=
  ⟨h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩

/-- The stack from the return of `AddPreItem` (`fb` the `fs` base, `ra` the return address): the saved registers,
the return address, the stack guard as at `fs:0x28`. -/
abbrev Stk (fb : Addr) (W : Addr → Byte) (S : Addr) (g0 : Gprs) (ra : Addr) : Prop :=
  rdq(W, S - 8) = g0.r12 ∧ rdq(W, S - 8 - 8) = g0.rbp ∧ rdq(W, S - 8 - 8 - 8) = g0.rbx ∧ rdq(W, S) = ra ∧
    rdq(W, aR S + 8#64) = rdq(W, fb + 40#64)

/-- A callee from the `call` before `j` (entry `ent`, the bytes `W`, the registers `A`): at its entry, and from its
return at `j` with the frame, `N` and `P`, the run goes on to the goal. -/
def KC (prof : Profile) (F : Footprint) (Wl : List Rgn) (L : List (Addr × List Byte)) (s₀ : State) (o : Oracle)
    (gev : List Event) (gP : State → Nat → List Event → Prop) (gE : Outcome → List Event → Prop)
    (S : Addr) (g0 : Gprs) (ent : Addr) (j : Nat) (W : Addr → Byte) (A : Gprs → Prop)
    (N P : State → (Addr → Byte) → Prop) : Prop :=
  ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y →
    Agree F Y.proc.mm.mem (Vst W (aR S - 8) (toBytesLE (anc_at.add j) 8)) →
    Y.cpu.rip = ent → Y.cpu.gpr.rsp = aR S - 8 → A Y.cpu.gpr →
    (∀ (Z : State) (W' : Addr → Byte) (t'' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem W' →
      Z.cpu.rip = anc_at.add j → Fm S g0 Z.cpu.gpr → N Z W' → P Z W' → GoG prof L o gev gP gE Z t'') →
    GoG prof L o gev gP gE Y t'

/-! ## The pieces -/

variable {F : Footprint} {Wl : List Rgn}

/-- The pushes, the frame, the mode loaded, the stack guard stored; to 60 (mode 0, or not 1) or to the `call` of
`DoesNameContainWildcard` (55, mode 1, `rdi` = `name`). The guard's value is named (`cn`). -/
theorem vc_0 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} {cn : BitVec 64}
    (hcn : rdq(Sv V g, fb + 40#64) = cn)
    (hs1 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8) i)) (hs2 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8) i))
    (hs3 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8 - 8) i))
    (hcl : ∀ i < 8, Foot F.data (Addr.add (fb + 40#64) i)) (f4 : ∀ i < 4, Foot F.data (Addr.add (g.rsi + 4#64) i))
    (hw : ∀ i < 8, Foot Wl (Addr.add (aR g.rsp + 8#64) i))
    (h60 : ∀ g', g'.rsp = aR g.rsp → g'.rbp = g.rdi → g'.rbx = g.rsi → g'.r12 = g.rdx → g'.r13 = g.r13 →
      g'.r14 = g.r14 → g'.r15 = g.r15 →
      ∀ fl, Q 60 g' fl (Vst (Sv V g) (aR g.rsp + 8#64) (toBytesLE cn 8)))
    (h55 : ∀ g', g'.rsp = aR g.rsp → g'.rbp = g.rdi → g'.rbx = g.rsi → g'.r12 = g.rdx → g'.r13 = g.r13 →
      g'.r14 = g.r14 → g'.r15 = g.r15 → g'.rdi = g.rdx →
      ∀ fl, Q 55 g' fl (Vst (Sv V g) (aR g.rsp + 8#64) (toBytesLE cn 8))) :
    W_0 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [aR, Sv] at hcn hs1 hs2 hs3 f4 hw h60 h55 ⊢
  wpx [W_0, W_45, W_52, o0, o1, o2, Op.ldf, hcn]
  all_goals repeat' (first
    | refine h60 _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ _
    | refine h55 _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ _
    | with_reducible rfl
    | with_reducible exact hs1
    | with_reducible exact hs2
    | with_reducible exact hs3
    | with_reducible exact hcl
    | with_reducible exact f4
    | with_reducible exact hw
    | apply And.intro
    | intro _)

/-- The props stored at `rsp + 5`, `esi` = `nop.Include`, `rcx` = `rsp + 5`, `rdx` = `r12`, `rdi` = `rbp`, to the
`call` of `AddPreItem` (the bytes not tracked). -/
theorem vc_60 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (f0 : ∀ i < 1, Foot F.data (Addr.add g.rbx i)) (f1 : ∀ i < 2, Foot F.data (Addr.add (g.rbx + 1#64) i))
    (w5 : ∀ i < 1, Foot Wl (Addr.add (g.rsp + 5#64) i)) (w6 : ∀ i < 2, Foot Wl (Addr.add (g.rsp + 6#64) i))
    (h : ∀ g' W, g'.rdi = g.rbp → g'.rdx = g.r12 → g'.rcx = g.rsp + 5#64 → Fr g g' → ∀ fl, Q 87 g' fl W) :
    W_60 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at f0 f1 w5 w6 h ⊢
  wpx [W_60, o3]
  all_goals repeat' (first
    | refine h _ _ ?_ ?_ ?_ ?_ _
    | with_reducible rfl
    | with_reducible exact f0
    | with_reducible exact f1
    | with_reducible exact w5
    | with_reducible exact w6
    | apply And.intro
    | intro _)

/-- The stack guard checked (as at `fs:0x28`: `jne` not taken), `add rsp, 0x10; pop rbx; pop rbp; pop r12` to the
`ret`. -/
theorem vc_92 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (hc : rdq(V, g.rsp + 8#64) = rdq(V, fb + 40#64)) (f8 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8#64) i))
    (fcl : ∀ i < 8, Foot F.data (Addr.add (fb + 40#64) i))
    (f16 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 16#64) i))
    (f24 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 16#64 + 8) i))
    (f32 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 16#64 + 8 + 8) i))
    (h : ∀ g', g'.rsp = g.rsp + 16#64 + 8 + 8 + 8 → g'.rbx = rdq(V, g.rsp + 16#64) →
      g'.rbp = rdq(V, g.rsp + 16#64 + 8) → g'.r12 = rdq(V, g.rsp + 16#64 + 8 + 8) → g'.r13 = g.r13 →
      g'.r14 = g.r14 → g'.r15 = g.r15 → ∀ fl, Q 116 g' fl V) :
    W_92 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hc f8 f16 f24 f32 h ⊢
  have z0 : ((0#64 : BitVec 64) == 0) = true := by decide
  wpx [W_92, W_108, o4, o5, Op.xormf, hc, BitVec.xor_self, z0, decide_true, Bool.not_true, Bool.false_eq_true,
    false_implies, eq_self_iff_true, true_implies]
  all_goals repeat' (first
    | refine h _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ _
    | with_reducible rfl
    | with_reducible exact f8
    | with_reducible exact fcl
    | with_reducible exact f16
    | with_reducible exact f24
    | with_reducible exact f32
    | apply And.intro
    | intro _)

/-! ## The runs -/

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {X : State} {t : Nat} {V : Addr → Byte} {e₂ : Addr} {code₂ : List Byte} {j₂ : Nat}

/-- From 92 (the frame, the stack `Stk`) to the return address `e₂.add j₂`. -/
theorem tail92 {fb : Addr} {W : Addr → Byte} {S : Addr} {g0 : Gprs} {Y : State} (c : Seg prof F Wl L s₀ o)
    (hfs : s₀.cpu.seg.fsBase = fb) (hin : CodeIn L anc_at anc) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = anc_at.add 92) (hm : Fm S g0 Y.cpu.gpr)
    (hst : Stk fb W S g0 (e₂.add j₂)) (hcl : ∀ i < 8, Foot F.data (Addr.add (fb + 40#64) i))
    (f8 : ∀ i < 8, Foot F.data (Addr.add (aR S + 8#64) i)) (f1 : ∀ i < 8, Foot F.data (Addr.add (S - 8) i))
    (f2 : ∀ i < 8, Foot F.data (Addr.add (S - 8 - 8) i)) (f3 : ∀ i < 8, Foot F.data (Addr.add (S - 8 - 8 - 8) i))
    (hl : ∀ i < 8, Foot F.data (Addr.add S i)) (hin₂ : CodeIn L e₂ code₂) (h₂ : j₂ < code₂.length)
    (k : ∀ (Z' : State) (t' : Nat), KeptW Wl s₀ Z' → Agree F Z'.proc.mm.mem W → Z'.cpu.rip = e₂.add j₂ →
      Z'.cpu.gpr.rsp = S + 8 → KS g0 Z'.cpu.gpr → GoG prof L o gev gP gE Z' t') :
    GoG prof L o gev gP gE Y t := by
  obtain ⟨ms, mp, mb, m12, m13, m14, m15⟩ := hm
  obtain ⟨s1, s2, s3, s4, s5⟩ := hst
  refine (c_92 prof fb).run c hfs hin (fun j' g' _ V' => j' = 116 ∧ V' = W ∧
      g'.rsp = Y.cpu.gpr.rsp + 16#64 + 8 + 8 + 8 ∧ g'.rbx = rdq(W, Y.cpu.gpr.rsp + 16#64) ∧
      g'.rbp = rdq(W, Y.cpu.gpr.rsp + 16#64 + 8) ∧ g'.r12 = rdq(W, Y.cpu.gpr.rsp + 16#64 + 8 + 8) ∧
      g'.r13 = Y.cpu.gpr.r13 ∧ g'.r14 = Y.cpu.gpr.r14 ∧ g'.r15 = Y.cpu.gpr.r15) hK hA hr
    (vc_92 (by rw [ms]; exact s5) (by rw [ms]; exact f8) hcl (by rw [ms, e16]; exact f3)
      (by rw [ms, e24]; exact f2) (by rw [ms, e32]; exact f1)
      fun _ a b d e f g h _ => ⟨rfl, rfl, a, b, d, e, f, g, h⟩) ?_
  rintro j' g fl V₁ ⟨rfl, hV₁, gs, gx, gb, g12, g13, g14, g15⟩ U t₁ hKU hAU hrU hgU -
  subst V₁ hgU
  have hsU : U.cpu.gpr.rsp = S := by rw [gs, ms]; exact e40 S
  have r1 : rdq(W, Y.cpu.gpr.rsp + 16#64) = g0.rbx := by rw [ms, e16]; exact s3
  have r2 : rdq(W, Y.cpu.gpr.rsp + 16#64 + 8) = g0.rbp := by rw [ms, e24]; exact s2
  have r3 : rdq(W, Y.cpu.gpr.rsp + 16#64 + 8 + 8) = g0.r12 := by rw [ms, e32]; exact s1
  refine c.s_ret hKU hAU hin (lt_len (by decide)) hrU (ret_116 _) (by rw [hsU]; exact hl) hin₂ h₂
    (by rw [hsU]; exact s4) ?_
  rintro Z' t₂ hKZ' hAZ' ⟨hrZ', hgZ'⟩
  refine k Z' t₂ hKZ' hAZ' hrZ' ?_ ?_
  · rw [hgZ']
    show U.cpu.gpr.rsp + 8 = _
    rw [hsU]
  · rw [hgZ']
    exact ⟨gx.trans r1, gb.trans r2, g12.trans r3, g13.trans m13, g14.trans m14, g15.trans m15⟩

/-- What the runs go on to: at the return address, `rsp` 8 above the entry's, the callee-saved registers as they
were, the bytes from `AddPreItem` (`P2`). -/
abbrev Kr (prof : Profile) (F : Footprint) (Wl : List Rgn) (L : List (Addr × List Byte)) (s₀ : State) (o : Oracle)
    (gev : List Event) (gP : State → Nat → List Event → Prop) (gE : Outcome → List Event → Prop)
    (S : Addr) (g0 : Gprs) (e₂ : Addr) (j₂ : Nat) (P2 : State → (Addr → Byte) → Prop) : Prop :=
  ∀ (W' : Addr → Byte) (Z' : State) (t' : Nat), KeptW Wl s₀ Z' → Agree F Z'.proc.mm.mem W' →
    Z'.cpu.rip = e₂.add j₂ → Z'.cpu.gpr.rsp = S + 8 → KS g0 Z'.cpu.gpr → (∃ Z₂, P2 Z₂ W') →
    GoG prof L o gev gP gE Z' t'

/-- From 60 (the bytes `W`): the props, `AddPreItem` (`k2`, for any bytes at its entry), from its return 92. -/
theorem from60 {fb : Addr} {W : Addr → Byte} {S : Addr} {g0 : Gprs} {Y : State}
    {P2 : State → (Addr → Byte) → Prop} (c : Seg prof F Wl L s₀ o) (hfs : s₀.cpu.seg.fsBase = fb)
    (hin : CodeIn L anc_at anc) (hinA : CodeIn L Api.api_at Api.api)
    (hK : KeptW Wl s₀ Y) (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = anc_at.add 60) (hm : Fm S g0 Y.cpu.gpr)
    (hcl : ∀ i < 8, Foot F.data (Addr.add (fb + 40#64) i))
    (hs1 : ∀ i < 8, Foot Wl (Addr.add (S - 8) i)) (hs2 : ∀ i < 8, Foot Wl (Addr.add (S - 8 - 8) i))
    (hs3 : ∀ i < 8, Foot Wl (Addr.add (S - 8 - 8 - 8) i)) (hw8 : ∀ i < 8, Foot Wl (Addr.add (aR S + 8#64) i))
    (w5 : ∀ i < 1, Foot Wl (Addr.add (aR S + 5#64) i)) (w6 : ∀ i < 2, Foot Wl (Addr.add (aR S + 6#64) i))
    (f0 : ∀ i < 1, Foot F.data (Addr.add g0.rsi i)) (f1 : ∀ i < 2, Foot F.data (Addr.add (g0.rsi + 1#64) i))
    (hr8 : ∀ i < 8, Foot Wl (Addr.add (aR S - 8) i))
    (hl : ∀ i < 8, Foot F.data (Addr.add S i)) (hin₂ : CodeIn L e₂ code₂) (h₂ : j₂ < code₂.length)
    (k2 : ∀ W₂ : Addr → Byte, KC prof F Wl L s₀ o gev gP gE S g0 Api.api_at 92 W₂
      (fun g => Kf g0 g ∧ g.rdi = g0.rdi ∧ g.rdx = g0.rdx ∧ g.rcx = aR S + 5#64)
      (fun _ W' => Stk fb W' S g0 (e₂.add j₂)) P2)
    (k : Kr prof F Wl L s₀ o gev gP gE S g0 e₂ j₂ P2) :
    GoG prof L o gev gP gE Y t := by
  have f8 : ∀ i < 8, Foot F.data (Addr.add (aR S + 8#64) i) := fun i hi => c.hws _ (hw8 i hi)
  have g1 : ∀ i < 8, Foot F.data (Addr.add (S - 8) i) := fun i hi => c.hws _ (hs1 i hi)
  have g2 : ∀ i < 8, Foot F.data (Addr.add (S - 8 - 8) i) := fun i hi => c.hws _ (hs2 i hi)
  have g3 : ∀ i < 8, Foot F.data (Addr.add (S - 8 - 8 - 8) i) := fun i hi => c.hws _ (hs3 i hi)
  refine (c_60 prof fb).run c hfs hin (fun j' g' _ V' => j' = 87 ∧ g'.rdi = Y.cpu.gpr.rbp ∧
      g'.rdx = Y.cpu.gpr.r12 ∧ g'.rcx = Y.cpu.gpr.rsp + 5#64 ∧ Fr Y.cpu.gpr g') hK hA hr
    (vc_60 (by rw [hm.2.2.1]; exact f0) (by rw [hm.2.2.1]; exact f1) (by rw [hm.1]; exact w5)
      (by rw [hm.1]; exact w6) fun _ _ a b d e _ => ⟨rfl, a, b, d, e⟩) ?_
  rintro j' g fl V₁ ⟨rfl, gdi, gdx, gcx, gf⟩ U t₁ hKU hAU hrU hgU -
  subst hgU
  have hmU := Fm.fr hm gf
  have hU : U.cpu.gpr.rsp - 8 = aR S - 8 := by rw [hmU.1]
  refine c.s_call hKU hAU hin (lt_len (by decide)) hrU (call_87 _) hinA (Api.lt_len (j := 0) (by decide)) tgt_87
    (by rw [hU]; exact hr8) ?_
  rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
  rw [hU] at hA₂
  refine k2 V₁ Y₂ t₂ hK₂ hA₂ hr₂ (by rw [hg₂]; exact hU)
    ⟨by rw [hg₂]; exact kf_set hmU, by rw [hg₂]; show U.cpu.gpr.rdi = _; rw [gdi, hm.2.1],
      by rw [hg₂]; show U.cpu.gpr.rdx = _; rw [gdx, hm.2.2.2.1],
      by rw [hg₂]; show U.cpu.gpr.rcx = _; rw [gcx, hm.1]⟩ ?_
  intro Z₂ W₂ t₃ hKZ hAZ hrZ hmZ hstZ hP2
  exact tail92 c hfs hin hKZ hAZ hrZ hmZ hstZ hcl f8 g1 g2 g3 hl hin₂ h₂ fun Z' t' a b d e f =>
    k W₂ Z' t' a b d e f ⟨Z₂, hP2⟩

/-- `AddNameToCensor (censor, nop, name)` (`rdi`, `rsi`, `rdx`) from its entry, `S` = `X`'s `rsp`, `fb` the `fs`
base: the pushes' slots, the guard's slot, the props' three bytes and the calls' return address slot in what the run
may store into; the return address, the guard at `fs:0x28`, `nop`'s first three bytes and its mode (`nop + 4`)
readable. The callees: `DoesNameContainWildcard (name)` (`k1`, mode 1 only), `censor.AddPreItem (…)` (`k2`, from its
return the stack `Stk` and `P2`). At the return address (`kr`): `rsp` 8 above the entry's, the callee-saved
registers as they were, the bytes from `AddPreItem`. -/
theorem anc_ok {fb : Addr} {P1 P2 : State → (Addr → Byte) → Prop}
    (c : Seg prof F Wl L s₀ o) (hfs : s₀.cpu.seg.fsBase = fb) (hin : CodeIn L anc_at anc)
    (hinD : CodeIn L Dnw.dnw_at Dnw.dnw) (hinA : CodeIn L Api.api_at Api.api)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = anc_at)
    (hcl : ∀ i < 8, Foot F.data (Addr.add (fb + 40#64) i))
    (hs1 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8) i))
    (hs2 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8 - 8) i))
    (hs3 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8 - 8 - 8) i))
    (hw8 : ∀ i < 8, Foot Wl (Addr.add (aR X.cpu.gpr.rsp + 8#64) i))
    (w5 : ∀ i < 1, Foot Wl (Addr.add (aR X.cpu.gpr.rsp + 5#64) i))
    (w6 : ∀ i < 2, Foot Wl (Addr.add (aR X.cpu.gpr.rsp + 6#64) i))
    (f0 : ∀ i < 1, Foot F.data (Addr.add X.cpu.gpr.rsi i))
    (f1 : ∀ i < 2, Foot F.data (Addr.add (X.cpu.gpr.rsi + 1#64) i))
    (f4 : ∀ i < 4, Foot F.data (Addr.add (X.cpu.gpr.rsi + 4#64) i))
    (hr8 : ∀ i < 8, Foot Wl (Addr.add (aR X.cpu.gpr.rsp - 8) i))
    (hl : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsp i)) (hin₂ : CodeIn L e₂ code₂)
    (h₂ : j₂ < code₂.length)
    (k1 : KC prof F Wl L s₀ o gev gP gE X.cpu.gpr.rsp X.cpu.gpr Dnw.dnw_at 60 (V0 fb V X.cpu.gpr)
      (fun g => Kf X.cpu.gpr g ∧ g.rdi = X.cpu.gpr.rdx) (fun _ _ => True) P1)
    (k2 : ∀ W₂ : Addr → Byte, KC prof F Wl L s₀ o gev gP gE X.cpu.gpr.rsp X.cpu.gpr Api.api_at 92 W₂
      (fun g => Kf X.cpu.gpr g ∧ g.rdi = X.cpu.gpr.rdi ∧ g.rdx = X.cpu.gpr.rdx ∧ g.rcx = aR X.cpu.gpr.rsp + 5#64)
      (fun _ W' => Stk fb W' X.cpu.gpr.rsp X.cpu.gpr (e₂.add j₂)) P2)
    (kr : Kr prof F Wl L s₀ o gev gP gE X.cpu.gpr.rsp X.cpu.gpr e₂ j₂ P2) :
    GoG prof L o gev gP gE X t := by
  -- the prologue, to 60 or to the `call` of `DoesNameContainWildcard`
  refine (c_0 prof fb).run c hfs hin (fun j' g' _ V' => V' = V0 fb V X.cpu.gpr ∧
      Fm X.cpu.gpr.rsp X.cpu.gpr g' ∧ (j' = 60 ∨ (j' = 55 ∧ g'.rdi = X.cpu.gpr.rdx))) hK hA
    (by rw [addr_add_zero]; exact hrip)
    (vc_0 rfl hs1 hs2 hs3 hcl f4 hw8 (fun _ a b d e f g h _ => ⟨rfl, ⟨a, b, d, e, f, g, h⟩, Or.inl rfl⟩)
      fun _ a b d e f g h i _ => ⟨rfl, ⟨a, b, d, e, f, g, h⟩, Or.inr ⟨rfl, i⟩⟩) ?_
  rintro j' g fl V₁ ⟨hV₁, hmY, hpost⟩ Y t₁ hKY hAY hrY hgY -
  subst V₁ hgY
  rcases hpost with rfl | ⟨rfl, gdi⟩
  · exact from60 c hfs hin hinA hKY hAY hrY hmY hcl hs1 hs2 hs3 hw8 w5 w6 f0 f1 hr8 hl hin₂ h₂ k2
      fun W' Z' t' a b d e f => kr W' Z' t' a b d e f
  · have hY : Y.cpu.gpr.rsp - 8 = aR X.cpu.gpr.rsp - 8 := by rw [hmY.1]
    refine c.s_call hKY hAY hin (lt_len (by decide)) hrY (call_55 _) hinD (Dnw.lt_len (j := 0) (by decide)) tgt_55
      (by rw [hY]; exact hr8) ?_
    rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
    rw [hY] at hA₂
    refine k1 Y₂ t₂ hK₂ hA₂ hr₂ (by rw [hg₂]; exact hY)
      ⟨by rw [hg₂]; exact kf_set hmY, by rw [hg₂]; exact gdi⟩ ?_
    intro Z₁ W₁ t₃ hKZ hAZ hrZ hmZ _ _
    exact from60 c hfs hin hinA hKZ hAZ hrZ hmZ hcl hs1 hs2 hs3 hw8 w5 w6 f0 f1 hr8 hl hin₂ h₂ k2 kr

end FV7z.Anc
