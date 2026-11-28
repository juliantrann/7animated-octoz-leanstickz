import FV7z.Npl.Cuts
import FV7z.Api.Holds
import FV7z.Tun.Inv
/-!
# `CStdOutStream::NormalizePrint_UString (s)` (0x5a1680): from the entry to its tail jump (PLAN.md §M, M1)

7-Zip 26.06's `CStdOutStream::NormalizePrint_UString (UString &s)` (`CPP/Common/StdOutStream.cpp`; `objdump -d`) at
`0x5a1680` in `7zzs`: `this` = `rdi` (`rbp`), `s` = `rsi` (`r12`). Two pushes (`r12`, `rbp`) and 8 bytes of frame
(`aR S`); when the byte at `this + 10` is not 0 and the byte at `this + 9` is 0, the `call` (61) of
`s.Replace (L'/', L'\\')` at `0x44e010` (its code a hypothesis) and a jump back (66) to 29; then `add rsp, 8`, the pops,
a tail jump (42) to `Normalize_UString (this, s)` at `0x5a15e0` (`FV7z.Nus`).

- `call_61`, `tgt_61`, `jmp_42`: the instructions outside the blocks.
- `aR`, `V0`, `q1`..`q3`, `Fm`, `Stk`, `KC`, `Ev`: the frame, the bytes after the pushes, the pops' addresses, the
  frame's registers, the stack, the callee as a continuation, the hypotheses of the runs.
- `vc_0`, `vc_29`, `vc_66`: the pieces.
- `npl_ok`: from the entry (`S` = the entry's `rsp`, `g0` = its registers, `I` of the bytes after the pushes, `V0`)
  to `Normalize_UString`'s entry (`Ev.kj`: `rsp` = `S`, the callee-saved registers as at the entry, `rdi` = `this`,
  `rsi` = `s`, `I` of the bytes) or the callee's goal.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
open FV7z.Api (KS)
namespace FV7z.Npl
set_option linter.unusedVariables false

/-! ## The instructions outside the blocks -/

/-- The `call` of `UString::Replace` (61). -/
def pc61 : List Byte := [0xe8, 0x4e, 0xc9, 0xea, 0xff]
theorem pc61_0 : ∀ feat, Dec feat pc61 0 (FV7z.mk .call 64 [.rel 18446744073708161358] 5) := by dec_rfl
theorem wc_61 : pc61 <+: npl.drop 61 := by decide +kernel
theorem call_61 (feat : Features) : Dec feat npl 61 (FV7z.mk .call 64 [.rel 18446744073708161358] 5) :=
  Dec.shift (j := 61) (k := 0) (pc61_0 feat) wc_61 (Nat.zero_le _)
theorem tgt_61 : npl_at.add (61 + 5) + BitVec.ofNat 64 18446744073708161358 = 0x44e010#64 := by decide

/-- The tail jump to `Normalize_UString` (42). -/
def pjm : List Byte := [0xe9, 0x31, 0xff, 0xff, 0xff]
theorem pjm_0 : ∀ feat, Dec feat pjm 0 (FV7z.mk .jmp 64 [.rel 18446744073709551409] 5) := by dec_rfl
theorem wj_42 : pjm <+: npl.drop 42 := by decide +kernel
theorem jmp_42 (feat : Features) : Dec feat npl 42 (FV7z.mk .jmp 64 [.rel 18446744073709551409] 5) :=
  Dec.shift (j := 42) (k := 0) (pjm_0 feat) wj_42 (Nat.zero_le _)

/-- `Normalize_UString`'s entry (`FV7z.Nus.nus_at`). -/
abbrev tgt_at : Addr := 0x5a15e0

/-! ## The frame -/

/-- The stack pointer after the two pushes and `sub rsp, 8`. -/
abbrev aR (S : Addr) : Addr := S - 8 - 8 - 8#64

/-- The bytes after the two pushes (`r12`, `rbp`). -/
abbrev V0 (V : Addr → Byte) (g : Gprs) : Addr → Byte :=
  Vst (Vst V (g.rsp - 8) (toBytesLE g.r12 8)) (g.rsp - 8 - 8) (toBytesLE g.rbp 8)

theorem q1 (S : Addr) : aR S + 8#64 = S - 8 - 8 := BitVec.sub_add_cancel _ _
theorem q2 (S : Addr) : aR S + 8#64 + 8 = S - 8 := by rw [q1, BitVec.sub_add_cancel]
theorem q3 (S : Addr) : aR S + 8#64 + 8 + 8 = S := by rw [q2, BitVec.sub_add_cancel]

/-- The frame from the prologue on: `rsp` = `aR S`, `rbp` = `this`, `r12` = `s`, `rbx`, `r13`..`r15` as at the
entry. -/
abbrev Fm (S : Addr) (g0 g : Gprs) : Prop :=
  g.rsp = aR S ∧ g.rbx = g0.rbx ∧ g.rbp = g0.rdi ∧ g.r12 = g0.rsi ∧ g.r13 = g0.r13 ∧ g.r14 = g0.r14 ∧
    g.r15 = g0.r15

/-- Back from the callee: `rsp` as before the `call`, the callee-saved registers kept. -/
theorem fm_ret {S : Addr} {g0 g g' : Gprs} (h : Fm S g0 g) (hs : g'.rsp = aR S) (hk : KS g g') : Fm S g0 g' :=
  ⟨hs, hk.1.trans h.2.1, hk.2.1.trans h.2.2.1, hk.2.2.1.trans h.2.2.2.1, hk.2.2.2.1.trans h.2.2.2.2.1,
    hk.2.2.2.2.1.trans h.2.2.2.2.2.1, hk.2.2.2.2.2.trans h.2.2.2.2.2.2⟩

/-- The stack: the two saved registers. -/
abbrev Stk (W : Addr → Byte) (S : Addr) (g0 : Gprs) : Prop :=
  rdq(W, S - 8) = g0.r12 ∧ rdq(W, S - 8 - 8) = g0.rbp

/-- The callee from the `call` before `j` (entry `ent`, the bytes `W`, the registers `A`): at its entry, and from its
return at `j` with `rsp` = `aR S`, the callee-saved registers as at its entry, `B` and the invariant `J`, the run
goes on to the goal. -/
def KC (prof : Profile) (F : Footprint) (Wl : List Rgn) (L : List (Addr × List Byte)) (s₀ : State) (o : Oracle)
    (gev : List Event) (gP : State → Nat → List Event → Prop) (gE : Outcome → List Event → Prop)
    (S : Addr) (J : (Addr → Byte) → Prop) (ent : Addr) (j : Nat) (W : Addr → Byte) (A B : Gprs → Prop) : Prop :=
  ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y →
    Agree F Y.proc.mm.mem (Vst W (aR S - 8) (toBytesLE (npl_at.add j) 8)) →
    Y.cpu.rip = ent → Y.cpu.gpr.rsp = aR S - 8 → A Y.cpu.gpr →
    (∀ (Z : State) (W' : Addr → Byte) (t'' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem W' →
      Z.cpu.rip = npl_at.add j → Z.cpu.gpr.rsp = aR S → KS Y.cpu.gpr Z.cpu.gpr → B Z.cpu.gpr → J W' →
      GoG prof L o gev gP gE Z t'') →
    GoG prof L o gev gP gE Y t'

/-! ## The hypotheses of the runs -/

/-- The hypotheses of the runs from the cut points (`S`, `g0` the entry's stack pointer and registers, `I` the
invariant of the bytes): the saved registers readable (`fb16`, `fb8`), the `call`'s slot, `this`'s two flag bytes
readable (`f9`, `f10`); the callee keeps `I`; `Normalize_UString`'s code and its entry as the goal (`kj`). -/
structure Ev (prof : Profile) (F : Footprint) (Wl : List Rgn) (L : List (Addr × List Byte)) (s₀ : State)
    (o : Oracle) (gev : List Event) (gP : State → Nat → List Event → Prop) (gE : Outcome → List Event → Prop)
    (S : Addr) (g0 : Gprs) (I : (Addr → Byte) → Prop) : Prop where
  c : Seg prof F Wl L s₀ o
  hin : CodeIn L npl_at npl
  hI : ∀ W, I W → Stk W S g0
  fb16 : ∀ i < 8, Foot F.data (Addr.add (S - 8 - 8) i)
  fb8 : ∀ i < 8, Foot F.data (Addr.add (S - 8) i)
  hr8 : ∀ i < 8, Foot Wl (Addr.add (aR S - 8) i)
  f9 : ∀ i < 1, Foot F.data (Addr.add (g0.rdi + 9#64) i)
  f10 : ∀ i < 1, Foot F.data (Addr.add (g0.rdi + 10#64) i)
  cR : ∃ code : List Byte, CodeIn L 0x44e010#64 code ∧ 0 < code.length
  cT : ∃ code : List Byte, CodeIn L tgt_at code ∧ 0 < code.length
  kR : ∀ j W, I W → KC prof F Wl L s₀ o gev gP gE S I 0x44e010#64 j W (fun _ => True) (fun _ => True)
  kj : ∀ (W : Addr → Byte) (Y : State) (t' : Nat), KeptW Wl s₀ Y → Agree F Y.proc.mm.mem W →
    Y.cpu.rip = tgt_at → Y.cpu.gpr.rsp = S → KS g0 Y.cpu.gpr → Y.cpu.gpr.rdi = g0.rdi →
    Y.cpu.gpr.rsi = g0.rsi → I W → GoG prof L o gev gP gE Y t'

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

/-- `endbr64`, the two pushes, `r12` = `s`, `rbp` = `this`, `sub rsp, 8`, the two flag bytes tested: to 29, or the
arguments of `Replace` and its `call` at 61. -/
theorem vc_0 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (hs1 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8) i)) (hs2 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8) i))
    (f9 : ∀ i < 1, Foot F.data (Addr.add (g.rdi + 9#64) i))
    (f10 : ∀ i < 1, Foot F.data (Addr.add (g.rdi + 10#64) i))
    (h29 : ∀ g', g'.rsp = aR g.rsp → g'.rbx = g.rbx → g'.rbp = g.rdi → g'.r12 = g.rsi → g'.r13 = g.r13 →
      g'.r14 = g.r14 → g'.r15 = g.r15 → ∀ fl, Q 29 g' fl (V0 V g))
    (h61 : ∀ g', g'.rsp = aR g.rsp → g'.rbx = g.rbx → g'.rbp = g.rdi → g'.r12 = g.rsi → g'.r13 = g.r13 →
      g'.r14 = g.r14 → g'.r15 = g.r15 → ∀ fl, Q 61 g' fl (V0 V g)) :
    W_0 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [aR, V0] at hs1 hs2 f9 f10 h29 h61 ⊢
  wpx [W_0, W_23, W_48, o0, o1, o3]
  all_goals repeat' (first
    | refine h29 _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ _
    | refine h61 _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ _
    | with_reducible exact hs1
    | with_reducible exact hs2
    | with_reducible exact f9
    | with_reducible exact f10
    | ostep)

/-- `add rsp, 8`, `rsi` = `s`, `rdi` = `this`, the two pops, to the tail jump at 42. -/
theorem vc_29 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (f1 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8#64) i))
    (f2 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8#64 + 8) i))
    (h : ∀ g', g'.rsp = g.rsp + 8#64 + 8 + 8 → g'.rbp = rdq(V, g.rsp + 8#64) → g'.r12 = rdq(V, g.rsp + 8#64 + 8) →
      g'.rbx = g.rbx → g'.r13 = g.r13 → g'.r14 = g.r14 → g'.r15 = g.r15 → g'.rdi = g.rbp → g'.rsi = g.r12 →
      ∀ fl, Q 42 g' fl V) :
    W_29 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at f1 f2 h ⊢
  wpx [W_29, o2]
  all_goals repeat' (first
    | refine h _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ _
    | with_reducible exact f1
    | with_reducible exact f2
    | ostep)

/-- Back from `Replace`: the jump back to 29. -/
theorem vc_66 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} (h : ∀ fl, Q 29 g fl V) :
    W_66 F Wl Q g f V :=
  h _

end Pieces

/-! ## The runs -/

section Runs
variable {prof : Profile} {F : Footprint} {Wl : List Rgn} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {S : Addr} {g0 : Gprs} {I : (Addr → Byte) → Prop} {X Y : State} {t : Nat} {V W : Addr → Byte}

/-- From 29: `add rsp, 8`, the arguments, the pops, the tail jump, to `kj`. -/
theorem from29 (E : Ev prof F Wl L s₀ o gev gP gE S g0 I) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = npl_at.add 29) (hm : Fm S g0 Y.cpu.gpr) (hIW : I W) :
    GoG prof L o gev gP gE Y t := by
  obtain ⟨s1, s2⟩ := E.hI W hIW
  have ms := hm.1
  have e1 : rdq(W, Y.cpu.gpr.rsp + 8#64) = g0.rbp := by rw [ms, q1]; exact s2
  have e2 : rdq(W, Y.cpu.gpr.rsp + 8#64 + 8) = g0.r12 := by rw [ms, q2]; exact s1
  refine (c_29 prof).run E.c E.hin (fun j' g' _ V' => j' = 42 ∧ V' = W ∧
      g'.rsp = Y.cpu.gpr.rsp + 8#64 + 8 + 8 ∧ g'.rbp = rdq(W, Y.cpu.gpr.rsp + 8#64) ∧
      g'.r12 = rdq(W, Y.cpu.gpr.rsp + 8#64 + 8) ∧ g'.rbx = Y.cpu.gpr.rbx ∧ g'.r13 = Y.cpu.gpr.r13 ∧
      g'.r14 = Y.cpu.gpr.r14 ∧ g'.r15 = Y.cpu.gpr.r15 ∧ g'.rdi = Y.cpu.gpr.rbp ∧ g'.rsi = Y.cpu.gpr.r12)
    hK hA hr
    (vc_29 (by rw [ms, q1]; exact E.fb16) (by rw [ms, q2]; exact E.fb8)
      fun _ a b c d e m n p q _ => ⟨rfl, rfl, a, b, c, d, e, m, n, p, q⟩) ?_
  rintro j' g fl V₁ ⟨rfl, hV₁, gs, gp, g12, gb, g13, g14, g15, gdi, gsi⟩ U t₁ hKU hAU hrU hgU -
  subst V₁ hgU
  have hsU : U.cpu.gpr.rsp = S := by rw [gs, ms]; exact q3 S
  obtain ⟨cT, hinT, hT⟩ := E.cT
  refine E.c.s_jmp_x hKU hAU E.hin (lt_len (by decide)) hrU (jmp_42 _) hinT hT (by decide) ?_
  rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
  refine E.kj W Y₂ t₂ hK₂ hA₂ (by rw [hr₂, addr_add_zero]) (by rw [hg₂]; exact hsU) ?_ ?_ ?_ hIW
  · rw [hg₂]
    exact ⟨gb.trans hm.2.1, gp.trans e1, g12.trans e2, g13.trans hm.2.2.2.2.1, g14.trans hm.2.2.2.2.2.1,
      g15.trans hm.2.2.2.2.2.2⟩
  · rw [hg₂]; exact gdi.trans hm.2.2.1
  · rw [hg₂]; exact gsi.trans hm.2.2.2.1

/-- From 66 (back from `Replace`): the jump back, to 29. -/
theorem from66 (E : Ev prof F Wl L s₀ o gev gP gE S g0 I) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = npl_at.add 66) (hm : Fm S g0 Y.cpu.gpr) (hIW : I W) :
    GoG prof L o gev gP gE Y t := by
  refine (c_66 prof).run E.c E.hin (fun j' g' _ V' => j' = 29 ∧ V' = W ∧ g' = Y.cpu.gpr) hK hA hr
    (vc_66 fun _ => ⟨rfl, rfl, rfl⟩) ?_
  rintro j' g fl V₁ ⟨rfl, hV₁, hg⟩ U t₁ hKU hAU hrU hgU -
  subst V₁ hgU
  exact from29 E hKU hAU hrU (by rw [hg]; exact hm) hIW

/-- `CStdOutStream::NormalizePrint_UString (this, s)` from its entry (`X`'s registers, `S` = their `rsp`; the
pushes' slots in what the run may store into, `I` of the bytes after the pushes). -/
theorem npl_ok (E : Ev prof F Wl L s₀ o gev gP gE X.cpu.gpr.rsp X.cpu.gpr I)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = npl_at)
    (hs1 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8) i))
    (hs2 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8 - 8) i)) (hI0 : I (V0 V X.cpu.gpr)) :
    GoG prof L o gev gP gE X t := by
  refine (c_0 prof).run E.c E.hin (fun j' g' _ V' => (j' = 29 ∨ j' = 61) ∧ V' = V0 V X.cpu.gpr ∧
      Fm X.cpu.gpr.rsp X.cpu.gpr g') hK hA (by rw [addr_add_zero]; exact hrip)
    (vc_0 hs1 hs2 E.f9 E.f10 (fun _ a b c d e m n _ => ⟨Or.inl rfl, rfl, a, b, c, d, e, m, n⟩)
      fun _ a b c d e m n _ => ⟨Or.inr rfl, rfl, a, b, c, d, e, m, n⟩) ?_
  rintro j' g fl V₁ ⟨hj, hV₁, hmY⟩ Y t₁ hKY hAY hrY hgY -
  subst V₁ hgY
  rcases hj with rfl | rfl
  · exact from29 E hKY hAY hrY hmY hI0
  · obtain ⟨cc, hinc, hcc⟩ := E.cR
    have hU : Y.cpu.gpr.rsp - 8 = aR X.cpu.gpr.rsp - 8 := by rw [hmY.1]
    refine E.c.s_call hKY hAY E.hin (lt_len (by decide)) hrY (call_61 _) hinc hcc tgt_61
      (by rw [hU]; exact E.hr8) ?_
    rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
    rw [hU] at hA₂
    refine E.kR _ _ hI0 Y₂ t₂ hK₂ hA₂ hr₂ (by rw [hg₂]; exact hU) trivial ?_
    intro Z W' t₃ hKZ hAZ hrZ hsZ hkZ hBZ hIZ
    rw [hg₂] at hkZ
    exact from66 E hKZ hAZ hrZ (fm_ret hmY hsZ hkZ) hIZ

end Runs

end FV7z.Npl
