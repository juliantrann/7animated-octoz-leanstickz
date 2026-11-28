import FV7z.Npu.Cuts
import FV7z.Api.Holds
import FV7z.Tun.Inv
/-!
# `CStdOutStream::NormalizePrint_UString_Path` (0x5a16d0): from the entry to its tail jump (PLAN.md §M, M1)

7-Zip 26.06's `CStdOutStream::NormalizePrint_UString_Path (s, tempU, tempA)` (`CPP/Common/StdOutStream.cpp`;
`objdump -d`) at `0x5a16d0` in `7zzs`: `this` = `rdi` (`r12`), `s` = `rsi`, `tempU` = `rdx` (`rbp`), `tempA` = `rcx`
(`r13`). Three pushes (`r13`, `r12`, `rbp`), the `call`s of `UString::operator= (tempU, s)` at `0x44d710` (21) and
`NormalizePrint_UString (tempU)` at `0x5a1680` (32) (their code hypotheses), the pops, a tail jump (51) to
`PrintUString (this, tempU, tempA)` at `0x5a14f0` (`FV7z.Pus`).

- `call_*`, `tgt_*`, `jmp_51`: the instructions outside the blocks.
- `aR`, `V0`, `q1`..`q3`, `Fm`, `Fr`, `Stk`, `KC`, `Ev`, `callK`: the frame, the bytes after the pushes, the pops'
  addresses, the frame's registers, what a piece keeps, the stack, a callee as a continuation, the hypotheses of the
  runs, a `call` and the run from its return.
- `vc_0`, `vc_26`, `vc_37`: the pieces.
- `npu_ok`: from the entry (`S` = the entry's `rsp`, `g0` = its registers, `I` of the bytes after the pushes, `V0`)
  to `PrintUString`'s entry (`Ev.kj`: `rsp` = `S`, the callee-saved registers as at the entry, `rdi` = `this`, `rsi`
  = `tempU`, `rdx` = `tempA`, `I` of the bytes) or a callee's goal.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
open FV7z.Api (KS)
namespace FV7z.Npu
set_option linter.unusedVariables false

/-! ## The instructions outside the blocks -/

/-- The `call` of `UString::operator=` (21). -/
def pc21 : List Byte := [0xe8, 0x26, 0xc0, 0xea, 0xff]
theorem pc21_0 : ∀ feat, Dec feat pc21 0 (FV7z.mk .call 64 [.rel 18446744073708159014] 5) := by dec_rfl
theorem wc_21 : pc21 <+: npu.drop 21 := by decide +kernel
theorem call_21 (feat : Features) : Dec feat npu 21 (FV7z.mk .call 64 [.rel 18446744073708159014] 5) :=
  Dec.shift (j := 21) (k := 0) (pc21_0 feat) wc_21 (Nat.zero_le _)
theorem tgt_21 : npu_at.add (21 + 5) + BitVec.ofNat 64 18446744073708159014 = 0x44d710#64 := by decide

/-- The `call` of `NormalizePrint_UString` (32). -/
def pc32 : List Byte := [0xe8, 0x8b, 0xff, 0xff, 0xff]
theorem pc32_0 : ∀ feat, Dec feat pc32 0 (FV7z.mk .call 64 [.rel 18446744073709551499] 5) := by dec_rfl
theorem wc_32 : pc32 <+: npu.drop 32 := by decide +kernel
theorem call_32 (feat : Features) : Dec feat npu 32 (FV7z.mk .call 64 [.rel 18446744073709551499] 5) :=
  Dec.shift (j := 32) (k := 0) (pc32_0 feat) wc_32 (Nat.zero_le _)
theorem tgt_32 : npu_at.add (32 + 5) + BitVec.ofNat 64 18446744073709551499 = 0x5a1680#64 := by decide

/-- The tail jump to `PrintUString` (51). -/
def pjm : List Byte := [0xe9, 0xe8, 0xfd, 0xff, 0xff]
theorem pjm_0 : ∀ feat, Dec feat pjm 0 (FV7z.mk .jmp 64 [.rel 18446744073709551080] 5) := by dec_rfl
theorem wj_51 : pjm <+: npu.drop 51 := by decide +kernel
theorem jmp_51 (feat : Features) : Dec feat npu 51 (FV7z.mk .jmp 64 [.rel 18446744073709551080] 5) :=
  Dec.shift (j := 51) (k := 0) (pjm_0 feat) wj_51 (Nat.zero_le _)

/-- `PrintUString`'s entry (`FV7z.Pus.pus_at`). -/
abbrev tgt_at : Addr := 0x5a14f0

/-! ## The frame -/

/-- The stack pointer after the three pushes. -/
abbrev aR (S : Addr) : Addr := S - 8 - 8 - 8

/-- The bytes after the three pushes (`r13`, `r12`, `rbp`). -/
abbrev V0 (V : Addr → Byte) (g : Gprs) : Addr → Byte :=
  Vst (Vst (Vst V (g.rsp - 8) (toBytesLE g.r13 8)) (g.rsp - 8 - 8) (toBytesLE g.r12 8)) (g.rsp - 8 - 8 - 8)
    (toBytesLE g.rbp 8)

theorem q1 (S : Addr) : aR S + 8 = S - 8 - 8 := BitVec.sub_add_cancel _ _
theorem q2 (S : Addr) : aR S + 8 + 8 = S - 8 := by rw [q1, BitVec.sub_add_cancel]
theorem q3 (S : Addr) : aR S + 8 + 8 + 8 = S := by rw [q2, BitVec.sub_add_cancel]

/-- The frame from the prologue on: `rsp` = `aR S`, `rbp` = `tempU`, `r12` = `this`, `r13` = `tempA`, `rbx`, `r14`,
`r15` as at the entry. -/
abbrev Fm (S : Addr) (g0 g : Gprs) : Prop :=
  g.rsp = aR S ∧ g.rbx = g0.rbx ∧ g.rbp = g0.rdx ∧ g.r12 = g0.rdi ∧ g.r13 = g0.rcx ∧ g.r14 = g0.r14 ∧
    g.r15 = g0.r15

/-- What a piece keeps: `rsp`, `rbx`, `rbp`, `r12`..`r15`. -/
abbrev Fr (g g' : Gprs) : Prop :=
  g'.rsp = g.rsp ∧ g'.rbx = g.rbx ∧ g'.rbp = g.rbp ∧ g'.r12 = g.r12 ∧ g'.r13 = g.r13 ∧ g'.r14 = g.r14 ∧
    g'.r15 = g.r15

theorem Fm.fr {S : Addr} {g0 g g' : Gprs} (h : Fm S g0 g) (h' : Fr g g') : Fm S g0 g' :=
  ⟨h'.1.trans h.1, h'.2.1.trans h.2.1, h'.2.2.1.trans h.2.2.1, h'.2.2.2.1.trans h.2.2.2.1,
    h'.2.2.2.2.1.trans h.2.2.2.2.1, h'.2.2.2.2.2.1.trans h.2.2.2.2.2.1, h'.2.2.2.2.2.2.trans h.2.2.2.2.2.2⟩

/-- Back from a callee: `rsp` as before the `call`, the callee-saved registers kept. -/
theorem fm_ret {S : Addr} {g0 g g' : Gprs} (h : Fm S g0 g) (hs : g'.rsp = aR S) (hk : KS g g') : Fm S g0 g' :=
  ⟨hs, hk.1.trans h.2.1, hk.2.1.trans h.2.2.1, hk.2.2.1.trans h.2.2.2.1, hk.2.2.2.1.trans h.2.2.2.2.1,
    hk.2.2.2.2.1.trans h.2.2.2.2.2.1, hk.2.2.2.2.2.trans h.2.2.2.2.2.2⟩

/-- The stack: the three saved registers. -/
abbrev Stk (W : Addr → Byte) (S : Addr) (g0 : Gprs) : Prop :=
  rdq(W, S - 8) = g0.r13 ∧ rdq(W, S - 8 - 8) = g0.r12 ∧ rdq(W, S - 8 - 8 - 8) = g0.rbp

/-- A callee from the `call` before `j` (entry `ent`, the bytes `W`, the registers `A`): at its entry, and from its
return at `j` with `rsp` = `aR S`, the callee-saved registers as at its entry, `B` and the invariant `J`, the run
goes on to the goal. -/
def KC (prof : Profile) (F : Footprint) (Wl : List Rgn) (L : List (Addr × List Byte)) (s₀ : State) (o : Oracle)
    (gev : List Event) (gP : State → Nat → List Event → Prop) (gE : Outcome → List Event → Prop)
    (S : Addr) (J : (Addr → Byte) → Prop) (ent : Addr) (j : Nat) (W : Addr → Byte) (A B : Gprs → Prop) : Prop :=
  ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y →
    Agree F Y.proc.mm.mem (Vst W (aR S - 8) (toBytesLE (npu_at.add j) 8)) →
    Y.cpu.rip = ent → Y.cpu.gpr.rsp = aR S - 8 → A Y.cpu.gpr →
    (∀ (Z : State) (W' : Addr → Byte) (t'' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem W' →
      Z.cpu.rip = npu_at.add j → Z.cpu.gpr.rsp = aR S → KS Y.cpu.gpr Z.cpu.gpr → B Z.cpu.gpr → J W' →
      GoG prof L o gev gP gE Z t'') →
    GoG prof L o gev gP gE Y t'

/-! ## The hypotheses of the runs -/

/-- The hypotheses of the runs from the cut points (`S`, `g0` the entry's stack pointer and registers, `I` the
invariant of the bytes): the saved registers readable (`fb24`..`fb8`), the `call`s' slot; the callees keep `I`, from
any return offset; `PrintUString`'s code and its entry as the goal (`kj`). -/
structure Ev (prof : Profile) (F : Footprint) (Wl : List Rgn) (L : List (Addr × List Byte)) (s₀ : State)
    (o : Oracle) (gev : List Event) (gP : State → Nat → List Event → Prop) (gE : Outcome → List Event → Prop)
    (S : Addr) (g0 : Gprs) (I : (Addr → Byte) → Prop) : Prop where
  c : Seg prof F Wl L s₀ o
  hin : CodeIn L npu_at npu
  hI : ∀ W, I W → Stk W S g0
  fb24 : ∀ i < 8, Foot F.data (Addr.add (S - 8 - 8 - 8) i)
  fb16 : ∀ i < 8, Foot F.data (Addr.add (S - 8 - 8) i)
  fb8 : ∀ i < 8, Foot F.data (Addr.add (S - 8) i)
  hr8 : ∀ i < 8, Foot Wl (Addr.add (aR S - 8) i)
  cA : ∃ code : List Byte, CodeIn L 0x44d710#64 code ∧ 0 < code.length
  cN : ∃ code : List Byte, CodeIn L 0x5a1680#64 code ∧ 0 < code.length
  cT : ∃ code : List Byte, CodeIn L tgt_at code ∧ 0 < code.length
  kA : ∀ j W, I W → KC prof F Wl L s₀ o gev gP gE S I 0x44d710#64 j W (fun _ => True) (fun _ => True)
  kN : ∀ j W, I W → KC prof F Wl L s₀ o gev gP gE S I 0x5a1680#64 j W (fun _ => True) (fun _ => True)
  kj : ∀ (W : Addr → Byte) (Y : State) (t' : Nat), KeptW Wl s₀ Y → Agree F Y.proc.mm.mem W →
    Y.cpu.rip = tgt_at → Y.cpu.gpr.rsp = S → KS g0 Y.cpu.gpr → Y.cpu.gpr.rdi = g0.rdi →
    Y.cpu.gpr.rsi = g0.rdx → Y.cpu.gpr.rdx = g0.rcx → I W → GoG prof L o gev gP gE Y t'

section Runs
variable {prof : Profile} {F : Footprint} {Wl : List Rgn} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {S : Addr} {g0 : Gprs} {I : (Addr → Byte) → Prop} {W : Addr → Byte}

/-- A `call` at `j` (`rsp` = `aR S`, the bytes `W`) of the callee `k`, and from its return at `j + 5`. -/
theorem callK (E : Ev prof F Wl L s₀ o gev gP gE S g0 I)
    {J : (Addr → Byte) → Prop} {U : State} {t₁ : Nat} {j R : Nat} {ent : Addr} {A B : Gprs → Prop}
    (hKU : KeptW Wl s₀ U) (hAU : Agree F U.proc.mm.mem W) (hrU : U.cpu.rip = npu_at.add j)
    (hs : U.cpu.gpr.rsp = aR S) (hj : j < npu.length) (hd : Dec prof.feat npu j (FV7z.mk .call 64 [.rel R] 5))
    (htgt : npu_at.add (j + 5) + BitVec.ofNat 64 R = ent)
    (hc : ∃ code : List Byte, CodeIn L ent code ∧ 0 < code.length)
    (k : KC prof F Wl L s₀ o gev gP gE S J ent (j + 5) W A B) (hA : A (U.cpu.gpr.set 4 (aR S - 8)))
    (h : ∀ (Z : State) (W' : Addr → Byte) (t'' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem W' →
      Z.cpu.rip = npu_at.add (j + 5) → Z.cpu.gpr.rsp = aR S → KS U.cpu.gpr Z.cpu.gpr → B Z.cpu.gpr → J W' →
      GoG prof L o gev gP gE Z t'') :
    GoG prof L o gev gP gE U t₁ := by
  have hU : U.cpu.gpr.rsp - 8 = aR S - 8 := by rw [hs]
  obtain ⟨cc, hinc, hcc⟩ := hc
  refine E.c.s_call hKU hAU E.hin hj hrU hd hinc hcc htgt (by rw [hU]; exact E.hr8) ?_
  rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
  rw [hU] at hA₂
  refine k Y₂ t₂ hK₂ hA₂ hr₂ (by rw [hg₂]; exact hU) (by rw [hg₂, hU]; exact hA) ?_
  intro Z W' t₃ hKZ hAZ hrZ hsZ hkZ hBZ hIZ
  rw [hg₂] at hkZ
  exact h Z W' t₃ hKZ hAZ hrZ hsZ hkZ hBZ hIZ

end Runs

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

/-- `endbr64`, the three pushes, `r13` = `tempA`, `r12` = `this`, `rdi` = `rbp` = `tempU`, to the `call` of
`UString::operator=` at 21. -/
theorem vc_0 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (hs1 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8) i)) (hs2 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8) i))
    (hs3 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8 - 8) i))
    (h : ∀ g', g'.rsp = aR g.rsp → g'.rbx = g.rbx → g'.rbp = g.rdx → g'.r12 = g.rdi → g'.r13 = g.rcx →
      g'.r14 = g.r14 → g'.r15 = g.r15 → ∀ fl, Q 21 g' fl (V0 V g)) :
    W_0 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [aR, V0] at hs1 hs2 hs3 h ⊢
  wpx [W_0, o0]
  all_goals repeat' (first
    | refine h _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ _
    | with_reducible exact hs1
    | with_reducible exact hs2
    | with_reducible exact hs3
    | ostep)

/-- Back from `UString::operator=`: `rsi` = `tempU`, `rdi` = `this`, to the `call` of `NormalizePrint_UString` at
32. -/
theorem vc_26 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} (h : ∀ g', Fr g g' → ∀ fl, Q 32 g' fl V) :
    W_26 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [Fr] at h ⊢
  wpx [W_26, o1]
  all_goals repeat' (first
    | refine h _ ?_ _
    | ostep)

/-- Back from `NormalizePrint_UString`: `rdx` = `tempA`, `rsi` = `tempU`, `rdi` = `this`, the three pops, to the
tail jump at 51. -/
theorem vc_37 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (f0 : ∀ i < 8, Foot F.data (Addr.add g.rsp i)) (f1 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8) i))
    (f2 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8 + 8) i))
    (h : ∀ g', g'.rsp = g.rsp + 8 + 8 + 8 → g'.rbp = rdq(V, g.rsp) → g'.r12 = rdq(V, g.rsp + 8) →
      g'.r13 = rdq(V, g.rsp + 8 + 8) → g'.rbx = g.rbx → g'.r14 = g.r14 → g'.r15 = g.r15 → g'.rdi = g.r12 →
      g'.rsi = g.rbp → g'.rdx = g.r13 → ∀ fl, Q 51 g' fl V) :
    W_37 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at f0 f1 f2 h ⊢
  wpx [W_37, o2]
  all_goals repeat' (first
    | refine h _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ _
    | with_reducible exact f0
    | with_reducible exact f1
    | with_reducible exact f2
    | ostep)

end Pieces

/-! ## The runs -/

section Runs
variable {prof : Profile} {F : Footprint} {Wl : List Rgn} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {S : Addr} {g0 : Gprs} {I : (Addr → Byte) → Prop} {X Y : State} {t : Nat} {V W : Addr → Byte}

/-- From 37 (back from `NormalizePrint_UString`): the arguments, the pops, the tail jump, to `kj`. -/
theorem from37 (E : Ev prof F Wl L s₀ o gev gP gE S g0 I) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = npu_at.add 37) (hm : Fm S g0 Y.cpu.gpr) (hIW : I W) :
    GoG prof L o gev gP gE Y t := by
  obtain ⟨s1, s2, s3⟩ := E.hI W hIW
  have ms := hm.1
  have e0 : rdq(W, Y.cpu.gpr.rsp) = g0.rbp := by rw [ms]; exact s3
  have e1 : rdq(W, Y.cpu.gpr.rsp + 8) = g0.r12 := by rw [ms, q1]; exact s2
  have e2 : rdq(W, Y.cpu.gpr.rsp + 8 + 8) = g0.r13 := by rw [ms, q2]; exact s1
  refine (c_37 prof).run E.c E.hin (fun j' g' _ V' => j' = 51 ∧ V' = W ∧
      g'.rsp = Y.cpu.gpr.rsp + 8 + 8 + 8 ∧ g'.rbp = rdq(W, Y.cpu.gpr.rsp) ∧ g'.r12 = rdq(W, Y.cpu.gpr.rsp + 8) ∧
      g'.r13 = rdq(W, Y.cpu.gpr.rsp + 8 + 8) ∧ g'.rbx = Y.cpu.gpr.rbx ∧ g'.r14 = Y.cpu.gpr.r14 ∧
      g'.r15 = Y.cpu.gpr.r15 ∧ g'.rdi = Y.cpu.gpr.r12 ∧ g'.rsi = Y.cpu.gpr.rbp ∧ g'.rdx = Y.cpu.gpr.r13)
    hK hA hr
    (vc_37 (by rw [ms]; exact E.fb24) (by rw [ms, q1]; exact E.fb16) (by rw [ms, q2]; exact E.fb8)
      fun _ a b c d e m n p q r _ => ⟨rfl, rfl, a, b, c, d, e, m, n, p, q, r⟩) ?_
  rintro j' g fl V₁ ⟨rfl, hV₁, gs, gp, g12, g13, gb, g14, g15, gdi, gsi, gdx⟩ U t₁ hKU hAU hrU hgU -
  subst V₁ hgU
  have hsU : U.cpu.gpr.rsp = S := by rw [gs, ms]; exact q3 S
  obtain ⟨cT, hinT, hT⟩ := E.cT
  refine E.c.s_jmp_x hKU hAU E.hin (lt_len (by decide)) hrU (jmp_51 _) hinT hT (by decide) ?_
  rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
  refine E.kj W Y₂ t₂ hK₂ hA₂ (by rw [hr₂, addr_add_zero]) (by rw [hg₂]; exact hsU) ?_ ?_ ?_ ?_ hIW
  · rw [hg₂]
    exact ⟨gb.trans hm.2.1, gp.trans e0, g12.trans e1, g13.trans e2, g14.trans hm.2.2.2.2.2.1,
      g15.trans hm.2.2.2.2.2.2⟩
  · rw [hg₂]; exact gdi.trans hm.2.2.2.1
  · rw [hg₂]; exact gsi.trans hm.2.2.1
  · rw [hg₂]; exact gdx.trans hm.2.2.2.2.1

/-- From 26 (back from `UString::operator=`): `NormalizePrint_UString (tempU)` (32), to 37. -/
theorem from26 (E : Ev prof F Wl L s₀ o gev gP gE S g0 I) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = npu_at.add 26) (hm : Fm S g0 Y.cpu.gpr) (hIW : I W) :
    GoG prof L o gev gP gE Y t := by
  refine (c_26 prof).run E.c E.hin (fun j' g' _ V' => j' = 32 ∧ V' = W ∧ Fr Y.cpu.gpr g') hK hA hr
    (vc_26 fun _ a _ => ⟨rfl, rfl, a⟩) ?_
  rintro j' g fl V₁ ⟨rfl, hV₁, gf⟩ U t₁ hKU hAU hrU hgU -
  subst V₁ hgU
  have hmU := Fm.fr hm gf
  refine callK E hKU hAU hrU hmU.1 (lt_len (by decide)) (call_32 _) tgt_32 E.cN (E.kN _ _ hIW) trivial ?_
  intro Z W' t₃ hKZ hAZ hrZ hsZ hkZ hBZ hIZ
  exact from37 E hKZ hAZ hrZ (fm_ret hmU hsZ hkZ) hIZ

/-- `CStdOutStream::NormalizePrint_UString_Path (this, s, tempU, tempA)` from its entry (`X`'s registers, `S` =
their `rsp`; the pushes' slots in what the run may store into, `I` of the bytes after the pushes). -/
theorem npu_ok (E : Ev prof F Wl L s₀ o gev gP gE X.cpu.gpr.rsp X.cpu.gpr I)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = npu_at)
    (hs1 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8) i))
    (hs2 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8 - 8) i))
    (hs3 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8 - 8 - 8) i)) (hI0 : I (V0 V X.cpu.gpr)) :
    GoG prof L o gev gP gE X t := by
  refine (c_0 prof).run E.c E.hin (fun j' g' _ V' => j' = 21 ∧ V' = V0 V X.cpu.gpr ∧
      Fm X.cpu.gpr.rsp X.cpu.gpr g') hK hA (by rw [addr_add_zero]; exact hrip)
    (vc_0 hs1 hs2 hs3 fun _ a b c d e m n _ => ⟨rfl, rfl, a, b, c, d, e, m, n⟩) ?_
  rintro j' g fl V₁ ⟨rfl, hV₁, hmY⟩ Y t₁ hKY hAY hrY hgY -
  subst V₁ hgY
  refine callK E hKY hAY hrY hmY.1 (lt_len (by decide)) (call_21 _) tgt_21 E.cA (E.kA _ _ hI0) trivial ?_
  intro Z W' t₃ hKZ hAZ hrZ hsZ hkZ hBZ hIZ
  exact from26 E hKZ hAZ hrZ (fm_ret hmY hsZ hkZ) hIZ

end Runs

end FV7z.Npu
