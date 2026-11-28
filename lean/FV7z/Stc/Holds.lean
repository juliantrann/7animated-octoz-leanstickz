import FV7z.Stc.Cuts
import FV7z.Api.Holds
import FV7z.Tun.Inv
/-!
# `CFileBase::seekToCur` (0x4560f0): from the entry to the return (PLAN.md §M, M1)

7-Zip 26.06's `NWindows::NFile::NIO::CFileBase::seekToCur ()` (`CPP/Windows/FileIO.cpp`; `objdump -d`) at
`0x4560f0` in `7zzs`: `this` = `rdi`; `sub rsp, 8`, `edx` = 1 (`SEEK_CUR`), `esi` = 0, the `call` of
`CFileBase::seek (0, SEEK_CUR)` at `0x4560b0` (15; its code a hypothesis, `Ev.kS`), `add rsp, 8`, the `ret` (24),
`rax` = what `seek` returned.

- `call_15`, `tgt_15`, `ret_24`: the instructions outside the blocks.
- `aR`, `Fm`, `KC`, `Ev`: the frame, the callee as a continuation, the hypotheses of the run.
- `vc_0`, `vc_20`: the pieces (to the `call`; back from it, to the `ret`).
- `stc_ok`: from the entry (`S` = the entry's `rsp`, `g0` = its registers, `I` of the bytes) to the return
  (`Ev.kr`: `rsp` 8 up, the callee-saved registers as at the entry, `I` of the bytes) or the callee's goal.

Not covered: the landing pad after the code (from 25).
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
open FV7z.Api (KS)
namespace FV7z.Stc
set_option linter.unusedVariables false

/-! ## The instructions outside the blocks -/

/-- The `call` of `CFileBase::seek` (15). -/
def pc15 : List Byte := [0xe8, 0xac, 0xff, 0xff, 0xff]
theorem pc15_0 : ∀ feat, Dec feat pc15 0 (FV7z.mk .call 64 [.rel 18446744073709551532] 5) := by dec_rfl
theorem wc_15 : pc15 <+: stc.drop 15 := by decide +kernel
theorem call_15 (feat : Features) : Dec feat stc 15 (FV7z.mk .call 64 [.rel 18446744073709551532] 5) :=
  Dec.shift (j := 15) (k := 0) (pc15_0 feat) wc_15 (Nat.zero_le _)
theorem tgt_15 : stc_at.add (15 + 5) + BitVec.ofNat 64 18446744073709551532 = 0x4560b0#64 := by decide

/-- The `ret` (24). -/
def pret : List Byte := [0xc3]
theorem pret_0 : ∀ feat, Dec feat pret 0 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem w_24 : pret <+: stc.drop 24 := by decide +kernel
theorem ret_24 (feat : Features) : Dec feat stc 24 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 24) (k := 0) (pret_0 feat) w_24 (Nat.zero_le _)

/-! ## The frame -/

/-- The stack pointer after `sub rsp, 8`. -/
abbrev aR (S : Addr) : Addr := S - 8#64

theorem q1 (S : Addr) : aR S + 8#64 = S := BitVec.sub_add_cancel _ _

/-- The frame from the prologue on: `rsp` = `aR S`, the callee-saved registers as at the entry. -/
abbrev Fm (S : Addr) (g0 g : Gprs) : Prop :=
  g.rsp = aR S ∧ g.rbx = g0.rbx ∧ g.rbp = g0.rbp ∧ g.r12 = g0.r12 ∧ g.r13 = g0.r13 ∧ g.r14 = g0.r14 ∧
    g.r15 = g0.r15

/-- Back from the callee: `rsp` as before the `call`, the callee-saved registers kept. -/
theorem fm_ret {S : Addr} {g0 g g' : Gprs} (h : Fm S g0 g) (hs : g'.rsp = aR S) (hk : KS g g') : Fm S g0 g' :=
  ⟨hs, hk.1.trans h.2.1, hk.2.1.trans h.2.2.1, hk.2.2.1.trans h.2.2.2.1, hk.2.2.2.1.trans h.2.2.2.2.1,
    hk.2.2.2.2.1.trans h.2.2.2.2.2.1, hk.2.2.2.2.2.trans h.2.2.2.2.2.2⟩

/-- The callee from the `call` before `j` (entry `ent`, the bytes `W`, the registers `A`): at its entry, and from its
return at `j` with `rsp` = `aR S`, the callee-saved registers as at its entry, `B` and the invariant `J`, the run
goes on to the goal. -/
def KC (prof : Profile) (F : Footprint) (Wl : List Rgn) (L : List (Addr × List Byte)) (s₀ : State) (o : Oracle)
    (gev : List Event) (gP : State → Nat → List Event → Prop) (gE : Outcome → List Event → Prop)
    (S : Addr) (J : (Addr → Byte) → Prop) (ent : Addr) (j : Nat) (W : Addr → Byte) (A B : Gprs → Prop) : Prop :=
  ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y →
    Agree F Y.proc.mm.mem (Vst W (aR S - 8) (toBytesLE (stc_at.add j) 8)) →
    Y.cpu.rip = ent → Y.cpu.gpr.rsp = aR S - 8 → A Y.cpu.gpr →
    (∀ (Z : State) (W' : Addr → Byte) (t'' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem W' →
      Z.cpu.rip = stc_at.add j → Z.cpu.gpr.rsp = aR S → KS Y.cpu.gpr Z.cpu.gpr → B Z.cpu.gpr → J W' →
      GoG prof L o gev gP gE Z t'') →
    GoG prof L o gev gP gE Y t'

/-- The hypotheses of the run (`S`, `g0` the entry's stack pointer and registers, `e₂.add j₂` the return address,
`I` the invariant of the bytes): the return address at `S`; the callee keeps `I`; the return. -/
structure Ev (prof : Profile) (F : Footprint) (Wl : List Rgn) (L : List (Addr × List Byte)) (s₀ : State)
    (o : Oracle) (gev : List Event) (gP : State → Nat → List Event → Prop) (gE : Outcome → List Event → Prop)
    (S : Addr) (g0 : Gprs) (e₂ : Addr) (code₂ : List Byte) (j₂ : Nat) (I : (Addr → Byte) → Prop) :
    Prop where
  c : Seg prof F Wl L s₀ o
  hin : CodeIn L stc_at stc
  hin₂ : CodeIn L e₂ code₂
  h₂ : j₂ < code₂.length
  hI : ∀ W, I W → rdq(W, S) = e₂.add j₂
  hl : ∀ i < 8, Foot F.data (Addr.add S i)
  hr8 : ∀ i < 8, Foot Wl (Addr.add (aR S - 8) i)
  cS : ∃ code : List Byte, CodeIn L 0x4560b0#64 code ∧ 0 < code.length
  kS : ∀ j W, I W → KC prof F Wl L s₀ o gev gP gE S I 0x4560b0#64 j W (fun _ => True) (fun _ => True)
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

/-- `endbr64`, `sub rsp, 8`, `edx` = 1, `esi` = 0, to the `call` of `seek` at 15. -/
theorem vc_0 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (h : ∀ g', g'.rsp = aR g.rsp → KS g g' → ∀ fl, Q 15 g' fl V) :
    W_0 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [aR] at h ⊢
  wpx [W_0, o0]
  all_goals repeat' (first
    | refine h _ ?_ ?_ _
    | ostep)

/-- Back from `seek`: `add rsp, 8`, to the `ret` at 24. -/
theorem vc_20 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (h : ∀ g', g'.rsp = g.rsp + 8#64 → KS g g' → ∀ fl, Q 24 g' fl V) :
    W_20 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h ⊢
  wpx [W_20, o1]
  all_goals repeat' (first
    | refine h _ ?_ ?_ _
    | ostep)

end Pieces

/-! ## The run -/

section Runs
variable {prof : Profile} {F : Footprint} {Wl : List Rgn} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {S : Addr} {g0 : Gprs} {e₂ : Addr} {code₂ : List Byte} {j₂ : Nat} {I : (Addr → Byte) → Prop}
  {X Y : State} {t : Nat} {V W : Addr → Byte}

/-- From 20 (back from `seek`): `add rsp, 8`, the `ret`, to `kr`. -/
theorem from20 (E : Ev prof F Wl L s₀ o gev gP gE S g0 e₂ code₂ j₂ I) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = stc_at.add 20) (hm : Fm S g0 Y.cpu.gpr) (hIW : I W) :
    GoG prof L o gev gP gE Y t := by
  have ms := hm.1
  refine (c_20 prof).run E.c E.hin (fun j' g' _ V' => j' = 24 ∧ V' = W ∧
      g'.rsp = Y.cpu.gpr.rsp + 8#64 ∧ KS Y.cpu.gpr g') hK hA hr
    (vc_20 fun _ a k _ => ⟨rfl, rfl, a, k⟩) ?_
  rintro j' g fl V₁ ⟨rfl, hV₁, gs, gk⟩ U t₁ hKU hAU hrU hgU -
  subst V₁ hgU
  have hsU : U.cpu.gpr.rsp = S := by rw [gs, ms]; exact q1 S
  refine E.c.s_ret hKU hAU E.hin (lt_len (by decide)) hrU (ret_24 _) (by rw [hsU]; exact E.hl) E.hin₂ E.h₂
    (by rw [hsU]; exact E.hI W hIW) ?_
  rintro Z' t₂ hKZ' hAZ' ⟨hrZ', hgZ'⟩
  refine E.kr W Z' t₂ hKZ' hAZ' hrZ' ?_ ?_ hIW
  · rw [hgZ']
    show U.cpu.gpr.rsp + 8 = _
    rw [hsU]
  · rw [hgZ']
    exact ⟨gk.1.trans hm.2.1, gk.2.1.trans hm.2.2.1, gk.2.2.1.trans hm.2.2.2.1, gk.2.2.2.1.trans hm.2.2.2.2.1,
      gk.2.2.2.2.1.trans hm.2.2.2.2.2.1, gk.2.2.2.2.2.trans hm.2.2.2.2.2.2⟩

/-- `CFileBase::seekToCur (this)` from its entry (`X`'s registers, `S` = their `rsp`, `I` of the bytes). -/
theorem stc_ok (E : Ev prof F Wl L s₀ o gev gP gE X.cpu.gpr.rsp X.cpu.gpr e₂ code₂ j₂ I)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = stc_at) (hI0 : I V) :
    GoG prof L o gev gP gE X t := by
  refine (c_0 prof).run E.c E.hin (fun j' g' _ V' => j' = 15 ∧ V' = V ∧ Fm X.cpu.gpr.rsp X.cpu.gpr g') hK hA
    (by rw [addr_add_zero]; exact hrip) (vc_0 fun _ a k _ => ⟨rfl, rfl, a, k⟩) ?_
  rintro j' g fl V₁ ⟨rfl, hV₁, hmY⟩ Y t₁ hKY hAY hrY hgY -
  subst V₁ hgY
  obtain ⟨cc, hinc, hcc⟩ := E.cS
  have hU : Y.cpu.gpr.rsp - 8 = aR X.cpu.gpr.rsp - 8 := by rw [hmY.1]
  refine E.c.s_call hKY hAY E.hin (lt_len (by decide)) hrY (call_15 _) hinc hcc tgt_15 (by rw [hU]; exact E.hr8) ?_
  rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
  rw [hU] at hA₂
  refine E.kS _ _ hI0 Y₂ t₂ hK₂ hA₂ hr₂ (by rw [hg₂]; exact hU) trivial ?_
  intro Z W' t₃ hKZ hAZ hrZ hsZ hkZ hBZ hIZ
  rw [hg₂] at hkZ
  exact from20 E hKZ hAZ hrZ (fm_ret hmY hsZ hkZ) hIZ

end Runs

end FV7z.Stc
