import FV7z.Psp.Cuts
import FV7z.Api.Holds
import FV7z.Tun.Inv
/-!
# `PrintSpaces (numSpaces)` (0x5ebdd0): from the entry to the return (PLAN.md §M, M1)

7-Zip 26.06's `PrintSpaces (unsigned numSpaces)` (`CPP/7zip/UI/Console/List.cpp`, the part GCC split off as
`.part.0`, called with `numSpaces` > 0; `objdump -d`) at `0x5ebdd0` in `7zzs`: `g_StdOut << kSpaces + (32 -
numSpaces)`, inlined as `fputs (kSpaces + (32 - numSpaces), g_StdOut._stream)`, `kSpaces` the 32 spaces at
`0x6ea260`. `numSpaces` = `edi`; `S` the stack pointer at the entry, 8 bytes of frame (`aR S`), no stack guard.
`rdi` = `0x6ea260 + (32 - edi)` (32-bit difference, zero-extended), `rsi` = the `FILE *` at `0x79ed70`
(`g_StdOut._stream`), then the `call` (35) of `fputs` at `0x624cc0` (its code a hypothesis, `Ev.kF`: the run from its
entry with those arguments to its return), then `add rsp, 8` and the `ret` (44). The landing pad after the `ret`
(45) is not on these runs.

- `call_35`, `tgt_35`, `ret_44`: the instructions outside the blocks.
- `aR`, `q1`, `Fm`, `ks_trans`, `KC`, `Ev`: the frame, the frame's registers, the callee as a continuation, the
  hypotheses of the runs.
- `spc`: the string's address; `vc_0`, `vc_40`: the pieces.
- `psp_ok`: from the entry (`S` = the entry's `rsp`, `g0` = its registers, `I` of the bytes) to the return
  (`Ev.kr`: `rsp` 8 up, the callee-saved registers as at the entry, `I` of the bytes) or the callee's goal.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
open FV7z.Api (KS)
namespace FV7z.Psp
set_option linter.unusedVariables false

/-! ## The instructions outside the blocks -/

/-- The `call` of `fputs` (35). -/
def pc35 : List Byte := [0xe8, 0xc8, 0x8e, 0x03, 0x00]
theorem pc35_0 : ∀ feat, Dec feat pc35 0 (FV7z.mk .call 64 [.rel 233160] 5) := by dec_rfl
theorem wc_35 : pc35 <+: psp.drop 35 := by decide +kernel
theorem call_35 (feat : Features) : Dec feat psp 35 (FV7z.mk .call 64 [.rel 233160] 5) :=
  Dec.shift (j := 35) (k := 0) (pc35_0 feat) wc_35 (Nat.zero_le _)
theorem tgt_35 : psp_at.add (35 + 5) + BitVec.ofNat 64 233160 = 0x624cc0#64 := by decide

/-- The `ret` (44). -/
def pret : List Byte := [0xc3]
theorem pret_0 : ∀ feat, Dec feat pret 0 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem w_44 : pret <+: psp.drop 44 := by decide +kernel
theorem ret_44 (feat : Features) : Dec feat psp 44 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 44) (k := 0) (pret_0 feat) w_44 (Nat.zero_le _)

/-! ## The frame -/

/-- `kSpaces + (32 - n)`: `0x6ea260` plus the 32-bit difference `32 - n`, zero-extended. -/
abbrev spc (n : BitVec 64) : Addr := BitVec.setWidth 64 (32#32 - n.setWidth 32) + 7250528#64

/-- The stack pointer after `sub rsp, 8`. -/
abbrev aR (S : Addr) : Addr := S - 8#64

theorem q1 (S : Addr) : aR S + 8#64 = S := BitVec.sub_add_cancel _ _

/-- The frame from the prologue on: `rsp` = `aR S`, the callee-saved registers as at the entry. -/
abbrev Fm (S : Addr) (g0 g : Gprs) : Prop := g.rsp = aR S ∧ KS g0 g

theorem ks_trans {a b c : Gprs} (h₁ : KS a b) (h₂ : KS b c) : KS a c :=
  ⟨h₂.1.trans h₁.1, h₂.2.1.trans h₁.2.1, h₂.2.2.1.trans h₁.2.2.1, h₂.2.2.2.1.trans h₁.2.2.2.1,
    h₂.2.2.2.2.1.trans h₁.2.2.2.2.1, h₂.2.2.2.2.2.trans h₁.2.2.2.2.2⟩

/-- The callee from the `call` before `j` (entry `ent`, the bytes `W`, the registers `A`): at its entry, and from its
return at `j` with `rsp` = `aR S`, the callee-saved registers as at its entry, `B` and the invariant `J`, the run
goes on to the goal. -/
def KC (prof : Profile) (F : Footprint) (Wl : List Rgn) (L : List (Addr × List Byte)) (s₀ : State) (o : Oracle)
    (gev : List Event) (gP : State → Nat → List Event → Prop) (gE : Outcome → List Event → Prop)
    (S : Addr) (J : (Addr → Byte) → Prop) (ent : Addr) (j : Nat) (W : Addr → Byte) (A B : Gprs → Prop) : Prop :=
  ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y →
    Agree F Y.proc.mm.mem (Vst W (aR S - 8) (toBytesLE (psp_at.add j) 8)) →
    Y.cpu.rip = ent → Y.cpu.gpr.rsp = aR S - 8 → A Y.cpu.gpr →
    (∀ (Z : State) (W' : Addr → Byte) (t'' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem W' →
      Z.cpu.rip = psp_at.add j → Z.cpu.gpr.rsp = aR S → KS Y.cpu.gpr Z.cpu.gpr → B Z.cpu.gpr → J W' →
      GoG prof L o gev gP gE Z t'') →
    GoG prof L o gev gP gE Y t'

/-- The hypotheses of the runs (`S`, `g0` the entry's stack pointer and registers, `e₂.add j₂` the return address,
`I` the invariant of the bytes): the return address; the load's bytes in the footprint; `fputs` (`kF`) from its
entry with `rdi` = `spc` of the entry's `rdi` and `rsi` = the `FILE *` at `0x79ed70`, keeping `I`; the return. -/
structure Ev (prof : Profile) (F : Footprint) (Wl : List Rgn) (L : List (Addr × List Byte)) (s₀ : State)
    (o : Oracle) (gev : List Event) (gP : State → Nat → List Event → Prop) (gE : Outcome → List Event → Prop)
    (S : Addr) (g0 : Gprs) (e₂ : Addr) (code₂ : List Byte) (j₂ : Nat) (I : (Addr → Byte) → Prop) : Prop where
  c : Seg prof F Wl L s₀ o
  hin : CodeIn L psp_at psp
  hin₂ : CodeIn L e₂ code₂
  h₂ : j₂ < code₂.length
  hI : ∀ W, I W → rdq(W, S) = e₂.add j₂
  hl : ∀ i < 8, Foot F.data (Addr.add S i)
  hr8 : ∀ i < 8, Foot Wl (Addr.add (aR S - 8) i)
  fso : ∀ i < 8, Foot F.data (Addr.add (0x79ed70#64) i)
  cF : ∃ code : List Byte, CodeIn L 0x624cc0#64 code ∧ 0 < code.length
  kF : ∀ j W, I W → KC prof F Wl L s₀ o gev gP gE S I 0x624cc0#64 j W
    (fun g => g.rdi = spc g0.rdi ∧ g.rsi = rdq(W, 0x79ed70#64)) (fun _ => True)
  kr : ∀ (W : Addr → Byte) (Z' : State) (t' : Nat), KeptW Wl s₀ Z' → Agree F Z'.proc.mm.mem W →
    Z'.cpu.rip = e₂.add j₂ → Z'.cpu.gpr.rsp = S + 8 → KS g0 Z'.cpu.gpr → I W → GoG prof L o gev gP gE Z' t'

/-! ## The pieces -/

variable {F : Footprint} {Wl : List Rgn}

/-- `r8d` = `edi`, `edi` = 32, `rax` = `0x6ea260`, `sub rsp, 8`, `edi -= r8d`, `rdi += rax`, `rax` = `0x79ed70`,
`rsi` = the pointer at `rax`, to the `call` of `fputs` at 35. -/
theorem vc_0 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (hso : ∀ i < 8, Foot F.data (Addr.add (0x79ed70#64) i))
    (h : ∀ g', g'.rsp = aR g.rsp → KS g g' → g'.rdi = spc g.rdi → g'.rsi = rdq(V, 0x79ed70#64) →
      ∀ fl, Q 35 g' fl V) :
    W_0 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [aR, spc] at h ⊢
  wpx [W_0, o0]
  all_goals repeat' (first
    | refine h _ ?_ ?_ ?_ ?_ _
    | exact hso
    | with_reducible rfl
    | exact rfl
    | apply And.intro
    | intro _
    | bv_omega)

/-- `add rsp, 8`, to the `ret` at 44. -/
theorem vc_40 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (h : ∀ g', g'.rsp = g.rsp + 8#64 → KS g g' → ∀ fl, Q 44 g' fl V) : W_40 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h ⊢
  wpx [W_40, o1]
  all_goals repeat' (first
    | refine h _ ?_ ?_ _
    | with_reducible rfl
    | exact rfl
    | apply And.intro
    | intro _)

/-! ## The runs -/

section Runs
variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {S : Addr} {g0 : Gprs} {e₂ : Addr} {code₂ : List Byte} {j₂ : Nat} {I : (Addr → Byte) → Prop}
  {Y : State} {t : Nat} {W : Addr → Byte}

/-- From 40 (back from `fputs`): the epilogue, the `ret`, to `kr`. -/
theorem from40 (E : Ev prof F Wl L s₀ o gev gP gE S g0 e₂ code₂ j₂ I) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = psp_at.add 40) (hm : Fm S g0 Y.cpu.gpr) (hIW : I W) :
    GoG prof L o gev gP gE Y t := by
  have s1 := E.hI W hIW
  have ms := hm.1
  refine (c_40 prof).run E.c E.hin (fun j' g' _ V' => j' = 44 ∧ V' = W ∧
      g'.rsp = Y.cpu.gpr.rsp + 8#64 ∧ KS Y.cpu.gpr g') hK hA hr
    (vc_40 fun _ a k _ => ⟨rfl, rfl, a, k⟩) ?_
  rintro j' g fl V₁ ⟨rfl, hV₁, gs, gk⟩ U t₁ hKU hAU hrU hgU -
  subst V₁ hgU
  have hsU : U.cpu.gpr.rsp = S := by rw [gs, ms]; exact q1 S
  refine E.c.s_ret hKU hAU E.hin (lt_len (by decide)) hrU (ret_44 _) (by rw [hsU]; exact E.hl) E.hin₂ E.h₂
    (by rw [hsU]; exact s1) ?_
  rintro Z' t₂ hKZ' hAZ' ⟨hrZ', hgZ'⟩
  refine E.kr W Z' t₂ hKZ' hAZ' hrZ' ?_ ?_ hIW
  · rw [hgZ']
    show U.cpu.gpr.rsp + 8 = _
    rw [hsU]
  · rw [hgZ']
    exact ks_trans hm.2 gk

end Runs

section Main
variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {e₂ : Addr} {code₂ : List Byte} {j₂ : Nat} {I : (Addr → Byte) → Prop}
  {X : State} {t : Nat} {V : Addr → Byte}

/-- `PrintSpaces (numSpaces)` from its entry (`X`'s registers, `S` = their `rsp`; `I` of the bytes). -/
theorem psp_ok (E : Ev prof F Wl L s₀ o gev gP gE X.cpu.gpr.rsp X.cpu.gpr e₂ code₂ j₂ I)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = psp_at) (hI0 : I V) :
    GoG prof L o gev gP gE X t := by
  refine (c_0 prof).run E.c E.hin (fun j' g' _ V' => j' = 35 ∧ V' = V ∧ Fm X.cpu.gpr.rsp X.cpu.gpr g' ∧
      g'.rdi = spc X.cpu.gpr.rdi ∧ g'.rsi = rdq(V, 0x79ed70#64)) hK hA
    (by rw [addr_add_zero]; exact hrip) (vc_0 E.fso fun _ a k d s _ => ⟨rfl, rfl, ⟨a, k⟩, d, s⟩) ?_
  rintro j' g fl V₁ ⟨rfl, hV₁, hmY, hdi, hsi⟩ Y t₁ hKY hAY hrY hgY -
  subst V₁ hgY
  obtain ⟨cc, hinc, hcc⟩ := E.cF
  have hU : Y.cpu.gpr.rsp - 8 = aR X.cpu.gpr.rsp - 8 := by rw [hmY.1]
  refine E.c.s_call hKY hAY E.hin (lt_len (by decide)) hrY (call_35 _) hinc hcc tgt_35 (by rw [hU]; exact E.hr8) ?_
  rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
  rw [hU] at hA₂
  refine E.kF _ _ hI0 Y₂ t₂ hK₂ hA₂ hr₂ (by rw [hg₂]; exact hU) (by rw [hg₂]; exact ⟨hdi, hsi⟩) ?_
  intro Z W' t₃ hKZ hAZ hrZ hsZ hkZ _ hIZ
  rw [hg₂] at hkZ
  exact from40 E hKZ hAZ hrZ ⟨hsZ, ks_trans hmY.2 hkZ⟩ hIZ

end Main

end FV7z.Psp
