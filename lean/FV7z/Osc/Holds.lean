import FV7z.Osc.Cuts
import FV7z.Api.Holds
import FV7z.Mys.Lem
/-!
# `CStdOutStream::operator<< (const char *)` (PLAN.md §M, M1)

7-Zip 26.06's `CStdOutStream::operator<< (const char *s)` at `0x5f4be0` in `7zzs` (`CPP/Common/StdOutStream.cpp`;
`objdump -d`): `fputs (s, _stream); return *this;` with `_stream` at `this`. `this` = `rdi` (kept in `r12`), `s` =
`rsi`, `S` the stack pointer at the entry: `push r12` (`P1`), `r12 = this`, `rdi = s`, `rsi = _stream` (0..16); the
`call` (16) of `fputs` at `0x624cc0` (a hypothesis, `kC`: at its entry with those arguments and the return address at
`S - 16`; from its return at 21 with `rsp` = `S - 8`, the callee-saved registers kept and `I` of the bytes);
`rax = r12`, `pop r12` (21..26), the `ret` (26). The landing pad after the `ret` (from 0x1b) is not covered.

The bytes at 21 are the caller's invariant `I` (held by the bytes after the push, `hI0`; given back by `fputs`); they
give the saved `r12` and the return address (`hIs`).

- `call_16`, `tgt_16`, `ret_26`: the instructions outside the blocks.
- `P1`, `KC`: the bytes after the push, the callee.
- `vc_0`, `vc_21`: the pieces; `osc_ok`: the function (it returns `this` in `rax`).
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn FV7z.Mys
open FV7z.Api (KS)
namespace FV7z.Osc
set_option linter.unusedVariables false

/-! ## The instructions outside the blocks -/

/-- The `call` of `fputs` (16). -/
def pc16 : List Byte := [0xe8, 0xcb, 0x00, 0x03, 0x00]
theorem pc16_0 : ∀ feat, Dec feat pc16 0 (FV7z.mk .call 64 [.rel 196811] 5) := by dec_rfl
theorem wc_16 : pc16 <+: osc.drop 16 := by decide +kernel
theorem call_16 (feat : Features) : Dec feat osc 16 (FV7z.mk .call 64 [.rel 196811] 5) :=
  Dec.shift (j := 16) (k := 0) (pc16_0 feat) wc_16 (Nat.zero_le _)
theorem tgt_16 : osc_at.add (16 + 5) + BitVec.ofNat 64 196811 = 0x624cc0#64 := by decide

/-- The `ret` (26). -/
def pret : List Byte := [0xc3]
theorem pret_0 : ∀ feat, Dec feat pret 0 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem w_26 : pret <+: osc.drop 26 := by decide +kernel
theorem ret_26 (feat : Features) : Dec feat osc 26 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 26) (k := 0) (pret_0 feat) w_26 (Nat.zero_le _)

/-! ## The bytes and the callee -/

/-- The bytes after `push r12`. -/
abbrev P1 (V : Addr → Byte) (g : Gprs) : Addr → Byte := Vst V (g.rsp - 8) (toBytesLE g.r12 8)

/-- The callee from the `call` at 16 (entry `ent`, the bytes `W`, the registers `A`): at its entry, and from its
return at 21 with `rsp` = `S - 8`, the callee-saved registers as at its entry, `B` and the invariant `J`, the run
goes on to the goal. -/
def KC (prof : Profile) (F : Footprint) (Wl : List Rgn) (L : List (Addr × List Byte)) (s₀ : State) (o : Oracle)
    (gev : List Event) (gP : State → Nat → List Event → Prop) (gE : Outcome → List Event → Prop)
    (S : Addr) (J : (Addr → Byte) → Prop) (ent : Addr) (W : Addr → Byte) (A B : Gprs → Prop) : Prop :=
  ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y →
    Agree F Y.proc.mm.mem (Vst W (S - 8 - 8) (toBytesLE (osc_at.add 21) 8)) →
    Y.cpu.rip = ent → Y.cpu.gpr.rsp = S - 8 - 8 → A Y.cpu.gpr →
    (∀ (Z : State) (W' : Addr → Byte) (t'' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem W' →
      Z.cpu.rip = osc_at.add 21 → Z.cpu.gpr.rsp = S - 8 → KS Y.cpu.gpr Z.cpu.gpr → B Z.cpu.gpr → J W' →
      GoG prof L o gev gP gE Z t'') →
    GoG prof L o gev gP gE Y t'

/-! ## The pieces -/

variable {F : Footprint} {Wl : List Rgn}

/-- `push r12; mov r12, rdi; mov rdi, rsi; mov rsi, [r12]`: to the `call` at 16. -/
theorem vc_0 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (hs1 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8) i))
    (f0 : ∀ i < 8, Foot F.data (Addr.add g.rdi i))
    (h : ∀ g', g'.rsp = g.rsp - 8 → g'.r12 = g.rdi → g'.rdi = g.rsi → g'.rsi = rdq(P1 V g, g.rdi) →
      g'.rbx = g.rbx → g'.rbp = g.rbp → g'.r13 = g.r13 → g'.r14 = g.r14 → g'.r15 = g.r15 →
      ∀ fl, Q 16 g' fl (P1 V g)) :
    W_0 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [P1] at hs1 f0 h ⊢
  wpx [W_0, o0]
  all_goals repeat' (first
    | refine h _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ _
    | with_reducible exact hs1
    | with_reducible exact f0
    | with_reducible rfl
    | exact rfl
    | apply And.intro
    | intro _)

/-- At 21, back from `fputs`: `mov rax, r12; pop r12`, to the `ret` at 26. -/
theorem vc_21 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (fp : ∀ i < 8, Foot F.data (Addr.add g.rsp i))
    (h : ∀ g', g'.rsp = g.rsp + 8 → g'.rax = g.r12 → g'.r12 = rdq(V, g.rsp) → g'.rbx = g.rbx →
      g'.rbp = g.rbp → g'.r13 = g.r13 → g'.r14 = g.r14 → g'.r15 = g.r15 → ∀ fl, Q 26 g' fl V) :
    W_21 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at fp h ⊢
  wpx [W_21, o1]
  all_goals repeat' (first
    | refine h _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ _
    | with_reducible exact fp
    | with_reducible rfl
    | exact rfl
    | apply And.intro
    | intro _)

/-! ## The function -/

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {X : State} {t : Nat} {V : Addr → Byte}

/-- `CStdOutStream::operator<< (const char *)` from its entry (`X`'s registers, `S` = their `rsp`, `this` = their
`rdi`, `s` = their `rsi`): the push's slot and the `call`'s return address slot in what the run may store into;
`_stream` and the return address readable. `fputs` (`kC`, with `rdi` = `s`, `rsi` = `_stream`) from the bytes after
the push (`hI0`) to bytes of `I`; bytes of `I` give the saved `r12` and the return address (`hIs`). At the return
address (`kr`): the bytes of `I`, the registers a call keeps (`Str.Back`), `rax` = `this`. -/
theorem osc_ok {I : (Addr → Byte) → Prop} {e₂ : Addr} {code₂ : List Byte} {j₂ : Nat}
    (c : Seg prof F Wl L s₀ o) (hin : CodeIn L osc_at osc) (hin₂ : CodeIn L e₂ code₂)
    (h₂ : j₂ < code₂.length)
    {cP : List Byte} (hinP : CodeIn L 0x624cc0#64 cP) (hP : 0 < cP.length)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = osc_at)
    (hs1 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8) i))
    (hr8 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8 - 8) i))
    (hl : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsp i))
    (f0 : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rdi i))
    (hI0 : I (P1 V X.cpu.gpr))
    (hIs : ∀ W, I W → rdq(W, X.cpu.gpr.rsp - 8) = X.cpu.gpr.r12 ∧ rdq(W, X.cpu.gpr.rsp) = e₂.add j₂)
    (kC : KC prof F Wl L s₀ o gev gP gE X.cpu.gpr.rsp I 0x624cc0#64 (P1 V X.cpu.gpr)
      (fun g => g.rdi = X.cpu.gpr.rsi ∧ g.rsi = rdq(P1 V X.cpu.gpr, X.cpu.gpr.rdi)) (fun _ => True))
    (kr : ∀ (W : Addr → Byte) (Z : State) (t' : Nat), I W → KeptW Wl s₀ Z → Agree F Z.proc.mm.mem W →
      Z.cpu.rip = e₂.add j₂ → Str.Back X.cpu.gpr Z.cpu.gpr → Z.cpu.gpr.rax = X.cpu.gpr.rdi →
      GoG prof L o gev gP gE Z t') :
    GoG prof L o gev gP gE X t := by
  have g1 : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rsp - 8) i) := fun i hi => c.hws _ (hs1 i hi)
  have hr0 : X.cpu.rip = osc_at.add 0 := by rw [addr_add_zero]; exact hrip
  refine (c_0 prof).run c hin (fun j' g' _ V' => j' = 16 ∧ V' = P1 V X.cpu.gpr ∧
      g'.rsp = X.cpu.gpr.rsp - 8 ∧ g'.r12 = X.cpu.gpr.rdi ∧ g'.rdi = X.cpu.gpr.rsi ∧
      g'.rsi = rdq(P1 V X.cpu.gpr, X.cpu.gpr.rdi) ∧ g'.rbx = X.cpu.gpr.rbx ∧ g'.rbp = X.cpu.gpr.rbp ∧
      g'.r13 = X.cpu.gpr.r13 ∧ g'.r14 = X.cpu.gpr.r14 ∧ g'.r15 = X.cpu.gpr.r15)
    hK hA hr0
    (vc_0 (g := X.cpu.gpr) hs1 f0 fun _ a b d e p q r s u _ => ⟨rfl, rfl, a, b, d, e, p, q, r, s, u⟩) ?_
  rintro j' g fl V₁ ⟨rfl, hV₁, gs, g12, gdi, gsi, gb, gp, g13, g14, g15⟩ U t₁ hKU hAU hrU hgU -
  subst V₁ hgU
  have hU : U.cpu.gpr.rsp - 8 = X.cpu.gpr.rsp - 8 - 8 := by rw [gs]
  refine c.s_call hKU hAU hin (lt_len (by decide)) hrU (call_16 _) hinP hP tgt_16 (by rw [hU]; exact hr8) ?_
  rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
  rw [hU] at hA₂
  refine kC Y₂ t₂ hK₂ hA₂ hr₂ (by rw [hg₂]; exact hU) (by rw [hg₂]; exact ⟨gdi, gsi⟩) ?_
  intro Z W' t₃ hKZ hAZ hrZ hsZ hkZ _ hIZ
  rw [hg₂] at hkZ
  obtain ⟨o1, o2⟩ := hIs W' hIZ
  refine (c_21 prof).run c hin (fun j' g' _ V' => j' = 26 ∧ V' = W' ∧ g'.rsp = Z.cpu.gpr.rsp + 8 ∧
      g'.rax = Z.cpu.gpr.r12 ∧ g'.r12 = rdq(W', Z.cpu.gpr.rsp) ∧ g'.rbx = Z.cpu.gpr.rbx ∧
      g'.rbp = Z.cpu.gpr.rbp ∧ g'.r13 = Z.cpu.gpr.r13 ∧ g'.r14 = Z.cpu.gpr.r14 ∧ g'.r15 = Z.cpu.gpr.r15)
    hKZ hAZ hrZ
    (vc_21 (g := Z.cpu.gpr) (by rw [hsZ]; exact g1)
      fun _ a b d e p q r s _ => ⟨rfl, rfl, a, b, d, e, p, q, r, s⟩) ?_
  rintro j' g fl V₁ ⟨rfl, hV, ss, sa, s12, sb, sp, s13, s14, s15⟩ U₂ t₄ hKU₂ hAU₂ hrU₂ hgU₂ -
  rw [hV] at hAU₂
  rw [← hgU₂] at ss sa s12 sb sp s13 s14 s15
  have hsU : U₂.cpu.gpr.rsp = X.cpu.gpr.rsp := by rw [ss, hsZ]; exact BitVec.sub_add_cancel _ _
  have hkp : Kp X.cpu.gpr U₂.cpu.gpr :=
    ⟨hsU, sb.trans (hkZ.1.trans gb), sp.trans (hkZ.2.1.trans gp), s12.trans (by rw [hsZ]; exact o1),
      s13.trans (hkZ.2.2.2.1.trans g13), s14.trans (hkZ.2.2.2.2.1.trans g14), s15.trans (hkZ.2.2.2.2.2.trans g15)⟩
  have hax : U₂.cpu.gpr.rax = X.cpu.gpr.rdi := sa.trans (hkZ.2.2.1.trans g12)
  exact ret_back c hin (lt_len (by decide)) (ret_26 _) hKU₂ hAU₂ hrU₂ hkp hl hin₂ h₂ o2
    fun Z' t'' hK' hA' hr' hb ha => kr W' Z' t'' hIZ hK' hA' hr' hb (ha.trans hax)

end FV7z.Osc
