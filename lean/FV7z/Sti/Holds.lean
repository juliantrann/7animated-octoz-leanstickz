import FV7z.Sti.Cuts
import FV7z.Api.Holds
import FV7z.Tun.Inv
/-!
# `StringToUInt32 (const wchar_t *, UInt32 &)` (PLAN.md §M, M1)

7-Zip 26.06's `StringToUInt32 (s, v)` at `0x5a6760` in `7zzs` (`CPP/7zip/UI/Common/ArchiveCommandLine.cpp`;
`objdump -d`): `const wchar_t *end; v = ConvertStringToUInt32 (s, &end); return *end == 0;`. `s` = `rdi`, `v`'s
address = `rsi` (kept in `rbx`), `S` the stack pointer at the entry: `push rbx; sub rsp, 0x10` (`aR S`), `end` at
`aR S`, the stack guard (`fs:0x28`) stored at `aR S + 8`. The `call` (27) of `ConvertStringToUInt32` at `0x451230`
(a hypothesis, `kC`: at its entry with `rdi` = `s`, `rsi` = `aR S` and the return address at `aR S - 8`; from its
return with `rsp` = `aR S`, the callee-saved registers kept and `I` of the bytes). Back (32): `eax` into `v`
(`Wst`), `*end` read (`setz al`, the return value, not followed), the stack guard checked, `add rsp, 0x10; pop rbx`
to the `ret` (66). Not covered: `__stack_chk_fail` (67).

The bytes after the callee are the caller's invariant `I` (held by the bytes after the prologue, `hI0`). With any
32 bits stored at `v` (`hIs`) they give the stack (`Stk`: the saved `rbx`, the return address, the guard equal to the
one at `fs:0x28`) and `end`'s 4 bytes readable.

- `call_27`, `tgt_27`, `ret_66`: the instructions outside the blocks.
- `aR`, `P1`, `V0`, `Wst`, `Stk`, `KC`: the frame, the bytes, the stack, the callee as a continuation.
- `vc_0`, `vc_32`: the pieces; `sti_ok`: the function.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
open FV7z.Api (KS)
namespace FV7z.Sti
set_option linter.unusedVariables false

/-! ## The instructions outside the blocks -/

/-- The `call` of `ConvertStringToUInt32` (27). -/
def pc27 : List Byte := [0xe8, 0xb0, 0xaa, 0xea, 0xff]
theorem pc27_0 : ∀ feat, Dec feat pc27 0 (FV7z.mk .call 64 [.rel 18446744073708153520] 5) := by dec_rfl
theorem wc_27 : pc27 <+: sti.drop 27 := by decide +kernel
theorem call_27 (feat : Features) : Dec feat sti 27 (FV7z.mk .call 64 [.rel 18446744073708153520] 5) :=
  Dec.shift (j := 27) (k := 0) (pc27_0 feat) wc_27 (Nat.zero_le _)
theorem tgt_27 : sti_at.add (27 + 5) + BitVec.ofNat 64 18446744073708153520 = 0x451230#64 := by decide

/-- The `ret` (66). -/
def pret : List Byte := [0xc3]
theorem pret_0 : ∀ feat, Dec feat pret 0 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem w_66 : pret <+: sti.drop 66 := by decide +kernel
theorem ret_66 (feat : Features) : Dec feat sti 66 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 66) (k := 0) (pret_0 feat) w_66 (Nat.zero_le _)

/-! ## The frame -/

/-- The stack pointer after `push rbx` and `sub rsp, 0x10`. -/
abbrev aR (S : Addr) : Addr := S - 8 - 16#64

/-- The bytes after `push rbx`. -/
abbrev P1 (V : Addr → Byte) (g : Gprs) : Addr → Byte := Vst V (g.rsp - 8) (toBytesLE g.rbx 8)

/-- The bytes after the prologue: the push, the stack guard stored. -/
abbrev V0 (fb : Addr) (V : Addr → Byte) (g : Gprs) : Addr → Byte :=
  Vst (P1 V g) (aR g.rsp + 8#64) (toBytesLE rdq(P1 V g, fb + 40#64) 8)

/-- The bytes with `eax` stored at `rbx` (`v`). -/
abbrev Wst (V : Addr → Byte) (g : Gprs) : Addr → Byte :=
  Vst V g.rbx (toBytesLE (BitVec.setWidth 32 g.rax) 4)

theorem q1 (S : Addr) : aR S + 16#64 = S - 8 := BitVec.sub_add_cancel _ _
theorem q2 (S : Addr) : aR S + 16#64 + 8 = S := by rw [q1, BitVec.sub_add_cancel]

/-- The stack (`fb` the `fs` base, `ra` the return address): the saved `rbx`, the return address, the stack guard as
at `fs:0x28`. -/
abbrev Stk (fb : Addr) (W : Addr → Byte) (S : Addr) (g0 : Gprs) (ra : Addr) : Prop :=
  rdq(W, S - 8) = g0.rbx ∧ rdq(W, S) = ra ∧ rdq(W, aR S + 8#64) = rdq(W, fb + 40#64)

/-- A callee from the `call` before `j` (entry `ent`, the bytes `W`, the registers `A`): at its entry, and from its
return at `j` with `rsp` = `aR S`, the callee-saved registers as at its entry, `B` and the invariant `J`, the run
goes on to the goal. -/
def KC (prof : Profile) (F : Footprint) (Wl : List Rgn) (L : List (Addr × List Byte)) (s₀ : State) (o : Oracle)
    (gev : List Event) (gP : State → Nat → List Event → Prop) (gE : Outcome → List Event → Prop)
    (S : Addr) (J : (Addr → Byte) → Prop) (ent : Addr) (j : Nat) (W : Addr → Byte) (A B : Gprs → Prop) : Prop :=
  ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y →
    Agree F Y.proc.mm.mem (Vst W (aR S - 8) (toBytesLE (sti_at.add j) 8)) →
    Y.cpu.rip = ent → Y.cpu.gpr.rsp = aR S - 8 → A Y.cpu.gpr →
    (∀ (Z : State) (W' : Addr → Byte) (t'' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem W' →
      Z.cpu.rip = sti_at.add j → Z.cpu.gpr.rsp = aR S → KS Y.cpu.gpr Z.cpu.gpr → B Z.cpu.gpr → J W' →
      GoG prof L o gev gP gE Z t'') →
    GoG prof L o gev gP gE Y t'

/-! ## The pieces -/

variable {F : Footprint} {Wl : List Rgn}

/-- `push rbx; mov rbx, rsi; sub rsp, 0x10`, the stack guard stored, `xor eax, eax; mov rsi, rsp`, to the `call` at
27. -/
theorem vc_0 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} {cn : BitVec 64}
    (hcn : rdq(P1 V g, fb + 40#64) = cn)
    (hs1 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8) i))
    (hcl : ∀ i < 8, Foot F.data (Addr.add (fb + 40#64) i))
    (hw : ∀ i < 8, Foot Wl (Addr.add (aR g.rsp + 8#64) i))
    (h : ∀ g', g'.rsp = aR g.rsp → g'.rbx = g.rsi → g'.rsi = aR g.rsp → g'.rdi = g.rdi → g'.rbp = g.rbp →
      g'.r12 = g.r12 → g'.r13 = g.r13 → g'.r14 = g.r14 → g'.r15 = g.r15 →
      ∀ fl, Q 27 g' fl (Vst (P1 V g) (aR g.rsp + 8#64) (toBytesLE cn 8))) :
    W_0 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [aR, P1] at hcn hs1 hw h ⊢
  wpx [W_0, o0, Op.ldf, hcn]
  all_goals repeat' (first
    | refine h _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ _
    | with_reducible exact hs1
    | with_reducible exact hcl
    | with_reducible exact hw
    | with_reducible rfl
    | with_reducible assumption
    | exact rfl
    | apply And.intro
    | intro _)

/-- Back from `ConvertStringToUInt32`, at 32: `mov [rbx], eax` (`Wst`), `rax` = `end`, `eax` = `*end`, `test`,
`sete al`, the stack guard checked (`hc`), `add rsp, 0x10; pop rbx`, to the `ret` at 66. -/
theorem vc_32 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (fw : ∀ i < 4, Foot Wl (Addr.add g.rbx i))
    (f0 : ∀ i < 8, Foot F.data (Addr.add g.rsp i))
    (fe : ∀ i < 4, Foot F.data (Addr.add rdq(Wst V g, g.rsp) i))
    (hc : rdq(Wst V g, g.rsp + 8#64) = rdq(Wst V g, fb + 40#64))
    (f8 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8#64) i))
    (fcl : ∀ i < 8, Foot F.data (Addr.add (fb + 40#64) i))
    (f1 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 16#64) i))
    (h : ∀ g', g'.rsp = g.rsp + 16#64 + 8 → g'.rbx = rdq(Wst V g, g.rsp + 16#64) → g'.rbp = g.rbp →
      g'.r12 = g.r12 → g'.r13 = g.r13 → g'.r14 = g.r14 → g'.r15 = g.r15 → ∀ fl, Q 66 g' fl (Wst V g)) :
    W_32 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [Wst] at fw f0 fe hc f8 f1 h ⊢
  have z0 : ((0#64 : BitVec 64) == 0) = true := by decide
  wpx [W_32, W_61, o1, o2, Op.setcc, Op.xormf, hc, BitVec.xor_self, z0, decide_true, Bool.not_true,
    Bool.false_eq_true, false_implies, eq_self_iff_true, true_implies]
  all_goals repeat' (first
    | refine h _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ _
    | with_reducible rfl
    | with_reducible exact fw
    | with_reducible exact f0
    | with_reducible exact fe
    | with_reducible exact f8
    | with_reducible exact fcl
    | with_reducible exact f1
    | apply And.intro
    | intro _)

/-! ## The function -/

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {X : State} {t : Nat} {V : Addr → Byte}

/-- `StringToUInt32 (s, v)` from its entry (`X`'s registers, `S` = their `rsp`, `fb` the `fs` base): the push's
slot, the guard's slot, the `call`'s return address slot and `v`'s 4 bytes in what the run may store into; the
guard at `fs:0x28`, `end` (`aR S`) and the return address readable. `ConvertStringToUInt32` (`kC`) from the bytes
after the prologue (`hI0`) to bytes of `I`; with `v` stored they give the stack and `end`'s 4 bytes readable (`hIs`).
At the return address (`kr`): `rsp` 8 above the entry's, the callee-saved registers as they were, the bytes of `I`
with 32 bits stored at `v`. -/
theorem sti_ok {fb : Addr} {I : (Addr → Byte) → Prop} {e₂ : Addr} {code₂ : List Byte} {j₂ : Nat}
    (c : Seg prof F Wl L s₀ o) (hfs : s₀.cpu.seg.fsBase = fb) (hin : CodeIn L sti_at sti)
    (hin₂ : CodeIn L e₂ code₂) (h₂ : j₂ < code₂.length)
    {cC : List Byte} (hinC : CodeIn L 0x451230#64 cC) (hC : 0 < cC.length)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = sti_at)
    (hcl : ∀ i < 8, Foot F.data (Addr.add (fb + 40#64) i))
    (hs1 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8) i))
    (hw : ∀ i < 8, Foot Wl (Addr.add (aR X.cpu.gpr.rsp + 8#64) i))
    (hr8 : ∀ i < 8, Foot Wl (Addr.add (aR X.cpu.gpr.rsp - 8) i))
    (fw : ∀ i < 4, Foot Wl (Addr.add X.cpu.gpr.rsi i))
    (f0 : ∀ i < 8, Foot F.data (Addr.add (aR X.cpu.gpr.rsp) i))
    (hl : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsp i))
    (hI0 : I (V0 fb V X.cpu.gpr))
    (hIs : ∀ W (v : BitVec 32), I W →
      Stk fb (Vst W X.cpu.gpr.rsi (toBytesLE v 4)) X.cpu.gpr.rsp X.cpu.gpr (e₂.add j₂) ∧
        ∀ i < 4, Foot F.data (Addr.add rdq(Vst W X.cpu.gpr.rsi (toBytesLE v 4), aR X.cpu.gpr.rsp) i))
    (kC : KC prof F Wl L s₀ o gev gP gE X.cpu.gpr.rsp I 0x451230#64 32 (V0 fb V X.cpu.gpr)
      (fun g => g.rdi = X.cpu.gpr.rdi ∧ g.rsi = aR X.cpu.gpr.rsp) (fun _ => True))
    (kr : ∀ (W : Addr → Byte) (v : BitVec 32) (Z' : State) (t' : Nat), I W → KeptW Wl s₀ Z' →
      Agree F Z'.proc.mm.mem (Vst W X.cpu.gpr.rsi (toBytesLE v 4)) → Z'.cpu.rip = e₂.add j₂ →
      Z'.cpu.gpr.rsp = X.cpu.gpr.rsp + 8 → KS X.cpu.gpr Z'.cpu.gpr → GoG prof L o gev gP gE Z' t') :
    GoG prof L o gev gP gE X t := by
  have f8 : ∀ i < 8, Foot F.data (Addr.add (aR X.cpu.gpr.rsp + 8#64) i) := fun i hi => c.hws _ (hw i hi)
  have g1 : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rsp - 8) i) := fun i hi => c.hws _ (hs1 i hi)
  -- the prologue, to the `call`
  refine (c_0 prof fb).run c hfs hin (fun j' g' _ V' => j' = 27 ∧ V' = V0 fb V X.cpu.gpr ∧
      g'.rsp = aR X.cpu.gpr.rsp ∧ g'.rbx = X.cpu.gpr.rsi ∧ g'.rsi = aR X.cpu.gpr.rsp ∧
      g'.rdi = X.cpu.gpr.rdi ∧ g'.rbp = X.cpu.gpr.rbp ∧ g'.r12 = X.cpu.gpr.r12 ∧ g'.r13 = X.cpu.gpr.r13 ∧
      g'.r14 = X.cpu.gpr.r14 ∧ g'.r15 = X.cpu.gpr.r15) hK hA (by rw [addr_add_zero]; exact hrip)
    (vc_0 rfl hs1 hcl hw fun _ a b d e p q r s u _ => ⟨rfl, rfl, a, b, d, e, p, q, r, s, u⟩) ?_
  rintro j' g fl V₁ ⟨rfl, hV₁, gs0, gb0, gsi0, gdi0, gp0, g120, g130, g140, g150⟩ U t₁ hKU hAU hrU hgU -
  subst V₁ hgU
  -- the `call` of `ConvertStringToUInt32`
  have hU : U.cpu.gpr.rsp - 8 = aR X.cpu.gpr.rsp - 8 := by rw [gs0]
  refine c.s_call hKU hAU hin (lt_len (by decide)) hrU (call_27 _) hinC hC tgt_27 (by rw [hU]; exact hr8) ?_
  rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
  rw [hU] at hA₂
  refine kC Y₂ t₂ hK₂ hA₂ hr₂ (by rw [hg₂]; exact hU) (by rw [hg₂]; exact ⟨gdi0, gsi0⟩) ?_
  intro Z W' t₃ hKZ hAZ hrZ hsZ hkZ hBZ hIZ
  rw [hg₂] at hkZ
  -- back at 32: `v` stored, `*end`, the guard, the pop, the `ret`
  obtain ⟨⟨s1, s2, s3⟩, fe⟩ := hIs W' (BitVec.setWidth 32 Z.cpu.gpr.rax) hIZ
  have zb : Z.cpu.gpr.rbx = X.cpu.gpr.rsi := hkZ.1.trans gb0
  have hW : Wst W' Z.cpu.gpr = Vst W' X.cpu.gpr.rsi (toBytesLE (BitVec.setWidth 32 Z.cpu.gpr.rax) 4) := by
    show Vst W' Z.cpu.gpr.rbx _ = _
    rw [zb]
  refine (c_32 prof fb).run c hfs hin (fun j' g' _ V' => j' = 66 ∧ V' = Wst W' Z.cpu.gpr ∧
      g'.rsp = Z.cpu.gpr.rsp + 16#64 + 8 ∧ g'.rbx = rdq(Wst W' Z.cpu.gpr, Z.cpu.gpr.rsp + 16#64) ∧
      g'.rbp = Z.cpu.gpr.rbp ∧ g'.r12 = Z.cpu.gpr.r12 ∧ g'.r13 = Z.cpu.gpr.r13 ∧ g'.r14 = Z.cpu.gpr.r14 ∧
      g'.r15 = Z.cpu.gpr.r15) hKZ hAZ hrZ
    (vc_32 (by rw [zb]; exact fw) (by rw [hsZ]; exact f0) (by rw [hW, hsZ]; exact fe)
      (by rw [hW, hsZ]; exact s3) (by rw [hsZ]; exact f8) hcl (by rw [hsZ, q1]; exact g1)
      fun _ a b d e p q r _ => ⟨rfl, rfl, a, b, d, e, p, q, r⟩) ?_
  rintro j' g fl V₁ ⟨rfl, hV₁, gs, gb, gp, g12, g13, g14, g15⟩ U' t₄ hKU' hAU' hrU' hgU' -
  subst V₁ hgU'
  have hsU : U'.cpu.gpr.rsp = X.cpu.gpr.rsp := by rw [gs, hsZ, q2]
  refine c.s_ret hKU' hAU' hin (lt_len (by decide)) hrU' (ret_66 _) (by rw [hsU]; exact hl) hin₂ h₂
    (by rw [hsU, hW]; exact s2) ?_
  rintro Z' t₅ hKZ' hAZ' ⟨hrZ', hgZ'⟩
  refine kr W' (BitVec.setWidth 32 Z.cpu.gpr.rax) Z' t₅ hIZ hKZ' (by rw [← hW]; exact hAZ') hrZ' ?_ ?_
  · rw [hgZ']
    show U'.cpu.gpr.rsp + 8 = _
    rw [hsU]
  · rw [hgZ']
    exact ⟨gb.trans (by rw [hW, hsZ, q1]; exact s1), gp.trans (hkZ.2.1.trans gp0),
      g12.trans (hkZ.2.2.1.trans g120), g13.trans (hkZ.2.2.2.1.trans g130),
      g14.trans (hkZ.2.2.2.2.1.trans g140), g15.trans (hkZ.2.2.2.2.2.trans g150)⟩

end FV7z.Sti
