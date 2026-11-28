import FV7z.Pui.Cuts
import FV7z.C64.Blocks1
import FV7z.Apc.Blocks1
import FV7z.Asp.Blocks1
import FV7z.Lemmas.LeafRet
/-!
# `Print_UInt64_and_String` (PLAN.md §M, M1)

7-Zip 26.06's `Print_UInt64_and_String (AString &s, UInt64 val, const char *name)` at `0x5e85f0` in `7zzs`
(`CPP/7zip/UI/Console/ExtractCallbackConsole.cpp`; `objdump -d`), `S` the stack pointer at the entry: `push r13;
push r12; mov r12, rdx; push rbp; mov rbp, rdi; mov rdi, rsi; sub rsp, 0x30`, the stack guard (`fs:0x28`) stored at
`aR S + 40`, `r13` = `rsi` = `aR S` (the buffer); the `call` (44) of `ConvertUInt64ToString (val, buf)`
(`C64.c64_at`); `s += buf` (55, `Apc.apc_at`); `s.Add_Space ()` (63, `Asp.asp_at`); `s += name` (74, `Apc.apc_at`);
the stack guard checked (79), `add rsp, 0x30; pop rbp; pop r12; pop r13; ret` (104).

The callees are hypotheses, as in `FV7z/Smd/Holds.lean`: each a continuation at its entry (`KC`: the bytes with the
return address at `aR S - 8`, `rsp` = `aR S - 8`, the registers it is given) that, from its return, has the frame
(`Fm`), a fact for the code after it (`N`) and its own post (`P`). The stack guard's check is not run on a failing
guard: from the return of `s += name` the stack is as it was (`Stk`: the saved registers, the return address and the
guard at `aR S + 40` equal to the one at `fs:0x28`), so `jne 105` is not taken. Not covered: `__stack_chk_fail`
(105).

- `aR`, `Sv`, `V0`, `Fr`, `Fm`, `Kf`, `KS`, `Stk`, `KC`: the frame, bytes, kept registers, the stack, contracts.
- `vc_0`, `vc_49`, `vc_60`, `vc_68`, `vc_79`: the pieces' verification conditions.
- `tail79`, `from68`, `from60`, `from49`: the runs from those offsets; `pui_ok`: the function.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Pui
set_option linter.unusedVariables false

/-! ## The instructions outside the blocks -/

/-- The `call` of `ConvertUInt64ToString`. -/
def pc1 : List Byte := [0xe8, 0x0f, 0x26, 0xe6, 0xff]
theorem pc1_0 : ∀ feat, Dec feat pc1 0 (FV7z.mk .call 64 [.rel 18446744073707857423] 5) := by intro feat f; rfl
theorem wc_44 : pc1 <+: pui.drop 44 := by decide +kernel
theorem call_44 (feat : Features) : Dec feat pui 44 (FV7z.mk .call 64 [.rel 18446744073707857423] 5) :=
  Dec.shift (j := 44) (k := 0) (pc1_0 feat) wc_44 (Nat.zero_le _)
theorem tgt_44 : pui_at.add (44 + 5) + BitVec.ofNat 64 18446744073707857423 = C64.c64_at := by decide

/-- The `call` of `AString::operator+= (const char *)` with the buffer. -/
def pc2 : List Byte := [0xe8, 0x64, 0x42, 0xe6, 0xff]
theorem pc2_0 : ∀ feat, Dec feat pc2 0 (FV7z.mk .call 64 [.rel 18446744073707864676] 5) := by intro feat f; rfl
theorem wc_55 : pc2 <+: pui.drop 55 := by decide +kernel
theorem call_55 (feat : Features) : Dec feat pui 55 (FV7z.mk .call 64 [.rel 18446744073707864676] 5) :=
  Dec.shift (j := 55) (k := 0) (pc2_0 feat) wc_55 (Nat.zero_le _)
theorem tgt_55 : pui_at.add (55 + 5) + BitVec.ofNat 64 18446744073707864676 = Apc.apc_at := by decide

/-- The `call` of `AString::Add_Space ()`. -/
def pc3 : List Byte := [0xe8, 0xbc, 0x40, 0xe6, 0xff]
theorem pc3_0 : ∀ feat, Dec feat pc3 0 (FV7z.mk .call 64 [.rel 18446744073707864252] 5) := by intro feat f; rfl
theorem wc_63 : pc3 <+: pui.drop 63 := by decide +kernel
theorem call_63 (feat : Features) : Dec feat pui 63 (FV7z.mk .call 64 [.rel 18446744073707864252] 5) :=
  Dec.shift (j := 63) (k := 0) (pc3_0 feat) wc_63 (Nat.zero_le _)
theorem tgt_63 : pui_at.add (63 + 5) + BitVec.ofNat 64 18446744073707864252 = Asp.asp_at := by decide

/-- The `call` of `AString::operator+= (const char *)` with `name`. -/
def pc4 : List Byte := [0xe8, 0x51, 0x42, 0xe6, 0xff]
theorem pc4_0 : ∀ feat, Dec feat pc4 0 (FV7z.mk .call 64 [.rel 18446744073707864657] 5) := by intro feat f; rfl
theorem wc_74 : pc4 <+: pui.drop 74 := by decide +kernel
theorem call_74 (feat : Features) : Dec feat pui 74 (FV7z.mk .call 64 [.rel 18446744073707864657] 5) :=
  Dec.shift (j := 74) (k := 0) (pc4_0 feat) wc_74 (Nat.zero_le _)
theorem tgt_74 : pui_at.add (74 + 5) + BitVec.ofNat 64 18446744073707864657 = Apc.apc_at := by decide

/-- The `ret`. -/
def pret : List Byte := [0xc3]
theorem pret_0 : ∀ feat, Dec feat pret 0 (FV7z.mk .ret 64 [] 1) := by intro feat f; rfl
theorem w_104 : pret <+: pui.drop 104 := by decide +kernel
theorem ret_104 (feat : Features) : Dec feat pui 104 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 104) (k := 0) (pret_0 feat) w_104 (Nat.zero_le _)

/-! ## The frame -/

/-- The stack pointer after the three `push`es and `sub rsp, 0x30`; the buffer there. -/
abbrev aR (S : Addr) : Addr := S - 8 - 8 - 8 - 48#64

theorem e48 (S : Addr) : aR S + 48#64 = S - 8 - 8 - 8 := by show S - 8 - 8 - 8 - 48#64 + 48#64 = _; bv_omega
theorem e56 (S : Addr) : aR S + 48#64 + 8 = S - 8 - 8 := by show S - 8 - 8 - 8 - 48#64 + 48#64 + 8 = _; bv_omega
theorem e64 (S : Addr) : aR S + 48#64 + 8 + 8 = S - 8 := by
  show S - 8 - 8 - 8 - 48#64 + 48#64 + 8 + 8 = _
  bv_omega
theorem e72 (S : Addr) : aR S + 48#64 + 8 + 8 + 8 = S := by
  show S - 8 - 8 - 8 - 48#64 + 48#64 + 8 + 8 + 8 = _
  bv_omega

/-- The bytes after the three `push`es: `r13`, `r12`, `rbp` below the stack pointer. -/
abbrev Sv (V : Addr → Byte) (g : Gprs) : Addr → Byte :=
  Vst (Vst (Vst V (g.rsp - 8) (toBytesLE g.r13 8)) (g.rsp - 8 - 8) (toBytesLE g.r12 8)) (g.rsp - 8 - 8 - 8)
    (toBytesLE g.rbp 8)

/-- The bytes at the first `call`: the three registers pushed, the stack guard stored. -/
abbrev V0 (fb : Addr) (V : Addr → Byte) (g : Gprs) : Addr → Byte :=
  Vst (Sv V g) (aR g.rsp + 40#64) (toBytesLE rdq(Sv V g, fb + 40#64) 8)

/-- What a piece keeps: `rsp`, `rbp`, `rbx`, `r12`–`r15`. -/
abbrev Fr (g g' : Gprs) : Prop :=
  g'.rsp = g.rsp ∧ g'.rbp = g.rbp ∧ g'.rbx = g.rbx ∧ g'.r12 = g.r12 ∧ g'.r13 = g.r13 ∧ g'.r14 = g.r14 ∧
    g'.r15 = g.r15

/-- The frame from 44 on: `rsp` = `r13` = `aR S`, `rbp` = `s`, `r12` = `name`, `rbx`, `r14`, `r15` as at the entry
(`g0`). -/
abbrev Fm (S : Addr) (g0 g : Gprs) : Prop :=
  g.rsp = aR S ∧ g.rbp = g0.rdi ∧ g.rbx = g0.rbx ∧ g.r12 = g0.rdx ∧ g.r13 = aR S ∧ g.r14 = g0.r14 ∧
    g.r15 = g0.r15

/-- `Fm` but `rsp`: what a callee is given. -/
abbrev Kf (S : Addr) (g0 g : Gprs) : Prop :=
  g.rbp = g0.rdi ∧ g.rbx = g0.rbx ∧ g.r12 = g0.rdx ∧ g.r13 = aR S ∧ g.r14 = g0.r14 ∧ g.r15 = g0.r15

/-- The callee-saved registers as at the entry. -/
abbrev KS (g0 g : Gprs) : Prop :=
  g.rbx = g0.rbx ∧ g.rbp = g0.rbp ∧ g.r12 = g0.r12 ∧ g.r13 = g0.r13 ∧ g.r14 = g0.r14 ∧ g.r15 = g0.r15

theorem Fm.fr {S : Addr} {g0 g g' : Gprs} (h : Fm S g0 g) (h' : Fr g g') : Fm S g0 g' :=
  ⟨h'.1.trans h.1, h'.2.1.trans h.2.1, h'.2.2.1.trans h.2.2.1, h'.2.2.2.1.trans h.2.2.2.1,
    h'.2.2.2.2.1.trans h.2.2.2.2.1, h'.2.2.2.2.2.1.trans h.2.2.2.2.2.1, h'.2.2.2.2.2.2.trans h.2.2.2.2.2.2⟩

theorem kf_set {S : Addr} {g0 g : Gprs} {x : Addr} (h : Fm S g0 g) : Kf S g0 (g.set 4 x) :=
  ⟨h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩

/-- The stack from the return of `s += name` (`fb` the `fs` base, `ra` the return address): the saved registers,
the return address, the stack guard as at `fs:0x28`. -/
abbrev Stk (fb : Addr) (W : Addr → Byte) (S : Addr) (g0 : Gprs) (ra : Addr) : Prop :=
  rdq(W, S - 8) = g0.r13 ∧ rdq(W, S - 8 - 8) = g0.r12 ∧ rdq(W, S - 8 - 8 - 8) = g0.rbp ∧ rdq(W, S) = ra ∧
    rdq(W, aR S + 40#64) = rdq(W, fb + 40#64)

/-- A callee from the `call` before `j` (entry `ent`, the bytes `W`, the registers `A`): at its entry, and from its
return at `j` with the frame, `N` and `P`, the run goes on to the goal. -/
def KC (prof : Profile) (F : Footprint) (Wl : List Rgn) (L : List (Addr × List Byte)) (s₀ : State) (o : Oracle)
    (gev : List Event) (gP : State → Nat → List Event → Prop) (gE : Outcome → List Event → Prop)
    (S : Addr) (g0 : Gprs) (ent : Addr) (j : Nat) (W : Addr → Byte) (A : Gprs → Prop)
    (N P : State → (Addr → Byte) → Prop) : Prop :=
  ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y →
    Agree F Y.proc.mm.mem (Vst W (aR S - 8) (toBytesLE (pui_at.add j) 8)) →
    Y.cpu.rip = ent → Y.cpu.gpr.rsp = aR S - 8 → A Y.cpu.gpr →
    (∀ (Z : State) (W' : Addr → Byte) (t'' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem W' →
      Z.cpu.rip = pui_at.add j → Fm S g0 Z.cpu.gpr → N Z W' → P Z W' → GoG prof L o gev gP gE Z t'') →
    GoG prof L o gev gP gE Y t'

/-! ## The pieces -/

variable {F : Footprint} {Wl : List Rgn}

/-- The pushes, `r12` = `rdx`, `rbp` = `rdi`, `rdi` = `rsi`, the frame, the stack guard stored, `r13` = `rsi` =
`rsp`, to the first `call`. The guard's value is named (`cn`). -/
theorem vc_0 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} {cn : BitVec 64}
    (hcn : rdq(Sv V g, fb + 40#64) = cn)
    (hs1 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8) i)) (hs2 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8) i))
    (hs3 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8 - 8) i))
    (hcl : ∀ i < 8, Foot F.data (Addr.add (fb + 40#64) i))
    (hw : ∀ i < 8, Foot Wl (Addr.add (aR g.rsp + 40#64) i))
    (h : ∀ g', g'.rsp = aR g.rsp → g'.rbp = g.rdi → g'.rdi = g.rsi → g'.rsi = aR g.rsp → g'.r12 = g.rdx →
      g'.r13 = aR g.rsp → g'.rbx = g.rbx → g'.r14 = g.r14 → g'.r15 = g.r15 →
      ∀ fl, Q 44 g' fl (Vst (Sv V g) (aR g.rsp + 40#64) (toBytesLE cn 8))) :
    W_0 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [aR, Sv] at hcn hs1 hs2 hs3 hw h ⊢
  wpx [W_0, o0, Op.ldf, hcn]
  all_goals repeat' (first
    | refine h _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ _
    | with_reducible rfl
    | with_reducible exact hs1
    | with_reducible exact hs2
    | with_reducible exact hs3
    | with_reducible exact hcl
    | with_reducible exact hw
    | apply And.intro
    | intro _)

/-- `mov rsi, r13; mov rdi, rbp` to the second `call`. -/
theorem vc_49 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (h : ∀ g', g'.rsi = g.r13 → g'.rdi = g.rbp → Fr g g' → ∀ fl, Q 55 g' fl V) :
    W_49 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h ⊢
  wpx [W_49, o1]
  all_goals repeat' (first
    | refine h _ ?_ ?_ ?_ _
    | with_reducible rfl
    | apply And.intro
    | intro _)

/-- `mov rdi, rbp` to the third `call`. -/
theorem vc_60 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (h : ∀ g', g'.rdi = g.rbp → Fr g g' → ∀ fl, Q 63 g' fl V) :
    W_60 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h ⊢
  wpx [W_60, o2]
  all_goals repeat' (first
    | refine h _ ?_ ?_ _
    | with_reducible rfl
    | apply And.intro
    | intro _)

/-- `mov rsi, r12; mov rdi, rbp` to the fourth `call`. -/
theorem vc_68 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (h : ∀ g', g'.rsi = g.r12 → g'.rdi = g.rbp → Fr g g' → ∀ fl, Q 74 g' fl V) :
    W_68 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h ⊢
  wpx [W_68, o3]
  all_goals repeat' (first
    | refine h _ ?_ ?_ ?_ _
    | with_reducible rfl
    | apply And.intro
    | intro _)

/-- The stack guard checked (as at `fs:0x28`: `jne` not taken), `add rsp, 0x30; pop rbp; pop r12; pop r13` to the
`ret`. -/
theorem vc_79 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (hc : rdq(V, g.rsp + 40#64) = rdq(V, fb + 40#64)) (f40 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 40#64) i))
    (fcl : ∀ i < 8, Foot F.data (Addr.add (fb + 40#64) i))
    (f48 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 48#64) i))
    (f56 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 48#64 + 8) i))
    (f64 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 48#64 + 8 + 8) i))
    (h : ∀ g', g'.rsp = g.rsp + 48#64 + 8 + 8 + 8 → g'.rbp = rdq(V, g.rsp + 48#64) →
      g'.r12 = rdq(V, g.rsp + 48#64 + 8) → g'.r13 = rdq(V, g.rsp + 48#64 + 8 + 8) → g'.rbx = g.rbx →
      g'.r14 = g.r14 → g'.r15 = g.r15 → ∀ fl, Q 104 g' fl V) :
    W_79 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hc f40 f48 f56 f64 h ⊢
  have z0 : ((0#64 : BitVec 64) == 0) = true := by decide
  wpx [W_79, W_95, o4, o5, Op.xormf, hc, BitVec.xor_self, z0, decide_true, Bool.not_true, Bool.false_eq_true,
    false_implies, eq_self_iff_true, true_implies]
  all_goals repeat' (first
    | refine h _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ _
    | with_reducible rfl
    | with_reducible exact f40
    | with_reducible exact fcl
    | with_reducible exact f48
    | with_reducible exact f56
    | with_reducible exact f64
    | apply And.intro
    | intro _)

/-! ## The runs -/

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {X : State} {t : Nat} {V : Addr → Byte} {e₂ : Addr} {code₂ : List Byte} {j₂ : Nat}

/-- From 79 (the frame, the stack `Stk`) to the return address `e₂.add j₂`. -/
theorem tail79 {fb : Addr} {W : Addr → Byte} {S : Addr} {g0 : Gprs} {Y : State} (c : Seg prof F Wl L s₀ o)
    (hfs : s₀.cpu.seg.fsBase = fb) (hin : CodeIn L pui_at pui) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = pui_at.add 79) (hm : Fm S g0 Y.cpu.gpr)
    (hst : Stk fb W S g0 (e₂.add j₂)) (hcl : ∀ i < 8, Foot F.data (Addr.add (fb + 40#64) i))
    (f40 : ∀ i < 8, Foot F.data (Addr.add (aR S + 40#64) i)) (f1 : ∀ i < 8, Foot F.data (Addr.add (S - 8) i))
    (f2 : ∀ i < 8, Foot F.data (Addr.add (S - 8 - 8) i)) (f3 : ∀ i < 8, Foot F.data (Addr.add (S - 8 - 8 - 8) i))
    (hl : ∀ i < 8, Foot F.data (Addr.add S i)) (hin₂ : CodeIn L e₂ code₂) (h₂ : j₂ < code₂.length)
    (k : ∀ (Z' : State) (t' : Nat), KeptW Wl s₀ Z' → Agree F Z'.proc.mm.mem W → Z'.cpu.rip = e₂.add j₂ →
      Z'.cpu.gpr.rsp = S + 8 → KS g0 Z'.cpu.gpr → GoG prof L o gev gP gE Z' t') :
    GoG prof L o gev gP gE Y t := by
  obtain ⟨ms, mp, mb, m12, m13, m14, m15⟩ := hm
  obtain ⟨s1, s2, s3, s4, s5⟩ := hst
  refine (c_79 prof fb).run c hfs hin (fun j' g' _ V' => j' = 104 ∧ V' = W ∧
      g'.rsp = Y.cpu.gpr.rsp + 48#64 + 8 + 8 + 8 ∧ g'.rbp = rdq(W, Y.cpu.gpr.rsp + 48#64) ∧
      g'.r12 = rdq(W, Y.cpu.gpr.rsp + 48#64 + 8) ∧ g'.r13 = rdq(W, Y.cpu.gpr.rsp + 48#64 + 8 + 8) ∧
      g'.rbx = Y.cpu.gpr.rbx ∧ g'.r14 = Y.cpu.gpr.r14 ∧ g'.r15 = Y.cpu.gpr.r15) hK hA hr
    (vc_79 (by rw [ms]; exact s5) (by rw [ms]; exact f40) hcl (by rw [ms, e48]; exact f3)
      (by rw [ms, e56]; exact f2) (by rw [ms, e64]; exact f1)
      fun _ a b d e f g h _ => ⟨rfl, rfl, a, b, d, e, f, g, h⟩) ?_
  rintro j' g fl V₁ ⟨rfl, hV₁, gs, gb, g12, g13, gx, g14, g15⟩ U t₁ hKU hAU hrU hgU -
  subst V₁ hgU
  have hsU : U.cpu.gpr.rsp = S := by rw [gs, ms]; exact e72 S
  have r1 : rdq(W, Y.cpu.gpr.rsp + 48#64) = g0.rbp := by rw [ms, e48]; exact s3
  have r2 : rdq(W, Y.cpu.gpr.rsp + 48#64 + 8) = g0.r12 := by rw [ms, e56]; exact s2
  have r3 : rdq(W, Y.cpu.gpr.rsp + 48#64 + 8 + 8) = g0.r13 := by rw [ms, e64]; exact s1
  refine c.s_ret hKU hAU hin (lt_len (by decide)) hrU (ret_104 _) (by rw [hsU]; exact hl) hin₂ h₂
    (by rw [hsU]; exact s4) ?_
  rintro Z' t₂ hKZ' hAZ' ⟨hrZ', hgZ'⟩
  refine k Z' t₂ hKZ' hAZ' hrZ' ?_ ?_
  · rw [hgZ']
    show U.cpu.gpr.rsp + 8 = _
    rw [hsU]
  · rw [hgZ']
    exact ⟨gx.trans mb, gb.trans r1, g12.trans r2, g13.trans r3, g14.trans m14, g15.trans m15⟩

/-- What the runs from 68, 60, 49 go on to: at the return address, `rsp` 8 above the entry's, the callee-saved
registers as they were, the bytes from `s += name` (`P4`). -/
abbrev Kr (prof : Profile) (F : Footprint) (Wl : List Rgn) (L : List (Addr × List Byte)) (s₀ : State) (o : Oracle)
    (gev : List Event) (gP : State → Nat → List Event → Prop) (gE : Outcome → List Event → Prop)
    (S : Addr) (g0 : Gprs) (e₂ : Addr) (j₂ : Nat) (P4 : State → (Addr → Byte) → Prop) : Prop :=
  ∀ (W' : Addr → Byte) (Z' : State) (t' : Nat), KeptW Wl s₀ Z' → Agree F Z'.proc.mm.mem W' →
    Z'.cpu.rip = e₂.add j₂ → Z'.cpu.gpr.rsp = S + 8 → KS g0 Z'.cpu.gpr → (∃ Z₄, P4 Z₄ W') →
    GoG prof L o gev gP gE Z' t'

/-- From 68 (the bytes `W`): `s += name` (`k4`), from its return 79. -/
theorem from68 {fb : Addr} {W : Addr → Byte} {S : Addr} {g0 : Gprs} {Y : State}
    {P4 : State → (Addr → Byte) → Prop} (c : Seg prof F Wl L s₀ o) (hfs : s₀.cpu.seg.fsBase = fb)
    (hin : CodeIn L pui_at pui) (hinA : CodeIn L Apc.apc_at Apc.apc)
    (hK : KeptW Wl s₀ Y) (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = pui_at.add 68) (hm : Fm S g0 Y.cpu.gpr)
    (hcl : ∀ i < 8, Foot F.data (Addr.add (fb + 40#64) i))
    (hs1 : ∀ i < 8, Foot Wl (Addr.add (S - 8) i)) (hs2 : ∀ i < 8, Foot Wl (Addr.add (S - 8 - 8) i))
    (hs3 : ∀ i < 8, Foot Wl (Addr.add (S - 8 - 8 - 8) i)) (hw40 : ∀ i < 8, Foot Wl (Addr.add (aR S + 40#64) i))
    (hr8 : ∀ i < 8, Foot Wl (Addr.add (aR S - 8) i))
    (hl : ∀ i < 8, Foot F.data (Addr.add S i)) (hin₂ : CodeIn L e₂ code₂) (h₂ : j₂ < code₂.length)
    (k4 : KC prof F Wl L s₀ o gev gP gE S g0 Apc.apc_at 79 W
      (fun g => Kf S g0 g ∧ g.rdi = g0.rdi ∧ g.rsi = g0.rdx)
      (fun _ W' => Stk fb W' S g0 (e₂.add j₂)) P4)
    (k : Kr prof F Wl L s₀ o gev gP gE S g0 e₂ j₂ P4) :
    GoG prof L o gev gP gE Y t := by
  have f40 : ∀ i < 8, Foot F.data (Addr.add (aR S + 40#64) i) := fun i hi => c.hws _ (hw40 i hi)
  have f1 : ∀ i < 8, Foot F.data (Addr.add (S - 8) i) := fun i hi => c.hws _ (hs1 i hi)
  have f2 : ∀ i < 8, Foot F.data (Addr.add (S - 8 - 8) i) := fun i hi => c.hws _ (hs2 i hi)
  have f3 : ∀ i < 8, Foot F.data (Addr.add (S - 8 - 8 - 8) i) := fun i hi => c.hws _ (hs3 i hi)
  refine (c_68 prof fb).run c hfs hin (fun j' g' _ V' => j' = 74 ∧ V' = W ∧ g'.rsi = Y.cpu.gpr.r12 ∧
      g'.rdi = Y.cpu.gpr.rbp ∧ Fr Y.cpu.gpr g') hK hA hr (vc_68 fun _ a b d _ => ⟨rfl, rfl, a, b, d⟩) ?_
  rintro j' g fl V₁ ⟨rfl, hV₁, gsi, gdi, gf⟩ U t₁ hKU hAU hrU hgU -
  subst V₁ hgU
  have hmU := Fm.fr hm gf
  have hU : U.cpu.gpr.rsp - 8 = aR S - 8 := by rw [hmU.1]
  refine c.s_call hKU hAU hin (lt_len (by decide)) hrU (call_74 _) hinA (Apc.lt_len (j := 0) (by decide)) tgt_74
    (by rw [hU]; exact hr8) ?_
  rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
  rw [hU] at hA₂
  refine k4 Y₂ t₂ hK₂ hA₂ hr₂ (by rw [hg₂]; exact hU)
    ⟨by rw [hg₂]; exact kf_set hmU, by rw [hg₂]; show U.cpu.gpr.rdi = _; rw [gdi, hm.2.1],
      by rw [hg₂]; show U.cpu.gpr.rsi = _; rw [gsi, hm.2.2.2.1]⟩ ?_
  intro Z₄ W₄ t₃ hKZ hAZ hrZ hmZ hstZ hP4
  exact tail79 c hfs hin hKZ hAZ hrZ hmZ hstZ hcl f40 f1 f2 f3 hl hin₂ h₂ fun Z' t' a b d e f =>
    k W₄ Z' t' a b d e f ⟨Z₄, hP4⟩

/-- From 60 (the bytes `W`): `s.Add_Space ()` (`k3`), from its return 68. -/
theorem from60 {fb : Addr} {W : Addr → Byte} {S : Addr} {g0 : Gprs} {Y : State}
    {P3 P4 : State → (Addr → Byte) → Prop} (c : Seg prof F Wl L s₀ o) (hfs : s₀.cpu.seg.fsBase = fb)
    (hin : CodeIn L pui_at pui) (hinA : CodeIn L Apc.apc_at Apc.apc) (hinS : CodeIn L Asp.asp_at Asp.asp)
    (hK : KeptW Wl s₀ Y) (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = pui_at.add 60) (hm : Fm S g0 Y.cpu.gpr)
    (hcl : ∀ i < 8, Foot F.data (Addr.add (fb + 40#64) i))
    (hs1 : ∀ i < 8, Foot Wl (Addr.add (S - 8) i)) (hs2 : ∀ i < 8, Foot Wl (Addr.add (S - 8 - 8) i))
    (hs3 : ∀ i < 8, Foot Wl (Addr.add (S - 8 - 8 - 8) i)) (hw40 : ∀ i < 8, Foot Wl (Addr.add (aR S + 40#64) i))
    (hr8 : ∀ i < 8, Foot Wl (Addr.add (aR S - 8) i))
    (hl : ∀ i < 8, Foot F.data (Addr.add S i)) (hin₂ : CodeIn L e₂ code₂) (h₂ : j₂ < code₂.length)
    (k3 : KC prof F Wl L s₀ o gev gP gE S g0 Asp.asp_at 68 W (fun g => Kf S g0 g ∧ g.rdi = g0.rdi)
      (fun _ _ => True) P3)
    (k4 : ∀ (Z₃ : State) (W₃ : Addr → Byte), P3 Z₃ W₃ →
      KC prof F Wl L s₀ o gev gP gE S g0 Apc.apc_at 79 W₃
      (fun g => Kf S g0 g ∧ g.rdi = g0.rdi ∧ g.rsi = g0.rdx) (fun _ W' => Stk fb W' S g0 (e₂.add j₂)) P4)
    (k : Kr prof F Wl L s₀ o gev gP gE S g0 e₂ j₂ P4) :
    GoG prof L o gev gP gE Y t := by
  refine (c_60 prof fb).run c hfs hin (fun j' g' _ V' => j' = 63 ∧ V' = W ∧ g'.rdi = Y.cpu.gpr.rbp ∧
      Fr Y.cpu.gpr g') hK hA hr (vc_60 fun _ a b _ => ⟨rfl, rfl, a, b⟩) ?_
  rintro j' g fl V₁ ⟨rfl, hV₁, gdi, gf⟩ U t₁ hKU hAU hrU hgU -
  subst V₁ hgU
  have hmU := Fm.fr hm gf
  have hU : U.cpu.gpr.rsp - 8 = aR S - 8 := by rw [hmU.1]
  refine c.s_call hKU hAU hin (lt_len (by decide)) hrU (call_63 _) hinS (Asp.lt_len (j := 0) (by decide)) tgt_63
    (by rw [hU]; exact hr8) ?_
  rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
  rw [hU] at hA₂
  refine k3 Y₂ t₂ hK₂ hA₂ hr₂ (by rw [hg₂]; exact hU)
    ⟨by rw [hg₂]; exact kf_set hmU, by rw [hg₂]; show U.cpu.gpr.rdi = _; rw [gdi, hm.2.1]⟩ ?_
  intro Z₃ W₃ t₃ hKZ hAZ hrZ hmZ _ hP3
  exact from68 c hfs hin hinA hKZ hAZ hrZ hmZ hcl hs1 hs2 hs3 hw40 hr8 hl hin₂ h₂ (k4 Z₃ W₃ hP3) k

/-- From 49 (back from `ConvertUInt64ToString`, the bytes `W`): `s += buf` (`k2`), from its return 60. -/
theorem from49 {fb : Addr} {W : Addr → Byte} {S : Addr} {g0 : Gprs} {Y : State}
    {P2 P3 P4 : State → (Addr → Byte) → Prop} (c : Seg prof F Wl L s₀ o) (hfs : s₀.cpu.seg.fsBase = fb)
    (hin : CodeIn L pui_at pui) (hinA : CodeIn L Apc.apc_at Apc.apc) (hinS : CodeIn L Asp.asp_at Asp.asp)
    (hK : KeptW Wl s₀ Y) (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = pui_at.add 49) (hm : Fm S g0 Y.cpu.gpr)
    (hcl : ∀ i < 8, Foot F.data (Addr.add (fb + 40#64) i))
    (hs1 : ∀ i < 8, Foot Wl (Addr.add (S - 8) i)) (hs2 : ∀ i < 8, Foot Wl (Addr.add (S - 8 - 8) i))
    (hs3 : ∀ i < 8, Foot Wl (Addr.add (S - 8 - 8 - 8) i)) (hw40 : ∀ i < 8, Foot Wl (Addr.add (aR S + 40#64) i))
    (hr8 : ∀ i < 8, Foot Wl (Addr.add (aR S - 8) i))
    (hl : ∀ i < 8, Foot F.data (Addr.add S i)) (hin₂ : CodeIn L e₂ code₂) (h₂ : j₂ < code₂.length)
    (k2 : KC prof F Wl L s₀ o gev gP gE S g0 Apc.apc_at 60 W (fun g => Kf S g0 g ∧ g.rdi = g0.rdi ∧ g.rsi = aR S)
      (fun _ _ => True) P2)
    (k3 : ∀ (Z₂ : State) (W₂ : Addr → Byte), P2 Z₂ W₂ →
      KC prof F Wl L s₀ o gev gP gE S g0 Asp.asp_at 68 W₂
      (fun g => Kf S g0 g ∧ g.rdi = g0.rdi) (fun _ _ => True) P3)
    (k4 : ∀ (Z₃ : State) (W₃ : Addr → Byte), P3 Z₃ W₃ →
      KC prof F Wl L s₀ o gev gP gE S g0 Apc.apc_at 79 W₃
      (fun g => Kf S g0 g ∧ g.rdi = g0.rdi ∧ g.rsi = g0.rdx) (fun _ W' => Stk fb W' S g0 (e₂.add j₂)) P4)
    (k : Kr prof F Wl L s₀ o gev gP gE S g0 e₂ j₂ P4) :
    GoG prof L o gev gP gE Y t := by
  refine (c_49 prof fb).run c hfs hin (fun j' g' _ V' => j' = 55 ∧ V' = W ∧ g'.rsi = Y.cpu.gpr.r13 ∧
      g'.rdi = Y.cpu.gpr.rbp ∧ Fr Y.cpu.gpr g') hK hA hr (vc_49 fun _ a b d _ => ⟨rfl, rfl, a, b, d⟩) ?_
  rintro j' g fl V₁ ⟨rfl, hV₁, gsi, gdi, gf⟩ U t₁ hKU hAU hrU hgU -
  subst V₁ hgU
  have hmU := Fm.fr hm gf
  have hU : U.cpu.gpr.rsp - 8 = aR S - 8 := by rw [hmU.1]
  refine c.s_call hKU hAU hin (lt_len (by decide)) hrU (call_55 _) hinA (Apc.lt_len (j := 0) (by decide)) tgt_55
    (by rw [hU]; exact hr8) ?_
  rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
  rw [hU] at hA₂
  refine k2 Y₂ t₂ hK₂ hA₂ hr₂ (by rw [hg₂]; exact hU)
    ⟨by rw [hg₂]; exact kf_set hmU, by rw [hg₂]; show U.cpu.gpr.rdi = _; rw [gdi, hm.2.1],
      by rw [hg₂]; show U.cpu.gpr.rsi = _; rw [gsi, hm.2.2.2.2.1]⟩ ?_
  intro Z₂ W₂ t₃ hKZ hAZ hrZ hmZ _ hP2
  exact from60 c hfs hin hinA hinS hKZ hAZ hrZ hmZ hcl hs1 hs2 hs3 hw40 hr8 hl hin₂ h₂ (k3 Z₂ W₂ hP2) k4 k

/-- `Print_UInt64_and_String (s, val, name)` (`rdi`, `rsi`, `rdx`) from its entry, `S` = `X`'s `rsp`, `fb` the `fs`
base: the pushes' slots, the stack guard's slot and the calls' return address slot in what the run may store into,
the return address and the guard at `fs:0x28` readable. The callees: `ConvertUInt64ToString (val, buf)` into the
frame's buffer (`k1`), from its return (`P1`) `s += buf` (`k2`, `P2`), `s.Add_Space ()` (`k3`, `P3`), `s += name`
(`k4`, from its return the stack `Stk` and `P4`). At the return address (`kr`): `rsp` 8 above the entry's, the
callee-saved registers as they were, the bytes from `s += name`. -/
theorem pui_ok {fb : Addr} {P1 P2 P3 P4 : State → (Addr → Byte) → Prop}
    (c : Seg prof F Wl L s₀ o) (hfs : s₀.cpu.seg.fsBase = fb) (hin : CodeIn L pui_at pui)
    (hinC : CodeIn L C64.c64_at C64.c64) (hinA : CodeIn L Apc.apc_at Apc.apc) (hinS : CodeIn L Asp.asp_at Asp.asp)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = pui_at)
    (hcl : ∀ i < 8, Foot F.data (Addr.add (fb + 40#64) i))
    (hs1 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8) i))
    (hs2 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8 - 8) i))
    (hs3 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8 - 8 - 8) i))
    (hw40 : ∀ i < 8, Foot Wl (Addr.add (aR X.cpu.gpr.rsp + 40#64) i))
    (hr8 : ∀ i < 8, Foot Wl (Addr.add (aR X.cpu.gpr.rsp - 8) i))
    (hl : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsp i)) (hin₂ : CodeIn L e₂ code₂)
    (h₂ : j₂ < code₂.length)
    (k1 : KC prof F Wl L s₀ o gev gP gE X.cpu.gpr.rsp X.cpu.gpr C64.c64_at 49 (V0 fb V X.cpu.gpr)
      (fun g => Kf X.cpu.gpr.rsp X.cpu.gpr g ∧ g.rdi = X.cpu.gpr.rsi ∧ g.rsi = aR X.cpu.gpr.rsp)
      (fun _ _ => True) P1)
    (k2 : ∀ (Z₁ : State) (W₁ : Addr → Byte), P1 Z₁ W₁ →
      KC prof F Wl L s₀ o gev gP gE X.cpu.gpr.rsp X.cpu.gpr Apc.apc_at 60 W₁
        (fun g => Kf X.cpu.gpr.rsp X.cpu.gpr g ∧ g.rdi = X.cpu.gpr.rdi ∧ g.rsi = aR X.cpu.gpr.rsp)
        (fun _ _ => True) P2)
    (k3 : ∀ (Z₂ : State) (W₂ : Addr → Byte), P2 Z₂ W₂ →
      KC prof F Wl L s₀ o gev gP gE X.cpu.gpr.rsp X.cpu.gpr Asp.asp_at 68 W₂
        (fun g => Kf X.cpu.gpr.rsp X.cpu.gpr g ∧ g.rdi = X.cpu.gpr.rdi) (fun _ _ => True) P3)
    (k4 : ∀ (Z₃ : State) (W₃ : Addr → Byte), P3 Z₃ W₃ →
      KC prof F Wl L s₀ o gev gP gE X.cpu.gpr.rsp X.cpu.gpr Apc.apc_at 79 W₃
        (fun g => Kf X.cpu.gpr.rsp X.cpu.gpr g ∧ g.rdi = X.cpu.gpr.rdi ∧ g.rsi = X.cpu.gpr.rdx)
        (fun _ W' => Stk fb W' X.cpu.gpr.rsp X.cpu.gpr (e₂.add j₂)) P4)
    (kr : Kr prof F Wl L s₀ o gev gP gE X.cpu.gpr.rsp X.cpu.gpr e₂ j₂ P4) :
    GoG prof L o gev gP gE X t := by
  -- the prologue, to the first `call`
  refine (c_0 prof fb).run c hfs hin (fun j' g' _ V' => j' = 44 ∧ V' = V0 fb V X.cpu.gpr ∧
      g'.rsp = aR X.cpu.gpr.rsp ∧ g'.rbp = X.cpu.gpr.rdi ∧ g'.rdi = X.cpu.gpr.rsi ∧
      g'.rsi = aR X.cpu.gpr.rsp ∧ g'.r12 = X.cpu.gpr.rdx ∧ g'.r13 = aR X.cpu.gpr.rsp ∧ g'.rbx = X.cpu.gpr.rbx ∧
      g'.r14 = X.cpu.gpr.r14 ∧ g'.r15 = X.cpu.gpr.r15) hK hA (by rw [addr_add_zero]; exact hrip)
    (vc_0 rfl hs1 hs2 hs3 hcl hw40 fun _ a b d e f g h i j _ => ⟨rfl, rfl, a, b, d, e, f, g, h, i, j⟩) ?_
  rintro j' g fl V₁ ⟨rfl, hV₁, gs, gp, gdi, gsi, g12, g13, gbx, g14, g15⟩ Y t₁ hKY hAY hrY hgY -
  subst V₁ hgY
  have hmY : Fm X.cpu.gpr.rsp X.cpu.gpr Y.cpu.gpr := ⟨gs, gp, gbx, g12, g13, g14, g15⟩
  have hY : Y.cpu.gpr.rsp - 8 = aR X.cpu.gpr.rsp - 8 := by rw [gs]
  refine c.s_call hKY hAY hin (lt_len (by decide)) hrY (call_44 _) hinC (C64.lt_len (j := 0) (by decide)) tgt_44
    (by rw [hY]; exact hr8) ?_
  rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
  rw [hY] at hA₂
  refine k1 Y₂ t₂ hK₂ hA₂ hr₂ (by rw [hg₂]; exact hY)
    ⟨by rw [hg₂]; exact kf_set hmY, by rw [hg₂]; exact gdi, by rw [hg₂]; exact gsi⟩ ?_
  -- back from `ConvertUInt64ToString`, at 49
  intro Z₁ W₁ t₃ hKZ hAZ hrZ hmZ _ hP1
  exact from49 c hfs hin hinA hinS hKZ hAZ hrZ hmZ hcl hs1 hs2 hs3 hw40 hr8 hl hin₂ h₂ (k2 Z₁ W₁ hP1)
    (fun Z₂ W₂ h => k3 Z₂ W₂ h) k4 kr

end FV7z.Pui
