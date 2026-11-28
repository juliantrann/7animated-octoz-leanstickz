import FV7z.Smd.Cuts
import FV7z.Acc.Blocks1
import FV7z.Rfp.Blocks1
import FV7z.Aas.Blocks1
import FV7z.Lemmas.LeafRet
/-!
# `Set_ModuleDirPrefix_From_ProgArg0` (PLAN.md §M, M1)

7-Zip 26.06's `Set_ModuleDirPrefix_From_ProgArg0 (const char *s)` at `0x5a9ed0` in `7zzs`
(`CPP/7zip/UI/Common/ArchiveCommandLine.cpp`; `objdump -d`), `s` in `rdi`, `S` the stack pointer at the entry:
`push rbp; mov rsi, rdi; sub rsp, 0x20`, the stack guard (`fs:0x28`) stored at `aR S + 24`, `rbp` = `rdi` = `aR S`
(an `AString` there: its chars at `aR S`, its length at `aR S + 8`); the `call` (34) of `AString (const char *)`
(`Acc.acc_at`); `mov rdi, rbp`, the `call` (42) of `ReverseFind_PathSepar ()` (`Rfp.rfp_at`); `add eax, 1`, and when
that is below the length (`jae 68` not taken) `_len = eax; _chars[eax] = 0` (56); `mov rsi, rbp; lea rdi, [0x79ed90]`,
the `call` (78) of `AString::operator= (const AString &)` (`Aas.aas_at`) into the global prefix; `mov rdi, [rsp]`,
unless NULL the `call` (92) of `operator delete []` (`0x6014f0`); the stack guard checked (97), `add rsp, 0x20; pop
rbp; ret` (118).

The callees are hypotheses, as in `FV7z/Fkd/Holds.lean`: each a continuation at its entry (`KC`: the bytes with the
return address at `aR S - 8`, `rsp` = `aR S - 8`, the registers it is given) that, from its return, has the frame
(`Fm`), a fact for the code after it (`N`) and its own post (`P`). Neither branch is resolved: the cut at 47 goes on
with the bytes as they were or with the string cut (`Tr`), the one at 83 with or without `delete []`. The byte stored
at 56 is in what the run may store into (`Nz`, from `ReverseFind_PathSepar`'s return: the separator's index plus 1 is
at most the length, so it is in the buffer). The stack guard's check is not run on a failing guard: from the returns
of `operator=` and `delete []` the stack is as it was (`Stk`: the saved `rbp`, the return address and the guard at
`aR S + 24` equal to the one at `fs:0x28`), so `jne 119` is not taken. Not covered: `__stack_chk_fail` (119).

- `aR`, `Fr`, `Fm`, `Kf`, `KS`, `Stk`, `V0`, `Tr`, `Nz`, `KC`: the frame, kept registers, the stack, bytes, contracts.
- `vc_0`, `vc_39`, `vc_47`, `vc_68`, `vc_83`, `vc_97`: the pieces' verification conditions.
- `tail97`, `from83`, `from68`, `from47`: the runs from those offsets; `smd_ok`: the function.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Smd
set_option linter.unusedVariables false

/-! ## The instructions outside the blocks -/

/-- The `call` of `AString (const char *)`. -/
def pc1 : List Byte := [0xe8, 0xc9, 0x24, 0xea, 0xff]
theorem pc1_0 : ∀ feat, Dec feat pc1 0 (FV7z.mk .call 64 [.rel 18446744073708119241] 5) := by intro feat f; rfl
theorem wc_34 : pc1 <+: smd.drop 34 := by decide +kernel
theorem call_34 (feat : Features) : Dec feat smd 34 (FV7z.mk .call 64 [.rel 18446744073708119241] 5) :=
  Dec.shift (j := 34) (k := 0) (pc1_0 feat) wc_34 (Nat.zero_le _)
theorem tgt_34 : smd_at.add (34 + 5) + BitVec.ofNat 64 18446744073708119241 = Acc.acc_at := by decide

/-- The `call` of `ReverseFind_PathSepar ()`. -/
def pc2 : List Byte := [0xe8, 0x51, 0x2c, 0xea, 0xff]
theorem pc2_0 : ∀ feat, Dec feat pc2 0 (FV7z.mk .call 64 [.rel 18446744073708121169] 5) := by intro feat f; rfl
theorem wc_42 : pc2 <+: smd.drop 42 := by decide +kernel
theorem call_42 (feat : Features) : Dec feat smd 42 (FV7z.mk .call 64 [.rel 18446744073708121169] 5) :=
  Dec.shift (j := 42) (k := 0) (pc2_0 feat) wc_42 (Nat.zero_le _)
theorem tgt_42 : smd_at.add (42 + 5) + BitVec.ofNat 64 18446744073708121169 = Rfp.rfp_at := by decide

/-- The `call` of `AString::operator= (const AString &)`. -/
def pc3 : List Byte := [0xe8, 0x2d, 0x26, 0xea, 0xff]
theorem pc3_0 : ∀ feat, Dec feat pc3 0 (FV7z.mk .call 64 [.rel 18446744073708119597] 5) := by intro feat f; rfl
theorem wc_78 : pc3 <+: smd.drop 78 := by decide +kernel
theorem call_78 (feat : Features) : Dec feat smd 78 (FV7z.mk .call 64 [.rel 18446744073708119597] 5) :=
  Dec.shift (j := 78) (k := 0) (pc3_0 feat) wc_78 (Nat.zero_le _)
theorem tgt_78 : smd_at.add (78 + 5) + BitVec.ofNat 64 18446744073708119597 = Aas.aas_at := by decide

/-- The `call` of `operator delete []`. -/
def pc4 : List Byte := [0xe8, 0xbf, 0x75, 0x05, 0x00]
theorem pc4_0 : ∀ feat, Dec feat pc4 0 (FV7z.mk .call 64 [.rel 357823] 5) := by intro feat f; rfl
theorem wc_92 : pc4 <+: smd.drop 92 := by decide +kernel
theorem call_92 (feat : Features) : Dec feat smd 92 (FV7z.mk .call 64 [.rel 357823] 5) :=
  Dec.shift (j := 92) (k := 0) (pc4_0 feat) wc_92 (Nat.zero_le _)
theorem tgt_92 : smd_at.add (92 + 5) + BitVec.ofNat 64 357823 = 0x6014f0#64 := by decide

/-- The `ret`. -/
def pret : List Byte := [0xc3]
theorem pret_0 : ∀ feat, Dec feat pret 0 (FV7z.mk .ret 64 [] 1) := by intro feat f; rfl
theorem w_118 : pret <+: smd.drop 118 := by decide +kernel
theorem ret_118 (feat : Features) : Dec feat smd 118 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 118) (k := 0) (pret_0 feat) w_118 (Nat.zero_le _)

/-! ## The frame -/

/-- The stack pointer after `push rbp; sub rsp, 0x20`; the `AString` there. -/
abbrev aR (S : Addr) : Addr := S - 8 - 32#64

theorem e32 (S : Addr) : aR S + 32#64 = S - 8 := by show S - 8 - 32#64 + 32#64 = S - 8; bv_omega
theorem e40 (S : Addr) : aR S + 32#64 + 8 = S := by show S - 8 - 32#64 + 32#64 + 8 = S; bv_omega

/-- What a piece keeps: `rsp`, `rbp`, `rbx`, `r12`–`r15`. -/
abbrev Fr (g g' : Gprs) : Prop :=
  g'.rsp = g.rsp ∧ g'.rbp = g.rbp ∧ g'.rbx = g.rbx ∧ g'.r12 = g.r12 ∧ g'.r13 = g.r13 ∧ g'.r14 = g.r14 ∧
    g'.r15 = g.r15

/-- The frame from 34 on: `rsp` = `rbp` = `aR S`, `rbx`, `r12`–`r15` as at the entry (`g0`). -/
abbrev Fm (S : Addr) (g0 g : Gprs) : Prop :=
  g.rsp = aR S ∧ g.rbp = aR S ∧ g.rbx = g0.rbx ∧ g.r12 = g0.r12 ∧ g.r13 = g0.r13 ∧ g.r14 = g0.r14 ∧
    g.r15 = g0.r15

/-- `Fm` but `rsp`: what a callee is given. -/
abbrev Kf (S : Addr) (g0 g : Gprs) : Prop :=
  g.rbp = aR S ∧ g.rbx = g0.rbx ∧ g.r12 = g0.r12 ∧ g.r13 = g0.r13 ∧ g.r14 = g0.r14 ∧ g.r15 = g0.r15

/-- The callee-saved registers as at the entry. -/
abbrev KS (g0 g : Gprs) : Prop :=
  g.rbx = g0.rbx ∧ g.rbp = g0.rbp ∧ g.r12 = g0.r12 ∧ g.r13 = g0.r13 ∧ g.r14 = g0.r14 ∧ g.r15 = g0.r15

theorem Fm.fr {S : Addr} {g0 g g' : Gprs} (h : Fm S g0 g) (h' : Fr g g') : Fm S g0 g' :=
  ⟨h'.1.trans h.1, h'.2.1.trans h.2.1, h'.2.2.1.trans h.2.2.1, h'.2.2.2.1.trans h.2.2.2.1,
    h'.2.2.2.2.1.trans h.2.2.2.2.1, h'.2.2.2.2.2.1.trans h.2.2.2.2.2.1, h'.2.2.2.2.2.2.trans h.2.2.2.2.2.2⟩

theorem kf_set {S : Addr} {g0 g : Gprs} {x : Addr} (h : Fm S g0 g) : Kf S g0 (g.set 4 x) :=
  ⟨h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩

theorem kf_of {S : Addr} {g0 g : Gprs} {x : Addr} (hp : g.rbp = aR S) (hb : g.rbx = g0.rbx) (h12 : g.r12 = g0.r12)
    (h13 : g.r13 = g0.r13) (h14 : g.r14 = g0.r14) (h15 : g.r15 = g0.r15) : Kf S g0 (g.set 4 x) :=
  ⟨hp, hb, h12, h13, h14, h15⟩

/-- The stack from the returns of `operator=` and `delete []` (`fb` the `fs` base, `ra` the return address): the
saved `rbp`, the return address, the stack guard as at `fs:0x28`. -/
abbrev Stk (fb : Addr) (W : Addr → Byte) (S : Addr) (g0 : Gprs) (ra : Addr) : Prop :=
  rdq(W, S - 8) = g0.rbp ∧ rdq(W, S) = ra ∧ rdq(W, aR S + 24#64) = rdq(W, fb + 40#64)

/-- The bytes at the first `call`: `rbp` pushed, the stack guard stored. -/
abbrev V0 (fb : Addr) (V : Addr → Byte) (g : Gprs) : Addr → Byte :=
  Vst (Vst V (g.rsp - 8) (toBytesLE g.rbp 8)) (aR g.rsp + 24#64)
    (toBytesLE rdq(Vst V (g.rsp - 8) (toBytesLE g.rbp 8), fb + 40#64) 8)

/-- The string cut at 56 (`p` the `AString`, `cc` its chars, `n` the new length). -/
abbrev Tr (V : Addr → Byte) (p cc : Addr) (n : BitVec 32) : Addr → Byte :=
  Vst (Vst V (p + 8#64) (toBytesLE n 4)) (cc + BitVec.setWidth 64 n) (toBytesLE (BitVec.ofNat 8 0) 1)

/-- From `ReverseFind_PathSepar`'s return: the byte at the chars plus `eax + 1` in what the run may store into. -/
abbrev Nz (Wl : List Rgn) (S : Addr) (Z : State) (W : Addr → Byte) : Prop :=
  ∀ i < 1, Foot Wl (Addr.add (rdq(W, aR S) + BitVec.setWidth 64 (BitVec.setWidth 32 Z.cpu.gpr.rax + 1#32)) i)

/-- A callee from the `call` before `j` (entry `ent`, the bytes `W`, the registers `A`): at its entry, and from its
return at `j` with the frame, `N` and `P`, the run goes on to the goal. -/
def KC (prof : Profile) (F : Footprint) (Wl : List Rgn) (L : List (Addr × List Byte)) (s₀ : State) (o : Oracle)
    (gev : List Event) (gP : State → Nat → List Event → Prop) (gE : Outcome → List Event → Prop)
    (S : Addr) (g0 : Gprs) (ent : Addr) (j : Nat) (W : Addr → Byte) (A : Gprs → Prop)
    (N P : State → (Addr → Byte) → Prop) : Prop :=
  ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y →
    Agree F Y.proc.mm.mem (Vst W (aR S - 8) (toBytesLE (smd_at.add j) 8)) →
    Y.cpu.rip = ent → Y.cpu.gpr.rsp = aR S - 8 → A Y.cpu.gpr →
    (∀ (Z : State) (W' : Addr → Byte) (t'' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem W' →
      Z.cpu.rip = smd_at.add j → Fm S g0 Z.cpu.gpr → N Z W' → P Z W' → GoG prof L o gev gP gE Z t'') →
    GoG prof L o gev gP gE Y t'

/-! ## The pieces -/

variable {F : Footprint} {Wl : List Rgn}

/-- The push, `rsi` = `rdi`, the frame, the stack guard stored, `rbp` = `rdi` = `rsp`, to the first `call`. The
guard's value is named (`cn`). -/
theorem vc_0 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} {cn : BitVec 64}
    (hcn : rdq(Vst V (g.rsp - 8) (toBytesLE g.rbp 8), fb + 40#64) = cn)
    (hs1 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8) i)) (hcl : ∀ i < 8, Foot F.data (Addr.add (fb + 40#64) i))
    (hw : ∀ i < 8, Foot Wl (Addr.add (aR g.rsp + 24#64) i))
    (h : ∀ g', g'.rsp = aR g.rsp → g'.rbp = aR g.rsp → g'.rdi = aR g.rsp → g'.rsi = g.rdi → g'.rbx = g.rbx →
      g'.r12 = g.r12 → g'.r13 = g.r13 → g'.r14 = g.r14 → g'.r15 = g.r15 →
      ∀ fl, Q 34 g' fl (Vst (Vst V (g.rsp - 8) (toBytesLE g.rbp 8)) (aR g.rsp + 24#64) (toBytesLE cn 8))) :
    W_0 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [aR] at hcn hs1 hw h ⊢
  wpx [W_0, o0, Op.ldf, hcn]
  all_goals repeat' (first
    | refine h _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ _
    | with_reducible rfl
    | with_reducible exact hs1
    | with_reducible exact hcl
    | with_reducible exact hw
    | apply And.intro
    | intro _)

/-- `mov rdi, rbp` to the second `call`. -/
theorem vc_39 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (h : ∀ g', g'.rdi = g.rbp → Fr g g' → ∀ fl, Q 42 g' fl V) :
    W_39 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h ⊢
  wpx [W_39, o1]
  all_goals repeat' (first
    | refine h _ ?_ ?_ _
    | with_reducible rfl
    | apply And.intro
    | intro _)

/-- `add eax, 1; cmp eax, [rsp + 8]`, to 68 as it was or (`jae` not taken) with the string cut at `eax`. The chars'
address (`cc`) and the new length (`n`) are named. -/
theorem vc_47 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} {cc : Addr} {n : BitVec 32}
    (hc : rdq(V, g.rsp) = cc) (hn : BitVec.setWidth 32 g.rax + 1#32 = n)
    (f8 : ∀ i < 4, Foot F.data (Addr.add (g.rsp + 8#64) i)) (fc : ∀ i < 8, Foot F.data (Addr.add g.rsp i))
    (w8 : ∀ i < 4, Foot Wl (Addr.add (g.rsp + 8#64) i))
    (wz : ∀ i < 1, Foot Wl (Addr.add (cc + BitVec.setWidth 64 n) i))
    (h : ∀ g' W, (W = V ∨ W = Tr V g.rsp cc n) → Fr g g' → ∀ fl, Q 68 g' fl W) :
    W_47 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [Tr] at hc hn f8 fc w8 h ⊢
  wpx [W_47, W_56, o2, o3, hc, hn]
  all_goals repeat' (first
    | refine h _ _ ?_ ?_ _
    | with_reducible rfl
    | with_reducible exact Or.inl rfl
    | with_reducible exact Or.inr rfl
    | with_reducible exact f8
    | with_reducible exact fc
    | with_reducible exact w8
    | with_reducible exact wz
    | apply And.intro
    | intro _)

/-- `mov rsi, rbp; lea rdi, [0x79ed90]` to the third `call`. -/
theorem vc_68 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (h : ∀ g', g'.rsi = g.rbp → g'.rdi = 7990672#64 → Fr g g' → ∀ fl, Q 78 g' fl V) :
    W_68 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h ⊢
  wpx [W_68, o4]
  all_goals repeat' (first
    | refine h _ ?_ ?_ ?_ _
    | with_reducible rfl
    | apply And.intro
    | intro _)

/-- `mov rdi, [rsp]; test rdi, rdi`: to 97, or to the `call` of `delete []` (92). -/
theorem vc_83 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (fc : ∀ i < 8, Foot F.data (Addr.add g.rsp i)) (h97 : ∀ g', Fr g g' → ∀ fl, Q 97 g' fl V)
    (h92 : ∀ g', g'.rdi = rdq(V, g.rsp) → Fr g g' → ∀ fl, Q 92 g' fl V) :
    W_83 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at fc h97 h92 ⊢
  wpx [W_83, o5]
  all_goals repeat' (first
    | refine h97 _ ?_ _
    | refine h92 _ ?_ ?_ _
    | with_reducible rfl
    | with_reducible exact fc
    | apply And.intro
    | intro _)

/-- The stack guard checked (as at `fs:0x28`: `jne` not taken), `add rsp, 0x20; pop rbp` to the `ret`. -/
theorem vc_97 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (hc : rdq(V, g.rsp + 24#64) = rdq(V, fb + 40#64)) (f24 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 24#64) i))
    (fcl : ∀ i < 8, Foot F.data (Addr.add (fb + 40#64) i))
    (f32 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 32#64) i))
    (h : ∀ g', g'.rsp = g.rsp + 32#64 + 8 → g'.rbp = rdq(V, g.rsp + 32#64) → g'.rbx = g.rbx → g'.r12 = g.r12 →
      g'.r13 = g.r13 → g'.r14 = g.r14 → g'.r15 = g.r15 → ∀ fl, Q 118 g' fl V) :
    W_97 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hc f24 f32 h ⊢
  have z0 : ((0#64 : BitVec 64) == 0) = true := by decide
  wpx [W_97, W_113, o6, o7, Op.xormf, hc, BitVec.xor_self, z0, decide_true, Bool.not_true, Bool.false_eq_true,
    false_implies, eq_self_iff_true, true_implies]
  all_goals repeat' (first
    | refine h _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ _
    | with_reducible rfl
    | with_reducible exact f24
    | with_reducible exact fcl
    | with_reducible exact f32
    | apply And.intro
    | intro _)

/-! ## The runs -/

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {X : State} {t : Nat} {V : Addr → Byte} {e₂ : Addr} {code₂ : List Byte} {j₂ : Nat}

/-- From 97 (the frame, the stack `Stk`) to the return address `e₂.add j₂`. -/
theorem tail97 {fb : Addr} {W : Addr → Byte} {S : Addr} {g0 : Gprs} {Y : State} (c : Seg prof F Wl L s₀ o)
    (hfs : s₀.cpu.seg.fsBase = fb) (hin : CodeIn L smd_at smd) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = smd_at.add 97) (hm : Fm S g0 Y.cpu.gpr)
    (hst : Stk fb W S g0 (e₂.add j₂)) (hcl : ∀ i < 8, Foot F.data (Addr.add (fb + 40#64) i))
    (f24 : ∀ i < 8, Foot F.data (Addr.add (aR S + 24#64) i)) (f32 : ∀ i < 8, Foot F.data (Addr.add (S - 8) i))
    (hl : ∀ i < 8, Foot F.data (Addr.add S i)) (hin₂ : CodeIn L e₂ code₂) (h₂ : j₂ < code₂.length)
    (k : ∀ (Z' : State) (t' : Nat), KeptW Wl s₀ Z' → Agree F Z'.proc.mm.mem W → Z'.cpu.rip = e₂.add j₂ →
      Z'.cpu.gpr.rsp = S + 8 → KS g0 Z'.cpu.gpr → GoG prof L o gev gP gE Z' t') :
    GoG prof L o gev gP gE Y t := by
  obtain ⟨ms, mp, mb, m12, m13, m14, m15⟩ := hm
  obtain ⟨s1, s2, s3⟩ := hst
  refine (c_97 prof fb).run c hfs hin (fun j' g' _ V' => j' = 118 ∧ V' = W ∧
      g'.rsp = Y.cpu.gpr.rsp + 32#64 + 8 ∧ g'.rbp = rdq(W, Y.cpu.gpr.rsp + 32#64) ∧ g'.rbx = Y.cpu.gpr.rbx ∧
      g'.r12 = Y.cpu.gpr.r12 ∧ g'.r13 = Y.cpu.gpr.r13 ∧ g'.r14 = Y.cpu.gpr.r14 ∧ g'.r15 = Y.cpu.gpr.r15) hK hA hr
    (vc_97 (by rw [ms]; exact s3) (by rw [ms]; exact f24) hcl (by rw [ms, e32]; exact f32)
      fun _ a b d e f g h _ => ⟨rfl, rfl, a, b, d, e, f, g, h⟩) ?_
  rintro j' g fl V₁ ⟨rfl, hV₁, gs, gb, gx, g12, g13, g14, g15⟩ U t₁ hKU hAU hrU hgU -
  subst V₁ hgU
  have hsU : U.cpu.gpr.rsp = S := by rw [gs, ms]; exact e40 S
  have e1 : rdq(W, Y.cpu.gpr.rsp + 32#64) = g0.rbp := by rw [ms, e32]; exact s1
  refine c.s_ret hKU hAU hin (lt_len (by decide)) hrU (ret_118 _) (by rw [hsU]; exact hl) hin₂ h₂
    (by rw [hsU]; exact s2) ?_
  rintro Z' t₂ hKZ' hAZ' ⟨hrZ', hgZ'⟩
  refine k Z' t₂ hKZ' hAZ' hrZ' ?_ ?_
  · rw [hgZ']
    show U.cpu.gpr.rsp + 8 = _
    rw [hsU]
  · rw [hgZ']
    exact ⟨gx.trans mb, gb.trans e1, g12.trans m12, g13.trans m13, g14.trans m14, g15.trans m15⟩

/-- From 83 (the bytes `W`): to 97, or `delete []` on the chars (`k4`) and from its return 97. -/
theorem from83 {fb : Addr} {W : Addr → Byte} {S : Addr} {g0 : Gprs} {Y : State} {codeD : List Byte}
    {P4 : State → (Addr → Byte) → Prop} (c : Seg prof F Wl L s₀ o) (hfs : s₀.cpu.seg.fsBase = fb)
    (hin : CodeIn L smd_at smd) (hinD : CodeIn L 0x6014f0#64 codeD) (hD : 0 < codeD.length)
    (hK : KeptW Wl s₀ Y) (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = smd_at.add 83) (hm : Fm S g0 Y.cpu.gpr)
    (hst : Stk fb W S g0 (e₂.add j₂)) (hcl : ∀ i < 8, Foot F.data (Addr.add (fb + 40#64) i))
    (hw0 : ∀ i < 8, Foot Wl (Addr.add (aR S) i)) (hw24 : ∀ i < 8, Foot Wl (Addr.add (aR S + 24#64) i))
    (hs1 : ∀ i < 8, Foot Wl (Addr.add (S - 8) i)) (hr8 : ∀ i < 8, Foot Wl (Addr.add (aR S - 8) i))
    (hl : ∀ i < 8, Foot F.data (Addr.add S i)) (hin₂ : CodeIn L e₂ code₂) (h₂ : j₂ < code₂.length)
    (k4 : KC prof F Wl L s₀ o gev gP gE S g0 0x6014f0#64 97 W (fun g => Kf S g0 g ∧ g.rdi = rdq(W, aR S))
      (fun _ W' => Stk fb W' S g0 (e₂.add j₂)) P4)
    (k : ∀ (W' : Addr → Byte) (Z' : State) (t' : Nat), KeptW Wl s₀ Z' → Agree F Z'.proc.mm.mem W' →
      Z'.cpu.rip = e₂.add j₂ → Z'.cpu.gpr.rsp = S + 8 → KS g0 Z'.cpu.gpr → (W' = W ∨ ∃ Z₄, P4 Z₄ W') →
      GoG prof L o gev gP gE Z' t') :
    GoG prof L o gev gP gE Y t := by
  have f24 : ∀ i < 8, Foot F.data (Addr.add (aR S + 24#64) i) := fun i hi => c.hws _ (hw24 i hi)
  have f32 : ∀ i < 8, Foot F.data (Addr.add (S - 8) i) := fun i hi => c.hws _ (hs1 i hi)
  refine (c_83 prof fb).run c hfs hin (fun j' g' _ V' => V' = W ∧ Fr Y.cpu.gpr g' ∧
      (j' = 97 ∨ (j' = 92 ∧ g'.rdi = rdq(W, Y.cpu.gpr.rsp)))) hK hA hr
    (vc_83 (by rw [hm.1]; exact fun i hi => c.hws _ (hw0 i hi)) (fun _ a _ => ⟨rfl, a, Or.inl rfl⟩)
      (fun _ a b _ => ⟨rfl, b, Or.inr ⟨rfl, a⟩⟩)) ?_
  rintro j' g fl V₁ ⟨hV₁, gf, hpost⟩ U t₁ hKU hAU hrU hgU -
  subst V₁ hgU
  have hmU := Fm.fr hm gf
  rcases hpost with rfl | ⟨rfl, gdi⟩
  · exact tail97 c hfs hin hKU hAU hrU hmU hst hcl f24 f32 hl hin₂ h₂ fun Z' t' a b d e f =>
      k W Z' t' a b d e f (Or.inl rfl)
  · have hU : U.cpu.gpr.rsp - 8 = aR S - 8 := by rw [hmU.1]
    refine c.s_call hKU hAU hin (lt_len (by decide)) hrU (call_92 _) hinD hD tgt_92 (by rw [hU]; exact hr8) ?_
    rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
    rw [hU] at hA₂
    refine k4 Y₂ t₂ hK₂ hA₂ hr₂ (by rw [hg₂]; exact hU)
      ⟨by rw [hg₂]; exact kf_set hmU, by rw [hg₂]; show U.cpu.gpr.rdi = _; rw [gdi, hm.1]⟩ ?_
    intro Z₄ W₄ t₃ hKZ hAZ hrZ hmZ hstZ hP4
    exact tail97 c hfs hin hKZ hAZ hrZ hmZ hstZ hcl f24 f32 hl hin₂ h₂ fun Z' t' a b d e f =>
      k W₄ Z' t' a b d e f (Or.inr ⟨Z₄, hP4⟩)

/-- From 68 (the bytes `W`): `operator=` into the global prefix (`k3`), from its return 83. -/
theorem from68 {fb : Addr} {W : Addr → Byte} {S : Addr} {g0 : Gprs} {Y : State} {codeD : List Byte}
    {P3 P4 : State → (Addr → Byte) → Prop} (c : Seg prof F Wl L s₀ o) (hfs : s₀.cpu.seg.fsBase = fb)
    (hin : CodeIn L smd_at smd) (hinA : CodeIn L Aas.aas_at Aas.aas) (hinD : CodeIn L 0x6014f0#64 codeD)
    (hD : 0 < codeD.length)
    (hK : KeptW Wl s₀ Y) (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = smd_at.add 68) (hm : Fm S g0 Y.cpu.gpr)
    (hcl : ∀ i < 8, Foot F.data (Addr.add (fb + 40#64) i))
    (hw0 : ∀ i < 8, Foot Wl (Addr.add (aR S) i)) (hw24 : ∀ i < 8, Foot Wl (Addr.add (aR S + 24#64) i))
    (hs1 : ∀ i < 8, Foot Wl (Addr.add (S - 8) i)) (hr8 : ∀ i < 8, Foot Wl (Addr.add (aR S - 8) i))
    (hl : ∀ i < 8, Foot F.data (Addr.add S i)) (hin₂ : CodeIn L e₂ code₂) (h₂ : j₂ < code₂.length)
    (k3 : KC prof F Wl L s₀ o gev gP gE S g0 Aas.aas_at 83 W
      (fun g => Kf S g0 g ∧ g.rdi = 7990672#64 ∧ g.rsi = aR S) (fun _ W' => Stk fb W' S g0 (e₂.add j₂)) P3)
    (k4 : ∀ (Z₃ : State) (W₃ : Addr → Byte), P3 Z₃ W₃ → KC prof F Wl L s₀ o gev gP gE S g0 0x6014f0#64 97 W₃
      (fun g => Kf S g0 g ∧ g.rdi = rdq(W₃, aR S)) (fun _ W' => Stk fb W' S g0 (e₂.add j₂)) P4)
    (k : ∀ (W' : Addr → Byte) (Z' : State) (t' : Nat), KeptW Wl s₀ Z' → Agree F Z'.proc.mm.mem W' →
      Z'.cpu.rip = e₂.add j₂ → Z'.cpu.gpr.rsp = S + 8 → KS g0 Z'.cpu.gpr →
      (∃ (Z₃ : State) (W₃ : Addr → Byte), P3 Z₃ W₃ ∧ (W' = W₃ ∨ ∃ Z₄, P4 Z₄ W')) → GoG prof L o gev gP gE Z' t') :
    GoG prof L o gev gP gE Y t := by
  refine (c_68 prof fb).run c hfs hin (fun j' g' _ V' => j' = 78 ∧ V' = W ∧ g'.rsi = Y.cpu.gpr.rbp ∧
      g'.rdi = 7990672#64 ∧ Fr Y.cpu.gpr g') hK hA hr (vc_68 fun _ a b d _ => ⟨rfl, rfl, a, b, d⟩) ?_
  rintro j' g fl V₁ ⟨rfl, hV₁, gsi, gdi, gf⟩ U t₁ hKU hAU hrU hgU -
  subst V₁ hgU
  have hmU := Fm.fr hm gf
  have hU : U.cpu.gpr.rsp - 8 = aR S - 8 := by rw [hmU.1]
  refine c.s_call hKU hAU hin (lt_len (by decide)) hrU (call_78 _) hinA (Aas.lt_len (j := 0) (by decide)) tgt_78
    (by rw [hU]; exact hr8) ?_
  rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
  rw [hU] at hA₂
  refine k3 Y₂ t₂ hK₂ hA₂ hr₂ (by rw [hg₂]; exact hU)
    ⟨by rw [hg₂]; exact kf_set hmU, by rw [hg₂]; exact gdi, by rw [hg₂]; show U.cpu.gpr.rsi = _; rw [gsi, hm.2.1]⟩
    ?_
  intro Z₃ W₃ t₃ hKZ hAZ hrZ hmZ hstZ hP3
  exact from83 c hfs hin hinD hD hKZ hAZ hrZ hmZ hstZ hcl hw0 hw24 hs1 hr8 hl hin₂ h₂ (k4 Z₃ W₃ hP3)
    fun W' Z' t' a b d e f g => k W' Z' t' a b d e f ⟨Z₃, W₃, hP3, g⟩

/-- From 47 (back from `ReverseFind_PathSepar`, the bytes `W`): the string cut or not, then 68. -/
theorem from47 {fb : Addr} {W : Addr → Byte} {S : Addr} {g0 : Gprs} {Y : State} {codeD : List Byte}
    {P3 P4 : State → (Addr → Byte) → Prop} (c : Seg prof F Wl L s₀ o) (hfs : s₀.cpu.seg.fsBase = fb)
    (hin : CodeIn L smd_at smd) (hinA : CodeIn L Aas.aas_at Aas.aas) (hinD : CodeIn L 0x6014f0#64 codeD)
    (hD : 0 < codeD.length)
    (hK : KeptW Wl s₀ Y) (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = smd_at.add 47) (hm : Fm S g0 Y.cpu.gpr)
    (hcl : ∀ i < 8, Foot F.data (Addr.add (fb + 40#64) i))
    (hw0 : ∀ i < 8, Foot Wl (Addr.add (aR S) i)) (hw8 : ∀ i < 4, Foot Wl (Addr.add (aR S + 8#64) i))
    (hw24 : ∀ i < 8, Foot Wl (Addr.add (aR S + 24#64) i))
    (hs1 : ∀ i < 8, Foot Wl (Addr.add (S - 8) i)) (hr8 : ∀ i < 8, Foot Wl (Addr.add (aR S - 8) i))
    (hl : ∀ i < 8, Foot F.data (Addr.add S i)) (hin₂ : CodeIn L e₂ code₂) (h₂ : j₂ < code₂.length)
    (hz : Nz Wl S Y W)
    (k3 : ∀ W' : Addr → Byte,
      (W' = W ∨ W' = Tr W (aR S) rdq(W, aR S) (BitVec.setWidth 32 Y.cpu.gpr.rax + 1#32)) →
      KC prof F Wl L s₀ o gev gP gE S g0 Aas.aas_at 83 W'
        (fun g => Kf S g0 g ∧ g.rdi = 7990672#64 ∧ g.rsi = aR S) (fun _ W' => Stk fb W' S g0 (e₂.add j₂)) P3)
    (k4 : ∀ (Z₃ : State) (W₃ : Addr → Byte), P3 Z₃ W₃ → KC prof F Wl L s₀ o gev gP gE S g0 0x6014f0#64 97 W₃
      (fun g => Kf S g0 g ∧ g.rdi = rdq(W₃, aR S)) (fun _ W' => Stk fb W' S g0 (e₂.add j₂)) P4)
    (k : ∀ (W' : Addr → Byte) (Z' : State) (t' : Nat), KeptW Wl s₀ Z' → Agree F Z'.proc.mm.mem W' →
      Z'.cpu.rip = e₂.add j₂ → Z'.cpu.gpr.rsp = S + 8 → KS g0 Z'.cpu.gpr →
      (∃ (Z₃ : State) (W₃ : Addr → Byte), P3 Z₃ W₃ ∧ (W' = W₃ ∨ ∃ Z₄, P4 Z₄ W')) → GoG prof L o gev gP gE Z' t') :
    GoG prof L o gev gP gE Y t := by
  have f0 : ∀ i < 8, Foot F.data (Addr.add (aR S) i) := fun i hi => c.hws _ (hw0 i hi)
  have f8 : ∀ i < 4, Foot F.data (Addr.add (aR S + 8#64) i) := fun i hi => c.hws _ (hw8 i hi)
  refine (c_47 prof fb).run c hfs hin (fun j' g' _ V' => j' = 68 ∧
      (V' = W ∨ V' = Tr W Y.cpu.gpr.rsp rdq(W, aR S) (BitVec.setWidth 32 Y.cpu.gpr.rax + 1#32)) ∧
      Fr Y.cpu.gpr g') hK hA hr
    (vc_47 (cc := rdq(W, aR S)) (n := BitVec.setWidth 32 Y.cpu.gpr.rax + 1#32) (by rw [hm.1]) rfl
      (by rw [hm.1]; exact f8) (by rw [hm.1]; exact f0) (by rw [hm.1]; exact hw8) hz
      (fun _ _ hW a _ => ⟨rfl, hW, a⟩)) ?_
  rintro j' g fl V₁ ⟨rfl, hV₁, gf⟩ U t₁ hKU hAU hrU hgU -
  subst hgU
  have hmU := Fm.fr hm gf
  rw [hm.1] at hV₁
  exact from68 c hfs hin hinA hinD hD hKU hAU hrU hmU hcl hw0 hw24 hs1 hr8 hl hin₂ h₂ (k3 V₁ hV₁) k4 k

/-- `Set_ModuleDirPrefix_From_ProgArg0 (s)` (`s` = `rdi`) from its entry, `S` = `X`'s `rsp`, `fb` the `fs` base: the
push's slot, the frame's chars address, length and stack guard slots and the calls' return address slot in what the
run may store into, the return address and the guard at `fs:0x28` readable. The callees: `AString (s)` on the frame
(`k1`), from its return (`P1`) `ReverseFind_PathSepar ()` (`k2`, from its return `Nz` and `P2`), `operator=` into the
global prefix from the frame's string as it was or cut (`k3`, from its return the stack `Stk` and `P3`), `delete []`
on the chars (`k4`, the same with `P4`). At the return address (`kr`): `rsp` 8 above the entry's, the callee-saved
registers as they were, the bytes from `operator=` or from `delete []` after it. -/
theorem smd_ok {fb : Addr} {codeD : List Byte} {P1 P2 P3 P4 : State → (Addr → Byte) → Prop}
    (c : Seg prof F Wl L s₀ o) (hfs : s₀.cpu.seg.fsBase = fb) (hin : CodeIn L smd_at smd)
    (hinC : CodeIn L Acc.acc_at Acc.acc) (hinR : CodeIn L Rfp.rfp_at Rfp.rfp) (hinA : CodeIn L Aas.aas_at Aas.aas)
    (hinD : CodeIn L 0x6014f0#64 codeD) (hD : 0 < codeD.length)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = smd_at)
    (hcl : ∀ i < 8, Foot F.data (Addr.add (fb + 40#64) i))
    (hs1 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8) i))
    (hw0 : ∀ i < 8, Foot Wl (Addr.add (aR X.cpu.gpr.rsp) i))
    (hw8 : ∀ i < 4, Foot Wl (Addr.add (aR X.cpu.gpr.rsp + 8#64) i))
    (hw24 : ∀ i < 8, Foot Wl (Addr.add (aR X.cpu.gpr.rsp + 24#64) i))
    (hr8 : ∀ i < 8, Foot Wl (Addr.add (aR X.cpu.gpr.rsp - 8) i))
    (hl : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsp i)) (hin₂ : CodeIn L e₂ code₂) (h₂ : j₂ < code₂.length)
    (k1 : KC prof F Wl L s₀ o gev gP gE X.cpu.gpr.rsp X.cpu.gpr Acc.acc_at 39 (V0 fb V X.cpu.gpr)
      (fun g => Kf X.cpu.gpr.rsp X.cpu.gpr g ∧ g.rdi = aR X.cpu.gpr.rsp ∧ g.rsi = X.cpu.gpr.rdi)
      (fun _ _ => True) P1)
    (k2 : ∀ (Z₁ : State) (W₁ : Addr → Byte), P1 Z₁ W₁ →
      KC prof F Wl L s₀ o gev gP gE X.cpu.gpr.rsp X.cpu.gpr Rfp.rfp_at 47 W₁
        (fun g => Kf X.cpu.gpr.rsp X.cpu.gpr g ∧ g.rdi = aR X.cpu.gpr.rsp) (Nz Wl X.cpu.gpr.rsp) P2)
    (k3 : ∀ (Z₂ : State) (W₂ : Addr → Byte), P2 Z₂ W₂ → ∀ W : Addr → Byte,
      (W = W₂ ∨ W = Tr W₂ (aR X.cpu.gpr.rsp) rdq(W₂, aR X.cpu.gpr.rsp)
        (BitVec.setWidth 32 Z₂.cpu.gpr.rax + 1#32)) →
      KC prof F Wl L s₀ o gev gP gE X.cpu.gpr.rsp X.cpu.gpr Aas.aas_at 83 W
        (fun g => Kf X.cpu.gpr.rsp X.cpu.gpr g ∧ g.rdi = 7990672#64 ∧ g.rsi = aR X.cpu.gpr.rsp)
        (fun _ W' => Stk fb W' X.cpu.gpr.rsp X.cpu.gpr (e₂.add j₂)) P3)
    (k4 : ∀ (Z₃ : State) (W₃ : Addr → Byte), P3 Z₃ W₃ →
      KC prof F Wl L s₀ o gev gP gE X.cpu.gpr.rsp X.cpu.gpr 0x6014f0#64 97 W₃
        (fun g => Kf X.cpu.gpr.rsp X.cpu.gpr g ∧ g.rdi = rdq(W₃, aR X.cpu.gpr.rsp))
        (fun _ W' => Stk fb W' X.cpu.gpr.rsp X.cpu.gpr (e₂.add j₂)) P4)
    (kr : ∀ (W : Addr → Byte) (Z' : State) (t' : Nat), KeptW Wl s₀ Z' → Agree F Z'.proc.mm.mem W →
      Z'.cpu.rip = e₂.add j₂ → Z'.cpu.gpr.rsp = X.cpu.gpr.rsp + 8 → KS X.cpu.gpr Z'.cpu.gpr →
      (∃ (Z₃ : State) (W₃ : Addr → Byte), P3 Z₃ W₃ ∧ (W = W₃ ∨ ∃ Z₄, P4 Z₄ W)) →
      GoG prof L o gev gP gE Z' t') :
    GoG prof L o gev gP gE X t := by
  -- the prologue, to the first `call`
  refine (c_0 prof fb).run c hfs hin (fun j' g' _ V' => j' = 34 ∧ V' = V0 fb V X.cpu.gpr ∧
      g'.rsp = aR X.cpu.gpr.rsp ∧ g'.rbp = aR X.cpu.gpr.rsp ∧ g'.rdi = aR X.cpu.gpr.rsp ∧
      g'.rsi = X.cpu.gpr.rdi ∧ g'.rbx = X.cpu.gpr.rbx ∧ g'.r12 = X.cpu.gpr.r12 ∧ g'.r13 = X.cpu.gpr.r13 ∧
      g'.r14 = X.cpu.gpr.r14 ∧ g'.r15 = X.cpu.gpr.r15) hK hA (by rw [addr_add_zero]; exact hrip)
    (vc_0 rfl hs1 hcl hw24 fun _ a b d e f g h i j _ => ⟨rfl, rfl, a, b, d, e, f, g, h, i, j⟩) ?_
  rintro j' g fl V₁ ⟨rfl, hV₁, gs, gp, gdi, gsi, gbx, g12, g13, g14, g15⟩ Y t₁ hKY hAY hrY hgY -
  subst V₁ hgY
  have hY : Y.cpu.gpr.rsp - 8 = aR X.cpu.gpr.rsp - 8 := by rw [gs]
  refine c.s_call hKY hAY hin (lt_len (by decide)) hrY (call_34 _) hinC (Acc.lt_len (j := 0) (by decide)) tgt_34
    (by rw [hY]; exact hr8) ?_
  rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
  rw [hY] at hA₂
  refine k1 Y₂ t₂ hK₂ hA₂ hr₂ (by rw [hg₂]; exact hY)
    ⟨by rw [hg₂]; exact kf_of gp gbx g12 g13 g14 g15, by rw [hg₂]; exact gdi, by rw [hg₂]; exact gsi⟩ ?_
  -- back from `AString (s)`, at 39
  intro Z₁ W₁ t₃ hKZ hAZ hrZ hmZ _ hP1
  refine (c_39 prof fb).run c hfs hin (fun j' g' _ V' => j' = 42 ∧ V' = W₁ ∧ g'.rdi = Z₁.cpu.gpr.rbp ∧
      Fr Z₁.cpu.gpr g') hKZ hAZ hrZ (vc_39 fun _ a b _ => ⟨rfl, rfl, a, b⟩) ?_
  rintro j' g fl V₂ ⟨rfl, hV₂, gdi', gf⟩ U t₄ hKU hAU hrU hgU -
  subst V₂ hgU
  have hmU := Fm.fr hmZ gf
  have hU : U.cpu.gpr.rsp - 8 = aR X.cpu.gpr.rsp - 8 := by rw [hmU.1]
  refine c.s_call hKU hAU hin (lt_len (by decide)) hrU (call_42 _) hinR (Rfp.lt_len (j := 0) (by decide)) tgt_42
    (by rw [hU]; exact hr8) ?_
  rintro Y₃ t₅ hK₃ hA₃ ⟨hr₃, hg₃⟩
  rw [hU] at hA₃
  refine k2 Z₁ W₁ hP1 Y₃ t₅ hK₃ hA₃ hr₃ (by rw [hg₃]; exact hU)
    ⟨by rw [hg₃]; exact kf_set hmU, by rw [hg₃]; show U.cpu.gpr.rdi = _; rw [gdi', hmZ.2.1]⟩ ?_
  -- back from `ReverseFind_PathSepar ()`, at 47
  intro Z₂ W₂ t₆ hKZ₂ hAZ₂ hrZ₂ hmZ₂ hz hP2
  exact from47 c hfs hin hinA hinD hD hKZ₂ hAZ₂ hrZ₂ hmZ₂ hcl hw0 hw8 hw24 hs1 hr8 hl hin₂ h₂ hz (k3 Z₂ W₂ hP2) k4 kr

end FV7z.Smd
