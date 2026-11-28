import FV7z.Dow.Cuts
import FV7z.Lemmas.LeafRet
import FV7z.Lemmas.CallM
import FV7z.Lemmas.AddMr64
/-!
# `CDummyOutStream::Write` (PLAN.md §M, M1)

7-Zip 26.06's `CDummyOutStream::Write (data, size, processedSize)` at `0x4e2470` in `7zzs`
(`CPP/7zip/UI/Common/Extract.cpp`; `objdump -d`), `this` in `rdi`, `data` in `rsi`, `size` in `edx`,
`processedSize` in `rcx`, `S` the stack pointer at the entry: `push rbp; mov rbp, rcx; push rbx; mov rbx, rdi;
sub rsp, 0x18` (`aR S`), `rdi` = `_stream` (`[this + 16]`, `sq`), the stack guard (`fs:0x28`) stored at `aR S + 8`,
`eax` = 0, `realProcessed` = `size` stored at `aR S + 4`; when `_stream` is not NULL, `rax` = its vtable,
`rcx` = `aR S + 4` and `call qword [rax + 0x18]` (53, `Seg.s_callM`: `_stream->Write (data, size, &realProcessed)`),
then `mov edx, [rsp + 4]` (56). Where the two ways meet (60): `mov ecx, edx`, `add [rbx + 0x18], rcx` (62, by hand:
`Seg.s_add_mr64`, `_size += realProcessed`), `*processedSize = realProcessed` unless NULL (71), the guard checked
(74), `add rsp, 0x18; pop rbx; pop rbp; ret` (96) with `eax` the result (0, or the callee's).

The callee is a hypothesis (`KC`, as in `FV7z/Smd/Holds.lean`): at its entry with the return address at
`aR S - 8`, from its return with the frame (`Fm`), the stack as it was (`Stk`: the saved `rbp`, `rbx`, the return
address and the guard at `aR S + 8` equal to the one at `fs:0x28`) and its own post (`P`). The stores at 62 and 71
are this function's own: that they keep the stack is a hypothesis (`sa`, `sp`: a store of 8 bytes at `this + 24`,
of 4 at `processedSize`, keeps `Stk`), as is `Stk` on the bytes of the prologue when `_stream` is NULL (`hs0`). Not
covered: `__stack_chk_fail` (97).

- `aR`, `Fr`, `Fm`, `Kf`, `KS`, `Stk`, `V1`, `V0c`, `V0`, `sq`, `vt`, `Up`, `Done`, `KC`: the frame, registers,
  bytes, contracts.
- `vc_0`, `vc_56`, `vc_60`, `vc_66`, `vc_74`: the pieces' verification conditions.
- `tail74`, `from60`: the runs from those offsets; `dow_ok`: the function.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Dow
set_option linter.unusedVariables false

/-! ## The instructions outside the blocks -/

/-- The `call` through the vtable. -/
def pcm : List Byte := [0xff, 0x50, 0x18]
theorem pcm_0 : ∀ feat, Dec feat pcm 0 (FV7z.mk .call 64 [.mem (mbd 0 24 64)] 3) := by dec_rfl
theorem wc_53 : pcm <+: dow.drop 53 := by decide +kernel
theorem call_53 (feat : Features) : Dec feat dow 53 (FV7z.mk .call 64 [.mem (mbd 0 24 64)] 3) :=
  Dec.shift (j := 53) (k := 0) (pcm_0 feat) wc_53 (Nat.zero_le _)

/-- `add qword [rbx + 0x18], rcx`. -/
def pad : List Byte := [0x48, 0x01, 0x4b, 0x18]
theorem pad_0 : ∀ feat, Dec feat pad 0 (FV7z.mk .add 64 [.mem (mbd 3 24 64), gr 64 1] 4) := by dec_rfl
theorem wa_62 : pad <+: dow.drop 62 := by decide +kernel
theorem add_62 (feat : Features) : Dec feat dow 62 (FV7z.mk .add 64 [.mem (mbd 3 24 64), gr 64 1] 4) :=
  Dec.shift (j := 62) (k := 0) (pad_0 feat) wa_62 (Nat.zero_le _)

/-- The `ret`. -/
def pret : List Byte := [0xc3]
theorem pret_0 : ∀ feat, Dec feat pret 0 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem w_96 : pret <+: dow.drop 96 := by decide +kernel
theorem ret_96 (feat : Features) : Dec feat dow 96 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 96) (k := 0) (pret_0 feat) w_96 (Nat.zero_le _)

/-! ## The frame -/

/-- The stack pointer after `push rbp; push rbx; sub rsp, 0x18`. -/
abbrev aR (S : Addr) : Addr := S - 8 - 8 - 24#64

theorem e24 (S : Addr) : aR S + 24#64 = S - 8 - 8 := by show S - 8 - 8 - 24#64 + 24#64 = S - 8 - 8; bv_omega
theorem e32 (S : Addr) : S - 8 - 8 + 8 = S - 8 := by bv_omega
theorem e40 (S : Addr) : S - 8 + 8 = S := by bv_omega

/-- What a piece from 56 on keeps: `rsp`, `rbp`, `rbx`, `r12`–`r15`, `rax`. -/
abbrev Fr (g g' : Gprs) : Prop :=
  g'.rsp = g.rsp ∧ g'.rbp = g.rbp ∧ g'.rbx = g.rbx ∧ g'.r12 = g.r12 ∧ g'.r13 = g.r13 ∧ g'.r14 = g.r14 ∧
    g'.r15 = g.r15 ∧ g'.rax = g.rax

/-- The frame: `rsp` = `aR S`, `rbp` = `processedSize`, `rbx` = `this`, `r12`–`r15` as at the entry (`g0`). -/
abbrev Fm (S : Addr) (g0 g : Gprs) : Prop :=
  g.rsp = aR S ∧ g.rbp = g0.rcx ∧ g.rbx = g0.rdi ∧ g.r12 = g0.r12 ∧ g.r13 = g0.r13 ∧ g.r14 = g0.r14 ∧
    g.r15 = g0.r15

/-- `Fm` but `rsp`: what the callee is given. -/
abbrev Kf (g0 g : Gprs) : Prop :=
  g.rbp = g0.rcx ∧ g.rbx = g0.rdi ∧ g.r12 = g0.r12 ∧ g.r13 = g0.r13 ∧ g.r14 = g0.r14 ∧ g.r15 = g0.r15

/-- The callee-saved registers as at the entry. -/
abbrev KS (g0 g : Gprs) : Prop :=
  g.rbx = g0.rbx ∧ g.rbp = g0.rbp ∧ g.r12 = g0.r12 ∧ g.r13 = g0.r13 ∧ g.r14 = g0.r14 ∧ g.r15 = g0.r15

theorem Fm.fr {S : Addr} {g0 g g' : Gprs} (h : Fm S g0 g) (h' : Fr g g') : Fm S g0 g' :=
  ⟨h'.1.trans h.1, h'.2.1.trans h.2.1, h'.2.2.1.trans h.2.2.1, h'.2.2.2.1.trans h.2.2.2.1,
    h'.2.2.2.2.1.trans h.2.2.2.2.1, h'.2.2.2.2.2.1.trans h.2.2.2.2.2.1, h'.2.2.2.2.2.2.1.trans h.2.2.2.2.2.2⟩

/-- The stack (`fb` the `fs` base, `ra` the return address): the saved `rbp` and `rbx`, the return address, the
stack guard as at `fs:0x28`. -/
abbrev Stk (fb : Addr) (W : Addr → Byte) (S : Addr) (g0 : Gprs) (ra : Addr) : Prop :=
  rdq(W, S - 8) = g0.rbp ∧ rdq(W, S - 8 - 8) = g0.rbx ∧ rdq(W, S) = ra ∧ rdq(W, aR S + 8#64) = rdq(W, fb + 40#64)

/-- The bytes after the pushes. -/
abbrev V1 (V : Addr → Byte) (g : Gprs) : Addr → Byte :=
  Vst (Vst V (g.rsp - 8) (toBytesLE g.rbp 8)) (g.rsp - 8 - 8) (toBytesLE g.rbx 8)

/-- `_stream`. -/
abbrev sq (V : Addr → Byte) (g : Gprs) : Addr := rdq(V1 V g, g.rdi + 16#64)

/-- The bytes after the prologue, the guard's value `cn`: the guard and `realProcessed` stored. -/
abbrev V0c (V : Addr → Byte) (g : Gprs) (cn : BitVec 64) : Addr → Byte :=
  Vst (Vst (V1 V g) (aR g.rsp + 8#64) (toBytesLE cn 8)) (aR g.rsp + 4#64) (toBytesLE (BitVec.setWidth 32 g.rdx) 4)

/-- `V0c` with the guard read from `fs:0x28`. -/
abbrev V0 (fb : Addr) (V : Addr → Byte) (g : Gprs) : Addr → Byte := V0c V g rdq(V1 V g, fb + 40#64)

/-- `_stream`'s vtable. -/
abbrev vt (fb : Addr) (V : Addr → Byte) (g : Gprs) : Addr := rdq(V0 fb V g, sq V g)

/-- `_size += v` (`a` = `this`). -/
abbrev Up (W : Addr → Byte) (a : Addr) (v : BitVec 32) : Addr → Byte :=
  Vst W (a + 24#64) (toBytesLE (ofBytesLE 64 ((byteAddrs (a + 24#64) 8).map W) + BitVec.setWidth 64 v) 8)

/-- The bytes at the return from the bytes `W` at 60: `_size += v`, then `*p = v` unless `p` is NULL. -/
abbrev Done (W W' : Addr → Byte) (a p : Addr) (v : BitVec 32) : Prop :=
  (p = 0 ∧ W' = Up W a v) ∨ (p ≠ 0 ∧ W' = Vst (Up W a v) p (toBytesLE v 4))

/-- The callee from the `call` before `j` (entry `ent`, the bytes `W`, the registers `A`): at its entry, and from
its return at `j` with the frame, `N` and `P`, the run goes on to the goal. -/
def KC (prof : Profile) (F : Footprint) (Wl : List Rgn) (L : List (Addr × List Byte)) (s₀ : State) (o : Oracle)
    (gev : List Event) (gP : State → Nat → List Event → Prop) (gE : Outcome → List Event → Prop)
    (S : Addr) (g0 : Gprs) (ent : Addr) (j : Nat) (W : Addr → Byte) (A : Gprs → Prop)
    (N P : State → (Addr → Byte) → Prop) : Prop :=
  ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y →
    Agree F Y.proc.mm.mem (Vst W (aR S - 8) (toBytesLE (dow_at.add j) 8)) →
    Y.cpu.rip = ent → Y.cpu.gpr.rsp = aR S - 8 → A Y.cpu.gpr →
    (∀ (Z : State) (W' : Addr → Byte) (t'' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem W' →
      Z.cpu.rip = dow_at.add j → Fm S g0 Z.cpu.gpr → N Z W' → P Z W' → GoG prof L o gev gP gE Z t'') →
    GoG prof L o gev gP gE Y t'

/-! ## The pieces -/

variable {F : Footprint} {Wl : List Rgn}

/-- The prologue (the guard's value named `cn`), then `test rdi, rdi`: with `_stream` NULL to 60, else
`mov rax, [rdi]; lea rcx, [rsp + 4]` to the `call` (53). -/
theorem vc_0 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} {cn : BitVec 64}
    (hcn : rdq(V1 V g, fb + 40#64) = cn)
    (hs1 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8) i)) (hs2 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8) i))
    (hcl : ∀ i < 8, Foot F.data (Addr.add (fb + 40#64) i)) (f16 : ∀ i < 8, Foot F.data (Addr.add (g.rdi + 16#64) i))
    (hw8 : ∀ i < 8, Foot Wl (Addr.add (aR g.rsp + 8#64) i)) (hw4 : ∀ i < 4, Foot Wl (Addr.add (aR g.rsp + 4#64) i))
    (fs : sq V g ≠ 0 → ∀ i < 8, Foot F.data (Addr.add (sq V g) i))
    (h60 : sq V g = 0 → ∀ g', g'.rsp = aR g.rsp → g'.rbp = g.rcx → g'.rbx = g.rdi → g'.rdx = g.rdx →
      g'.rax = 0#64 → g'.r12 = g.r12 → g'.r13 = g.r13 → g'.r14 = g.r14 → g'.r15 = g.r15 →
      ∀ fl, Q 60 g' fl (V0c V g cn))
    (h53 : sq V g ≠ 0 → ∀ g', g'.rsp = aR g.rsp → g'.rbp = g.rcx → g'.rbx = g.rdi → g'.rdi = sq V g →
      g'.rax = rdq(V0c V g cn, sq V g) → g'.rcx = aR g.rsp + 4#64 → g'.rsi = g.rsi → g'.rdx = g.rdx →
      g'.r12 = g.r12 → g'.r13 = g.r13 → g'.r14 = g.r14 → g'.r15 = g.r15 → ∀ fl, Q 53 g' fl (V0c V g cn)) :
    W_0 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [aR, sq, V1, V0c] at hcn hs1 hs2 f16 hw8 hw4 fs h60 h53 ⊢
  by_cases h0 : rdq(Vst (Vst V (rsp - 8) (toBytesLE rbp 8)) (rsp - 8 - 8) (toBytesLE rbx 8), rdi + 16#64) = 0
  · have hb : (rdq(Vst (Vst V (rsp - 8) (toBytesLE rbp 8)) (rsp - 8 - 8) (toBytesLE rbx 8), rdi + 16#64) == 0) =
        true := beq_iff_eq.2 h0
    have h := h60 h0
    wpx [W_0, W_45, o0, o1, Op.ldf, hcn, hb, BitVec.and_self, BitVec.xor_self, BitVec.reduceSetWidth,
      Bool.false_eq_true, Bool.true_eq_false, false_implies, implies_true]
    all_goals repeat' (first
      | refine h _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ _
      | with_reducible rfl
      | with_reducible exact hs1
      | with_reducible exact hs2
      | with_reducible exact hcl
      | with_reducible exact f16
      | with_reducible exact hw8
      | with_reducible exact hw4
      | apply And.intro
      | intro _)
  · have hb : (rdq(Vst (Vst V (rsp - 8) (toBytesLE rbp 8)) (rsp - 8 - 8) (toBytesLE rbx 8), rdi + 16#64) == 0) =
        false := beq_eq_false_iff_ne.2 h0
    have h := h53 h0
    have fs' := fs h0
    wpx [W_0, W_45, o0, o1, Op.ldf, hcn, hb, BitVec.and_self, BitVec.xor_self, BitVec.reduceSetWidth,
      Bool.false_eq_true, Bool.true_eq_false, false_implies, implies_true]
    all_goals repeat' (first
      | refine h _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ _
      | with_reducible rfl
      | with_reducible exact hs1
      | with_reducible exact hs2
      | with_reducible exact hcl
      | with_reducible exact f16
      | with_reducible exact hw8
      | with_reducible exact hw4
      | with_reducible exact fs'
      | apply And.intro
      | intro _)

/-- Back from the callee: `mov edx, [rsp + 4]` to 60. -/
theorem vc_56 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (f4 : ∀ i < 4, Foot F.data (Addr.add (g.rsp + 4#64) i))
    (h : ∀ g', g'.rdx = BitVec.setWidth 64 rdd(V, g.rsp + 4#64) → Fr g g' → ∀ fl, Q 60 g' fl V) :
    W_56 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at f4 h ⊢
  wpx [W_56, o2]
  all_goals repeat' (first
    | refine h _ ?_ ?_ _
    | with_reducible rfl
    | with_reducible exact f4
    | apply And.intro
    | intro _)

/-- `mov ecx, edx` to the `add` at 62. -/
theorem vc_60 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (h : ∀ g', g'.rcx = BitVec.setWidth 64 (BitVec.setWidth 32 g.rdx) → g'.rdx = g.rdx → Fr g g' →
      ∀ fl, Q 62 g' fl V) :
    W_60 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h ⊢
  wpx [W_60, o3]
  all_goals repeat' (first
    | refine h _ ?_ ?_ ?_ _
    | with_reducible rfl
    | apply And.intro
    | intro _)

/-- `test rbp, rbp`: NULL to 74, else `mov [rbp], edx` (71) and 74. -/
theorem vc_66 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (wq : g.rbp ≠ 0 → ∀ i < 4, Foot Wl (Addr.add g.rbp i))
    (hz : g.rbp = 0 → ∀ g', Fr g g' → ∀ fl, Q 74 g' fl V)
    (hn : g.rbp ≠ 0 → ∀ g', Fr g g' → ∀ fl, Q 74 g' fl (Vst V g.rbp (toBytesLE (BitVec.setWidth 32 g.rdx) 4))) :
    W_66 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at wq hz hn ⊢
  by_cases h0 : rbp = 0
  · have hb : (rbp == 0) = true := beq_iff_eq.2 h0
    have h := hz h0
    wpx [W_66, W_71, o4, o5, hb, BitVec.and_self, Bool.false_eq_true, Bool.true_eq_false, false_implies,
      implies_true]
    all_goals repeat' (first
      | refine h _ ?_ _
      | with_reducible rfl
      | apply And.intro
      | intro _)
  · have hb : (rbp == 0) = false := beq_eq_false_iff_ne.2 h0
    have h := hn h0
    have wq' := wq h0
    wpx [W_66, W_71, o4, o5, hb, BitVec.and_self, Bool.false_eq_true, Bool.true_eq_false, false_implies,
      implies_true]
    all_goals repeat' (first
      | refine h _ ?_ _
      | with_reducible rfl
      | with_reducible exact wq'
      | apply And.intro
      | intro _)

/-- The stack guard checked (as at `fs:0x28`: `jne` not taken), `add rsp, 0x18; pop rbx; pop rbp` to the `ret`. -/
theorem vc_74 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (hc : rdq(V, g.rsp + 8#64) = rdq(V, fb + 40#64)) (f8 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8#64) i))
    (fcl : ∀ i < 8, Foot F.data (Addr.add (fb + 40#64) i))
    (f24 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 24#64) i))
    (f32 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 24#64 + 8) i))
    (h : ∀ g', g'.rsp = g.rsp + 24#64 + 8 + 8 → g'.rbx = rdq(V, g.rsp + 24#64) →
      g'.rbp = rdq(V, g.rsp + 24#64 + 8) → g'.r12 = g.r12 → g'.r13 = g.r13 → g'.r14 = g.r14 → g'.r15 = g.r15 →
      g'.rax = g.rax → ∀ fl, Q 96 g' fl V) :
    W_74 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hc f8 f24 f32 h ⊢
  have z0 : ((0#64 : BitVec 64) == 0) = true := by decide
  wpx [W_74, W_90, o6, o7, Op.xormf, hc, BitVec.xor_self, z0, decide_true, Bool.not_true, Bool.false_eq_true,
    false_implies, eq_self_iff_true, true_implies]
  all_goals repeat' (first
    | refine h _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ _
    | with_reducible rfl
    | with_reducible exact f8
    | with_reducible exact fcl
    | with_reducible exact f24
    | with_reducible exact f32
    | apply And.intro
    | intro _)

/-! ## The runs -/

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {X : State} {t : Nat} {V : Addr → Byte} {e₂ : Addr} {code₂ : List Byte} {j₂ : Nat}

/-- From 74 (the frame, the stack `Stk`) to the return address `e₂.add j₂`, `rax` kept. -/
theorem tail74 {fb : Addr} {W : Addr → Byte} {S : Addr} {g0 : Gprs} {Y : State} (c : Seg prof F Wl L s₀ o)
    (hfs : s₀.cpu.seg.fsBase = fb) (hin : CodeIn L dow_at dow) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = dow_at.add 74) (hm : Fm S g0 Y.cpu.gpr)
    (hst : Stk fb W S g0 (e₂.add j₂)) (hcl : ∀ i < 8, Foot F.data (Addr.add (fb + 40#64) i))
    (f8 : ∀ i < 8, Foot F.data (Addr.add (aR S + 8#64) i)) (f16 : ∀ i < 8, Foot F.data (Addr.add (S - 8 - 8) i))
    (f24 : ∀ i < 8, Foot F.data (Addr.add (S - 8) i))
    (hl : ∀ i < 8, Foot F.data (Addr.add S i)) (hin₂ : CodeIn L e₂ code₂) (h₂ : j₂ < code₂.length)
    (k : ∀ (Z' : State) (t' : Nat), KeptW Wl s₀ Z' → Agree F Z'.proc.mm.mem W → Z'.cpu.rip = e₂.add j₂ →
      Z'.cpu.gpr.rsp = S + 8 → KS g0 Z'.cpu.gpr → Z'.cpu.gpr.rax = Y.cpu.gpr.rax → GoG prof L o gev gP gE Z' t') :
    GoG prof L o gev gP gE Y t := by
  obtain ⟨ms, mp, mb, m12, m13, m14, m15⟩ := hm
  obtain ⟨s1, s2, s3, s4⟩ := hst
  refine (c_74 prof fb).run c hfs hin (fun j' g' _ V' => j' = 96 ∧ V' = W ∧
      g'.rsp = Y.cpu.gpr.rsp + 24#64 + 8 + 8 ∧ g'.rbx = rdq(W, Y.cpu.gpr.rsp + 24#64) ∧
      g'.rbp = rdq(W, Y.cpu.gpr.rsp + 24#64 + 8) ∧ g'.r12 = Y.cpu.gpr.r12 ∧ g'.r13 = Y.cpu.gpr.r13 ∧
      g'.r14 = Y.cpu.gpr.r14 ∧ g'.r15 = Y.cpu.gpr.r15 ∧ g'.rax = Y.cpu.gpr.rax) hK hA hr
    (vc_74 (by rw [ms]; exact s4) (by rw [ms]; exact f8) hcl (by rw [ms, e24]; exact f16)
      (by rw [ms, e24, e32]; exact f24)
      fun _ a b d e f g h i _ => ⟨rfl, rfl, a, b, d, e, f, g, h, i⟩) ?_
  rintro j' g fl V₁ ⟨rfl, hV₁, gs, gb, gp, g12, g13, g14, g15, ga⟩ U t₁ hKU hAU hrU hgU -
  subst V₁ hgU
  have hsU : U.cpu.gpr.rsp = S := by rw [gs, ms, e24, e32, e40]
  have eb : rdq(W, Y.cpu.gpr.rsp + 24#64) = g0.rbx := by rw [ms, e24]; exact s2
  have ep : rdq(W, Y.cpu.gpr.rsp + 24#64 + 8) = g0.rbp := by rw [ms, e24, e32]; exact s1
  refine c.s_ret hKU hAU hin (lt_len (by decide)) hrU (ret_96 _) (by rw [hsU]; exact hl) hin₂ h₂
    (by rw [hsU]; exact s3) ?_
  rintro Z' t₂ hKZ' hAZ' ⟨hrZ', hgZ'⟩
  refine k Z' t₂ hKZ' hAZ' hrZ' ?_ ?_ ?_
  · rw [hgZ']
    show U.cpu.gpr.rsp + 8 = _
    rw [hsU]
  · rw [hgZ']
    exact ⟨gb.trans eb, gp.trans ep, g12.trans m12, g13.trans m13, g14.trans m14, g15.trans m15⟩
  · rw [hgZ']
    exact ga

/-- From 60 (the bytes `W`, the stack `Stk`): `mov ecx, edx`, `_size += edx` (62), `*processedSize = edx` unless
NULL, then 74 and the return, with `rax` as at 60 and the bytes `Done`. -/
theorem from60 {fb : Addr} {W : Addr → Byte} {S : Addr} {g0 : Gprs} {Y : State} (c : Seg prof F Wl L s₀ o)
    (hfs : s₀.cpu.seg.fsBase = fb) (hin : CodeIn L dow_at dow) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = dow_at.add 60) (hm : Fm S g0 Y.cpu.gpr)
    (hst : Stk fb W S g0 (e₂.add j₂)) (hcl : ∀ i < 8, Foot F.data (Addr.add (fb + 40#64) i))
    (f8 : ∀ i < 8, Foot F.data (Addr.add (aR S + 8#64) i)) (f16 : ∀ i < 8, Foot F.data (Addr.add (S - 8 - 8) i))
    (f24 : ∀ i < 8, Foot F.data (Addr.add (S - 8) i))
    (hl : ∀ i < 8, Foot F.data (Addr.add S i)) (hin₂ : CodeIn L e₂ code₂) (h₂ : j₂ < code₂.length)
    (wa : ∀ i < 8, Foot Wl (Addr.add (g0.rdi + 24#64) i)) (wq : g0.rcx ≠ 0 → ∀ i < 4, Foot Wl (Addr.add g0.rcx i))
    (sa : ∀ (W' : Addr → Byte) (bs : List Byte), bs.length = 8 → Stk fb W' S g0 (e₂.add j₂) →
      Stk fb (Vst W' (g0.rdi + 24#64) bs) S g0 (e₂.add j₂))
    (sp : g0.rcx ≠ 0 → ∀ (W' : Addr → Byte) (bs : List Byte), bs.length = 4 → Stk fb W' S g0 (e₂.add j₂) →
      Stk fb (Vst W' g0.rcx bs) S g0 (e₂.add j₂))
    (k : ∀ (W' : Addr → Byte) (Z' : State) (t' : Nat), KeptW Wl s₀ Z' → Agree F Z'.proc.mm.mem W' →
      Z'.cpu.rip = e₂.add j₂ → Z'.cpu.gpr.rsp = S + 8 → KS g0 Z'.cpu.gpr → Z'.cpu.gpr.rax = Y.cpu.gpr.rax →
      Done W W' g0.rdi g0.rcx (BitVec.setWidth 32 Y.cpu.gpr.rdx) → GoG prof L o gev gP gE Z' t') :
    GoG prof L o gev gP gE Y t := by
  refine (c_60 prof fb).run c hfs hin (fun j' g' _ V' => j' = 62 ∧ V' = W ∧
      g'.rcx = BitVec.setWidth 64 (BitVec.setWidth 32 Y.cpu.gpr.rdx) ∧ g'.rdx = Y.cpu.gpr.rdx ∧
      Fr Y.cpu.gpr g') hK hA hr (vc_60 fun _ a b d _ => ⟨rfl, rfl, a, b, d⟩) ?_
  rintro j' g fl V₁ ⟨rfl, hV₁, gc, gd, gf⟩ U t₁ hKU hAU hrU hgU -
  subst V₁ hgU
  have hmU := Fm.fr hm gf
  have he : eaD U 3 24 = g0.rdi + 24#64 := by
    show U.cpu.gpr.get (regOf 3) + BitVec.ofNat 64 24 = _
    rw [show U.cpu.gpr.get (regOf 3) = U.cpu.gpr.rbx from rfl, hmU.2.2.1]
  have hv : rv U 64 1 = BitVec.setWidth 64 (BitVec.setWidth 32 Y.cpu.gpr.rdx) := by
    show BitVec.setWidth 64 (U.cpu.gpr.get (regOf 1)) = _
    rw [show U.cpu.gpr.get (regOf 1) = U.cpu.gpr.rcx from rfl, gc, BitVec.setWidth_eq]
  refine c.s_add_mr64 hKU hAU hin (lt_len (by decide)) hrU (add_62 _) (by rw [he]; exact wa) ?_
  rw [he, hv]
  rintro Y₆ t₂ hK₆ hA₆ ⟨hr₆, hg₆⟩
  have hm6 : Fm S g0 Y₆.cpu.gpr := by rw [hg₆]; exact hmU
  have hst6 : Stk fb (Up W g0.rdi (BitVec.setWidth 32 Y.cpu.gpr.rdx)) S g0 (e₂.add j₂) :=
    sa _ _ (toBytesLE_length ..) hst
  have hp6 : Y₆.cpu.gpr.rbp = g0.rcx := hm6.2.1
  have hd6 : Y₆.cpu.gpr.rdx = Y.cpu.gpr.rdx := by rw [hg₆]; exact gd
  have ha6 : Y₆.cpu.gpr.rax = Y.cpu.gpr.rax := by rw [hg₆]; exact gf.2.2.2.2.2.2.2
  refine (c_66 prof fb).run c hfs hin (fun j' g' _ V' => j' = 74 ∧ Fr Y₆.cpu.gpr g' ∧
      ((g0.rcx = 0 ∧ V' = Up W g0.rdi (BitVec.setWidth 32 Y.cpu.gpr.rdx)) ∨
        (g0.rcx ≠ 0 ∧ V' = Vst (Up W g0.rdi (BitVec.setWidth 32 Y.cpu.gpr.rdx)) g0.rcx
          (toBytesLE (BitVec.setWidth 32 Y.cpu.gpr.rdx) 4)))) hK₆ hA₆ hr₆
    (vc_66 (by rw [hp6]; exact wq) (fun hz _ a _ => ⟨rfl, a, Or.inl ⟨by rw [← hp6]; exact hz, rfl⟩⟩)
      (fun hn _ a _ => ⟨rfl, a, Or.inr ⟨by rw [← hp6]; exact hn, by rw [hp6, hd6]⟩⟩)) ?_
  rintro j' g fl V₂ ⟨rfl, gf', hpost⟩ U₂ t₃ hKU₂ hAU₂ hrU₂ hgU₂ -
  subst hgU₂
  have hmU₂ := Fm.fr hm6 gf'
  have haU₂ : U₂.cpu.gpr.rax = Y.cpu.gpr.rax := gf'.2.2.2.2.2.2.2.trans ha6
  rcases hpost with ⟨hz, rfl⟩ | ⟨hn, rfl⟩
  · exact tail74 c hfs hin hKU₂ hAU₂ hrU₂ hmU₂ hst6 hcl f8 f16 f24 hl hin₂ h₂ fun Z' t' a b d e f g =>
      k _ Z' t' a b d e f (g.trans haU₂) (Or.inl ⟨hz, rfl⟩)
  · exact tail74 c hfs hin hKU₂ hAU₂ hrU₂ hmU₂ (sp hn _ _ (toBytesLE_length ..) hst6) hcl f8 f16 f24 hl hin₂ h₂
      fun Z' t' a b d e f g => k _ Z' t' a b d e f (g.trans haU₂) (Or.inr ⟨hn, rfl⟩)

/-- `CDummyOutStream::Write (data, size, processedSize)` from its entry, `S` = `X`'s `rsp`, `fb` the `fs` base:
the pushes' slots, the guard's and `realProcessed`'s slots and the `call`'s return address slot, `_size`
(`this + 24`) and `*processedSize` unless NULL in what the run may store into; `_stream` (`this + 16`), the guard at
`fs:0x28` and the return address readable, and when `_stream` is set its vtable and the vtable's entry at 24. When
`_stream` is NULL, `Stk` on the prologue's bytes (`hs0`); else the callee (`kf`, at `eF`, the entry's `rsi`, `rdx`,
`rdi` = `_stream`, `rcx` = `aR S + 4`; from its return the stack `Stk` and `P1`). The stores at 62 and 71 keep the
stack (`sa`, `sp`). At the return address (`kr`): `rsp` 8 above the entry's, the callee-saved registers as they
were, and with `_stream` NULL `rax` 0 and the prologue's bytes updated with `size`, else `rax` the callee's and its
bytes updated with `realProcessed` (`Done`). -/
theorem dow_ok {fb : Addr} {eF : Addr} {codeF : List Byte} {P1 : State → (Addr → Byte) → Prop}
    (c : Seg prof F Wl L s₀ o) (hfs : s₀.cpu.seg.fsBase = fb) (hin : CodeIn L dow_at dow)
    (hinF : CodeIn L eF codeF) (hF0 : 0 < codeF.length)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = dow_at)
    (hcl : ∀ i < 8, Foot F.data (Addr.add (fb + 40#64) i))
    (hs1 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8) i))
    (hs2 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8 - 8) i))
    (hw8 : ∀ i < 8, Foot Wl (Addr.add (aR X.cpu.gpr.rsp + 8#64) i))
    (hw4 : ∀ i < 4, Foot Wl (Addr.add (aR X.cpu.gpr.rsp + 4#64) i))
    (hr8 : ∀ i < 8, Foot Wl (Addr.add (aR X.cpu.gpr.rsp - 8) i))
    (hl : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsp i))
    (f16 : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rdi + 16#64) i))
    (fs : sq V X.cpu.gpr ≠ 0 → ∀ i < 8, Foot F.data (Addr.add (sq V X.cpu.gpr) i))
    (fv : sq V X.cpu.gpr ≠ 0 → ∀ i < 8, Foot F.data (Addr.add (vt fb V X.cpu.gpr + 24#64) i))
    (htgt : sq V X.cpu.gpr ≠ 0 → rdq(V0 fb V X.cpu.gpr, vt fb V X.cpu.gpr + 24#64) = eF)
    (wa : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rdi + 24#64) i))
    (wq : X.cpu.gpr.rcx ≠ 0 → ∀ i < 4, Foot Wl (Addr.add X.cpu.gpr.rcx i))
    (hin₂ : CodeIn L e₂ code₂) (h₂ : j₂ < code₂.length)
    (hs0 : sq V X.cpu.gpr = 0 → Stk fb (V0 fb V X.cpu.gpr) X.cpu.gpr.rsp X.cpu.gpr (e₂.add j₂))
    (sa : ∀ (W' : Addr → Byte) (bs : List Byte), bs.length = 8 → Stk fb W' X.cpu.gpr.rsp X.cpu.gpr (e₂.add j₂) →
      Stk fb (Vst W' (X.cpu.gpr.rdi + 24#64) bs) X.cpu.gpr.rsp X.cpu.gpr (e₂.add j₂))
    (sp : X.cpu.gpr.rcx ≠ 0 → ∀ (W' : Addr → Byte) (bs : List Byte), bs.length = 4 →
      Stk fb W' X.cpu.gpr.rsp X.cpu.gpr (e₂.add j₂) →
      Stk fb (Vst W' X.cpu.gpr.rcx bs) X.cpu.gpr.rsp X.cpu.gpr (e₂.add j₂))
    (kf : sq V X.cpu.gpr ≠ 0 → KC prof F Wl L s₀ o gev gP gE X.cpu.gpr.rsp X.cpu.gpr eF 56 (V0 fb V X.cpu.gpr)
      (fun g => Kf X.cpu.gpr g ∧ g.rdi = sq V X.cpu.gpr ∧ g.rsi = X.cpu.gpr.rsi ∧ g.rdx = X.cpu.gpr.rdx ∧
        g.rcx = aR X.cpu.gpr.rsp + 4#64)
      (fun _ W' => Stk fb W' X.cpu.gpr.rsp X.cpu.gpr (e₂.add j₂)) P1)
    (kr : ∀ (W' : Addr → Byte) (Z' : State) (t' : Nat), KeptW Wl s₀ Z' → Agree F Z'.proc.mm.mem W' →
      Z'.cpu.rip = e₂.add j₂ → Z'.cpu.gpr.rsp = X.cpu.gpr.rsp + 8 → KS X.cpu.gpr Z'.cpu.gpr →
      ((sq V X.cpu.gpr = 0 ∧ Z'.cpu.gpr.rax = 0#64 ∧
          Done (V0 fb V X.cpu.gpr) W' X.cpu.gpr.rdi X.cpu.gpr.rcx (BitVec.setWidth 32 X.cpu.gpr.rdx)) ∨
        (∃ (Z₁ : State) (W₁ : Addr → Byte), P1 Z₁ W₁ ∧ Z'.cpu.gpr.rax = Z₁.cpu.gpr.rax ∧
          Done W₁ W' X.cpu.gpr.rdi X.cpu.gpr.rcx rdd(W₁, aR X.cpu.gpr.rsp + 4#64))) →
      GoG prof L o gev gP gE Z' t') :
    GoG prof L o gev gP gE X t := by
  have f8 : ∀ i < 8, Foot F.data (Addr.add (aR X.cpu.gpr.rsp + 8#64) i) := fun i hi => c.hws _ (hw8 i hi)
  have f4 : ∀ i < 4, Foot F.data (Addr.add (aR X.cpu.gpr.rsp + 4#64) i) := fun i hi => c.hws _ (hw4 i hi)
  have g16 : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rsp - 8 - 8) i) := fun i hi => c.hws _ (hs2 i hi)
  have g24 : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rsp - 8) i) := fun i hi => c.hws _ (hs1 i hi)
  -- the prologue, to 60 or to the `call`
  refine (c_0 prof fb).run c hfs hin (fun j' g' _ V' => V' = V0 fb V X.cpu.gpr ∧
      g'.rsp = aR X.cpu.gpr.rsp ∧ g'.rbp = X.cpu.gpr.rcx ∧ g'.rbx = X.cpu.gpr.rdi ∧ g'.r12 = X.cpu.gpr.r12 ∧
      g'.r13 = X.cpu.gpr.r13 ∧ g'.r14 = X.cpu.gpr.r14 ∧ g'.r15 = X.cpu.gpr.r15 ∧
      ((sq V X.cpu.gpr = 0 ∧ j' = 60 ∧ g'.rdx = X.cpu.gpr.rdx ∧ g'.rax = 0#64) ∨
        (sq V X.cpu.gpr ≠ 0 ∧ j' = 53 ∧ g'.rdi = sq V X.cpu.gpr ∧ g'.rax = vt fb V X.cpu.gpr ∧
          g'.rcx = aR X.cpu.gpr.rsp + 4#64 ∧ g'.rsi = X.cpu.gpr.rsi ∧ g'.rdx = X.cpu.gpr.rdx))) hK hA
    (by rw [addr_add_zero]; exact hrip)
    (vc_0 rfl hs1 hs2 hcl f16 hw8 hw4 fs
      (fun hz _ a b d e f g h i j _ => ⟨rfl, a, b, d, g, h, i, j, Or.inl ⟨hz, rfl, e, f⟩⟩)
      (fun hn _ a b d e f g h i j l m n _ => ⟨rfl, a, b, d, j, l, m, n, Or.inr ⟨hn, rfl, e, f, g, h, i⟩⟩)) ?_
  rintro j' g fl V₁ ⟨hV₁, gs, gp, gb, g12, g13, g14, g15, hpost⟩ Y t₁ hKY hAY hrY hgY -
  subst V₁ hgY
  rcases hpost with ⟨hz, rfl, gd, ga⟩ | ⟨hn, rfl, gdi, ga, gc, gsi, gd⟩
  · -- `_stream` NULL: at 60 with the prologue's bytes
    refine from60 c hfs hin hKY hAY hrY ⟨gs, gp, gb, g12, g13, g14, g15⟩ (hs0 hz) hcl f8 g16 g24 hl hin₂ h₂
      wa wq sa sp ?_
    intro W' Z' t' a b d e f g hd
    rw [gd] at hd
    exact kr W' Z' t' a b d e f (Or.inl ⟨hz, g.trans ga, hd⟩)
  · -- `_stream` set: the `call` at 53
    have hY : Y.cpu.gpr.rsp - 8 = aR X.cpu.gpr.rsp - 8 := by rw [gs]
    have he : eaD Y 0 24 = vt fb V X.cpu.gpr + 24#64 := by
      show Y.cpu.gpr.get (regOf 0) + BitVec.ofNat 64 24 = _
      rw [show Y.cpu.gpr.get (regOf 0) = Y.cpu.gpr.rax from rfl, ga]
    refine c.s_callM hKY hAY hin (lt_len (by decide)) hrY (call_53 _) (by rw [he]; exact fv hn) hinF hF0
      (by rw [he]; exact htgt hn) (by rw [hY]; exact hr8) ?_
    rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
    rw [hY] at hA₂
    refine kf hn Y₂ t₂ hK₂ hA₂ hr₂ (by rw [hg₂]; exact hY)
      ⟨by rw [hg₂]; exact ⟨gp, gb, g12, g13, g14, g15⟩, by rw [hg₂]; exact gdi, by rw [hg₂]; exact gsi,
        by rw [hg₂]; exact gd, by rw [hg₂]; exact gc⟩ ?_
    -- back from the callee, at 56
    intro Z₁ W₁ t₃ hKZ hAZ hrZ hmZ hstZ hP1
    refine (c_56 prof fb).run c hfs hin (fun j' g' _ V' => j' = 60 ∧ V' = W₁ ∧
        g'.rdx = BitVec.setWidth 64 rdd(W₁, Z₁.cpu.gpr.rsp + 4#64) ∧ Fr Z₁.cpu.gpr g') hKZ hAZ hrZ
      (vc_56 (by rw [hmZ.1]; exact f4) fun _ a b _ => ⟨rfl, rfl, a, b⟩) ?_
    rintro j' g fl V₂ ⟨rfl, hV₂, gd', gf⟩ U t₄ hKU hAU hrU hgU -
    subst V₂ hgU
    have hmU := Fm.fr hmZ gf
    refine from60 c hfs hin hKU hAU hrU hmU hstZ hcl f8 g16 g24 hl hin₂ h₂ wa wq sa sp ?_
    intro W' Z' t' a b d e f g hd
    rw [gd', hmZ.1, sw_64_32] at hd
    exact kr W' Z' t' a b d e f (Or.inr ⟨Z₁, W₁, hP1, g.trans gf.2.2.2.2.2.2.2, hd⟩)

end FV7z.Dow
