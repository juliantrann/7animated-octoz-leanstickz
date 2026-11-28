import FV7z.Rst.Cuts
import FV7z.Lemmas.LeafRet
import FV7z.Lemmas.CallM
import FV7z.Lemmas.AddMr64
import FV7z.Wst.Holds
/-!
# `ReadStream` (PLAN.md §M, M1)

7-Zip 26.06's `ReadStream (stream, data, size)` at `0x4632b0` in `7zzs` (`CPP/7zip/Common/StreamUtils.cpp`;
`objdump -d`), `stream` in `rdi`, `data` in `rsi`, `size` (a pointer) in `rdx`, `S` the stack pointer at the entry:
the six pushes and `sub rsp, 0x18` (`aR S`), `rbx` = `*size` (what is left, `r`), the stack guard (`fs:0x28`)
stored at `aR S + 8`, `eax` = 0, `*size = 0`; `rbx` 0 to 168. Else (49) `r15` = `stream`, `r13` = `data`, `r14` =
`size`, `rbp` = `0x80000000` (`m`), `r12` = `aR S + 4`, and the loop (89): `rax` = the vtable, `rdx` = `r` capped
at `m` (`Wst.rq`), `call qword [rax + 0x18]` (111, `Seg.s_callM`: `stream->Read (data, cur, &processed)`). Back
(114): `edx` = `processed` (`v`), `add [r14], rdx` (118, by hand: `Seg.s_add_mr64`, `*size += v`), `r13 += v`,
`rbx -= v`; the callee's `eax` not 0, or `v` 0, to 131; `rbx` 0 to 168 (`eax` = 0); else 89. At 131 the guard
checked, `add rsp, 0x18`, the six pops, `ret` (161).

As in `FV7z/Wst/Holds.lean`: the memory is the caller's invariant `I`, here also kept by the stores to `*size`
(`hIa`); the loop by induction on what is left. Not covered: `__stack_chk_fail` (172).

- `aR`, `Stk`, `V1`, `V0c`, `V0`, `Lp`, `Ar`, `KC`: the frame, registers, bytes, contracts (`Wst.rq`, `Wst.KS`).
- `vc_0`, `vc_89`, `vc_114`, `vc_121a`, `vc_121s`, `vc_121z`, `vc_121c`, `vc_131`, `vc_168`: the pieces'
  verification conditions.
- `tail131`: the run from 131; `rst_ok`: the function.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Rst
set_option linter.unusedVariables false

open FV7z.Wst (rq rq_le sw_toNat sub_dec pos_of_ne sa8 KS)

/-! ## The instructions outside the blocks -/

/-- The `call` through the vtable. -/
def pcm : List Byte := [0xff, 0x50, 0x18]
theorem pcm_0 : ∀ feat, Dec feat pcm 0 (FV7z.mk .call 64 [.mem (mbd 0 24 64)] 3) := by dec_rfl
theorem wc_111 : pcm <+: rst.drop 111 := by decide +kernel
theorem call_111 (feat : Features) : Dec feat rst 111 (FV7z.mk .call 64 [.mem (mbd 0 24 64)] 3) :=
  Dec.shift (j := 111) (k := 0) (pcm_0 feat) wc_111 (Nat.zero_le _)

/-- `add qword [r14], rdx`. -/
def pad : List Byte := [0x49, 0x01, 0x16]
theorem pad_0 : ∀ feat, Dec feat pad 0 (FV7z.mk .add 64 [.mem (mbd 14 0 64), gr 64 2] 3) := by dec_rfl
theorem wa_118 : pad <+: rst.drop 118 := by decide +kernel
theorem add_118 (feat : Features) : Dec feat rst 118 (FV7z.mk .add 64 [.mem (mbd 14 0 64), gr 64 2] 3) :=
  Dec.shift (j := 118) (k := 0) (pad_0 feat) wa_118 (Nat.zero_le _)

/-- The `ret`. -/
def pret : List Byte := [0xc3]
theorem pret_0 : ∀ feat, Dec feat pret 0 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem w_161 : pret <+: rst.drop 161 := by decide +kernel
theorem ret_161 (feat : Features) : Dec feat rst 161 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 161) (k := 0) (pret_0 feat) w_161 (Nat.zero_le _)

/-! ## The frame -/

/-- The stack pointer after the six pushes and `sub rsp, 0x18`. -/
abbrev aR (S : Addr) : Addr := S - 8 - 8 - 8 - 8 - 8 - 8 - 24#64

theorem e24 (S : Addr) : aR S + 24#64 = S - 8 - 8 - 8 - 8 - 8 - 8 := BitVec.sub_add_cancel _ _

/-- The stack: the saved `r15`, `r14`, `r13`, `r12`, `rbp`, `rbx`, the return address, the guard as at
`fs:0x28`. -/
abbrev Stk (fb : Addr) (W : Addr → Byte) (S : Addr) (g0 : Gprs) (ra : Addr) : Prop :=
  rdq(W, S - 8) = g0.r15 ∧ rdq(W, S - 8 - 8) = g0.r14 ∧ rdq(W, S - 8 - 8 - 8) = g0.r13 ∧
    rdq(W, S - 8 - 8 - 8 - 8) = g0.r12 ∧ rdq(W, S - 8 - 8 - 8 - 8 - 8) = g0.rbp ∧
    rdq(W, S - 8 - 8 - 8 - 8 - 8 - 8) = g0.rbx ∧ rdq(W, S) = ra ∧ rdq(W, aR S + 8#64) = rdq(W, fb + 40#64)

/-- The bytes after the pushes. -/
abbrev V1 (V : Addr → Byte) (g : Gprs) : Addr → Byte :=
  Vst (Vst (Vst (Vst (Vst (Vst V (g.rsp - 8) (toBytesLE g.r15 8)) (g.rsp - 8 - 8) (toBytesLE g.r14 8))
    (g.rsp - 8 - 8 - 8) (toBytesLE g.r13 8)) (g.rsp - 8 - 8 - 8 - 8) (toBytesLE g.r12 8))
    (g.rsp - 8 - 8 - 8 - 8 - 8) (toBytesLE g.rbp 8)) (g.rsp - 8 - 8 - 8 - 8 - 8 - 8) (toBytesLE g.rbx 8)

/-- The bytes after the prologue, the guard's value `cn`: the guard stored, `*size = 0`. -/
abbrev V0c (V : Addr → Byte) (g : Gprs) (cn : BitVec 64) : Addr → Byte :=
  Vst (Vst (V1 V g) (aR g.rsp + 8#64) (toBytesLE cn 8)) g.rdx (toBytesLE 0#64 8)

/-- `V0c` with the guard read from `fs:0x28`. -/
abbrev V0 (fb : Addr) (V : Addr → Byte) (g : Gprs) : Addr → Byte := V0c V g rdq(V1 V g, fb + 40#64)

/-- The loop's registers: `rbx` = what is left `r`, `r13` = the data `p`, `rbp` = the cap `m`, `r12` =
`aR S + 4`, `r15` = `stream`, `r14` = `size`. -/
abbrev Lp (S : Addr) (g0 : Gprs) (m r p : BitVec 64) (g : Gprs) : Prop :=
  g.rsp = aR S ∧ g.rbx = r ∧ g.r13 = p ∧ g.rbp = m ∧ g.r12 = aR S + 4#64 ∧ g.r15 = g0.rdi ∧ g.r14 = g0.rdx

/-- What the callee is given: `Lp` but `rsp`, `rdi` = `stream`, `rsi` = `p`, `rdx` = `rq m r`, `rcx` =
`aR S + 4`. -/
abbrev Ar (S : Addr) (g0 : Gprs) (m r p : BitVec 64) (g : Gprs) : Prop :=
  g.rbx = r ∧ g.r13 = p ∧ g.rbp = m ∧ g.r12 = aR S + 4#64 ∧ g.r15 = g0.rdi ∧ g.r14 = g0.rdx ∧
    g.rdi = g0.rdi ∧ g.rsi = p ∧ g.rdx = rq m r ∧ g.rcx = aR S + 4#64

/-- The callee from the `call` at 111 (entry `ent`, the bytes `W`, the registers `A`): at its entry, and from its
return at 114 with `B` and `N`, the run goes on to the goal. -/
def KC (prof : Profile) (F : Footprint) (Wl : List Rgn) (L : List (Addr × List Byte)) (s₀ : State) (o : Oracle)
    (gev : List Event) (gP : State → Nat → List Event → Prop) (gE : Outcome → List Event → Prop)
    (S ent : Addr) (W : Addr → Byte) (A B : Gprs → Prop) (N : (Addr → Byte) → Prop) : Prop :=
  ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y →
    Agree F Y.proc.mm.mem (Vst W (aR S - 8) (toBytesLE (rst_at.add 114) 8)) →
    Y.cpu.rip = ent → Y.cpu.gpr.rsp = aR S - 8 → A Y.cpu.gpr →
    (∀ (Z : State) (W' : Addr → Byte) (t'' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem W' →
      Z.cpu.rip = rst_at.add 114 → B Z.cpu.gpr → N W' → GoG prof L o gev gP gE Z t'') →
    GoG prof L o gev gP gE Y t'

/-! ## The pieces -/

variable {F : Footprint} {Wl : List Rgn}

/-- The prologue (the guard's value named `cn`), `test rbx, rbx` (`rbx` = `*size`): 0 to 168, else the loop's
registers set (49) and 89. -/
theorem vc_0 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} {cn : BitVec 64}
    (hcn : rdq(V1 V g, fb + 40#64) = cn)
    (hs1 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8) i)) (hs2 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8) i))
    (hs3 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8 - 8) i))
    (hs4 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8 - 8 - 8) i))
    (hs5 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8 - 8 - 8 - 8) i))
    (hs6 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8 - 8 - 8 - 8 - 8) i))
    (hcl : ∀ i < 8, Foot F.data (Addr.add (fb + 40#64) i))
    (hw8 : ∀ i < 8, Foot Wl (Addr.add (aR g.rsp + 8#64) i))
    (fz : ∀ i < 8, Foot F.data (Addr.add g.rdx i)) (wz : ∀ i < 8, Foot Wl (Addr.add g.rdx i))
    (h168 : rdq(V1 V g, g.rdx) = 0 → ∀ g', g'.rsp = aR g.rsp → ∀ fl, Q 168 g' fl (V0c V g cn))
    (h89 : rdq(V1 V g, g.rdx) ≠ 0 → ∀ g', g'.rsp = aR g.rsp → g'.rbx = rdq(V1 V g, g.rdx) → g'.r13 = g.rsi →
      g'.rbp = 2147483648#64 → g'.r12 = aR g.rsp + 4#64 → g'.r15 = g.rdi → g'.r14 = g.rdx →
      ∀ fl, Q 89 g' fl (V0c V g cn)) :
    W_0 fb F Wl Q g f V := by
  by_cases h0 : rdq(V1 V g, g.rdx) = 0
  · have hb : (rdq(V1 V g, g.rdx) == 0) = true := beq_iff_eq.2 h0
    have h := h168 h0
    obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
    dsimp only [aR, V1, V0c] at hcn hs1 hs2 hs3 hs4 hs5 hs6 hw8 fz wz hb h ⊢
    wpx [W_0, W_49, o0, o1, Op.ldf, hcn, hb, BitVec.and_self, BitVec.xor_self, BitVec.reduceSetWidth,
      Bool.false_eq_true, Bool.true_eq_false, false_implies, implies_true]
    all_goals repeat' (first
      | refine h _ ?_ _
      | with_reducible rfl
      | with_reducible exact hs1
      | with_reducible exact hs2
      | with_reducible exact hs3
      | with_reducible exact hs4
      | with_reducible exact hs5
      | with_reducible exact hs6
      | with_reducible exact hcl
      | with_reducible exact hw8
      | with_reducible exact fz
      | with_reducible exact wz
      | apply And.intro
      | intro _)
  · have hb : (rdq(V1 V g, g.rdx) == 0) = false := beq_eq_false_iff_ne.2 h0
    have h := h89 h0
    obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
    dsimp only [aR, V1, V0c] at hcn hs1 hs2 hs3 hs4 hs5 hs6 hw8 fz wz hb h ⊢
    wpx [W_0, W_49, o0, o1, Op.ldf, hcn, hb, BitVec.and_self, BitVec.xor_self, BitVec.reduceSetWidth,
      Bool.false_eq_true, Bool.true_eq_false, false_implies, implies_true]
    all_goals repeat' (first
      | refine h _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ _
      | with_reducible rfl
      | with_reducible exact hs1
      | with_reducible exact hs2
      | with_reducible exact hs3
      | with_reducible exact hs4
      | with_reducible exact hs5
      | with_reducible exact hs6
      | with_reducible exact hcl
      | with_reducible exact hw8
      | with_reducible exact fz
      | with_reducible exact wz
      | apply And.intro
      | intro _)

/-- The loop's head: `rax` = the vtable, `rdx` = `rq rbp rbx`, `rsi` = `r13`, `rcx` = `r12`, `rdi` = `r15`, to the
`call` (111). -/
theorem vc_89 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (fa : ∀ i < 8, Foot F.data (Addr.add g.r15 i))
    (h : ∀ g', g'.rax = rdq(V, g.r15) → g'.rdx = rq g.rbp g.rbx → g'.rsi = g.r13 → g'.rcx = g.r12 →
      g'.rdi = g.r15 → g'.rsp = g.rsp → g'.rbx = g.rbx → g'.rbp = g.rbp → g'.r12 = g.r12 → g'.r13 = g.r13 →
      g'.r14 = g.r14 → g'.r15 = g.r15 → ∀ fl, Q 111 g' fl V) :
    W_89 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at fa h ⊢
  by_cases hc : rbx.toNat < rbp.toNat
  · have hd : decide (rbx.toNat < rbp.toNat) = true := decide_eq_true hc
    rw [show rq rbp rbx = rbx from if_pos hc] at h
    wpx [W_89, o4, hd, eq_self_iff_true, ↓reduceIte]
    all_goals repeat' (first
      | refine h _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ _
      | with_reducible rfl
      | with_reducible exact fa
      | apply And.intro
      | intro _)
  · have hd : decide (rbx.toNat < rbp.toNat) = false := decide_eq_false hc
    rw [show rq rbp rbx = rbp from if_neg hc] at h
    wpx [W_89, o4, hd, Bool.false_eq_true, ↓reduceIte]
    all_goals repeat' (first
      | refine h _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ _
      | with_reducible rfl
      | with_reducible exact fa
      | apply And.intro
      | intro _)

/-- Back from the callee: `mov edx, [rsp + 4]` to the `add` at 118. -/
theorem vc_114 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (f4 : ∀ i < 4, Foot F.data (Addr.add (g.rsp + 4#64) i))
    (h : ∀ g', g'.rdx = BitVec.setWidth 64 rdd(V, g.rsp + 4#64) → g'.rsp = g.rsp → g'.rbx = g.rbx →
      g'.rbp = g.rbp → g'.r12 = g.r12 → g'.r13 = g.r13 → g'.r14 = g.r14 → g'.r15 = g.r15 → g'.rax = g.rax →
      ∀ fl, Q 118 g' fl V) :
    W_114 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at f4 h ⊢
  wpx [W_114, o5]
  all_goals repeat' (first
    | refine h _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ _
    | with_reducible rfl
    | with_reducible exact f4
    | apply And.intro
    | intro _)

/-- `r13 += rdx`, `rbx -= rdx`, the callee's `eax` not 0: to 131. -/
theorem vc_121a {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (ha : (BitVec.setWidth 32 g.rax == 0) = false)
    (h : ∀ g', g'.rsp = g.rsp → ∀ fl, Q 131 g' fl V) :
    W_121 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at ha h ⊢
  wpx [W_121, o6, ha, BitVec.and_self, Bool.false_eq_true, Bool.true_eq_false, false_implies, eq_self_iff_true,
    implies_true]
  all_goals repeat' (first
    | refine h _ ?_ _
    | with_reducible rfl
    | apply And.intro
    | intro _)

/-- `eax` 0 and `edx` 0 (nothing read): to 131. -/
theorem vc_121s {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (ha : (BitVec.setWidth 32 g.rax == 0) = true) (hv : (BitVec.setWidth 32 g.rdx == 0) = true)
    (h : ∀ g', g'.rsp = g.rsp → ∀ fl, Q 131 g' fl V) :
    W_121 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at ha hv h ⊢
  wpx [W_121, W_80, o6, o2, ha, hv, BitVec.and_self, Bool.false_eq_true, Bool.true_eq_false, false_implies,
    eq_self_iff_true, implies_true]
  all_goals repeat' (first
    | refine h _ ?_ _
    | with_reducible rfl
    | apply And.intro
    | intro _)

/-- `eax` 0, `edx` not 0 and nothing left: to 168. -/
theorem vc_121z {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (ha : (BitVec.setWidth 32 g.rax == 0) = true) (hv : (BitVec.setWidth 32 g.rdx == 0) = false)
    (hr : (g.rbx - g.rdx == 0) = true)
    (h : ∀ g', g'.rsp = g.rsp → ∀ fl, Q 168 g' fl V) :
    W_121 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at ha hv hr h ⊢
  wpx [W_121, W_80, W_84, o6, o2, o3, ha, hv, hr, BitVec.and_self, Bool.false_eq_true, Bool.true_eq_false,
    false_implies, eq_self_iff_true, implies_true]
  all_goals repeat' (first
    | refine h _ ?_ _
    | with_reducible rfl
    | apply And.intro
    | intro _)

/-- `eax` 0, `edx` not 0 and something left: to 89. -/
theorem vc_121c {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (ha : (BitVec.setWidth 32 g.rax == 0) = true) (hv : (BitVec.setWidth 32 g.rdx == 0) = false)
    (hr : (g.rbx - g.rdx == 0) = false)
    (h : ∀ g', g'.rsp = g.rsp → g'.rbx = g.rbx - g.rdx → g'.r13 = g.r13 + g.rdx → g'.rbp = g.rbp →
      g'.r12 = g.r12 → g'.r14 = g.r14 → g'.r15 = g.r15 → ∀ fl, Q 89 g' fl V) :
    W_121 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at ha hv hr h ⊢
  wpx [W_121, W_80, W_84, o6, o2, o3, ha, hv, hr, BitVec.and_self, Bool.false_eq_true, Bool.true_eq_false,
    false_implies, eq_self_iff_true, implies_true]
  all_goals repeat' (first
    | refine h _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ _
    | with_reducible rfl
    | apply And.intro
    | intro _)

/-- The stack guard checked, `add rsp, 0x18` and the six pops to the `ret`. -/
theorem vc_131 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (hc : rdq(V, g.rsp + 8#64) = rdq(V, fb + 40#64)) (f8 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8#64) i))
    (fcl : ∀ i < 8, Foot F.data (Addr.add (fb + 40#64) i))
    (p1 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 24#64) i))
    (p2 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 24#64 + 8) i))
    (p3 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 24#64 + 8 + 8) i))
    (p4 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 24#64 + 8 + 8 + 8) i))
    (p5 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 24#64 + 8 + 8 + 8 + 8) i))
    (p6 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 24#64 + 8 + 8 + 8 + 8 + 8) i))
    (h : ∀ g', g'.rsp = g.rsp + 24#64 + 8 + 8 + 8 + 8 + 8 + 8 → g'.rbx = rdq(V, g.rsp + 24#64) →
      g'.rbp = rdq(V, g.rsp + 24#64 + 8) → g'.r12 = rdq(V, g.rsp + 24#64 + 8 + 8) →
      g'.r13 = rdq(V, g.rsp + 24#64 + 8 + 8 + 8) → g'.r14 = rdq(V, g.rsp + 24#64 + 8 + 8 + 8 + 8) →
      g'.r15 = rdq(V, g.rsp + 24#64 + 8 + 8 + 8 + 8 + 8) → ∀ fl, Q 161 g' fl V) :
    W_131 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hc f8 p1 p2 p3 p4 p5 p6 h ⊢
  have z0 : ((0#64 : BitVec 64) == 0) = true := by decide
  wpx [W_131, W_147, o7, o8, Op.xormf, hc, BitVec.xor_self, z0, decide_true, Bool.not_true, Bool.false_eq_true,
    false_implies, eq_self_iff_true, true_implies]
  all_goals repeat' (first
    | refine h _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ _
    | with_reducible rfl
    | with_reducible exact f8
    | with_reducible exact fcl
    | with_reducible exact p1
    | with_reducible exact p2
    | with_reducible exact p3
    | with_reducible exact p4
    | with_reducible exact p5
    | with_reducible exact p6
    | apply And.intro
    | intro _)

/-- `xor eax, eax`, to 131. -/
theorem vc_168 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (h : ∀ g', g'.rsp = g.rsp → ∀ fl, Q 131 g' fl V) :
    W_168 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h ⊢
  wpx [W_168, o9]
  all_goals repeat' (first
    | refine h _ ?_ _
    | with_reducible rfl
    | apply And.intro
    | intro _)

/-! ## The runs -/

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {X : State} {t : Nat} {V : Addr → Byte} {e₂ : Addr} {code₂ : List Byte} {j₂ : Nat}

/-- From 131 (`rsp` = `aR S`, the stack `Stk`) to the return address `e₂.add j₂`. -/
theorem tail131 {fb : Addr} {W : Addr → Byte} {S : Addr} {g0 : Gprs} {Y : State} (c : Seg prof F Wl L s₀ o)
    (hfs : s₀.cpu.seg.fsBase = fb) (hin : CodeIn L rst_at rst) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = rst_at.add 131) (hs : Y.cpu.gpr.rsp = aR S)
    (hst : Stk fb W S g0 (e₂.add j₂))
    (hcl : ∀ i < 8, Foot F.data (Addr.add (fb + 40#64) i)) (f8 : ∀ i < 8, Foot F.data (Addr.add (aR S + 8#64) i))
    (g1 : ∀ i < 8, Foot F.data (Addr.add (S - 8) i)) (g2 : ∀ i < 8, Foot F.data (Addr.add (S - 8 - 8) i))
    (g3 : ∀ i < 8, Foot F.data (Addr.add (S - 8 - 8 - 8) i))
    (g4 : ∀ i < 8, Foot F.data (Addr.add (S - 8 - 8 - 8 - 8) i))
    (g5 : ∀ i < 8, Foot F.data (Addr.add (S - 8 - 8 - 8 - 8 - 8) i))
    (g6 : ∀ i < 8, Foot F.data (Addr.add (S - 8 - 8 - 8 - 8 - 8 - 8) i))
    (hl : ∀ i < 8, Foot F.data (Addr.add S i)) (hin₂ : CodeIn L e₂ code₂) (h₂ : j₂ < code₂.length)
    (k : ∀ (Z' : State) (t' : Nat), KeptW Wl s₀ Z' → Agree F Z'.proc.mm.mem W → Z'.cpu.rip = e₂.add j₂ →
      Z'.cpu.gpr.rsp = S + 8 → KS g0 Z'.cpu.gpr → GoG prof L o gev gP gE Z' t') :
    GoG prof L o gev gP gE Y t := by
  obtain ⟨s1, s2, s3, s4, s5, s6, s7, s8⟩ := hst
  have q1 : Y.cpu.gpr.rsp + 24#64 = S - 8 - 8 - 8 - 8 - 8 - 8 := by rw [hs, e24]
  have q2 : Y.cpu.gpr.rsp + 24#64 + 8 = S - 8 - 8 - 8 - 8 - 8 := by rw [q1, sa8]
  have q3 : Y.cpu.gpr.rsp + 24#64 + 8 + 8 = S - 8 - 8 - 8 - 8 := by rw [q2, sa8]
  have q4 : Y.cpu.gpr.rsp + 24#64 + 8 + 8 + 8 = S - 8 - 8 - 8 := by rw [q3, sa8]
  have q5 : Y.cpu.gpr.rsp + 24#64 + 8 + 8 + 8 + 8 = S - 8 - 8 := by rw [q4, sa8]
  have q6 : Y.cpu.gpr.rsp + 24#64 + 8 + 8 + 8 + 8 + 8 = S - 8 := by rw [q5, sa8]
  have q7 : Y.cpu.gpr.rsp + 24#64 + 8 + 8 + 8 + 8 + 8 + 8 = S := by rw [q6, sa8]
  refine (c_131 prof fb).run c hfs hin (fun j' g' _ V' => j' = 161 ∧ V' = W ∧ g'.rsp = S ∧
      g'.rbx = g0.rbx ∧ g'.rbp = g0.rbp ∧ g'.r12 = g0.r12 ∧ g'.r13 = g0.r13 ∧ g'.r14 = g0.r14 ∧
      g'.r15 = g0.r15) hK hA hr
    (vc_131 (by rw [hs]; exact s8) (by rw [hs]; exact f8) hcl (by rw [q1]; exact g6) (by rw [q2]; exact g5)
      (by rw [q3]; exact g4) (by rw [q4]; exact g3) (by rw [q5]; exact g2) (by rw [q6]; exact g1)
      fun _ a1 a2 a3 a4 a5 a6 a7 _ => ⟨rfl, rfl, a1.trans q7, a2.trans (by rw [q1]; exact s6),
        a3.trans (by rw [q2]; exact s5), a4.trans (by rw [q3]; exact s4), a5.trans (by rw [q4]; exact s3),
        a6.trans (by rw [q5]; exact s2), a7.trans (by rw [q6]; exact s1)⟩) ?_
  rintro j' g fl V₁ ⟨rfl, hV₁, gs, gb, gp, g12, g13, g14, g15⟩ U t₁ hKU hAU hrU hgU -
  subst V₁ hgU
  refine c.s_ret hKU hAU hin (lt_len (by decide)) hrU (ret_161 _) (by rw [gs]; exact hl) hin₂ h₂
    (by rw [gs]; exact s7) ?_
  rintro Z' t₂ hKZ' hAZ' ⟨hrZ', hgZ'⟩
  refine k Z' t₂ hKZ' hAZ' hrZ' ?_ ?_
  · rw [hgZ']
    show U.cpu.gpr.rsp + 8 = _
    rw [gs]
  · rw [hgZ']
    exact ⟨gb, gp, g12, g13, g14, g15⟩

/-- `ReadStream (stream, data, size)` from its entry (`X`'s registers `g0`, `S` = `g0.rsp`), `fb` the `fs` base,
`m` = `0x80000000`: the pushes' slots, the guard's slot, the `call`'s return address slot and `*size` in what the
run may store into; the guard at `fs:0x28`, `processed` (`aR S + 4`), the vtable's slot (`stream`) and the return
address readable. The memory invariant `I`: of the bytes after the prologue (`hI0`), kept by a store of 8 bytes to
`*size` (`hIa`), giving the stack (`hIs`), the vtable's entry at 24 readable and equal to `eF` (`fv`, `htgt`). The
callee (`kf`, at `eF`, for `r` not 0 left and the data `p`, the bytes `W` with `I`): from its return the loop's
registers as they were, `I` and `processed` at most what was asked. At the return address (`kr`): `rsp` 8 above the
entry's, the callee-saved registers as they were. -/
theorem rst_ok {fb : Addr} {eF : Addr} {codeF : List Byte} {g0 : Gprs} {m : BitVec 64}
    {I : (Addr → Byte) → Prop}
    (c : Seg prof F Wl L s₀ o) (hfs : s₀.cpu.seg.fsBase = fb) (hin : CodeIn L rst_at rst)
    (hinF : CodeIn L eF codeF) (hF0 : 0 < codeF.length)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = rst_at) (hg0 : X.cpu.gpr = g0)
    (hm : m = 2147483648#64)
    (hcl : ∀ i < 8, Foot F.data (Addr.add (fb + 40#64) i))
    (hs1 : ∀ i < 8, Foot Wl (Addr.add (g0.rsp - 8) i)) (hs2 : ∀ i < 8, Foot Wl (Addr.add (g0.rsp - 8 - 8) i))
    (hs3 : ∀ i < 8, Foot Wl (Addr.add (g0.rsp - 8 - 8 - 8) i))
    (hs4 : ∀ i < 8, Foot Wl (Addr.add (g0.rsp - 8 - 8 - 8 - 8) i))
    (hs5 : ∀ i < 8, Foot Wl (Addr.add (g0.rsp - 8 - 8 - 8 - 8 - 8) i))
    (hs6 : ∀ i < 8, Foot Wl (Addr.add (g0.rsp - 8 - 8 - 8 - 8 - 8 - 8) i))
    (hw8 : ∀ i < 8, Foot Wl (Addr.add (aR g0.rsp + 8#64) i))
    (hr8 : ∀ i < 8, Foot Wl (Addr.add (aR g0.rsp - 8) i))
    (wz : ∀ i < 8, Foot Wl (Addr.add g0.rdx i))
    (f4 : ∀ i < 4, Foot F.data (Addr.add (aR g0.rsp + 4#64) i))
    (hl : ∀ i < 8, Foot F.data (Addr.add g0.rsp i))
    (fa : ∀ i < 8, Foot F.data (Addr.add g0.rdi i))
    (fv : ∀ W, I W → ∀ i < 8, Foot F.data (Addr.add (rdq(W, g0.rdi) + 24#64) i))
    (htgt : ∀ W, I W → rdq(W, rdq(W, g0.rdi) + 24#64) = eF)
    (hin₂ : CodeIn L e₂ code₂) (h₂ : j₂ < code₂.length)
    (hI0 : I (V0 fb V g0)) (hIa : ∀ W (bs : List Byte), bs.length = 8 → I W → I (Vst W g0.rdx bs))
    (hIs : ∀ W, I W → Stk fb W g0.rsp g0 (e₂.add j₂))
    (kf : ∀ (r p : BitVec 64) (W : Addr → Byte), r ≠ 0 → I W →
      KC prof F Wl L s₀ o gev gP gE g0.rsp eF W (Ar g0.rsp g0 m r p) (Lp g0.rsp g0 m r p)
        fun W' => I W' ∧ (rdd(W', aR g0.rsp + 4#64)).toNat ≤ (rq m r).toNat)
    (kr : ∀ (W' : Addr → Byte) (Z' : State) (t' : Nat), KeptW Wl s₀ Z' → Agree F Z'.proc.mm.mem W' →
      Z'.cpu.rip = e₂.add j₂ → Z'.cpu.gpr.rsp = g0.rsp + 8 → KS g0 Z'.cpu.gpr →
      GoG prof L o gev gP gE Z' t') :
    GoG prof L o gev gP gE X t := by
  subst hg0 hm
  have f8 : ∀ i < 8, Foot F.data (Addr.add (aR X.cpu.gpr.rsp + 8#64) i) := fun i hi => c.hws _ (hw8 i hi)
  have fz : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rdx i) := fun i hi => c.hws _ (wz i hi)
  have g1 : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rsp - 8) i) := fun i hi => c.hws _ (hs1 i hi)
  have g2 : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rsp - 8 - 8) i) := fun i hi => c.hws _ (hs2 i hi)
  have g3 : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rsp - 8 - 8 - 8) i) := fun i hi => c.hws _ (hs3 i hi)
  have g4 : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rsp - 8 - 8 - 8 - 8) i) := fun i hi => c.hws _ (hs4 i hi)
  have g5 : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rsp - 8 - 8 - 8 - 8 - 8) i) :=
    fun i hi => c.hws _ (hs5 i hi)
  have g6 : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rsp - 8 - 8 - 8 - 8 - 8 - 8) i) :=
    fun i hi => c.hws _ (hs6 i hi)
  -- from 131 and from 168
  have T131 : ∀ (Y : State) (W : Addr → Byte) (t' : Nat), KeptW Wl s₀ Y → Agree F Y.proc.mm.mem W →
      Y.cpu.rip = rst_at.add 131 → Y.cpu.gpr.rsp = aR X.cpu.gpr.rsp → I W →
      GoG prof L o gev gP gE Y t' := fun Y W t' hKY hAY hrY hsY hIW =>
    tail131 c hfs hin hKY hAY hrY hsY (hIs W hIW) hcl f8 g1 g2 g3 g4 g5 g6 hl hin₂ h₂
      fun Z' t'' a b d e f => kr W Z' t'' a b d e f
  have T168 : ∀ (Y : State) (W : Addr → Byte) (t' : Nat), KeptW Wl s₀ Y → Agree F Y.proc.mm.mem W →
      Y.cpu.rip = rst_at.add 168 → Y.cpu.gpr.rsp = aR X.cpu.gpr.rsp → I W →
      GoG prof L o gev gP gE Y t' := by
    intro Y W t' hKY hAY hrY hsY hIW
    refine (c_168 prof fb).run c hfs hin (fun j' g' _ V' => j' = 131 ∧ V' = W ∧ g'.rsp = Y.cpu.gpr.rsp)
      hKY hAY hrY (vc_168 fun _ a _ => ⟨rfl, rfl, a⟩) ?_
    rintro j' g fl V₁ ⟨rfl, hV₁, gs⟩ U t₁ hKU hAU hrU hgU -
    subst V₁ hgU
    exact T131 U W t₁ hKU hAU hrU (gs.trans hsY) hIW
  -- the loop, by induction on a bound of what is left
  have LP : ∀ (n : Nat) (Y : State) (W : Addr → Byte) (t' : Nat) (r p : BitVec 64), r.toNat < n → r ≠ 0 →
      KeptW Wl s₀ Y → Agree F Y.proc.mm.mem W → Y.cpu.rip = rst_at.add 89 →
      Lp X.cpu.gpr.rsp X.cpu.gpr 2147483648#64 r p Y.cpu.gpr → I W → GoG prof L o gev gP gE Y t' := by
    intro n
    induction n with
    | zero => intro Y W t' r p hn; exact absurd hn (Nat.not_lt_zero _)
    | succ n ih =>
      intro Y W t' r p hn hr0 hKY hAY hrY hLp hIW
      obtain ⟨ls, lb, lp, l12, l13, l14, l15⟩ := hLp
      -- `ls` rsp, `lb` rbx, `lp` r13, `l12` rbp, `l13` r12, `l14` r15, `l15` r14
      refine (c_89 prof fb).run c hfs hin (fun j' g' _ V' => j' = 111 ∧ V' = W ∧
          g'.rax = rdq(W, X.cpu.gpr.rdi) ∧ g'.rdx = rq 2147483648#64 r ∧ g'.rsi = p ∧
          g'.rcx = aR X.cpu.gpr.rsp + 4#64 ∧ g'.rdi = X.cpu.gpr.rdi ∧ g'.rsp = aR X.cpu.gpr.rsp ∧ g'.rbx = r ∧
          g'.rbp = 2147483648#64 ∧ g'.r12 = aR X.cpu.gpr.rsp + 4#64 ∧ g'.r13 = p ∧ g'.r14 = X.cpu.gpr.rdx ∧
          g'.r15 = X.cpu.gpr.rdi) hKY hAY hrY
        (vc_89 (by rw [l14]; exact fa) fun _ a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 _ =>
          ⟨rfl, rfl, by rw [a1, l14], by rw [a2, lb, l12], by rw [a3, lp], by rw [a4, l13], by rw [a5, l14],
            by rw [a6, ls], by rw [a7, lb], by rw [a8, l12], by rw [a9, l13], by rw [a10, lp], by rw [a11, l15],
            by rw [a12, l14]⟩) ?_
      rintro j' g fl V₁ ⟨rfl, hV₁, ga, gd, gsi, gc, gdi, gs, gb, gp, g12, g13, g14, g15⟩ U t₁ hKU hAU hrU
        hgU -
      subst V₁ hgU
      have he : eaD U 0 24 = rdq(W, X.cpu.gpr.rdi) + 24#64 := by
        show U.cpu.gpr.get (regOf 0) + BitVec.ofNat 64 24 = _
        rw [show U.cpu.gpr.get (regOf 0) = U.cpu.gpr.rax from rfl, ga]
      have hU : U.cpu.gpr.rsp - 8 = aR X.cpu.gpr.rsp - 8 := by rw [gs]
      refine c.s_callM hKU hAU hin (lt_len (by decide)) hrU (call_111 _) (by rw [he]; exact fv W hIW) hinF
        hF0 (by rw [he]; exact htgt W hIW) (by rw [hU]; exact hr8) ?_
      rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
      rw [hU] at hA₂
      refine kf r p W hr0 hIW Y₂ t₂ hK₂ hA₂ hr₂ (by rw [hg₂]; exact hU)
        (by rw [hg₂]; exact ⟨gb, g13, gp, g12, g15, g14, gdi, gsi, gd, gc⟩) ?_
      -- back from the callee, at 114
      intro Z W' t₃ hKZ hAZ hrZ hLZ hN
      obtain ⟨hIW', hle⟩ := hN
      obtain ⟨zs, zb, zp, z12, z13, z14, z15⟩ := hLZ
      refine (c_114 prof fb).run c hfs hin (fun j' g' _ V' => j' = 118 ∧ V' = W' ∧
          g'.rdx = BitVec.setWidth 64 rdd(W', Z.cpu.gpr.rsp + 4#64) ∧ g'.rsp = Z.cpu.gpr.rsp ∧
          g'.rbx = Z.cpu.gpr.rbx ∧ g'.rbp = Z.cpu.gpr.rbp ∧ g'.r12 = Z.cpu.gpr.r12 ∧ g'.r13 = Z.cpu.gpr.r13 ∧
          g'.r14 = Z.cpu.gpr.r14 ∧ g'.r15 = Z.cpu.gpr.r15) hKZ hAZ hrZ
        (vc_114 (by rw [zs]; exact f4) fun _ a1 a2 a3 a4 a5 a6 a7 a8 _ _ =>
          ⟨rfl, rfl, a1, a2, a3, a4, a5, a6, a7, a8⟩) ?_
      rintro j' g fl V₁ ⟨rfl, hV₁, ud, us, ub, up, u12, u13, u14, u15⟩ U₁ t₄ hKU₁ hAU₁ hrU₁ hgU₁ -
      subst V₁ hgU₁
      rw [zs] at ud
      -- `*size += v` (118)
      have he' : eaD U₁ 14 0 = X.cpu.gpr.rdx := by
        show U₁.cpu.gpr.get (regOf 14) + BitVec.ofNat 64 0 = _
        rw [show U₁.cpu.gpr.get (regOf 14) = U₁.cpu.gpr.r14 from rfl, u14, z15]
        exact BitVec.add_zero _
      refine c.s_add_mr64 hKU₁ hAU₁ hin (lt_len (by decide)) hrU₁ (add_118 _) (by rw [he']; exact wz) ?_
      rw [he']
      suffices KK : ∀ bs : List Byte, bs.length = 8 → ContG prof F Wl L s₀ o gev gP gE (Vst W' X.cpu.gpr.rdx bs)
          (fun Y => Y.cpu.rip = rst_at.add (118 + 3) ∧ Y.cpu.gpr = U₁.cpu.gpr) from
        KK _ (toBytesLE_length ..)
      intro bs6 hl6
      rintro Y₆ t₅ hK₆ hA₆ ⟨hr₆, hg₆⟩
      have hI6 := hIa W' bs6 hl6 hIW'
      have y_s : Y₆.cpu.gpr.rsp = aR X.cpu.gpr.rsp := by rw [hg₆]; exact us.trans zs
      have y_b : Y₆.cpu.gpr.rbx = r := by rw [hg₆]; exact ub.trans zb
      have y_d : Y₆.cpu.gpr.rdx = BitVec.setWidth 64 rdd(W', aR X.cpu.gpr.rsp + 4#64) := by rw [hg₆]; exact ud
      by_cases ha : BitVec.setWidth 32 Y₆.cpu.gpr.rax = 0
      · by_cases hv0 : rdd(W', aR X.cpu.gpr.rsp + 4#64) = 0
        · -- nothing read: to 131
          have hv : (BitVec.setWidth 32 Y₆.cpu.gpr.rdx == 0) = true := by
            rw [y_d, sw_64_32]; exact beq_iff_eq.2 hv0
          refine (c_121 prof fb).run c hfs hin (fun j' g' _ V' => j' = 131 ∧ V' = Vst W' X.cpu.gpr.rdx bs6 ∧
              g'.rsp = Y₆.cpu.gpr.rsp) hK₆ hA₆ hr₆
            (vc_121s (beq_iff_eq.2 ha) hv fun _ a _ => ⟨rfl, rfl, a⟩) ?_
          rintro j' g fl V₁ ⟨rfl, hV₁, gs'⟩ U₂ t₆ hKU₂ hAU₂ hrU₂ hgU₂ -
          subst V₁ hgU₂
          exact T131 U₂ _ t₆ hKU₂ hAU₂ hrU₂ (gs'.trans y_s) hI6
        · have hv : (BitVec.setWidth 32 Y₆.cpu.gpr.rdx == 0) = false := by
            rw [y_d, sw_64_32]; exact beq_eq_false_iff_ne.2 hv0
          by_cases hz : Y₆.cpu.gpr.rbx - Y₆.cpu.gpr.rdx = 0
          · -- all read: to 168
            refine (c_121 prof fb).run c hfs hin (fun j' g' _ V' => j' = 168 ∧ V' = Vst W' X.cpu.gpr.rdx bs6 ∧
                g'.rsp = Y₆.cpu.gpr.rsp) hK₆ hA₆ hr₆
              (vc_121z (beq_iff_eq.2 ha) hv (beq_iff_eq.2 hz) fun _ a _ => ⟨rfl, rfl, a⟩) ?_
            rintro j' g fl V₁ ⟨rfl, hV₁, gs'⟩ U₂ t₆ hKU₂ hAU₂ hrU₂ hgU₂ -
            subst V₁ hgU₂
            exact T168 U₂ _ t₆ hKU₂ hAU₂ hrU₂ (gs'.trans y_s) hI6
          · -- something left: round again
            refine (c_121 prof fb).run c hfs hin (fun j' g' _ V' => j' = 89 ∧ V' = Vst W' X.cpu.gpr.rdx bs6 ∧
                g'.rsp = Y₆.cpu.gpr.rsp ∧ g'.rbx = Y₆.cpu.gpr.rbx - Y₆.cpu.gpr.rdx ∧
                g'.r13 = Y₆.cpu.gpr.r13 + Y₆.cpu.gpr.rdx ∧ g'.rbp = Y₆.cpu.gpr.rbp ∧
                g'.r12 = Y₆.cpu.gpr.r12 ∧ g'.r14 = Y₆.cpu.gpr.r14 ∧ g'.r15 = Y₆.cpu.gpr.r15) hK₆ hA₆ hr₆
              (vc_121c (beq_iff_eq.2 ha) hv (beq_eq_false_iff_ne.2 hz)
                fun _ a b d e f g h _ => ⟨rfl, rfl, a, b, d, e, f, g, h⟩) ?_
            rintro j' g fl V₁ ⟨rfl, hV₁, gs', gb', gp', g12', g13', g14', g15'⟩ U₂ t₆ hKU₂ hAU₂ hrU₂
              hgU₂ -
            subst V₁ hgU₂
            rw [y_b, y_d] at gb' hz
            rw [y_d] at gp'
            have hx := sw_toNat rdd(W', aR X.cpu.gpr.rsp + 4#64)
            have hlt : (r - BitVec.setWidth 64 rdd(W', aR X.cpu.gpr.rsp + 4#64)).toNat < n :=
              sub_dec (by rw [hx]; exact pos_of_ne hv0)
                (by rw [hx]; exact Nat.le_trans hle (rq_le _ r)) hn
            have y_p : Y₆.cpu.gpr.r13 = p := by rw [hg₆]; exact u13.trans zp
            rw [y_p] at gp'
            exact ih U₂ _ t₆ (r - BitVec.setWidth 64 rdd(W', aR X.cpu.gpr.rsp + 4#64))
              (p + BitVec.setWidth 64 rdd(W', aR X.cpu.gpr.rsp + 4#64)) hlt hz hKU₂ hAU₂ hrU₂
              ⟨gs'.trans y_s, gb', gp', g12'.trans (by rw [hg₆]; exact up.trans z12),
                g13'.trans (by rw [hg₆]; exact u12.trans z13), g15'.trans (by rw [hg₆]; exact u15.trans z14),
                g14'.trans (by rw [hg₆]; exact u14.trans z15)⟩ hI6
      · -- the callee's error: to 131
        refine (c_121 prof fb).run c hfs hin (fun j' g' _ V' => j' = 131 ∧ V' = Vst W' X.cpu.gpr.rdx bs6 ∧
            g'.rsp = Y₆.cpu.gpr.rsp) hK₆ hA₆ hr₆
          (vc_121a (beq_eq_false_iff_ne.2 ha) fun _ a _ => ⟨rfl, rfl, a⟩) ?_
        rintro j' g fl V₁ ⟨rfl, hV₁, gs'⟩ U₂ t₆ hKU₂ hAU₂ hrU₂ hgU₂ -
        subst V₁ hgU₂
        exact T131 U₂ _ t₆ hKU₂ hAU₂ hrU₂ (gs'.trans y_s) hI6
  -- the entry
  have hrip' : X.cpu.rip = rst_at.add 0 := by rw [addr_add_zero]; exact hrip
  refine (c_0 prof fb).run c hfs hin (fun j' g' _ V' => V' = V0 fb V X.cpu.gpr ∧
      g'.rsp = aR X.cpu.gpr.rsp ∧
      ((rdq(V1 V X.cpu.gpr, X.cpu.gpr.rdx) = 0 ∧ j' = 168) ∨
        (rdq(V1 V X.cpu.gpr, X.cpu.gpr.rdx) ≠ 0 ∧ j' = 89 ∧ g'.rbx = rdq(V1 V X.cpu.gpr, X.cpu.gpr.rdx) ∧
          g'.r13 = X.cpu.gpr.rsi ∧ g'.rbp = 2147483648#64 ∧ g'.r12 = aR X.cpu.gpr.rsp + 4#64 ∧
          g'.r15 = X.cpu.gpr.rdi ∧ g'.r14 = X.cpu.gpr.rdx))) hK hA hrip'
    (vc_0 rfl hs1 hs2 hs3 hs4 hs5 hs6 hcl hw8 fz wz (fun hz _ a _ => ⟨rfl, a, Or.inl ⟨hz, rfl⟩⟩)
      (fun hn _ a b d e f g h _ => ⟨rfl, a, Or.inr ⟨hn, rfl, b, d, e, f, g, h⟩⟩)) ?_
  rintro j' g fl V₁ ⟨hV₁, gs, hpost⟩ Y t₁ hKY hAY hrY hgY -
  subst V₁ hgY
  rcases hpost with ⟨hz, rfl⟩ | ⟨hn, rfl, gb, gp, g12, g13, g15, g14⟩
  · exact T168 Y _ t₁ hKY hAY hrY gs hI0
  · exact LP ((rdq(V1 V X.cpu.gpr, X.cpu.gpr.rdx)).toNat + 1) Y _ t₁ _ _ (Nat.lt_succ_self _) hn hKY hAY hrY
      ⟨gs, gb, gp, g12, g13, g15, g14⟩ hI0

end FV7z.Rst
