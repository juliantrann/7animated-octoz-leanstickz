import FV7z.Wst.Cuts
import FV7z.Lemmas.LeafRet
import FV7z.Lemmas.CallM
/-!
# `WriteStream` (PLAN.md §M, M1)

7-Zip 26.06's `WriteStream (stream, data, size)` at `0x463420` in `7zzs` (`CPP/7zip/Common/StreamUtils.cpp`;
`objdump -d`), `stream` in `rdi`, `data` in `rsi`, `size` in `rdx`, `S` the stack pointer at the entry:
`push r14; push r13; push r12; push rbp; push rbx; sub rsp, 0x10` (`aR S`), the stack guard (`fs:0x28`) stored at
`aR S + 8`, `eax` = 0; `size` 0 to 144. Else (37) `r14` = `stream`, `rbp` = `data`, `rbx` = `size` (what is left,
`r`), `r12` = `0x80000000` (`m`), `r13` = `aR S + 4`, and the loop (73): `rax` = the vtable, `rdx` = `r` capped
at `m` (`cmp rbx, r12; cmovb rdx, rbx`: `rq`), `rcx` = `aR S + 4`, `call qword [rax + 0x18]` (95, `Seg.s_callM`:
`stream->Write (data, cur, &processed)`). Back (98): `edx` = `processed` (`v`), `rbp += v`, `rbx -= v`; the
callee's `eax` not 0 to 112; `v` 0: `eax` = `E_FAIL` (152) to 112; `rbx` 0 to 144 (`eax` = 0); else 73. At 112 the
guard checked, `add rsp, 0x10; pop rbx; pop rbp; pop r12; pop r13; pop r14; ret` (140).

The memory is the caller's invariant `I` (as `I` in `FV7z/Ocv/Holds.lean`): it holds of the bytes after the
prologue (`hI0`), gives the stack (`hIs`: `Stk`, the saved registers, the return address and the guard equal to the
one at `fs:0x28`), the vtable's entry at 24 readable and equal to the callee's entry `eF` (`fv`, `htgt`), and the
callee keeps it (`kf`, `KC`: from its return the registers of the loop as they were, `I` and `v` at most what was
asked). As `v` is not 0 and at most `rq m r` ≤ `r`, `r` goes down: the loop is by induction on it. Not covered:
`__stack_chk_fail` (159).

- `aR`, `Stk`, `V1`, `V0c`, `V0`, `rq`, `Lp`, `Ar`, `KS`, `KC`: the frame, registers, bytes, contracts.
- `vc_0`, `vc_73`, `vc_98a`, `vc_98f`, `vc_98z`, `vc_98c`, `vc_112`, `vc_144`: the pieces' verification conditions.
- `tail112`: the run from 112; `wst_ok`: the function.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Wst
set_option linter.unusedVariables false

/-! ## The instructions outside the blocks -/

/-- The `call` through the vtable. -/
def pcm : List Byte := [0xff, 0x50, 0x18]
theorem pcm_0 : ∀ feat, Dec feat pcm 0 (FV7z.mk .call 64 [.mem (mbd 0 24 64)] 3) := by dec_rfl
theorem wc_95 : pcm <+: wst.drop 95 := by decide +kernel
theorem call_95 (feat : Features) : Dec feat wst 95 (FV7z.mk .call 64 [.mem (mbd 0 24 64)] 3) :=
  Dec.shift (j := 95) (k := 0) (pcm_0 feat) wc_95 (Nat.zero_le _)

/-- The `ret`. -/
def pret : List Byte := [0xc3]
theorem pret_0 : ∀ feat, Dec feat pret 0 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem w_140 : pret <+: wst.drop 140 := by decide +kernel
theorem ret_140 (feat : Features) : Dec feat wst 140 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 140) (k := 0) (pret_0 feat) w_140 (Nat.zero_le _)

/-! ## The frame -/

/-- The stack pointer after the five pushes and `sub rsp, 0x10`. -/
abbrev aR (S : Addr) : Addr := S - 8 - 8 - 8 - 8 - 8 - 16#64

theorem e16 (S : Addr) : aR S + 16#64 = S - 8 - 8 - 8 - 8 - 8 := BitVec.sub_add_cancel _ _
theorem sa8 (x : Addr) : x - 8 + 8 = x := BitVec.sub_add_cancel _ _

/-- The stack (`fb` the `fs` base, `g0` the registers at the entry, `ra` the return address): the saved `r14`,
`r13`, `r12`, `rbp`, `rbx`, the return address, the stack guard as at `fs:0x28`. -/
abbrev Stk (fb : Addr) (W : Addr → Byte) (S : Addr) (g0 : Gprs) (ra : Addr) : Prop :=
  rdq(W, S - 8) = g0.r14 ∧ rdq(W, S - 8 - 8) = g0.r13 ∧ rdq(W, S - 8 - 8 - 8) = g0.r12 ∧
    rdq(W, S - 8 - 8 - 8 - 8) = g0.rbp ∧ rdq(W, S - 8 - 8 - 8 - 8 - 8) = g0.rbx ∧ rdq(W, S) = ra ∧
    rdq(W, aR S + 8#64) = rdq(W, fb + 40#64)

/-- The bytes after the pushes. -/
abbrev V1 (V : Addr → Byte) (g : Gprs) : Addr → Byte :=
  Vst (Vst (Vst (Vst (Vst V (g.rsp - 8) (toBytesLE g.r14 8)) (g.rsp - 8 - 8) (toBytesLE g.r13 8))
    (g.rsp - 8 - 8 - 8) (toBytesLE g.r12 8)) (g.rsp - 8 - 8 - 8 - 8) (toBytesLE g.rbp 8))
    (g.rsp - 8 - 8 - 8 - 8 - 8) (toBytesLE g.rbx 8)

/-- The bytes after the prologue, the guard's value `cn`. -/
abbrev V0c (V : Addr → Byte) (g : Gprs) (cn : BitVec 64) : Addr → Byte :=
  Vst (V1 V g) (aR g.rsp + 8#64) (toBytesLE cn 8)

/-- `V0c` with the guard read from `fs:0x28`. -/
abbrev V0 (fb : Addr) (V : Addr → Byte) (g : Gprs) : Addr → Byte := V0c V g rdq(V1 V g, fb + 40#64)

/-- What is asked of the callee: what is left, `r`, capped at `m` (`cmp rbx, r12; cmovb rdx, rbx`). -/
def rq (m r : BitVec 64) : BitVec 64 := if r.toNat < m.toNat then r else m

theorem rq_le (m r : BitVec 64) : (rq m r).toNat ≤ r.toNat := by
  unfold rq; split <;> omega

theorem sw_toNat (v : BitVec 32) : (BitVec.setWidth 64 v).toNat = v.toNat := by bv_omega

theorem sub_dec {r x : BitVec 64} {n : Nat} (h0 : 0 < x.toNat) (hle : x.toNat ≤ r.toNat) (hn : r.toNat < n + 1) :
    (r - x).toNat < n := by bv_omega

theorem pos_of_ne {v : BitVec 32} (h : ¬ v = 0) : 0 < v.toNat :=
  Nat.pos_of_ne_zero fun e => h (BitVec.eq_of_toNat_eq (e.trans rfl))

/-- The loop's registers (`S` the entry's `rsp`, `g0` the entry's registers): `rbx` = what is left `r`, `rbp` =
the data `p`, `r12` = the cap `m`, `r13` = `aR S + 4`, `r14` = `stream`. -/
abbrev Lp (S : Addr) (g0 : Gprs) (m r p : BitVec 64) (g : Gprs) : Prop :=
  g.rsp = aR S ∧ g.rbx = r ∧ g.rbp = p ∧ g.r12 = m ∧ g.r13 = aR S + 4#64 ∧ g.r14 = g0.rdi ∧ g.r15 = g0.r15

/-- What the callee is given: `Lp` but `rsp`, `rdi` = `stream`, `rsi` = `p`, `rdx` = `rq m r`, `rcx` =
`aR S + 4`. -/
abbrev Ar (S : Addr) (g0 : Gprs) (m r p : BitVec 64) (g : Gprs) : Prop :=
  g.rbx = r ∧ g.rbp = p ∧ g.r12 = m ∧ g.r13 = aR S + 4#64 ∧ g.r14 = g0.rdi ∧ g.r15 = g0.r15 ∧
    g.rdi = g0.rdi ∧ g.rsi = p ∧ g.rdx = rq m r ∧ g.rcx = aR S + 4#64

/-- The callee-saved registers as at the entry. -/
abbrev KS (g0 g : Gprs) : Prop :=
  g.rbx = g0.rbx ∧ g.rbp = g0.rbp ∧ g.r12 = g0.r12 ∧ g.r13 = g0.r13 ∧ g.r14 = g0.r14 ∧ g.r15 = g0.r15

/-- The callee from the `call` at 95 (entry `ent`, the bytes `W`, the registers `A`): at its entry, and from its
return at 98 with `B` and `N`, the run goes on to the goal. -/
def KC (prof : Profile) (F : Footprint) (Wl : List Rgn) (L : List (Addr × List Byte)) (s₀ : State) (o : Oracle)
    (gev : List Event) (gP : State → Nat → List Event → Prop) (gE : Outcome → List Event → Prop)
    (S ent : Addr) (W : Addr → Byte) (A B : Gprs → Prop) (N : (Addr → Byte) → Prop) : Prop :=
  ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y →
    Agree F Y.proc.mm.mem (Vst W (aR S - 8) (toBytesLE (wst_at.add 98) 8)) →
    Y.cpu.rip = ent → Y.cpu.gpr.rsp = aR S - 8 → A Y.cpu.gpr →
    (∀ (Z : State) (W' : Addr → Byte) (t'' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem W' →
      Z.cpu.rip = wst_at.add 98 → B Z.cpu.gpr → N W' → GoG prof L o gev gP gE Z t'') →
    GoG prof L o gev gP gE Y t'

/-! ## The pieces -/

variable {F : Footprint} {Wl : List Rgn}

/-- The prologue (the guard's value named `cn`), `test rdx, rdx`: `size` 0 to 144, else the loop's registers set
(37) and 73. -/
theorem vc_0 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} {cn : BitVec 64}
    (hcn : rdq(V1 V g, fb + 40#64) = cn)
    (hs1 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8) i)) (hs2 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8) i))
    (hs3 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8 - 8) i))
    (hs4 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8 - 8 - 8) i))
    (hs5 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8 - 8 - 8 - 8) i))
    (hcl : ∀ i < 8, Foot F.data (Addr.add (fb + 40#64) i))
    (hw8 : ∀ i < 8, Foot Wl (Addr.add (aR g.rsp + 8#64) i))
    (h144 : g.rdx = 0 → ∀ g', g'.rsp = aR g.rsp → g'.r15 = g.r15 → ∀ fl, Q 144 g' fl (V0c V g cn))
    (h73 : g.rdx ≠ 0 → ∀ g', g'.rsp = aR g.rsp → g'.rbx = g.rdx → g'.rbp = g.rsi →
      g'.r12 = 2147483648#64 → g'.r13 = aR g.rsp + 4#64 → g'.r14 = g.rdi → g'.r15 = g.r15 →
      ∀ fl, Q 73 g' fl (V0c V g cn)) :
    W_0 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [aR, V1, V0c] at hcn hs1 hs2 hs3 hs4 hs5 hw8 h144 h73 ⊢
  by_cases h0 : rdx = 0
  · have hb : (rdx == 0) = true := beq_iff_eq.2 h0
    have h := h144 h0
    wpx [W_0, W_37, o0, o1, Op.ldf, hcn, hb, BitVec.and_self, BitVec.xor_self, BitVec.reduceSetWidth,
      Bool.false_eq_true, Bool.true_eq_false, false_implies, implies_true]
    all_goals repeat' (first
      | refine h _ ?_ ?_ _
      | with_reducible rfl
      | with_reducible exact hs1
      | with_reducible exact hs2
      | with_reducible exact hs3
      | with_reducible exact hs4
      | with_reducible exact hs5
      | with_reducible exact hcl
      | with_reducible exact hw8
      | apply And.intro
      | intro _)
  · have hb : (rdx == 0) = false := beq_eq_false_iff_ne.2 h0
    have h := h73 h0
    wpx [W_0, W_37, o0, o1, Op.ldf, hcn, hb, BitVec.and_self, BitVec.xor_self, BitVec.reduceSetWidth,
      Bool.false_eq_true, Bool.true_eq_false, false_implies, implies_true]
    all_goals repeat' (first
      | refine h _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ _
      | with_reducible rfl
      | with_reducible exact hs1
      | with_reducible exact hs2
      | with_reducible exact hs3
      | with_reducible exact hs4
      | with_reducible exact hs5
      | with_reducible exact hcl
      | with_reducible exact hw8
      | apply And.intro
      | intro _)

/-- The loop's head: `rax` = the vtable, `rdx` = `rq r12 rbx`, `rsi` = `rbp`, `rcx` = `r13`, `rdi` = `r14`, to the
`call` (95). -/
theorem vc_73 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (fa : ∀ i < 8, Foot F.data (Addr.add g.r14 i))
    (h : ∀ g', g'.rax = rdq(V, g.r14) → g'.rdx = rq g.r12 g.rbx → g'.rsi = g.rbp → g'.rcx = g.r13 →
      g'.rdi = g.r14 → g'.rsp = g.rsp → g'.rbx = g.rbx → g'.rbp = g.rbp → g'.r12 = g.r12 → g'.r13 = g.r13 →
      g'.r14 = g.r14 → g'.r15 = g.r15 → ∀ fl, Q 95 g' fl V) :
    W_73 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at fa h ⊢
  by_cases hc : rbx.toNat < r12.toNat
  · have hd : decide (rbx.toNat < r12.toNat) = true := decide_eq_true hc
    rw [show rq r12 rbx = rbx from if_pos hc] at h
    wpx [W_73, o4, hd, eq_self_iff_true, ↓reduceIte]
    all_goals repeat' (first
      | refine h _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ _
      | with_reducible rfl
      | with_reducible exact fa
      | apply And.intro
      | intro _)
  · have hd : decide (rbx.toNat < r12.toNat) = false := decide_eq_false hc
    rw [show rq r12 rbx = r12 from if_neg hc] at h
    wpx [W_73, o4, hd, Bool.false_eq_true, ↓reduceIte]
    all_goals repeat' (first
      | refine h _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ _
      | with_reducible rfl
      | with_reducible exact fa
      | apply And.intro
      | intro _)

/-- Back from the callee (`v` = `[rsp + 4]`), its `eax` not 0: to 112. -/
theorem vc_98a {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (ha : (BitVec.setWidth 32 g.rax == 0) = false) (f4 : ∀ i < 4, Foot F.data (Addr.add (g.rsp + 4#64) i))
    (h : ∀ g', g'.rsp = g.rsp → g'.r15 = g.r15 → ∀ fl, Q 112 g' fl V) :
    W_98 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at ha f4 h ⊢
  wpx [W_98, o5, ha, BitVec.and_self, Bool.false_eq_true, Bool.true_eq_false, false_implies, eq_self_iff_true,
    implies_true]
  all_goals repeat' (first
    | refine h _ ?_ ?_ _
    | with_reducible rfl
    | with_reducible exact f4
    | apply And.intro
    | intro _)

/-- `eax` 0 and `v` 0: `eax` = `E_FAIL` (152), to 112. -/
theorem vc_98f {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (ha : (BitVec.setWidth 32 g.rax == 0) = true) (hv : (rdd(V, g.rsp + 4#64) == 0) = true)
    (f4 : ∀ i < 4, Foot F.data (Addr.add (g.rsp + 4#64) i))
    (h : ∀ g', g'.rsp = g.rsp → g'.r15 = g.r15 → ∀ fl, Q 112 g' fl V) :
    W_98 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at ha hv f4 h ⊢
  wpx [W_98, W_64, W_152, o5, o2, o9, ha, hv, BitVec.and_self, Bool.false_eq_true, Bool.true_eq_false,
    false_implies, eq_self_iff_true, implies_true]
  all_goals repeat' (first
    | refine h _ ?_ ?_ _
    | with_reducible rfl
    | with_reducible exact f4
    | apply And.intro
    | intro _)

/-- `eax` 0, `v` not 0 and nothing left: to 144. -/
theorem vc_98z {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (ha : (BitVec.setWidth 32 g.rax == 0) = true) (hv : (rdd(V, g.rsp + 4#64) == 0) = false)
    (hr : (g.rbx - BitVec.setWidth 64 rdd(V, g.rsp + 4#64) == 0) = true)
    (f4 : ∀ i < 4, Foot F.data (Addr.add (g.rsp + 4#64) i))
    (h : ∀ g', g'.rsp = g.rsp → g'.r15 = g.r15 → ∀ fl, Q 144 g' fl V) :
    W_98 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at ha hv hr f4 h ⊢
  wpx [W_98, W_64, W_68, o5, o2, o3, ha, hv, hr, BitVec.and_self, Bool.false_eq_true, Bool.true_eq_false,
    false_implies, eq_self_iff_true, implies_true]
  all_goals repeat' (first
    | refine h _ ?_ ?_ _
    | with_reducible rfl
    | with_reducible exact f4
    | apply And.intro
    | intro _)

/-- `eax` 0, `v` not 0 and something left: `rbx -= v`, `rbp += v`, to 73. -/
theorem vc_98c {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (ha : (BitVec.setWidth 32 g.rax == 0) = true) (hv : (rdd(V, g.rsp + 4#64) == 0) = false)
    (hr : (g.rbx - BitVec.setWidth 64 rdd(V, g.rsp + 4#64) == 0) = false)
    (f4 : ∀ i < 4, Foot F.data (Addr.add (g.rsp + 4#64) i))
    (h : ∀ g', g'.rsp = g.rsp → g'.rbx = g.rbx - BitVec.setWidth 64 rdd(V, g.rsp + 4#64) →
      g'.rbp = g.rbp + BitVec.setWidth 64 rdd(V, g.rsp + 4#64) → g'.r12 = g.r12 → g'.r13 = g.r13 →
      g'.r14 = g.r14 → g'.r15 = g.r15 → ∀ fl, Q 73 g' fl V) :
    W_98 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at ha hv hr f4 h ⊢
  wpx [W_98, W_64, W_68, o5, o2, o3, ha, hv, hr, BitVec.and_self, Bool.false_eq_true, Bool.true_eq_false,
    false_implies, eq_self_iff_true, implies_true]
  all_goals repeat' (first
    | refine h _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ _
    | with_reducible rfl
    | with_reducible exact f4
    | apply And.intro
    | intro _)

/-- The stack guard checked (as at `fs:0x28`: `jne` not taken), `add rsp, 0x10` and the five pops to the `ret`. -/
theorem vc_112 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (hc : rdq(V, g.rsp + 8#64) = rdq(V, fb + 40#64)) (f8 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8#64) i))
    (fcl : ∀ i < 8, Foot F.data (Addr.add (fb + 40#64) i))
    (p1 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 16#64) i))
    (p2 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 16#64 + 8) i))
    (p3 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 16#64 + 8 + 8) i))
    (p4 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 16#64 + 8 + 8 + 8) i))
    (p5 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 16#64 + 8 + 8 + 8 + 8) i))
    (h : ∀ g', g'.rsp = g.rsp + 16#64 + 8 + 8 + 8 + 8 + 8 → g'.rbx = rdq(V, g.rsp + 16#64) →
      g'.rbp = rdq(V, g.rsp + 16#64 + 8) → g'.r12 = rdq(V, g.rsp + 16#64 + 8 + 8) →
      g'.r13 = rdq(V, g.rsp + 16#64 + 8 + 8 + 8) → g'.r14 = rdq(V, g.rsp + 16#64 + 8 + 8 + 8 + 8) →
      g'.r15 = g.r15 → ∀ fl, Q 140 g' fl V) :
    W_112 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hc f8 p1 p2 p3 p4 p5 h ⊢
  have z0 : ((0#64 : BitVec 64) == 0) = true := by decide
  wpx [W_112, W_128, o6, o7, Op.xormf, hc, BitVec.xor_self, z0, decide_true, Bool.not_true, Bool.false_eq_true,
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
    | apply And.intro
    | intro _)

/-- `xor eax, eax`, to 112. -/
theorem vc_144 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (h : ∀ g', g'.rsp = g.rsp → g'.r15 = g.r15 → ∀ fl, Q 112 g' fl V) :
    W_144 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h ⊢
  wpx [W_144, o8]
  all_goals repeat' (first
    | refine h _ ?_ ?_ _
    | with_reducible rfl
    | apply And.intro
    | intro _)

/-! ## The runs -/

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {X : State} {t : Nat} {V : Addr → Byte} {e₂ : Addr} {code₂ : List Byte} {j₂ : Nat}

/-- From 112 (`rsp` = `aR S`, `r15` as at the entry, the stack `Stk`) to the return address `e₂.add j₂`. -/
theorem tail112 {fb : Addr} {W : Addr → Byte} {S : Addr} {g0 : Gprs} {Y : State} (c : Seg prof F Wl L s₀ o)
    (hfs : s₀.cpu.seg.fsBase = fb) (hin : CodeIn L wst_at wst) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = wst_at.add 112) (hs : Y.cpu.gpr.rsp = aR S)
    (h15 : Y.cpu.gpr.r15 = g0.r15) (hst : Stk fb W S g0 (e₂.add j₂))
    (hcl : ∀ i < 8, Foot F.data (Addr.add (fb + 40#64) i)) (f8 : ∀ i < 8, Foot F.data (Addr.add (aR S + 8#64) i))
    (g1 : ∀ i < 8, Foot F.data (Addr.add (S - 8) i)) (g2 : ∀ i < 8, Foot F.data (Addr.add (S - 8 - 8) i))
    (g3 : ∀ i < 8, Foot F.data (Addr.add (S - 8 - 8 - 8) i))
    (g4 : ∀ i < 8, Foot F.data (Addr.add (S - 8 - 8 - 8 - 8) i))
    (g5 : ∀ i < 8, Foot F.data (Addr.add (S - 8 - 8 - 8 - 8 - 8) i))
    (hl : ∀ i < 8, Foot F.data (Addr.add S i)) (hin₂ : CodeIn L e₂ code₂) (h₂ : j₂ < code₂.length)
    (k : ∀ (Z' : State) (t' : Nat), KeptW Wl s₀ Z' → Agree F Z'.proc.mm.mem W → Z'.cpu.rip = e₂.add j₂ →
      Z'.cpu.gpr.rsp = S + 8 → KS g0 Z'.cpu.gpr → GoG prof L o gev gP gE Z' t') :
    GoG prof L o gev gP gE Y t := by
  obtain ⟨s1, s2, s3, s4, s5, s6, s7⟩ := hst
  have q1 : Y.cpu.gpr.rsp + 16#64 = S - 8 - 8 - 8 - 8 - 8 := by rw [hs, e16]
  have q2 : Y.cpu.gpr.rsp + 16#64 + 8 = S - 8 - 8 - 8 - 8 := by rw [q1, sa8]
  have q3 : Y.cpu.gpr.rsp + 16#64 + 8 + 8 = S - 8 - 8 - 8 := by rw [q2, sa8]
  have q4 : Y.cpu.gpr.rsp + 16#64 + 8 + 8 + 8 = S - 8 - 8 := by rw [q3, sa8]
  have q5 : Y.cpu.gpr.rsp + 16#64 + 8 + 8 + 8 + 8 = S - 8 := by rw [q4, sa8]
  have q6 : Y.cpu.gpr.rsp + 16#64 + 8 + 8 + 8 + 8 + 8 = S := by rw [q5, sa8]
  refine (c_112 prof fb).run c hfs hin (fun j' g' _ V' => j' = 140 ∧ V' = W ∧ g'.rsp = S ∧
      g'.rbx = g0.rbx ∧ g'.rbp = g0.rbp ∧ g'.r12 = g0.r12 ∧ g'.r13 = g0.r13 ∧ g'.r14 = g0.r14 ∧
      g'.r15 = g0.r15) hK hA hr
    (vc_112 (by rw [hs]; exact s7) (by rw [hs]; exact f8) hcl (by rw [q1]; exact g5) (by rw [q2]; exact g4)
      (by rw [q3]; exact g3) (by rw [q4]; exact g2) (by rw [q5]; exact g1)
      fun _ a1 a2 a3 a4 a5 a6 a7 _ => ⟨rfl, rfl, a1.trans q6, a2.trans (by rw [q1]; exact s5),
        a3.trans (by rw [q2]; exact s4), a4.trans (by rw [q3]; exact s3), a5.trans (by rw [q4]; exact s2),
        a6.trans (by rw [q5]; exact s1), a7.trans h15⟩) ?_
  rintro j' g fl V₁ ⟨rfl, hV₁, gs, gb, gp, g12, g13, g14, g15⟩ U t₁ hKU hAU hrU hgU -
  subst V₁ hgU
  refine c.s_ret hKU hAU hin (lt_len (by decide)) hrU (ret_140 _) (by rw [gs]; exact hl) hin₂ h₂
    (by rw [gs]; exact s6) ?_
  rintro Z' t₂ hKZ' hAZ' ⟨hrZ', hgZ'⟩
  refine k Z' t₂ hKZ' hAZ' hrZ' ?_ ?_
  · rw [hgZ']
    show U.cpu.gpr.rsp + 8 = _
    rw [gs]
  · rw [hgZ']
    exact ⟨gb, gp, g12, g13, g14, g15⟩

/-- `WriteStream (stream, data, size)` from its entry (`X`'s registers `g0`, `S` = `g0.rsp`), `fb` the `fs` base,
`m` = `0x80000000`: the pushes' slots, the guard's slot and the `call`'s return address slot in what the run may
store into; the guard at `fs:0x28`, `processed` (`aR S + 4`), the vtable's slot (`stream`) and the return address
readable. The memory invariant `I`: of the bytes after the prologue (`hI0`), giving the stack (`hIs`), the vtable's
entry at 24 readable and equal to `eF` (`fv`, `htgt`). The callee (`kf`, at `eF`, for `r` not 0 left and the data
`p`, the bytes `W` with `I`): from its return the loop's registers as they were, `I` and `processed` at most what
was asked. At the return address (`kr`): `rsp` 8 above the entry's, the callee-saved registers as they were. -/
theorem wst_ok {fb : Addr} {eF : Addr} {codeF : List Byte} {g0 : Gprs} {m : BitVec 64}
    {I : (Addr → Byte) → Prop}
    (c : Seg prof F Wl L s₀ o) (hfs : s₀.cpu.seg.fsBase = fb) (hin : CodeIn L wst_at wst)
    (hinF : CodeIn L eF codeF) (hF0 : 0 < codeF.length)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = wst_at) (hg0 : X.cpu.gpr = g0)
    (hm : m = 2147483648#64)
    (hcl : ∀ i < 8, Foot F.data (Addr.add (fb + 40#64) i))
    (hs1 : ∀ i < 8, Foot Wl (Addr.add (g0.rsp - 8) i)) (hs2 : ∀ i < 8, Foot Wl (Addr.add (g0.rsp - 8 - 8) i))
    (hs3 : ∀ i < 8, Foot Wl (Addr.add (g0.rsp - 8 - 8 - 8) i))
    (hs4 : ∀ i < 8, Foot Wl (Addr.add (g0.rsp - 8 - 8 - 8 - 8) i))
    (hs5 : ∀ i < 8, Foot Wl (Addr.add (g0.rsp - 8 - 8 - 8 - 8 - 8) i))
    (hw8 : ∀ i < 8, Foot Wl (Addr.add (aR g0.rsp + 8#64) i))
    (hr8 : ∀ i < 8, Foot Wl (Addr.add (aR g0.rsp - 8) i))
    (f4 : ∀ i < 4, Foot F.data (Addr.add (aR g0.rsp + 4#64) i))
    (hl : ∀ i < 8, Foot F.data (Addr.add g0.rsp i))
    (fa : ∀ i < 8, Foot F.data (Addr.add g0.rdi i))
    (fv : ∀ W, I W → ∀ i < 8, Foot F.data (Addr.add (rdq(W, g0.rdi) + 24#64) i))
    (htgt : ∀ W, I W → rdq(W, rdq(W, g0.rdi) + 24#64) = eF)
    (hin₂ : CodeIn L e₂ code₂) (h₂ : j₂ < code₂.length)
    (hI0 : I (V0 fb V g0)) (hIs : ∀ W, I W → Stk fb W g0.rsp g0 (e₂.add j₂))
    (kf : ∀ (r p : BitVec 64) (W : Addr → Byte), r ≠ 0 → I W →
      KC prof F Wl L s₀ o gev gP gE g0.rsp eF W (Ar g0.rsp g0 m r p) (Lp g0.rsp g0 m r p)
        fun W' => I W' ∧ (rdd(W', aR g0.rsp + 4#64)).toNat ≤ (rq m r).toNat)
    (kr : ∀ (W' : Addr → Byte) (Z' : State) (t' : Nat), KeptW Wl s₀ Z' → Agree F Z'.proc.mm.mem W' →
      Z'.cpu.rip = e₂.add j₂ → Z'.cpu.gpr.rsp = g0.rsp + 8 → KS g0 Z'.cpu.gpr →
      GoG prof L o gev gP gE Z' t') :
    GoG prof L o gev gP gE X t := by
  subst hg0 hm
  have f8 : ∀ i < 8, Foot F.data (Addr.add (aR X.cpu.gpr.rsp + 8#64) i) := fun i hi => c.hws _ (hw8 i hi)
  have g1 : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rsp - 8) i) := fun i hi => c.hws _ (hs1 i hi)
  have g2 : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rsp - 8 - 8) i) := fun i hi => c.hws _ (hs2 i hi)
  have g3 : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rsp - 8 - 8 - 8) i) := fun i hi => c.hws _ (hs3 i hi)
  have g4 : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rsp - 8 - 8 - 8 - 8) i) := fun i hi => c.hws _ (hs4 i hi)
  have g5 : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rsp - 8 - 8 - 8 - 8 - 8) i) :=
    fun i hi => c.hws _ (hs5 i hi)
  -- from 112 and from 144
  have T112 : ∀ (Y : State) (W : Addr → Byte) (t' : Nat), KeptW Wl s₀ Y → Agree F Y.proc.mm.mem W →
      Y.cpu.rip = wst_at.add 112 → Y.cpu.gpr.rsp = aR X.cpu.gpr.rsp → Y.cpu.gpr.r15 = X.cpu.gpr.r15 → I W →
      GoG prof L o gev gP gE Y t' := fun Y W t' hKY hAY hrY hsY h15 hIW =>
    tail112 c hfs hin hKY hAY hrY hsY h15 (hIs W hIW) hcl f8 g1 g2 g3 g4 g5 hl hin₂ h₂
      fun Z' t'' a b d e f => kr W Z' t'' a b d e f
  have T144 : ∀ (Y : State) (W : Addr → Byte) (t' : Nat), KeptW Wl s₀ Y → Agree F Y.proc.mm.mem W →
      Y.cpu.rip = wst_at.add 144 → Y.cpu.gpr.rsp = aR X.cpu.gpr.rsp → Y.cpu.gpr.r15 = X.cpu.gpr.r15 → I W →
      GoG prof L o gev gP gE Y t' := by
    intro Y W t' hKY hAY hrY hsY h15 hIW
    refine (c_144 prof fb).run c hfs hin (fun j' g' _ V' => j' = 112 ∧ V' = W ∧ g'.rsp = Y.cpu.gpr.rsp ∧
        g'.r15 = Y.cpu.gpr.r15) hKY hAY hrY (vc_144 fun _ a b _ => ⟨rfl, rfl, a, b⟩) ?_
    rintro j' g fl V₁ ⟨rfl, hV₁, gs, g15⟩ U t₁ hKU hAU hrU hgU -
    subst V₁ hgU
    exact T112 U W t₁ hKU hAU hrU (gs.trans hsY) (g15.trans h15) hIW
  -- the loop, by induction on a bound of what is left
  have LP : ∀ (n : Nat) (Y : State) (W : Addr → Byte) (t' : Nat) (r p : BitVec 64), r.toNat < n → r ≠ 0 →
      KeptW Wl s₀ Y → Agree F Y.proc.mm.mem W → Y.cpu.rip = wst_at.add 73 →
      Lp X.cpu.gpr.rsp X.cpu.gpr 2147483648#64 r p Y.cpu.gpr → I W → GoG prof L o gev gP gE Y t' := by
    intro n
    induction n with
    | zero => intro Y W t' r p hn; exact absurd hn (Nat.not_lt_zero _)
    | succ n ih =>
      intro Y W t' r p hn hr0 hKY hAY hrY hLp hIW
      obtain ⟨ls, lb, lp, l12, l13, l14, l15⟩ := hLp
      refine (c_73 prof fb).run c hfs hin (fun j' g' _ V' => j' = 95 ∧ V' = W ∧
          g'.rax = rdq(W, X.cpu.gpr.rdi) ∧ g'.rdx = rq 2147483648#64 r ∧ g'.rsi = p ∧
          g'.rcx = aR X.cpu.gpr.rsp + 4#64 ∧ g'.rdi = X.cpu.gpr.rdi ∧ g'.rsp = aR X.cpu.gpr.rsp ∧ g'.rbx = r ∧
          g'.rbp = p ∧ g'.r12 = 2147483648#64 ∧ g'.r13 = aR X.cpu.gpr.rsp + 4#64 ∧ g'.r14 = X.cpu.gpr.rdi ∧
          g'.r15 = X.cpu.gpr.r15) hKY hAY hrY
        (vc_73 (by rw [l14]; exact fa) fun _ a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 _ =>
          ⟨rfl, rfl, by rw [a1, l14], by rw [a2, lb, l12], by rw [a3, lp], by rw [a4, l13], by rw [a5, l14],
            by rw [a6, ls], by rw [a7, lb], by rw [a8, lp], by rw [a9, l12], by rw [a10, l13], by rw [a11, l14],
            by rw [a12, l15]⟩) ?_
      rintro j' g fl V₁ ⟨rfl, hV₁, ga, gd, gsi, gc, gdi, gs, gb, gp, g12, g13, g14, g15⟩ U t₁ hKU hAU hrU
        hgU -
      subst V₁ hgU
      have he : eaD U 0 24 = rdq(W, X.cpu.gpr.rdi) + 24#64 := by
        show U.cpu.gpr.get (regOf 0) + BitVec.ofNat 64 24 = _
        rw [show U.cpu.gpr.get (regOf 0) = U.cpu.gpr.rax from rfl, ga]
      have hU : U.cpu.gpr.rsp - 8 = aR X.cpu.gpr.rsp - 8 := by rw [gs]
      refine c.s_callM hKU hAU hin (lt_len (by decide)) hrU (call_95 _) (by rw [he]; exact fv W hIW) hinF hF0
        (by rw [he]; exact htgt W hIW) (by rw [hU]; exact hr8) ?_
      rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
      rw [hU] at hA₂
      refine kf r p W hr0 hIW Y₂ t₂ hK₂ hA₂ hr₂ (by rw [hg₂]; exact hU)
        (by rw [hg₂]; exact ⟨gb, gp, g12, g13, g14, g15, gdi, gsi, gd, gc⟩) ?_
      -- back from the callee, at 98
      intro Z W' t₃ hKZ hAZ hrZ hLZ hN
      obtain ⟨hIW', hle⟩ := hN
      obtain ⟨zs, zb, zp, z12, z13, z14, z15⟩ := hLZ
      have f4' : ∀ i < 4, Foot F.data (Addr.add (Z.cpu.gpr.rsp + 4#64) i) := by rw [zs]; exact f4
      by_cases ha : BitVec.setWidth 32 Z.cpu.gpr.rax = 0
      · by_cases hv0 : rdd(W', Z.cpu.gpr.rsp + 4#64) = 0
        · -- nothing written: `E_FAIL`
          refine (c_98 prof fb).run c hfs hin (fun j' g' _ V' => j' = 112 ∧ V' = W' ∧ g'.rsp = Z.cpu.gpr.rsp ∧
              g'.r15 = Z.cpu.gpr.r15) hKZ hAZ hrZ
            (vc_98f (beq_iff_eq.2 ha) (beq_iff_eq.2 hv0) f4' fun _ a b _ => ⟨rfl, rfl, a, b⟩) ?_
          rintro j' g fl V₁ ⟨rfl, hV₁, gs', g15'⟩ U₂ t₄ hKU₂ hAU₂ hrU₂ hgU₂ -
          subst V₁ hgU₂
          exact T112 U₂ W' t₄ hKU₂ hAU₂ hrU₂ (gs'.trans zs) (g15'.trans z15) hIW'
        · by_cases hz : Z.cpu.gpr.rbx - BitVec.setWidth 64 rdd(W', Z.cpu.gpr.rsp + 4#64) = 0
          · -- all written: to 144
            refine (c_98 prof fb).run c hfs hin (fun j' g' _ V' => j' = 144 ∧ V' = W' ∧
                g'.rsp = Z.cpu.gpr.rsp ∧ g'.r15 = Z.cpu.gpr.r15) hKZ hAZ hrZ
              (vc_98z (beq_iff_eq.2 ha) (beq_eq_false_iff_ne.2 hv0) (beq_iff_eq.2 hz) f4'
                fun _ a b _ => ⟨rfl, rfl, a, b⟩) ?_
            rintro j' g fl V₁ ⟨rfl, hV₁, gs', g15'⟩ U₂ t₄ hKU₂ hAU₂ hrU₂ hgU₂ -
            subst V₁ hgU₂
            exact T144 U₂ W' t₄ hKU₂ hAU₂ hrU₂ (gs'.trans zs) (g15'.trans z15) hIW'
          · -- something left: round again
            refine (c_98 prof fb).run c hfs hin (fun j' g' _ V' => j' = 73 ∧ V' = W' ∧
                g'.rsp = Z.cpu.gpr.rsp ∧
                g'.rbx = Z.cpu.gpr.rbx - BitVec.setWidth 64 rdd(W', Z.cpu.gpr.rsp + 4#64) ∧
                g'.rbp = Z.cpu.gpr.rbp + BitVec.setWidth 64 rdd(W', Z.cpu.gpr.rsp + 4#64) ∧
                g'.r12 = Z.cpu.gpr.r12 ∧ g'.r13 = Z.cpu.gpr.r13 ∧ g'.r14 = Z.cpu.gpr.r14 ∧
                g'.r15 = Z.cpu.gpr.r15) hKZ hAZ hrZ
              (vc_98c (beq_iff_eq.2 ha) (beq_eq_false_iff_ne.2 hv0) (beq_eq_false_iff_ne.2 hz) f4'
                fun _ a b d e f g h _ => ⟨rfl, rfl, a, b, d, e, f, g, h⟩) ?_
            rintro j' g fl V₁ ⟨rfl, hV₁, gs', gb', gp', g12', g13', g14', g15'⟩ U₂ t₄ hKU₂ hAU₂ hrU₂
              hgU₂ -
            subst V₁ hgU₂
            rw [zs, zb] at gb' hz
            rw [zs, zp] at gp'
            rw [zs] at hv0
            have hx := sw_toNat rdd(W', aR X.cpu.gpr.rsp + 4#64)
            have hlt : (r - BitVec.setWidth 64 rdd(W', aR X.cpu.gpr.rsp + 4#64)).toNat < n :=
              sub_dec (by rw [hx]; exact pos_of_ne hv0)
                (by rw [hx]; exact Nat.le_trans hle (rq_le _ r)) hn
            exact ih U₂ W' t₄ (r - BitVec.setWidth 64 rdd(W', aR X.cpu.gpr.rsp + 4#64))
              (p + BitVec.setWidth 64 rdd(W', aR X.cpu.gpr.rsp + 4#64)) hlt hz hKU₂ hAU₂ hrU₂
              ⟨gs'.trans zs, gb', gp', g12'.trans z12, g13'.trans z13, g14'.trans z14, g15'.trans z15⟩ hIW'
      · -- the callee's error: to 112
        refine (c_98 prof fb).run c hfs hin (fun j' g' _ V' => j' = 112 ∧ V' = W' ∧ g'.rsp = Z.cpu.gpr.rsp ∧
            g'.r15 = Z.cpu.gpr.r15) hKZ hAZ hrZ
          (vc_98a (beq_eq_false_iff_ne.2 ha) f4' fun _ a b _ => ⟨rfl, rfl, a, b⟩) ?_
        rintro j' g fl V₁ ⟨rfl, hV₁, gs', g15'⟩ U₂ t₄ hKU₂ hAU₂ hrU₂ hgU₂ -
        subst V₁ hgU₂
        exact T112 U₂ W' t₄ hKU₂ hAU₂ hrU₂ (gs'.trans zs) (g15'.trans z15) hIW'
  -- the entry
  have hrip' : X.cpu.rip = wst_at.add 0 := by rw [addr_add_zero]; exact hrip
  refine (c_0 prof fb).run c hfs hin (fun j' g' _ V' => V' = V0 fb V X.cpu.gpr ∧
      g'.rsp = aR X.cpu.gpr.rsp ∧ g'.r15 = X.cpu.gpr.r15 ∧
      ((X.cpu.gpr.rdx = 0 ∧ j' = 144) ∨
        (X.cpu.gpr.rdx ≠ 0 ∧ j' = 73 ∧ g'.rbx = X.cpu.gpr.rdx ∧ g'.rbp = X.cpu.gpr.rsi ∧
          g'.r12 = 2147483648#64 ∧ g'.r13 = aR X.cpu.gpr.rsp + 4#64 ∧ g'.r14 = X.cpu.gpr.rdi))) hK hA hrip'
    (vc_0 rfl hs1 hs2 hs3 hs4 hs5 hcl hw8 (fun hz _ a b _ => ⟨rfl, a, b, Or.inl ⟨hz, rfl⟩⟩)
      (fun hn _ a b d e f g h _ => ⟨rfl, a, h, Or.inr ⟨hn, rfl, b, d, e, f, g⟩⟩)) ?_
  rintro j' g fl V₁ ⟨hV₁, gs, g15, hpost⟩ Y t₁ hKY hAY hrY hgY -
  subst V₁ hgY
  rcases hpost with ⟨hz, rfl⟩ | ⟨hn, rfl, gb, gp, g12, g13, g14⟩
  · exact T144 Y _ t₁ hKY hAY hrY gs g15 hI0
  · exact LP (X.cpu.gpr.rdx.toNat + 1) Y _ t₁ _ _ (Nat.lt_succ_self _) hn hKY hAY hrY
      ⟨gs, gb, gp, g12, g13, g14, g15⟩ hI0

end FV7z.Wst
