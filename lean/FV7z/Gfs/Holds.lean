import FV7z.Gfs.Cuts
import FV7z.Lemmas.Fr40
/-!
# `NDir::GetFullPathAndSplit` (PLAN.md §M, M1)

7-Zip 26.06's `bool GetFullPathAndSplit (CFSTR path, FString &resDirPrefix, FString &resFileName)` at `0x454a50` in
`7zzs` (`CPP/Windows/FileDir.cpp`; `objdump -d`), `path` = `rdi`, `resDirPrefix` (an `AString`: its chars at `b`, its
length at `b + 8`) = `rsi` = `b`, `resFileName` = `rdx`: `endbr64; push r14; push r13; mov r13, rdx; push r12;
push rbp; mov rbp, rdi; push rbx; mov rbx, rsi`; at 21 the `call` of `GetFullPath (path, resDirPrefix)`
(`0x454a40`); at 26 `mov r12d, eax; test al, al; je 96` (96: `mov rsi, rbp; mov rdi, rbx`, at 102 the `call` of
`AString::operator= (const char *)` (`0x44c4c0`), `resDirPrefix = path`, at 107 `jmp 33`); at 33 `mov rdi, rbx`, at
36 the `call` of `ReverseFind_PathSepar` (`0x44cb50`); at 41 `mov rsi, [rbx]; mov rdi, r13; lea r14d, [rax + 1];
add rsi, r14` (`i + 1` = `r14`), at 54 the `call` of `operator=` (`resFileName = resDirPrefix.Ptr (i + 1)`); at 59
`cmp r14d, [rbx + 8]; jae 77`; at 65 `mov rax, [rbx]; mov [rbx + 8], r14d; mov byte [rax + r14], 0`
(`DeleteFrom (i + 1)`); at 77 `pop rbx; mov eax, r12d; pop rbp; pop r12; pop r13; pop r14`, the `ret` at 88.

Design as `FV7z/Fkd/Holds.lean`, the frame of `FV7z/Lemmas/Fr40.lean`: the four callees are hypotheses, each a
continuation at its entry (`KC`: the registers at the `call` `G` with `rsp` 8 down, the return address pushed),
given the run from its return (the registers `Fr` keeps as in `G`, the saved registers and the return address in the
bytes `StkF`, and the callee's own post): `k1` at `GetFullPath` (post `P1`), `k4` at `operator=` for `al` = 0
(`P4`), `k2` at `ReverseFind_PathSepar` from 33 by either way (`P2`), `k3` at `operator=` from 54 (`P3`). Of the
bytes `W₃` that `k3` leaves, when `DeleteFrom` stores (`Trim`), the caller gives the stores' facts (`hdl`, `Dlf`:
writable, apart from the six slots, as `Aba.Cpy`). `kr`: the return address, the bytes `Res` (as `W₃`, or with the
stores `Dl`), `eax` = `GetFullPath`'s `eax`.

- `g21`, `V0`, `g26`, `g96`, `g41`, `g77`: the registers (and bytes) at the cuts; `Fm`: the frame from 21 on.
- `Dl`, `Trim`, `Res`, `Dlf`, `rdDl`, `StkF.dl`: the `DeleteFrom` stores; the saved registers after them.
- `vc_0`, `vc_26z`, `vc_26n`, `vc_33`, `vc_41`, `vc_59k`, `vc_59d`, `vc_77`, `vc_107`: the pieces' conditions.
- `tail77`: from 77 to the return address; `from33`: from 33 through `k2`, `k3`; `gfs_ok`: the function.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn FV7z.Fr40
namespace FV7z.Gfs
set_option linter.unusedVariables false

/-! ## The instructions outside the blocks -/

/-- The `call`s: of `GetFullPath`, `ReverseFind_PathSepar`, `operator=` (twice); the `ret`. -/
def pc1 : List Byte := [0xe8, 0xd6, 0xff, 0xff, 0xff]
theorem pc1_0 : ∀ feat, Dec feat pc1 0 (FV7z.mk .call 64 [.rel 18446744073709551574] 5) := by dec_rfl
theorem wc_21 : pc1 <+: gfs.drop 21 := by decide +kernel
theorem call_21 (feat : Features) : Dec feat gfs 21 (FV7z.mk .call 64 [.rel 18446744073709551574] 5) :=
  Dec.shift (j := 21) (k := 0) (pc1_0 feat) wc_21 (Nat.zero_le _)

def pc2 : List Byte := [0xe8, 0xd7, 0x80, 0xff, 0xff]
theorem pc2_0 : ∀ feat, Dec feat pc2 0 (FV7z.mk .call 64 [.rel 18446744073709519063] 5) := by dec_rfl
theorem wc_36 : pc2 <+: gfs.drop 36 := by decide +kernel
theorem call_36 (feat : Features) : Dec feat gfs 36 (FV7z.mk .call 64 [.rel 18446744073709519063] 5) :=
  Dec.shift (j := 36) (k := 0) (pc2_0 feat) wc_36 (Nat.zero_le _)

def pc3 : List Byte := [0xe8, 0x35, 0x7a, 0xff, 0xff]
theorem pc3_0 : ∀ feat, Dec feat pc3 0 (FV7z.mk .call 64 [.rel 18446744073709517365] 5) := by dec_rfl
theorem wc_54 : pc3 <+: gfs.drop 54 := by decide +kernel
theorem call_54 (feat : Features) : Dec feat gfs 54 (FV7z.mk .call 64 [.rel 18446744073709517365] 5) :=
  Dec.shift (j := 54) (k := 0) (pc3_0 feat) wc_54 (Nat.zero_le _)

def pc4 : List Byte := [0xe8, 0x05, 0x7a, 0xff, 0xff]
theorem pc4_0 : ∀ feat, Dec feat pc4 0 (FV7z.mk .call 64 [.rel 18446744073709517317] 5) := by dec_rfl
theorem wc_102 : pc4 <+: gfs.drop 102 := by decide +kernel
theorem call_102 (feat : Features) : Dec feat gfs 102 (FV7z.mk .call 64 [.rel 18446744073709517317] 5) :=
  Dec.shift (j := 102) (k := 0) (pc4_0 feat) wc_102 (Nat.zero_le _)

def pret : List Byte := [0xc3]
theorem pret_0 : ∀ feat, Dec feat pret 0 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem w_88 : pret <+: gfs.drop 88 := by decide +kernel
theorem ret_88 (feat : Features) : Dec feat gfs 88 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 88) (k := 0) (pret_0 feat) w_88 (Nat.zero_le _)

/-! ## Registers and bytes -/

/-- The bytes after the five pushes. -/
abbrev V0 (V : Addr → Byte) (g : Gprs) : Addr → Byte :=
  Vst (Vst (Vst (Vst (Vst V (g.rsp - 8) (toBytesLE g.r14 8)) (g.rsp - 8 - 8) (toBytesLE g.r13 8))
    (g.rsp - 8 - 8 - 8) (toBytesLE g.r12 8)) (g.rsp - 8 - 8 - 8 - 8) (toBytesLE g.rbp 8))
    (g.rsp - 8 - 8 - 8 - 8 - 8) (toBytesLE g.rbx 8)

/-- The registers at the first `call`: `rbx` = `b`, `rbp` = `path`, `r13` = `resFileName`, `rsp` 40 down. -/
abbrev g21 (g : Gprs) : Gprs :=
  { g with
    rbx := g.rsi
    rsp := g.rsp - 8 - 8 - 8 - 8 - 8
    rbp := g.rdi
    r13 := g.rdx }

/-- At 33 for `al` not 0: `r12` = `eax`. -/
abbrev g26 (g : Gprs) : Gprs := { g with r12 := BitVec.setWidth 64 (BitVec.setWidth 32 g.rax) }

/-- At the `call` at 102 (`al` = 0): `r12` = `eax`, `rsi` = `path`, `rdi` = `b`. -/
abbrev g96 (g : Gprs) : Gprs :=
  { g with
    r12 := BitVec.setWidth 64 (BitVec.setWidth 32 g.rax)
    rsi := g.rbp
    rdi := g.rbx }

/-- At the `call` at 54: `r14` = `i + 1` (`eax` + 1, 32 bits), `rsi` = the chars of `b` + `r14`,
`rdi` = `resFileName`. -/
abbrev g41 (V : Addr → Byte) (g : Gprs) : Gprs :=
  { g with
    rsi := rdq(V, g.rbx) + ((g.rax + 1#64).setWidth 32).setWidth 64
    rdi := g.r13
    r14 := ((g.rax + 1#64).setWidth 32).setWidth 64 }

/-- At the `ret`: `eax` = `r12d`, the five pops. -/
abbrev g77 (V : Addr → Byte) (g : Gprs) : Gprs :=
  { g with
    rax := BitVec.setWidth 64 (BitVec.setWidth 32 g.r12)
    rbx := rdq(V, g.rsp)
    rbp := rdq(V, g.rsp + 8)
    r12 := rdq(V, g.rsp + 8 + 8)
    r13 := rdq(V, g.rsp + 8 + 8 + 8)
    r14 := rdq(V, g.rsp + 8 + 8 + 8 + 8)
    rsp := g.rsp + 8 + 8 + 8 + 8 + 8 }

/-- `i + 1` from the return of `ReverseFind_PathSepar` (`Z`). -/
abbrev nr (Z : State) : Addr := ((Z.cpu.gpr.rax + 1#64).setWidth 32).setWidth 64

/-- The frame from 21 on (`S` the entry's `rsp`, `g0` its registers): the five pushes, `rbx` = `b`, `rbp` = `path`,
`r13` = `resFileName`, `r15` as at the entry. -/
abbrev Fm (S : Addr) (g0 g : Gprs) : Prop :=
  g.rsp = S - 8 - 8 - 8 - 8 - 8 ∧ g.rbx = g0.rsi ∧ g.rbp = g0.rdi ∧ g.r13 = g0.rdx ∧ g.r15 = g0.r15

theorem Fm.fr {S : Addr} {g0 g g' : Gprs} (h : Fm S g0 g) (h' : Fr g g') : Fm S g0 g' :=
  ⟨h'.1.trans h.1, h'.2.1.trans h.2.1, h'.2.2.1.trans h.2.2.1, h'.2.2.2.2.1.trans h.2.2.2.1,
    h'.2.2.2.2.2.2.trans h.2.2.2.2⟩

/-! ## `DeleteFrom` -/

/-- The bytes after `mov [b + 8], r14d; mov byte [chars + r14], 0` (`n` = `r14`). -/
abbrev Dl (W : Addr → Byte) (b n : Addr) : Addr → Byte :=
  Vst (Vst W (b + 8#64) (toBytesLE (BitVec.setWidth 32 n) 4)) (rdq(W, b) + n) (toBytesLE (0#8) 1)

/-- `DeleteFrom` stores: `n` (32 bits) below the length at `b + 8`. -/
abbrev Trim (W : Addr → Byte) (b n : Addr) : Prop := (BitVec.setWidth 32 n).toNat < rdd(W, b + 8#64).toNat

/-- The bytes at the return: as `W`, or with the stores. -/
abbrev Res (W : Addr → Byte) (b n : Addr) (W' : Addr → Byte) : Prop :=
  (¬Trim W b n ∧ W' = W) ∨ (Trim W b n ∧ W' = Dl W b n)

/-- The stores' facts: writable, apart from the six slots of the frame at `S`. -/
structure Dlf (F : Footprint) (Wl : List Rgn) (S : Addr) (W : Addr → Byte) (b n : Addr) : Prop where
  w8 : ∀ i < 4, Foot Wl (Addr.add (b + 8#64) i)
  w1 : ∀ i < 1, Foot Wl (Addr.add (rdq(W, b) + n) i)
  a8 : Ap6 S (b + 8#64) 4
  a1 : Ap6 S (rdq(W, b) + n) 1

theorem rdDl {W : Addr → Byte} {b n x : Addr} (h4 : Ap x (b + 8#64) 4) (h1 : Ap x (rdq(W, b) + n) 1) :
    rdq(Dl W b n, x) = rdq(W, x) :=
  (rdSt (V := Vst W (b + 8#64) (toBytesLE (BitVec.setWidth 32 n) 4)) (bs := toBytesLE (0#8) 1)
    (toBytesLE_length _ _) h1).trans
    (rdSt (V := W) (bs := toBytesLE (BitVec.setWidth 32 n) 4) (toBytesLE_length _ _) h4)

theorem StkF.dl {W : Addr → Byte} {S : Addr} {g0 : Gprs} {ra b n : Addr} (h : StkF W S g0 ra)
    (h4 : Ap6 S (b + 8#64) 4) (h1 : Ap6 S (rdq(W, b) + n) 1) : StkF (Dl W b n) S g0 ra := by
  obtain ⟨s1, s2, s3, s4, s5, s6⟩ := h
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ := h4
  obtain ⟨b1, b2, b3, b4, b5, b6⟩ := h1
  exact ⟨(rdDl a1 b1).trans s1, (rdDl a2 b2).trans s2, (rdDl a3 b3).trans s3, (rdDl a4 b4).trans s4,
    (rdDl a5 b5).trans s5, (rdDl a6 b6).trans s6⟩

/-! ## The pieces -/

variable {F : Footprint} {Wl : List Rgn}

/-- The pushes, `r13` = `resFileName`, `rbp` = `path`, `rbx` = `b`, to the first `call`. -/
theorem vc_0 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (hs1 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8) i)) (hs2 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8) i))
    (hs3 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8 - 8) i))
    (hs4 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8 - 8 - 8) i))
    (hs5 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8 - 8 - 8 - 8) i))
    (h : ∀ fl, Q 21 (g21 g) fl (V0 V g)) :
    W_0 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [g21, V0] at hs1 hs2 hs3 hs4 hs5 h ⊢
  wpx [W_0, o0]
  all_goals repeat' (first | exact h _ | assumption | exact trivial | apply And.intro | intro _)

/-- `al` = 0: `r12d` = `eax`, `rsi` = `path`, `rdi` = `b`, to the `call` at 102. -/
theorem vc_26z {g : Gprs} {f : Rflags} {V : Addr → Byte} (h : BitVec.setWidth 8 g.rax = 0) :
    W_26 F Wl (fun j' g' _ V' => j' = 102 ∧ g' = g96 g ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [g96] at h ⊢
  have hz : (BitVec.setWidth 8 rax == 0) = true := beq_iff_eq.2 h
  wpx [W_26, W_96, o1, o7, hz, BitVec.and_self, Bool.false_eq_true, Bool.true_eq_false, false_implies,
    implies_true]
  all_goals repeat' (first
    | exact rfl
    | assumption
    | exact trivial
    | (intro hh; exact absurd hh h)
    | (intro hh; exact absurd h hh)
    | apply And.intro
    | intro _)

/-- `al` not 0: `r12d` = `eax`, to 33. -/
theorem vc_26n {g : Gprs} {f : Rflags} {V : Addr → Byte} (h : ¬BitVec.setWidth 8 g.rax = 0) :
    W_26 F Wl (fun j' g' _ V' => j' = 33 ∧ g' = g26 g ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [g26] at h ⊢
  have hz : (BitVec.setWidth 8 rax == 0) = false := beq_eq_false_iff_ne.2 h
  wpx [W_26, W_96, o1, o7, hz, BitVec.and_self, Bool.false_eq_true, Bool.true_eq_false, false_implies,
    implies_true]
  all_goals repeat' (first
    | exact rfl
    | assumption
    | exact trivial
    | (intro hh; exact absurd hh h)
    | (intro hh; exact absurd h hh)
    | apply And.intro
    | intro _)

/-- `mov rdi, rbx`, to the `call` at 36. -/
theorem vc_33 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (h : ∀ fl, Q 36 { g with rdi := g.rbx } fl V) : W_33 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h ⊢
  wpx [W_33, o2]
  all_goals repeat' (first | exact h _ | assumption | exact trivial | apply And.intro | intro _)

/-- `mov rsi, [rbx]; mov rdi, r13; lea r14d, [rax + 1]; add rsi, r14`, to the `call` at 54. -/
theorem vc_41 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} (fq : ∀ i < 8, Foot F.data (Addr.add g.rbx i))
    (h : ∀ fl, Q 54 (g41 V g) fl V) : W_41 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [g41] at fq h ⊢
  wpx [W_41, o3]
  all_goals repeat' (first | exact h _ | assumption | exact trivial | apply And.intro | intro _)

/-- `cmp r14d, [rbx + 8]; jae 77`: `r14d` not below the length, to 77. -/
theorem vc_59k {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (f4 : ∀ i < 4, Foot F.data (Addr.add (g.rbx + 8#64) i))
    (h : ¬(BitVec.setWidth 32 g.r14).toNat < rdd(V, g.rbx + 8#64).toNat) :
    W_59 F Wl (fun j' g' _ V' => j' = 77 ∧ g' = g ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at f4 h ⊢
  have hc' := eq_false h
  wpx [W_59, W_65, o4, o5, hc', Bool.not_true, Bool.not_false, Bool.false_eq_true, Bool.true_eq_false,
    false_implies, implies_true, beq_iff_eq, beq_eq_false_iff_ne, ne_eq, Bool.not_eq_true', Bool.not_eq_false',
    decide_eq_true_eq, decide_eq_false_iff_not]
  all_goals repeat' (first
    | exact rfl
    | assumption
    | exact trivial
    | (intro hh; exact absurd hh h)
    | (intro hh; exact absurd h hh)
    | apply And.intro
    | intro _)

/-- `r14d` below the length: `mov rax, [rbx]; mov [rbx + 8], r14d; mov byte [rax + r14], 0`, to 77. -/
theorem vc_59d {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (f4 : ∀ i < 4, Foot F.data (Addr.add (g.rbx + 8#64) i)) (f8 : ∀ i < 8, Foot F.data (Addr.add g.rbx i))
    (w4 : ∀ i < 4, Foot Wl (Addr.add (g.rbx + 8#64) i))
    (w1 : ∀ i < 1, Foot Wl (Addr.add (rdq(V, g.rbx) + g.r14) i))
    (h : (BitVec.setWidth 32 g.r14).toNat < rdd(V, g.rbx + 8#64).toNat) :
    W_59 F Wl (fun j' g' _ V' => j' = 77 ∧ g' = { g with rax := rdq(V, g.rbx) } ∧ V' = Dl V g.rbx g.r14)
      g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [Dl] at f4 f8 w4 w1 h ⊢
  have hc' := eq_true h
  wpx [W_59, W_65, o4, o5, hc', not_true_eq_false, Bool.not_true, Bool.not_false, Bool.false_eq_true,
    Bool.true_eq_false, false_implies, implies_true, beq_iff_eq, beq_eq_false_iff_ne, ne_eq, Bool.not_eq_true', Bool.not_eq_false',
    decide_eq_true_eq, decide_eq_false_iff_not]
  all_goals repeat' (first
    | exact rfl
    | assumption
    | exact trivial
    | (intro hh; exact absurd hh h)
    | (intro hh; exact absurd h hh)
    | (intro hh; exact absurd trivial hh)
    | apply And.intro
    | intro _)

/-- `pop rbx; mov eax, r12d; pop rbp; pop r12; pop r13; pop r14`, to the `ret` at 88. -/
theorem vc_77 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (p1 : ∀ i < 8, Foot F.data (Addr.add g.rsp i)) (p2 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8) i))
    (p3 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8 + 8) i))
    (p4 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8 + 8 + 8) i))
    (p5 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8 + 8 + 8 + 8) i)) (h : ∀ fl, Q 88 (g77 V g) fl V) :
    W_77 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [g77] at p1 p2 p3 p4 p5 h ⊢
  wpx [W_77, o6]
  all_goals repeat' (first
    | exact h _
    | with_reducible exact p1
    | with_reducible exact p2
    | with_reducible exact p3
    | with_reducible exact p4
    | with_reducible exact p5
    | exact trivial
    | apply And.intro
    | intro _)

/-- `jmp 33`. -/
theorem vc_107 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} (h : ∀ fl, Q 33 g fl V) :
    W_107 F Wl Q g f V :=
  h (rfz f)

/-! ## The runs -/

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {X : State} {t : Nat} {V : Addr → Byte} {e₂ : Addr} {code₂ : List Byte} {j₂ : Nat}

/-- A callee at `tg` from a `call` returning to `gfs_at + r` (registers `G` there, bytes `W`): at its entry, and from
its return with the registers `Fr` keeps, the frame's slots (`StkF`, the entry's `rsp` `S` and registers `g0`, the
return address `ra`) and its post `P`, the run goes on to the goal. -/
def KC (prof : Profile) (F : Footprint) (Wl : List Rgn) (L : List (Addr × List Byte)) (s₀ : State) (o : Oracle)
    (gev : List Event) (gP : State → Nat → List Event → Prop) (gE : Outcome → List Event → Prop)
    (S : Addr) (g0 : Gprs) (ra : Addr) (tg : Addr) (r : Nat) (G : Gprs) (W : Addr → Byte)
    (P : State → (Addr → Byte) → Prop) : Prop :=
  ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y → Agree F Y.proc.mm.mem (Vst W (G.rsp - 8) (toBytesLE (gfs_at.add r) 8)) →
    Y.cpu.rip = tg → Y.cpu.gpr = G.set 4 (G.rsp - 8) →
    (∀ (Z : State) (W' : Addr → Byte) (t'' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem W' →
      Z.cpu.rip = gfs_at.add r → Fr G Z.cpu.gpr → StkF W' S g0 ra → P Z W' →
      GoG prof L o gev gP gE Z t'') →
    GoG prof L o gev gP gE Y t'

/-- From 77 (the bytes `W`, `r12` = `R` widened) to the return address `e₂.add j₂`, with `eax` = `R`. -/
theorem tail77 {W : Addr → Byte} {S : Addr} {g0 : Gprs} {R : BitVec 32} {Y : State} (c : Seg prof F Wl L s₀ o)
    (hin : CodeIn L gfs_at gfs) (hK : KeptW Wl s₀ Y) (hA : Agree F Y.proc.mm.mem W)
    (hr : Y.cpu.rip = gfs_at.add 77) (hm : Fm S g0 Y.cpu.gpr) (h12 : Y.cpu.gpr.r12 = BitVec.setWidth 64 R)
    (hst : StkF W S g0 (e₂.add j₂)) (ft : FtsF F S) (hin₂ : CodeIn L e₂ code₂) (h₂ : j₂ < code₂.length)
    (k : ∀ (Z' : State) (t' : Nat), KeptW Wl s₀ Z' → Agree F Z'.proc.mm.mem W → Z'.cpu.rip = e₂.add j₂ →
      Z'.cpu.gpr.rsp = S + 8 → KS g0 Z'.cpu.gpr → Z'.cpu.gpr.rax = BitVec.setWidth 64 R →
      GoG prof L o gev gP gE Z' t') :
    GoG prof L o gev gP gE Y t := by
  obtain ⟨ms, mb, mp, m13, m15⟩ := hm
  obtain ⟨s1, s2, s3, s4, s5, s6⟩ := hst
  obtain ⟨f1, f2, f3, f4, f5, f6⟩ := ft
  refine (c_77 prof).run c hin (fun j' g' _ V' => j' = 88 ∧ g' = g77 W Y.cpu.gpr ∧ V' = W) hK hA hr
    (vc_77 (by rw [ms]; exact f1) (by rw [ms]; exact f2) (by rw [ms]; exact f3) (by rw [ms]; exact f4)
      (by rw [ms]; exact f5) fun _ => ⟨rfl, rfl, rfl⟩) ?_
  rintro j' g fl V₁ ⟨rfl, hg, hV₁⟩ U t₁ hKU hAU hrU hgU -
  subst g V₁
  have hsU : U.cpu.gpr.rsp = S := by
    rw [hgU]
    show Y.cpu.gpr.rsp + 8 + 8 + 8 + 8 + 8 = S
    rw [ms, r5]
  have e1 : rdq(W, Y.cpu.gpr.rsp) = g0.rbx := by rw [ms]; exact s1
  have e2 : rdq(W, Y.cpu.gpr.rsp + 8) = g0.rbp := by rw [ms]; exact s2
  have e3 : rdq(W, Y.cpu.gpr.rsp + 8 + 8) = g0.r12 := by rw [ms]; exact s3
  have e4 : rdq(W, Y.cpu.gpr.rsp + 8 + 8 + 8) = g0.r13 := by rw [ms]; exact s4
  have e5 : rdq(W, Y.cpu.gpr.rsp + 8 + 8 + 8 + 8) = g0.r14 := by rw [ms]; exact s5
  refine c.s_ret hKU hAU hin (lt_len (by decide)) hrU (ret_88 _) (by rw [hsU]; exact f6) hin₂ h₂
    (by rw [hsU]; exact s6) ?_
  rintro Z' t₂ hKZ' hAZ' ⟨hrZ', hgZ'⟩
  refine k Z' t₂ hKZ' hAZ' hrZ' ?_ ?_ ?_
  · rw [hgZ']
    show U.cpu.gpr.rsp + 8 = _
    rw [hsU]
  · rw [hgZ', hgU]
    exact ⟨e1, e2, e3, e4, e5, m15⟩
  · rw [hgZ', hgU]
    show BitVec.setWidth 64 (BitVec.setWidth 32 Y.cpu.gpr.r12) = _
    rw [h12, sw_64_32]

/-- From 33 (the bytes `W`, `r12` = `R` widened): `ReverseFind_PathSepar` (`k2`), `operator=` on `resFileName`
(`k3`), `DeleteFrom` when `Trim` (its facts `hdl`), to the return address (`kr`). -/
theorem from33 {P2 : (Addr → Byte) → State → (Addr → Byte) → Prop} {P3 : State → State → (Addr → Byte) → Prop}
    {S : Addr} {g0 : Gprs} {R : BitVec 32} {W : Addr → Byte} {Y : State}
    (c : Seg prof F Wl L s₀ o) (hin : CodeIn L gfs_at gfs)
    {code2 : List Byte} (hin2 : CodeIn L 0x44cb50#64 code2) (hc2 : 0 < code2.length)
    {code3 : List Byte} (hin3 : CodeIn L 0x44c4c0#64 code3) (hc3 : 0 < code3.length)
    (hs6 : ∀ i < 8, Foot Wl (Addr.add (S - 8 - 8 - 8 - 8 - 8 - 8) i)) (ft : FtsF F S)
    (hb8 : ∀ i < 8, Foot F.data (Addr.add g0.rsi i)) (hb4 : ∀ i < 4, Foot F.data (Addr.add (g0.rsi + 8#64) i))
    (hin₂ : CodeIn L e₂ code₂) (h₂ : j₂ < code₂.length)
    (hK : KeptW Wl s₀ Y) (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = gfs_at.add 33)
    (hm : Fm S g0 Y.cpu.gpr) (h12 : Y.cpu.gpr.r12 = BitVec.setWidth 64 R) (hst : StkF W S g0 (e₂.add j₂))
    (k2 : KC prof F Wl L s₀ o gev gP gE S g0 (e₂.add j₂) 0x44cb50#64 41 { Y.cpu.gpr with rdi := Y.cpu.gpr.rbx } W
      (P2 W))
    (k3 : ∀ (Z₂ : State) (W₂ : Addr → Byte), P2 W Z₂ W₂ →
      KC prof F Wl L s₀ o gev gP gE S g0 (e₂.add j₂) 0x44c4c0#64 59 (g41 W₂ Z₂.cpu.gpr) W₂ (P3 Z₂))
    (hdl : ∀ (Z₂ Z₃ : State) (W₃ : Addr → Byte), P3 Z₂ Z₃ W₃ → Trim W₃ g0.rsi (nr Z₂) →
      Dlf F Wl S W₃ g0.rsi (nr Z₂))
    (kr : ∀ (Z₂ : State) (W₂ : Addr → Byte) (Z₃ : State) (W₃ : Addr → Byte), P2 W Z₂ W₂ → P3 Z₂ Z₃ W₃ →
      ∀ (W' : Addr → Byte) (Z' : State) (t' : Nat), KeptW Wl s₀ Z' → Agree F Z'.proc.mm.mem W' →
      Res W₃ g0.rsi (nr Z₂) W' → Z'.cpu.rip = e₂.add j₂ → Z'.cpu.gpr.rsp = S + 8 → KS g0 Z'.cpu.gpr →
      Z'.cpu.gpr.rax = BitVec.setWidth 64 R → GoG prof L o gev gP gE Z' t') :
    GoG prof L o gev gP gE Y t := by
  -- `mov rdi, rbx`, the `call` of `ReverseFind_PathSepar`
  refine (c_33 prof).run c hin (fun j' g' _ V' => j' = 36 ∧ g' = { Y.cpu.gpr with rdi := Y.cpu.gpr.rbx } ∧ V' = W)
    hK hA hr (vc_33 fun _ => ⟨rfl, rfl, rfl⟩) ?_
  rintro j' g fl V₁ ⟨rfl, hg, hV₁⟩ U t₁ hKU hAU hrU hgU -
  subst g V₁
  have hU : U.cpu.gpr.rsp - 8 = S - 8 - 8 - 8 - 8 - 8 - 8 := by
    rw [hgU]
    show Y.cpu.gpr.rsp - 8 = _
    rw [hm.1]
  refine c.s_call hKU hAU hin (lt_len (by decide)) hrU (call_36 _) hin2 hc2 (by decide) (by rw [hU]; exact hs6) ?_
  rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
  rw [hgU] at hA₂ hg₂
  refine k2 Y₂ t₂ hK₂ hA₂ hr₂ hg₂ ?_
  -- back at 41: `rsi` = the chars + `i + 1`, the `call` of `operator=`
  intro Z₂ W₂ t₃ hKZ hAZ hrZ hfr hst2 hP2
  have hmZ : Fm S g0 Z₂.cpu.gpr := Fm.fr (g := { Y.cpu.gpr with rdi := Y.cpu.gpr.rbx }) hm hfr
  have h12Z : Z₂.cpu.gpr.r12 = BitVec.setWidth 64 R := hfr.2.2.2.1.trans h12
  refine (c_41 prof).run c hin (fun j' g' _ V' => j' = 54 ∧ g' = g41 W₂ Z₂.cpu.gpr ∧ V' = W₂) hKZ hAZ hrZ
    (vc_41 (by rw [hmZ.2.1]; exact hb8) fun _ => ⟨rfl, rfl, rfl⟩) ?_
  rintro j' g fl V₁ ⟨rfl, hg, hV₁⟩ U₂ t₄ hKU₂ hAU₂ hrU₂ hgU₂ -
  subst g V₁
  have hU₂ : U₂.cpu.gpr.rsp - 8 = S - 8 - 8 - 8 - 8 - 8 - 8 := by
    rw [hgU₂]
    show Z₂.cpu.gpr.rsp - 8 = _
    rw [hmZ.1]
  refine c.s_call hKU₂ hAU₂ hin (lt_len (by decide)) hrU₂ (call_54 _) hin3 hc3 (by decide) (by rw [hU₂]; exact hs6)
    ?_
  rintro Y₃ t₅ hK₃ hA₃ ⟨hr₃, hg₃⟩
  rw [hgU₂] at hA₃ hg₃
  refine k3 Z₂ W₂ hP2 Y₃ t₅ hK₃ hA₃ hr₃ hg₃ ?_
  -- back at 59: `DeleteFrom (i + 1)` when `i + 1` is below the length
  intro Z₃ W₃ t₆ hKZ3 hAZ3 hrZ3 hfr3 hst3 hP3
  have hmZ3 : Fm S g0 Z₃.cpu.gpr := Fm.fr (g := g41 W₂ Z₂.cpu.gpr) hmZ hfr3
  have h12Z3 : Z₃.cpu.gpr.r12 = BitVec.setWidth 64 R := hfr3.2.2.2.1.trans h12Z
  have h14Z3 : Z₃.cpu.gpr.r14 = nr Z₂ := hfr3.2.2.2.2.2.1
  have hbZ3 : Z₃.cpu.gpr.rbx = g0.rsi := hmZ3.2.1
  by_cases hlt : Trim W₃ g0.rsi (nr Z₂)
  · have dl := hdl Z₂ Z₃ W₃ hP3 hlt
    refine (c_59 prof).run c hin (fun j' g' _ V' => j' = 77 ∧
        g' = { Z₃.cpu.gpr with rax := rdq(W₃, Z₃.cpu.gpr.rbx) } ∧ V' = Dl W₃ Z₃.cpu.gpr.rbx Z₃.cpu.gpr.r14)
      hKZ3 hAZ3 hrZ3
      (vc_59d (by rw [hbZ3]; exact hb4) (by rw [hbZ3]; exact hb8) (by rw [hbZ3]; exact dl.w8)
        (by rw [hbZ3, h14Z3]; exact dl.w1) (by rw [hbZ3, h14Z3]; exact hlt)) ?_
    rintro j' g fl V₁ ⟨rfl, hg, hV₁⟩ U₃ t₇ hKU₃ hAU₃ hrU₃ hgU₃ -
    subst g V₁
    rw [hbZ3, h14Z3] at hAU₃
    exact tail77 c hin hKU₃ hAU₃ hrU₃ (by rw [hgU₃]; exact hmZ3) (by rw [hgU₃]; exact h12Z3)
      (StkF.dl hst3 dl.a8 dl.a1) ft hin₂ h₂ fun Z' t' a b =>
        kr Z₂ W₂ Z₃ W₃ hP2 hP3 _ Z' t' a b (Or.inr ⟨hlt, rfl⟩)
  · refine (c_59 prof).run c hin (fun j' g' _ V' => j' = 77 ∧ g' = Z₃.cpu.gpr ∧ V' = W₃) hKZ3 hAZ3 hrZ3
      (vc_59k (by rw [hbZ3]; exact hb4) (by rw [hbZ3, h14Z3]; exact hlt)) ?_
    rintro j' g fl V₁ ⟨rfl, hg, hV₁⟩ U₃ t₇ hKU₃ hAU₃ hrU₃ hgU₃ -
    subst g V₁
    exact tail77 c hin hKU₃ hAU₃ hrU₃ (by rw [hgU₃]; exact hmZ3) (by rw [hgU₃]; exact h12Z3) hst3 ft hin₂ h₂
      fun Z' t' a b => kr Z₂ W₂ Z₃ W₃ hP2 hP3 _ Z' t' a b (Or.inl ⟨hlt, rfl⟩)

/-- `GetFullPathAndSplit (path, resDirPrefix, resFileName)` (`rdi`, `rsi` = `b`, `rdx`) from its entry, the five
registers saved at `rsp - 8` … `rsp - 40`: `GetFullPath` at its entry with the registers `g21` (`k1`); from its return
(`P1`), for `al` = 0 `operator=` with `path` (`k4`, `g96`), and either way at 33 (the registers `G` there, the bytes
`W'` as `k1` or `k4` left them) `ReverseFind_PathSepar` on `b` (`k2`); from its return (`P2`), `operator=` on
`resFileName` with the chars from `i + 1` (`k3`, `g41`); from its return (`P3`), with the stores' facts (`hdl`) when
`Trim`, at the return address (`kr`): `rsp` 8 above the entry's, the callee-saved registers as they were, `eax` =
`GetFullPath`'s `eax`, the bytes `Res`. -/
theorem gfs_ok {P1 : State → (Addr → Byte) → Prop} {P4 : State → State → (Addr → Byte) → Prop}
    {P2 : (Addr → Byte) → State → (Addr → Byte) → Prop} {P3 : State → State → (Addr → Byte) → Prop}
    (c : Seg prof F Wl L s₀ o) (hin : CodeIn L gfs_at gfs)
    {code1 : List Byte} (hin1 : CodeIn L 0x454a40#64 code1) (hc1 : 0 < code1.length)
    {code2 : List Byte} (hin2 : CodeIn L 0x44cb50#64 code2) (hc2 : 0 < code2.length)
    {code3 : List Byte} (hin3 : CodeIn L 0x44c4c0#64 code3) (hc3 : 0 < code3.length)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = gfs_at)
    (hs1 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8) i))
    (hs2 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8 - 8) i))
    (hs3 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8 - 8 - 8) i))
    (hs4 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8 - 8 - 8 - 8) i))
    (hs5 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8 - 8 - 8 - 8 - 8) i))
    (hs6 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8 - 8 - 8 - 8 - 8 - 8) i))
    (hl : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsp i))
    (hb8 : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsi i))
    (hb4 : ∀ i < 4, Foot F.data (Addr.add (X.cpu.gpr.rsi + 8#64) i))
    (hin₂ : CodeIn L e₂ code₂) (h₂ : j₂ < code₂.length)
    (k1 : KC prof F Wl L s₀ o gev gP gE X.cpu.gpr.rsp X.cpu.gpr (e₂.add j₂) 0x454a40#64 26 (g21 X.cpu.gpr)
      (V0 V X.cpu.gpr) P1)
    (k4 : ∀ (Z : State) (W : Addr → Byte), P1 Z W → BitVec.setWidth 8 Z.cpu.gpr.rax = 0 →
      KC prof F Wl L s₀ o gev gP gE X.cpu.gpr.rsp X.cpu.gpr (e₂.add j₂) 0x44c4c0#64 107 (g96 Z.cpu.gpr) W (P4 Z))
    (k2 : ∀ (Z : State) (W : Addr → Byte), P1 Z W → ∀ (G : Gprs) (W' : Addr → Byte), Fm X.cpu.gpr.rsp X.cpu.gpr G →
      G.r12 = BitVec.setWidth 64 (BitVec.setWidth 32 Z.cpu.gpr.rax) → G.r14 = X.cpu.gpr.r14 →
      ((¬BitVec.setWidth 8 Z.cpu.gpr.rax = 0 ∧ W' = W) ∨
        (BitVec.setWidth 8 Z.cpu.gpr.rax = 0 ∧ ∃ Z₄ : State, P4 Z Z₄ W')) →
      KC prof F Wl L s₀ o gev gP gE X.cpu.gpr.rsp X.cpu.gpr (e₂.add j₂) 0x44cb50#64 41 { G with rdi := G.rbx } W'
        (P2 W'))
    (k3 : ∀ (W : Addr → Byte) (Z₂ : State) (W₂ : Addr → Byte), P2 W Z₂ W₂ →
      KC prof F Wl L s₀ o gev gP gE X.cpu.gpr.rsp X.cpu.gpr (e₂.add j₂) 0x44c4c0#64 59 (g41 W₂ Z₂.cpu.gpr) W₂
        (P3 Z₂))
    (hdl : ∀ (Z₂ Z₃ : State) (W₃ : Addr → Byte), P3 Z₂ Z₃ W₃ → Trim W₃ X.cpu.gpr.rsi (nr Z₂) →
      Dlf F Wl X.cpu.gpr.rsp W₃ X.cpu.gpr.rsi (nr Z₂))
    (kr : ∀ (Z : State) (W : Addr → Byte), P1 Z W → ∀ (W₀ : Addr → Byte) (Z₂ : State) (W₂ : Addr → Byte)
      (Z₃ : State) (W₃ : Addr → Byte), P2 W₀ Z₂ W₂ → P3 Z₂ Z₃ W₃ →
      ∀ (W' : Addr → Byte) (Z' : State) (t' : Nat), KeptW Wl s₀ Z' → Agree F Z'.proc.mm.mem W' →
      Res W₃ X.cpu.gpr.rsi (nr Z₂) W' → Z'.cpu.rip = e₂.add j₂ → Z'.cpu.gpr.rsp = X.cpu.gpr.rsp + 8 →
      KS X.cpu.gpr Z'.cpu.gpr → Z'.cpu.gpr.rax = BitVec.setWidth 64 (BitVec.setWidth 32 Z.cpu.gpr.rax) →
      GoG prof L o gev gP gE Z' t') :
    GoG prof L o gev gP gE X t := by
  have ft : FtsF F X.cpu.gpr.rsp :=
    ⟨fun i hi => c.hws _ (hs5 i hi), by rw [r1]; exact fun i hi => c.hws _ (hs4 i hi),
      by rw [r2]; exact fun i hi => c.hws _ (hs3 i hi), by rw [r3]; exact fun i hi => c.hws _ (hs2 i hi),
      by rw [r4]; exact fun i hi => c.hws _ (hs1 i hi), hl⟩
  -- the prologue, to the `call` of `GetFullPath`
  refine (c_0 prof).run c hin (fun j' g' _ V' => j' = 21 ∧ g' = g21 X.cpu.gpr ∧ V' = V0 V X.cpu.gpr) hK hA
    (by rw [addr_add_zero]; exact hrip) (vc_0 hs1 hs2 hs3 hs4 hs5 fun _ => ⟨rfl, rfl, rfl⟩) ?_
  rintro j' g fl V₁ ⟨rfl, hg, hV₁⟩ Y t₁ hKY hAY hrY hgY -
  subst g V₁
  have hY : Y.cpu.gpr.rsp - 8 = X.cpu.gpr.rsp - 8 - 8 - 8 - 8 - 8 - 8 := by rw [hgY]
  refine c.s_call hKY hAY hin (lt_len (by decide)) hrY (call_21 _) hin1 hc1 (by decide) (by rw [hY]; exact hs6) ?_
  rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
  rw [hgY] at hA₂ hg₂
  refine k1 Y₂ t₂ hK₂ hA₂ hr₂ hg₂ ?_
  -- back from `GetFullPath`, at 26
  intro Z W t₃ hKZ hAZ hrZ hfr hst hP1
  have hmZ : Fm X.cpu.gpr.rsp X.cpu.gpr Z.cpu.gpr := Fm.fr (g := g21 X.cpu.gpr) ⟨rfl, rfl, rfl, rfl, rfl⟩ hfr
  have h14Z : Z.cpu.gpr.r14 = X.cpu.gpr.r14 := hfr.2.2.2.2.2.1
  by_cases h0 : BitVec.setWidth 8 Z.cpu.gpr.rax = 0
  · -- `al` = 0: `resDirPrefix = path`, then 33
    refine (c_26 prof).run c hin (fun j' g' _ V' => j' = 102 ∧ g' = g96 Z.cpu.gpr ∧ V' = W) hKZ hAZ hrZ
      (vc_26z h0) ?_
    rintro j' g fl V₁ ⟨rfl, hg, hV₁⟩ U t₄ hKU hAU hrU hgU -
    subst g V₁
    have hU : U.cpu.gpr.rsp - 8 = X.cpu.gpr.rsp - 8 - 8 - 8 - 8 - 8 - 8 := by
      rw [hgU]
      show Z.cpu.gpr.rsp - 8 = _
      rw [hmZ.1]
    refine c.s_call hKU hAU hin (lt_len (by decide)) hrU (call_102 _) hin3 hc3 (by decide) (by rw [hU]; exact hs6)
      ?_
    rintro Y₃ t₅ hK₃ hA₃ ⟨hr₃, hg₃⟩
    rw [hgU] at hA₃ hg₃
    refine k4 Z W hP1 h0 Y₃ t₅ hK₃ hA₃ hr₃ hg₃ ?_
    intro Z₄ W₄ t₆ hKZ4 hAZ4 hrZ4 hfr4 hst4 hP4
    refine (c_107 prof).run c hin (fun j' g' _ V' => j' = 33 ∧ g' = Z₄.cpu.gpr ∧ V' = W₄) hKZ4 hAZ4 hrZ4
      (vc_107 fun _ => ⟨rfl, rfl, rfl⟩) ?_
    rintro j' g fl V₁ ⟨rfl, hg, hV₁⟩ U₁ t₇ hKU₁ hAU₁ hrU₁ hgU₁ -
    subst g V₁
    have hmU : Fm X.cpu.gpr.rsp X.cpu.gpr U₁.cpu.gpr := by
      rw [hgU₁]; exact Fm.fr (g := g96 Z.cpu.gpr) hmZ hfr4
    have h12U : U₁.cpu.gpr.r12 = BitVec.setWidth 64 (BitVec.setWidth 32 Z.cpu.gpr.rax) :=
      (congrArg Gprs.r12 hgU₁).trans hfr4.2.2.2.1
    have h14U : U₁.cpu.gpr.r14 = X.cpu.gpr.r14 := ((congrArg Gprs.r14 hgU₁).trans hfr4.2.2.2.2.2.1).trans h14Z
    exact from33 (P2 := P2) (P3 := P3) (S := X.cpu.gpr.rsp) (g0 := X.cpu.gpr)
      (R := BitVec.setWidth 32 Z.cpu.gpr.rax) c hin hin2 hc2 hin3 hc3 hs6 ft hb8 hb4 hin₂ h₂ hKU₁ hAU₁
      hrU₁ hmU h12U hst4 (k2 Z W hP1 U₁.cpu.gpr W₄ hmU h12U h14U (Or.inr ⟨h0, Z₄, hP4⟩)) (k3 W₄) hdl
      (fun Z₂ W₂ Z₃ W₃ h2 h3 => kr Z W hP1 W₄ Z₂ W₂ Z₃ W₃ h2 h3)
  · -- `al` not 0: 33
    refine (c_26 prof).run c hin (fun j' g' _ V' => j' = 33 ∧ g' = g26 Z.cpu.gpr ∧ V' = W) hKZ hAZ hrZ
      (vc_26n h0) ?_
    rintro j' g fl V₁ ⟨rfl, hg, hV₁⟩ U t₄ hKU hAU hrU hgU -
    subst g V₁
    have hmU : Fm X.cpu.gpr.rsp X.cpu.gpr U.cpu.gpr := by rw [hgU]; exact hmZ
    have h12U : U.cpu.gpr.r12 = BitVec.setWidth 64 (BitVec.setWidth 32 Z.cpu.gpr.rax) :=
      (congrArg Gprs.r12 hgU).trans rfl
    have h14U : U.cpu.gpr.r14 = X.cpu.gpr.r14 := (congrArg Gprs.r14 hgU).trans h14Z
    exact from33 (P2 := P2) (P3 := P3) (S := X.cpu.gpr.rsp) (g0 := X.cpu.gpr)
      (R := BitVec.setWidth 32 Z.cpu.gpr.rax) c hin hin2 hc2 hin3 hc3 hs6 ft hb8 hb4 hin₂ h₂ hKU hAU
      hrU hmU h12U hst (k2 Z W hP1 U.cpu.gpr W hmU h12U h14U (Or.inl ⟨h0, rfl⟩)) (k3 W) hdl
      (fun Z₂ W₂ Z₃ W₃ h2 h3 => kr Z W hP1 W Z₂ W₂ Z₃ W₃ h2 h3)

end FV7z.Gfs
