import FV7z.Ldd.Cuts
import FV7z.Cpt.Holds
import FV7z.Lemmas.LeafRet
import FV7z.Lemmas.CallM
/-!
# `NCompress::NLzma::CDecoder::~CDecoder` (PLAN.md §M, M1)

7-Zip 26.06's `NCompress::NLzma::CDecoder::~CDecoder ()` at `0x57fc30` in `7zzs`
(`CPP/7zip/Compress/LzmaDecoder.cpp`; `objdump -d`), `this` = `p` in `rdi`, `S` the stack pointer at the entry:
`push rbx; mov rbx, rdi; sub rdi, -0x80` (`rdi` = `p + 128`, `_state`), the 8 vtable pointers of the class's
interfaces back in the 8 bytes at `p + 8 * i` (`D`, the same values as `Ldc.M`), `rsi` = `&g_AlignedAlloc`
(`0x777ae0`); the `call` (110) of `LzmaDec_Free (&_state, &g_AlignedAlloc)` (`0x42be70`, `Ldf.ldf_at`); `rdi` =
`_inBuf` (the 8 bytes at `p + 96`), the `call` (119) of `MidFree` (`0x41f3f0`); `rdi` = `_inStream` (the 8 bytes at
`p + 256`, `sI`), and when it is set `rax` = its vtable (`vt`) and `call qword [rax + 16]` (139, `Seg.s_callM`:
`Release`); `pop rbx; ret` (142, 143).

The callees are hypotheses (`k1`, `k2`, `k3`), as in `FV7z/Cib/Holds.lean` and `FV7z/Ris/Holds.lean`: each a
continuation at its entry, given the run from its return (`Rt`: `rsp` = `S - 8`, `rbx` = `p`, the saved `rbx` at
`S - 8` and the return address at `S` as they were, and the callee's own post `P1`, `P2`, `P3`) to the return
address. The literal displacements of the stores (`-0x80` to `-0x48` from `p + 128`) are folded by `s0`, `d0`–`d7`
(`bv_omega`) inside `wpx`, so no address holds a 64-bit literal.

- `V1`, `D`, `g1`, `sI`, `vt`, `Rt`: the bytes after `push rbx` and the stores, the registers at the first `call`,
  `_inStream` and its vtable, the callees' returns.
- `vc_0`, `vc_115`, `vc_124z`, `vc_124n`, `vc_142`: the pieces' verification conditions.
- `ldd_ok`: from the entry through the callees to the return address (`k0` without `_inStream`, else `kr`).
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Ldd
set_option linter.unusedVariables false

/-! ## The instructions outside the blocks -/

/-- The `call` of `LzmaDec_Free`. -/
def pc1 : List Byte := [0xe8, 0xcd, 0xc1, 0xea, 0xff]
theorem pc1_0 : ∀ feat, Dec feat pc1 0 (FV7z.mk .call 64 [.rel 18446744073708159437] 5) := by dec_rfl
theorem wc_110 : pc1 <+: ldd.drop 110 := by decide +kernel
theorem call_110 (feat : Features) : Dec feat ldd 110 (FV7z.mk .call 64 [.rel 18446744073708159437] 5) :=
  Dec.shift (j := 110) (k := 0) (pc1_0 feat) wc_110 (Nat.zero_le _)
theorem tgt_110 : ldd_at.add (110 + 5) + BitVec.ofNat 64 18446744073708159437 = 0x42be70#64 := by decide

/-- The `call` of `MidFree`. -/
def pc2 : List Byte := [0xe8, 0x44, 0xf7, 0xe9, 0xff]
theorem pc2_0 : ∀ feat, Dec feat pc2 0 (FV7z.mk .call 64 [.rel 18446744073708107588] 5) := by dec_rfl
theorem wc_119 : pc2 <+: ldd.drop 119 := by decide +kernel
theorem call_119 (feat : Features) : Dec feat ldd 119 (FV7z.mk .call 64 [.rel 18446744073708107588] 5) :=
  Dec.shift (j := 119) (k := 0) (pc2_0 feat) wc_119 (Nat.zero_le _)
theorem tgt_119 : ldd_at.add (119 + 5) + BitVec.ofNat 64 18446744073708107588 = 0x41f3f0#64 := by decide

/-- The `call` through the vtable. -/
def pc3 : List Byte := [0xff, 0x50, 0x10]
theorem pc3_0 : ∀ feat, Dec feat pc3 0 (FV7z.mk .call 64 [.mem (mbd 0 16 64)] 3) := by dec_rfl
theorem wc_139 : pc3 <+: ldd.drop 139 := by decide +kernel
theorem call_139 (feat : Features) : Dec feat ldd 139 (FV7z.mk .call 64 [.mem (mbd 0 16 64)] 3) :=
  Dec.shift (j := 139) (k := 0) (pc3_0 feat) wc_139 (Nat.zero_le _)

/-- The `ret`. -/
def pret : List Byte := [0xc3]
theorem pret_0 : ∀ feat, Dec feat pret 0 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem w_143 : pret <+: ldd.drop 143 := by decide +kernel
theorem ret_143 (feat : Features) : Dec feat ldd 143 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 143) (k := 0) (pret_0 feat) w_143 (Nat.zero_le _)

/-! ## The displacements from `p + 128` -/

theorem s0 (p : Addr) : p - 18446744073709551488#64 = p + 128#64 := by bv_omega
theorem d0 (p : Addr) : p + 128#64 + 18446744073709551488#64 = p := by bv_omega
theorem d1 (p : Addr) : p + 128#64 + 18446744073709551496#64 = p + 8#64 := by bv_omega
theorem d2 (p : Addr) : p + 128#64 + 18446744073709551504#64 = p + 16#64 := by bv_omega
theorem d3 (p : Addr) : p + 128#64 + 18446744073709551512#64 = p + 24#64 := by bv_omega
theorem d4 (p : Addr) : p + 128#64 + 18446744073709551520#64 = p + 32#64 := by bv_omega
theorem d5 (p : Addr) : p + 128#64 + 18446744073709551528#64 = p + 40#64 := by bv_omega
theorem d6 (p : Addr) : p + 128#64 + 18446744073709551536#64 = p + 48#64 := by bv_omega
theorem d7 (p : Addr) : p + 128#64 + 18446744073709551544#64 = p + 56#64 := by bv_omega
theorem m16 (x : Addr) : x - 8 - 8 = x - 16 := by bv_omega

/-! ## Bytes, registers, contracts -/

/-- The bytes after `push rbx`. -/
abbrev V1 (V : Addr → Byte) (g : Gprs) : Addr → Byte := Vst V (g.rsp - 8) (toBytesLE g.rbx 8)

/-- The 8 vtable pointers stored into the object at `p`, in their order. -/
abbrev D (W : Addr → Byte) (p : Addr) : Addr → Byte :=
  Vst (Vst (Vst (Vst (Vst (Vst (Vst (Vst W
    p (toBytesLE 7914664#64 8))
    (p + 8#64) (toBytesLE 7914784#64 8))
    (p + 16#64) (toBytesLE 7914832#64 8))
    (p + 24#64) (toBytesLE 7914880#64 8))
    (p + 32#64) (toBytesLE 7914928#64 8))
    (p + 40#64) (toBytesLE 7914984#64 8))
    (p + 48#64) (toBytesLE 7915040#64 8))
    (p + 56#64) (toBytesLE 7915088#64 8)

/-- The registers at the first `call` (`rax`, `rdx` as the stores left them). -/
abbrev g1 (g : Gprs) (a d : BitVec 64) : Gprs :=
  { g with rax := a, rdx := d, rbx := g.rdi, rsp := g.rsp - 8, rsi := 7830240#64, rdi := g.rdi + 128#64 }

/-- `_inStream`, from the bytes `V`. -/
abbrev sI (V : Addr → Byte) (p : Addr) : Addr := rdq(V, p + 256#64)
/-- Its vtable. -/
abbrev vt (V : Addr → Byte) (p : Addr) : Addr := rdq(V, sI V p)

/-- A callee's return (`g0` the registers at the entry, `ra` the return address): `rsp` 8 below the entry's, `rbx` =
`this`, the saved `rbx` and the return address as they were. -/
abbrev Rt (g0 : Gprs) (ra : Addr) (Z : State) (W : Addr → Byte) : Prop :=
  Z.cpu.gpr.rsp = g0.rsp - 8 ∧ Z.cpu.gpr.rbx = g0.rdi ∧ rdq(W, g0.rsp - 8) = g0.rbx ∧ rdq(W, g0.rsp) = ra

/-! ## The pieces -/

variable {F : Footprint} {Wl : List Rgn}

/-- `push rbx`, the 8 vtable pointers, to the first `call`. -/
theorem vc_0 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (hs1 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8) i)) (hw : ∀ i < 64, Foot Wl (Addr.add g.rdi i))
    (h : ∀ (a d : BitVec 64) fl, Q 110 (g1 g a d) fl (D (V1 V g) g.rdi)) :
    W_0 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [g1, D, V1] at hs1 hw h ⊢
  have w0 : ∀ i < 8, Foot Wl (Addr.add rdi i) := Cpt.off_ft hw 0 (BitVec.add_zero _).symm (by decide)
  have w8 : ∀ i < 8, Foot Wl (Addr.add (rdi + 8#64) i) := Cpt.off_ft hw 8 rfl (by decide)
  have w16 : ∀ i < 8, Foot Wl (Addr.add (rdi + 16#64) i) := Cpt.off_ft hw 16 rfl (by decide)
  have w24 : ∀ i < 8, Foot Wl (Addr.add (rdi + 24#64) i) := Cpt.off_ft hw 24 rfl (by decide)
  have w32 : ∀ i < 8, Foot Wl (Addr.add (rdi + 32#64) i) := Cpt.off_ft hw 32 rfl (by decide)
  have w40 : ∀ i < 8, Foot Wl (Addr.add (rdi + 40#64) i) := Cpt.off_ft hw 40 rfl (by decide)
  have w48 : ∀ i < 8, Foot Wl (Addr.add (rdi + 48#64) i) := Cpt.off_ft hw 48 rfl (by decide)
  have w56 : ∀ i < 8, Foot Wl (Addr.add (rdi + 56#64) i) := Cpt.off_ft hw 56 rfl (by decide)
  wpx [W_0, o0, s0, d0, d1, d2, d3, d4, d5, d6, d7, BitVec.reduceAdd]
  all_goals repeat' (first
    | refine h _ _ _
    | with_reducible assumption
    | apply And.intro
    | intro _)

/-- `mov rdi, [rbx + 96]`, to the second `call`. -/
theorem vc_115 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (f96 : ∀ i < 8, Foot F.data (Addr.add (g.rbx + 96#64) i))
    (h : ∀ fl, Q 119 { g with rdi := rdq(V, g.rbx + 96#64) } fl V) :
    W_115 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at f96 h ⊢
  wpx [W_115, o1]
  all_goals repeat' (first
    | exact h _
    | with_reducible assumption
    | apply And.intro
    | intro _)

/-- `_inStream` not set: `mov rdi, [rbx + 256]; test rdi, rdi; je` taken, to 142. -/
theorem vc_124z {g : Gprs} {f : Rflags} {V : Addr → Byte} (h : sI V g.rbx = 0)
    (f256 : ∀ i < 8, Foot F.data (Addr.add (g.rbx + 256#64) i)) :
    W_124 F Wl (fun j' g' _ V' => j' = 142 ∧ g' = { g with rdi := 0#64 } ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [sI] at h f256 ⊢
  wpx [W_124, W_136, o2, o3, h, BitVec.and_self, beq_iff_eq, beq_eq_false_iff_ne, ne_eq, beq_self_eq_true,
    not_true_eq_false, not_false_eq_true, false_implies, Bool.true_eq_false, Bool.false_eq_true, implies_true]
  all_goals repeat' (first
    | with_reducible assumption
    | exact ⟨rfl, rfl, rfl⟩
    | exact ⟨rfl, rfl⟩
    | with_reducible rfl
    | exact fun hh => absurd hh (by decide)
    | apply And.intro
    | intro _
    | exact rfl)

/-- `_inStream` set: `je` not taken, `mov rax, [rdi]`, to the `call` through the vtable. -/
theorem vc_124n {g : Gprs} {f : Rflags} {V : Addr → Byte} (h : ¬sI V g.rbx = 0)
    (f256 : ∀ i < 8, Foot F.data (Addr.add (g.rbx + 256#64) i))
    (fs : ∀ i < 8, Foot F.data (Addr.add (sI V g.rbx) i)) :
    W_124 F Wl (fun j' g' _ V' => j' = 139 ∧ g' = { g with rax := vt V g.rbx, rdi := sI V g.rbx } ∧ V' = V)
      g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [vt, sI] at h f256 fs ⊢
  wpx [W_124, W_136, o2, o3, h, BitVec.and_self, beq_iff_eq, beq_eq_false_iff_ne, ne_eq,
    not_true_eq_false, not_false_eq_true, false_implies, Bool.true_eq_false, Bool.false_eq_true, implies_true]
  all_goals repeat' (first
    | with_reducible assumption
    | exact ⟨rfl, rfl, rfl⟩
    | exact ⟨rfl, rfl⟩
    | with_reducible rfl
    | exact fun hh => absurd hh h
    | exact fun hh => absurd hh (by decide)
    | apply And.intro
    | intro _
    | exact rfl)

/-- `pop rbx`, to the `ret`. -/
theorem vc_142 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (hl : ∀ i < 8, Foot F.data (Addr.add g.rsp i))
    (h : ∀ fl, Q 143 { g with rbx := rdq(V, g.rsp), rsp := g.rsp + 8 } fl V) :
    W_142 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hl h ⊢
  wpx [W_142, o4]
  first
  | exact ⟨hl, h _⟩
  | exact fun _ => ⟨hl, h _⟩
  | (refine ⟨hl, ?_⟩; simpa using h _)
  | exact h _

/-! ## The run -/

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {X : State} {t : Nat} {V : Addr → Byte}

/-- `CDecoder::~CDecoder ()` (`this` = `rdi`) from its entry. At `LzmaDec_Free`'s entry the registers are `g1` with
`rsp` 16 below the entry's and the bytes `D (V1 V)` with the return address pushed (`k1`); from its return at
`ldd_at + 115` (`Rt`, `P1`), at `MidFree`'s entry with `rdi` = `_inBuf` (`k2`); from its return at `ldd_at + 124`
(`Rt`, `P2`): with `_inStream` 0 at the return address with `rdi` = 0 and `rbx`, `rsp` restored (`k0`); else at
`Release`'s entry (the 8 bytes at `vt + 16`, code `hcR`) with `rax` = `vt`, `rdi` = `_inStream` (`k3`), and from its
return at `ldd_at + 142` (`Rt`, `P3`) at the return address with `rbx`, `rsp` restored (`kr`). -/
theorem ldd_ok {P1 P2 P3 : State → (Addr → Byte) → Prop} (c : Seg prof F Wl L s₀ o) (hin : CodeIn L ldd_at ldd)
    {codeF codeM : List Byte} (hinF : CodeIn L 0x42be70#64 codeF) (hF : 0 < codeF.length)
    (hinM : CodeIn L 0x41f3f0#64 codeM) (hM : 0 < codeM.length)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = ldd_at)
    (hs1 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8) i))
    (hs2 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 16) i))
    (hl : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsp i))
    (hw : ∀ i < 64, Foot Wl (Addr.add X.cpu.gpr.rdi i))
    (f96 : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rdi + 96#64) i))
    (f256 : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rdi + 256#64) i))
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (k1 : ∀ (a d : BitVec 64) (Y : State) (t' : Nat), KeptW Wl s₀ Y →
      Agree F Y.proc.mm.mem
        (Vst (D (V1 V X.cpu.gpr) X.cpu.gpr.rdi) (X.cpu.gpr.rsp - 16) (toBytesLE (ldd_at.add 115) 8)) →
      Y.cpu.rip = 0x42be70#64 → Y.cpu.gpr = (g1 X.cpu.gpr a d).set 4 (X.cpu.gpr.rsp - 16) →
      (∀ (Z : State) (V' : Addr → Byte) (t'' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V' →
        Z.cpu.rip = ldd_at.add 115 → Rt X.cpu.gpr (e₂.add j₂) Z V' → P1 Z V' →
        GoG prof L o gev gP gE Z t'') →
      GoG prof L o gev gP gE Y t')
    (k2 : ∀ (Z : State) (V' : Addr → Byte), P1 Z V' → ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y →
      Agree F Y.proc.mm.mem (Vst V' (X.cpu.gpr.rsp - 16) (toBytesLE (ldd_at.add 124) 8)) →
      Y.cpu.rip = 0x41f3f0#64 →
      Y.cpu.gpr = { Z.cpu.gpr with rdi := rdq(V', X.cpu.gpr.rdi + 96#64) }.set 4 (X.cpu.gpr.rsp - 16) →
      (∀ (Z₂ : State) (V'' : Addr → Byte) (t'' : Nat), KeptW Wl s₀ Z₂ → Agree F Z₂.proc.mm.mem V'' →
        Z₂.cpu.rip = ldd_at.add 124 → Rt X.cpu.gpr (e₂.add j₂) Z₂ V'' → P2 Z₂ V'' →
        GoG prof L o gev gP gE Z₂ t'') →
      GoG prof L o gev gP gE Y t')
    (k0 : ∀ (Z₂ : State) (V'' : Addr → Byte) (Z' : State) (t' : Nat), P2 Z₂ V'' → sI V'' X.cpu.gpr.rdi = 0 →
      KeptW Wl s₀ Z' → Agree F Z'.proc.mm.mem V'' → Z'.cpu.rip = e₂.add j₂ →
      Z'.cpu.gpr = { Z₂.cpu.gpr with rdi := 0#64, rbx := X.cpu.gpr.rbx, rsp := X.cpu.gpr.rsp }.set 4
        (X.cpu.gpr.rsp + 8) →
      GoG prof L o gev gP gE Z' t')
    (fs : ∀ (Z₂ : State) (V'' : Addr → Byte), P2 Z₂ V'' → ¬sI V'' X.cpu.gpr.rdi = 0 →
      ∀ i < 8, Foot F.data (Addr.add (sI V'' X.cpu.gpr.rdi) i))
    (fb : ∀ (Z₂ : State) (V'' : Addr → Byte), P2 Z₂ V'' → ¬sI V'' X.cpu.gpr.rdi = 0 →
      ∀ i < 8, Foot F.data (Addr.add (vt V'' X.cpu.gpr.rdi + 16#64) i))
    (hcR : ∀ (Z₂ : State) (V'' : Addr → Byte), P2 Z₂ V'' → ¬sI V'' X.cpu.gpr.rdi = 0 →
      ∃ codeR : List Byte, CodeIn L rdq(V'', vt V'' X.cpu.gpr.rdi + 16#64) codeR ∧ 0 < codeR.length)
    (k3 : ∀ (Z₂ : State) (V'' : Addr → Byte), P2 Z₂ V'' → ¬sI V'' X.cpu.gpr.rdi = 0 →
      ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y →
      Agree F Y.proc.mm.mem (Vst V'' (X.cpu.gpr.rsp - 16) (toBytesLE (ldd_at.add 142) 8)) →
      Y.cpu.rip = rdq(V'', vt V'' X.cpu.gpr.rdi + 16#64) →
      Y.cpu.gpr = { Z₂.cpu.gpr with rax := vt V'' X.cpu.gpr.rdi, rdi := sI V'' X.cpu.gpr.rdi }.set 4
        (X.cpu.gpr.rsp - 16) →
      (∀ (Z₃ : State) (V₃ : Addr → Byte) (t'' : Nat), KeptW Wl s₀ Z₃ → Agree F Z₃.proc.mm.mem V₃ →
        Z₃.cpu.rip = ldd_at.add 142 → Rt X.cpu.gpr (e₂.add j₂) Z₃ V₃ → P3 Z₃ V₃ →
        GoG prof L o gev gP gE Z₃ t'') →
      GoG prof L o gev gP gE Y t')
    (kr : ∀ (Z₃ : State) (V₃ : Addr → Byte) (Z' : State) (t' : Nat), P3 Z₃ V₃ → KeptW Wl s₀ Z' →
      Agree F Z'.proc.mm.mem V₃ → Z'.cpu.rip = e₂.add j₂ →
      Z'.cpu.gpr = { Z₃.cpu.gpr with rbx := X.cpu.gpr.rbx, rsp := X.cpu.gpr.rsp }.set 4 (X.cpu.gpr.rsp + 8) →
      GoG prof L o gev gP gE Z' t') :
    GoG prof L o gev gP gE X t := by
  have e16 : X.cpu.gpr.rsp - 8 - 8 = X.cpu.gpr.rsp - 16 := m16 _
  have e8 : X.cpu.gpr.rsp - 8 + 8 = X.cpu.gpr.rsp := BitVec.sub_add_cancel _ _
  have h8 : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rsp - 8) i) := fun i hi => c.hws _ (hs1 i hi)
  -- from 142: `pop rbx; ret`
  have tail : ∀ (Z : State) (W : Addr → Byte) (t₀ : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem W →
      Z.cpu.rip = ldd_at.add 142 → Z.cpu.gpr.rsp = X.cpu.gpr.rsp - 8 → rdq(W, X.cpu.gpr.rsp - 8) = X.cpu.gpr.rbx →
      rdq(W, X.cpu.gpr.rsp) = e₂.add j₂ →
      (∀ (Z' : State) (t' : Nat), KeptW Wl s₀ Z' → Agree F Z'.proc.mm.mem W → Z'.cpu.rip = e₂.add j₂ →
        Z'.cpu.gpr = { Z.cpu.gpr with rbx := X.cpu.gpr.rbx, rsp := X.cpu.gpr.rsp }.set 4 (X.cpu.gpr.rsp + 8) →
        GoG prof L o gev gP gE Z' t') → GoG prof L o gev gP gE Z t₀ := by
    intro Z W t₀ hKZ hAZ hrZ hzs hb hr kk
    refine (c_142 prof).run c hin (fun j' g' _ V' => j' = 143 ∧
        g' = { Z.cpu.gpr with rbx := X.cpu.gpr.rbx, rsp := X.cpu.gpr.rsp } ∧ V' = W) hKZ hAZ hrZ
      (vc_142 (by rw [hzs]; exact h8) fun _ => ⟨rfl, by rw [hzs, hb, e8], rfl⟩) ?_
    rintro j' g fl V₁ ⟨rfl, rfl, hV₁⟩ U t₁ hKU hAU hrU hgU -
    subst V₁
    have hsU : U.cpu.gpr.rsp = X.cpu.gpr.rsp := by rw [hgU]
    refine c.s_ret hKU hAU hin (lt_len (by decide)) hrU (ret_143 _) (by rw [hsU]; exact hl) hin₂ h₂
      (by rw [hsU]; exact hr) ?_
    rintro Z' t₂ hKZ' hAZ' ⟨hrZ', hgZ'⟩
    exact kk Z' t₂ hKZ' hAZ' hrZ' (by rw [hgZ', hsU, hgU])
  -- to the first `call`
  refine (c_0 prof).run c hin (fun j' g' _ V' => j' = 110 ∧ (∃ a d, g' = g1 X.cpu.gpr a d) ∧
      V' = D (V1 V X.cpu.gpr) X.cpu.gpr.rdi) hK hA (by rw [addr_add_zero]; exact hrip)
    (vc_0 hs1 hw fun a d _ => ⟨rfl, ⟨a, d, rfl⟩, rfl⟩) ?_
  rintro j' g fl V₁ ⟨rfl, ⟨a, d, rfl⟩, hV₁⟩ Y t₁ hKY hAY hrY hgY -
  subst V₁
  have hsY : Y.cpu.gpr.rsp = X.cpu.gpr.rsp - 8 := by rw [hgY]
  have hst : ∀ i < 8, Foot Wl (Addr.add (Y.cpu.gpr.rsp - 8) i) := by rw [hsY, e16]; exact hs2
  refine c.s_call hKY hAY hin (lt_len (by decide)) hrY (call_110 _) hinF hF tgt_110 hst ?_
  rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
  rw [hsY, e16] at hA₂
  have hg₂' : Y₂.cpu.gpr = (g1 X.cpu.gpr a d).set 4 (X.cpu.gpr.rsp - 16) := by
    rw [hg₂, hgY]
    exact congrArg (fun v => (g1 X.cpu.gpr a d).set 4 v) e16
  refine k1 a d Y₂ t₂ hK₂ hA₂ hr₂ hg₂' ?_
  -- back from `LzmaDec_Free`: `rdi` = `_inBuf`, the `call` of `MidFree`
  rintro Z V' t₃ hKZ hAZ hrZ ⟨hzs, hzb, -, -⟩ hP1
  refine (c_115 prof).run c hin (fun j' g' _ V'' => j' = 119 ∧
      g' = { Z.cpu.gpr with rdi := rdq(V', X.cpu.gpr.rdi + 96#64) } ∧ V'' = V') hKZ hAZ hrZ
    (vc_115 (by rw [hzb]; exact f96) fun _ => ⟨rfl, by simp only [hzb], rfl⟩) ?_
  rintro j' g fl V₂ ⟨rfl, rfl, hV₂⟩ Y₃ t₄ hK₃ hA₃ hr₃ hg₃ -
  subst V₂
  have hs3 : Y₃.cpu.gpr.rsp = X.cpu.gpr.rsp - 8 := by rw [hg₃]; exact hzs
  have hst3 : ∀ i < 8, Foot Wl (Addr.add (Y₃.cpu.gpr.rsp - 8) i) := by rw [hs3, e16]; exact hs2
  refine c.s_call hK₃ hA₃ hin (lt_len (by decide)) hr₃ (call_119 _) hinM hM tgt_119 hst3 ?_
  rintro Y₄ t₅ hK₄ hA₄ ⟨hr₄, hg₄⟩
  rw [hs3, e16] at hA₄
  refine k2 Z V' hP1 Y₄ t₅ hK₄ hA₄ hr₄ (by rw [hg₄, hs3, e16, hg₃]) ?_
  -- back from `MidFree`: `_inStream`
  rintro Z₂ V'' t₆ hK₅ hA₅ hr₅ ⟨hz2s, hz2b, hb₂, hr₂'⟩ hP2
  by_cases hs : sI V'' X.cpu.gpr.rdi = 0
  · refine (c_124 prof).run c hin
      (fun j' g' _ V₃ => j' = 142 ∧ g' = { Z₂.cpu.gpr with rdi := 0#64 } ∧ V₃ = V'')
      hK₅ hA₅ hr₅ (vc_124z (by rw [hz2b]; exact hs) (by rw [hz2b]; exact f256)) ?_
    rintro j' g fl V₃ ⟨rfl, rfl, hV₃⟩ U t₇ hKU hAU hrU hgU -
    subst V₃
    refine tail U V'' t₇ hKU hAU hrU (by rw [hgU]; exact hz2s) hb₂ hr₂' ?_
    intro Z' t' a b d e
    refine k0 Z₂ V'' Z' t' hP2 hs a b d ?_
    rw [e, hgU]
    try rfl
  · refine (c_124 prof).run c hin (fun j' g' _ V₃ => j' = 139 ∧
        g' = { Z₂.cpu.gpr with rax := vt V'' Z₂.cpu.gpr.rbx, rdi := sI V'' Z₂.cpu.gpr.rbx } ∧ V₃ = V'')
      hK₅ hA₅ hr₅ (vc_124n (by rw [hz2b]; exact hs) (by rw [hz2b]; exact f256)
        (by rw [hz2b]; exact fs Z₂ V'' hP2 hs)) ?_
    rintro j' g fl V₃ ⟨rfl, rfl, hV₃⟩ U t₇ hKU hAU hrU hgU -
    subst V₃
    have hsU : U.cpu.gpr.rsp = X.cpu.gpr.rsp - 8 := by rw [hgU]; exact hz2s
    have he : eaD U 0 16 = vt V'' X.cpu.gpr.rdi + 16#64 := by
      show U.cpu.gpr.get (regOf 0) + BitVec.ofNat 64 16 = _
      rw [hgU, hz2b]
      try rfl
    have hst4 : ∀ i < 8, Foot Wl (Addr.add (U.cpu.gpr.rsp - 8) i) := by rw [hsU, e16]; exact hs2
    obtain ⟨codeR, hinR, hR⟩ := hcR Z₂ V'' hP2 hs
    refine c.s_callM hKU hAU hin (lt_len (by decide)) hrU (call_139 _) (by rw [he]; exact fb Z₂ V'' hP2 hs)
      hinR hR (by rw [he]) hst4 ?_
    rintro Y₅ t₈ hK₆ hA₆ ⟨hr₆, hg₆⟩
    rw [hsU, e16] at hA₆
    refine k3 Z₂ V'' hP2 hs Y₅ t₈ hK₆ hA₆ hr₆ ?_ ?_
    · rw [hg₆, hsU, e16, hgU, hz2b]
    · rintro Z₃ V₃ t₉ hK₇ hA₇ hr₇ ⟨hz3s, -, hb₃, hr₃⟩ hP3
      exact tail Z₃ V₃ t₉ hK₇ hA₇ hr₇ hz3s hb₃ hr₃ fun Z' t' a b d e => kr Z₃ V₃ Z' t' hP3 a b d e

end FV7z.Ldd
