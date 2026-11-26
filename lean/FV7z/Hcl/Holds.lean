import FV7z.Hcl.Cuts
import FV7z.Lemmas.LeafRet
import FV7z.Lemmas.CallM
import FV7z.Tun.Inv
/-!
# `NArchive::NLzma::CHandler::Close` (PLAN.md §M, M1)

7-Zip 26.06's `NArchive::NLzma::CHandler::Close ()` at `0x49ea60` in `7zzs` (`CPP/7zip/Archive/LzmaHandler.cpp`;
`objdump -d`): the flags and sizes at `this + 21`, `+ 29`, `+ 64` cleared, then `_seqStream.Release ()` and
`_stream.Release ()` (the 8 bytes at `this + 48` and `this + 56`, each through its vtable's entry at 16 when set, and
then set to 0), `return S_OK`. `push rbx`, `rbx` = `this`; the stores; `rdi` = `_seqStream`; if it is set,
`call qword [rax + 16]` (40, `Seg.s_callM`) and `_seqStream` = 0 (43). Where the two ways meet (51): `rdi` =
`_stream`; if it is set, `call qword [rax + 16]` (63) and `_stream` = 0 (66); `xor eax, eax; pop rbx; ret` (74 to 77).

The two calls are each a hypothesis (`kf`), as in `FV7z.Ris`. The memory at the second call is what the first callee
left, so the run is cut where the two ways meet (51):

- `hcl_ok`: from the entry to 51 (`kM`), through the first callee when `_seqStream` is set.
- `hcl_mid`: from 51 (any state there with `rsp` 8 below `S`, the saved `rbx` at `S - 8` and the return address at
  `S`, as `kM` gives) through the second callee when `_stream` is set, to the return address with `rax` 0.

- `V0`: the bytes after `push rbx` and the stores; `sq`, `vt1`, `gC1`: `_seqStream`, its vtable and the registers at
  the first `call`; `s2`, `vt2`, `gC2`: `_stream`, its vtable and the registers at the second `call`.
- `vc_0z`, `vc_0n`, `vc_43`, `vc_51z`, `vc_51n`, `vc_66`, `vc_74`: the verification conditions of the pieces.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Hcl

/-- The `call`s through the vtables. -/
def pcall : List Byte := [0xff, 0x50, 0x10]
theorem pcall_0 : ∀ feat, Dec feat pcall 0 (FV7z.mk .call 64 [.mem (mbd 0 16 64)] 3) := by dec_rfl
theorem wc_40 : pcall <+: hcl.drop 40 := by decide +kernel
theorem call_40 (feat : Features) : Dec feat hcl 40 (FV7z.mk .call 64 [.mem (mbd 0 16 64)] 3) :=
  Dec.shift (j := 40) (k := 0) (pcall_0 feat) wc_40 (Nat.zero_le _)
theorem wc_63 : pcall <+: hcl.drop 63 := by decide +kernel
theorem call_63 (feat : Features) : Dec feat hcl 63 (FV7z.mk .call 64 [.mem (mbd 0 16 64)] 3) :=
  Dec.shift (j := 63) (k := 0) (pcall_0 feat) wc_63 (Nat.zero_le _)

/-- The `ret`. -/
def pret : List Byte := [0xc3]
theorem pret_0 : ∀ feat, Dec feat pret 0 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem w_77 : pret <+: hcl.drop 77 := by decide +kernel
theorem ret_77 (feat : Features) : Dec feat hcl 77 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 77) (k := 0) (pret_0 feat) w_77 (Nat.zero_le _)

/-- The bytes after `push rbx` and the stores into `this + 21`, `+ 29`, `+ 64`. -/
abbrev V0 (V : Addr → Byte) (g : Gprs) : Addr → Byte :=
  Vst (Vst (Vst (Vst V (g.rsp - 8) (toBytesLE g.rbx 8)) (g.rdi + 21#64) (toBytesLE 0#64 8)) (g.rdi + 29#64)
    (toBytesLE 0#8 1)) (g.rdi + 64#64) (toBytesLE 0#64 8)
/-- `_seqStream`, read from `V0`. -/
abbrev sq (V : Addr → Byte) (g : Gprs) : Addr := rdq(V0 V g, g.rdi + 48#64)
/-- Its vtable. -/
abbrev vt1 (V : Addr → Byte) (g : Gprs) : Addr := rdq(V0 V g, sq V g)
/-- The registers at the first `call`. -/
abbrev gC1 (V : Addr → Byte) (g : Gprs) : Gprs :=
  { g with rax := vt1 V g, rbx := g.rdi, rsp := g.rsp - 8, rdi := sq V g }
/-- `_stream` (`rbx` = `this` at 51). -/
abbrev s2 (V : Addr → Byte) (g : Gprs) : Addr := rdq(V, g.rbx + 56#64)
/-- Its vtable. -/
abbrev vt2 (V : Addr → Byte) (g : Gprs) : Addr := rdq(V, s2 V g)
/-- The registers at the second `call`. -/
abbrev gC2 (V : Addr → Byte) (g : Gprs) : Gprs := { g with rax := vt2 V g, rdi := s2 V g }

theorem t8 (S : Addr) (h : 8 ≤ S.toNat) : (S - 8).toNat = S.toNat - 8 := by bv_omega
theorem b16 (S : Addr) : S - 8 - 8 = S - 16 := by bv_omega

variable {F : Footprint} {Wl : List Rgn}

/-- `_seqStream` not set: `push rbx; mov rbx, rdi`, the stores, `mov rdi, [rdi + 48]; test rdi, rdi; je` taken. -/
theorem vc_0z {g : Gprs} {f : Rflags} {V : Addr → Byte} (h : sq V g = 0)
    (hst : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8) i)) (w21 : ∀ i < 8, Foot Wl (Addr.add (g.rdi + 21#64) i))
    (w29 : ∀ i < 1, Foot Wl (Addr.add (g.rdi + 29#64) i)) (w64 : ∀ i < 8, Foot Wl (Addr.add (g.rdi + 64#64) i))
    (fa : ∀ i < 8, Foot F.data (Addr.add (g.rdi + 48#64) i)) :
    W_0 F Wl (fun j' g' _ V' => j' = 51 ∧ g' = { g with rbx := g.rdi, rsp := g.rsp - 8, rdi := 0#64 } ∧
      V' = V0 V g) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [sq, V0] at h hst w21 w29 w64 fa ⊢
  wpx [W_0, W_37, o0, o1, h, BitVec.and_self, beq_iff_eq, beq_eq_false_iff_ne, ne_eq, beq_self_eq_true,
    not_true_eq_false, not_false_eq_true, false_implies, Bool.true_eq_false, Bool.false_eq_true, implies_true]
  all_goals repeat' (first
    | exact rfl
    | assumption
    | exact trivial
    | (intro hh; exact absurd hh (by decide))
    | apply And.intro
    | intro _)

/-- `_seqStream` set: `je` not taken, `mov rax, [rdi]`, up to the first `call`. -/
theorem vc_0n {g : Gprs} {f : Rflags} {V : Addr → Byte} (h : sq V g ≠ 0)
    (hst : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8) i)) (w21 : ∀ i < 8, Foot Wl (Addr.add (g.rdi + 21#64) i))
    (w29 : ∀ i < 1, Foot Wl (Addr.add (g.rdi + 29#64) i)) (w64 : ∀ i < 8, Foot Wl (Addr.add (g.rdi + 64#64) i))
    (fa : ∀ i < 8, Foot F.data (Addr.add (g.rdi + 48#64) i)) (fs : ∀ i < 8, Foot F.data (Addr.add (sq V g) i)) :
    W_0 F Wl (fun j' g' _ V' => j' = 40 ∧ g' = gC1 V g ∧ V' = V0 V g) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [gC1, vt1, sq, V0] at h hst w21 w29 w64 fa fs ⊢
  wpx [W_0, W_37, o0, o1, h, BitVec.and_self, beq_iff_eq, beq_eq_false_iff_ne, ne_eq,
    not_true_eq_false, not_false_eq_true, false_implies, Bool.true_eq_false, Bool.false_eq_true, implies_true]
  all_goals repeat' (first
    | exact rfl
    | assumption
    | exact trivial
    | (intro hh; exact absurd hh h)
    | apply And.intro
    | intro _)

/-- `mov qword [rbx + 48], 0`. -/
theorem vc_43 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (hw : ∀ i < 8, Foot Wl (Addr.add (g.rbx + 48#64) i))
    (h : ∀ fl, Q 51 g fl (Vst V (g.rbx + 48#64) (toBytesLE 0#64 8))) :
    W_43 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hw h ⊢
  wpx [W_43, o2]
  first
  | exact ⟨hw, h _⟩
  | (refine ⟨hw, ?_⟩; simpa using h _)

/-- `_stream` not set: `mov rdi, [rbx + 56]; test rdi, rdi; je` taken. -/
theorem vc_51z {g : Gprs} {f : Rflags} {V : Addr → Byte} (h : s2 V g = 0)
    (fa : ∀ i < 8, Foot F.data (Addr.add (g.rbx + 56#64) i)) :
    W_51 F Wl (fun j' g' _ V' => j' = 74 ∧ g' = { g with rdi := 0#64 } ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [s2] at h fa ⊢
  wpx [W_51, W_60, o3, o1, h, BitVec.and_self, beq_iff_eq, beq_eq_false_iff_ne, ne_eq, beq_self_eq_true,
    not_true_eq_false, not_false_eq_true, false_implies, Bool.true_eq_false, Bool.false_eq_true, implies_true]
  all_goals repeat' (first
    | exact rfl
    | assumption
    | exact trivial
    | (intro hh; exact absurd hh (by decide))
    | apply And.intro
    | intro _)

/-- `_stream` set: `je` not taken, `mov rax, [rdi]`, up to the second `call`. -/
theorem vc_51n {g : Gprs} {f : Rflags} {V : Addr → Byte} (h : s2 V g ≠ 0)
    (fa : ∀ i < 8, Foot F.data (Addr.add (g.rbx + 56#64) i)) (fs : ∀ i < 8, Foot F.data (Addr.add (s2 V g) i)) :
    W_51 F Wl (fun j' g' _ V' => j' = 63 ∧ g' = gC2 V g ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [gC2, vt2, s2] at h fa fs ⊢
  wpx [W_51, W_60, o3, o1, h, BitVec.and_self, beq_iff_eq, beq_eq_false_iff_ne, ne_eq,
    not_true_eq_false, not_false_eq_true, false_implies, Bool.true_eq_false, Bool.false_eq_true, implies_true]
  all_goals repeat' (first
    | exact rfl
    | assumption
    | exact trivial
    | (intro hh; exact absurd hh h)
    | apply And.intro
    | intro _)

/-- `mov qword [rbx + 56], 0`. -/
theorem vc_66 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (hw : ∀ i < 8, Foot Wl (Addr.add (g.rbx + 56#64) i))
    (h : ∀ fl, Q 74 g fl (Vst V (g.rbx + 56#64) (toBytesLE 0#64 8))) :
    W_66 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hw h ⊢
  wpx [W_66, o4]
  first
  | exact ⟨hw, h _⟩
  | (refine ⟨hw, ?_⟩; simpa using h _)

/-- `xor eax, eax; pop rbx`. -/
theorem vc_74 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (hl : ∀ i < 8, Foot F.data (Addr.add g.rsp i))
    (h : ∀ fl, Q 77 { g with rax := 0#64, rbx := rdq(V, g.rsp), rsp := g.rsp + 8 } fl V) :
    W_74 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hl h ⊢
  wpx [W_74, o5, BitVec.xor_self, BitVec.setWidth_zero]
  first
  | exact fun _ => ⟨hl, h _⟩
  | exact ⟨hl, h _⟩
  | exact ⟨by simpa using hl, h _⟩
  | (refine ⟨hl, ?_⟩; simpa using h _)
  | (refine ⟨?_, ?_⟩; (simpa using hl); simpa using h _)
  | exact h _

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {X : State} {t : Nat} {V : Addr → Byte}

/-- `CHandler::Close ()` (`this` = `rdi`) from its entry to where the two ways meet (51, `kM`): `rsp` 8 below the
entry's, `rbx` = `this`, the saved `rbx` and the return address as they were (`hb0`, `hr0` for the bytes `V0`), and
either `_seqStream` (`sq`) not set and the bytes `V0`, or the run through its `Release`: at the callee's entry `eF`
the registers `gC1` with `rsp` 16 below the entry's and the bytes `V0` with the return address into `Close` pushed
(`kf`); the callee returns to `hcl_at + 43` with `rsp`, `rbx`, the saved `rbx` and the return address as they were
and its own post `Pc`, and then `_seqStream` = 0. -/
theorem hcl_ok {Pc : State → (Addr → Byte) → Prop} (c : Seg prof F Wl L s₀ o) (hin : CodeIn L hcl_at hcl)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = hcl_at)
    (hp : 16 ≤ X.cpu.gpr.rsp.toNat) (hp8 : X.cpu.gpr.rsp.toNat + 8 ≤ 2 ^ 64)
    (hs1 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8) i))
    (w21 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rdi + 21#64) i))
    (w29 : ∀ i < 1, Foot Wl (Addr.add (X.cpu.gpr.rdi + 29#64) i))
    (w64 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rdi + 64#64) i))
    (fa : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rdi + 48#64) i))
    (hq : (X.cpu.gpr.rdi + 48#64).toNat + 8 ≤ 2 ^ 64)
    (hdp : (X.cpu.gpr.rdi + 48#64).toNat + 8 ≤ X.cpu.gpr.rsp.toNat - 8 ∨
      X.cpu.gpr.rsp.toNat + 8 ≤ (X.cpu.gpr.rdi + 48#64).toNat)
    {e₂ : Addr} (hb0 : rdq(V0 V X.cpu.gpr, X.cpu.gpr.rsp - 8) = X.cpu.gpr.rbx)
    (hr0 : rdq(V0 V X.cpu.gpr, X.cpu.gpr.rsp) = e₂)
    (kM : ∀ (Z : State) (V' : Addr → Byte) (t' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V' →
      Z.cpu.rip = hcl_at.add 51 → Z.cpu.gpr.rsp = X.cpu.gpr.rsp - 8 → Z.cpu.gpr.rbx = X.cpu.gpr.rdi →
      rdq(V', X.cpu.gpr.rsp - 8) = X.cpu.gpr.rbx → rdq(V', X.cpu.gpr.rsp) = e₂ →
      ((sq V X.cpu.gpr = 0 ∧ V' = V0 V X.cpu.gpr ∧
          Z.cpu.gpr = { X.cpu.gpr with rbx := X.cpu.gpr.rdi, rsp := X.cpu.gpr.rsp - 8, rdi := 0#64 }) ∨
        (∃ (Zc : State) (Vc : Addr → Byte), Pc Zc Vc ∧
          V' = Vst Vc (X.cpu.gpr.rdi + 48#64) (toBytesLE 0#64 8) ∧ Z.cpu.gpr = Zc.cpu.gpr)) →
      GoG prof L o gev gP gE Z t')
    (hs2 : sq V X.cpu.gpr ≠ 0 → ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 16) i))
    (fs : sq V X.cpu.gpr ≠ 0 → ∀ i < 8, Foot F.data (Addr.add (sq V X.cpu.gpr) i))
    (fb : sq V X.cpu.gpr ≠ 0 → ∀ i < 8, Foot F.data (Addr.add (vt1 V X.cpu.gpr + 16#64) i))
    (fw : sq V X.cpu.gpr ≠ 0 → ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rdi + 48#64) i))
    {eF : Addr} {codeF : List Byte} (hinF : CodeIn L eF codeF) (hF0 : 0 < codeF.length)
    (htgt : sq V X.cpu.gpr ≠ 0 → rdq(V0 V X.cpu.gpr, vt1 V X.cpu.gpr + 16#64) = eF)
    (kf : sq V X.cpu.gpr ≠ 0 → ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y →
      Agree F Y.proc.mm.mem (Vst (V0 V X.cpu.gpr) (X.cpu.gpr.rsp - 16) (toBytesLE (hcl_at.add 43) 8)) →
      Y.cpu.rip = eF → Y.cpu.gpr = (gC1 V X.cpu.gpr).set 4 (X.cpu.gpr.rsp - 16) →
      (∀ (Z : State) (V' : Addr → Byte) (t'' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V' →
        Z.cpu.rip = hcl_at.add 43 → Z.cpu.gpr.rsp = X.cpu.gpr.rsp - 8 → Z.cpu.gpr.rbx = X.cpu.gpr.rdi →
        rdq(V', X.cpu.gpr.rsp - 8) = X.cpu.gpr.rbx → rdq(V', X.cpu.gpr.rsp) = e₂ → Pc Z V' →
        GoG prof L o gev gP gE Z t'') →
      GoG prof L o gev gP gE Y t') :
    GoG prof L o gev gP gE X t := by
  have hlt := X.cpu.gpr.rsp.isLt
  have tn8 := t8 X.cpu.gpr.rsp (by omega)
  have e16 := b16 X.cpu.gpr.rsp
  have hq8 : (X.cpu.gpr.rsp - 8).toNat + 8 ≤ 2 ^ 64 := by rw [tn8]; omega
  -- the bytes stored by `mov qword [rbx + 48], 0`
  have m0 : ∀ (W : Addr → Byte) (x : Addr), x.toNat + 8 ≤ 2 ^ 64 →
      ((X.cpu.gpr.rdi + 48#64).toNat + 8 ≤ x.toNat ∨ x.toNat + 8 ≤ (X.cpu.gpr.rdi + 48#64).toNat) →
      (byteAddrs x 8).map (Vst W (X.cpu.gpr.rdi + 48#64) (toBytesLE 0#64 8)) = (byteAddrs x 8).map W :=
    fun W x hx h => Tun.rd_Vst W _ _ x 8 (by rw [toBytesLE_length]; exact hq) hx (by rw [toBytesLE_length]; exact h)
  by_cases hs : sq V X.cpu.gpr = 0
  · -- `_seqStream` not set
    refine (c_0 prof).run c hin (fun j' g' _ V' => j' = 51 ∧
        g' = { X.cpu.gpr with rbx := X.cpu.gpr.rdi, rsp := X.cpu.gpr.rsp - 8, rdi := 0#64 } ∧
        V' = V0 V X.cpu.gpr) hK hA (by rw [addr_add_zero]; exact hrip) (vc_0z hs hs1 w21 w29 w64 fa) ?_
    rintro j' g fl V₁ ⟨rfl, rfl, hV₁⟩ Y t₁ hKY hAY hrY hgY -
    subst V₁
    exact kM Y _ t₁ hKY hAY hrY (by rw [hgY]) (by rw [hgY]) hb0 hr0 (Or.inl ⟨hs, rfl, hgY⟩)
  · -- `_seqStream` set: to the first `call`
    refine (c_0 prof).run c hin (fun j' g' _ V' => j' = 40 ∧ g' = gC1 V X.cpu.gpr ∧ V' = V0 V X.cpu.gpr) hK hA
      (by rw [addr_add_zero]; exact hrip) (vc_0n hs hs1 w21 w29 w64 fa (fs hs)) ?_
    rintro j' g fl V₁ ⟨rfl, rfl, hV₁⟩ Y t₁ hKY hAY hrY hgY -
    subst V₁
    have hsY : Y.cpu.gpr.rsp = X.cpu.gpr.rsp - 8 := by rw [hgY]
    have he : eaD Y 0 16 = vt1 V X.cpu.gpr + 16#64 := by
      show Y.cpu.gpr.get (regOf 0) + BitVec.ofNat 64 16 = _
      rw [hgY]
      rfl
    have hst : ∀ i < 8, Foot Wl (Addr.add (Y.cpu.gpr.rsp - 8) i) := by rw [hsY, e16]; exact hs2 hs
    refine c.s_callM hKY hAY hin (lt_len (by decide)) hrY (call_40 _) (by rw [he]; exact fb hs) hinF hF0
      (by rw [he]; exact htgt hs) hst ?_
    rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
    rw [hsY, e16] at hA₂
    have hg₂' : Y₂.cpu.gpr = (gC1 V X.cpu.gpr).set 4 (X.cpu.gpr.rsp - 16) := by
      rw [hg₂, hgY]
      exact congrArg (fun v => (gC1 V X.cpu.gpr).set 4 v) e16
    refine kf hs Y₂ t₂ hK₂ hA₂ hr₂ hg₂' ?_
    -- back from the callee
    intro Z V' t'' hKZ hAZ hrZ hzs hzb hb hr' hPc
    have hb' : rdq(Vst V' (X.cpu.gpr.rdi + 48#64) (toBytesLE 0#64 8), X.cpu.gpr.rsp - 8) = X.cpu.gpr.rbx := by
      rw [m0 V' _ hq8 (by rw [tn8]; omega)]
      exact hb
    have hr'' : rdq(Vst V' (X.cpu.gpr.rdi + 48#64) (toBytesLE 0#64 8), X.cpu.gpr.rsp) = e₂ := by
      rw [m0 V' _ hp8 (by omega)]
      exact hr'
    refine (c_43 prof).run c hin (fun j' g' _ V'' => j' = 51 ∧ g' = Z.cpu.gpr ∧
        V'' = Vst V' (X.cpu.gpr.rdi + 48#64) (toBytesLE 0#64 8)) hKZ hAZ hrZ
      (vc_43 (by rw [hzb]; exact fw hs) fun _ => ⟨rfl, rfl, by rw [hzb]⟩) ?_
    rintro j' g fl V₂ ⟨rfl, rfl, hV₂⟩ U t₃ hKU hAU hrU hgU -
    subst V₂
    exact kM U _ t₃ hKU hAU hrU (by rw [hgU, hzs]) (by rw [hgU, hzb]) hb' hr'' (Or.inr ⟨Z, V', hPc, rfl, hgU⟩)

/-- `CHandler::Close ()` from where the two ways meet (51): `rsp` = `S - 8`, the saved `rbx` (`b0`) at `S - 8` and
the return address at `S`. With `_stream` (`s2`) 0 the run reaches the return address with `rax` = `rdi` = 0 and
`rbx` = `b0` (`k0`). Else, at the callee's entry `eF` the registers are `gC2` with `rsp` = `S - 16` and the bytes
with the return address into `Close` pushed (`kf`); if the callee returns to `hcl_at + 66` with `rsp`, `rbx`, the
saved `rbx` and the return address as they were, the run reaches that return address with `_stream` = 0, `rax` 0
and `rbx` = `b0` (`kr`). -/
theorem hcl_mid {Pc : State → (Addr → Byte) → Prop} (c : Seg prof F Wl L s₀ o) (hin : CodeIn L hcl_at hcl)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = hcl_at.add 51) {S : Addr}
    (hzs : X.cpu.gpr.rsp = S - 8) (hp : 16 ≤ S.toNat) (hp8 : S.toNat + 8 ≤ 2 ^ 64)
    (hs1 : ∀ i < 8, Foot F.data (Addr.add (S - 8) i)) (hl : ∀ i < 8, Foot F.data (Addr.add S i))
    {b0 : BitVec 64} (hb : rdq(V, S - 8) = b0)
    (fa : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rbx + 56#64) i))
    (hq : (X.cpu.gpr.rbx + 56#64).toNat + 8 ≤ 2 ^ 64)
    (hdp : (X.cpu.gpr.rbx + 56#64).toNat + 8 ≤ S.toNat - 8 ∨ S.toNat + 8 ≤ (X.cpu.gpr.rbx + 56#64).toNat)
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (hra : rdq(V, S) = e₂.add j₂)
    (k0 : s2 V X.cpu.gpr = 0 → ∀ (Z : State) (t' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V →
      Z.cpu.rip = e₂.add j₂ →
      Z.cpu.gpr = { X.cpu.gpr with rax := 0#64, rbx := b0, rsp := S, rdi := 0#64 }.set 4 (S + 8) →
      GoG prof L o gev gP gE Z t')
    (hs2 : s2 V X.cpu.gpr ≠ 0 → ∀ i < 8, Foot Wl (Addr.add (S - 16) i))
    (fs : s2 V X.cpu.gpr ≠ 0 → ∀ i < 8, Foot F.data (Addr.add (s2 V X.cpu.gpr) i))
    (fb : s2 V X.cpu.gpr ≠ 0 → ∀ i < 8, Foot F.data (Addr.add (vt2 V X.cpu.gpr + 16#64) i))
    (fw : s2 V X.cpu.gpr ≠ 0 → ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rbx + 56#64) i))
    {eF : Addr} {codeF : List Byte} (hinF : CodeIn L eF codeF) (hF0 : 0 < codeF.length)
    (htgt : s2 V X.cpu.gpr ≠ 0 → rdq(V, vt2 V X.cpu.gpr + 16#64) = eF)
    (kf : s2 V X.cpu.gpr ≠ 0 → ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y →
      Agree F Y.proc.mm.mem (Vst V (S - 16) (toBytesLE (hcl_at.add 66) 8)) →
      Y.cpu.rip = eF → Y.cpu.gpr = (gC2 V X.cpu.gpr).set 4 (S - 16) →
      (∀ (Z : State) (V' : Addr → Byte) (t'' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V' →
        Z.cpu.rip = hcl_at.add 66 → Z.cpu.gpr.rsp = S - 8 → Z.cpu.gpr.rbx = X.cpu.gpr.rbx →
        rdq(V', S - 8) = b0 → rdq(V', S) = e₂.add j₂ → Pc Z V' → GoG prof L o gev gP gE Z t'') →
      GoG prof L o gev gP gE Y t')
    (kr : ∀ (Z : State) (V' : Addr → Byte) (Z' : State) (t' : Nat), Pc Z V' → KeptW Wl s₀ Z' →
      Agree F Z'.proc.mm.mem (Vst V' (X.cpu.gpr.rbx + 56#64) (toBytesLE 0#64 8)) → Z'.cpu.rip = e₂.add j₂ →
      Z'.cpu.gpr = { Z.cpu.gpr with rax := 0#64, rbx := b0, rsp := S + 8 } → GoG prof L o gev gP gE Z' t') :
    GoG prof L o gev gP gE X t := by
  have hlt := S.isLt
  have tn8 := t8 S (by omega)
  have e16 := b16 S
  have e8 : S - 8 + 8 = S := BitVec.sub_add_cancel _ _
  have hq8 : (S - 8).toNat + 8 ≤ 2 ^ 64 := by rw [tn8]; omega
  -- the bytes stored by `mov qword [rbx + 56], 0`
  have m0 : ∀ (W : Addr → Byte) (x : Addr), x.toNat + 8 ≤ 2 ^ 64 →
      ((X.cpu.gpr.rbx + 56#64).toNat + 8 ≤ x.toNat ∨ x.toNat + 8 ≤ (X.cpu.gpr.rbx + 56#64).toNat) →
      (byteAddrs x 8).map (Vst W (X.cpu.gpr.rbx + 56#64) (toBytesLE 0#64 8)) = (byteAddrs x 8).map W :=
    fun W x hx h => Tun.rd_Vst W _ _ x 8 (by rw [toBytesLE_length]; exact hq) hx (by rw [toBytesLE_length]; exact h)
  by_cases hs : s2 V X.cpu.gpr = 0
  · -- `_stream` not set
    refine (c_51 prof).run c hin (fun j' g' _ V' => j' = 74 ∧ g' = { X.cpu.gpr with rdi := 0#64 } ∧ V' = V) hK hA
      hrip (vc_51z hs fa) ?_
    rintro j' g fl V₁ ⟨rfl, rfl, hV₁⟩ Y t₁ hKY hAY hrY hgY -
    subst V₁
    have hsY : Y.cpu.gpr.rsp = S - 8 := by rw [hgY]; exact hzs
    refine (c_74 prof).run c hin (fun j' g' _ V' => j' = 77 ∧
        g' = { Y.cpu.gpr with rax := 0#64, rbx := b0, rsp := S } ∧ V' = V) hKY hAY hrY
      (vc_74 (by rw [hsY]; exact hs1) fun _ => ⟨rfl, by rw [hsY, hb, e8], rfl⟩) ?_
    rintro j' g fl V₂ ⟨rfl, rfl, hV₂⟩ U t₂ hKU hAU hrU hgU -
    subst V₂
    have hsU : U.cpu.gpr.rsp = S := by rw [hgU]
    refine c.s_ret hKU hAU hin (lt_len (by decide)) hrU (ret_77 _) (by rw [hsU]; exact hl) hin₂ h₂
      (by rw [hsU]; exact hra) ?_
    rintro Z t₃ hKZ hAZ ⟨hrZ, hgZ⟩
    refine k0 hs Z t₃ hKZ hAZ hrZ ?_
    rw [hgZ, hgU, hgY]
    try rfl
  · -- `_stream` set: to the second `call`
    refine (c_51 prof).run c hin (fun j' g' _ V' => j' = 63 ∧ g' = gC2 V X.cpu.gpr ∧ V' = V) hK hA hrip
      (vc_51n hs fa (fs hs)) ?_
    rintro j' g fl V₁ ⟨rfl, rfl, hV₁⟩ Y t₁ hKY hAY hrY hgY -
    subst V₁
    have hsY : Y.cpu.gpr.rsp = S - 8 := by rw [hgY]; exact hzs
    have he : eaD Y 0 16 = vt2 V X.cpu.gpr + 16#64 := by
      show Y.cpu.gpr.get (regOf 0) + BitVec.ofNat 64 16 = _
      rw [hgY]
      rfl
    have hst : ∀ i < 8, Foot Wl (Addr.add (Y.cpu.gpr.rsp - 8) i) := by rw [hsY, e16]; exact hs2 hs
    refine c.s_callM hKY hAY hin (lt_len (by decide)) hrY (call_63 _) (by rw [he]; exact fb hs) hinF hF0
      (by rw [he]; exact htgt hs) hst ?_
    rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
    rw [hsY, e16] at hA₂
    have hg₂' : Y₂.cpu.gpr = (gC2 V X.cpu.gpr).set 4 (S - 16) := by
      rw [hg₂, hsY, e16, hgY]
    refine kf hs Y₂ t₂ hK₂ hA₂ hr₂ hg₂' ?_
    -- back from the callee
    intro Z V' t'' hKZ hAZ hrZ hzs₂ hzb hb' hr' hPc
    have hb'' : rdq(Vst V' (X.cpu.gpr.rbx + 56#64) (toBytesLE 0#64 8), S - 8) = b0 := by
      rw [m0 V' _ hq8 (by rw [tn8]; omega)]
      exact hb'
    have hr'' : rdq(Vst V' (X.cpu.gpr.rbx + 56#64) (toBytesLE 0#64 8), S) = e₂.add j₂ := by
      rw [m0 V' _ hp8 (by omega)]
      exact hr'
    refine (c_66 prof).run c hin (fun j' g' _ V'' => j' = 74 ∧ g' = Z.cpu.gpr ∧
        V'' = Vst V' (X.cpu.gpr.rbx + 56#64) (toBytesLE 0#64 8)) hKZ hAZ hrZ
      (vc_66 (by rw [hzb]; exact fw hs) fun _ => ⟨rfl, rfl, by rw [hzb]⟩) ?_
    rintro j' g fl V₂ ⟨rfl, rfl, hV₂⟩ U t₃ hKU hAU hrU hgU -
    subst V₂
    have hsU : U.cpu.gpr.rsp = S - 8 := by rw [hgU, hzs₂]
    refine (c_74 prof).run c hin (fun j' g' _ V'' => j' = 77 ∧
        g' = { Z.cpu.gpr with rax := 0#64, rbx := b0, rsp := S } ∧
        V'' = Vst V' (X.cpu.gpr.rbx + 56#64) (toBytesLE 0#64 8)) hKU hAU hrU
      (vc_74 (by rw [hsU]; exact hs1) fun _ => ⟨rfl, by rw [hsU, hb'', e8, hgU], rfl⟩) ?_
    rintro j' g fl V₃ ⟨rfl, rfl, hV₃⟩ U' t₄ hKU' hAU' hrU' hgU' -
    subst V₃
    have hsU' : U'.cpu.gpr.rsp = S := by rw [hgU']
    refine c.s_ret hKU' hAU' hin (lt_len (by decide)) hrU' (ret_77 _) (by rw [hsU']; exact hl) hin₂ h₂
      (by rw [hsU']; exact hr'') ?_
    rintro Z' t₅ hKZ' hAZ' ⟨hrZ', hgZ'⟩
    refine kr Z V' Z' t₅ hPc hKZ' hAZ' hrZ' ?_
    rw [hgZ', hgU']
    try rfl

end FV7z.Hcl
