import FV7z.Sis.Cuts
import FV7z.Lemmas.LeafRet
import FV7z.Lemmas.CallM
import FV7z.Tun.Inv
/-!
# `NCompress::NLzma::CDecoder::SetInStream` (PLAN.md §M, M1)

7-Zip 26.06's `NCompress::NLzma::CDecoder::SetInStream (inStream)` at `0x57f8d0` in `7zzs`
(`CPP/7zip/Compress/LzmaDecoder.cpp`; `objdump -d`): `_inStream = inStream` through `CMyComPtr`: `inStream->AddRef ()`
when it is set, the old `_inStream` (the 8 bytes at `this + 256`) `->Release ()` when it is set, then the store,
`return S_OK`. `push rbp; mov rbp, rdi; push rbx; mov rbx, rsi; sub rsp, 8`; if `rsi` is set, `rdi` = `rsi`,
`call qword [rax + 8]` (27, `Seg.s_callM`). Where the two ways meet (30): `rdi` = the old `_inStream`; if it is set,
`call qword [rax + 16]` (45). Where they meet again (48): `mov [rbp + 256], rbx; add rsp, 8; xor eax, eax;
pop rbx; pop rbp; ret` (to 63).

The two calls are each a hypothesis (`kf`), as in `FV7z.Ris`. The memory at the second call is what the first callee
left, so the run is cut where the two ways meet (30):

- `sis_ok`: from the entry to 30 (`kM`), through `AddRef` when `inStream` is set.
- `sis_mid`: from 30 (any state there with `rsp` 24 below `S`, the saved `rbx`, `rbp` at `S - 16`, `S - 8` and the
  return address at `S`, as `kM` gives) through `Release` when the old `_inStream` is set, to the return address.
- `sis_tail`: from 48 to the return address (both ways of `sis_mid`).

- `V1`: the bytes after the two pushes; `gZ0`, `gA`: the registers at 30 without the first call and at it;
  `old`, `vt2`, `gC2`: the old `_inStream`, its vtable and the registers at the second `call`.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Sis

/-- The `call`s through the vtables. -/
def pc8 : List Byte := [0xff, 0x50, 0x08]
theorem pc8_0 : ∀ feat, Dec feat pc8 0 (FV7z.mk .call 64 [.mem (mbd 0 8 64)] 3) := by dec_rfl
theorem wc_27 : pc8 <+: sis.drop 27 := by decide +kernel
theorem call_27 (feat : Features) : Dec feat sis 27 (FV7z.mk .call 64 [.mem (mbd 0 8 64)] 3) :=
  Dec.shift (j := 27) (k := 0) (pc8_0 feat) wc_27 (Nat.zero_le _)
def pc16 : List Byte := [0xff, 0x50, 0x10]
theorem pc16_0 : ∀ feat, Dec feat pc16 0 (FV7z.mk .call 64 [.mem (mbd 0 16 64)] 3) := by dec_rfl
theorem wc_45 : pc16 <+: sis.drop 45 := by decide +kernel
theorem call_45 (feat : Features) : Dec feat sis 45 (FV7z.mk .call 64 [.mem (mbd 0 16 64)] 3) :=
  Dec.shift (j := 45) (k := 0) (pc16_0 feat) wc_45 (Nat.zero_le _)

/-- The `ret`. -/
def pret : List Byte := [0xc3]
theorem pret_0 : ∀ feat, Dec feat pret 0 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem w_63 : pret <+: sis.drop 63 := by decide +kernel
theorem ret_63 (feat : Features) : Dec feat sis 63 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 63) (k := 0) (pret_0 feat) w_63 (Nat.zero_le _)

/-- The bytes after `push rbp; push rbx`. -/
abbrev V1 (V : Addr → Byte) (g : Gprs) : Addr → Byte :=
  Vst (Vst V (g.rsp - 8) (toBytesLE g.rbp 8)) (g.rsp - 8 - 8) (toBytesLE g.rbx 8)
/-- The registers at 30 without the first call. -/
abbrev gZ0 (g : Gprs) : Gprs := { g with rbx := g.rsi, rsp := g.rsp - 8 - 8 - 8#64, rbp := g.rdi }
/-- The registers at the first `call`: `rax` the vtable of `inStream`, `rdi` = it. -/
abbrev gA (V : Addr → Byte) (g : Gprs) : Gprs :=
  { g with rax := rdq(V1 V g, g.rsi), rbx := g.rsi, rsp := g.rsp - 8 - 8 - 8#64, rbp := g.rdi, rdi := g.rsi }
/-- The old `_inStream` (`rbp` = `this` at 30). -/
abbrev old (V : Addr → Byte) (g : Gprs) : Addr := rdq(V, g.rbp + 256#64)
/-- Its vtable. -/
abbrev vt2 (V : Addr → Byte) (g : Gprs) : Addr := rdq(V, old V g)
/-- The registers at the second `call`. -/
abbrev gC2 (V : Addr → Byte) (g : Gprs) : Gprs := { g with rax := vt2 V g, rdi := old V g }

theorem b24 (S : Addr) : S - 8 - 8 - 8#64 = S - 24 := by bv_omega
theorem b32 (S : Addr) : S - 24 - 8 = S - 32 := by bv_omega
theorem c16 (S : Addr) : S - 24 + 8#64 = S - 16 := by bv_omega
theorem c8 (S : Addr) : S - 16 + 8 = S - 8 := by bv_omega
theorem t16 (S : Addr) (h : 16 ≤ S.toNat) : (S - 16).toNat = S.toNat - 16 := by bv_omega
theorem t8 (S : Addr) (h : 8 ≤ S.toNat) : (S - 8).toNat = S.toNat - 8 := by bv_omega

variable {F : Footprint} {Wl : List Rgn}

/-- `inStream` not set: the pushes, `sub rsp, 8; test rsi, rsi; je` taken. -/
theorem vc_0z {g : Gprs} {f : Rflags} {V : Addr → Byte} (h : g.rsi = 0)
    (hst1 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8) i)) (hst2 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8) i)) :
    W_0 F Wl (fun j' g' _ V' => j' = 30 ∧ g' = gZ0 g ∧ V' = V1 V g) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [gZ0, V1] at h hst1 hst2 ⊢
  subst h
  wpx [W_0, W_21, o0, o1, BitVec.and_self, beq_iff_eq, beq_eq_false_iff_ne, ne_eq, beq_self_eq_true,
    not_true_eq_false, not_false_eq_true, false_implies, Bool.true_eq_false, Bool.false_eq_true, implies_true]
  all_goals repeat' (first
    | exact rfl
    | assumption
    | exact trivial
    | (intro hh; exact absurd hh (by decide))
    | apply And.intro
    | intro _)

/-- `inStream` set: `je` not taken, `mov rax, [rsi]; mov rdi, rsi`, up to the first `call`. -/
theorem vc_0n {g : Gprs} {f : Rflags} {V : Addr → Byte} (h : g.rsi ≠ 0)
    (hst1 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8) i)) (hst2 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8) i))
    (fs : ∀ i < 8, Foot F.data (Addr.add g.rsi i)) :
    W_0 F Wl (fun j' g' _ V' => j' = 27 ∧ g' = gA V g ∧ V' = V1 V g) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [gA, V1] at h hst1 hst2 fs ⊢
  wpx [W_0, W_21, o0, o1, h, BitVec.and_self, beq_iff_eq, beq_eq_false_iff_ne, ne_eq,
    not_true_eq_false, not_false_eq_true, false_implies, Bool.true_eq_false, Bool.false_eq_true, implies_true]
  all_goals repeat' (first
    | exact rfl
    | assumption
    | exact trivial
    | (intro hh; exact absurd hh h)
    | apply And.intro
    | intro _)

/-- The old `_inStream` not set: `mov rdi, [rbp + 256]; test rdi, rdi; je` taken. -/
theorem vc_30z {g : Gprs} {f : Rflags} {V : Addr → Byte} (h : old V g = 0)
    (fa : ∀ i < 8, Foot F.data (Addr.add (g.rbp + 256#64) i)) :
    W_30 F Wl (fun j' g' _ V' => j' = 48 ∧ g' = { g with rdi := 0#64 } ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [old] at h fa ⊢
  wpx [W_30, W_42, o2, o3, h, BitVec.and_self, beq_iff_eq, beq_eq_false_iff_ne, ne_eq, beq_self_eq_true,
    not_true_eq_false, not_false_eq_true, false_implies, Bool.true_eq_false, Bool.false_eq_true, implies_true]
  all_goals repeat' (first
    | exact rfl
    | assumption
    | exact trivial
    | (intro hh; exact absurd hh (by decide))
    | apply And.intro
    | intro _)

/-- The old `_inStream` set: `je` not taken, `mov rax, [rdi]`, up to the second `call`. -/
theorem vc_30n {g : Gprs} {f : Rflags} {V : Addr → Byte} (h : old V g ≠ 0)
    (fa : ∀ i < 8, Foot F.data (Addr.add (g.rbp + 256#64) i)) (fo : ∀ i < 8, Foot F.data (Addr.add (old V g) i)) :
    W_30 F Wl (fun j' g' _ V' => j' = 45 ∧ g' = gC2 V g ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [gC2, vt2, old] at h fa fo ⊢
  wpx [W_30, W_42, o2, o3, h, BitVec.and_self, beq_iff_eq, beq_eq_false_iff_ne, ne_eq,
    not_true_eq_false, not_false_eq_true, false_implies, Bool.true_eq_false, Bool.false_eq_true, implies_true]
  all_goals repeat' (first
    | exact rfl
    | assumption
    | exact trivial
    | (intro hh; exact absurd hh h)
    | apply And.intro
    | intro _)

/-- `mov [rbp + 256], rbx; add rsp, 8; xor eax, eax; pop rbx; pop rbp`. -/
theorem vc_48 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (hw : ∀ i < 8, Foot Wl (Addr.add (g.rbp + 256#64) i))
    (hl1 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8#64) i))
    (hl2 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8#64 + 8) i))
    (h : ∀ fl, Q 63
      { g with
        rax := 0#64, rbx := rdq(Vst V (g.rbp + 256#64) (toBytesLE g.rbx 8), g.rsp + 8#64),
        rsp := g.rsp + 8#64 + 8 + 8, rbp := rdq(Vst V (g.rbp + 256#64) (toBytesLE g.rbx 8), g.rsp + 8#64 + 8) } fl
      (Vst V (g.rbp + 256#64) (toBytesLE g.rbx 8))) :
    W_48 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hw hl1 hl2 h ⊢
  wpx [W_48, o4, lf_xz, BitVec.xor_self, BitVec.setWidth_zero]
  all_goals repeat' (first
    | exact h _
    | assumption
    | exact trivial
    | (simpa using h _)
    | apply And.intro
    | intro _)

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {X : State} {t : Nat} {V : Addr → Byte}

/-- `SetInStream (inStream)` (`this` = `rdi`, `inStream` = `rsi`) from its entry to where the two ways meet (30,
`kM`): `rsp` 24 below the entry's, `rbp` = `this`, `rbx` = `inStream`, the saved `rbp`, `rbx` and the return address
as they were (`hb0`, `hb1`, `hr0` for the bytes `V1`), and either `inStream` not set and the bytes `V1`, or the run
through its `AddRef`: at the callee's entry `eF` the registers `gA` with `rsp` 32 below the entry's and the bytes
`V1` with the return address into `SetInStream` pushed (`kf`); the callee returns to `sis_at + 30` with `rsp`,
`rbp`, `rbx`, the saved registers and the return address as they were and its own post `Pc`. -/
theorem sis_ok {Pc : State → (Addr → Byte) → Prop} (c : Seg prof F Wl L s₀ o) (hin : CodeIn L sis_at sis)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = sis_at)
    (hs1 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8) i))
    (hs2 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8 - 8) i))
    {e₂ : Addr} (hb0 : rdq(V1 V X.cpu.gpr, X.cpu.gpr.rsp - 8) = X.cpu.gpr.rbp)
    (hb1 : rdq(V1 V X.cpu.gpr, X.cpu.gpr.rsp - 16) = X.cpu.gpr.rbx)
    (hr0 : rdq(V1 V X.cpu.gpr, X.cpu.gpr.rsp) = e₂)
    (kM : ∀ (Z : State) (V' : Addr → Byte) (t' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V' →
      Z.cpu.rip = sis_at.add 30 → Z.cpu.gpr.rsp = X.cpu.gpr.rsp - 24 → Z.cpu.gpr.rbp = X.cpu.gpr.rdi →
      Z.cpu.gpr.rbx = X.cpu.gpr.rsi → rdq(V', X.cpu.gpr.rsp - 8) = X.cpu.gpr.rbp →
      rdq(V', X.cpu.gpr.rsp - 16) = X.cpu.gpr.rbx → rdq(V', X.cpu.gpr.rsp) = e₂ →
      ((X.cpu.gpr.rsi = 0 ∧ V' = V1 V X.cpu.gpr ∧ Z.cpu.gpr = gZ0 X.cpu.gpr) ∨ Pc Z V') →
      GoG prof L o gev gP gE Z t')
    (hs3 : X.cpu.gpr.rsi ≠ 0 → ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 32) i))
    (fs : X.cpu.gpr.rsi ≠ 0 → ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsi i))
    (fb : X.cpu.gpr.rsi ≠ 0 → ∀ i < 8, Foot F.data (Addr.add (rdq(V1 V X.cpu.gpr, X.cpu.gpr.rsi) + 8#64) i))
    {eF : Addr} {codeF : List Byte} (hinF : CodeIn L eF codeF) (hF0 : 0 < codeF.length)
    (htgt : X.cpu.gpr.rsi ≠ 0 → rdq(V1 V X.cpu.gpr, rdq(V1 V X.cpu.gpr, X.cpu.gpr.rsi) + 8#64) = eF)
    (kf : X.cpu.gpr.rsi ≠ 0 → ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y →
      Agree F Y.proc.mm.mem (Vst (V1 V X.cpu.gpr) (X.cpu.gpr.rsp - 32) (toBytesLE (sis_at.add 30) 8)) →
      Y.cpu.rip = eF → Y.cpu.gpr = (gA V X.cpu.gpr).set 4 (X.cpu.gpr.rsp - 32) →
      (∀ (Z : State) (V' : Addr → Byte) (t'' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V' →
        Z.cpu.rip = sis_at.add 30 → Z.cpu.gpr.rsp = X.cpu.gpr.rsp - 24 → Z.cpu.gpr.rbp = X.cpu.gpr.rdi →
        Z.cpu.gpr.rbx = X.cpu.gpr.rsi → rdq(V', X.cpu.gpr.rsp - 8) = X.cpu.gpr.rbp →
        rdq(V', X.cpu.gpr.rsp - 16) = X.cpu.gpr.rbx → rdq(V', X.cpu.gpr.rsp) = e₂ → Pc Z V' →
        GoG prof L o gev gP gE Z t'') →
      GoG prof L o gev gP gE Y t') :
    GoG prof L o gev gP gE X t := by
  have e24 := b24 X.cpu.gpr.rsp
  have e32 := b32 X.cpu.gpr.rsp
  by_cases hs : X.cpu.gpr.rsi = 0
  · -- `inStream` not set
    refine (c_0 prof).run c hin (fun j' g' _ V' => j' = 30 ∧ g' = gZ0 X.cpu.gpr ∧ V' = V1 V X.cpu.gpr) hK hA
      (by rw [addr_add_zero]; exact hrip) (vc_0z hs hs1 hs2) ?_
    rintro j' g fl V₁ ⟨rfl, rfl, hV₁⟩ Y t₁ hKY hAY hrY hgY -
    subst V₁
    exact kM Y _ t₁ hKY hAY hrY (by rw [hgY]; exact e24) (by rw [hgY]) (by rw [hgY]) hb0 hb1 hr0
      (Or.inl ⟨hs, rfl, hgY⟩)
  · -- `inStream` set: to the first `call`
    refine (c_0 prof).run c hin (fun j' g' _ V' => j' = 27 ∧ g' = gA V X.cpu.gpr ∧ V' = V1 V X.cpu.gpr) hK hA
      (by rw [addr_add_zero]; exact hrip) (vc_0n hs hs1 hs2 (fs hs)) ?_
    rintro j' g fl V₁ ⟨rfl, rfl, hV₁⟩ Y t₁ hKY hAY hrY hgY -
    subst V₁
    have hsY : Y.cpu.gpr.rsp = X.cpu.gpr.rsp - 24 := by rw [hgY]; exact e24
    have he : eaD Y 0 8 = rdq(V1 V X.cpu.gpr, X.cpu.gpr.rsi) + 8#64 := by
      show Y.cpu.gpr.get (regOf 0) + BitVec.ofNat 64 8 = _
      rw [hgY]
      rfl
    have hst : ∀ i < 8, Foot Wl (Addr.add (Y.cpu.gpr.rsp - 8) i) := by rw [hsY, e32]; exact hs3 hs
    refine c.s_callM hKY hAY hin (lt_len (by decide)) hrY (call_27 _) (by rw [he]; exact fb hs) hinF hF0
      (by rw [he]; exact htgt hs) hst ?_
    rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
    rw [hsY, e32] at hA₂
    have hg₂' : Y₂.cpu.gpr = (gA V X.cpu.gpr).set 4 (X.cpu.gpr.rsp - 32) := by
      rw [hg₂, hsY, e32, hgY]
    refine kf hs Y₂ t₂ hK₂ hA₂ hr₂ hg₂' ?_
    intro Z V' t'' hKZ hAZ hrZ hzs hzp hzb hb hb' hr' hPc
    exact kM Z V' t'' hKZ hAZ hrZ hzs hzp hzb hb hb' hr' (Or.inr hPc)

/-- From where the two ways meet again (48) to the return address: the store of `rbx` into `rbp + 256`, the saved
`rbx`, `rbp` (`bx0`, `bp0` at `S - 16`, `S - 8`) back, `rax` 0. -/
theorem sis_tail (c : Seg prof F Wl L s₀ o) (hin : CodeIn L sis_at sis) {Y : State} {W : Addr → Byte}
    (hK : KeptW Wl s₀ Y) (hA : Agree F Y.proc.mm.mem W) (hrip : Y.cpu.rip = sis_at.add 48) {S : Addr}
    (hzs : Y.cpu.gpr.rsp = S - 24) (hp : 32 ≤ S.toNat) (hp8 : S.toNat + 8 ≤ 2 ^ 64)
    (hl2 : ∀ i < 8, Foot F.data (Addr.add (S - 16) i)) (hl1 : ∀ i < 8, Foot F.data (Addr.add (S - 8) i))
    (hl : ∀ i < 8, Foot F.data (Addr.add S i)) {bx0 bp0 : BitVec 64} (hbx : rdq(W, S - 16) = bx0)
    (hbp : rdq(W, S - 8) = bp0) (fw : ∀ i < 8, Foot Wl (Addr.add (Y.cpu.gpr.rbp + 256#64) i))
    (hq : (Y.cpu.gpr.rbp + 256#64).toNat + 8 ≤ 2 ^ 64)
    (hdp : (Y.cpu.gpr.rbp + 256#64).toNat + 8 ≤ S.toNat - 16 ∨ S.toNat + 8 ≤ (Y.cpu.gpr.rbp + 256#64).toNat)
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (hra : rdq(W, S) = e₂.add j₂)
    (k : ∀ (Z : State) (t' : Nat), KeptW Wl s₀ Z →
      Agree F Z.proc.mm.mem (Vst W (Y.cpu.gpr.rbp + 256#64) (toBytesLE Y.cpu.gpr.rbx 8)) →
      Z.cpu.rip = e₂.add j₂ →
      Z.cpu.gpr = { Y.cpu.gpr with rax := 0#64, rbx := bx0, rsp := S + 8, rbp := bp0 } →
      GoG prof L o gev gP gE Z t') :
    GoG prof L o gev gP gE Y t := by
  have hlt := S.isLt
  have a16 := c16 S
  have a8 := c8 S
  have e8 : S - 8 + 8 = S := BitVec.sub_add_cancel _ _
  have tn16 := t16 S (by omega)
  have tn8 := t8 S (by omega)
  have m0 : ∀ x : Addr, x.toNat + 8 ≤ 2 ^ 64 →
      ((Y.cpu.gpr.rbp + 256#64).toNat + 8 ≤ x.toNat ∨ x.toNat + 8 ≤ (Y.cpu.gpr.rbp + 256#64).toNat) →
      (byteAddrs x 8).map (Vst W (Y.cpu.gpr.rbp + 256#64) (toBytesLE Y.cpu.gpr.rbx 8)) = (byteAddrs x 8).map W :=
    fun x hx h => Tun.rd_Vst W _ _ x 8 (by rw [toBytesLE_length]; exact hq) hx (by rw [toBytesLE_length]; exact h)
  have hbx' : rdq(Vst W (Y.cpu.gpr.rbp + 256#64) (toBytesLE Y.cpu.gpr.rbx 8), S - 16) = bx0 := by
    rw [m0 _ (by rw [tn16]; omega) (by rw [tn16]; omega)]
    exact hbx
  have hbp' : rdq(Vst W (Y.cpu.gpr.rbp + 256#64) (toBytesLE Y.cpu.gpr.rbx 8), S - 8) = bp0 := by
    rw [m0 _ (by rw [tn8]; omega) (by rw [tn8]; omega)]
    exact hbp
  have hr' : rdq(Vst W (Y.cpu.gpr.rbp + 256#64) (toBytesLE Y.cpu.gpr.rbx 8), S) = e₂.add j₂ := by
    rw [m0 _ hp8 (by omega)]
    exact hra
  refine (c_48 prof).run c hin (fun j' g' _ V' => j' = 63 ∧
      g' = { Y.cpu.gpr with rax := 0#64, rbx := bx0, rsp := S, rbp := bp0 } ∧
      V' = Vst W (Y.cpu.gpr.rbp + 256#64) (toBytesLE Y.cpu.gpr.rbx 8)) hK hA hrip
    (vc_48 fw (by rw [hzs, a16]; exact hl2) (by rw [hzs, a16, a8]; exact hl1)
      fun _ => ⟨rfl, by rw [hzs, a16, a8, e8, hbx', hbp'], rfl⟩) ?_
  rintro j' g fl V₂ ⟨rfl, rfl, hV₂⟩ U t₂ hKU hAU hrU hgU -
  subst V₂
  have hsU : U.cpu.gpr.rsp = S := by rw [hgU]
  refine c.s_ret hKU hAU hin (lt_len (by decide)) hrU (ret_63 _) (by rw [hsU]; exact hl) hin₂ h₂
    (by rw [hsU]; exact hr') ?_
  rintro Z t₃ hKZ hAZ ⟨hrZ, hgZ⟩
  refine k Z t₃ hKZ hAZ hrZ ?_
  rw [hgZ, hgU]
  try rfl

/-- `SetInStream` from where the two ways meet (30): `rsp` = `S - 24`, the saved `rbx`, `rbp` (`bx0`, `bp0`) at
`S - 16`, `S - 8` and the return address at `S`. With the old `_inStream` (`old`) 0 the run reaches the return
address with `rax` = `rdi` = 0, `rbx`, `rbp` restored and `rbx` stored into `rbp + 256` (`k0`). Else, at the callee's
entry `eF` the registers are `gC2` with `rsp` = `S - 32` and the bytes with the return address into `SetInStream`
pushed (`kf`); if the callee returns to `sis_at + 48` with `rsp`, `rbp`, `rbx`, the saved registers and the return
address as they were, the run reaches that return address likewise (`kr`). -/
theorem sis_mid {Pc : State → (Addr → Byte) → Prop} (c : Seg prof F Wl L s₀ o) (hin : CodeIn L sis_at sis)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = sis_at.add 30) {S : Addr}
    (hzs : X.cpu.gpr.rsp = S - 24) (hp : 32 ≤ S.toNat) (hp8 : S.toNat + 8 ≤ 2 ^ 64)
    (hl2 : ∀ i < 8, Foot F.data (Addr.add (S - 16) i)) (hl1 : ∀ i < 8, Foot F.data (Addr.add (S - 8) i))
    (hl : ∀ i < 8, Foot F.data (Addr.add S i)) {bx0 bp0 : BitVec 64} (hbx : rdq(V, S - 16) = bx0)
    (hbp : rdq(V, S - 8) = bp0) (fa : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rbp + 256#64) i))
    (fw : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rbp + 256#64) i))
    (hq : (X.cpu.gpr.rbp + 256#64).toNat + 8 ≤ 2 ^ 64)
    (hdp : (X.cpu.gpr.rbp + 256#64).toNat + 8 ≤ S.toNat - 16 ∨ S.toNat + 8 ≤ (X.cpu.gpr.rbp + 256#64).toNat)
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (hra : rdq(V, S) = e₂.add j₂)
    (k0 : old V X.cpu.gpr = 0 → ∀ (Z : State) (t' : Nat), KeptW Wl s₀ Z →
      Agree F Z.proc.mm.mem (Vst V (X.cpu.gpr.rbp + 256#64) (toBytesLE X.cpu.gpr.rbx 8)) →
      Z.cpu.rip = e₂.add j₂ →
      Z.cpu.gpr = { X.cpu.gpr with rax := 0#64, rbx := bx0, rsp := S + 8, rbp := bp0, rdi := 0#64 } →
      GoG prof L o gev gP gE Z t')
    (hs3 : old V X.cpu.gpr ≠ 0 → ∀ i < 8, Foot Wl (Addr.add (S - 32) i))
    (fo : old V X.cpu.gpr ≠ 0 → ∀ i < 8, Foot F.data (Addr.add (old V X.cpu.gpr) i))
    (fb : old V X.cpu.gpr ≠ 0 → ∀ i < 8, Foot F.data (Addr.add (vt2 V X.cpu.gpr + 16#64) i))
    {eF : Addr} {codeF : List Byte} (hinF : CodeIn L eF codeF) (hF0 : 0 < codeF.length)
    (htgt : old V X.cpu.gpr ≠ 0 → rdq(V, vt2 V X.cpu.gpr + 16#64) = eF)
    (kf : old V X.cpu.gpr ≠ 0 → ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y →
      Agree F Y.proc.mm.mem (Vst V (S - 32) (toBytesLE (sis_at.add 48) 8)) →
      Y.cpu.rip = eF → Y.cpu.gpr = (gC2 V X.cpu.gpr).set 4 (S - 32) →
      (∀ (Z : State) (V' : Addr → Byte) (t'' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V' →
        Z.cpu.rip = sis_at.add 48 → Z.cpu.gpr.rsp = S - 24 → Z.cpu.gpr.rbp = X.cpu.gpr.rbp →
        Z.cpu.gpr.rbx = X.cpu.gpr.rbx → rdq(V', S - 16) = bx0 → rdq(V', S - 8) = bp0 →
        rdq(V', S) = e₂.add j₂ →
        Pc Z V' → GoG prof L o gev gP gE Z t'') →
      GoG prof L o gev gP gE Y t')
    (kr : ∀ (Z : State) (V' : Addr → Byte) (Z' : State) (t' : Nat), Pc Z V' → KeptW Wl s₀ Z' →
      Agree F Z'.proc.mm.mem (Vst V' (X.cpu.gpr.rbp + 256#64) (toBytesLE X.cpu.gpr.rbx 8)) →
      Z'.cpu.rip = e₂.add j₂ →
      Z'.cpu.gpr = { Z.cpu.gpr with rax := 0#64, rbx := bx0, rsp := S + 8, rbp := bp0 } →
      GoG prof L o gev gP gE Z' t') :
    GoG prof L o gev gP gE X t := by
  have e32 := b32 S
  by_cases hs : old V X.cpu.gpr = 0
  · -- the old `_inStream` not set
    refine (c_30 prof).run c hin (fun j' g' _ V' => j' = 48 ∧ g' = { X.cpu.gpr with rdi := 0#64 } ∧ V' = V) hK hA
      hrip (vc_30z hs fa) ?_
    rintro j' g fl V₁ ⟨rfl, rfl, hV₁⟩ Y t₁ hKY hAY hrY hgY -
    subst V₁
    refine sis_tail c hin hKY hAY hrY (by rw [hgY]; exact hzs) hp hp8 hl2 hl1 hl hbx hbp (by rw [hgY]; exact fw)
      (by rw [hgY]; exact hq) (by rw [hgY]; exact hdp) hin₂ h₂ hra ?_
    intro Z t' hKZ hAZ hrZ hgZ
    rw [hgY] at hAZ
    exact k0 hs Z t' hKZ hAZ hrZ (by rw [hgZ, hgY])
  · -- the old `_inStream` set: to the second `call`
    refine (c_30 prof).run c hin (fun j' g' _ V' => j' = 45 ∧ g' = gC2 V X.cpu.gpr ∧ V' = V) hK hA hrip
      (vc_30n hs fa (fo hs)) ?_
    rintro j' g fl V₁ ⟨rfl, rfl, hV₁⟩ Y t₁ hKY hAY hrY hgY -
    subst V₁
    have hsY : Y.cpu.gpr.rsp = S - 24 := by rw [hgY]; exact hzs
    have he : eaD Y 0 16 = vt2 V X.cpu.gpr + 16#64 := by
      show Y.cpu.gpr.get (regOf 0) + BitVec.ofNat 64 16 = _
      rw [hgY]
      rfl
    have hst : ∀ i < 8, Foot Wl (Addr.add (Y.cpu.gpr.rsp - 8) i) := by rw [hsY, e32]; exact hs3 hs
    refine c.s_callM hKY hAY hin (lt_len (by decide)) hrY (call_45 _) (by rw [he]; exact fb hs) hinF hF0
      (by rw [he]; exact htgt hs) hst ?_
    rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
    rw [hsY, e32] at hA₂
    have hg₂' : Y₂.cpu.gpr = (gC2 V X.cpu.gpr).set 4 (S - 32) := by
      rw [hg₂, hsY, e32, hgY]
    refine kf hs Y₂ t₂ hK₂ hA₂ hr₂ hg₂' ?_
    -- back from the callee
    intro Z V' t'' hKZ hAZ hrZ hzs₂ hzp hzb hbx' hbp' hr' hPc
    refine sis_tail c hin hKZ hAZ hrZ hzs₂ hp hp8 hl2 hl1 hl hbx' hbp' (by rw [hzp]; exact fw)
      (by rw [hzp]; exact hq) (by rw [hzp]; exact hdp) hin₂ h₂ hr' ?_
    intro Z' t' hKZ' hAZ' hrZ' hgZ'
    rw [hzp, hzb] at hAZ'
    exact kr Z V' Z' t' hPc hKZ' hAZ' hrZ' hgZ'

end FV7z.Sis
