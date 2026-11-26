import FV7z.Ris.Cuts
import FV7z.Lemmas.LeafRet
import FV7z.Lemmas.CallM
import FV7z.Tun.Inv
/-!
# `CDecoder::ReleaseInStream` (PLAN.md §M, M1)

7-Zip 26.06's `NCompress::NLzma::CDecoder::ReleaseInStream ()` at `0x57f930` in `7zzs`
(`CPP/7zip/Compress/LzmaDecoder.cpp`; `objdump -d`): `_inStream.Release ()`, `return S_OK`. `push rbx`, `rbx` =
`this`, `rdi` = `_inStream` (the 8 bytes at `this + 256`); if it is set, `rax` = its vtable,
`call qword [rax + 16]` (23, `Seg.s_callM`) and `_inStream` = 0 (26); then `xor eax, eax; pop rbx; ret` (37 to 40).

The callee (`Release`) is a hypothesis (`kf`), as in `FV7z.Lfp`: a continuation at its entry, given the run from its
return (`ris_at + 26`, `rsp` 8 below the entry's, `rbx` = `this`, the saved `rbx` and the return address left as they
were, and the callee's own post `Pc`) to the return address.

- `V1`: the bytes after `push rbx`; `s`, `vt`: `_inStream` and its vtable, read from them; `gC`: the registers at
  the `call`.
- `vc_0z`, `vc_0n`, `vc_26`, `vc_37`: the verification conditions of the pieces.
- `ris_ok`: from the entry, through the callee when `_inStream` is set, to the return address with `rax` 0.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Ris

/-- The `call` through the vtable. -/
def pcall : List Byte := [0xff, 0x50, 0x10]
theorem pcall_0 : ∀ feat, Dec feat pcall 0 (FV7z.mk .call 64 [.mem (mbd 0 16 64)] 3) := by dec_rfl
theorem wc_23 : pcall <+: ris.drop 23 := by decide +kernel
theorem call_23 (feat : Features) : Dec feat ris 23 (FV7z.mk .call 64 [.mem (mbd 0 16 64)] 3) :=
  Dec.shift (j := 23) (k := 0) (pcall_0 feat) wc_23 (Nat.zero_le _)

/-- The `ret`. -/
def pret : List Byte := [0xc3]
theorem pret_0 : ∀ feat, Dec feat pret 0 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem w_40 : pret <+: ris.drop 40 := by decide +kernel
theorem ret_40 (feat : Features) : Dec feat ris 40 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 40) (k := 0) (pret_0 feat) w_40 (Nat.zero_le _)

/-- The bytes after `push rbx`. -/
abbrev V1 (V : Addr → Byte) (g : Gprs) : Addr → Byte := Vst V (g.rsp - 8) (toBytesLE g.rbx 8)
/-- `_inStream`, read after `push rbx`. -/
abbrev s (V : Addr → Byte) (g : Gprs) : Addr := rdq(V1 V g, g.rdi + 256#64)
/-- Its vtable. -/
abbrev vt (V : Addr → Byte) (g : Gprs) : Addr := rdq(V1 V g, s V g)
/-- The registers at the `call`. -/
abbrev gC (V : Addr → Byte) (g : Gprs) : Gprs :=
  { g with rax := vt V g, rbx := g.rdi, rsp := g.rsp - 8, rdi := s V g }

variable {F : Footprint} {Wl : List Rgn}

/-- `_inStream` not set: `push rbx; mov rbx, rdi; mov rdi, [rdi + 256]; test rdi, rdi; je` taken. -/
theorem vc_0z {g : Gprs} {f : Rflags} {V : Addr → Byte} (h : s V g = 0)
    (hst : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8) i)) (fa : ∀ i < 8, Foot F.data (Addr.add (g.rdi + 256#64) i)) :
    W_0 F Wl (fun j' g' _ V' => j' = 37 ∧ g' = { g with rbx := g.rdi, rsp := g.rsp - 8, rdi := 0#64 } ∧
      V' = V1 V g) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [s, V1] at h hst fa ⊢
  wpx [W_0, W_20, o0, o1, h, BitVec.and_self, beq_iff_eq, beq_eq_false_iff_ne, ne_eq, beq_self_eq_true,
    not_true_eq_false, not_false_eq_true, false_implies, Bool.true_eq_false, Bool.false_eq_true, implies_true]
  all_goals first
  | exact ⟨hst, fa⟩
  | exact ⟨hst, fa, fun _ => ⟨rfl, rfl, rfl⟩⟩
  | exact ⟨hst, fa, fun _ => ⟨rfl, rfl, rfl⟩, fun hh => absurd hh (by decide)⟩
  | exact ⟨hst, fa, ⟨rfl, rfl, rfl⟩⟩
  | (refine ⟨hst, fa, ?_⟩; done)

/-- `_inStream` set: `je` not taken, `mov rax, [rdi]`, up to the `call`. -/
theorem vc_0n {g : Gprs} {f : Rflags} {V : Addr → Byte} (h : s V g ≠ 0)
    (hst : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8) i)) (fa : ∀ i < 8, Foot F.data (Addr.add (g.rdi + 256#64) i))
    (fs : ∀ i < 8, Foot F.data (Addr.add (s V g) i)) :
    W_0 F Wl (fun j' g' _ V' => j' = 23 ∧ g' = gC V g ∧ V' = V1 V g) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [gC, vt, s, V1] at h hst fa fs ⊢
  wpx [W_0, W_20, o0, o1, h, BitVec.and_self, beq_iff_eq, beq_eq_false_iff_ne, ne_eq,
    not_true_eq_false, not_false_eq_true, false_implies, Bool.true_eq_false, Bool.false_eq_true, implies_true]
  all_goals first
  | exact ⟨hst, fa, fs⟩
  | exact ⟨hst, fa, fun hh => absurd hh h, fun _ => ⟨fs, rfl, rfl, rfl⟩⟩
  | exact ⟨hst, fa, fun hh => absurd hh h, fun _ => fs⟩
  | exact ⟨hst, fa, fs, rfl, rfl, rfl⟩
  | exact ⟨hst, fa, fs, rfl, rfl⟩
  | (refine ⟨hst, fa, ?_⟩; done)

/-- `mov qword [rbx + 256], 0`. -/
theorem vc_26 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (hw : ∀ i < 8, Foot Wl (Addr.add (g.rbx + 256#64) i))
    (h : ∀ fl, Q 37 g fl (Vst V (g.rbx + 256#64) (toBytesLE 0#64 8))) :
    W_26 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hw h ⊢
  wpx [W_26, o2]
  first
  | exact ⟨hw, h _⟩
  | (refine ⟨hw, ?_⟩; simpa using h _)

/-- `xor eax, eax; pop rbx`. -/
theorem vc_37 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (hl : ∀ i < 8, Foot F.data (Addr.add g.rsp i))
    (h : ∀ fl, Q 40 { g with rax := 0#64, rbx := rdq(V, g.rsp), rsp := g.rsp + 8 } fl V) :
    W_37 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hl h ⊢
  wpx [W_37, o3, BitVec.xor_self, BitVec.setWidth_zero]
  first
  | exact ⟨hl, h _⟩
  | exact ⟨by simpa using hl, h _⟩
  | (refine ⟨hl, ?_⟩; simpa using h _)
  | (refine ⟨?_, ?_⟩; (simpa using hl); simpa using h _)
  | exact h _

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {X : State} {t : Nat} {V : Addr → Byte}

/-- `CDecoder::ReleaseInStream ()` (`this` = `rdi`) from its entry. With `_inStream` (`s`) 0 the run reaches the
return address with `rax` = `rdi` = 0 and the bytes `V1` (`k0`). Else, at the callee's entry `eF` (the 8 bytes at
`vt + 16`) the registers are `gC` with `rsp` 16 below the entry's and the bytes `V1` with the return address into
`ReleaseInStream` pushed (`kf`); if the callee returns to `ris_at + 26` with `rsp` and `rbx` as at its entry, and the
saved `rbx` and the return address of `ReleaseInStream` as they were, the run reaches that return address with
`_inStream` = 0, `rax` 0 and `rbx`, `rsp` restored (`kr`). -/
theorem ris_ok {Pc : State → (Addr → Byte) → Prop} (c : Seg prof F Wl L s₀ o) (hin : CodeIn L ris_at ris)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = ris_at)
    (hp : 16 ≤ X.cpu.gpr.rsp.toNat) (hp8 : X.cpu.gpr.rsp.toNat + 8 ≤ 2 ^ 64)
    (hs1 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8) i))
    (hl : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsp i))
    (fa : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rdi + 256#64) i))
    (hq : (X.cpu.gpr.rdi + 256#64).toNat + 8 ≤ 2 ^ 64)
    (hdp : (X.cpu.gpr.rdi + 256#64).toNat + 8 ≤ X.cpu.gpr.rsp.toNat - 8 ∨
      X.cpu.gpr.rsp.toNat + 8 ≤ (X.cpu.gpr.rdi + 256#64).toNat)
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (hra : rdq(V, X.cpu.gpr.rsp) = e₂.add j₂)
    (k0 : s V X.cpu.gpr = 0 → ∀ (Z : State) (t' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem (V1 V X.cpu.gpr) →
      Z.cpu.rip = e₂.add j₂ → Z.cpu.gpr = { X.cpu.gpr with rax := 0#64, rdi := 0#64 }.set 4 (X.cpu.gpr.rsp + 8) →
      GoG prof L o gev gP gE Z t')
    (hs2 : s V X.cpu.gpr ≠ 0 → ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 16) i))
    (fs : s V X.cpu.gpr ≠ 0 → ∀ i < 8, Foot F.data (Addr.add (s V X.cpu.gpr) i))
    (fb : s V X.cpu.gpr ≠ 0 → ∀ i < 8, Foot F.data (Addr.add (vt V X.cpu.gpr + 16#64) i))
    (fw : s V X.cpu.gpr ≠ 0 → ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rdi + 256#64) i))
    {eF : Addr} {codeF : List Byte} (hinF : CodeIn L eF codeF) (hF0 : 0 < codeF.length)
    (htgt : s V X.cpu.gpr ≠ 0 → rdq(V1 V X.cpu.gpr, vt V X.cpu.gpr + 16#64) = eF)
    (kf : s V X.cpu.gpr ≠ 0 → ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y →
      Agree F Y.proc.mm.mem (Vst (V1 V X.cpu.gpr) (X.cpu.gpr.rsp - 16) (toBytesLE (ris_at.add 26) 8)) →
      Y.cpu.rip = eF → Y.cpu.gpr = (gC V X.cpu.gpr).set 4 (X.cpu.gpr.rsp - 16) →
      (∀ (Z : State) (V' : Addr → Byte) (t'' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V' →
        Z.cpu.rip = ris_at.add 26 → Z.cpu.gpr.rsp = X.cpu.gpr.rsp - 8 → Z.cpu.gpr.rbx = X.cpu.gpr.rdi →
        rdq(V', X.cpu.gpr.rsp - 8) = X.cpu.gpr.rbx → rdq(V', X.cpu.gpr.rsp) = e₂.add j₂ → Pc Z V' →
        GoG prof L o gev gP gE Z t'') →
      GoG prof L o gev gP gE Y t')
    (kr : ∀ (Z : State) (V' : Addr → Byte) (Z' : State) (t' : Nat), Pc Z V' → KeptW Wl s₀ Z' →
      Agree F Z'.proc.mm.mem (Vst V' (X.cpu.gpr.rdi + 256#64) (toBytesLE 0#64 8)) → Z'.cpu.rip = e₂.add j₂ →
      Z'.cpu.gpr = { Z.cpu.gpr with rax := 0#64, rbx := X.cpu.gpr.rbx, rsp := X.cpu.gpr.rsp + 8 } →
      GoG prof L o gev gP gE Z' t') :
    GoG prof L o gev gP gE X t := by
  have hlt := X.cpu.gpr.rsp.isLt
  have tn8 : (X.cpu.gpr.rsp - 8).toNat = X.cpu.gpr.rsp.toNat - 8 := by rw [BitVec.toNat_sub]; simp <;> omega
  have tn16 : (X.cpu.gpr.rsp - 16).toNat = X.cpu.gpr.rsp.toNat - 16 := by rw [BitVec.toNat_sub]; simp <;> omega
  have e16 : X.cpu.gpr.rsp - 8 - 8 = X.cpu.gpr.rsp - 16 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, tn8, tn16]
    simp <;> omega
  have e8 : X.cpu.gpr.rsp - 8 + 8 = X.cpu.gpr.rsp := BitVec.sub_add_cancel _ _
  have hq8 : (X.cpu.gpr.rsp - 8).toNat + 8 ≤ 2 ^ 64 := by rw [tn8]; omega
  have h8 : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rsp - 8) i) := fun i hi => c.hws _ (hs1 i hi)
  -- the saved `rbx` and the return address, after `push rbx`
  have hb1 : rdq(V1 V X.cpu.gpr, X.cpu.gpr.rsp - 8) = X.cpu.gpr.rbx := by
    show ofBytesLE 64 (List.map (Vst V _ (toBytesLE X.cpu.gpr.rbx 8)) (byteAddrs _ 8)) = _
    rw [Tun.rd_Vst_self V (X.cpu.gpr.rsp - 8) (toBytesLE X.cpu.gpr.rbx 8) (toBytesLE_length _ _) hq8,
      ofBytesLE_toBytesLE (n := 8) rfl]
  have hr1 : rdq(V1 V X.cpu.gpr, X.cpu.gpr.rsp) = e₂.add j₂ := by
    show ofBytesLE 64 (List.map (Vst V _ (toBytesLE X.cpu.gpr.rbx 8)) (byteAddrs _ 8)) = _
    rw [Tun.rd_Vst V (X.cpu.gpr.rsp - 8) (toBytesLE X.cpu.gpr.rbx 8) X.cpu.gpr.rsp 8
      (by rw [toBytesLE_length]; exact hq8) hp8 (by rw [toBytesLE_length, tn8]; omega)]
    exact hra
  -- the bytes stored by `mov qword [rbx + 256], 0`
  have m0 : ∀ (W : Addr → Byte) (x : Addr), x.toNat + 8 ≤ 2 ^ 64 →
      ((X.cpu.gpr.rdi + 256#64).toNat + 8 ≤ x.toNat ∨ x.toNat + 8 ≤ (X.cpu.gpr.rdi + 256#64).toNat) →
      (byteAddrs x 8).map (Vst W (X.cpu.gpr.rdi + 256#64) (toBytesLE 0#64 8)) = (byteAddrs x 8).map W :=
    fun W x hx h => Tun.rd_Vst W _ _ x 8 (by rw [toBytesLE_length]; exact hq) hx (by rw [toBytesLE_length]; exact h)
  by_cases hs : s V X.cpu.gpr = 0
  · -- `_inStream` not set
    refine (c_0 prof).run c hin (fun j' g' _ V' => j' = 37 ∧
        g' = { X.cpu.gpr with rbx := X.cpu.gpr.rdi, rsp := X.cpu.gpr.rsp - 8, rdi := 0#64 } ∧
        V' = V1 V X.cpu.gpr) hK hA (by rw [addr_add_zero]; exact hrip) (vc_0z hs hs1 fa) ?_
    rintro j' g fl V₁ ⟨rfl, rfl, hV₁⟩ Y t₁ hKY hAY hrY hgY -
    subst V₁
    have hsY : Y.cpu.gpr.rsp = X.cpu.gpr.rsp - 8 := by rw [hgY]
    refine (c_37 prof).run c hin (fun j' g' _ V' => j' = 40 ∧
        g' = { Y.cpu.gpr with rax := 0#64, rbx := X.cpu.gpr.rbx, rsp := X.cpu.gpr.rsp } ∧
        V' = V1 V X.cpu.gpr) hKY hAY hrY
      (vc_37 (by rw [hsY]; exact h8) fun _ => ⟨rfl, by rw [hsY, hb1, e8], rfl⟩) ?_
    rintro j' g fl V₂ ⟨rfl, rfl, hV₂⟩ U t₂ hKU hAU hrU hgU -
    subst V₂
    have hsU : U.cpu.gpr.rsp = X.cpu.gpr.rsp := by rw [hgU]
    refine c.s_ret hKU hAU hin (lt_len (by decide)) hrU (ret_40 _) (by rw [hsU]; exact hl) hin₂ h₂
      (by rw [hsU]; exact hr1) ?_
    rintro Z t₃ hKZ hAZ ⟨hrZ, hgZ⟩
    refine k0 hs Z t₃ hKZ hAZ hrZ ?_
    rw [hgZ, hgU, hgY]
    try rfl
  · -- `_inStream` set: to the `call`
    refine (c_0 prof).run c hin (fun j' g' _ V' => j' = 23 ∧ g' = gC V X.cpu.gpr ∧ V' = V1 V X.cpu.gpr) hK hA
      (by rw [addr_add_zero]; exact hrip) (vc_0n hs hs1 fa (fs hs)) ?_
    rintro j' g fl V₁ ⟨rfl, rfl, hV₁⟩ Y t₁ hKY hAY hrY hgY -
    subst V₁
    have hsY : Y.cpu.gpr.rsp = X.cpu.gpr.rsp - 8 := by rw [hgY]
    have he : eaD Y 0 16 = vt V X.cpu.gpr + 16#64 := by
      show Y.cpu.gpr.get (regOf 0) + BitVec.ofNat 64 16 = _
      rw [hgY]
      rfl
    have hst : ∀ i < 8, Foot Wl (Addr.add (Y.cpu.gpr.rsp - 8) i) := by rw [hsY, e16]; exact hs2 hs
    refine c.s_callM hKY hAY hin (lt_len (by decide)) hrY (call_23 _) (by rw [he]; exact fb hs) hinF hF0
      (by rw [he]; exact htgt hs) hst ?_
    rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
    rw [hsY, e16] at hA₂
    have hg₂' : Y₂.cpu.gpr = (gC V X.cpu.gpr).set 4 (X.cpu.gpr.rsp - 16) := by
      rw [hg₂, hgY]
      exact congrArg (fun v => (gC V X.cpu.gpr).set 4 v) e16
    refine kf hs Y₂ t₂ hK₂ hA₂ hr₂ hg₂' ?_
    -- back from the callee
    intro Z V' t'' hKZ hAZ hrZ hzs hzb hb hr' hPc
    have hb' : rdq(Vst V' (X.cpu.gpr.rdi + 256#64) (toBytesLE 0#64 8), X.cpu.gpr.rsp - 8) = X.cpu.gpr.rbx := by
      rw [m0 V' _ hq8 (by rw [tn8]; omega)]
      exact hb
    have hr'' : rdq(Vst V' (X.cpu.gpr.rdi + 256#64) (toBytesLE 0#64 8), X.cpu.gpr.rsp) = e₂.add j₂ := by
      rw [m0 V' _ hp8 (by omega)]
      exact hr'
    refine (c_26 prof).run c hin (fun j' g' _ V'' => j' = 37 ∧ g' = Z.cpu.gpr ∧
        V'' = Vst V' (X.cpu.gpr.rdi + 256#64) (toBytesLE 0#64 8)) hKZ hAZ hrZ
      (vc_26 (by rw [hzb]; exact fw hs) fun _ => ⟨rfl, rfl, by rw [hzb]⟩) ?_
    rintro j' g fl V₂ ⟨rfl, rfl, hV₂⟩ U t₃ hKU hAU hrU hgU -
    subst V₂
    have hsU : U.cpu.gpr.rsp = X.cpu.gpr.rsp - 8 := by rw [hgU, hzs]
    refine (c_37 prof).run c hin (fun j' g' _ V'' => j' = 40 ∧
        g' = { Z.cpu.gpr with rax := 0#64, rbx := X.cpu.gpr.rbx, rsp := X.cpu.gpr.rsp } ∧
        V'' = Vst V' (X.cpu.gpr.rdi + 256#64) (toBytesLE 0#64 8)) hKU hAU hrU
      (vc_37 (by rw [hsU]; exact h8) fun _ => ⟨rfl, by rw [hsU, hb', e8, hgU], rfl⟩) ?_
    rintro j' g fl V₃ ⟨rfl, rfl, hV₃⟩ U' t₄ hKU' hAU' hrU' hgU' -
    subst V₃
    have hsU' : U'.cpu.gpr.rsp = X.cpu.gpr.rsp := by rw [hgU']
    refine c.s_ret hKU' hAU' hin (lt_len (by decide)) hrU' (ret_40 _) (by rw [hsU']; exact hl) hin₂ h₂
      (by rw [hsU']; exact hr'') ?_
    rintro Z' t₅ hKZ' hAZ' ⟨hrZ', hgZ'⟩
    refine kr Z V' Z' t₅ hPc hKZ' hAZ' hrZ' ?_
    rw [hgZ', hgU']
    try rfl

end FV7z.Ris
