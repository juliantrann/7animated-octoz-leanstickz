import FV7z.Lfp.Cuts
import FV7z.Lemmas.LeafRet
import FV7z.Lemmas.CallM
import FV7z.Tun.Inv
/-!
# `LzmaDec_FreeProbs` (PLAN.md §M, M1)

7-Zip 26.06's `LzmaDec_FreeProbs (p, alloc)` at `0x42bde0` in `7zzs` (`C/LzmaDec.c`):
`ISzAlloc_Free (alloc, p->probs); p->probs = NULL`. `push rbx`, `rbx` = `p`, `rsi` = `p->probs` (the 8 bytes at
`p + 8`), `rdi` = `alloc`, `call qword [alloc + 8]` (18, `Seg.s_callM`), then `p->probs` = 0, `pop rbx; ret`.

The callee (`alloc->Free`) is a hypothesis (`kf`): a continuation at its entry, given the run from its return
(`lfp_at + 21`, `rsp` 8 below the entry's, `rbx` = `p`, the saved `rbx` and the return address left as they were,
and the callee's own post `Pc`) to the return address.

- `gC`: the registers at the `call`.
- `vc_0`, `vc_21`: the verification conditions of the two pieces.
- `lfp_ok`: from the entry, through the callee, to the return address with `p->probs` = 0 and `rbx` restored.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Lfp

/-- The `call` through `alloc->Free`. -/
def pcall : List Byte := [0xff, 0x50, 0x08]
theorem pcall_0 : ∀ feat, Dec feat pcall 0 (FV7z.mk .call 64 [.mem (mbd 0 8 64)] 3) := by dec_rfl
theorem wc_18 : pcall <+: lfp.drop 18 := by decide +kernel
theorem call_18 (feat : Features) : Dec feat lfp 18 (FV7z.mk .call 64 [.mem (mbd 0 8 64)] 3) :=
  Dec.shift (j := 18) (k := 0) (pcall_0 feat) wc_18 (Nat.zero_le _)

/-- The `ret`. -/
def pret : List Byte := [0xc3]
theorem pret_0 : ∀ feat, Dec feat pret 0 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem w_30 : pret <+: lfp.drop 30 := by decide +kernel
theorem ret_30 (feat : Features) : Dec feat lfp 30 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 30) (k := 0) (pret_0 feat) w_30 (Nat.zero_le _)

/-- The registers at the `call`: `rbx` = `p`, `rsi` = `p->probs`, `rax` = `rdi` = `alloc`, `rbx` pushed. -/
abbrev gC (V : Addr → Byte) (g : Gprs) : Gprs :=
  { g with rax := g.rsi, rbx := g.rdi, rsp := g.rsp - 8, rsi := rdq(V, g.rdi + 8#64), rdi := g.rsi }

variable {F : Footprint} {Wl : List Rgn}

/-- `push rbx; mov rax, rsi; mov rbx, rdi; mov rsi, [rdi + 8]; mov rdi, rax`. -/
theorem vc_0 {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (hst : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8) i)) (fa : ∀ i < 8, Foot F.data (Addr.add (g.rdi + 8#64) i))
    (hx : rdq(Vst V (g.rsp - 8) (toBytesLE g.rbx 8), g.rdi + 8#64) = rdq(V, g.rdi + 8#64)) :
    wp F Wl o0 (fun g' _ V' => g' = gC V g ∧ V' = Vst V (g.rsp - 8) (toBytesLE g.rbx 8)) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hst fa hx ⊢
  wpx [o0, gC, hx]
  first
  | exact ⟨hst, fa⟩
  | exact ⟨hst, fa, rfl, rfl⟩
  | (refine ⟨hst, fa, ?_⟩; simp only [hx])

/-- `mov qword [rbx + 8], 0; pop rbx`. -/
theorem vc_21 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (hw : ∀ i < 8, Foot Wl (Addr.add (g.rbx + 8#64) i)) (hl : ∀ i < 8, Foot F.data (Addr.add g.rsp i))
    (h : ∀ fl, Q 30 { g with rbx := rdq(Vst V (g.rbx + 8#64) (toBytesLE 0#64 8), g.rsp), rsp := g.rsp + 8 } fl
      (Vst V (g.rbx + 8#64) (toBytesLE 0#64 8))) :
    W_21 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hw hl h ⊢
  wpx [W_21, o1]
  first
  | exact ⟨hw, hl, h _⟩
  | exact ⟨hw, by simpa using hl, h _⟩
  | (refine ⟨hw, ?_⟩; simpa using ⟨hl, h _⟩)

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {X : State} {t : Nat} {V : Addr → Byte}

/-- `LzmaDec_FreeProbs (p, alloc)` (`p` = `rdi`, `alloc` = `rsi`) from its entry. At the callee's entry `eF` (the 8
bytes at `alloc + 8`) the registers are `gC` with `rsp` 16 below the entry's and the bytes `V` with `rbx` and the
return address into `LzmaDec_FreeProbs` pushed (`kf`); if the callee returns to `lfp_at + 21` with `rsp` and `rbx` as
at its entry, and the saved `rbx` and the return address of `LzmaDec_FreeProbs` as they were, the run reaches that
return address with `p->probs` = 0 and `rbx`, `rsp` restored (`kr`). -/
theorem lfp_ok {Pc : State → (Addr → Byte) → Prop} (c : Seg prof F Wl L s₀ o) (hin : CodeIn L lfp_at lfp)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = lfp_at)
    (hp : 16 ≤ X.cpu.gpr.rsp.toNat) (hp8 : X.cpu.gpr.rsp.toNat + 8 ≤ 2 ^ 64)
    (hs1 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8) i))
    (hs2 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 16) i))
    (hl : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsp i))
    (fw : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rdi + 8#64) i)) (hq : (X.cpu.gpr.rdi + 8#64).toNat + 8 ≤ 2 ^ 64)
    (hdp : (X.cpu.gpr.rdi + 8#64).toNat + 8 ≤ X.cpu.gpr.rsp.toNat - 8 ∨
      X.cpu.gpr.rsp.toNat + 8 ≤ (X.cpu.gpr.rdi + 8#64).toNat)
    (fb : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rsi + 8#64) i))
    (hq' : (X.cpu.gpr.rsi + 8#64).toNat + 8 ≤ 2 ^ 64)
    (hda : (X.cpu.gpr.rsi + 8#64).toNat + 8 ≤ X.cpu.gpr.rsp.toNat - 8 ∨
      X.cpu.gpr.rsp.toNat ≤ (X.cpu.gpr.rsi + 8#64).toNat)
    {eF : Addr} {codeF : List Byte} (hinF : CodeIn L eF codeF) (hF0 : 0 < codeF.length)
    (htgt : rdq(V, X.cpu.gpr.rsi + 8#64) = eF)
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (hra : rdq(V, X.cpu.gpr.rsp) = e₂.add j₂)
    (kf : ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y →
      Agree F Y.proc.mm.mem (Vst (Vst V (X.cpu.gpr.rsp - 8) (toBytesLE X.cpu.gpr.rbx 8)) (X.cpu.gpr.rsp - 16)
        (toBytesLE (lfp_at.add 21) 8)) →
      Y.cpu.rip = eF → Y.cpu.gpr = (gC V X.cpu.gpr).set 4 (X.cpu.gpr.rsp - 16) →
      (∀ (Z : State) (V' : Addr → Byte) (t'' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V' →
        Z.cpu.rip = lfp_at.add 21 → Z.cpu.gpr.rsp = X.cpu.gpr.rsp - 8 → Z.cpu.gpr.rbx = X.cpu.gpr.rdi →
        rdq(V', X.cpu.gpr.rsp - 8) = X.cpu.gpr.rbx → rdq(V', X.cpu.gpr.rsp) = e₂.add j₂ → Pc Z V' →
        GoG prof L o gev gP gE Z t'') →
      GoG prof L o gev gP gE Y t')
    (kr : ∀ (Z : State) (V' : Addr → Byte) (Z' : State) (t' : Nat), Pc Z V' → KeptW Wl s₀ Z' →
      Agree F Z'.proc.mm.mem (Vst V' (X.cpu.gpr.rdi + 8#64) (toBytesLE 0#64 8)) → Z'.cpu.rip = e₂.add j₂ →
      Z'.cpu.gpr = { Z.cpu.gpr with rbx := X.cpu.gpr.rbx, rsp := X.cpu.gpr.rsp + 8 } →
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
  -- the bytes stored by `push rbx` and by `mov qword [rbx + 8], 0`
  have m8 : ∀ (x : Addr) (n : Nat), x.toNat + n ≤ 2 ^ 64 →
      (x.toNat + n ≤ X.cpu.gpr.rsp.toNat - 8 ∨ X.cpu.gpr.rsp.toNat ≤ x.toNat) →
      (byteAddrs x n).map (Vst V (X.cpu.gpr.rsp - 8) (toBytesLE X.cpu.gpr.rbx 8)) = (byteAddrs x n).map V :=
    fun x n hx h => Tun.rd_Vst V _ _ x n (by rw [toBytesLE_length, tn8]; omega) hx
      (by rw [toBytesLE_length, tn8]; omega)
  have m0 : ∀ (W : Addr → Byte) (x : Addr), x.toNat + 8 ≤ 2 ^ 64 →
      ((X.cpu.gpr.rdi + 8#64).toNat + 8 ≤ x.toNat ∨ x.toNat + 8 ≤ (X.cpu.gpr.rdi + 8#64).toNat) →
      (byteAddrs x 8).map (Vst W (X.cpu.gpr.rdi + 8#64) (toBytesLE 0#64 8)) = (byteAddrs x 8).map W :=
    fun W x hx h => Tun.rd_Vst W _ _ x 8 (by rw [toBytesLE_length]; exact hq) hx (by rw [toBytesLE_length]; exact h)
  have hx : rdq(Vst V (X.cpu.gpr.rsp - 8) (toBytesLE X.cpu.gpr.rbx 8), X.cpu.gpr.rdi + 8#64) =
      rdq(V, X.cpu.gpr.rdi + 8#64) := by
    rw [m8 _ 8 hq (by omega)]
  have h8 : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rsp - 8) i) := fun i hi => c.hws _ (hs1 i hi)
  -- to the `call`
  refine (c_0 prof).run c hin (fun j' g' _ V' => j' = 18 ∧ g' = gC V X.cpu.gpr ∧
      V' = Vst V (X.cpu.gpr.rsp - 8) (toBytesLE X.cpu.gpr.rbx 8)) hK hA (by rw [addr_add_zero]; exact hrip)
    (wp_mono o0 (fun _ _ _ h => ⟨rfl, h⟩) (vc_0 hs1 (fun i hi => c.hws _ (fw i hi)) hx)) ?_
  rintro j' g fl V₁ ⟨rfl, rfl, hV₁⟩ Y t₁ hKY hAY hrY hgY -
  subst V₁
  have hsY : Y.cpu.gpr.rsp = X.cpu.gpr.rsp - 8 := by rw [hgY]
  have he : eaD Y 0 8 = X.cpu.gpr.rsi + 8#64 := by
    show Y.cpu.gpr.get (regOf 0) + BitVec.ofNat 64 8 = _
    rw [hgY]
    rfl
  have hst : ∀ i < 8, Foot Wl (Addr.add (Y.cpu.gpr.rsp - 8) i) := by rw [hsY, e16]; exact hs2
  refine c.s_callM hKY hAY hin (lt_len (by decide)) hrY (call_18 _) (by rw [he]; exact fb) hinF hF0
    (by rw [he, m8 _ 8 hq' hda]; exact htgt) hst ?_
  rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
  rw [hsY, e16] at hA₂
  have hg₂' : Y₂.cpu.gpr = (gC V X.cpu.gpr).set 4 (X.cpu.gpr.rsp - 16) := by
    rw [hg₂, hgY]
    exact congrArg (fun v => (gC V X.cpu.gpr).set 4 v) e16
  refine kf Y₂ t₂ hK₂ hA₂ hr₂ hg₂' ?_
  -- back from the callee
  intro Z V' t'' hKZ hAZ hrZ hzs hzb hb hr' hPc
  have hb' : rdq(Vst V' (X.cpu.gpr.rdi + 8#64) (toBytesLE 0#64 8), X.cpu.gpr.rsp - 8) = X.cpu.gpr.rbx := by
    rw [m0 V' _ hq8 (by rw [tn8]; omega)]
    exact hb
  have hr'' : rdq(Vst V' (X.cpu.gpr.rdi + 8#64) (toBytesLE 0#64 8), X.cpu.gpr.rsp) = e₂.add j₂ := by
    rw [m0 V' _ hp8 (by omega)]
    exact hr'
  refine (c_21 prof).run c hin (fun j' g' _ V'' => j' = 30 ∧
      g' = { Z.cpu.gpr with rbx := X.cpu.gpr.rbx, rsp := X.cpu.gpr.rsp } ∧
      V'' = Vst V' (X.cpu.gpr.rdi + 8#64) (toBytesLE 0#64 8)) hKZ hAZ hrZ
    (vc_21 (by rw [hzb]; exact fw) (by rw [hzs]; exact h8)
      fun _ => ⟨rfl, by rw [hzb, hzs, hb', e8], by rw [hzb]⟩) ?_
  rintro j' g fl V₂ ⟨rfl, rfl, hV₂⟩ U t₃ hKU hAU hrU hgU -
  subst V₂
  have hsU : U.cpu.gpr.rsp = X.cpu.gpr.rsp := by rw [hgU]
  refine c.s_ret hKU hAU hin (lt_len (by decide)) hrU (ret_30 _) (by rw [hsU]; exact hl) hin₂ h₂
    (by rw [hsU]; exact hr'') ?_
  rintro Z' t₄ hKZ' hAZ' ⟨hrZ', hgZ'⟩
  refine kr Z V' Z' t₄ hPc hKZ' hAZ' hrZ' ?_
  rw [hgZ', hgU]
  try rfl

end FV7z.Lfp
