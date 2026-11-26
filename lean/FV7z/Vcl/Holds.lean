import FV7z.Vcl.Cuts
import FV7z.Sfs.Cuts
import FV7z.Lemmas.LeafRet
import FV7z.Tun.Inv
/-!
# `VariantClear` (PLAN.md §M, M1)

7-Zip 26.06's `VariantClear (prop)` at `0x5a0120` in `7zzs` (`CPP/Common/MyWindows.cpp`): if the 16-bit type tag
`prop->vt` (the 2 bytes at `prop`) is `VT_BSTR` (8), `SysFreeString (prop->bstrVal)` (the 8 bytes at `prop + 8`;
`call` at 36 to `Sfs.sfs_at`); then `prop->vt = VT_EMPTY` (0) and the result `S_OK` (0). `push rbx`, `rbx` = `prop`
across the call, `pop rbx; ret` (22 or 49).

The callee is a hypothesis (`kf`), as in `FV7z/Lfp/Holds.lean`: a continuation at its entry, given the run from its
return (`vcl_at + 41`, `rsp` 8 below the entry's, `rbx` = `prop`, the saved `rbx` and the return address left as they
were, and the callee's own post `Pc`) to the return address.

- `gC`: the registers at the `call`.
- `vc_n`, `vc_y`, `vc_41`: the verification conditions of the pieces (the tag not 8; 8, to the `call`; after it).
- `vcl_ok`: from the entry to the return address with the tag 0 and `rax` = 0 (`kn`), or through the callee (`kf`,
  `kr`).
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Vcl

/-- The `call` to `SysFreeString`. -/
def pcall : List Byte := [0xe8, 0x77, 0xff, 0xff, 0xff]
theorem pcall_0 : ∀ feat, Dec feat pcall 0 (FV7z.mk .call 64 [.rel 18446744073709551479] 5) := by dec_rfl
theorem wc_36 : pcall <+: vcl.drop 36 := by decide +kernel
theorem call_36 (feat : Features) : Dec feat vcl 36 (FV7z.mk .call 64 [.rel 18446744073709551479] 5) :=
  Dec.shift (j := 36) (k := 0) (pcall_0 feat) wc_36 (Nat.zero_le _)

/-- The `ret`s. -/
def pret : List Byte := [0xc3]
theorem pret_0 : ∀ feat, Dec feat pret 0 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem w_22 : pret <+: vcl.drop 22 := by decide +kernel
theorem ret_22 (feat : Features) : Dec feat vcl 22 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 22) (k := 0) (pret_0 feat) w_22 (Nat.zero_le _)
theorem w_49 : pret <+: vcl.drop 49 := by decide +kernel
theorem ret_49 (feat : Features) : Dec feat vcl 49 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 49) (k := 0) (pret_0 feat) w_49 (Nat.zero_le _)

/-- The registers at the `call`: `rbx` = `prop`, `rdi` = `prop->bstrVal`, `rbx` pushed. -/
abbrev gC (V : Addr → Byte) (g : Gprs) : Gprs :=
  { g with rbx := g.rdi, rsp := g.rsp - 8, rdi := rdq(V, g.rdi + 8#64) }

variable {F : Footprint} {Wl : List Rgn}

/-- The tag not 8: `push rbx; cmp word [rdi], 8; mov rbx, rdi`, then `xor eax, eax; mov [rbx], ax; xor eax, eax;
pop rbx` to the `ret` at 22. -/
theorem vc_n {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (hst : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8) i)) (ft : ∀ i < 2, Foot F.data (Addr.add g.rdi i))
    (fw : ∀ i < 2, Foot Wl (Addr.add g.rdi i)) (hl : ∀ i < 8, Foot F.data (Addr.add (g.rsp - 8) i))
    (ht : ofBytesLE 16 ((byteAddrs g.rdi 2).map (Vst V (g.rsp - 8) (toBytesLE g.rbx 8))) ≠ 8#16) :
    W_0 F Wl (fun j' g' _ V' => j' = 22 ∧
      g' = { g with
          rax := 0#64,
          rbx := rdq(Vst (Vst V (g.rsp - 8) (toBytesLE g.rbx 8)) g.rdi (toBytesLE 0#16 2), g.rsp - 8),
          rsp := g.rsp - 8 + 8 } ∧
      V' = Vst (Vst V (g.rsp - 8) (toBytesLE g.rbx 8)) g.rdi (toBytesLE 0#16 2)) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hst ft fw hl ht ⊢
  wpx [W_0, W_14, W_32, o0, o1, o2, Op.cmpmi, ht, BitVec.xor_self, BitVec.setWidth_zero, decide_false,
    decide_true, Bool.false_eq_true, Bool.true_eq_false, false_implies, implies_true]
  all_goals repeat'
    first
    | exact rfl
    | assumption
    | exact trivial
    | (intro h; exact absurd h (by decide))
    | apply And.intro
    | intro _

/-- The tag 8: `push rbx; cmp word [rdi], 8; mov rbx, rdi`, then `mov rdi, [rdi + 8]` to the `call` at 36. -/
theorem vc_y {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (hst : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8) i)) (ft : ∀ i < 2, Foot F.data (Addr.add g.rdi i))
    (fb : ∀ i < 8, Foot F.data (Addr.add (g.rdi + 8#64) i))
    (ht : ofBytesLE 16 ((byteAddrs g.rdi 2).map (Vst V (g.rsp - 8) (toBytesLE g.rbx 8))) = 8#16)
    (hx : rdq(Vst V (g.rsp - 8) (toBytesLE g.rbx 8), g.rdi + 8#64) = rdq(V, g.rdi + 8#64)) :
    W_0 F Wl (fun j' g' _ V' => j' = 36 ∧ g' = gC V g ∧ V' = Vst V (g.rsp - 8) (toBytesLE g.rbx 8)) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hst ft fb ht hx ⊢
  wpx [W_0, W_14, W_32, o0, o1, o2, Op.cmpmi, gC, ht, hx, decide_false, decide_true, Bool.false_eq_true,
    Bool.true_eq_false, false_implies, implies_true]
  all_goals repeat'
    first
    | exact rfl
    | assumption
    | exact trivial
    | (intro h; exact absurd h (by decide))
    | apply And.intro
    | intro _

/-- Back from the callee: `xor eax, eax; mov [rbx], ax; xor eax, eax; pop rbx` to the `ret` at 49. -/
theorem vc_41 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (hw : ∀ i < 2, Foot Wl (Addr.add g.rbx i)) (hl : ∀ i < 8, Foot F.data (Addr.add g.rsp i))
    (h : ∀ fl, Q 49 { g with rax := 0#64, rbx := rdq(Vst V g.rbx (toBytesLE 0#16 2), g.rsp), rsp := g.rsp + 8 } fl
      (Vst V g.rbx (toBytesLE 0#16 2))) :
    W_41 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hw hl h ⊢
  wpx [W_41, o1, BitVec.xor_self, BitVec.setWidth_zero]
  all_goals repeat' (first | exact h _ | assumption | exact trivial | apply And.intro | intro _)

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {X : State} {t : Nat} {V : Addr → Byte}

/-- `VariantClear (prop)` (`prop` = `rdi`) from its entry. The tag not 8: at the return address with the tag 0, `rax`
= 0, the other registers as at the entry (`kn`). The tag 8: at `SysFreeString`'s entry the registers are `gC` with `rsp`
16 below the entry's and the bytes `V` with `rbx` and the return address into `VariantClear` pushed (`kf`); if the
callee returns to `vcl_at + 41` with `rsp` and `rbx` as at its entry, and the saved `rbx` and the return address of
`VariantClear` as they were, the run reaches that return address with the tag 0, `rax` = 0 and `rbx`, `rsp` restored
(`kr`). -/
theorem vcl_ok {Pc : State → (Addr → Byte) → Prop} (c : Seg prof F Wl L s₀ o) (hin : CodeIn L vcl_at vcl)
    (hinS : CodeIn L Sfs.sfs_at Sfs.sfs)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = vcl_at)
    (hp : 16 ≤ X.cpu.gpr.rsp.toNat) (hp8 : X.cpu.gpr.rsp.toNat + 8 ≤ 2 ^ 64)
    (hs1 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8) i))
    (hs2 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 16) i))
    (hl : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsp i))
    (fw : ∀ i < 2, Foot Wl (Addr.add X.cpu.gpr.rdi i)) (hq : X.cpu.gpr.rdi.toNat + 2 ≤ 2 ^ 64)
    (hd : X.cpu.gpr.rdi.toNat + 2 ≤ X.cpu.gpr.rsp.toNat - 16 ∨ X.cpu.gpr.rsp.toNat + 8 ≤ X.cpu.gpr.rdi.toNat)
    (fb : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rdi + 8#64) i))
    (hq' : (X.cpu.gpr.rdi + 8#64).toNat + 8 ≤ 2 ^ 64)
    (hdb : (X.cpu.gpr.rdi + 8#64).toNat + 8 ≤ X.cpu.gpr.rsp.toNat - 8 ∨
      X.cpu.gpr.rsp.toNat ≤ (X.cpu.gpr.rdi + 8#64).toNat)
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (hra : rdq(V, X.cpu.gpr.rsp) = e₂.add j₂)
    (kn : ofBytesLE 16 ((byteAddrs X.cpu.gpr.rdi 2).map V) ≠ 8#16 → ∀ (Z : State) (t' : Nat), KeptW Wl s₀ Z →
      Agree F Z.proc.mm.mem
        (Vst (Vst V (X.cpu.gpr.rsp - 8) (toBytesLE X.cpu.gpr.rbx 8)) X.cpu.gpr.rdi (toBytesLE 0#16 2)) →
      Z.cpu.rip = e₂.add j₂ → Z.cpu.gpr = { X.cpu.gpr with rax := 0#64, rsp := X.cpu.gpr.rsp + 8 } →
      GoG prof L o gev gP gE Z t')
    (kf : ofBytesLE 16 ((byteAddrs X.cpu.gpr.rdi 2).map V) = 8#16 → ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y →
      Agree F Y.proc.mm.mem (Vst (Vst V (X.cpu.gpr.rsp - 8) (toBytesLE X.cpu.gpr.rbx 8)) (X.cpu.gpr.rsp - 16)
        (toBytesLE (vcl_at.add 41) 8)) →
      Y.cpu.rip = Sfs.sfs_at → Y.cpu.gpr = (gC V X.cpu.gpr).set 4 (X.cpu.gpr.rsp - 16) →
      (∀ (Z : State) (V' : Addr → Byte) (t'' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V' →
        Z.cpu.rip = vcl_at.add 41 → Z.cpu.gpr.rsp = X.cpu.gpr.rsp - 8 → Z.cpu.gpr.rbx = X.cpu.gpr.rdi →
        rdq(V', X.cpu.gpr.rsp - 8) = X.cpu.gpr.rbx → rdq(V', X.cpu.gpr.rsp) = e₂.add j₂ → Pc Z V' →
        GoG prof L o gev gP gE Z t'') →
      GoG prof L o gev gP gE Y t')
    (kr : ∀ (Z : State) (V' : Addr → Byte) (Z' : State) (t' : Nat), Pc Z V' → KeptW Wl s₀ Z' →
      Agree F Z'.proc.mm.mem (Vst V' X.cpu.gpr.rdi (toBytesLE 0#16 2)) → Z'.cpu.rip = e₂.add j₂ →
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
  -- the bytes stored by `push rbx` and by `mov word [rbx], ax`
  have m8 : ∀ (x : Addr) (n : Nat), x.toNat + n ≤ 2 ^ 64 →
      (x.toNat + n ≤ X.cpu.gpr.rsp.toNat - 8 ∨ X.cpu.gpr.rsp.toNat ≤ x.toNat) →
      (byteAddrs x n).map (Vst V (X.cpu.gpr.rsp - 8) (toBytesLE X.cpu.gpr.rbx 8)) = (byteAddrs x n).map V :=
    fun x n hx h => Tun.rd_Vst V _ _ x n (by rw [toBytesLE_length, tn8]; omega) hx
      (by rw [toBytesLE_length, tn8]; omega)
  have mz : ∀ (W : Addr → Byte) (x : Addr), x.toNat + 8 ≤ 2 ^ 64 →
      (X.cpu.gpr.rdi.toNat + 2 ≤ x.toNat ∨ x.toNat + 8 ≤ X.cpu.gpr.rdi.toNat) →
      (byteAddrs x 8).map (Vst W X.cpu.gpr.rdi (toBytesLE 0#16 2)) = (byteAddrs x 8).map W :=
    fun W x hx h => Tun.rd_Vst W _ _ x 8 (by rw [toBytesLE_length]; exact hq) hx (by rw [toBytesLE_length]; exact h)
  have htg : ofBytesLE 16 ((byteAddrs X.cpu.gpr.rdi 2).map (Vst V (X.cpu.gpr.rsp - 8) (toBytesLE X.cpu.gpr.rbx 8)))
      = ofBytesLE 16 ((byteAddrs X.cpu.gpr.rdi 2).map V) := by
    rw [m8 _ 2 hq (by omega)]
  have h8 : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rsp - 8) i) := fun i hi => c.hws _ (hs1 i hi)
  have hrip' : X.cpu.rip = vcl_at.add 0 := by rw [addr_add_zero]; exact hrip
  by_cases ht : ofBytesLE 16 ((byteAddrs X.cpu.gpr.rdi 2).map V) = 8#16
  · -- to the `call`
    have hx : rdq(Vst V (X.cpu.gpr.rsp - 8) (toBytesLE X.cpu.gpr.rbx 8), X.cpu.gpr.rdi + 8#64) =
        rdq(V, X.cpu.gpr.rdi + 8#64) := by
      rw [m8 _ 8 hq' hdb]
    refine (c_0 prof).run c hin (fun j' g' _ V' => j' = 36 ∧ g' = gC V X.cpu.gpr ∧
        V' = Vst V (X.cpu.gpr.rsp - 8) (toBytesLE X.cpu.gpr.rbx 8)) hK hA hrip'
      (vc_y hs1 (fun i hi => c.hws _ (fw i hi)) fb (by rw [htg]; exact ht) hx) ?_
    rintro j' g fl V₁ ⟨rfl, rfl, hV₁⟩ Y t₁ hKY hAY hrY hgY -
    subst V₁
    have hsY : Y.cpu.gpr.rsp = X.cpu.gpr.rsp - 8 := by rw [hgY]
    have hst : ∀ i < 8, Foot Wl (Addr.add (Y.cpu.gpr.rsp - 8) i) := by rw [hsY, e16]; exact hs2
    refine c.s_call hKY hAY hin (lt_len (by decide)) hrY (call_36 _) hinS (Sfs.lt_len (by decide)) (by decide)
      hst ?_
    rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
    rw [hsY, e16] at hA₂
    have hg₂' : Y₂.cpu.gpr = (gC V X.cpu.gpr).set 4 (X.cpu.gpr.rsp - 16) := by
      rw [hg₂, hgY]
      exact congrArg (fun v => (gC V X.cpu.gpr).set 4 v) e16
    refine kf ht Y₂ t₂ hK₂ hA₂ hr₂ hg₂' ?_
    -- back from the callee
    intro Z V' t'' hKZ hAZ hrZ hzs hzb hb hr' hPc
    have hb' : rdq(Vst V' X.cpu.gpr.rdi (toBytesLE 0#16 2), X.cpu.gpr.rsp - 8) = X.cpu.gpr.rbx := by
      rw [mz V' _ hq8 (by rw [tn8]; omega)]
      exact hb
    have hr'' : rdq(Vst V' X.cpu.gpr.rdi (toBytesLE 0#16 2), X.cpu.gpr.rsp) = e₂.add j₂ := by
      rw [mz V' _ hp8 (by omega)]
      exact hr'
    refine (c_41 prof).run c hin (fun j' g' _ V'' => j' = 49 ∧
        g' = { Z.cpu.gpr with rax := 0#64, rbx := X.cpu.gpr.rbx, rsp := X.cpu.gpr.rsp } ∧
        V'' = Vst V' X.cpu.gpr.rdi (toBytesLE 0#16 2)) hKZ hAZ hrZ
      (vc_41 (by rw [hzb]; exact fw) (by rw [hzs]; exact h8)
        fun _ => ⟨rfl, by rw [hzb, hzs, hb', e8], by rw [hzb]⟩) ?_
    rintro j' g fl V₂ ⟨rfl, rfl, hV₂⟩ U t₃ hKU hAU hrU hgU -
    subst V₂
    have hsU : U.cpu.gpr.rsp = X.cpu.gpr.rsp := by rw [hgU]
    refine c.s_ret hKU hAU hin (lt_len (by decide)) hrU (ret_49 _) (by rw [hsU]; exact hl) hin₂ h₂
      (by rw [hsU]; exact hr'') ?_
    rintro Z' t₄ hKZ' hAZ' ⟨hrZ', hgZ'⟩
    refine kr Z V' Z' t₄ hPc hKZ' hAZ' hrZ' ?_
    rw [hgZ', hgU]
    try rfl
  · -- to the `ret` at 22
    have hsb : rdq(Vst (Vst V (X.cpu.gpr.rsp - 8) (toBytesLE X.cpu.gpr.rbx 8)) X.cpu.gpr.rdi (toBytesLE 0#16 2),
        X.cpu.gpr.rsp - 8) = X.cpu.gpr.rbx := by
      rw [mz _ _ hq8 (by rw [tn8]; omega), Tun.rd_Vst_self _ _ _ (toBytesLE_length _ _) hq8,
        ofBytesLE_toBytesLE (n := 8) rfl]
    have hr'' : rdq(Vst (Vst V (X.cpu.gpr.rsp - 8) (toBytesLE X.cpu.gpr.rbx 8)) X.cpu.gpr.rdi (toBytesLE 0#16 2),
        X.cpu.gpr.rsp) = e₂.add j₂ := by
      rw [mz _ _ hp8 (by omega), m8 _ 8 hp8 (by omega)]
      exact hra
    refine (c_0 prof).run c hin (fun j' g' _ V' => j' = 22 ∧
        g' = { X.cpu.gpr with
            rax := 0#64,
            rbx := rdq(Vst (Vst V (X.cpu.gpr.rsp - 8) (toBytesLE X.cpu.gpr.rbx 8)) X.cpu.gpr.rdi (toBytesLE 0#16 2),
              X.cpu.gpr.rsp - 8),
            rsp := X.cpu.gpr.rsp - 8 + 8 } ∧
        V' = Vst (Vst V (X.cpu.gpr.rsp - 8) (toBytesLE X.cpu.gpr.rbx 8)) X.cpu.gpr.rdi (toBytesLE 0#16 2)) hK hA hrip'
      (vc_n hs1 (fun i hi => c.hws _ (fw i hi)) fw h8 (by rw [htg]; exact ht)) ?_
    rintro j' g fl V₂ ⟨rfl, rfl, hV₂⟩ U t₁ hKU hAU hrU hgU -
    subst V₂
    have hsU : U.cpu.gpr.rsp = X.cpu.gpr.rsp := by rw [hgU]; exact e8
    refine c.s_ret hKU hAU hin (lt_len (by decide)) hrU (ret_22 _) (by rw [hsU]; exact hl) hin₂ h₂
      (by rw [hsU]; exact hr'') ?_
    rintro Z t₂ hKZ hAZ ⟨hrZ, hgZ⟩
    refine kn ht Z t₂ hKZ hAZ hrZ ?_
    rw [hgZ, hgU, hsb, e8]
    try rfl

end FV7z.Vcl
