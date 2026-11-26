import FV7z.Pvd.Cuts
import FV7z.Vcl.Code
import FV7z.Lemmas.LeafRet
import FV7z.Lemmas.CmpImm
/-!
# `CPropVariant::~CPropVariant` (PLAN.md §M, M1)

7-Zip 26.06's `NWindows::NCOM::CPropVariant::~CPropVariant ()` at `0x456f60` in `7zzs`
(`CPP/Windows/PropVariant.h`, `InternalClear` inlined as `PropVariant_Clear`'s test), `this` = `rdi`: the 16-bit
type tag `vt` (the 2 bytes at `this`) zero-extended into `eax`; if `vt ≤ 7` (unsigned), to the `ret` at 56; else
`eax -= 10`, and if `ax ≤ 54` and bit `eax` of `0x40000000003fc3` is set (`vt` one of 10, 11, 16..23, 64: nothing to
free), to the `ret` at 52; else `sub rsp, 8`, `VariantClear (this)` (`call` at 42 to `Vcl.vcl_at`), `add rsp, 8`
and the `ret` at 51.

The callee is a hypothesis (`kf`), as in `FV7z/Vcl/Holds.lean`: a continuation at its entry, given the run from its
return (`pvd_at + 47`, `rsp` 8 below the entry's, the return address of the destructor as it was, and the callee's own
post `Pc`) to that return address (`kr`).

- `vtOf V g`: the type tag; `yOf x`: `eax` after `sub eax, 10`; `Simple x`: no call (the `ret` at 56 or 52).
- `vc_le7`, `vc_ja`, `vc_bit`, `vc_nobit`, `vc_38`, `vc_47`: the verification conditions of the pieces.
- `pvd_ok`: from the entry to the return address, directly (`kS`) or through `VariantClear` (`kf`, `kr`).
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Pvd

theorem pvd_42 : ∀ feat, Dec feat pvd 42 (FV7z.mk .call 64 [.rel 1347985] 5) := by intro feat f; rfl
theorem pvd_51 : ∀ feat, Dec feat pvd 51 (FV7z.mk .ret 64 [] 1) := by intro feat f; rfl
theorem pvd_52 : ∀ feat, Dec feat pvd 52 (FV7z.mk .ret 64 [] 1) := by intro feat f; rfl
theorem pvd_56 : ∀ feat, Dec feat pvd 56 (FV7z.mk .ret 64 [] 1) := by intro feat f; rfl

/-- The type tag `vt`: the 2 bytes at `this`. -/
abbrev vtOf (V : Addr → Byte) (g : Gprs) : BitVec 16 := ofBytesLE 16 ((byteAddrs g.rdi 2).map V)

/-- `eax` after `movzx eax, word [rdi]; sub eax, 10`. -/
abbrev yOf (x : BitVec 16) : BitVec 32 := x.setWidth 32 - 10#32

/-- The mask of the type tags `vt - 10` that own nothing (`VT_ERROR`, `VT_BOOL`, `VT_I1` .. `VT_UINT` and
`VT_FILETIME`, less 10). -/
abbrev mask : BitVec 64 := 18014398509498307#64

/-- No call: `vt ≤ 7`, or `vt - 10 ≤ 54` (16 bits, unsigned) with its bit of `mask` set. -/
def Simple (x : BitVec 16) : Prop :=
  x.toNat ≤ 7 ∨ ((yOf x).setWidth 16).toNat ≤ 54 ∧ mask.getLsbD (((yOf x).setWidth 64).toNat % 64) = true

theorem sw16 (x : BitVec 16) : (x.setWidth 32).setWidth 16 = x := by
  apply BitVec.eq_of_toNat_eq
  have h := x.isLt
  simp only [BitVec.toNat_setWidth, Nat.reducePow] at h ⊢
  omega

variable {F : Footprint} {Wl : List Rgn}

/-- `vt ≤ 7`: `movzx eax, word [rdi]; cmp ax, 7; jbe`, to the `ret` at 56. -/
theorem vc_le7 {g : Gprs} {f : Rflags} {V : Addr → Byte} (ft : ∀ i < 2, Foot F.data (Addr.add g.rdi i))
    (h1 : (vtOf V g).toNat ≤ 7) :
    W_0 F Wl (fun j' g' _ V' => j' = 56 ∧ g' = { g with rax := ((vtOf V g).setWidth 32).setWidth 64 } ∧ V' = V)
      g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  have h1' := decide_eq_true h1
  dsimp only [vtOf] at ft h1' ⊢
  wpx [W_0, W_13, W_22, o0, o1, o2, Op.bt64, sw16, be_imm (w := 16) _ 7 (by decide),
    be_imm (w := 16) _ 54 (by decide), h1', Bool.not_true, Bool.not_false, Bool.false_eq_true, Bool.true_eq_false,
    false_implies, implies_true]
  all_goals repeat'
    first
    | exact rfl
    | assumption
    | exact trivial
    | (intro h; exact absurd h (by decide))
    | apply And.intro
    | intro _

/-- `vt > 7`, `vt - 10 > 54`: `sub eax, 10; cmp ax, 54; ja`, to `sub rsp, 8` at 38. -/
theorem vc_ja {g : Gprs} {f : Rflags} {V : Addr → Byte} (ft : ∀ i < 2, Foot F.data (Addr.add g.rdi i))
    (h1 : ¬ (vtOf V g).toNat ≤ 7) (h2 : ¬ ((yOf (vtOf V g)).setWidth 16).toNat ≤ 54) :
    W_0 F Wl (fun j' g' _ V' => j' = 38 ∧ g' = { g with rax := (yOf (vtOf V g)).setWidth 64 } ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  have h1' := decide_eq_false h1
  have h2' := decide_eq_false h2
  dsimp only [vtOf, yOf] at ft h1' h2' ⊢
  wpx [W_0, W_13, W_22, o0, o1, o2, Op.bt64, sw16, be_imm (w := 16) _ 7 (by decide),
    be_imm (w := 16) _ 54 (by decide), h1', h2', Bool.not_true, Bool.not_false, Bool.false_eq_true,
    Bool.true_eq_false, false_implies, implies_true]
  all_goals repeat'
    first
    | exact rfl
    | assumption
    | exact trivial
    | (intro h; exact absurd h (by decide))
    | apply And.intro
    | intro _

/-- `vt > 7`, `vt - 10 ≤ 54`, its bit set: `mov rdx, mask; bt rdx, rax; jb`, to the `ret` at 52. -/
theorem vc_bit {g : Gprs} {f : Rflags} {V : Addr → Byte} (ft : ∀ i < 2, Foot F.data (Addr.add g.rdi i))
    (h1 : ¬ (vtOf V g).toNat ≤ 7) (h2 : ((yOf (vtOf V g)).setWidth 16).toNat ≤ 54)
    (h3 : mask.getLsbD (((yOf (vtOf V g)).setWidth 64).toNat % 64) = true) :
    W_0 F Wl (fun j' g' _ V' => j' = 52 ∧
      g' = { g with
        rax := (yOf (vtOf V g)).setWidth 64
        rdx := mask } ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  have h1' := decide_eq_false h1
  have h2' := decide_eq_true h2
  dsimp only [vtOf, yOf, mask] at ft h1' h2' h3 ⊢
  wpx [W_0, W_13, W_22, o0, o1, o2, Op.bt64, sw16, be_imm (w := 16) _ 7 (by decide),
    be_imm (w := 16) _ 54 (by decide), h1', h2', Bool.not_true, Bool.not_false, Bool.false_eq_true,
    Bool.true_eq_false, false_implies, implies_true]
  all_goals repeat'
    first
    | exact rfl
    | assumption
    | exact trivial
    | (intro h; exact absurd h (by decide))
    | (intro h; rename_i hb; exact absurd (h3.symm.trans (hb.symm.trans h)) (by decide))
    | apply And.intro
    | intro _

/-- `vt > 7`, `vt - 10 ≤ 54`, its bit clear: `mov rdx, mask; bt rdx, rax; jb`, to `sub rsp, 8` at 38. -/
theorem vc_nobit {g : Gprs} {f : Rflags} {V : Addr → Byte} (ft : ∀ i < 2, Foot F.data (Addr.add g.rdi i))
    (h1 : ¬ (vtOf V g).toNat ≤ 7) (h2 : ((yOf (vtOf V g)).setWidth 16).toNat ≤ 54)
    (h3 : mask.getLsbD (((yOf (vtOf V g)).setWidth 64).toNat % 64) = false) :
    W_0 F Wl (fun j' g' _ V' => j' = 38 ∧
      g' = { g with
        rax := (yOf (vtOf V g)).setWidth 64
        rdx := mask } ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  have h1' := decide_eq_false h1
  have h2' := decide_eq_true h2
  dsimp only [vtOf, yOf, mask] at ft h1' h2' h3 ⊢
  wpx [W_0, W_13, W_22, o0, o1, o2, Op.bt64, sw16, be_imm (w := 16) _ 7 (by decide),
    be_imm (w := 16) _ 54 (by decide), h1', h2', Bool.not_true, Bool.not_false, Bool.false_eq_true,
    Bool.true_eq_false, false_implies, implies_true]
  all_goals repeat'
    first
    | exact rfl
    | assumption
    | exact trivial
    | (intro h; exact absurd h (by decide))
    | (intro h; rename_i hb; exact absurd (h3.symm.trans (hb.symm.trans h)) (by decide))
    | apply And.intro
    | intro _

/-- `sub rsp, 8`, to the `call` at 42. -/
theorem vc_38 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (h : ∀ fl, Q 42 { g with rsp := g.rsp - 8 } fl V) : W_38 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h ⊢
  wpx [W_38, o3]
  all_goals repeat' (first | exact h _ | assumption | exact trivial | apply And.intro | intro _)

/-- Back from `VariantClear`: `add rsp, 8`, to the `ret` at 51. -/
theorem vc_47 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (h : ∀ fl, Q 51 { g with rsp := g.rsp + 8 } fl V) : W_47 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h ⊢
  wpx [W_47, o4]
  all_goals repeat' (first | exact h _ | assumption | exact trivial | apply And.intro | intro _)

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {X : State} {t : Nat} {V : Addr → Byte}

/-- `CPropVariant::~CPropVariant ()` (`this` = `rdi`) from its entry. `vt` `Simple`: at the return address with the
bytes `V`, `rax`, `rdx` some values, the other registers as at the entry (`kS`). Else at `VariantClear`'s entry
(`Vcl.vcl_at`) with `rax`, `rdx` some values, `rsp` 16 below the entry's, the other registers as at the entry (so
`rdi` = `this`) and the bytes `V` with the return address into the destructor pushed (`kf`); if `VariantClear`
returns to `pvd_at + 47` with `rsp` as at its entry and the destructor's return address as it was, the run reaches
that return address with `rsp` 8 above the entry's, the other registers as `VariantClear` left them (`kr`). -/
theorem pvd_ok {Pc : State → (Addr → Byte) → Prop} (c : Seg prof F Wl L s₀ o) (hin : CodeIn L pvd_at pvd)
    (hinV : CodeIn L Vcl.vcl_at Vcl.vcl)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = pvd_at)
    (hp : 16 ≤ X.cpu.gpr.rsp.toNat)
    (hs2 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 16) i))
    (hl : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsp i))
    (ft : ∀ i < 2, Foot F.data (Addr.add X.cpu.gpr.rdi i))
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (hra : rdq(V, X.cpu.gpr.rsp) = e₂.add j₂)
    (kS : Simple (vtOf V X.cpu.gpr) → ∀ (Z : State) (t' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V →
      Z.cpu.rip = e₂.add j₂ →
      (∃ a d : BitVec 64, Z.cpu.gpr = { X.cpu.gpr with
        rax := a
        rdx := d
        rsp := X.cpu.gpr.rsp + 8 }) →
      GoG prof L o gev gP gE Z t')
    (kf : ¬ Simple (vtOf V X.cpu.gpr) → ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y →
      Agree F Y.proc.mm.mem (Vst V (X.cpu.gpr.rsp - 16) (toBytesLE (pvd_at.add 47) 8)) →
      Y.cpu.rip = Vcl.vcl_at →
      (∃ a d : BitVec 64, Y.cpu.gpr = { X.cpu.gpr with
        rax := a
        rdx := d
        rsp := X.cpu.gpr.rsp - 16 }) →
      (∀ (Z : State) (V' : Addr → Byte) (t'' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V' →
        Z.cpu.rip = pvd_at.add 47 → Z.cpu.gpr.rsp = X.cpu.gpr.rsp - 8 → rdq(V', X.cpu.gpr.rsp) = e₂.add j₂ →
        Pc Z V' → GoG prof L o gev gP gE Z t'') →
      GoG prof L o gev gP gE Y t')
    (kr : ∀ (Z : State) (V' : Addr → Byte) (Z' : State) (t' : Nat), Pc Z V' → KeptW Wl s₀ Z' →
      Agree F Z'.proc.mm.mem V' → Z'.cpu.rip = e₂.add j₂ →
      Z'.cpu.gpr = { Z.cpu.gpr with rsp := X.cpu.gpr.rsp + 8 } →
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
  have hrip' : X.cpu.rip = pvd_at.add 0 := by rw [addr_add_zero]; exact hrip
  -- the `ret` at 52 or 56, the registers as at the entry but `rax`, `rdx`
  have tR : ∀ {j : Nat} (a d : BitVec 64) (U : State) (t₁ : Nat), j < pvd.length →
      (∀ feat, Dec feat pvd j (FV7z.mk .ret 64 [] 1)) → Simple (vtOf V X.cpu.gpr) → KeptW Wl s₀ U →
      Agree F U.proc.mm.mem V → U.cpu.rip = pvd_at.add j →
      U.cpu.gpr = { X.cpu.gpr with
        rax := a
        rdx := d } →
      GoG prof L o gev gP gE U t₁ := by
    intro j a d U t₁ hj hdec hS hKU hAU hrU hgU
    have hsU : U.cpu.gpr.rsp = X.cpu.gpr.rsp := by rw [hgU]
    refine c.s_ret hKU hAU hin hj hrU (hdec _) (by rw [hsU]; exact hl) hin₂ h₂ (by rw [hsU]; exact hra) ?_
    rintro Z t₂ hKZ hAZ ⟨hrZ, hgZ⟩
    refine kS hS Z t₂ hKZ hAZ hrZ ⟨a, d, ?_⟩
    rw [hgZ, hgU]
    try rfl
  -- through `VariantClear`
  have t38 : ∀ (a d : BitVec 64) (U : State) (t₁ : Nat), ¬ Simple (vtOf V X.cpu.gpr) → KeptW Wl s₀ U →
      Agree F U.proc.mm.mem V → U.cpu.rip = pvd_at.add 38 →
      U.cpu.gpr = { X.cpu.gpr with
        rax := a
        rdx := d } →
      GoG prof L o gev gP gE U t₁ := by
    intro a d U t₁ hS hKU hAU hrU hgU
    refine (c_38 prof).run c hin (fun j' g' _ V' => j' = 42 ∧
        g' = { X.cpu.gpr with
          rax := a
          rdx := d
          rsp := X.cpu.gpr.rsp - 8 } ∧ V' = V) hKU hAU hrU
      (vc_38 fun _ => ⟨rfl, (by rw [hgU]; try rfl), rfl⟩) ?_
    rintro j' g fl V₁ ⟨rfl, rfl, hV₁⟩ Y t₂ hKY hAY hrY hgY -
    subst V₁
    have hsY : Y.cpu.gpr.rsp = X.cpu.gpr.rsp - 8 := by rw [hgY]
    have hst : ∀ i < 8, Foot Wl (Addr.add (Y.cpu.gpr.rsp - 8) i) := by rw [hsY, e16]; exact hs2
    refine c.s_call hKY hAY hin (lt_len (by decide)) hrY (pvd_42 _) hinV (by rw [Vcl.vcl_length]; decide)
      (by decide) hst ?_
    rintro Y₂ t₃ hK₂ hA₂ ⟨hr₂, hg₂⟩
    rw [hsY, e16] at hA₂
    refine kf hS Y₂ t₃ hK₂ hA₂ hr₂ ⟨a, d, (by rw [hg₂, hsY, e16, hgY]; try rfl)⟩ ?_
    -- back from the callee
    intro Z V' t'' hKZ hAZ hrZ hzs hr' hPc
    refine (c_47 prof).run c hin (fun j' g' _ V'' => j' = 51 ∧
        g' = { Z.cpu.gpr with rsp := X.cpu.gpr.rsp } ∧ V'' = V') hKZ hAZ hrZ
      (vc_47 fun _ => ⟨rfl, by rw [hzs, e8], rfl⟩) ?_
    rintro j' g fl V₂ ⟨rfl, rfl, hV₂⟩ U₂ t₄ hKU₂ hAU₂ hrU₂ hgU₂ -
    subst V₂
    have hsU : U₂.cpu.gpr.rsp = X.cpu.gpr.rsp := by rw [hgU₂]
    refine c.s_ret hKU₂ hAU₂ hin (lt_len (by decide)) hrU₂ (pvd_51 _) (by rw [hsU]; exact hl) hin₂ h₂
      (by rw [hsU]; exact hr') ?_
    rintro Z' t₅ hKZ' hAZ' ⟨hrZ', hgZ'⟩
    refine kr Z V' Z' t₅ hPc hKZ' hAZ' hrZ' ?_
    rw [hgZ', hgU₂]
    try rfl
  by_cases h1 : (vtOf V X.cpu.gpr).toNat ≤ 7
  · -- `vt ≤ 7`
    refine (c_0 prof).run c hin (fun j' g' _ V' => j' = 56 ∧
        g' = { X.cpu.gpr with rax := ((vtOf V X.cpu.gpr).setWidth 32).setWidth 64 } ∧ V' = V) hK hA hrip'
      (vc_le7 ft h1) ?_
    rintro j' g fl V₁ ⟨rfl, rfl, hV₁⟩ U t₁ hKU hAU hrU hgU -
    subst V₁
    exact tR _ X.cpu.gpr.rdx U t₁ (lt_len (by decide)) pvd_56 (Or.inl h1) hKU hAU hrU hgU
  by_cases h2 : ((yOf (vtOf V X.cpu.gpr)).setWidth 16).toNat ≤ 54
  · cases h3 : mask.getLsbD (((yOf (vtOf V X.cpu.gpr)).setWidth 64).toNat % 64)
    · -- its bit clear: `VariantClear`
      refine (c_0 prof).run c hin (fun j' g' _ V' => j' = 38 ∧
          g' = { X.cpu.gpr with
            rax := (yOf (vtOf V X.cpu.gpr)).setWidth 64
            rdx := mask } ∧ V' = V) hK hA hrip' (vc_nobit ft h1 h2 h3) ?_
      rintro j' g fl V₁ ⟨rfl, rfl, hV₁⟩ U t₁ hKU hAU hrU hgU -
      subst V₁
      exact t38 _ _ U t₁ (fun h => Or.elim h h1 fun h' => absurd (h3.symm.trans h'.2) (by decide)) hKU hAU hrU hgU
    · -- its bit set
      refine (c_0 prof).run c hin (fun j' g' _ V' => j' = 52 ∧
          g' = { X.cpu.gpr with
            rax := (yOf (vtOf V X.cpu.gpr)).setWidth 64
            rdx := mask } ∧ V' = V) hK hA hrip' (vc_bit ft h1 h2 h3) ?_
      rintro j' g fl V₁ ⟨rfl, rfl, hV₁⟩ U t₁ hKU hAU hrU hgU -
      subst V₁
      exact tR _ _ U t₁ (lt_len (by decide)) pvd_52 (Or.inr ⟨h2, h3⟩) hKU hAU hrU hgU
  · -- `vt - 10 > 54`: `VariantClear`
    refine (c_0 prof).run c hin (fun j' g' _ V' => j' = 38 ∧
        g' = { X.cpu.gpr with rax := (yOf (vtOf V X.cpu.gpr)).setWidth 64 } ∧ V' = V) hK hA hrip'
      (vc_ja ft h1 h2) ?_
    rintro j' g fl V₁ ⟨rfl, rfl, hV₁⟩ U t₁ hKU hAU hrU hgU -
    subst V₁
    exact t38 _ X.cpu.gpr.rdx U t₁ (fun h => Or.elim h h1 fun h' => h2 h'.1) hKU hAU hrU hgU

end FV7z.Pvd
