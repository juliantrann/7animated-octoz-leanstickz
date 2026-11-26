import FV7z.Pic.Cuts
import FV7z.Lemmas.LeafRet
/-!
# `CPropVariant::InternalClear` (PLAN.md §M, M1)

7-Zip 26.06's `NWindows::NCOM::CPropVariant::InternalClear ()` at `0x457130` in `7zzs`
(`CPP/Windows/PropVariant.cpp`), `this` = `rdi`: if the 16-bit type tag `vt` (the 2 bytes at `this`) is `VT_EMPTY`
(0), `wReserved1` (the 2 bytes at `this + 2`) = 0 and the result `S_OK` (0), to the `ret` at 23; else
`PropVariant_Clear (this)` (`call` at 32 to `0x457020`) and, if its result `eax` is negative, `vt` = `VT_ERROR` (10)
and `scode` (the 4 bytes at `this + 8`) = the result, to the `ret` at 53. `push rbx`, `rbx` = `this` across the call,
`pop rbx` (22, or before 53).

The callee is a hypothesis (`kf`), as in `FV7z/Vcl/Holds.lean`: a continuation at its entry, given the run from its
return (`pic_at + 37`, `rsp` 8 below the entry's, `rbx` = `this`, the saved `rbx` and the return address left as they
were, and the callee's own post `Pc`) to the return address (`kr`, `ke`).

- `vtOf V g`: the type tag; `gN g`: the registers at the `call`.
- `vc_z`, `vc_n`, `vc_22`, `vc_ok`, `vc_err`: the verification conditions of the pieces.
- `pic_ok`: from the entry to the return address, directly (`kz`) or through the callee (`kf`, `kr`, `ke`).
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Pic

theorem pic_23 : ∀ feat, Dec feat pic 23 (FV7z.mk .ret 64 [] 1) := by intro feat f; rfl
theorem pic_32 : ∀ feat, Dec feat pic 32 (FV7z.mk .call 64 [.rel 18446744073709551307] 5) := by intro feat f; rfl
theorem pic_53 : ∀ feat, Dec feat pic 53 (FV7z.mk .ret 64 [] 1) := by intro feat f; rfl

/-- The type tag `vt`: the 2 bytes at `this`. -/
abbrev vtOf (V : Addr → Byte) (g : Gprs) : BitVec 16 := ofBytesLE 16 ((byteAddrs g.rdi 2).map V)

/-- The registers at the `call`: `rbx` pushed, `rbx` = `this`. -/
abbrev gN (g : Gprs) : Gprs :=
  { g with
    rbx := g.rdi
    rsp := g.rsp - 8 }

theorem sw10 : (10#32).setWidth 64 = 10#64 := by decide
theorem sw10a : (10#32).setWidth 16 = 10#16 := by decide
theorem sw10b : (10#64).setWidth 16 = 10#16 := by decide

variable {F : Footprint} {Wl : List Rgn}

/-- `vt` 0: `cmp word [rdi], 0; push rbx; mov rbx, rdi`, then `xor ecx, ecx; xor eax, eax; mov [rdi + 2], cx`, to
`pop rbx` at 22. -/
theorem vc_z {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (ft : ∀ i < 2, Foot F.data (Addr.add g.rdi i)) (hst : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8) i))
    (fw : ∀ i < 2, Foot Wl (Addr.add (g.rdi + 2#64) i)) (ht : vtOf V g = 0#16) :
    W_0 F Wl (fun j' g' _ V' => j' = 22 ∧
      g' = { g with
        rax := 0#64
        rcx := 0#64
        rbx := g.rdi
        rsp := g.rsp - 8 } ∧
      V' = Vst (Vst V (g.rsp - 8) (toBytesLE g.rbx 8)) (g.rdi + 2#64) (toBytesLE 0#16 2)) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [vtOf] at ft hst fw ht ⊢
  wpx [W_0, W_14, o0, o1, Op.cmpmi, ht, BitVec.xor_self, BitVec.setWidth_zero, decide_false, decide_true,
    Bool.not_true, Bool.false_eq_true, Bool.true_eq_false, false_implies, implies_true]
  all_goals repeat'
    first
    | exact rfl
    | assumption
    | exact trivial
    | (intro h; exact absurd h (by decide))
    | apply And.intro
    | intro _

/-- `vt` not 0: `cmp word [rdi], 0; push rbx; mov rbx, rdi`, to the `call` at 32. -/
theorem vc_n {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (ft : ∀ i < 2, Foot F.data (Addr.add g.rdi i)) (hst : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8) i))
    (ht : vtOf V g ≠ 0#16) :
    W_0 F Wl (fun j' g' _ V' => j' = 32 ∧ g' = gN g ∧ V' = Vst V (g.rsp - 8) (toBytesLE g.rbx 8)) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [vtOf] at ft hst ht ⊢
  wpx [W_0, W_14, o0, o1, Op.cmpmi, gN, ht, decide_false, decide_true, Bool.not_false, Bool.not_true,
    Bool.false_eq_true, Bool.true_eq_false, false_implies, implies_true]
  all_goals repeat'
    first
    | exact rfl
    | assumption
    | exact trivial
    | (intro h; exact absurd h (by decide))
    | apply And.intro
    | intro _

/-- `pop rbx`, to the `ret` at 23. -/
theorem vc_22 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} (hl : ∀ i < 8, Foot F.data (Addr.add g.rsp i))
    (h : ∀ fl, Q 23 { g with rbx := rdq(V, g.rsp), rsp := g.rsp + 8 } fl V) : W_22 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hl h ⊢
  wpx [W_22, o2]
  all_goals repeat' (first | exact h _ | assumption | exact trivial | apply And.intro | intro _)

/-- Back from the callee, its result not negative: `test eax, eax; jns`, to `pop rbx` at 22. -/
theorem vc_ok {g : Gprs} {f : Rflags} {V : Addr → Byte} (hm : (g.rax.setWidth 32).msb = false) :
    W_37 F Wl (fun j' g' _ V' => j' = 22 ∧ g' = g ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hm ⊢
  wpx [W_37, W_41, o3, o4, BitVec.and_self, hm, Bool.not_false, Bool.not_true, Bool.false_eq_true,
    Bool.true_eq_false, false_implies, implies_true]
  all_goals repeat'
    first
    | exact rfl
    | assumption
    | exact trivial
    | (intro h; exact absurd h (by decide))
    | apply And.intro
    | intro _

/-- Back from the callee, its result negative: `mov edx, 10; mov [rbx + 8], eax; mov [rbx], dx; pop rbx`, to the
`ret` at 53. -/
theorem vc_err {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} (hm : (g.rax.setWidth 32).msb = true)
    (fw8 : ∀ i < 4, Foot Wl (Addr.add (g.rbx + 8#64) i)) (fw : ∀ i < 2, Foot Wl (Addr.add g.rbx i))
    (hl : ∀ i < 8, Foot F.data (Addr.add g.rsp i))
    (h : ∀ fl, Q 53
      { g with
        rdx := 10#64
        rbx := rdq(Vst (Vst V (g.rbx + 8#64) (toBytesLE (g.rax.setWidth 32) 4)) g.rbx (toBytesLE 10#16 2), g.rsp)
        rsp := g.rsp + 8 } fl
      (Vst (Vst V (g.rbx + 8#64) (toBytesLE (g.rax.setWidth 32) 4)) g.rbx (toBytesLE 10#16 2))) :
    W_37 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hm fw8 fw hl h ⊢
  wpx [W_37, W_41, o3, o4, BitVec.and_self, hm, sw10, sw10a, sw10b, Bool.not_false, Bool.not_true,
    Bool.false_eq_true, Bool.true_eq_false, false_implies, implies_true]
  all_goals repeat'
    first
    | exact h _
    | assumption
    | exact trivial
    | (intro h; exact absurd h (by decide))
    | apply And.intro
    | intro _

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {X : State} {t : Nat} {V : Addr → Byte}

/-- `CPropVariant::InternalClear ()` (`this` = `rdi`) from its entry. `vt` 0: at the return address with
`wReserved1` = 0, `rax` = `rcx` = 0, the other registers as at the entry (`kz`). `vt` not 0: at the callee's entry
(`0x457020`) the registers are `gN` with `rsp` 16 below the entry's and the bytes `V` with `rbx` and the return
address into `InternalClear` pushed (`kf`); if the callee returns to `pic_at + 37` with `rsp` and `rbx` as at its
entry, and the saved `rbx` and the return address as they were, the run reaches that return address with `rbx`,
`rsp` restored: as the callee left them if its result (`eax`) is not negative (`kr`), else with `vt` = `VT_ERROR`,
`scode` = the result and `rdx` = 10 (`ke`). -/
theorem pic_ok {Pc : State → (Addr → Byte) → Prop} (c : Seg prof F Wl L s₀ o) (hin : CodeIn L pic_at pic)
    {codeC : List Byte} (hinC : CodeIn L 0x457020#64 codeC) (hC0 : 0 < codeC.length)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = pic_at)
    (hp : 16 ≤ X.cpu.gpr.rsp.toNat) (hp8 : X.cpu.gpr.rsp.toNat + 8 ≤ 2 ^ 64)
    (hs1 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8) i))
    (hs2 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 16) i))
    (hl : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsp i))
    (ft : ∀ i < 2, Foot F.data (Addr.add X.cpu.gpr.rdi i))
    (fw2 : ∀ i < 2, Foot Wl (Addr.add (X.cpu.gpr.rdi + 2#64) i))
    (fw8 : ∀ i < 4, Foot Wl (Addr.add (X.cpu.gpr.rdi + 8#64) i))
    (fw : ∀ i < 2, Foot Wl (Addr.add X.cpu.gpr.rdi i))
    (hq : X.cpu.gpr.rdi.toNat + 12 ≤ 2 ^ 64)
    (hd : X.cpu.gpr.rdi.toNat + 12 ≤ X.cpu.gpr.rsp.toNat - 16 ∨ X.cpu.gpr.rsp.toNat + 8 ≤ X.cpu.gpr.rdi.toNat)
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (hra : rdq(V, X.cpu.gpr.rsp) = e₂.add j₂)
    (kz : vtOf V X.cpu.gpr = 0#16 → ∀ (Z : State) (t' : Nat), KeptW Wl s₀ Z →
      Agree F Z.proc.mm.mem
        (Vst (Vst V (X.cpu.gpr.rsp - 8) (toBytesLE X.cpu.gpr.rbx 8)) (X.cpu.gpr.rdi + 2#64) (toBytesLE 0#16 2)) →
      Z.cpu.rip = e₂.add j₂ →
      Z.cpu.gpr = { X.cpu.gpr with
        rax := 0#64
        rcx := 0#64
        rsp := X.cpu.gpr.rsp + 8 } →
      GoG prof L o gev gP gE Z t')
    (kf : vtOf V X.cpu.gpr ≠ 0#16 → ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y →
      Agree F Y.proc.mm.mem (Vst (Vst V (X.cpu.gpr.rsp - 8) (toBytesLE X.cpu.gpr.rbx 8)) (X.cpu.gpr.rsp - 16)
        (toBytesLE (pic_at.add 37) 8)) →
      Y.cpu.rip = 0x457020#64 → Y.cpu.gpr = (gN X.cpu.gpr).set 4 (X.cpu.gpr.rsp - 16) →
      (∀ (Z : State) (V' : Addr → Byte) (t'' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V' →
        Z.cpu.rip = pic_at.add 37 → Z.cpu.gpr.rsp = X.cpu.gpr.rsp - 8 → Z.cpu.gpr.rbx = X.cpu.gpr.rdi →
        rdq(V', X.cpu.gpr.rsp - 8) = X.cpu.gpr.rbx → rdq(V', X.cpu.gpr.rsp) = e₂.add j₂ → Pc Z V' →
        GoG prof L o gev gP gE Z t'') →
      GoG prof L o gev gP gE Y t')
    (kr : ∀ (Z : State) (V' : Addr → Byte) (Z' : State) (t' : Nat), Pc Z V' →
      (Z.cpu.gpr.rax.setWidth 32).msb = false → KeptW Wl s₀ Z' → Agree F Z'.proc.mm.mem V' →
      Z'.cpu.rip = e₂.add j₂ →
      Z'.cpu.gpr = { Z.cpu.gpr with
        rbx := X.cpu.gpr.rbx
        rsp := X.cpu.gpr.rsp + 8 } →
      GoG prof L o gev gP gE Z' t')
    (ke : ∀ (Z : State) (V' : Addr → Byte) (Z' : State) (t' : Nat), Pc Z V' →
      (Z.cpu.gpr.rax.setWidth 32).msb = true → KeptW Wl s₀ Z' →
      Agree F Z'.proc.mm.mem (Vst (Vst V' (X.cpu.gpr.rdi + 8#64) (toBytesLE (Z.cpu.gpr.rax.setWidth 32) 4))
        X.cpu.gpr.rdi (toBytesLE 10#16 2)) →
      Z'.cpu.rip = e₂.add j₂ →
      Z'.cpu.gpr = { Z.cpu.gpr with
        rdx := 10#64
        rbx := X.cpu.gpr.rbx
        rsp := X.cpu.gpr.rsp + 8 } →
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
  have td2 : (X.cpu.gpr.rdi + 2#64).toNat = X.cpu.gpr.rdi.toNat + 2 := by
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]; omega
  have td8 : (X.cpu.gpr.rdi + 8#64).toNat = X.cpu.gpr.rdi.toNat + 8 := by
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]; omega
  have h8 : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rsp - 8) i) := fun i hi => c.hws _ (hs1 i hi)
  -- reads of 8 bytes past the stores
  have mP : ∀ (W : Addr → Byte) (x : Addr), x.toNat + 8 ≤ 2 ^ 64 →
      (x.toNat + 8 ≤ X.cpu.gpr.rsp.toNat - 8 ∨ X.cpu.gpr.rsp.toNat ≤ x.toNat) →
      (byteAddrs x 8).map (Vst W (X.cpu.gpr.rsp - 8) (toBytesLE X.cpu.gpr.rbx 8)) = (byteAddrs x 8).map W :=
    fun W x hx h => Tun.rd_Vst W _ _ x 8 (by rw [toBytesLE_length, tn8]; omega) hx
      (by rw [toBytesLE_length, tn8]; omega)
  have m2 : ∀ (W : Addr → Byte) (x : Addr), x.toNat + 8 ≤ 2 ^ 64 →
      (X.cpu.gpr.rdi.toNat + 4 ≤ x.toNat ∨ x.toNat + 8 ≤ X.cpu.gpr.rdi.toNat + 2) →
      (byteAddrs x 8).map (Vst W (X.cpu.gpr.rdi + 2#64) (toBytesLE 0#16 2)) = (byteAddrs x 8).map W :=
    fun W x hx h => Tun.rd_Vst W _ _ x 8 (by rw [toBytesLE_length, td2]; omega) hx
      (by rw [toBytesLE_length, td2]; omega)
  have m0 : ∀ (W : Addr → Byte) (x : Addr), x.toNat + 8 ≤ 2 ^ 64 →
      (X.cpu.gpr.rdi.toNat + 2 ≤ x.toNat ∨ x.toNat + 8 ≤ X.cpu.gpr.rdi.toNat) →
      (byteAddrs x 8).map (Vst W X.cpu.gpr.rdi (toBytesLE 10#16 2)) = (byteAddrs x 8).map W :=
    fun W x hx h => Tun.rd_Vst W _ _ x 8 (by rw [toBytesLE_length]; omega) hx (by rw [toBytesLE_length]; omega)
  have m8 : ∀ (W : Addr → Byte) (v : BitVec 32) (x : Addr), x.toNat + 8 ≤ 2 ^ 64 →
      (X.cpu.gpr.rdi.toNat + 12 ≤ x.toNat ∨ x.toNat + 8 ≤ X.cpu.gpr.rdi.toNat + 8) →
      (byteAddrs x 8).map (Vst W (X.cpu.gpr.rdi + 8#64) (toBytesLE v 4)) = (byteAddrs x 8).map W :=
    fun W v x hx h => Tun.rd_Vst W _ _ x 8 (by rw [toBytesLE_length, td8]; omega) hx
      (by rw [toBytesLE_length, td8]; omega)
  have hrip' : X.cpu.rip = pic_at.add 0 := by rw [addr_add_zero]; exact hrip
  by_cases ht : vtOf V X.cpu.gpr = 0#16
  · -- `vt` 0: to `pop rbx` at 22, then the `ret` at 23
    have hsb : rdq(Vst (Vst V (X.cpu.gpr.rsp - 8) (toBytesLE X.cpu.gpr.rbx 8)) (X.cpu.gpr.rdi + 2#64)
        (toBytesLE 0#16 2), X.cpu.gpr.rsp - 8) = X.cpu.gpr.rbx := by
      rw [m2 _ _ hq8 (by rw [tn8]; omega), Tun.rd_Vst_self _ _ _ (toBytesLE_length _ _) hq8,
        ofBytesLE_toBytesLE (n := 8) rfl]
    have hrz : rdq(Vst (Vst V (X.cpu.gpr.rsp - 8) (toBytesLE X.cpu.gpr.rbx 8)) (X.cpu.gpr.rdi + 2#64)
        (toBytesLE 0#16 2), X.cpu.gpr.rsp) = e₂.add j₂ := by
      rw [m2 _ _ hp8 (by omega), mP _ _ hp8 (by omega)]
      exact hra
    refine (c_0 prof).run c hin (fun j' g' _ V' => j' = 22 ∧
        g' = { X.cpu.gpr with
          rax := 0#64
          rcx := 0#64
          rbx := X.cpu.gpr.rdi
          rsp := X.cpu.gpr.rsp - 8 } ∧
        V' = Vst (Vst V (X.cpu.gpr.rsp - 8) (toBytesLE X.cpu.gpr.rbx 8)) (X.cpu.gpr.rdi + 2#64)
          (toBytesLE 0#16 2)) hK hA hrip' (vc_z ft hs1 fw2 ht) ?_
    rintro j' g fl V₁ ⟨rfl, rfl, hV₁⟩ U t₁ hKU hAU hrU hgU -
    subst V₁
    refine (c_22 prof).run c hin (fun j' g' _ V' => j' = 23 ∧
        g' = { X.cpu.gpr with
          rax := 0#64
          rcx := 0#64
          rsp := X.cpu.gpr.rsp } ∧
        V' = Vst (Vst V (X.cpu.gpr.rsp - 8) (toBytesLE X.cpu.gpr.rbx 8)) (X.cpu.gpr.rdi + 2#64)
          (toBytesLE 0#16 2)) hKU hAU hrU
      (vc_22 (by rw [hgU]; exact h8) fun _ => ⟨rfl, by rw [hgU]; dsimp only; rw [hsb, e8], rfl⟩) ?_
    rintro j' g fl V₂ ⟨rfl, rfl, hV₂⟩ U₂ t₂ hKU₂ hAU₂ hrU₂ hgU₂ -
    subst V₂
    have hsU : U₂.cpu.gpr.rsp = X.cpu.gpr.rsp := by rw [hgU₂]
    refine c.s_ret hKU₂ hAU₂ hin (lt_len (by decide)) hrU₂ (pic_23 _) (by rw [hsU]; exact hl) hin₂ h₂
      (by rw [hsU]; exact hrz) ?_
    rintro Z t₃ hKZ hAZ ⟨hrZ, hgZ⟩
    refine kz ht Z t₃ hKZ hAZ hrZ ?_
    rw [hgZ, hgU₂]
    try rfl
  · -- `vt` not 0: to the `call`
    refine (c_0 prof).run c hin (fun j' g' _ V' => j' = 32 ∧ g' = gN X.cpu.gpr ∧
        V' = Vst V (X.cpu.gpr.rsp - 8) (toBytesLE X.cpu.gpr.rbx 8)) hK hA hrip' (vc_n ft hs1 ht) ?_
    rintro j' g fl V₁ ⟨rfl, rfl, hV₁⟩ Y t₁ hKY hAY hrY hgY -
    subst V₁
    have hsY : Y.cpu.gpr.rsp = X.cpu.gpr.rsp - 8 := by rw [hgY]
    have hst : ∀ i < 8, Foot Wl (Addr.add (Y.cpu.gpr.rsp - 8) i) := by rw [hsY, e16]; exact hs2
    refine c.s_call hKY hAY hin (lt_len (by decide)) hrY (pic_32 _) hinC hC0 (by decide) hst ?_
    rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
    rw [hsY, e16] at hA₂
    have hg₂' : Y₂.cpu.gpr = (gN X.cpu.gpr).set 4 (X.cpu.gpr.rsp - 16) := by
      rw [hg₂, hgY]
      exact congrArg (fun v => (gN X.cpu.gpr).set 4 v) e16
    refine kf ht Y₂ t₂ hK₂ hA₂ hr₂ hg₂' ?_
    -- back from the callee
    intro Z V' t'' hKZ hAZ hrZ hzs hzb hb hr' hPc
    by_cases hm : (Z.cpu.gpr.rax.setWidth 32).msb = true
    · -- the result negative: `vt` = `VT_ERROR`, `scode` = the result
      have hbE : rdq(Vst (Vst V' (X.cpu.gpr.rdi + 8#64) (toBytesLE (Z.cpu.gpr.rax.setWidth 32) 4))
          X.cpu.gpr.rdi (toBytesLE 10#16 2), X.cpu.gpr.rsp - 8) = X.cpu.gpr.rbx := by
        rw [m0 _ _ hq8 (by rw [tn8]; omega), m8 _ _ _ hq8 (by rw [tn8]; omega)]
        exact hb
      have hrE : rdq(Vst (Vst V' (X.cpu.gpr.rdi + 8#64) (toBytesLE (Z.cpu.gpr.rax.setWidth 32) 4))
          X.cpu.gpr.rdi (toBytesLE 10#16 2), X.cpu.gpr.rsp) = e₂.add j₂ := by
        rw [m0 _ _ hp8 (by omega), m8 _ _ _ hp8 (by omega)]
        exact hr'
      refine (c_37 prof).run c hin (fun j' g' _ V'' => j' = 53 ∧
          g' = { Z.cpu.gpr with
            rdx := 10#64
            rbx := X.cpu.gpr.rbx
            rsp := X.cpu.gpr.rsp } ∧
          V'' = Vst (Vst V' (X.cpu.gpr.rdi + 8#64) (toBytesLE (Z.cpu.gpr.rax.setWidth 32) 4))
            X.cpu.gpr.rdi (toBytesLE 10#16 2)) hKZ hAZ hrZ
        (vc_err hm (by rw [hzb]; exact fw8) (by rw [hzb]; exact fw) (by rw [hzs]; exact h8)
          fun _ => ⟨rfl, by rw [hzb, hzs, hbE, e8], by rw [hzb]⟩) ?_
      rintro j' g fl V₂ ⟨rfl, rfl, hV₂⟩ U t₃ hKU hAU hrU hgU -
      subst V₂
      have hsU : U.cpu.gpr.rsp = X.cpu.gpr.rsp := by rw [hgU]
      refine c.s_ret hKU hAU hin (lt_len (by decide)) hrU (pic_53 _) (by rw [hsU]; exact hl) hin₂ h₂
        (by rw [hsU]; exact hrE) ?_
      rintro Z' t₄ hKZ' hAZ' ⟨hrZ', hgZ'⟩
      refine ke Z V' Z' t₄ hPc hm hKZ' hAZ' hrZ' ?_
      rw [hgZ', hgU]
      try rfl
    · -- the result not negative
      have hm' : (Z.cpu.gpr.rax.setWidth 32).msb = false := by simpa using hm
      refine (c_37 prof).run c hin (fun j' g' _ V'' => j' = 22 ∧ g' = Z.cpu.gpr ∧ V'' = V') hKZ hAZ hrZ
        (vc_ok hm') ?_
      rintro j' g fl V₂ ⟨rfl, rfl, hV₂⟩ U t₃ hKU hAU hrU hgU -
      subst V₂
      refine (c_22 prof).run c hin (fun j' g' _ V'' => j' = 23 ∧
          g' = { Z.cpu.gpr with
            rbx := X.cpu.gpr.rbx
            rsp := X.cpu.gpr.rsp } ∧ V'' = V') hKU hAU hrU
        (vc_22 (by rw [hgU, hzs]; exact h8) fun _ => ⟨rfl, by rw [hgU, hzs, hb, e8], rfl⟩) ?_
      rintro j' g fl V₃ ⟨rfl, rfl, hV₃⟩ U₂ t₄ hKU₂ hAU₂ hrU₂ hgU₂ -
      subst V₃
      have hsU : U₂.cpu.gpr.rsp = X.cpu.gpr.rsp := by rw [hgU₂]
      refine c.s_ret hKU₂ hAU₂ hin (lt_len (by decide)) hrU₂ (pic_23 _) (by rw [hsU]; exact hl) hin₂ h₂
        (by rw [hsU]; exact hr') ?_
      rintro Z' t₅ hKZ' hAZ' ⟨hrZ', hgZ'⟩
      refine kr Z V' Z' t₅ hPc hm' hKZ' hAZ' hrZ' ?_
      rw [hgZ', hgU₂]
      try rfl

end FV7z.Pic
