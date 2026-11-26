import FV7z.Pdt.Cuts
import FV7z.Lemmas.LeafRet
/-!
# `CPropVariant::Detach` (PLAN.md §M, M1)

7-Zip 26.06's `NWindows::NCOM::CPropVariant::Detach (PROPVARIANT *pDest)` at `0x4570f0` in `7zzs`
(`CPP/Windows/PropVariant.cpp`), `this` = `rdi`, `pDest` = `rsi`: `push rbp; push rbx` (`rbp` = `this`, `rbx` =
`pDest`), `sub rsp, 8`; if `pDest`'s type tag `vt` (the 2 bytes at `pDest`) is not `VT_EMPTY` (0),
`PropVariant_Clear (pDest)` (`call` at 51 to `0x456fb0`), and if its result `eax` is negative, that result, to
`add rsp, 8; pop rbx; pop rbp` (39) and the `ret` at 45; else (22) the 16 bytes at `this` copied to `pDest`
(`movdqu`/`movups`, the bytes not followed), the 4 bytes at `this` = 0 and the result `S_OK` (0), to 39.

The callee is a hypothesis (`kf`), as in `FV7z/Vcl/Holds.lean`: a continuation at its entry, given the run from its
return (`pdt_at + 56`, `rsp` 24 below the entry's, `rbx` = `pDest`, `rbp` = `this`, the saved `rbx`, `rbp` and the
return address left as they were, and the callee's own post `Pc`) to the return address (`kr`, `ke`).

- `vtOf V g`: `pDest`'s type tag; `pV V g`: the bytes after the two `push`es; `gP0 g`, `gF0 g`, `gF g`: the registers
  after the prologue and at the `call`.
- `vc_z`, `vc_n`, `vc_22`, `vc_39`, `vc_ok`, `vc_err`: the verification conditions of the pieces.
- `run_39`: from 39 to the return address.
- `pdt_ok`: from the entry to the return address, directly (`kz`) or through the callee (`kf`, `kr`, `ke`).
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Pdt

theorem pdt_45 : ∀ feat, Dec feat pdt 45 (FV7z.mk .ret 64 [] 1) := by intro feat f; rfl
theorem pdt_51 : ∀ feat, Dec feat pdt 51 (FV7z.mk .call 64 [.rel 18446744073709551240] 5) := by intro feat f; rfl

/-- `pDest`'s type tag `vt`: the 2 bytes at `rsi`. -/
abbrev vtOf (V : Addr → Byte) (g : Gprs) : BitVec 16 := ofBytesLE 16 ((byteAddrs g.rsi 2).map V)

/-- The bytes after `push rbp; push rbx`. -/
abbrev pV (V : Addr → Byte) (g : Gprs) : Addr → Byte :=
  Vst (Vst V (g.rsp - 8) (toBytesLE g.rbp 8)) (g.rsp - 8 - 8) (toBytesLE g.rbx 8)

/-- The registers after the prologue: `rbx` = `pDest`, `rbp` = `this`, `rsp` 24 down. -/
abbrev gP0 (g : Gprs) : Gprs :=
  { g with
    rbx := g.rsi
    rsp := g.rsp - 8 - 8 - 8
    rbp := g.rdi }

/-- The registers at the `call`, `rsp` as the three steps down leave it. -/
abbrev gF0 (g : Gprs) : Gprs :=
  { g with
    rbx := g.rsi
    rsp := g.rsp - 8 - 8 - 8
    rbp := g.rdi
    rdi := g.rsi }

/-- The registers at the `call`: `rdi` = `pDest`. -/
abbrev gF (g : Gprs) : Gprs :=
  { g with
    rbx := g.rsi
    rsp := g.rsp - 24
    rbp := g.rdi
    rdi := g.rsi }

variable {F : Footprint} {Wl : List Rgn}

/-- `vt` 0: the prologue and `cmp word [rsi], 0`, to the copy at 22. -/
theorem vc_z {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (w1 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8) i)) (w2 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8) i))
    (ft : ∀ i < 2, Foot F.data (Addr.add g.rsi i)) (ht : ofBytesLE 16 ((byteAddrs g.rsi 2).map (pV V g)) = 0#16) :
    W_0 F Wl (fun j' g' _ V' => j' = 22 ∧ g' = gP0 g ∧ V' = pV V g) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [pV] at w1 w2 ft ht ⊢
  wpx [W_0, W_48, o0, o3, Op.cmpmi, gP0, ht, decide_false, decide_true, Bool.not_false, Bool.not_true,
    Bool.false_eq_true, Bool.true_eq_false, false_implies, implies_true]
  all_goals repeat'
    first
    | exact rfl
    | assumption
    | exact trivial
    | (intro h; exact absurd h (by decide))
    | apply And.intro
    | intro _

/-- `vt` not 0: the prologue, `cmp word [rsi], 0` and `mov rdi, rsi`, to the `call` at 51. -/
theorem vc_n {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (w1 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8) i)) (w2 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8) i))
    (ft : ∀ i < 2, Foot F.data (Addr.add g.rsi i)) (ht : ofBytesLE 16 ((byteAddrs g.rsi 2).map (pV V g)) ≠ 0#16) :
    W_0 F Wl (fun j' g' _ V' => j' = 51 ∧ g' = gF0 g ∧ V' = pV V g) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [pV] at w1 w2 ft ht ⊢
  wpx [W_0, W_48, o0, o3, Op.cmpmi, gF0, ht, decide_false, decide_true, Bool.not_false, Bool.not_true,
    Bool.false_eq_true, Bool.true_eq_false, false_implies, implies_true]
  all_goals repeat'
    first
    | exact rfl
    | assumption
    | exact trivial
    | (intro h; exact absurd h (by decide))
    | apply And.intro
    | intro _

/-- The copy: `movdqu xmm0, [rbp]; xor eax, eax; movups [rbx], xmm0; mov dword [rbp], 0`, to 39. -/
theorem vc_22 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (fl : ∀ i < 16, Foot F.data (Addr.add g.rbp i)) (fs : ∀ i < 16, Foot Wl (Addr.add g.rbx i))
    (fp : ∀ i < 4, Foot Wl (Addr.add g.rbp i))
    (h : ∀ bs : List Byte, bs.length = 16 → ∀ fl,
      Q 39 { g with rax := 0#64 } fl (Vst (Vst V g.rbx bs) g.rbp (toBytesLE 0#32 4))) :
    W_22 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at fl fs fp h ⊢
  wpx [W_22, o1, Op.vl, Op.vs, BitVec.xor_self, BitVec.setWidth_zero]
  all_goals repeat'
    first
    | exact h _ (by assumption) _
    | assumption
    | exact trivial
    | apply And.intro
    | intro _

/-- `add rsp, 8; pop rbx; pop rbp`, to the `ret` at 45. -/
theorem vc_39 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (h1 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8) i)) (h2 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8 + 8) i))
    (h : ∀ fl, Q 45
      { g with
        rbx := rdq(V, g.rsp + 8)
        rsp := g.rsp + 8 + 8 + 8
        rbp := rdq(V, g.rsp + 8 + 8) } fl V) :
    W_39 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h1 h2 h ⊢
  wpx [W_39, o2]
  all_goals repeat' (first | exact h _ | assumption | exact trivial | apply And.intro | intro _)

/-- Back from the callee, its result not negative: `test eax, eax; jns`, to the copy at 22. -/
theorem vc_ok {g : Gprs} {f : Rflags} {V : Addr → Byte} (hm : (g.rax.setWidth 32).msb = false) :
    W_56 F Wl (fun j' g' _ V' => j' = 22 ∧ g' = g ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hm ⊢
  wpx [W_56, W_60, o4, BitVec.and_self, hm, Bool.not_false, Bool.not_true, Bool.false_eq_true,
    Bool.true_eq_false, false_implies, implies_true]
  all_goals repeat'
    first
    | exact rfl
    | assumption
    | exact trivial
    | (intro h; exact absurd h (by decide))
    | apply And.intro
    | intro _

/-- Back from the callee, its result negative: `test eax, eax; jns; jmp`, to 39. -/
theorem vc_err {g : Gprs} {f : Rflags} {V : Addr → Byte} (hm : (g.rax.setWidth 32).msb = true) :
    W_56 F Wl (fun j' g' _ V' => j' = 39 ∧ g' = g ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hm ⊢
  wpx [W_56, W_60, o4, BitVec.and_self, hm, Bool.not_false, Bool.not_true, Bool.false_eq_true,
    Bool.true_eq_false, false_implies, implies_true]
  all_goals repeat'
    first
    | exact rfl
    | assumption
    | exact trivial
    | (intro h; exact absurd h (by decide))
    | apply And.intro
    | intro _

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {X : State} {t : Nat} {V : Addr → Byte}

/-- From 39 (`rsp` = `r`): `rbx`, `rbp` from the 8 bytes at `r + 8`, `r + 16`, to the return address at `r + 24`. -/
theorem run_39 (c : Seg prof F Wl L s₀ o) (hin : CodeIn L pdt_at pdt) {U : State} {W : Addr → Byte}
    (hK : KeptW Wl s₀ U) (hA : Agree F U.proc.mm.mem W) (hr : U.cpu.rip = pdt_at.add 39)
    (h1 : ∀ i < 8, Foot F.data (Addr.add (U.cpu.gpr.rsp + 8) i))
    (h2 : ∀ i < 8, Foot F.data (Addr.add (U.cpu.gpr.rsp + 8 + 8) i))
    (h3 : ∀ i < 8, Foot F.data (Addr.add (U.cpu.gpr.rsp + 8 + 8 + 8) i))
    {b p : BitVec 64} (hb : rdq(W, U.cpu.gpr.rsp + 8) = b) (hp : rdq(W, U.cpu.gpr.rsp + 8 + 8) = p)
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (hra : rdq(W, U.cpu.gpr.rsp + 8 + 8 + 8) = e₂.add j₂)
    (k : ∀ (Z' : State) (t' : Nat), KeptW Wl s₀ Z' → Agree F Z'.proc.mm.mem W → Z'.cpu.rip = e₂.add j₂ →
      Z'.cpu.gpr = { U.cpu.gpr with
        rbx := b
        rsp := U.cpu.gpr.rsp + 8 + 8 + 8 + 8
        rbp := p } →
      GoG prof L o gev gP gE Z' t') :
    GoG prof L o gev gP gE U t := by
  refine (c_39 prof).run c hin (fun j' g' _ V' => j' = 45 ∧
      g' = { U.cpu.gpr with
        rbx := b
        rsp := U.cpu.gpr.rsp + 8 + 8 + 8
        rbp := p } ∧ V' = W) hK hA hr
    (vc_39 h1 h2 fun _ => ⟨rfl, by rw [hb, hp], rfl⟩) ?_
  rintro j' g fl V₁ ⟨rfl, rfl, hV₁⟩ U₁ t₁ hKU hAU hrU hgU -
  subst V₁
  have hsU : U₁.cpu.gpr.rsp = U.cpu.gpr.rsp + 8 + 8 + 8 := by rw [hgU]
  refine c.s_ret hKU hAU hin (lt_len (by decide)) hrU (pdt_45 _) (by rw [hsU]; exact h3) hin₂ h₂
    (by rw [hsU]; exact hra) ?_
  rintro Z' t₂ hKZ hAZ ⟨hrZ, hgZ⟩
  refine k Z' t₂ hKZ hAZ hrZ ?_
  rw [hgZ, hgU]
  try rfl

/-- `CPropVariant::Detach (pDest)` (`this` = `rdi`, `pDest` = `rsi`) from its entry. `vt` 0: at the return address
with the 16 bytes at `pDest` some `bs` (the copy), the 4 bytes at `this` 0, `rax` = 0, the other registers as at the
entry (`kz`). `vt` not 0: at the callee's entry (`0x456fb0`) the registers are `gF` with `rsp` 32 below the entry's
and the bytes `V` with `rbp`, `rbx` and the return address into `Detach` pushed (`kf`); if the callee returns to
`pdt_at + 56` with `rsp`, `rbx`, `rbp` as at its entry and the saved `rbx`, `rbp` and the return address as they
were, the run reaches that return address with `rbx`, `rbp`, `rsp` restored: after the copy, `rax` = 0, if the
callee's result (`eax`) is not negative (`kr`), else as the callee left them (`ke`). -/
theorem pdt_ok {Pc : State → (Addr → Byte) → Prop} (c : Seg prof F Wl L s₀ o) (hin : CodeIn L pdt_at pdt)
    {codeC : List Byte} (hinC : CodeIn L 0x456fb0#64 codeC) (hC0 : 0 < codeC.length)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = pdt_at)
    (hp : 32 ≤ X.cpu.gpr.rsp.toNat) (hp8 : X.cpu.gpr.rsp.toNat + 8 ≤ 2 ^ 64)
    (hs1 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8) i))
    (hs2 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 16) i))
    (hs4 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 32) i))
    (hl : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsp i))
    (ft : ∀ i < 2, Foot F.data (Addr.add X.cpu.gpr.rsi i))
    (fl : ∀ i < 16, Foot F.data (Addr.add X.cpu.gpr.rdi i))
    (fs : ∀ i < 16, Foot Wl (Addr.add X.cpu.gpr.rsi i))
    (fp : ∀ i < 4, Foot Wl (Addr.add X.cpu.gpr.rdi i))
    (hq : X.cpu.gpr.rsi.toNat + 16 ≤ 2 ^ 64) (hq' : X.cpu.gpr.rdi.toNat + 4 ≤ 2 ^ 64)
    (hdq : X.cpu.gpr.rsi.toNat + 16 ≤ X.cpu.gpr.rsp.toNat - 32 ∨ X.cpu.gpr.rsp.toNat + 8 ≤ X.cpu.gpr.rsi.toNat)
    (hdp : X.cpu.gpr.rdi.toNat + 4 ≤ X.cpu.gpr.rsp.toNat - 32 ∨ X.cpu.gpr.rsp.toNat + 8 ≤ X.cpu.gpr.rdi.toNat)
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (hra : rdq(V, X.cpu.gpr.rsp) = e₂.add j₂)
    (kz : vtOf V X.cpu.gpr = 0#16 → ∀ (bs : List Byte) (Z : State) (t' : Nat), bs.length = 16 → KeptW Wl s₀ Z →
      Agree F Z.proc.mm.mem (Vst (Vst (pV V X.cpu.gpr) X.cpu.gpr.rsi bs) X.cpu.gpr.rdi (toBytesLE 0#32 4)) →
      Z.cpu.rip = e₂.add j₂ →
      Z.cpu.gpr = { X.cpu.gpr with
        rax := 0#64
        rsp := X.cpu.gpr.rsp + 8 } →
      GoG prof L o gev gP gE Z t')
    (kf : vtOf V X.cpu.gpr ≠ 0#16 → ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y →
      Agree F Y.proc.mm.mem (Vst (pV V X.cpu.gpr) (X.cpu.gpr.rsp - 32) (toBytesLE (pdt_at.add 56) 8)) →
      Y.cpu.rip = 0x456fb0#64 → Y.cpu.gpr = (gF X.cpu.gpr).set 4 (X.cpu.gpr.rsp - 32) →
      (∀ (Z : State) (V' : Addr → Byte) (t'' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V' →
        Z.cpu.rip = pdt_at.add 56 → Z.cpu.gpr.rsp = X.cpu.gpr.rsp - 24 → Z.cpu.gpr.rbx = X.cpu.gpr.rsi →
        Z.cpu.gpr.rbp = X.cpu.gpr.rdi → rdq(V', X.cpu.gpr.rsp - 16) = X.cpu.gpr.rbx →
        rdq(V', X.cpu.gpr.rsp - 8) = X.cpu.gpr.rbp → rdq(V', X.cpu.gpr.rsp) = e₂.add j₂ → Pc Z V' →
        GoG prof L o gev gP gE Z t'') →
      GoG prof L o gev gP gE Y t')
    (kr : ∀ (Z : State) (V' : Addr → Byte) (bs : List Byte) (Z' : State) (t' : Nat), Pc Z V' →
      (Z.cpu.gpr.rax.setWidth 32).msb = false → bs.length = 16 → KeptW Wl s₀ Z' →
      Agree F Z'.proc.mm.mem (Vst (Vst V' X.cpu.gpr.rsi bs) X.cpu.gpr.rdi (toBytesLE 0#32 4)) →
      Z'.cpu.rip = e₂.add j₂ →
      Z'.cpu.gpr = { Z.cpu.gpr with
        rax := 0#64
        rbx := X.cpu.gpr.rbx
        rsp := X.cpu.gpr.rsp + 8
        rbp := X.cpu.gpr.rbp } →
      GoG prof L o gev gP gE Z' t')
    (ke : ∀ (Z : State) (V' : Addr → Byte) (Z' : State) (t' : Nat), Pc Z V' →
      (Z.cpu.gpr.rax.setWidth 32).msb = true → KeptW Wl s₀ Z' → Agree F Z'.proc.mm.mem V' →
      Z'.cpu.rip = e₂.add j₂ →
      Z'.cpu.gpr = { Z.cpu.gpr with
        rbx := X.cpu.gpr.rbx
        rsp := X.cpu.gpr.rsp + 8
        rbp := X.cpu.gpr.rbp } →
      GoG prof L o gev gP gE Z' t') :
    GoG prof L o gev gP gE X t := by
  have hlt := X.cpu.gpr.rsp.isLt
  have tn8 : (X.cpu.gpr.rsp - 8).toNat = X.cpu.gpr.rsp.toNat - 8 := by rw [BitVec.toNat_sub]; simp <;> omega
  have tn16 : (X.cpu.gpr.rsp - 16).toNat = X.cpu.gpr.rsp.toNat - 16 := by rw [BitVec.toNat_sub]; simp <;> omega
  have tn24 : (X.cpu.gpr.rsp - 24).toNat = X.cpu.gpr.rsp.toNat - 24 := by rw [BitVec.toNat_sub]; simp <;> omega
  have tn32 : (X.cpu.gpr.rsp - 32).toNat = X.cpu.gpr.rsp.toNat - 32 := by rw [BitVec.toNat_sub]; simp <;> omega
  have e16 : X.cpu.gpr.rsp - 8 - 8 = X.cpu.gpr.rsp - 16 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, tn8, tn16]
    simp <;> omega
  have e24 : X.cpu.gpr.rsp - 16 - 8 = X.cpu.gpr.rsp - 24 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, tn16, tn24]
    simp <;> omega
  have e32 : X.cpu.gpr.rsp - 24 - 8 = X.cpu.gpr.rsp - 32 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, tn24, tn32]
    simp <;> omega
  have a16 : X.cpu.gpr.rsp - 24 + 8 = X.cpu.gpr.rsp - 16 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, tn24, tn16]
    simp <;> omega
  have a8 : X.cpu.gpr.rsp - 16 + 8 = X.cpu.gpr.rsp - 8 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, tn16, tn8]
    simp <;> omega
  have a0 : X.cpu.gpr.rsp - 8 + 8 = X.cpu.gpr.rsp := BitVec.sub_add_cancel _ _
  have hgF : gF0 X.cpu.gpr = gF X.cpu.gpr := by
    unfold gF0 gF
    rw [e16, e24]
  have hl16 : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rsp - 16) i) := fun i hi => c.hws _ (hs2 i hi)
  have hl8 : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rsp - 8) i) := fun i hi => c.hws _ (hs1 i hi)
  have hq16 : (X.cpu.gpr.rsp - 16).toNat + 8 ≤ 2 ^ 64 := by rw [tn16]; omega
  have hq8 : (X.cpu.gpr.rsp - 8).toNat + 8 ≤ 2 ^ 64 := by rw [tn8]; omega
  -- reads of 8 bytes on the stack past the stores at `pDest` and `this`
  have mC : ∀ (W : Addr → Byte) (bs : List Byte) (x : Addr), bs.length = 16 → x.toNat + 8 ≤ 2 ^ 64 →
      X.cpu.gpr.rsp.toNat - 24 ≤ x.toNat → x.toNat ≤ X.cpu.gpr.rsp.toNat →
      (byteAddrs x 8).map (Vst (Vst W X.cpu.gpr.rsi bs) X.cpu.gpr.rdi (toBytesLE 0#32 4)) =
        (byteAddrs x 8).map W := by
    intro W bs x hn hx h h'
    rw [Tun.rd_Vst (Vst W X.cpu.gpr.rsi bs) X.cpu.gpr.rdi (toBytesLE 0#32 4) x 8 (by rw [toBytesLE_length]; omega) hx
        (by rw [toBytesLE_length]; omega),
      Tun.rd_Vst W X.cpu.gpr.rsi bs x 8 (by rw [hn]; omega) hx (by rw [hn]; omega)]
  -- reads past a `push`
  have r8 : ∀ (W : Addr → Byte) (a : Addr) (v : BitVec 64) (x : Addr) (n : Nat), a.toNat + 8 ≤ 2 ^ 64 →
      x.toNat + n ≤ 2 ^ 64 → (a.toNat + 8 ≤ x.toNat ∨ x.toNat + n ≤ a.toNat) →
      (byteAddrs x n).map (Vst W a (toBytesLE v 8)) = (byteAddrs x n).map W :=
    fun W a v x n ha hx h =>
      Tun.rd_Vst W a (toBytesLE v 8) x n (by rw [toBytesLE_length]; exact ha) hx (by rw [toBytesLE_length]; exact h)
  -- the bytes after the two `push`es
  have hsb : rdq(pV V X.cpu.gpr, X.cpu.gpr.rsp - 16) = X.cpu.gpr.rbx := by
    dsimp only [pV]
    rw [e16, Tun.rd_Vst_self _ _ _ (toBytesLE_length _ _) hq16, ofBytesLE_toBytesLE (n := 8) rfl]
  have hsp : rdq(pV V X.cpu.gpr, X.cpu.gpr.rsp - 8) = X.cpu.gpr.rbp := by
    dsimp only [pV]
    rw [e16, r8 _ (X.cpu.gpr.rsp - 16) X.cpu.gpr.rbx (X.cpu.gpr.rsp - 8) 8 (by rw [tn16]; omega) hq8
        (by rw [tn16, tn8]; omega),
      Tun.rd_Vst_self _ _ _ (toBytesLE_length _ _) hq8, ofBytesLE_toBytesLE (n := 8) rfl]
  have hsr : rdq(pV V X.cpu.gpr, X.cpu.gpr.rsp) = e₂.add j₂ := by
    dsimp only [pV]
    rw [e16, r8 _ (X.cpu.gpr.rsp - 16) X.cpu.gpr.rbx X.cpu.gpr.rsp 8 (by rw [tn16]; omega) hp8
        (by rw [tn16]; omega),
      r8 _ (X.cpu.gpr.rsp - 8) X.cpu.gpr.rbp X.cpu.gpr.rsp 8 (by rw [tn8]; omega) hp8 (by rw [tn8]; omega)]
    exact hra
  have hvt : ofBytesLE 16 ((byteAddrs X.cpu.gpr.rsi 2).map (pV V X.cpu.gpr)) = vtOf V X.cpu.gpr := by
    dsimp only [pV, vtOf]
    rw [e16, r8 _ (X.cpu.gpr.rsp - 16) X.cpu.gpr.rbx X.cpu.gpr.rsi 2 (by rw [tn16]; omega) (by omega)
        (by rw [tn16]; omega),
      r8 _ (X.cpu.gpr.rsp - 8) X.cpu.gpr.rbp X.cpu.gpr.rsi 2 (by rw [tn8]; omega) (by omega) (by rw [tn8]; omega)]
  have w2 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8 - 8) i) := by rw [e16]; exact hs2
  -- from the copy at 22 (`rsp` 24 below the entry's, `rbx` = `pDest`, `rbp` = `this`) to the return address
  have t22 : ∀ (U : State) (W : Addr → Byte) (t₁ : Nat), KeptW Wl s₀ U → Agree F U.proc.mm.mem W →
      U.cpu.rip = pdt_at.add 22 → U.cpu.gpr.rsp = X.cpu.gpr.rsp - 24 → U.cpu.gpr.rbx = X.cpu.gpr.rsi →
      U.cpu.gpr.rbp = X.cpu.gpr.rdi → rdq(W, X.cpu.gpr.rsp - 16) = X.cpu.gpr.rbx →
      rdq(W, X.cpu.gpr.rsp - 8) = X.cpu.gpr.rbp → rdq(W, X.cpu.gpr.rsp) = e₂.add j₂ →
      (∀ (bs : List Byte) (Z' : State) (t' : Nat), bs.length = 16 → KeptW Wl s₀ Z' →
        Agree F Z'.proc.mm.mem (Vst (Vst W X.cpu.gpr.rsi bs) X.cpu.gpr.rdi (toBytesLE 0#32 4)) →
        Z'.cpu.rip = e₂.add j₂ →
        Z'.cpu.gpr = { U.cpu.gpr with
          rax := 0#64
          rbx := X.cpu.gpr.rbx
          rsp := X.cpu.gpr.rsp + 8
          rbp := X.cpu.gpr.rbp } →
        GoG prof L o gev gP gE Z' t') →
      GoG prof L o gev gP gE U t₁ := by
    intro U W t₁ hKU hAU hrU hsU hbU hpU hb hp' hr k
    refine (c_22 prof).run c hin (fun j' g' _ V' => j' = 39 ∧ g' = { U.cpu.gpr with rax := 0#64 } ∧
        ∃ bs : List Byte, bs.length = 16 ∧
          V' = Vst (Vst W X.cpu.gpr.rsi bs) X.cpu.gpr.rdi (toBytesLE 0#32 4)) hKU hAU hrU
      (vc_22 (by rw [hpU]; exact fl) (by rw [hbU]; exact fs) (by rw [hpU]; exact fp)
        fun bs hn _ => ⟨rfl, rfl, bs, hn, by rw [hbU, hpU]⟩) ?_
    rintro j' g fl₁ V₁ ⟨rfl, rfl, bs, hn, hV₁⟩ U₁ t₂ hKU₁ hAU₁ hrU₁ hgU₁ -
    subst V₁
    have hs₁ : U₁.cpu.gpr.rsp = X.cpu.gpr.rsp - 24 := by rw [hgU₁]; exact hsU
    refine run_39 c hin hKU₁ hAU₁ hrU₁ (b := X.cpu.gpr.rbx) (p := X.cpu.gpr.rbp) (by rw [hs₁, a16]; exact hl16)
      (by rw [hs₁, a16, a8]; exact hl8)
      (by rw [hs₁, a16, a8, a0]; exact hl)
      (by rw [hs₁, a16, mC _ _ _ hn hq16 (by rw [tn16]; omega) (by rw [tn16]; omega)]; exact hb)
      (by rw [hs₁, a16, a8, mC _ _ _ hn hq8 (by rw [tn8]; omega) (by rw [tn8]; omega)]; exact hp')
      hin₂ h₂ (by rw [hs₁, a16, a8, a0, mC _ _ _ hn hp8 (by omega) (by omega)]; exact hr) ?_
    intro Z' t₃ hKZ hAZ hrZ hgZ
    refine k bs Z' t₃ hn hKZ hAZ hrZ ?_
    rw [hgZ, hs₁, hgU₁, a16, a8, a0]
    try rfl
  have hrip' : X.cpu.rip = pdt_at.add 0 := by rw [addr_add_zero]; exact hrip
  by_cases ht : vtOf V X.cpu.gpr = 0#16
  · -- `vt` 0: the copy
    refine (c_0 prof).run c hin (fun j' g' _ V' => j' = 22 ∧ g' = gP0 X.cpu.gpr ∧ V' = pV V X.cpu.gpr) hK hA hrip'
      (vc_z hs1 w2 ft (by rw [hvt]; exact ht)) ?_
    rintro j' g fl₁ V₁ ⟨rfl, rfl, hV₁⟩ U t₁ hKU hAU hrU hgU -
    subst V₁
    refine t22 U _ t₁ hKU hAU hrU (by rw [hgU]; dsimp only [gP0]; rw [e16, e24]) (by rw [hgU]) (by rw [hgU])
      hsb hsp hsr ?_
    intro bs Z t' hn hKZ hAZ hrZ hgZ
    refine kz ht bs Z t' hn hKZ hAZ hrZ ?_
    rw [hgZ, hgU]
    try rfl
  · -- `vt` not 0: to the `call`
    refine (c_0 prof).run c hin (fun j' g' _ V' => j' = 51 ∧ g' = gF0 X.cpu.gpr ∧ V' = pV V X.cpu.gpr) hK hA hrip'
      (vc_n hs1 w2 ft (by rw [hvt]; exact ht)) ?_
    rintro j' g fl₁ V₁ ⟨rfl, rfl, hV₁⟩ Y t₁ hKY hAY hrY hgY -
    subst V₁
    have hsY : Y.cpu.gpr.rsp = X.cpu.gpr.rsp - 24 := by rw [hgY, hgF]
    have hst : ∀ i < 8, Foot Wl (Addr.add (Y.cpu.gpr.rsp - 8) i) := by rw [hsY, e32]; exact hs4
    refine c.s_call hKY hAY hin (lt_len (by decide)) hrY (pdt_51 _) hinC hC0 (by decide) hst ?_
    rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
    rw [hsY, e32] at hA₂
    have hg₂' : Y₂.cpu.gpr = (gF X.cpu.gpr).set 4 (X.cpu.gpr.rsp - 32) := by
      rw [hg₂, hsY, e32, hgY, hgF]
    refine kf ht Y₂ t₂ hK₂ hA₂ hr₂ hg₂' ?_
    -- back from the callee
    intro Z V' t'' hKZ hAZ hrZ hzs hzb hzp hb hp' hr' hPc
    by_cases hm : (Z.cpu.gpr.rax.setWidth 32).msb = true
    · -- the result negative
      refine (c_56 prof).run c hin (fun j' g' _ V'' => j' = 39 ∧ g' = Z.cpu.gpr ∧ V'' = V') hKZ hAZ hrZ
        (vc_err hm) ?_
      rintro j' g fl₁ V₂ ⟨rfl, rfl, hV₂⟩ U t₃ hKU hAU hrU hgU -
      subst V₂
      have hsU : U.cpu.gpr.rsp = X.cpu.gpr.rsp - 24 := by rw [hgU]; exact hzs
      refine run_39 c hin hKU hAU hrU (b := X.cpu.gpr.rbx) (p := X.cpu.gpr.rbp) (by rw [hsU, a16]; exact hl16)
        (by rw [hsU, a16, a8]; exact hl8)
        (by rw [hsU, a16, a8, a0]; exact hl) (by rw [hsU, a16]; exact hb) (by rw [hsU, a16, a8]; exact hp')
        hin₂ h₂ (by rw [hsU, a16, a8, a0]; exact hr') ?_
      intro Z' t₄ hKZ' hAZ' hrZ' hgZ'
      refine ke Z V' Z' t₄ hPc hm hKZ' hAZ' hrZ' ?_
      rw [hgZ', hgU, hzs, a16, a8, a0]
      try rfl
    · -- the result not negative: the copy
      have hm' : (Z.cpu.gpr.rax.setWidth 32).msb = false := by simpa using hm
      refine (c_56 prof).run c hin (fun j' g' _ V'' => j' = 22 ∧ g' = Z.cpu.gpr ∧ V'' = V') hKZ hAZ hrZ
        (vc_ok hm') ?_
      rintro j' g fl₁ V₂ ⟨rfl, rfl, hV₂⟩ U t₃ hKU hAU hrU hgU -
      subst V₂
      refine t22 U V' t₃ hKU hAU hrU (by rw [hgU]; exact hzs) (by rw [hgU]; exact hzb) (by rw [hgU]; exact hzp)
        hb hp' hr' ?_
      intro bs Z' t₄ hn hKZ' hAZ' hrZ' hgZ'
      refine kr Z V' bs Z' t₄ hPc hm' hn hKZ' hAZ' hrZ' ?_
      rw [hgZ', hgU]

end FV7z.Pdt
