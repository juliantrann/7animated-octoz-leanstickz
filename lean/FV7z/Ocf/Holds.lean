import FV7z.Ocf.Cuts
import FV7z.Lemmas.LeafRet
/-!
# `COpenCallbackConsole::Open_Finished` (PLAN.md §M, M1)

7-Zip 26.06's `COpenCallbackConsole::Open_Finished ()` at `0x5f66a0` in `7zzs`
(`CPP/7zip/UI/Console/OpenCallbackConsole.cpp`; `objdump -d`), `this` = `rdi`: `ClosePercents ()`, then `S_OK`.
`cmp qword [rdi + 64], 0; je 48` (`_percent._so`); at 11 `cmp byte [rdi + 72], 0; jne 48`
(`_percent.DisableOutput`); at 17 `sub rsp, 8; add rdi, 8; mov esi, 1`; at 30 `call 0x5f67c0`
(`CPercentPrinter::ClosePrint (true)` on `_percent` at `this + 8`); at 35 `xor eax, eax; add rsp, 8; ret` (41); at 48
`xor eax, eax; ret` (50). Cuts 0, 35, 48.

- `pb V a`: the byte at `a`; `gC g`: the registers at the `call`.
- `vc_0`: from the entry, to 48 when `_so` = 0 or `DisableOutput` ≠ 0 (`h48`), else to the `call` (`h30`); the
  conditions by `subF_zf` (`ZF` of `cmp m, 0` is `m = 0`). `vc_35`, `vc_48`: the two tails to their `ret`s.
- `ocf_ok`: from the entry to the return address. Without the `call`: `rax` = 0, the memory as it was (`k0`).
  With it: at the callee's entry with the registers `gC` and the return address `ocf_at + 35` at `rsp - 16` (`kf`);
  if the callee returns there with `rsp` as it found it and the return address left as it was, the run reaches the
  return address with `rax` = 0 and the callee's registers otherwise (`kr`).
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Ocf

theorem ocf_30 : ∀ feat, Dec feat ocf 30 (FV7z.mk .call 64 [.rel 253] 5) := by intro feat f; rfl
theorem ocf_41 : ∀ feat, Dec feat ocf 41 (FV7z.mk .ret 64 [] 1) := by intro feat f; rfl
theorem ocf_50 : ∀ feat, Dec feat ocf 50 (FV7z.mk .ret 64 [] 1) := by intro feat f; rfl

/-- The byte at `a`. -/
abbrev pb (V : Addr → Byte) (a : Addr) : BitVec 8 := ofBytesLE 8 (List.map V (byteAddrs a 1))

/-- The registers at the `call`: `rsp` 8 down, `rdi` = `&_percent`, `esi` = 1. -/
abbrev gC (g : Gprs) : Gprs :=
  { g with
    rsp := g.rsp - 8#64
    rsi := BitVec.setWidth 64 1#32
    rdi := g.rdi + 8#64 }

theorem pS (s : Addr) : s - 8#64 - 8 = s - 16 := by bv_omega
theorem pR (s : Addr) : s - 8#64 + 8#64 = s := BitVec.sub_add_cancel _ _

variable {F : Footprint} {Wl : List Rgn}

/-- `cmp qword [rdi + 64], 0; je 48; cmp byte [rdi + 72], 0; jne 48; sub rsp, 8; add rdi, 8; mov esi, 1`: to 48 or
to the `call` at 30. -/
theorem vc_0 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (fq : ∀ i < 8, Foot F.data (Addr.add (g.rdi + 64#64) i))
    (fb : ∀ i < 1, Foot F.data (Addr.add (g.rdi + 72#64) i))
    (h48 : rdq(V, g.rdi + 64#64) = 0#64 ∨ ¬ pb V (g.rdi + 72#64) = 0#8 → ∀ fl, Q 48 g fl V)
    (h30 : ¬ rdq(V, g.rdi + 64#64) = 0#64 → pb V (g.rdi + 72#64) = 0#8 → ∀ fl, Q 30 (gC g) fl V) :
    W_0 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [gC, pb] at fq fb h48 h30 ⊢
  wpx [W_0, W_11, W_17, o0, o1, o2, Op.cmpmi, Bool.not_eq_true', Bool.not_eq_false', decide_eq_true_eq,
    decide_eq_false_iff_not]
  all_goals repeat' (first
    | exact rfl
    | assumption
    | exact trivial
    | (intro hh; exact h48 (Or.inl hh) _)
    | (intro hh; exact h48 (Or.inr hh) _)
    | (apply h30 <;> assumption)
    | apply And.intro
    | intro _)

/-- `xor eax, eax; add rsp, 8`, to the `ret` at 41. -/
theorem vc_35 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (h : ∀ fl, Q 41 { g with rax := 0, rsp := g.rsp + 8#64 } fl V) : W_35 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h ⊢
  wpx [W_35, o3, lf_xz, BitVec.xor_self, BitVec.setWidth_zero]
  all_goals repeat' (first | exact h _ | assumption | exact trivial | apply And.intro | intro _)

/-- `xor eax, eax`, to the `ret` at 50. -/
theorem vc_48 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (h : ∀ fl, Q 50 { g with rax := 0 } fl V) : W_48 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h ⊢
  wpx [W_48, o4, lf_xz, BitVec.xor_self, BitVec.setWidth_zero]
  all_goals repeat' (first | exact h _ | assumption | exact trivial | apply And.intro | intro _)

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {X : State} {t : Nat} {V : Addr → Byte}

/-- `COpenCallbackConsole::Open_Finished ()` (`this` = `rdi`) from its entry. With `_percent._so` = 0 or
`_percent.DisableOutput` ≠ 0: at the return address with `rax` = 0, the memory as it was (`k0`). Else at
`ClosePrint`'s entry (`0x5f67c0`) with the registers `gC` and the return address `ocf_at + 35` at `rsp - 16` (`kf`); if
the callee returns there with `rsp` 8 below the entry's and the return address left as it was, the run reaches the
return address with `rax` = 0 (`kr`). -/
theorem ocf_ok {Pc : State → (Addr → Byte) → Prop} (c : Seg prof F Wl L s₀ o) (hin : CodeIn L ocf_at ocf)
    {codeC : List Byte} (hinC : CodeIn L 0x5f67c0#64 codeC) (hC0 : 0 < codeC.length)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = ocf_at)
    (fq : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rdi + 64#64) i))
    (fb : ∀ i < 1, Foot F.data (Addr.add (X.cpu.gpr.rdi + 72#64) i))
    (hs2 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 16) i))
    (hl : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsp i))
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (hra : rdq(V, X.cpu.gpr.rsp) = e₂.add j₂)
    (k0 : rdq(V, X.cpu.gpr.rdi + 64#64) = 0#64 ∨ ¬ pb V (X.cpu.gpr.rdi + 72#64) = 0#8 →
      ∀ (Z : State) (t' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V → Z.cpu.rip = e₂.add j₂ →
      Z.cpu.gpr = { X.cpu.gpr with rax := 0, rsp := X.cpu.gpr.rsp + 8 } → GoG prof L o gev gP gE Z t')
    (kf : ¬ rdq(V, X.cpu.gpr.rdi + 64#64) = 0#64 → pb V (X.cpu.gpr.rdi + 72#64) = 0#8 →
      ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y →
      Agree F Y.proc.mm.mem (Vst V (X.cpu.gpr.rsp - 16) (toBytesLE (ocf_at.add 35) 8)) →
      Y.cpu.rip = 0x5f67c0#64 → Y.cpu.gpr = (gC X.cpu.gpr).set 4 (X.cpu.gpr.rsp - 16) →
      (∀ (Z : State) (V' : Addr → Byte) (t'' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V' →
        Z.cpu.rip = ocf_at.add 35 → Z.cpu.gpr.rsp = X.cpu.gpr.rsp - 8#64 →
        rdq(V', X.cpu.gpr.rsp) = e₂.add j₂ →
        Pc Z V' → GoG prof L o gev gP gE Z t'') →
      GoG prof L o gev gP gE Y t')
    (kr : ∀ (Z : State) (V' : Addr → Byte) (Z' : State) (t' : Nat), Pc Z V' → KeptW Wl s₀ Z' →
      Agree F Z'.proc.mm.mem V' → Z'.cpu.rip = e₂.add j₂ →
      Z'.cpu.gpr = { Z.cpu.gpr with rax := 0, rsp := X.cpu.gpr.rsp + 8 } → GoG prof L o gev gP gE Z' t') :
    GoG prof L o gev gP gE X t := by
  have hrip' : X.cpu.rip = ocf_at.add 0 := by rw [addr_add_zero]; exact hrip
  by_cases h1 : rdq(V, X.cpu.gpr.rdi + 64#64) = 0#64 ∨ ¬ pb V (X.cpu.gpr.rdi + 72#64) = 0#8
  · -- no `call`: to 48, then the `ret` at 50
    refine (c_0 prof).run c hin (fun j' g' _ V' => j' = 48 ∧ g' = X.cpu.gpr ∧ V' = V) hK hA hrip'
      (vc_0 fq fb (fun _ _ => ⟨rfl, rfl, rfl⟩) (fun h2 h3 => (h1.elim h2 (fun h => h h3)).elim)) ?_
    rintro j' g fl V₁ ⟨rfl, rfl, hV₁⟩ U t₁ hKU hAU hrU hgU -
    subst V₁
    refine (c_48 prof).run c hin (fun j' g' _ V' => j' = 50 ∧ g' = { X.cpu.gpr with rax := 0 } ∧ V' = V)
      hKU hAU hrU (vc_48 fun _ => ⟨rfl, by rw [hgU], rfl⟩) ?_
    rintro j' g fl V₂ ⟨rfl, rfl, hV₂⟩ U₂ t₂ hKU₂ hAU₂ hrU₂ hgU₂ -
    subst V₂
    have hsp : U₂.cpu.gpr.rsp = X.cpu.gpr.rsp := by rw [hgU₂]
    refine c.s_ret hKU₂ hAU₂ hin (lt_len (by decide)) hrU₂ (ocf_50 _) (by rw [hsp]; exact hl) hin₂ h₂
      (by rw [hsp]; exact hra) ?_
    rintro Z t₃ hKZ hAZ ⟨hrZ, hgZ⟩
    refine k0 h1 Z t₃ hKZ hAZ hrZ ?_
    rw [hgZ, hgU₂]
    try rfl
  · -- the `call` of `ClosePrint`
    have h2 : ¬ rdq(V, X.cpu.gpr.rdi + 64#64) = 0#64 := fun h => h1 (Or.inl h)
    have h3 : pb V (X.cpu.gpr.rdi + 72#64) = 0#8 := Decidable.of_not_not fun h => h1 (Or.inr h)
    refine (c_0 prof).run c hin (fun j' g' _ V' => j' = 30 ∧ g' = gC X.cpu.gpr ∧ V' = V) hK hA hrip'
      (vc_0 fq fb (fun h _ => absurd h h1) (fun _ _ _ => ⟨rfl, rfl, rfl⟩)) ?_
    rintro j' g fl V₁ ⟨rfl, rfl, hV₁⟩ Y t₁ hKY hAY hrY hgY -
    subst V₁
    have hsY : Y.cpu.gpr.rsp = X.cpu.gpr.rsp - 8#64 := by rw [hgY]
    have hst : ∀ i < 8, Foot Wl (Addr.add (Y.cpu.gpr.rsp - 8) i) := by rw [hsY, pS]; exact hs2
    refine c.s_call hKY hAY hin (lt_len (by decide)) hrY (ocf_30 _) hinC hC0 (by decide) hst ?_
    rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
    rw [hsY, pS] at hA₂
    have hg₂' : Y₂.cpu.gpr = (gC X.cpu.gpr).set 4 (X.cpu.gpr.rsp - 16) := by
      rw [hg₂, hgY]
      exact congrArg (fun v => (gC X.cpu.gpr).set 4 v) (pS X.cpu.gpr.rsp)
    refine kf h2 h3 Y₂ t₂ hK₂ hA₂ hr₂ hg₂' ?_
    -- back from the callee, at 35
    intro Z V' t'' hKZ hAZ hrZ hzs hr' hPc
    refine (c_35 prof).run c hin (fun j' g' _ V'' => j' = 41 ∧
        g' = { Z.cpu.gpr with rax := 0, rsp := X.cpu.gpr.rsp } ∧ V'' = V') hKZ hAZ hrZ
      (vc_35 fun _ => ⟨rfl, by rw [hzs, pR], rfl⟩) ?_
    rintro j' g fl V₂ ⟨rfl, rfl, hV₂⟩ U t₃ hKU hAU hrU hgU -
    subst V₂
    have hsU : U.cpu.gpr.rsp = X.cpu.gpr.rsp := by rw [hgU]
    refine c.s_ret hKU hAU hin (lt_len (by decide)) hrU (ocf_41 _) (by rw [hsU]; exact hl) hin₂ h₂
      (by rw [hsU]; exact hr') ?_
    rintro Z' t₄ hKZ' hAZ' ⟨hrZ', hgZ'⟩
    refine kr Z V' Z' t₄ hPc hKZ' hAZ' hrZ' ?_
    rw [hgZ', hgU]
    try rfl

end FV7z.Ocf
