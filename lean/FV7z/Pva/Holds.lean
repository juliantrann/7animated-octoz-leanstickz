import FV7z.Pva.Cuts
import FV7z.Lemmas.LeafRet
import FV7z.Lemmas.Fr24
/-!
# `CPropVariant::operator=(const char *)` (PLAN.md §M, M1)

7-Zip 26.06's `NWindows::NCOM::CPropVariant::operator=(const char *s)` at `0x4572a0` in `7zzs`
(`CPP/Windows/PropVariant.cpp`; `objdump -d`), `p` = `rdi` (`this`), `s` = `rsi`:
`push r12; mov r12, rdi; push rbp; mov rbp, rsi; sub rsp, 8`; at 17 `call 0x457130` (`InternalClear`); at 22
`mov dword [r12], 8` (`vt` = `VT_BSTR`, `wReserved1` = 0); `mov rdi, rbp`; at 33 `call 0x456e50`
(`AllocBstrFromAscii (s)`, `FV7z/Aba`); at 38 `mov [r12 + 8], rax; test rax, rax`; at 46 `je 0x401cf6` (the throw
of `kMemException`, by hand: its target is outside); at 52 `add rsp, 8; mov rax, r12; pop rbp; pop r12; ret` (62).
Cuts 0, 22, 38, 52.

The frame of `FV7z/Lemmas/Fr24.lean` (`r12` at `rsp - 8`, `rbp` at `rsp - 16`, the return addresses of the two
`call`s at `rsp - 32`), as in `FV7z/Pvq/Holds.lean`, with two callees, each a hypothesis: a continuation at its entry
given the run from its return (`kf1`: `rsp` 24 below the entry's, `r12` = `p`, `rbp` = `s`, its own post `P1`;
`kf2`: also the saved `rbp`, `r12` and the return address left as they were, its post `P2`). The 8 bytes `bstrVal`
at `p + 8` are the result `rax`; the return address and the saved registers are read past that store (`hd`, `m8`).
The `je` is taken by `Seg.s_jcc_x` as in `FV7z/Arb/Holds.lean`: on NULL to the throw (`kt`), else to 52 (`kr`).

- `gN g`: the registers after the prologue; `pd8`: `p + 8` without wrap.
- `vc_0`, `vc_22`, `vc_38`, `vc_52`: the verification conditions of the four pieces (`vc_38` also gives `ZF` of
  `test rax, rax`).
- `pva_ok`: from the entry through both callees to the throw (`rax` = 0) or to the return address with `rax` = `p`
  and `rbp`, `r12`, `rsp` restored.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn FV7z.Fr24
namespace FV7z.Pva

theorem pva_17 : ∀ feat, Dec feat pva 17 (FV7z.mk .call 64 [.rel 18446744073709551226] 5) := by intro feat f; rfl
theorem pva_33 : ∀ feat, Dec feat pva 33 (FV7z.mk .call 64 [.rel 18446744073709550474] 5) := by intro feat f; rfl
theorem pva_46 : ∀ feat, Dec feat pva 46 (FV7z.mk (.jcc 4) 64 [.rel 18446744073709201954] 6) := by
  intro feat f; rfl
theorem pva_62 : ∀ feat, Dec feat pva 62 (FV7z.mk .ret 64 [] 1) := by intro feat f; rfl

/-- The registers after the prologue: `r12` = `p`, `rbp` = `s`, `rsp` 24 down. -/
abbrev gN (g : Gprs) : Gprs :=
  { g with
    rsp := g.rsp - 8 - 8 - 8#64
    rbp := g.rsi
    r12 := g.rdi }

theorem pd8 (p : BitVec 64) (h : p.toNat + 16 ≤ 2 ^ 64) : (p + 8#64).toNat = p.toNat + 8 := by bv_omega

variable {F : Footprint} {Wl : List Rgn}

/-- `push r12; mov r12, rdi; push rbp; mov rbp, rsi; sub rsp, 8`, to the `call` at 17. -/
theorem vc_0 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (hs1 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8) i)) (hs2 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8) i))
    (h : ∀ fl, Q 17 (gN g) fl (Vst (Vst V (g.rsp - 8) (toBytesLE g.r12 8)) (g.rsp - 8 - 8) (toBytesLE g.rbp 8))) :
    W_0 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [gN] at hs1 hs2 h ⊢
  wpx [W_0, o0]
  all_goals repeat' (first | exact h _ | assumption | exact trivial | apply And.intro | intro _)

/-- `mov dword [r12], 8; mov rdi, rbp`, to the `call` at 33. -/
theorem vc_22 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} (fw : ∀ i < 4, Foot Wl (Addr.add g.r12 i))
    (h : ∀ fl, Q 33 { g with rdi := g.rbp } fl (Vst V g.r12 (toBytesLE 8#32 4))) : W_22 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at fw h ⊢
  wpx [W_22, o1]
  all_goals repeat' (first | exact h _ | assumption | exact trivial | apply And.intro | intro _)

/-- `mov [r12 + 8], rax; test rax, rax`, to the `je` at 46: `ZF` is `rax = 0`. -/
theorem vc_38 {g : Gprs} {f : Rflags} {V : Addr → Byte} {p : Addr} (hp : g.r12 = p)
    (fw8 : ∀ i < 8, Foot Wl (Addr.add (p + 8#64) i)) :
    W_38 F Wl (fun j' g' f' V' => j' = 46 ∧ g' = g ∧ V' = Vst V (p + 8#64) (toBytesLE g.rax 8) ∧
      f'.zf = (g.rax == 0)) g f V := by
  subst hp
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at fw8 ⊢
  wpx [W_38, o2, BitVec.and_self]
  all_goals repeat' (first | exact rfl | assumption | exact trivial | apply And.intro | intro _)

/-- `add rsp, 8; mov rax, r12; pop rbp; pop r12`, to the `ret` at 62. -/
theorem vc_52 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (hl1 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8#64) i))
    (hl2 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8#64 + 8) i))
    (h : ∀ fl, Q 62
      { g with
        rax := g.r12
        rsp := g.rsp + 8#64 + 8 + 8
        rbp := rdq(V, g.rsp + 8#64)
        r12 := rdq(V, g.rsp + 8#64 + 8) } fl V) :
    W_52 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hl1 hl2 h ⊢
  wpx [W_52, o3]
  all_goals repeat' (first | exact h _ | assumption | exact trivial | apply And.intro | intro _)

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {X : State} {t : Nat} {V : Addr → Byte}

/-- `CPropVariant::operator=(const char *)` (`p` = `rdi`, `s` = `rsi`) from its entry: at `InternalClear`'s entry
(`kf1`); from its return, `vt` = `VT_BSTR` and `wReserved1` = 0 stored, at `AllocBstrFromAscii`'s entry with `rdi` =
`s` (`kf2`); from its return with the result `rax` stored as `bstrVal`: when NULL at the throw (`kt`), else at the
return address with `rax` = `p` and `rbp`, `r12`, `rsp` as at the entry (`kr`). -/
theorem pva_ok {P1 P2 : State → (Addr → Byte) → Prop} (c : Seg prof F Wl L s₀ o) (hin : CodeIn L pva_at pva)
    {codeC : List Byte} (hinC : CodeIn L 0x457130#64 codeC) (hC0 : 0 < codeC.length)
    {codeA : List Byte} (hinA : CodeIn L 0x456e50#64 codeA) (hA0 : 0 < codeA.length)
    {codeT : List Byte} (hinT : CodeIn L 0x401cf6#64 codeT) (hT : 0 < codeT.length)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = pva_at)
    (hp : 32 ≤ X.cpu.gpr.rsp.toNat) (hp8 : X.cpu.gpr.rsp.toNat + 8 ≤ 2 ^ 64)
    (hs1 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8) i))
    (hs2 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 16) i))
    (hs4 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 32) i))
    (hl : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsp i))
    (fw : ∀ i < 4, Foot Wl (Addr.add X.cpu.gpr.rdi i))
    (fw8 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rdi + 8#64) i))
    (hq : X.cpu.gpr.rdi.toNat + 16 ≤ 2 ^ 64)
    (hd : X.cpu.gpr.rdi.toNat + 16 ≤ X.cpu.gpr.rsp.toNat - 16 ∨ X.cpu.gpr.rsp.toNat + 8 ≤ X.cpu.gpr.rdi.toNat + 8)
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (kf1 : ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y →
      Agree F Y.proc.mm.mem (Vst (Vst (Vst V (X.cpu.gpr.rsp - 8) (toBytesLE X.cpu.gpr.r12 8)) (X.cpu.gpr.rsp - 16)
        (toBytesLE X.cpu.gpr.rbp 8)) (X.cpu.gpr.rsp - 32) (toBytesLE (pva_at.add 22) 8)) →
      Y.cpu.rip = 0x457130#64 → Y.cpu.gpr = (gN X.cpu.gpr).set 4 (X.cpu.gpr.rsp - 32) →
      (∀ (Z : State) (V' : Addr → Byte) (t'' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V' →
        Z.cpu.rip = pva_at.add 22 → Z.cpu.gpr.rsp = X.cpu.gpr.rsp - 24 → Z.cpu.gpr.r12 = X.cpu.gpr.rdi →
        Z.cpu.gpr.rbp = X.cpu.gpr.rsi → P1 Z V' → GoG prof L o gev gP gE Z t'') →
      GoG prof L o gev gP gE Y t')
    (kf2 : ∀ (Z : State) (V' : Addr → Byte), P1 Z V' → ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y →
      Agree F Y.proc.mm.mem (Vst (Vst V' X.cpu.gpr.rdi (toBytesLE 8#32 4)) (X.cpu.gpr.rsp - 32)
        (toBytesLE (pva_at.add 38) 8)) →
      Y.cpu.rip = 0x456e50#64 → Y.cpu.gpr = ({ Z.cpu.gpr with rdi := X.cpu.gpr.rsi }).set 4 (X.cpu.gpr.rsp - 32) →
      (∀ (U : State) (W : Addr → Byte) (t'' : Nat), KeptW Wl s₀ U → Agree F U.proc.mm.mem W →
        U.cpu.rip = pva_at.add 38 → U.cpu.gpr.rsp = X.cpu.gpr.rsp - 24 → U.cpu.gpr.r12 = X.cpu.gpr.rdi →
        rdq(W, X.cpu.gpr.rsp - 16) = X.cpu.gpr.rbp → rdq(W, X.cpu.gpr.rsp - 8) = X.cpu.gpr.r12 →
        rdq(W, X.cpu.gpr.rsp) = e₂.add j₂ → P2 U W → GoG prof L o gev gP gE U t'') →
      GoG prof L o gev gP gE Y t')
    (kt : ∀ (U : State) (W : Addr → Byte), P2 U W → U.cpu.gpr.rax = 0 →
      ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y →
      Agree F Y.proc.mm.mem (Vst W (X.cpu.gpr.rdi + 8#64) (toBytesLE U.cpu.gpr.rax 8)) →
      Y.cpu.rip = 0x401cf6#64 → Y.cpu.gpr = U.cpu.gpr → GoG prof L o gev gP gE Y t')
    (kr : ∀ (U : State) (W : Addr → Byte) (Z' : State) (t' : Nat), P2 U W → U.cpu.gpr.rax ≠ 0 →
      KeptW Wl s₀ Z' →
      Agree F Z'.proc.mm.mem (Vst W (X.cpu.gpr.rdi + 8#64) (toBytesLE U.cpu.gpr.rax 8)) →
      Z'.cpu.rip = e₂.add j₂ →
      Z'.cpu.gpr = { U.cpu.gpr with
        rax := X.cpu.gpr.rdi
        rbp := X.cpu.gpr.rbp
        rsp := X.cpu.gpr.rsp + 8
        r12 := X.cpu.gpr.r12 } →
      GoG prof L o gev gP gE Z' t') :
    GoG prof L o gev gP gE X t := by
  have t8 := pt8 _ hp
  have t16 := pt16 _ hp
  have d8 := pd8 _ hq
  have h8 : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rsp - 8) i) := fun i hi => c.hws _ (hs1 i hi)
  have h16 : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rsp - 16) i) := fun i hi => c.hws _ (hs2 i hi)
  -- reads of 8 bytes past the store of `bstrVal`
  have m8 : ∀ (W : Addr → Byte) (v : BitVec 64) (x : Addr), x.toNat + 8 ≤ 2 ^ 64 →
      (X.cpu.gpr.rdi.toNat + 16 ≤ x.toNat ∨ x.toNat + 8 ≤ X.cpu.gpr.rdi.toNat + 8) →
      (byteAddrs x 8).map (Vst W (X.cpu.gpr.rdi + 8#64) (toBytesLE v 8)) = (byteAddrs x 8).map W :=
    fun W v x hx h => Tun.rd_Vst W _ _ x 8 (by rw [toBytesLE_length, d8]; omega) hx
      (by rw [toBytesLE_length, d8]; omega)
  have hq8 : (X.cpu.gpr.rsp - 8).toNat + 8 ≤ 2 ^ 64 := by rw [t8]; omega
  have hq16 : (X.cpu.gpr.rsp - 16).toNat + 8 ≤ 2 ^ 64 := by rw [t16]; omega
  have hrip' : X.cpu.rip = pva_at.add 0 := by rw [addr_add_zero]; exact hrip
  -- the prologue, to the `call` of `InternalClear`
  refine (c_0 prof).run c hin (fun j' g' _ V' => j' = 17 ∧ g' = gN X.cpu.gpr ∧
      V' = Vst (Vst V (X.cpu.gpr.rsp - 8) (toBytesLE X.cpu.gpr.r12 8)) (X.cpu.gpr.rsp - 16)
        (toBytesLE X.cpu.gpr.rbp 8)) hK hA hrip'
    (vc_0 hs1 (by rw [pe16]; exact hs2) fun _ => ⟨rfl, rfl, by rw [pe16]⟩) ?_
  rintro j' g fl V₁ ⟨rfl, rfl, hV₁⟩ Y t₁ hKY hAY hrY hgY -
  subst V₁
  have hsY : Y.cpu.gpr.rsp = X.cpu.gpr.rsp - 8 - 8 - 8#64 := by rw [hgY]
  have hst : ∀ i < 8, Foot Wl (Addr.add (Y.cpu.gpr.rsp - 8) i) := by rw [hsY, pe32]; exact hs4
  refine c.s_call hKY hAY hin (lt_len (by decide)) hrY (pva_17 _) hinC hC0 (by decide) hst ?_
  rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
  rw [hsY, pe32] at hA₂
  have hg₂' : Y₂.cpu.gpr = (gN X.cpu.gpr).set 4 (X.cpu.gpr.rsp - 32) := by
    rw [hg₂, hgY]
    exact congrArg (fun v => (gN X.cpu.gpr).set 4 v) (pe32 X.cpu.gpr.rsp)
  refine kf1 Y₂ t₂ hK₂ hA₂ hr₂ hg₂' ?_
  -- back from `InternalClear`, at 22: the tag, to the `call` of `AllocBstrFromAscii`
  intro Z V' t'' hKZ hAZ hrZ hzs hz12 hzb hP1
  refine (c_22 prof).run c hin (fun j' g' _ V'' => j' = 33 ∧ g' = { Z.cpu.gpr with rdi := X.cpu.gpr.rsi } ∧
      V'' = Vst V' X.cpu.gpr.rdi (toBytesLE 8#32 4)) hKZ hAZ hrZ
    (vc_22 (by rw [hz12]; exact fw) fun _ => ⟨rfl, by rw [hzb], by rw [hz12]⟩) ?_
  rintro j' g fl V₂ ⟨rfl, rfl, hV₂⟩ U t₃ hKU hAU hrU hgU -
  subst V₂
  have hsU : U.cpu.gpr.rsp = X.cpu.gpr.rsp - 24 := by rw [hgU]; exact hzs
  have hst2 : ∀ i < 8, Foot Wl (Addr.add (U.cpu.gpr.rsp - 8) i) := by rw [hsU, peD]; exact hs4
  refine c.s_call hKU hAU hin (lt_len (by decide)) hrU (pva_33 _) hinA hA0 (by decide) hst2 ?_
  rintro Y₃ t₄ hK₃ hA₃ ⟨hr₃, hg₃⟩
  rw [hsU, peD] at hA₃
  have hg₃' : Y₃.cpu.gpr = ({ Z.cpu.gpr with rdi := X.cpu.gpr.rsi }).set 4 (X.cpu.gpr.rsp - 32) := by
    rw [hg₃, hgU]
    exact congrArg (fun v => ({ Z.cpu.gpr with rdi := X.cpu.gpr.rsi }).set 4 v)
      (show Z.cpu.gpr.rsp - 8 = X.cpu.gpr.rsp - 32 by rw [hzs, peD])
  refine kf2 Z V' hP1 Y₃ t₄ hK₃ hA₃ hr₃ hg₃' ?_
  -- back from `AllocBstrFromAscii`, at 38: `bstrVal`, to the `je`
  intro U₂ W t₅ hKU₂ hAU₂ hrU₂ hus hu12 hvb hv12 hvra hP2
  refine (c_38 prof).run c hin (fun j' g' f' V'' => j' = 46 ∧ g' = U₂.cpu.gpr ∧
      V'' = Vst W (X.cpu.gpr.rdi + 8#64) (toBytesLE U₂.cpu.gpr.rax 8) ∧ f'.zf = (U₂.cpu.gpr.rax == 0))
    hKU₂ hAU₂ hrU₂ (vc_38 hu12 fw8) ?_
  rintro j' g fl V₃ ⟨rfl, rfl, hV₃, hzf⟩ Y₄ t₆ hKY₄ hAY₄ hrY₄ hgY₄ hfY₄
  subst V₃
  have hcc : Y₄.cpu.rflags.cond 4 = (U₂.cpu.gpr.rax == 0) := by rw [hfY₄, cond_4]; exact hzf
  refine c.s_jcc_x hKY₄ hAY₄ hin (lt_len (by decide)) hrY₄ (pva_46 _) hinT hT (tgt := 0) (by decide) ?_ ?_
  · -- NULL: the throw
    intro hc Y₁ t₇ hK₁ hA₁ ⟨hr₁, hg₁⟩
    rw [hcc] at hc
    exact kt U₂ W hP2 (beq_iff_eq.mp hc) Y₁ t₇ hK₁ hA₁ (by rw [hr₁, addr_add_zero]) (by rw [hg₁, hgY₄])
  intro hc Y₁ t₇ hK₁ hA₁ ⟨hr₁, hg₁⟩
  rw [hcc] at hc
  have hnz : U₂.cpu.gpr.rax ≠ 0 := fun h => by rw [h] at hc; exact absurd hc (by decide)
  have hsY₁ : Y₁.cpu.gpr.rsp = X.cpu.gpr.rsp - 24 := by rw [hg₁, hgY₄]; exact hus
  have hb1 : rdq(Vst W (X.cpu.gpr.rdi + 8#64) (toBytesLE U₂.cpu.gpr.rax 8), X.cpu.gpr.rsp - 16) =
      X.cpu.gpr.rbp := by
    rw [m8 _ _ _ hq16 (by rw [t16]; omega)]
    exact hvb
  have hb2 : rdq(Vst W (X.cpu.gpr.rdi + 8#64) (toBytesLE U₂.cpu.gpr.rax 8), X.cpu.gpr.rsp - 8) =
      X.cpu.gpr.r12 := by
    rw [m8 _ _ _ hq8 (by rw [t8]; omega)]
    exact hv12
  have hb3 : rdq(Vst W (X.cpu.gpr.rdi + 8#64) (toBytesLE U₂.cpu.gpr.rax 8), X.cpu.gpr.rsp) = e₂.add j₂ := by
    rw [m8 _ _ _ hp8 (by omega)]
    exact hvra
  -- at 52, to the `ret`
  refine (c_52 prof).run c hin (fun j' g' _ V'' => j' = 62 ∧
      g' = { U₂.cpu.gpr with
        rax := X.cpu.gpr.rdi
        rbp := X.cpu.gpr.rbp
        rsp := X.cpu.gpr.rsp
        r12 := X.cpu.gpr.r12 } ∧
      V'' = Vst W (X.cpu.gpr.rdi + 8#64) (toBytesLE U₂.cpu.gpr.rax 8)) hK₁ hA₁ hr₁
    (vc_52 (by rw [hsY₁, peA']; exact h16) (by rw [hsY₁, peA', peB]; exact h8)
      fun _ => ⟨rfl, by rw [hg₁, hgY₄]; dsimp only; rw [hus, hu12, peA', peB, peC, hb1, hb2], rfl⟩) ?_
  rintro j' g fl V₄ ⟨rfl, rfl, hV₄⟩ U₃ t₈ hKU₃ hAU₃ hrU₃ hgU₃ -
  subst V₄
  have hsU₃ : U₃.cpu.gpr.rsp = X.cpu.gpr.rsp := by rw [hgU₃]
  refine c.s_ret hKU₃ hAU₃ hin (lt_len (by decide)) hrU₃ (pva_62 _) (by rw [hsU₃]; exact hl) hin₂ h₂
    (by rw [hsU₃]; exact hb3) ?_
  rintro Z' t₉ hKZ' hAZ' ⟨hrZ', hgZ'⟩
  refine kr U₂ W Z' t₉ hP2 hnz hKZ' hAZ' hrZ' ?_
  rw [hgZ', hgU₃]
  try rfl

end FV7z.Pva
