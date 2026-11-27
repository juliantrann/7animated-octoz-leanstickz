import FV7z.Efn.Cuts
import FV7z.Lemmas.LeafRet
import FV7z.Lemmas.Fr24
/-!
# `ExtractFileNameFromPath` (PLAN.md §M, M1)

7-Zip 26.06's `ExtractFileNameFromPath (const UString &path)` at `0x4528f0` in `7zzs`, `p` = `rdi` (the result),
`q` = `rsi` (`path`): `push r12; mov r12, rdi; mov rdi, rsi; push rbx; mov rbx, rsi; sub rsp, 8`; at 20
`call 0x44dd80` (`ReverseFind_PathSepar`, `FV7z/Rpp`, `rel` 18446744073709532279); at 25 `mov rdi, r12;
lea edx, [rax + 1]; mov rax, [rbx]; lea rsi, [rax + rdx * 4]`; at 38 `call 0x44d480` (`UString (const wchar_t *)`,
`FV7z/Ucw`, `rel` 18446744073709529957); at 43 `add rsp, 8; mov rax, r12; pop rbx; pop r12; ret` (53). Cuts 0, 25,
43 (kt632).

The wpx goals (kt632 probe):
- `W_0`: `Foot Wl` of `rsp - 8`, `rsp - 8 - 8` ∧ `Q 20 { g with rbx := rsi, rsp := rsp - 8 - 8 - 8#64,
  rdi := rsi, r12 := rdi } (subF …) Vp` (the same `Vp` as `Pvu`'s).
- `W_25`: `Foot F.data` of `rbx` (8) ∧ `Q 38 { g with rax := rdq(V, rbx), rdx := sw64 (sw32 (rax + 1#64)),
  rsi := rdq(V, rbx) + sw64 (sw32 (rax + 1#64)) * 4#64, rdi := r12 } (rfz f) V`.
- `W_43`: `Foot F.data` of `rsp + 8#64`, `rsp + 8#64 + 8` ∧ `Q 53 { g with rax := r12, rbx := rdq(V, rsp + 8#64),
  rsp := rsp + 8#64 + 8 + 8, r12 := rdq(V, rsp + 8#64 + 8) } … V`.

Design (as `FV7z/Pvu/Holds.lean`, the frame facts in `FV7z/Lemmas/Fr24.lean`): both callees are hypotheses, each a
continuation at its entry given the run from its return (`rsp` 24 below the entry's, `rbx` = `q` after the first,
`r12` = `p`, the saved `rbx`, `r12` and the return address left as they were, and the callee's own post `P1`, `P2`):
`k1` at `0x44dd80`, `k2` at `0x44d480` (registers `g38`: the second call's arguments from the first's result `rax`
and the bytes then), `kr` at the return address. Register equations are named and rewritten (`rw [h32, hgU]`), no
`congr`/`rfl` search.
- `gE g`: the registers at the first `call`; `g38 g V`: at the second.
- `efn_ok`: from the entry to the return address.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn FV7z.Fr24
namespace FV7z.Efn

theorem efn_20 : ∀ feat, Dec feat efn 20 (FV7z.mk .call 64 [.rel 18446744073709532279] 5) := by intro feat f; rfl
theorem efn_38 : ∀ feat, Dec feat efn 38 (FV7z.mk .call 64 [.rel 18446744073709529957] 5) := by intro feat f; rfl
theorem efn_53 : ∀ feat, Dec feat efn 53 (FV7z.mk .ret 64 [] 1) := by intro feat f; rfl

/-- The registers at the first `call`: `r12` = `p`, `rbx` = `rdi` = `q`, `rsp` 24 down. -/
abbrev gE (g : Gprs) : Gprs :=
  { g with
    rbx := g.rsi
    rsp := g.rsp - 8 - 8 - 8#64
    rdi := g.rsi
    r12 := g.rdi }

/-- The registers at the second `call`: `rdi` = `p`, `rsi` = `q`'s buffer + 4 (`rax` + 1). -/
abbrev g38 (g : Gprs) (V : Addr → Byte) : Gprs :=
  { g with
    rax := rdq(V, g.rbx)
    rdx := ((g.rax + 1#64).setWidth 32).setWidth 64
    rsi := rdq(V, g.rbx) + ((g.rax + 1#64).setWidth 32).setWidth 64 * 4#64
    rdi := g.r12 }

variable {F : Footprint} {Wl : List Rgn}

/-- `push r12; mov r12, rdi; mov rdi, rsi; push rbx; mov rbx, rsi; sub rsp, 8`, to the `call` at 20. -/
theorem vc_0 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (hs1 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8) i)) (hs2 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8) i))
    (h : ∀ fl, Q 20 (gE g) fl (Vst (Vst V (g.rsp - 8) (toBytesLE g.r12 8)) (g.rsp - 8 - 8) (toBytesLE g.rbx 8))) :
    W_0 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [gE] at hs1 hs2 h ⊢
  wpx [W_0, o0]
  all_goals repeat' (first | exact h _ | assumption | exact trivial | apply And.intro | intro _)

/-- `mov rdi, r12; lea edx, [rax + 1]; mov rax, [rbx]; lea rsi, [rax + rdx * 4]`, to the `call` at 38. -/
theorem vc_25 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} (fq : ∀ i < 8, Foot F.data (Addr.add g.rbx i))
    (h : ∀ fl, Q 38 (g38 g V) fl V) : W_25 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [g38] at fq h ⊢
  wpx [W_25, o1]
  all_goals repeat' (first | exact h _ | assumption | exact trivial | apply And.intro | intro _)

/-- `add rsp, 8; mov rax, r12; pop rbx; pop r12`, to the `ret` at 53. -/
theorem vc_43 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (hl1 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8#64) i))
    (hl2 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8#64 + 8) i))
    (h : ∀ fl, Q 53
      { g with
        rax := g.r12
        rbx := rdq(V, g.rsp + 8#64)
        rsp := g.rsp + 8#64 + 8 + 8
        r12 := rdq(V, g.rsp + 8#64 + 8) } fl V) :
    W_43 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hl1 hl2 h ⊢
  wpx [W_43, o2]
  all_goals repeat' (first | exact h _ | assumption | exact trivial | apply And.intro | intro _)

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE' : Outcome → List Event → Prop}
  {X : State} {t : Nat} {V : Addr → Byte}

/-- `ExtractFileNameFromPath (path)` (`p` = `rdi`, `q` = `rsi`) from its entry, `r12` and `rbx` saved at `rsp - 8`
and `rsp - 16`: at the first callee's entry (`0x44dd80`) with the registers `gE`, the return address `efn_at + 25` at
`rsp - 32` (`k1`); from its return, at the second's (`0x44d480`) with the registers `g38` (`k2`); from that return,
at the return address with `rax` = `p`, `rbx`, `r12`, `rsp` restored (`kr`). -/
theorem efn_ok {P1 P2 : State → (Addr → Byte) → Prop} (c : Seg prof F Wl L s₀ o) (hin : CodeIn L efn_at efn)
    {code1 : List Byte} (hin1 : CodeIn L 0x44dd80#64 code1) (hc1 : 0 < code1.length)
    {code2 : List Byte} (hin2 : CodeIn L 0x44d480#64 code2) (hc2 : 0 < code2.length)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = efn_at)
    (hp : 32 ≤ X.cpu.gpr.rsp.toNat)
    (hs1 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8) i))
    (hs2 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 16) i))
    (hs4 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 32) i))
    (hl : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsp i))
    (fq : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsi i))
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (k1 : ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y →
      Agree F Y.proc.mm.mem (Vst (Vst (Vst V (X.cpu.gpr.rsp - 8) (toBytesLE X.cpu.gpr.r12 8)) (X.cpu.gpr.rsp - 16)
        (toBytesLE X.cpu.gpr.rbx 8)) (X.cpu.gpr.rsp - 32) (toBytesLE (efn_at.add 25) 8)) →
      Y.cpu.rip = 0x44dd80#64 → Y.cpu.gpr = (gE X.cpu.gpr).set 4 (X.cpu.gpr.rsp - 32) →
      (∀ (Z : State) (V' : Addr → Byte) (t'' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V' →
        Z.cpu.rip = efn_at.add 25 → Z.cpu.gpr.rsp = X.cpu.gpr.rsp - 24 → Z.cpu.gpr.rbx = X.cpu.gpr.rsi →
        Z.cpu.gpr.r12 = X.cpu.gpr.rdi → rdq(V', X.cpu.gpr.rsp - 16) = X.cpu.gpr.rbx →
        rdq(V', X.cpu.gpr.rsp - 8) = X.cpu.gpr.r12 → rdq(V', X.cpu.gpr.rsp) = e₂.add j₂ → P1 Z V' →
        GoG prof L o gev gP gE' Z t'') →
      GoG prof L o gev gP gE' Y t')
    (k2 : ∀ (Z : State) (V' : Addr → Byte), P1 Z V' → ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y →
      Agree F Y.proc.mm.mem (Vst V' (X.cpu.gpr.rsp - 32) (toBytesLE (efn_at.add 43) 8)) →
      Y.cpu.rip = 0x44d480#64 → Y.cpu.gpr = (g38 Z.cpu.gpr V').set 4 (X.cpu.gpr.rsp - 32) →
      (∀ (Z₂ : State) (V₂ : Addr → Byte) (t'' : Nat), KeptW Wl s₀ Z₂ → Agree F Z₂.proc.mm.mem V₂ →
        Z₂.cpu.rip = efn_at.add 43 → Z₂.cpu.gpr.rsp = X.cpu.gpr.rsp - 24 → Z₂.cpu.gpr.r12 = X.cpu.gpr.rdi →
        rdq(V₂, X.cpu.gpr.rsp - 16) = X.cpu.gpr.rbx → rdq(V₂, X.cpu.gpr.rsp - 8) = X.cpu.gpr.r12 →
        rdq(V₂, X.cpu.gpr.rsp) = e₂.add j₂ → P2 Z₂ V₂ →
        GoG prof L o gev gP gE' Z₂ t'') →
      GoG prof L o gev gP gE' Y t')
    (kr : ∀ (Z₂ : State) (V₂ : Addr → Byte) (Z' : State) (t' : Nat), P2 Z₂ V₂ → KeptW Wl s₀ Z' →
      Agree F Z'.proc.mm.mem V₂ → Z'.cpu.rip = e₂.add j₂ →
      Z'.cpu.gpr = { Z₂.cpu.gpr with
        rax := X.cpu.gpr.rdi
        rbx := X.cpu.gpr.rbx
        rsp := X.cpu.gpr.rsp + 8
        r12 := X.cpu.gpr.r12 } →
      GoG prof L o gev gP gE' Z' t') :
    GoG prof L o gev gP gE' X t := by
  have h8 : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rsp - 8) i) := fun i hi => c.hws _ (hs1 i hi)
  have h16 : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rsp - 16) i) := fun i hi => c.hws _ (hs2 i hi)
  have hrip' : X.cpu.rip = efn_at.add 0 := by rw [addr_add_zero]; exact hrip
  -- the prologue, to the first `call`
  refine (c_0 prof).run c hin (fun j' g' _ V' => j' = 20 ∧ g' = gE X.cpu.gpr ∧
      V' = Vst (Vst V (X.cpu.gpr.rsp - 8) (toBytesLE X.cpu.gpr.r12 8)) (X.cpu.gpr.rsp - 16)
        (toBytesLE X.cpu.gpr.rbx 8)) hK hA hrip'
    (vc_0 hs1 (by rw [pe16]; exact hs2) fun _ => ⟨rfl, rfl, by rw [pe16]⟩) ?_
  rintro j' g fl V₁ ⟨rfl, rfl, hV₁⟩ Y t₁ hKY hAY hrY hgY -
  subst V₁
  have hsY : Y.cpu.gpr.rsp = X.cpu.gpr.rsp - 8 - 8 - 8#64 := by rw [hgY]
  have hY32 : Y.cpu.gpr.rsp - 8 = X.cpu.gpr.rsp - 32 := by rw [hsY, pe32]
  have hst : ∀ i < 8, Foot Wl (Addr.add (Y.cpu.gpr.rsp - 8) i) := by rw [hY32]; exact hs4
  refine c.s_call hKY hAY hin (lt_len (by decide)) hrY (efn_20 _) hin1 hc1 (by decide) hst ?_
  rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
  rw [hY32] at hA₂
  have hg₂' : Y₂.cpu.gpr = (gE X.cpu.gpr).set 4 (X.cpu.gpr.rsp - 32) := by rw [hg₂, hY32, hgY]
  refine k1 Y₂ t₂ hK₂ hA₂ hr₂ hg₂' ?_
  -- back from the first callee, at 25: to the second `call`
  intro Z V' t'' hKZ hAZ hrZ hzs hzb hz12 hb hr12 hr' hP1
  refine (c_25 prof).run c hin (fun j' g' _ V'' => j' = 38 ∧ g' = g38 Z.cpu.gpr V' ∧ V'' = V') hKZ hAZ hrZ
    (vc_25 (by rw [hzb]; exact fq) fun _ => ⟨rfl, rfl, rfl⟩) ?_
  rintro j' g fl V₂ ⟨rfl, rfl, hV₂⟩ U t₃ hKU hAU hrU hgU -
  subst V₂
  have hsU : U.cpu.gpr.rsp = X.cpu.gpr.rsp - 24 := by rw [hgU]; exact hzs
  have hU32 : U.cpu.gpr.rsp - 8 = X.cpu.gpr.rsp - 32 := by rw [hsU, peD]
  have hst2 : ∀ i < 8, Foot Wl (Addr.add (U.cpu.gpr.rsp - 8) i) := by rw [hU32]; exact hs4
  refine c.s_call hKU hAU hin (lt_len (by decide)) hrU (efn_38 _) hin2 hc2 (by decide) hst2 ?_
  rintro Y₃ t₄ hK₃ hA₃ ⟨hr₃, hg₃⟩
  rw [hU32] at hA₃
  have hg₃' : Y₃.cpu.gpr = (g38 Z.cpu.gpr V').set 4 (X.cpu.gpr.rsp - 32) := by rw [hg₃, hU32, hgU]
  refine k2 Z V' hP1 Y₃ t₄ hK₃ hA₃ hr₃ hg₃' ?_
  -- back from the second callee, at 43: the epilogue, then the `ret` at 53
  intro Z₂ V₂ t₅ hKZ₂ hAZ₂ hrZ₂ hz2s hz2r hb2 h12b hr2 hP2
  refine (c_43 prof).run c hin (fun j' g' _ V'' => j' = 53 ∧
      g' = { Z₂.cpu.gpr with
        rax := X.cpu.gpr.rdi
        rbx := X.cpu.gpr.rbx
        rsp := X.cpu.gpr.rsp
        r12 := X.cpu.gpr.r12 } ∧ V'' = V₂) hKZ₂ hAZ₂ hrZ₂
    (vc_43 (by rw [hz2s, peA']; exact h16) (by rw [hz2s, peA', peB]; exact h8)
      fun _ => ⟨rfl, by rw [hz2s, hz2r, peA', peB, peC, hb2, h12b], rfl⟩) ?_
  rintro j' g fl V₃ ⟨rfl, rfl, hV₃⟩ U₂ t₆ hKU₂ hAU₂ hrU₂ hgU₂ -
  subst V₃
  have hsU₂ : U₂.cpu.gpr.rsp = X.cpu.gpr.rsp := by rw [hgU₂]
  refine c.s_ret hKU₂ hAU₂ hin (lt_len (by decide)) hrU₂ (efn_53 _) (by rw [hsU₂]; exact hl) hin₂ h₂
    (by rw [hsU₂]; exact hr2) ?_
  rintro Z' t₇ hKZ' hAZ' ⟨hrZ', hgZ'⟩
  refine kr Z₂ V₂ Z' t₇ hP2 hKZ' hAZ' hrZ' ?_
  rw [hgZ', hgU₂]
  try rfl

end FV7z.Efn
