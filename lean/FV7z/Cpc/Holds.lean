import FV7z.Cpc.Cuts
import FV7z.Nst
import FV7z.Uct.Blocks
import FV7z.Lemmas.LeafRet
import FV7z.Lemmas.Lock2
/-!
# `NCommandLineParser::CParser::CParser ()` (PLAN.md §M, M1)

7-Zip 26.06's `CParser::CParser ()` at `0x5a0490` in `7zzs` (`CPP/Common/CommandLineParser.cpp`): `r13`, `r12`,
`rbp`, `rbx` saved, `rbx` = `this`, `rsp` 8 lower, the 24 bytes of `_switches` (at `this`) 0 and `StopSwitchIndex`
(the 4 bytes at `this + 24`) -1, then the `AString` at `this + 32` (`call` at 52 to the function at `0x44c360`,
`Nst.nst_at`) and the `UString` at `this + 48` (`call` at 61 to `UString::UString ()`, `Uct.uct_at`); the frame
given back (66) and `ret` (76).

The callees are hypotheses (`kf1`, `kf2`), as in `FV7z/Uct/Holds.lean`: each a continuation at its entry, given the
run from its return (`cpc_at + 57`, `cpc_at + 66`, `rsp` as at the `call`) on. The second's run also gives the saved
registers and the return address back as they were (`kf2`), and its own post `P2`; `kr` takes the run on from the
return address.

- `gA`, `VA`: the registers and the bytes at the first `call`.
- `vc_0`, `vc_57`, `vc_66`: the verification conditions of the three pieces.
- `cpc_ok`: from the entry, through the two callees, to the return address with `rbx`, `rbp`, `r12`, `r13`
  restored and `rsp` 8 up.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Cpc

/-- The `call` to the `AString` set-up. -/
def pcall1 : List Byte := [0xe8, 0x97, 0xbe, 0xea, 0xff]
theorem pcall1_0 : ∀ feat, Dec feat pcall1 0 (FV7z.mk .call 64 [.rel 18446744073708158615] 5) := by dec_rfl
theorem wc_52 : pcall1 <+: cpc.drop 52 := by decide +kernel
theorem call_52 (feat : Features) : Dec feat cpc 52 (FV7z.mk .call 64 [.rel 18446744073708158615] 5) :=
  Dec.shift (j := 52) (k := 0) (pcall1_0 feat) wc_52 (Nat.zero_le _)
theorem tgt_52 : cpc_at.add (52 + 5) + BitVec.ofNat 64 18446744073708158615 = Nst.nst_at.add 0 := by decide

/-- The `call` to `UString::UString ()`. -/
def pcall2 : List Byte := [0xe8, 0x0e, 0xcf, 0xea, 0xff]
theorem pcall2_0 : ∀ feat, Dec feat pcall2 0 (FV7z.mk .call 64 [.rel 18446744073708162830] 5) := by dec_rfl
theorem wc_61 : pcall2 <+: cpc.drop 61 := by decide +kernel
theorem call_61 (feat : Features) : Dec feat cpc 61 (FV7z.mk .call 64 [.rel 18446744073708162830] 5) :=
  Dec.shift (j := 61) (k := 0) (pcall2_0 feat) wc_61 (Nat.zero_le _)
theorem tgt_61 : cpc_at.add (61 + 5) + BitVec.ofNat 64 18446744073708162830 = Uct.uct_at.add 0 := by decide

/-- The `ret`. -/
def pret : List Byte := [0xc3]
theorem pret_0 : ∀ feat, Dec feat pret 0 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem w_76 : pret <+: cpc.drop 76 := by decide +kernel
theorem ret_76 (feat : Features) : Dec feat cpc 76 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 76) (k := 0) (pret_0 feat) w_76 (Nat.zero_le _)

/-- The stores' addresses `rdi + 32 - 32`, `- 24`, `- 16`, `- 8`. -/
theorem ea0 (x : Addr) : x + 32#64 + 18446744073709551584#64 = x := by bv_omega
theorem ea8 (x : Addr) : x + 32#64 + 18446744073709551592#64 = x + 8#64 := by bv_omega
theorem ea16 (x : Addr) : x + 32#64 + 18446744073709551600#64 = x + 16#64 := by bv_omega
theorem ea24 (x : Addr) : x + 32#64 + 18446744073709551608#64 = x + 24#64 := by bv_omega

theorem a5s (S : Addr) : S - 8 - 8 - 8 - 8 - 8#64 + 8#64 = S - 8 - 8 - 8 - 8 := BitVec.sub_add_cancel _ _
theorem a4s (S : Addr) : S - 8 - 8 - 8 - 8 + 8 = S - 8 - 8 - 8 := BitVec.sub_add_cancel _ _
theorem a3s (S : Addr) : S - 8 - 8 - 8 + 8 = S - 8 - 8 := BitVec.sub_add_cancel _ _
theorem a2s (S : Addr) : S - 8 - 8 + 8 = S - 8 := BitVec.sub_add_cancel _ _
theorem a1s (S : Addr) : S - 8 + 8 = S := BitVec.sub_add_cancel _ _

/-- The registers at the first `call`: `rbx` = `this`, `rdi` = `this + 32`, four pushes and 8 more. -/
abbrev gA (g : Gprs) : Gprs :=
  { g with
      rbx := g.rdi,
      rdi := g.rdi + 32#64,
      rsp := g.rsp - 8 - 8 - 8 - 8 - 8#64 }

/-- The bytes at the first `call`: the four pushes, `_switches` 0 and `StopSwitchIndex` -1. -/
abbrev VA (V : Addr → Byte) (g : Gprs) : Addr → Byte :=
  Vst (Vst (Vst (Vst (Vst (Vst (Vst (Vst V (g.rsp - 8) (toBytesLE g.r13 8)) (g.rsp - 8 - 8) (toBytesLE g.r12 8))
    (g.rsp - 8 - 8 - 8) (toBytesLE g.rbp 8)) (g.rsp - 8 - 8 - 8 - 8) (toBytesLE g.rbx 8))
    g.rdi (toBytesLE 0#64 8)) (g.rdi + 8#64) (toBytesLE 0#64 8)) (g.rdi + 16#64) (toBytesLE 0#64 8))
    (g.rdi + 24#64) (toBytesLE 4294967295#32 4)

variable {F : Footprint} {Wl : List Rgn}

/-- The four pushes, `mov rbx, rdi; lea rdi, [rdi + 32]; sub rsp, 8` and the four stores, to the `call` at 52. -/
theorem vc_0 {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (h1 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8) i)) (h2 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8) i))
    (h3 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8 - 8) i))
    (h4 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8 - 8 - 8) i))
    (fw0 : ∀ i < 8, Foot Wl (Addr.add g.rdi i)) (fw8 : ∀ i < 8, Foot Wl (Addr.add (g.rdi + 8#64) i))
    (fw16 : ∀ i < 8, Foot Wl (Addr.add (g.rdi + 16#64) i)) (fw24 : ∀ i < 4, Foot Wl (Addr.add (g.rdi + 24#64) i)) :
    W_0 F Wl (fun j' g' _ V' => j' = 52 ∧ g' = gA g ∧ V' = VA V g) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h1 h2 h3 h4 fw0 fw8 fw16 fw24 ⊢
  wpx [W_0, o0, gA, VA, ea0, ea8, ea16, ea24]
  all_goals repeat'
    first
    | exact rfl
    | assumption
    | exact trivial
    | apply And.intro
    | intro _

/-- Back from the first callee: `lea rdi, [rbx + 48]`, to the `call` at 61. -/
theorem vc_57 {g : Gprs} {f : Rflags} {V : Addr → Byte} :
    W_57 F Wl (fun j' g' _ V' => j' = 61 ∧ g' = { g with rdi := g.rbx + 48#64 } ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  try dsimp only
  wpx [W_57, o1]
  all_goals repeat'
    first
    | exact rfl
    | exact trivial
    | apply And.intro
    | intro _

/-- Back from the second callee: `add rsp, 8` and the four pops, to the `ret` at 76. -/
theorem vc_66 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (p0 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8#64) i))
    (p1 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8#64 + 8) i))
    (p2 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8#64 + 8 + 8) i))
    (p3 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8#64 + 8 + 8 + 8) i))
    (h : ∀ fl, Q 76
      { g with
          rbx := rdq(V, g.rsp + 8#64),
          rbp := rdq(V, g.rsp + 8#64 + 8),
          r12 := rdq(V, g.rsp + 8#64 + 8 + 8),
          r13 := rdq(V, g.rsp + 8#64 + 8 + 8 + 8),
          rsp := g.rsp + 8#64 + 8 + 8 + 8 + 8 } fl V) :
    W_66 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at p0 p1 p2 p3 h ⊢
  wpx [W_66, o2]
  all_goals repeat' (first | exact h _ | assumption | exact trivial | apply And.intro | intro _)

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {X : State} {t : Nat} {V : Addr → Byte}

/-- `CParser::CParser ()` (`this` = `rdi`) from its entry. At the first callee's entry the registers are `gA` with
the return address `cpc_at + 57` pushed and the bytes `VA` (`kf1`); back at `cpc_at + 57` with `rsp` as at the
`call` and `P1`, the run goes to the second callee's entry with `rdi` = `rbx + 48` and the return address
`cpc_at + 66` pushed (`kf2`); back at `cpc_at + 66` with `rsp` as at the `call`, the saved registers and the return
address as they were and `P2`, the run reaches the return address with `rbx`, `rbp`, `r12`, `r13` restored and
`rsp` 8 up (`kr`). -/
theorem cpc_ok {P1 P2 : State → (Addr → Byte) → Prop} (c : Seg prof F Wl L s₀ o) (hin : CodeIn L cpc_at cpc)
    (hinN : CodeIn L Nst.nst_at Nst.nst) (hinU : CodeIn L Uct.uct_at Uct.uct)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = cpc_at)
    (h1 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8) i))
    (h2 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8 - 8) i))
    (h3 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8 - 8 - 8) i))
    (h4 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8 - 8 - 8 - 8) i))
    (h6 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8 - 8 - 8 - 8 - 8#64 - 8) i))
    (hl : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsp i))
    (fw0 : ∀ i < 8, Foot Wl (Addr.add X.cpu.gpr.rdi i))
    (fw8 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rdi + 8#64) i))
    (fw16 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rdi + 16#64) i))
    (fw24 : ∀ i < 4, Foot Wl (Addr.add (X.cpu.gpr.rdi + 24#64) i))
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (kf1 : ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y →
      Agree F Y.proc.mm.mem (Vst (VA V X.cpu.gpr) (X.cpu.gpr.rsp - 8 - 8 - 8 - 8 - 8#64 - 8)
        (toBytesLE (cpc_at.add 57) 8)) →
      Y.cpu.rip = Nst.nst_at.add 0 → Y.cpu.gpr = (gA X.cpu.gpr).set 4 (X.cpu.gpr.rsp - 8 - 8 - 8 - 8 - 8#64 - 8) →
      (∀ (Z : State) (V' : Addr → Byte) (t'' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V' →
        Z.cpu.rip = cpc_at.add 57 → Z.cpu.gpr.rsp = X.cpu.gpr.rsp - 8 - 8 - 8 - 8 - 8#64 →
        P1 Z V' → GoG prof L o gev gP gE Z t'') →
      GoG prof L o gev gP gE Y t')
    (kf2 : ∀ (Z : State) (V' : Addr → Byte), P1 Z V' → ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y →
      Agree F Y.proc.mm.mem (Vst V' (X.cpu.gpr.rsp - 8 - 8 - 8 - 8 - 8#64 - 8) (toBytesLE (cpc_at.add 66) 8)) →
      Y.cpu.rip = Uct.uct_at.add 0 →
      Y.cpu.gpr = { Z.cpu.gpr with rdi := Z.cpu.gpr.rbx + 48#64 }.set 4 (X.cpu.gpr.rsp - 8 - 8 - 8 - 8 - 8#64 - 8) →
      (∀ (Z₂ : State) (V'' : Addr → Byte) (t'' : Nat), KeptW Wl s₀ Z₂ → Agree F Z₂.proc.mm.mem V'' →
        Z₂.cpu.rip = cpc_at.add 66 → Z₂.cpu.gpr.rsp = X.cpu.gpr.rsp - 8 - 8 - 8 - 8 - 8#64 →
        rdq(V'', X.cpu.gpr.rsp - 8 - 8 - 8 - 8) = X.cpu.gpr.rbx →
        rdq(V'', X.cpu.gpr.rsp - 8 - 8 - 8) = X.cpu.gpr.rbp →
        rdq(V'', X.cpu.gpr.rsp - 8 - 8) = X.cpu.gpr.r12 → rdq(V'', X.cpu.gpr.rsp - 8) = X.cpu.gpr.r13 →
        rdq(V'', X.cpu.gpr.rsp) = e₂.add j₂ → P2 Z₂ V'' → GoG prof L o gev gP gE Z₂ t'') →
      GoG prof L o gev gP gE Y t')
    (kr : ∀ (Z₂ : State) (V'' : Addr → Byte) (Z' : State) (t' : Nat), P2 Z₂ V'' → KeptW Wl s₀ Z' →
      Agree F Z'.proc.mm.mem V'' → Z'.cpu.rip = e₂.add j₂ →
      Z'.cpu.gpr = { Z₂.cpu.gpr with rbx := X.cpu.gpr.rbx, rbp := X.cpu.gpr.rbp, r12 := X.cpu.gpr.r12,
        r13 := X.cpu.gpr.r13, rsp := X.cpu.gpr.rsp + 8 } →
      GoG prof L o gev gP gE Z' t') :
    GoG prof L o gev gP gE X t := by
  have hrip' : X.cpu.rip = cpc_at.add 0 := by rw [addr_add_zero]; exact hrip
  -- to the first `call`
  refine (c_0 prof).run c hin (fun j' g' _ V' => j' = 52 ∧ g' = gA X.cpu.gpr ∧ V' = VA V X.cpu.gpr) hK hA hrip'
    (vc_0 h1 h2 h3 h4 fw0 fw8 fw16 fw24) ?_
  rintro j' g fl V₁ ⟨rfl, rfl, hV₁⟩ Y t₁ hKY hAY hrY hgY -
  subst V₁
  have hsY : Y.cpu.gpr.rsp = X.cpu.gpr.rsp - 8 - 8 - 8 - 8 - 8#64 := by rw [hgY]
  refine c.s_call_x hKY hAY hin (lt_len (by decide)) hrY (call_52 _) hinN (tgt := 0) (Nst.lt_len (by decide))
    tgt_52 (by rw [hsY]; exact h6) ?_
  rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
  rw [hsY] at hA₂
  refine kf1 Y₂ t₂ hK₂ hA₂ hr₂ (by rw [hg₂, hsY, hgY]) ?_
  -- back from the first callee, to the second `call`
  intro Z V' t'' hKZ hAZ hrZ hzs hP1
  refine (c_57 prof).run c hin (fun j' g' _ V'' => j' = 61 ∧ g' = { Z.cpu.gpr with rdi := Z.cpu.gpr.rbx + 48#64 } ∧
    V'' = V') hKZ hAZ hrZ vc_57 ?_
  rintro j' g fl V₂ ⟨rfl, rfl, hV₂⟩ U t₃ hKU hAU hrU hgU -
  subst V₂
  have hsU : U.cpu.gpr.rsp = X.cpu.gpr.rsp - 8 - 8 - 8 - 8 - 8#64 := by rw [hgU]; exact hzs
  refine c.s_call_x hKU hAU hin (lt_len (by decide)) hrU (call_61 _) hinU (tgt := 0) (Uct.lt_len (by decide))
    tgt_61 (by rw [hsU]; exact h6) ?_
  rintro Y₃ t₄ hK₃ hA₃ ⟨hr₃, hg₃⟩
  rw [hsU] at hA₃
  refine kf2 Z V' hP1 Y₃ t₄ hK₃ hA₃ hr₃ (by rw [hg₃, hsU, hgU]) ?_
  -- back from the second callee, to the `ret`
  intro Z₂ V'' t₅ hKZ₂ hAZ₂ hrZ₂ hzs₂ hb4 hb3 hb2 hb1 hra hP2
  have q4 : ∀ i < 8, Foot F.data (Addr.add (Z₂.cpu.gpr.rsp + 8#64) i) := by
    rw [hzs₂, a5s]; exact fun i hi => c.hws _ (h4 i hi)
  have q3 : ∀ i < 8, Foot F.data (Addr.add (Z₂.cpu.gpr.rsp + 8#64 + 8) i) := by
    rw [hzs₂, a5s, a4s]; exact fun i hi => c.hws _ (h3 i hi)
  have q2 : ∀ i < 8, Foot F.data (Addr.add (Z₂.cpu.gpr.rsp + 8#64 + 8 + 8) i) := by
    rw [hzs₂, a5s, a4s, a3s]; exact fun i hi => c.hws _ (h2 i hi)
  have q1 : ∀ i < 8, Foot F.data (Addr.add (Z₂.cpu.gpr.rsp + 8#64 + 8 + 8 + 8) i) := by
    rw [hzs₂, a5s, a4s, a3s, a2s]; exact fun i hi => c.hws _ (h1 i hi)
  refine (c_66 prof).run c hin (fun j' g' _ V₃ => j' = 76 ∧
      g' = { Z₂.cpu.gpr with rbx := X.cpu.gpr.rbx, rbp := X.cpu.gpr.rbp, r12 := X.cpu.gpr.r12,
        r13 := X.cpu.gpr.r13, rsp := X.cpu.gpr.rsp } ∧ V₃ = V'') hKZ₂ hAZ₂ hrZ₂
    (vc_66 q4 q3 q2 q1 fun _ => ⟨rfl, by rw [hzs₂, a5s, a4s, a3s, a2s, a1s, hb4, hb3, hb2, hb1], rfl⟩) ?_
  rintro j' g fl V₃ ⟨rfl, rfl, hV₃⟩ U₂ t₆ hKU₂ hAU₂ hrU₂ hgU₂ -
  subst V₃
  have hsU₂ : U₂.cpu.gpr.rsp = X.cpu.gpr.rsp := by rw [hgU₂]
  refine c.s_ret hKU₂ hAU₂ hin (lt_len (by decide)) hrU₂ (ret_76 _) (by rw [hsU₂]; exact hl) hin₂ h₂
    (by rw [hsU₂]; exact hra) ?_
  rintro Z' t₇ hKZ' hAZ' ⟨hrZ', hgZ'⟩
  refine kr Z₂ V'' Z' t₇ hP2 hKZ' hAZ' hrZ' ?_
  rw [hgZ', hgU₂]
  try rfl

end FV7z.Cpc
