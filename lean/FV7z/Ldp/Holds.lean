import FV7z.Ldp.Cuts
import FV7z.Api.Holds
import FV7z.Mys.Lem
/-!
# `NCompress::NLzma::CDecoder::SetDecoderProperties2 (prop, size)` (PLAN.md §M, M1)

7-Zip 26.06's `NCompress::NLzma::CDecoder::SetDecoderProperties2` at `0x57fd10` in `7zzs`
(`CPP/7zip/Compress/LzmaDecoder.cpp`; `objdump -d`):
`RINOK (SResToHRESULT (LzmaDec_Allocate (&_state, prop, size, &g_AllocBig))) _propsWereSet = true;
return CreateInputBuffer ();` with `_state` at `this + 0x80`, `_propsWereSet` at `this + 0x45`. `this` = `rdi`
(kept in `rbp`), `S` the stack pointer at the entry: `push rbp` (`P1`), `rcx = &g_AllocBig` (`0x777ae0`),
`rdi = this + 0x80` (0..22); the `call` (22) of `LzmaDec_Allocate` at `0x42bf80` (a hypothesis, `kA`; back at 27
with `rsp` = `S - 8`, the callee-saved registers kept and `I` of the bytes). At 27, `r` = `eax`: `r > 5` (`ja`):
`eax = E_FAIL`, `pop rbp`, the `ret` (62); else the table of `SResToHRESULT` at `0x6e68c0` (`[0x6e68c0 + 4 r]`),
nonzero: `pop rbp`, the `ret` (49); zero: `_propsWereSet = 1` (64), the `call` (71) of `CreateInputBuffer` at
`0x57fcc0` (a hypothesis, `kB`; back at 76 likewise), `pop rbp`, the `ret` (77). The landing pad (from 0x4e) is not
covered; the result in `eax` is not stated.

The bytes at 27 and at 76 are the caller's invariant `I` (held by the bytes after the push, `hI0`; given back by the
callees); they give the saved `rbp` and the return address (`hIs`).

- `call_22`, `call_71`, `ret_49`, `ret_62`, `ret_77`: the instructions outside the blocks.
- `bj`, `c7`: the `ja` after `cmp eax, 5`.
- `P1`, `Pp`, `KC`: the bytes after the push, `pop rbp` from them, a callee.
- `vc_0`, `vc_27e`, `vc_27n`, `vc_27z`, `vc_76`: the pieces; `ldp_ok`: the function.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn FV7z.Mys
open FV7z.Api (KS)
namespace FV7z.Ldp
set_option linter.unusedVariables false

/-! ## The instructions outside the blocks -/

/-- The `call` of `LzmaDec_Allocate` (22). -/
def pc22 : List Byte := [0xe8, 0x55, 0xc2, 0xea, 0xff]
theorem pc22_0 : ∀ feat, Dec feat pc22 0 (FV7z.mk .call 64 [.rel 18446744073708159573] 5) := by dec_rfl
theorem wc_22 : pc22 <+: ldp.drop 22 := by decide +kernel
theorem call_22 (feat : Features) : Dec feat ldp 22 (FV7z.mk .call 64 [.rel 18446744073708159573] 5) :=
  Dec.shift (j := 22) (k := 0) (pc22_0 feat) wc_22 (Nat.zero_le _)
theorem tgt_22 : ldp_at.add (22 + 5) + BitVec.ofNat 64 18446744073708159573 = 0x42bf80#64 := by decide

/-- The `call` of `CreateInputBuffer` (71). -/
def pc71 : List Byte := [0xe8, 0x64, 0xff, 0xff, 0xff]
theorem pc71_0 : ∀ feat, Dec feat pc71 0 (FV7z.mk .call 64 [.rel 18446744073709551460] 5) := by dec_rfl
theorem wc_71 : pc71 <+: ldp.drop 71 := by decide +kernel
theorem call_71 (feat : Features) : Dec feat ldp 71 (FV7z.mk .call 64 [.rel 18446744073709551460] 5) :=
  Dec.shift (j := 71) (k := 0) (pc71_0 feat) wc_71 (Nat.zero_le _)
theorem tgt_71 : ldp_at.add (71 + 5) + BitVec.ofNat 64 18446744073709551460 = 0x57fcc0#64 := by decide

/-- The `ret`s (49, 62, 77). -/
def pret : List Byte := [0xc3]
theorem pret_0 : ∀ feat, Dec feat pret 0 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem w_49 : pret <+: ldp.drop 49 := by decide +kernel
theorem ret_49 (feat : Features) : Dec feat ldp 49 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 49) (k := 0) (pret_0 feat) w_49 (Nat.zero_le _)
theorem w_62 : pret <+: ldp.drop 62 := by decide +kernel
theorem ret_62 (feat : Features) : Dec feat ldp 62 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 62) (k := 0) (pret_0 feat) w_62 (Nat.zero_le _)
theorem w_77 : pret <+: ldp.drop 77 := by decide +kernel
theorem ret_77 (feat : Features) : Dec feat ldp 77 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 77) (k := 0) (pret_0 feat) w_77 (Nat.zero_le _)

/-! ## The `ja` after `cmp eax, 5` -/

theorem bj (m : BitVec 32) : (!(decide (m.toNat < 5) || decide (m = 5#32))) = decide (5 < m.toNat) := by
  have hy : (5#32 : BitVec 32).toNat = 5 := rfl
  have e : (m = 5#32) ↔ m.toNat = 5 := by rw [BitVec.toNat_eq, hy]
  by_cases h : 5 < m.toNat
  · have h1 : ¬ m.toNat < 5 := by omega
    have h2 : ¬ m = 5#32 := fun h' => by rw [e] at h'; omega
    simp [h, h1, h2]
  · by_cases h3 : m.toNat < 5
    · simp [h, h3]
    · have h2 : m = 5#32 := e.2 (by omega)
      simp [h, h3, h2]

theorem c7 (f : Rflags) (m : BitVec 32) : (subF f m 5#32).cond 7 = decide (5 < m.toNat) := by
  rw [cond_7, subF_cf, subF_zf]; exact bj m

/-! ## The bytes and the callees -/

/-- The bytes after `push rbp`. -/
abbrev P1 (V : Addr → Byte) (g : Gprs) : Addr → Byte := Vst V (g.rsp - 8) (toBytesLE g.rbp 8)

/-- `pop rbp` from the bytes `V` and the registers `g` to the registers `g'`. -/
abbrev Pp (V : Addr → Byte) (g g' : Gprs) : Prop :=
  g'.rsp = g.rsp + 8 ∧ g'.rbp = rdq(V, g.rsp) ∧ g'.rbx = g.rbx ∧ g'.r12 = g.r12 ∧ g'.r13 = g.r13 ∧
    g'.r14 = g.r14 ∧ g'.r15 = g.r15

/-- A callee from a `call` returning at `jr` (entry `ent`, the bytes `W`, the registers `A`): at its entry, and from
its return with `rsp` = `S - 8`, the callee-saved registers as at its entry, `B` and the invariant `J`, the run goes
on to the goal. -/
def KC (prof : Profile) (F : Footprint) (Wl : List Rgn) (L : List (Addr × List Byte)) (s₀ : State) (o : Oracle)
    (gev : List Event) (gP : State → Nat → List Event → Prop) (gE : Outcome → List Event → Prop)
    (S : Addr) (J : (Addr → Byte) → Prop) (jr : Nat) (ent : Addr) (W : Addr → Byte) (A B : Gprs → Prop) :
    Prop :=
  ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y →
    Agree F Y.proc.mm.mem (Vst W (S - 8 - 8) (toBytesLE (ldp_at.add jr) 8)) →
    Y.cpu.rip = ent → Y.cpu.gpr.rsp = S - 8 - 8 → A Y.cpu.gpr →
    (∀ (Z : State) (W' : Addr → Byte) (t'' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem W' →
      Z.cpu.rip = ldp_at.add jr → Z.cpu.gpr.rsp = S - 8 → KS Y.cpu.gpr Z.cpu.gpr → B Z.cpu.gpr → J W' →
      GoG prof L o gev gP gE Z t'') →
    GoG prof L o gev gP gE Y t'

/-! ## The pieces -/

variable {F : Footprint} {Wl : List Rgn}

/-- `push rbp; mov rcx, 0x777ae0; mov rbp, rdi; lea rdi, [rdi + 0x80]`: to the `call` at 22. -/
theorem vc_0 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (hs1 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8) i))
    (h : ∀ g', g'.rsp = g.rsp - 8 → g'.rbp = g.rdi → g'.rdi = g.rdi + 128#64 → g'.rcx = 7830240#64 →
      g'.rsi = g.rsi → g'.rdx = g.rdx → g'.rbx = g.rbx → g'.r12 = g.r12 → g'.r13 = g.r13 → g'.r14 = g.r14 →
      g'.r15 = g.r15 → ∀ fl, Q 22 g' fl (P1 V g)) :
    W_0 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [P1] at hs1 h ⊢
  wpx [W_0, o0]
  all_goals repeat' (first
    | refine h _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ _
    | with_reducible exact hs1
    | with_reducible rfl
    | exact rfl
    | apply And.intro
    | intro _)

/-- At 27, `eax > 5`: `mov eax, E_FAIL; pop rbp`, to the `ret` at 62. -/
theorem vc_27e {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (hx : ¬ (BitVec.setWidth 32 g.rax).toNat ≤ 5)
    (fp : ∀ i < 8, Foot F.data (Addr.add g.rsp i))
    (h : ∀ g', Pp V g g' → ∀ fl, Q 62 g' fl V) :
    W_27 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [Pp] at hx fp h ⊢
  have d : decide (5 < (BitVec.setWidth 32 rax).toNat) = true := decide_eq_true (by omega)
  wpx [W_27, o1, W_56, o4, c7, bj, d, Bool.false_eq_true, Bool.true_eq_false, false_implies, true_implies,
    implies_true, eq_self_iff_true, and_true]
  all_goals repeat' (first
    | refine h _ ?_ _
    | with_reducible exact fp
    | with_reducible rfl
    | exact rfl
    | apply And.intro
    | intro _)

/-- At 27, `eax ≤ 5`, the table's entry nonzero: `pop rbp`, to the `ret` at 49. -/
theorem vc_27n {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (hx : (BitVec.setWidth 32 g.rax).toNat ≤ 5)
    (ft : ∀ i < 4, Foot F.data (Addr.add (7235776#64 + BitVec.setWidth 64 (BitVec.setWidth 32 g.rax) * 4#64) i))
    (hz : (rdd(V, 7235776#64 + BitVec.setWidth 64 (BitVec.setWidth 32 g.rax) * 4#64) == 0) = false)
    (fp : ∀ i < 8, Foot F.data (Addr.add g.rsp i))
    (h : ∀ g', Pp V g g' → ∀ fl, Q 49 g' fl V) :
    W_27 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [Pp] at hx ft hz fp h ⊢
  have d : decide (5 < (BitVec.setWidth 32 rax).toNat) = false := decide_eq_false (by omega)
  wpx [W_27, o1, W_32, o2, W_48, o3, c7, bj, d, hz, BitVec.and_self, Bool.not_true, Bool.not_false,
    Bool.false_eq_true, Bool.true_eq_false, false_implies, true_implies, implies_true, eq_self_iff_true, and_true]
  all_goals repeat' (first
    | refine h _ ?_ _
    | with_reducible exact ft
    | with_reducible exact fp
    | with_reducible rfl
    | exact rfl
    | apply And.intro
    | intro _)

/-- At 27, `eax ≤ 5`, the table's entry zero: `_propsWereSet = 1; mov rdi, rbp`, to the `call` at 71. -/
theorem vc_27z {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (hx : (BitVec.setWidth 32 g.rax).toNat ≤ 5)
    (ft : ∀ i < 4, Foot F.data (Addr.add (7235776#64 + BitVec.setWidth 64 (BitVec.setWidth 32 g.rax) * 4#64) i))
    (hz : (rdd(V, 7235776#64 + BitVec.setWidth 64 (BitVec.setWidth 32 g.rax) * 4#64) == 0) = true)
    (hw : ∀ i < 1, Foot Wl (Addr.add (g.rbp + 69#64) i))
    (h : ∀ g', g'.rsp = g.rsp → g'.rdi = g.rbp → g'.rbp = g.rbp → g'.rbx = g.rbx → g'.r12 = g.r12 →
      g'.r13 = g.r13 → g'.r14 = g.r14 → g'.r15 = g.r15 →
      ∀ fl, Q 71 g' fl (Vst V (g.rbp + 69#64) (toBytesLE 1#8 1))) :
    W_27 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hx ft hz hw h ⊢
  have d : decide (5 < (BitVec.setWidth 32 rax).toNat) = false := decide_eq_false (by omega)
  wpx [W_27, o1, W_32, o2, W_64, o5, c7, bj, d, hz, BitVec.and_self, Bool.not_true, Bool.not_false,
    Bool.false_eq_true, Bool.true_eq_false, false_implies, true_implies, implies_true, eq_self_iff_true, and_true]
  all_goals repeat' (first
    | refine h _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ _
    | with_reducible exact ft
    | with_reducible exact hw
    | with_reducible rfl
    | exact rfl
    | apply And.intro
    | intro _)

/-- At 76, back from `CreateInputBuffer`: `pop rbp`, to the `ret` at 77. -/
theorem vc_76 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (fp : ∀ i < 8, Foot F.data (Addr.add g.rsp i))
    (h : ∀ g', Pp V g g' → ∀ fl, Q 77 g' fl V) :
    W_76 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [Pp] at fp h ⊢
  wpx [W_76, o3]
  all_goals repeat' (first
    | refine h _ ?_ _
    | with_reducible exact fp
    | with_reducible rfl
    | exact rfl
    | apply And.intro
    | intro _)

/-! ## The function -/

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {X : State} {t : Nat} {V : Addr → Byte}

/-- `SetDecoderProperties2` from its entry (`X`'s registers, `S` = their `rsp`, `this` = their `rdi`, `prop`, `size`
= their `rsi`, `edx`): the push's slot, the `call`s' return address slot and `_propsWereSet` in what the run may
store into; the return address and the table's six entries readable. `LzmaDec_Allocate` (`kA`, with `rdi` =
`&_state`, `rsi`, `rdx` as at the entry, `rcx` = `&g_AllocBig`) from the bytes after the push (`hI0`) to bytes of
`I`; `CreateInputBuffer` (`kB`, `rdi` = `this`) from bytes of `I` with `_propsWereSet` set to bytes of `I`; bytes of
`I` give the saved `rbp` and the return address (`hIs`). At the return address (`kr`): the bytes of `I`, the
registers a call keeps (`Str.Back`). -/
theorem ldp_ok {I : (Addr → Byte) → Prop} {e₂ : Addr} {code₂ : List Byte} {j₂ : Nat}
    (c : Seg prof F Wl L s₀ o) (hin : CodeIn L ldp_at ldp) (hin₂ : CodeIn L e₂ code₂)
    (h₂ : j₂ < code₂.length)
    {cA : List Byte} (hinA : CodeIn L 0x42bf80#64 cA) (hcA : 0 < cA.length)
    {cB : List Byte} (hinB : CodeIn L 0x57fcc0#64 cB) (hcB : 0 < cB.length)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = ldp_at)
    (hs1 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8) i))
    (hr8 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8 - 8) i))
    (hl : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsp i))
    (hw : ∀ i < 1, Foot Wl (Addr.add (X.cpu.gpr.rdi + 69#64) i))
    (ht : ∀ x : BitVec 32, x.toNat ≤ 5 →
      ∀ i < 4, Foot F.data (Addr.add (7235776#64 + BitVec.setWidth 64 x * 4#64) i))
    (hI0 : I (P1 V X.cpu.gpr))
    (hIs : ∀ W, I W → rdq(W, X.cpu.gpr.rsp - 8) = X.cpu.gpr.rbp ∧ rdq(W, X.cpu.gpr.rsp) = e₂.add j₂)
    (kA : KC prof F Wl L s₀ o gev gP gE X.cpu.gpr.rsp I 27 0x42bf80#64 (P1 V X.cpu.gpr)
      (fun g => g.rdi = X.cpu.gpr.rdi + 128#64 ∧ g.rcx = 7830240#64 ∧ g.rsi = X.cpu.gpr.rsi ∧
        g.rdx = X.cpu.gpr.rdx) (fun _ => True))
    (kB : ∀ W, I W → KC prof F Wl L s₀ o gev gP gE X.cpu.gpr.rsp I 76 0x57fcc0#64
      (Vst W (X.cpu.gpr.rdi + 69#64) (toBytesLE 1#8 1)) (fun g => g.rdi = X.cpu.gpr.rdi) (fun _ => True))
    (kr : ∀ (W : Addr → Byte) (Z : State) (t' : Nat), I W → KeptW Wl s₀ Z → Agree F Z.proc.mm.mem W →
      Z.cpu.rip = e₂.add j₂ → Str.Back X.cpu.gpr Z.cpu.gpr → GoG prof L o gev gP gE Z t') :
    GoG prof L o gev gP gE X t := by
  have g1 : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rsp - 8) i) := fun i hi => c.hws _ (hs1 i hi)
  -- after a `pop rbp` from bytes of `I`: the `ret`
  have kret : ∀ (jr : Nat), jr < ldp.length → Dec prof.feat ldp jr (FV7z.mk .ret 64 [] 1) →
      ∀ (W : Addr → Byte) (U : State) (t' : Nat), I W → KeptW Wl s₀ U → Agree F U.proc.mm.mem W →
      U.cpu.rip = ldp_at.add jr → ∀ g₁ : Gprs, g₁.rsp = X.cpu.gpr.rsp - 8 → g₁.rbx = X.cpu.gpr.rbx →
      g₁.r12 = X.cpu.gpr.r12 → g₁.r13 = X.cpu.gpr.r13 → g₁.r14 = X.cpu.gpr.r14 →
      g₁.r15 = X.cpu.gpr.r15 →
      Pp W g₁ U.cpu.gpr → GoG prof L o gev gP gE U t' := by
    intro jr hj hd W U t' hIW hKU hAU hrU g₁ s1 b1 c12 c13 c14 c15 ⟨ps, pp, pb, p12, p13, p14, p15⟩
    obtain ⟨o1, o2⟩ := hIs W hIW
    have hsU : U.cpu.gpr.rsp = X.cpu.gpr.rsp := by rw [ps, s1]; exact BitVec.sub_add_cancel _ _
    have hkp : Kp X.cpu.gpr U.cpu.gpr :=
      ⟨hsU, pb.trans b1, pp.trans (by rw [s1]; exact o1), p12.trans c12, p13.trans c13, p14.trans c14,
        p15.trans c15⟩
    exact ret_back c hin hj hd hKU hAU hrU hkp hl hin₂ h₂ o2
      fun Z' t'' hK' hA' hr' hb _ => kr W Z' t'' hIW hK' hA' hr' hb
  have hr0 : X.cpu.rip = ldp_at.add 0 := by rw [addr_add_zero]; exact hrip
  refine (c_0 prof).run c hin (fun j' g' _ V' => j' = 22 ∧ V' = P1 V X.cpu.gpr ∧
      g'.rsp = X.cpu.gpr.rsp - 8 ∧ g'.rbp = X.cpu.gpr.rdi ∧ g'.rdi = X.cpu.gpr.rdi + 128#64 ∧
      g'.rcx = 7830240#64 ∧ g'.rsi = X.cpu.gpr.rsi ∧ g'.rdx = X.cpu.gpr.rdx ∧ g'.rbx = X.cpu.gpr.rbx ∧
      g'.r12 = X.cpu.gpr.r12 ∧ g'.r13 = X.cpu.gpr.r13 ∧ g'.r14 = X.cpu.gpr.r14 ∧ g'.r15 = X.cpu.gpr.r15)
    hK hA hr0
    (vc_0 (g := X.cpu.gpr) hs1 fun _ a b d e p q r s u v w _ => ⟨rfl, rfl, a, b, d, e, p, q, r, s, u, v, w⟩) ?_
  rintro j' g fl V₁ ⟨rfl, hV₁, gs, gp, gdi, gcx, gsi, gdx, gb, g12, g13, g14, g15⟩ U t₁ hKU hAU hrU hgU -
  subst V₁ hgU
  have hU : U.cpu.gpr.rsp - 8 = X.cpu.gpr.rsp - 8 - 8 := by rw [gs]
  refine c.s_call hKU hAU hin (lt_len (by decide)) hrU (call_22 _) hinA hcA tgt_22 (by rw [hU]; exact hr8) ?_
  rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
  rw [hU] at hA₂
  refine kA Y₂ t₂ hK₂ hA₂ hr₂ (by rw [hg₂]; exact hU) (by rw [hg₂]; exact ⟨gdi, gcx, gsi, gdx⟩) ?_
  intro Z W' t₃ hKZ hAZ hrZ hsZ hkZ _ hIZ
  rw [hg₂] at hkZ
  have zb : Z.cpu.gpr.rbx = X.cpu.gpr.rbx := hkZ.1.trans gb
  have zp : Z.cpu.gpr.rbp = X.cpu.gpr.rdi := hkZ.2.1.trans gp
  have z12 : Z.cpu.gpr.r12 = X.cpu.gpr.r12 := hkZ.2.2.1.trans g12
  have z13 : Z.cpu.gpr.r13 = X.cpu.gpr.r13 := hkZ.2.2.2.1.trans g13
  have z14 : Z.cpu.gpr.r14 = X.cpu.gpr.r14 := hkZ.2.2.2.2.1.trans g14
  have z15 : Z.cpu.gpr.r15 = X.cpu.gpr.r15 := hkZ.2.2.2.2.2.trans g15
  by_cases hb : (BitVec.setWidth 32 Z.cpu.gpr.rax).toNat ≤ 5
  · by_cases hz :
        (rdd(W', 7235776#64 + BitVec.setWidth 64 (BitVec.setWidth 32 Z.cpu.gpr.rax) * 4#64) == 0) = true
    · -- `S_OK`: `_propsWereSet`, the `call` of `CreateInputBuffer`, back at 76, the `ret` at 77
      refine (c_27 prof).run c hin (fun j' g' _ V' => j' = 71 ∧
          V' = Vst W' (Z.cpu.gpr.rbp + 69#64) (toBytesLE 1#8 1) ∧ g'.rsp = Z.cpu.gpr.rsp ∧
          g'.rdi = Z.cpu.gpr.rbp ∧ g'.rbp = Z.cpu.gpr.rbp ∧ g'.rbx = Z.cpu.gpr.rbx ∧ g'.r12 = Z.cpu.gpr.r12 ∧
          g'.r13 = Z.cpu.gpr.r13 ∧ g'.r14 = Z.cpu.gpr.r14 ∧ g'.r15 = Z.cpu.gpr.r15) hKZ hAZ hrZ
        (vc_27z (g := Z.cpu.gpr) hb (ht _ hb) hz (by rw [zp]; exact hw)
          fun _ a b d e p q r s _ => ⟨rfl, rfl, a, b, d, e, p, q, r, s⟩) ?_
      rintro j' g fl V₁ ⟨rfl, hV, ss, sdi, sp, sb, s12, s13, s14, s15⟩ U₂ t₄ hKU₂ hAU₂ hrU₂ hgU₂ -
      rw [hV] at hAU₂
      rw [← hgU₂] at ss sdi sp sb s12 s13 s14 s15
      have hU₂ : U₂.cpu.gpr.rsp - 8 = X.cpu.gpr.rsp - 8 - 8 := by rw [ss, hsZ]
      refine c.s_call hKU₂ hAU₂ hin (lt_len (by decide)) hrU₂ (call_71 _) hinB hcB tgt_71
        (by rw [hU₂]; exact hr8) ?_
      rintro Y₃ t₅ hK₃ hA₃ ⟨hr₃, hg₃⟩
      rw [hU₂, zp] at hA₃
      refine kB W' hIZ Y₃ t₅ hK₃ hA₃ hr₃ (by rw [hg₃]; exact hU₂) (by rw [hg₃]; exact sdi.trans zp) ?_
      intro Z₂ W₂ t₆ hKZ₂ hAZ₂ hrZ₂ hsZ₂ hkZ₂ _ hIZ₂
      rw [hg₃] at hkZ₂
      refine (c_76 prof).run c hin (fun j' g' _ V' => j' = 77 ∧ V' = W₂ ∧ Pp W₂ Z₂.cpu.gpr g')
        hKZ₂ hAZ₂ hrZ₂
        (vc_76 (g := Z₂.cpu.gpr) (by rw [hsZ₂]; exact g1) fun _ a _ => ⟨rfl, rfl, a⟩) ?_
      rintro j' g fl V₁ ⟨rfl, hV₂, hP⟩ U₃ t₇ hKU₃ hAU₃ hrU₃ hgU₃ -
      rw [hV₂] at hAU₃
      rw [← hgU₃] at hP
      exact kret 77 (lt_len (by decide)) (ret_77 _) W₂ U₃ t₇ hIZ₂ hKU₃ hAU₃ hrU₃ Z₂.cpu.gpr hsZ₂
        (hkZ₂.1.trans (sb.trans zb)) (hkZ₂.2.2.1.trans (s12.trans z12)) (hkZ₂.2.2.2.1.trans (s13.trans z13))
        (hkZ₂.2.2.2.2.1.trans (s14.trans z14)) (hkZ₂.2.2.2.2.2.trans (s15.trans z15)) hP
    · -- an error from the table: the `ret` at 49
      refine (c_27 prof).run c hin (fun j' g' _ V' => j' = 49 ∧ V' = W' ∧ Pp W' Z.cpu.gpr g') hKZ hAZ hrZ
        (vc_27n (g := Z.cpu.gpr) hb (ht _ hb) (Bool.eq_false_of_ne_true hz) (by rw [hsZ]; exact g1)
          fun _ a _ => ⟨rfl, rfl, a⟩) ?_
      rintro j' g fl V₁ ⟨rfl, hV, hP⟩ U₂ t₄ hKU₂ hAU₂ hrU₂ hgU₂ -
      rw [hV] at hAU₂
      rw [← hgU₂] at hP
      exact kret 49 (lt_len (by decide)) (ret_49 _) W' U₂ t₄ hIZ hKU₂ hAU₂ hrU₂ Z.cpu.gpr
        hsZ zb z12 z13 z14 z15 hP
  · -- `r > 5`: `E_FAIL`, the `ret` at 62
    refine (c_27 prof).run c hin (fun j' g' _ V' => j' = 62 ∧ V' = W' ∧ Pp W' Z.cpu.gpr g') hKZ hAZ hrZ
      (vc_27e (g := Z.cpu.gpr) hb (by rw [hsZ]; exact g1) fun _ a _ => ⟨rfl, rfl, a⟩) ?_
    rintro j' g fl V₁ ⟨rfl, hV, hP⟩ U₂ t₄ hKU₂ hAU₂ hrU₂ hgU₂ -
    rw [hV] at hAU₂
    rw [← hgU₂] at hP
    exact kret 62 (lt_len (by decide)) (ret_62 _) W' U₂ t₄ hIZ hKU₂ hAU₂ hrU₂ Z.cpu.gpr hsZ zb z12 z13 z14 z15
      hP

end FV7z.Ldp
