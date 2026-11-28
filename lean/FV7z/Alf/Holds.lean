import FV7z.Alf.Cuts
import FV7z.Api.Holds
import FV7z.Mys.Lem
/-!
# `UString::Add_LF ()` (PLAN.md §M, M1)

7-Zip 26.06's `UString::Add_LF ()` at `0x44dab0` in `7zzs` (`CPP/Common/MyString.cpp`; `objdump -d`):
`if (_limit == _len) Grow_1 (); _chars[_len] = '\n'; _len++; _chars[_len] = 0;` with `_chars` at `this`, `_len` at
`this + 8`, `_limit` at `this + 12`, `wchar_t` 4 bytes. `this` = `rdi` (kept in `rbx`), `S` the stack pointer at the
entry: `push rbx` (`P1`), `eax = _len`, `cmp _limit, eax` (0..14); equal: the `call` (48) of `Grow_1` at `0x44d0a0`
(a hypothesis, `kC`: at its entry with `rdi` = `this` and the return address at `S - 16`; from its return at 53 with
`rsp` = `S - 8`, the callee-saved registers kept and `I` of the bytes), `eax = _len` again (53), to 16; at 16 the
three stores (`St3`), `pop rbx`, the `ret` (42).

The bytes at 16 are the caller's invariant `I` (held by the bytes after the push, `hI0`; given back by `Grow_1`). With
the three stores they give the stores' footprint, the saved `rbx` and the return address (`Out`).

- `call_48`, `tgt_48`, `ret_42`: the instructions outside the blocks.
- `P1`, `St3`, `Out`, `KC`: the bytes after the push, the three stores, what `I` gives, the callee.
- `vc_0e`, `vc_0n`, `vc_16`, `vc_53`: the pieces; `alf_ok`: the function.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn FV7z.Mys
open FV7z.Api (KS)
namespace FV7z.Alf
set_option linter.unusedVariables false

/-! ## The instructions outside the blocks -/

/-- The `call` of `Grow_1` (48). -/
def pc48 : List Byte := [0xe8, 0xbb, 0xf5, 0xff, 0xff]
theorem pc48_0 : ∀ feat, Dec feat pc48 0 (FV7z.mk .call 64 [.rel 18446744073709548987] 5) := by dec_rfl
theorem wc_48 : pc48 <+: alf.drop 48 := by decide +kernel
theorem call_48 (feat : Features) : Dec feat alf 48 (FV7z.mk .call 64 [.rel 18446744073709548987] 5) :=
  Dec.shift (j := 48) (k := 0) (pc48_0 feat) wc_48 (Nat.zero_le _)
theorem tgt_48 : alf_at.add (48 + 5) + BitVec.ofNat 64 18446744073709548987 = 0x44d0a0#64 := by decide

/-- The `ret` (42). -/
def pret : List Byte := [0xc3]
theorem pret_0 : ∀ feat, Dec feat pret 0 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem w_42 : pret <+: alf.drop 42 := by decide +kernel
theorem ret_42 (feat : Features) : Dec feat alf 42 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 42) (k := 0) (pret_0 feat) w_42 (Nat.zero_le _)

/-! ## The bytes -/

/-- The bytes after `push rbx`. -/
abbrev P1 (V : Addr → Byte) (g : Gprs) : Addr → Byte := Vst V (g.rsp - 8) (toBytesLE g.rbx 8)

/-- The three stores at 16 on the bytes `W`, `this` = `p`, `rax` = `ax` (`_len` zero-extended): `'\n'` at
`_chars[_len]`, 0 at `_chars[_len + 1]`, `_len + 1` into `_len`. -/
abbrev St3 (W : Addr → Byte) (p ax : BitVec 64) : Addr → Byte :=
  Vst (Vst (Vst W (rdq(W, p) + ax * 4#64) (toBytesLE 10#32 4))
      (rdq(W, p) + BitVec.setWidth 64 (BitVec.setWidth 32 (ax + 1#64)) * 4#64) (toBytesLE 0#32 4))
    (p + 8#64) (toBytesLE (BitVec.setWidth 32 (ax + 1#64)) 4)

/-- What bytes `W` at 16 give (`this` = `p`, `S` the entry's `rsp`, `b` its `rbx`, `ra` the return address): the
three stores in what the run may store into; after them, the saved `rbx` and the return address. -/
abbrev Out (Wl : List Rgn) (W : Addr → Byte) (p S b ra : Addr) : Prop :=
  (∀ i < 4, Foot Wl (Addr.add (rdq(W, p) + BitVec.setWidth 64 rdd(W, p + 8#64) * 4#64) i)) ∧
  (∀ i < 4, Foot Wl (Addr.add (rdq(W, p) +
    BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.setWidth 64 rdd(W, p + 8#64) + 1#64)) * 4#64) i)) ∧
  (∀ i < 4, Foot Wl (Addr.add (p + 8#64) i)) ∧
  rdq(St3 W p (BitVec.setWidth 64 rdd(W, p + 8#64)), S - 8) = b ∧
  rdq(St3 W p (BitVec.setWidth 64 rdd(W, p + 8#64)), S) = ra

/-- The callee from the `call` at 48 (entry `ent`, the bytes `W`, the registers `A`): at its entry, and from its
return at 53 with `rsp` = `S - 8`, the callee-saved registers as at its entry, `B` and the invariant `J`, the run
goes on to the goal. -/
def KC (prof : Profile) (F : Footprint) (Wl : List Rgn) (L : List (Addr × List Byte)) (s₀ : State) (o : Oracle)
    (gev : List Event) (gP : State → Nat → List Event → Prop) (gE : Outcome → List Event → Prop)
    (S : Addr) (J : (Addr → Byte) → Prop) (ent : Addr) (W : Addr → Byte) (A B : Gprs → Prop) : Prop :=
  ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y →
    Agree F Y.proc.mm.mem (Vst W (S - 8 - 8) (toBytesLE (alf_at.add 53) 8)) →
    Y.cpu.rip = ent → Y.cpu.gpr.rsp = S - 8 - 8 → A Y.cpu.gpr →
    (∀ (Z : State) (W' : Addr → Byte) (t'' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem W' →
      Z.cpu.rip = alf_at.add 53 → Z.cpu.gpr.rsp = S - 8 → KS Y.cpu.gpr Z.cpu.gpr → B Z.cpu.gpr → J W' →
      GoG prof L o gev gP gE Z t'') →
    GoG prof L o gev gP gE Y t'

/-! ## The pieces -/

variable {F : Footprint} {Wl : List Rgn}

/-- `push rbx; mov eax, [rdi + 8]; mov rbx, rdi; cmp [rdi + 12], eax`, equal: to the `call` at 48. -/
theorem vc_0e {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (hs1 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8) i))
    (f8 : ∀ i < 4, Foot F.data (Addr.add (g.rdi + 8#64) i))
    (f12 : ∀ i < 4, Foot F.data (Addr.add (g.rdi + 12#64) i))
    (he : rdd(P1 V g, g.rdi + 12#64) = rdd(P1 V g, g.rdi + 8#64))
    (h : ∀ g', g'.rsp = g.rsp - 8 → g'.rbx = g.rdi → g'.rdi = g.rdi → g'.rbp = g.rbp → g'.r12 = g.r12 →
      g'.r13 = g.r13 → g'.r14 = g.r14 → g'.r15 = g.r15 → ∀ fl, Q 48 g' fl (P1 V g)) :
    W_0 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [P1] at hs1 f8 f12 he h ⊢
  have d := decide_eq_true he
  wpx [W_0, o0, Op.cmpmr, d, Bool.not_true, Bool.not_false, Bool.false_eq_true, Bool.true_eq_false,
    false_implies, true_implies, implies_true, eq_self_iff_true, and_true]
  all_goals repeat' (first
    | refine h _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ _
    | with_reducible exact hs1
    | with_reducible exact f8
    | with_reducible exact f12
    | with_reducible rfl
    | exact rfl
    | apply And.intro
    | intro _)

/-- As `vc_0e`, not equal: to 16 with `rax` = `_len` (zero-extended). -/
theorem vc_0n {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (hs1 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8) i))
    (f8 : ∀ i < 4, Foot F.data (Addr.add (g.rdi + 8#64) i))
    (f12 : ∀ i < 4, Foot F.data (Addr.add (g.rdi + 12#64) i))
    (he : ¬ rdd(P1 V g, g.rdi + 12#64) = rdd(P1 V g, g.rdi + 8#64))
    (h : ∀ g', g'.rsp = g.rsp - 8 → g'.rbx = g.rdi → g'.rax = BitVec.setWidth 64 rdd(P1 V g, g.rdi + 8#64) →
      g'.rbp = g.rbp → g'.r12 = g.r12 → g'.r13 = g.r13 → g'.r14 = g.r14 → g'.r15 = g.r15 →
      ∀ fl, Q 16 g' fl (P1 V g)) :
    W_0 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [P1] at hs1 f8 f12 he h ⊢
  have d := decide_eq_false he
  wpx [W_0, o0, Op.cmpmr, d, Bool.not_true, Bool.not_false, Bool.false_eq_true, Bool.true_eq_false,
    false_implies, true_implies, implies_true, eq_self_iff_true, and_true]
  all_goals repeat' (first
    | refine h _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ _
    | with_reducible exact hs1
    | with_reducible exact f8
    | with_reducible exact f12
    | with_reducible rfl
    | exact rfl
    | apply And.intro
    | intro _)

/-- At 16: `mov rcx, [rbx]; lea edx, [rax + 1]`, the two characters stored, `_len` stored, `pop rbx`, to the `ret`
at 42. -/
theorem vc_16 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (f0 : ∀ i < 8, Foot F.data (Addr.add g.rbx i))
    (w1 : ∀ i < 4, Foot Wl (Addr.add (rdq(V, g.rbx) + g.rax * 4#64) i))
    (w2 : ∀ i < 4,
      Foot Wl (Addr.add (rdq(V, g.rbx) + BitVec.setWidth 64 (BitVec.setWidth 32 (g.rax + 1#64)) * 4#64) i))
    (w3 : ∀ i < 4, Foot Wl (Addr.add (g.rbx + 8#64) i))
    (fp : ∀ i < 8, Foot F.data (Addr.add g.rsp i))
    (h : ∀ g', g'.rsp = g.rsp + 8 → g'.rbx = rdq(St3 V g.rbx g.rax, g.rsp) → g'.rbp = g.rbp → g'.r12 = g.r12 →
      g'.r13 = g.r13 → g'.r14 = g.r14 → g'.r15 = g.r15 → ∀ fl, Q 42 g' fl (St3 V g.rbx g.rax)) :
    W_16 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [St3] at f0 w1 w2 w3 fp h ⊢
  wpx [W_16, o1]
  all_goals repeat' (first
    | refine h _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ _
    | with_reducible exact f0
    | with_reducible exact w1
    | with_reducible exact w2
    | with_reducible exact w3
    | with_reducible exact fp
    | with_reducible rfl
    | exact rfl
    | apply And.intro
    | intro _)

/-- At 53, back from `Grow_1`: `mov eax, [rbx + 8]`, to 16. -/
theorem vc_53 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (f8 : ∀ i < 4, Foot F.data (Addr.add (g.rbx + 8#64) i))
    (h : ∀ fl, Q 16 { g with rax := BitVec.setWidth 64 rdd(V, g.rbx + 8#64) } fl V) :
    W_53 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at f8 h ⊢
  wpx [W_53, o2]
  all_goals repeat' (first
    | exact h _
    | with_reducible exact f8
    | with_reducible rfl
    | exact rfl
    | apply And.intro
    | intro _)

/-! ## The function -/

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {X : State} {t : Nat} {V : Addr → Byte}

/-- `UString::Add_LF ()` from its entry (`X`'s registers, `S` = their `rsp`, `this` = their `rdi`): the push's slot
and the `call`'s return address slot in what the run may store into; `_chars`, `_len`, `_limit`, the return address
readable. `Grow_1` (`kC`) from the bytes after the push (`hI0`) to bytes of `I`; bytes of `I` give the stores'
footprint, the saved `rbx` and the return address after them (`hIs`). At the return address (`kr`): the registers a
call keeps (`Str.Back`), the bytes of `I` with the three stores (`St3`, `_len` as in those bytes). -/
theorem alf_ok {I : (Addr → Byte) → Prop} {e₂ : Addr} {code₂ : List Byte} {j₂ : Nat}
    (c : Seg prof F Wl L s₀ o) (hin : CodeIn L alf_at alf) (hin₂ : CodeIn L e₂ code₂)
    (h₂ : j₂ < code₂.length)
    {cG : List Byte} (hinG : CodeIn L 0x44d0a0#64 cG) (hG : 0 < cG.length)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = alf_at)
    (hs1 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8) i))
    (hr8 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8 - 8) i))
    (hl : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsp i))
    (f0 : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rdi i))
    (f8 : ∀ i < 4, Foot F.data (Addr.add (X.cpu.gpr.rdi + 8#64) i))
    (f12 : ∀ i < 4, Foot F.data (Addr.add (X.cpu.gpr.rdi + 12#64) i))
    (hI0 : I (P1 V X.cpu.gpr))
    (hIs : ∀ W, I W → Out Wl W X.cpu.gpr.rdi X.cpu.gpr.rsp X.cpu.gpr.rbx (e₂.add j₂))
    (kC : KC prof F Wl L s₀ o gev gP gE X.cpu.gpr.rsp I 0x44d0a0#64 (P1 V X.cpu.gpr)
      (fun g => g.rdi = X.cpu.gpr.rdi) (fun _ => True))
    (kr : ∀ (W : Addr → Byte) (Z : State) (t' : Nat), I W → KeptW Wl s₀ Z →
      Agree F Z.proc.mm.mem (St3 W X.cpu.gpr.rdi (BitVec.setWidth 64 rdd(W, X.cpu.gpr.rdi + 8#64))) →
      Z.cpu.rip = e₂.add j₂ → Str.Back X.cpu.gpr Z.cpu.gpr → GoG prof L o gev gP gE Z t') :
    GoG prof L o gev gP gE X t := by
  have g1 : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rsp - 8) i) := fun i hi => c.hws _ (hs1 i hi)
  -- from 16: the stores, the pop, the `ret`
  have k16 : ∀ (W : Addr → Byte) (Z : State) (t' : Nat), I W → KeptW Wl s₀ Z → Agree F Z.proc.mm.mem W →
      Z.cpu.rip = alf_at.add 16 → Z.cpu.gpr.rsp = X.cpu.gpr.rsp - 8 → Z.cpu.gpr.rbx = X.cpu.gpr.rdi →
      Z.cpu.gpr.rax = BitVec.setWidth 64 rdd(W, X.cpu.gpr.rdi + 8#64) → Z.cpu.gpr.rbp = X.cpu.gpr.rbp →
      Z.cpu.gpr.r12 = X.cpu.gpr.r12 → Z.cpu.gpr.r13 = X.cpu.gpr.r13 → Z.cpu.gpr.r14 = X.cpu.gpr.r14 →
      Z.cpu.gpr.r15 = X.cpu.gpr.r15 → GoG prof L o gev gP gE Z t' := by
    intro W Z t' hIW hKZ hAZ hrZ zs zb za zp z12 z13 z14 z15
    obtain ⟨w1, w2, w3, o1, o2⟩ := hIs W hIW
    have e3 : St3 W Z.cpu.gpr.rbx Z.cpu.gpr.rax =
        St3 W X.cpu.gpr.rdi (BitVec.setWidth 64 rdd(W, X.cpu.gpr.rdi + 8#64)) := by rw [zb, za]
    refine (c_16 prof).run c hin (fun j' g' _ V' => j' = 42 ∧ V' = St3 W Z.cpu.gpr.rbx Z.cpu.gpr.rax ∧
        g'.rsp = Z.cpu.gpr.rsp + 8 ∧ g'.rbx = rdq(St3 W Z.cpu.gpr.rbx Z.cpu.gpr.rax, Z.cpu.gpr.rsp) ∧
        g'.rbp = Z.cpu.gpr.rbp ∧ g'.r12 = Z.cpu.gpr.r12 ∧ g'.r13 = Z.cpu.gpr.r13 ∧ g'.r14 = Z.cpu.gpr.r14 ∧
        g'.r15 = Z.cpu.gpr.r15) hKZ hAZ hrZ
      (vc_16 (g := Z.cpu.gpr) (by rw [zb]; exact f0) (by rw [zb, za]; exact w1) (by rw [zb, za]; exact w2)
        (by rw [zb]; exact w3) (by rw [zs]; exact g1) fun _ a b d e p q r _ => ⟨rfl, rfl, a, b, d, e, p, q, r⟩) ?_
    rintro j' g fl V₁ ⟨rfl, hV₁, gs, gb, gp, g12, g13, g14, g15⟩ U t₁ hKU hAU hrU hgU -
    subst V₁ hgU
    rw [e3] at hAU gb
    have hsU : U.cpu.gpr.rsp = X.cpu.gpr.rsp := by rw [gs, zs]; exact BitVec.sub_add_cancel _ _
    have hkp : Kp X.cpu.gpr U.cpu.gpr :=
      ⟨hsU, gb.trans (by rw [zs]; exact o1), gp.trans zp, g12.trans z12, g13.trans z13, g14.trans z14,
        g15.trans z15⟩
    exact ret_back c hin (lt_len (by decide)) (ret_42 _) hKU hAU hrU hkp hl hin₂ h₂ o2
      fun Z' t'' hK' hA' hr' hb _ => kr W Z' t'' hIW hK' hA' hr' hb
  have hr0 : X.cpu.rip = alf_at.add 0 := by rw [addr_add_zero]; exact hrip
  by_cases he : rdd(P1 V X.cpu.gpr, X.cpu.gpr.rdi + 12#64) = rdd(P1 V X.cpu.gpr, X.cpu.gpr.rdi + 8#64)
  · -- `_limit` = `_len`: the `call` of `Grow_1`, back at 53, to 16
    refine (c_0 prof).run c hin (fun j' g' _ V' => j' = 48 ∧ V' = P1 V X.cpu.gpr ∧
        g'.rsp = X.cpu.gpr.rsp - 8 ∧ g'.rbx = X.cpu.gpr.rdi ∧ g'.rdi = X.cpu.gpr.rdi ∧ g'.rbp = X.cpu.gpr.rbp ∧
        g'.r12 = X.cpu.gpr.r12 ∧ g'.r13 = X.cpu.gpr.r13 ∧ g'.r14 = X.cpu.gpr.r14 ∧ g'.r15 = X.cpu.gpr.r15)
      hK hA hr0
      (vc_0e (g := X.cpu.gpr) hs1 f8 f12 he fun _ a b d e p q r s _ => ⟨rfl, rfl, a, b, d, e, p, q, r, s⟩) ?_
    rintro j' g fl V₁ ⟨rfl, hV₁, gs, gb, gdi, gp, g12, g13, g14, g15⟩ U t₁ hKU hAU hrU hgU -
    subst V₁ hgU
    have hU : U.cpu.gpr.rsp - 8 = X.cpu.gpr.rsp - 8 - 8 := by rw [gs]
    refine c.s_call hKU hAU hin (lt_len (by decide)) hrU (call_48 _) hinG hG tgt_48 (by rw [hU]; exact hr8) ?_
    rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
    rw [hU] at hA₂
    refine kC Y₂ t₂ hK₂ hA₂ hr₂ (by rw [hg₂]; exact hU) (by rw [hg₂]; exact gdi) ?_
    intro Z W' t₃ hKZ hAZ hrZ hsZ hkZ _ hIZ
    rw [hg₂] at hkZ
    have zb : Z.cpu.gpr.rbx = X.cpu.gpr.rdi := hkZ.1.trans gb
    refine (c_53 prof).run c hin (fun j' g' _ V' => j' = 16 ∧ V' = W' ∧
        g' = { Z.cpu.gpr with rax := BitVec.setWidth 64 rdd(W', Z.cpu.gpr.rbx + 8#64) }) hKZ hAZ hrZ
      (vc_53 (g := Z.cpu.gpr) (by rw [zb]; exact f8) fun _ => ⟨rfl, rfl, rfl⟩) ?_
    rintro j' g fl V₁ ⟨rfl, hV, hg⟩ U₂ t₄ hKU₂ hAU₂ hrU₂ hgU₂ -
    rw [hg] at hgU₂
    refine k16 W' U₂ t₄ hIZ hKU₂ (by rw [← hV]; exact hAU₂) hrU₂ (by rw [hgU₂]; exact hsZ)
      (by rw [hgU₂]; exact zb) ?_ (by rw [hgU₂]; exact hkZ.2.1.trans gp) (by rw [hgU₂]; exact hkZ.2.2.1.trans g12)
      (by rw [hgU₂]; exact hkZ.2.2.2.1.trans g13) (by rw [hgU₂]; exact hkZ.2.2.2.2.1.trans g14)
      (by rw [hgU₂]; exact hkZ.2.2.2.2.2.trans g15)
    rw [hgU₂]
    show BitVec.setWidth 64 rdd(W', Z.cpu.gpr.rbx + 8#64) = _
    rw [zb]
  · -- `_limit` ≠ `_len`: to 16
    refine (c_0 prof).run c hin (fun j' g' _ V' => j' = 16 ∧ V' = P1 V X.cpu.gpr ∧
        g'.rsp = X.cpu.gpr.rsp - 8 ∧ g'.rbx = X.cpu.gpr.rdi ∧
        g'.rax = BitVec.setWidth 64 rdd(P1 V X.cpu.gpr, X.cpu.gpr.rdi + 8#64) ∧ g'.rbp = X.cpu.gpr.rbp ∧
        g'.r12 = X.cpu.gpr.r12 ∧ g'.r13 = X.cpu.gpr.r13 ∧ g'.r14 = X.cpu.gpr.r14 ∧ g'.r15 = X.cpu.gpr.r15)
      hK hA hr0
      (vc_0n (g := X.cpu.gpr) hs1 f8 f12 he fun _ a b d e p q r s _ => ⟨rfl, rfl, a, b, d, e, p, q, r, s⟩) ?_
    rintro j' g fl V₁ ⟨rfl, hV₁, gs, gb, ga, gp, g12, g13, g14, g15⟩ U t₁ hKU hAU hrU hgU -
    subst V₁ hgU
    exact k16 (P1 V X.cpu.gpr) U t₁ hI0 hKU hAU hrU gs gb ga gp g12 g13 g14 g15

end FV7z.Alf
