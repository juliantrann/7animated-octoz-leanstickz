import FV7z.Fkd.Cuts
import FV7z.Fnd.Holds
import FV7z.Aac.Blocks
/-!
# `FindFile_KeepDots` (PLAN.md §M, M1)

7-Zip 26.06's `FindFile_KeepDots (NFind::CFileInfo &fi, const FString &path, bool followLink)` at `0x5bff20` in
`7zzs` (`CPP/UI/Common/EnumDirItems.cpp`), `fi` in `rdi`, `path` (an `AString`: its chars at `path`, its length at
`path + 8`) in `rsi`, `followLink` in `dl`: `push r12; movzx edx, dl; push rbp; mov rbp, rdi; push rbx; mov rbx, rsi;
mov rsi, [rsi]`, the `call` (16) of `CFileInfo::Find (path, followLink)` (`Fnd.fnd_at`); `mov r12d, eax; test al, al;
je 97`. Then the dots: the length 0 to 97; `rsi` = the last char `p`, not '.' to 97; `p` the first char, or the one
before it '/', to 88 with `p`; the one before it not '.' to 97; it the first char to 88 with it (through 112), else
the one before it '/' to 88 with it (80), else to 97. At 88 `lea rdi, [rbp + 0x68]`, the `call` (92) of
`AString::operator= (const char *)` (`Aac.aac_at`) on `fi.Name`. At 97 `mov eax, r12d`, the pops and the `ret` (104).

The callees are hypotheses, as in `FV7z/Fnd/Holds.lean`: `CFileInfo::Find` a continuation at its entry (`k1`), given
the run from its return (`rsp` 24 below the entry's, `rbx` = `path`, `rbp` = `fi`, the saved registers and the return
address as they were (`Fnd.StkF`), the footprints of the reads from 21 (`KdF`) and its own post `P1`);
`AString::operator=` likewise (`k2`, `KAs`: the dots at `p`, `p - 1` or the string's start; from its return the frame,
the stack as it was and its post `P2`).

- `pe`, `KdF`: the last char of the path; the footprints of the reads from 21.
- `Fr`, `Fm`: registers kept by a piece; the frame from 21 on.
- `vc_0`, `vc_21`, `vc_88`, `vc_97`: the pieces' verification conditions.
- `tail97`: from 97 to the return address; `from88`: from 88 through `operator=`; `fkd_ok`: the function.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Fkd
set_option linter.unusedVariables false

/-! ## The instructions outside the blocks -/

/-- The `call` of `CFileInfo::Find`. -/
def pc1 : List Byte := [0xe8, 0x4b, 0x5c, 0xe9, 0xff]
theorem pc1_0 : ∀ feat, Dec feat pc1 0 (FV7z.mk .call 64 [.rel 18446744073708067915] 5) := by dec_rfl
theorem wc_16 : pc1 <+: fkd.drop 16 := by decide +kernel
theorem call_16 (feat : Features) : Dec feat fkd 16 (FV7z.mk .call 64 [.rel 18446744073708067915] 5) :=
  Dec.shift (j := 16) (k := 0) (pc1_0 feat) wc_16 (Nat.zero_le _)
theorem tgt_16 : fkd_at.add (16 + 5) + BitVec.ofNat 64 18446744073708067915 = Fnd.fnd_at.add 0 := by decide

/-- The `call` of `AString::operator= (const char *)`. -/
def pc2 : List Byte := [0xe8, 0x3f, 0xc5, 0xe8, 0xff]
theorem pc2_0 : ∀ feat, Dec feat pc2 0 (FV7z.mk .call 64 [.rel 18446744073708029247] 5) := by dec_rfl
theorem wc_92 : pc2 <+: fkd.drop 92 := by decide +kernel
theorem call_92 (feat : Features) : Dec feat fkd 92 (FV7z.mk .call 64 [.rel 18446744073708029247] 5) :=
  Dec.shift (j := 92) (k := 0) (pc2_0 feat) wc_92 (Nat.zero_le _)
theorem tgt_92 : fkd_at.add (92 + 5) + BitVec.ofNat 64 18446744073708029247 = Aac.aac_at.add 0 := by decide

/-- The `ret`. -/
def pret : List Byte := [0xc3]
theorem pret_0 : ∀ feat, Dec feat pret 0 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem w_104 : pret <+: fkd.drop 104 := by decide +kernel
theorem ret_104 (feat : Features) : Dec feat fkd 104 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 104) (k := 0) (pret_0 feat) w_104 (Nat.zero_le _)

/-! ## The path -/

/-- The last char of a string with chars at `cc`, of length `ll`. -/
abbrev pc (cc : Addr) (ll : BitVec 32) : Addr := cc + BitVec.setWidth 64 ll + 18446744073709551615#64

/-- The last char of the path (`b`: the `AString`, its chars at `b`, its length at `b + 8`). -/
abbrev pe (V : Addr → Byte) (b : Addr) : Addr := pc rdq(V, b) rdd(V, b + 8#64)

/-- The footprints of the reads from 21 (`b` = `path`): the length and the chars' address; if the length is not 0
the last char; if it is '.' and not the first, the one before; if that is '.' too and not the first, the one before
it. -/
structure KdF (F : Footprint) (V : Addr → Byte) (b : Addr) : Prop where
  n4 : ∀ i < 4, Foot F.data (Addr.add (b + 8#64) i)
  c8 : ∀ i < 8, Foot F.data (Addr.add b i)
  l1 : ¬rdd(V, b + 8#64) = 0 → ∀ i < 1, Foot F.data (Addr.add (pe V b) i)
  m1 : ¬rdd(V, b + 8#64) = 0 → V (pe V b) = 46#8 → ¬rdq(V, b) = pe V b →
    ∀ i < 1, Foot F.data (Addr.add (pe V b + 18446744073709551615#64) i)
  m2 : ¬rdd(V, b + 8#64) = 0 → V (pe V b) = 46#8 → ¬rdq(V, b) = pe V b →
    V (pe V b + 18446744073709551615#64) = 46#8 → ¬rdq(V, b) = pe V b + 18446744073709551615#64 →
    ∀ i < 1, Foot F.data (Addr.add (pe V b + 18446744073709551614#64) i)

/-! ## Registers -/

/-- What a piece keeps: `rsp`, `rbx`, `rbp`, `r13`–`r15`. -/
abbrev Fr (g g' : Gprs) : Prop :=
  g'.rsp = g.rsp ∧ g'.rbx = g.rbx ∧ g'.rbp = g.rbp ∧ g'.r13 = g.r13 ∧ g'.r14 = g.r14 ∧ g'.r15 = g.r15

/-- The frame from 21 on: the three pushes, `rbx` = `path`, `rbp` = `fi`, `r13`–`r15` as at the entry (`S`, `g0`). -/
abbrev Fm (S : Addr) (g0 g : Gprs) : Prop :=
  g.rsp = S - 8 - 8 - 8 ∧ g.rbx = g0.rsi ∧ g.rbp = g0.rdi ∧ g.r13 = g0.r13 ∧ g.r14 = g0.r14 ∧ g.r15 = g0.r15

theorem Fm.fr {S : Addr} {g0 g g' : Gprs} (h : Fm S g0 g) (h' : Fr g g') : Fm S g0 g' :=
  ⟨h'.1.trans h.1, h'.2.1.trans h.2.1, h'.2.2.1.trans h.2.2.1, h'.2.2.2.1.trans h.2.2.2.1,
    h'.2.2.2.2.1.trans h.2.2.2.2.1, h'.2.2.2.2.2.trans h.2.2.2.2.2⟩

/-! ## The pieces -/

variable {F : Footprint} {Wl : List Rgn}

/-- The pushes, `edx` = `dl`, `rbp` = `fi`, `rbx` = `path`, `rsi` = its chars, to the first `call`. -/
theorem vc_0 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (hs1 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8) i)) (hs2 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8) i))
    (hs3 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8 - 8) i)) (fp : ∀ i < 8, Foot F.data (Addr.add g.rsi i))
    (h : ∀ g', g'.rsp = g.rsp - 8 - 8 - 8 → g'.rdi = g.rdi → g'.rsi = rdq(Ffp.V1 V g, g.rsi) →
      g'.rdx = BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.setWidth 8 g.rdx)) → g'.rbx = g.rsi →
      g'.rbp = g.rdi → g'.r12 = g.r12 → g'.r13 = g.r13 → g'.r14 = g.r14 → g'.r15 = g.r15 →
      ∀ fl, Q 16 g' fl (Ffp.V1 V g)) :
    W_0 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [Ffp.V1] at hs1 hs2 hs3 fp h ⊢
  wpx [W_0, o0, Op.zxr]
  all_goals repeat' (first
    | refine h _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ _
    | with_reducible rfl
    | with_reducible exact hs1
    | with_reducible exact hs2
    | with_reducible exact hs3
    | with_reducible exact fp
    | apply And.intro
    | intro _)

/-- Back from `Find` at 21: `r12d` = `eax`; to 97, or (`al` not 0) to 88 with `rsi` the last char, the one before
it, or the first. The path's chars' address and length are named (`cc`, `ll`), so that no two addresses are compared
through the reads. -/
theorem vc_21 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} {cc : Addr} {ll : BitVec 32}
    (hc : rdq(V, g.rbx) = cc) (hl : rdd(V, g.rbx + 8#64) = ll)
    (n4 : ∀ i < 4, Foot F.data (Addr.add (g.rbx + 8#64) i)) (c8 : ∀ i < 8, Foot F.data (Addr.add g.rbx i))
    (l1 : ¬ll = 0 → ∀ i < 1, Foot F.data (Addr.add (pc cc ll) i))
    (m1 : ¬ll = 0 → V (pc cc ll) = 46#8 → ¬cc = pc cc ll →
      ∀ i < 1, Foot F.data (Addr.add (pc cc ll + 18446744073709551615#64) i))
    (m2 : ¬ll = 0 → V (pc cc ll) = 46#8 → ¬cc = pc cc ll → V (pc cc ll + 18446744073709551615#64) = 46#8 →
      ¬cc = pc cc ll + 18446744073709551615#64 →
      ∀ i < 1, Foot F.data (Addr.add (pc cc ll + 18446744073709551614#64) i))
    (h97 : ∀ g', g'.r12 = BitVec.setWidth 64 (BitVec.setWidth 32 g.rax) → Fr g g' → ∀ fl, Q 97 g' fl V)
    (h88 : ¬BitVec.setWidth 8 g.rax = 0 → ∀ g',
      (g'.rsi = pc cc ll ∨ g'.rsi = pc cc ll + 18446744073709551615#64 ∨ g'.rsi = cc) →
      g'.r12 = BitVec.setWidth 64 (BitVec.setWidth 32 g.rax) → Fr g g' → ∀ fl, Q 88 g' fl V) :
    W_21 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [pc] at hc hl n4 c8 l1 m1 m2 h97 h88 ⊢
  wpx [W_21, W_28, W_35, W_48, W_53, W_61, W_65, W_74, W_80, W_112, o1, o2, o3, o4, o5, o6, o7, o8, o9, o12,
    Op.cmpmi, Tun.rd1, Tun.sw_8_32_8, hc, hl, BitVec.and_self, beq_iff_eq, beq_eq_false_iff_ne, ne_eq,
    Bool.not_eq_true', Bool.not_eq_false', decide_eq_true_eq, decide_eq_false_iff_not]
  all_goals repeat' (first
    | refine h97 _ ?_ ?_ _
    | refine h88 (by assumption) _ ?_ ?_ ?_ _
    | with_reducible rfl
    | with_reducible exact Or.inr (Or.inr rfl)
    | with_reducible exact Or.inl rfl
    | with_reducible exact Or.inr (Or.inl rfl)
    | with_reducible exact n4
    | with_reducible exact c8
    | with_reducible exact l1 (by assumption)
    | with_reducible exact m1 (by assumption) (by assumption) (by assumption)
    | with_reducible exact m2 (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)
    | apply And.intro
    | intro _)

/-- `lea rdi, [rbp + 0x68]` to the second `call`. -/
theorem vc_88 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (h : ∀ g', g'.rdi = g.rbp + 104#64 → g'.rsi = g.rsi → g'.r12 = g.r12 → Fr g g' → ∀ fl, Q 92 g' fl V) :
    W_88 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h ⊢
  wpx [W_88, o10]
  all_goals repeat' (first
    | refine h _ ?_ ?_ ?_ ?_ _
    | with_reducible rfl
    | apply And.intro
    | intro _)

/-- `mov eax, r12d` and the pops to the `ret` (the registers there: `Fnd.g122`, the same code). -/
theorem vc_97 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (p1 : ∀ i < 8, Foot F.data (Addr.add g.rsp i)) (p2 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8) i))
    (p3 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8 + 8) i)) (h : ∀ fl, Q 104 (Fnd.g122 V g) fl V) :
    W_97 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [Fnd.g122] at p1 p2 p3 h ⊢
  wpx [W_97, o11]
  all_goals repeat' (first
    | exact h _
    | with_reducible exact p1
    | with_reducible exact p2
    | with_reducible exact p3
    | apply And.intro
    | intro _)

/-! ## The runs -/

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {X : State} {t : Nat} {V : Addr → Byte} {e₂ : Addr} {code₂ : List Byte} {j₂ : Nat}

/-- From 97 (`r12` = `r`, the bytes `W`) to the return address `e₂.add j₂`, with `eax` = `r32`. -/
theorem tail97 {W : Addr → Byte} {S : Addr} {g0 : Gprs} {r : BitVec 64} {Y : State} (c : Seg prof F Wl L s₀ o)
    (hin : CodeIn L fkd_at fkd) (hK : KeptW Wl s₀ Y) (hA : Agree F Y.proc.mm.mem W)
    (hr : Y.cpu.rip = fkd_at.add 97) (hm : Fm S g0 Y.cpu.gpr) (h12 : Y.cpu.gpr.r12 = r)
    (hst : Fnd.StkF W S g0 (e₂.add j₂)) (ft : Fnd.FtsF F S) (hin₂ : CodeIn L e₂ code₂)
    (h₂ : j₂ < code₂.length)
    (k : ∀ (Z' : State) (t' : Nat), KeptW Wl s₀ Z' → Agree F Z'.proc.mm.mem W → Z'.cpu.rip = e₂.add j₂ →
      Z'.cpu.gpr.rsp = S + 8 → Fnd.KS g0 Z'.cpu.gpr → Z'.cpu.gpr.rax = BitVec.setWidth 64 (BitVec.setWidth 32 r) →
      GoG prof L o gev gP gE Z' t') :
    GoG prof L o gev gP gE Y t := by
  obtain ⟨ms, mb, mp, m13, m14, m15⟩ := hm
  obtain ⟨s1, s2, s3, s4⟩ := hst
  obtain ⟨f3, f2, f1, f0⟩ := ft
  refine (c_97 prof).run c hin (fun j' g' _ V' => j' = 104 ∧ g' = Fnd.g122 W Y.cpu.gpr ∧ V' = W) hK hA hr
    (vc_97 (by rw [ms]; exact f3) (by rw [ms]; exact f2) (by rw [ms]; exact f1) fun _ => ⟨rfl, rfl, rfl⟩) ?_
  rintro j' g fl V₁ ⟨rfl, rfl, hV₁⟩ U t₁ hKU hAU hrU hgU -
  subst V₁
  have hsU : U.cpu.gpr.rsp = S := by
    rw [hgU]
    show Y.cpu.gpr.rsp + 8 + 8 + 8 = S
    rw [ms, Fnd.q3]
  have e1 : rdq(W, Y.cpu.gpr.rsp) = g0.rbx := by rw [ms]; exact s1
  have e2 : rdq(W, Y.cpu.gpr.rsp + 8) = g0.rbp := by rw [ms]; exact s2
  have e3 : rdq(W, Y.cpu.gpr.rsp + 8 + 8) = g0.r12 := by rw [ms]; exact s3
  refine c.s_ret hKU hAU hin (lt_len (by decide)) hrU (ret_104 _) (by rw [hsU]; exact f0) hin₂ h₂
    (by rw [hsU]; exact s4) ?_
  rintro Z' t₂ hKZ' hAZ' ⟨hrZ', hgZ'⟩
  refine k Z' t₂ hKZ' hAZ' hrZ' ?_ ?_ ?_
  · rw [hgZ']
    show U.cpu.gpr.rsp + 8 = _
    rw [hsU]
  · rw [hgZ', hgU]
    exact ⟨e1, e2, e3, m13, m14, m15⟩
  · rw [hgZ', hgU]
    show BitVec.setWidth 64 (BitVec.setWidth 32 Y.cpu.gpr.r12) = _
    rw [h12]

/-- `AString::operator=` from the `call` at 92 (the bytes `V'`, `rsi` = `a`, `r12` = `r`): at its entry, and from
its return with the frame, `r12`, the stack as it was and `P2`, the run goes on to the goal. -/
def KAs (prof : Profile) (F : Footprint) (Wl : List Rgn) (L : List (Addr × List Byte)) (s₀ : State) (o : Oracle)
    (gev : List Event) (gP : State → Nat → List Event → Prop) (gE : Outcome → List Event → Prop)
    (P2 : State → (Addr → Byte) → Prop) (S : Addr) (g0 : Gprs) (ra : Addr) (V' : Addr → Byte) (a : Addr)
    (r : BitVec 64) : Prop :=
  ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y →
    Agree F Y.proc.mm.mem (Vst V' (S - 8 - 8 - 8 - 8) (toBytesLE (fkd_at.add 97) 8)) →
    Y.cpu.rip = Aac.aac_at → Y.cpu.gpr.rsp = S - 8 - 8 - 8 - 8 → Y.cpu.gpr.rdi = g0.rdi + 104#64 →
    Y.cpu.gpr.rsi = a → Y.cpu.gpr.rbx = g0.rsi → Y.cpu.gpr.rbp = g0.rdi → Y.cpu.gpr.r12 = r →
    Y.cpu.gpr.r13 = g0.r13 → Y.cpu.gpr.r14 = g0.r14 → Y.cpu.gpr.r15 = g0.r15 →
    (∀ (Z₂ : State) (V₂ : Addr → Byte) (t'' : Nat), KeptW Wl s₀ Z₂ → Agree F Z₂.proc.mm.mem V₂ →
      Z₂.cpu.rip = fkd_at.add 97 → Fm S g0 Z₂.cpu.gpr → Z₂.cpu.gpr.r12 = r → Fnd.StkF V₂ S g0 ra →
      P2 Z₂ V₂ →
      GoG prof L o gev gP gE Z₂ t'') →
    GoG prof L o gev gP gE Y t'

/-- From 88 (`rsi` = `a`): `rdi` = `&fi.Name`, the `call` of `operator=`; from its return 97. -/
theorem from88 {V' : Addr → Byte} {S : Addr} {g0 : Gprs} {r : BitVec 64} {a : Addr}
    {P2 : State → (Addr → Byte) → Prop} {Y : State} (c : Seg prof F Wl L s₀ o) (hin : CodeIn L fkd_at fkd)
    (hinA : CodeIn L Aac.aac_at Aac.aac) (hs4 : ∀ i < 8, Foot Wl (Addr.add (S - 8 - 8 - 8 - 8) i))
    (ft : Fnd.FtsF F S) (hin₂ : CodeIn L e₂ code₂) (h₂ : j₂ < code₂.length)
    (k2 : KAs prof F Wl L s₀ o gev gP gE P2 S g0 (e₂.add j₂) V' a r)
    (kr : ∀ (W : Addr → Byte) (Z' : State) (t' : Nat), KeptW Wl s₀ Z' → Agree F Z'.proc.mm.mem W →
      Z'.cpu.rip = e₂.add j₂ → Z'.cpu.gpr.rsp = S + 8 → Fnd.KS g0 Z'.cpu.gpr →
      Z'.cpu.gpr.rax = BitVec.setWidth 64 (BitVec.setWidth 32 r) →
      (∃ (Z₂ : State) (V₂ : Addr → Byte), P2 Z₂ V₂ ∧ W = V₂) → GoG prof L o gev gP gE Z' t')
    (hK : KeptW Wl s₀ Y) (hA : Agree F Y.proc.mm.mem V') (hr : Y.cpu.rip = fkd_at.add 88)
    (hm : Fm S g0 Y.cpu.gpr) (h12 : Y.cpu.gpr.r12 = r) (hsi : Y.cpu.gpr.rsi = a) :
    GoG prof L o gev gP gE Y t := by
  refine (c_88 prof).run c hin (fun j' g' _ V'' => j' = 92 ∧ V'' = V' ∧ g'.rdi = Y.cpu.gpr.rbp + 104#64 ∧
      g'.rsi = Y.cpu.gpr.rsi ∧ g'.r12 = Y.cpu.gpr.r12 ∧ Fr Y.cpu.gpr g') hK hA hr
    (vc_88 fun _ a b d e _ => ⟨rfl, rfl, a, b, d, e⟩) ?_
  rintro j' g fl V₁ ⟨rfl, hV₁, gdi, gsi, g12, gf⟩ U t₁ hKU hAU hrU hgU -
  subst V₁ hgU
  have hmU := Fm.fr hm gf
  have hU : U.cpu.gpr.rsp - 8 = S - 8 - 8 - 8 - 8 := by rw [hmU.1]
  refine c.s_call_x hKU hAU hin (lt_len (by decide)) hrU (call_92 _) hinA (tgt := 0) (Aac.lt_len (by decide))
    tgt_92 (by rw [hU]; exact hs4) ?_
  rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
  rw [hU] at hA₂
  refine k2 Y₂ t₂ hK₂ hA₂ (by rw [hr₂, addr_add_zero]) (by rw [hg₂]; exact hU)
    (by rw [hg₂]; show U.cpu.gpr.rdi = _; rw [gdi, hm.2.2.1]) (by rw [hg₂]; show U.cpu.gpr.rsi = _; rw [gsi, hsi])
    (by rw [hg₂]; exact hmU.2.1) (by rw [hg₂]; exact hmU.2.2.1)
    (by rw [hg₂]; show U.cpu.gpr.r12 = _; rw [g12, h12])
    (by rw [hg₂]; exact hmU.2.2.2.1) (by rw [hg₂]; exact hmU.2.2.2.2.1) (by rw [hg₂]; exact hmU.2.2.2.2.2) ?_
  intro Z₂ V₂ t₃ hKZ hAZ hrZ hmZ hz12 hst hP2
  exact tail97 c hin hKZ hAZ hrZ hmZ hz12 hst ft hin₂ h₂ fun Z' t₄ a b d e f g =>
    kr V₂ Z' t₄ a b d e f g ⟨Z₂, V₂, hP2, rfl⟩

/-- `FindFile_KeepDots (fi, path, followLink)` (`fi` = `rdi`, `path` = `rsi`) from its entry. `CFileInfo::Find` at
its entry with `rsp` 32 below the entry's, the three registers pushed and the return address, `rsi` = the path's chars
(`k1`); from its return (`P1`, the reads from 21 in the footprint) to the return address with the bytes it left, or
(`al` not 0, the path ends in "." or ".." after a '/' or at its start) `AString::operator=` on `fi.Name` with the dots
(`k2`), and from its return (`P2`) to the return address. There (`kr`): `rsp` 8 above the entry's, the callee-saved
registers as they were, `eax` = `Find`'s `eax`. -/
theorem fkd_ok {P1 P2 : State → (Addr → Byte) → Prop} (c : Seg prof F Wl L s₀ o)
    (hin : CodeIn L fkd_at fkd) (hinF : CodeIn L Fnd.fnd_at Fnd.fnd) (hinA : CodeIn L Aac.aac_at Aac.aac)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = fkd_at)
    (hs1 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8) i))
    (hs2 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8 - 8) i))
    (hs3 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8 - 8 - 8) i))
    (hs4 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8 - 8 - 8 - 8) i))
    (hl : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsp i)) (hp : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsi i))
    (hin₂ : CodeIn L e₂ code₂) (h₂ : j₂ < code₂.length)
    (k1 : ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y →
      Agree F Y.proc.mm.mem
        (Vst (Ffp.V1 V X.cpu.gpr) (X.cpu.gpr.rsp - 8 - 8 - 8 - 8) (toBytesLE (fkd_at.add 21) 8)) →
      Y.cpu.rip = Fnd.fnd_at → Y.cpu.gpr.rsp = X.cpu.gpr.rsp - 8 - 8 - 8 - 8 → Y.cpu.gpr.rdi = X.cpu.gpr.rdi →
      Y.cpu.gpr.rsi = rdq(Ffp.V1 V X.cpu.gpr, X.cpu.gpr.rsi) →
      Y.cpu.gpr.rdx = BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.setWidth 8 X.cpu.gpr.rdx)) →
      Y.cpu.gpr.rbx = X.cpu.gpr.rsi → Y.cpu.gpr.rbp = X.cpu.gpr.rdi → Y.cpu.gpr.r12 = X.cpu.gpr.r12 →
      Y.cpu.gpr.r13 = X.cpu.gpr.r13 → Y.cpu.gpr.r14 = X.cpu.gpr.r14 → Y.cpu.gpr.r15 = X.cpu.gpr.r15 →
      (∀ (Z : State) (V' : Addr → Byte) (t'' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V' →
        Z.cpu.rip = fkd_at.add 21 → Fm X.cpu.gpr.rsp X.cpu.gpr Z.cpu.gpr →
        Fnd.StkF V' X.cpu.gpr.rsp X.cpu.gpr (e₂.add j₂) → KdF F V' X.cpu.gpr.rsi → P1 Z V' →
        GoG prof L o gev gP gE Z t'') →
      GoG prof L o gev gP gE Y t')
    (k2 : ∀ (Z : State) (V' : Addr → Byte), P1 Z V' → ¬BitVec.setWidth 8 Z.cpu.gpr.rax = 0 → ∀ a : Addr,
      (a = pe V' X.cpu.gpr.rsi ∨ a = pe V' X.cpu.gpr.rsi + 18446744073709551615#64 ∨ a = rdq(V', X.cpu.gpr.rsi)) →
      KAs prof F Wl L s₀ o gev gP gE P2 X.cpu.gpr.rsp X.cpu.gpr (e₂.add j₂) V' a
        (BitVec.setWidth 64 (BitVec.setWidth 32 Z.cpu.gpr.rax)))
    (kr : ∀ (W : Addr → Byte) (Z' : State) (t' : Nat), KeptW Wl s₀ Z' → Agree F Z'.proc.mm.mem W →
      Z'.cpu.rip = e₂.add j₂ → Z'.cpu.gpr.rsp = X.cpu.gpr.rsp + 8 → Fnd.KS X.cpu.gpr Z'.cpu.gpr →
      (∃ (Z : State) (V' : Addr → Byte), P1 Z V' ∧
        Z'.cpu.gpr.rax = BitVec.setWidth 64 (BitVec.setWidth 32 Z.cpu.gpr.rax) ∧
        (W = V' ∨ ∃ (Z₂ : State) (V₂ : Addr → Byte), P2 Z₂ V₂ ∧ W = V₂)) →
      GoG prof L o gev gP gE Z' t') :
    GoG prof L o gev gP gE X t := by
  have ft : Fnd.FtsF F X.cpu.gpr.rsp :=
    ⟨fun i hi => c.hws _ (hs3 i hi), by rw [Fnd.q1]; exact fun i hi => c.hws _ (hs2 i hi),
      by rw [Fnd.q2]; exact fun i hi => c.hws _ (hs1 i hi), hl⟩
  -- the prologue, to the first `call`
  refine (c_0 prof).run c hin (fun j' g' _ V' => j' = 16 ∧ V' = Ffp.V1 V X.cpu.gpr ∧
      g'.rsp = X.cpu.gpr.rsp - 8 - 8 - 8 ∧ g'.rdi = X.cpu.gpr.rdi ∧
      g'.rsi = rdq(Ffp.V1 V X.cpu.gpr, X.cpu.gpr.rsi) ∧
      g'.rdx = BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.setWidth 8 X.cpu.gpr.rdx)) ∧
      g'.rbx = X.cpu.gpr.rsi ∧ g'.rbp = X.cpu.gpr.rdi ∧ g'.r12 = X.cpu.gpr.r12 ∧ g'.r13 = X.cpu.gpr.r13 ∧
      g'.r14 = X.cpu.gpr.r14 ∧ g'.r15 = X.cpu.gpr.r15) hK hA (by rw [addr_add_zero]; exact hrip)
    (vc_0 hs1 hs2 hs3 hp fun _ a b d e f g h i j k _ => ⟨rfl, rfl, a, b, d, e, f, g, h, i, j, k⟩) ?_
  rintro j' g fl V₁ ⟨rfl, rfl, gs, gdi, gsi, gdx, gbx, gbp, g12, g13, g14, g15⟩ Y t₁ hKY hAY hrY hgY -
  subst hgY
  have hY : Y.cpu.gpr.rsp - 8 = X.cpu.gpr.rsp - 8 - 8 - 8 - 8 := by rw [gs]
  refine c.s_call_x hKY hAY hin (lt_len (by decide)) hrY (call_16 _) hinF (tgt := 0) (Fnd.lt_len (by decide))
    tgt_16 (by rw [hY]; exact hs4) ?_
  rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
  rw [hY] at hA₂
  refine k1 Y₂ t₂ hK₂ hA₂ (by rw [hr₂, addr_add_zero]) (by rw [hg₂]; exact hY) (by rw [hg₂]; exact gdi)
    (by rw [hg₂]; exact gsi) (by rw [hg₂]; exact gdx) (by rw [hg₂]; exact gbx) (by rw [hg₂]; exact gbp)
    (by rw [hg₂]; exact g12) (by rw [hg₂]; exact g13) (by rw [hg₂]; exact g14) (by rw [hg₂]; exact g15) ?_
  -- back from `Find`, at 21
  intro Z V' t₃ hKZ hAZ hrZ hmZ hst hT hP1
  have hT' : KdF F V' Z.cpu.gpr.rbx := by rw [hmZ.2.1]; exact hT
  refine (c_21 prof).run c hin (fun j' g' _ V'' => V'' = V' ∧
      g'.r12 = BitVec.setWidth 64 (BitVec.setWidth 32 Z.cpu.gpr.rax) ∧ Fr Z.cpu.gpr g' ∧
      (j' = 97 ∨ (j' = 88 ∧ ¬BitVec.setWidth 8 Z.cpu.gpr.rax = 0 ∧
        (g'.rsi = pe V' X.cpu.gpr.rsi ∨ g'.rsi = pe V' X.cpu.gpr.rsi + 18446744073709551615#64 ∨
          g'.rsi = rdq(V', X.cpu.gpr.rsi))))) hKZ hAZ hrZ
    (vc_21 (cc := rdq(V', Z.cpu.gpr.rbx)) (ll := rdd(V', Z.cpu.gpr.rbx + 8#64)) rfl rfl hT'.n4 hT'.c8 hT'.l1
      hT'.m1 hT'.m2 (fun _ a b _ => ⟨rfl, a, b, Or.inl rfl⟩)
      (fun h0 _ hs a b _ => ⟨rfl, a, b, Or.inr ⟨rfl, h0, by rw [hmZ.2.1] at hs; exact hs⟩⟩)) ?_
  rintro j' g fl V₂ ⟨hV₂, g12, gf, hpost⟩ U t₄ hKU hAU hrU hgU -
  subst V₂ hgU
  have hmU := Fm.fr hmZ gf
  rcases hpost with rfl | ⟨rfl, h0, hsi⟩
  · -- no dots kept: `eax` back, the pops and the `ret`
    exact tail97 c hin hKU hAU hrU hmU g12 hst ft hin₂ h₂ fun Z' t₅ a b d e f g =>
      kr V' Z' t₅ a b d e f ⟨Z, V', hP1, by rw [g, sw_64_32], Or.inl rfl⟩
  · -- the dots to `fi.Name`
    exact from88 c hin hinA hs4 ft hin₂ h₂ (k2 Z V' hP1 h0 _ hsi)
      (fun W Z' t' a b d e f g hw => kr W Z' t' a b d e f ⟨Z, V', hP1, by rw [g, sw_64_32], Or.inr hw⟩)
      hKU hAU hrU hmU g12 rfl

end FV7z.Fkd
