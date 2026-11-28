import FV7z.Gcf.Cuts
import FV7z.Lemmas.LeafRet
import FV7z.Lemmas.Fr24
/-!
# `Get_Correct_FsFile_Name` (PLAN.md §M, M1)

7-Zip 26.06's `UString Get_Correct_FsFile_Name (const UString &name)` at `0x5c7070` in `7zzs`
(`CPP/7zip/UI/Common/ExtractingFilePath.cpp`; `objdump -d`), `p` = `rdi` (the result), `q` = `rsi` (`name`):
`endbr64; push r12; mov r12, rdi; push rbp; sub rsp, 8`; at 14 the `call` of `UString (const UString &)` (`0x44d5d0`,
`res = name`); at 19 `mov edx, [r12 + 8]; test edx, edx; je 64`; at 28 `mov rdi, r12`, at 31 the `call` of
`Correct_PathPart (res)` (`0x5c6ee0`, `.part.0`: the part for a string not empty); at 36 `mov eax, [r12 + 8];
test eax, eax; je 64`; at 45 `add rsp, 8; mov rax, r12; pop rbp; pop r12; ret` (55); at 64 `mov esi, 0x5f;
mov rdi, r12`, at 72 the `call` of `UString::operator= (wchar_t)` (`0x44d600`, `res = '_'`); at 77 the same epilogue,
`ret` (87). Cuts 0, 19, 36, 64, 77. The landing pad after 88 is left out.

Design as `FV7z/Efn/Holds.lean` (the 24-byte frame of `FV7z/Lemmas/Fr24.lean`, `rbp` saved where `Efn` saves `rbx`):
the three callees are hypotheses, each a continuation at its entry given the run from its return (`rsp` 24 below the
entry's, `r12` = `p`, the saved `rbp`, `r12` and the return address left as they were, and the callee's own post
`P1`, `P2`, `P3`): `k1` at the copy constructor, `k2` at `Correct_PathPart` (when `res._len`, the 4 bytes at `p + 8`,
is not 0), `k3` at `operator=` (when `res._len` is 0, after `k1` or after `k2`); `kr` at the return address (after
`k2` with `res._len` not 0, or after `k3`). The way from 64 is one `have` (`k64`), used from 19 and from 36.

- `gE`: the registers at the first `call`; `g19`, `g31`: the registers after the `mov edx` and
  at the second `call`; `g36`: after the `mov eax`; `g72`: at the third `call`.
- `vc_0`, `vc_19`, `vc_36`, `vc_64`, `vc_77`: the verification conditions of the pieces.
- `gcf_ok`: from the entry to the return address with `rax` = `p` and `rbp`, `r12`, `rsp` restored.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn FV7z.Fr24
namespace FV7z.Gcf

/-- The `call` to `UString (const UString &)`. -/
def pc1 : List Byte := [0xe8, 0x4d, 0x65, 0xe8, 0xff]
theorem pc1_0 : ∀ feat, Dec feat pc1 0 (FV7z.mk .call 64 [.rel 18446744073708004685] 5) := by dec_rfl
theorem wc_14 : pc1 <+: gcf.drop 14 := by decide +kernel
theorem call_14 (feat : Features) : Dec feat gcf 14 (FV7z.mk .call 64 [.rel 18446744073708004685] 5) :=
  Dec.shift (j := 14) (k := 0) (pc1_0 feat) wc_14 (Nat.zero_le _)

/-- The `call` to `Correct_PathPart`. -/
def pc2 : List Byte := [0xe8, 0x4c, 0xfe, 0xff, 0xff]
theorem pc2_0 : ∀ feat, Dec feat pc2 0 (FV7z.mk .call 64 [.rel 18446744073709551180] 5) := by dec_rfl
theorem wc_31 : pc2 <+: gcf.drop 31 := by decide +kernel
theorem call_31 (feat : Features) : Dec feat gcf 31 (FV7z.mk .call 64 [.rel 18446744073709551180] 5) :=
  Dec.shift (j := 31) (k := 0) (pc2_0 feat) wc_31 (Nat.zero_le _)

/-- The `call` to `UString::operator= (wchar_t)`. -/
def pc3 : List Byte := [0xe8, 0x43, 0x65, 0xe8, 0xff]
theorem pc3_0 : ∀ feat, Dec feat pc3 0 (FV7z.mk .call 64 [.rel 18446744073708004675] 5) := by dec_rfl
theorem wc_72 : pc3 <+: gcf.drop 72 := by decide +kernel
theorem call_72 (feat : Features) : Dec feat gcf 72 (FV7z.mk .call 64 [.rel 18446744073708004675] 5) :=
  Dec.shift (j := 72) (k := 0) (pc3_0 feat) wc_72 (Nat.zero_le _)

/-- The `ret`s. -/
def pret : List Byte := [0xc3]
theorem pret_0 : ∀ feat, Dec feat pret 0 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem w_55 : pret <+: gcf.drop 55 := by decide +kernel
theorem ret_55 (feat : Features) : Dec feat gcf 55 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 55) (k := 0) (pret_0 feat) w_55 (Nat.zero_le _)
theorem w_87 : pret <+: gcf.drop 87 := by decide +kernel
theorem ret_87 (feat : Features) : Dec feat gcf 87 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 87) (k := 0) (pret_0 feat) w_87 (Nat.zero_le _)

/-- The registers at the first `call`: `r12` = `p`, `rsp` 24 down (`rdi` = `p`, `rsi` = `q` as at the entry). -/
abbrev gE (g : Gprs) : Gprs := { g with rsp := g.rsp - 8 - 8 - 8#64, r12 := g.rdi }

/-- After `mov edx, [r12 + 8]`: `edx` = `res._len`. -/
abbrev g19 (g : Gprs) (V : Addr → Byte) : Gprs := { g with rdx := BitVec.setWidth 64 rdd(V, g.r12 + 8#64) }

/-- The registers at the second `call`: `rdi` = `res`. -/
abbrev g31 (g : Gprs) (V : Addr → Byte) : Gprs :=
  { g with rdx := BitVec.setWidth 64 rdd(V, g.r12 + 8#64), rdi := g.r12 }

/-- After `mov eax, [r12 + 8]`: `eax` = `res._len`. -/
abbrev g36 (g : Gprs) (V : Addr → Byte) : Gprs := { g with rax := BitVec.setWidth 64 rdd(V, g.r12 + 8#64) }

/-- The registers at the third `call`: `rdi` = `res`, `esi` = `'_'`. -/
abbrev g72 (g : Gprs) : Gprs := { g with rsi := 95#64, rdi := g.r12 }

variable {F : Footprint} {Wl : List Rgn}

/-- `endbr64; push r12; mov r12, rdi; push rbp; sub rsp, 8`, to the `call` at 14. -/
theorem vc_0 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (hs1 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8) i)) (hs2 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8) i))
    (h : ∀ fl, Q 14 (gE g) fl (Vst (Vst V (g.rsp - 8) (toBytesLE g.r12 8)) (g.rsp - 8 - 8) (toBytesLE g.rbp 8))) :
    W_0 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [gE] at hs1 hs2 h ⊢
  wpx [W_0, o0]
  all_goals repeat' (first | exact h _ | assumption | exact trivial | apply And.intro | intro _)

/-- `mov edx, [r12 + 8]; test edx, edx; je 64`, else `mov rdi, r12` to the `call` at 31. -/
theorem vc_19 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (fd : ∀ i < 4, Foot F.data (Addr.add (g.r12 + 8#64) i))
    (h64 : rdd(V, g.r12 + 8#64) = 0 → ∀ fl, Q 64 (g19 g V) fl V)
    (h31 : rdd(V, g.r12 + 8#64) ≠ 0 → ∀ fl, Q 31 (g31 g V) fl V) :
    W_19 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [g19, g31] at fd h64 h31 ⊢
  by_cases h0 : rdd(V, r12 + 8#64) = 0
  · have hz : (rdd(V, r12 + 8#64) == 0) = true := beq_iff_eq.2 h0
    wpx [W_19, W_28, o1, o2, hz, BitVec.and_self, Bool.false_eq_true, Bool.true_eq_false, false_implies,
      implies_true]
    all_goals repeat' (first | exact h64 h0 _ | assumption | exact trivial | apply And.intro | intro _)
  · have hz : (rdd(V, r12 + 8#64) == 0) = false := beq_eq_false_iff_ne.2 h0
    wpx [W_19, W_28, o1, o2, hz, BitVec.and_self, Bool.false_eq_true, Bool.true_eq_false, false_implies,
      implies_true]
    all_goals repeat' (first | exact h31 h0 _ | assumption | exact trivial | apply And.intro | intro _)

/-- `mov eax, [r12 + 8]; test eax, eax; je 64`, else the epilogue to the `ret` at 55. -/
theorem vc_36 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (fd : ∀ i < 4, Foot F.data (Addr.add (g.r12 + 8#64) i))
    (hl1 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8#64) i))
    (hl2 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8#64 + 8) i))
    (h64 : rdd(V, g.r12 + 8#64) = 0 → ∀ fl, Q 64 (g36 g V) fl V)
    (h55 : rdd(V, g.r12 + 8#64) ≠ 0 → ∀ fl, Q 55
      { g with
        rax := g.r12
        rbp := rdq(V, g.rsp + 8#64)
        rsp := g.rsp + 8#64 + 8 + 8
        r12 := rdq(V, g.rsp + 8#64 + 8) } fl V) :
    W_36 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [g36] at fd hl1 hl2 h64 h55 ⊢
  by_cases h0 : rdd(V, r12 + 8#64) = 0
  · have hz : (rdd(V, r12 + 8#64) == 0) = true := beq_iff_eq.2 h0
    wpx [W_36, W_45, o3, o4, hz, BitVec.and_self, Bool.false_eq_true, Bool.true_eq_false, false_implies,
      implies_true]
    all_goals repeat' (first | exact h64 h0 _ | assumption | exact trivial | apply And.intro | intro _)
  · have hz : (rdd(V, r12 + 8#64) == 0) = false := beq_eq_false_iff_ne.2 h0
    wpx [W_36, W_45, o3, o4, hz, BitVec.and_self, Bool.false_eq_true, Bool.true_eq_false, false_implies,
      implies_true]
    all_goals repeat' (first | exact h55 h0 _ | assumption | exact trivial | apply And.intro | intro _)

/-- `mov esi, 0x5f; mov rdi, r12`, to the `call` at 72. -/
theorem vc_64 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} (h : ∀ fl, Q 72 (g72 g) fl V) :
    W_64 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [g72] at h ⊢
  wpx [W_64, o5]
  all_goals repeat' (first | exact h _ | assumption | exact trivial | apply And.intro | intro _)

/-- The epilogue at 77, to the `ret` at 87. -/
theorem vc_77 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (hl1 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8#64) i))
    (hl2 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8#64 + 8) i))
    (h : ∀ fl, Q 87
      { g with
        rax := g.r12
        rbp := rdq(V, g.rsp + 8#64)
        rsp := g.rsp + 8#64 + 8 + 8
        r12 := rdq(V, g.rsp + 8#64 + 8) } fl V) :
    W_77 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hl1 hl2 h ⊢
  wpx [W_77, o4]
  all_goals repeat' (first | exact h _ | assumption | exact trivial | apply And.intro | intro _)

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE' : Outcome → List Event → Prop}
  {X : State} {t : Nat} {V : Addr → Byte}

/-- `Get_Correct_FsFile_Name (name)` (`p` = `rdi`, `q` = `rsi`) from its entry, `r12` and `rbp` saved at `rsp - 8`
and `rsp - 16`: at the copy constructor (`0x44d5d0`) with the registers `gE`, the return address `gcf_at + 19` at
`rsp - 32` (`k1`); from its return, when `res._len` is not 0, at `Correct_PathPart` (`0x5c6ee0`) with `g31` (`k2`);
when `res._len` is 0 then (after `k1` or `k2`), at `operator= (wchar_t)` (`0x44d600`) with `g72` (`k3`); then at the
return address with `rax` = `p`, `rbp`, `r12`, `rsp` restored (`kr`). -/
theorem gcf_ok {P1 P2 P3 : State → (Addr → Byte) → Prop} (c : Seg prof F Wl L s₀ o) (hin : CodeIn L gcf_at gcf)
    {code1 : List Byte} (hin1 : CodeIn L 0x44d5d0#64 code1) (hc1 : 0 < code1.length)
    {code2 : List Byte} (hin2 : CodeIn L 0x5c6ee0#64 code2) (hc2 : 0 < code2.length)
    {code3 : List Byte} (hin3 : CodeIn L 0x44d600#64 code3) (hc3 : 0 < code3.length)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = gcf_at)
    (hs1 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8) i))
    (hs2 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 16) i))
    (hs4 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 32) i))
    (hl : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsp i))
    (hfl : ∀ i < 4, Foot F.data (Addr.add (X.cpu.gpr.rdi + 8#64) i))
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (k1 : ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y →
      Agree F Y.proc.mm.mem (Vst (Vst (Vst V (X.cpu.gpr.rsp - 8) (toBytesLE X.cpu.gpr.r12 8)) (X.cpu.gpr.rsp - 16)
        (toBytesLE X.cpu.gpr.rbp 8)) (X.cpu.gpr.rsp - 32) (toBytesLE (gcf_at.add 19) 8)) →
      Y.cpu.rip = 0x44d5d0#64 → Y.cpu.gpr = (gE X.cpu.gpr).set 4 (X.cpu.gpr.rsp - 32) →
      (∀ (Z : State) (V' : Addr → Byte) (t'' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V' →
        Z.cpu.rip = gcf_at.add 19 → Z.cpu.gpr.rsp = X.cpu.gpr.rsp - 24 → Z.cpu.gpr.r12 = X.cpu.gpr.rdi →
        rdq(V', X.cpu.gpr.rsp - 16) = X.cpu.gpr.rbp → rdq(V', X.cpu.gpr.rsp - 8) = X.cpu.gpr.r12 →
        rdq(V', X.cpu.gpr.rsp) = e₂.add j₂ → P1 Z V' →
        GoG prof L o gev gP gE' Z t'') →
      GoG prof L o gev gP gE' Y t')
    (k2 : ∀ (Z : State) (V' : Addr → Byte), P1 Z V' → rdd(V', X.cpu.gpr.rdi + 8#64) ≠ 0 →
      ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y →
      Agree F Y.proc.mm.mem (Vst V' (X.cpu.gpr.rsp - 32) (toBytesLE (gcf_at.add 36) 8)) →
      Y.cpu.rip = 0x5c6ee0#64 → Y.cpu.gpr = (g31 Z.cpu.gpr V').set 4 (X.cpu.gpr.rsp - 32) →
      (∀ (Z₂ : State) (V₂ : Addr → Byte) (t'' : Nat), KeptW Wl s₀ Z₂ → Agree F Z₂.proc.mm.mem V₂ →
        Z₂.cpu.rip = gcf_at.add 36 → Z₂.cpu.gpr.rsp = X.cpu.gpr.rsp - 24 → Z₂.cpu.gpr.r12 = X.cpu.gpr.rdi →
        rdq(V₂, X.cpu.gpr.rsp - 16) = X.cpu.gpr.rbp → rdq(V₂, X.cpu.gpr.rsp - 8) = X.cpu.gpr.r12 →
        rdq(V₂, X.cpu.gpr.rsp) = e₂.add j₂ → P2 Z₂ V₂ →
        GoG prof L o gev gP gE' Z₂ t'') →
      GoG prof L o gev gP gE' Y t')
    (k3 : ∀ (Z : State) (V' : Addr → Byte), P1 Z V' ∨ P2 Z V' → rdd(V', X.cpu.gpr.rdi + 8#64) = 0 →
      ∀ (G : Gprs), G.rsp = X.cpu.gpr.rsp - 24 → G.r12 = X.cpu.gpr.rdi →
      ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y →
      Agree F Y.proc.mm.mem (Vst V' (X.cpu.gpr.rsp - 32) (toBytesLE (gcf_at.add 77) 8)) →
      Y.cpu.rip = 0x44d600#64 → Y.cpu.gpr = (g72 G).set 4 (X.cpu.gpr.rsp - 32) →
      (∀ (Z₃ : State) (V₃ : Addr → Byte) (t'' : Nat), KeptW Wl s₀ Z₃ → Agree F Z₃.proc.mm.mem V₃ →
        Z₃.cpu.rip = gcf_at.add 77 → Z₃.cpu.gpr.rsp = X.cpu.gpr.rsp - 24 → Z₃.cpu.gpr.r12 = X.cpu.gpr.rdi →
        rdq(V₃, X.cpu.gpr.rsp - 16) = X.cpu.gpr.rbp → rdq(V₃, X.cpu.gpr.rsp - 8) = X.cpu.gpr.r12 →
        rdq(V₃, X.cpu.gpr.rsp) = e₂.add j₂ → P3 Z₃ V₃ →
        GoG prof L o gev gP gE' Z₃ t'') →
      GoG prof L o gev gP gE' Y t')
    (kr : ∀ (Z₂ : State) (V₂ : Addr → Byte) (Z' : State) (t' : Nat),
      (P2 Z₂ V₂ ∧ rdd(V₂, X.cpu.gpr.rdi + 8#64) ≠ 0) ∨ P3 Z₂ V₂ → KeptW Wl s₀ Z' →
      Agree F Z'.proc.mm.mem V₂ → Z'.cpu.rip = e₂.add j₂ →
      Z'.cpu.gpr = { Z₂.cpu.gpr with
        rax := X.cpu.gpr.rdi
        rbp := X.cpu.gpr.rbp
        rsp := X.cpu.gpr.rsp + 8
        r12 := X.cpu.gpr.r12 } →
      GoG prof L o gev gP gE' Z' t') :
    GoG prof L o gev gP gE' X t := by
  have h8 : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rsp - 8) i) := fun i hi => c.hws _ (hs1 i hi)
  have h16 : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rsp - 16) i) := fun i hi => c.hws _ (hs2 i hi)
  have hrip' : X.cpu.rip = gcf_at.add 0 := by rw [addr_add_zero]; exact hrip
  -- the way from 64: `operator= (wchar_t)`, the epilogue at 77, the `ret` at 87
  have k64 : ∀ (Z : State) (V' : Addr → Byte), P1 Z V' ∨ P2 Z V' → rdd(V', X.cpu.gpr.rdi + 8#64) = 0 →
      ∀ (U : State) (t' : Nat), KeptW Wl s₀ U → Agree F U.proc.mm.mem V' → U.cpu.rip = gcf_at.add 64 →
      U.cpu.gpr.rsp = X.cpu.gpr.rsp - 24 → U.cpu.gpr.r12 = X.cpu.gpr.rdi → GoG prof L o gev gP gE' U t' := by
    intro Z V' hP h0 U t' hKU hAU hrU hus hu12
    refine (c_64 prof).run c hin (fun j' g' _ V'' => j' = 72 ∧ g' = g72 U.cpu.gpr ∧ V'' = V') hKU hAU hrU
      (vc_64 fun _ => ⟨rfl, rfl, rfl⟩) ?_
    rintro j' g fl V₂ ⟨rfl, rfl, hV₂⟩ Y t₃ hKY hAY hrY hgY -
    subst V₂
    have hsY : Y.cpu.gpr.rsp = X.cpu.gpr.rsp - 24 := by rw [hgY]; exact hus
    have hY32 : Y.cpu.gpr.rsp - 8 = X.cpu.gpr.rsp - 32 := by rw [hsY, peD]
    have hst : ∀ i < 8, Foot Wl (Addr.add (Y.cpu.gpr.rsp - 8) i) := by rw [hY32]; exact hs4
    refine c.s_call hKY hAY hin (lt_len (by decide)) hrY (call_72 _) hin3 hc3 (by decide) hst ?_
    rintro Y₂ t₄ hK₂ hA₂ ⟨hr₂, hg₂⟩
    rw [hY32] at hA₂
    have hg₂' : Y₂.cpu.gpr = (g72 U.cpu.gpr).set 4 (X.cpu.gpr.rsp - 32) := by rw [hg₂, hY32, hgY]
    refine k3 Z V' hP h0 U.cpu.gpr hus hu12 Y₂ t₄ hK₂ hA₂ hr₂ hg₂' ?_
    intro Z₃ V₃ t₅ hKZ hAZ hrZ hzs hz12 hb3 h12b hr3 hP3
    refine (c_77 prof).run c hin (fun j' g' _ V'' => j' = 87 ∧
        g' = { Z₃.cpu.gpr with
          rax := X.cpu.gpr.rdi
          rbp := X.cpu.gpr.rbp
          rsp := X.cpu.gpr.rsp
          r12 := X.cpu.gpr.r12 } ∧ V'' = V₃) hKZ hAZ hrZ
      (vc_77 (by rw [hzs, peA']; exact h16) (by rw [hzs, peA', peB]; exact h8)
        fun _ => ⟨rfl, by rw [hzs, hz12, peA', peB, peC, hb3, h12b], rfl⟩) ?_
    rintro j' g fl V₄ ⟨rfl, rfl, hV₄⟩ U₂ t₆ hKU₂ hAU₂ hrU₂ hgU₂ -
    subst V₄
    have hsU₂ : U₂.cpu.gpr.rsp = X.cpu.gpr.rsp := by rw [hgU₂]
    refine c.s_ret hKU₂ hAU₂ hin (lt_len (by decide)) hrU₂ (ret_87 _) (by rw [hsU₂]; exact hl) hin₂ h₂
      (by rw [hsU₂]; exact hr3) ?_
    rintro Z' t₇ hKZ' hAZ' ⟨hrZ', hgZ'⟩
    refine kr Z₃ V₃ Z' t₇ (Or.inr hP3) hKZ' hAZ' hrZ' ?_
    rw [hgZ', hgU₂]
    try rfl
  -- the prologue, to the first `call`
  refine (c_0 prof).run c hin (fun j' g' _ V' => j' = 14 ∧ g' = gE X.cpu.gpr ∧
      V' = Vst (Vst V (X.cpu.gpr.rsp - 8) (toBytesLE X.cpu.gpr.r12 8)) (X.cpu.gpr.rsp - 16)
        (toBytesLE X.cpu.gpr.rbp 8)) hK hA hrip'
    (vc_0 hs1 (by rw [pe16]; exact hs2) fun _ => ⟨rfl, rfl, by rw [pe16]⟩) ?_
  rintro j' g fl V₁ ⟨rfl, rfl, hV₁⟩ Y t₁ hKY hAY hrY hgY -
  subst V₁
  have hsY : Y.cpu.gpr.rsp = X.cpu.gpr.rsp - 8 - 8 - 8#64 := by rw [hgY]
  have hY32 : Y.cpu.gpr.rsp - 8 = X.cpu.gpr.rsp - 32 := by rw [hsY, pe32]
  have hst : ∀ i < 8, Foot Wl (Addr.add (Y.cpu.gpr.rsp - 8) i) := by rw [hY32]; exact hs4
  refine c.s_call hKY hAY hin (lt_len (by decide)) hrY (call_14 _) hin1 hc1 (by decide) hst ?_
  rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
  rw [hY32] at hA₂
  have hg₂' : Y₂.cpu.gpr = (gE X.cpu.gpr).set 4 (X.cpu.gpr.rsp - 32) := by rw [hg₂, hY32, hgY]
  refine k1 Y₂ t₂ hK₂ hA₂ hr₂ hg₂' ?_
  -- back from the copy constructor, at 19: `res._len` 0 to 64, else to the second `call`
  intro Z V' t'' hKZ hAZ hrZ hzs hz12 hb hr12 hr' hP1
  have flZ : ∀ i < 4, Foot F.data (Addr.add (Z.cpu.gpr.r12 + 8#64) i) := by rw [hz12]; exact hfl
  refine (c_19 prof).run c hin (fun j' g' _ V'' => V'' = V' ∧
      ((rdd(V', Z.cpu.gpr.r12 + 8#64) = 0 ∧ j' = 64 ∧ g' = g19 Z.cpu.gpr V') ∨
        (rdd(V', Z.cpu.gpr.r12 + 8#64) ≠ 0 ∧ j' = 31 ∧ g' = g31 Z.cpu.gpr V'))) hKZ hAZ hrZ
    (vc_19 flZ (fun h0 _ => ⟨rfl, Or.inl ⟨h0, rfl, rfl⟩⟩) (fun h0 _ => ⟨rfl, Or.inr ⟨h0, rfl, rfl⟩⟩)) ?_
  rintro j' g fl V₂ ⟨hV₂, hpost⟩ U t₃ hKU hAU hrU hgU -
  subst V₂
  rw [hz12] at hpost
  rcases hpost with ⟨h0, rfl, hg⟩ | ⟨h0, rfl, hg⟩
  · -- `res._len` 0: the way from 64
    subst hg
    exact k64 Z V' (Or.inl hP1) h0 U t₃ hKU hAU hrU (by rw [hgU]; exact hzs) (by rw [hgU]; exact hz12)
  · -- the `call` of `Correct_PathPart`
    subst hg
    have hsU : U.cpu.gpr.rsp = X.cpu.gpr.rsp - 24 := by rw [hgU]; exact hzs
    have hU32 : U.cpu.gpr.rsp - 8 = X.cpu.gpr.rsp - 32 := by rw [hsU, peD]
    have hst2 : ∀ i < 8, Foot Wl (Addr.add (U.cpu.gpr.rsp - 8) i) := by rw [hU32]; exact hs4
    refine c.s_call hKU hAU hin (lt_len (by decide)) hrU (call_31 _) hin2 hc2 (by decide) hst2 ?_
    rintro Y₃ t₄ hK₃ hA₃ ⟨hr₃, hg₃⟩
    rw [hU32] at hA₃
    have hg₃' : Y₃.cpu.gpr = (g31 Z.cpu.gpr V').set 4 (X.cpu.gpr.rsp - 32) := by rw [hg₃, hU32, hgU]
    refine k2 Z V' hP1 h0 Y₃ t₄ hK₃ hA₃ hr₃ hg₃' ?_
    -- back from `Correct_PathPart`, at 36: `res._len` 0 to 64, else the epilogue and the `ret` at 55
    intro Z₂ V₂ t₅ hKZ₂ hAZ₂ hrZ₂ hz2s hz2r hb2 h12b hr2 hP2
    have flZ₂ : ∀ i < 4, Foot F.data (Addr.add (Z₂.cpu.gpr.r12 + 8#64) i) := by rw [hz2r]; exact hfl
    refine (c_36 prof).run c hin (fun j' g' _ V'' => V'' = V₂ ∧
        ((rdd(V₂, Z₂.cpu.gpr.r12 + 8#64) = 0 ∧ j' = 64 ∧ g' = g36 Z₂.cpu.gpr V₂) ∨
          (rdd(V₂, Z₂.cpu.gpr.r12 + 8#64) ≠ 0 ∧ j' = 55 ∧
            g' = { Z₂.cpu.gpr with
              rax := X.cpu.gpr.rdi
              rbp := X.cpu.gpr.rbp
              rsp := X.cpu.gpr.rsp
              r12 := X.cpu.gpr.r12 }))) hKZ₂ hAZ₂ hrZ₂
      (vc_36 flZ₂ (by rw [hz2s, peA']; exact h16) (by rw [hz2s, peA', peB]; exact h8)
        (fun h0 _ => ⟨rfl, Or.inl ⟨h0, rfl, rfl⟩⟩)
        (fun h0 _ => ⟨rfl, Or.inr ⟨h0, rfl, by rw [hz2s, hz2r, peA', peB, peC, hb2, h12b]⟩⟩)) ?_
    rintro j' g fl V₃ ⟨hV₃, hpost⟩ U₁ t₆ hKU₁ hAU₁ hrU₁ hgU₁ -
    subst V₃
    rw [hz2r] at hpost
    rcases hpost with ⟨h0', rfl, hg⟩ | ⟨h0', rfl, hg⟩
    · -- `res._len` 0: the way from 64
      subst hg
      exact k64 Z₂ V₂ (Or.inr hP2) h0' U₁ t₆ hKU₁ hAU₁ hrU₁ (by rw [hgU₁]; exact hz2s) (by rw [hgU₁]; exact hz2r)
    · -- the `ret` at 55
      subst hg
      have hsU₁ : U₁.cpu.gpr.rsp = X.cpu.gpr.rsp := by rw [hgU₁]
      refine c.s_ret hKU₁ hAU₁ hin (lt_len (by decide)) hrU₁ (ret_55 _) (by rw [hsU₁]; exact hl) hin₂ h₂
        (by rw [hsU₁]; exact hr2) ?_
      rintro Z' t₇ hKZ' hAZ' ⟨hrZ', hgZ'⟩
      refine kr Z₂ V₂ Z' t₇ (Or.inl ⟨hP2, h0'⟩) hKZ' hAZ' hrZ' ?_
      rw [hgZ', hgU₁]
      try rfl

end FV7z.Gcf
