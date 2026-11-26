import FV7z.Aaa.Cuts
import FV7z.Sea.Code
import FV7z.Sea.Blocks
import FV7z.Lemmas.LeafRet
import FV7z.Tun.Inv
/-!
# `NWildcard::CItem::AreAllAllowed` (PLAN.md §M, M1)

7-Zip 26.06's `CItem::AreAllAllowed ()` at `0x452990` in `7zzs` (`CPP/Common/Wildcard.cpp`): with `this` in `rdi`,
unless the flags `ForFile`, `ForDir`, `WildcardMatching` (the bytes at `this + 17`, `+ 18`, `+ 19`) are all set and
`PathParts.Size ()` (the 4 bytes at `this + 8`) is 1 (`aOk`), 0 in `rax` (`xor eax, eax` at 28, the `ret` at 30);
else a tail jump (48) to `StringsAreEqual_Ascii (PathParts[0], "*")` (`Sea.sea_at`), `rdi` the string's characters
(`this->PathParts._items[0]->_chars`) and `rsi` the address of `"*"` (`0x6edcd9`).

The callee is a hypothesis (`kf`), as in `FV7z/Ifs/Holds.lean`.

- `aOk`: the condition; `aG`: the registers at the jump.
- `vc_0`, `vc_28`: the verification conditions of the pieces.
- `aaa_ok`: from the entry to the return address with `rax` = 0 (`kn`), or to the callee's entry (`kf`).
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Aaa

/-- The jump to `StringsAreEqual_Ascii`. -/
def pjm : List Byte := [0xe9, 0x9b, 0x91, 0xff, 0xff]
theorem pjm_0 : ∀ feat, Dec feat pjm 0 (FV7z.mk .jmp 64 [.rel 18446744073709523355] 5) := by dec_rfl
theorem wj_48 : pjm <+: aaa.drop 48 := by decide +kernel
theorem jmp_48 (feat : Features) : Dec feat aaa 48 (FV7z.mk .jmp 64 [.rel 18446744073709523355] 5) :=
  Dec.shift (j := 48) (k := 0) (pjm_0 feat) wj_48 (Nat.zero_le _)

/-- The `ret`. -/
def pret : List Byte := [0xc3]
theorem pret_0 : ∀ feat, Dec feat pret 0 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem w_30 : pret <+: aaa.drop 30 := by decide +kernel
theorem ret_30 (feat : Features) : Dec feat aaa 30 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 30) (k := 0) (pret_0 feat) w_30 (Nat.zero_le _)

/-- The three flags set and one path part. -/
abbrev aOk (V : Addr → Byte) (p : Addr) : Prop :=
  ¬ ofBytesLE 8 ((byteAddrs (p + 17#64) 1).map V) = 0#8 ∧ ¬ ofBytesLE 8 ((byteAddrs (p + 18#64) 1).map V) = 0#8 ∧
    ¬ ofBytesLE 8 ((byteAddrs (p + 19#64) 1).map V) = 0#8 ∧ ofBytesLE 32 ((byteAddrs (p + 8#64) 4).map V) = 1#32

/-- The registers at the jump: `rax` = `PathParts._items[0]`, `rsi` = `"*"`, `rdi` = its `_chars`. -/
abbrev aG (V : Addr → Byte) (g : Gprs) : Gprs :=
  { g with
    rax := rdq(V, rdq(V, g.rdi)),
    rsi := 0x6edcd9#64,
    rdi := rdq(V, rdq(V, rdq(V, g.rdi))) }

variable {F : Footprint} {Wl : List Rgn}

/-- `cmp byte [rdi + 17], 0; je; cmp byte [rdi + 18], 0; je; cmp byte [rdi + 19], 0; je; cmp dword [rdi + 8], 1;
je`, then to 28, or `mov rax, [rdi]; lea rsi, [rip + …]; mov rax, [rax]; mov rdi, [rax]` to the jump at 48. -/
theorem vc_0 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (f17 : ∀ i < 1, Foot F.data (Addr.add (g.rdi + 17#64) i))
    (f18 : ∀ i < 1, Foot F.data (Addr.add (g.rdi + 18#64) i))
    (f19 : ∀ i < 1, Foot F.data (Addr.add (g.rdi + 19#64) i))
    (f8 : ∀ i < 4, Foot F.data (Addr.add (g.rdi + 8#64) i))
    (fp : aOk V g.rdi → (∀ i < 8, Foot F.data (Addr.add g.rdi i)) ∧
      (∀ i < 8, Foot F.data (Addr.add rdq(V, g.rdi) i)) ∧ (∀ i < 8, Foot F.data (Addr.add rdq(V, rdq(V, g.rdi)) i)))
    (h28 : ¬ aOk V g.rdi → ∀ fl, Q 28 g fl V) (h48 : aOk V g.rdi → ∀ fl, Q 48 (aG V g) fl V) :
    W_0 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at f17 f18 f19 f8 ⊢
  by_cases h1 : ofBytesLE 8 ((byteAddrs (rdi + 17#64) 1).map V) = 0#8
  · have hn : ¬ aOk V rdi := fun hk => hk.1 h1
    wpx [W_0, o0, Op.cmpmi, h1, decide_false, decide_true, Bool.false_eq_true, Bool.true_eq_false, false_implies,
      implies_true]
    all_goals repeat'
      first
      | exact h28 hn _
      | assumption
      | exact trivial
      | apply And.intro
      | intro _
  by_cases h2 : ofBytesLE 8 ((byteAddrs (rdi + 18#64) 1).map V) = 0#8
  · have hn : ¬ aOk V rdi := fun hk => hk.2.1 h2
    wpx [W_0, W_10, o0, o1, Op.cmpmi, h1, h2, decide_false, decide_true, Bool.false_eq_true, Bool.true_eq_false,
      false_implies, implies_true]
    all_goals repeat'
      first
      | exact h28 hn _
      | assumption
      | exact trivial
      | apply And.intro
      | intro _
  by_cases h3 : ofBytesLE 8 ((byteAddrs (rdi + 19#64) 1).map V) = 0#8
  · have hn : ¬ aOk V rdi := fun hk => hk.2.2.1 h3
    wpx [W_0, W_10, W_16, o0, o1, o2, Op.cmpmi, h1, h2, h3, decide_false, decide_true, Bool.false_eq_true,
      Bool.true_eq_false, false_implies, implies_true]
    all_goals repeat'
      first
      | exact h28 hn _
      | assumption
      | exact trivial
      | apply And.intro
      | intro _
  by_cases h4 : ofBytesLE 32 ((byteAddrs (rdi + 8#64) 4).map V) = 1#32
  · have hy : aOk V rdi := ⟨h1, h2, h3, h4⟩
    obtain ⟨fa, fb, fc⟩ := fp hy
    dsimp only at fa fb fc
    wpx [W_0, W_10, W_16, W_22, W_32, o0, o1, o2, o3, o5, Op.cmpmi, h1, h2, h3, h4, decide_false, decide_true,
      Bool.false_eq_true, Bool.true_eq_false, false_implies, implies_true]
    all_goals repeat'
      first
      | exact h48 hy _
      | assumption
      | exact trivial
      | apply And.intro
      | intro _
  · have hn : ¬ aOk V rdi := fun hk => h4 hk.2.2.2
    wpx [W_0, W_10, W_16, W_22, o0, o1, o2, o3, Op.cmpmi, h1, h2, h3, h4, decide_false, decide_true,
      Bool.false_eq_true, Bool.true_eq_false, false_implies, implies_true]
    all_goals repeat'
      first
      | exact h28 hn _
      | assumption
      | exact trivial
      | apply And.intro
      | intro _

/-- `xor eax, eax` to the `ret` at 30. -/
theorem vc_28 {g : Gprs} {f : Rflags} {V : Addr → Byte} :
    W_28 F Wl (fun j' g' _ V' => j' = 30 ∧ g' = { g with rax := 0#64 } ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_28, o4, BitVec.xor_self, BitVec.setWidth_zero]
  all_goals repeat' (first | exact rfl | assumption | exact trivial | apply And.intro | intro _)

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {X : State} {t : Nat} {V : Addr → Byte}

/-- `CItem::AreAllAllowed ()` (`this` = `rdi`) from its entry, no byte written. Not `aOk`: at the return address with
`rax` = 0 (`kn`). `aOk`: at `StringsAreEqual_Ascii`'s entry with the registers `aG` (`kf`). -/
theorem aaa_ok (c : Seg prof F Wl L s₀ o) (hin : CodeIn L aaa_at aaa) (hinS : CodeIn L Sea.sea_at Sea.sea)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = aaa_at)
    (f17 : ∀ i < 1, Foot F.data (Addr.add (X.cpu.gpr.rdi + 17#64) i))
    (f18 : ∀ i < 1, Foot F.data (Addr.add (X.cpu.gpr.rdi + 18#64) i))
    (f19 : ∀ i < 1, Foot F.data (Addr.add (X.cpu.gpr.rdi + 19#64) i))
    (f8 : ∀ i < 4, Foot F.data (Addr.add (X.cpu.gpr.rdi + 8#64) i))
    (fp : aOk V X.cpu.gpr.rdi → (∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rdi i)) ∧
      (∀ i < 8, Foot F.data (Addr.add rdq(V, X.cpu.gpr.rdi) i)) ∧
      (∀ i < 8, Foot F.data (Addr.add rdq(V, rdq(V, X.cpu.gpr.rdi)) i)))
    (hl : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsp i))
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (hra : rdq(V, X.cpu.gpr.rsp) = e₂.add j₂)
    (kn : ¬ aOk V X.cpu.gpr.rdi → ∀ (Z : State) (t' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V →
      Z.cpu.rip = e₂.add j₂ → Z.cpu.gpr = { X.cpu.gpr with rax := 0#64, rsp := X.cpu.gpr.rsp + 8 } →
      GoG prof L o gev gP gE Z t')
    (kf : aOk V X.cpu.gpr.rdi → ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y → Agree F Y.proc.mm.mem V →
      Y.cpu.rip = Sea.sea_at → Y.cpu.gpr = aG V X.cpu.gpr → GoG prof L o gev gP gE Y t') :
    GoG prof L o gev gP gE X t := by
  refine (c_0 prof).run c hin (fun j' g' _ V' => V' = V ∧
      ((j' = 28 ∧ g' = X.cpu.gpr ∧ ¬ aOk V X.cpu.gpr.rdi) ∨ (j' = 48 ∧ g' = aG V X.cpu.gpr ∧ aOk V X.cpu.gpr.rdi)))
    hK hA (by rw [addr_add_zero]; exact hrip)
    (vc_0 f17 f18 f19 f8 fp (fun hn _ => ⟨rfl, Or.inl ⟨rfl, rfl, hn⟩⟩) (fun hy _ => ⟨rfl, Or.inr ⟨rfl, rfl, hy⟩⟩)) ?_
  rintro j' g fl V₁ ⟨rfl, h⟩ Y t₁ hKY hAY hrY hgY -
  rcases h with ⟨rfl, rfl, hn⟩ | ⟨rfl, rfl, hy⟩
  · -- `xor eax, eax; ret`
    refine (c_28 prof).run c hin (fun j' g' _ V' => j' = 30 ∧ g' = { X.cpu.gpr with rax := 0#64 } ∧ V' = V)
      hKY hAY hrY (by rw [hgY]; exact vc_28) ?_
    rintro j' g fl V₂ ⟨rfl, rfl, hV₂⟩ U t₂ hKU hAU hrU hgU -
    subst V₂
    have hsU : U.cpu.gpr.rsp = X.cpu.gpr.rsp := by rw [hgU]
    refine c.s_ret hKU hAU hin (lt_len (by decide)) hrU (ret_30 _) (by rw [hsU]; exact hl) hin₂ h₂
      (by rw [hsU]; exact hra) ?_
    rintro Z t₃ hKZ hAZ ⟨hrZ, hgZ⟩
    refine kn hn Z t₃ hKZ hAZ hrZ ?_
    rw [hgZ, hgU]
    try rfl
  · -- the jump to `StringsAreEqual_Ascii`
    refine c.s_jmp_x hKY hAY hin (lt_len (by decide)) hrY (jmp_48 _) hinS (Sea.lt_len (j := 0) (by decide))
      (by decide) ?_
    rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
    exact kf hy Y₂ t₂ hK₂ hA₂ (by rw [hr₂, addr_add_zero]) (by rw [hg₂, hgY])

end FV7z.Aaa
