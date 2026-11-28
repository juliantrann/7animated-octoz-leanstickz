import FV7z.Upl.Cuts
import FV7z.Uc4.Code
import FV7z.Uc4.Blocks
import FV7z.Lemmas.LeafRet
import FV7z.Lemmas.FnFar
import FV7z.Lemmas.Lock2
/-!
# `operator+ (const UString &, const UString &)` (PLAN.md §M, M1)

7-Zip 26.06's `operator+ (const UString &s1, const UString &s2)` at `0x44d330` in `7zzs` (`CPP/Common/MyString.cpp`),
the result's address in `rdi`, `s1` in `rsi`, `s2` in `rdx`: `push r12; mov r9d, [rsi + 8]; mov r12, rdi;
mov r8d, [rdx + 8]; mov rcx, [rdx]; mov rsi, [rsi]; mov edx, r9d`, the `call` (26) of
`UString::UString (s1._chars, s1._len, s2._chars, s2._len)` (`Uc4.uc4_at`), then `mov rax, r12; pop r12; ret` (36).
`AString`'s `operator+` (`FV7z/Apl`) has the same bytes; this is its proof with the callee renamed.

The callee is a hypothesis (`kf`), as in `FV7z/Uct/Holds.lean`: a continuation at its entry, given the run from its
return (`upl_at + 31`, `rsp` 8 below the entry's, `r12` = the result's address as the ABI keeps it, the saved `r12` and
the return address left as they were, and the callee's own post `Pc`) to the return address (`kr`). The loads come
after the `push`, so the arguments are read from the bytes `V0` (the caller's, with `r12` pushed).

- `V0`, `gC`: the bytes and the registers at the `call`.
- `vc_0`, `vc_31`: the verification conditions of the two pieces.
- `upl_ok`: from the entry, through the callee, to the return address with `rax` = the result's address and `r12`,
  `rsp` restored.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Upl

/-- The `call` to `UString::UString (const char *, unsigned, const char *, unsigned)`. -/
def pcall : List Byte := [0xe8, 0x91, 0xff, 0xff, 0xff]
theorem pcall_0 : ∀ feat, Dec feat pcall 0 (FV7z.mk .call 64 [.rel 18446744073709551505] 5) := by dec_rfl
theorem wc_26 : pcall <+: upl.drop 26 := by decide +kernel
theorem call_26 (feat : Features) : Dec feat upl 26 (FV7z.mk .call 64 [.rel 18446744073709551505] 5) :=
  Dec.shift (j := 26) (k := 0) (pcall_0 feat) wc_26 (Nat.zero_le _)
theorem tgt_26 : upl_at.add (26 + 5) + BitVec.ofNat 64 18446744073709551505 = Uc4.uc4_at.add 0 := by decide

/-- The `ret`. -/
def pret : List Byte := [0xc3]
theorem pret_0 : ∀ feat, Dec feat pret 0 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem w_36 : pret <+: upl.drop 36 := by decide +kernel
theorem ret_36 (feat : Features) : Dec feat upl 36 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 36) (k := 0) (pret_0 feat) w_36 (Nat.zero_le _)

/-- The bytes at the `call`: `r12` pushed. -/
abbrev V0 (V : Addr → Byte) (g : Gprs) : Addr → Byte := Vst V (g.rsp - 8) (toBytesLE g.r12 8)

/-- The registers at the `call`, the loads from `W`: `rsi`, `edx` = `s1._chars`, `s1._len`, `rcx`, `r8d` =
`s2._chars`, `s2._len`, `r9d` = `s1._len`, `r12` = the result's address, `r12` pushed. -/
abbrev gC (g : Gprs) (W : Addr → Byte) : Gprs :=
  { g with
      rcx := rdq(W, g.rdx),
      rdx := BitVec.setWidth 64 rdd(W, g.rsi + 8#64),
      rsp := g.rsp - 8,
      rsi := rdq(W, g.rsi),
      r8 := BitVec.setWidth 64 rdd(W, g.rdx + 8#64),
      r9 := BitVec.setWidth 64 rdd(W, g.rsi + 8#64),
      r12 := g.rdi }

variable {F : Footprint} {Wl : List Rgn}

/-- `push r12; mov r9d, [rsi + 8]; mov r12, rdi; mov r8d, [rdx + 8]; mov rcx, [rdx]; mov rsi, [rsi];
mov edx, r9d`. -/
theorem vc_0 {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (hs1 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8) i))
    (f1 : ∀ i < 4, Foot F.data (Addr.add (g.rsi + 8#64) i)) (f2 : ∀ i < 4, Foot F.data (Addr.add (g.rdx + 8#64) i))
    (f3 : ∀ i < 8, Foot F.data (Addr.add g.rdx i)) (f4 : ∀ i < 8, Foot F.data (Addr.add g.rsi i)) :
    W_0 F Wl (fun j' g' _ V' => j' = 26 ∧ g' = gC g (V0 V g) ∧ V' = V0 V g) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hs1 f1 f2 f3 f4 ⊢
  wpx [W_0, o0, gC, V0]
  all_goals repeat'
    first
    | exact rfl
    | assumption
    | exact trivial
    | apply And.intro
    | intro _

/-- Back from the callee: `mov rax, r12; pop r12` to the `ret` at 36. -/
theorem vc_31 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (hl : ∀ i < 8, Foot F.data (Addr.add g.rsp i))
    (h : ∀ fl, Q 36 { g with rax := g.r12, rsp := g.rsp + 8, r12 := rdq(V, g.rsp) } fl V) :
    W_31 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hl h ⊢
  wpx [W_31, o1]
  all_goals repeat' (first | exact h _ | assumption | exact trivial | apply And.intro | intro _)

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {X : State} {t : Nat} {V : Addr → Byte}

/-- `operator+ (s1, s2)` (the result's address `rdi`, `s1` = `rsi`, `s2` = `rdx`) from its entry. At the
constructor's entry the registers are `gC` (the loads from `V0`) with `rsp` 16 below the entry's and the bytes `V0`
with the return address into `operator+` pushed (`kf`); if the callee returns to `upl_at + 31` with `rsp` and `r12` as
at its entry and the saved `r12` and the return address of `operator+` as they were, the run reaches that return
address with `rax` = the result's address and `r12`, `rsp` restored (`kr`). -/
theorem upl_ok {Pc : State → (Addr → Byte) → Prop} (c : Seg prof F Wl L s₀ o) (hin : CodeIn L upl_at upl)
    (hinC : CodeIn L Uc4.uc4_at Uc4.uc4)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = upl_at)
    (hp : 16 ≤ X.cpu.gpr.rsp.toNat)
    (hs1 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8) i))
    (hs2 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 16) i))
    (hl : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsp i))
    (f1 : ∀ i < 4, Foot F.data (Addr.add (X.cpu.gpr.rsi + 8#64) i))
    (f2 : ∀ i < 4, Foot F.data (Addr.add (X.cpu.gpr.rdx + 8#64) i))
    (f3 : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rdx i)) (f4 : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsi i))
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (kf : ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y →
      Agree F Y.proc.mm.mem (Vst (V0 V X.cpu.gpr) (X.cpu.gpr.rsp - 16) (toBytesLE (upl_at.add 31) 8)) →
      Y.cpu.rip = Uc4.uc4_at.add 0 → Y.cpu.gpr = (gC X.cpu.gpr (V0 V X.cpu.gpr)).set 4 (X.cpu.gpr.rsp - 16) →
      (∀ (Z : State) (V' : Addr → Byte) (t'' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V' →
        Z.cpu.rip = upl_at.add 31 → Z.cpu.gpr.rsp = X.cpu.gpr.rsp - 8 → Z.cpu.gpr.r12 = X.cpu.gpr.rdi →
        rdq(V', X.cpu.gpr.rsp - 8) = X.cpu.gpr.r12 → rdq(V', X.cpu.gpr.rsp) = e₂.add j₂ →
        Pc Z V' → GoG prof L o gev gP gE Z t'') →
      GoG prof L o gev gP gE Y t')
    (kr : ∀ (Z : State) (V' : Addr → Byte) (Z' : State) (t' : Nat), Pc Z V' → KeptW Wl s₀ Z' →
      Agree F Z'.proc.mm.mem V' → Z'.cpu.rip = e₂.add j₂ →
      Z'.cpu.gpr = { Z.cpu.gpr with rax := X.cpu.gpr.rdi, rsp := X.cpu.gpr.rsp + 8, r12 := X.cpu.gpr.r12 } →
      GoG prof L o gev gP gE Z' t') :
    GoG prof L o gev gP gE X t := by
  have hlt := X.cpu.gpr.rsp.isLt
  have tn8 : (X.cpu.gpr.rsp - 8).toNat = X.cpu.gpr.rsp.toNat - 8 := by rw [BitVec.toNat_sub]; simp <;> omega
  have tn16 : (X.cpu.gpr.rsp - 16).toNat = X.cpu.gpr.rsp.toNat - 16 := by rw [BitVec.toNat_sub]; simp <;> omega
  have e16 : X.cpu.gpr.rsp - 8 - 8 = X.cpu.gpr.rsp - 16 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, tn8, tn16]
    simp <;> omega
  have e8 : X.cpu.gpr.rsp - 8 + 8 = X.cpu.gpr.rsp := BitVec.sub_add_cancel _ _
  have hrip' : X.cpu.rip = upl_at.add 0 := by rw [addr_add_zero]; exact hrip
  -- to the `call`
  refine (c_0 prof).run c hin (fun j' g' _ V' => j' = 26 ∧ g' = gC X.cpu.gpr (V0 V X.cpu.gpr) ∧
      V' = V0 V X.cpu.gpr) hK hA hrip' (vc_0 hs1 f1 f2 f3 f4) ?_
  rintro j' g fl V₁ ⟨rfl, rfl, hV₁⟩ Y t₁ hKY hAY hrY hgY -
  subst V₁
  have hsY : Y.cpu.gpr.rsp = X.cpu.gpr.rsp - 8 := by rw [hgY]
  have hst : ∀ i < 8, Foot Wl (Addr.add (Y.cpu.gpr.rsp - 8) i) := by rw [hsY, e16]; exact hs2
  refine c.s_call_x hKY hAY hin (lt_len (by decide)) hrY (call_26 _) hinC (tgt := 0) (Uc4.lt_len (by decide))
    tgt_26 hst ?_
  rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
  rw [hsY, e16] at hA₂
  have hg₂' : Y₂.cpu.gpr = (gC X.cpu.gpr (V0 V X.cpu.gpr)).set 4 (X.cpu.gpr.rsp - 16) := by
    rw [hg₂, hgY]
    exact congrArg (fun v => (gC X.cpu.gpr (V0 V X.cpu.gpr)).set 4 v) e16
  refine kf Y₂ t₂ hK₂ hA₂ hr₂ hg₂' ?_
  -- back from the callee
  intro Z V' t'' hKZ hAZ hrZ hzs hz12 hb hr' hPc
  have h8 : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rsp - 8) i) := fun i hi => c.hws _ (hs1 i hi)
  refine (c_31 prof).run c hin (fun j' g' _ V'' => j' = 36 ∧
      g' = { Z.cpu.gpr with rax := X.cpu.gpr.rdi, rsp := X.cpu.gpr.rsp, r12 := X.cpu.gpr.r12 } ∧ V'' = V')
    hKZ hAZ hrZ (vc_31 (by rw [hzs]; exact h8) fun _ => ⟨rfl, by rw [hz12, hzs, e8, hb], rfl⟩) ?_
  rintro j' g fl V₂ ⟨rfl, rfl, hV₂⟩ U t₃ hKU hAU hrU hgU -
  subst V₂
  have hsU : U.cpu.gpr.rsp = X.cpu.gpr.rsp := by rw [hgU]
  refine c.s_ret hKU hAU hin (lt_len (by decide)) hrU (ret_36 _) (by rw [hsU]; exact hl) hin₂ h₂
    (by rw [hsU]; exact hr') ?_
  rintro Z' t₄ hKZ' hAZ' ⟨hrZ', hgZ'⟩
  refine kr Z V' Z' t₄ hPc hKZ' hAZ' hrZ' ?_
  rw [hgZ', hgU]
  try rfl

end FV7z.Upl
