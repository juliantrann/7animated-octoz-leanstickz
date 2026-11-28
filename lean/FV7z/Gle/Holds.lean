import FV7z.Gle.Cuts
import FV7z.Erl.Code
import FV7z.Lemmas.LeafRet
import FV7z.Lemmas.Lock2
/-!
# `GetLastError ()` (PLAN.md §M, M1)

7-Zip 26.06's `GetLastError ()` at `0x5a0200` in `7zzs` (`CPP/Common/MyWindows.cpp`), `return errno`: `sub rsp, 8`,
the `call` at 8 to `__errno_location` (`Erl.erl_at`), `mov eax, [rax]; add rsp, 8; ret` (19).

`__errno_location` (glibc 2.31: `rax` = the thread pointer's `errno`) is a hypothesis, as the callees of
`FV7z/Ucu/Holds.lean`: `ke` is a continuation at its entry, given the run from its return (`rsp` 8 below the entry's,
the return address as it was) and its own post `Pe`; `pe`: the 4 bytes at the `rax` it returns readable.

- `vc_0`, `vc_13`: the verification conditions of the pieces.
- `gle_ok`: from the entry, through `__errno_location`, to the return address with `rax` the 4 bytes at its result.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Gle

/-- The `call` to `__errno_location`. -/
def pce : List Byte := [0xe8, 0x93, 0xfc, 0x05, 0x00]
theorem pce_0 : ∀ feat, Dec feat pce 0 (FV7z.mk .call 64 [.rel 392339] 5) := by dec_rfl
theorem wc_8 : pce <+: gle.drop 8 := by decide +kernel
theorem call_8 (feat : Features) : Dec feat gle 8 (FV7z.mk .call 64 [.rel 392339] 5) :=
  Dec.shift (j := 8) (k := 0) (pce_0 feat) wc_8 (Nat.zero_le _)
theorem tgt_8 : gle_at.add (8 + 5) + BitVec.ofNat 64 392339 = Erl.erl_at.add 0 := by decide

theorem erl_lt : 0 < Erl.erl.length := by rw [Erl.erl_length]; decide

/-- The `ret`. -/
def pret : List Byte := [0xc3]
theorem pret_0 : ∀ feat, Dec feat pret 0 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem w_19 : pret <+: gle.drop 19 := by decide +kernel
theorem ret_19 (feat : Features) : Dec feat gle 19 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 19) (k := 0) (pret_0 feat) w_19 (Nat.zero_le _)

variable {F : Footprint} {Wl : List Rgn}

/-- `sub rsp, 8` to the `call` at 8. -/
theorem vc_0 {g : Gprs} {f : Rflags} {V : Addr → Byte} :
    W_0 F Wl (fun j' g' _ V' => j' = 8 ∧ g' = { g with rsp := g.rsp - 8 } ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_0, o0]
  all_goals repeat'
    first
    | exact rfl
    | exact trivial
    | apply And.intro
    | intro _

/-- Back from `__errno_location`: `mov eax, [rax]; add rsp, 8` to the `ret` at 19. -/
theorem vc_13 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (fa : ∀ i < 4, Foot F.data (Addr.add g.rax i))
    (h : ∀ fl, Q 19 { g with rax := (rdd(V, g.rax)).setWidth 64, rsp := g.rsp + 8#64 } fl V) :
    W_13 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at fa h ⊢
  wpx [W_13, o1]
  all_goals repeat' (first | exact h _ | assumption | exact trivial | apply And.intro | intro _)

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {X : State} {t : Nat} {V : Addr → Byte}

/-- `GetLastError ()` from its entry. At `__errno_location`'s entry the registers are the entry's with `rsp` 16
below, the bytes with the return address pushed (`ke`); back at `gle_at + 13` (`Pe`), at the return address with
`rax` the 4 bytes at the `rax` `__errno_location` returned (`kr`). -/
theorem gle_ok {Pe : State → (Addr → Byte) → Prop}
    (c : Seg prof F Wl L s₀ o) (hin : CodeIn L gle_at gle) (hinE : CodeIn L Erl.erl_at Erl.erl)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = gle_at)
    (hp : 16 ≤ X.cpu.gpr.rsp.toNat)
    (hs2 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 16) i))
    (hl : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsp i))
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (ke : ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y →
      Agree F Y.proc.mm.mem (Vst V (X.cpu.gpr.rsp - 16) (toBytesLE (gle_at.add 13) 8)) →
      Y.cpu.rip = Erl.erl_at → Y.cpu.gpr = { X.cpu.gpr with rsp := X.cpu.gpr.rsp - 8 }.set 4 (X.cpu.gpr.rsp - 16) →
      (∀ (Z : State) (V₁ : Addr → Byte) (t'' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V₁ →
        Z.cpu.rip = gle_at.add 13 → Z.cpu.gpr.rsp = X.cpu.gpr.rsp - 8 → rdq(V₁, X.cpu.gpr.rsp) = e₂.add j₂ →
        Pe Z V₁ → GoG prof L o gev gP gE Z t'') →
      GoG prof L o gev gP gE Y t')
    (pe : ∀ (Z : State) (V₁ : Addr → Byte), Pe Z V₁ → ∀ i < 4, Foot F.data (Addr.add Z.cpu.gpr.rax i))
    (kr : ∀ (Z : State) (V₁ : Addr → Byte) (Z' : State) (t' : Nat), Pe Z V₁ → KeptW Wl s₀ Z' →
      Agree F Z'.proc.mm.mem V₁ → Z'.cpu.rip = e₂.add j₂ →
      Z'.cpu.gpr = { Z.cpu.gpr with rax := (rdd(V₁, Z.cpu.gpr.rax)).setWidth 64, rsp := X.cpu.gpr.rsp + 8 } →
      GoG prof L o gev gP gE Z' t') :
    GoG prof L o gev gP gE X t := by
  have hlt := X.cpu.gpr.rsp.isLt
  have tn8 : (X.cpu.gpr.rsp - 8).toNat = X.cpu.gpr.rsp.toNat - 8 := by rw [BitVec.toNat_sub]; simp <;> omega
  have tn16 : (X.cpu.gpr.rsp - 16).toNat = X.cpu.gpr.rsp.toNat - 16 := by rw [BitVec.toNat_sub]; simp <;> omega
  have c16 : X.cpu.gpr.rsp - 8 - 8 = X.cpu.gpr.rsp - 16 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, tn8, tn16]
    simp <;> omega
  have e8 : X.cpu.gpr.rsp - 8 + 8#64 = X.cpu.gpr.rsp := BitVec.sub_add_cancel _ _
  have hrip' : X.cpu.rip = gle_at.add 0 := by rw [addr_add_zero]; exact hrip
  -- to the `call` of `__errno_location`
  refine (c_0 prof).run c hin (fun j' g' _ V' => j' = 8 ∧ g' = { X.cpu.gpr with rsp := X.cpu.gpr.rsp - 8 } ∧
      V' = V) hK hA hrip' vc_0 ?_
  rintro j' g fl V₁ ⟨rfl, rfl, hV₁⟩ Y t₁ hKY hAY hrY hgY -
  subst V₁
  have hsY : Y.cpu.gpr.rsp = X.cpu.gpr.rsp - 8 := by rw [hgY] <;> rfl
  have hst : ∀ i < 8, Foot Wl (Addr.add (Y.cpu.gpr.rsp - 8) i) := by rw [hsY, c16]; exact hs2
  refine c.s_call_x hKY hAY hin (lt_len (by decide)) hrY (call_8 _) hinE (tgt := 0) erl_lt tgt_8 hst ?_
  rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
  rw [hsY, c16] at hA₂
  have hg₂' : Y₂.cpu.gpr = { X.cpu.gpr with rsp := X.cpu.gpr.rsp - 8 }.set 4 (X.cpu.gpr.rsp - 16) := by
    rw [hg₂, hsY, c16, hgY]
  refine ke Y₂ t₂ hK₂ hA₂ (by rw [hr₂, addr_add_zero]) hg₂' ?_
  -- back from `__errno_location`
  intro Z V₁ t₃ hKZ hAZ hrZ hzs hra hPe
  have hz8 : Z.cpu.gpr.rsp + 8#64 = X.cpu.gpr.rsp := by rw [hzs]; exact e8
  refine (c_13 prof).run c hin (fun j' g' _ V' => j' = 19 ∧
      g' = { Z.cpu.gpr with rax := (rdd(V₁, Z.cpu.gpr.rax)).setWidth 64, rsp := X.cpu.gpr.rsp } ∧ V' = V₁)
    hKZ hAZ hrZ (vc_13 (pe Z V₁ hPe) fun _ => ⟨rfl, by rw [hz8], rfl⟩) ?_
  rintro j' g fl V₂ ⟨rfl, rfl, hV₂⟩ U t₄ hKU hAU hrU hgU -
  subst V₂
  have hsU : U.cpu.gpr.rsp = X.cpu.gpr.rsp := by rw [hgU] <;> rfl
  refine c.s_ret hKU hAU hin (lt_len (by decide)) hrU (ret_19 _) (by rw [hsU]; exact hl) hin₂ h₂
    (by rw [hsU]; exact hra) ?_
  rintro Z' t₅ hKZ' hAZ' ⟨hrZ', hgZ'⟩
  refine kr Z V₁ Z' t₅ hPe hKZ' hAZ' hrZ' ?_
  rw [hgZ', hgU]
  try rfl

end FV7z.Gle
