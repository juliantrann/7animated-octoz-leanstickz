import FV7z.Aeq.Holds
import FV7z.Ecq.Tail
/-!
# `CArchiveExtractCallback::QueryInterface`: the `AddRef`s and the returns (PLAN.md §M, M1)

- `add_52`, `add_158`: `add dword [rdi + 0x38], 1` (`AddRef` inline); `ret_58`, `ret_162`, `ret_366`: `ret`.
- `Vadd`: `FV7z.Ecq`'s.
- `tail52`: from 52 (`AddRef`, `xor eax, eax`, `ret`) back to the caller with `S_OK`.
- `tail158`: from 158 (`AddRef`, `ret`; `rax` already 0) back to the caller.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
open FV7z.Ecq (Vadd)
namespace FV7z.Aeq

def padd : List Byte := [0x83, 0x47, 0x38, 0x01]
theorem padd_0 : ∀ feat, Dec feat padd 0 (FV7z.mk .add 32 [.mem (mbd 7 56 32), .imm 32 1] 4) := by dec_rfl
theorem w_52 : padd <+: aeq.drop 52 := by decide +kernel
theorem w_158 : padd <+: aeq.drop 158 := by decide +kernel
/-- `add dword [rdi + 0x38], 1`. -/
theorem add_52 (feat : Features) : Dec feat aeq 52 (FV7z.mk .add 32 [.mem (mbd 7 56 32), .imm 32 1] 4) :=
  Dec.shift (j := 52) (k := 0) (padd_0 feat) w_52 (Nat.zero_le _)
/-- `add dword [rdi + 0x38], 1`. -/
theorem add_158 (feat : Features) : Dec feat aeq 158 (FV7z.mk .add 32 [.mem (mbd 7 56 32), .imm 32 1] 4) :=
  Dec.shift (j := 158) (k := 0) (padd_0 feat) w_158 (Nat.zero_le _)

def pret : List Byte := [0xc3]
theorem pret_0 : ∀ feat, Dec feat pret 0 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem w_58 : pret <+: aeq.drop 58 := by decide +kernel
theorem w_162 : pret <+: aeq.drop 162 := by decide +kernel
theorem w_366 : pret <+: aeq.drop 366 := by decide +kernel
theorem ret_58 (feat : Features) : Dec feat aeq 58 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 58) (k := 0) (pret_0 feat) w_58 (Nat.zero_le _)
theorem ret_162 (feat : Features) : Dec feat aeq 162 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 162) (k := 0) (pret_0 feat) w_162 (Nat.zero_le _)
theorem ret_366 (feat : Features) : Dec feat aeq 366 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 366) (k := 0) (pret_0 feat) w_366 (Nat.zero_le _)

variable {F : Footprint} {Wl : List Rgn} {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State}
  {o : Oracle} {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}

/-- From 52: `AddRef` inline, `xor eax, eax`, `ret`: back to the caller with `rax` = `S_OK`, `rsp` 8 up. -/
theorem tail52 (c : Seg prof F Wl L s₀ o) (hin : CodeIn L aeq_at aeq) {V : Addr → Byte} {X : State} {t : Nat}
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = aeq_at.add 52)
    (hst : ∀ i < 4, Foot Wl (Addr.add (X.cpu.gpr.rdi + 56#64) i))
    (hl : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsp i))
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (hra : ofBytesLE 64 ((byteAddrs X.cpu.gpr.rsp 8).map (Vadd V (X.cpu.gpr.rdi + 56#64))) = e₂.add j₂)
    (k : ∀ (Z : State) (t' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem (Vadd V (X.cpu.gpr.rdi + 56#64)) →
      Z.cpu.rip = e₂.add j₂ → Z.cpu.gpr = ({ X.cpu.gpr with rax := 0#64 }).set 4 (X.cpu.gpr.rsp + 8) →
      GoG prof L o gev gP gE Z t') :
    GoG prof L o gev gP gE X t := by
  have e : eaD X 7 56 = X.cpu.gpr.rdi + 56#64 := rfl
  refine c.s_add_mi32 hK hA hin (lt_len (by decide)) hrip (add_52 _) (by rw [e]; exact hst) ?_
  rintro Y t₁ hK₁ hA₁ ⟨hr₁, hg₁⟩
  rw [e] at hA₁
  refine (c_56 prof).run c hin
    (fun j' g' _ V' => j' = 58 ∧ g' = { Y.cpu.gpr with rax := 0#64 } ∧ V' = Vadd V (X.cpu.gpr.rdi + 56#64))
    hK₁ hA₁ hr₁ (vc_56 fun _ => ⟨rfl, rfl, rfl⟩) ?_
  rintro j' g fl V₂ ⟨rfl, rfl, rfl⟩ Y₂ t₂ hK₂ hA₂ hr₂ hg₂ -
  refine c.s_ret hK₂ hA₂ hin (lt_len (by decide)) hr₂ (ret_58 _) (by rw [hg₂, hg₁]; exact hl) hin₂ h₂
    (by rw [hg₂, hg₁]; exact hra) ?_
  rintro Z t' hKZ hAZ ⟨hrZ, hgZ⟩
  refine k Z t' hKZ hAZ hrZ ?_
  rw [hgZ, hg₂, hg₁]
  try rfl

/-- From 158: `AddRef` inline, `ret` (`rax` already `S_OK`): back to the caller, `rsp` 8 up. -/
theorem tail158 (c : Seg prof F Wl L s₀ o) (hin : CodeIn L aeq_at aeq) {V : Addr → Byte} {X : State} {t : Nat}
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = aeq_at.add 158)
    (hst : ∀ i < 4, Foot Wl (Addr.add (X.cpu.gpr.rdi + 56#64) i))
    (hl : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsp i))
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (hra : ofBytesLE 64 ((byteAddrs X.cpu.gpr.rsp 8).map (Vadd V (X.cpu.gpr.rdi + 56#64))) = e₂.add j₂)
    (k : ∀ (Z : State) (t' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem (Vadd V (X.cpu.gpr.rdi + 56#64)) →
      Z.cpu.rip = e₂.add j₂ → Z.cpu.gpr = X.cpu.gpr.set 4 (X.cpu.gpr.rsp + 8) → GoG prof L o gev gP gE Z t') :
    GoG prof L o gev gP gE X t := by
  have e : eaD X 7 56 = X.cpu.gpr.rdi + 56#64 := rfl
  refine c.s_add_mi32 hK hA hin (lt_len (by decide)) hrip (add_158 _) (by rw [e]; exact hst) ?_
  rintro Y t₁ hK₁ hA₁ ⟨hr₁, hg₁⟩
  rw [e] at hA₁
  refine c.s_ret hK₁ hA₁ hin (lt_len (by decide)) hr₁ (ret_162 _) (by rw [hg₁]; exact hl) hin₂ h₂
    (by rw [hg₁]; exact hra) ?_
  rintro Z t' hKZ hAZ ⟨hrZ, hgZ⟩
  refine k Z t' hKZ hAZ hrZ ?_
  rw [hgZ, hg₁]

end FV7z.Aeq
