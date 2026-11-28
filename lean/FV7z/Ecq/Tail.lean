import FV7z.Ecq.Loop1
import FV7z.Lemmas.Lock2
/-!
# `CExtractCallbackConsole::QueryInterface`: the `AddRef`s and the returns (PLAN.md §M, M1)

- `add_48`, `add_158`: `add dword [rdi + 0x138], 1` (`AddRef` inline); `ret_57`, `ret_165`, `ret_278`: `ret`.
- `Vadd V a`: the bytes `V` with the dword at `a` one more.
- `tail48`: from 48 (`AddRef`, `xor eax, eax`, `ret`) back to the caller with `S_OK`.
- `tail158`: from 158 (`AddRef`, `ret`; `rax` already 0) back to the caller.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Ecq

def padd : List Byte := [0x83, 0x87, 0x38, 0x01, 0x00, 0x00, 0x01]
theorem padd_0 : ∀ feat, Dec feat padd 0 (FV7z.mk .add 32 [.mem (mbd 7 312 32), .imm 32 1] 7) := by dec_rfl
theorem w_48 : padd <+: ecq.drop 48 := by decide +kernel
theorem w_158 : padd <+: ecq.drop 158 := by decide +kernel
/-- `add dword [rdi + 0x138], 1`. -/
theorem add_48 (feat : Features) : Dec feat ecq 48 (FV7z.mk .add 32 [.mem (mbd 7 312 32), .imm 32 1] 7) :=
  Dec.shift (j := 48) (k := 0) (padd_0 feat) w_48 (Nat.zero_le _)
/-- `add dword [rdi + 0x138], 1`. -/
theorem add_158 (feat : Features) : Dec feat ecq 158 (FV7z.mk .add 32 [.mem (mbd 7 312 32), .imm 32 1] 7) :=
  Dec.shift (j := 158) (k := 0) (padd_0 feat) w_158 (Nat.zero_le _)

def pret : List Byte := [0xc3]
theorem pret_0 : ∀ feat, Dec feat pret 0 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem w_57 : pret <+: ecq.drop 57 := by decide +kernel
theorem w_165 : pret <+: ecq.drop 165 := by decide +kernel
theorem w_278 : pret <+: ecq.drop 278 := by decide +kernel
theorem ret_57 (feat : Features) : Dec feat ecq 57 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 57) (k := 0) (pret_0 feat) w_57 (Nat.zero_le _)
theorem ret_165 (feat : Features) : Dec feat ecq 165 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 165) (k := 0) (pret_0 feat) w_165 (Nat.zero_le _)
theorem ret_278 (feat : Features) : Dec feat ecq 278 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 278) (k := 0) (pret_0 feat) w_278 (Nat.zero_le _)

/-- The bytes `V` with the dword at `a` one more. -/
abbrev Vadd (V : Addr → Byte) (a : Addr) : Addr → Byte :=
  Vst V a (toBytesLE (ofBytesLE 32 ((byteAddrs a 4).map V) + BitVec.ofNat 32 1) 4)

variable {F : Footprint} {Wl : List Rgn} {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State}
  {o : Oracle} {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}

/-- From 48: `AddRef` inline, `xor eax, eax`, `ret`: back to the caller with `rax` = `S_OK`, `rsp` 8 up. -/
theorem tail48 (c : Seg prof F Wl L s₀ o) (hin : CodeIn L ecq_at ecq) {V : Addr → Byte} {X : State} {t : Nat}
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = ecq_at.add 48)
    (hst : ∀ i < 4, Foot Wl (Addr.add (X.cpu.gpr.rdi + 312#64) i))
    (hl : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsp i))
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (hra : ofBytesLE 64 ((byteAddrs X.cpu.gpr.rsp 8).map (Vadd V (X.cpu.gpr.rdi + 312#64))) = e₂.add j₂)
    (k : ∀ (Z : State) (t' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem (Vadd V (X.cpu.gpr.rdi + 312#64)) →
      Z.cpu.rip = e₂.add j₂ → Z.cpu.gpr = ({ X.cpu.gpr with rax := 0#64 }).set 4 (X.cpu.gpr.rsp + 8) →
      GoG prof L o gev gP gE Z t') :
    GoG prof L o gev gP gE X t := by
  have e : eaD X 7 312 = X.cpu.gpr.rdi + 312#64 := rfl
  refine c.s_add_mi32 hK hA hin (lt_len (by decide)) hrip (add_48 _) (by rw [e]; exact hst) ?_
  rintro Y t₁ hK₁ hA₁ ⟨hr₁, hg₁⟩
  rw [e] at hA₁
  refine (c_55 prof).run c hin
    (fun j' g' _ V' => j' = 57 ∧ g' = { Y.cpu.gpr with rax := 0#64 } ∧ V' = Vadd V (X.cpu.gpr.rdi + 312#64))
    hK₁ hA₁ hr₁ (vc_55 fun _ => ⟨rfl, rfl, rfl⟩) ?_
  rintro j' g fl V₂ ⟨rfl, rfl, rfl⟩ Y₂ t₂ hK₂ hA₂ hr₂ hg₂ -
  refine c.s_ret hK₂ hA₂ hin (lt_len (by decide)) hr₂ (ret_57 _) (by rw [hg₂, hg₁]; exact hl) hin₂ h₂
    (by rw [hg₂, hg₁]; exact hra) ?_
  rintro Z t' hKZ hAZ ⟨hrZ, hgZ⟩
  refine k Z t' hKZ hAZ hrZ ?_
  rw [hgZ, hg₂, hg₁]
  try rfl

/-- From 158: `AddRef` inline, `ret` (`rax` already `S_OK`): back to the caller, `rsp` 8 up. -/
theorem tail158 (c : Seg prof F Wl L s₀ o) (hin : CodeIn L ecq_at ecq) {V : Addr → Byte} {X : State} {t : Nat}
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = ecq_at.add 158)
    (hst : ∀ i < 4, Foot Wl (Addr.add (X.cpu.gpr.rdi + 312#64) i))
    (hl : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsp i))
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (hra : ofBytesLE 64 ((byteAddrs X.cpu.gpr.rsp 8).map (Vadd V (X.cpu.gpr.rdi + 312#64))) = e₂.add j₂)
    (k : ∀ (Z : State) (t' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem (Vadd V (X.cpu.gpr.rdi + 312#64)) →
      Z.cpu.rip = e₂.add j₂ → Z.cpu.gpr = X.cpu.gpr.set 4 (X.cpu.gpr.rsp + 8) → GoG prof L o gev gP gE Z t') :
    GoG prof L o gev gP gE X t := by
  have e : eaD X 7 312 = X.cpu.gpr.rdi + 312#64 := rfl
  refine c.s_add_mi32 hK hA hin (lt_len (by decide)) hrip (add_158 _) (by rw [e]; exact hst) ?_
  rintro Y t₁ hK₁ hA₁ ⟨hr₁, hg₁⟩
  rw [e] at hA₁
  refine c.s_ret hK₁ hA₁ hin (lt_len (by decide)) hr₁ (ret_165 _) (by rw [hg₁]; exact hl) hin₂ h₂
    (by rw [hg₁]; exact hra) ?_
  rintro Z t' hKZ hAZ ⟨hrZ, hgZ⟩
  refine k Z t' hKZ hAZ hrZ ?_
  rw [hgZ, hg₁]

end FV7z.Ecq
