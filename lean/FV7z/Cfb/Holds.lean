import FV7z.Cfb.Cuts
import FV7z.Lemmas.LeafRet
import FV7z.Tun.Inv
/-!
# `CFileInfoBase::ClearBase` (PLAN.md §M, M1)

7-Zip 26.06's `NWindows::NFile::NFind::CFileInfoBase::ClearBase ()` at `0x4558d0` in `7zzs`
(`CPP/Windows/FileFind.cpp`; `objdump -d`): for the object at `p` = `rdi`, 0 in the 8 bytes at `p + 8 * i` for
`i` < 9, in the 4 bytes at `p + 72`, and in the 8 bytes at `p + 80`, `p + 88`, `p + 96`. No register is written. One
`ret` (106).

- `M`: the bytes after the stores; `vc_0`: from the entry to the `ret`.
- `cfb_ok`: from the entry to the return address.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Cfb

/-- The `ret`. -/
def pret : List Byte := [0xc3]
theorem pret_0 : ∀ feat, Dec feat pret 0 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem w_106 : pret <+: cfb.drop 106 := by decide +kernel
theorem ret_106 (feat : Features) : Dec feat cfb 106 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 106) (k := 0) (pret_0 feat) w_106 (Nat.zero_le _)

/-- The bytes after the stores into the object at `p`, in their order. -/
abbrev M (V : Addr → Byte) (p : Addr) : Addr → Byte :=
  Vst (Vst (Vst (Vst (Vst (Vst (Vst (Vst (Vst (Vst (Vst (Vst (Vst V
    p (toBytesLE 0#64 8))
    (p + 8#64) (toBytesLE 0#64 8))
    (p + 16#64) (toBytesLE 0#64 8))
    (p + 24#64) (toBytesLE 0#64 8))
    (p + 32#64) (toBytesLE 0#64 8))
    (p + 40#64) (toBytesLE 0#64 8))
    (p + 48#64) (toBytesLE 0#64 8))
    (p + 56#64) (toBytesLE 0#64 8))
    (p + 64#64) (toBytesLE 0#64 8))
    (p + 72#64) (toBytesLE 0#32 4))
    (p + 80#64) (toBytesLE 0#64 8))
    (p + 88#64) (toBytesLE 0#64 8))
    (p + 96#64) (toBytesLE 0#64 8)

/-- The object's 100 bytes in `Wl`, as the stores need them. -/
def Ws (Wl : List Rgn) (p : Addr) : Prop :=
  (∀ i < 8, Foot Wl (Addr.add p i)) ∧ (∀ i < 8, Foot Wl (Addr.add (p + 8#64) i)) ∧
  (∀ i < 8, Foot Wl (Addr.add (p + 16#64) i)) ∧ (∀ i < 8, Foot Wl (Addr.add (p + 24#64) i)) ∧
  (∀ i < 8, Foot Wl (Addr.add (p + 32#64) i)) ∧ (∀ i < 8, Foot Wl (Addr.add (p + 40#64) i)) ∧
  (∀ i < 8, Foot Wl (Addr.add (p + 48#64) i)) ∧ (∀ i < 8, Foot Wl (Addr.add (p + 56#64) i)) ∧
  (∀ i < 8, Foot Wl (Addr.add (p + 64#64) i)) ∧ (∀ i < 4, Foot Wl (Addr.add (p + 72#64) i)) ∧
  (∀ i < 8, Foot Wl (Addr.add (p + 80#64) i)) ∧ (∀ i < 8, Foot Wl (Addr.add (p + 88#64) i)) ∧
  (∀ i < 8, Foot Wl (Addr.add (p + 96#64) i))

variable {prof : Profile} {F : Footprint} {Wl : List Rgn} {L : List (Addr × List Byte)} {s₀ : State}
  {o : Oracle} {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {X : State} {t : Nat} {V : Addr → Byte}

/-- The stores, from the entry to the `ret`. -/
theorem vc_0 {g : Gprs} {f : Rflags} (hw : Ws Wl g.rdi) :
    wp F Wl o0 (fun g' _ V' => g' = g ∧ V' = M V g.rdi) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  obtain ⟨w0, w8, w16, w24, w32, w40, w48, w56, w64, w72, w80, w88, w96⟩ := hw
  dsimp only at w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 ⊢
  wpx [o0, M]
  all_goals first
  | exact ⟨w0, w8, w16, w24, w32, w40, w48, w56, w64, w72, w80, w88, w96⟩
  | exact ⟨w0, w8, w16, w24, w32, w40, w48, w56, w64, w72, w80, w88, w96, rfl, rfl⟩
  | (refine ⟨w0, w8, w16, w24, w32, w40, w48, w56, w64, w72, w80, w88, w96, ?_⟩; done)

/-- `CFileInfoBase::ClearBase ()` from its entry to the return address: the bytes `M` of the object at `rdi`, the
registers as at the entry but `rsp`. -/
theorem cfb_ok (c : Seg prof F Wl L s₀ o) (hin : CodeIn L cfb_at cfb) (hK : KeptW Wl s₀ X)
    (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = cfb_at) (hw : Ws Wl X.cpu.gpr.rdi)
    (hl : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsp i))
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (hra : rdq(M V X.cpu.gpr.rdi, X.cpu.gpr.rsp) = e₂.add j₂)
    (k : ∀ (Z : State) (t' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem (M V X.cpu.gpr.rdi) →
      Z.cpu.rip = e₂.add j₂ → Z.cpu.gpr = X.cpu.gpr.set 4 (X.cpu.gpr.rsp + 8) →
      GoG prof L o gev gP gE Z t') :
    GoG prof L o gev gP gE X t := by
  refine (c_0 prof).run c hin
    (fun j' g' _ V' => j' = 106 ∧ g' = X.cpu.gpr ∧ V' = M V X.cpu.gpr.rdi) hK hA
    (by rw [addr_add_zero]; exact hrip)
    (wp_mono o0 (fun _ _ _ h => ⟨rfl, h⟩) (vc_0 hw)) ?_
  rintro j' g fl V₁ ⟨rfl, rfl, hV₁⟩ Y t₁ hKY hAY hrY hgY -
  subst V₁
  have hspY : Y.cpu.gpr.rsp = X.cpu.gpr.rsp := by rw [hgY]
  refine c.s_ret hKY hAY hin (lt_len (by decide)) hrY (ret_106 _) (by rw [hspY]; exact hl) hin₂ h₂
    (by rw [hspY]; exact hra) ?_
  rintro Z t₂ hKZ hAZ ⟨hrZ, hgZ⟩
  exact k Z t₂ hKZ hAZ hrZ (by rw [hgZ, hspY, hgY])

end FV7z.Cfb
