import FV7z.Cdi.Cuts
import FV7z.Cpt.Holds
/-!
# `CDirItems::CDirItems` (PLAN.md §M, M1)

7-Zip 26.06's `CDirItems::CDirItems ()` at `0x5c0830` in `7zzs` (`CPP/7zip/UI/Common/DirItem.h`; `objdump -d`): for
the object at `p` = `rdi`, 0 in the 8 bytes at `p + 8 * i` for `i` < 8, in the 4 bytes at `p + 64`, in the byte at
`p + 68`, in the 8 bytes at `p + 72 + 8 * i` for `i` < 14, in the byte at `p + 184` and in the 8 bytes at `p + 192`
(the object's fields, all empty). No register is written. One `ret` (229).

- `M`: the bytes after the stores; `vc_0`: from the entry to the `ret`, the stores' bytes from the object's 200
  bytes in `Wl` (`Cpt.off_ft`).
- `cdi_ok`: from the entry to the return address.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Cdi

/-- The `ret`. -/
def pret : List Byte := [0xc3]
theorem pret_0 : ∀ feat, Dec feat pret 0 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem w_229 : pret <+: cdi.drop 229 := by decide +kernel
theorem ret_229 (feat : Features) : Dec feat cdi 229 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 229) (k := 0) (pret_0 feat) w_229 (Nat.zero_le _)

/-- The bytes after the stores into the object at `p`, in their order. -/
abbrev M (V : Addr → Byte) (p : Addr) : Addr → Byte :=
  Vst (Vst (Vst (Vst (Vst (Vst (Vst (Vst (Vst (Vst (Vst (Vst (Vst (
    Vst (Vst (Vst (Vst (Vst (Vst (Vst (Vst (Vst (Vst (Vst (Vst (Vst V
    p (toBytesLE 0#64 8))
    (p + 8#64) (toBytesLE 0#64 8))
    (p + 16#64) (toBytesLE 0#64 8))
    (p + 24#64) (toBytesLE 0#64 8))
    (p + 32#64) (toBytesLE 0#64 8))
    (p + 40#64) (toBytesLE 0#64 8))
    (p + 48#64) (toBytesLE 0#64 8))
    (p + 56#64) (toBytesLE 0#64 8))
    (p + 64#64) (toBytesLE 0#32 4))
    (p + 68#64) (toBytesLE 0#8 1))
    (p + 72#64) (toBytesLE 0#64 8))
    (p + 80#64) (toBytesLE 0#64 8))
    (p + 88#64) (toBytesLE 0#64 8))
    (p + 96#64) (toBytesLE 0#64 8))
    (p + 104#64) (toBytesLE 0#64 8))
    (p + 112#64) (toBytesLE 0#64 8))
    (p + 120#64) (toBytesLE 0#64 8))
    (p + 128#64) (toBytesLE 0#64 8))
    (p + 136#64) (toBytesLE 0#64 8))
    (p + 144#64) (toBytesLE 0#64 8))
    (p + 152#64) (toBytesLE 0#64 8))
    (p + 160#64) (toBytesLE 0#64 8))
    (p + 168#64) (toBytesLE 0#64 8))
    (p + 176#64) (toBytesLE 0#64 8))
    (p + 184#64) (toBytesLE 0#8 1))
    (p + 192#64) (toBytesLE 0#64 8)

variable {prof : Profile} {F : Footprint} {Wl : List Rgn} {L : List (Addr × List Byte)} {s₀ : State}
  {o : Oracle} {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {X : State} {t : Nat} {V : Addr → Byte}

/-- The stores, from the entry to the `ret`. -/
theorem vc_0 {g : Gprs} {f : Rflags} (hw : ∀ i < 200, Foot Wl (Addr.add g.rdi i)) :
    wp F Wl o0 (fun g' _ V' => g' = g ∧ V' = M V g.rdi) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hw ⊢
  have w0 : ∀ i < 8, Foot Wl (Addr.add rdi i) := Cpt.off_ft hw 0 (BitVec.add_zero _).symm (by decide)
  have w8 : ∀ i < 8, Foot Wl (Addr.add (rdi + 8#64) i) := Cpt.off_ft hw 8 rfl (by decide)
  have w16 : ∀ i < 8, Foot Wl (Addr.add (rdi + 16#64) i) := Cpt.off_ft hw 16 rfl (by decide)
  have w24 : ∀ i < 8, Foot Wl (Addr.add (rdi + 24#64) i) := Cpt.off_ft hw 24 rfl (by decide)
  have w32 : ∀ i < 8, Foot Wl (Addr.add (rdi + 32#64) i) := Cpt.off_ft hw 32 rfl (by decide)
  have w40 : ∀ i < 8, Foot Wl (Addr.add (rdi + 40#64) i) := Cpt.off_ft hw 40 rfl (by decide)
  have w48 : ∀ i < 8, Foot Wl (Addr.add (rdi + 48#64) i) := Cpt.off_ft hw 48 rfl (by decide)
  have w56 : ∀ i < 8, Foot Wl (Addr.add (rdi + 56#64) i) := Cpt.off_ft hw 56 rfl (by decide)
  have w64 : ∀ i < 4, Foot Wl (Addr.add (rdi + 64#64) i) := Cpt.off_ft hw 64 rfl (by decide)
  have w68 : ∀ i < 1, Foot Wl (Addr.add (rdi + 68#64) i) := Cpt.off_ft hw 68 rfl (by decide)
  have w72 : ∀ i < 8, Foot Wl (Addr.add (rdi + 72#64) i) := Cpt.off_ft hw 72 rfl (by decide)
  have w80 : ∀ i < 8, Foot Wl (Addr.add (rdi + 80#64) i) := Cpt.off_ft hw 80 rfl (by decide)
  have w88 : ∀ i < 8, Foot Wl (Addr.add (rdi + 88#64) i) := Cpt.off_ft hw 88 rfl (by decide)
  have w96 : ∀ i < 8, Foot Wl (Addr.add (rdi + 96#64) i) := Cpt.off_ft hw 96 rfl (by decide)
  have w104 : ∀ i < 8, Foot Wl (Addr.add (rdi + 104#64) i) := Cpt.off_ft hw 104 rfl (by decide)
  have w112 : ∀ i < 8, Foot Wl (Addr.add (rdi + 112#64) i) := Cpt.off_ft hw 112 rfl (by decide)
  have w120 : ∀ i < 8, Foot Wl (Addr.add (rdi + 120#64) i) := Cpt.off_ft hw 120 rfl (by decide)
  have w128 : ∀ i < 8, Foot Wl (Addr.add (rdi + 128#64) i) := Cpt.off_ft hw 128 rfl (by decide)
  have w136 : ∀ i < 8, Foot Wl (Addr.add (rdi + 136#64) i) := Cpt.off_ft hw 136 rfl (by decide)
  have w144 : ∀ i < 8, Foot Wl (Addr.add (rdi + 144#64) i) := Cpt.off_ft hw 144 rfl (by decide)
  have w152 : ∀ i < 8, Foot Wl (Addr.add (rdi + 152#64) i) := Cpt.off_ft hw 152 rfl (by decide)
  have w160 : ∀ i < 8, Foot Wl (Addr.add (rdi + 160#64) i) := Cpt.off_ft hw 160 rfl (by decide)
  have w168 : ∀ i < 8, Foot Wl (Addr.add (rdi + 168#64) i) := Cpt.off_ft hw 168 rfl (by decide)
  have w176 : ∀ i < 8, Foot Wl (Addr.add (rdi + 176#64) i) := Cpt.off_ft hw 176 rfl (by decide)
  have w184 : ∀ i < 1, Foot Wl (Addr.add (rdi + 184#64) i) := Cpt.off_ft hw 184 rfl (by decide)
  have w192 : ∀ i < 8, Foot Wl (Addr.add (rdi + 192#64) i) := Cpt.off_ft hw 192 rfl (by decide)
  wpx [o0, M]
  all_goals first
  | exact ⟨w0, w8, w16, w24, w32, w40, w48, w56, w64, w68, w72, w80, w88, w96, w104, w112, w120, w128, w136, w144,
    w152, w160, w168, w176, w184, w192⟩
  | exact ⟨w0, w8, w16, w24, w32, w40, w48, w56, w64, w68, w72, w80, w88, w96, w104, w112, w120, w128, w136, w144,
    w152, w160, w168, w176, w184, w192, rfl, rfl⟩
  | (refine ⟨w0, w8, w16, w24, w32, w40, w48, w56, w64, w68, w72, w80, w88, w96, w104, w112, w120, w128, w136, w144,
    w152, w160, w168, w176, w184, w192, ?_⟩; done)

/-- `CDirItems::CDirItems ()` from its entry to the return address: the bytes `M` of the object at `rdi`, the
registers as at the entry but `rsp`. -/
theorem cdi_ok (c : Seg prof F Wl L s₀ o) (hin : CodeIn L cdi_at cdi) (hK : KeptW Wl s₀ X)
    (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = cdi_at) (hw : ∀ i < 200, Foot Wl (Addr.add X.cpu.gpr.rdi i))
    (hl : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsp i))
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (hra : rdq(M V X.cpu.gpr.rdi, X.cpu.gpr.rsp) = e₂.add j₂)
    (k : ∀ (Z : State) (t' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem (M V X.cpu.gpr.rdi) →
      Z.cpu.rip = e₂.add j₂ → Z.cpu.gpr = X.cpu.gpr.set 4 (X.cpu.gpr.rsp + 8) →
      GoG prof L o gev gP gE Z t') :
    GoG prof L o gev gP gE X t := by
  refine (c_0 prof).run c hin
    (fun j' g' _ V' => j' = 229 ∧ g' = X.cpu.gpr ∧ V' = M V X.cpu.gpr.rdi) hK hA
    (by rw [addr_add_zero]; exact hrip)
    (wp_mono o0 (fun _ _ _ h => ⟨rfl, h⟩) (vc_0 hw)) ?_
  rintro j' g fl V₁ ⟨rfl, rfl, hV₁⟩ Y t₁ hKY hAY hrY hgY -
  subst V₁
  have hspY : Y.cpu.gpr.rsp = X.cpu.gpr.rsp := by rw [hgY]
  refine c.s_ret hKY hAY hin (lt_len (by decide)) hrY (ret_229 _) (by rw [hspY]; exact hl) hin₂ h₂
    (by rw [hspY]; exact hra) ?_
  rintro Z t₂ hKZ hAZ ⟨hrZ, hgZ⟩
  exact k Z t₂ hKZ hAZ hrZ (by rw [hgZ, hspY, hgY])

end FV7z.Cdi
