import FV7z.Ldc.Cuts
import FV7z.Cpt.Holds
/-!
# `NCompress::NLzma::CDecoder::CDecoder` (PLAN.md §M, M1)

7-Zip 26.06's `NCompress::NLzma::CDecoder::CDecoder ()` at `0x57fb70` in `7zzs`
(`CPP/7zip/Compress/LzmaDecoder.cpp`; `objdump -d`): for the object at `p` = `rdi`, the 8 vtable pointers of the
class's interfaces (`0x78c498` plus 0x10, 0x88, 0xb8, 0xe8, 0x118, 0x150, 0x188, 0x1b8) in the 8 bytes at `p + 8 * i`
(the one at `p + 48` stored after the one at `p + 56`), 0 in the byte at `p + 70`, the 4 bytes at `p + 64`, the 2
bytes at `p + 68` and the 8 bytes at `p + 112`, `p + 256`, `p + 88`, `p + 96`, `p + 152`, `p + 136`, and 1 MiB
(`_inBufSize`, `_outStep`) in the 8 bytes at `p + 72` and `p + 80`. `rax` and `rdx` are changed. One `ret` (184).

- `M`: the bytes after the stores, in their order; `vc_0`: from the entry to the `ret`, the stores' bytes from the
  object's 264 bytes in `Wl` (`Cpt.off_ft`).
- `ldc_ok`: from the entry to the return address.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Ldc

/-- The `ret`. -/
def pret : List Byte := [0xc3]
theorem pret_0 : ∀ feat, Dec feat pret 0 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem w_184 : pret <+: ldc.drop 184 := by decide +kernel
theorem ret_184 (feat : Features) : Dec feat ldc 184 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 184) (k := 0) (pret_0 feat) w_184 (Nat.zero_le _)

/-- The bytes after the stores into the object at `p`, in their order. -/
abbrev M (V : Addr → Byte) (p : Addr) : Addr → Byte :=
  Vst (Vst (Vst (Vst (Vst (Vst (Vst (Vst (Vst (Vst (Vst (Vst (Vst (Vst (Vst (Vst (Vst (Vst (Vst V
    (p + 70#64) (toBytesLE 0#8 1))
    (p + 64#64) (toBytesLE 0#32 4))
    (p + 112#64) (toBytesLE 0#64 8))
    p (toBytesLE 7914664#64 8))
    (p + 8#64) (toBytesLE 7914784#64 8))
    (p + 16#64) (toBytesLE 7914832#64 8))
    (p + 24#64) (toBytesLE 7914880#64 8))
    (p + 32#64) (toBytesLE 7914928#64 8))
    (p + 40#64) (toBytesLE 7914984#64 8))
    (p + 56#64) (toBytesLE 7915088#64 8))
    (p + 48#64) (toBytesLE 7915040#64 8))
    (p + 68#64) (toBytesLE 0#16 2))
    (p + 256#64) (toBytesLE 0#64 8))
    (p + 72#64) (toBytesLE 1048576#64 8))
    (p + 80#64) (toBytesLE 1048576#64 8))
    (p + 88#64) (toBytesLE 0#64 8))
    (p + 96#64) (toBytesLE 0#64 8))
    (p + 152#64) (toBytesLE 0#64 8))
    (p + 136#64) (toBytesLE 0#64 8)

variable {prof : Profile} {F : Footprint} {Wl : List Rgn} {L : List (Addr × List Byte)} {s₀ : State}
  {o : Oracle} {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {X : State} {t : Nat} {V : Addr → Byte}

/-- The stores, from the entry to the `ret`. -/
theorem vc_0 {g : Gprs} {f : Rflags} (hw : ∀ i < 264, Foot Wl (Addr.add g.rdi i)) :
    wp F Wl o0 (fun g' _ V' => (∃ a d, g' = { g with rax := a, rdx := d }) ∧ V' = M V g.rdi) g f V := by
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
  have w68 : ∀ i < 2, Foot Wl (Addr.add (rdi + 68#64) i) := Cpt.off_ft hw 68 rfl (by decide)
  have w70 : ∀ i < 1, Foot Wl (Addr.add (rdi + 70#64) i) := Cpt.off_ft hw 70 rfl (by decide)
  have w72 : ∀ i < 8, Foot Wl (Addr.add (rdi + 72#64) i) := Cpt.off_ft hw 72 rfl (by decide)
  have w80 : ∀ i < 8, Foot Wl (Addr.add (rdi + 80#64) i) := Cpt.off_ft hw 80 rfl (by decide)
  have w88 : ∀ i < 8, Foot Wl (Addr.add (rdi + 88#64) i) := Cpt.off_ft hw 88 rfl (by decide)
  have w96 : ∀ i < 8, Foot Wl (Addr.add (rdi + 96#64) i) := Cpt.off_ft hw 96 rfl (by decide)
  have w112 : ∀ i < 8, Foot Wl (Addr.add (rdi + 112#64) i) := Cpt.off_ft hw 112 rfl (by decide)
  have w136 : ∀ i < 8, Foot Wl (Addr.add (rdi + 136#64) i) := Cpt.off_ft hw 136 rfl (by decide)
  have w152 : ∀ i < 8, Foot Wl (Addr.add (rdi + 152#64) i) := Cpt.off_ft hw 152 rfl (by decide)
  have w256 : ∀ i < 8, Foot Wl (Addr.add (rdi + 256#64) i) := Cpt.off_ft hw 256 rfl (by decide)
  wpx [o0, M, BitVec.xor_self, BitVec.setWidth_zero, BitVec.reduceAdd]
  all_goals repeat'
    first
    | with_reducible assumption
    | exact ⟨_, _, rfl⟩
    | with_reducible rfl
    | rfl
    | apply And.intro
    | intro _

/-- `CDecoder::CDecoder ()` from its entry to the return address: the bytes `M` of the object at `rdi`, the
registers as at the entry but `rax`, `rdx` and `rsp`. -/
theorem ldc_ok (c : Seg prof F Wl L s₀ o) (hin : CodeIn L ldc_at ldc) (hK : KeptW Wl s₀ X)
    (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = ldc_at) (hw : ∀ i < 264, Foot Wl (Addr.add X.cpu.gpr.rdi i))
    (hl : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsp i))
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (hra : rdq(M V X.cpu.gpr.rdi, X.cpu.gpr.rsp) = e₂.add j₂)
    (k : ∀ (Z : State) (t' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem (M V X.cpu.gpr.rdi) →
      Z.cpu.rip = e₂.add j₂ →
      (∃ a d, Z.cpu.gpr = { X.cpu.gpr with rax := a, rdx := d }.set 4 (X.cpu.gpr.rsp + 8)) →
      GoG prof L o gev gP gE Z t') :
    GoG prof L o gev gP gE X t := by
  refine (c_0 prof).run c hin
    (fun j' g' _ V' => j' = 184 ∧ (∃ a d, g' = { X.cpu.gpr with rax := a, rdx := d }) ∧ V' = M V X.cpu.gpr.rdi)
    hK hA (by rw [addr_add_zero]; exact hrip)
    (wp_mono o0 (fun _ _ _ h => ⟨rfl, h⟩) (vc_0 hw)) ?_
  rintro j' g fl V₁ ⟨rfl, ⟨a, d, rfl⟩, hV₁⟩ Y t₁ hKY hAY hrY hgY -
  subst V₁
  have hspY : Y.cpu.gpr.rsp = X.cpu.gpr.rsp := by rw [hgY]
  refine c.s_ret hKY hAY hin (lt_len (by decide)) hrY (ret_184 _) (by rw [hspY]; exact hl) hin₂ h₂
    (by rw [hspY]; exact hra) ?_
  rintro Z t₂ hKZ hAZ ⟨hrZ, hgZ⟩
  exact k Z t₂ hKZ hAZ hrZ ⟨a, d, by rw [hgZ, hspY, hgY]⟩

end FV7z.Ldc
