import FV7z.Srt.Cuts
import FV7z.Sri.Holds
import FV7z.Lemmas.FnFar
/-!
# The thunk of `CArchiveExtractCallback::SetRatioInfo` (PLAN.md §M, M1)

7-Zip 26.06's thunk at `0x5aa1b0` in `7zzs` of `CArchiveExtractCallback::SetRatioInfo (inSize, outSize)` for the
object's `ICompressProgressInfo` base (`objdump -d`): `sub rdi, 24` (the object from the base) and a jump to the method
at `0x5aa190` (`FV7z.Sri`), which goes on through `_compressProgress`'s vtable.

- `gT`: the registers at the method's entry; `vc_0`: the `sub`.
- `srt_ok`: from the thunk's entry, through `Sri.sri_ok`, at the vtable's entry with the registers `Sri.gJ`.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Srt

/-- The jump to the method. -/
def pjm : List Byte := [0xeb, 0xd6]
theorem pjm_0 : ∀ feat, Dec feat pjm 0 (FV7z.mk .jmp 64 [.rel 18446744073709551574] 2) := by dec_rfl
theorem wj_8 : pjm <+: srt.drop 8 := by decide +kernel
theorem jmp_8 (feat : Features) : Dec feat srt 8 (FV7z.mk .jmp 64 [.rel 18446744073709551574] 2) :=
  Dec.shift (j := 8) (k := 0) (pjm_0 feat) wj_8 (Nat.zero_le _)
theorem tgt8 : srt_at.add (8 + 2) + BitVec.ofNat 64 18446744073709551574 = Sri.sri_at.add 0 := by decide

/-- The registers at the method's entry: `this` from the base. -/
abbrev gT (g : Gprs) : Gprs := { g with rdi := g.rdi - 24#64 }

variable {prof : Profile} {F : Footprint} {Wl : List Rgn} {L : List (Addr × List Byte)} {s₀ : State}
  {o : Oracle} {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {X : State} {t : Nat} {V : Addr → Byte}

/-- `sub rdi, 24`. -/
theorem vc_0 {g : Gprs} {f : Rflags} : wp F Wl o0 (fun g' _ V' => g' = gT g ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [o0, gT]
  all_goals first
  | exact ⟨rfl, rfl⟩
  | rfl
  | trivial
  | (intro _; exact ⟨rfl, rfl⟩)

/-- The thunk from its entry: through the method (`Sri.sri_ok`, for `this` = `rdi - 24`), at the vtable's entry
(`e₂.add tgt`) with the registers `Sri.gJ`. -/
theorem srt_ok (c : Seg prof F Wl L s₀ o) (hin : CodeIn L srt_at srt) (hinS : CodeIn L Sri.sri_at Sri.sri)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = srt_at)
    (fa : ∀ i < 8, Foot F.data (Addr.add ((gT X.cpu.gpr).rdi + 552#64) i))
    (fb : ∀ i < 8, Foot F.data (Addr.add (Sri.obj V (gT X.cpu.gpr)) i))
    (fc : ∀ i < 8, Foot F.data (Addr.add (Sri.vtb V (gT X.cpu.gpr) + 24#64) i))
    {e₂ : Addr} {code₂ : List Byte} {tgt : Nat} (hin₂ : CodeIn L e₂ code₂) (ht : tgt < code₂.length)
    (htgt : rdq(V, Sri.vtb V (gT X.cpu.gpr) + 24#64) = e₂.add tgt)
    (k : ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y → Agree F Y.proc.mm.mem V → Y.cpu.rip = e₂.add tgt →
      Y.cpu.gpr = Sri.gJ V (gT X.cpu.gpr) → GoG prof L o gev gP gE Y t') :
    GoG prof L o gev gP gE X t := by
  refine (c_0 prof).run c hin (fun j' g' _ V' => j' = 8 ∧ g' = gT X.cpu.gpr ∧ V' = V) hK hA
    (by rw [addr_add_zero]; exact hrip) (wp_mono o0 (fun _ _ _ h => ⟨rfl, h⟩) vc_0) ?_
  rintro j' g fl V₁ ⟨rfl, rfl, hV₁⟩ Y t₁ hKY hAY hrY hgY -
  subst V₁
  refine c.s_jmp_x hKY hAY hin (lt_len (by decide)) hrY (jmp_8 _) hinS (Sri.lt_len (by decide)) tgt8 ?_
  rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
  have hg : Y₂.cpu.gpr = gT X.cpu.gpr := hg₂.trans hgY
  refine Sri.sri_ok c hinS hK₂ hA₂ (by rw [hr₂, addr_add_zero]) (by rw [hg]; exact fa) (by rw [hg]; exact fb)
    (by rw [hg]; exact fc) hin₂ ht (by rw [hg]; exact htgt) ?_
  intro Y₃ t₃ hK₃ hA₃ hr₃ hg₃
  exact k Y₃ t₃ hK₃ hA₃ hr₃ (by rw [hg₃, hg])

end FV7z.Srt
