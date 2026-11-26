import FV7z.Sri.Cuts
import FV7z.Lemmas.LeafRet
import FV7z.Lemmas.FnJm
/-!
# `CArchiveExtractCallback::SetRatioInfo` (PLAN.md §M, M1)

7-Zip 26.06's `CArchiveExtractCallback::SetRatioInfo (inSize, outSize)` at `0x5aa190` in `7zzs`
(`CPP/7zip/UI/Common/ArchiveExtractCallback.cpp`): `_compressProgress->SetRatioInfo (inSize, outSize)`, the object at
`this + 552`, as a tail jump through its vtable's entry at 24 (`jmp qword [rax + 24]`, `Seg.s_jmp_mx`). The callee's
code is a hypothesis (`hin₂`).

- `obj`, `vtb`: the object and its vtable; `gJ`: the registers at the jump.
- `sri_ok`: the run at the vtable's entry, `rdi` the object, `rax` its vtable, the other registers those of the entry.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Sri

/-- The jump through the vtable. -/
def pjm : List Byte := [0xff, 0x60, 0x18]
theorem pjm_0 : ∀ feat, Dec feat pjm 0 (FV7z.mk .jmp 64 [.mem (mbd 0 24 64)] 3) := by dec_rfl
theorem wj_14 : pjm <+: sri.drop 14 := by decide +kernel
theorem jmp_14 (feat : Features) : Dec feat sri 14 (FV7z.mk .jmp 64 [.mem (mbd 0 24 64)] 3) :=
  Dec.shift (j := 14) (k := 0) (pjm_0 feat) wj_14 (Nat.zero_le _)

/-- `_compressProgress` (at `this + 552`). -/
abbrev obj (V : Addr → Byte) (g : Gprs) : Addr := rdq(V, g.rdi + 552#64)
/-- Its vtable. -/
abbrev vtb (V : Addr → Byte) (g : Gprs) : Addr := rdq(V, obj V g)
/-- The registers at the jump: `rdi` the object, `rax` its vtable. -/
abbrev gJ (V : Addr → Byte) (g : Gprs) : Gprs := { g with rax := vtb V g, rdi := obj V g }

variable {prof : Profile} {F : Footprint} {Wl : List Rgn} {L : List (Addr × List Byte)} {s₀ : State}
  {o : Oracle} {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {X : State} {t : Nat} {V : Addr → Byte}

/-- `mov rdi, [rdi + 552]; mov rax, [rdi]`. -/
theorem vc_0 {g : Gprs} {f : Rflags} (fa : ∀ i < 8, Foot F.data (Addr.add (g.rdi + 552#64) i))
    (fb : ∀ i < 8, Foot F.data (Addr.add (obj V g) i)) :
    wp F Wl o0 (fun g' _ V' => g' = gJ V g ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at fa fb ⊢
  wpx [o0]
  first
  | rfl
  | exact ⟨fa, fb⟩
  | exact ⟨fa, fb, rfl⟩
  | exact ⟨fa, fb, rfl, rfl⟩
  | exact ⟨fa, by simpa using fb⟩
  | exact ⟨fa, by simpa using fb, rfl⟩
  | repeat' (first | exact fa | exact fb | (simpa using fb) | rfl | trivial | (refine ⟨?_, ?_⟩) | (intro _))

/-- `CArchiveExtractCallback::SetRatioInfo` from its entry: at the vtable's entry (`e₂.add tgt`), the registers
`gJ`. -/
theorem sri_ok (c : Seg prof F Wl L s₀ o) (hin : CodeIn L sri_at sri) (hK : KeptW Wl s₀ X)
    (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = sri_at)
    (fa : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rdi + 552#64) i))
    (fb : ∀ i < 8, Foot F.data (Addr.add (obj V X.cpu.gpr) i))
    (fc : ∀ i < 8, Foot F.data (Addr.add (vtb V X.cpu.gpr + 24#64) i))
    {e₂ : Addr} {code₂ : List Byte} {tgt : Nat} (hin₂ : CodeIn L e₂ code₂) (ht : tgt < code₂.length)
    (htgt : rdq(V, vtb V X.cpu.gpr + 24#64) = e₂.add tgt)
    (k : ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y → Agree F Y.proc.mm.mem V → Y.cpu.rip = e₂.add tgt →
      Y.cpu.gpr = gJ V X.cpu.gpr → GoG prof L o gev gP gE Y t') :
    GoG prof L o gev gP gE X t := by
  refine (c_0 prof).run c hin (fun j' g' _ V' => j' = 14 ∧ g' = gJ V X.cpu.gpr ∧ V' = V) hK hA
    (by rw [addr_add_zero]; exact hrip) (wp_mono o0 (fun _ _ _ h => ⟨rfl, h⟩) (vc_0 fa fb)) ?_
  rintro j' g fl V₁ ⟨rfl, rfl, rfl⟩ Y t₁ hKY hAY hrY hgY -
  have he : eaD Y 0 24 = vtb V X.cpu.gpr + 24#64 := by
    show Y.cpu.gpr.get (regOf 0) + BitVec.ofNat 64 24 = _
    rw [hgY]
    rfl
  refine c.s_jmp_mx hKY hAY hin (lt_len (by decide)) hrY (jmp_14 _) (by rw [he]; exact fc) hin₂ ht
    (by rw [he]; exact htgt) ?_
  rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
  exact k Y₂ t₂ hK₂ hA₂ hr₂ (hg₂.trans hgY)

end FV7z.Sri
