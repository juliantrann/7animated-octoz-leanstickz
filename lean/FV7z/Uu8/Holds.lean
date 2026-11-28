import FV7z.Uu8.Cuts
import FV7z.Lemmas.LeafRet
import FV7z.Lemmas.FnFar
/-!
# `ConvertUnicodeToUTF8` (PLAN.md §M, M1)

7-Zip 26.06's `ConvertUnicodeToUTF8` at `0x4520b0` in `7zzs` (`CPP/Common/UTFConvert.cpp`; `objdump -d`): `mov rax,
0x79217c; mov edx, [rax]`, then a tail jump to `0x452010` (`ConvertUnicodeToUTF8_Flags`; its code a hypothesis,
`hinT`) with `edx` = the global flags word at `0x79217c`.

- `gq`: the registers at the jump; `vc_0`: the straight-line code.
- `uu8_ok`: from the entry, at `0x452010` with the registers `gq`.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Uu8

/-- The tail jump. -/
def pjm : List Byte := [0xe9, 0x4e, 0xff, 0xff, 0xff]
theorem pjm_0 : ∀ feat, Dec feat pjm 0 (FV7z.mk .jmp 64 [.rel 18446744073709551438] 5) := by dec_rfl
theorem wj_13 : pjm <+: uu8.drop 13 := by decide +kernel
theorem jmp_13 (feat : Features) : Dec feat uu8 13 (FV7z.mk .jmp 64 [.rel 18446744073709551438] 5) :=
  Dec.shift (j := 13) (k := 0) (pjm_0 feat) wj_13 (Nat.zero_le _)

/-- `ConvertUnicodeToUTF8_Flags` (not proved here). -/
abbrev tgt_at : Addr := 0x452010
theorem tgt_13 : uu8_at.add (13 + 5) + BitVec.ofNat 64 18446744073709551438 = tgt_at.add 0 := by decide

/-- The registers at the jump. -/
abbrev gq (V : Addr → Byte) (g : Gprs) : Gprs :=
  { g with rax := 7938428#64, rdx := BitVec.setWidth 64 rdd(V, 7938428#64) }

variable {F : Footprint} {Wl : List Rgn}

/-- `mov rax, 0x79217c; mov edx, [rax]`. -/
theorem vc_0 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (f1 : ∀ i < 4, Foot F.data (Addr.add (7938428#64) i))
    (h : ∀ fl, Q 13 (gq V g) fl V) : W_0 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at f1 h ⊢
  wpx [W_0, o0]
  all_goals repeat' (first | exact h _ | exact f1 | apply And.intro | intro _)

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {X : State} {t : Nat} {V : Addr → Byte}

/-- From its entry: at `ConvertUnicodeToUTF8_Flags` with the registers `gq`. -/
theorem uu8_ok (c : Seg prof F Wl L s₀ o) (hin : CodeIn L uu8_at uu8)
    {codeT : List Byte} (hinT : CodeIn L tgt_at codeT) (hT : 0 < codeT.length)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = uu8_at)
    (f1 : ∀ i < 4, Foot F.data (Addr.add (7938428#64) i))
    (kf : ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y → Agree F Y.proc.mm.mem V → Y.cpu.rip = tgt_at →
      Y.cpu.gpr = gq V X.cpu.gpr → GoG prof L o gev gP gE Y t') :
    GoG prof L o gev gP gE X t := by
  refine (c_0 prof).run c hin (fun j' g' _ V' => j' = 13 ∧ g' = gq V X.cpu.gpr ∧ V' = V)
    hK hA (by rw [addr_add_zero]; exact hrip) (vc_0 f1 fun _ => ⟨rfl, rfl, rfl⟩) ?_
  rintro j' g fl V₁ ⟨rfl, hg, hV⟩ Y t₁ hKY hAY hrY hgY -
  subst hg; subst V₁
  refine c.s_jmp_x hKY hAY hin (lt_len (by decide)) hrY (jmp_13 _) hinT (tgt := 0) hT tgt_13 ?_
  rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
  exact kf Y₂ t₂ hK₂ hA₂ (by rw [hr₂, addr_add_zero]) (hg₂.trans hgY)

end FV7z.Uu8
