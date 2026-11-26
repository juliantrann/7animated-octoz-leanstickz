import FV7z.Lzi.Cuts
import FV7z.Lid.Holds
/-!
# `LzmaDec_Init` (PLAN.md §M, M1)

7-Zip 26.06's `LzmaDec_Init (p)` at `0x42b640` in `7zzs` (`C/LzmaDec.c`): `p->dicPos` (the 8 bytes at `p + 40`) = 0,
`edx` = `esi` = 1, then a tail jump (22) to `LzmaDec_InitDicAndState (p, True, True)` (`Lid.lid_ok`).

- `lzG`: the registers at the jump; `vc_0`: the one piece.
- `lzi_ok`: from the entry through `LzmaDec_InitDicAndState` to the return address.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Lzi

/-- The jump to `LzmaDec_InitDicAndState`. -/
def pjm : List Byte := [0xe9, 0xa5, 0xff, 0xff, 0xff]
theorem pjm_0 : ∀ feat, Dec feat pjm 0 (FV7z.mk .jmp 64 [.rel 18446744073709551525] 5) := by dec_rfl
theorem wj_22 : pjm <+: lzi.drop 22 := by decide +kernel
theorem jmp_22 (feat : Features) : Dec feat lzi 22 (FV7z.mk .jmp 64 [.rel 18446744073709551525] 5) :=
  Dec.shift (j := 22) (k := 0) (pjm_0 feat) wj_22 (Nat.zero_le _)

/-- The registers at the jump: `edx` = `esi` = 1. -/
abbrev lzG (g : Gprs) : Gprs := { g with rdx := 1#64, rsi := 1#64 }

variable {F : Footprint} {Wl : List Rgn}

/-- `mov qword [rdi + 40], 0; mov edx, 1; mov esi, 1`. -/
theorem vc_0 {g : Gprs} {f : Rflags} {V : Addr → Byte} (hw : ∀ i < 8, Foot Wl (Addr.add (g.rdi + 40#64) i)) :
    W_0 F Wl (fun j' g' _ V' => j' = 22 ∧ g' = lzG g ∧ V' = Vst V (g.rdi + 40#64) (toBytesLE 0#64 8)) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hw ⊢
  wpx [W_0, o0, lzG]
  all_goals repeat' (first | exact rfl | assumption | exact trivial | apply And.intro | intro _)

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {X : State} {t : Nat} {V : Addr → Byte}

/-- `LzmaDec_Init (p)` (`p` = `rdi`) from its entry: `p->dicPos` = 0, then `LzmaDec_InitDicAndState`'s stores
(`Lid.Mf`) with `initDic` and `initState` true, at the return address with `edx` = `esi` = 1. -/
theorem lzi_ok (c : Seg prof F Wl L s₀ o) (hin : CodeIn L lzi_at lzi) (hinL : CodeIn L Lid.lid_at Lid.lid)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = lzi_at)
    (w40 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rdi + 40#64) i))
    (w92 : ∀ i < 4, Foot Wl (Addr.add (X.cpu.gpr.rdi + 92#64) i))
    (w100 : ∀ i < 4, Foot Wl (Addr.add (X.cpu.gpr.rdi + 100#64) i))
    (w64 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rdi + 64#64) i))
    (hl : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsp i))
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (hra : rdq(Lid.Mf (Vst V (X.cpu.gpr.rdi + 40#64) (toBytesLE 0#64 8)) (lzG X.cpu.gpr), X.cpu.gpr.rsp) = e₂.add j₂)
    (k : ∀ (Z : State) (t' : Nat), KeptW Wl s₀ Z →
      Agree F Z.proc.mm.mem (Lid.Mf (Vst V (X.cpu.gpr.rdi + 40#64) (toBytesLE 0#64 8)) (lzG X.cpu.gpr)) →
      Z.cpu.rip = e₂.add j₂ → Z.cpu.gpr = (lzG X.cpu.gpr).set 4 (X.cpu.gpr.rsp + 8) →
      GoG prof L o gev gP gE Z t') :
    GoG prof L o gev gP gE X t := by
  refine (c_0 prof).run c hin (fun j' g' _ V' => j' = 22 ∧ g' = lzG X.cpu.gpr ∧
      V' = Vst V (X.cpu.gpr.rdi + 40#64) (toBytesLE 0#64 8)) hK hA (by rw [addr_add_zero]; exact hrip)
    (vc_0 w40) ?_
  rintro j' g fl V₁ ⟨rfl, rfl, hV₁⟩ Y t₁ hKY hAY hrY hgY -
  subst V₁
  refine c.s_jmp_x hKY hAY hin (lt_len (by decide)) hrY (jmp_22 _) hinL (Lid.lt_len (j := 0) (by decide))
    (by decide) ?_
  rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
  have hg : Y₂.cpu.gpr = lzG X.cpu.gpr := by rw [hg₂, hgY]
  refine Lid.lid_ok c hinL hK₂ hA₂ (by rw [hr₂, addr_add_zero]) (by rw [hg]; exact w92) (by rw [hg]; exact w100)
    (by rw [hg]; exact w64) (by rw [hg]; exact hl) hin₂ h₂ (by rw [hg]; exact hra) ?_
  intro Z t' hKZ hAZ hrZ hgZ
  rw [hg] at hAZ hgZ
  exact k Z t' hKZ hAZ hrZ hgZ

end FV7z.Lzi
