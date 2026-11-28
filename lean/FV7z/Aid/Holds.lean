import FV7z.Aid.Cuts
import FV7z.Lemmas.LeafRet
import FV7z.Lemmas.FnFar
/-!
# `Archive_IsItem_Dir` (PLAN.md §M, M1)

7-Zip 26.06's `Archive_IsItem_Dir (arc, index, result)` at `0x5d1670` in `7zzs` (`CPP/7zip/UI/Common/OpenArchive.cpp`;
`objdump -d`): `return Archive_GetItemBoolProp (arc, index, kpidIsDir, result);` as a tail jump to `0x5d15e0`
(its code a hypothesis, `hinT`) with `rcx` = `result` and `edx` = `kpidIsDir` (6).

- `gA`: the registers at the jump; `vc_0`: the two moves.
- `aid_ok`: from the entry, at `0x5d15e0` with the registers `gA`.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Aid

/-- The tail jump. -/
def pjm : List Byte := [0xe9, 0x5f, 0xff, 0xff, 0xff]
theorem pjm_0 : ∀ feat, Dec feat pjm 0 (FV7z.mk .jmp 64 [.rel 18446744073709551455] 5) := by dec_rfl
theorem wj_12 : pjm <+: aid.drop 12 := by decide +kernel
theorem jmp_12 (feat : Features) : Dec feat aid 12 (FV7z.mk .jmp 64 [.rel 18446744073709551455] 5) :=
  Dec.shift (j := 12) (k := 0) (pjm_0 feat) wj_12 (Nat.zero_le _)

/-- `Archive_GetItemBoolProp` (not proved here). -/
abbrev tgt_at : Addr := 0x5d15e0
theorem tgt12 : aid_at.add (12 + 5) + BitVec.ofNat 64 18446744073709551455 = tgt_at.add 0 := by decide

/-- The registers at the jump: `rcx` = `result`, `rdx` = `kpidIsDir`. -/
abbrev gA (g : Gprs) : Gprs := { g with rcx := g.rdx, rdx := 6#64 }

variable {prof : Profile} {F : Footprint} {Wl : List Rgn} {L : List (Addr × List Byte)} {s₀ : State}
  {o : Oracle} {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {X : State} {t : Nat} {V : Addr → Byte}

/-- `mov rcx, rdx; mov edx, 6`. -/
theorem vc_0 {g : Gprs} {f : Rflags} : wp F Wl o0 (fun g' _ V' => g' = gA g ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [o0, gA]
  all_goals first
  | exact ⟨rfl, rfl⟩
  | rfl
  | trivial

/-- `Archive_IsItem_Dir (arc, index, result)` from its entry: at `Archive_GetItemBoolProp` with the registers `gA`. -/
theorem aid_ok (c : Seg prof F Wl L s₀ o) (hin : CodeIn L aid_at aid) (hK : KeptW Wl s₀ X)
    (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = aid_at)
    {cT : List Byte} (hinT : CodeIn L tgt_at cT) (hT : 0 < cT.length)
    (k : ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y → Agree F Y.proc.mm.mem V → Y.cpu.rip = tgt_at →
      Y.cpu.gpr = gA X.cpu.gpr → GoG prof L o gev gP gE Y t') :
    GoG prof L o gev gP gE X t := by
  refine (c_0 prof).run c hin (fun j' g' _ V' => j' = 12 ∧ g' = gA X.cpu.gpr ∧ V' = V) hK hA
    (by rw [addr_add_zero]; exact hrip) (wp_mono o0 (fun _ _ _ h => ⟨rfl, h⟩) vc_0) ?_
  rintro j' g fl V₁ ⟨rfl, rfl, hV₁⟩ Y t₁ hKY hAY hrY hgY -
  subst V₁
  refine c.s_jmp_x hKY hAY hin (lt_len (by decide)) hrY (jmp_12 _) hinT hT tgt12 ?_
  rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
  exact k Y₂ t₂ hK₂ hA₂ (by rw [hr₂, addr_add_zero]) (hg₂.trans hgY)

end FV7z.Aid
