import FV7z.U8u.Cuts
import FV7z.Lemmas.LeafRet
import FV7z.Lemmas.FnFar
/-!
# `ConvertUTF8ToUnicode` (PLAN.md §M, M1)

7-Zip 26.06's `ConvertUTF8ToUnicode` at `0x452000` in `7zzs` (`CPP/Common/UTFConvert.cpp`; `objdump -d`): `mov edx,
7`, then a tail jump to `0x451fe0` (`ConvertUTF8ToUnicode_Flags`; its code a hypothesis, `hinT`) with `edx` = the
default flags (7); the callee is `U8f.u8f_ok`.

- `gq`: the registers at the jump; `vc_0`: the straight-line code.
- `u8u_ok`: from the entry, at `0x451fe0` with the registers `gq`.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.U8u

/-- The tail jump. -/
def pjm : List Byte := [0xe9, 0xd2, 0xff, 0xff, 0xff]
theorem pjm_0 : ∀ feat, Dec feat pjm 0 (FV7z.mk .jmp 64 [.rel 18446744073709551570] 5) := by dec_rfl
theorem wj_9 : pjm <+: u8u.drop 9 := by decide +kernel
theorem jmp_9 (feat : Features) : Dec feat u8u 9 (FV7z.mk .jmp 64 [.rel 18446744073709551570] 5) :=
  Dec.shift (j := 9) (k := 0) (pjm_0 feat) wj_9 (Nat.zero_le _)

/-- `ConvertUTF8ToUnicode_Flags` (not proved here). -/
abbrev tgt_at : Addr := 0x451fe0
theorem tgt_9 : u8u_at.add (9 + 5) + BitVec.ofNat 64 18446744073709551570 = tgt_at.add 0 := by decide

/-- The registers at the jump. -/
abbrev gq (g : Gprs) : Gprs :=
  { g with rdx := 7#64 }

variable {F : Footprint} {Wl : List Rgn}

/-- `mov edx, 7`. -/
theorem vc_0 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (h : ∀ fl, Q 9 (gq g) fl V) : W_0 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_0, o0]
  all_goals repeat' (first | exact h _ | apply And.intro | intro _)

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {X : State} {t : Nat} {V : Addr → Byte}

/-- From its entry: at `ConvertUTF8ToUnicode_Flags` with the registers `gq`. -/
theorem u8u_ok (c : Seg prof F Wl L s₀ o) (hin : CodeIn L u8u_at u8u)
    {codeT : List Byte} (hinT : CodeIn L tgt_at codeT) (hT : 0 < codeT.length)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = u8u_at)
    (kf : ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y → Agree F Y.proc.mm.mem V → Y.cpu.rip = tgt_at →
      Y.cpu.gpr = gq X.cpu.gpr → GoG prof L o gev gP gE Y t') :
    GoG prof L o gev gP gE X t := by
  refine (c_0 prof).run c hin (fun j' g' _ V' => j' = 9 ∧ g' = gq X.cpu.gpr ∧ V' = V)
    hK hA (by rw [addr_add_zero]; exact hrip) (vc_0 fun _ => ⟨rfl, rfl, rfl⟩) ?_
  rintro j' g fl V₁ ⟨rfl, hg, hV⟩ Y t₁ hKY hAY hrY hgY -
  subst hg; subst V₁
  refine c.s_jmp_x hKY hAY hin (lt_len (by decide)) hrY (jmp_9 _) hinT (tgt := 0) hT tgt_9 ?_
  rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
  exact kf Y₂ t₂ hK₂ hA₂ (by rw [hr₂, addr_add_zero]) (hg₂.trans hgY)

end FV7z.U8u
