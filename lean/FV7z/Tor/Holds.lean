import FV7z.Tor.Cuts
import FV7z.Lemmas.LeafRet
import FV7z.Lemmas.FnFar
/-!
# `CExtractCallbackConsole::OpenResult` thunk (`_ZThn8`) (PLAN.md §M, M1)

7-Zip 26.06's `CExtractCallbackConsole::OpenResult` at `0x5e9ef0` in `7zzs`
(`CPP/7zip/UI/Console/ExtractCallbackConsole.cpp`; `objdump -d`): `sub rdi, 8`, then a tail jump to `0x5e9820`
(`CExtractCallbackConsole::OpenResult`; its code a hypothesis, `hinT`) with `rdi` = `this - 8` (from the base at
offset 8 to the whole object).

- `gq`: the registers at the jump; `vc_0`: the straight-line code.
- `tor_ok`: from the entry, at `0x5e9820` with the registers `gq`.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Tor

/-- The tail jump. -/
def pjm : List Byte := [0xe9, 0x23, 0xf9, 0xff, 0xff]
theorem pjm_0 : ∀ feat, Dec feat pjm 0 (FV7z.mk .jmp 64 [.rel 18446744073709549859] 5) := by dec_rfl
theorem wj_8 : pjm <+: tor.drop 8 := by decide +kernel
theorem jmp_8 (feat : Features) : Dec feat tor 8 (FV7z.mk .jmp 64 [.rel 18446744073709549859] 5) :=
  Dec.shift (j := 8) (k := 0) (pjm_0 feat) wj_8 (Nat.zero_le _)

/-- `CExtractCallbackConsole::OpenResult` (not proved here). -/
abbrev tgt_at : Addr := 0x5e9820
theorem tgt_8 : tor_at.add (8 + 5) + BitVec.ofNat 64 18446744073709549859 = tgt_at.add 0 := by decide

/-- The registers at the jump. -/
abbrev gq (g : Gprs) : Gprs :=
  { g with
      rdi := g.rdi - 8#64 }

variable {F : Footprint} {Wl : List Rgn}

/-- `sub rdi, 8`. -/
theorem vc_0 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (h : ∀ fl, Q 8 (gq g) fl V) : W_0 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_0, o0]
  all_goals repeat' (first | exact h _ | apply And.intro | intro _)

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {X : State} {t : Nat} {V : Addr → Byte}

/-- From its entry: at `CExtractCallbackConsole::OpenResult` with the registers `gq`. -/
theorem tor_ok (c : Seg prof F Wl L s₀ o) (hin : CodeIn L tor_at tor)
    {codeT : List Byte} (hinT : CodeIn L tgt_at codeT) (hT : 0 < codeT.length)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = tor_at)
    (kf : ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y → Agree F Y.proc.mm.mem V → Y.cpu.rip = tgt_at →
      Y.cpu.gpr = gq X.cpu.gpr → GoG prof L o gev gP gE Y t') :
    GoG prof L o gev gP gE X t := by
  refine (c_0 prof).run c hin (fun j' g' _ V' => j' = 8 ∧ g' = gq X.cpu.gpr ∧ V' = V)
    hK hA (by rw [addr_add_zero]; exact hrip) (vc_0 fun _ => ⟨rfl, rfl, rfl⟩) ?_
  rintro j' g fl V₁ ⟨rfl, hg, hV⟩ Y t₁ hKY hAY hrY hgY -
  subst hg; subst V₁
  refine c.s_jmp_x hKY hAY hin (lt_len (by decide)) hrY (jmp_8 _) hinT (tgt := 0) hT tgt_8 ?_
  rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
  exact kf Y₂ t₂ hK₂ hA₂ (by rw [hr₂, addr_add_zero]) (hg₂.trans hgY)

end FV7z.Tor
