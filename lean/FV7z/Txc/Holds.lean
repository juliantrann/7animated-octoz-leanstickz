import FV7z.Txc.Cuts
import FV7z.Lemmas.LeafRet
import FV7z.Lemmas.FnFar
/-!
# `_txnal_cow_string_c_str` (PLAN.md §M, M1)

The symbol `_txnal_cow_string_c_str` at `0x454a40` in `7zzs` (folded with other bytes; `objdump -d`): `endbr64`, then
a tail jump to `0x456e30` (`NWindows::NFile::NName::GetFullPath`, `FV7z/Gfp/Holds.lean`; its code a hypothesis,
`hinT`) with the registers as they were.

- `vc_0`: the straight-line code (`endbr64`).
- `txc_ok`: from the entry, at `0x456e30` with the entry's registers and bytes.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Txc

/-- The tail jump. -/
def pjm : List Byte := [0xe9, 0xe7, 0x23, 0x00, 0x00]
theorem pjm_0 : ∀ feat, Dec feat pjm 0 (FV7z.mk .jmp 64 [.rel 9191] 5) := by dec_rfl
theorem wj_4 : pjm <+: txc.drop 4 := by decide +kernel
theorem jmp_4 (feat : Features) : Dec feat txc 4 (FV7z.mk .jmp 64 [.rel 9191] 5) :=
  Dec.shift (j := 4) (k := 0) (pjm_0 feat) wj_4 (Nat.zero_le _)

/-- `GetFullPath (path, fullPath)` (`Gfp.gfp_at`; not proved here). -/
abbrev tgt_at : Addr := 0x456e30
theorem tgt_4 : txc_at.add (4 + 5) + BitVec.ofNat 64 9191 = tgt_at.add 0 := by decide

variable {F : Footprint} {Wl : List Rgn}

/-- `endbr64`. -/
theorem vc_0 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (h : ∀ fl, Q 4 g fl V) : W_0 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_0, o0]
  all_goals repeat' (first | exact h _ | apply And.intro | intro _)

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {X : State} {t : Nat} {V : Addr → Byte}

/-- From its entry: at `GetFullPath` with the entry's registers. -/
theorem txc_ok (c : Seg prof F Wl L s₀ o) (hin : CodeIn L txc_at txc)
    {codeT : List Byte} (hinT : CodeIn L tgt_at codeT) (hT : 0 < codeT.length)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = txc_at)
    (kf : ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y → Agree F Y.proc.mm.mem V → Y.cpu.rip = tgt_at →
      Y.cpu.gpr = X.cpu.gpr → GoG prof L o gev gP gE Y t') :
    GoG prof L o gev gP gE X t := by
  refine (c_0 prof).run c hin (fun j' g' _ V' => j' = 4 ∧ g' = X.cpu.gpr ∧ V' = V)
    hK hA (by rw [addr_add_zero]; exact hrip) (vc_0 fun _ => ⟨rfl, rfl, rfl⟩) ?_
  rintro j' g fl V₁ ⟨rfl, hg, hV⟩ Y t₁ hKY hAY hrY hgY -
  subst hg; subst V₁
  refine c.s_jmp_x hKY hAY hin (lt_len (by decide)) hrY (jmp_4 _) hinT (tgt := 0) hT tgt_4 ?_
  rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
  exact kf Y₂ t₂ hK₂ hA₂ (by rw [hr₂, addr_add_zero]) (hg₂.trans hgY)

end FV7z.Txc
