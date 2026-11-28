import FV7z.Gfp.Cuts
import FV7z.Lemmas.LeafRet
import FV7z.Lemmas.FnFar
/-!
# `NWindows::NFile::NName::GetFullPath` (PLAN.md §M, M1)

7-Zip 26.06's `NWindows::NFile::NName::GetFullPath` at `0x456e30` in `7zzs` (`CPP/Windows/FileName.cpp`; `objdump
-d`): `mov rdx, rsi; mov rsi, rdi; xor edi, edi`, then a tail jump to `0x456a80` (`GetFullPath (dirPrefix, path,
fullPath)`; its code a hypothesis, `hinT`) with `rdi` = no directory prefix (0), `rsi` = `path`, `rdx` = `fullPath`.

- `gq`: the registers at the jump; `vc_0`: the straight-line code.
- `gfp_ok`: from the entry, at `0x456a80` with the registers `gq`.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Gfp

/-- The tail jump. -/
def pjm : List Byte := [0xe9, 0x3f, 0xfc, 0xff, 0xff]
theorem pjm_0 : ∀ feat, Dec feat pjm 0 (FV7z.mk .jmp 64 [.rel 18446744073709550655] 5) := by dec_rfl
theorem wj_12 : pjm <+: gfp.drop 12 := by decide +kernel
theorem jmp_12 (feat : Features) : Dec feat gfp 12 (FV7z.mk .jmp 64 [.rel 18446744073709550655] 5) :=
  Dec.shift (j := 12) (k := 0) (pjm_0 feat) wj_12 (Nat.zero_le _)

/-- `GetFullPath (dirPrefix, path, fullPath)` (not proved here). -/
abbrev tgt_at : Addr := 0x456a80
theorem tgt_12 : gfp_at.add (12 + 5) + BitVec.ofNat 64 18446744073709550655 = tgt_at.add 0 := by decide

/-- The registers at the jump. -/
abbrev gq (g : Gprs) : Gprs :=
  { g with
      rdx := g.rsi,
      rsi := g.rdi,
      rdi := 0#64 }

/-- `xor r32, r32`. -/
theorem xz (x : BitVec 32) : BitVec.setWidth 64 (x ^^^ x) = 0#64 := by simp

variable {F : Footprint} {Wl : List Rgn}

/-- `mov rdx, rsi; mov rsi, rdi; xor edi, edi`. -/
theorem vc_0 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (h : ∀ fl, Q 12 (gq g) fl V) : W_0 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_0, o0, xz, BitVec.reduceSetWidth]
  all_goals repeat' (first | exact h _ | apply And.intro | intro _)

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {X : State} {t : Nat} {V : Addr → Byte}

/-- From its entry: at `GetFullPath (dirPrefix, path, fullPath)` with the registers `gq`. -/
theorem gfp_ok (c : Seg prof F Wl L s₀ o) (hin : CodeIn L gfp_at gfp)
    {codeT : List Byte} (hinT : CodeIn L tgt_at codeT) (hT : 0 < codeT.length)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = gfp_at)
    (kf : ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y → Agree F Y.proc.mm.mem V → Y.cpu.rip = tgt_at →
      Y.cpu.gpr = gq X.cpu.gpr → GoG prof L o gev gP gE Y t') :
    GoG prof L o gev gP gE X t := by
  refine (c_0 prof).run c hin (fun j' g' _ V' => j' = 12 ∧ g' = gq X.cpu.gpr ∧ V' = V)
    hK hA (by rw [addr_add_zero]; exact hrip) (vc_0 fun _ => ⟨rfl, rfl, rfl⟩) ?_
  rintro j' g fl V₁ ⟨rfl, hg, hV⟩ Y t₁ hKY hAY hrY hgY -
  subst hg; subst V₁
  refine c.s_jmp_x hKY hAY hin (lt_len (by decide)) hrY (jmp_12 _) hinT (tgt := 0) hT tgt_12 ?_
  rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
  exact kf Y₂ t₂ hK₂ hA₂ (by rw [hr₂, addr_add_zero]) (hg₂.trans hgY)

end FV7z.Gfp
