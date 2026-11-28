import FV7z.U8f.Cuts
import FV7z.Lemmas.LeafRet
import FV7z.Lemmas.FnFar
/-!
# `ConvertUTF8ToUnicode_Flags` (PLAN.md §M, M1)

7-Zip 26.06's `ConvertUTF8ToUnicode_Flags` at `0x451fe0` in `7zzs` (`CPP/Common/UTFConvert.cpp`; `objdump -d`): `mov
r8, rsi; mov esi, [rdi+8]; mov rdi, [rdi]; mov ecx, edx; mov rdx, r8`, then a tail jump to `0x451f20`
(`Convert_UTF8_Buf_To_Unicode`; its code a hypothesis, `hinT`) with `rdi` = `src._chars`, `esi` = `src._len`, `rdx` =
`dest`, `ecx` = `flags`.

- `gq`: the registers at the jump; `vc_0`: the straight-line code.
- `u8f_ok`: from the entry, at `0x451f20` with the registers `gq`.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.U8f

/-- The tail jump. -/
def pjm : List Byte := [0xe9, 0x29, 0xff, 0xff, 0xff]
theorem pjm_0 : ∀ feat, Dec feat pjm 0 (FV7z.mk .jmp 64 [.rel 18446744073709551401] 5) := by dec_rfl
theorem wj_18 : pjm <+: u8f.drop 18 := by decide +kernel
theorem jmp_18 (feat : Features) : Dec feat u8f 18 (FV7z.mk .jmp 64 [.rel 18446744073709551401] 5) :=
  Dec.shift (j := 18) (k := 0) (pjm_0 feat) wj_18 (Nat.zero_le _)

/-- `Convert_UTF8_Buf_To_Unicode` (not proved here). -/
abbrev tgt_at : Addr := 0x451f20
theorem tgt_18 : u8f_at.add (18 + 5) + BitVec.ofNat 64 18446744073709551401 = tgt_at.add 0 := by decide

/-- The registers at the jump. -/
abbrev gq (V : Addr → Byte) (g : Gprs) : Gprs :=
  { g with r8 := g.rsi, rsi := BitVec.setWidth 64 rdd(V, g.rdi + 8#64), rdi := rdq(V, g.rdi),
      rcx := BitVec.setWidth 64 (BitVec.setWidth 32 g.rdx), rdx := g.rsi }

variable {F : Footprint} {Wl : List Rgn}

/-- `mov r8, rsi; mov esi, [rdi+8]; mov rdi, [rdi]; mov ecx, edx; mov rdx, r8`. -/
theorem vc_0 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (f1 : ∀ i < 4, Foot F.data (Addr.add (g.rdi + 8#64) i))
    (f2 : ∀ i < 8, Foot F.data (Addr.add (g.rdi) i))
    (h : ∀ fl, Q 18 (gq V g) fl V) : W_0 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at f1 f2 h ⊢
  wpx [W_0, o0]
  all_goals repeat' (first | exact h _ | exact f1 | exact f2 | apply And.intro | intro _)

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {X : State} {t : Nat} {V : Addr → Byte}

/-- From its entry: at `Convert_UTF8_Buf_To_Unicode` with the registers `gq`. -/
theorem u8f_ok (c : Seg prof F Wl L s₀ o) (hin : CodeIn L u8f_at u8f)
    {codeT : List Byte} (hinT : CodeIn L tgt_at codeT) (hT : 0 < codeT.length)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = u8f_at)
    (f1 : ∀ i < 4, Foot F.data (Addr.add (X.cpu.gpr.rdi + 8#64) i))
    (f2 : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rdi) i))
    (kf : ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y → Agree F Y.proc.mm.mem V → Y.cpu.rip = tgt_at →
      Y.cpu.gpr = gq V X.cpu.gpr → GoG prof L o gev gP gE Y t') :
    GoG prof L o gev gP gE X t := by
  refine (c_0 prof).run c hin (fun j' g' _ V' => j' = 18 ∧ g' = gq V X.cpu.gpr ∧ V' = V)
    hK hA (by rw [addr_add_zero]; exact hrip) (vc_0 f1 f2 fun _ => ⟨rfl, rfl, rfl⟩) ?_
  rintro j' g fl V₁ ⟨rfl, hg, hV⟩ Y t₁ hKY hAY hrY hgY -
  subst hg; subst V₁
  refine c.s_jmp_x hKY hAY hin (lt_len (by decide)) hrY (jmp_18 _) hinT (tgt := 0) hT tgt_18 ?_
  rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
  exact kf Y₂ t₂ hK₂ hA₂ (by rw [hr₂, addr_add_zero]) (hg₂.trans hgY)

end FV7z.U8f
