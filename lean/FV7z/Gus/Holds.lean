import FV7z.Gus.Cuts
import FV7z.Lemmas.LeafRet
import FV7z.Lemmas.FnFar
import FV7z.Tun.Inv
/-!
# `CArchiveExtractCallback::GetUnpackSize` (PLAN.md §M, M1)

7-Zip 26.06's `CArchiveExtractCallback::GetUnpackSize ()` at `0x5abac0` in `7zzs`
(`CPP/UI/Common/ArchiveExtractCallback.cpp`), `this` in `rdi`: `mov esi, [rdi + 0x1a8]; lea rcx, [rdi + 0x6a];
lea rdx, [rdi + 0x198]; mov rdi, [rdi + 0x40]`, then a tail jump (25) to `CArc::GetItem_Size (index, size, defined)`
at `0x5d2880`. No byte is written.

The callee is a hypothesis (`kf`): a continuation at its entry with the registers `gq`.

- `gq`: the registers at the jump: `rsi` = `_index`, `rcx` = `&_fi.SizeDefined`, `rdx` = `&_fi.Size`, `rdi` = `_arc`.
- `vc_0`: the verification condition of the one piece.
- `gus_ok`: from the entry to `CArc::GetItem_Size`'s entry with the registers `gq`, the bytes as they were.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Gus

/-- The tail jump to `CArc::GetItem_Size`. -/
def pjm : List Byte := [0xe9, 0xa2, 0x6d, 0x02, 0x00]
theorem pjm_0 : ∀ feat, Dec feat pjm 0 (FV7z.mk .jmp 64 [.rel 159138] 5) := by dec_rfl
theorem wm_25 : pjm <+: gus.drop 25 := by decide +kernel
theorem jmp_25 (feat : Features) : Dec feat gus 25 (FV7z.mk .jmp 64 [.rel 159138] 5) :=
  Dec.shift (j := 25) (k := 0) (pjm_0 feat) wm_25 (Nat.zero_le _)
theorem tgt_25 : gus_at.add (25 + 5) + BitVec.ofNat 64 159138 = (0x5d2880#64).add 0 := by decide

/-- The registers at the jump. -/
abbrev gq (V : Addr → Byte) (g : Gprs) : Gprs :=
  { g with
      rcx := g.rdi + 106#64,
      rdx := g.rdi + 408#64,
      rsi := BitVec.setWidth 64 rdd(V, g.rdi + 424#64),
      rdi := rdq(V, g.rdi + 64#64) }

variable {F : Footprint} {Wl : List Rgn}

/-- `mov esi, [rdi + 0x1a8]; lea rcx, [rdi + 0x6a]; lea rdx, [rdi + 0x198]; mov rdi, [rdi + 0x40]`. -/
theorem vc_0 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (f1 : ∀ i < 4, Foot F.data (Addr.add (g.rdi + 424#64) i)) (f2 : ∀ i < 8, Foot F.data (Addr.add (g.rdi + 64#64) i))
    (h : ∀ fl, Q 25 (gq V g) fl V) : W_0 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at f1 f2 h ⊢
  wpx [W_0, o0]
  all_goals repeat' (first | exact h _ | exact f1 | exact f2 | apply And.intro | intro _)

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {X : State} {t : Nat} {V : Addr → Byte}

/-- `CArchiveExtractCallback::GetUnpackSize ()` (`this` = `rdi`) from its entry: at `CArc::GetItem_Size`'s entry
(`0x5d2880`) with the registers `gq` and the bytes as they were (`kf`). -/
theorem gus_ok (c : Seg prof F Wl L s₀ o) (hin : CodeIn L gus_at gus)
    {codeT : List Byte} (hinT : CodeIn L 0x5d2880#64 codeT) (hT : 0 < codeT.length)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = gus_at)
    (f1 : ∀ i < 4, Foot F.data (Addr.add (X.cpu.gpr.rdi + 424#64) i))
    (f2 : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rdi + 64#64) i))
    (kf : ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y → Agree F Y.proc.mm.mem V → Y.cpu.rip = 0x5d2880#64 →
      Y.cpu.gpr = gq V X.cpu.gpr → GoG prof L o gev gP gE Y t') :
    GoG prof L o gev gP gE X t := by
  refine (c_0 prof).run c hin (fun j' g' _ V' => j' = 25 ∧ g' = gq V X.cpu.gpr ∧ V' = V)
    hK hA (by rw [addr_add_zero]; exact hrip) (vc_0 f1 f2 fun _ => ⟨rfl, rfl, rfl⟩) ?_
  rintro j' g fl V₁ ⟨rfl, hg, hV⟩ Y t₁ hKY hAY hrY hgY -
  subst hg; subst V₁
  refine c.s_jmp_x hKY hAY hin (lt_len (by decide)) hrY (jmp_25 _) hinT (tgt := 0) hT tgt_25 ?_
  rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
  exact kf Y₂ t₂ hK₂ hA₂ (by rw [hr₂, addr_add_zero]) (hg₂.trans hgY)

end FV7z.Gus
