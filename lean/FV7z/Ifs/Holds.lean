import FV7z.Ifs.Cuts
import FV7z.Fxs.Code
import FV7z.Fxs.Blocks
import FV7z.Lemmas.LeafRet
import FV7z.Tun.Inv
/-!
# `_IO_file_stat` (PLAN.md §M, M1)

glibc 2.31's `_IO_file_stat (fp, st)` at `0x6287b0` in `7zzs` (`libio/fileops.c`): `rdx` = `st`, `esi` =
`fp->_fileno` (the 4 bytes at `fp + 112`), `edi` = 1 (`_STAT_VER`), then a tail jump (15) to `__fxstat`
(`Fxs.fxs_at`).

- `ifG`: the registers at the jump; `vc_0`: the one piece.
- `ifs_ok`: from the entry to `__fxstat`'s entry (`kf`), the bytes as they were.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Ifs

/-- The jump to `__fxstat`. -/
def pjm : List Byte := [0xe9, 0x9c, 0xcb, 0x03, 0x00]
theorem pjm_0 : ∀ feat, Dec feat pjm 0 (FV7z.mk .jmp 64 [.rel 248732] 5) := by dec_rfl
theorem wj_15 : pjm <+: ifs.drop 15 := by decide +kernel
theorem jmp_15 (feat : Features) : Dec feat ifs 15 (FV7z.mk .jmp 64 [.rel 248732] 5) :=
  Dec.shift (j := 15) (k := 0) (pjm_0 feat) wj_15 (Nat.zero_le _)

/-- The registers at the jump: `rdx` = `st`, `esi` = `fp->_fileno`, `edi` = 1. -/
abbrev ifG (V : Addr → Byte) (g : Gprs) : Gprs :=
  { g with rdx := g.rsi, rsi := rdd(V, g.rdi + 112#64).setWidth 64, rdi := 1#64 }

variable {F : Footprint} {Wl : List Rgn}

/-- `mov rdx, rsi; mov esi, [rdi + 112]; mov edi, 1`. -/
theorem vc_0 {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (hf : ∀ i < 4, Foot F.data (Addr.add (g.rdi + 112#64) i)) :
    W_0 F Wl (fun j' g' _ V' => j' = 15 ∧ g' = ifG V g ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hf ⊢
  wpx [W_0, o0, ifG]
  all_goals repeat' (first | exact rfl | assumption | exact trivial | apply And.intro | intro _)

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {X : State} {t : Nat} {V : Addr → Byte}

/-- `_IO_file_stat (fp, st)` (`fp` = `rdi`, `st` = `rsi`) from its entry: at `__fxstat`'s entry with the registers
`ifG`, no byte written (`kf`). -/
theorem ifs_ok (c : Seg prof F Wl L s₀ o) (hin : CodeIn L ifs_at ifs) (hinF : CodeIn L Fxs.fxs_at Fxs.fxs)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = ifs_at)
    (hf : ∀ i < 4, Foot F.data (Addr.add (X.cpu.gpr.rdi + 112#64) i))
    (kf : ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y → Agree F Y.proc.mm.mem V → Y.cpu.rip = Fxs.fxs_at →
      Y.cpu.gpr = ifG V X.cpu.gpr → GoG prof L o gev gP gE Y t') :
    GoG prof L o gev gP gE X t := by
  refine (c_0 prof).run c hin (fun j' g' _ V' => j' = 15 ∧ g' = ifG V X.cpu.gpr ∧ V' = V) hK hA
    (by rw [addr_add_zero]; exact hrip) (vc_0 hf) ?_
  rintro j' g fl V₁ ⟨rfl, rfl, hV₁⟩ Y t₁ hKY hAY hrY hgY -
  subst V₁
  refine c.s_jmp_x hKY hAY hin (lt_len (by decide)) hrY (jmp_15 _) hinF (Fxs.lt_len (j := 0) (by decide))
    (by decide) ?_
  rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
  exact kf Y₂ t₂ hK₂ hA₂ (by rw [hr₂, addr_add_zero]) (by rw [hg₂, hgY])

end FV7z.Ifs
