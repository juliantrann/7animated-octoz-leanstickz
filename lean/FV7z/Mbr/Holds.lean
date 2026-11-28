import FV7z.Mbr.Cuts
import FV7z.Lemmas.LeafRet
import FV7z.Lemmas.FnFar
/-!
# `__mbsrtowcs` (PLAN.md §M, M1)

glibc 2.31's `__mbsrtowcs (dst, src, len, ps)` at `0x65d320` in `7zzs` (`wcsmbs/mbsrtowcs.c`; `objdump -d`):
`return __mbsrtowcs_l (dst, src, len, ps ?: &state, _NL_CURRENT_LOCALE);` as a tail jump to `__mbsrtowcs_l` at
`0x65ddb0` (its code a hypothesis, `hinT`): `rcx` = `ps`, or the static `state` at `0x7a45b0` for NULL (`cmove`,
`ps0`); `r8` = the thread's locale, the 8 bytes at `fs:-128` (`fb` the `fs` base); `rax` = -128.

- `ps0`, `gA`: the registers at the jump; `vc_0`: the code to the jump, by the value of `ps`.
- `mbr_ok`: from the entry, at `0x65ddb0` with the registers `gA`.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Mbr

/-- The tail jump. -/
def pjm : List Byte := [0xe9, 0x6e, 0x0a, 0x00, 0x00]
theorem pjm_0 : ∀ feat, Dec feat pjm 0 (FV7z.mk .jmp 64 [.rel 2670] 5) := by dec_rfl
theorem wj_29 : pjm <+: mbr.drop 29 := by decide +kernel
theorem jmp_29 (feat : Features) : Dec feat mbr 29 (FV7z.mk .jmp 64 [.rel 2670] 5) :=
  Dec.shift (j := 29) (k := 0) (pjm_0 feat) wj_29 (Nat.zero_le _)

/-- `__mbsrtowcs_l` (not proved here). -/
abbrev tgt_at : Addr := 0x65ddb0
theorem tgt29 : mbr_at.add (29 + 5) + BitVec.ofNat 64 2670 = tgt_at.add 0 := by decide

/-- `ps ?: &state`. -/
def ps0 (x : BitVec 64) : BitVec 64 := if x = 0#64 then 8013232#64 else x

/-- The registers at the jump (`fb` the `fs` base, `c` = `ps0 ps`): `rax` = -128, `rcx` = `c`, `r8` = the locale. -/
abbrev gA (fb : Addr) (V : Addr → Byte) (g : Gprs) (c : BitVec 64) : Gprs :=
  { g with rax := 18446744073709551488#64, rcx := c, r8 := rdq(V, fb + 18446744073709551488#64) }

variable {prof : Profile} {F : Footprint} {Wl : List Rgn} {L : List (Addr × List Byte)} {s₀ : State}
  {o : Oracle} {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {X : State} {t : Nat} {V : Addr → Byte}

/-- `lea rax, [state]; test rcx, rcx; cmove rcx, rax; mov rax, -128; mov r8, fs:[rax]`, by the value `c` of
`rcx` after the `cmove`. -/
theorem vc_0 {fb : Addr} {g : Gprs} {f : Rflags} {c : BitVec 64}
    (hv : (g.rcx = 0#64 ∧ c = 8013232#64) ∨ (¬g.rcx = 0#64 ∧ c = g.rcx))
    (hl : ∀ i < 8, Foot F.data (Addr.add (fb + 18446744073709551488#64) i)) :
    W_0 fb F Wl (fun j' g' _ V' => j' = 29 ∧ g' = gA fb V g c ∧ V' = V) g f V := by
  rcases hv with ⟨hs, rfl⟩ | ⟨hs, rfl⟩
  · obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
    dsimp only at hs hl ⊢
    subst hs
    wpx [W_0, o0, gA, Op.cmov64, Op.ldf, BitVec.and_self, beq_self_eq_true, ↓reduceIte]
    all_goals repeat' (first
      | exact ⟨rfl, rfl, rfl⟩
      | with_reducible exact hl
      | rfl
      | trivial
      | apply And.intro
      | intro _)
  · obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
    dsimp only at hs hl ⊢
    have hb : (rcx == 0) = false := by simpa [beq_eq_false_iff_ne] using hs
    wpx [W_0, o0, gA, Op.cmov64, Op.ldf, BitVec.and_self, beq_eq_false_iff_ne.2 hs, hb, Bool.false_eq_true,
      ↓reduceIte]
    all_goals repeat' (first
      | exact ⟨rfl, rfl, rfl⟩
      | with_reducible exact hl
      | rfl
      | trivial
      | apply And.intro
      | intro _)

/-- `__mbsrtowcs (dst, src, len, ps)` from its entry (`fb` the `fs` base, the locale's 8 bytes readable): at
`__mbsrtowcs_l` with the registers `gA` (`rcx` = `ps0 ps`). -/
theorem mbr_ok {fb : Addr} (c : Seg prof F Wl L s₀ o) (hfs : s₀.cpu.seg.fsBase = fb) (hin : CodeIn L mbr_at mbr)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = mbr_at)
    (hl : ∀ i < 8, Foot F.data (Addr.add (fb + 18446744073709551488#64) i))
    {cT : List Byte} (hinT : CodeIn L tgt_at cT) (hT : 0 < cT.length)
    (k : ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y → Agree F Y.proc.mm.mem V → Y.cpu.rip = tgt_at →
      Y.cpu.gpr = gA fb V X.cpu.gpr (ps0 X.cpu.gpr.rcx) → GoG prof L o gev gP gE Y t') :
    GoG prof L o gev gP gE X t := by
  have hv : (X.cpu.gpr.rcx = 0#64 ∧ ps0 X.cpu.gpr.rcx = 8013232#64) ∨
      (¬X.cpu.gpr.rcx = 0#64 ∧ ps0 X.cpu.gpr.rcx = X.cpu.gpr.rcx) := by
    by_cases h : X.cpu.gpr.rcx = 0#64
    · exact Or.inl ⟨h, by simp [ps0, h]⟩
    · exact Or.inr ⟨h, by simp [ps0, h]⟩
  refine (c_0 prof fb).run c hfs hin (fun j' g' _ V' => j' = 29 ∧ g' = gA fb V X.cpu.gpr (ps0 X.cpu.gpr.rcx) ∧
      V' = V) hK hA (by rw [addr_add_zero]; exact hrip) (vc_0 hv hl) ?_
  rintro j' g fl V₁ ⟨rfl, rfl, hV₁⟩ Y t₁ hKY hAY hrY hgY -
  subst V₁
  refine c.s_jmp_x hKY hAY hin (lt_len (by decide)) hrY (jmp_29 _) hinT hT tgt29 ?_
  rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
  exact k Y₂ t₂ hK₂ hA₂ (by rw [hr₂, addr_add_zero]) (hg₂.trans hgY)

end FV7z.Mbr
