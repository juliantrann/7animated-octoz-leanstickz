import FV7z.Gac.Cuts
import FV7z.Lemmas.LeafRet
import FV7z.Lemmas.FnFar
/-!
# `__gconv_alias_compare` (PLAN.md §M, M1)

glibc 2.31's `__gconv_alias_compare (p1, p2)` at `0x452930` in `7zzs` (`iconv/gconv_db.c`; `objdump -d`):
`return strcmp (s1->fromname, s2->fromname);` with `fromname` the first field of `struct gconv_alias`, as a tail jump
to `strcmp` at `0x452190` (its code a hypothesis, `hinT`) with `rsi` = `[rsi]` and `rdi` = `[rdi]`.

- `gA`: the registers at the jump; `vc_0`: the two loads.
- `gac_ok`: from the entry, at `0x452190` with the registers `gA`.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Gac

/-- The tail jump. -/
def pjm : List Byte := [0xe9, 0x51, 0xf8, 0xff, 0xff]
theorem pjm_0 : ∀ feat, Dec feat pjm 0 (FV7z.mk .jmp 64 [.rel 18446744073709549649] 5) := by dec_rfl
theorem wj_10 : pjm <+: gac.drop 10 := by decide +kernel
theorem jmp_10 (feat : Features) : Dec feat gac 10 (FV7z.mk .jmp 64 [.rel 18446744073709549649] 5) :=
  Dec.shift (j := 10) (k := 0) (pjm_0 feat) wj_10 (Nat.zero_le _)

/-- `strcmp` (not proved here). -/
abbrev tgt_at : Addr := 0x452190
theorem tgt10 : gac_at.add (10 + 5) + BitVec.ofNat 64 18446744073709549649 = tgt_at.add 0 := by decide

/-- The registers at the jump: `rsi` = `p2->fromname`, `rdi` = `p1->fromname`. -/
abbrev gA (V : Addr → Byte) (g : Gprs) : Gprs := { g with rsi := rdq(V, g.rsi), rdi := rdq(V, g.rdi) }

variable {prof : Profile} {F : Footprint} {Wl : List Rgn} {L : List (Addr × List Byte)} {s₀ : State}
  {o : Oracle} {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {X : State} {t : Nat} {V : Addr → Byte}

/-- `endbr64; mov rsi, [rsi]; mov rdi, [rdi]`. -/
theorem vc_0 {g : Gprs} {f : Rflags} (h6 : ∀ i < 8, Foot F.data (Addr.add g.rsi i))
    (h7 : ∀ i < 8, Foot F.data (Addr.add g.rdi i)) :
    wp F Wl o0 (fun g' _ V' => g' = gA V g ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h6 h7 ⊢
  wpx [o0, gA]
  all_goals repeat' (first
    | exact ⟨rfl, rfl⟩
    | with_reducible exact h6
    | with_reducible exact h7
    | rfl
    | trivial
    | apply And.intro
    | intro _)

/-- `__gconv_alias_compare (p1, p2)` from its entry (`p1->fromname` and `p2->fromname` readable): at `strcmp` with
the registers `gA`. -/
theorem gac_ok (c : Seg prof F Wl L s₀ o) (hin : CodeIn L gac_at gac) (hK : KeptW Wl s₀ X)
    (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = gac_at)
    (h6 : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsi i)) (h7 : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rdi i))
    {cT : List Byte} (hinT : CodeIn L tgt_at cT) (hT : 0 < cT.length)
    (k : ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y → Agree F Y.proc.mm.mem V → Y.cpu.rip = tgt_at →
      Y.cpu.gpr = gA V X.cpu.gpr → GoG prof L o gev gP gE Y t') :
    GoG prof L o gev gP gE X t := by
  refine (c_0 prof).run c hin (fun j' g' _ V' => j' = 10 ∧ g' = gA V X.cpu.gpr ∧ V' = V) hK hA
    (by rw [addr_add_zero]; exact hrip) (wp_mono o0 (fun _ _ _ h => ⟨rfl, h⟩) (vc_0 h6 h7)) ?_
  rintro j' g fl V₁ ⟨rfl, rfl, hV₁⟩ Y t₁ hKY hAY hrY hgY -
  subst V₁
  refine c.s_jmp_x hKY hAY hin (lt_len (by decide)) hrY (jmp_10 _) hinT hT tgt10 ?_
  rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
  exact k Y₂ t₂ hK₂ hA₂ (by rw [hr₂, addr_add_zero]) (hg₂.trans hgY)

end FV7z.Gac
