import FV7z.Nan.Cuts
import FV7z.Lemmas.LeafRet
import FV7z.Lemmas.FnFar
/-!
# `__nan` (PLAN.md §M, M1)

glibc 2.31's `__nan (tagp)` at `0x4621f0` in `7zzs` (`math/s_nan.c`; `objdump -d`): `return __strtod_nan (tagp, NULL,
0);` as `endbr64; xor edx, edx; xor esi, esi`, then a tail jump to `0x461ed0` (`__strtod_nan`; its code a hypothesis,
`hinT`) with `rdi` = `tagp`, `rsi` = `NULL`, `rdx` = 0.

- `gq`: the registers at the jump; `vc_0`: the straight-line code.
- `nan_ok`: from the entry, at `0x461ed0` with the registers `gq`.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Nan

/-- The tail jump. -/
def pjm : List Byte := [0xe9, 0xd3, 0xfc, 0xff, 0xff]
theorem pjm_0 : ∀ feat, Dec feat pjm 0 (FV7z.mk .jmp 64 [.rel 18446744073709550803] 5) := by dec_rfl
theorem wj_8 : pjm <+: nan.drop 8 := by decide +kernel
theorem jmp_8 (feat : Features) : Dec feat nan 8 (FV7z.mk .jmp 64 [.rel 18446744073709550803] 5) :=
  Dec.shift (j := 8) (k := 0) (pjm_0 feat) wj_8 (Nat.zero_le _)

/-- `__strtod_nan (tagp, endptr, sep)` (not proved here). -/
abbrev tgt_at : Addr := 0x461ed0
theorem tgt_8 : nan_at.add (8 + 5) + BitVec.ofNat 64 18446744073709550803 = tgt_at.add 0 := by decide

/-- The registers at the jump. -/
abbrev gq (g : Gprs) : Gprs :=
  { g with
      rdx := 0#64,
      rsi := 0#64 }

/-- `xor r32, r32`. -/
theorem xz (x : BitVec 32) : BitVec.setWidth 64 (x ^^^ x) = 0#64 := by simp

variable {F : Footprint} {Wl : List Rgn}

/-- `endbr64; xor edx, edx; xor esi, esi`. -/
theorem vc_0 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (h : ∀ fl, Q 8 (gq g) fl V) : W_0 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_0, o0, xz, BitVec.reduceSetWidth]
  all_goals repeat' (first | exact h _ | apply And.intro | intro _)

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {X : State} {t : Nat} {V : Addr → Byte}

/-- From its entry: at `__strtod_nan (tagp, NULL, 0)` with the registers `gq`. -/
theorem nan_ok (c : Seg prof F Wl L s₀ o) (hin : CodeIn L nan_at nan)
    {codeT : List Byte} (hinT : CodeIn L tgt_at codeT) (hT : 0 < codeT.length)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = nan_at)
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

end FV7z.Nan
