import FV7z.Stw.Cuts
import FV7z.Lemmas.LeafRet
import FV7z.Lemmas.FnFar
/-!
# `__strtol` (PLAN.md §M, M1)

glibc 2.31's `__strtol (nptr, endptr, base)` at `0x623890` in `7zzs` (`stdlib/strtol.c`; `objdump -d`):
`____strtol_l_internal (nptr, endptr, base, 0, _NL_CURRENT_LOCALE)` as `mov rax, -128; xor ecx, ecx;
mov r8, fs:[rax]` (the thread's locale, at `fs` base - 128), then a tail jump to `0x6238b0` (`Stl.stl_at`,
`FV7z/Stl/Holds.lean`; its code a hypothesis, `hinT`).

- `gq`: the registers at the jump, `lc` the locale's pointer; `vc_0`: the straight-line code.
- `stw_ok`: from the entry (the `fs` base `fb`), at `0x6238b0` with the registers `gq` of the 8 bytes at `fb - 128`.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Stw

/-- The tail jump. -/
def pjm : List Byte := [0xe9, 0x0a, 0x00, 0x00, 0x00]
theorem pjm_0 : ∀ feat, Dec feat pjm 0 (FV7z.mk .jmp 64 [.rel 10] 5) := by dec_rfl
theorem wj_17 : pjm <+: stw.drop 17 := by decide +kernel
theorem jmp_17 (feat : Features) : Dec feat stw 17 (FV7z.mk .jmp 64 [.rel 10] 5) :=
  Dec.shift (j := 17) (k := 0) (pjm_0 feat) wj_17 (Nat.zero_le _)

/-- `____strtol_l_internal` (`Stl.stl_at`; not proved here). -/
abbrev tgt_at : Addr := 0x6238b0
theorem tgt_17 : stw_at.add (17 + 5) + BitVec.ofNat 64 10 = tgt_at.add 0 := by decide

/-- The registers at the jump: `rax` = -128, `rcx` = 0 (`group`), `r8` = `lc` (the locale). -/
abbrev gq (g : Gprs) (lc : BitVec 64) : Gprs :=
  { g with
      rax := 18446744073709551488#64,
      rcx := 0#64,
      r8 := lc }

/-- `xor r32, r32`. -/
theorem xz (x : BitVec 32) : BitVec.setWidth 64 (x ^^^ x) = 0#64 := by simp

variable {F : Footprint} {Wl : List Rgn}

/-- `mov rax, -128; xor ecx, ecx; mov r8, fs:[rax]`. -/
theorem vc_0 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (f1 : ∀ i < 8, Foot F.data ((fb + 18446744073709551488#64).add i))
    (h : ∀ fl, Q 17 (gq g rdq(V, fb + 18446744073709551488#64)) fl V) : W_0 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_0, o0, Op.ldf, xz, BitVec.reduceSetWidth]
  all_goals repeat' (first | exact h _ | with_reducible exact f1 | apply And.intro | intro _)

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {X : State} {t : Nat} {V : Addr → Byte}

/-- From its entry (the `fs` base `fb`): at `____strtol_l_internal` with the registers `gq` of the locale's pointer
at `fb - 128`. -/
theorem stw_ok {fb : Addr} (c : Seg prof F Wl L s₀ o) (hfs : s₀.cpu.seg.fsBase = fb) (hin : CodeIn L stw_at stw)
    {codeT : List Byte} (hinT : CodeIn L tgt_at codeT) (hT : 0 < codeT.length)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = stw_at)
    (f1 : ∀ i < 8, Foot F.data ((fb - 128#64).add i))
    (kf : ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y → Agree F Y.proc.mm.mem V → Y.cpu.rip = tgt_at →
      Y.cpu.gpr = gq X.cpu.gpr rdq(V, fb - 128#64) → GoG prof L o gev gP gE Y t') :
    GoG prof L o gev gP gE X t := by
  have e0 : fb - 128#64 = fb + 18446744073709551488#64 := by bv_omega
  rw [e0] at f1 kf
  refine (c_0 prof fb).run c hfs hin
    (fun j' g' _ V' => j' = 17 ∧ g' = gq X.cpu.gpr rdq(V, fb + 18446744073709551488#64) ∧ V' = V)
    hK hA (by rw [addr_add_zero]; exact hrip) (vc_0 f1 fun _ => ⟨rfl, rfl, rfl⟩) ?_
  rintro j' g fl V₁ ⟨rfl, hg, hV⟩ Y t₁ hKY hAY hrY hgY -
  subst hg; subst V₁
  refine c.s_jmp_x hKY hAY hin (lt_len (by decide)) hrY (jmp_17 _) hinT (tgt := 0) hT tgt_17 ?_
  rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
  exact kf Y₂ t₂ hK₂ hA₂ (by rw [hr₂, addr_add_zero]) (hg₂.trans hgY)

end FV7z.Stw
