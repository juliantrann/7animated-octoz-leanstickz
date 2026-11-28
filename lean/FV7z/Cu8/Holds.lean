import FV7z.Cu8.Cuts
import FV7z.Lemmas.LeafRet
import FV7z.Lemmas.FnFar
/-!
# `ConvertUnicodeToUTF8` (0x4520b0): from the entry to its tail jump (PLAN.md §M, M1)

7-Zip 26.06's `ConvertUnicodeToUTF8 (src, dest)` (`CPP/Common/UTFConvert.cpp`; `objdump -d`) at `0x4520b0` in
`7zzs`: `rax` = `0x79217c`, `edx` = the 4 bytes there (the global UTF-8 flags), a tail jump (13) to
`ConvertUnicodeToUTF8_Flags (src, dest, flags)` at `0x452010` (its code a hypothesis).

- `cu8_ok`: from the entry to `ConvertUnicodeToUTF8_Flags`'s entry, the registers as at the entry but for `rax`,
  `rdx`, the bytes as they were.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Cu8
set_option linter.unusedVariables false

/-- The tail jump. -/
def pjm : List Byte := [0xe9, 0x4e, 0xff, 0xff, 0xff]
theorem pjm_0 : ∀ feat, Dec feat pjm 0 (FV7z.mk .jmp 64 [.rel 18446744073709551438] 5) := by dec_rfl
theorem wj_13 : pjm <+: cu8.drop 13 := by decide +kernel
theorem jmp_13 (feat : Features) : Dec feat cu8 13 (FV7z.mk .jmp 64 [.rel 18446744073709551438] 5) :=
  Dec.shift (j := 13) (k := 0) (pjm_0 feat) wj_13 (Nat.zero_le _)

/-- `ConvertUnicodeToUTF8_Flags`'s entry (its code a hypothesis). -/
abbrev tgt_at : Addr := 0x452010

variable {F : Footprint} {Wl : List Rgn}

/-- From the entry: `rax`, `rdx` set, to the jump. -/
theorem vc_0 {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (ff : ∀ i < 4, Foot F.data (Addr.add (7938428#64) i)) :
    W_0 F Wl (fun j' g' _ V' => j' = 13 ∧ (∃ a d, g' = { g with rax := a, rdx := d }) ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_0, o0]
  all_goals repeat' (first
    | exact ⟨rfl, ⟨_, _, rfl⟩, rfl⟩
    | with_reducible exact ff
    | exact ff
    | exact trivial
    | apply And.intro
    | intro _)

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop} {X : State}
  {t : Nat} {V : Addr → Byte}

/-- `ConvertUnicodeToUTF8 (src, dest)` from its entry, the flags readable: at `ConvertUnicodeToUTF8_Flags`'s entry
with the registers of the entry but for `rax`, `rdx` (`kj`), the bytes as they were. -/
theorem cu8_ok (c : Seg prof F Wl L s₀ o) (hin : CodeIn L cu8_at cu8) (hK : KeptW Wl s₀ X)
    (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = cu8_at)
    (ff : ∀ i < 4, Foot F.data (Addr.add (7938428#64) i))
    {cT : List Byte} (hinT : CodeIn L tgt_at cT) (hT : 0 < cT.length)
    (kj : ∀ (a d : BitVec 64) (Y : State) (t' : Nat), KeptW Wl s₀ Y → Agree F Y.proc.mm.mem V →
      Y.cpu.rip = tgt_at → Y.cpu.gpr = { X.cpu.gpr with rax := a, rdx := d } → GoG prof L o gev gP gE Y t') :
    GoG prof L o gev gP gE X t := by
  refine (c_0 prof).run c hin (fun j' g' _ V' => j' = 13 ∧ (∃ a d, g' = { X.cpu.gpr with rax := a, rdx := d }) ∧
      V' = V) hK hA (by rw [addr_add_zero]; exact hrip) (vc_0 ff) ?_
  rintro j' g fl V₁ ⟨rfl, ⟨a, d, rfl⟩, rfl⟩ Y t₁ hKY hAY hrY hgY -
  refine c.s_jmp_x hKY hAY hin (lt_len (by decide)) hrY (jmp_13 _) hinT hT (by decide) ?_
  rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
  exact kj a d Y₂ t₂ hK₂ hA₂ (by rw [hr₂, addr_add_zero]) (hg₂.trans hgY)

end FV7z.Cu8
