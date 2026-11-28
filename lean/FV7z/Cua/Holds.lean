import FV7z.Cua.Cuts
import FV7z.Lemmas.LeafRet
import FV7z.Lemmas.FnFar
/-!
# `CStdOutStream::Convert_UString_to_AString` (0x5a14a0): from the entry to its tail jumps (PLAN.md §M, M1)

7-Zip 26.06's `CStdOutStream::Convert_UString_to_AString (s, temp)` (`CPP/Common/StdOutStream.cpp`; `objdump -d`)
at `0x5a14a0` in `7zzs`: `this` = `rdi`, `s` = `rsi`, `temp` = `rdx`. By `CodePage` (the 4 bytes at `this + 12`):
`CP_UTF8` (65001), a tail jump to `ConvertUnicodeToUTF8 (s, temp)` at `0x4520b0` (70); else a tail jump to
`UnicodeStringToMultiByte2 (temp, s, codePage)` at `0x450d20` (33; at 56 with `codePage` 1 for `CodePage` = -1).
The callees' code is a hypothesis.

- `vc_0`: from the entry to one of the three jumps, the registers as at the entry but for `rdx`, `rsi`, `rdi`, `r8`,
  `r9`, the bytes as they were.
- `cua_ok`: from the entry to `UnicodeStringToMultiByte2`'s entry with `rdi` = `temp`, `rsi` = `s` (`kM`), or to
  `ConvertUnicodeToUTF8`'s with `rdi` = `s`, `rsi` = `temp` (`kU`); `rsp` and the return address as at the entry.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Cua
set_option linter.unusedVariables false

/-- The tail jump at 33. -/
def pj33 : List Byte := [0xe9, 0x5a, 0xf8, 0xea, 0xff]
theorem pj33_0 : ∀ feat, Dec feat pj33 0 (FV7z.mk .jmp 64 [.rel 18446744073708173402] 5) := by dec_rfl
theorem wj_33 : pj33 <+: cua.drop 33 := by decide +kernel
theorem jmp_33 (feat : Features) : Dec feat cua 33 (FV7z.mk .jmp 64 [.rel 18446744073708173402] 5) :=
  Dec.shift (j := 33) (k := 0) (pj33_0 feat) wj_33 (Nat.zero_le _)

/-- The tail jump at 56. -/
def pj56 : List Byte := [0xe9, 0x43, 0xf8, 0xea, 0xff]
theorem pj56_0 : ∀ feat, Dec feat pj56 0 (FV7z.mk .jmp 64 [.rel 18446744073708173379] 5) := by dec_rfl
theorem wj_56 : pj56 <+: cua.drop 56 := by decide +kernel
theorem jmp_56 (feat : Features) : Dec feat cua 56 (FV7z.mk .jmp 64 [.rel 18446744073708173379] 5) :=
  Dec.shift (j := 56) (k := 0) (pj56_0 feat) wj_56 (Nat.zero_le _)

/-- The tail jump at 70. -/
def pj70 : List Byte := [0xe9, 0xc5, 0x0b, 0xeb, 0xff]
theorem pj70_0 : ∀ feat, Dec feat pj70 0 (FV7z.mk .jmp 64 [.rel 18446744073708178373] 5) := by dec_rfl
theorem wj_70 : pj70 <+: cua.drop 70 := by decide +kernel
theorem jmp_70 (feat : Features) : Dec feat cua 70 (FV7z.mk .jmp 64 [.rel 18446744073708178373] 5) :=
  Dec.shift (j := 70) (k := 0) (pj70_0 feat) wj_70 (Nat.zero_le _)

/-- `UnicodeStringToMultiByte2`'s entry (its code a hypothesis). -/
abbrev mb_at : Addr := 0x450d20
/-- `ConvertUnicodeToUTF8`'s entry (its code a hypothesis). -/
abbrev u8_at : Addr := 0x4520b0

/-- The registers at the jumps to `UnicodeStringToMultiByte2` (`rdx` = `codePage`). -/
abbrev gM (g : Gprs) (a : BitVec 64) : Gprs := { g with rdx := a, rdi := g.rdx, r8 := g.rsi, r9 := g.rdi }
/-- The registers at the jump to `ConvertUnicodeToUTF8`. -/
abbrev gU (g : Gprs) (a : BitVec 64) : Gprs :=
  { g with rdx := a, rsi := g.rdx, rdi := g.rsi, r8 := g.rsi, r9 := g.rdi }

variable {F : Footprint} {Wl : List Rgn}

/-- From the entry: `CodePage` read, to one of the three jumps. -/
theorem vc_0 {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (f12 : ∀ i < 4, Foot F.data (Addr.add (g.rdi + 12#64) i)) :
    W_0 F Wl (fun j' g' _ V' => V' = V ∧ ((j' = 33 ∧ ∃ a, g' = gM g a) ∨ (j' = 56 ∧ ∃ a, g' = gM g a) ∨
      (j' = 70 ∧ ∃ a, g' = gU g a))) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [gM, gU] at f12 ⊢
  wpx [W_0, W_22, W_30, W_48, W_64, o0, o1, o2, o3, o4]
  all_goals repeat' (first
    | exact ⟨rfl, Or.inl ⟨rfl, _, rfl⟩⟩
    | exact ⟨rfl, Or.inr (Or.inl ⟨rfl, _, rfl⟩)⟩
    | exact ⟨rfl, Or.inr (Or.inr ⟨rfl, _, rfl⟩)⟩
    | with_reducible exact f12
    | exact trivial
    | apply And.intro
    | intro _)

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop} {X : State}
  {t : Nat} {V : Addr → Byte}

/-- `Convert_UString_to_AString (this, s, temp)` from its entry, `CodePage` readable: at `UnicodeStringToMultiByte2`
with the registers `gM` (`kM`) or at `ConvertUnicodeToUTF8` with the registers `gU` (`kU`), the bytes as they were. -/
theorem cua_ok (c : Seg prof F Wl L s₀ o) (hin : CodeIn L cua_at cua) (hK : KeptW Wl s₀ X)
    (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = cua_at)
    (f12 : ∀ i < 4, Foot F.data (Addr.add (X.cpu.gpr.rdi + 12#64) i))
    {cM : List Byte} (hinM : CodeIn L mb_at cM) (hM : 0 < cM.length)
    {cU : List Byte} (hinU : CodeIn L u8_at cU) (hU : 0 < cU.length)
    (kM : ∀ (a : BitVec 64) (Y : State) (t' : Nat), KeptW Wl s₀ Y → Agree F Y.proc.mm.mem V →
      Y.cpu.rip = mb_at → Y.cpu.gpr = gM X.cpu.gpr a → GoG prof L o gev gP gE Y t')
    (kU : ∀ (a : BitVec 64) (Y : State) (t' : Nat), KeptW Wl s₀ Y → Agree F Y.proc.mm.mem V →
      Y.cpu.rip = u8_at → Y.cpu.gpr = gU X.cpu.gpr a → GoG prof L o gev gP gE Y t') :
    GoG prof L o gev gP gE X t := by
  refine (c_0 prof).run c hin (fun j' g' _ V' => V' = V ∧ ((j' = 33 ∧ ∃ a, g' = gM X.cpu.gpr a) ∨
      (j' = 56 ∧ ∃ a, g' = gM X.cpu.gpr a) ∨ (j' = 70 ∧ ∃ a, g' = gU X.cpu.gpr a))) hK hA
    (by rw [addr_add_zero]; exact hrip) (vc_0 f12) ?_
  rintro j' g fl V₁ ⟨rfl, h⟩ Y t₁ hKY hAY hrY hgY -
  rcases h with ⟨rfl, a, rfl⟩ | ⟨rfl, a, rfl⟩ | ⟨rfl, a, rfl⟩
  · refine c.s_jmp_x hKY hAY hin (lt_len (by decide)) hrY (jmp_33 _) hinM hM (by decide) ?_
    rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
    exact kM a Y₂ t₂ hK₂ hA₂ (by rw [hr₂, addr_add_zero]) (hg₂.trans hgY)
  · refine c.s_jmp_x hKY hAY hin (lt_len (by decide)) hrY (jmp_56 _) hinM hM (by decide) ?_
    rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
    exact kM a Y₂ t₂ hK₂ hA₂ (by rw [hr₂, addr_add_zero]) (hg₂.trans hgY)
  · refine c.s_jmp_x hKY hAY hin (lt_len (by decide)) hrY (jmp_70 _) hinU hU (by decide) ?_
    rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
    exact kU a Y₂ t₂ hK₂ hA₂ (by rw [hr₂, addr_add_zero]) (hg₂.trans hgY)

end FV7z.Cua
