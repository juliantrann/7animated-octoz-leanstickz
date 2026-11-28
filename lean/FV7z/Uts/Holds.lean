import FV7z.Uts.Cuts
import FV7z.Lemmas.LeafRet
import FV7z.Lemmas.FnFar
/-!
# `ConvertUtcFileTimeToString` (PLAN.md §M, M1)

7-Zip 26.06's `ConvertUtcFileTimeToString (ft, s, level)` at `0x457a10` in `7zzs`
(`CPP/Windows/PropVariantConv.cpp`; `objdump -d`): `return ConvertUtcFileTimeToString2 (ft, 0, s, level, 0);` as a
tail jump (14) to `0x4576f0` (its code a hypothesis, `hinT`, as in `FV7z/Aid/Holds.lean`):
`mov ecx, edx; xor r8d, r8d; mov rdx, rsi; xor esi, esi`.

- `gU`: the registers at the jump; `vc_0`: the four instructions.
- `uts_ok`: from the entry, at `ConvertUtcFileTimeToString2` with the registers `gU`, the bytes as they were.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Uts

/-- The tail jump. -/
def pjm : List Byte := [0xe9, 0xcd, 0xfc, 0xff, 0xff]
theorem pjm_0 : ∀ feat, Dec feat pjm 0 (FV7z.mk .jmp 64 [.rel 18446744073709550797] 5) := by dec_rfl
theorem wj_14 : pjm <+: uts.drop 14 := by decide +kernel
theorem jmp_14 (feat : Features) : Dec feat uts 14 (FV7z.mk .jmp 64 [.rel 18446744073709550797] 5) :=
  Dec.shift (j := 14) (k := 0) (pjm_0 feat) wj_14 (Nat.zero_le _)

/-- `ConvertUtcFileTimeToString2` (not proved here). -/
abbrev tgt_at : Addr := 0x4576f0
theorem tgt14 : uts_at.add (14 + 5) + BitVec.ofNat 64 18446744073709550797 = tgt_at.add 0 := by decide

/-- The registers at the jump: `rsi` = `ns100` = 0, `rdx` = `s`, `ecx` = `level`, `r8` = `flags` = 0. -/
abbrev gU (g : Gprs) : Gprs :=
  { g with rcx := BitVec.setWidth 64 (BitVec.setWidth 32 g.rdx), rdx := g.rsi, rsi := 0#64, r8 := 0#64 }

variable {prof : Profile} {F : Footprint} {Wl : List Rgn} {L : List (Addr × List Byte)} {s₀ : State}
  {o : Oracle} {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {X : State} {t : Nat} {V : Addr → Byte}

/-- `mov ecx, edx; xor r8d, r8d; mov rdx, rsi; xor esi, esi`. -/
theorem vc_0 {g : Gprs} {f : Rflags} : wp F Wl o0 (fun g' _ V' => g' = gU g ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [o0, gU, BitVec.xor_self, BitVec.setWidth_zero]
  all_goals first
  | exact ⟨rfl, rfl⟩
  | rfl
  | trivial

/-- `ConvertUtcFileTimeToString (ft, s, level)` from its entry: at `ConvertUtcFileTimeToString2` with the registers
`gU`. -/
theorem uts_ok (c : Seg prof F Wl L s₀ o) (hin : CodeIn L uts_at uts) (hK : KeptW Wl s₀ X)
    (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = uts_at)
    {cT : List Byte} (hinT : CodeIn L tgt_at cT) (hT : 0 < cT.length)
    (k : ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y → Agree F Y.proc.mm.mem V → Y.cpu.rip = tgt_at →
      Y.cpu.gpr = gU X.cpu.gpr → GoG prof L o gev gP gE Y t') :
    GoG prof L o gev gP gE X t := by
  refine (c_0 prof).run c hin (fun j' g' _ V' => j' = 14 ∧ g' = gU X.cpu.gpr ∧ V' = V) hK hA
    (by rw [addr_add_zero]; exact hrip) (wp_mono o0 (fun _ _ _ h => ⟨rfl, h⟩) vc_0) ?_
  rintro j' g fl V₁ ⟨rfl, rfl, hV₁⟩ Y t₁ hKY hAY hrY hgY -
  subst V₁
  refine c.s_jmp_x hKY hAY hin (lt_len (by decide)) hrY (jmp_14 _) hinT hT tgt14 ?_
  rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
  exact k Y₂ t₂ hK₂ hA₂ (by rw [hr₂, addr_add_zero]) (hg₂.trans hgY)

end FV7z.Uts
