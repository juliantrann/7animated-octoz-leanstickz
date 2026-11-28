import FV7z.Oex.Cuts
import FV7z.Obw.Code
import FV7z.Lemmas.FnFar
/-!
# `NWindows::NFile::NIO::COutFile::Open_EXISTING (name)` (PLAN.md §M, M1)

7-Zip 26.06's `COutFile::Open_EXISTING (name)` at `0x456290` in `7zzs` (`CPP/Windows/FileIO.cpp`; `objdump -d`):
`return OpenBinary_forWrite_oflag (name, O_WRONLY)` as `mov edx, 1` and the tail `jmp` (9) to `Obw.obw_at`.

- `vc_0`: `edx` = 1, the rest as at the entry.
- `oex_ok`: from the entry to `OpenBinary_forWrite_oflag`'s entry (`kj`).
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Oex

/-- The tail `jmp` to `OpenBinary_forWrite_oflag`. -/
def pjm : List Byte := [0xe9, 0xb2, 0xff, 0xff, 0xff]
theorem pjm_0 : ∀ feat, Dec feat pjm 0 (FV7z.mk .jmp 64 [.rel 18446744073709551538] 5) := by dec_rfl
theorem wj_9 : pjm <+: oex.drop 9 := by decide +kernel
theorem jmp_9 (feat : Features) : Dec feat oex 9 (FV7z.mk .jmp 64 [.rel 18446744073709551538] 5) :=
  Dec.shift (j := 9) (k := 0) (pjm_0 feat) wj_9 (Nat.zero_le _)
theorem tgt_9 : oex_at.add (9 + 5) + BitVec.ofNat 64 18446744073709551538 = Obw.obw_at.add 0 := by decide

theorem obw_lt : 0 < Obw.obw.length := by rw [Obw.obw_length]; decide

variable {F : Footprint} {Wl : List Rgn}

/-- `mov edx, 1` to the `jmp` at 9. -/
theorem vc_0 {g : Gprs} {f : Rflags} {V : Addr → Byte} :
    W_0 F Wl (fun j' g' _ V' => j' = 9 ∧ g' = { g with rdx := BitVec.setWidth 64 1#32 } ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_0, o0]
  all_goals repeat'
    first
    | exact rfl
    | exact trivial
    | apply And.intro
    | intro _

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {X : State} {t : Nat} {V : Addr → Byte}

/-- `COutFile::Open_EXISTING (name)` from its entry: at `OpenBinary_forWrite_oflag`'s entry with the bytes as they
were and the registers as at the entry but `edx` = 1 (`kj`). -/
theorem oex_ok (c : Seg prof F Wl L s₀ o) (hin : CodeIn L oex_at oex) (hinO : CodeIn L Obw.obw_at Obw.obw)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = oex_at)
    (kj : ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y → Agree F Y.proc.mm.mem V → Y.cpu.rip = Obw.obw_at →
      Y.cpu.gpr = { X.cpu.gpr with rdx := BitVec.setWidth 64 1#32 } → GoG prof L o gev gP gE Y t') :
    GoG prof L o gev gP gE X t := by
  have hrip' : X.cpu.rip = oex_at.add 0 := by rw [addr_add_zero]; exact hrip
  refine (c_0 prof).run c hin
    (fun j' g' _ V' => j' = 9 ∧ g' = { X.cpu.gpr with rdx := BitVec.setWidth 64 1#32 } ∧ V' = V)
    hK hA hrip' vc_0 ?_
  rintro j' g fl V₁ ⟨rfl, rfl, hV₁⟩ Y t₁ hKY hAY hrY hgY -
  subst V₁
  refine c.s_jmp_x hKY hAY hin (lt_len (by decide)) hrY (jmp_9 _) hinO (tgt := 0) obw_lt tgt_9 ?_
  rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
  exact kj Y₂ t₂ hK₂ hA₂ (by rw [hr₂, addr_add_zero]) (by rw [hg₂, hgY])

end FV7z.Oex
