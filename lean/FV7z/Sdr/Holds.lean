import FV7z.Sdr.Cuts
import FV7z.Lemmas.LeafRet
import FV7z.Lemmas.FnFar
/-!
# `NWindows::NFile::NDir::SetDirTime` (PLAN.md §M, M1)

7-Zip 26.06's `NDir::SetDirTime (path, cTime, aTime, mTime)` at `0x4556e0` in `7zzs` (`CPP/Windows/FileDir.cpp`;
`objdump -d`), the Linux build: `cTime` is dropped and the rest goes on as a tail jump (12) to
`SetFileTime_Base (path, aTime, mTime, 0)` (`0x4549b0`, its code a hypothesis, `hinT`, as in `FV7z/Aid/Holds.lean`):
`mov rsi, rdx; mov rdx, rcx; xor ecx, ecx`.

- `gR`: the registers at the jump; `vc_0`: the three instructions.
- `sdr_ok`: from the entry, at `SetFileTime_Base` with the registers `gR`, the bytes as they were.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Sdr

/-- The tail jump. -/
def pjm : List Byte := [0xe9, 0xbf, 0xf2, 0xff, 0xff]
theorem pjm_0 : ∀ feat, Dec feat pjm 0 (FV7z.mk .jmp 64 [.rel 18446744073709548223] 5) := by dec_rfl
theorem wj_12 : pjm <+: sdr.drop 12 := by decide +kernel
theorem jmp_12 (feat : Features) : Dec feat sdr 12 (FV7z.mk .jmp 64 [.rel 18446744073709548223] 5) :=
  Dec.shift (j := 12) (k := 0) (pjm_0 feat) wj_12 (Nat.zero_le _)

/-- `SetFileTime_Base` (`[clone .isra.0]`, not proved here). -/
abbrev tgt_at : Addr := 0x4549b0
theorem tgt12 : sdr_at.add (12 + 5) + BitVec.ofNat 64 18446744073709548223 = tgt_at.add 0 := by decide

/-- The registers at the jump: `rsi` = `aTime`, `rdx` = `mTime`, `rcx` = 0. -/
abbrev gR (g : Gprs) : Gprs := { g with rcx := 0#64, rdx := g.rcx, rsi := g.rdx }

variable {prof : Profile} {F : Footprint} {Wl : List Rgn} {L : List (Addr × List Byte)} {s₀ : State}
  {o : Oracle} {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {X : State} {t : Nat} {V : Addr → Byte}

/-- `mov rsi, rdx; mov rdx, rcx; xor ecx, ecx`. -/
theorem vc_0 {g : Gprs} {f : Rflags} : wp F Wl o0 (fun g' _ V' => g' = gR g ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [o0, gR, BitVec.xor_self, BitVec.setWidth_zero]
  all_goals first
  | exact ⟨rfl, rfl⟩
  | rfl
  | trivial

/-- `NDir::SetDirTime (path, cTime, aTime, mTime)` from its entry: at `SetFileTime_Base` with the registers `gR`. -/
theorem sdr_ok (c : Seg prof F Wl L s₀ o) (hin : CodeIn L sdr_at sdr) (hK : KeptW Wl s₀ X)
    (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = sdr_at)
    {cT : List Byte} (hinT : CodeIn L tgt_at cT) (hT : 0 < cT.length)
    (k : ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y → Agree F Y.proc.mm.mem V → Y.cpu.rip = tgt_at →
      Y.cpu.gpr = gR X.cpu.gpr → GoG prof L o gev gP gE Y t') :
    GoG prof L o gev gP gE X t := by
  refine (c_0 prof).run c hin (fun j' g' _ V' => j' = 12 ∧ g' = gR X.cpu.gpr ∧ V' = V) hK hA
    (by rw [addr_add_zero]; exact hrip) (wp_mono o0 (fun _ _ _ h => ⟨rfl, h⟩) vc_0) ?_
  rintro j' g fl V₁ ⟨rfl, rfl, hV₁⟩ Y t₁ hKY hAY hrY hgY -
  subst V₁
  refine c.s_jmp_x hKY hAY hin (lt_len (by decide)) hrY (jmp_12 _) hinT hT tgt12 ?_
  rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
  exact k Y₂ t₂ hK₂ hA₂ (by rw [hr₂, addr_add_zero]) (hg₂.trans hgY)

end FV7z.Sdr
