import FV7z.Cao.Cuts
import FV7z.Obw.Code
import FV7z.Lemmas.FnFar
/-!
# `NWindows::NFile::NIO::COutFile::Create_ALWAYS_or_Open_ALWAYS (name, createAlways)` (PLAN.md §M, M1)

7-Zip 26.06's `COutFile::Create_ALWAYS_or_Open_ALWAYS (name, createAlways)` at `0x4562c0` in `7zzs`
(`CPP/Windows/FileIO.cpp`; `objdump -d`): `return OpenBinary_forWrite_oflag (name, createAlways ? O_WRONLY | O_CREAT |
O_TRUNC : O_WRONLY | O_CREAT)` as `cmp dl, 1; sbb edx, edx; and edx, 0xfffffe00; add edx, 0x241` and the tail `jmp`
(21) to `Obw.obw_at`.

- `ofl`: the flags for the byte `dl`: `0x41` if it is 0, else `0x241`; `ofl_eq`: what the four instructions compute.
- `vc_0`: `edx` = `ofl dl`, the rest as at the entry.
- `cao_ok`: from the entry to `OpenBinary_forWrite_oflag`'s entry (`kj`).
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Cao

/-- The tail `jmp` to `OpenBinary_forWrite_oflag`. -/
def pjm : List Byte := [0xe9, 0x76, 0xff, 0xff, 0xff]
theorem pjm_0 : ∀ feat, Dec feat pjm 0 (FV7z.mk .jmp 64 [.rel 18446744073709551478] 5) := by dec_rfl
theorem wj_21 : pjm <+: cao.drop 21 := by decide +kernel
theorem jmp_21 (feat : Features) : Dec feat cao 21 (FV7z.mk .jmp 64 [.rel 18446744073709551478] 5) :=
  Dec.shift (j := 21) (k := 0) (pjm_0 feat) wj_21 (Nat.zero_le _)
theorem tgt_21 : cao_at.add (21 + 5) + BitVec.ofNat 64 18446744073709551478 = Obw.obw_at.add 0 := by decide

theorem obw_lt : 0 < Obw.obw.length := by rw [Obw.obw_length]; decide

/-- The flags for `dl` = the low byte of `a`. -/
def ofl (a : BitVec 64) : BitVec 32 := if BitVec.setWidth 8 a = 0#8 then 65#32 else 577#32

/-- `cmp dl, 1; sbb edx, edx; and edx, 0xfffffe00; add edx, 0x241` as `ofl` (as `FV7z.Cpv.sgc_eq`). -/
theorem ofl_eq (a : BitVec 64) :
    ((BitVec.setWidth 32 a - BitVec.setWidth 32 a -
      BitVec.setWidth 32 (BitVec.ofBool (decide ((BitVec.setWidth 8 a).toNat < 1)))) &&& 4294966784#32) + 577#32 =
      ofl a := by
  rw [BitVec.sub_self]
  unfold ofl
  by_cases hw : (BitVec.setWidth 8 a).toNat < 1
  · rw [decide_eq_true hw,
      if_pos (BitVec.eq_of_toNat_eq (by simp only [BitVec.toNat_ofNat, Nat.zero_mod]; omega))]
    decide
  · rw [decide_eq_false hw, if_neg fun h => hw (by rw [h]; decide)]
    decide

variable {F : Footprint} {Wl : List Rgn}

/-- `cmp dl, 1; sbb edx, edx; and edx, 0xfffffe00; add edx, 0x241` to the `jmp` at 21. -/
theorem vc_0 {g : Gprs} {f : Rflags} {V : Addr → Byte} :
    W_0 F Wl (fun j' g' _ V' => j' = 21 ∧ g' = { g with rdx := BitVec.setWidth 64 (ofl g.rdx) } ∧ V' = V)
      g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_0, o0, ofl_eq]
  all_goals repeat'
    first
    | exact rfl
    | exact trivial
    | apply And.intro
    | intro _

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {X : State} {t : Nat} {V : Addr → Byte}

/-- `COutFile::Create_ALWAYS_or_Open_ALWAYS (name, createAlways)` from its entry: at `OpenBinary_forWrite_oflag`'s
entry with the bytes as they were and the registers as at the entry but `edx` = `ofl dl` (`kj`). -/
theorem cao_ok (c : Seg prof F Wl L s₀ o) (hin : CodeIn L cao_at cao) (hinO : CodeIn L Obw.obw_at Obw.obw)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = cao_at)
    (kj : ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y → Agree F Y.proc.mm.mem V → Y.cpu.rip = Obw.obw_at →
      Y.cpu.gpr = { X.cpu.gpr with rdx := BitVec.setWidth 64 (ofl X.cpu.gpr.rdx) } →
      GoG prof L o gev gP gE Y t') :
    GoG prof L o gev gP gE X t := by
  have hrip' : X.cpu.rip = cao_at.add 0 := by rw [addr_add_zero]; exact hrip
  refine (c_0 prof).run c hin
    (fun j' g' _ V' => j' = 21 ∧ g' = { X.cpu.gpr with rdx := BitVec.setWidth 64 (ofl X.cpu.gpr.rdx) } ∧ V' = V)
    hK hA hrip' vc_0 ?_
  rintro j' g fl V₁ ⟨rfl, rfl, hV₁⟩ Y t₁ hKY hAY hrY hgY -
  subst V₁
  refine c.s_jmp_x hKY hAY hin (lt_len (by decide)) hrY (jmp_21 _) hinO (tgt := 0) obw_lt tgt_21 ?_
  rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
  exact kj Y₂ t₂ hK₂ hA₂ (by rw [hr₂, addr_add_zero]) (by rw [hg₂, hgY])

end FV7z.Cao
