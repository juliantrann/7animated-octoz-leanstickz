import FV7z.Sfs.Cuts
import FV7z.Fre.Blocks
/-!
# `SysFreeString` (PLAN.md §M, M1)

7-Zip 26.06's `SysFreeString (bstr)` at `0x5a00c0` in `7zzs` (`CPP/Common/MyWindows.cpp`; `objdump -d`): a null
`bstr`, the `ret` (24); else `sub rdi, 4` and a tail jump to `free` (`Fre.fre_at`) at the allocation, the 4-byte
length before the string.

- `vc_z`, `vc_nz`: the two ways from the entry; `sfs_ok`: from the entry to the return address (`k0`) or to `free`'s
  entry with `rdi` 4 lower, the other registers as at the entry (`kf`).
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Sfs

/-- The jump to `free`. -/
def pjm : List Byte := [0xe9, 0x7e, 0x36, 0x09, 0x00]
theorem pjm_0 : ∀ feat, Dec feat pjm 0 (FV7z.mk .jmp 64 [.rel 603774] 5) := by dec_rfl
theorem wj_13 : pjm <+: sfs.drop 13 := by decide +kernel
theorem jmp_13 (feat : Features) : Dec feat sfs 13 (FV7z.mk .jmp 64 [.rel 603774] 5) :=
  Dec.shift (j := 13) (k := 0) (pjm_0 feat) wj_13 (Nat.zero_le _)

/-- The `ret`. -/
def pret : List Byte := [0xc3]
theorem pret_0 : ∀ feat, Dec feat pret 0 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem w_24 : pret <+: sfs.drop 24 := by decide +kernel
theorem ret_24 (feat : Features) : Dec feat sfs 24 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 24) (k := 0) (pret_0 feat) w_24 (Nat.zero_le _)

variable {F : Footprint} {Wl : List Rgn}

/-- A null `bstr`: to the `ret`. -/
theorem vc_z {g : Gprs} {f : Rflags} {V : Addr → Byte} (h : g.rdi = 0) :
    W_0 F Wl (fun j' g' _ V' => j' = 24 ∧ g' = g ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h ⊢
  subst h
  wpx [W_0, W_9, o0, o1, BitVec.and_self, beq_self_eq_true, Bool.true_eq_false, Bool.false_eq_true, false_implies, implies_true]
  all_goals repeat' (first | exact rfl | exact trivial | apply And.intro | intro _)
  all_goals (exfalso; simp_all)

/-- Not null: to the jump, `rdi` 4 lower. -/
theorem vc_nz {g : Gprs} {f : Rflags} {V : Addr → Byte} (h : g.rdi ≠ 0) :
    W_0 F Wl (fun j' g' _ V' => j' = 13 ∧ g' = { g with rdi := g.rdi - 4#64 } ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h ⊢
  have hz : (rdi == 0#64) = false := beq_eq_false_iff_ne.2 h
  wpx [W_0, W_9, o0, o1, BitVec.and_self, hz, Bool.true_eq_false, Bool.false_eq_true, false_implies, implies_true]
  all_goals repeat' (first | exact rfl | exact trivial | apply And.intro | intro _)

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop} {X : State}
  {t : Nat} {V : Addr → Byte}

/-- `SysFreeString (bstr)` from its entry: null, at the return address, the return address popped (`k0`); else at
`free`'s entry with `rdi` the allocation (`bstr - 4`), the other registers as at the entry (`kf`). -/
theorem sfs_ok (c : Seg prof F Wl L s₀ o) (hin : CodeIn L sfs_at sfs) (hinF : CodeIn L Fre.fre_at Fre.fre)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = sfs_at)
    (hl : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsp i))
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (hra : ofBytesLE 64 ((byteAddrs X.cpu.gpr.rsp 8).map V) = e₂.add j₂)
    (k0 : X.cpu.gpr.rdi = 0 → ∀ (Z : State) (t' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V →
      Z.cpu.rip = e₂.add j₂ → Z.cpu.gpr = X.cpu.gpr.set 4 (X.cpu.gpr.rsp + 8) → GoG prof L o gev gP gE Z t')
    (kf : X.cpu.gpr.rdi ≠ 0 → ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y → Agree F Y.proc.mm.mem V →
      Y.cpu.rip = Fre.fre_at → Y.cpu.gpr = { X.cpu.gpr with rdi := X.cpu.gpr.rdi - 4#64 } →
      GoG prof L o gev gP gE Y t') :
    GoG prof L o gev gP gE X t := by
  have hrip' : X.cpu.rip = sfs_at.add 0 := by rw [addr_add_zero]; exact hrip
  by_cases h : X.cpu.gpr.rdi = 0
  · refine (c_0 prof).run c hin _ hK hA hrip' (vc_z h) ?_
    rintro j' g fl V' ⟨rfl, hg, hV'⟩ Y t₁ hKY hAY hrY hgY -
    subst V'
    have hsp : Y.cpu.gpr.rsp = X.cpu.gpr.rsp := by rw [hgY, hg]
    refine c.s_ret hKY hAY hin (lt_len (by decide)) hrY (ret_24 _) (fun i hi => by rw [hsp]; exact hl i hi) hin₂ h₂
      (by rw [hsp]; exact hra) ?_
    rintro Z t₂ hKZ hAZ ⟨hrZ, hgZ⟩
    exact k0 h Z t₂ hKZ hAZ hrZ (by rw [hgZ, hgY, hg])
  · refine (c_0 prof).run c hin _ hK hA hrip' (vc_nz h) ?_
    rintro j' g fl V' ⟨rfl, hg, hV'⟩ Y t₁ hKY hAY hrY hgY -
    subst V'
    refine c.s_jmp_x hKY hAY hin (lt_len (by decide)) hrY (jmp_13 _) hinF (Fre.lt_len (j := 0) (by decide))
      (by decide) ?_
    rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
    exact kf h Y₂ t₂ hK₂ hA₂ (by rw [hr₂, addr_add_zero]) (by rw [hg₂, hgY, hg])

end FV7z.Sfs
