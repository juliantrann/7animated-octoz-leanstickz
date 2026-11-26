import FV7z.Mya.Cuts
import FV7z.Lemmas.LeafRet
import FV7z.Lemmas.FnFar
/-!
# `MyAlloc` (PLAN.md §M, M1)

7-Zip 26.06's `MyAlloc (size)` at `0x41f3c0` in `7zzs` (`C/Alloc.c`): with `size` 0, null in `rax` and a `ret`; else a
tail jump to `0x633160` (glibc's `__libc_malloc` by the symbol table; its code a hypothesis, `hinT`) with the
registers of the entry.

- `mya_ok`: `size` not 0, the run at `0x633160` with the registers of the entry (`kj`); `size` 0, at the return
  address with the return address popped and `rax` 0 (`kr`).
-/open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Mya

/-- The tail jump. -/
def pjm : List Byte := [0xe9, 0x92, 0x3d, 0x21, 0x00]
theorem pjm_0 : ∀ feat, Dec feat pjm 0 (FV7z.mk .jmp 64 [.rel 2178450] 5) := by dec_rfl
theorem wj_9 : pjm <+: mya.drop 9 := by decide +kernel
theorem jmp_9 (feat : Features) : Dec feat mya 9 (FV7z.mk .jmp 64 [.rel 2178450] 5) :=
  Dec.shift (j := 9) (k := 0) (pjm_0 feat) wj_9 (Nat.zero_le _)

/-- The `ret`. -/
def pret : List Byte := [0xc3]
theorem pret_0 : ∀ feat, Dec feat pret 0 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem w_18 : pret <+: mya.drop 18 := by decide +kernel
theorem ret_18 (feat : Features) : Dec feat mya 18 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 18) (k := 0) (pret_0 feat) w_18 (Nat.zero_le _)

/-- The jump's target (glibc's code, not proved here). -/
abbrev tgt_at : Addr := 0x633160

variable {F : Footprint} {Wl : List Rgn}

/-- `size` 0: `eax` 0, to the `ret`. -/
theorem vc_z {g : Gprs} {f : Rflags} {V : Addr → Byte} (h : g.rdi = 0) :
    W_0 F Wl (fun j' g' _ V' => j' = 18 ∧ g' = g.set 0 0 ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h
  subst h
  wpx [W_0, W_16, o0, o1, lf_xz]
  first
  | done
  | rfl
  | exact ⟨fun _ => ⟨rfl, rfl⟩, fun hh => absurd hh (by decide)⟩
  | exact fun hh => absurd hh (by decide)
  | repeat' (first | rfl | trivial | (refine ⟨?_, ?_⟩) | (intro hh; exact absurd hh (by decide)) | intro _)

/-- `size` not 0: to the jump. -/
theorem vc_n {g : Gprs} {f : Rflags} {V : Addr → Byte} (h : g.rdi ≠ 0) :
    W_0 F Wl (fun j' g' _ V' => j' = 9 ∧ g' = g ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h
  wpx [W_0, W_16, o0, o1, lf_xz, BitVec.and_self, beq_iff_eq, h]
  first
  | done
  | rfl
  | exact ⟨fun hh => absurd hh h, fun _ => ⟨rfl, rfl⟩⟩
  | exact fun hh => absurd hh h
  | (intro hh; simp at hh; exact absurd hh h)
  | repeat' (first | rfl | trivial | (refine ⟨?_, ?_⟩) | (intro hh; exact absurd hh h) | intro _)

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop} {X : State}
  {t : Nat} {V : Addr → Byte}

/-- `MyAlloc (size)` from its entry: `size` not 0, at `0x633160` with the registers of the entry (`kj`); `size` 0, at
the return address with the return address popped and `rax` 0 (`kr`). -/
theorem mya_ok (c : Seg prof F Wl L s₀ o) (hin : CodeIn L mya_at mya) (hK : KeptW Wl s₀ X)
    (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = mya_at)
    {cT : List Byte} (hinT : CodeIn L tgt_at cT) (hT : 0 < cT.length)
    (hl : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsp i))
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (hra : ofBytesLE 64 ((byteAddrs X.cpu.gpr.rsp 8).map V) = e₂.add j₂)
    (kj : X.cpu.gpr.rdi ≠ 0 → ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y → Agree F Y.proc.mm.mem V →
      Y.cpu.rip = tgt_at → Y.cpu.gpr = X.cpu.gpr → GoG prof L o gev gP gE Y t')
    (kr : X.cpu.gpr.rdi = 0 → ∀ (Z : State) (t' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V →
      Z.cpu.rip = e₂.add j₂ → Z.cpu.gpr = (X.cpu.gpr.set 0 0).set 4 (X.cpu.gpr.rsp + 8) →
      GoG prof L o gev gP gE Z t') :
    GoG prof L o gev gP gE X t := by
  by_cases h0 : X.cpu.gpr.rdi = 0
  · refine (c_0 prof).run c hin (fun j' g' _ V' => j' = 18 ∧ g' = X.cpu.gpr.set 0 0 ∧ V' = V) hK hA
      (by rw [addr_add_zero]; exact hrip) (vc_z h0) ?_
    rintro j' g fl V₁ ⟨rfl, rfl, rfl⟩ Y t₁ hKY hAY hrY hgY -
    refine c.s_ret hKY hAY hin (lt_len (by decide)) hrY (ret_18 _) (fun i hi => by rw [hgY]; exact hl i hi)
      hin₂ h₂ (by rw [hgY]; exact hra) ?_
    rintro Z t' hKZ hAZ ⟨hrZ, hgZ⟩
    exact kr h0 Z t' hKZ hAZ hrZ (by rw [hgZ, hgY] <;> rfl)
  · refine (c_0 prof).run c hin (fun j' g' _ V' => j' = 9 ∧ g' = X.cpu.gpr ∧ V' = V) hK hA
      (by rw [addr_add_zero]; exact hrip) (vc_n h0) ?_
    rintro j' g fl V₁ ⟨rfl, rfl, rfl⟩ Y t₁ hKY hAY hrY hgY -
    refine c.s_jmp_x hKY hAY hin (lt_len (by decide)) hrY (jmp_9 _) hinT hT (by decide) ?_
    rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
    exact kj h0 Y₂ t₂ hK₂ hA₂ (by rw [hr₂, addr_add_zero]) (hg₂.trans hgY)

end FV7z.Mya
