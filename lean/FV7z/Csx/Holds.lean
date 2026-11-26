import FV7z.Csx.Cuts
import FV7z.Lemmas.LeafRet
import FV7z.Lemmas.FnFar
/-!
# `CriticalSection_Delete` at `0x448b80` (PLAN.md §M, M1)

7-Zip 26.06's second `CriticalSection_Delete (p)`, at `0x448b80` in `7zzs` (`C/Threads.c`; the name is the symbol
table's): with `p` null, a `ret`; else a tail jump to `0x5fd1d0` (glibc's `__pthread_mutex_unlock` by the symbol
table; its code a hypothesis, `hinT`) with the registers of the entry.

- `csx_ok`: `p` not null, the run at `0x5fd1d0` with the registers of the entry (`kj`); `p` null, at the return
  address with the return address popped (`kr`).
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Csx

/-- The tail jump. -/
def pjm : List Byte := [0xe9, 0x42, 0x46, 0x1b, 0x00]
theorem pjm_0 : ∀ feat, Dec feat pjm 0 (FV7z.mk .jmp 64 [.rel 1787458] 5) := by dec_rfl
theorem wj_9 : pjm <+: csx.drop 9 := by decide +kernel
theorem jmp_9 (feat : Features) : Dec feat csx 9 (FV7z.mk .jmp 64 [.rel 1787458] 5) :=
  Dec.shift (j := 9) (k := 0) (pjm_0 feat) wj_9 (Nat.zero_le _)

/-- The `ret`. -/
def pret : List Byte := [0xc3]
theorem pret_0 : ∀ feat, Dec feat pret 0 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem w_16 : pret <+: csx.drop 16 := by decide +kernel
theorem ret_16 (feat : Features) : Dec feat csx 16 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 16) (k := 0) (pret_0 feat) w_16 (Nat.zero_le _)

/-- The jump's target (glibc's code, not proved here). -/
abbrev tgt_at : Addr := 0x5fd1d0

variable {F : Footprint} {Wl : List Rgn}

/-- `p` null: to the `ret`. -/
theorem vc_z {g : Gprs} {f : Rflags} {V : Addr → Byte} (h : g.rdi = 0) :
    W_0 F Wl (fun j' g' _ V' => j' = 16 ∧ g' = g ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h
  subst h
  wpx [W_0, o0]
  first
  | done
  | rfl
  | exact ⟨fun _ => ⟨rfl, rfl⟩, fun hh => absurd hh (by decide)⟩
  | exact fun hh => absurd hh (by decide)
  | repeat' (first | rfl | trivial | (refine ⟨?_, ?_⟩) | (intro hh; exact absurd hh (by decide)) | intro _)

/-- `p` not null: to the jump. -/
theorem vc_n {g : Gprs} {f : Rflags} {V : Addr → Byte} (h : g.rdi ≠ 0) :
    W_0 F Wl (fun j' g' _ V' => j' = 9 ∧ g' = g ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h
  wpx [W_0, o0, BitVec.and_self, beq_iff_eq, h]
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

/-- `CriticalSection_Delete (p)` at `0x448b80` from its entry: `p` not null, at `0x5fd1d0` with the registers of the
entry (`kj`); `p` null, at the return address with the return address popped (`kr`). -/
theorem csx_ok (c : Seg prof F Wl L s₀ o) (hin : CodeIn L csx_at csx) (hK : KeptW Wl s₀ X)
    (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = csx_at)
    {cT : List Byte} (hinT : CodeIn L tgt_at cT) (hT : 0 < cT.length)
    (hl : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsp i))
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (hra : ofBytesLE 64 ((byteAddrs X.cpu.gpr.rsp 8).map V) = e₂.add j₂)
    (kj : X.cpu.gpr.rdi ≠ 0 → ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y → Agree F Y.proc.mm.mem V →
      Y.cpu.rip = tgt_at → Y.cpu.gpr = X.cpu.gpr → GoG prof L o gev gP gE Y t')
    (kr : X.cpu.gpr.rdi = 0 → ∀ (Z : State) (t' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V →
      Z.cpu.rip = e₂.add j₂ → Z.cpu.gpr = X.cpu.gpr.set 4 (X.cpu.gpr.rsp + 8) → GoG prof L o gev gP gE Z t') :
    GoG prof L o gev gP gE X t := by
  by_cases h0 : X.cpu.gpr.rdi = 0
  · refine (c_0 prof).run c hin (fun j' g' _ V' => j' = 16 ∧ g' = X.cpu.gpr ∧ V' = V) hK hA
      (by rw [addr_add_zero]; exact hrip) (vc_z h0) ?_
    rintro j' g fl V₁ ⟨rfl, rfl, rfl⟩ Y t₁ hKY hAY hrY hgY -
    refine c.s_ret hKY hAY hin (lt_len (by decide)) hrY (ret_16 _) (fun i hi => by rw [hgY]; exact hl i hi)
      hin₂ h₂ (by rw [hgY]; exact hra) ?_
    rintro Z t' hKZ hAZ ⟨hrZ, hgZ⟩
    exact kr h0 Z t' hKZ hAZ hrZ (by rw [hgZ, hgY] <;> rfl)
  · refine (c_0 prof).run c hin (fun j' g' _ V' => j' = 9 ∧ g' = X.cpu.gpr ∧ V' = V) hK hA
      (by rw [addr_add_zero]; exact hrip) (vc_n h0) ?_
    rintro j' g fl V₁ ⟨rfl, rfl, rfl⟩ Y t₁ hKY hAY hrY hgY -
    refine c.s_jmp_x hKY hAY hin (lt_len (by decide)) hrY (jmp_9 _) hinT hT (by decide) ?_
    rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
    exact kj h0 Y₂ t₂ hK₂ hA₂ (by rw [hr₂, addr_add_zero]) (hg₂.trans hgY)

end FV7z.Csx
