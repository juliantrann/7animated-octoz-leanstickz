import FV7z.Sgw.Cuts
import FV7z.Close.Holds
import FV7z.Sga.Holds
import FV7z.Lemmas.CmpImm
/-!
# `__sigaction` checks the signal, then is `__libc_sigaction` (PLAN.md §M, M1)

glibc 2.31's `__sigaction (sig, act, oact)` at `0x6011d0` in `7zzs`: if `sig` (32 bits) is from 1 to 64 and not
`SIGCANCEL` (32) or `SIGSETXID` (33), a tail jump to `__libc_sigaction` (`Sga.sga_at`, `Sga.sga_ok`) with the
registers of the entry but `rax`; else `errno` (`fs:-0x48`, `Close.errnoAt`) set to `EINVAL` (22) and -1 in `eax`.
Two pieces of the code: from the entry (0) to the jump (20) or to the error path (32), and from 32 to the `ret` (51).

- `SigOk`: the two unsigned comparisons of the code, `sig - 1 ≤ 63` and `sig - 32 > 1` at 32 bits.
- `sgw_ok`: with `SigOk`, the run reaches `__libc_sigaction`'s entry with the registers of the entry but `rax`;
  without, the return address with `errno` set and `eax` -1.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn FV7z.Close
namespace FV7z.Sgw

/-- The jump to `__libc_sigaction`. -/
def pjm : List Byte := [0xe9, 0x07, 0xfe, 0xff, 0xff]
theorem pjm_0 : ∀ feat, Dec feat pjm 0 (FV7z.mk .jmp 64 [.rel 18446744073709551111] 5) := by dec_rfl
theorem wj_20 : pjm <+: sgw.drop 20 := by decide +kernel
theorem jmp_20 (feat : Features) : Dec feat sgw 20 (FV7z.mk .jmp 64 [.rel 18446744073709551111] 5) :=
  Dec.shift (j := 20) (k := 0) (pjm_0 feat) wj_20 (Nat.zero_le _)

/-- The `ret`. -/
def pret : List Byte := [0xc3]
theorem pret_0 : ∀ feat, Dec feat pret 0 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem w_51 : pret <+: sgw.drop 51 := by decide +kernel
theorem ret_51 (feat : Features) : Dec feat sgw 51 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 51) (k := 0) (pret_0 feat) w_51 (Nat.zero_le _)

/-- The signal from 1 to 64, not 32 or 33: `sig - 1 ≤ 63` and `sig - 32 > 1`, unsigned at 32 bits (`lea`: the sum
at 64 bits, its low half). -/
def SigOk (r : BitVec 64) : Prop :=
  (BitVec.setWidth 32 (r + 18446744073709551615#64)).toNat ≤ 63 ∧
    1 < (BitVec.setWidth 32 (r + 18446744073709551584#64)).toNat
/-- `EINVAL` as `errno`'s bytes. -/
abbrev einval : List Byte := toBytesLE (22#32) 4

variable {F : Footprint} {Wl : List Rgn}

/-- From the entry to the jump: a signal `SigOk`. -/
theorem vc_ok {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} (h : SigOk g.rdi) :
    W_0 fb F Wl (fun j' g' _ V' => j' = 20 ∧ (∃ a, g' = { g with rax := a }) ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  obtain ⟨h1, h2⟩ := h
  dsimp only at h1 h2 ⊢
  wpx [W_0, W_12, o0, o1, be_imm (w := 32) _ 63 (by decide), be_imm (w := 32) _ 1 (by decide)]
  refine ⟨fun hc => ?_, fun _ => ⟨fun hc => ?_, fun _ => ⟨_, rfl⟩⟩⟩
  · first
    | exact absurd h1 (by simpa using hc)
    | (simp at hc; omega)
  · first
    | exact absurd h2 (by simpa using hc)
    | (simp at hc; omega)

/-- From the entry to the error path: a signal not `SigOk`. -/
theorem vc_bad {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} (h : ¬ SigOk g.rdi) :
    W_0 fb F Wl (fun j' g' _ V' => j' = 32 ∧ (∃ a, g' = { g with rax := a }) ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  unfold SigOk at h
  dsimp only at h ⊢
  wpx [W_0, W_12, o0, o1, be_imm (w := 32) _ 63 (by decide), be_imm (w := 32) _ 1 (by decide)]
  refine ⟨fun _ => ⟨_, rfl⟩, fun hc0 => ⟨fun _ => ⟨_, rfl⟩, fun hc => (h ⟨?_, ?_⟩).elim⟩⟩
  · first
    | simpa using hc0
    | (simp at hc0; omega)
  · first
    | simpa using hc
    | (simp at hc; omega)

/-- The error path: `errno` = `EINVAL`, `eax` -1. -/
theorem vc_32 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} (fe : ∀ i < 4, Foot Wl ((errnoAt fb).add i)) :
    W_32 fb F Wl (fun j' g' _ V' => j' = 51 ∧ g' = { g with rax := 4294967295#64 } ∧ V' = Vst V (errnoAt fb) einval)
      g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_32, o2, Op.stfi]
  first
  | exact ⟨fe, rfl⟩
  | exact ⟨fe, by rw [show BitVec.setWidth 64 4294967295#32 = 4294967295#64 by decide]⟩

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop} {X : State}
  {t : Nat} {V : Addr → Byte}

/-- `__sigaction (sig, act, oact)` from its entry: with `SigOk`, at `__libc_sigaction`'s entry with the registers of
the entry but `rax` (`kj`); else at the return address, the return address popped, `errno` = `EINVAL` and `eax` -1
(`ke`). -/
theorem sgw_ok {fb : Addr} (c : Seg prof F Wl L s₀ o) (hfs : s₀.cpu.seg.fsBase = fb) (hin : CodeIn L sgw_at sgw)
    (hinl : CodeIn L Sga.sga_at Sga.sga) (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V)
    (hrip : X.cpu.rip = sgw_at)
    (fe : ∀ i < 4, Foot Wl ((errnoAt fb).add i)) (hfe : (errnoAt fb).toNat + 4 ≤ 2 ^ 64)
    (hl : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsp i)) (hsp : X.cpu.gpr.rsp.toNat + 8 ≤ 2 ^ 64)
    (hsa : (errnoAt fb).toNat + 4 ≤ X.cpu.gpr.rsp.toNat ∨ X.cpu.gpr.rsp.toNat + 8 ≤ (errnoAt fb).toNat)
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (hra : ofBytesLE 64 ((byteAddrs X.cpu.gpr.rsp 8).map V) = e₂.add j₂)
    (kj : SigOk X.cpu.gpr.rdi → ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y → Agree F Y.proc.mm.mem V →
      Y.cpu.rip = Sga.sga_at → (∃ a, Y.cpu.gpr = { X.cpu.gpr with rax := a }) → GoG prof L o gev gP gE Y t')
    (ke : ¬ SigOk X.cpu.gpr.rdi → ∀ (Z : State) (t' : Nat), KeptW Wl s₀ Z → Z.cpu.rip = e₂.add j₂ →
      Agree F Z.proc.mm.mem (Vst V (errnoAt fb) einval) →
      Z.cpu.gpr = { X.cpu.gpr with rax := 4294967295#64 }.set 4 (X.cpu.gpr.rsp + 8) →
      GoG prof L o gev gP gE Z t') :
    GoG prof L o gev gP gE X t := by
  by_cases hok : SigOk X.cpu.gpr.rdi
  · refine (c_0 prof fb).run c hfs hin
      (fun j' g' _ V' => j' = 20 ∧ (∃ a, g' = { X.cpu.gpr with rax := a }) ∧ V' = V) hK hA
      (by rw [addr_add_zero]; exact hrip) (vc_ok hok) ?_
    rintro j' g fl V₁ ⟨rfl, ⟨a, rfl⟩, hV₁⟩ Y t₁ hKY hAY hrY hgY -
    subst V₁
    refine c.s_jmp_x hKY hAY hin (lt_len (by decide)) hrY (jmp_20 _) hinl (Sga.lt_len (j := 0) (by decide))
      (by decide) ?_
    rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
    exact kj hok Y₂ t₂ hK₂ hA₂ (by rw [hr₂, addr_add_zero]) ⟨a, hg₂.trans hgY⟩
  · refine (c_0 prof fb).run c hfs hin
      (fun j' g' _ V' => j' = 32 ∧ (∃ a, g' = { X.cpu.gpr with rax := a }) ∧ V' = V) hK hA
      (by rw [addr_add_zero]; exact hrip) (vc_bad hok) ?_
    rintro j' g fl V₁ ⟨rfl, ⟨a, rfl⟩, hV₁⟩ Y t₁ hKY hAY hrY hgY -
    subst V₁
    refine (c_32 prof fb).run c hfs hin
      (fun j' g' _ V' => j' = 51 ∧ g' = { Y.cpu.gpr with rax := 4294967295#64 } ∧ V' = Vst V (errnoAt fb) einval)
      hKY hAY hrY (vc_32 fe) ?_
    rintro j' g fl V₂ ⟨rfl, rfl, rfl⟩ Z t₂ hKZ hAZ hrZ hgZ -
    have hspZ : Z.cpu.gpr.rsp = X.cpu.gpr.rsp := by rw [hgZ, hgY] <;> rfl
    refine c.s_ret hKZ hAZ hin (lt_len (by decide)) hrZ (ret_51 _) (fun i hi => by rw [hspZ]; exact hl i hi)
      hin₂ h₂ ?_ ?_
    · have hb : einval.length = 4 := toBytesLE_length _ _
      have h1 : (errnoAt fb).toNat + einval.length ≤ 2 ^ 64 := by rw [hb]; exact hfe
      have h2 : (errnoAt fb).toNat + einval.length ≤ X.cpu.gpr.rsp.toNat ∨
          X.cpu.gpr.rsp.toNat + 8 ≤ (errnoAt fb).toNat := by rw [hb]; exact hsa
      rw [hspZ, Tun.rd_Vst V (errnoAt fb) einval X.cpu.gpr.rsp 8 h1 hsp h2]
      exact hra
    rintro Z' t₃ hKZ' hAZ' ⟨hrZ', hgZ'⟩
    exact ke hok Z' t₃ hKZ' hrZ' hAZ' (by rw [hgZ', hgZ, hgY] <;> rfl)

end FV7z.Sgw
