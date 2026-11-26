import FV7z.Bsn.Cuts
import FV7z.Bsg.Blocks
import FV7z.Close.Holds
import FV7z.Lemmas.FnFar
import FV7z.Tun.Inv
/-!
# `__bsd_signal` (PLAN.md §M, M1)

glibc 2.31's `__bsd_signal (sig, handler)` at `0x6225b0` in `7zzs` (`signal/signal.c`; `objdump -d`): `sig` out of
1 to 64 (the `ja` at 10), `handler` = `SIG_ERR` (the `je` at 16), or `sig` 32 or 33, glibc's own (the `jbe` at 24):
`errno` (`Close.errnoAt`) set to `EINVAL` (22) and -1 in `rax` (32 to the `ret` at 53); else a tail jump (26) to
`__bsd_signal.part.0` (`Bsg.bsg_at`) with the registers as at the entry but `rax`.

The contract does not say which way a `sig` goes: a caller gives both ways (`k0`, `kj`).

- `vc_0`: from the entry to 26 or 32, only `rax` changed; `vc_32`: `errno` = `EINVAL`, `rax` -1.
- `bsn_ok`: from the entry to the return address (`k0`) or to `Bsg.bsg_at` (`kj`).
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn FV7z.Close
namespace FV7z.Bsn

/-- The jump to `__bsd_signal.part.0`. -/
def pjm : List Byte := [0xe9, 0x41, 0xff, 0xff, 0xff]
theorem pjm_0 : ∀ feat, Dec feat pjm 0 (FV7z.mk .jmp 64 [.rel 18446744073709551425] 5) := by dec_rfl
theorem wj_26 : pjm <+: bsn.drop 26 := by decide +kernel
theorem jmp_26 (feat : Features) : Dec feat bsn 26 (FV7z.mk .jmp 64 [.rel 18446744073709551425] 5) :=
  Dec.shift (j := 26) (k := 0) (pjm_0 feat) wj_26 (Nat.zero_le _)

/-- The `ret`. -/
def pret : List Byte := [0xc3]
theorem pret_0 : ∀ feat, Dec feat pret 0 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem w_53 : pret <+: bsn.drop 53 := by decide +kernel
theorem ret_53 (feat : Features) : Dec feat bsn 53 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 53) (k := 0) (pret_0 feat) w_53 (Nat.zero_le _)

/-- `EINVAL` as `errno`'s bytes. -/
abbrev einval : List Byte := toBytesLE (22#32) 4

variable {F : Footprint} {Wl : List Rgn}

/-- The checks of `sig` and `handler`: to 26 or 32, `rax` the only register changed, the bytes as they were. -/
theorem vc_0 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} :
    W_0 fb F Wl (fun j' g' _ V' => (j' = 26 ∨ j' = 32) ∧ (∃ a, g' = { g with rax := a }) ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_0, W_12, W_18, o0, o1, o2]
  all_goals repeat' (first
    | exact ⟨Or.inl rfl, ⟨_, rfl⟩, rfl⟩
    | exact ⟨Or.inr rfl, ⟨_, rfl⟩, rfl⟩
    | exact Or.inl trivial
    | exact Or.inr trivial
    | exact ⟨_, rfl⟩
    | exact trivial
    | exact rfl
    | apply And.intro
    | intro _)

/-- The error: `errno` = `EINVAL`, `rax` -1. -/
theorem vc_32 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} (fe : ∀ i < 4, Foot Wl ((errnoAt fb).add i)) :
    W_32 fb F Wl (fun j' g' _ V' => j' = 53 ∧ g' = { g with rax := 18446744073709551615#64 } ∧
      V' = Vst V (errnoAt fb) einval) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_32, o3, Op.stfi]
  first
  | exact fe
  | exact ⟨fe, rfl⟩

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {X : State} {t : Nat} {V : Addr → Byte}

/-- `__bsd_signal (sig, handler)` from its entry. The error: at the return address, the return address popped,
`errno` = `EINVAL` and `rax` -1 (`k0`). Else at `__bsd_signal.part.0`'s entry with the bytes as they were and the
registers as at the entry but `rax` (`kj`). -/
theorem bsn_ok {fb : Addr} (c : Seg prof F Wl L s₀ o)
    (hfs : s₀.cpu.seg.fsBase = fb) (hin : CodeIn L bsn_at bsn) (hinB : CodeIn L Bsg.bsg_at Bsg.bsg)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = bsn_at)
    (fe : ∀ i < 4, Foot Wl ((errnoAt fb).add i)) (hfe : (errnoAt fb).toNat + 4 ≤ 2 ^ 64)
    (hl : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsp i)) (hsp : X.cpu.gpr.rsp.toNat + 8 ≤ 2 ^ 64)
    (hsa : (errnoAt fb).toNat + 4 ≤ X.cpu.gpr.rsp.toNat ∨ X.cpu.gpr.rsp.toNat + 8 ≤ (errnoAt fb).toNat)
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (hra : ofBytesLE 64 ((byteAddrs X.cpu.gpr.rsp 8).map V) = e₂.add j₂)
    (k0 : ∀ (Z : State) (t' : Nat), KeptW Wl s₀ Z → Z.cpu.rip = e₂.add j₂ →
      Agree F Z.proc.mm.mem (Vst V (errnoAt fb) einval) →
      Z.cpu.gpr = { X.cpu.gpr with rax := 18446744073709551615#64 }.set 4 (X.cpu.gpr.rsp + 8) →
      GoG prof L o gev gP gE Z t')
    (kj : ∀ (Y : State) (t' : Nat) (a : BitVec 64), KeptW Wl s₀ Y → Agree F Y.proc.mm.mem V →
      Y.cpu.rip = Bsg.bsg_at → Y.cpu.gpr = { X.cpu.gpr with rax := a } → GoG prof L o gev gP gE Y t') :
    GoG prof L o gev gP gE X t := by
  have hrip' : X.cpu.rip = bsn_at.add 0 := by rw [addr_add_zero]; exact hrip
  refine (c_0 prof fb).run c hfs hin
    (fun j' g' _ V' => (j' = 26 ∨ j' = 32) ∧ (∃ a, g' = { X.cpu.gpr with rax := a }) ∧ V' = V)
    hK hA hrip' vc_0 ?_
  rintro j' g fl V₁ ⟨hj | hj, ⟨a, rfl⟩, hV₁⟩ Y t₁ hKY hAY hrY hgY - <;> subst hj <;> subst V₁
  · -- the tail jump
    refine c.s_jmp_x hKY hAY hin (lt_len (by decide)) hrY (jmp_26 _) hinB (Bsg.lt_len (j := 0) (by decide))
      (by decide) ?_
    rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
    exact kj Y₂ t₂ a hK₂ hA₂ (by rw [hr₂, addr_add_zero]) (by rw [hg₂, hgY])
  · -- the error
    refine (c_32 prof fb).run c hfs hin
      (fun j' g' _ V' => j' = 53 ∧ g' = { X.cpu.gpr with rax := 18446744073709551615#64 } ∧
        V' = Vst V (errnoAt fb) einval) hKY hAY hrY ?_ ?_
    · rw [hgY]
      exact vc_32 fe
    rintro j' g fl V₂ ⟨rfl, rfl, rfl⟩ Z t₂ hKZ hAZ hrZ hgZ -
    have hspZ : Z.cpu.gpr.rsp = X.cpu.gpr.rsp := by rw [hgZ] <;> rfl
    refine c.s_ret hKZ hAZ hin (lt_len (by decide)) hrZ (ret_53 _) (fun i hi => by rw [hspZ]; exact hl i hi)
      hin₂ h₂ ?_ ?_
    · have hb : einval.length = 4 := toBytesLE_length _ _
      have h1 : (errnoAt fb).toNat + einval.length ≤ 2 ^ 64 := by rw [hb]; exact hfe
      have h2 : (errnoAt fb).toNat + einval.length ≤ X.cpu.gpr.rsp.toNat ∨
          X.cpu.gpr.rsp.toNat + 8 ≤ (errnoAt fb).toNat := by rw [hb]; exact hsa
      rw [hspZ, Tun.rd_Vst V (errnoAt fb) einval X.cpu.gpr.rsp 8 h1 hsp h2]
      exact hra
    rintro Z' t₃ hKZ' hAZ' ⟨hrZ', hgZ'⟩
    exact k0 Z' t₃ hKZ' hrZ' hAZ' (by rw [hgZ', hgZ] <;> rfl)

end FV7z.Bsn
